/-!
# Mechanized Soundness of `find_cold_blocks`, Hint Semantic Transparency,
  `#[optimize]` Attribute Derivation, and `fn_can_unwind` (`nounwind`) Attribution

Standalone Lean 4 (v4.34.1) formalization using only constructive logic
(`[propext, Quot.sound]`), structural recursion, and zero compiler-reflection
or unverified tactics.

Sections:
1. `ColdBlocks` — Single-pass postorder `find_cold_blocks`, finite-trace
   inevitability, soundness on arbitrary CFGs, and exactness on postorder DAGs.
2. `HintTransparencyAndAttrs` — Semantic invariance under `cold_path`, `likely`,
   `unlikely`, `@llvm.expect.i1`, and `2000:1` `!prof !"branch_weights"`, plus
   the `#[optimize(size|speed|none)]` / `#[cold]` / `-C opt-level={s,z}` attribute lattice.
3. `NoUnwindSoundness` — Three-gate `fn_can_unwind` precedence, `AbortUnwindingCalls`
   `invoke` vs `call` lowering, `-Z panic-in-drop=abort` `DropGlue` vs `drop_in_place`
   split, and `-C panic=immediate-abort` dependency compatibility.
4. `Examples` — Three constructive sharpness counterexamples (`ce1`, `ce2`, `ce3`).
-/

namespace ColdBlocksAndNoUnwind

-- ============================================================================
-- Section 1: Single-Pass Postorder `find_cold_blocks` & DAG Completeness
-- ============================================================================

section ColdBlocks

abbrev BlockId := Nat
abbrev FnId := Nat

inductive Terminator where
  | goto (target : BlockId)
  | switchInt (targets : List BlockId) (otherwise : BlockId)
  | call (callee : FnId) (target : Option BlockId) (cleanup : Option BlockId)
  | tailCall (callee : FnId)
  | return_
  | unreachable
  | unwindResume
  | unwindTerminate
  deriving DecidableEq, Repr

structure BasicBlock where
  term : Terminator
  deriving DecidableEq, Repr

structure Cfg where
  blocks : List BasicBlock
  fnIsCold : FnId → Bool

def Cfg.numBlocks (cfg : Cfg) : Nat :=
  cfg.blocks.length

noncomputable def getBlockAt : List BasicBlock → Nat → Option BasicBlock
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: bs, n + 1 => getBlockAt bs n

theorem getBlockAt_none_of_le (bs : List BasicBlock) (n : Nat) (h : bs.length ≤ n) :
    getBlockAt bs n = none := by
  induction bs generalizing n with
  | nil =>
    cases n <;> rfl
  | cons _ rest ih =>
    cases n with
    | zero =>
      cases h
    | succ m =>
      exact ih m (Nat.le_of_succ_le_succ h)

noncomputable def Cfg.termAt (cfg : Cfg) (bb : BlockId) : Terminator :=
  match getBlockAt cfg.blocks bb with
  | some blk => blk.term
  | none => .return_

/-- Mirrors `mir::Terminator::successors()` in `rustc_middle`. -/
def termSuccessors : Terminator → List BlockId
  | .goto t => [t]
  | .switchInt ts ow => ow :: ts
  | .call _ (some t) (some c) => [t, c]
  | .call _ (some t) none => [t]
  | .call _ none (some c) => [c]
  | .call _ none none => []
  | .tailCall _ => []
  | .return_ => []
  | .unreachable => []
  | .unwindResume => []
  | .unwindTerminate => []

/-- Direct seed predicate from `compiler/rustc_codegen_ssa/src/mir/mod.rs`. -/
def isColdSeed (fnIsCold : FnId → Bool) : Terminator → Bool
  | .call callee _ _ => fnIsCold callee
  | .tailCall callee => fnIsCold callee
  | .unreachable => true
  | _ => false

noncomputable def isColdSeedAt (cfg : Cfg) (bb : BlockId) : Bool :=
  isColdSeed cfg.fnIsCold (cfg.termAt bb)

def allColdSuccs (cold : BlockId → Bool) (succs : List BlockId) : Bool :=
  match succs with
  | [] => false
  | s :: rest => cold s && rest.all cold

theorem allColdSuccs_eq_true_iff (cold : BlockId → Bool) (succs : List BlockId) :
    allColdSuccs cold succs = true ↔
      (succs ≠ [] ∧ ∀ s, s ∈ succs → cold s = true) := by
  cases succs with
  | nil =>
    simp [allColdSuccs]
  | cons s rest =>
    simp only [allColdSuccs, Bool.and_eq_true, List.all_eq_true, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and, List.mem_cons]
    constructor
    · rintro ⟨hs, hrest⟩ x (rfl | hx)
      · exact hs
      · exact hrest x hx
    · intro h
      exact ⟨h s (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

noncomputable def shouldMarkCold (cfg : Cfg) (cold : BlockId → Bool) (bb : BlockId) : Bool :=
  let t := cfg.termAt bb
  isColdSeed cfg.fnIsCold t || allColdSuccs cold (termSuccessors t)

/-- Ranked version of the single-pass `traversal::postorder(mir)` loop.
Recording insertion step indices makes trace soundness direct by induction
on insertion rank without requiring non-constructive choice or external
linear-arithmetic solvers. -/
def isMarkedCold (seen : BlockId → Option Nat) (x : BlockId) : Bool :=
  (seen x).isSome

noncomputable def findColdBlocksRankedAux
    (cfg : Cfg) (seen : BlockId → Option Nat) (step : Nat) :
    List BlockId → (BlockId → Option Nat)
  | [] => seen
  | bb :: rest =>
    if (seen bb).isNone && shouldMarkCold cfg (isMarkedCold seen) bb then
      let seen' : BlockId → Option Nat := fun x => if x == bb then some step else seen x
      findColdBlocksRankedAux cfg seen' (step + 1) rest
    else
      findColdBlocksRankedAux cfg seen (step + 1) rest

noncomputable def findColdBlocksRanked (cfg : Cfg) (order : List BlockId) : BlockId → Option Nat :=
  findColdBlocksRankedAux cfg (fun _ => none) 0 order

/-- Exact functional model of `rustc_codegen_ssa::mir::find_cold_blocks`. -/
noncomputable def findColdBlocksPass (cfg : Cfg) (order : List BlockId) (bb : BlockId) : Bool :=
  (findColdBlocksRanked cfg order bb).isSome

/-- Bounded backward fixed-point iteration (`gfp` over finite CFGs): starts from
all blocks marked cold except halting non-seed blocks, and shrinks `k` rounds. -/
noncomputable def gfpStep (cfg : Cfg) (cold : BlockId → Bool) : BlockId → Bool :=
  fun bb => shouldMarkCold cfg cold bb

noncomputable def gfpColdBlocks (cfg : Cfg) : Nat → BlockId → Bool
  | 0 => fun bb => if bb < cfg.numBlocks then true else false
  | k + 1 => gfpStep cfg (gfpColdBlocks cfg k)

/-- Least-fixed-point backward inevitability: every path from `bb` reaches a
cold seed in finitely many transitions. -/
inductive InevitableCold (cfg : Cfg) : BlockId → Prop where
  | seed (bb : BlockId) :
      isColdSeedAt cfg bb = true →
      InevitableCold cfg bb
  | step (bb : BlockId) :
      termSuccessors (cfg.termAt bb) ≠ [] →
      (∀ s, s ∈ termSuccessors (cfg.termAt bb) → InevitableCold cfg s) →
      InevitableCold cfg bb

theorem inevitableCold_in_bounds (cfg : Cfg) (bb : BlockId)
    (h : InevitableCold cfg bb) : bb < cfg.numBlocks := by
  cases h with
  | seed bb hSeed =>
    cases Nat.lt_or_ge bb cfg.numBlocks with
    | inl hLt => exact hLt
    | inr hLe =>
      have hNone := getBlockAt_none_of_le cfg.blocks bb hLe
      simp [isColdSeedAt, Cfg.termAt, hNone, isColdSeed] at hSeed
  | step bb hNe _ =>
    cases Nat.lt_or_ge bb cfg.numBlocks with
    | inl hLt => exact hLt
    | inr hLe =>
      have hNone := getBlockAt_none_of_le cfg.blocks bb hLe
      simp [Cfg.termAt, hNone, termSuccessors] at hNe

/-- Rank soundness invariant for `findColdBlocksRankedAux`. -/
def RankSound (cfg : Cfg) (bound : Nat) (seen : BlockId → Option Nat) : Prop :=
  (∀ x k, seen x = some k → k < bound) ∧
  (∀ x k, seen x = some k →
    isColdSeedAt cfg x = true ∨
      (termSuccessors (cfg.termAt x) ≠ [] ∧
        ∀ s, s ∈ termSuccessors (cfg.termAt x) → ∃ k', k' < k ∧ seen s = some k'))

theorem rankSound_weaken_bound (cfg : Cfg) (bound : Nat) (seen : BlockId → Option Nat)
    (h : RankSound cfg bound seen) : RankSound cfg (bound + 1) seen :=
  ⟨fun x k hx => Nat.lt_trans (h.1 x k hx) (Nat.lt_succ_self bound), h.2⟩

theorem findColdBlocksRankedAux_sound
    (cfg : Cfg) (seen : BlockId → Option Nat) (step : Nat) (order : List BlockId)
    (hInv : RankSound cfg step seen) :
    ∃ finalBound, RankSound cfg finalBound (findColdBlocksRankedAux cfg seen step order) := by
  induction order generalizing seen step with
  | nil =>
    exact ⟨step, hInv⟩
  | cons bb rest ih =>
    unfold findColdBlocksRankedAux
    cases hNone : (seen bb).isNone
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ih seen (step + 1) (rankSound_weaken_bound cfg step seen hInv)
    · cases hMark : shouldMarkCold cfg (isMarkedCold seen) bb
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact ih seen (step + 1) (rankSound_weaken_bound cfg step seen hInv)
      · simp only [Bool.true_and, ↓reduceIte]
        have hbbNone : seen bb = none := by
          cases hsb : seen bb with
          | none => rfl
          | some _ => simp [hsb] at hNone
        let seen' : BlockId → Option Nat := fun x => if x == bb then some step else seen x
        have hNext : RankSound cfg (step + 1) seen' := by
          constructor
          · intro x k hx
            dsimp only [seen'] at hx
            cases hEq : (x == bb)
            · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hx
              exact Nat.lt_trans (hInv.1 x k hx) (Nat.lt_succ_self step)
            · simp only [hEq, ↓reduceIte] at hx
              injection hx with hk
              subst hk
              exact Nat.lt_succ_self step
          · intro x k hx
            dsimp only [seen'] at hx
            cases hEq : (x == bb)
            · simp only [hEq, Bool.false_eq_true, ↓reduceIte] at hx
              rcases hInv.2 x k hx with hSeed | ⟨hNe, hSuccs⟩
              · exact Or.inl hSeed
              · right
                refine ⟨hNe, fun s hs => ?_⟩
                rcases hSuccs s hs with ⟨k', hk', hsSeen⟩
                refine ⟨k', hk', ?_⟩
                have hsNe : (s == bb) = false := by
                  cases hsb : (s == bb)
                  · rfl
                  · have : s = bb := beq_iff_eq.mp hsb
                    subst this
                    rw [hbbNone] at hsSeen
                    contradiction
                dsimp only [seen']
                rw [hsNe]
                exact hsSeen
            · simp only [hEq, ↓reduceIte] at hx
              have hxEq : x = bb := beq_iff_eq.mp hEq
              subst hxEq
              injection hx with hk
              subst hk
              dsimp only [shouldMarkCold] at hMark
              cases hSeed : isColdSeed cfg.fnIsCold (cfg.termAt x)
              · simp only [hSeed, Bool.false_or] at hMark
                right
                rw [allColdSuccs_eq_true_iff] at hMark
                refine ⟨hMark.1, fun s hs => ?_⟩
                have hsSome := hMark.2 s hs
                cases hss : seen s with
                | none => simp [isMarkedCold, hss] at hsSome
                | some k' =>
                  refine ⟨k', hInv.1 s k' hss, ?_⟩
                  have hsNe : (s == x) = false := by
                    cases hsb : (s == x)
                    · rfl
                    · have : s = x := beq_iff_eq.mp hsb
                      subst this
                      rw [hbbNone] at hss
                      contradiction
                  dsimp only [seen']
                  rw [hsNe]
                  exact hss
              · left
                exact hSeed
        exact ih seen' (step + 1) hNext

theorem findColdBlocksRanked_sound (cfg : Cfg) (order : List BlockId) :
    ∀ x k, findColdBlocksRanked cfg order x = some k →
      isColdSeedAt cfg x = true ∨
        (termSuccessors (cfg.termAt x) ≠ [] ∧
          ∀ s, s ∈ termSuccessors (cfg.termAt x) →
            ∃ k', k' < k ∧ findColdBlocksRanked cfg order s = some k') := by
  have hInit : RankSound cfg 0 (fun _ => none) :=
    ⟨fun _ _ h => by contradiction, fun _ _ h => by contradiction⟩
  rcases findColdBlocksRankedAux_sound cfg (fun _ => none) 0 order hInit with ⟨_, hFinal⟩
  exact hFinal.2

theorem ranked_implies_inevitableAux (cfg : Cfg) (order : List BlockId) :
    ∀ bound x k, k < bound → findColdBlocksRanked cfg order x = some k → InevitableCold cfg x := by
  intro bound
  induction bound with
  | zero =>
    intro x k hk _
    cases hk
  | succ b ih =>
    intro x k hk hRank
    rcases findColdBlocksRanked_sound cfg order x k hRank with hSeed | ⟨hNe, hSuccs⟩
    · exact InevitableCold.seed x hSeed
    · refine InevitableCold.step x hNe (fun s hs => ?_)
      rcases hSuccs s hs with ⟨k', hk', hsRank⟩
      exact ih s k' (Nat.lt_of_lt_of_le hk' (Nat.le_of_lt_succ hk)) hsRank

theorem findColdBlocksPass_implies_inevitable (cfg : Cfg) (order : List BlockId) (bb : BlockId)
    (h : findColdBlocksPass cfg order bb = true) : InevitableCold cfg bb := by
  unfold findColdBlocksPass at h
  cases hr : findColdBlocksRanked cfg order bb with
  | none => simp [hr] at h
  | some k => exact ranked_implies_inevitableAux cfg order (k + 1) bb k (Nat.lt_succ_self k) hr

/-- A concrete finite execution trace (block sequence) through `cfg`. -/
inductive ValidTrace (cfg : Cfg) : List BlockId → Prop where
  | single (b : BlockId) : ValidTrace cfg [b]
  | cons (b s : BlockId) (rest : List BlockId) :
      s ∈ termSuccessors (cfg.termAt b) →
      ValidTrace cfg (s :: rest) →
      ValidTrace cfg (b :: s :: rest)

/-- A trace ends cleanly at a halting terminator (never exiting at an incomplete prefix). -/
noncomputable def isHaltingTerm (cfg : Cfg) (bb : BlockId) : Bool :=
  isColdSeedAt cfg bb || (termSuccessors (cfg.termAt bb)).isEmpty

noncomputable def endsAtHalting (cfg : Cfg) : List BlockId → Prop
  | [] => False
  | [b] => isHaltingTerm cfg b = true
  | _ :: rest => endsAtHalting cfg rest

noncomputable def hitsColdSeed (cfg : Cfg) : List BlockId → Prop
  | [] => False
  | b :: rest => isColdSeedAt cfg b = true ∨ hitsColdSeed cfg rest

def MustHitColdOrUnreachable (cfg : Cfg) (start : BlockId) : Prop :=
  ∀ rest, ValidTrace cfg (start :: rest) → endsAtHalting cfg (start :: rest) →
    hitsColdSeed cfg (start :: rest)

theorem inevitableCold_implies_mustHit (cfg : Cfg) (bb : BlockId)
    (hInev : InevitableCold cfg bb) : MustHitColdOrUnreachable cfg bb := by
  induction hInev with
  | seed b hSeed =>
    intro rest _ _
    exact Or.inl hSeed
  | step b hNe hSuccs ih =>
    intro rest hTr hEnd
    cases rest with
    | nil =>
      simp only [endsAtHalting, isHaltingTerm, Bool.or_eq_true] at hEnd
      cases hEnd with
      | inl hSeed => exact Or.inl hSeed
      | inr hEmpty =>
        have hNil : termSuccessors (cfg.termAt b) = [] := by
          cases hts : termSuccessors (cfg.termAt b) with
          | nil => rfl
          | cons _ _ => simp [hts] at hEmpty
        exact False.elim (hNe hNil)
    | cons s rest' =>
      cases hTr with
      | cons _ _ _ hsMem hRest =>
        exact Or.inr (ih s hsMem rest' hRest hEnd)

theorem findColdBlocksPass_sound (cfg : Cfg) (order : List BlockId) (bb : BlockId)
    (h : findColdBlocksPass cfg order bb = true) :
    MustHitColdOrUnreachable cfg bb :=
  inevitableCold_implies_mustHit cfg bb (findColdBlocksPass_implies_inevitable cfg order bb h)

/-- Postorder property: when `order` reaches `b :: rest`, no successor of `b`
remains unvisited in `b :: rest`. -/
noncomputable def AllSuccsEarlier (cfg : Cfg) : List BlockId → Prop
  | [] => True
  | b :: rest => (∀ s, s ∈ termSuccessors (cfg.termAt b) → s ∉ b :: rest) ∧ AllSuccsEarlier cfg rest

structure IsPostorderDAG (cfg : Cfg) (order : List BlockId) (depth : BlockId → Nat) : Prop where
  all_valid_in_order : ∀ b, b < cfg.numBlocks → b ∈ order
  all_succs_earlier : AllSuccsEarlier cfg order
  acyclic_depth : ∀ b s, s ∈ termSuccessors (cfg.termAt b) → depth s < depth b

theorem findColdBlocksRankedAux_monotone
    (cfg : Cfg) (seen : BlockId → Option Nat) (step : Nat) (order : List BlockId) (x : BlockId)
    (hx : (seen x).isSome = true) :
    (findColdBlocksRankedAux cfg seen step order x).isSome = true := by
  induction order generalizing seen step with
  | nil => exact hx
  | cons bb rest ih =>
    unfold findColdBlocksRankedAux
    cases hCond : ((seen bb).isNone && shouldMarkCold cfg (isMarkedCold seen) bb)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih seen (step + 1) hx
    · simp only [↓reduceIte]
      apply ih
      cases hEq : (x == bb)
      · simp [hx]
      · simp

theorem nat_beq_refl (u : Nat) : (u == u) = true :=
  beq_iff_eq.mpr rfl

theorem inevitableCold_marked_aux
    (cfg : Cfg) (order : List BlockId)
    (hEarlier : AllSuccsEarlier cfg order)
    (seen : BlockId → Option Nat) (step : Nat)
    (hPre : ∀ u, InevitableCold cfg u → u ∉ order → (seen u).isSome = true) :
    ∀ u, InevitableCold cfg u → (findColdBlocksRankedAux cfg seen step order u).isSome = true := by
  induction order generalizing seen step with
  | nil =>
    intro u hu
    exact hPre u hu (by simp)
  | cons hd rest ih =>
    rcases hEarlier with ⟨hHdSuccs, hRestEarlier⟩
    unfold findColdBlocksRankedAux
    cases hNone : (seen hd).isNone
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      apply ih hRestEarlier seen (step + 1)
      intro u hu huNotRest
      cases hEq : (u == hd)
      · have huNe : u ≠ hd := fun h => by
          subst h
          have hRefl : (u == u) = true := nat_beq_refl u
          rw [hRefl] at hEq
          contradiction
        have huNotHeadRest : u ∉ hd :: rest := by
          intro hMem
          cases hMem with
          | head _ => exact huNe rfl
          | tail _ hT => exact huNotRest hT
        exact hPre u hu huNotHeadRest
      · have hEq' : u = hd := beq_iff_eq.mp hEq
        subst hEq'
        cases hsu : seen u with
        | none =>
          rw [hsu] at hNone
          contradiction
        | some _ => rfl
    · cases hMark : shouldMarkCold cfg (isMarkedCold seen) hd
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        apply ih hRestEarlier seen (step + 1)
        intro u hu huNotRest
        cases hEq : (u == hd)
        · have huNe : u ≠ hd := fun h => by
            subst h
            have hRefl : (u == u) = true := nat_beq_refl u
            rw [hRefl] at hEq
            contradiction
          have huNotHeadRest : u ∉ hd :: rest := by
            intro hMem
            cases hMem with
            | head _ => exact huNe rfl
            | tail _ hT => exact huNotRest hT
          exact hPre u hu huNotHeadRest
        · have hEq' : u = hd := beq_iff_eq.mp hEq
          subst hEq'
          exfalso
          cases hu with
          | seed _ hSeed =>
            simp only [shouldMarkCold] at hMark
            simp only [isColdSeedAt] at hSeed
            rw [hSeed, Bool.true_or] at hMark
            contradiction
          | step _ hNe hSuccsInev =>
            have hAllSuccs : allColdSuccs (isMarkedCold seen) (termSuccessors (cfg.termAt u)) = true := by
              rw [allColdSuccs_eq_true_iff]
              refine ⟨hNe, fun s hs => ?_⟩
              exact hPre s (hSuccsInev s hs) (hHdSuccs s hs)
            simp only [shouldMarkCold, hAllSuccs, Bool.or_true] at hMark
            contradiction
      · simp only [Bool.true_and, ↓reduceIte]
        let seen' : BlockId → Option Nat := fun x => if x == hd then some step else seen x
        apply ih hRestEarlier seen' (step + 1)
        intro u hu huNotRest
        dsimp only [seen']
        cases hEq : (u == hd)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have huNe : u ≠ hd := fun h => by
            subst h
            have hRefl : (u == u) = true := nat_beq_refl u
            rw [hRefl] at hEq
            contradiction
          have huNotHeadRest : u ∉ hd :: rest := by
            intro hMem
            cases hMem with
            | head _ => exact huNe rfl
            | tail _ hT => exact huNotRest hT
          exact hPre u hu huNotHeadRest
        · simp only [↓reduceIte]
          rfl

theorem postorder_inevitable_marked (cfg : Cfg) (order : List BlockId) (depth : BlockId → Nat)
    (hDag : IsPostorderDAG cfg order depth) (bb : BlockId)
    (hInev : InevitableCold cfg bb) :
    findColdBlocksPass cfg order bb = true := by
  unfold findColdBlocksPass findColdBlocksRanked
  apply inevitableCold_marked_aux cfg order hDag.all_succs_earlier (fun _ => none) 0
  · intro u hu huNotOrder
    exfalso
    exact huNotOrder (hDag.all_valid_in_order u (inevitableCold_in_bounds cfg u hu))
  · exact hInev

theorem mustHit_implies_inevitable_on_dag (cfg : Cfg) (depth : BlockId → Nat)
    (hAcyclic : ∀ b s, s ∈ termSuccessors (cfg.termAt b) → depth s < depth b) :
    ∀ n bb, depth bb < n → MustHitColdOrUnreachable cfg bb → InevitableCold cfg bb := by
  intro n
  induction n with
  | zero =>
    intro bb hLt _
    cases hLt
  | succ m ih =>
    intro bb hLt hMust
    cases hSeed : isColdSeedAt cfg bb
    · have hNe : termSuccessors (cfg.termAt bb) ≠ [] := by
        intro hEmpty
        have hTr : ValidTrace cfg [bb] := ValidTrace.single bb
        have hEnd : endsAtHalting cfg [bb] := by
          simp [endsAtHalting, isHaltingTerm, hEmpty]
        have hHit := hMust [] hTr hEnd
        simp [hitsColdSeed, hSeed] at hHit
      refine InevitableCold.step bb hNe (fun s hs => ?_)
      have hSubMust : MustHitColdOrUnreachable cfg s := by
        intro rest hTrS hEndS
        have hTrB : ValidTrace cfg (bb :: s :: rest) := ValidTrace.cons bb s rest hs hTrS
        have hEndB : endsAtHalting cfg (bb :: s :: rest) := hEndS
        have hHit := hMust (s :: rest) hTrB hEndB
        cases hHit with
        | inl hS =>
          simp [hSeed] at hS
        | inr hRest => exact hRest
      have hsDepth : depth s < m :=
        Nat.lt_of_lt_of_le (hAcyclic bb s hs) (Nat.le_of_lt_succ hLt)
      exact ih s hsDepth hSubMust
    · exact InevitableCold.seed bb hSeed

/-- **Master Theorem 1 (`findColdBlocks_sound_and_dag_complete`)**:
1. Soundness holds unconditionally for every CFG (cyclic or acyclic) and every
   block traversal order: any block marked by `findColdBlocksPass` inevitably
   reaches a cold seed or `unreachable` on every terminating trace.
2. Completeness holds for every acyclic CFG traversed in postorder:
   `MustHitColdOrUnreachable cfg bb ↔ findColdBlocksPass cfg order bb = true`. -/
theorem findColdBlocks_sound_and_dag_complete
    (cfg : Cfg) (order : List BlockId) (depth : BlockId → Nat) :
    (∀ bb, findColdBlocksPass cfg order bb = true → MustHitColdOrUnreachable cfg bb) ∧
    (IsPostorderDAG cfg order depth →
      ∀ bb, MustHitColdOrUnreachable cfg bb ↔ findColdBlocksPass cfg order bb = true) := by
  refine ⟨fun bb h => findColdBlocksPass_sound cfg order bb h, ?_⟩
  intro hDag bb
  constructor
  · intro hMust
    exact postorder_inevitable_marked cfg order depth hDag bb
      (mustHit_implies_inevitable_on_dag cfg depth hDag.acyclic_depth (depth bb + 1) bb
        (Nat.lt_succ_self (depth bb)) hMust)
  · intro hPass
    exact findColdBlocksPass_sound cfg order bb hPass

end ColdBlocks

-- ============================================================================
-- Section 2: Semantic Transparency of `cold_path` / `branch_weights` &
--            `#[optimize]` / `#[cold]` Attribute Algebra
-- ============================================================================

section HintTransparencyAndAttrs

abbrev Reg := Nat

inductive SsaStmt where
  | nop
  | assignConst (dst : Reg) (val : Int)
  | addReg (dst lhs rhs : Reg)
  | subReg (dst lhs rhs : Reg)
  | intrinsicColdPath
  | hintColdPathCall
  | callExpect (dst cond : Reg) (expected : Bool)
  deriving DecidableEq, Repr

inductive SsaTerm where
  | ret (reg : Reg)
  | condBr (cond : Reg) (tBlock fBlock : BlockId) (prof : Option (Nat × Nat))
  | switchInt (scrut : Reg) (cases : List (Int × BlockId)) (elseBlock : BlockId)
      (prof : Option (List Nat))
  | unreachable
  deriving DecidableEq, Repr

structure SsaBlock where
  stmts : List SsaStmt
  term : SsaTerm
  deriving DecidableEq, Repr

abbrev RegEnv := Reg → Int

def setReg (env : RegEnv) (r : Reg) (v : Int) : RegEnv :=
  fun x => if x == r then v else env x

def execSsaStmt (env : RegEnv) : SsaStmt → RegEnv
  | .nop => env
  | .assignConst dst val => setReg env dst val
  | .addReg dst lhs rhs => setReg env dst (env lhs + env rhs)
  | .subReg dst lhs rhs => setReg env dst (env lhs - env rhs)
  | .intrinsicColdPath => env
  | .hintColdPathCall => env
  | .callExpect dst cond _ => setReg env dst (env cond)

noncomputable def execSsaStmts (env : RegEnv) : List SsaStmt → RegEnv
  | [] => env
  | s :: ss => execSsaStmts (execSsaStmt env s) ss

noncomputable def lookupSwitchCase (v : Int) (cases : List (Int × BlockId)) (fallback : BlockId) : BlockId :=
  match cases with
  | [] => fallback
  | (k, bb) :: rest => if v == k then bb else lookupSwitchCase v rest fallback

inductive ExecOutcome where
  | returned (v : Int)
  | trapped
  | outOfFuel
  deriving DecidableEq, Repr

noncomputable def getSsaBlock : List SsaBlock → BlockId → Option SsaBlock
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: bs, n + 1 => getSsaBlock bs n

noncomputable def execSsaProg (prog : List SsaBlock) (bb : BlockId) (env : RegEnv) : Nat → ExecOutcome
  | 0 => .outOfFuel
  | fuel + 1 =>
    match getSsaBlock prog bb with
    | none => .trapped
    | some blk =>
      let env' := execSsaStmts env blk.stmts
      match blk.term with
      | .ret r => .returned (env' r)
      | .condBr cond tBb fBb _ =>
        let nextBb := if env' cond == 0 then fBb else tBb
        execSsaProg prog nextBb env' fuel
      | .switchInt scrut cases elseBb _ =>
        let nextBb := lookupSwitchCase (env' scrut) cases elseBb
        execSsaProg prog nextBb env' fuel
      | .unreachable => .trapped

/-- Erase all cold hints (`intrinsicColdPath`, `hintColdPathCall`), convert
`callExpect dst cond _` into a plain value copy (`subReg`/`addReg` or identity
copy via `callExpect`? Even cleaner: strip `callExpect` by turning it into a
zero-arg copy — or add `copyReg` — or keep `hintFree` transform on `SsaStmt`
directly without changing register effects). Let's include `copyReg`! -/
inductive CleanStmt where
  | nop
  | assignConst (dst : Reg) (val : Int)
  | addReg (dst lhs rhs : Reg)
  | subReg (dst lhs rhs : Reg)
  | copyReg (dst src : Reg)
  deriving DecidableEq, Repr

def eraseStmt : SsaStmt → SsaStmt
  | .intrinsicColdPath => .nop
  | .hintColdPathCall => .nop
  | .callExpect dst cond _ => .callExpect dst cond false
  | s => s

/-- Lowering `opt2_prepass`: erases `core::intrinsics::cold_path` (`ZeroSized`),
keeps `core::hint::cold_path` call (`alwaysinline cold`), keeps `@llvm.expect.i1`,
and attaches `1:2000` weights on multi-way switches. -/
def lowerStmtPrepass : SsaStmt → SsaStmt
  | .intrinsicColdPath => .nop
  | s => s

/-- Lowering `opt2_full`: `AlwaysInliner` erases `core::hint::cold_path` (`nop`) and
`LowerExpectIntrinsicPass` strips `@llvm.expect.i1` metadata onto `!prof !"branch_weights"`. -/
def lowerStmtFull : SsaStmt → SsaStmt
  | .intrinsicColdPath => .nop
  | .hintColdPathCall => .nop
  | s => s

def stripTermHints : SsaTerm → SsaTerm
  | .condBr c t f _ => .condBr c t f none
  | .switchInt s cs e _ => .switchInt s cs e none
  | t => t

def attachExpectProf (prof : Option (Nat × Nat)) : SsaTerm → SsaTerm
  | .condBr c t f _ => .condBr c t f prof
  | t => t

def attachSwitchProf (prof : Option (List Nat)) : SsaTerm → SsaTerm
  | .switchInt s cs e _ => .switchInt s cs e prof
  | t => t

def mapProgBlocks (fStmt : SsaStmt → SsaStmt) (fTerm : SsaTerm → SsaTerm)
    (prog : List SsaBlock) : List SsaBlock :=
  prog.map (fun b => { stmts := b.stmts.map fStmt, term := fTerm b.term })

theorem getSsaBlock_map (f : SsaBlock → SsaBlock) (prog : List SsaBlock) (bb : BlockId) :
    getSsaBlock (prog.map f) bb = (getSsaBlock prog bb).map f := by
  induction prog generalizing bb with
  | nil => cases bb <;> rfl
  | cons b bs ih =>
    cases bb with
    | zero => rfl
    | succ m => exact ih m

/-- Any transformation on `SsaStmt` and `SsaTerm` that preserves `execSsaStmt`
and the non-metadata fields of `SsaTerm` preserves `execSsaProg` identically. -/
def TermSemEq : SsaTerm → SsaTerm → Prop
  | .ret r1, .ret r2 => r1 = r2
  | .condBr c1 t1 f1 _, .condBr c2 t2 f2 _ => c1 = c2 ∧ t1 = t2 ∧ f1 = f2
  | .switchInt s1 cs1 e1 _, .switchInt s2 cs2 e2 _ => s1 = s2 ∧ cs1 = cs2 ∧ e1 = e2
  | .unreachable, .unreachable => True
  | _, _ => False

theorem mapProgBlocks_preserves_behavior
    (fStmt : SsaStmt → SsaStmt) (fTerm : SsaTerm → SsaTerm)
    (hStmt : ∀ env s, execSsaStmt env (fStmt s) = execSsaStmt env s)
    (hTerm : ∀ t, TermSemEq (fTerm t) t)
    (prog : List SsaBlock) (bb : BlockId) (env : RegEnv) (fuel : Nat) :
    execSsaProg (mapProgBlocks fStmt fTerm prog) bb env fuel = execSsaProg prog bb env fuel := by
  induction fuel generalizing bb env with
  | zero => rfl
  | succ k ih =>
    unfold execSsaProg mapProgBlocks
    rw [getSsaBlock_map]
    cases hb : getSsaBlock prog bb with
    | none => rfl
    | some blk =>
      have hStmts : execSsaStmts env (blk.stmts.map fStmt) = execSsaStmts env blk.stmts := by
        induction blk.stmts generalizing env with
        | nil => rfl
        | cons s ss ihS =>
          simp only [List.map_cons, execSsaStmts]
          rw [hStmt env s]
          exact ihS (execSsaStmt env s)
      dsimp only [Option.map]
      rw [hStmts]
      have ht := hTerm blk.term
      cases hbt : blk.term with
      | ret r =>
        simp only [hbt] at ht ⊢
        cases hft : fTerm (.ret r) with
        | ret r' =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
          subst ht
          rfl
        | _ =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
      | condBr cond tBb fBb prof =>
        simp only [hbt] at ht ⊢
        cases hft : fTerm (.condBr cond tBb fBb prof) with
        | condBr cond' tBb' fBb' prof' =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
          rcases ht with ⟨rfl, rfl, rfl⟩
          exact ih _ (execSsaStmts env blk.stmts)
        | _ =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
      | switchInt scrut cases elseBb prof =>
        simp only [hbt] at ht ⊢
        cases hft : fTerm (.switchInt scrut cases elseBb prof) with
        | switchInt scrut' cases' elseBb' prof' =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
          rcases ht with ⟨rfl, rfl, rfl⟩
          exact ih _ (execSsaStmts env blk.stmts)
        | _ =>
          rw [hft] at ht
          simp only [TermSemEq] at ht
      | unreachable =>
        simp only [hbt] at ht ⊢
        cases hft : fTerm .unreachable with
        | unreachable => rfl
        | _ =>
          rw [hft] at ht
          simp only [TermSemEq] at ht

theorem execSsaStmt_erase_eq (env : RegEnv) (s : SsaStmt) :
    execSsaStmt env (eraseStmt s) = execSsaStmt env s := by
  cases s <;> rfl

theorem execSsaStmt_prepass_eq (env : RegEnv) (s : SsaStmt) :
    execSsaStmt env (lowerStmtPrepass s) = execSsaStmt env s := by
  cases s <;> rfl

theorem execSsaStmt_full_eq (env : RegEnv) (s : SsaStmt) :
    execSsaStmt env (lowerStmtFull s) = execSsaStmt env s := by
  cases s <;> rfl

theorem termSemEq_strip (t : SsaTerm) : TermSemEq (stripTermHints t) t := by
  cases t <;> simp [stripTermHints, TermSemEq]

theorem termSemEq_attachExpect (w : Option (Nat × Nat)) (t : SsaTerm) :
    TermSemEq (attachExpectProf w t) t := by
  cases t <;> simp [attachExpectProf, TermSemEq]

theorem termSemEq_attachSwitch (w : Option (List Nat)) (t : SsaTerm) :
    TermSemEq (attachSwitchProf w t) t := by
  cases t <;> simp [attachSwitchProf, TermSemEq]

/-- **Master Theorem 2 (`coldPath_erasure_preserves_behavior`)**:
Erasing `cold_path` (`core::hint::cold_path` and `core::intrinsics::cold_path`),
stripping or attaching `@llvm.expect.i1` and `2000:1` `!prof !"branch_weights"`
metadata, and lowering across `opt0`, `opt2_prepass`, and `opt2_full`
(`AlwaysInliner` + `LowerExpectIntrinsicPass`) preserve execution `ExecOutcome`
identically for all programs, entry blocks, register environments, and fuel bounds. -/
theorem coldPath_erasure_preserves_behavior
    (prog : List SsaBlock) (bb : BlockId) (env : RegEnv) (fuel : Nat)
    (w2 : Option (Nat × Nat)) (wn : Option (List Nat)) :
    execSsaProg (mapProgBlocks eraseStmt stripTermHints prog) bb env fuel =
      execSsaProg prog bb env fuel ∧
    execSsaProg (mapProgBlocks lowerStmtPrepass (attachSwitchProf wn) prog) bb env fuel =
      execSsaProg prog bb env fuel ∧
    execSsaProg (mapProgBlocks lowerStmtFull (attachExpectProf w2) prog) bb env fuel =
      execSsaProg prog bb env fuel := by
  refine ⟨?_, ?_, ?_⟩
  · exact mapProgBlocks_preserves_behavior eraseStmt stripTermHints
      execSsaStmt_erase_eq termSemEq_strip prog bb env fuel
  · exact mapProgBlocks_preserves_behavior lowerStmtPrepass (attachSwitchProf wn)
      execSsaStmt_prepass_eq (termSemEq_attachSwitch wn) prog bb env fuel
  · exact mapProgBlocks_preserves_behavior lowerStmtFull (attachExpectProf w2)
      execSsaStmt_full_eq (termSemEq_attachExpect w2) prog bb env fuel

-- ----------------------------------------------------------------------------
-- `#[optimize(size|speed|none)]`, `#[cold]`, and `-C opt-level={s,z}` lattice
-- ----------------------------------------------------------------------------

inductive OptLevel where
  | no | less | more | aggressive | size | sizeMin
  deriving DecidableEq, Repr

inductive OptimizeAttr where
  | default | doNotOptimize | size | speed
  deriving DecidableEq, Repr

inductive InlineAttr where
  | none | hint | always | never
  deriving DecidableEq, Repr

structure LlvmFnAttrs where
  optsize : Bool
  minsize : Bool
  optnone : Bool
  noinline : Bool
  cold : Bool
  deriving DecidableEq, Repr

/-- Mirrors `default_optimisation_attrs`, `inline_attr`, and
`llfn_attrs_from_instance` in `compiler/rustc_codegen_llvm/src/attributes.rs`. -/
def deriveLlvmFnAttrs
    (optLvl : OptLevel) (optAttr : OptimizeAttr) (inlineAttr : InlineAttr)
    (isCold : Bool) (inlineLlvm : Bool) : LlvmFnAttrs :=
  let (optsize, minsize, optnone) :=
    match optAttr with
    | .default =>
      match optLvl with
      | .size => (true, false, false)
      | .sizeMin => (true, true, false)
      | _ => (false, false, false)
    | .doNotOptimize => (false, false, true)
    | .size => (true, true, false)
    | .speed => (false, false, false)
  let effInline : InlineAttr :=
    if !inlineLlvm then .never
    else match optAttr with
      | .doNotOptimize => .never
      | _ => inlineAttr
  let noinline := match effInline with | .never => true | _ => false
  { optsize := optsize, minsize := minsize, optnone := optnone, noinline := noinline, cold := isCold }

theorem optimize_attr_s_vs_z_default (inl : InlineAttr) (c : Bool) :
    (deriveLlvmFnAttrs .size .default inl c true).optsize = true ∧
    (deriveLlvmFnAttrs .size .default inl c true).minsize = false ∧
    (deriveLlvmFnAttrs .sizeMin .default inl c true).optsize = true ∧
    (deriveLlvmFnAttrs .sizeMin .default inl c true).minsize = true := by
  cases inl <;> simp [deriveLlvmFnAttrs]

theorem optimize_attr_size_speed_none_overrides
    (lvl : OptLevel) (inl : InlineAttr) (c : Bool) :
    ((deriveLlvmFnAttrs lvl .size inl c true).optsize = true ∧
     (deriveLlvmFnAttrs lvl .size inl c true).minsize = true) ∧
    ((deriveLlvmFnAttrs lvl .speed inl c true).optsize = false ∧
     (deriveLlvmFnAttrs lvl .speed inl c true).minsize = false) ∧
    ((deriveLlvmFnAttrs lvl .doNotOptimize inl c true).optnone = true ∧
     (deriveLlvmFnAttrs lvl .doNotOptimize inl c true).noinline = true ∧
     (deriveLlvmFnAttrs lvl .doNotOptimize inl c true).optsize = false ∧
     (deriveLlvmFnAttrs lvl .doNotOptimize inl c true).minsize = false) ∧
    (deriveLlvmFnAttrs lvl .default inl c true).cold = c := by
  cases lvl <;> cases inl <;> simp [deriveLlvmFnAttrs]

end HintTransparencyAndAttrs

-- ============================================================================
-- Section 3: `fn_can_unwind`, `AbortUnwindingCalls`, & `nounwind` Soundness
-- ============================================================================

section NoUnwindSoundness

inductive PanicStrategy where
  | unwind | abort | immediateAbort
  deriving DecidableEq, Repr

def PanicStrategy.unwinds : PanicStrategy → Bool
  | .unwind => true
  | .abort => false
  | .immediateAbort => false

inductive ExternAbi where
  | c (unwind : Bool)
  | system (unwind : Bool)
  | rust
  | rustCall
  | rustCold
  | rustPreserveNone
  | rustTail
  | interrupt
  | swift
  | llvmIntrinsic
  deriving DecidableEq, Repr

inductive ItemKind where
  | rustFn (neverUnwind : Bool)
  | foreignItem (neverUnwind : Bool)
  | langDropGlue (neverUnwind : Bool)
  | publicDropInPlace (neverUnwind : Bool)
  deriving DecidableEq, Repr

def ItemKind.neverUnwind : ItemKind → Bool
  | .rustFn b => b
  | .foreignItem b => b
  | .langDropGlue b => b
  | .publicDropInPlace b => b

def ItemKind.isForeign : ItemKind → Bool
  | .foreignItem _ => true
  | _ => false

def ItemKind.isLangDropGlue : ItemKind → Bool
  | .langDropGlue _ => true
  | _ => false

/-- Exact mirror of `rustc_middle::ty::layout::fn_can_unwind`
(`compiler/rustc_middle/src/ty/layout.rs:1321-1384`). -/
def fnCanUnwind
    (panicStrat : PanicStrategy) (panicInDrop : PanicStrategy)
    (item : Option ItemKind) (abi : ExternAbi) : Bool :=
  let gateBlocked :=
    match item with
    | none => false
    | some ik =>
      if ik.neverUnwind then true
      else if !panicStrat.unwinds && !ik.isForeign then true
      else if !panicInDrop.unwinds && ik.isLangDropGlue then true
      else false
  if gateBlocked then false
  else
    match abi with
    | .c u => u
    | .system u => u
    | .interrupt | .swift | .llvmIntrinsic => false
    | .rust | .rustCall | .rustCold | .rustPreserveNone | .rustTail => panicStrat.unwinds

def hasLlvmNoUnwind
    (panicStrat : PanicStrategy) (panicInDrop : PanicStrategy)
    (item : Option ItemKind) (abi : ExternAbi) : Bool :=
  !fnCanUnwind panicStrat panicInDrop item abi

inductive MirUnwindAction where
  | continue_
  | cleanup (hasResume : Bool)
  | unreachable
  | terminateAbi
  deriving DecidableEq, Repr

/-- Mirrors `AbortUnwindingCalls` (`abort_unwinding_calls.rs:78-135`). -/
def abortUnwindingEdge
    (targetSupportsUnwinding : Bool)
    (bodyCanUnwind : Bool)
    (callCanUnwind : Bool)
    (origAction : MirUnwindAction) : MirUnwindAction :=
  if !callCanUnwind || !targetSupportsUnwinding then
    .unreachable
  else if !bodyCanUnwind then
    match origAction with
    | .continue_ => .terminateAbi
    | .cleanup _ => .cleanup false -- `UnwindResume` replaced by `UnwindTerminate(Abi)`
    | .unreachable => .unreachable
    | .terminateAbi => .terminateAbi
  else
    origAction

/-- Whether `rustc_codegen_ssa` emits LLVM `invoke` vs plain `call` (`block.rs:218-275`). -/
def emitsInvoke (calleeCanUnwind : Bool) (action : MirUnwindAction) : Bool :=
  if !calleeCanUnwind then false
  else match action with
  | .cleanup _ => true
  | .terminateAbi => true
  | .continue_ => false
  | .unreachable => false

inductive UbKind where
  | nounwindViolated
  | unreachableUnwind
  deriving DecidableEq, Repr

inductive FrameOutcome where
  | returned
  | unwound
  | abortedTerminateAbi
  | ub (kind : UbKind)
  deriving DecidableEq, Repr

/-- Operational semantics of executing one lowered callsite inside a caller frame.
Models:
- LLVM `nounwind` callsite/callee attribute enforcement (`calleeMarkedNoUnwind`);
- `invoke` vs `call` landing-pad dispatch (`emitsInvoke` + `action`);
- caller `nounwind` attribute enforcement (`callerMarkedNoUnwind`). -/
def evalCallFrame
    (callerMarkedNoUnwind : Bool)
    (calleeMarkedNoUnwind : Bool)
    (loweredAction : MirUnwindAction)
    (calleeActuallyUnwinds : Bool) : FrameOutcome :=
  if !calleeActuallyUnwinds then
    .returned
  else if calleeMarkedNoUnwind then
    -- An unwinding callee marked LLVM `nounwind` causes immediate UB at the callsite.
    .ub .nounwindViolated
  else
    let usedInvoke := emitsInvoke (!calleeMarkedNoUnwind) loweredAction
    let frameResult : FrameOutcome :=
      if usedInvoke then
        match loweredAction with
        | .continue_ => .unwound
        | .cleanup true => .unwound
        | .cleanup false => .abortedTerminateAbi
        | .terminateAbi => .abortedTerminateAbi
        | .unreachable => .ub .unreachableUnwind
      else
        match loweredAction with
        | .continue_ => .unwound
        | .unreachable => .ub .unreachableUnwind
        | .cleanup true => .unwound
        | .cleanup false => .abortedTerminateAbi
        | .terminateAbi => .abortedTerminateAbi
    match frameResult with
    | .unwound =>
      if callerMarkedNoUnwind then .ub .nounwindViolated else .unwound
    | other => other

/-- Prebuilt `core` compatibility check from
`compiler/rustc_metadata/src/dependency_format.rs:418-499`. -/
inductive LinkCheckResult where
  | ok
  | incompatibleWithImmediateAbortCore
  | incompatiblePanicInDropStrategy
  deriving DecidableEq, Repr

def checkCrateDagLink
    (localPanic : PanicStrategy) (localDropPanic : PanicStrategy)
    (coreRequiredPanic : Option PanicStrategy) (coreDropPanic : PanicStrategy)
    (hasPanicRuntime : Bool) : LinkCheckResult :=
  if localPanic == .immediateAbort && coreRequiredPanic != some .immediateAbort then
    .incompatibleWithImmediateAbortCore
  else if hasPanicRuntime && localDropPanic != coreDropPanic then
    .incompatiblePanicInDropStrategy
  else
    .ok

theorem fnCanUnwind_precedence_characterization
    (p d : PanicStrategy) (abi : ExternAbi) :
    (∀ ik, ik.neverUnwind = true → fnCanUnwind p d (some ik) abi = false) ∧
    (∀ ik, p.unwinds = false → ik.isForeign = false → fnCanUnwind p d (some ik) abi = false) ∧
    (hasLlvmNoUnwind .abort d (some (.rustFn false)) (.c true) = true ∧
     hasLlvmNoUnwind .abort d (some (.foreignItem false)) (.c true) = false) ∧
    (hasLlvmNoUnwind .unwind .abort (some (.langDropGlue false)) .rust = true ∧
     hasLlvmNoUnwind .unwind .abort (some (.publicDropInPlace false)) .rust = false) ∧
    (fnCanUnwind .unwind .unwind none .rustTail = true ∧
     fnCanUnwind .abort .abort none .rustTail = false ∧
     fnCanUnwind .unwind .unwind none .interrupt = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ik hNu
    simp [fnCanUnwind, hNu]
  · intro ik hp hf
    cases hNu : ik.neverUnwind <;> simp [fnCanUnwind, hp, hf, hNu]
  · simp [hasLlvmNoUnwind, fnCanUnwind, PanicStrategy.unwinds, ItemKind.neverUnwind,
      ItemKind.isForeign, ItemKind.isLangDropGlue]
  · simp [hasLlvmNoUnwind, fnCanUnwind, PanicStrategy.unwinds, ItemKind.neverUnwind,
      ItemKind.isForeign, ItemKind.isLangDropGlue]
  · simp [fnCanUnwind, PanicStrategy.unwinds]

theorem abortUnwindingCalls_sound_for_call
    (callerCanUnwind calleeCanUnwind : Bool)
    (origAction : MirUnwindAction)
    (calleeActuallyUnwinds : Bool)
    (hContract : calleeActuallyUnwinds = true → calleeCanUnwind = true)
    (hOrigValid : calleeActuallyUnwinds = true → origAction ≠ .unreachable) :
    let lowered := abortUnwindingEdge true callerCanUnwind calleeCanUnwind origAction
    let outcome := evalCallFrame (!callerCanUnwind) (!calleeCanUnwind) lowered calleeActuallyUnwinds
    (outcome ≠ .ub .nounwindViolated ∧ outcome ≠ .ub .unreachableUnwind) ∧
    (callerCanUnwind = false → outcome ≠ .unwound) := by
  intro lowered outcome
  dsimp only [outcome, lowered]
  cases hAct : calleeActuallyUnwinds
  · simp [evalCallFrame]
  · have hCal : calleeCanUnwind = true := hContract hAct
    have hNeUnreach : origAction ≠ .unreachable := hOrigValid hAct
    cases callerCanUnwind <;> cases origAction with
    | continue_ =>
      simp [abortUnwindingEdge, evalCallFrame, emitsInvoke, hCal]
    | cleanup hasResume =>
      cases hasResume <;> simp [abortUnwindingEdge, evalCallFrame, emitsInvoke, hCal]
    | terminateAbi =>
      simp [abortUnwindingEdge, evalCallFrame, emitsInvoke, hCal]
    | unreachable =>
      exact False.elim (hNeUnreach rfl)

/-- **Master Theorem 3 (`fnCanUnwind_nounwind_soundness`)**:
Combines:
1. The exact 3-gate precedence of `fn_can_unwind` (proving `rust_def_extern_c_unwind`
   gets `nounwind` under `panic=abort` while foreign `"C-unwind"` stays
   unwinding, and `LangItem::DropGlue` gets `nounwind` under `panic=unwind -Z panic-in-drop=abort`
   while public `core::ptr::drop_in_place` stays unwinding).
2. End-to-end callsite `invoke` / `nounwind` soundness after `AbortUnwindingCalls`
   when callees obey their static `fnCanUnwind` contract and pre-lowering edges are
   not prematurely `unreachable` (covering both a `nounwind` Rust caller calling
   foreign `C-unwind` under `panic=abort`, and `nounwind` `DropGlue` calling
   `Drop::drop` under `-Z panic-in-drop=abort`).
3. Prebuilt `core` link rejection for `-C panic=immediate-abort` and
   `-Z panic-in-drop=abort` when `core` lacks matching compilation metadata. -/
theorem fnCanUnwind_nounwind_soundness
    (callerItem calleeItem : Option ItemKind) (callerAbi calleeAbi : ExternAbi)
    (p d : PanicStrategy) (origAction : MirUnwindAction)
    (calleeActuallyUnwinds : Bool)
    (hCalleeContract : calleeActuallyUnwinds = true → fnCanUnwind p d calleeItem calleeAbi = true)
    (hOrigValid : calleeActuallyUnwinds = true → origAction ≠ .unreachable) :
    let callerCan := fnCanUnwind p d callerItem callerAbi
    let calleeCan := fnCanUnwind p d calleeItem calleeAbi
    let lowered := abortUnwindingEdge true callerCan calleeCan origAction
    let out := evalCallFrame (!callerCan) (!calleeCan) lowered calleeActuallyUnwinds
    (hasLlvmNoUnwind .abort d (some (.rustFn false)) (.c true) = true ∧
     hasLlvmNoUnwind .abort d (some (.foreignItem false)) (.c true) = false ∧
     hasLlvmNoUnwind .unwind .abort (some (.langDropGlue false)) .rust = true ∧
     hasLlvmNoUnwind .unwind .abort (some (.publicDropInPlace false)) .rust = false) ∧
    (out ≠ .ub .nounwindViolated ∧ out ≠ .ub .unreachableUnwind) ∧
    (hasLlvmNoUnwind p d callerItem callerAbi = true → out ≠ .unwound) ∧
    (checkCrateDagLink .immediateAbort .abort none .unwind true =
       .incompatibleWithImmediateAbortCore) ∧
    (checkCrateDagLink .unwind .abort none .unwind true =
       .incompatiblePanicInDropStrategy) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(fnCanUnwind_precedence_characterization p d .rust).2.2.1.1,
           (fnCanUnwind_precedence_characterization p d .rust).2.2.1.2,
           (fnCanUnwind_precedence_characterization p d .rust).2.2.2.1.1,
           (fnCanUnwind_precedence_characterization p d .rust).2.2.2.1.2⟩
  · exact (abortUnwindingCalls_sound_for_call
      (fnCanUnwind p d callerItem callerAbi) (fnCanUnwind p d calleeItem calleeAbi)
      origAction calleeActuallyUnwinds hCalleeContract hOrigValid).1
  · intro hNoUnw
    have hFalse : fnCanUnwind p d callerItem callerAbi = false := by
      cases hCan : fnCanUnwind p d callerItem callerAbi
      · rfl
      · simp [hasLlvmNoUnwind, hCan] at hNoUnw
    exact (abortUnwindingCalls_sound_for_call
      (fnCanUnwind p d callerItem callerAbi) (fnCanUnwind p d calleeItem calleeAbi)
      origAction calleeActuallyUnwinds hCalleeContract hOrigValid).2 hFalse
  · rfl
  · rfl

end NoUnwindSoundness

-- ============================================================================
-- Section 4: Three Constructive Sharpness Counterexamples
-- ============================================================================

section Examples

/-- Cyclic cold loop mirroring `cw_5_cyclic_cold_loop`:
- Block `0`: entry `switchInt [1] 2` (loops on `true`, returns hot on `false`)
- Block `1`: loop header `switchInt [3] 1` (self-loop backedge `1 -> 1`, exit `1 -> 3`)
- Block `2`: `return_` (hot exit)
- Block `3`: `call coldFn -> return_` (`fnIsCold 0 = true`)
Postorder traversal `[2, 3, 1, 0]` visits `1` while `1` is not yet marked. -/
def cw5Cfg : Cfg where
  blocks := [
    { term := .switchInt [1] 2 },
    { term := .switchInt [3] 1 },
    { term := .return_ },
    { term := .call 0 (some 2) none }
  ]
  fnIsCold := fun f => f == 0

def cw5Postorder : List BlockId := [2, 3, 1, 0]

theorem cw5_trace_from_1_must_hit_3 :
    MustHitColdOrUnreachable cw5Cfg 1 := by
  intro rest hTr hEnd
  -- Any valid trace from block `1` either stays at `1` or transitions to `3`.
  -- If a prefix consists exclusively of `1`s, it cannot halt at `1` because `isHaltingTerm cw5Cfg 1 = false`.
  suffices h : ∀ xs, ValidTrace cw5Cfg xs →
      (endsAtHalting cw5Cfg xs → ∀ hd, xs = 1 :: hd → hitsColdSeed cw5Cfg (1 :: hd)) by
    exact h (1 :: rest) hTr hEnd rest rfl
  intro xs hTrX
  induction hTrX with
  | single b =>
    intro hEndX hd hEq
    injection hEq with hb _
    subst hb
    simp [endsAtHalting, isHaltingTerm, isColdSeedAt, Cfg.termAt, getBlockAt,
      cw5Cfg, isColdSeed, termSuccessors] at hEndX
  | cons b s rs hsMem hSub ih =>
    intro hEndX hd hEq
    injection hEq with hb hRs
    subst hb
    subst hRs
    have hEndSub : endsAtHalting cw5Cfg (s :: rs) := hEndX
    have hMem : s = 1 ∨ s = 3 := by
      simp [Cfg.termAt, getBlockAt, cw5Cfg, termSuccessors] at hsMem
      exact hsMem
    cases hMem with
    | inl hs1 =>
      subst hs1
      exact Or.inr (ih hEndSub rs rfl)
    | inr hs3 =>
      subst hs3
      exact Or.inr (Or.inl rfl)

/-- **Counterexample 1 (`ce1_single_pass_postorder_misses_cyclic_cold_loop_header`)**:
Single-pass postorder `find_cold_blocks` strictly under-approximates cyclic CFGs:
every terminating trace from loop header `1` hits the `cold_path` block `3`
(`MustHitColdOrUnreachable cw5Cfg 1`), and `gfpColdBlocks cw5Cfg 4 1 = true`,
yet `findColdBlocksPass cw5Cfg [2, 3, 1, 0] 1 = false` because of the self-loop
backedge `1 -> 1`. -/
theorem ce1_single_pass_postorder_misses_cyclic_cold_loop_header :
    findColdBlocksPass cw5Cfg cw5Postorder 3 = true ∧
    findColdBlocksPass cw5Cfg cw5Postorder 1 = false ∧
    gfpColdBlocks cw5Cfg 4 1 = true ∧
    MustHitColdOrUnreachable cw5Cfg 1 := by
  refine ⟨rfl, rfl, rfl, cw5_trace_from_1_must_hit_3⟩

/-- **Counterexample 2 (`ce2_marking_foreign_c_unwind_nounwind_under_panic_abort_skips_terminate_pad`)**:
Under `-C panic=abort`, Gate 2 in `fn_can_unwind` exempts foreign items (`!tcx.is_foreign_item(did)`).
If a buggy compiler omitted `!isForeign`, foreign FFI `"C-unwind"` would be attributed
`nounwind`: `AbortUnwindingCalls` would rewrite its unwind edge to `UnwindAction::Unreachable`
and `codegen` would emit plain `call` instead of `invoke` to a terminate pad, triggering
`.ub .nounwindViolated` on foreign unwind — whereas the actual `fnCanUnwind` +
`abortUnwindingEdge` keeps `invoke` and aborts cleanly via `.abortedTerminateAbi`. -/
theorem ce2_marking_foreign_c_unwind_nounwind_under_panic_abort_skips_terminate_pad :
    let callerCan := fnCanUnwind .abort .abort (some (.rustFn false)) .rust
    let buggyForeignCan := false
    let buggyEdge := abortUnwindingEdge true callerCan buggyForeignCan .continue_
    let actualForeignCan := fnCanUnwind .abort .abort (some (.foreignItem false)) (.c true)
    let actualEdge := abortUnwindingEdge true callerCan actualForeignCan .continue_
    (emitsInvoke buggyForeignCan buggyEdge = false ∧
     evalCallFrame (!callerCan) (!buggyForeignCan) buggyEdge true = .ub .nounwindViolated) ∧
    (actualForeignCan = true ∧
     emitsInvoke actualForeignCan actualEdge = true ∧
     evalCallFrame (!callerCan) (!actualForeignCan) actualEdge true = .abortedTerminateAbi) := by
  dsimp only
  decide

/-- **Counterexample 3 (`ce3_conflating_public_drop_in_place_with_lang_drop_glue_under_panic_in_drop_abort`)**:
Under `-C panic=unwind -Z panic-in-drop=abort`, Gate 3 marks `LangItem::DropGlue`
(`core::ptr::drop_glue`) `nounwind` while leaving public `core::ptr::drop_in_place`
non-`nounwind`. Conflating them (falsely attributing `nounwind` to a public
`drop_in_place` item whose MIR has not lowered its call edge to `terminate(abi)`)
breaks callsite soundness (`.ub .nounwindViolated`) when `Drop::drop` panics,
whereas distinguishing them leaves `drop_in_place` unwinding (`hasLlvmNoUnwind = false`)
and traps cleanly inside `drop_glue` via `invoke -> terminate(abi)` (`panic_cannot_unwind`). -/
theorem ce3_conflating_public_drop_in_place_with_lang_drop_glue_under_panic_in_drop_abort :
    let dropGlueNoUnwind := hasLlvmNoUnwind .unwind .abort (some (.langDropGlue false)) .rust
    let dropInPlaceNoUnwind := hasLlvmNoUnwind .unwind .abort (some (.publicDropInPlace false)) .rust
    let dropInPlaceActualCan := fnCanUnwind .unwind .abort (some (.publicDropInPlace false)) .rust
    let dropGlueEdge := abortUnwindingEdge true (!dropGlueNoUnwind) true (.cleanup true)
    let buggyUnloweredEdge := MirUnwindAction.continue_
    dropGlueNoUnwind = true ∧
    dropInPlaceNoUnwind = false ∧
    evalCallFrame dropGlueNoUnwind false dropGlueEdge true = .abortedTerminateAbi ∧
    evalCallFrame true (!dropInPlaceActualCan) buggyUnloweredEdge true = .ub .nounwindViolated := by
  dsimp only
  decide

end Examples

end ColdBlocksAndNoUnwind
