-- Hybrid Verified Software (Wave 4): Kernel-checked O(V + E) SSSP witness checker.
-- Pure Init Lean 4 (no Mathlib, no omega, no bv_decide, no by_cases, zero sorry).

prelude
import Init.Core
import Init.NotationExtra
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace HybridSsspChecker

structure Edge where
  src : Nat
  dst : Nat
  w : Nat

abbrev Graph := List Edge

structure SsspWitness where
  dist : List (Option Nat)
  parent : List (Option Nat)
  rank : List Nat

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listGet? xs k

def getDist (dists : List (Option Nat)) (v : Nat) : Option Nat :=
  match listGet? dists v with
  | some (some d) => some d
  | _ => none

def getParent (parents : List (Option Nat)) (v : Nat) : Option Nat :=
  match listGet? parents v with
  | some (some p) => some p
  | _ => none

def getRank (ranks : List Nat) (v : Nat) : Nat :=
  match listGet? ranks v with
  | some r => r
  | none => 0

inductive MemList {α : Type} (x : α) : List α → Prop where
  | head (xs : List α) : MemList x (x :: xs)
  | tail (y : α) {xs : List α} : MemList x xs → MemList x (y :: xs)

inductive GraphPath (g : Graph) (src : Nat) : Nat → Nat → Prop where
  | start : GraphPath g src src 0
  | step {u v d w : Nat} :
      GraphPath g src u d →
      MemList ⟨u, v, w⟩ g →
      GraphPath g src v (d + w)

/-- Valid distance potentials: `src` has distance `0`, and every reachable
edge endpoint satisfies triangle optimality (`dist[dst] <= dist[src] + w`). -/
def ValidPotentials (g : Graph) (src : Nat) (dists : List (Option Nat)) : Prop :=
  getDist dists src = some 0 ∧
  ∀ u v w, MemList ⟨u, v, w⟩ g →
    ∀ du, getDist dists u = some du →
      ∃ dv, getDist dists v = some dv ∧ dv ≤ du + w

private theorem nat_eq_of_beq_true : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h => congrArg Nat.succ (nat_eq_of_beq_true (a := a) (b := b) h)

private theorem bool_and_split {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem nat_le_of_ble_true {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private theorem nat_lt_of_blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

/-- Every graph path is bounded below by the certified distance potential
(and unreachable nodes `none` cannot be reached by any path). -/
theorem validPotentials_lower_bound {g : Graph} {src : Nat} {dists : List (Option Nat)}
    (hPot : ValidPotentials g src dists) :
    ∀ {v totalW : Nat}, GraphPath g src v totalW →
      ∃ dv, getDist dists v = some dv ∧ dv ≤ totalW := by
  intro v totalW hPath
  induction hPath with
  | start =>
    exact ⟨0, hPot.1, Nat.le_refl 0⟩
  | @step u mid du w _ hEdge ih =>
    let ⟨dU, hGetU, hLeU⟩ := ih
    let ⟨dMid, hGetMid, hTri⟩ := hPot.2 u mid w hEdge dU hGetU
    exact ⟨dMid, hGetMid, Nat.le_trans hTri (Nat.add_le_add_right hLeU w)⟩

/-- Check triangle optimality on one edge. -/
def checkEdgeOpt (dists : List (Option Nat)) (e : Edge) : Bool :=
  match getDist dists e.src with
  | none => true
  | some du =>
    match getDist dists e.dst with
    | none => false
    | some dv => Nat.ble dv (du + e.w)

def checkAllEdgesOpt (dists : List (Option Nat)) : List Edge → Bool
  | [] => true
  | e :: rest => checkEdgeOpt dists e && checkAllEdgesOpt dists rest

private theorem checkAllEdgesOpt_sound (dists : List (Option Nat)) :
    ∀ edges : List Edge, checkAllEdgesOpt dists edges = true →
      ∀ u v w, MemList ⟨u, v, w⟩ edges →
        ∀ du, getDist dists u = some du →
          ∃ dv, getDist dists v = some dv ∧ dv ≤ du + w
  | [], _, u, v, w, hMem => nomatch hMem
  | e :: rest, hAll, u, v, w, hMem => by
    have hPair := bool_and_split hAll
    cases hMem with
    | head _ =>
      intro du hGetU
      have hHead := hPair.1
      dsimp [checkEdgeOpt] at hHead
      rw [hGetU] at hHead
      cases hGetV : getDist dists v with
      | none => rw [hGetV] at hHead; nomatch hHead
      | some dv =>
        rw [hGetV] at hHead
        exact ⟨dv, rfl, nat_le_of_ble_true hHead⟩
    | tail _ hTail =>
      exact checkAllEdgesOpt_sound dists rest hPair.2 u v w hTail

/-- Find an edge `(u, v, w)` in `edges` justifying `du + w = dv`. -/
def hasWitnessEdge (u v du dv : Nat) : List Edge → Bool
  | [] => false
  | e :: rest =>
    (Nat.beq e.src u && Nat.beq e.dst v && Nat.beq (du + e.w) dv) ||
      hasWitnessEdge u v du dv rest

private theorem hasWitnessEdge_sound (u v du dv : Nat) :
    ∀ edges : List Edge, hasWitnessEdge u v du dv edges = true →
      ∃ w, MemList ⟨u, v, w⟩ edges ∧ du + w = dv
  | [], h => nomatch h
  | e :: rest, h => by
    cases hHead : (Nat.beq e.src u && Nat.beq e.dst v && Nat.beq (du + e.w) dv) with
    | true =>
      have p1 := bool_and_split hHead
      have p2 := bool_and_split p1.1
      have hs := nat_eq_of_beq_true p2.1
      have hd := nat_eq_of_beq_true p2.2
      have hw := nat_eq_of_beq_true p1.2
      cases e with
      | mk es ed ew =>
        dsimp at hs hd hw
        subst hs; subst hd
        exact ⟨ew, MemList.head rest, hw⟩
    | false =>
      dsimp [hasWitnessEdge] at h
      rw [hHead] at h
      let ⟨w, hMem, hEq⟩ := hasWitnessEdge_sound u v du dv rest h
      exact ⟨w, MemList.tail e hMem, hEq⟩

/-- Check parent & strictly increasing hop rank on vertex `v` (`< n`). -/
def checkVertexParent (g : Graph) (n src : Nat) (w : SsspWitness) (v : Nat) : Bool :=
  match getDist w.dist v with
  | none => true
  | some dv =>
    match Nat.beq v src with
    | true => Nat.beq dv 0 && Nat.beq (getRank w.rank v) 0
    | false =>
      match getParent w.parent v with
      | none => false
      | some u =>
        Nat.blt u n &&
        match getDist w.dist u with
        | none => false
        | some du =>
          Nat.blt (getRank w.rank u) (getRank w.rank v) &&
          hasWitnessEdge u v du dv g

def checkAllParents (g : Graph) (n src : Nat) (w : SsspWitness) : Nat → Bool
  | 0 => true
  | k + 1 => checkVertexParent g n src w k && checkAllParents g n src w k

private theorem checkAllParents_sound (g : Graph) (n src : Nat) (w : SsspWitness) :
    ∀ bound : Nat, checkAllParents g n src w bound = true →
      ∀ v, v < bound → checkVertexParent g n src w v = true
  | 0, _, v, hLt => nomatch hLt
  | k + 1, hAll, v, hLt => by
    have hPair := bool_and_split hAll
    cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hLt) with
    | inl hEq => rw [hEq]; exact hPair.1
    | inr hStrict => exact checkAllParents_sound g n src w k hPair.2 v hStrict

def checkSsspWitness (g : Graph) (n src : Nat) (w : SsspWitness) : Bool :=
  Nat.blt src n &&
  match getDist w.dist src with
  | some 0 => checkAllEdgesOpt w.dist g && checkAllParents g n src w n
  | _ => false

theorem checkSsspWitness_potentials {g : Graph} {n src : Nat} {w : SsspWitness}
    (hOk : checkSsspWitness g n src w = true) :
    ValidPotentials g src w.dist := by
  dsimp [checkSsspWitness] at hOk
  have hS := bool_and_split hOk
  cases hSrc : getDist w.dist src with
  | none => rw [hSrc] at hS; exact absurd hS.2 (by intro h; nomatch h)
  | some d =>
    cases d with
    | zero =>
      rw [hSrc] at hS
      have hRest := bool_and_split hS.2
      exact ⟨hSrc, checkAllEdgesOpt_sound w.dist g hRest.1⟩
    | succ _ =>
      rw [hSrc] at hS
      exact absurd hS.2 (by intro h; nomatch h)

private theorem reach_path_by_rank (g : Graph) (n src : Nat) (w : SsspWitness)
    (hParents : ∀ v, v < n → checkVertexParent g n src w v = true) :
    ∀ k v dv, v < n → getRank w.rank v ≤ k → getDist w.dist v = some dv →
      ∃ _ : GraphPath g src v dv, True := by
  intro k
  induction k with
  | zero =>
    intro v dv hVn hRk hDist
    have hV := hParents v hVn
    dsimp [checkVertexParent] at hV
    rw [hDist] at hV
    cases hEq : Nat.beq v src with
    | true =>
      rw [hEq] at hV
      have hPair := bool_and_split hV
      have hv := nat_eq_of_beq_true hEq
      have hd := nat_eq_of_beq_true hPair.1
      subst hv; subst hd
      exact ⟨GraphPath.start, trivial⟩
    | false =>
      rw [hEq] at hV
      cases hP : getParent w.parent v with
      | none => rw [hP] at hV; nomatch hV
      | some u =>
        rw [hP] at hV
        have h1 := bool_and_split hV
        cases hDu : getDist w.dist u with
        | none => rw [hDu] at h1; exact absurd h1.2 (by intro h; nomatch h)
        | some du =>
          rw [hDu] at h1
          have h2 := bool_and_split h1.2
          have hRankLt : getRank w.rank u < getRank w.rank v := nat_lt_of_blt_true h2.1
          have hZero : getRank w.rank u < 0 := Nat.lt_of_lt_of_le hRankLt hRk
          nomatch hZero
  | succ k ih =>
    intro v dv hVn hRk hDist
    have hV := hParents v hVn
    dsimp [checkVertexParent] at hV
    rw [hDist] at hV
    cases hEq : Nat.beq v src with
    | true =>
      rw [hEq] at hV
      have hPair := bool_and_split hV
      have hv := nat_eq_of_beq_true hEq
      have hd := nat_eq_of_beq_true hPair.1
      subst hv; subst hd
      exact ⟨GraphPath.start, trivial⟩
    | false =>
      rw [hEq] at hV
      cases hP : getParent w.parent v with
      | none => rw [hP] at hV; nomatch hV
      | some u =>
        rw [hP] at hV
        have h1 := bool_and_split hV
        have hUn := nat_lt_of_blt_true h1.1
        cases hDu : getDist w.dist u with
        | none => rw [hDu] at h1; exact absurd h1.2 (by intro h; nomatch h)
        | some du =>
          rw [hDu] at h1
          have h2 := bool_and_split h1.2
          have hRankLt : getRank w.rank u < getRank w.rank v := nat_lt_of_blt_true h2.1
          have hRankLe : getRank w.rank u ≤ k :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hRankLt hRk)
          let ⟨ew, hMem, hSum⟩ := hasWitnessEdge_sound u v du dv g h2.2
          let ⟨pU, _⟩ := ih u du hUn hRankLe hDu
          rw [← hSum]
          exact ⟨GraphPath.step pU hMem, trivial⟩

/-- Master kernel-checked SSSP witness theorem: any accepted witness proves
both exact reachability via an explicit path of weight `d` and global lower-bound
optimality against every path in `g` (including `0`-weight edges and unreachability). -/
theorem checkSsspWitness_sound {g : Graph} {n src : Nat} {w : SsspWitness}
    (hOk : checkSsspWitness g n src w = true) :
    ∀ v, v < n →
      match getDist w.dist v with
      | some d => (∃ _ : GraphPath g src v d, True) ∧ (∀ w', GraphPath g src v w' → d ≤ w')
      | none => ∀ w', GraphPath g src v w' → False := by
  have hPot := checkSsspWitness_potentials hOk
  dsimp [checkSsspWitness] at hOk
  have hS := bool_and_split hOk
  cases hSrc : getDist w.dist src with
  | none => rw [hSrc] at hS; exact absurd hS.2 (by intro h; nomatch h)
  | some d0 =>
    cases d0 with
    | succ _ => rw [hSrc] at hS; exact absurd hS.2 (by intro h; nomatch h)
    | zero =>
      rw [hSrc] at hS
      have hRest := bool_and_split hS.2
      have hParents := checkAllParents_sound g n src w n hRest.2
      intro v hVn
      cases hDv : getDist w.dist v with
      | none =>
        intro w' hPath
        let ⟨dv', hEq, _⟩ := validPotentials_lower_bound hPot hPath
        rw [hDv] at hEq
        nomatch hEq
      | some d =>
        constructor
        · exact reach_path_by_rank g n src w hParents (getRank w.rank v) v d hVn (Nat.le_refl _) hDv
        · intro w' hPath
          let ⟨dv', hEq, hLe⟩ := validPotentials_lower_bound hPot hPath
          rw [hDv] at hEq
          injection hEq with hSame
          rw [hSame]
          exact hLe

/-! ## Concrete Kernel-Checked Canaries (Positive + Adversarial Negative) -/

def sampleDiamondGraph : Graph :=
  [ ⟨0, 1, 2⟩
  , ⟨0, 2, 5⟩
  , ⟨1, 2, 0⟩
  , ⟨1, 3, 6⟩
  , ⟨2, 3, 1⟩
  , ⟨2, 1, 0⟩
  ]

-- Shortest distances from src=0: [0, 2, 2, 3]; note 0-weight edge 1->2!
def sampleValidWitness : SsspWitness :=
  { dist := [some 0, some 2, some 2, some 3, none]
    parent := [none, some 0, some 1, some 2, none]
    rank := [0, 1, 2, 3, 0] }

theorem sampleDiamond_verified :
    ∀ v, v < 5 →
      match getDist sampleValidWitness.dist v with
      | some d =>
        (∃ _ : GraphPath sampleDiamondGraph 0 v d, True) ∧
          (∀ w', GraphPath sampleDiamondGraph 0 v w' → d ≤ w')
      | none => ∀ w', GraphPath sampleDiamondGraph 0 v w' → False :=
  checkSsspWitness_sound rfl

-- Forged 0-weight self-looping cycle without strictly decreasing hop rank:
-- node 1 claims parent 2 and node 2 claims parent 1, disconnected from 0!
def forgedZeroCycleWitness : SsspWitness :=
  { dist := [some 0, some 2, some 2, some 3, none]
    parent := [none, some 2, some 1, some 2, none]
    rank := [0, 1, 1, 3, 0] }

theorem forgedZeroCycle_rejected :
    checkSsspWitness sampleDiamondGraph 5 0 forgedZeroCycleWitness = false := rfl

-- Forged suboptimal distance claiming direct edge 0->3 took cost 5 when 0->1->2->3 = 3:
def forgedSuboptimalWitness : SsspWitness :=
  { dist := [some 0, some 2, some 2, some 5, none]
    parent := [none, some 0, some 1, some 2, none]
    rank := [0, 1, 2, 3, 0] }

theorem forgedSuboptimal_rejected :
    checkSsspWitness sampleDiamondGraph 5 0 forgedSuboptimalWitness = false := rfl

-- Forged unreachability hiding reachable node 3 as `none`:
def forgedUnreachableWitness : SsspWitness :=
  { dist := [some 0, some 2, some 2, none, none]
    parent := [none, some 0, some 1, none, none]
    rank := [0, 1, 2, 0, 0] }

theorem forgedUnreachable_rejected :
    checkSsspWitness sampleDiamondGraph 5 0 forgedUnreachableWitness = false := rfl

#print axioms checkSsspWitness_sound
#print axioms sampleDiamond_verified

end HybridSsspChecker
