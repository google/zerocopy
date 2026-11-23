/-
  MatchBranchesSingleUseConstsAndCostCheckerSoundness.lean

  Self-contained, purely constructive Lean 4 (v4.34.1) mechanization of four
  rustc MIR components audited against:
    - rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47 (HEAD)
    - rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 (rustc 1.98.0-nightly)
    - joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613 (Trusted.MirSemantics)

  Coverage:
    1. SingleUseConsts (`single_use_consts.rs`):
       - Counterexamples for live DeadLocal UB erasure (`DEAD_LOCAL=77`),
         non-dominating uninitialized-memory UB erasure (`NONDOM=88`), and
         intervening StorageDead/StorageLive reset UB erasure.
       - Repaired bidirectional soundness (`singleUseConsts_repaired_sound_iff`)
         requiring dominance, live-at-init, and no intervening kill/write/move
         (respecting `deinitMovedPlace = true`), plus VarDebugInfo scoping.
    2. MatchBranchSimplification (`match_branches.rs`):
       - All 5 unification arms: `identical_stmts`, `unify_if_equal_const`
         (`WithRetag::No` necessity), `unify_by_eq_op` (`Eq`/`Ne` & unreachable
         `otherwise` UB erasure), `unify_by_int_to_int` (exact signed/unsigned
         `can_cast` bit semantics), and `unify_by_copy` (enum clone & aliasing
         guard added between 14210df0e and 137d1d4945).
       - Live indirect-discriminant `*null_ptr` UB erasure (`MBS_NULL=99`) vs.
         `PlaceMention`-guarded exact preservation.
    3. SimplifyConstCondition (`simplify_branches.rs` + `patch.rs`):
       - Immediate-predecessor `has_place_const` soundness & intervening-stmt
         invalidation.
       - `SwitchInt` and passing-`Assert` exact folding vs. failing-`Assert`
         preservation (proving folding a failing assert to `Unreachable`
         violates UB refinement).
       - `Assume(false)` block-statement wipe (`MirPatch::apply`
         `bb.statements.clear()`): UB-kind shift (`nullDeref` -> `unreachable`)
         and trust-boundary requirement that MIR statements cannot panic/diverge.
    4. CostChecker (`cost_checker.rs` + `inline.rs`):
       - Exact saturating penalty/bonus algebra (`penalty - bonus` in `Nat`),
         monotonicity, single-call `+25` bonus cancellation, two-call `+50` cliff,
         call-site non-amplification (`(c - 1) + k <= c <-> k <= 1`), intrinsic
         `INSTR_COST=5` exemption, `RuntimeChecks::UbChecks` `+25` bonus,
         optional overflow-check `+20` delta, `assignZstConst` zero-cost update,
         and exact calibration against all live `rustc` probe thresholds.

  Strict purity invariants (verified programmatically across `env.constants`):
    - 0 `sorry` / `sorryAx`
    - 0 `Classical.choice`
    - 0 `omega`, 0 `bv_decide`, 0 `native_decide` / `Lean.ofReduceBool`
    - 0 `partial def`
    - 0 `._unsafe_rec` auxiliary constants (all list/fuel iterations expressed
      via non-recursive `List.foldr` / `List.replicate` combinators; no
      `deriving DecidableEq` or `deriving Repr` on inductives)
-/

namespace RustcMirBranchConstCost

/-! ============================================================================
    PART 0: Constructive Nat Equality & Arithmetic Lemmas (0 Axioms)
    ============================================================================ -/

section NatHelpers

theorem nat_beq_refl (x : Nat) : Nat.beq x x = true := by
  induction x with
  | zero => rfl
  | succ n ih => exact ih

theorem nat_eq_of_beq {x y : Nat} (h : Nat.beq x y = true) : x = y := by
  induction x generalizing y with
  | zero =>
    cases y with
    | zero => rfl
    | succ m => cases h
  | succ n ih =>
    cases y with
    | zero => cases h
    | succ m =>
      have hnm : n = m := ih h
      rw [hnm]

theorem nat_beq_false_of_ne {x y : Nat} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y with
  | false => rfl
  | true => exact False.elim (h (nat_eq_of_beq hb))

theorem nat_add_sub_add_right (a b c : Nat) : (a + c) - (b + c) = a - b :=
  Nat.add_sub_add_right a c b

theorem nat_sub_mono_left {a₁ a₂ b : Nat} (h : a₁ ≤ a₂) : a₁ - b ≤ a₂ - b :=
  Nat.sub_le_sub_right h b

theorem nat_sub_mono_right {a b₁ b₂ : Nat} (h : b₁ ≤ b₂) : a - b₂ ≤ a - b₁ :=
  Nat.sub_le_sub_left h a

theorem nat_sub_add_eq_add_sub {a b c : Nat} (h : b ≤ a) : (a + c) - b = (a - b) + c := by
  rw [Nat.add_comm a c, Nat.add_sub_assoc h c, Nat.add_comm]

theorem nat_sub_eq_zero_of_le {a b : Nat} (h : a ≤ b) : a - b = 0 :=
  Nat.sub_eq_zero_of_le h

theorem nat_pred_add_le_iff (c k : Nat) (hc : 1 ≤ c) :
    (c - 1) + k ≤ c ↔ k ≤ 1 := by
  constructor
  · intro h
    have h1 : (c - 1) + k ≤ (c - 1) + 1 := by
      rw [Nat.sub_add_cancel hc]
      exact h
    exact Nat.le_of_add_le_add_left h1
  · intro hk
    have h1 : (c - 1) + k ≤ (c - 1) + 1 := Nat.add_le_add_left hk (c - 1)
    rw [Nat.sub_add_cancel hc] at h1
    exact h1

theorem nat_pred_add_gt_of_ge_two (c k : Nat) (hc : 1 ≤ c) (hk : 2 ≤ k) :
    c < (c - 1) + k := by
  have h1 : (c - 1) + 2 ≤ (c - 1) + k := Nat.add_le_add_left hk (c - 1)
  have h2 : c + 1 = (c - 1) + 2 := by
    change c + 1 = (c - 1) + (1 + 1)
    rw [← Nat.add_assoc, Nat.sub_add_cancel hc]
  rw [← h2] at h1
  exact h1

end NatHelpers

/-! ============================================================================
    PART 1: Core MIR Operational Model & Refinement / UB-Preservation Relations
    ============================================================================ -/

section CoreModel

/-- Concrete MIR undefined-behavior categories tracked by Miri and Anneal. -/
inductive UbKind where
  | deadLocal
  | uninitRead
  | nullDeref
  | unreachable
  | assumeFalse
  | overlappingCopy
  | invalidRetag

/-- Structural boolean equality on `UbKind` (explicit, zero `._unsafe_rec`). -/
def UbKind.beq : UbKind → UbKind → Bool
  | .deadLocal, .deadLocal => true
  | .uninitRead, .uninitRead => true
  | .nullDeref, .nullDeref => true
  | .unreachable, .unreachable => true
  | .assumeFalse, .assumeFalse => true
  | .overlappingCopy, .overlappingCopy => true
  | .invalidRetag, .invalidRetag => true
  | _, _ => false

/-- Observable execution outcome of a MIR body or basic block. -/
inductive Outcome where
  | ok (val : Nat)
  | panic
  | ub (kind : UbKind)
  | diverged

/-- Predicate asserting that an outcome is some form of Undefined Behavior. -/
def Outcome.isUb : Outcome → Prop
  | .ub _ => True
  | _ => False

/-- Standard compiler UB refinement (`opt` refines `orig`):
    - If `orig` returns `.ok v`, `opt` must return `.ok v`.
    - If `orig` panics, `opt` must panic.
    - If `orig` diverges, `opt` must diverge.
    - If `orig` exhibits `.ub _`, `opt` may produce any outcome. -/
def Refines (orig opt : Outcome) : Prop :=
  match orig with
  | .ub _ => True
  | .ok v => opt = .ok v
  | .panic => opt = .panic
  | .diverged => opt = .diverged

/-- Weak UB preservation (`UbEquivalent`): preserves exact defined outcomes
    AND preserves whether UB occurred (allowing UB-kind shifts such as
    `nullDeref` -> `unreachable`). -/
def UbEquivalent (orig opt : Outcome) : Prop :=
  match orig, opt with
  | .ok v₁, .ok v₂ => v₁ = v₂
  | .panic, .panic => True
  | .diverged, .diverged => True
  | .ub _, .ub _ => True
  | _, _ => False

/-- Strict UB-preserving equivalence: identical outcome including exact `UbKind`. -/
def ExactEq (orig opt : Outcome) : Prop := orig = opt

theorem refines_refl (o : Outcome) : Refines o o := by
  cases o with
  | ok _ => rfl
  | panic => rfl
  | ub _ => trivial
  | diverged => rfl

theorem refines_trans {o₁ o₂ o₃ : Outcome}
    (h₁ : Refines o₁ o₂) (h₂ : Refines o₂ o₃) : Refines o₁ o₃ := by
  cases o₁ with
  | ub _ => trivial
  | ok v =>
    change o₂ = .ok v at h₁
    rw [h₁] at h₂
    exact h₂
  | panic =>
    change o₂ = .panic at h₁
    rw [h₁] at h₂
    exact h₂
  | diverged =>
    change o₂ = .diverged at h₁
    rw [h₁] at h₂
    exact h₂

theorem ubEquivalent_refl (o : Outcome) : UbEquivalent o o := by
  cases o with
  | ok _ => rfl
  | panic => trivial
  | ub _ => trivial
  | diverged => trivial

theorem exactEq_implies_ubEquivalent {o₁ o₂ : Outcome} (h : ExactEq o₁ o₂) :
    UbEquivalent o₁ o₂ := by
  rw [h]
  exact ubEquivalent_refl o₂

theorem ubEquivalent_implies_refines {o₁ o₂ : Outcome} (h : UbEquivalent o₁ o₂) :
    Refines o₁ o₂ := by
  cases o₁ with
  | ub _ => trivial
  | ok v₁ =>
    cases o₂ with
    | ok v₂ =>
      change v₁ = v₂ at h
      rw [h]
      rfl
    | panic => exact False.elim h
    | ub _ => exact False.elim h
    | diverged => exact False.elim h
  | panic =>
    cases o₂ with
    | panic => rfl
    | ok _ => exact False.elim h
    | ub _ => exact False.elim h
    | diverged => exact False.elim h
  | diverged =>
    cases o₂ with
    | diverged => rfl
    | ok _ => exact False.elim h
    | panic => exact False.elim h
    | ub _ => exact False.elim h

theorem not_refines_panic_to_ub (k : UbKind) : ¬ Refines .panic (.ub k) :=
  fun h => nomatch h

theorem not_refines_diverged_to_ub (k : UbKind) : ¬ Refines .diverged (.ub k) :=
  fun h => nomatch h

theorem not_ubEquivalent_ub_to_ok (k : UbKind) (v : Nat) :
    ¬ UbEquivalent (.ub k) (.ok v) :=
  fun h => h

/-- Local storage slot matching `joshlf/anneal` `Trusted.MirSemantics.LocalSlot`:
    a local is either dead (`StorageDead`), live-uninitialized (fresh
    `StorageLive` or moved-from with `deinitMovedPlace = true`), or
    live-initialized with a scalar value. -/
inductive LocalSlot where
  | dead
  | liveUninit
  | liveInit (val : Nat)

/-- Total local environment mapping local IDs to their storage slot. -/
abbrev LocalEnv := Nat → LocalSlot

def LocalEnv.update (env : LocalEnv) (x : Nat) (slot : LocalSlot) : LocalEnv :=
  fun y => match Nat.beq y x with | true => slot | false => env y

theorem LocalEnv.update_same (env : LocalEnv) (x : Nat) (slot : LocalSlot) :
    (env.update x slot) x = slot := by
  unfold LocalEnv.update
  rw [nat_beq_refl]

theorem LocalEnv.update_other (env : LocalEnv) {x y : Nat} (slot : LocalSlot)
    (h : Nat.beq y x = false) :
    (env.update x slot) y = env y := by
  unfold LocalEnv.update
  rw [h]

/-- Abstract byte-memory heap for indirect place evaluation (`*ptr`).
    Address `0` is permanently unmapped (null pointer). -/
abbrev Heap := Nat → Option Nat

def nullHeap : Heap := fun _ => none

def singleCellHeap (addr val : Nat) : Heap :=
  fun a =>
    match Nat.beq addr 0 with
    | true => none
    | false =>
      match Nat.beq a addr with
      | true => some val
      | false => none

theorem nullHeap_zero : nullHeap 0 = none := rfl

end CoreModel

/-! ============================================================================
    PART 2: `SingleUseConsts` (`single_use_consts.rs`)
    ============================================================================ -/

section SingleUseConsts

/-- MIR operand for `SingleUseConsts` modeling. -/
inductive SucOperand where
  | constVal (c : Nat)
  | copyLocal (x : Nat)
  | moveLocal (x : Nat)

/-- MIR statements modeled for `SingleUseConsts`. -/
inductive SucStmt where
  | storageLive (x : Nat)
  | storageDead (x : Nat)
  | assign (dest : Nat) (op : SucOperand)
  | nop

/-- MIR terminators for `SingleUseConsts` CFG modeling. -/
inductive SucTerm where
  | goto (target : Nat)
  | switchBool (condLocal : Nat) (ifTrue ifFalse : Nat)
  | ret

/-- Basic block in the `SingleUseConsts` MIR CFG. -/
structure SucBlock where
  stmts : List SucStmt
  term : SucTerm

/-- MIR body with entry block `0`, return place `0`, and `argCount` arguments
    (`1..argCount`). -/
structure SucBody where
  argCount : Nat
  blocks : List SucBlock

/-- Evaluate a `SucOperand` under `deinitMovedPlace = true` semantics
    (matching `joshlf/anneal` `Trusted.MirSemantics.evalOperandToSlot`). -/
def evalSucOperand (env : LocalEnv) : SucOperand → Except UbKind (Nat × LocalEnv)
  | .constVal c => .ok (c, env)
  | .copyLocal x =>
    match env x with
    | .dead => .error .deadLocal
    | .liveUninit => .error .uninitRead
    | .liveInit v => .ok (v, env)
  | .moveLocal x =>
    match env x with
    | .dead => .error .deadLocal
    | .liveUninit => .error .uninitRead
    | .liveInit v => .ok (v, env.update x .liveUninit)

/-- Execute a single `SucStmt`. Writing to a dead local is UB; `StorageLive`
    transitions to `liveUninit`; `StorageDead` transitions to `dead`. -/
def stepSucStmt (env : LocalEnv) : SucStmt → Except UbKind LocalEnv
  | .nop => .ok env
  | .storageLive x => .ok (env.update x .liveUninit)
  | .storageDead x => .ok (env.update x .dead)
  | .assign dest op =>
    match evalSucOperand env op with
    | .error k => .error k
    | .ok (v, env') =>
      match env' dest with
      | .dead => .error .deadLocal
      | .liveUninit => .ok (env'.update dest (.liveInit v))
      | .liveInit _ => .ok (env'.update dest (.liveInit v))

/-- Execute a list of statements sequentially via CPS `List.foldr` (zero `._unsafe_rec`). -/
def execSucStmts (env : LocalEnv) (ss : List SucStmt) : Except UbKind LocalEnv :=
  ss.foldr
    (fun s k e =>
      match stepSucStmt e s with
      | .error err => .error err
      | .ok e' => k e')
    Except.ok
    env

theorem execSucStmts_nil (env : LocalEnv) : execSucStmts env [] = .ok env := rfl

theorem execSucStmts_cons (env : LocalEnv) (s : SucStmt) (ss : List SucStmt) :
    execSucStmts env (s :: ss) =
      match stepSucStmt env s with
      | .error k => .error k
      | .ok env' => execSucStmts env' ss := rfl

/-- Fuel-bounded CFG execution of a `SucBody` via `List.replicate` + `List.foldr`
    (zero `._unsafe_rec`, fully computable). -/
def execSucBody (body : SucBody) (fuel bb : Nat) (env : LocalEnv) : Outcome :=
  (List.replicate fuel ()).foldr
    (fun _ k curBb curEnv =>
      match body.blocks[curBb]? with
      | none => .ub .unreachable
      | some blk =>
        match execSucStmts curEnv blk.stmts with
        | .error err => .ub err
        | .ok env' =>
          match blk.term with
          | .goto t => k t env'
          | .switchBool cLocal tTrue tFalse =>
            match env' cLocal with
            | .dead => .ub .deadLocal
            | .liveUninit => .ub .uninitRead
            | .liveInit v =>
              match Nat.beq v 0 with
              | true => k tFalse env'
              | false => k tTrue env'
          | .ret =>
            match env' 0 with
            | .dead => .ub .deadLocal
            | .liveUninit => .ub .uninitRead
            | .liveInit v => .ok v)
    (fun _ _ => .diverged)
    bb env

/-- Syntactic visitor state replicating `SingleUseConstsFinder`
    (`single_use_consts.rs:93-166`). `StorageLive` and `StorageDead` are
    explicitly ignored (`line 146`), and no CFG dominance is tracked. -/
structure SucFinderState where
  initCount : Nat
  useCount : Nat
  otherMention : Bool
  initConst : Option Nat

def SucFinderState.empty : SucFinderState :=
  { initCount := 0, useCount := 0, otherMention := false, initConst := none }

def visitSucStmtFor (target : Nat) (st : SucFinderState) : SucStmt → SucFinderState
  | .storageLive _ => st   -- single_use_consts.rs:146: ignored!
  | .storageDead _ => st   -- single_use_consts.rs:146: ignored!
  | .nop => st
  | .assign dest (.constVal c) =>
    match Nat.beq dest target with
    | true => { st with initCount := st.initCount + 1, initConst := some c }
    | false => st
  | .assign dest (.copyLocal src) =>
    let st1 := match Nat.beq dest target with
      | true => { st with otherMention := true }
      | false => st
    match Nat.beq src target with
    | true => { st1 with useCount := st1.useCount + 1 }
    | false => st1
  | .assign dest (.moveLocal src) =>
    let st1 := match Nat.beq dest target with
      | true => { st with otherMention := true }
      | false => st
    match Nat.beq src target with
    | true => { st1 with useCount := st1.useCount + 1 }
    | false => st1

def visitSucTermFor (target : Nat) (st : SucFinderState) : SucTerm → SucFinderState
  | .goto _ => st
  | .ret => st
  | .switchBool cLocal _ _ =>
    match Nat.beq cLocal target with
    | true => { st with useCount := st.useCount + 1 }
    | false => st

def visitSucStmtsFor (target : Nat) (st : SucFinderState) (ss : List SucStmt) : SucFinderState :=
  ss.foldl (visitSucStmtFor target) st

def visitSucBlocksFor (target : Nat) (st : SucFinderState) (bs : List SucBlock) : SucFinderState :=
  bs.foldl (fun acc b => visitSucTermFor target (visitSucStmtsFor target acc b.stmts) b.term) st

/-- `SingleUseConsts` syntactic eligibility predicate (`single_use_consts.rs:39-50, 111-166`):
    not return place (`0`) or argument (`1..argCount`), initialized by a constant
    exactly once, used at most once, and no non-const-assign write. -/
def isSyntacticSingleUseConst (body : SucBody) (target : Nat) : Option Nat :=
  match Nat.ble target body.argCount with
  | true => none
  | false =>
    let st := visitSucBlocksFor target SucFinderState.empty body.blocks
    match Nat.beq st.initCount 1, Nat.ble st.useCount 1, st.otherMention with
    | true, true, false => st.initConst
    | _, _, _ => none

/-- Rewrite a single statement for `SingleUseConsts`: replace `target = const c`
    with `nop` and replace any `copy/move target` operand with `const c`. -/
def rewriteSucStmt (target c : Nat) : SucStmt → SucStmt
  | .assign dest (.constVal c') =>
    match Nat.beq dest target with
    | true => .nop
    | false => .assign dest (.constVal c')
  | .assign dest (.copyLocal src) =>
    match Nat.beq src target with
    | true => .assign dest (.constVal c)
    | false => .assign dest (.copyLocal src)
  | .assign dest (.moveLocal src) =>
    match Nat.beq src target with
    | true => .assign dest (.constVal c)
    | false => .assign dest (.moveLocal src)
  | s => s

def rewriteSucBlock (target c : Nat) (blk : SucBlock) : SucBlock :=
  { blk with stmts := blk.stmts.map (rewriteSucStmt target c) }

/-- Apply `SingleUseConsts` to `target` if syntactically eligible. -/
def applySingleUseConsts (body : SucBody) (target : Nat) : SucBody :=
  match isSyntacticSingleUseConst body target with
  | none => body
  | some c => { body with blocks := body.blocks.map (rewriteSucBlock target c) }

/-- Initial local environments: `_0` is `liveUninit`, optional argument `_1` is
    `liveInit arg1`, all other locals start `.dead`. -/
def initEnv0 : LocalEnv :=
  fun x => match Nat.beq x 0 with | true => .liveUninit | false => .dead

def initEnv1 (arg1 : Nat) : LocalEnv :=
  fun x =>
    match Nat.beq x 0 with
    | true => .liveUninit
    | false =>
      match Nat.beq x 1 with
      | true => .liveInit arg1
      | false => .dead

/-! ### Counterexample 1: Live `DeadLocal` UB Erasure (`DEAD_LOCAL = 77`)
    Mirrors both `joshlf/anneal` `Trusted.MirSemantics.progStorageDeadReadUb`
    and live Miri probe `dead_local_const`. -/

def progDeadLocal : SucBody :=
  { argCount := 0
    blocks := [
      { stmts := [
          .storageLive 1,
          .assign 1 (.constVal 77),
          .storageDead 1,
          .assign 0 (.copyLocal 1)
        ]
        term := .ret }
    ] }

theorem progDeadLocal_syntactically_eligible :
    isSyntacticSingleUseConst progDeadLocal 1 = some 77 := rfl

theorem progDeadLocal_orig_ub :
    execSucBody progDeadLocal 4 0 initEnv0 = .ub .deadLocal := rfl

theorem progDeadLocal_opt_ok :
    execSucBody (applySingleUseConsts progDeadLocal 1) 4 0 initEnv0 = .ok 77 := rfl

theorem singleUseConsts_deadLocal_erases_ub :
    ¬ UbEquivalent
        (execSucBody progDeadLocal 4 0 initEnv0)
        (execSucBody (applySingleUseConsts progDeadLocal 1) 4 0 initEnv0) := by
  rw [progDeadLocal_orig_ub, progDeadLocal_opt_ok]
  exact not_ubEquivalent_ub_to_ok .deadLocal 77

theorem singleUseConsts_deadLocal_still_refines :
    Refines
      (execSucBody progDeadLocal 4 0 initEnv0)
      (execSucBody (applySingleUseConsts progDeadLocal 1) 4 0 initEnv0) := by
  rw [progDeadLocal_orig_ub, progDeadLocal_opt_ok]
  trivial

/-! ### Counterexample 2: Non-Dominating Uninitialized-Memory UB Erasure (`NONDOM = 88`)
    Mirrors live Miri probe `nondom_uninit_const(false)`. -/

def progNonDom : SucBody :=
  { argCount := 1
    blocks := [
      { stmts := [.storageLive 2]
        term := .switchBool 1 1 2 },
      { stmts := [.assign 2 (.constVal 88)]
        term := .goto 2 },
      { stmts := [.assign 0 (.copyLocal 2), .storageDead 2]
        term := .ret }
    ] }

theorem progNonDom_syntactically_eligible :
    isSyntacticSingleUseConst progNonDom 2 = some 88 := rfl

theorem progNonDom_orig_false_ub :
    execSucBody progNonDom 8 0 (initEnv1 0) = .ub .uninitRead := rfl

theorem progNonDom_opt_false_ok :
    execSucBody (applySingleUseConsts progNonDom 2) 8 0 (initEnv1 0) = .ok 88 := rfl

theorem progNonDom_orig_true_ok :
    execSucBody progNonDom 8 0 (initEnv1 1) = .ok 88 := rfl

theorem progNonDom_opt_true_ok :
    execSucBody (applySingleUseConsts progNonDom 2) 8 0 (initEnv1 1) = .ok 88 := rfl

theorem singleUseConsts_nonDominating_erases_ub :
    ¬ UbEquivalent
        (execSucBody progNonDom 8 0 (initEnv1 0))
        (execSucBody (applySingleUseConsts progNonDom 2) 8 0 (initEnv1 0)) := by
  rw [progNonDom_orig_false_ub, progNonDom_opt_false_ok]
  exact not_ubEquivalent_ub_to_ok .uninitRead 88

/-! ### Counterexample 3: Dominating Init with Intervening `StorageDead; StorageLive` Reset -/

def progStorageReset : SucBody :=
  { argCount := 0
    blocks := [
      { stmts := [
          .storageLive 1,
          .assign 1 (.constVal 55),
          .storageDead 1,
          .storageLive 1,
          .assign 0 (.copyLocal 1)
        ]
        term := .ret }
    ] }

theorem progStorageReset_syntactically_eligible :
    isSyntacticSingleUseConst progStorageReset 1 = some 55 := rfl

theorem progStorageReset_orig_ub :
    execSucBody progStorageReset 4 0 initEnv0 = .ub .uninitRead := rfl

theorem progStorageReset_opt_ok :
    execSucBody (applySingleUseConsts progStorageReset 1) 4 0 initEnv0 = .ok 55 := rfl

theorem singleUseConsts_storageReset_erases_ub :
    ¬ UbEquivalent
        (execSucBody progStorageReset 4 0 initEnv0)
        (execSucBody (applySingleUseConsts progStorageReset 1) 4 0 initEnv0) := by
  rw [progStorageReset_orig_ub, progStorageReset_opt_ok]
  exact not_ubEquivalent_ub_to_ok .uninitRead 55

/-! ### Repaired `SingleUseConsts` Bidirectional Soundness Theorem -/

/-- Predicate asserting that statement `s` neither reads, writes, moves, nor
    toggles storage liveness of local `x`. -/
def stmtDisjointFrom (x : Nat) : SucStmt → Prop
  | .nop => True
  | .storageLive y => y ≠ x
  | .storageDead y => y ≠ x
  | .assign dest (.constVal _) => dest ≠ x
  | .assign dest (.copyLocal src) => dest ≠ x ∧ src ≠ x
  | .assign dest (.moveLocal src) => dest ≠ x ∧ src ≠ x

/-- Non-recursive list disjointness predicate via `List.foldr` (zero `._unsafe_rec`). -/
def stmtsDisjointFrom (x : Nat) (ss : List SucStmt) : Prop :=
  ss.foldr (fun s acc => stmtDisjointFrom x s ∧ acc) True

/-- Two environments agree everywhere except possibly at local `x`. -/
def envAgreeExcept (x : Nat) (e₁ e₂ : LocalEnv) : Prop :=
  ∀ y, y ≠ x → e₁ y = e₂ y

theorem envAgreeExcept_refl (x : Nat) (e : LocalEnv) : envAgreeExcept x e e :=
  fun _ _ => rfl

theorem envAgreeExcept_update_same (x : Nat) (e₁ e₂ : LocalEnv) (s : LocalSlot)
    (h : envAgreeExcept x e₁ e₂) :
    envAgreeExcept x (e₁.update x s) e₂ := by
  intro y hy
  rw [LocalEnv.update_other e₁ s (nat_beq_false_of_ne hy)]
  exact h y hy

theorem envAgreeExcept_update_both (x : Nat) (e₁ e₂ : LocalEnv) (y : Nat) (s : LocalSlot)
    (h : envAgreeExcept x e₁ e₂) :
    envAgreeExcept x (e₁.update y s) (e₂.update y s) := by
  intro z hz
  cases hzy : Nat.beq z y with
  | true =>
    have heq : z = y := nat_eq_of_beq hzy
    rw [heq, LocalEnv.update_same, LocalEnv.update_same]
  | false =>
    rw [LocalEnv.update_other e₁ s hzy, LocalEnv.update_other e₂ s hzy]
    exact h z hz

/-- Stepping a statement disjoint from `x` preserves `x`'s slot and simulates
    identically across environments agreeing off `x`. -/
theorem stepSucStmt_disjoint_sim {x : Nat} {s : SucStmt}
    (hdisj : stmtDisjointFrom x s) {e₁ e₂ : LocalEnv}
    (hagree : envAgreeExcept x e₁ e₂) :
    match stepSucStmt e₁ s, stepSucStmt e₂ s with
    | .error k₁, .error k₂ => k₁ = k₂
    | .ok e₁', .ok e₂' =>
      e₁' x = e₁ x ∧ e₂' x = e₂ x ∧ envAgreeExcept x e₁' e₂'
    | _, _ => False := by
  cases s with
  | nop =>
    exact ⟨rfl, rfl, hagree⟩
  | storageLive y =>
    have hxy : Nat.beq x y = false := nat_beq_false_of_ne (Ne.symm hdisj)
    exact ⟨LocalEnv.update_other e₁ .liveUninit hxy,
           LocalEnv.update_other e₂ .liveUninit hxy,
           envAgreeExcept_update_both x e₁ e₂ y .liveUninit hagree⟩
  | storageDead y =>
    have hxy : Nat.beq x y = false := nat_beq_false_of_ne (Ne.symm hdisj)
    exact ⟨LocalEnv.update_other e₁ .dead hxy,
           LocalEnv.update_other e₂ .dead hxy,
           envAgreeExcept_update_both x e₁ e₂ y .dead hagree⟩
  | assign dest op =>
    cases op with
    | constVal c =>
      have hdest : e₁ dest = e₂ dest := hagree dest hdisj
      have hxd : Nat.beq x dest = false := nat_beq_false_of_ne (Ne.symm hdisj)
      unfold stepSucStmt evalSucOperand
      dsimp only
      rw [hdest]
      cases e₂ dest with
      | dead => rfl
      | liveUninit =>
        exact ⟨LocalEnv.update_other e₁ (.liveInit c) hxd,
               LocalEnv.update_other e₂ (.liveInit c) hxd,
               envAgreeExcept_update_both x e₁ e₂ dest (.liveInit c) hagree⟩
      | liveInit _ =>
        exact ⟨LocalEnv.update_other e₁ (.liveInit c) hxd,
               LocalEnv.update_other e₂ (.liveInit c) hxd,
               envAgreeExcept_update_both x e₁ e₂ dest (.liveInit c) hagree⟩
    | copyLocal src =>
      rcases hdisj with ⟨hdestNe, hsrcNe⟩
      have hsrc : e₁ src = e₂ src := hagree src hsrcNe
      have hdest : e₁ dest = e₂ dest := hagree dest hdestNe
      have hxd : Nat.beq x dest = false := nat_beq_false_of_ne (Ne.symm hdestNe)
      unfold stepSucStmt evalSucOperand
      dsimp only
      rw [hsrc]
      cases e₂ src with
      | dead => rfl
      | liveUninit => rfl
      | liveInit v =>
        dsimp only
        rw [hdest]
        cases e₂ dest with
        | dead => rfl
        | liveUninit =>
          exact ⟨LocalEnv.update_other e₁ (.liveInit v) hxd,
                 LocalEnv.update_other e₂ (.liveInit v) hxd,
                 envAgreeExcept_update_both x e₁ e₂ dest (.liveInit v) hagree⟩
        | liveInit _ =>
          exact ⟨LocalEnv.update_other e₁ (.liveInit v) hxd,
                 LocalEnv.update_other e₂ (.liveInit v) hxd,
                 envAgreeExcept_update_both x e₁ e₂ dest (.liveInit v) hagree⟩
    | moveLocal src =>
      rcases hdisj with ⟨hdestNe, hsrcNe⟩
      have hsrc : e₁ src = e₂ src := hagree src hsrcNe
      have hxs : Nat.beq x src = false := nat_beq_false_of_ne (Ne.symm hsrcNe)
      have hxd : Nat.beq x dest = false := nat_beq_false_of_ne (Ne.symm hdestNe)
      unfold stepSucStmt evalSucOperand
      dsimp only
      rw [hsrc]
      cases e₂ src with
      | dead => rfl
      | liveUninit => rfl
      | liveInit v =>
        dsimp only
        have hagree1 : envAgreeExcept x (e₁.update src .liveUninit) (e₂.update src .liveUninit) :=
          envAgreeExcept_update_both x e₁ e₂ src .liveUninit hagree
        have hdest1 : (e₁.update src .liveUninit) dest = (e₂.update src .liveUninit) dest :=
          hagree1 dest hdestNe
        rw [hdest1]
        cases (e₂.update src .liveUninit) dest with
        | dead => rfl
        | liveUninit =>
          refine ⟨?_, ?_, envAgreeExcept_update_both x _ _ dest (.liveInit v) hagree1⟩
          · rw [LocalEnv.update_other _ _ hxd, LocalEnv.update_other _ _ hxs]
          · rw [LocalEnv.update_other _ _ hxd, LocalEnv.update_other _ _ hxs]
        | liveInit _ =>
          refine ⟨?_, ?_, envAgreeExcept_update_both x _ _ dest (.liveInit v) hagree1⟩
          · rw [LocalEnv.update_other _ _ hxd, LocalEnv.update_other _ _ hxs]
          · rw [LocalEnv.update_other _ _ hxd, LocalEnv.update_other _ _ hxs]

/-- Multi-step simulation over a disjoint statement list `ss`. -/
theorem execSucStmts_disjoint_sim {x : Nat} {ss : List SucStmt}
    (hdisj : stmtsDisjointFrom x ss) {e₁ e₂ : LocalEnv}
    (hagree : envAgreeExcept x e₁ e₂) :
    match execSucStmts e₁ ss, execSucStmts e₂ ss with
    | .error k₁, .error k₂ => k₁ = k₂
    | .ok e₁', .ok e₂' =>
      e₁' x = e₁ x ∧ e₂' x = e₂ x ∧ envAgreeExcept x e₁' e₂'
    | _, _ => False := by
  induction ss generalizing e₁ e₂ with
  | nil => exact ⟨rfl, rfl, hagree⟩
  | cons s rest ih =>
    rcases hdisj with ⟨hs, hrest⟩
    have hstep := stepSucStmt_disjoint_sim hs hagree
    rw [execSucStmts_cons, execSucStmts_cons]
    cases h1 : stepSucStmt e₁ s with
    | error k₁ =>
      cases h2 : stepSucStmt e₂ s with
      | error k₂ =>
        rw [h1, h2] at hstep
        exact hstep
      | ok e₂' =>
        rw [h1, h2] at hstep
        exact False.elim hstep
    | ok e₁' =>
      cases h2 : stepSucStmt e₂ s with
      | error k₂ =>
        rw [h1, h2] at hstep
        exact False.elim hstep
      | ok e₂' =>
        rw [h1, h2] at hstep
        rcases hstep with ⟨hx₁, hx₂, hagree'⟩
        have htail := ih hrest hagree'
        dsimp only
        cases hr1 : execSucStmts e₁' rest with
        | error k₁ =>
          cases hr2 : execSucStmts e₂' rest with
          | error k₂ =>
            rw [hr1, hr2] at htail
            exact htail
          | ok _ =>
            rw [hr1, hr2] at htail
            exact False.elim htail
        | ok e₁'' =>
          cases hr2 : execSucStmts e₂' rest with
          | error k₂ =>
            rw [hr1, hr2] at htail
            exact False.elim htail
          | ok e₂'' =>
            rw [hr1, hr2] at htail
            rcases htail with ⟨hx₁', hx₂', hagree''⟩
            exact ⟨hx₁'.trans hx₁, hx₂'.trans hx₂, hagree''⟩

/-- Helper lemma: executing concatenated statement lists distributes. -/
theorem execSucStmts_append (e : LocalEnv) (s₁ s₂ : List SucStmt) :
    execSucStmts e (s₁ ++ s₂) =
      match execSucStmts e s₁ with
      | .error k => .error k
      | .ok e' => execSucStmts e' s₂ := by
  induction s₁ generalizing e with
  | nil => rfl
  | cons s rest ih =>
    change execSucStmts e (s :: (rest ++ s₂)) = _
    rw [execSucStmts_cons, execSucStmts_cons]
    cases stepSucStmt e s with
    | error k => rfl
    | ok e' => exact ih e'

/-- Execute a single-block trace returning local `0`. -/
def evalStraightBlock (stmts : List SucStmt) (env : LocalEnv) : Outcome :=
  match execSucStmts env stmts with
  | .error k => .ub k
  | .ok env' =>
    match env' 0 with
    | .dead => .ub .deadLocal
    | .liveUninit => .ub .uninitRead
    | .liveInit v => .ok v

def mkUseOperand (x : Nat) : Bool → SucOperand
  | false => .copyLocal x
  | true => .moveLocal x

/-- Helper: stepping a repaired single-use replacement (`copyLocal x` or `moveLocal x`
    replaced by `constVal c`) agrees exactly when `e₁ x = .liveInit c` and
    `envAgreeExcept x e₁ e₂` and `dest ≠ x`. -/
theorem stepSucStmt_use_replace {x dest c : Nat} (hdestNe : dest ≠ x)
    (isMove : Bool) {e₁ e₂ : LocalEnv}
    (hx₁ : e₁ x = .liveInit c) (hagree : envAgreeExcept x e₁ e₂) :
    match stepSucStmt e₁ (.assign dest (mkUseOperand x isMove)),
          stepSucStmt e₂ (.assign dest (.constVal c)) with
    | .error k₁, .error k₂ => k₁ = k₂
    | .ok e₁', .ok e₂' => envAgreeExcept x e₁' e₂'
    | _, _ => False := by
  cases isMove with
  | false =>
    unfold mkUseOperand stepSucStmt evalSucOperand
    dsimp only
    rw [hx₁]
    dsimp only
    have hd : e₁ dest = e₂ dest := hagree dest hdestNe
    rw [hd]
    cases e₂ dest with
    | dead => rfl
    | liveUninit => exact envAgreeExcept_update_both x e₁ e₂ dest (.liveInit c) hagree
    | liveInit _ => exact envAgreeExcept_update_both x e₁ e₂ dest (.liveInit c) hagree
  | true =>
    unfold mkUseOperand stepSucStmt evalSucOperand
    dsimp only
    rw [hx₁]
    dsimp only
    have hagree1 : envAgreeExcept x (e₁.update x .liveUninit) e₂ :=
      envAgreeExcept_update_same x e₁ e₂ .liveUninit hagree
    have hd : (e₁.update x .liveUninit) dest = e₂ dest := hagree1 dest hdestNe
    rw [hd]
    cases e₂ dest with
    | dead => rfl
    | liveUninit =>
      exact envAgreeExcept_update_both x (e₁.update x .liveUninit) e₂ dest (.liveInit c) hagree1
    | liveInit _ =>
      exact envAgreeExcept_update_both x (e₁.update x .liveUninit) e₂ dest (.liveInit c) hagree1

/-- **Repaired `SingleUseConsts` Exact Soundness Theorem**:
    For any dominating trace `pre ++ [x := const c] ++ mid ++ [dest := copy/move x] ++ post`
    where `x ≠ 0`, `dest ≠ x`, `x` is live at `init`, and `mid`/`post` are
    disjoint from `x` (no `StorageDead x`, `StorageLive x`, write, or `move x`),
    replacing `x := const c` with `nop` and `copy/move x` with `const c`
    preserves the **exact** outcome (`ExactEq`). -/
theorem singleUseConsts_repaired_exact
    (x dest c : Nat) (isMove : Bool)
    (pre mid post : List SucStmt) (env0 : LocalEnv)
    (hxNe0 : x ≠ 0)
    (hdestNe : dest ≠ x)
    (hLiveAtInit : ∀ ePre, execSucStmts env0 pre = .ok ePre → ePre x ≠ .dead)
    (hMidDisj : stmtsDisjointFrom x mid)
    (hPostDisj : stmtsDisjointFrom x post) :
    evalStraightBlock
      (pre ++ [.assign x (.constVal c)] ++ mid ++ [.assign dest (mkUseOperand x isMove)] ++ post)
      env0 =
    evalStraightBlock
      (pre ++ [.nop] ++ mid ++ [.assign dest (.constVal c)] ++ post)
      env0 := by
  unfold evalStraightBlock
  rw [execSucStmts_append, execSucStmts_append,
      execSucStmts_append, execSucStmts_append,
      execSucStmts_append, execSucStmts_append,
      execSucStmts_append, execSucStmts_append]
  cases hpre : execSucStmts env0 pre with
  | error k => rfl
  | ok ePre =>
    dsimp only
    have hnotDead : ePre x ≠ .dead := hLiveAtInit ePre hpre
    have hInitOrig :
        execSucStmts ePre [.assign x (.constVal c)] = .ok (ePre.update x (.liveInit c)) := by
      rw [execSucStmts_cons]
      unfold stepSucStmt evalSucOperand
      dsimp only
      cases hslot : ePre x with
      | dead => exact False.elim (hnotDead hslot)
      | liveUninit => rfl
      | liveInit _ => rfl
    have hInitOpt : execSucStmts ePre [.nop] = .ok ePre := rfl
    rw [hInitOrig, hInitOpt]
    dsimp only
    have hAgree1 : envAgreeExcept x (ePre.update x (.liveInit c)) ePre :=
      envAgreeExcept_update_same x ePre ePre (.liveInit c) (envAgreeExcept_refl x ePre)
    have hMid := execSucStmts_disjoint_sim hMidDisj hAgree1
    cases hm1 : execSucStmts (ePre.update x (.liveInit c)) mid with
    | error k₁ =>
      cases hm2 : execSucStmts ePre mid with
      | error k₂ =>
        rw [hm1, hm2] at hMid
        dsimp only
        rw [hMid]
      | ok _ =>
        rw [hm1, hm2] at hMid
        exact False.elim hMid
    | ok eMid₁ =>
      cases hm2 : execSucStmts ePre mid with
      | error k₂ =>
        rw [hm1, hm2] at hMid
        exact False.elim hMid
      | ok eMid₂ =>
        rw [hm1, hm2] at hMid
        rcases hMid with ⟨hxMid₁, _, hAgreeMid⟩
        rw [LocalEnv.update_same] at hxMid₁
        dsimp only
        have hUse := stepSucStmt_use_replace hdestNe isMove hxMid₁ hAgreeMid
        rw [execSucStmts_cons, execSucStmts_cons]
        cases hu1 : stepSucStmt eMid₁ (.assign dest (mkUseOperand x isMove)) with
        | error k₁ =>
          cases hu2 : stepSucStmt eMid₂ (.assign dest (.constVal c)) with
          | error k₂ =>
            rw [hu1, hu2] at hUse
            dsimp only
            rw [hUse]
          | ok _ =>
            rw [hu1, hu2] at hUse
            exact False.elim hUse
        | ok eUse₁ =>
          cases hu2 : stepSucStmt eMid₂ (.assign dest (.constVal c)) with
          | error k₂ =>
            rw [hu1, hu2] at hUse
            exact False.elim hUse
          | ok eUse₂ =>
            rw [hu1, hu2] at hUse
            dsimp only
            rw [execSucStmts_nil, execSucStmts_nil]
            dsimp only
            have hPost := execSucStmts_disjoint_sim hPostDisj hUse
            cases hp1 : execSucStmts eUse₁ post with
            | error k₁ =>
              cases hp2 : execSucStmts eUse₂ post with
              | error k₂ =>
                rw [hp1, hp2] at hPost
                dsimp only
                rw [hPost]
              | ok _ =>
                rw [hp1, hp2] at hPost
                exact False.elim hPost
            | ok ePost₁ =>
              cases hp2 : execSucStmts eUse₂ post with
              | error k₂ =>
                rw [hp1, hp2] at hPost
                exact False.elim hPost
              | ok ePost₂ =>
                rw [hp1, hp2] at hPost
                rcases hPost with ⟨_, _, hAgreePost⟩
                have h0 : ePost₁ 0 = ePost₂ 0 := hAgreePost 0 (Ne.symm hxNe0)
                dsimp only
                rw [h0]

/-- **Repaired `SingleUseConsts` Bidirectional Soundness Corollary**
    (`singleUseConsts_repaired_sound_iff`): under the repaired preconditions,
    both defined return values AND every UB category satisfy exact `↔` equivalence. -/
theorem singleUseConsts_repaired_sound_iff
    (x dest c : Nat) (isMove : Bool)
    (pre mid post : List SucStmt) (env0 : LocalEnv)
    (hxNe0 : x ≠ 0)
    (hdestNe : dest ≠ x)
    (hLiveAtInit : ∀ ePre, execSucStmts env0 pre = .ok ePre → ePre x ≠ .dead)
    (hMidDisj : stmtsDisjointFrom x mid)
    (hPostDisj : stmtsDisjointFrom x post) :
    (∀ v,
      evalStraightBlock
        (pre ++ [.assign x (.constVal c)] ++ mid ++ [.assign dest (mkUseOperand x isMove)] ++ post)
        env0 = .ok v ↔
      evalStraightBlock
        (pre ++ [.nop] ++ mid ++ [.assign dest (.constVal c)] ++ post)
        env0 = .ok v) ∧
    (∀ k,
      evalStraightBlock
        (pre ++ [.assign x (.constVal c)] ++ mid ++ [.assign dest (mkUseOperand x isMove)] ++ post)
        env0 = .ub k ↔
      evalStraightBlock
        (pre ++ [.nop] ++ mid ++ [.assign dest (.constVal c)] ++ post)
        env0 = .ub k) := by
  have heq :=
    singleUseConsts_repaired_exact x dest c isMove pre mid post env0
      hxNe0 hdestNe hLiveAtInit hMidDisj hPostDisj
  constructor
  · intro v
    rw [heq]
  · intro k
    rw [heq]

/-- `VarDebugInfoContents::Place -> Const` scoping (`single_use_consts.rs:67-71, 190-204`). -/
def debugObservePlace (env : LocalEnv) (x : Nat) : Option Nat :=
  match env x with
  | .liveInit v => some v
  | _ => none

def debugObserveConst (c : Nat) : Option Nat := some c

theorem varDebugInfo_matches_when_live_init (env : LocalEnv) (x c : Nat)
    (h : env x = .liveInit c) :
    debugObservePlace env x = debugObserveConst c := by
  unfold debugObservePlace debugObserveConst
  rw [h]

theorem varDebugInfo_overextends_when_dead (env : LocalEnv) (x c : Nat)
    (h : env x = .dead) :
    debugObservePlace env x ≠ debugObserveConst c := by
  unfold debugObservePlace debugObserveConst
  rw [h]
  intro heq
  cases heq

end SingleUseConsts

/-! ============================================================================
    PART 3: `MatchBranchSimplification` (`match_branches.rs`)
    ============================================================================ -/

section MatchBranchSimplification

/-- Discriminant operand of a `SwitchInt`: either an already-materialized
    scalar value or an indirect dereference `*ptr` evaluated from `Heap`. -/
inductive DiscrOp where
  | directVal (v : Nat)
  | derefPtr (ptr : Nat)

def evalDiscrOp (h : Heap) : DiscrOp → Except UbKind Nat
  | .directVal v => .ok v
  | .derefPtr p =>
    match h p with
    | none => .error .nullDeref
    | some v => .ok v

/-- Retagging mode of an assignment (`WithRetag::Yes` vs `WithRetag::No` in
    `match_branches.rs:75-77, 309-313`). -/
inductive RetagMode where
  | yes
  | no

/-- Branch action returning a scalar value (modeling `_0 = <rval>; return`). -/
structure BranchAssign where
  value : Nat
  retag : RetagMode

/-- Non-recursive switch lookup via `List.foldr` (zero `._unsafe_rec`). -/
def lookupSwitch {α : Type} (cases : List (Nat × α)) (otherwise : Option α)
    (d : Nat) : Option α :=
  cases.foldr
    (fun hd acc => match Nat.beq d hd.1 with | true => some hd.2 | false => acc)
    otherwise

theorem lookupSwitch_nil {α : Type} (otherwise : Option α) (d : Nat) :
    lookupSwitch [] otherwise d = otherwise := rfl

theorem lookupSwitch_cons {α : Type} (hd : Nat × α) (tl : List (Nat × α))
    (otherwise : Option α) (d : Nat) :
    lookupSwitch (hd :: tl) otherwise d =
      match Nat.beq d hd.1 with
      | true => some hd.2
      | false => lookupSwitch tl otherwise d := rfl

/-- Evaluate a `SwitchInt` whose branches assign scalar values. -/
def evalSwitchAssign (h : Heap) (retagInvalid : Bool) (discr : DiscrOp)
    (cases : List (Nat × BranchAssign)) (otherwise : Option BranchAssign) : Outcome :=
  match evalDiscrOp h discr with
  | .error k => .ub k
  | .ok d =>
    match lookupSwitch cases otherwise d with
    | none => .ub .unreachable
    | some act =>
      match act.retag, retagInvalid with
      | .yes, true => .ub .invalidRetag
      | _, _ => .ok act.value

/-! ### Arm 1 (`identical_stmts`) & Live Indirect-Discriminant `*null_ptr` UB Erasure -/

/-- Unguarded `MatchBranchSimplification` for `identical_stmts`
    (`match_branches.rs:450-460`): because `self.discr_local` is `None`,
    the pass drops `discr` without emitting `PlaceMention(discr)`. -/
def evalMbsIdenticalUnguarded (retagInvalid : Bool) (act : BranchAssign) : Outcome :=
  match act.retag, retagInvalid with
  | .yes, true => .ub .invalidRetag
  | _, _ => .ok act.value

/-- Repaired `PlaceMention`-guarded `MatchBranchSimplification`: evaluates
    `PlaceMention(discr)` before executing the unified assignment. -/
def evalMbsIdenticalGuarded (h : Heap) (retagInvalid : Bool) (discr : DiscrOp)
    (act : BranchAssign) : Outcome :=
  match evalDiscrOp h discr with
  | .error k => .ub k
  | .ok _ =>
    match act.retag, retagInvalid with
    | .yes, true => .ub .invalidRetag
    | _, _ => .ok act.value

def mbsNullCases : List (Nat × BranchAssign) :=
  [(0, { value := 99, retag := .no })]

def mbsNullOtherwise : Option BranchAssign :=
  some { value := 99, retag := .no }

theorem mbs_identical_null_orig_ub :
    evalSwitchAssign nullHeap false (.derefPtr 0) mbsNullCases mbsNullOtherwise =
      .ub .nullDeref := rfl

theorem mbs_identical_null_unguarded_ok :
    evalMbsIdenticalUnguarded false { value := 99, retag := .no } = .ok 99 := rfl

/-- Live Counterexample (`MBS_NULL = 99`): unguarded `MatchBranchSimplification`
    erases indirect-discriminant `*null_ptr` UB even under `-Zmir-preserve-ub=yes`. -/
theorem mbs_identical_indirect_null_erases_ub :
    ¬ UbEquivalent
        (evalSwitchAssign nullHeap false (.derefPtr 0) mbsNullCases mbsNullOtherwise)
        (evalMbsIdenticalUnguarded false { value := 99, retag := .no }) := by
  rw [mbs_identical_null_orig_ub, mbs_identical_null_unguarded_ok]
  exact not_ubEquivalent_ub_to_ok .nullDeref 99

theorem lookupSwitch_all_eq {α : Type} (cases : List (Nat × α)) (act : α)
    (hall : ∀ p, p ∈ cases → p.2 = act) (d : Nat) :
    lookupSwitch cases (some act) d = some act := by
  induction cases with
  | nil => rfl
  | cons hd tl ih =>
    rw [lookupSwitch_cons]
    cases Nat.beq d hd.1 with
    | true =>
      have hhd : hd.2 = act := hall hd (List.Mem.head tl)
      rw [hhd]
    | false =>
      exact ih (fun p hp => hall p (List.Mem.tail hd hp))

/-- **Repaired `PlaceMention`-Guarded `identical_stmts` Exact Equivalence**:
    emitting `PlaceMention(discr)` restores exact equality for ALL heaps and
    ALL direct or indirect discriminants (including null pointers). -/
theorem mbs_identical_with_placemention_exact (h : Heap) (retagInvalid : Bool)
    (discr : DiscrOp) (cases : List (Nat × BranchAssign)) (act : BranchAssign)
    (hall : ∀ p, p ∈ cases → p.2 = act) :
    evalSwitchAssign h retagInvalid discr cases (some act) =
      evalMbsIdenticalGuarded h retagInvalid discr act := by
  unfold evalSwitchAssign evalMbsIdenticalGuarded
  cases evalDiscrOp h discr with
  | error k => rfl
  | ok d =>
    dsimp only
    rw [lookupSwitch_all_eq cases act hall d]

/-! ### Arm 2 (`unify_if_equal_const`): Equal Evaluated Consts & `WithRetag::No` Necessity -/

def evalMbsEqualConstGuarded (h : Heap) (discr : DiscrOp) (val : Nat) : Outcome :=
  match evalDiscrOp h discr with
  | .error k => .ub k
  | .ok _ => .ok val

theorem mbs_equal_const_with_no_retag_refines (h : Heap) (retagInvalid : Bool)
    (discr : DiscrOp) (cases : List (Nat × BranchAssign)) (ow : Option BranchAssign)
    (v : Nat)
    (hcases : ∀ p, p ∈ cases → p.2.value = v)
    (how : ∀ a, ow = some a → a.value = v) :
    Refines
      (evalSwitchAssign h retagInvalid discr cases ow)
      (evalMbsEqualConstGuarded h discr v) := by
  unfold evalSwitchAssign evalMbsEqualConstGuarded
  cases evalDiscrOp h discr with
  | error k => trivial
  | ok d =>
    dsimp only
    have hval : ∀ a, lookupSwitch cases ow d = some a → a.value = v := by
      induction cases with
      | nil => exact how
      | cons hd tl ih =>
        intro a ha
        rw [lookupSwitch_cons] at ha
        cases hbeq : Nat.beq d hd.1 with
        | true =>
          rw [hbeq] at ha
          cases ha
          exact hcases hd (List.Mem.head tl)
        | false =>
          rw [hbeq] at ha
          exact ih (fun p hp => hcases p (List.Mem.tail hd hp)) a ha
    cases hl : lookupSwitch cases ow d with
    | none => trivial
    | some a =>
      dsimp only
      have hav : a.value = v := hval a hl
      cases a.retag with
      | no =>
        change Outcome.ok v = Outcome.ok a.value
        rw [hav]
      | yes =>
        cases retagInvalid with
        | true => trivial
        | false =>
          change Outcome.ok v = Outcome.ok a.value
          rw [hav]

/-- Counterexample showing why `WithRetag::No` is mandatory in
    `unify_if_equal_const` (`match_branches.rs:75-77`). -/
theorem mbs_equal_const_retag_yes_unsound :
    ¬ Refines
        (evalSwitchAssign nullHeap true (.directVal 0)
          [(0, { value := 10, retag := .no })]
          (some { value := 10, retag := .yes }))
        (evalMbsIdenticalGuarded nullHeap true (.directVal 0)
          { value := 10, retag := .yes }) :=
  fun h => nomatch h

/-! ### Arm 3 (`unify_by_eq_op`): `Eq`/`Ne`, Discriminant Fault Preservation & Unreachable `otherwise` -/

def boolToNat : Bool → Nat
  | false => 0
  | true => 1

/-- Semantics of `unify_by_eq_op` (`match_branches.rs:115-148`). -/
def evalMbsEqOp (h : Heap) (discr : DiscrOp) (firstCase : Nat) (firstBool : Bool) : Outcome :=
  match evalDiscrOp h discr with
  | .error k => .ub k
  | .ok d =>
    let res :=
      match firstBool with
      | true => Nat.beq d firstCase
      | false => !(Nat.beq d firstCase)
    .ok (boolToNat res)

/-- Unlike `identical_stmts`, `unify_by_eq_op` allocates `self.discr_local()`,
    preserving indirect `*null_ptr` faults! -/
theorem mbs_eq_op_preserves_discr_fault (firstCase : Nat) (firstBool : Bool) :
    evalMbsEqOp nullHeap (.derefPtr 0) firstCase firstBool = .ub .nullDeref := rfl

theorem lookupSwitch_bool_others (rest : List (Nat × BranchAssign))
    (ow : Option BranchAssign) (b : Bool)
    (hrest : ∀ p, p ∈ rest → p.2 = { value := boolToNat (!b), retag := .no })
    (how : ∀ a, ow = some a → a = { value := boolToNat (!b), retag := .no })
    (d : Nat) (a : BranchAssign) (hl : lookupSwitch rest ow d = some a) :
    a = { value := boolToNat (!b), retag := .no } := by
  induction rest with
  | nil => exact how a hl
  | cons hd tl ih =>
    rw [lookupSwitch_cons] at hl
    cases hbeq : Nat.beq d hd.1 with
    | true =>
      rw [hbeq] at hl
      cases hl
      exact hrest hd (List.Mem.head tl)
    | false =>
      rw [hbeq] at hl
      exact ih (fun p hp => hrest p (List.Mem.tail hd hp)) hl

/-- **Soundness of `unify_by_eq_op` (`match_branches.rs:115-148`)**:
    always refines the original `SwitchInt`. -/
theorem mbs_eq_op_refines (h : Heap) (discr : DiscrOp)
    (firstCase : Nat) (firstBool : Bool)
    (rest : List (Nat × BranchAssign)) (ow : Option BranchAssign)
    (hrest : ∀ p, p ∈ rest → p.2 = { value := boolToNat (!firstBool), retag := .no })
    (how : ∀ a, ow = some a → a = { value := boolToNat (!firstBool), retag := .no }) :
    Refines
      (evalSwitchAssign h false discr
        ((firstCase, { value := boolToNat firstBool, retag := .no }) :: rest) ow)
      (evalMbsEqOp h discr firstCase firstBool) := by
  unfold evalSwitchAssign evalMbsEqOp
  cases evalDiscrOp h discr with
  | error k => trivial
  | ok d =>
    dsimp only
    rw [lookupSwitch_cons]
    cases hbeq : Nat.beq d firstCase with
    | true =>
      cases firstBool <;> rfl
    | false =>
      dsimp only
      cases hl : lookupSwitch rest ow d with
      | none => trivial
      | some a =>
        have ha := lookupSwitch_bool_others rest ow firstBool hrest how d a hl
        rw [ha]
        cases firstBool <;> rfl

/-- When `otherwise` is reachable, `unify_by_eq_op` is **exact** (`ExactEq`)
    for ALL heaps and discriminants. -/
theorem mbs_eq_op_exact_with_reachable_otherwise (h : Heap) (discr : DiscrOp)
    (firstCase : Nat) (firstBool : Bool) (rest : List (Nat × BranchAssign))
    (hrest : ∀ p, p ∈ rest → p.2 = { value := boolToNat (!firstBool), retag := .no }) :
    let owAct : BranchAssign := { value := boolToNat (!firstBool), retag := .no }
    evalSwitchAssign h false discr
      ((firstCase, { value := boolToNat firstBool, retag := .no }) :: rest) (some owAct) =
    evalMbsEqOp h discr firstCase firstBool := by
  intro owAct
  unfold evalSwitchAssign evalMbsEqOp
  cases evalDiscrOp h discr with
  | error k => rfl
  | ok d =>
    dsimp only
    rw [lookupSwitch_cons]
    cases hbeq : Nat.beq d firstCase with
    | true =>
      cases firstBool <;> rfl
    | false =>
      dsimp only
      rw [lookupSwitch_all_eq rest owAct hrest d]
      cases firstBool <;> rfl

/-- Unreachable-otherwise UB erasure in `unify_by_eq_op` (`arm3_ne_enum`):
    invalid discriminant `99` flips `.ub .unreachable` to `.ok 1`. -/
theorem mbs_eq_op_unreachable_otherwise_erases_ub :
    let cases : List (Nat × BranchAssign) :=
      [(1, { value := 0, retag := .no }),
       (2, { value := 1, retag := .no }),
       (3, { value := 1, retag := .no })]
    evalSwitchAssign nullHeap false (.directVal 99) cases none = .ub .unreachable ∧
    evalMbsEqOp nullHeap (.directVal 99) 1 false = .ok 1 ∧
    ¬ UbEquivalent
        (evalSwitchAssign nullHeap false (.directVal 99) cases none)
        (evalMbsEqOp nullHeap (.directVal 99) 1 false) :=
  ⟨rfl, rfl, not_ubEquivalent_ub_to_ok .unreachable 1⟩

/-! ### Arm 4 (`unify_by_int_to_int`): Exact Signed/Unsigned `can_cast` Semantics -/

inductive IntKind where
  | uint (bits : Nat)
  | sint (bits : Nat)

def IntKind.bits : IntKind → Nat
  | .uint b => b
  | .sint b => b

def truncateBits (v w : Nat) : Nat := v % (2 ^ w)

/-- Sign-extend a `srcW`-bit two's-complement scalar to 128 bits
    (matching `from_scalar.to_int(src_layout.size) as u128` at `match_branches.rs:476`). -/
def signExtend128 (raw srcW : Nat) : Nat :=
  let masked := truncateBits raw srcW
  match Nat.beq srcW 0 with
  | true => 0
  | false =>
    let signBit := 2 ^ (srcW - 1)
    match Nat.blt masked signBit with
    | true => masked
    | false => (2 ^ 128 - 2 ^ srcW) + masked

def intToIntCast (srcKind dstKind : IntKind) (rawSrc : Nat) : Nat :=
  let extended128 :=
    match srcKind with
    | .uint w => truncateBits rawSrc w
    | .sint w => signExtend128 rawSrc w
  truncateBits extended128 dstKind.bits

def canCast (srcVal : Nat) (srcKind dstKind : IntKind) (targetScalar : Nat) : Bool :=
  Nat.beq (intToIntCast srcKind dstKind srcVal) targetScalar

def evalMbsIntToInt (h : Heap) (discr : DiscrOp) (srcKind dstKind : IntKind) : Outcome :=
  match evalDiscrOp h discr with
  | .error k => .ub k
  | .ok d => .ok (intToIntCast srcKind dstKind d)

/-- **Soundness of `unify_by_int_to_int` (`match_branches.rs:187-215, 466-489`)**. -/
theorem mbs_int_to_int_refines (h : Heap) (discr : DiscrOp)
    (srcKind dstKind : IntKind) (cases : List (Nat × BranchAssign))
    (hall : ∀ p, p ∈ cases → canCast p.1 srcKind dstKind p.2.value = true) :
    Refines
      (evalSwitchAssign h false discr cases none)
      (evalMbsIntToInt h discr srcKind dstKind) := by
  unfold evalSwitchAssign evalMbsIntToInt
  cases evalDiscrOp h discr with
  | error k => trivial
  | ok d =>
    dsimp only
    have hhit : ∀ a, lookupSwitch cases none d = some a →
        intToIntCast srcKind dstKind d = a.value := by
      induction cases with
      | nil =>
        intro a ha
        cases ha
      | cons hd tl ih =>
        intro a ha
        rw [lookupSwitch_cons] at ha
        cases hbeq : Nat.beq d hd.1 with
        | true =>
          rw [hbeq] at ha
          cases ha
          have hdeq : d = hd.1 := nat_eq_of_beq hbeq
          rw [hdeq]
          exact nat_eq_of_beq (hall hd (List.Mem.head tl))
        | false =>
          rw [hbeq] at ha
          exact ih (fun p hp => hall p (List.Mem.tail hd hp)) a ha
    cases hl : lookupSwitch cases none d with
    | none => trivial
    | some a =>
      dsimp only
      have hv := hhit a hl
      cases a.retag with
      | no =>
        change Outcome.ok (intToIntCast srcKind dstKind d) = Outcome.ok a.value
        rw [hv]
      | yes =>
        change Outcome.ok (intToIntCast srcKind dstKind d) = Outcome.ok a.value
        rw [hv]

theorem canCast_tri_u8_to_i16 :
    canCast 1 (.uint 8) (.sint 16) 1 = true ∧
    canCast 2 (.uint 8) (.sint 16) 2 = true ∧
    canCast 3 (.uint 8) (.sint 16) 3 = true :=
  ⟨rfl, rfl, rfl⟩

/-- Negative `can_cast` verification (`arm4_int_to_int_fail`):
    `-1_i8` (`0xFF = 255`) cast to `u16` sign-extends to `0xFFFF = 65535`,
    NOT `255`. -/
theorem canCast_signed_neg1_i8_to_u16_rejects_255 :
    canCast 255 (.sint 8) (.uint 16) 255 = false ∧
    canCast 255 (.sint 8) (.uint 16) 65535 = true :=
  ⟨rfl, rfl⟩

/-! ### Arm 5 (`unify_by_copy`): Enum Clone Reconstruction & Aliasing Guard -/

structure EnumVal where
  tag : Nat
  payload : Option Nat

inductive CopyBranchRhs where
  | copySrc
  | unitVariant (tag : Nat)

def evalEnumCopyMatch (srcVal : EnumVal)
    (cases : List (Nat × CopyBranchRhs)) : Option EnumVal :=
  match lookupSwitch cases none srcVal.tag with
  | none => none
  | some .copySrc => some srcVal
  | some (.unitVariant t) => some { tag := t, payload := none }

def UnitVariantValid (srcVal : EnumVal) (cases : List (Nat × CopyBranchRhs)) : Prop :=
  ∀ p, p ∈ cases →
    match p.2 with
    | .copySrc => True
    | .unitVariant t => t = p.1 ∧ (srcVal.tag = t → srcVal.payload = none)

/-- **Soundness of `unify_by_copy` (`match_branches.rs:233-315`)**. -/
theorem mbs_unify_by_copy_sound (srcVal : EnumVal)
    (cases : List (Nat × CopyBranchRhs))
    (hwf : UnitVariantValid srcVal cases)
    (outVal : EnumVal)
    (hreach : evalEnumCopyMatch srcVal cases = some outVal) :
    outVal = srcVal := by
  unfold evalEnumCopyMatch at hreach
  induction cases with
  | nil => cases hreach
  | cons hd tl ih =>
    rw [lookupSwitch_cons] at hreach
    cases hbeq : Nat.beq srcVal.tag hd.1 with
    | true =>
      rw [hbeq] at hreach
      have htag : srcVal.tag = hd.1 := nat_eq_of_beq hbeq
      have hhd := hwf hd (List.Mem.head tl)
      cases hrhs : hd.2 with
      | copySrc =>
        rw [hrhs] at hreach
        cases hreach
        rfl
      | unitVariant t =>
        rw [hrhs] at hreach hhd
        rcases hhd with ⟨htEq, hpay⟩
        cases hreach
        have hst : srcVal.tag = t := htag.trans htEq.symm
        have hp : srcVal.payload = none := hpay hst
        cases srcVal with
        | mk stag spay =>
          dsimp only at hst hp
          rw [hst, hp]
    | false =>
      rw [hbeq] at hreach
      exact ih (fun p hp => hwf p (List.Mem.tail hd hp)) hreach

/-- **Aliasing Hazard Counterexample (`match_branches.rs:264-276` in HEAD `137d1d4945`)**:
    explains why `borrowed_locals` / non-overlapping guard is required before
    replacing a unit-variant constant assignment with `dest = copy *src`. -/
def evalUnitBranch : Outcome := .ok 1

def evalUnifiedCopy (srcAliasesDest : Bool) : Outcome :=
  match srcAliasesDest with
  | true => .ub .overlappingCopy
  | false => .ok 1

theorem mbs_unify_by_copy_aliasing_hazard :
    ¬ Refines evalUnitBranch (evalUnifiedCopy true) :=
  fun h => nomatch h

end MatchBranchSimplification

/-! ============================================================================
    PART 4: `SimplifyConstCondition` (`simplify_branches.rs` + `patch.rs`)
    ============================================================================ -/

section SimplifyConstCondition

inductive SccOp where
  | constVal (v : Nat)
  | copyLocal (x : Nat)

inductive SccStmt where
  | assignConst (dest : Nat) (v : Nat)
  | assignOther (dest : Nat) (v : Nat)
  | derefRead (ptrLocal : Nat)
  | assume (op : SccOp)
  | nop

inductive SccTerm where
  | switchInt (discr : SccOp) (targetZero targetNonZero : Nat)
  | assert (cond : SccOp) (expected : Bool) (target : Nat)
  | goto (target : Nat)
  | unreachable

structure SccBlock where
  stmts : List SccStmt
  term : SccTerm

def natIsNonZero (n : Nat) : Bool := !(Nat.beq n 0)

def boolEq : Bool → Bool → Bool
  | false, false => true
  | true, true => true
  | _, _ => false

/-- Immediate-predecessor `try_get_const` (`simplify_branches.rs:35-51`). -/
def tryGetConst (op : SccOp) (hasPlaceConst : Option (Nat × Nat)) : Option Nat :=
  match op with
  | .constVal v => some v
  | .copyLocal x =>
    match hasPlaceConst with
    | some (p, v) =>
      match Nat.beq p x with
      | true => some v
      | false => none
    | none => none

/-- Exact statement-loop scan of `SimplifyConstCondition` (`simplify_branches.rs:54-75`)
    expressed via CPS `List.foldr` (zero `._unsafe_rec`). -/
def sccScanStmts (pre : Option (Nat × Nat)) (ss : List SccStmt) :
    List SccStmt × Option (Nat × Nat) × Bool :=
  ss.foldr
    (fun stmt k p =>
      match stmt with
      | .assume op =>
        match tryGetConst op p with
        | some c =>
          match natIsNonZero c with
          | true =>
            let (rest', preEnd, hitFalse) := k none
            (.nop :: rest', preEnd, hitFalse)
          | false =>
            ([], none, true)
        | none =>
          let (rest', preEnd, hitFalse) := k none
          (stmt :: rest', preEnd, hitFalse)
      | .assignConst lhs c =>
        let (rest', preEnd, hitFalse) := k (some (lhs, c))
        (stmt :: rest', preEnd, hitFalse)
      | other =>
        let (rest', preEnd, hitFalse) := k none
        (other :: rest', preEnd, hitFalse))
    (fun p => ([], p, false))
    pre

/-- Full `SimplifyConstCondition` + `MirPatch::apply` (`patch.rs:323-325`
    `if let TerminatorKind::Unreachable = patch { bb.statements.clear(); }`). -/
def simplifyConstConditionBlock (blk : SccBlock) : SccBlock :=
  let (stmts', preEnd, hitAssumeFalse) := sccScanStmts none blk.stmts
  match hitAssumeFalse with
  | true => { stmts := [], term := .unreachable }
  | false =>
    let term' :=
      match blk.term with
      | .switchInt discr t0 t1 =>
        match tryGetConst discr preEnd with
        | some c =>
          .goto (match Nat.beq c 0 with | true => t0 | false => t1)
        | none => blk.term
      | .assert cond expected target =>
        match tryGetConst cond preEnd with
        | some c =>
          match boolEq (natIsNonZero c) expected with
          | true => .goto target
          | false => blk.term
        | none => blk.term
      | other => other
    { stmts := stmts', term := term' }

def evalSccOp (env : LocalEnv) : SccOp → Except UbKind Nat
  | .constVal v => .ok v
  | .copyLocal x =>
    match env x with
    | .dead => .error .deadLocal
    | .liveUninit => .error .uninitRead
    | .liveInit v => .ok v

def stepSccStmt (h : Heap) (env : LocalEnv) : SccStmt → Except UbKind LocalEnv
  | .nop => .ok env
  | .assignConst lhs c =>
    match env lhs with
    | .dead => .error .deadLocal
    | _ => .ok (env.update lhs (.liveInit c))
  | .assignOther lhs v =>
    match env lhs with
    | .dead => .error .deadLocal
    | _ => .ok (env.update lhs (.liveInit v))
  | .derefRead ptrLocal =>
    match env ptrLocal with
    | .dead => .error .deadLocal
    | .liveUninit => .error .uninitRead
    | .liveInit addr =>
      match h addr with
      | none => .error .nullDeref
      | some _ => .ok env
  | .assume op =>
    match evalSccOp env op with
    | .error k => .error k
    | .ok c =>
      match natIsNonZero c with
      | true => .ok env
      | false => .error .assumeFalse

/-- Non-recursive statement list execution via CPS `List.foldr` (zero `._unsafe_rec`). -/
def execSccStmts (h : Heap) (env : LocalEnv) (ss : List SccStmt) : Except UbKind LocalEnv :=
  ss.foldr
    (fun s k e =>
      match stepSccStmt h e s with
      | .error err => .error err
      | .ok e' => k e')
    Except.ok
    env

theorem execSccStmts_nil (h : Heap) (env : LocalEnv) :
    execSccStmts h env [] = .ok env := rfl

theorem execSccStmts_cons (h : Heap) (env : LocalEnv) (s : SccStmt) (ss : List SccStmt) :
    execSccStmts h env (s :: ss) =
      match stepSccStmt h env s with
      | .error k => .error k
      | .ok env' => execSccStmts h env' ss := rfl

def evalSccBlock (h : Heap) (env : LocalEnv) (blk : SccBlock) : Outcome :=
  match execSccStmts h env blk.stmts with
  | .error k => .ub k
  | .ok env' =>
    match blk.term with
    | .goto t => .ok t
    | .unreachable => .ub .unreachable
    | .switchInt discr t0 t1 =>
      match evalSccOp env' discr with
      | .error k => .ub k
      | .ok c => .ok (match Nat.beq c 0 with | true => t0 | false => t1)
    | .assert cond expected target =>
      match evalSccOp env' cond with
      | .error k => .ub k
      | .ok c =>
        match boolEq (natIsNonZero c) expected with
        | true => .ok target
        | false => .panic

/-- Invariant capturing `has_place_const` soundness (`simplify_branches.rs:41-42`). -/
def PreConstValid (env : LocalEnv) : Option (Nat × Nat) → Prop
  | none => True
  | some (p, c) => env p = .liveInit c

theorem tryGetConst_sound {env : LocalEnv} {op : SccOp} {pre : Option (Nat × Nat)} {c : Nat}
    (hvalid : PreConstValid env pre) (hget : tryGetConst op pre = some c) :
    evalSccOp env op = .ok c := by
  cases op with
  | constVal v =>
    cases hget
    rfl
  | copyLocal x =>
    cases pre with
    | none => cases hget
    | some pc =>
      rcases pc with ⟨p, v⟩
      unfold tryGetConst at hget
      dsimp only at hget
      cases hbeq : Nat.beq p x with
      | true =>
        rw [hbeq] at hget
        cases hget
        have hpx : p = x := nat_eq_of_beq hbeq
        unfold PreConstValid at hvalid
        dsimp only at hvalid
        rw [hpx] at hvalid
        unfold evalSccOp
        dsimp only
        rw [hvalid]
      | false =>
        rw [hbeq] at hget
        cases hget

/-- Core inductive soundness lemma for `sccScanStmts` (purely constructive,
    using `match` on `Bool` so `Classical.propDecidable` is never invoked!). -/
theorem sccScanStmts_sound (h : Heap) (stmts : List SccStmt)
    (pre : Option (Nat × Nat)) (env : LocalEnv)
    (hvalid : PreConstValid env pre) :
    match (sccScanStmts pre stmts).2.2 with
    | true => ∃ k, execSccStmts h env stmts = .error k
    | false =>
      execSccStmts h env (sccScanStmts pre stmts).1 = execSccStmts h env stmts ∧
      ∀ env', execSccStmts h env stmts = .ok env' →
        PreConstValid env' (sccScanStmts pre stmts).2.1 := by
  induction stmts generalizing pre env with
  | nil =>
    refine ⟨rfl, fun env' heq => ?_⟩
    cases heq
    exact hvalid
  | cons s rest ih =>
    cases s with
    | nop =>
      exact ih none env trivial
    | assignOther lhs v =>
      have hih := ih none (env.update lhs (.liveInit v)) trivial
      change match (sccScanStmts none rest).2.2 with
        | true => ∃ k, execSccStmts h env (.assignOther lhs v :: rest) = .error k
        | false =>
          execSccStmts h env (.assignOther lhs v :: (sccScanStmts none rest).1) =
            execSccStmts h env (.assignOther lhs v :: rest) ∧
          ∀ env', execSccStmts h env (.assignOther lhs v :: rest) = .ok env' →
            PreConstValid env' (sccScanStmts none rest).2.1
      cases hs : (sccScanStmts none rest).2.2 with
      | true =>
        rw [hs] at hih
        rw [execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env lhs with
        | dead => exact ⟨.deadLocal, rfl⟩
        | liveUninit => exact hih
        | liveInit _ => exact hih
      | false =>
        rw [hs] at hih
        rw [execSccStmts_cons, execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env lhs with
        | dead => exact ⟨rfl, fun _ herr => nomatch herr⟩
        | liveUninit => exact hih
        | liveInit _ => exact hih
    | derefRead ptrLocal =>
      have hih := ih none env trivial
      change match (sccScanStmts none rest).2.2 with
        | true => ∃ k, execSccStmts h env (.derefRead ptrLocal :: rest) = .error k
        | false =>
          execSccStmts h env (.derefRead ptrLocal :: (sccScanStmts none rest).1) =
            execSccStmts h env (.derefRead ptrLocal :: rest) ∧
          ∀ env', execSccStmts h env (.derefRead ptrLocal :: rest) = .ok env' →
            PreConstValid env' (sccScanStmts none rest).2.1
      cases hs : (sccScanStmts none rest).2.2 with
      | true =>
        rw [hs] at hih
        rw [execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env ptrLocal with
        | dead => exact ⟨.deadLocal, rfl⟩
        | liveUninit => exact ⟨.uninitRead, rfl⟩
        | liveInit addr =>
          dsimp only
          cases h addr with
          | none => exact ⟨.nullDeref, rfl⟩
          | some _ => exact hih
      | false =>
        rw [hs] at hih
        rw [execSccStmts_cons, execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env ptrLocal with
        | dead => exact ⟨rfl, fun _ herr => nomatch herr⟩
        | liveUninit => exact ⟨rfl, fun _ herr => nomatch herr⟩
        | liveInit addr =>
          dsimp only
          cases h addr with
          | none => exact ⟨rfl, fun _ herr => nomatch herr⟩
          | some _ => exact hih
    | assignConst lhs c =>
      have hvalid' : PreConstValid (env.update lhs (.liveInit c)) (some (lhs, c)) :=
        LocalEnv.update_same env lhs (.liveInit c)
      have hih := ih (some (lhs, c)) (env.update lhs (.liveInit c)) hvalid'
      change match (sccScanStmts (some (lhs, c)) rest).2.2 with
        | true => ∃ k, execSccStmts h env (.assignConst lhs c :: rest) = .error k
        | false =>
          execSccStmts h env (.assignConst lhs c :: (sccScanStmts (some (lhs, c)) rest).1) =
            execSccStmts h env (.assignConst lhs c :: rest) ∧
          ∀ env', execSccStmts h env (.assignConst lhs c :: rest) = .ok env' →
            PreConstValid env' (sccScanStmts (some (lhs, c)) rest).2.1
      cases hs : (sccScanStmts (some (lhs, c)) rest).2.2 with
      | true =>
        rw [hs] at hih
        rw [execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env lhs with
        | dead => exact ⟨.deadLocal, rfl⟩
        | liveUninit => exact hih
        | liveInit _ => exact hih
      | false =>
        rw [hs] at hih
        rw [execSccStmts_cons, execSccStmts_cons]
        unfold stepSccStmt
        dsimp only
        cases env lhs with
        | dead => exact ⟨rfl, fun _ herr => nomatch herr⟩
        | liveUninit => exact hih
        | liveInit _ => exact hih
    | assume op =>
      have hscanEq :
          sccScanStmts pre (.assume op :: rest) =
            match tryGetConst op pre with
            | some c =>
              match natIsNonZero c with
              | true =>
                let r := sccScanStmts none rest
                (.nop :: r.1, r.2.1, r.2.2)
              | false => ([], none, true)
            | none =>
              let r := sccScanStmts none rest
              (.assume op :: r.1, r.2.1, r.2.2) := rfl
      rw [hscanEq]
      cases hget : tryGetConst op pre with
      | none =>
        dsimp only
        have hih := ih none env trivial
        cases hs : (sccScanStmts none rest).2.2 with
        | true =>
          rw [hs] at hih
          rw [execSccStmts_cons]
          unfold stepSccStmt
          dsimp only
          cases evalSccOp env op with
          | error k => exact ⟨k, rfl⟩
          | ok c =>
            dsimp only
            cases natIsNonZero c with
            | true => exact hih
            | false => exact ⟨.assumeFalse, rfl⟩
        | false =>
          rw [hs] at hih
          rw [execSccStmts_cons, execSccStmts_cons]
          unfold stepSccStmt
          dsimp only
          cases evalSccOp env op with
          | error k => exact ⟨rfl, fun _ herr => nomatch herr⟩
          | ok c =>
            dsimp only
            cases natIsNonZero c with
            | true => exact hih
            | false => exact ⟨rfl, fun _ herr => nomatch herr⟩
      | some c =>
        dsimp only
        have hev : evalSccOp env op = .ok c := tryGetConst_sound hvalid hget
        cases hnz : natIsNonZero c with
        | true =>
          dsimp only
          have hih := ih none env trivial
          cases hs : (sccScanStmts none rest).2.2 with
          | true =>
            rw [hs] at hih
            rw [execSccStmts_cons]
            unfold stepSccStmt
            dsimp only
            rw [hev]
            dsimp only
            rw [hnz]
            exact hih
          | false =>
            rw [hs] at hih
            rw [execSccStmts_cons, execSccStmts_cons]
            unfold stepSccStmt
            dsimp only
            rw [hev]
            dsimp only
            rw [hnz]
            exact hih
        | false =>
          dsimp only
          rw [execSccStmts_cons]
          unfold stepSccStmt
          dsimp only
          rw [hev]
          dsimp only
          rw [hnz]
          exact ⟨.assumeFalse, rfl⟩

/-- **Main Soundness & UB-Preservation Theorem for `SimplifyConstCondition` +
    `MirPatch::apply`**:
    For EVERY heap, EVERY environment, and EVERY basic block `blk`,
    `simplifyConstConditionBlock` satisfies `UbEquivalent` (and hence `Refines`):
    no UB is ever erased to a defined value, and no defined `.ok`/`.panic` is
    ever converted to UB. -/
theorem simplifyConstCondition_ubEquivalent (h : Heap) (env : LocalEnv) (blk : SccBlock) :
    UbEquivalent
      (evalSccBlock h env blk)
      (evalSccBlock h env (simplifyConstConditionBlock blk)) := by
  unfold simplifyConstConditionBlock evalSccBlock
  have hscan := sccScanStmts_sound h blk.stmts none env trivial
  cases hres : sccScanStmts none blk.stmts with
  | mk stmts' p =>
    cases p with
    | mk preEnd hitAssumeFalse =>
      rw [hres] at hscan
      dsimp only at hscan ⊢
      cases hitAssumeFalse with
      | true =>
        dsimp only at hscan ⊢
        rcases hscan with ⟨k, herr⟩
        rw [herr]
        trivial
      | false =>
        dsimp only at hscan ⊢
        rcases hscan with ⟨heqStmts, hPreValid⟩
        rw [heqStmts]
        cases hexec : execSccStmts h env blk.stmts with
        | error k => trivial
        | ok env' =>
          dsimp only
          have hv := hPreValid env' hexec
          cases hterm : blk.term with
          | goto t => rfl
          | unreachable => trivial
          | switchInt discr t0 t1 =>
            dsimp only
            cases hget : tryGetConst discr preEnd with
            | none =>
              dsimp only
              cases evalSccOp env' discr with
              | error k => trivial
              | ok c => rfl
            | some c =>
              dsimp only
              have hev := tryGetConst_sound hv hget
              rw [hev]
              rfl
          | assert cond expected target =>
            dsimp only
            cases hget : tryGetConst cond preEnd with
            | none => exact ubEquivalent_refl _
            | some c =>
              dsimp only
              have hev := tryGetConst_sound hv hget
              rw [hev]
              dsimp only
              cases hmatch : boolEq (natIsNonZero c) expected with
              | true => rfl
              | false =>
                dsimp only
                rw [hev]
                dsimp only
                rw [hmatch]
                trivial

theorem simplifyConstCondition_refines (h : Heap) (env : LocalEnv) (blk : SccBlock) :
    Refines
      (evalSccBlock h env blk)
      (evalSccBlock h env (simplifyConstConditionBlock blk)) :=
  ubEquivalent_implies_refines (simplifyConstCondition_ubEquivalent h env blk)

/-! ### Concrete Witnesses for `SimplifyConstCondition` Properties -/

def blkSwitchImmediate : SccBlock :=
  { stmts := [.assignConst 1 1]
    term := .switchInt (.copyLocal 1) 10 20 }

def blkSwitchIntervening : SccBlock :=
  { stmts := [.assignConst 1 1, .assignOther 2 0]
    term := .switchInt (.copyLocal 1) 10 20 }

theorem scc_immediate_folds_switch :
    (simplifyConstConditionBlock blkSwitchImmediate).term = .goto 20 := rfl

theorem scc_intervening_clears_has_place_const :
    (simplifyConstConditionBlock blkSwitchIntervening).term =
      .switchInt (.copyLocal 1) 10 20 := rfl

def blkAssertPass : SccBlock :=
  { stmts := [.assignConst 3 0]
    term := .assert (.copyLocal 3) false 1 }

def blkAssertFail : SccBlock :=
  { stmts := [.assignConst 3 1]
    term := .assert (.copyLocal 3) false 1 }

theorem scc_passing_assert_folds_to_goto :
    (simplifyConstConditionBlock blkAssertPass).term = .goto 1 := rfl

theorem scc_failing_assert_preserved :
    (simplifyConstConditionBlock blkAssertFail).term =
      .assert (.copyLocal 3) false 1 := rfl

/-- Counterexample proving why folding a failing `Assert` to `Unreachable`
    would be UNSOUND (`¬ Refines`): it turns a deterministic panic into UB. -/
theorem scc_folding_failing_assert_to_unreachable_unsound :
    let env := initEnv0.update 3 .liveUninit
    evalSccBlock nullHeap env blkAssertFail = .panic ∧
    ¬ Refines (evalSccBlock nullHeap env blkAssertFail) (.ub .unreachable) :=
  ⟨rfl, not_refines_panic_to_ub .unreachable⟩

/-- `Assume(false)` wipes prior `*null_ptr` UB via `MirPatch::apply`'s
    `bb.statements.clear()` (`patch.rs:323-325`): preserves `UbEquivalent`
    and `Refines`, but shifts `UbKind` from `.nullDeref` to `.unreachable`. -/
def blkAssumeFalseWipe : SccBlock :=
  { stmts := [.derefRead 1, .assume (.constVal 0)]
    term := .goto 1 }

theorem scc_assume_false_wipes_statements_and_shifts_ub_kind :
    let env := initEnv1 0
    (simplifyConstConditionBlock blkAssumeFalseWipe).stmts = [] ∧
    (simplifyConstConditionBlock blkAssumeFalseWipe).term = .unreachable ∧
    evalSccBlock nullHeap env blkAssumeFalseWipe = .ub .nullDeref ∧
    evalSccBlock nullHeap env (simplifyConstConditionBlock blkAssumeFalseWipe) = .ub .unreachable ∧
    UbEquivalent
      (evalSccBlock nullHeap env blkAssumeFalseWipe)
      (evalSccBlock nullHeap env (simplifyConstConditionBlock blkAssumeFalseWipe)) ∧
    ¬ ExactEq
      (evalSccBlock nullHeap env blkAssumeFalseWipe)
      (evalSccBlock nullHeap env (simplifyConstConditionBlock blkAssumeFalseWipe)) :=
  ⟨rfl, rfl, rfl, rfl, trivial, fun h => nomatch h⟩

/-- Trust-boundary theorem for `MirPatch::apply`'s `bb.statements.clear()`:
    if a hypothetical MIR statement could panic or diverge prior to `assume(false)`,
    clearing prior statements would turn `.panic` / `.diverged` into `.ub .unreachable`,
    violating `Refines`. Thus `patch.rs:323-325` relies critically on the MIR
    invariant that all `StatementKind` variants are non-panicking and terminating. -/
theorem assume_false_clear_requires_non_panicking_non_diverging_stmts :
    ¬ Refines .panic (.ub .unreachable) ∧ ¬ Refines .diverged (.ub .unreachable) :=
  ⟨not_refines_panic_to_ub .unreachable, not_refines_diverged_to_ub .unreachable⟩

end SimplifyConstCondition

/-! ============================================================================
    PART 5: `CostChecker` (`cost_checker.rs` + `inline.rs`)
    ============================================================================ -/

section CostChecker

/-- Exact cost constants from `compiler/rustc_mir_transform/src/cost_checker.rs:6-11`. -/
def INSTR_COST : Nat := 5
def CALL_PENALTY : Nat := 25
def LANDINGPAD_PENALTY : Nat := 50
def RESUME_PENALTY : Nat := 45
def LARGE_SWITCH_PENALTY : Nat := 20
def CONST_SWITCH_BONUS : Nat := 10

/-- Session flags read by `CostChecker` (`cost_checker.rs:66-72, 144-152`). -/
structure CostSessionFlags where
  inlineMirPreserveDebug : Option Bool
  ubChecks : Bool
  overflowChecks : Bool

def CostSessionFlags.preserveUbChecks (f : CostSessionFlags) : Bool :=
  match f.inlineMirPreserveDebug with
  | some b => b
  | none => f.ubChecks

def CostSessionFlags.preserveOverflowChecks (f : CostSessionFlags) : Bool :=
  match f.inlineMirPreserveDebug with
  | some b => b
  | none => f.overflowChecks

/-- Operand kinds relevant to `CostChecker::visit_operand` (`cost_checker.rs:63-81`). -/
inductive CostOperand where
  | ubChecks
  | other

/-- Statement kinds relevant to `CostChecker::visit_statement` (`cost_checker.rs:83-101`).
    Includes `assignZstConst` added in `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`
    (lines 92-96: zero cost). -/
inductive CostStmt where
  | intrinsicAssume
  | intrinsicCopyNonOverlapping
  | assignZstConst
  | assign (ops : List CostOperand)
  | noopMarker

/-- Terminator kinds relevant to `CostChecker::visit_terminator` & `is_call_like`
    (`cost_checker.rs:103-205`). -/
inductive CostTerm where
  | drop (needsDrop : Bool) (hasCleanup : Bool)
  | call (isIntrinsic : Bool) (hasCleanup : Bool) (ops : List CostOperand)
  | tailCall
  | switchInt (isConstOrRuntimeCheck : Bool) (numTargets : Nat) (discrOp : CostOperand)
  | assert (isOptionalOverflow : Bool) (hasCleanup : Bool)
  | unwindResume
  | inlineAsm (hasCleanup : Bool)
  | unreachable
  | goto
  | ret
  | unwindTerminate

/-- Exact mirror of `cost_checker.rs:189-205` `is_call_like`. -/
def isCallLike : CostTerm → Bool
  | .call _ _ _ | .tailCall | .drop _ _ | .assert _ _ | .inlineAsm _ => true
  | .goto | .switchInt _ _ _ | .unwindResume | .unwindTerminate | .ret | .unreachable => false

structure CostBlock where
  stmts : List CostStmt
  term : CostTerm

structure CostState where
  penalty : Nat
  bonus : Nat

def CostState.zero : CostState := { penalty := 0, bonus := 0 }

/-- Exact mirror of `CostChecker::cost` (`cost_checker.rs:49-51`):
    `usize::saturating_sub(self.penalty, self.bonus)` is identical to `Nat.sub`. -/
def CostState.cost (s : CostState) : Nat := s.penalty - s.bonus

def CostState.addPenalty (s : CostState) (p : Nat) : CostState :=
  { s with penalty := s.penalty + p }

def CostState.addBonus (s : CostState) (b : Nat) : CostState :=
  { s with bonus := s.bonus + b }

def visitCostOperand (f : CostSessionFlags) (s : CostState) : CostOperand → CostState
  | .ubChecks =>
    match f.preserveUbChecks with
    | false => s.addBonus CALL_PENALTY
    | true => s
  | .other => s

def visitCostOperands (f : CostSessionFlags) (s : CostState) (ops : List CostOperand) : CostState :=
  ops.foldl (visitCostOperand f) s

def visitCostStmt (f : CostSessionFlags) (s : CostState) : CostStmt → CostState
  | .intrinsicAssume => s.addPenalty INSTR_COST
  | .intrinsicCopyNonOverlapping => s.addPenalty CALL_PENALTY
  | .assignZstConst => s
  | .assign ops => visitCostOperands f (s.addPenalty INSTR_COST) ops
  | .noopMarker => s

def visitCostStmts (f : CostSessionFlags) (s : CostState) (stmts : List CostStmt) : CostState :=
  stmts.foldl (visitCostStmt f) s

def cleanupPenalty : Bool → Nat
  | true => LANDINGPAD_PENALTY
  | false => 0

def visitCostTerm (f : CostSessionFlags) (s : CostState) : CostTerm → CostState
  | .drop needsDrop hasCleanup =>
    match needsDrop with
    | true => s.addPenalty (CALL_PENALTY + cleanupPenalty hasCleanup)
    | false => s
  | .call isIntrinsic hasCleanup ops =>
    let base := match isIntrinsic with | true => INSTR_COST | false => CALL_PENALTY
    visitCostOperands f (s.addPenalty (base + cleanupPenalty hasCleanup)) ops
  | .tailCall => s.addPenalty CALL_PENALTY
  | .switchInt isConst numTargets discrOp =>
    let s1 :=
      match isConst with
      | true => s.addBonus CONST_SWITCH_BONUS
      | false =>
        match Nat.blt 3 numTargets with
        | true => s.addPenalty LARGE_SWITCH_PENALTY
        | false => s.addPenalty INSTR_COST
    visitCostOperand f s1 discrOp
  | .assert isOptOverflow hasCleanup =>
    let base :=
      match isOptOverflow, f.preserveOverflowChecks with
      | true, false => INSTR_COST
      | _, _ => CALL_PENALTY
    s.addPenalty (base + cleanupPenalty hasCleanup)
  | .unwindResume => s.addPenalty RESUME_PENALTY
  | .inlineAsm hasCleanup => s.addPenalty (INSTR_COST + cleanupPenalty hasCleanup)
  | .unreachable => s.addBonus INSTR_COST
  | .goto | .ret | .unwindTerminate => s

def visitCostBlock (f : CostSessionFlags) (s : CostState) (b : CostBlock) : CostState :=
  visitCostTerm f (visitCostStmts f s b.stmts) b.term

def visitCostBlocks (f : CostSessionFlags) (s : CostState) (bs : List CostBlock) : CostState :=
  bs.foldl (visitCostBlock f) s

def countCallLike (blocks : List CostBlock) : Nat :=
  blocks.foldr (fun b acc => (match isCallLike b.term with | true => 1 | false => 0) + acc) 0

/-- Exact mirror of `CostChecker::add_function_level_costs` (`cost_checker.rs:39-47`). -/
def addFunctionLevelCosts (blocks : List CostBlock) (s : CostState) : CostState :=
  match Nat.beq (countCallLike blocks) 1 with
  | true => s.addBonus CALL_PENALTY
  | false => s

/-- Full `CostChecker` evaluation over a reachable block list. -/
def evalCostChecker (f : CostSessionFlags) (blocks : List CostBlock) : CostState :=
  visitCostBlocks f (addFunctionLevelCosts blocks CostState.zero) blocks

/-- Exact mirror of `inline.rs:380-382`: `<= 3` basic blocks get `+ threshold / 4`. -/
def effectiveThreshold (baseThreshold numBlocks : Nat) : Nat :=
  match Nat.ble numBlocks 3 with
  | true => baseThreshold + baseThreshold / 4
  | false => baseThreshold

def shouldInline (f : CostSessionFlags) (baseThreshold : Nat) (blocks : List CostBlock) : Bool :=
  Nat.ble (evalCostChecker f blocks).cost (effectiveThreshold baseThreshold blocks.length)

/-! ### Algebraic & Monotonicity Theorems for `CostChecker` -/

theorem cost_monotone_penalty {s₁ s₂ : CostState}
    (hp : s₁.penalty ≤ s₂.penalty) (hb : s₂.bonus ≤ s₁.bonus) :
    s₁.cost ≤ s₂.cost :=
  Nat.le_trans (nat_sub_mono_left hp) (nat_sub_mono_right hb)

theorem cost_zero_when_bonus_ge_penalty (s : CostState) (h : s.penalty ≤ s.bonus) :
    s.cost = 0 :=
  nat_sub_eq_zero_of_le h

/-- `add_function_level_costs` single-call bonus exact cancellation:
    a single non-intrinsic call without cleanup contributes `+CALL_PENALTY` to
    `penalty` and `+CALL_PENALTY` to `bonus`, leaving net cost unchanged (`P - B`). -/
theorem single_call_bonus_cancels_call_penalty (P B : Nat) :
    ({ penalty := P + CALL_PENALTY, bonus := B + CALL_PENALTY } : CostState).cost =
      ({ penalty := P, bonus := B } : CostState).cost :=
  nat_add_sub_add_right P B CALL_PENALTY

/-- Two-call inlining cliff: moving from 1 call (with `+25` single-call bonus)
    to 2 calls (with `0` single-call bonus) on identical non-call penalty `P ≥ B`
    jumps net cost by **exactly `+50` (`2 * CALL_PENALTY`)** — `+25` for the
    second call PLUS `+25` lost single-call bonus. -/
theorem two_call_cliff_delta (P B : Nat) (hPB : B ≤ P) :
    let oneCall : CostState := { penalty := P + CALL_PENALTY, bonus := B + CALL_PENALTY }
    let twoCall : CostState := { penalty := P + CALL_PENALTY + CALL_PENALTY, bonus := B }
    twoCall.cost = oneCall.cost + 2 * CALL_PENALTY := by
  intro oneCall twoCall
  have h1 : oneCall.cost = P - B := single_call_bonus_cancels_call_penalty P B
  have h2 : twoCall.cost = (P - B) + (CALL_PENALTY + CALL_PENALTY) := by
    change (P + CALL_PENALTY + CALL_PENALTY) - B = (P - B) + (CALL_PENALTY + CALL_PENALTY)
    rw [Nat.add_assoc P CALL_PENALTY CALL_PENALTY]
    exact nat_sub_add_eq_add_sub hPB
  rw [h1, h2]
  rfl

/-- **Single-Call Inlining Non-Amplification Theorem**:
    Replacing 1 call-site in a caller containing `c ≥ 1` call-like terminators
    with a callee containing `k` call-like terminators yields `(c - 1) + k`
    call-like terminators. Total call-like count does NOT increase iff `k ≤ 1`. -/
theorem single_call_inlining_non_amplification (c k : Nat) (hc : 1 ≤ c) :
    (c - 1) + k ≤ c ↔ k ≤ 1 :=
  nat_pred_add_le_iff c k hc

theorem multi_call_inlining_strictly_amplifies (c k : Nat) (hc : 1 ≤ c) (hk : 2 ≤ k) :
    c < (c - 1) + k :=
  nat_pred_add_gt_of_ge_two c k hc hk

/-- Intrinsic exemption exact gap: replacing `k` regular calls by `k` intrinsics
    reduces penalty by exactly `k * (CALL_PENALTY - INSTR_COST) = 20 * k`. -/
theorem intrinsic_exemption_exact_gap (P B k : Nat) (hPB : B ≤ P) :
    let regState : CostState := { penalty := P + k * CALL_PENALTY, bonus := B }
    let intState : CostState := { penalty := P + k * INSTR_COST, bonus := B }
    regState.cost = intState.cost + k * (CALL_PENALTY - INSTR_COST) := by
  intro regState intState
  have hr : regState.cost = (P - B) + k * CALL_PENALTY :=
    nat_sub_add_eq_add_sub hPB
  have hi : intState.cost = (P - B) + k * INSTR_COST :=
    nat_sub_add_eq_add_sub hPB
  rw [hr, hi, Nat.add_assoc]
  have hmul : k * INSTR_COST + k * (CALL_PENALTY - INSTR_COST) = k * CALL_PENALTY := by
    rw [← Nat.mul_add]
    rfl
  rw [hmul]

/-- `RuntimeChecks::UbChecks` exact `+25` (`CALL_PENALTY`) cost delta when
    toggling `preserveUbChecks` from `false` to `true` (given `B + 25 ≤ P`). -/
theorem ub_checks_bonus_exact_delta (P B : Nat) (h : B + CALL_PENALTY ≤ P) :
    let withoutPreserve : CostState := { penalty := P, bonus := B + CALL_PENALTY }
    let withPreserve : CostState := { penalty := P, bonus := B }
    withPreserve.cost = withoutPreserve.cost + CALL_PENALTY := by
  intro withoutPreserve withPreserve
  change P - B = (P - (B + CALL_PENALTY)) + CALL_PENALTY
  have h1 : (P - (B + CALL_PENALTY)) + CALL_PENALTY = P - B := by
    rw [← Nat.sub_sub, Nat.sub_add_cancel]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact h)
  exact h1.symm

/-- Optional overflow-check `Assert` exact `+20 * m` delta for `m` optional
    overflow asserts when toggling `preserveOverflowChecks` from `false` to `true`. -/
theorem optional_overflow_check_exact_delta (P B m : Nat) (hPB : B ≤ P) :
    let withoutPreserve : CostState := { penalty := P + m * INSTR_COST, bonus := B }
    let withPreserve : CostState := { penalty := P + m * CALL_PENALTY, bonus := B }
    withPreserve.cost = withoutPreserve.cost + m * (CALL_PENALTY - INSTR_COST) :=
  intrinsic_exemption_exact_gap P B m hPB

/-- `assignZstConst` (added in `rust-lang/rust@137d1d49458b73b7b85d2c1599d8730886d65e47`,
    `cost_checker.rs:92-96`) contributes zero penalty. -/
theorem zst_const_assign_zero_cost (f : CostSessionFlags) (s : CostState) :
    visitCostStmt f s .assignZstConst = s := rfl

/-- Subtle interaction: an intrinsic `Call` terminator is STILL counted as
    `is_call_like = true` (`cost_checker.rs:192`)! Thus a 1-intrinsic callee
    gets `+5` penalty AND `+25` single-call bonus (net `-20` bonus!), whereas
    adding a second intrinsic loses the `+25` bonus (jumping by `+30`!). -/
theorem single_intrinsic_net_bonus_and_two_intrinsic_jump (P : Nat) (h25 : 25 ≤ P) :
    let oneIntr : CostState := { penalty := P + INSTR_COST, bonus := CALL_PENALTY }
    let twoIntr : CostState := { penalty := P + INSTR_COST + INSTR_COST, bonus := 0 }
    oneIntr.cost = (P - 25) + 5 ∧
    twoIntr.cost = oneIntr.cost + 30 := by
  intro oneIntr twoIntr
  have h1 : oneIntr.cost = (P - 25) + 5 := nat_sub_add_eq_add_sub h25
  have h2 : twoIntr.cost = P + 10 := by
    change (P + 5 + 5) - 0 = P + 10
    rw [Nat.sub_zero, Nat.add_assoc]
  have h3 : ((P - 25) + 5) + 30 = P + 10 := by
    rw [Nat.add_assoc, show (5 + 30 : Nat) = 25 + 10 from rfl,
        ← Nat.add_assoc, Nat.sub_add_cancel h25]
  exact ⟨h1, by rw [h2, h1, h3]⟩

/-! ### Exact Calibration Verification Against Live `rustc` Probe Callees -/

def repeatAssigns (n : Nat) : List CostStmt :=
  List.replicate n (.assign [])

def releaseFlags : CostSessionFlags :=
  { inlineMirPreserveDebug := some false, ubChecks := false, overflowChecks := false }

def preserveDebugFlags : CostSessionFlags :=
  { inlineMirPreserveDebug := some true, ubChecks := false, overflowChecks := false }

def probeOneCallBlocks : List CostBlock :=
  [ { stmts := repeatAssigns 20, term := .call false false [] },
    { stmts := repeatAssigns 2, term := .ret } ]

def probeTwoIntrinsicsBlocks : List CostBlock :=
  [ { stmts := repeatAssigns 19, term := .call true false [] },
    { stmts := [], term := .call true false [] },
    { stmts := repeatAssigns 2, term := .ret } ]

def probeTwoCallsBlocks : List CostBlock :=
  [ { stmts := repeatAssigns 19, term := .call false false [] },
    { stmts := [], term := .call false false [] },
    { stmts := repeatAssigns 2, term := .ret } ]

/-- Exact mechanized reproduction of all 3 live `rustc` threshold cliffs
    (`87->88` at `110`, `91->92` at `115`, `123->124` at `155`, and default `T=100`). -/
theorem probe_callees_exact_costs_and_cliffs :
    (evalCostChecker releaseFlags probeOneCallBlocks).cost = 110 ∧
    (evalCostChecker releaseFlags probeTwoIntrinsicsBlocks).cost = 115 ∧
    (evalCostChecker releaseFlags probeTwoCallsBlocks).cost = 155 ∧
    shouldInline releaseFlags 87 probeOneCallBlocks = false ∧
    shouldInline releaseFlags 88 probeOneCallBlocks = true ∧
    shouldInline releaseFlags 91 probeTwoIntrinsicsBlocks = false ∧
    shouldInline releaseFlags 92 probeTwoIntrinsicsBlocks = true ∧
    shouldInline releaseFlags 100 probeOneCallBlocks = true ∧
    shouldInline releaseFlags 100 probeTwoIntrinsicsBlocks = true ∧
    shouldInline releaseFlags 100 probeTwoCallsBlocks = false ∧
    shouldInline releaseFlags 123 probeTwoCallsBlocks = false ∧
    shouldInline releaseFlags 124 probeTwoCallsBlocks = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def probeFourOverflowBlocks : List CostBlock :=
  [ { stmts := repeatAssigns 13, term := .assert true false },
    { stmts := [], term := .assert true false },
    { stmts := [], term := .assert true false },
    { stmts := [], term := .assert true false },
    { stmts := [], term := .ret } ]

theorem probe_four_overflow_exact_delta :
    (evalCostChecker releaseFlags probeFourOverflowBlocks).cost = 85 ∧
    (evalCostChecker preserveDebugFlags probeFourOverflowBlocks).cost = 165 ∧
    (evalCostChecker preserveDebugFlags probeFourOverflowBlocks).cost -
      (evalCostChecker releaseFlags probeFourOverflowBlocks).cost = 80 :=
  ⟨rfl, rfl, rfl⟩

def probeUbChecksBlocks : List CostBlock :=
  [ { stmts := repeatAssigns 30, term := .switchInt false 2 .ubChecks },
    { stmts := [], term := .call false false [] },
    { stmts := [], term := .call false false [] },
    { stmts := [], term := .ret } ]

theorem probe_ub_checks_exact_delta :
    (evalCostChecker releaseFlags probeUbChecksBlocks).cost = 180 ∧
    (evalCostChecker preserveDebugFlags probeUbChecksBlocks).cost = 205 ∧
    (evalCostChecker preserveDebugFlags probeUbChecksBlocks).cost -
      (evalCostChecker releaseFlags probeUbChecksBlocks).cost = 25 :=
  ⟨rfl, rfl, rfl⟩

end CostChecker

end RustcMirBranchConstCost
