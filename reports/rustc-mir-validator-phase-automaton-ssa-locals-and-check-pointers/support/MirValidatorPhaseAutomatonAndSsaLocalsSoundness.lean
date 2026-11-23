/-!
# Soundness of `rustc` Phase-Indexed MIR Validation, `SsaLocals`, and `CheckPointers`

Self-contained constructive Lean 4 (`v4.34.1`) mechanization of the core invariants
governing three interdependent `rustc_mir_transform` modules audited against
`rust-lang/rust` commit `137d1d49458b73b7b85d2c1599d8730886d65e47` (and
cross-checked against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):

1. **Part I (`validate.rs` — `MirPhase` Lattice & Bipartite Unwind Automaton):**
   - Exact 6-phase linear order `MirPhase` (`Built < Analysis(Initial) <
     Analysis(PostCleanup) < Runtime(Initial) < Runtime(PostCleanup) <
     Runtime(Optimized)`).
   - Phase-indexed statement, rvalue, projection, and terminator ban predicates,
     proving monotone strengthening (`mirPhase_invariant_monotonicity`) for all
     monotone-ban constructs and across the entire `Runtime` dialect, while
     explicitly separating dialect-introduced constructs (`SetDiscriminant`,
     `AggregateKind::RawPtr`, pre-runtime `Subslice` ordering).
   - Exact 3-of-8 `(src.is_cleanup, dst.is_cleanup, EdgeKind)` transition matrix,
     `START_BLOCK` zero-predecessor invariant, `can_unwind` gate, and
     `cleanup_automaton_path_separation` (every valid CFG path from `START_BLOCK`
     crosses at most one `Unwind` edge, never returns from cleanup to normal
     blocks, and can only execute `Return` in Phase A).
   - Contracted cleanup-graph acyclicity and out-degree `<= 1` unique root
     termination (`check_cleanup_control_flow` in `validate.rs:168-244`).

2. **Part II (`ssa.rs` — `SsaLocals`, `Set1`, Dominance, `Freeze` Soundness,
   and `!Freeze` / `Move`-Deinitialization Counterexamples):**
   - Exact `Set1` semilattice (`Empty < One < Many`), `DefLocation`, and
     dominance over reachable blocks (`traversal::reverse_postorder`).
   - Concrete small-step operational model with `isFreeze : Nat -> Bool` and
     Rust shared-reference immutability (`r[undefined.alias]`,
     `r[interior-mut.unsafe-cell]`), proving `ssaLocals_freeze_shared_borrow_value_sound`
     and exhibiting constructive counterexamples `ssaLocals_nonFreeze_counterexample`
     (matching `Cell<u32>`) and `ssaLocals_move_deinit_counterexample` (matching
     Miri and Anneal's `deinitMovedPlace = true` semantics).

3. **Part III (`ssa.rs` — `compute_copy_classes` & `meet_copy_equivalence`):**
   - Exact finite-domain (`Fin n`) mechanization of RPO `compute_copy_classes`
     with `RETURN_PLACE` absorption of `LocalKind.temp` classes, `LocalKind.arg`
     isolation, and address-observability (`atMostOneBorrowed` per copy class,
     capturing the exact `copy_prop.rs:65-69` re-rooting of a borrowed temp into
     `RETURN_PLACE`).
   - Proofs of union-find idempotence (`computeCopyClasses_idempotent`),
     `RETURN_PLACE` fixed-point (`computeCopyClasses_return_place_fixed`),
     argument isolation (`computeCopyClasses_arg_never_return_place`), and
     unique-borrow preservation (`computeCopyClasses_at_most_one_borrowed`).
   - Exact in-place two-pass `meet_copy_equivalence` mechanization proving
     `meetCopyEquivalence_uniform_iff_all_copies`, class uniformity, monotone
     shrinking, idempotence, and a counterexample showing idempotence is
     necessary for two-pass uniformity.

4. **Part IV (`check_pointers.rs`, `check_alignment.rs`, `check_null.rs`):**
   - Preservation of `ValidCfg` edge invariants under block splitting with
     `UnwindAction.unreachable` and inherited `is_cleanup` bit.
   - Modular alignment equivalence (`aligned_base_iff_aligned_field`) justifying
     `BorrowedFieldProjectionMode::FollowProjections` on non-packed structs.

Purity guarantees (enforced by construction and verified by kernel audit):
- Zero unproven holes, zero classical choice, zero external-oracle tactics,
  zero partial definitions, and zero compiler-generated unsafe recursors.
-/

namespace MirValidatorSsaSoundness

/-! ## General Constructive Helpers (Zero Choice, Zero Unsafe Recursors) -/

/-- Pure structural equality on `Nat` (`Nat.beq`), avoiding `LawfulBEq` choice chains. -/
def natEq (a b : Nat) : Bool := Nat.beq a b

private theorem natEq_self (a : Nat) : natEq a a = true := by
  induction a with
  | zero => rfl
  | succ n ih => exact ih

private theorem natEq_true_iff (a b : Nat) : natEq a b = true ↔ a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ _ =>
      exact ⟨fun h => False.elim (Bool.noConfusion h), fun h => False.elim (Nat.noConfusion h)⟩
  | succ n ih =>
    cases b with
    | zero =>
      exact ⟨fun h => False.elim (Bool.noConfusion h), fun h => False.elim (Nat.noConfusion h)⟩
    | succ m =>
      constructor
      · intro h
        exact congrArg Nat.succ ((ih m).mp h)
      · intro h
        injection h with hnm
        exact (ih m).mpr hnm

private theorem natEq_false_iff (a b : Nat) : natEq a b = false ↔ a ≠ b := by
  constructor
  · intro h heq
    subst heq
    have hr : natEq a a = true := natEq_self a
    rw [hr] at h
    cases h
  · intro hne
    cases hb : natEq a b with
    | false => rfl
    | true => exact False.elim (hne ((natEq_true_iff a b).mp hb))

private theorem finEq_self {n : Nat} (a : Fin n) : natEq a.val a.val = true :=
  natEq_self a.val

private theorem finEq_true_iff {n : Nat} (a b : Fin n) : natEq a.val b.val = true ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext ((natEq_true_iff a.val b.val).mp h)
  · intro h
    subst h
    exact natEq_self a.val

private theorem finEq_false_iff {n : Nat} (a b : Fin n) : natEq a.val b.val = false ↔ a ≠ b := by
  constructor
  · intro h heq
    subst heq
    have hr : natEq a.val a.val = true := natEq_self a.val
    rw [hr] at h
    cases h
  · intro hne
    cases hb : natEq a.val b.val with
    | false => rfl
    | true => exact False.elim (hne (Fin.ext ((natEq_true_iff a.val b.val).mp hb)))

private theorem false_of_mono_imp {a b : Bool} (himp : a = true → b = true) (hb : b = false) :
    a = false := by
  cases ha : a with
  | false => rfl
  | true =>
    have hbt := himp ha
    rw [hbt] at hb
    cases hb

/-!
================================================================================
## Part I: `MirPhase` Lattice, Monotone Invariants, and Bipartite Unwind Automaton
================================================================================
-/

/-- Exact 6-point phase lattice from `compiler/rustc_middle/src/mir/syntax.rs:44-144`. -/
inductive MirPhase where
  | built : MirPhase
  | analysisInitial : MirPhase
  | analysisPostCleanup : MirPhase
  | runtimeInitial : MirPhase
  | runtimePostCleanup : MirPhase
  | runtimeOptimized : MirPhase

/-- Numeric rank matching Rust's derived `Ord` on `MirPhase`. -/
def MirPhase.rank : MirPhase → Nat
  | .built               => 0
  | .analysisInitial     => 1
  | .analysisPostCleanup => 2
  | .runtimeInitial      => 3
  | .runtimePostCleanup  => 4
  | .runtimeOptimized    => 5

/-- Propositional phase ordering (`p ≤ q` in `rustc`). -/
def MirPhase.le (p q : MirPhase) : Prop := p.rank ≤ q.rank

/-- Boolean phase ordering (`p <= q` in `validate.rs`). -/
def MirPhase.ble (p q : MirPhase) : Bool := Nat.ble p.rank q.rank

/-- Predicate identifying the `Runtime` dialect (`MirPhase::Runtime(_)`). -/
def MirPhase.isRuntime : MirPhase → Bool
  | .runtimeInitial | .runtimePostCleanup | .runtimeOptimized => true
  | _ => false

theorem MirPhase.rank_injective {p q : MirPhase} (h : p.rank = q.rank) : p = q := by
  cases p <;> cases q <;> first | rfl | cases h

theorem MirPhase.le_refl (p : MirPhase) : MirPhase.le p p :=
  Nat.le_refl p.rank

theorem MirPhase.le_trans {p q r : MirPhase} (h1 : MirPhase.le p q) (h2 : MirPhase.le q r) :
    MirPhase.le p r :=
  Nat.le_trans h1 h2

theorem MirPhase.le_antisymm {p q : MirPhase} (h1 : MirPhase.le p q) (h2 : MirPhase.le q p) :
    p = q :=
  MirPhase.rank_injective (Nat.le_antisymm h1 h2)

theorem MirPhase.le_total (p q : MirPhase) : MirPhase.le p q ∨ MirPhase.le q p :=
  Nat.le_total p.rank q.rank

theorem MirPhase.ble_true_iff (p q : MirPhase) : MirPhase.ble p q = true ↔ MirPhase.le p q := by
  unfold MirPhase.ble MirPhase.le
  exact Iff.of_eq Nat.ble_eq

theorem MirPhase.isRuntime_iff_ge_runtimeInitial (p : MirPhase) :
    p.isRuntime = true ↔ MirPhase.le .runtimeInitial p := by
  cases p with
  | built =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | analysisInitial =>
    constructor
    · intro h; cases h
    · intro h; cases h; rename_i h1; cases h1
  | analysisPostCleanup =>
    constructor
    · intro h; cases h
    · intro h; cases h; rename_i h1; cases h1; rename_i h2; cases h2
  | runtimeInitial =>
    constructor
    · intro _; exact Nat.le_refl 3
    · intro _; rfl
  | runtimePostCleanup =>
    constructor
    · intro _; exact Nat.le_succ 3
    · intro _; rfl
  | runtimeOptimized =>
    constructor
    · intro _; exact Nat.le_trans (Nat.le_succ 3) (Nat.le_succ 4)
    · intro _; rfl

/-- Abstract MIR statement kinds modeled after `validate.rs:294-338, 1482-1597`. -/
inductive StmtKind where
  | assign : StmtKind
  | storageLive : StmtKind
  | storageDead : StmtKind
  | fakeRead : StmtKind
  | ascribeUserType : StmtKind
  | setDiscriminant : StmtKind
  | coverageAnalysisOnly : StmtKind
  | coverageVirtualCounter : StmtKind
  | backwardIncompatibleDropHint : StmtKind
  | placeMention : StmtKind
  | nop : StmtKind

/-- Abstract MIR rvalue kinds modeled after `validate.rs:1018-1480`. -/
inductive RvalueKind where
  | useOp : RvalueKind
  | copyForDeref : RvalueKind
  | refShared : RvalueKind
  | refMut : RvalueKind
  | refFake : RvalueKind
  | rawPtr : RvalueKind
  | aggregateAdt : RvalueKind
  | aggregateRawPtr : RvalueKind
  | ptrCoercionMutToConst : RvalueKind
  | ptrCoercionArrayToPtr : RvalueKind
  | castOther : RvalueKind

/-- Abstract MIR projection elements modeled after `validate.rs:668-912, 952-1016`. -/
inductive ProjElem where
  | derefNonBox : ProjElem
  | derefBox : ProjElem
  | field : ProjElem
  | downcast : ProjElem
  | index : ProjElem
  | constantIndex : ProjElem
  | subslice : ProjElem
  | opaqueCast : ProjElem

/-- Place usage context distinguishing `VarDebugInfo` exemption (`validate.rs:958`). -/
inductive PlaceUseCtx where
  | runtimeUse : PlaceUseCtx
  | varDebugInfo : PlaceUseCtx

/-- Terminator kinds modeled after `validate.rs:340-541`. -/
inductive TermKind where
  | goto : TermKind
  | switchInt : TermKind
  | call : TermKind
  | callCriticalEdge : TermKind
  | callUninlinedForceInline : TermKind
  | tailCall : TermKind
  | dropSync : TermKind
  | dropAsync : TermKind
  | assert_ : TermKind
  | yield : TermKind
  | falseEdge : TermKind
  | falseUnwind : TermKind
  | coroutineDrop : TermKind
  | unwindResume : TermKind
  | unwindTerminate : TermKind
  | return_ : TermKind
  | unreachable : TermKind

/-- Monotone-ban statement predicate (`validate.rs:296-326`). -/
def stmtMonotoneBanAt (p : MirPhase) : StmtKind → Bool
  | .fakeRead             => MirPhase.ble .runtimeInitial p
  | .ascribeUserType      => MirPhase.ble .runtimeInitial p
  | .coverageAnalysisOnly => MirPhase.ble .analysisPostCleanup p
  | _                     => false

/-- Full statement ban predicate at phase `p` (`validate.rs:296-335`). -/
def stmtForbiddenAt (p : MirPhase) : StmtKind → Bool
  | .setDiscriminant => !MirPhase.ble .runtimeInitial p
  | s                => stmtMonotoneBanAt p s

/-- Monotone-ban rvalue predicate (`validate.rs:1028-1032, 1157-1164, 1326-1345`). -/
def rvalueMonotoneBanAt (p : MirPhase) : RvalueKind → Bool
  | .copyForDeref          => MirPhase.ble .runtimeInitial p
  | .refFake               => MirPhase.ble .runtimeInitial p
  | .ptrCoercionMutToConst => MirPhase.ble .analysisPostCleanup p
  | .ptrCoercionArrayToPtr => MirPhase.ble .analysisPostCleanup p
  | _                      => false

/-- Full rvalue ban predicate at phase `p`, including `AggregateKind::RawPtr`
(`validate.rs:1116-1121`, allowed only in `MirPhase::Runtime(_)`). -/
def rvalueForbiddenAt (p : MirPhase) : RvalueKind → Bool
  | .aggregateRawPtr => !p.isRuntime
  | r                => rvalueMonotoneBanAt p r

/-- Does a projection list contain any `Deref` (Box or non-Box) element? -/
def hasAnyDeref (xs : List ProjElem) : Bool :=
  xs.any (fun e => match e with | .derefNonBox | .derefBox => true | _ => false)

/-- Does a projection list contain `Deref` at index `>= 1` (`place.projection[1..]`)? -/
def hasLaterDeref : List ProjElem → Bool
  | [] => false
  | _ :: tl => hasAnyDeref tl

/-- Does a projection list contain a `Box` deref anywhere? -/
def hasBoxDeref (xs : List ProjElem) : Bool :=
  xs.any (fun e => match e with | .derefBox => true | _ => false)

/-- Does a projection list contain `OpaqueCast`? -/
def hasOpaqueCast (xs : List ProjElem) : Bool :=
  xs.any (fun e => match e with | .opaqueCast => true | _ => false)

/-- Does a projection list satisfy `Downcast` must be immediately followed by `Field`
(`validate.rs:968-980`, enforced in all phases)? Implemented as a 2-state fold. -/
def downcastFollowedByField (xs : List ProjElem) : Bool :=
  let res := xs.foldl
    (fun (st : Bool × Bool) e =>
      match st.2 with
      | true =>
        match e with
        | .field => (st.1, false)
        | _ => (false, false)
      | false =>
        match e with
        | .downcast => (st.1, true)
        | _ => (st.1, false))
    (true, false)
  res.1 && !res.2

/-- Does a projection list contain `ConstantIndex` or `Subslice` after a `Subslice`
(`validate.rs:996-1013`, forbidden strictly before `Runtime(Initial)`)? -/
def hasSubsliceViolation (xs : List ProjElem) : Bool :=
  (xs.foldl
    (fun (st : Bool × Bool) e =>
      match st.1 with
      | true =>
        match e with
        | .constantIndex | .subslice => (true, true)
        | _ => (true, st.2)
      | false =>
        match e with
        | .subslice => (true, st.2)
        | _ => (false, st.2))
    (false, false)).2

/-- Monotone-ban projection check at phase `p` (`validate.rs:676-684, 882-889, 956-980`). -/
def placeMonotoneBanAt (p : MirPhase) (ctx : PlaceUseCtx) (proj : List ProjElem) : Bool :=
  let rt := MirPhase.ble .runtimeInitial p
  let badLaterDeref :=
    match ctx with
    | .varDebugInfo => false
    | .runtimeUse   => rt && hasLaterDeref proj
  let badBoxDeref := rt && hasBoxDeref proj
  let badOpaque := rt && hasOpaqueCast proj
  let badDowncast := !downcastFollowedByField proj
  badLaterDeref || badBoxDeref || badOpaque || badDowncast

/-- Full projection ban check including pre-runtime `Subslice` ordering (`validate.rs:996-1013`). -/
def placeForbiddenAt (p : MirPhase) (ctx : PlaceUseCtx) (proj : List ProjElem) : Bool :=
  placeMonotoneBanAt p ctx proj || (!MirPhase.ble .runtimeInitial p && hasSubsliceViolation proj)

/-- Monotone-ban terminator predicate (`validate.rs:369-515`). -/
def termMonotoneBanAt (p : MirPhase) : TermKind → Bool
  | .dropAsync                => MirPhase.ble .runtimeInitial p
  | .yield                    => MirPhase.ble .runtimeInitial p
  | .falseEdge                => MirPhase.ble .runtimeInitial p
  | .falseUnwind              => MirPhase.ble .runtimeInitial p
  | .coroutineDrop            => MirPhase.ble .runtimeInitial p
  | .callCriticalEdge         => MirPhase.ble .runtimeOptimized p
  | .callUninlinedForceInline => MirPhase.ble .runtimeOptimized p
  | _                         => false

private theorem ble_monotone_right {t p q : MirPhase}
    (hpq : MirPhase.le p q) (htp : MirPhase.ble t p = true) :
    MirPhase.ble t q = true := by
  have h1 : MirPhase.le t p := (MirPhase.ble_true_iff t p).mp htp
  exact (MirPhase.ble_true_iff t q).mpr (MirPhase.le_trans h1 hpq)

theorem stmtMonotoneBanAt_mono {p q : MirPhase} (hpq : MirPhase.le p q) (s : StmtKind) :
    stmtMonotoneBanAt p s = true → stmtMonotoneBanAt q s = true := by
  cases s <;> intro h
  · cases h
  · cases h
  · cases h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · cases h
  · exact ble_monotone_right hpq h
  · cases h
  · cases h
  · cases h
  · cases h

theorem rvalueMonotoneBanAt_mono {p q : MirPhase} (hpq : MirPhase.le p q) (r : RvalueKind) :
    rvalueMonotoneBanAt p r = true → rvalueMonotoneBanAt q r = true := by
  cases r <;> intro h
  · cases h
  · exact ble_monotone_right hpq h
  · cases h
  · cases h
  · exact ble_monotone_right hpq h
  · cases h
  · cases h
  · cases h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · cases h

theorem termMonotoneBanAt_mono {p q : MirPhase} (hpq : MirPhase.le p q) (t : TermKind) :
    termMonotoneBanAt p t = true → termMonotoneBanAt q t = true := by
  cases t <;> intro h
  · cases h
  · cases h
  · cases h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · cases h
  · cases h
  · exact ble_monotone_right hpq h
  · cases h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · exact ble_monotone_right hpq h
  · cases h
  · cases h
  · cases h
  · cases h

theorem placeMonotoneBanAt_mono {p q : MirPhase} (hpq : MirPhase.le p q)
    (ctx : PlaceUseCtx) (proj : List ProjElem) :
    placeMonotoneBanAt p ctx proj = true → placeMonotoneBanAt q ctx proj = true := by
  unfold placeMonotoneBanAt
  intro h
  cases hrt : MirPhase.ble .runtimeInitial p with
  | false =>
    cases ctx <;> simp [hrt] at h
    · cases hq : MirPhase.ble .runtimeInitial q <;> simp [h]
    · cases hq : MirPhase.ble .runtimeInitial q <;> simp [h]
  | true =>
    have hq : MirPhase.ble .runtimeInitial q = true := ble_monotone_right hpq hrt
    cases ctx <;> simp [hrt, hq] at h ⊢ <;> exact h

/-- Abstract MIR body items audited by phase-indexed rules. -/
structure PhaseAuditBody where
  stmts : List StmtKind
  rvalues : List RvalueKind
  places : List (PlaceUseCtx × List ProjElem)
  terms : List TermKind

/-- Monotone-ban validity at phase `p`. -/
def MonotoneValidAt (p : MirPhase) (b : PhaseAuditBody) : Prop :=
  (∀ s, s ∈ b.stmts → stmtMonotoneBanAt p s = false) ∧
  (∀ r, r ∈ b.rvalues → rvalueMonotoneBanAt p r = false) ∧
  (∀ cp, cp ∈ b.places → placeMonotoneBanAt p cp.1 cp.2 = false) ∧
  (∀ t, t ∈ b.terms → termMonotoneBanAt p t = false)

/-- Full phase validity at phase `p` (including dialect-introduced constructs). -/
def FullValidAt (p : MirPhase) (b : PhaseAuditBody) : Prop :=
  (∀ s, s ∈ b.stmts → stmtForbiddenAt p s = false) ∧
  (∀ r, r ∈ b.rvalues → rvalueForbiddenAt p r = false) ∧
  (∀ cp, cp ∈ b.places → placeForbiddenAt p cp.1 cp.2 = false) ∧
  (∀ t, t ∈ b.terms → termMonotoneBanAt p t = false)

/-- **Main Theorem 1a (`mirPhase_invariant_monotonicity`):**
1. Across the entire 6-phase lattice (`p ≤ q`), every monotone-ban invariant
   strengthens monotonically: `MonotoneValidAt q b → MonotoneValidAt p b`.
2. Within the `Runtime` dialect (`Runtime(Initial) ≤ p ≤ q`), all `Validator`
   phase invariants (including `SetDiscriminant`, `AggregateKind::RawPtr`, and
   `Subslice` rules) strengthen monotonically: `FullValidAt q b → FullValidAt p b`. -/
theorem mirPhase_invariant_monotonicity :
    (∀ p q b, MirPhase.le p q → MonotoneValidAt q b → MonotoneValidAt p b) ∧
    (∀ p q b, MirPhase.le .runtimeInitial p → MirPhase.le p q →
      FullValidAt q b → FullValidAt p b) := by
  constructor
  · intro p q b hpq ⟨hs, hr, hp, ht⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hmem
      exact false_of_mono_imp (stmtMonotoneBanAt_mono hpq s) (hs s hmem)
    · intro r hmem
      exact false_of_mono_imp (rvalueMonotoneBanAt_mono hpq r) (hr r hmem)
    · intro cp hmem
      exact false_of_mono_imp (placeMonotoneBanAt_mono hpq cp.1 cp.2) (hp cp hmem)
    · intro t hmem
      exact false_of_mono_imp (termMonotoneBanAt_mono hpq t) (ht t hmem)
  · intro p q b hrt hpq ⟨hs, hr, hp, ht⟩
    have hbleP : MirPhase.ble .runtimeInitial p = true :=
      (MirPhase.ble_true_iff .runtimeInitial p).mpr hrt
    have hbleQ : MirPhase.ble .runtimeInitial q = true :=
      ble_monotone_right hpq hbleP
    have hisRtP : p.isRuntime = true :=
      (MirPhase.isRuntime_iff_ge_runtimeInitial p).mpr hrt
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hmem
      have hsq := hs s hmem
      cases s with
      | setDiscriminant =>
        unfold stmtForbiddenAt
        rw [hbleP]
        rfl
      | _ =>
        unfold stmtForbiddenAt at hsq ⊢
        exact false_of_mono_imp (stmtMonotoneBanAt_mono hpq _) hsq
    · intro r hmem
      have hrq := hr r hmem
      cases r with
      | aggregateRawPtr =>
        unfold rvalueForbiddenAt
        rw [hisRtP]
        rfl
      | _ =>
        unfold rvalueForbiddenAt at hrq ⊢
        exact false_of_mono_imp (rvalueMonotoneBanAt_mono hpq _) hrq
    · intro cp hmem
      have hpq' := hp cp hmem
      unfold placeForbiddenAt at hpq' ⊢
      rw [hbleP]
      rw [hbleQ] at hpq'
      simp at hpq' ⊢
      exact false_of_mono_imp (placeMonotoneBanAt_mono hpq cp.1 cp.2) hpq'
    · intro t hmem
      exact false_of_mono_imp (termMonotoneBanAt_mono hpq t) (ht t hmem)

/-- Non-monotonicity & exemption witnesses across the `Analysis -> Runtime` boundary. -/
theorem dialect_boundary_witnesses :
    stmtForbiddenAt .analysisPostCleanup .setDiscriminant = true ∧
    stmtForbiddenAt .runtimeInitial .setDiscriminant = false ∧
    rvalueForbiddenAt .analysisPostCleanup .aggregateRawPtr = true ∧
    rvalueForbiddenAt .runtimeInitial .aggregateRawPtr = false ∧
    placeMonotoneBanAt .runtimeOptimized .runtimeUse [.field, .derefNonBox] = true ∧
    placeMonotoneBanAt .runtimeOptimized .varDebugInfo [.field, .derefNonBox] = false ∧
    placeMonotoneBanAt .built .runtimeUse [.downcast] = true ∧
    placeMonotoneBanAt .built .runtimeUse [.downcast, .field] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Bipartite `(is_cleanup, EdgeKind)` Unwind Automaton (`validate.rs:139-275, 516-537`) -/

/-- Exact `EdgeKind` enum from `validate.rs:26-29`. -/
inductive EdgeKind where
  | unwind : EdgeKind
  | normal : EdgeKind

/-- Exact `UnwindAction` enum from `rustc_middle::mir::UnwindAction`. -/
inductive UnwindAction where
  | cleanup (target : Nat) : UnwindAction
  | continue_ : UnwindAction
  | terminateInCleanup : UnwindAction
  | terminateAbi : UnwindAction
  | unreachable : UnwindAction

/-- Exact 3-of-8 transition matrix from `CfgChecker::check_edge` (`validate.rs:145-162`). -/
def validEdgeTransition (srcCleanup dstCleanup : Bool) (kind : EdgeKind) : Bool :=
  match srcCleanup, dstCleanup, kind with
  | false, false, .normal => true
  | true,  true,  .normal => true
  | false, true,  .unwind => true
  | _,     _,     _       => false

/-- Exhaustive verification of the 3-of-8 valid / 5-of-8 forbidden transition matrix. -/
theorem validEdgeTransition_exact_3_of_8 :
    validEdgeTransition false false .normal = true ∧
    validEdgeTransition true  true  .normal = true ∧
    validEdgeTransition false true  .unwind = true ∧
    validEdgeTransition false true  .normal = false ∧
    validEdgeTransition true  false .normal = false ∧
    validEdgeTransition false false .unwind = false ∧
    validEdgeTransition true  false .unwind = false ∧
    validEdgeTransition true  true  .unwind = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact `CfgChecker::check_unwind_edge` legality predicate (`validate.rs:246-275`). -/
def validUnwindAction (srcCleanup canUnwind : Bool) (dstIsCleanup : Nat → Bool) :
    UnwindAction → Bool
  | .cleanup dst        => !srcCleanup && dstIsCleanup dst
  | .continue_          => !srcCleanup && canUnwind
  | .terminateInCleanup => srcCleanup
  | .terminateAbi       => true
  | .unreachable        => true

/-- CFG exit terminators relevant to cleanup separation (`validate.rs:516-537`). -/
inductive ExitKind where
  | return_ : ExitKind
  | unwindResume : ExitKind
  | unwindTerminate : ExitKind
  | unreachable : ExitKind
  | nonExit : ExitKind

/-- Exact exit-terminator legality from `validate.rs:516-537`. -/
def validExitKind (bbCleanup canUnwind : Bool) : ExitKind → Bool
  | .return_         => !bbCleanup
  | .unwindResume    => bbCleanup && canUnwind
  | .unwindTerminate => bbCleanup
  | .unreachable     => true
  | .nonExit         => true

/-- Directed CFG edge with explicit `EdgeKind`. -/
structure CfgEdge where
  src : Nat
  dst : Nat
  kind : EdgeKind

/-- Abstract CFG with `START_BLOCK = 0`, `isCleanup` labels, `canUnwind` flag,
edges, and per-block exit classification. -/
structure MirCfg where
  numBlocks : Nat
  isCleanup : Nat → Bool
  canUnwind : Bool
  edges : List CfgEdge
  exitOf : Nat → ExitKind

/-- Well-formedness of a `MirCfg` as enforced by `CfgChecker` (`validate.rs:139-275, 516-537`). -/
structure ValidCfg (cfg : MirCfg) : Prop where
  startInBounds : 0 < cfg.numBlocks
  startNotCleanup : cfg.isCleanup 0 = false
  noStartPred : ∀ e, e ∈ cfg.edges → e.dst ≠ 0
  edgesInBounds : ∀ e, e ∈ cfg.edges → e.src < cfg.numBlocks ∧ e.dst < cfg.numBlocks
  edgesValid : ∀ e, e ∈ cfg.edges →
    validEdgeTransition (cfg.isCleanup e.src) (cfg.isCleanup e.dst) e.kind = true
  exitsValid : ∀ bb, bb < cfg.numBlocks →
    validExitKind (cfg.isCleanup bb) cfg.canUnwind (cfg.exitOf bb) = true

/-- A valid finite execution path in `cfg` from `a` to `b`, recording traversed `EdgeKind`s. -/
inductive CfgPath (cfg : MirCfg) : Nat → Nat → List EdgeKind → Prop where
  | nil (bb : Nat) (hbb : bb < cfg.numBlocks) : CfgPath cfg bb bb []
  | snoc {a b c : Nat} {ks : List EdgeKind} {e : CfgEdge}
      (hpath : CfgPath cfg a b ks)
      (he : e ∈ cfg.edges)
      (hsrc : e.src = b)
      (hdst : e.dst = c) :
      CfgPath cfg a c (ks ++ [e.kind])

/-- Count of `EdgeKind.unwind` transitions in an edge-kind trace (zero-recursor `foldr`). -/
def countUnwind (xs : List EdgeKind) : Nat :=
  xs.foldr (fun k acc => match k with | .unwind => acc + 1 | .normal => acc) 0

theorem countUnwind_append (xs ys : List EdgeKind) :
    countUnwind (xs ++ ys) = countUnwind xs + countUnwind ys := by
  induction xs with
  | nil =>
    change countUnwind ys = 0 + countUnwind ys
    rw [Nat.zero_add]
  | cons k tl ih =>
    cases k with
    | normal => exact ih
    | unwind =>
      change countUnwind (tl ++ ys) + 1 = (countUnwind tl + 1) + countUnwind ys
      rw [ih, Nat.add_assoc, Nat.add_comm (countUnwind ys) 1, ← Nat.add_assoc]

/-- Inductive predicate asserting every transition in `ks` is `EdgeKind.normal`. -/
inductive AllNormal : List EdgeKind → Prop where
  | nil : AllNormal []
  | cons {tl : List EdgeKind} : AllNormal tl → AllNormal (.normal :: tl)

theorem allNormal_append {xs ys : List EdgeKind} (hx : AllNormal xs) (hy : AllNormal ys) :
    AllNormal (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons _ ih => exact .cons ih

theorem countUnwind_zero_of_allNormal {xs : List EdgeKind} (h : AllNormal xs) :
    countUnwind xs = 0 := by
  induction h with
  | nil => rfl
  | cons _ ih => exact ih

/-- Phase-decomposed trace invariant:
- Phase A (`cleanup = false`): every traversed edge is `Normal` (`countUnwind = 0`).
- Phase B (`cleanup = true`): the trace splits into `ks₁ ++ (.unwind :: ks₂)` with
  `AllNormal ks₁` and `AllNormal ks₂` (so `countUnwind = 1`). -/
def BipartiteTraceShape (cleanup : Bool) (ks : List EdgeKind) : Prop :=
  match cleanup with
  | false => AllNormal ks
  | true  => ∃ ks₁ ks₂, ks = ks₁ ++ (.unwind :: ks₂) ∧ AllNormal ks₁ ∧ AllNormal ks₂

theorem cfgPath_dst_inBounds {cfg : MirCfg} (hv : ValidCfg cfg)
    {a b : Nat} {ks : List EdgeKind} (hp : CfgPath cfg a b ks) : b < cfg.numBlocks := by
  cases hp with
  | nil hbb => exact hbb
  | snoc _ he _ hdst =>
    rw [← hdst]
    exact (hv.edgesInBounds _ he).2

/-- Non-empty paths from `START_BLOCK` never re-enter `START_BLOCK`. -/
theorem start_block_unreachable_after_step {cfg : MirCfg} (hv : ValidCfg cfg)
    {dst : Nat} {ks : List EdgeKind}
    (hp : CfgPath cfg 0 dst ks) (hne : ks ≠ []) : dst ≠ 0 := by
  cases hp with
  | nil _ => exact False.elim (hne rfl)
  | snoc _ he _ hdst =>
    rw [← hdst]
    exact hv.noStartPred _ he

/-- Sticky cleanup invariant: from any cleanup block, every reachable block is a
cleanup block and every traversed edge is `Normal`. -/
theorem cleanup_sticky_under_valid_edges {cfg : MirCfg} (hv : ValidCfg cfg)
    {a b : Nat} {ks : List EdgeKind}
    (hp : CfgPath cfg a b ks) (ha : cfg.isCleanup a = true) :
    cfg.isCleanup b = true ∧ AllNormal ks := by
  induction hp with
  | nil _ => exact ⟨ha, .nil⟩
  | @snoc b c ks e _ he hsrc hdst ih =>
    have ⟨hb, hnorm⟩ := ih
    have hed := hv.edgesValid e he
    rw [hsrc, hdst, hb] at hed
    cases hc : cfg.isCleanup c with
    | false =>
      cases ek : e.kind <;> rw [hc, ek] at hed <;> cases hed
    | true =>
      cases ek : e.kind with
      | unwind =>
        rw [hc, ek] at hed
        cases hed
      | normal =>
        exact ⟨rfl, allNormal_append hnorm (.cons .nil)⟩

/-- **Main Theorem 1b (`cleanup_automaton_path_separation`):**
Every valid execution path from `START_BLOCK` satisfies:
1. **Exact two-phase decomposition (`BipartiteTraceShape`):**
   - While in `isCleanup = false` (Phase A), every edge is `Normal` (`countUnwind = 0`).
   - While in `isCleanup = true` (Phase B), the trace has the exact form
     `ks₁ ++ [.unwind] ++ ks₂` with `AllNormal ks₁` and `AllNormal ks₂` (`countUnwind = 1`).
2. **At-most-one unwind crossing:** `countUnwind ks = if cfg.isCleanup dst then 1 else 0`.
3. **Exit separation:**
   - `Return` implies `isCleanup dst = false` and `countUnwind ks = 0`.
   - `UnwindResume` implies `isCleanup dst = true`, `countUnwind ks = 1`, and `canUnwind = true`.
   - `UnwindTerminate` implies `isCleanup dst = true` and `countUnwind ks = 1`. -/
theorem cleanup_automaton_path_separation {cfg : MirCfg} (hv : ValidCfg cfg)
    {dst : Nat} {ks : List EdgeKind} (hp : CfgPath cfg 0 dst ks) :
    BipartiteTraceShape (cfg.isCleanup dst) ks ∧
    countUnwind ks = (if cfg.isCleanup dst then 1 else 0) ∧
    (cfg.exitOf dst = .return_ → cfg.isCleanup dst = false ∧ countUnwind ks = 0) ∧
    (cfg.exitOf dst = .unwindResume →
      cfg.isCleanup dst = true ∧ countUnwind ks = 1 ∧ cfg.canUnwind = true) ∧
    (cfg.exitOf dst = .unwindTerminate →
      cfg.isCleanup dst = true ∧ countUnwind ks = 1) := by
  have hshape : BipartiteTraceShape (cfg.isCleanup dst) ks := by
    induction hp with
    | nil _ =>
      rw [hv.startNotCleanup]
      exact .nil
    | @snoc b c ks e _ he hsrc hdst ih =>
      have hed := hv.edgesValid e he
      rw [hsrc, hdst] at hed
      cases hb : cfg.isCleanup b with
      | false =>
        rw [hb] at ih hed
        cases hc : cfg.isCleanup c with
        | false =>
          rw [hc] at hed
          cases ek : e.kind with
          | unwind =>
            rw [ek] at hed
            cases hed
          | normal =>
            change AllNormal (ks ++ [.normal])
            exact allNormal_append ih (.cons .nil)
        | true =>
          rw [hc] at hed
          cases ek : e.kind with
          | normal =>
            rw [ek] at hed
            cases hed
          | unwind =>
            change ∃ ks₁ ks₂, ks ++ [.unwind] = ks₁ ++ (.unwind :: ks₂) ∧
              AllNormal ks₁ ∧ AllNormal ks₂
            exact ⟨ks, [], rfl, ih, .nil⟩
      | true =>
        rw [hb] at ih hed
        cases hc : cfg.isCleanup c with
        | false =>
          rw [hc] at hed
          cases ek : e.kind <;> rw [ek] at hed <;> cases hed
        | true =>
          rw [hc] at hed
          cases ek : e.kind with
          | unwind =>
            rw [ek] at hed
            cases hed
          | normal =>
            rcases ih with ⟨ks₁, ks₂, hks, h1, h2⟩
            change ∃ ks₁' ks₂', ks ++ [.normal] = ks₁' ++ (.unwind :: ks₂') ∧
              AllNormal ks₁' ∧ AllNormal ks₂'
            refine ⟨ks₁, ks₂ ++ [.normal], ?_, h1, allNormal_append h2 (.cons .nil)⟩
            rw [hks, List.append_assoc]
            rfl
  have hcnt : countUnwind ks = (if cfg.isCleanup dst then 1 else 0) := by
    cases hd : cfg.isCleanup dst with
    | false =>
      rw [hd] at hshape
      exact countUnwind_zero_of_allNormal hshape
    | true =>
      rw [hd] at hshape
      rcases hshape with ⟨ks₁, ks₂, hks, h1, h2⟩
      rw [hks, countUnwind_append]
      change countUnwind ks₁ + (countUnwind ks₂ + 1) = 1
      rw [countUnwind_zero_of_allNormal h1, countUnwind_zero_of_allNormal h2]
  have hdstIn : dst < cfg.numBlocks := cfgPath_dst_inBounds hv hp
  have hexit := hv.exitsValid dst hdstIn
  refine ⟨hshape, hcnt, ?_, ?_, ?_⟩
  · intro hret
    rw [hret] at hexit
    cases hd : cfg.isCleanup dst with
    | true =>
      rw [hd] at hexit
      cases hexit
    | false =>
      rw [hd] at hcnt
      exact ⟨rfl, hcnt⟩
  · intro hres
    rw [hres] at hexit
    cases hd : cfg.isCleanup dst with
    | false =>
      rw [hd] at hexit
      cases hexit
    | true =>
      rw [hd] at hexit hcnt
      cases hcu : cfg.canUnwind with
      | false =>
        rw [hcu] at hexit
        cases hexit
      | true =>
        exact ⟨rfl, hcnt, rfl⟩
  · intro hterm
    rw [hterm] at hexit
    cases hd : cfg.isCleanup dst with
    | false =>
      rw [hd] at hexit
      cases hexit
    | true =>
      rw [hd] at hcnt
      exact ⟨rfl, hcnt⟩

/-- Corollary: when `canUnwind = false`, no reachable block in a valid CFG may exit
with `UnwindResume` (`validate.rs:521-523`). -/
theorem nounwind_path_cannot_resume {cfg : MirCfg} (hv : ValidCfg cfg)
    (hno : cfg.canUnwind = false) {dst : Nat} {ks : List EdgeKind}
    (hp : CfgPath cfg 0 dst ks) : cfg.exitOf dst ≠ .unwindResume := by
  intro hres
  have ⟨_, _, _, hresume, _⟩ := cleanup_automaton_path_separation hv hp
  have ⟨_, _, hcu⟩ := hresume hres
  rw [hno] at hcu
  cases hcu

/-! ### Contracted Cleanup Forest (`check_cleanup_control_flow`, `validate.rs:168-244`) -/

/-- A contracted cleanup parent map `parent : Fin n → Option (Fin n)` captures
`validate.rs:194-222` (at most one outgoing inter-region edge per contracted cleanup node)
and acyclicity (`validate.rs:224-243`, witnessed constructively by a strictly
decreasing topological rank). -/
structure ContractedCleanupForest (n : Nat) where
  parent : Fin n → Option (Fin n)
  rank : Fin n → Nat
  strictDec : ∀ u v, parent u = some v → rank v < rank u

/-- Single contracted-parent step (roots are fixed points). -/
def stepCleanupParent {n : Nat} (f : ContractedCleanupForest n) (u : Fin n) : Fin n :=
  match f.parent u with
  | none => u
  | some v => v

/-- Iterate `stepCleanupParent` `k` times via `Nat.repeat` (zero unsafe recursors). -/
def followCleanupParent {n : Nat} (f : ContractedCleanupForest n) (k : Nat) (u : Fin n) : Fin n :=
  Nat.repeat (stepCleanupParent f) k u

private theorem followCleanupParent_succ {n : Nat} (f : ContractedCleanupForest n)
    (k : Nat) (u : Fin n) :
    followCleanupParent f (k + 1) u = followCleanupParent f k (stepCleanupParent f u) := by
  induction k generalizing u with
  | zero => rfl
  | succ k' ih =>
    unfold followCleanupParent at ih ⊢
    change stepCleanupParent f (Nat.repeat (stepCleanupParent f) (k' + 1) u) =
      stepCleanupParent f (Nat.repeat (stepCleanupParent f) k' (stepCleanupParent f u))
    rw [ih u]

theorem followCleanupParent_root_fixed {n : Nat} (f : ContractedCleanupForest n)
    (u : Fin n) (hroot : f.parent u = none) :
    ∀ k, followCleanupParent f k u = u := by
  intro k
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [followCleanupParent_succ]
    have hstep : stepCleanupParent f u = u := by
      unfold stepCleanupParent
      rw [hroot]
    rw [hstep]
    exact ih

/-- Every node in a valid `ContractedCleanupForest` reaches a root (`parent r = none`)
within `f.rank u` steps, and all sufficiently large fuel bounds agree on that unique root. -/
theorem cleanup_contraction_unique_root {n : Nat} (f : ContractedCleanupForest n) :
    ∀ bound (u : Fin n), f.rank u ≤ bound →
      f.parent (followCleanupParent f bound u) = none ∧
      ∀ k, bound ≤ k → followCleanupParent f k u = followCleanupParent f bound u := by
  intro bound
  induction bound with
  | zero =>
    intro u hle
    have hparent : f.parent u = none := by
      cases hp : f.parent u with
      | none => rfl
      | some v =>
        have hlt := f.strictDec u v hp
        have hlt0 : f.rank v < 0 := Nat.lt_of_lt_of_le hlt hle
        exact False.elim (Nat.not_lt_zero _ hlt0)
    refine ⟨hparent, ?_⟩
    intro k _
    exact followCleanupParent_root_fixed f u hparent k
  | succ b ih =>
    intro u hle
    cases hp : f.parent u with
    | none =>
      have hfix := followCleanupParent_root_fixed f u hp
      refine ⟨?_, ?_⟩
      · rw [hfix (b + 1)]
        exact hp
      · intro k _
        rw [hfix k, hfix (b + 1)]
    | some v =>
      have hlt : f.rank v < f.rank u := f.strictDec u v hp
      have hvle : f.rank v ≤ b := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
      have ⟨hroot, huniq⟩ := ih v hvle
      have hstep : stepCleanupParent f u = v := by
        unfold stepCleanupParent
        rw [hp]
      refine ⟨?_, ?_⟩
      · rw [followCleanupParent_succ, hstep]
        exact hroot
      · intro k hk
        cases k with
        | zero => cases hk
        | succ k' =>
          have hbk : b ≤ k' := Nat.le_of_succ_le_succ hk
          rw [followCleanupParent_succ, followCleanupParent_succ, hstep]
          exact huniq k' hbk

/-!
================================================================================
## Part II: `SsaLocals` (`ssa.rs`), `Set1`, `Freeze`-Aware Shared-Borrow Soundness,
           and `!Freeze` / `Move`-Deinitialization Counterexamples
================================================================================
-/

/-- Exact `Set1` three-point semilattice from `rustc_middle::middle::resolve_bound_vars::Set1`
used in `ssa.rs:22, 204, 274`. -/
inductive Set1 (α : Type) where
  | empty : Set1 α
  | one (x : α) : Set1 α
  | many : Set1 α

/-- `Set1::insert`: `empty -> one x`, `one _ -> many`, `many -> many`. -/
def Set1.insert {α : Type} (s : Set1 α) (x : α) : Set1 α :=
  match s with
  | .empty => .one x
  | .one _ => .many
  | .many  => .many

/-- Lattice rank `Empty (0) < One (1) < Many (2)`. -/
def Set1.rank {α : Type} : Set1 α → Nat
  | .empty => 0
  | .one _ => 1
  | .many  => 2

theorem Set1.insert_rank_ge {α : Type} (s : Set1 α) (x : α) :
    s.rank ≤ (s.insert x).rank := by
  cases s with
  | empty => exact Nat.le_succ 0
  | one _ => exact Nat.le_succ 1
  | many  => exact Nat.le_refl 2

theorem Set1.insert_many {α : Type} (x : α) :
    (Set1.many : Set1 α).insert x = .many := rfl

/-- Exact `DefLocation` enum from `compiler/rustc_middle/src/mir/mod.rs:1676-1680`. -/
inductive DefLocation where
  | argument : DefLocation
  | assignment (bb stmt : Nat) : DefLocation
  | callReturn (call : Nat) (target : Option Nat) : DefLocation

/-- Exact `DefLocation::dominates` from `compiler/rustc_middle/src/mir/mod.rs:1684-1703`. -/
def DefLocation.dominates (dom : Nat → Nat → Bool) (defLoc : DefLocation)
    (useBb useStmt : Nat) : Bool :=
  match defLoc with
  | .argument => true
  | .assignment defBb defStmt =>
    if natEq defBb useBb then Nat.ble (defStmt + 1) useStmt
    else dom defBb useBb
  | .callReturn _ none => false
  | .callReturn call (some target) =>
    !(natEq call target) && dom call target && dom target useBb

theorem DefLocation.callReturn_none_never_dominates (dom : Nat → Nat → Bool)
    (call useBb useStmt : Nat) :
    DefLocation.dominates dom (.callReturn call none) useBb useStmt = false := rfl

theorem DefLocation.callReturn_selfLoop_never_dominates (dom : Nat → Nat → Bool)
    (call useBb useStmt : Nat) :
    DefLocation.dominates dom (.callReturn call (some call)) useBb useStmt = false := by
  dsimp only [DefLocation.dominates]
  rw [natEq_self call]
  rfl

/-! ### Operational Small-Step Trace Model for `SsaLocals` (`Freeze` vs `!Freeze`) -/

/-- Events along a reachable MIR execution trace relevant to `SsaLocals`. -/
inductive TraceEvent where
  | assign (l : Nat) (v : Nat) : TraceEvent
  | sharedBorrowCall (l : Nat) (mutated : Option Nat) : TraceEvent
  | mutOrRawBorrowCall (l : Nat) (mutated : Option Nat) : TraceEvent
  | copyRead (l : Nat) : TraceEvent
  | moveRead (l : Nat) : TraceEvent

/-- Runtime local store mapping each local ID to `Option Nat` (`none` = uninitialized). -/
abbrev LocalStore := Nat → Option Nat

def storeUpdate (st : LocalStore) (l : Nat) (val : Option Nat) : LocalStore :=
  fun x => if natEq x l then val else st x

theorem storeUpdate_eq (st : LocalStore) (l : Nat) (val : Option Nat) :
    storeUpdate st l val l = val := by
  dsimp only [storeUpdate]
  rw [natEq_self l]
  rfl

theorem storeUpdate_ne (st : LocalStore) (l x : Nat) (val : Option Nat) (hne : x ≠ l) :
    storeUpdate st l val x = st x := by
  dsimp only [storeUpdate]
  rw [(natEq_false_iff x l).mpr hne]
  rfl

/-- Single-step operational execution of a `TraceEvent` parameterized by `deinitMove`. -/
def execEvent (deinitMove : Bool) (st : LocalStore) : TraceEvent → LocalStore
  | .assign l v => storeUpdate st l (some v)
  | .sharedBorrowCall l (some v') => storeUpdate st l (some v')
  | .sharedBorrowCall _ none => st
  | .mutOrRawBorrowCall l (some v') => storeUpdate st l (some v')
  | .mutOrRawBorrowCall _ none => st
  | .copyRead _ => st
  | .moveRead l => if deinitMove then storeUpdate st l none else st

/-- Execute a list of `TraceEvent`s from an initial store (`List.foldl`, zero unsafe recursors). -/
def execTrace (deinitMove : Bool) (st : LocalStore) (tr : List TraceEvent) : LocalStore :=
  tr.foldl (execEvent deinitMove) st

/-- Rust shared-reference immutability rule (`rust-lang/reference`, `r[undefined.alias]`
and `r[interior-mut.unsafe-cell]`): mutating a local through a shared reference is
UB-free only when the local's type is `!Freeze` (contains `UnsafeCell`). -/
def EventUbFree (isFreeze : Nat → Bool) : TraceEvent → Prop
  | .sharedBorrowCall l (some _) => isFreeze l = false
  | _ => True

inductive TraceUbFree (isFreeze : Nat → Bool) : List TraceEvent → Prop where
  | nil : TraceUbFree isFreeze []
  | cons {ev : TraceEvent} {tl : List TraceEvent} :
      EventUbFree isFreeze ev → TraceUbFree isFreeze tl → TraceUbFree isFreeze (ev :: tl)

/-- Abstract `SsaVisitor` state mirroring `ssa.rs:201-293` along a trace. -/
structure SsaScanState where
  assignments : Nat → Set1 Nat
  borrowed : Nat → Bool

def SsaScanState.empty : SsaScanState :=
  { assignments := fun _ => .empty, borrowed := fun _ => false }

def setAssign (f : Nat → Set1 Nat) (l : Nat) (s : Set1 Nat) : Nat → Set1 Nat :=
  fun x => if natEq x l then s else f x

def setBorrowed (f : Nat → Bool) (l : Nat) (b : Bool) : Nat → Bool :=
  fun x => if natEq x l then b else f x

/-- Mirror `SsaVisitor::visit_local` / `visit_place` (`ssa.rs:228-292`) on a single event. -/
def scanEvent (st : SsaScanState) (idx : Nat) : TraceEvent → SsaScanState
  | .assign l _ =>
    { st with assignments := setAssign st.assignments l ((st.assignments l).insert idx) }
  | .sharedBorrowCall l _ =>
    let b' := setBorrowed st.borrowed l true
    let a' :=
      match st.assignments l with
      | .one _ => st.assignments
      | _ => setAssign st.assignments l .many
    { assignments := a', borrowed := b' }
  | .mutOrRawBorrowCall l _ =>
    { assignments := setAssign st.assignments l .many
    , borrowed := setBorrowed st.borrowed l true }
  | .copyRead l | .moveRead l =>
    let a' :=
      match st.assignments l with
      | .one _ => st.assignments
      | _ => setAssign st.assignments l .many
    { st with assignments := a' }

/-- Scan an entire trace from step index `idx` via `List.foldl` (zero unsafe recursors). -/
def scanTrace (st : SsaScanState) (idx : Nat) (tr : List TraceEvent) : SsaScanState :=
  (tr.foldl (fun (acc : SsaScanState × Nat) ev => (scanEvent acc.1 acc.2 ev, acc.2 + 1)) (st, idx)).1

private theorem scanTrace_nil (st : SsaScanState) (idx : Nat) :
    scanTrace st idx [] = st := rfl

private theorem scanTrace_cons (st : SsaScanState) (idx : Nat) (ev : TraceEvent)
    (tl : List TraceEvent) :
    scanTrace st idx (ev :: tl) = scanTrace (scanEvent st idx ev) (idx + 1) tl := rfl

/-- Exact post-visitor `Freeze` demotion loop from `ssa.rs:77-81`. -/
def applyFreezeDemotion (isFreeze : Nat → Bool) (st : SsaScanState) : SsaScanState :=
  { st with
    assignments := fun l =>
      if st.borrowed l && !isFreeze l then .many else st.assignments l }

/-- Complete `SsaLocals` analysis over a trace. -/
def analyzeSsa (isFreeze : Nat → Bool) (tr : List TraceEvent) : SsaScanState :=
  applyFreezeDemotion isFreeze (scanTrace SsaScanState.empty 0 tr)

private theorem scanEvent_many_preserved (st : SsaScanState) (idx : Nat) (ev : TraceEvent) (l : Nat)
    (hm : st.assignments l = .many) :
    (scanEvent st idx ev).assignments l = .many := by
  have hsetMany : ∀ l', setAssign st.assignments l' .many l = .many := by
    intro l'
    dsimp only [setAssign]
    cases natEq l l' with
    | false => exact hm
    | true => rfl
  cases ev with
  | assign l' _ =>
    dsimp only [scanEvent, setAssign]
    cases h : natEq l l' with
    | false => exact hm
    | true =>
      have heq : l = l' := (natEq_true_iff l l').mp h
      subst heq
      simp [hm, Set1.insert]
  | sharedBorrowCall l' _ =>
    dsimp only [scanEvent]
    cases st.assignments l' with
    | one _ => exact hm
    | empty => exact hsetMany l'
    | many => exact hsetMany l'
  | mutOrRawBorrowCall l' _ =>
    dsimp only [scanEvent]
    exact hsetMany l'
  | copyRead l' =>
    dsimp only [scanEvent]
    cases st.assignments l' with
    | one _ => exact hm
    | empty => exact hsetMany l'
    | many => exact hsetMany l'
  | moveRead l' =>
    dsimp only [scanEvent]
    cases st.assignments l' with
    | one _ => exact hm
    | empty => exact hsetMany l'
    | many => exact hsetMany l'

private theorem scanTrace_many_preserved (tr : List TraceEvent) (st : SsaScanState)
    (idx l : Nat) (hm : st.assignments l = .many) :
    (scanTrace st idx tr).assignments l = .many := by
  induction tr generalizing st idx with
  | nil => exact hm
  | cons ev tl ih =>
    rw [scanTrace_cons]
    exact ih (scanEvent st idx ev) (idx + 1) (scanEvent_many_preserved st idx ev l hm)

private theorem scanEvent_borrowed_preserved (st : SsaScanState) (idx : Nat) (ev : TraceEvent)
    (l : Nat) (hb : st.borrowed l = true) :
    (scanEvent st idx ev).borrowed l = true := by
  cases ev with
  | assign _ _ => exact hb
  | sharedBorrowCall l' _ =>
    dsimp only [scanEvent, setBorrowed]
    cases natEq l l' with
    | false => exact hb
    | true => rfl
  | mutOrRawBorrowCall l' _ =>
    dsimp only [scanEvent, setBorrowed]
    cases natEq l l' with
    | false => exact hb
    | true => rfl
  | copyRead _ => exact hb
  | moveRead _ => exact hb

private theorem scanTrace_borrowed_preserved (tr : List TraceEvent) (st : SsaScanState)
    (idx l : Nat) (hb : st.borrowed l = true) :
    (scanTrace st idx tr).borrowed l = true := by
  induction tr generalizing st idx with
  | nil => exact hb
  | cons ev tl ih =>
    rw [scanTrace_cons]
    exact ih (scanEvent st idx ev) (idx + 1) (scanEvent_borrowed_preserved st idx ev l hb)

/-- Inductive predicate asserting a trace suffix performs no `moveRead l`. -/
inductive NoMoveOn (l : Nat) : List TraceEvent → Prop where
  | nil : NoMoveOn l []
  | cons {ev : TraceEvent} {tl : List TraceEvent} :
      (∀ l', ev = .moveRead l' → l' ≠ l) → NoMoveOn l tl → NoMoveOn l (ev :: tl)

/-- Core post-definition invariance lemma for `SsaLocals`. -/
theorem post_def_store_invariant
    (isFreeze : Nat → Bool) (deinitMove : Bool)
    (tr : List TraceEvent) (st : SsaScanState) (store : LocalStore)
    (idx l defIdx v₀ : Nat)
    (hub : TraceUbFree isFreeze tr)
    (hmove : deinitMove = false ∨ NoMoveOn l tr)
    (hone : st.assignments l = .one defIdx)
    (hval : store l = some v₀)
    (hfinal : (applyFreezeDemotion isFreeze (scanTrace st idx tr)).assignments l = .one defIdx) :
    (execTrace deinitMove store tr) l = some v₀ := by
  induction tr generalizing st store idx with
  | nil => exact hval
  | cons ev tl ih =>
    cases hub with
    | cons hubEv hubTl =>
      have hmoveTl : deinitMove = false ∨ NoMoveOn l tl := by
        cases hmove with
        | inl hf => exact Or.inl hf
        | inr hnm =>
          cases hnm with
          | cons _ htl => exact Or.inr htl
      have hstep :
          (scanEvent st idx ev).assignments l = .one defIdx ∧
          (execEvent deinitMove store ev) l = some v₀ := by
        cases ev with
        | assign l' v' =>
          cases hEq : natEq l l' with
          | true =>
            have heq : l = l' := (natEq_true_iff l l').mp hEq
            subst heq
            have hmany : (scanEvent st idx (.assign l v')).assignments l = .many := by
              dsimp only [scanEvent, setAssign]
              rw [natEq_self l, hone]
              rfl
            have hfinMany := scanTrace_many_preserved tl _ (idx + 1) l hmany
            unfold applyFreezeDemotion at hfinal
            rw [scanTrace_cons] at hfinal
            simp [hfinMany] at hfinal
          | false =>
            have hne : l ≠ l' := (natEq_false_iff l l').mp hEq
            refine ⟨?_, ?_⟩
            · dsimp only [scanEvent, setAssign]
              rw [hEq]
              exact hone
            · dsimp only [execEvent]
              rw [storeUpdate_ne store l' l (some v') hne]
              exact hval
        | sharedBorrowCall l' mutOpt =>
          cases hEq : natEq l l' with
          | false =>
            have hne : l ≠ l' := (natEq_false_iff l l').mp hEq
            have ha : (scanEvent st idx (.sharedBorrowCall l' mutOpt)).assignments l = .one defIdx := by
              dsimp only [scanEvent]
              cases st.assignments l' with
              | one _ => exact hone
              | empty => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
              | many  => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
            have hv : (execEvent deinitMove store (.sharedBorrowCall l' mutOpt)) l = some v₀ := by
              cases mutOpt with
              | none => exact hval
              | some v' =>
                dsimp only [execEvent]
                rw [storeUpdate_ne store l' l (some v') hne]
                exact hval
            exact ⟨ha, hv⟩
          | true =>
            have heq : l = l' := (natEq_true_iff l l').mp hEq
            subst heq
            have ha : (scanEvent st idx (.sharedBorrowCall l mutOpt)).assignments l = .one defIdx := by
              dsimp only [scanEvent]
              rw [hone]
              exact hone
            have hborr0 : (scanEvent st idx (.sharedBorrowCall l mutOpt)).borrowed l = true := by
              dsimp only [scanEvent, setBorrowed]
              rw [natEq_self l]
              rfl
            have hborrEnd := scanTrace_borrowed_preserved tl _ (idx + 1) l hborr0
            cases mutOpt with
            | none => exact ⟨ha, hval⟩
            | some _ =>
              have hnotFreeze : isFreeze l = false := hubEv
              unfold applyFreezeDemotion at hfinal
              rw [scanTrace_cons] at hfinal
              simp [hborrEnd, hnotFreeze] at hfinal
        | mutOrRawBorrowCall l' mutOpt =>
          cases hEq : natEq l l' with
          | true =>
            have heq : l = l' := (natEq_true_iff l l').mp hEq
            subst heq
            have hmany : (scanEvent st idx (.mutOrRawBorrowCall l mutOpt)).assignments l = .many := by
              dsimp only [scanEvent, setAssign]
              rw [natEq_self l]
              rfl
            have hfinMany := scanTrace_many_preserved tl _ (idx + 1) l hmany
            unfold applyFreezeDemotion at hfinal
            rw [scanTrace_cons] at hfinal
            simp [hfinMany] at hfinal
          | false =>
            have hne : l ≠ l' := (natEq_false_iff l l').mp hEq
            refine ⟨?_, ?_⟩
            · dsimp only [scanEvent, setAssign]
              rw [hEq]
              exact hone
            · cases mutOpt with
              | none => exact hval
              | some v' =>
                dsimp only [execEvent]
                rw [storeUpdate_ne store l' l (some v') hne]
                exact hval
        | copyRead l' =>
          have ha : (scanEvent st idx (.copyRead l')).assignments l = .one defIdx := by
            cases hEq : natEq l l' with
            | true =>
              have heq : l = l' := (natEq_true_iff l l').mp hEq
              subst heq
              dsimp only [scanEvent]
              rw [hone]
              exact hone
            | false =>
              dsimp only [scanEvent]
              cases st.assignments l' with
              | one _ => exact hone
              | empty => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
              | many  => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
          exact ⟨ha, hval⟩
        | moveRead l' =>
          have ha : (scanEvent st idx (.moveRead l')).assignments l = .one defIdx := by
            cases hEq : natEq l l' with
            | true =>
              have heq : l = l' := (natEq_true_iff l l').mp hEq
              subst heq
              dsimp only [scanEvent]
              rw [hone]
              exact hone
            | false =>
              dsimp only [scanEvent]
              cases st.assignments l' with
              | one _ => exact hone
              | empty => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
              | many  => simp only [setAssign, hEq, Bool.false_eq_true, ↓reduceIte]; exact hone
          have hv : (execEvent deinitMove store (.moveRead l')) l = some v₀ := by
            cases hmove with
            | inl hf =>
              dsimp only [execEvent]
              rw [hf]
              exact hval
            | inr hnm =>
              cases hnm with
              | cons hneEv _ =>
                have hne : l ≠ l' := fun h => hneEv l' rfl h.symm
                dsimp only [execEvent]
                cases deinitMove with
                | false => exact hval
                | true =>
                  simp only [↓reduceIte]
                  rw [storeUpdate_ne store l' l none hne]
                  exact hval
          exact ⟨ha, hv⟩
      rw [scanTrace_cons] at hfinal
      exact ih (scanEvent st idx ev) (execEvent deinitMove store ev) (idx + 1)
        hubTl hmoveTl hstep.1 hstep.2 hfinal

/-- **Main Theorem 2a (`ssaLocals_freeze_shared_borrow_value_sound`):**
If `analyzeSsa isFreeze` classifies local `l` as `Set1.one pref.length` on a UB-free
trace `pref ++ [assign l v₀] ++ suff` (allowing arbitrary shared borrows `&l` of `Freeze`
locals in `suff`) and either `deinitMove = false` or `NoMoveOn l suff`, then `l` retains
its assigned value `some v₀` at the end of execution. -/
theorem ssaLocals_freeze_shared_borrow_value_sound
    (isFreeze : Nat → Bool) (deinitMove : Bool)
    (initStore : LocalStore)
    (pref suff : List TraceEvent) (l v₀ : Nat)
    (hubSuff : TraceUbFree isFreeze suff)
    (hmoveSuff : deinitMove = false ∨ NoMoveOn l suff)
    (hpreEmpty : (scanTrace SsaScanState.empty 0 pref).assignments l = .empty)
    (hssa : (analyzeSsa isFreeze (pref ++ .assign l v₀ :: suff)).assignments l =
      .one pref.length) :
    (execTrace deinitMove initStore (pref ++ .assign l v₀ :: suff)) l = some v₀ := by
  have hscanAppend : ∀ (xs ys : List TraceEvent) (st : SsaScanState) (idx : Nat),
      scanTrace st idx (xs ++ ys) = scanTrace (scanTrace st idx xs) (idx + xs.length) ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys st idx
      simp [scanTrace]
    | cons e tl ih =>
      intro ys st idx
      simp only [List.cons_append, scanTrace_cons, List.length_cons]
      rw [ih ys (scanEvent st idx e) (idx + 1)]
      have hidx : idx + 1 + tl.length = idx + (tl.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 tl.length]
      rw [hidx]
  have hexecAppend : ∀ (xs ys : List TraceEvent) (st : LocalStore),
      execTrace deinitMove st (xs ++ ys) = execTrace deinitMove (execTrace deinitMove st xs) ys := by
    intro xs ys st
    unfold execTrace
    exact List.foldl_append
  rw [hexecAppend]
  change (execTrace deinitMove (storeUpdate (execTrace deinitMove initStore pref) l (some v₀)) suff) l = some v₀
  unfold analyzeSsa at hssa
  rw [hscanAppend] at hssa
  simp only [Nat.zero_add, scanTrace_cons] at hssa
  have honeAfterDef :
      (scanEvent (scanTrace SsaScanState.empty 0 pref) pref.length (.assign l v₀)).assignments l =
      .one pref.length := by
    dsimp only [scanEvent, setAssign]
    rw [natEq_self l, hpreEmpty]
    rfl
  have hvalAfterDef :
      (storeUpdate (execTrace deinitMove initStore pref) l (some v₀)) l = some v₀ :=
    storeUpdate_eq _ l (some v₀)
  exact post_def_store_invariant isFreeze deinitMove suff
    (scanEvent (scanTrace SsaScanState.empty 0 pref) pref.length (.assign l v₀))
    (storeUpdate (execTrace deinitMove initStore pref) l (some v₀))
    (pref.length + 1) l pref.length v₀
    hubSuff hmoveSuff honeAfterDef hvalAfterDef hssa

/-- Concrete `!Freeze` (`Cell<u32>`) trace: `c = 42; mutate_cell(&c) [sets c := 100]; read c`. -/
def cellCounterexampleTrace : List TraceEvent :=
  [.assign 1 42, .sharedBorrowCall 1 (some 100), .copyRead 1]

def isFreezeCell : Nat → Bool := fun _ => false

/-- **Main Theorem 2b (`ssaLocals_nonFreeze_counterexample`):**
On `cellCounterexampleTrace` (`isFreeze 1 = false`, modeling `Cell<u32>`):
1. The trace is UB-free (`TraceUbFree isFreezeCell cellCounterexampleTrace`).
2. Without `applyFreezeDemotion` (`ssa.rs:77-81`), `scanTrace` leaves local `1` as
   `Set1.one 0` (falsely marking `c` as SSA with value `42`).
3. Runtime execution yields `some 100 ≠ some 42`.
4. With `applyFreezeDemotion`, `analyzeSsa` demotes local `1` to `Set1.many`. -/
theorem ssaLocals_nonFreeze_counterexample :
    TraceUbFree isFreezeCell cellCounterexampleTrace ∧
    (scanTrace SsaScanState.empty 0 cellCounterexampleTrace).assignments 1 = .one 0 ∧
    (execTrace false (fun _ => none) cellCounterexampleTrace) 1 = some 100 ∧
    (some 100 : Option Nat) ≠ some 42 ∧
    (analyzeSsa isFreezeCell cellCounterexampleTrace).assignments 1 = .many := by
  refine ⟨?_, rfl, rfl, ?_, rfl⟩
  · exact .cons trivial (.cons rfl (.cons trivial .nil))
  · intro h
    cases h

/-- Concrete `Operand::Move` deinitialization counterexample (`deinitMovedPlace = true`
in Miri and Anneal `Trusted.MirSemantics`): `x = 42; move x; copy x`. -/
def moveDeinitTrace : List TraceEvent :=
  [.assign 1 42, .moveRead 1, .copyRead 1]

def isFreezeAll : Nat → Bool := fun _ => true

/-- **Corollary 2c (`ssaLocals_move_deinit_counterexample`):**
`analyzeSsa` classifies local `1` as `Set1.one 0` (matching `ssa.rs:247-250`), yet
under `deinitMove = true` (Miri / Anneal `Trusted.MirSemantics`), `moveRead 1`
deinitializes local `1` (`none ≠ some 42`). -/
theorem ssaLocals_move_deinit_counterexample :
    (analyzeSsa isFreezeAll moveDeinitTrace).assignments 1 = .one 0 ∧
    (execTrace false (fun _ => none) moveDeinitTrace) 1 = some 42 ∧
    (execTrace true  (fun _ => none) moveDeinitTrace) 1 = none ∧
    (none : Option Nat) ≠ some 42 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-!
================================================================================
## Part III: `compute_copy_classes` Union-Find Idempotence, `RETURN_PLACE` Barrier,
            and Two-Pass `meet_copy_equivalence` Uniformity (`ssa.rs:150-199, 296-361`)
================================================================================
-/

/-- Exact `LocalKind` classification relevant to `compute_copy_classes` (`ssa.rs:335`). -/
inductive LocalKind where
  | returnPlace : LocalKind
  | arg : LocalKind
  | temp : LocalKind

def LocalKind.isTemp : LocalKind → Bool
  | .temp => true
  | _     => false

/-- Copy assignment edge `local = copy/move rhs` visited in RPO `assignment_order`. -/
structure CopyEdge (n : Nat) where
  local_ : Fin n
  rhs : Fin n
  typesEq : Bool

/-- Static body context for `compute_copy_classes` (`n > 0` so `RETURN_PLACE = 0` exists). -/
structure CopyCtx (n : Nat) where
  hpos : 0 < n
  kind : Fin n → LocalKind
  isSsa : Fin n → Bool
  borrowed : Fin n → Bool
  retKind : kind ⟨0, hpos⟩ = .returnPlace
  nonRetKind : ∀ l : Fin n, l.val ≠ 0 → kind l ≠ .returnPlace

abbrev CopyMap (n : Nat) := Fin n → Fin n

def CopyCtx.retPlace {n : Nat} (ctx : CopyCtx n) : Fin n := ⟨0, ctx.hpos⟩

def idCopyMap (n : Nat) : CopyMap n := fun l => l

/-- Complete loop invariant maintained by `compute_copy_classes` (`ssa.rs:296-361`):
1. `idempotent`: union-find path compression (`copies[copies[x]] = copies[x]`, `ssa.rs:355`).
2. `retFixed`: `copies[RETURN_PLACE] = RETURN_PLACE` (`ssa.rs:357`).
3. `argFixed`: every `LocalKind.arg` remains its own representative (never absorbed into `_0`).
4. `atMostOneBorrowed`: at most one local per copy class is in `borrowed_locals`
   (soundly preserving distinct observable addresses even when a borrowed `temp` class
   is re-rooted at `RETURN_PLACE` per `ssa.rs:338-342` and `copy_prop.rs:65-69`). -/
structure CopyClassInv {n : Nat} (ctx : CopyCtx n) (copies : CopyMap n) : Prop where
  idempotent : ∀ x : Fin n, copies (copies x) = copies x
  retFixed : copies ctx.retPlace = ctx.retPlace
  argFixed : ∀ l : Fin n, ctx.kind l = .arg → copies l = l
  atMostOneBorrowed : ∀ x y : Fin n,
    copies x = copies y → ctx.borrowed x = true → ctx.borrowed y = true → x = y

/-- RPO freshness invariant for an SSA local `l`: before its unique defining assignment
is processed in RPO `assignment_order`, no other local already maps to `l`. -/
def FreshClass {n : Nat} (copies : CopyMap n) (l : Fin n) : Prop :=
  copies l = l ∧ ∀ x : Fin n, copies x = l → x = l

/-- Exact single-edge update matching `compute_copy_classes` (`ssa.rs:300-347`). -/
def copyClassStep {n : Nat} (ctx : CopyCtx n) (copies : CopyMap n) (e : CopyEdge n) :
    CopyMap n :=
  if !e.typesEq then
    copies
  else if !ctx.isSsa e.rhs then
    copies
  else if ctx.borrowed e.local_ then
    copies
  else
    let head := copies e.rhs
    if natEq e.local_.val 0 then
      if (ctx.kind head).isTemp then
        fun x => if natEq (copies x).val head.val then ctx.retPlace else copies x
      else
        copies
    else
      fun x => if natEq x.val e.local_.val then head else copies x

/-- Folding `copyClassStep` over an RPO edge list (`ssa.rs:300-347`). -/
def computeCopyClasses {n : Nat} (ctx : CopyCtx n) (edges : List (CopyEdge n)) : CopyMap n :=
  edges.foldl (copyClassStep ctx) (idCopyMap n)

/-- Inductive RPO admissibility predicate on an assignment-edge sequence yielded by
`ssa.assignments(body)` (zero unsafe recursors). -/
inductive ValidRpoEdges {n : Nat} (ctx : CopyCtx n) : CopyMap n → List (CopyEdge n) → Prop where
  | nil (copies : CopyMap n) : ValidRpoEdges ctx copies []
  | cons {copies : CopyMap n} {e : CopyEdge n} {tl : List (CopyEdge n)} :
      ctx.kind e.local_ ≠ .arg →
      FreshClass copies e.local_ →
      ValidRpoEdges ctx (copyClassStep ctx copies e) tl →
      ValidRpoEdges ctx copies (e :: tl)

theorem idCopyMap_inv {n : Nat} (ctx : CopyCtx n) : CopyClassInv ctx (idCopyMap n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _; rfl
  · rfl
  · intro _ _; rfl
  · intro _ _ hEq _ _; exact hEq

/-- Core step preservation theorem for `compute_copy_classes`. -/
theorem copyClassStep_preserves_inv {n : Nat} (ctx : CopyCtx n)
    (copies : CopyMap n) (e : CopyEdge n)
    (hinv : CopyClassInv ctx copies)
    (hnotArg : ctx.kind e.local_ ≠ .arg)
    (hfresh : FreshClass copies e.local_) :
    CopyClassInv ctx (copyClassStep ctx copies e) := by
  unfold copyClassStep
  cases hteq : e.typesEq with
  | false => exact hinv
  | true =>
    cases hssa : ctx.isSsa e.rhs with
    | false => exact hinv
    | true =>
      cases hbor : ctx.borrowed e.local_ with
      | true => exact hinv
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hloc0 : natEq e.local_.val 0 with
        | true =>
          have hl0 : e.local_ = ctx.retPlace := Fin.ext ((natEq_true_iff e.local_.val 0).mp hloc0)
          cases htemp : (ctx.kind (copies e.rhs)).isTemp with
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hinv
          | true =>
            simp only [↓reduceIte]
            have hheadNotRet : copies e.rhs ≠ ctx.retPlace := by
              intro hEq
              have hk : ctx.kind ctx.retPlace = .returnPlace := ctx.retKind
              rw [← hEq] at hk
              rw [hk] at htemp
              cases htemp
            have hretNeHeadBool : natEq ctx.retPlace.val (copies e.rhs).val = false :=
              (finEq_false_iff ctx.retPlace (copies e.rhs)).mpr (fun h => hheadNotRet h.symm)
            have hretNotBorr : ctx.borrowed ctx.retPlace = false := by
              rw [← hl0]
              exact hbor
            have hretFresh : ∀ x : Fin n, copies x = ctx.retPlace → x = ctx.retPlace := by
              rw [← hl0]
              exact hfresh.2
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro x
              cases hx : natEq (copies x).val (copies e.rhs).val with
              | true =>
                simp only [↓reduceIte]
                rw [hinv.retFixed, hretNeHeadBool]
                rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [hinv.idempotent x, hx]
                rfl
            · rw [hinv.retFixed, hretNeHeadBool]
              rfl
            · intro l harg
              have hcl : copies l = l := hinv.argFixed l harg
              have hne : l ≠ copies e.rhs := by
                intro hEq
                rw [← hEq, harg] at htemp
                cases htemp
              have hb : natEq (copies l).val (copies e.rhs).val = false := by
                rw [hcl]
                exact (finEq_false_iff l (copies e.rhs)).mpr hne
              rw [hb]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hcl
            · intro x y hEq hbx hby
              cases hx : natEq (copies x).val (copies e.rhs).val with
              | true =>
                have hcx : copies x = copies e.rhs := (finEq_true_iff _ _).mp hx
                cases hy : natEq (copies y).val (copies e.rhs).val with
                | true =>
                  have hcy : copies y = copies e.rhs := (finEq_true_iff _ _).mp hy
                  exact hinv.atMostOneBorrowed x y (hcx.trans hcy.symm) hbx hby
                | false =>
                  rw [hx, hy] at hEq
                  simp only [Bool.false_eq_true, ↓reduceIte] at hEq
                  have hyRet : y = ctx.retPlace := hretFresh y hEq.symm
                  rw [hyRet, hretNotBorr] at hby
                  cases hby
              | false =>
                cases hy : natEq (copies y).val (copies e.rhs).val with
                | true =>
                  rw [hx, hy] at hEq
                  simp only [Bool.false_eq_true, ↓reduceIte] at hEq
                  have hxRet : x = ctx.retPlace := hretFresh x hEq
                  rw [hxRet, hretNotBorr] at hbx
                  cases hbx
                | false =>
                  rw [hx, hy] at hEq
                  simp only [Bool.false_eq_true, ↓reduceIte] at hEq
                  exact hinv.atMostOneBorrowed x y hEq hbx hby
        | false =>
          have hlNe0 : e.local_.val ≠ 0 := (natEq_false_iff e.local_.val 0).mp hloc0
          have ⟨_, huniq⟩ := hfresh
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro x
            cases hx : natEq x.val e.local_.val with
            | true =>
              simp only [↓reduceIte]
              cases hheadEq : natEq (copies e.rhs).val e.local_.val with
              | true =>
                simp only [↓reduceIte]
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                exact hinv.idempotent e.rhs
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              have hxNe : x ≠ e.local_ := (finEq_false_iff x e.local_).mp hx
              have hcxNe : copies x ≠ e.local_ := fun hEq => hxNe (huniq x hEq)
              have hcxBool : natEq (copies x).val e.local_.val = false :=
                (finEq_false_iff (copies x) e.local_).mpr hcxNe
              rw [hcxBool]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hinv.idempotent x
          · have hretNe : natEq ctx.retPlace.val e.local_.val = false :=
              (natEq_false_iff 0 e.local_.val).mpr (fun h => hlNe0 h.symm)
            rw [hretNe]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hinv.retFixed
          · intro l harg
            have hne : l ≠ e.local_ := by
              intro hEq
              rw [← hEq] at hnotArg
              exact hnotArg harg
            have hb : natEq l.val e.local_.val = false := (finEq_false_iff l e.local_).mpr hne
            rw [hb]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact hinv.argFixed l harg
          · intro x y hEq hbx hby
            have hxNe : x ≠ e.local_ := by
              intro hE
              rw [hE, hbor] at hbx
              cases hbx
            have hyNe : y ≠ e.local_ := by
              intro hE
              rw [hE, hbor] at hby
              cases hby
            have hxB : natEq x.val e.local_.val = false := (finEq_false_iff x e.local_).mpr hxNe
            have hyB : natEq y.val e.local_.val = false := (finEq_false_iff y e.local_).mpr hyNe
            rw [hxB, hyB] at hEq
            simp only [Bool.false_eq_true, ↓reduceIte] at hEq
            exact hinv.atMostOneBorrowed x y hEq hbx hby

private theorem foldl_copyClassStep_preserves_inv {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (init : CopyMap n)
    (hinv : CopyClassInv ctx init) (hvalid : ValidRpoEdges ctx init edges) :
    CopyClassInv ctx (edges.foldl (copyClassStep ctx) init) := by
  induction edges generalizing init with
  | nil => exact hinv
  | cons e tl ih =>
    cases hvalid with
    | cons hnotArg hfresh htl =>
      exact ih (copyClassStep ctx init e)
        (copyClassStep_preserves_inv ctx init e hinv hnotArg hfresh) htl

/-- **Main Theorem 3a (`computeCopyClasses_soundness`):**
For any RPO-valid sequence of copy edges, `computeCopyClasses` satisfies:
1. Union-find idempotence (`copies (copies x) = copies x`, `ssa.rs:355`).
2. `RETURN_PLACE` fixed-point (`copies _0 = _0`, `ssa.rs:357`).
3. `LocalKind.arg` isolation (`copies arg = arg`, hence never merged into `_0`).
4. Unique-borrow preservation (`atMostOneBorrowed` per copy class). -/
theorem computeCopyClasses_soundness {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (hvalid : ValidRpoEdges ctx (idCopyMap n) edges) :
    CopyClassInv ctx (computeCopyClasses ctx edges) :=
  foldl_copyClassStep_preserves_inv ctx edges (idCopyMap n) (idCopyMap_inv ctx) hvalid

theorem computeCopyClasses_idempotent {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (hvalid : ValidRpoEdges ctx (idCopyMap n) edges) :
    ∀ x : Fin n, computeCopyClasses ctx edges (computeCopyClasses ctx edges x) =
      computeCopyClasses ctx edges x :=
  (computeCopyClasses_soundness ctx edges hvalid).idempotent

theorem computeCopyClasses_return_place_fixed {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (hvalid : ValidRpoEdges ctx (idCopyMap n) edges) :
    computeCopyClasses ctx edges ctx.retPlace = ctx.retPlace :=
  (computeCopyClasses_soundness ctx edges hvalid).retFixed

theorem computeCopyClasses_arg_never_return_place {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (hvalid : ValidRpoEdges ctx (idCopyMap n) edges) :
    ∀ l : Fin n, ctx.kind l = .arg → computeCopyClasses ctx edges l ≠ ctx.retPlace := by
  intro l harg hEq
  have hfix := (computeCopyClasses_soundness ctx edges hvalid).argFixed l harg
  rw [hfix] at hEq
  have hk : ctx.kind ctx.retPlace = .returnPlace := ctx.retKind
  rw [← hEq, harg] at hk
  cases hk

theorem computeCopyClasses_at_most_one_borrowed {n : Nat} (ctx : CopyCtx n)
    (edges : List (CopyEdge n)) (hvalid : ValidRpoEdges ctx (idCopyMap n) edges) :
    ∀ x y : Fin n,
      computeCopyClasses ctx edges x = computeCopyClasses ctx edges y →
      ctx.borrowed x = true → ctx.borrowed y = true → x = y :=
  (computeCopyClasses_soundness ctx edges hvalid).atMostOneBorrowed

/-! ### Two-Pass In-Place `meet_copy_equivalence` (`ssa.rs:174-198`) -/

/-- Exact finite bitset over `Fin n`. -/
abbrev LocalProp (n : Nat) := Fin n → Bool

def propRemove {n : Nat} (p : LocalProp n) (target : Fin n) : LocalProp n :=
  fun x => if natEq x.val target.val then false else p x

/-- Exact in-place Pass 1 of `SsaLocals::meet_copy_equivalence` (`ssa.rs:179-184`, `foldl`). -/
def meetPass1List {n : Nat} (copies : CopyMap n) (xs : List (Fin n)) (acc : LocalProp n) :
    LocalProp n :=
  xs.foldl (fun a l => if !a l then propRemove a (copies l) else a) acc

/-- Exact in-place Pass 2 of `SsaLocals::meet_copy_equivalence` (`ssa.rs:185-191`, `foldl`). -/
def meetPass2List {n : Nat} (copies : CopyMap n) (xs : List (Fin n)) (acc : LocalProp n) :
    LocalProp n :=
  xs.foldl (fun a l => if !a (copies l) then propRemove a l else a) acc

/-- Exact two-pass `SsaLocals::meet_copy_equivalence` (`ssa.rs:174-198`). -/
def meetCopyEquivalence {n : Nat} (copies : CopyMap n) (prop : LocalProp n) : LocalProp n :=
  let afterPass1 := meetPass1List copies (List.finRange n) prop
  meetPass2List copies (List.finRange n) afterPass1

private theorem propRemove_self {n : Nat} (p : LocalProp n) (t : Fin n) :
    propRemove p t t = false := by
  dsimp only [propRemove]
  rw [finEq_self t]
  rfl

private theorem propRemove_ne {n : Nat} (p : LocalProp n) (t x : Fin n) (hne : x ≠ t) :
    propRemove p t x = p x := by
  dsimp only [propRemove]
  rw [(finEq_false_iff x t).mpr hne]
  rfl

private theorem meetPass1List_false_preserved {n : Nat} (copies : CopyMap n)
    (xs : List (Fin n)) (acc : LocalProp n) (x : Fin n) (hf : acc x = false) :
    meetPass1List copies xs acc x = false := by
  induction xs generalizing acc with
  | nil => exact hf
  | cons l tl ih =>
    unfold meetPass1List at ih ⊢
    dsimp only [List.foldl]
    apply ih
    cases acc l with
    | true => exact hf
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      dsimp only [propRemove]
      cases natEq x.val (copies l).val with
      | true => rfl
      | false => exact hf

private theorem meetPass1List_spec_false {n : Nat} (copies : CopyMap n)
    (xs : List (Fin n)) (acc : LocalProp n) (m : Fin n)
    (hmem : m ∈ xs) (hf : acc m = false) :
    meetPass1List copies xs acc (copies m) = false := by
  induction xs generalizing acc with
  | nil => cases hmem
  | cons l tl ih =>
    unfold meetPass1List at ih ⊢
    dsimp only [List.foldl]
    cases hmem with
    | head =>
      rw [hf]
      simp only [Bool.not_false, ↓reduceIte]
      exact meetPass1List_false_preserved copies tl _ (copies m) (propRemove_self acc (copies m))
    | tail _ htl =>
      have hfm' : (if !acc l then propRemove acc (copies l) else acc) m = false := by
        cases acc l with
        | true => exact hf
        | false =>
          simp only [Bool.not_false, ↓reduceIte]
          dsimp only [propRemove]
          cases natEq m.val (copies l).val with
          | true => rfl
          | false => exact hf
      exact ih _ htl hfm'

private theorem meetPass1List_preserves_head_if_all_true {n : Nat} (copies : CopyMap n)
    (hidem : ∀ x : Fin n, copies (copies x) = copies x)
    (xs : List (Fin n)) (acc : LocalProp n) (h : Fin n)
    (hhead : copies h = h)
    (hall : ∀ m : Fin n, copies m = h → acc m = true) :
    meetPass1List copies xs acc h = true := by
  induction xs generalizing acc with
  | nil => exact hall h hhead
  | cons l tl ih =>
    unfold meetPass1List at ih ⊢
    dsimp only [List.foldl]
    apply ih
    intro m hm
    cases hal : acc l with
    | true => exact hall m hm
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      have hclNe : copies l ≠ h := by
        intro hEq
        have htl' := hall l hEq
        rw [hal] at htl'
        cases htl'
      have hmNeCl : m ≠ copies l := by
        intro hEq
        have hcm : copies m = copies l := by
          rw [hEq]
          exact hidem l
        rw [hm] at hcm
        exact hclNe hcm.symm
      rw [propRemove_ne acc (copies l) m hmNeCl]
      exact hall m hm

private theorem meetPass2List_elem_eq {n : Nat} (copies : CopyMap n)
    (hidem : ∀ x : Fin n, copies (copies x) = copies x)
    (xs : List (Fin n)) (acc : LocalProp n) (x : Fin n)
    (hmem : x ∈ xs) :
    meetPass2List copies xs acc x = (acc x && acc (copies x)) := by
  induction xs generalizing acc with
  | nil => cases hmem
  | cons l tl ih =>
    unfold meetPass2List at ih ⊢
    dsimp only [List.foldl]
    cases hmem with
    | head =>
      cases hcx : acc (copies x) with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, Bool.and_false]
        have hfalseStay : ∀ (ys : List (Fin n)) (p : LocalProp n),
            p x = false → meetPass2List copies ys p x = false := by
          intro ys
          induction ys with
          | nil => intro p hp; exact hp
          | cons y ytl ihy =>
            intro p hp
            unfold meetPass2List at ihy ⊢
            dsimp only [List.foldl]
            apply ihy
            cases p (copies y) with
            | true => exact hp
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              dsimp only [propRemove]
              cases natEq x.val y.val with
              | true => rfl
              | false => exact hp
        exact hfalseStay tl _ (propRemove_self acc x)
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_true]
        have htrueStay : ∀ (ys : List (Fin n)) (p : LocalProp n),
            p (copies x) = true → meetPass2List copies ys p x = p x := by
          intro ys
          induction ys with
          | nil => intro p _; rfl
          | cons y ytl ihy =>
            intro p hpcx
            unfold meetPass2List at ihy ⊢
            dsimp only [List.foldl]
            have hnext : (if !p (copies y) then propRemove p y else p) (copies x) = true := by
              cases hpy : p (copies y) with
              | true => exact hpcx
              | false =>
                simp only [Bool.not_false, ↓reduceIte]
                have hne : copies x ≠ y := by
                  intro hEq
                  have hcy : copies y = copies x := by rw [← hEq]; exact hidem x
                  rw [hcy, hpcx] at hpy
                  cases hpy
                rw [propRemove_ne p y (copies x) hne]
                exact hpcx
            rw [ihy _ hnext]
            cases hpy : p (copies y) with
            | true => rfl
            | false =>
              simp only [Bool.not_false, ↓reduceIte]
              have hne : x ≠ y := by
                intro hEq
                subst hEq
                rw [hpcx] at hpy
                cases hpy
              exact propRemove_ne p y x hne
        exact htrueStay tl acc hcx
    | tail _ htl =>
      rw [ih _ htl]
      cases hcl : acc (copies l) with
      | true => rfl
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        have hcxPres : propRemove acc l (copies x) = acc (copies x) := by
          cases heq : natEq (copies x).val l.val with
          | true =>
            have hEq : copies x = l := (finEq_true_iff _ _).mp heq
            rw [← hEq, hidem x] at hcl
            rw [hEq, propRemove_self acc l, ← hEq, hcl]
          | false =>
            exact propRemove_ne acc l (copies x) ((finEq_false_iff _ _).mp heq)
        rw [hcxPres]
        cases hxl : natEq x.val l.val with
        | true =>
          have hEq : x = l := (finEq_true_iff x l).mp hxl
          subst hEq
          rw [propRemove_self acc x, hcl]
          simp [Bool.and_false]
        | false =>
          rw [propRemove_ne acc l x ((finEq_false_iff x l).mp hxl)]

/-- **Main Theorem 3b (`meetCopyEquivalence_uniform_iff_all_copies`):**
For any idempotent `copies : CopyMap n` and any initial property `prop : LocalProp n`,
the two-pass in-place `meetCopyEquivalence copies prop` satisfies:
1. **Exact characterization:** `meetCopyEquivalence copies prop l = true` iff EVERY
   local `m` in `l`'s copy class (`copies m = copies l`) satisfies `prop m = true`.
2. **Class uniformity (`ssa.rs:196`):** `meetCopyEquivalence copies prop l =
   meetCopyEquivalence copies prop (copies l)`.
3. **Monotone shrinking:** `meetCopyEquivalence copies prop l = true → prop l = true`.
4. **Idempotence of `meetCopyEquivalence`:** applying it twice equals applying it once. -/
theorem meetCopyEquivalence_uniform_iff_all_copies {n : Nat}
    (copies : CopyMap n) (hidem : ∀ x : Fin n, copies (copies x) = copies x)
    (prop : LocalProp n) :
    (∀ l : Fin n, meetCopyEquivalence copies prop l = true ↔
      ∀ m : Fin n, copies m = copies l → prop m = true) ∧
    (∀ l : Fin n, meetCopyEquivalence copies prop l =
      meetCopyEquivalence copies prop (copies l)) ∧
    (∀ l : Fin n, meetCopyEquivalence copies prop l = true → prop l = true) ∧
    (∀ l : Fin n, meetCopyEquivalence copies (meetCopyEquivalence copies prop) l =
      meetCopyEquivalence copies prop l) := by
  have hchar : ∀ (p : LocalProp n) (l : Fin n),
      meetCopyEquivalence copies p l = true ↔
      ∀ m : Fin n, copies m = copies l → p m = true := by
    intro p l
    unfold meetCopyEquivalence
    rw [meetPass2List_elem_eq copies hidem (List.finRange n) _ l (List.mem_finRange l)]
    constructor
    · intro hboth m hm
      have hp1Head : meetPass1List copies (List.finRange n) p (copies l) = true := by
        cases h2 : meetPass1List copies (List.finRange n) p (copies l) with
        | true => rfl
        | false => rw [h2, Bool.and_false] at hboth; cases hboth
      cases hpm : p m with
      | true => rfl
      | false =>
        have hfalse := meetPass1List_spec_false copies (List.finRange n) p m
          (List.mem_finRange m) hpm
        rw [hm] at hfalse
        rw [hfalse] at hp1Head
        cases hp1Head
    · intro hall
      have hp1Head : meetPass1List copies (List.finRange n) p (copies l) = true :=
        meetPass1List_preserves_head_if_all_true copies hidem (List.finRange n) p
          (copies l) (hidem l) hall
      have hp1L : meetPass1List copies (List.finRange n) p l = true := by
        cases hcl : natEq l.val (copies l).val with
        | true =>
          have hEq : l = copies l := (finEq_true_iff l (copies l)).mp hcl
          rw [hEq]
          exact hp1Head
        | false =>
          have hne : l ≠ copies l := (finEq_false_iff l (copies l)).mp hcl
          have hnotImg : ∀ x : Fin n, copies x ≠ l := by
            intro x hEq
            have hid := hidem x
            rw [hEq] at hid
            exact hne hid.symm
          have hstay : ∀ (ys : List (Fin n)) (q : LocalProp n),
              q l = true → meetPass1List copies ys q l = true := by
            intro ys
            induction ys with
            | nil => intro q hq; exact hq
            | cons y ytl ihy =>
              intro q hq
              unfold meetPass1List at ihy ⊢
              dsimp only [List.foldl]
              apply ihy
              cases q y with
              | true => exact hq
              | false =>
                simp only [Bool.not_false, ↓reduceIte]
                rw [propRemove_ne q (copies y) l (fun h => hnotImg y h.symm)]
                exact hq
          exact hstay (List.finRange n) p (hall l rfl)
      rw [hp1L, hp1Head]
      rfl
  have hunif : ∀ l : Fin n,
      meetCopyEquivalence copies prop l = meetCopyEquivalence copies prop (copies l) := by
    intro l
    cases hl : meetCopyEquivalence copies prop l with
    | true =>
      have hall := (hchar prop l).mp hl
      have hhead : meetCopyEquivalence copies prop (copies l) = true := by
        apply (hchar prop (copies l)).mpr
        intro m hm
        rw [hidem l] at hm
        exact hall m hm
      rw [hhead]
    | false =>
      cases hh : meetCopyEquivalence copies prop (copies l) with
      | false => rfl
      | true =>
        have hall := (hchar prop (copies l)).mp hh
        have hlt : meetCopyEquivalence copies prop l = true := by
          apply (hchar prop l).mpr
          intro m hm
          apply hall m
          rw [hidem l]
          exact hm
        rw [hlt] at hl
        cases hl
  have hshrink : ∀ l : Fin n, meetCopyEquivalence copies prop l = true → prop l = true := by
    intro l hl
    exact (hchar prop l).mp hl l rfl
  have hmeetIdem : ∀ l : Fin n,
      meetCopyEquivalence copies (meetCopyEquivalence copies prop) l =
      meetCopyEquivalence copies prop l := by
    intro l
    cases hl : meetCopyEquivalence copies prop l with
    | true =>
      apply (hchar (meetCopyEquivalence copies prop) l).mpr
      intro m hm
      rw [hunif m, hm, ← hunif l]
      exact hl
    | false =>
      cases h2 : meetCopyEquivalence copies (meetCopyEquivalence copies prop) l with
      | false => rfl
      | true =>
        have hl' := ((hchar (meetCopyEquivalence copies prop) l).mp h2) l rfl
        rw [hl] at hl'
        cases hl'
  exact ⟨hchar prop, hunif, hshrink, hmeetIdem⟩

/-- Non-idempotent counterexample showing why `copies[copies[x]] = copies[x]` (`ssa.rs:355`)
is strictly necessary for two-pass `meet_copy_equivalence` uniformity (`ssa.rs:196`). -/
def nonIdemCopies : CopyMap 3 := fun x =>
  match x.val with
  | 0 => ⟨0, Nat.zero_lt_succ 2⟩
  | 1 => ⟨0, Nat.zero_lt_succ 2⟩
  | _ => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩

def nonIdemProp : LocalProp 3 := fun x =>
  match x.val with
  | 2 => false
  | _ => true

theorem meetCopyEquivalence_requires_idempotence :
    meetCopyEquivalence nonIdemCopies nonIdemProp ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩ = false ∧
    meetCopyEquivalence nonIdemCopies nonIdemProp
      (nonIdemCopies ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩) = true :=
  ⟨rfl, rfl⟩

/-!
================================================================================
## Part IV: `CheckPointers` (`check_pointers.rs`, `check_alignment.rs`, `check_null.rs`)
================================================================================
-/

/-- Exact `BorrowedFieldProjectionMode` enum from `check_pointers.rs:19-22`. -/
inductive BorrowedFieldProjectionMode where
  | followProjections : BorrowedFieldProjectionMode
  | noFollowProjections : BorrowedFieldProjectionMode

/-- Block splitting transformation performed by `check_pointers` (`check_pointers.rs:126-141`). -/
def splitBlockCfg (cfg : MirCfg) (b : Nat) : MirCfg :=
  let newBb := cfg.numBlocks
  { numBlocks := cfg.numBlocks + 1
  , isCleanup := fun x => if natEq x newBb then cfg.isCleanup b else cfg.isCleanup x
  , canUnwind := cfg.canUnwind
  , edges :=
      { src := b, dst := newBb, kind := .normal } ::
      cfg.edges.map (fun e => if natEq e.src b then { e with src := newBb } else e)
  , exitOf := fun x =>
      if natEq x newBb then cfg.exitOf b
      else if natEq x b then .nonExit
      else cfg.exitOf x }

/-- **Main Theorem 4a (`checkPointers_splitBlock_preserves_validCfg`):**
Splitting any valid block `b` in `check_pointers` (`check_pointers.rs:126-141`) preserves
all `ValidCfg` invariants (`START_BLOCK` zero-predecessor, 3-of-8 `(is_cleanup, EdgeKind)`
matrix, and exit legality), and its `Assert` terminator uses `UnwindAction.unreachable`
which is valid in both `isCleanup = false` and `isCleanup = true` blocks. -/
theorem checkPointers_splitBlock_preserves_validCfg (cfg : MirCfg) (hv : ValidCfg cfg)
    (b : Nat) (hb : b < cfg.numBlocks) :
    ValidCfg (splitBlockCfg cfg b) ∧
    (∀ c cu f, validUnwindAction c cu f .unreachable = true) := by
  have hnewNe0 : cfg.numBlocks ≠ 0 := Nat.ne_of_gt hv.startInBounds
  have h0NeNew : natEq 0 cfg.numBlocks = false :=
    (natEq_false_iff 0 cfg.numBlocks).mpr (fun h => hnewNe0 h.symm)
  have hclOld : ∀ x, x < cfg.numBlocks →
      (splitBlockCfg cfg b).isCleanup x = cfg.isCleanup x := by
    intro x hx
    unfold splitBlockCfg
    have hne : natEq x cfg.numBlocks = false :=
      (natEq_false_iff x cfg.numBlocks).mpr (Nat.ne_of_lt hx)
    change (if natEq x cfg.numBlocks = true then cfg.isCleanup b else cfg.isCleanup x) = cfg.isCleanup x
    rw [hne]
    rfl
  have hclNew : (splitBlockCfg cfg b).isCleanup cfg.numBlocks = cfg.isCleanup b := by
    unfold splitBlockCfg
    change (if natEq cfg.numBlocks cfg.numBlocks = true then cfg.isCleanup b else cfg.isCleanup cfg.numBlocks) = cfg.isCleanup b
    rw [natEq_self cfg.numBlocks]
    rfl
  refine ⟨?_, fun _ _ _ => rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_of_lt hv.startInBounds
  · unfold splitBlockCfg
    change (if natEq 0 cfg.numBlocks = true then cfg.isCleanup b else cfg.isCleanup 0) = false
    rw [h0NeNew]
    exact hv.startNotCleanup
  · intro e he
    unfold splitBlockCfg at he
    cases he with
    | head => exact hnewNe0
    | tail _ hmap =>
      rcases List.mem_map.mp hmap with ⟨e0, he0, rfl⟩
      cases natEq e0.src b with
      | true => exact hv.noStartPred e0 he0
      | false => exact hv.noStartPred e0 he0
  · intro e he
    unfold splitBlockCfg at he
    cases he with
    | head => exact ⟨Nat.lt_succ_of_lt hb, Nat.lt_succ_self cfg.numBlocks⟩
    | tail _ hmap =>
      rcases List.mem_map.mp hmap with ⟨e0, he0, rfl⟩
      have ⟨hs0, hd0⟩ := hv.edgesInBounds e0 he0
      cases natEq e0.src b with
      | true => exact ⟨Nat.lt_succ_self cfg.numBlocks, Nat.lt_succ_of_lt hd0⟩
      | false => exact ⟨Nat.lt_succ_of_lt hs0, Nat.lt_succ_of_lt hd0⟩
  · intro e he
    unfold splitBlockCfg at he
    cases he with
    | head =>
      change validEdgeTransition
        ((splitBlockCfg cfg b).isCleanup b)
        ((splitBlockCfg cfg b).isCleanup cfg.numBlocks) .normal = true
      rw [hclOld b hb, hclNew]
      cases cfg.isCleanup b <;> rfl
    | tail _ hmap =>
      rcases List.mem_map.mp hmap with ⟨e0, he0, rfl⟩
      have ⟨hs0, hd0⟩ := hv.edgesInBounds e0 he0
      have hve0 := hv.edgesValid e0 he0
      cases hsb : natEq e0.src b with
      | true =>
        have hEq : e0.src = b := (natEq_true_iff e0.src b).mp hsb
        simp only [↓reduceIte]
        change validEdgeTransition
          ((splitBlockCfg cfg b).isCleanup cfg.numBlocks)
          ((splitBlockCfg cfg b).isCleanup e0.dst) e0.kind = true
        rw [hclNew, hclOld e0.dst hd0, ← hEq]
        exact hve0
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        change validEdgeTransition
          ((splitBlockCfg cfg b).isCleanup e0.src)
          ((splitBlockCfg cfg b).isCleanup e0.dst) e0.kind = true
        rw [hclOld e0.src hs0, hclOld e0.dst hd0]
        exact hve0
  · intro bb hbb
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hbb) with
    | inr hEq =>
      subst hEq
      rw [hclNew]
      unfold splitBlockCfg
      change validExitKind (cfg.isCleanup b) cfg.canUnwind
        (if natEq cfg.numBlocks cfg.numBlocks = true then cfg.exitOf b
         else if natEq cfg.numBlocks b = true then .nonExit else cfg.exitOf cfg.numBlocks) = true
      rw [natEq_self cfg.numBlocks]
      exact hv.exitsValid b hb
    | inl hlt =>
      rw [hclOld bb hlt]
      have hneNew : natEq bb cfg.numBlocks = false :=
        (natEq_false_iff bb cfg.numBlocks).mpr (Nat.ne_of_lt hlt)
      unfold splitBlockCfg
      change validExitKind (cfg.isCleanup bb) cfg.canUnwind
        (if natEq bb cfg.numBlocks = true then cfg.exitOf b
         else if natEq bb b = true then .nonExit else cfg.exitOf bb) = true
      rw [hneNew]
      cases natEq bb b with
      | true => rfl
      | false => exact hv.exitsValid bb hlt

/-- **Main Theorem 4b (`aligned_base_iff_aligned_field`):**
Whenever a field's byte offset is a multiple of the field's alignment (`offset % align = 0`,
guaranteed by Rust layout for every non-`#[repr(packed)]` struct/tuple), checking
alignment on the base pointer address (`addr % align = 0`, as `check_pointers.rs:208`
+ `check_alignment.rs:32` do under `BorrowedFieldProjectionMode::FollowProjections`)
is mathematically equivalent to checking alignment on the projected field address
(`(addr + offset) % align = 0`). -/
theorem aligned_base_iff_aligned_field (addr offset align : Nat)
    (hoff : offset % align = 0) :
    addr % align = 0 ↔ (addr + offset) % align = 0 := by
  rw [Nat.add_mod, hoff, Nat.add_zero, Nat.mod_mod]

end MirValidatorSsaSoundness
