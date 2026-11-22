/-!
# Consolidated `rustc` Query Engine: Red-Green Early Cutoff, `QueryMode::EnsureOk`,
# Rotating vs. Unconditional ICH Verification, `feedable` Consistency, and
# Multi-Tier Cycle / Depth-Limit Recovery

Standalone kernel-checked Lean `v4.34.1` mechanization grounded in `rust-lang/rust`
(`compiler/rustc_middle/src/{queries.rs, dep_graph/graph.rs, query/calls.rs, query/system.rs}`,
`compiler/rustc_query_impl/src/{execution.rs, incremental.rs, dep_kind_vtables.rs, handle_cycle_error.rs}`,
and `compiler/rustc_incremental/src/{assert_dep_graph.rs, persist/save.rs}`).

Axiom and hygiene discipline:
- Zero incomplete proofs (`0` proof holes).
- Purely constructive proofs (no non-constructive choice axioms).
- No arithmetic SMT/decision reflection tactics or unverified codegen shims.
- All definitions are marked `noncomputable def` with zero auto-derived `Repr` instances.
-/

namespace RustcQueryEngineSoundness

/-! ## Section 1: Core Query System & Red-Green Dependency Graph Model -/

/-- Query invocation mode (`compiler/rustc_middle/src/query/system.rs:19-24`). -/
inductive QueryMode where
  | get
  | ensureOk

/-- Color assigned to a previous-session `DepNode` during the current session
    (`compiler/rustc_middle/src/dep_graph/graph.rs:127-131`). -/
inductive DepColor where
  | unknown
  | red
  | green

/-- Outcome of executing `execute_query_incr_inner` in `QueryMode::EnsureOk`
    (`compiler/rustc_query_impl/src/execution.rs:595-665`). -/
inductive EnsureOkOutcome where
  /-- `ensure_can_skip_execution` returned `true`: returned `None` with zero
      `query-cache.bin` deserialization and zero provider invocation. -/
  | skippedNoDiskLoad
  /-- `ensure_can_skip_execution` returned `false`: fell through to `try_execute_query`. -/
  | fellThroughToExecute

/-- Query modifier metadata corresponding to `QueryVTable` / `DepKindVTable`
    (`compiler/rustc_middle/src/query/system.rs:27-90`,
     `compiler/rustc_query_impl/src/dep_kind_vtables.rs:101-130`). -/
structure QueryMeta where
  evalAlways : Bool
  cacheOnDisk : Bool
  noHash : Bool
  feedable : Bool
  noForce : Bool
  canRecoverKey : Bool
  depthLimit : Bool
  handleCycleError : Bool

/-- Whether `DepKindVTable::force_from_dep_node_fn` is populated
    (`compiler/rustc_query_impl/src/dep_kind_vtables.rs:117`). -/
noncomputable def forceEnabled (m : QueryMeta) : Bool :=
  m.canRecoverKey && !m.noForce

/-- Abstract two-session incremental compilation model over query keys `Q` and values `Val`. -/
structure QuerySystemModel (Q : Type) (Val : Type) where
  metaOf : Q → QueryMeta
  /-- Previous-session dependency edges `prevDeps q` recorded in `dep-graph.bin`. -/
  prevDeps : Q → List Q
  /-- Previous-session semantic value for each query present in the prior graph. -/
  prevVal : Q → Val
  /-- Current-session semantic value produced by the query provider. -/
  currVal : Q → Val
  /-- Stable incremental compilation hash (`StableHash` -> 128-bit `Fingerprint`). -/
  valHash : Val → Nat
  /-- Previous-session diagnostic/error-free status (`prevOk q` holds for any committed session,
      since `save_dep_graph` aborts when `has_errors_or_delayed_bugs().is_some()`). -/
  prevOk : Q → Prop
  /-- Current-session error-free status for query `q`. -/
  currOk : Q → Prop
  /-- Whether `q` has a serialized value in `query-cache.bin`. -/
  diskCache : Q → Option Val

/-- Previous-session stored value fingerprint (`SerializedDepGraph::value_fingerprints`).
    For `no_hash` queries, `rustc` stores `Fingerprint::ZERO` (`graph.rs:810-817`). -/
noncomputable def prevStoredHash {Q Val : Type} (S : QuerySystemModel Q Val) (q : Q) : Nat :=
  if (S.metaOf q).noHash then 0 else S.valHash (S.prevVal q)

/-- Static reachability in the previous-session dependency graph (`assert_dep_graph.rs:194`).
    `StaticReachable prevDeps target source` means `target` transitively depends on `source`. -/
inductive StaticReachable {Q : Type} (prevDeps : Q → List Q) : Q → Q → Prop where
  | refl (q : Q) : StaticReachable prevDeps q q
  | step {q d src : Q} :
      d ∈ prevDeps q →
      StaticReachable prevDeps d src →
      StaticReachable prevDeps q src

/-- Soundness of tracked dependencies for non-`eval_always` queries:
    if every recorded dependency `d ∈ prevDeps q` preserves its value from the
    previous session, then `q` produces the same value and preserves error-freedom. -/
noncomputable def DepTrackingSound {Q Val : Type} (S : QuerySystemModel Q Val) : Prop :=
  ∀ q : Q,
    (S.metaOf q).evalAlways = false →
    (∀ d : Q, d ∈ S.prevDeps q → S.currVal d = S.prevVal d) →
    S.currVal q = S.prevVal q ∧ (S.prevOk q → S.currOk q)

/-- Collision freedom (injectivity) of the 128-bit stable hash on query results. -/
noncomputable def HashCollisionFree {Val : Type} (h : Val → Nat) : Prop :=
  ∀ v₁ v₂ : Val, h v₁ = h v₂ → v₁ = v₂

/-- Inductive red-green marking relation faithfully modeling
    `DepGraphData::try_mark_green` + `try_mark_previous_green` + `alloc_and_color_node`
    (`compiler/rustc_middle/src/dep_graph/graph.rs:791-835, 903-1029`).

    A node `q` can be colored **green** in two ways:
    1. `forcedSameHash`: `q` was forced/re-executed (`alloc_and_color_node` lines 799-803),
       `q` is NOT `no_hash` (lines 809-815: `no_hash` always marks red on recomputation),
       and its recomputed fingerprint equals `prevStoredHash S q`.
       This is the exact **early-cutoff** rule.
    2. `allDepsGreen`: `q` is NOT `eval_always` (`graph.rs:908, 949, 971`) and every
       dependency `d ∈ prevDeps q` is marked green (either recursively or via forced
       early cutoff). -/
inductive MarkedGreen {Q Val : Type} (S : QuerySystemModel Q Val) : Q → Prop where
  | forcedSameHash {q : Q} :
      (S.metaOf q).noHash = false →
      S.valHash (S.currVal q) = prevStoredHash S q →
      (S.prevOk q → S.currOk q) →
      MarkedGreen S q
  | allDepsGreen {q : Q} :
      (S.metaOf q).evalAlways = false →
      (∀ d : Q, d ∈ S.prevDeps q → MarkedGreen S d) →
      MarkedGreen S q

/-- `ensure_can_skip_execution` (`compiler/rustc_query_impl/src/execution.rs:595-626`)
    paired with `execute_query_incr_inner` (`execution.rs:643-665`).
    Notice that disk deserialization (`try_load_from_disk_fn`) is NEVER invoked on
    the `skippedNoDiskLoad` branch even when `(S.metaOf q).cacheOnDisk = true`. -/
inductive EnsureOkExec {Q Val : Type} (S : QuerySystemModel Q Val) (q : Q) :
    EnsureOkOutcome → Bool → Prop where
  | skipGreen :
      (S.metaOf q).evalAlways = false →
      MarkedGreen S q →
      EnsureOkExec S q EnsureOkOutcome.skippedNoDiskLoad false
  | fallThroughEvalAlways :
      (S.metaOf q).evalAlways = true →
      EnsureOkExec S q EnsureOkOutcome.fellThroughToExecute false
  | fallThroughNotGreen :
      ¬ MarkedGreen S q →
      EnsureOkExec S q EnsureOkOutcome.fellThroughToExecute false

/-- Core induction: under sound dependency tracking and hash collision freedom,
    every green-marked node preserves its previous-session semantic value and
    error-free status, including across early-cutoff boundaries. -/
theorem markedGreen_preserves_value_and_ok
    {Q Val : Type}
    (S : QuerySystemModel Q Val)
    (hDep : DepTrackingSound S)
    (hInj : HashCollisionFree S.valHash)
    {q : Q}
    (hGreen : MarkedGreen S q) :
    S.currVal q = S.prevVal q ∧ (S.prevOk q → S.currOk q) := by
  induction hGreen with
  | @forcedSameHash q' hNoHash hHashEq hOk =>
    have hPrev : prevStoredHash S q' = S.valHash (S.prevVal q') := by
      unfold prevStoredHash
      rw [hNoHash]
      rfl
    rw [hPrev] at hHashEq
    exact ⟨hInj _ _ hHashEq, hOk⟩
  | @allDepsGreen q' hNotEval _ ih =>
    apply hDep q' hNotEval
    intro d hd
    exact (ih d hd).1

/-- **Theorem 1: Red-Green Early-Cutoff & `QueryMode::EnsureOk` Deserialization-Skip Soundness.**

    Given sound dependency tracking (`DepTrackingSound`) and ICH collision freedom
    (`HashCollisionFree`), if a non-`eval_always` query `q` is marked green (potentially
    via early cutoff at an intermediate query whose own upstream HIR input mutated), then:
    1. `q`'s current semantic value equals its previous-session value (`currVal q = prevVal q`),
    2. `q` preserves error-freedom (`prevOk q → currOk q`), AND
    3. `QueryMode::EnsureOk` soundly skips BOTH provider execution and `query-cache.bin`
       deserialization (`EnsureOkOutcome.skippedNoDiskLoad`, `loadedFromDisk = false`),
       regardless of whether `cacheOnDisk = true` and `diskCache q = some v`. -/
theorem ensureOk_green_skip_and_early_cutoff_sound
    {Q Val : Type}
    (S : QuerySystemModel Q Val)
    (hDep : DepTrackingSound S)
    (hInj : HashCollisionFree S.valHash)
    (q : Q)
    (hNotEval : (S.metaOf q).evalAlways = false)
    (hGreen : MarkedGreen S q) :
    S.currVal q = S.prevVal q ∧
    (S.prevOk q → S.currOk q) ∧
    EnsureOkExec S q EnsureOkOutcome.skippedNoDiskLoad false := by
  have hPres := markedGreen_preserves_value_and_ok S hDep hInj hGreen
  exact ⟨hPres.1, hPres.2, EnsureOkExec.skipGreen hNotEval hGreen⟩

/-! ## Section 2: 32-Session Rotating vs. Unconditional `100%` ICH Verification -/

/-- Constructive arithmetic helpers. -/
private theorem nat_mod_lt_32 (n : Nat) : n % 32 < 32 :=
  Nat.mod_lt n (Nat.zero_lt_succ 31)

private theorem nat_add_mod_self_cancel (a b : Nat) (h : b < 32) :
    (b + (a + (32 - b))) % 32 = a % 32 := by
  have hle : b ≤ 32 := Nat.le_of_lt h
  have h1 : b + (a + (32 - b)) = a + (b + (32 - b)) := by
    rw [Nat.add_left_comm]
  rw [h1, Nat.add_sub_cancel' hle, Nat.add_mod_right]

private theorem nat_beq_self_true (n : Nat) : Nat.beq n n = true :=
  Nat.beq_refl n

private theorem nat_eq_of_beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

/-- `should_verify_loaded_value` at `rust-lang/rust` HEAD (`342d74463`,
    `compiler/rustc_query_impl/src/incremental.rs:95-103`). -/
noncomputable def shouldVerifyLoaded (verifyFlag : Bool) (sessionCount keyHash : Nat) : Bool :=
  Nat.beq (keyHash % 32) (sessionCount % 32) || verifyFlag

/-- Historical static `1/32` slice at `1.98.0-nightly` (`14210df0e`,
    `compiler/rustc_query_impl/src/execution.rs:523-524`). -/
noncomputable def shouldVerifyLoadedStatic198 (verifyFlag : Bool) (prevValHash : Nat) : Bool :=
  Nat.beq (prevValHash % 32) 0 || verifyFlag

/-- Unified verification decision in `load_from_disk_or_invoke_provider_green`
    (`compiler/rustc_query_impl/src/execution.rs:544-563`):
    - `diskLoaded = some _`: uses `shouldVerifyLoaded` (`1/32` rotating or `-Zincremental-verify-ich`);
    - `diskLoaded = none`: recomputed green hit sets `verify = true` (`100%` unconditional). -/
noncomputable def shouldVerifyGreen
    {Val : Type}
    (verifyFlag : Bool)
    (sessionCount keyHash : Nat)
    (diskLoaded : Option Val) : Bool :=
  match diskLoaded with
  | some _ => shouldVerifyLoaded verifyFlag sessionCount keyHash
  | none => true

/-- Outcome of `incremental_verify_ich` (`compiler/rustc_middle/src/verify_ich.rs:14-35`). -/
inductive IchCheckOutcome where
  | skipped
  | verifiedMatch
  | unstableFingerprintIce

/-- Full green-node ICH check combining `load_from_disk_or_invoke_provider_green`
    and `incremental_verify_ich`. -/
noncomputable def runGreenIchCheck
    {Val : Type}
    (verifyFlag : Bool)
    (sessionCount keyHash prevHash currHash : Nat)
    (diskLoaded : Option Val) : IchCheckOutcome :=
  if shouldVerifyGreen verifyFlag sessionCount keyHash diskLoaded then
    if Nat.beq currHash prevHash then
      IchCheckOutcome.verifiedMatch
    else
      IchCheckOutcome.unstableFingerprintIce
  else
    IchCheckOutcome.skipped

/-- Explicit constructive witness for the session offset `k < 32` at which `keyHash`
    hits the rotating `1/32` verification slice starting from `session0`. -/
noncomputable def rotatingOffset (session0 keyHash : Nat) : Nat :=
  (keyHash % 32 + (32 - session0 % 32)) % 32

theorem rotatingOffset_lt_32 (session0 keyHash : Nat) :
    rotatingOffset session0 keyHash < 32 :=
  nat_mod_lt_32 _

theorem rotatingOffset_hits_slice (session0 keyHash : Nat) :
    (session0 + rotatingOffset session0 keyHash) % 32 = keyHash % 32 := by
  unfold rotatingOffset
  have h1 :
      (session0 + (keyHash % 32 + (32 - session0 % 32)) % 32) % 32 =
      (session0 % 32 + (keyHash % 32 + (32 - session0 % 32)) % 32 % 32) % 32 :=
    Nat.add_mod _ _ _
  have h2 :
      (session0 % 32 + (keyHash % 32 + (32 - session0 % 32))) % 32 =
      (session0 % 32 % 32 + (keyHash % 32 + (32 - session0 % 32)) % 32) % 32 :=
    Nat.add_mod _ _ _
  rw [Nat.mod_mod] at h1
  rw [Nat.mod_mod] at h2
  rw [h1, ← h2]
  rw [nat_add_mod_self_cancel (keyHash % 32) (session0 % 32) (nat_mod_lt_32 session0)]
  exact Nat.mod_mod keyHash 32

/-- **Theorem 2: 32-Session Rotating + `100%` Recomputed-Green ICH Verification Coverage.**

    Establishes four exact properties of the asymmetric ICH verification policy:
    1. **32-Session Rotating Completeness (HEAD `incremental.rs:100-103`):** For any
       starting `session0` and any `keyHash`, there exists `k < 32` such that
       `shouldVerifyLoaded false (session0 + k) keyHash = true`.
    2. **Unconditional `100%` Verification on Non-Disk Recomputed Green Hits
       (`execution.rs:554-562`):** Whenever `diskLoaded = none`, `shouldVerifyGreen`
       returns `true` for every `(verifyFlag, sessionCount, keyHash)` and catches any
       fingerprint mismatch (`currHash ≠ prevHash`) as `IchCheckOutcome.unstableFingerprintIce`.
    3. **Full Override under `-Zincremental-verify-ich`:** Setting `verifyFlag = true`
       forces `shouldVerifyGreen true sessionCount keyHash diskLoaded = true` even for
       disk-loaded hits.
    4. **Strict Separation from Historical Static `1/32` (`1.98.0-nightly` `execution.rs:523`):**
       There exists a concrete fingerprint (`prevValHash = 1`) that `shouldVerifyLoadedStatic198`
       NEVER verifies across any number of sessions when `verifyFlag = false`. -/
theorem ich_rotating_32_and_recomputed_green_complete :
    (∀ session0 keyHash : Nat,
      ∃ k : Nat, k < 32 ∧ shouldVerifyLoaded false (session0 + k) keyHash = true) ∧
    (∀ (Val : Type) (verifyFlag : Bool) (sessionCount keyHash prevHash currHash : Nat),
      shouldVerifyGreen (Val := Val) verifyFlag sessionCount keyHash none = true ∧
      (currHash ≠ prevHash →
        runGreenIchCheck (Val := Val) verifyFlag sessionCount keyHash prevHash currHash none =
          IchCheckOutcome.unstableFingerprintIce)) ∧
    (∀ (Val : Type) (sessionCount keyHash : Nat) (diskLoaded : Option Val),
      shouldVerifyGreen true sessionCount keyHash diskLoaded = true) ∧
    (∃ prevValHash : Nat, ∀ _session : Nat,
      shouldVerifyLoadedStatic198 false prevValHash = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro session0 keyHash
    refine ⟨rotatingOffset session0 keyHash, rotatingOffset_lt_32 session0 keyHash, ?_⟩
    unfold shouldVerifyLoaded
    rw [rotatingOffset_hits_slice session0 keyHash, nat_beq_self_true]
    rfl
  · intro Val verifyFlag sessionCount keyHash prevHash currHash
    constructor
    · rfl
    · intro hNe
      unfold runGreenIchCheck shouldVerifyGreen
      have hBeqFalse : Nat.beq currHash prevHash = false := by
        cases hEq : Nat.beq currHash prevHash with
        | false => rfl
        | true =>
          exfalso
          exact hNe (nat_eq_of_beq_true hEq)
      rw [hBeqFalse]
      rfl
  · intro Val sessionCount keyHash diskLoaded
    cases diskLoaded with
    | none => rfl
    | some _ =>
      unfold shouldVerifyGreen shouldVerifyLoaded
      cases Nat.beq (keyHash % 32) (sessionCount % 32) <;> rfl
  · refine ⟨1, ?_⟩
    intro _session
    rfl

/-! ## Section 3: `feedable` Consistency, `no_force` Cycle-Stack Completeness,
    Cycle Nesting Dispatch, Frame Rotation, and Depth-Limit Progress -/

/-- Outcome of `check_feedable_consistency` (`compiler/rustc_query_impl/src/execution.rs:363-401`). -/
inductive FeedConsistencyResult where
  /-- Key was not previously fed in memory; normal completion proceeds. -/
  | notPreviouslyFed
  /-- `no_hash` fed query was later recomputed (`execution.rs:375-382`): unconditional panic. -/
  | panicNoHashRecompute
  /-- Hashes matched (`old_hash == new_hash`). -/
  | okHashMatch
  /-- Hashes differed, tolerated only because compilation already has errors (`execution.rs:391-392`). -/
  | okErrorTainted
  /-- Hashes differed on an error-free compilation (`execution.rs:391-399`): assertion failure. -/
  | panicInconsistent

/-- Direct model of `check_feedable_consistency` (`execution.rs:363-401`). -/
noncomputable def checkFeedableConsistency
    {Val : Type}
    (cached : Option Val)
    (hashFn : Option (Val → Nat))
    (hasErrors : Bool)
    (computed : Val) : FeedConsistencyResult :=
  match cached with
  | none => FeedConsistencyResult.notPreviouslyFed
  | some oldVal =>
    match hashFn with
    | none => FeedConsistencyResult.panicNoHashRecompute
    | some h =>
      if Nat.beq (h oldVal) (h computed) then
        FeedConsistencyResult.okHashMatch
      else if hasErrors then
        FeedConsistencyResult.okErrorTainted
      else
        FeedConsistencyResult.panicInconsistent

/-- Multi-tier cycle nesting dispatch (`compiler/rustc_query_impl/src/execution.rs:47-66`). -/
inductive CycleDispatch where
  | customOrDefaultHandler
  | forcedDefaultNested
  | fatalDoublyNestedBug

noncomputable def dispatchCycleNesting (nesting : Nat) : CycleDispatch :=
  match nesting with
  | 0 => CycleDispatch.customOrDefaultHandler
  | 1 => CycleDispatch.forcedDefaultNested
  | _ => CycleDispatch.fatalDoublyNestedBug

/-- `depth_limit_error` suggested limit (`compiler/rustc_query_impl/src/execution.rs:407-410`):
    `Limit(0) => Limit(2)`, `limit => limit * 2`. -/
noncomputable def suggestedRecursionLimit (limit : Nat) : Nat :=
  match limit with
  | 0 => 2
  | n + 1 => (n + 1) * 2

/-- Left cyclic rotation of a list by `k` steps (`VecDeque::rotate_left(1)` in
    `handle_cycle_error.rs:110-126`). -/
noncomputable def rotateLeftOnce {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

noncomputable def rotateLeft {α : Type} : Nat → List α → List α
  | 0, xs => xs
  | n + 1, xs => rotateLeft n (rotateLeftOnce xs)

private theorem rotateLeftOnce_head_of_append {α : Type} (xs ys : List α) :
    rotateLeft xs.length (xs ++ ys) = ys ++ xs := by
  induction xs generalizing ys with
  | nil =>
    simp [rotateLeft]
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append, rotateLeft, rotateLeftOnce]
    have hAssoc : (xs ++ ys) ++ [x] = xs ++ (ys ++ [x]) := List.append_assoc xs ys [x]
    rw [hAssoc]
    rw [ih (ys ++ [x])]
    exact List.append_assoc ys [x] xs

private theorem split_at_mem {α : Type} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ pre suf : List α, xs = pre ++ (x :: suf) ∧ pre.length < xs.length := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head =>
      exact ⟨[], ys, rfl, Nat.zero_lt_succ ys.length⟩
    | tail _ hMem =>
      obtain ⟨pre, suf, hEq, hLt⟩ := ih hMem
      refine ⟨y :: pre, suf, ?_, Nat.succ_lt_succ hLt⟩
      simp [hEq]

/-- Completeness of `search_for_cycle_permutation` (`handle_cycle_error.rs:110-126`):
    if any frame `x ∈ frames` satisfies `P`, then some cyclic rotation `r < frames.length`
    places `x` at index `0` (`rotateLeft r frames = x :: tail`). -/
theorem search_for_cycle_permutation_complete
    {α : Type}
    (frames : List α)
    (P : α → Prop)
    (hEx : ∃ x, x ∈ frames ∧ P x) :
    ∃ r : Nat, r < frames.length ∧ ∃ hd tl, rotateLeft r frames = hd :: tl ∧ P hd := by
  obtain ⟨x, hMem, hPx⟩ := hEx
  obtain ⟨pre, suf, hEq, hLt⟩ := split_at_mem hMem
  refine ⟨pre.length, hLt, x, suf ++ pre, ?_, hPx⟩
  rw [hEq]
  exact rotateLeftOnce_head_of_append pre (x :: suf)

/-- Abstract active query-stack visibility during red-green `try_mark_previous_green`
    vs. normal execution (`compiler/rustc_middle/src/dep_graph/graph.rs:951-997`,
    `compiler/rustc_query_impl/src/dep_kind_vtables.rs:117-122`).

    When `try_mark_previous_green` visits a dependency `d` of `q`, if `forceEnabled (metaOf d)`
    is `true`, `rustc` invokes `force_query_dep_node(d)` while `q` is NOT yet executing its
    provider body (so `q` is absent from `d`'s `QueryJob` parent chain during the forced call).
    When `noForce = true`, `forceEnabled` is `false`, so `try_mark_previous_green` returns
    `None`, forcing normal top-down execution where `q` IS pushed onto the active `QueryJob`
    stack before calling `d`. -/
noncomputable def cycleStackAfterDepCheck
    {Q : Type}
    (metaOf : Q → QueryMeta)
    (caller callee : Q) : List Q :=
  if forceEnabled (metaOf callee) then
    -- Out-of-band `force_query_dep_node(callee)`: caller is NOT on the forced job's stack.
    [callee]
  else
    -- `force_from_dep_node_fn == None` (`no_force`): falls back to normal execution with caller on stack.
    [caller, callee]

/-- **Theorem 3: `feedable` Hash-Consistency, `no_force` Cycle-Stack Completeness,
    Multi-Tier Cycle Nesting, Permutation Search, and Depth-Limit Strict Progress.** -/
theorem feedable_consistency_and_no_force_cycle_stack_sound :
    -- (1) `feedable + no_hash` recomputation unconditionally panics (`execution.rs:375-382`)
    (∀ (Val : Type) (oldVal computed : Val) (hasErrors : Bool),
      checkFeedableConsistency (some oldVal) none hasErrors computed =
        FeedConsistencyResult.panicNoHashRecompute) ∧
    -- (2) Error-free hashed `feedable` recomputation succeeds iff hashes match (`execution.rs:384-400`)
    (∀ (Val : Type) (oldVal computed : Val) (h : Val → Nat),
      checkFeedableConsistency (some oldVal) (some h) false computed =
        FeedConsistencyResult.okHashMatch ↔ h oldVal = h computed) ∧
    -- (3) `no_force` disables `force_from_dep_node_fn` (`dep_kind_vtables.rs:117`) and
    --     preserves both caller and callee frames on the active cycle stack
    (∀ (Q : Type) (metaOf : Q → QueryMeta) (caller callee : Q),
      (metaOf callee).noForce = true →
      forceEnabled (metaOf callee) = false ∧
      caller ∈ cycleStackAfterDepCheck metaOf caller callee ∧
      callee ∈ cycleStackAfterDepCheck metaOf caller callee) ∧
    -- (4) Multi-tier cycle nesting (`execution.rs:47-66`)
    (dispatchCycleNesting 0 = CycleDispatch.customOrDefaultHandler ∧
     dispatchCycleNesting 1 = CycleDispatch.forcedDefaultNested ∧
     (∀ n : Nat, dispatchCycleNesting (n + 2) = CycleDispatch.fatalDoublyNestedBug)) ∧
    -- (5) Depth-limit suggestion strictly exceeds current limit (`execution.rs:407-410`)
    (∀ L : Nat, L < suggestedRecursionLimit L) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro Val oldVal computed hasErrors
    rfl
  · intro Val oldVal computed h
    dsimp only [checkFeedableConsistency]
    constructor
    · intro hOk
      cases hEq : Nat.beq (h oldVal) (h computed) with
      | true => exact nat_eq_of_beq_true hEq
      | false =>
        rw [hEq] at hOk
        cases hOk
    · intro hEq
      rw [hEq, nat_beq_self_true]
      rfl
  · intro Q metaOf caller callee hNoForce
    have hForceFalse : forceEnabled (metaOf callee) = false := by
      unfold forceEnabled
      rw [hNoForce]
      cases (metaOf callee).canRecoverKey <;> rfl
    refine ⟨hForceFalse, ?_, ?_⟩
    · unfold cycleStackAfterDepCheck
      rw [hForceFalse]
      exact List.Mem.head _
    · unfold cycleStackAfterDepCheck
      rw [hForceFalse]
      exact List.Mem.tail _ (List.Mem.head _)
  · refine ⟨rfl, rfl, ?_⟩
    intro n
    rfl
  · intro L
    cases L with
    | zero =>
      dsimp only [suggestedRecursionLimit]
      exact Nat.zero_lt_succ 1
    | succ n =>
      dsimp only [suggestedRecursionLimit]
      have hMul : (n + 1) * 2 = (n + 1) + (n + 1) := by
        rw [Nat.mul_succ, Nat.mul_one]
      rw [hMul]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)

/-! ## Section 4: Constructive Sharpness Counterexamples -/

/-- Three-node crate model witnessing static reachability vs. dynamic early cutoff
    (`hir_owner(helper_body) -> fn_sig(helper_body) -> typeck_root(caller_reused)`). -/
inductive CutoffNode where
  | hirOwnerHelper
  | fnSigHelper
  | typeckRootCaller

noncomputable def cutoffMeta : CutoffNode → QueryMeta
  | CutoffNode.hirOwnerHelper =>
      { evalAlways := false, cacheOnDisk := false, noHash := false, feedable := true,
        noForce := false, canRecoverKey := true, depthLimit := false, handleCycleError := false }
  | CutoffNode.fnSigHelper =>
      { evalAlways := false, cacheOnDisk := true, noHash := false, feedable := false,
        noForce := false, canRecoverKey := true, depthLimit := false, handleCycleError := true }
  | CutoffNode.typeckRootCaller =>
      { evalAlways := false, cacheOnDisk := true, noHash := false, feedable := false,
        noForce := false, canRecoverKey := true, depthLimit := false, handleCycleError := false }

noncomputable def cutoffDeps : CutoffNode → List CutoffNode
  | CutoffNode.hirOwnerHelper => []
  | CutoffNode.fnSigHelper => [CutoffNode.hirOwnerHelper]
  | CutoffNode.typeckRootCaller => [CutoffNode.fnSigHelper]

/-- In session 2 (`rev2`), `helper_body`'s HIR body changes (`10 -> 20`), while its
    signature `fn(u32) -> u32` (`100`) and caller's typeck result (`200`) stay identical. -/
noncomputable def cutoffSystem : QuerySystemModel CutoffNode Nat where
  metaOf := cutoffMeta
  prevDeps := cutoffDeps
  prevVal := fun
    | CutoffNode.hirOwnerHelper => 10
    | CutoffNode.fnSigHelper => 100
    | CutoffNode.typeckRootCaller => 200
  currVal := fun
    | CutoffNode.hirOwnerHelper => 20
    | CutoffNode.fnSigHelper => 100
    | CutoffNode.typeckRootCaller => 200
  valHash := fun v => v
  prevOk := fun _ => True
  currOk := fun _ => True
  diskCache := fun
    | CutoffNode.hirOwnerHelper => none
    | CutoffNode.fnSigHelper => some 100
    | CutoffNode.typeckRootCaller => some 200

/-- **Sharpness Counterexample 1 (`ce1`):**
    Even though a static dependency path exists from `hir_owner(helper_body)` to
    `typeck_root(caller_reused)` (matching `#[rustc_if_this_changed(hir_owner)]` ->
    `#[rustc_then_this_would_need(typeck_root)]` emitting `OK`) AND `hir_owner(helper_body)`
    mutated (`20 ≠ 10`), dynamic red-green early cutoff at `fn_sig(helper_body)` colors
    `typeck_root(caller_reused)` **green** and causes `QueryMode::EnsureOk` to skip
    deserializing `typeck_root(caller_reused)` from `query-cache.bin` (`loadedFromDisk = false`)
    even though `typeck_root` has `cacheOnDisk = true` and `diskCache = some 200`. -/
theorem ce1_static_dep_path_exists_despite_dynamic_fn_sig_cutoff :
    StaticReachable cutoffSystem.prevDeps CutoffNode.typeckRootCaller CutoffNode.hirOwnerHelper ∧
    cutoffSystem.currVal CutoffNode.hirOwnerHelper ≠ cutoffSystem.prevVal CutoffNode.hirOwnerHelper ∧
    (cutoffSystem.metaOf CutoffNode.typeckRootCaller).cacheOnDisk = true ∧
    cutoffSystem.diskCache CutoffNode.typeckRootCaller = some 200 ∧
    MarkedGreen cutoffSystem CutoffNode.typeckRootCaller ∧
    EnsureOkExec cutoffSystem CutoffNode.typeckRootCaller EnsureOkOutcome.skippedNoDiskLoad false := by
  have hReach :
      StaticReachable cutoffSystem.prevDeps CutoffNode.typeckRootCaller CutoffNode.hirOwnerHelper :=
    StaticReachable.step (List.Mem.head _)
      (StaticReachable.step (List.Mem.head _) (StaticReachable.refl _))
  have hFnSigGreen : MarkedGreen cutoffSystem CutoffNode.fnSigHelper :=
    MarkedGreen.forcedSameHash rfl rfl (fun _ => trivial)
  have hCallerGreen : MarkedGreen cutoffSystem CutoffNode.typeckRootCaller := by
    apply MarkedGreen.allDepsGreen rfl
    intro d hd
    cases hd with
    | head => exact hFnSigGreen
    | tail _ hNil => cases hNil
  have hMut :
      cutoffSystem.currVal CutoffNode.hirOwnerHelper ≠
        cutoffSystem.prevVal CutoffNode.hirOwnerHelper := by
    intro hEq
    cases hEq
  exact ⟨hReach, hMut, rfl, rfl, hCallerGreen, EnsureOkExec.skipGreen rfl hCallerGreen⟩

/-- Two-node mutually recursive ADT representability cycle (`AdtA` <-> `AdtB`). -/
inductive ReprNode where
  | adtA
  | adtB

/-- Counterfactual query metadata omitting `no_force` (`noForce := false`) on a
    recoverable `LocalDefId`-keyed `check_representability` query. -/
noncomputable def buggyReprMetaWithoutNoForce : ReprNode → QueryMeta :=
  fun _ =>
    { evalAlways := false, cacheOnDisk := false, noHash := false, feedable := false,
      noForce := false, canRecoverKey := true, depthLimit := false, handleCycleError := true }

/-- **Sharpness Counterexample 2 (`ce2`):**
    Removing `no_force` from a `LocalDefId`-keyed representability query enables
    `force_from_dep_node_fn`, causing `try_mark_previous_green` to force `adtB`
    out-of-band without `adtA` on the active `QueryJob` stack — truncating the
    cycle frames needed by `check_representability_inner` to report `E0072`. -/
theorem ce2_forcing_inside_cycle_truncates_active_cycle_frames_without_no_force :
    forceEnabled (buggyReprMetaWithoutNoForce ReprNode.adtB) = true ∧
    ReprNode.adtA ∉ cycleStackAfterDepCheck buggyReprMetaWithoutNoForce ReprNode.adtA ReprNode.adtB ∧
    (cycleStackAfterDepCheck buggyReprMetaWithoutNoForce ReprNode.adtA ReprNode.adtB).length = 1 := by
  refine ⟨rfl, ?_, rfl⟩
  intro hMem
  unfold cycleStackAfterDepCheck forceEnabled buggyReprMetaWithoutNoForce at hMem
  cases hMem with
  | tail _ hNil => cases hNil

/-- Single-node system with an untracked provider nondeterminism bug (e.g., sorting
    by session-unstable `DefId`, `execution.rs:568-574`): all tracked dependencies
    are empty (green), yet `currVal ≠ prevVal`. -/
inductive BuggyNode where
  | unstableQuery

noncomputable def buggyNondetSystem : QuerySystemModel BuggyNode Nat where
  metaOf := fun _ =>
    { evalAlways := false, cacheOnDisk := true, noHash := false, feedable := false,
      noForce := false, canRecoverKey := true, depthLimit := false, handleCycleError := false }
  prevDeps := fun _ => []
  prevVal := fun _ => 111
  currVal := fun _ => 222
  valHash := fun v => v
  prevOk := fun _ => True
  currOk := fun _ => True
  diskCache := fun _ => some 111

/-- **Sharpness Counterexample 3 (`ce3`):**
    When a buggy provider violates `DepTrackingSound` (returns `222` vs. previous `111`
    despite having zero red dependencies):
    1. `MarkedGreen` erroneously colors the node green (`currVal ≠ prevVal`), demonstrating
       that `DepTrackingSound` cannot be dropped from Theorem 1;
    2. On a non-disk green recomputation (`diskLoaded = none`), `runGreenIchCheck`
       unconditionally catches the mismatch (`IchCheckOutcome.unstableFingerprintIce`)
       even with `-Zincremental-verify-ich = false`;
    3. On a disk-loaded green hit with `keyHash = 5`, `session = 0`, and `verifyFlag = false`,
       the single session skips verification (`IchCheckOutcome.skipped`), yet at offset
       `k = 5 < 32` (`session = 5`) the rotating slice catches it (`unstableFingerprintIce`). -/
theorem ce3_untracked_provider_nondeterminism_caught_by_ich_verify :
    MarkedGreen buggyNondetSystem BuggyNode.unstableQuery ∧
    buggyNondetSystem.currVal BuggyNode.unstableQuery ≠
      buggyNondetSystem.prevVal BuggyNode.unstableQuery ∧
    runGreenIchCheck (Val := Nat) false 0 5 111 222 none =
      IchCheckOutcome.unstableFingerprintIce ∧
    runGreenIchCheck (Val := Nat) false 0 5 111 222 (some 222) =
      IchCheckOutcome.skipped ∧
    (∃ k : Nat, k < 32 ∧
      runGreenIchCheck (Val := Nat) false (0 + k) 5 111 222 (some 222) =
        IchCheckOutcome.unstableFingerprintIce) := by
  have hGreen : MarkedGreen buggyNondetSystem BuggyNode.unstableQuery := by
    apply MarkedGreen.allDepsGreen rfl
    intro d hd
    cases hd
  have hNe :
      buggyNondetSystem.currVal BuggyNode.unstableQuery ≠
        buggyNondetSystem.prevVal BuggyNode.unstableQuery := by
    intro hEq
    cases hEq
  refine ⟨hGreen, hNe, rfl, rfl, ⟨5, ?_, rfl⟩⟩
  exact Nat.lt_of_sub_eq_succ (rfl : 32 - 5 = 26 + 1)

end RustcQueryEngineSoundness

-- Kernel axiom audits (must report zero non-constructive or reduction axioms):
#print axioms RustcQueryEngineSoundness.ensureOk_green_skip_and_early_cutoff_sound
#print axioms RustcQueryEngineSoundness.ich_rotating_32_and_recomputed_green_complete
#print axioms RustcQueryEngineSoundness.feedable_consistency_and_no_force_cycle_stack_sound
#print axioms RustcQueryEngineSoundness.search_for_cycle_permutation_complete
#print axioms RustcQueryEngineSoundness.ce1_static_dep_path_exists_despite_dynamic_fn_sig_cutoff
#print axioms RustcQueryEngineSoundness.ce2_forcing_inside_cycle_truncates_active_cycle_frames_without_no_force
#print axioms RustcQueryEngineSoundness.ce3_untracked_provider_nondeterminism_caught_by_ich_verify
