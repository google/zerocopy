/-!
# Mixed-Backend Codegen Parity, Unwind/LSDA Completeness, and Fail-Closed Flag Admission

Kernel-checked Lean 4 formalization (`v4.34.1`, purely constructive kernel proofs
relying at most on `propext`, with no choice axioms, no reflection/SMT decision
oracles, and no partial recursion) modeling mixed-backend compilation across
`rustc_codegen_llvm` and `rustc_codegen_cranelift`.

Main results:
1. `mixed_backend_normal_call_preserves_result`:
   Cross-backend non-panicking call chains preserve exact observational return values
   whenever every frame satisfies `abiCompat`, independently of unwind LSDA or sanitizer flags.
2. `mixed_unwind_complete_iff_all_frames_lsda`:
   Necessary and sufficient condition (`↔`) for mixed-backend stack unwinding to match the
   ideal Rust reference unwinder (zero leaked `Drop` guards, zero missed `catch_unwind`
   boundaries, zero missing-`.eh_frame` aborts) across all drop/catch placements: every
   frame's backend profile must emit `.eh_frame`, LSDA cleanup tables, and LSDA catch tables.
3. `fail_closed_flag_gate_prevents_silent_disable`:
   Any fail-closed `CodegenBackend` flag admission gate (`admitsFlags`) prevents silent
   disablement of `-Z sanitizer=address` (guaranteeing heap OOB detection) and prevents
   silent degradation of `-C panic=unwind` (guaranteeing full unwind/drop/`catch_unwind` parity).
4. Three constructive counterexamples witnessing the observed empirical failures:
   - `ce1_eh_frame_without_lsda_leaks_callee_drop_on_cross_backend_unwind`
   - `ce2_missing_lsda_catch_turns_catch_unwind_into_uncaught_abort`
   - `ce3_unvalidated_sanitizer_flag_silently_passes_heap_oob`
-/

namespace CodegenBackendParityAndUnwindContract

/-! ## 1. Backend Profiles, ABI Compatibility, and Call Frames -/

/-- Calling-convention and aggregate/vtable/sret/track-caller binary ABI family. -/
inductive AbiTag where
  | sysvRustV1
  | incompatibleCustom
  deriving DecidableEq, Repr

/-- Observable codegen-backend capability profile carried by each compiled stack frame. -/
structure BackendProfile where
  hasEhFrame : Bool
  hasLsdaCleanup : Bool
  hasLsdaCatch : Bool
  abiTag : AbiTag
  enforcesSanitizer : Bool
  deriving DecidableEq, Repr

/-- Standard `rustc_codegen_llvm` profile on `x86_64-unknown-linux-gnu` with `-C panic=unwind`. -/
noncomputable def llvmProfile : BackendProfile :=
  { hasEhFrame := true
    hasLsdaCleanup := true
    hasLsdaCatch := true
    abiTag := .sysvRustV1
    enforcesSanitizer := true }

/-- Default shipped `rustc_codegen_cranelift` profile (`Cargo.toml` feature `unwinding` disabled).
    Emits System V `.eh_frame` FDEs and matches LLVM's binary ABI, but omits `.gcc_except_table`
    LSDA cleanup/catch pads and ignores `-Z sanitizer=address`. -/
noncomputable def craneliftDefaultProfile : BackendProfile :=
  { hasEhFrame := true
    hasLsdaCleanup := false
    hasLsdaCatch := false
    abiTag := .sysvRustV1
    enforcesSanitizer := false }

/-- `rustc_codegen_cranelift` built with `--features unwinding` (still lacking ASan). -/
noncomputable def craneliftUnwindingProfile : BackendProfile :=
  { hasEhFrame := true
    hasLsdaCleanup := true
    hasLsdaCatch := true
    abiTag := .sysvRustV1
    enforcesSanitizer := false }

/-- Hypothetical backend omitting `.eh_frame` entirely (cannot even be unwound through). -/
noncomputable def noEhFrameProfile : BackendProfile :=
  { hasEhFrame := false
    hasLsdaCleanup := false
    hasLsdaCatch := false
    abiTag := .sysvRustV1
    enforcesSanitizer := false }

/-- Pairwise binary ABI compatibility between a caller backend and a callee backend. -/
noncomputable def abiCompat (caller callee : BackendProfile) : Bool :=
  caller.abiTag == callee.abiTag

theorem abiCompat_refl (p : BackendProfile) : abiCompat p p = true := by
  unfold abiCompat
  cases p.abiTag <;> rfl

theorem abiCompat_symm (a b : BackendProfile) : abiCompat a b = abiCompat b a := by
  unfold abiCompat
  cases a.abiTag <;> cases b.abiTag <;> rfl

theorem abiCompat_trans {a b c : BackendProfile}
    (hab : abiCompat a b = true) (hbc : abiCompat b c = true) :
    abiCompat a c = true := by
  unfold abiCompat at hab hbc ⊢
  cases ha : a.abiTag <;> cases hb : b.abiTag <;> cases hc : c.abiTag <;>
    simp_all

theorem abiCompat_eq_iff (a b : BackendProfile) :
    abiCompat a b = true ↔ a.abiTag = b.abiTag := by
  unfold abiCompat
  cases a.abiTag <;> cases b.abiTag <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- One activation record on a mixed-backend call stack.
    Stacks are ordered innermost-first (head = active/panicking frame, tail = callers). -/
structure CallFrame where
  frameId : Nat
  profile : BackendProfile
  hasDropGuard : Bool
  isCatchBoundary : Bool
  deriving DecidableEq, Repr

/-- Normalize any call frame to the ideal LLVM reference profile while keeping its source
    frame ID, drop-guard presence, and `catch_unwind` boundary placement unchanged. -/
noncomputable def toReferenceFrame (f : CallFrame) : CallFrame :=
  { f with profile := llvmProfile }

/-! ## 2. Normal (Non-Panicking) Mixed-Backend Call Execution -/

/-- Outcome of executing a non-panicking call chain across compiled frames. -/
inductive CallOutcome where
  | ok (val : Nat)
  | abiMismatch (frameId : Nat)
  deriving DecidableEq, Repr

/-- Reference semantics of a non-panicking call chain independent of backend metadata:
    each frame applies its pure value transformation `step f.frameId` to the marshalled ABI payload. -/
noncomputable def evalNormalRef (step : Nat → Nat → Nat) : List CallFrame → Nat → Nat
  | [], acc => acc
  | f :: rest, acc => evalNormalRef step rest (step f.frameId acc)

/-- Mixed-backend non-panicking execution checking `abiCompat` against the caller's ABI profile
    at every call boundary before transferring control and marshalling arguments/returns. -/
noncomputable def execNormalStack (step : Nat → Nat → Nat) (callerProfile : BackendProfile) :
    List CallFrame → Nat → CallOutcome
  | [], acc => .ok acc
  | f :: rest, acc =>
      if abiCompat callerProfile f.profile then
        execNormalStack step f.profile rest (step f.frameId acc)
      else
        .abiMismatch f.frameId

/-- **Theorem 1 (Mixed-Backend Non-Panicking Call Preservation).**
    If every frame in a mixed-backend call stack shares `callerProfile`'s binary ABI tag
    (`abiCompat callerProfile f.profile = true`), then normal non-panicking execution succeeds
    and yields the exact same observational result as the pure reference semantics (and therefore
    as a homogeneous LLVM execution), regardless of `hasEhFrame`, `hasLsdaCleanup`,
    `hasLsdaCatch`, or `enforcesSanitizer`. -/
theorem mixed_backend_normal_call_preserves_result
    (step : Nat → Nat → Nat)
    (callerProfile : BackendProfile)
    (frames : List CallFrame)
    (init : Nat)
    (hCompat : ∀ f, f ∈ frames → abiCompat callerProfile f.profile = true) :
    execNormalStack step callerProfile frames init = .ok (evalNormalRef step frames init) := by
  induction frames generalizing callerProfile init with
  | nil =>
      rfl
  | cons f rest ih =>
      have hHead : abiCompat callerProfile f.profile = true :=
        hCompat f (List.mem_cons_self)
      have hTail : ∀ g, g ∈ rest → abiCompat f.profile g.profile = true := by
        intro g hg
        have hcg : abiCompat callerProfile g.profile = true :=
          hCompat g (List.mem_cons_of_mem f hg)
        have hfc : abiCompat f.profile callerProfile = true := by
          rw [abiCompat_symm]
          exact hHead
        exact abiCompat_trans hfc hcg
      unfold execNormalStack evalNormalRef
      rw [hHead]
      exact ih f.profile (step f.frameId init) hTail

/-- Corollary: All four cells of the 2x2 `(lib ∈ {llvm, cranelift}) × (bin ∈ {llvm, cranelift})`
    matrix preserve identical non-panicking ABI results. -/
theorem mixed_backend_normal_call_full_2x2_parity
    (step : Nat → Nat → Nat) (init : Nat) (libId binId : Nat)
    (libDrop binDrop libCatch binCatch : Bool) :
    let runPair (libProf binProf : BackendProfile) : CallOutcome :=
      execNormalStack step binProf
        [ { frameId := libId, profile := libProf, hasDropGuard := libDrop, isCatchBoundary := libCatch }
        , { frameId := binId, profile := binProf, hasDropGuard := binDrop, isCatchBoundary := binCatch } ]
        init
    runPair llvmProfile llvmProfile = .ok (step binId (step libId init)) ∧
    runPair llvmProfile craneliftDefaultProfile = .ok (step binId (step libId init)) ∧
    runPair craneliftDefaultProfile llvmProfile = .ok (step binId (step libId init)) ∧
    runPair craneliftDefaultProfile craneliftDefaultProfile = .ok (step binId (step libId init)) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3. Mixed-Backend Stack Unwinding, Drop Cleanup, and `catch_unwind` Parity -/

/-- Final outcome of unwinding a panicking thread across a call stack. -/
inductive UnwindDisposition where
  | caughtAt (frameId : Nat)
  | uncaughtAbort
  | missingEhFrameAbort (frameId : Nat)
  deriving DecidableEq, Repr

/-- Complete observable trace of stack unwinding:
    - `disposition`: where unwinding stopped (`caughtAt`, `uncaughtAbort`, or `missingEhFrameAbort`)
    - `executedDrops`: frame IDs whose local `Drop` guards actually ran during unwinding
    - `leakedDrops`: frame IDs whose live `Drop` guards were silently skipped (missing LSDA cleanup)
    - `missedCatches`: frame IDs whose `catch_unwind` boundary was silently bypassed (missing LSDA catch) -/
structure UnwindTrace where
  disposition : UnwindDisposition
  executedDrops : List Nat
  leakedDrops : List Nat
  missedCatches : List Nat
  deriving DecidableEq, Repr

/-- Operational semantics of Itanium / System V stack unwinding across a mixed-backend call stack. -/
noncomputable def unwindStack : List CallFrame → UnwindTrace
  | [] =>
      { disposition := .uncaughtAbort
        executedDrops := []
        leakedDrops := []
        missedCatches := [] }
  | f :: rest =>
      if !f.profile.hasEhFrame then
        { disposition := .missingEhFrameAbort f.frameId
          executedDrops := []
          leakedDrops := []
          missedCatches := [] }
      else
        let execHere : List Nat :=
          if f.hasDropGuard && f.profile.hasLsdaCleanup then [f.frameId] else []
        let leakHere : List Nat :=
          if f.hasDropGuard && !f.profile.hasLsdaCleanup then [f.frameId] else []
        if f.isCatchBoundary then
          if f.profile.hasLsdaCatch then
            { disposition := .caughtAt f.frameId
              executedDrops := execHere
              leakedDrops := leakHere
              missedCatches := [] }
          else
            let tail := unwindStack rest
            { disposition := tail.disposition
              executedDrops := execHere ++ tail.executedDrops
              leakedDrops := leakHere ++ tail.leakedDrops
              missedCatches := f.frameId :: tail.missedCatches }
        else
          let tail := unwindStack rest
          { disposition := tail.disposition
            executedDrops := execHere ++ tail.executedDrops
            leakedDrops := leakHere ++ tail.leakedDrops
            missedCatches := tail.missedCatches }

/-- Reference unwinding semantics: every frame runs with full `.eh_frame` + LSDA cleanup + LSDA catch. -/
noncomputable def referenceUnwindStack (stack : List CallFrame) : UnwindTrace :=
  unwindStack (stack.map toReferenceFrame)

/-- A backend profile is unwind-complete iff it emits `.eh_frame`, LSDA cleanup, and LSDA catch tables. -/
noncomputable def UnwindComplete (p : BackendProfile) : Prop :=
  p.hasEhFrame = true ∧ p.hasLsdaCleanup = true ∧ p.hasLsdaCatch = true

private theorem referenceUnwindStack_leaked_nil (stack : List CallFrame) :
    (referenceUnwindStack stack).leakedDrops = [] := by
  induction stack with
  | nil => rfl
  | cons f rest ih =>
      unfold referenceUnwindStack at ih ⊢
      simp only [List.map_cons, toReferenceFrame, unwindStack, llvmProfile]
      cases f.hasDropGuard <;> cases f.isCatchBoundary <;> simp [ih]

private theorem referenceUnwindStack_missed_nil (stack : List CallFrame) :
    (referenceUnwindStack stack).missedCatches = [] := by
  induction stack with
  | nil => rfl
  | cons f rest ih =>
      unfold referenceUnwindStack at ih ⊢
      simp only [List.map_cons, toReferenceFrame, unwindStack, llvmProfile]
      cases f.hasDropGuard <;> cases f.isCatchBoundary <;> simp [ih]

private noncomputable def mkTestFrame (hasDrop isCatch : Bool) (p : BackendProfile) : CallFrame :=
  { frameId := 0
    profile := p
    hasDropGuard := hasDrop
    isCatchBoundary := isCatch }

private theorem map_profile_mkTestFrame (hasDrop isCatch : Bool) (profs : List BackendProfile) :
    (profs.map (mkTestFrame hasDrop isCatch)).map CallFrame.profile = profs := by
  induction profs with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.map_cons, mkTestFrame]
      exact congrArg (List.cons p) ih

private theorem referenceUnwindStack_dropOnly_disposition (profs : List BackendProfile) :
    (referenceUnwindStack (profs.map (mkTestFrame true false))).disposition = .uncaughtAbort := by
  induction profs with
  | nil => rfl
  | cons p rest ih =>
      unfold referenceUnwindStack at ih ⊢
      simp only [List.map_cons, mkTestFrame, toReferenceFrame, unwindStack, llvmProfile]
      exact ih

private theorem dropOnly_ehFrame_and_cleanup_of_parity (profs : List BackendProfile)
    (hEq : unwindStack (profs.map (mkTestFrame true false)) =
           referenceUnwindStack (profs.map (mkTestFrame true false))) :
    ∀ p, p ∈ profs → p.hasEhFrame = true ∧ p.hasLsdaCleanup = true := by
  induction profs with
  | nil =>
      intro p hp
      cases hp
  | cons q rest ih =>
      have hDisp : (unwindStack ((q :: rest).map (mkTestFrame true false))).disposition =
          .uncaughtAbort := by
        rw [hEq]
        exact referenceUnwindStack_dropOnly_disposition (q :: rest)
      have hLeak : (unwindStack ((q :: rest).map (mkTestFrame true false))).leakedDrops = [] := by
        rw [hEq]
        exact referenceUnwindStack_leaked_nil ((q :: rest).map (mkTestFrame true false))
      have hEh : q.hasEhFrame = true := by
        cases hq : q.hasEhFrame with
        | true => rfl
        | false =>
            simp only [List.map_cons, mkTestFrame, unwindStack, hq] at hDisp
            cases hDisp
      have hClean : q.hasLsdaCleanup = true := by
        cases hc : q.hasLsdaCleanup with
        | true => rfl
        | false =>
            simp only [List.map_cons, mkTestFrame, unwindStack, hEh, hc] at hLeak
            cases hLeak
      have hTailEq : unwindStack (rest.map (mkTestFrame true false)) =
          referenceUnwindStack (rest.map (mkTestFrame true false)) := by
        unfold referenceUnwindStack at hEq ⊢
        simp only [List.map_cons, mkTestFrame, toReferenceFrame, unwindStack, llvmProfile, hEh, hClean] at hEq
        cases hU : unwindStack (rest.map (mkTestFrame true false))
        cases hR : unwindStack ((rest.map (mkTestFrame true false)).map toReferenceFrame)
        rw [hU, hR] at hEq
        cases hEq
        rfl
      have hRest := ih hTailEq
      intro p hp
      cases hp with
      | head => exact ⟨hEh, hClean⟩
      | tail _ hMem => exact hRest p hMem

private theorem mem_split_constructive {α : Type} :
    ∀ {x : α} {xs : List α}, x ∈ xs → ∃ pre post, xs = pre ++ x :: post
  | _, [], h => by cases h
  | x, y :: rest, h => by
      cases h with
      | head => exact ⟨[], rest, rfl⟩
      | tail _ hMem =>
          let ⟨pre, post, hEq⟩ := mem_split_constructive hMem
          exact ⟨y :: pre, post, congrArg (List.cons y) hEq⟩

private theorem unwind_pass_prefix_missed
    (pre : List BackendProfile) (suffix : List CallFrame)
    (hEhPre : ∀ q, q ∈ pre → q.hasEhFrame = true) :
    (unwindStack (pre.map (mkTestFrame false false) ++ suffix)).missedCatches =
      (unwindStack suffix).missedCatches := by
  induction pre with
  | nil => rfl
  | cons q rest ih =>
      have hq : q.hasEhFrame = true := hEhPre q List.mem_cons_self
      have hRest : ∀ r, r ∈ rest → r.hasEhFrame = true := fun r hr =>
        hEhPre r (List.mem_cons_of_mem q hr)
      simp only [List.map_cons, List.cons_append, mkTestFrame, unwindStack, hq]
      exact ih hRest

/-- **Theorem 2 (Necessary & Sufficient LSDA Condition for Complete Unwind Parity).**
    For any assignment of backend profiles `profs` to stack frames, mixed-backend unwinding
    matches the ideal Rust reference unwinder (`unwindStack stack = referenceUnwindStack stack`)
    across all drop-guard and `catch_unwind` placements **if and only if** every profile in
    `profs` emits `.eh_frame`, LSDA cleanup tables, and LSDA catch tables. -/
theorem mixed_unwind_complete_iff_all_frames_lsda (profs : List BackendProfile) :
    (∀ (stack : List CallFrame),
      stack.map CallFrame.profile = profs →
      unwindStack stack = referenceUnwindStack stack) ↔
    (∀ p, p ∈ profs → UnwindComplete p) := by
  constructor
  · intro hAll
    have hDropEq : unwindStack (profs.map (mkTestFrame true false)) =
        referenceUnwindStack (profs.map (mkTestFrame true false)) :=
      hAll (profs.map (mkTestFrame true false)) (map_profile_mkTestFrame true false profs)
    have hEhClean := dropOnly_ehFrame_and_cleanup_of_parity profs hDropEq
    intro p hp
    have ⟨hEh, hClean⟩ := hEhClean p hp
    have hCatch : p.hasLsdaCatch = true := by
      let ⟨pre, post, hSplit⟩ := mem_split_constructive hp
      let catchStack : List CallFrame :=
        pre.map (mkTestFrame false false) ++
        [mkTestFrame false true p] ++
        post.map (mkTestFrame false false)
      have hMap : catchStack.map CallFrame.profile = profs := by
        simp only [catchStack, List.map_append, List.map_cons, List.map_nil,
          map_profile_mkTestFrame, mkTestFrame]
        rw [hSplit]
        simp [List.append_assoc]
      have hEqCatch := hAll catchStack hMap
      have hMissedNil : (unwindStack catchStack).missedCatches = [] := by
        rw [hEqCatch]
        exact referenceUnwindStack_missed_nil catchStack
      have hEhPre : ∀ q, q ∈ pre → q.hasEhFrame = true := by
        intro q hq
        have hqProfs : q ∈ profs := by
          rw [hSplit]
          exact List.mem_append_left (p :: post) hq
        exact (hEhClean q hqProfs).1
      have hPass :
          (unwindStack catchStack).missedCatches =
          (unwindStack (mkTestFrame false true p :: post.map (mkTestFrame false false))).missedCatches := by
        have hAssoc : catchStack =
            pre.map (mkTestFrame false false) ++
            (mkTestFrame false true p :: post.map (mkTestFrame false false)) := by
          simp [catchStack, List.append_assoc]
        rw [hAssoc]
        exact unwind_pass_prefix_missed pre _ hEhPre
      rw [hPass] at hMissedNil
      cases hCat : p.hasLsdaCatch with
      | true => rfl
      | false =>
          simp only [mkTestFrame, unwindStack, hEh, hCat] at hMissedNil
          cases hMissedNil
    exact ⟨hEh, hClean, hCatch⟩
  · intro hComplete stack hMap
    induction stack generalizing profs with
    | nil => rfl
    | cons f rest ih =>
        rw [List.map_cons] at hMap
        have hfMem : f.profile ∈ profs := by
          rw [← hMap]
          exact List.mem_cons_self
        have ⟨hEh, hClean, hCatch⟩ := hComplete f.profile hfMem
        have hRestComplete : ∀ p, p ∈ rest.map CallFrame.profile → UnwindComplete p := by
          intro p hp
          apply hComplete p
          rw [← hMap]
          exact List.mem_cons_of_mem f.profile hp
        have hTail := ih (rest.map CallFrame.profile) hRestComplete rfl
        unfold referenceUnwindStack at hTail ⊢
        simp only [List.map_cons, toReferenceFrame, unwindStack, llvmProfile, hEh, hClean, hCatch]
        cases f.hasDropGuard <;> cases f.isCatchBoundary <;> simp [hTail]

/-! ## 4. Fail-Closed Security and Feature Flag Admission -/

/-- Security and codegen feature flags requested on the `rustc` command line. -/
structure RequestedFlags where
  ltoThin : Bool
  instrumentCoverage : Bool
  sanitizerAddress : Bool
  panicUnwind : Bool
  deriving DecidableEq, Repr

/-- Declared capability surface of a `CodegenBackend` implementation. -/
structure BackendCapabilities where
  supportsLto : Bool
  supportsCoverage : Bool
  supportsAddressSanitizer : Bool
  supportsUnwindLsda : Bool
  deriving DecidableEq, Repr

/-- Runtime result of executing the heap out-of-bounds read probe (`read_volatile(p.add(32))`). -/
inductive HeapOobOutcome where
  | abortedAsan
  | silentReadSurvived
  deriving DecidableEq, Repr

/-- Runtime execution model of the heap-OOB probe under a given backend profile. -/
noncomputable def runHeapOobProbe (profile : BackendProfile) : HeapOobOutcome :=
  if profile.enforcesSanitizer then .abortedAsan else .silentReadSurvived

/-- Capabilities truthfully realized by a concrete `BackendProfile`. -/
noncomputable def CapabilitiesMatchProfile (cap : BackendCapabilities) (p : BackendProfile) : Prop :=
  cap.supportsAddressSanitizer = p.enforcesSanitizer ∧
  cap.supportsUnwindLsda = (p.hasEhFrame && p.hasLsdaCleanup && p.hasLsdaCatch)

/-- Required fail-closed `CodegenBackend::init` flag admission gate: every requested
    security or semantic capability must be supported by the selected backend. -/
noncomputable def admitsFlags (cap : BackendCapabilities) (req : RequestedFlags) : Bool :=
  (!req.ltoThin || cap.supportsLto) &&
  (!req.instrumentCoverage || cap.supportsCoverage) &&
  (!req.sanitizerAddress || cap.supportsAddressSanitizer) &&
  (!req.panicUnwind || cap.supportsUnwindLsda)

/-- Actual flag gate observed in `compiler/rustc_codegen_cranelift/src/lib.rs:134-144`:
    rejects `-C lto=*` and `-C instrument-coverage`, but never inspects `sess.sanitizers()`
    or `cfg!(feature = "unwinding")` against `-C panic=unwind`. -/
noncomputable def admitsFlagsCraneliftActual (req : RequestedFlags) : Bool :=
  (!req.ltoThin) && (!req.instrumentCoverage)

/-- Capabilities of shipped `rustc_codegen_llvm`. -/
noncomputable def llvmCapabilities : BackendCapabilities :=
  { supportsLto := true
    supportsCoverage := true
    supportsAddressSanitizer := true
    supportsUnwindLsda := true }

/-- True capabilities of shipped `rustc_codegen_cranelift` (default build without `unwinding`). -/
noncomputable def craneliftDefaultCapabilities : BackendCapabilities :=
  { supportsLto := false
    supportsCoverage := false
    supportsAddressSanitizer := false
    supportsUnwindLsda := false }

private theorem bool_and_eq_true_elim {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem bool_or_true_left_false {b : Bool} (h : ((!true) || b) = true) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- **Theorem 3 (Fail-Closed Security Flag Soundness).**
    Under any truthful backend capability declaration (`CapabilitiesMatchProfile cap profile`),
    the fail-closed gate `admitsFlags cap req = true` guarantees:
    1. If `-Z sanitizer=address` was requested (`req.sanitizerAddress = true`), then the
       compiled binary enforces ASan (`profile.enforcesSanitizer = true`) and detects the
       heap OOB probe (`runHeapOobProbe profile = .abortedAsan`).
    2. If `-C panic=unwind` was requested (`req.panicUnwind = true`), then `profile` is
       `UnwindComplete` (`.eh_frame` + LSDA cleanup + LSDA catch). -/
theorem fail_closed_flag_gate_prevents_silent_disable
    (cap : BackendCapabilities)
    (profile : BackendProfile)
    (req : RequestedFlags)
    (hMatch : CapabilitiesMatchProfile cap profile)
    (hAdmit : admitsFlags cap req = true) :
    (req.sanitizerAddress = true →
      profile.enforcesSanitizer = true ∧ runHeapOobProbe profile = .abortedAsan) ∧
    (req.panicUnwind = true → UnwindComplete profile) := by
  unfold admitsFlags at hAdmit
  have ⟨h123, h4⟩ := bool_and_eq_true_elim hAdmit
  have ⟨h12, h3⟩ := bool_and_eq_true_elim h123
  constructor
  · intro hSan
    rw [hSan] at h3
    have hCapSan : cap.supportsAddressSanitizer = true := bool_or_true_left_false h3
    have hEnf : profile.enforcesSanitizer = true := by
      rw [← hMatch.1]
      exact hCapSan
    refine ⟨hEnf, ?_⟩
    unfold runHeapOobProbe
    rw [hEnf]
    rfl
  · intro hUnw
    rw [hUnw] at h4
    have hCapUnw : cap.supportsUnwindLsda = true := bool_or_true_left_false h4
    have hAllThree : (profile.hasEhFrame && profile.hasLsdaCleanup && profile.hasLsdaCatch) = true := by
      rw [← hMatch.2]
      exact hCapUnw
    have ⟨hEhClean, hCatch⟩ := bool_and_eq_true_elim hAllThree
    have ⟨hEh, hClean⟩ := bool_and_eq_true_elim hEhClean
    exact ⟨hEh, hClean, hCatch⟩

/-- Corollary: A stack composed solely of frames admitted under `-C panic=unwind` by a
    fail-closed gate automatically achieves full unwind/drop/`catch_unwind` parity. -/
theorem fail_closed_unwind_admitted_stack_has_parity
    (stack : List CallFrame)
    (caps : CallFrame → BackendCapabilities)
    (req : RequestedFlags)
    (hReqUnw : req.panicUnwind = true)
    (hMatchAll : ∀ f, f ∈ stack → CapabilitiesMatchProfile (caps f) f.profile)
    (hAdmitAll : ∀ f, f ∈ stack → admitsFlags (caps f) req = true) :
    unwindStack stack = referenceUnwindStack stack := by
  have hIff := (mixed_unwind_complete_iff_all_frames_lsda (stack.map CallFrame.profile)).2
  apply hIff
  · intro p hp
    have hExists : ∀ (xs : List CallFrame), p ∈ xs.map CallFrame.profile →
        ∃ f, f ∈ xs ∧ f.profile = p := by
      intro xs hMem
      induction xs with
      | nil => cases hMem
      | cons hd tl ih =>
          cases hMem with
          | head => exact ⟨hd, List.mem_cons_self, rfl⟩
          | tail _ hTl =>
              let ⟨f, hf, hEq⟩ := ih hTl
              exact ⟨f, List.mem_cons_of_mem hd hf, hEq⟩
    let ⟨f, hfMem, hfEq⟩ := hExists stack hp
    rw [← hfEq]
    exact (fail_closed_flag_gate_prevents_silent_disable
      (caps f) f.profile req (hMatchAll f hfMem) (hAdmitAll f hfMem)).2 hReqUnw
  · rfl

/-! ## 5. Constructive Counterexamples Matching Empirical Differential Probes -/

/-- **Counterexample 1 (`lib_cranelift__bin_llvm`):**
    Cranelift callee (`frameId = 0`, `.eh_frame = true`, `hasLsdaCleanup = false`) panics
    inside an LLVM caller's `catch_unwind` (`frameId = 1`, full `.eh_frame` + LSDA).
    Unwinding traverses the Cranelift `.eh_frame` cleanly into the LLVM catch pad
    (`disposition = .caughtAt 1`, `executedDrops = [1]` matching `BIN_DROPS = 1`),
    while **silently leaking the Cranelift callee's `Drop` guard** (`leakedDrops = [0]`,
    matching `LIB_DROPS = 0`), diverging from the ideal reference (`executedDrops = [0, 1]`). -/
theorem ce1_eh_frame_without_lsda_leaks_callee_drop_on_cross_backend_unwind :
    ∃ stack : List CallFrame,
      (∀ f, f ∈ stack → f.profile.hasEhFrame = true) ∧
      (unwindStack stack).disposition = .caughtAt 1 ∧
      (unwindStack stack).executedDrops = [1] ∧
      (unwindStack stack).leakedDrops = [0] ∧
      (referenceUnwindStack stack).executedDrops = [0, 1] ∧
      (referenceUnwindStack stack).leakedDrops = [] := by
  refine ⟨
    [ { frameId := 0, profile := craneliftDefaultProfile, hasDropGuard := true, isCatchBoundary := false }
    , { frameId := 1, profile := llvmProfile, hasDropGuard := true, isCatchBoundary := true } ],
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro f hf
  cases hf with
  | head => rfl
  | tail _ hf2 =>
      cases hf2 with
      | head => rfl
      | tail _ hf3 => cases hf3

/-- **Counterexample 2 (`lib_llvm__bin_cranelift`):**
    LLVM callee (`frameId = 0`, full LSDA) panics inside a Cranelift caller's `catch_unwind`
    (`frameId = 1`, `.eh_frame = true`, `hasLsdaCatch = false`, `hasLsdaCleanup = false`).
    Because Cranelift lowers `intrinsics::catch_unwind` to a bare `call_indirect` without an
    LSDA catch action, the panic escapes uncaught (`disposition = .uncaughtAbort`, matching
    `rc = 101`, `missedCatches = [1]`, `leakedDrops = [1]`), whereas the reference catches at
    `frameId = 1`. -/
theorem ce2_missing_lsda_catch_turns_catch_unwind_into_uncaught_abort :
    ∃ stack : List CallFrame,
      (∀ f, f ∈ stack → f.profile.hasEhFrame = true) ∧
      (unwindStack stack).disposition = .uncaughtAbort ∧
      (unwindStack stack).executedDrops = [0] ∧
      (unwindStack stack).leakedDrops = [1] ∧
      (unwindStack stack).missedCatches = [1] ∧
      (referenceUnwindStack stack).disposition = .caughtAt 1 := by
  refine ⟨
    [ { frameId := 0, profile := llvmProfile, hasDropGuard := true, isCatchBoundary := false }
    , { frameId := 1, profile := craneliftDefaultProfile, hasDropGuard := true, isCatchBoundary := true } ],
    ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro f hf
  cases hf with
  | head => rfl
  | tail _ hf2 =>
      cases hf2 with
      | head => rfl
      | tail _ hf3 => cases hf3

/-- Companion to CE2 (`lib_cranelift__bin_cranelift`): when both callee and caller use default
    Cranelift, both drop guards leak (`leakedDrops = [0, 1]`), `catch_unwind` is bypassed
    (`missedCatches = [1]`), and the process aborts (`disposition = .uncaughtAbort`). -/
theorem ce2b_cranelift_both_leaks_all_drops_and_aborts :
    let stack : List CallFrame :=
      [ { frameId := 0, profile := craneliftDefaultProfile, hasDropGuard := true, isCatchBoundary := false }
      , { frameId := 1, profile := craneliftDefaultProfile, hasDropGuard := true, isCatchBoundary := true } ]
    unwindStack stack =
      { disposition := .uncaughtAbort
        executedDrops := []
        leakedDrops := [0, 1]
        missedCatches := [1] } :=
  rfl

/-- **Counterexample 3 (Silent Fail-Open `-Z sanitizer=address`):**
    Cranelift's actual `init` gate accepts `-Z sanitizer=address` (`admitsFlagsCraneliftActual req = true`),
    and the resulting binary silently survives heap OOB (`runHeapOobProbe craneliftDefaultProfile = .silentReadSurvived`,
    matching `ASAN_SURVIVED_OOB=0`, `rc = 0`), whereas the fail-closed gate rejects the build at compile
    time (`admitsFlags craneliftDefaultCapabilities req = false`) and LLVM enforces ASan (`rc = 1`). -/
theorem ce3_unvalidated_sanitizer_flag_silently_passes_heap_oob :
    ∃ req : RequestedFlags,
      req.sanitizerAddress = true ∧
      admitsFlagsCraneliftActual req = true ∧
      runHeapOobProbe craneliftDefaultProfile = .silentReadSurvived ∧
      admitsFlags craneliftDefaultCapabilities req = false ∧
      admitsFlags llvmCapabilities req = true ∧
      runHeapOobProbe llvmProfile = .abortedAsan :=
  ⟨ { ltoThin := false
      instrumentCoverage := false
      sanitizerAddress := true
      panicUnwind := false }
  , rfl, rfl, rfl, rfl, rfl, rfl ⟩

/-- Empirical contrast: Cranelift's actual gate DOES fail closed on `-C lto=thin` and
    `-C instrument-coverage` (`rc = 1`), proving the asymmetry is selective rather than uniform. -/
theorem cranelift_actual_gate_rejects_lto_and_coverage :
    admitsFlagsCraneliftActual
      { ltoThin := true, instrumentCoverage := false, sanitizerAddress := false, panicUnwind := false } = false ∧
    admitsFlagsCraneliftActual
      { ltoThin := false, instrumentCoverage := true, sanitizerAddress := false, panicUnwind := false } = false :=
  ⟨rfl, rfl⟩

/-- Necessity of `.eh_frame`: without `.eh_frame` CFI, unwinding cannot even reach an outer
    LLVM `catch_unwind` frame (`missingEhFrameAbort 0`). -/
theorem no_eh_frame_aborts_even_with_outer_llvm_catch :
    let stack : List CallFrame :=
      [ { frameId := 0, profile := noEhFrameProfile, hasDropGuard := true, isCatchBoundary := false }
      , { frameId := 1, profile := llvmProfile, hasDropGuard := true, isCatchBoundary := true } ]
    (unwindStack stack).disposition = .missingEhFrameAbort 0 :=
  rfl

end CodegenBackendParityAndUnwindContract

#print axioms CodegenBackendParityAndUnwindContract.mixed_backend_normal_call_preserves_result
#print axioms CodegenBackendParityAndUnwindContract.mixed_backend_normal_call_full_2x2_parity
#print axioms CodegenBackendParityAndUnwindContract.mixed_unwind_complete_iff_all_frames_lsda
#print axioms CodegenBackendParityAndUnwindContract.fail_closed_flag_gate_prevents_silent_disable
#print axioms CodegenBackendParityAndUnwindContract.fail_closed_unwind_admitted_stack_has_parity
#print axioms CodegenBackendParityAndUnwindContract.ce1_eh_frame_without_lsda_leaks_callee_drop_on_cross_backend_unwind
#print axioms CodegenBackendParityAndUnwindContract.ce2_missing_lsda_catch_turns_catch_unwind_into_uncaught_abort
#print axioms CodegenBackendParityAndUnwindContract.ce2b_cranelift_both_leaks_all_drops_and_aborts
#print axioms CodegenBackendParityAndUnwindContract.ce3_unvalidated_sanitizer_flag_silently_passes_heap_oob
#print axioms CodegenBackendParityAndUnwindContract.cranelift_actual_gate_rejects_lto_and_coverage
#print axioms CodegenBackendParityAndUnwindContract.no_eh_frame_aborts_even_with_outer_llvm_catch
