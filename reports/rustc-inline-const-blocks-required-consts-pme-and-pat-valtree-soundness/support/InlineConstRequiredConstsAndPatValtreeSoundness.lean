/-
  InlineConstRequiredConstsAndPatValtreeSoundness.lean
  Standalone Lean v4.34.1 mechanization (Init-only; zero external imports;
  zero `sorry`, `omega`, `bv_decide`, `native_decide`, `Classical.choice`,
  `partial def`, `unsafe def`, `axiom`, `opaque`, or `._unsafe_rec`).

  Formalizes empirical and primary-source invariants for:
  1. Inline `const { ... }` block lowering, pre-DCE `RequiredConstsVisitor`
     collection in `mir_promoted`, `--emit=metadata` skipping, lazy CGU
     `cross_crate_inlinable` deferral, promoted-fragment `KnownPanicsLint`
     extraction out of `if false`, and `GVN` constant evaluation of generic
     functions under `-Copt-level=2`.
  2. `&const { ... }` static promotion eligibility (`!HasMutInterior`,
     `!NeedsDrop` with `[T; 0]` exception, and `&mut []` zero-length carve-out)
     vs stack-temporary lifetime (`E0515`), static `.rodata` immutability,
     drop-count preservation, and concrete sharpness counterexamples.
  3. `TyKind::Pat` (`pattern_types`) valtree base-type erasure, pre-valtree
     range validity necessity, scalar range & wrapping two's-complement
     (`i8 is -128..=-1 | 1..=127`) niche layouts, single/nested `Option`
     niche-encoding injectivity (`Option<Small>` in 4 bytes,
     `Option<Option<OneTwo>>` in 1 byte), LLVM `!range` metadata refinement
     vs transmute UB, `ConstructorSet::Unlistable` exhaustiveness, and Anneal's
     fail-closed admission boundary.
-/

namespace InlineConstRequiredConstsAndPatValtreeSoundness

/-! ## Part 0: Elementary Utilities (Pure Structural / Noncomputable) -/

noncomputable def allList {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && allList p xs

noncomputable def anyList {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || anyList p xs

noncomputable def filterList {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterList p xs else filterList p xs

noncomputable def appendMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ appendMap f xs

noncomputable def mapList {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapList f xs

theorem allList_append {α : Type} (p : α → Bool) (xs ys : List α) :
    allList p (xs ++ ys) = (allList p xs && allList p ys) := by
  induction xs with
  | nil => simp [allList]
  | cons x xs ih =>
    simp [allList, ih, Bool.and_assoc]

theorem anyList_append {α : Type} (p : α → Bool) (xs ys : List α) :
    anyList p (xs ++ ys) = (anyList p xs || anyList p ys) := by
  induction xs with
  | nil => simp [anyList]
  | cons x xs ih =>
    simp [anyList, ih, Bool.or_assoc]

theorem mem_appendMap {α β : Type} (f : α → List β) (x : α) (y : β) (xs : List α)
    (hx : x ∈ xs) (hy : y ∈ f x) : y ∈ appendMap f xs := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [appendMap, List.mem_append]
    cases hx with
    | head => exact Or.inl hy
    | tail _ hrest => exact Or.inr (ih hrest)

theorem appendMap_append {α β : Type} (f : α → List β) (xs ys : List α) :
    appendMap f (xs ++ ys) = appendMap f xs ++ appendMap f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, appendMap, ih, List.append_assoc]

theorem allList_of_mem {α : Type} (p : α → Bool) (xs : List α) (h : allList p xs = true)
    (x : α) (hx : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [allList, Bool.and_eq_true] at h
    cases hx with
    | head => exact h.1
    | tail _ hrest => exact ih h.2 hrest

theorem mem_filterList_iff {α : Type} (p : α → Bool) (xs : List α) (x : α) :
    x ∈ filterList p xs ↔ x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
    simp [filterList]
  | cons a rest ih =>
    simp only [filterList]
    cases hp : p a with
    | true =>
      simp only [ite_true, List.mem_cons, ih]
      constructor
      · intro h
        cases h with
        | inl heq =>
          subst heq
          exact ⟨Or.inl rfl, hp⟩
        | inr hr => exact ⟨Or.inr hr.1, hr.2⟩
      · intro h
        cases h.1 with
        | inl heq => exact Or.inl heq
        | inr hrest => exact Or.inr ⟨hrest, h.2⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.mem_cons, ih]
      constructor
      · intro h
        exact ⟨Or.inr h.1, h.2⟩
      · intro h
        cases h.1 with
        | inl heq =>
          subst heq
          rw [h.2] at hp
          contradiction
        | inr hrest => exact ⟨hrest, h.2⟩

theorem mem_of_not_anyList {α : Type} (p : α → Bool) (xs : List α)
    (h : anyList p xs = false) (x : α) (hx : x ∈ xs) : p x = false := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [anyList, Bool.or_eq_false_iff] at h
    cases hx with
    | head => exact h.1
    | tail _ hrest => exact ih h.2 hrest

/-! ## Part 1: Inline `const { ... }`, `required_consts`, and Two-Stage PME Timing -/

/-- CTFE outcome for an inline `const { ... }` block. -/
inductive ConstOutcome where
  | ok (v : Nat)
  | divByZero
  | patInvalid (raw : Nat)
  | tooGeneric

noncomputable def ConstOutcome.isError : ConstOutcome → Bool
  | .ok _ => false
  | .divByZero => true
  | .patInvalid _ => true
  | .tooGeneric => false

noncomputable def ConstOutcome.eqBool : ConstOutcome → ConstOutcome → Bool
  | .ok a, .ok b => a == b
  | .divByZero, .divByZero => true
  | .patInvalid a, .patInvalid b => a == b
  | .tooGeneric, .tooGeneric => true
  | _, _ => false

/-- CFG status relative to `mir_built` and `SimplifyCfg::Initial` before
    `RequiredConstsVisitor::compute_required_consts` (`required_consts.rs`) and
    before runtime DCE / `SimplifyConstCondition`. -/
inductive BlockStage where
  | liveEntry
  | deadBranchPreDce
  | prunedAfterReturn

noncomputable def BlockStage.survivesToMirPromoted : BlockStage → Bool
  | .liveEntry => true
  | .deadBranchPreDce => true
  | .prunedAfterReturn => false

noncomputable def BlockStage.liveUnderKnownPanicsSwitchInt : BlockStage → Bool
  | .liveEntry => true
  | .deadBranchPreDce => false
  | .prunedAfterReturn => false

/-- Single `hir::ExprKind::ConstBlock` lowered to `Const::Unevaluated`. -/
structure InlineConstSite where
  cid : Nat
  dependsOnGenericParam : Bool
  promotedToFragment : Bool
  monoOutcome : ConstOutcome

/-- Basic block containing inline `const` sites. -/
structure MirBlock where
  stage : BlockStage
  consts : List InlineConstSite

/-- Function item inside a crate. -/
structure MirFnItem where
  fid : Nat
  pubExported : Bool
  isMainEntry : Bool
  isGeneric : Bool
  hasNoInlineAttr : Bool
  hasNonZeroRuntimeCalls : Bool
  stmtsCount : Nat
  inlinableThreshold : Nat
  callees : List Nat
  blocks : List MirBlock

/-- Compiler invocation modes across our empirical PME matrix. -/
inductive BuildProfile where
  | emitMetadata
  | libOpt0
  | libOpt2
  | libOpt2MirOpt0
  | binOpt0
  | binOpt2

noncomputable def BuildProfile.shouldCodegen : BuildProfile → Bool
  | .emitMetadata => false
  | _ => true

noncomputable def BuildProfile.optLevelAtLeast1 : BuildProfile → Bool
  | .emitMetadata => false
  | .libOpt0 => false
  | .libOpt2 => true
  | .libOpt2MirOpt0 => true
  | .binOpt0 => false
  | .binOpt2 => true

noncomputable def BuildProfile.mirOptInlineActive : BuildProfile → Bool
  | .libOpt2 => true
  | .binOpt2 => true
  | _ => false

noncomputable def BuildProfile.isBinaryCrate : BuildProfile → Bool
  | .binOpt0 => true
  | .binOpt2 => true
  | _ => false

/-- Collects `required_consts` right before `PromoteTemps` (`mir_promoted`),
    ignoring blocks already pruned by `SimplifyCfg::Initial` (`return; const { ... }`),
    while capturing BOTH `liveEntry` and `deadBranchPreDce` (`if false { const { ... } }`). -/
noncomputable def computeRequiredConsts (f : MirFnItem) : List InlineConstSite :=
  appendMap
    (fun b => if b.stage.survivesToMirPromoted then b.consts else [])
    f.blocks

/-- Mirrors `rustc_mir_transform::cross_crate_inline::cross_crate_inlinable`:
    returns `true` if `f` can be deferred to downstream callers in lazy library builds. -/
noncomputable def crossCrateInlinable (prof : BuildProfile) (f : MirFnItem) : Bool :=
  if f.isGeneric then
    false
  else if f.hasNoInlineAttr then
    false
  else if !prof.optLevelAtLeast1 then
    false
  else
    let effectiveCalls :=
      if prof.mirOptInlineActive then false else f.hasNonZeroRuntimeCalls
    (!effectiveCalls) && (f.stmtsCount <= f.inlinableThreshold)

/-- Mirrors `rustc_passes::reachable` + `rustc_codegen_ssa::back::symbol_export`:
    non-generic local root exported for eager local monomorphization. -/
noncomputable def isLocalMonoRoot (prof : BuildProfile) (f : MirFnItem) : Bool :=
  if !prof.shouldCodegen then
    false
  else if f.isGeneric then
    false
  else if f.isMainEntry && prof.isBinaryCrate then
    true
  else if !prof.isBinaryCrate then
    f.pubExported && !(crossCrateInlinable prof f)
  else
    false

/-- Diagnostics emitted by `KnownPanicsLint` (`known_panics_lint.rs:30-45,254,758`). -/
noncomputable def knownPanicsErrors (prof : BuildProfile) (f : MirFnItem) : List ConstOutcome :=
  if prof.shouldCodegen && !(f.isGeneric && !prof.mirOptInlineActive) then
    if f.isGeneric then
      -- `KnownPanicsLint` explicitly returns `None` when `c.has_param()` (line 254).
      []
    else if crossCrateInlinable prof f || isLocalMonoRoot prof f then
      -- Run-runtime-lowering visits live branches (via SwitchInt folding) + promoted fragments unconditionally.
      let mainBranchConsts :=
        appendMap
          (fun b =>
            if b.stage.liveUnderKnownPanicsSwitchInt then b.consts
            else filterList (fun c => c.promotedToFragment) b.consts)
          f.blocks
      filterList (fun o => o.isError) (mapList (fun c => c.monoOutcome) mainBranchConsts)
    else
      []
  else
    []

/-- Additional metadata-encode check (`encoder.rs:1869,2312`): `promoted_mir` evaluates
    extracted promoted fragments (which strip enclosing `if false`!) when `encode_opt = true`. -/
noncomputable def promotedMirMetadataErrors (prof : BuildProfile) (f : MirFnItem) : List ConstOutcome :=
  if prof.shouldCodegen && f.pubExported && crossCrateInlinable prof f then
    let promotedConsts :=
      filterList (fun c => c.promotedToFragment) (computeRequiredConsts f)
    filterList (fun o => o.isError) (mapList (fun c => c.monoOutcome) promotedConsts)
  else
    []

noncomputable def gvnEvalSite (c : InlineConstSite) : Option ConstOutcome :=
  if c.dependsOnGenericParam then
    none
  else if c.monoOutcome.isError then
    some c.monoOutcome
  else
    none

/-- `GVN` pass evaluation during `-Copt-level=2` (`gvn.rs:605`): runs on `optimized_mir`
    for generic items with `mirOptInlineActive = true` and triggers `E0080` on non-param-dependent
    constants even without instantiation. -/
noncomputable def gvnGenericErrors (prof : BuildProfile) (f : MirFnItem) : List ConstOutcome :=
  if prof.shouldCodegen && prof.mirOptInlineActive && f.isGeneric then
    let rawConsts :=
      appendMap
        (fun b => if b.stage.liveUnderKnownPanicsSwitchInt then b.consts else [])
        f.blocks
    appendMap
      (fun c => match gvnEvalSite c with | some o => [o] | none => [])
      rawConsts
  else
    []

/-- Collector evaluation of `body.required_consts` (`collector.rs:1347-1353`) for an instantiated `MirFnItem`. -/
noncomputable def collectorRequiredConstErrors (f : MirFnItem) : List ConstOutcome :=
  let reqs := computeRequiredConsts f
  filterList (fun o => o.isError) (mapList (fun c => c.monoOutcome) reqs)

/-- Looks up an item by `fid` in a crate's item list. -/
noncomputable def findFnById (id : Nat) : List MirFnItem → Option MirFnItem
  | [] => none
  | f :: fs => if f.fid == id then some f else findFnById id fs

/-- Single-hop instantiated callee errors plus root errors when local root exists (modulo MIR inline deferral). -/
noncomputable def crateCollectorErrors (prof : BuildProfile) (items : List MirFnItem) : List ConstOutcome :=
  if !prof.shouldCodegen then
    []
  else
    let monoRoots := filterList (fun f => isLocalMonoRoot prof f) items
    appendMap
      (fun root =>
        let ownErrs := collectorRequiredConstErrors root
        let calleeErrs :=
          if prof.mirOptInlineActive && crossCrateInlinable prof root then
            []
          else
            appendMap
              (fun cid =>
                match findFnById cid items with
                | some callee => collectorRequiredConstErrors callee
                | none => [])
              root.callees
        ownErrs ++ calleeErrs)
      monoRoots

/-- Total `E0080` constant errors reported by compilation under `prof`. -/
noncomputable def reportCratePmeErrors (prof : BuildProfile) (items : List MirFnItem) : List ConstOutcome :=
  if !prof.shouldCodegen then
    []
  else
    appendMap (fun f => knownPanicsErrors prof f ++ promotedMirMetadataErrors prof f ++ gvnGenericErrors prof f) items
      ++ crateCollectorErrors prof items

theorem requiredConsts_captures_deadBranchPreDce
    (f : MirFnItem) (b : MirBlock) (c : InlineConstSite)
    (hb : b ∈ f.blocks) (hstage : b.stage = .deadBranchPreDce) (hc : c ∈ b.consts) :
    c ∈ computeRequiredConsts f := by
  unfold computeRequiredConsts
  apply mem_appendMap _ b c f.blocks hb
  rw [hstage]
  simpa [BlockStage.survivesToMirPromoted] using hc

theorem computeRequiredConsts_nil_of_pruned
    (bl : List MirBlock)
    (honly : ∀ b ∈ bl, b.stage = .prunedAfterReturn) :
    appendMap (fun b => if b.stage.survivesToMirPromoted then b.consts else []) bl = [] := by
  induction bl with
  | nil => rfl
  | cons b rest ih =>
    have hb : b.stage = .prunedAfterReturn := honly b (List.mem_cons.mpr (Or.inl rfl))
    simp only [appendMap, hb, BlockStage.survivesToMirPromoted, Bool.false_eq_true, ↓reduceIte,
      List.nil_append]
    exact ih (fun b' hb' => honly b' (List.mem_cons.mpr (Or.inr hb')))

theorem requiredConsts_excludes_prunedAfterReturn
    (f : MirFnItem) (c : InlineConstSite)
    (honly : ∀ b ∈ f.blocks, b.stage = .prunedAfterReturn) :
    c ∉ computeRequiredConsts f := by
  unfold computeRequiredConsts
  rw [computeRequiredConsts_nil_of_pruned f.blocks honly]
  intro h
  cases h

theorem emitMetadata_always_skips_pme (items : List MirFnItem) :
    reportCratePmeErrors .emitMetadata items = [] := by
  simp [reportCratePmeErrors, BuildProfile.shouldCodegen]

theorem postReturn_unreachable_never_produces_collector_err
    (f : MirFnItem)
    (honly : ∀ b ∈ f.blocks, b.stage = .prunedAfterReturn) :
    collectorRequiredConstErrors f = [] := by
  unfold collectorRequiredConstErrors computeRequiredConsts
  rw [computeRequiredConsts_nil_of_pruned f.blocks honly]
  rfl

theorem monoRoot_deadConst_triggers_pme_at_codegen
    (prof : BuildProfile) (items : List MirFnItem) (f : MirFnItem)
    (b : MirBlock) (c : InlineConstSite)
    (hcodegen : prof.shouldCodegen = true)
    (hfmem : f ∈ items)
    (hroot : isLocalMonoRoot prof f = true)
    (hbmem : b ∈ f.blocks)
    (hstage : b.stage = .deadBranchPreDce)
    (hcmem : c ∈ b.consts)
    (herr : c.monoOutcome.isError = true) :
    c.monoOutcome ∈ reportCratePmeErrors prof items := by
  simp only [reportCratePmeErrors, crateCollectorErrors, hcodegen, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, List.mem_append]
  apply Or.inr
  have hfroot : f ∈ filterList (fun x => isLocalMonoRoot prof x) items :=
    (mem_filterList_iff _ _ _).mpr ⟨hfmem, hroot⟩
  apply mem_appendMap _ f c.monoOutcome _ hfroot
  rw [List.mem_append]
  apply Or.inl
  unfold collectorRequiredConstErrors
  rw [mem_filterList_iff]
  constructor
  · have hcreq : c ∈ computeRequiredConsts f :=
      requiredConsts_captures_deadBranchPreDce f b c hbmem hstage hcmem
    clear herr hroot hcodegen hbmem hstage hcmem hfmem hfroot
    generalize computeRequiredConsts f = reqs at hcreq ⊢
    induction reqs with
    | nil => cases hcreq
    | cons x xs ih =>
      simp only [mapList, List.mem_cons]
      cases hcreq with
      | head => exact Or.inl rfl
      | tail _ hxs => exact Or.inr (ih hxs)
  · exact herr

theorem gvnGenericConsts_nil_of_allParam
    (cs : List InlineConstSite)
    (hall : ∀ c ∈ cs, c.dependsOnGenericParam = true ∧ c.monoOutcome = .tooGeneric) :
    appendMap (fun c => match gvnEvalSite c with | some o => [o] | none => []) cs = [] := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hall x (List.mem_cons.mpr (Or.inl rfl))
    simp only [appendMap, gvnEvalSite, hx.1, ↓reduceIte, List.nil_append]
    exact ih (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))

theorem gvnGenericBlocks_nil_of_allParam
    (bl : List MirBlock)
    (hall : ∀ b ∈ bl, ∀ c ∈ b.consts,
      c.dependsOnGenericParam = true ∧ c.monoOutcome = .tooGeneric) :
    appendMap
      (fun c => match gvnEvalSite c with | some o => [o] | none => [])
      (appendMap (fun b => if b.stage.liveUnderKnownPanicsSwitchInt then b.consts else []) bl) = [] := by
  induction bl with
  | nil => rfl
  | cons b rest ih =>
    have hb0 := gvnGenericConsts_nil_of_allParam b.consts (hall b (List.mem_cons.mpr (Or.inl rfl)))
    have hrest := ih (fun b' hb' => hall b' (List.mem_cons.mpr (Or.inr hb')))
    cases hs : b.stage.liveUnderKnownPanicsSwitchInt with
    | false =>
      simp only [appendMap, hs, Bool.false_eq_true, ↓reduceIte, List.nil_append]
      exact hrest
    | true =>
      simp only [appendMap, hs, ↓reduceIte, appendMap_append, hb0, List.nil_append]
      exact hrest

theorem uninstantiated_paramGeneric_zero_errors
    (prof : BuildProfile) (f : MirFnItem)
    (hgen : f.isGeneric = true)
    (hall : ∀ b ∈ f.blocks, ∀ c ∈ b.consts,
      c.dependsOnGenericParam = true ∧ c.monoOutcome = .tooGeneric) :
    knownPanicsErrors prof f = [] ∧
      promotedMirMetadataErrors prof f = [] ∧
      gvnGenericErrors prof f = [] ∧
      isLocalMonoRoot prof f = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold knownPanicsErrors
    cases prof <;> simp [hgen, BuildProfile.shouldCodegen]
  · unfold promotedMirMetadataErrors
    have hcci : crossCrateInlinable prof f = false := by
      unfold crossCrateInlinable
      simp [hgen]
    simp [hcci]
  · unfold gvnGenericErrors
    cases prof with
    | emitMetadata | libOpt0 | libOpt2MirOpt0 | binOpt0 =>
      simp [BuildProfile.shouldCodegen, BuildProfile.mirOptInlineActive]
    | libOpt2 | binOpt2 =>
      simp only [BuildProfile.shouldCodegen, BuildProfile.mirOptInlineActive, hgen, Bool.and_self,
        ↓reduceIte]
      exact gvnGenericBlocks_nil_of_allParam f.blocks hall
  · unfold isLocalMonoRoot
    cases prof <;> simp [hgen, BuildProfile.shouldCodegen]

theorem promotedInlineConst_surfaces_in_libOpt2_despite_ifFalse
    (f : MirFnItem) (b : MirBlock) (c : InlineConstSite)
    (hpub : f.pubExported = true)
    (hnoinline : f.hasNoInlineAttr = false)
    (hgen : f.isGeneric = false)
    (hsmall : f.stmtsCount <= f.inlinableThreshold)
    (hb : b ∈ f.blocks)
    (hstage : b.stage = .deadBranchPreDce)
    (hc : c ∈ b.consts)
    (hprom : c.promotedToFragment = true)
    (herr : c.monoOutcome.isError = true) :
    c.monoOutcome ∈ promotedMirMetadataErrors .libOpt2 f := by
  unfold promotedMirMetadataErrors
  have hcci : crossCrateInlinable .libOpt2 f = true := by
    unfold crossCrateInlinable
    simp [BuildProfile.optLevelAtLeast1, BuildProfile.mirOptInlineActive,
      hgen, hnoinline, hsmall]
  simp only [BuildProfile.shouldCodegen, hpub, hcci, Bool.and_self, ↓reduceIte]
  rw [mem_filterList_iff]
  constructor
  · have hmem1 : c ∈ filterList (fun x => x.promotedToFragment) (computeRequiredConsts f) := by
      rw [mem_filterList_iff]
      exact ⟨requiredConsts_captures_deadBranchPreDce f b c hb hstage hc, hprom⟩
    clear hpub hnoinline hgen hsmall hb hstage hc hprom herr hcci
    generalize filterList (fun x => x.promotedToFragment) (computeRequiredConsts f) = filtered at hmem1 ⊢
    induction filtered with
    | nil => cases hmem1
    | cons x xs ih =>
      simp only [mapList, List.mem_cons]
      cases hmem1 with
      | head => exact Or.inl rfl
      | tail _ hxs => exact Or.inr (ih hxs)
  · exact herr

theorem gvn_nonparam_generic_divergence
    (f : MirFnItem) (b : MirBlock) (c : InlineConstSite)
    (hgen : f.isGeneric = true)
    (hb : b ∈ f.blocks)
    (hstage : b.stage = .liveEntry)
    (hc : c ∈ b.consts)
    (hnoparam : c.dependsOnGenericParam = false)
    (herr : c.monoOutcome.isError = true) :
    c.monoOutcome ∈ gvnGenericErrors .libOpt2 f ∧
      gvnGenericErrors .libOpt0 f = [] ∧
      gvnGenericErrors .libOpt2MirOpt0 f = [] ∧
      gvnGenericErrors .emitMetadata f = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold gvnGenericErrors
    simp only [BuildProfile.shouldCodegen, BuildProfile.mirOptInlineActive, hgen, Bool.and_self,
      ↓reduceIte]
    apply mem_appendMap _ c c.monoOutcome
    · apply mem_appendMap _ b c f.blocks hb
      rw [hstage]
      exact hc
    · simp [gvnEvalSite, hnoparam, herr]
  · simp [gvnGenericErrors, BuildProfile.mirOptInlineActive]
  · simp [gvnGenericErrors, BuildProfile.mirOptInlineActive]
  · simp [gvnGenericErrors, BuildProfile.shouldCodegen]

/-- Exact 4-mode differential matrix theorem for instantiated dead-branch generic const blocks:
    - Without `#[inline(never)]`, `trigger` is small and call-free after MIR inlining at `-Copt-level=2`,
      so `crossCrateInlinable` defers `trigger` + its callee `genDead` (`[]`), whereas `-O0` (`libOpt0`),
      `-O2 -Zmir-opt-level=0` (`libOpt2MirOpt0`), and `#[inline(never)]` (`noinline = true`) all catch
      `divByZero` via `crateCollectorErrors`. -/
theorem instantiatedGeneric_leafCaller_inlining_deferral_matrix :
    let deadConstSite : InlineConstSite :=
      { cid := 0
        dependsOnGenericParam := true
        promotedToFragment := false
        monoOutcome := .divByZero }
    let genDead : MirFnItem :=
      { fid := 2
        pubExported := true
        isMainEntry := false
        isGeneric := true
        hasNoInlineAttr := false
        hasNonZeroRuntimeCalls := false
        stmtsCount := 2
        inlinableThreshold := 45
        callees := []
        blocks := [{ stage := .deadBranchPreDce, consts := [deadConstSite] }] }
    let triggerLeaf : MirFnItem :=
      { fid := 1
        pubExported := true
        isMainEntry := false
        isGeneric := false
        hasNoInlineAttr := false
        hasNonZeroRuntimeCalls := true
        stmtsCount := 3
        inlinableThreshold := 45
        callees := [2]
        blocks := [{ stage := .liveEntry, consts := [] }] }
    let triggerNoInline : MirFnItem :=
      { triggerLeaf with hasNoInlineAttr := true }
    reportCratePmeErrors .emitMetadata [triggerLeaf, genDead] = [] ∧
      .divByZero ∈ reportCratePmeErrors .libOpt0 [triggerLeaf, genDead] ∧
      reportCratePmeErrors .libOpt2 [triggerLeaf, genDead] = [] ∧
      .divByZero ∈ reportCratePmeErrors .libOpt2MirOpt0 [triggerLeaf, genDead] ∧
      .divByZero ∈ reportCratePmeErrors .libOpt2 [triggerNoInline, genDead] := by
  simp [reportCratePmeErrors, crateCollectorErrors, knownPanicsErrors,
    promotedMirMetadataErrors, gvnGenericErrors, gvnEvalSite, collectorRequiredConstErrors,
    computeRequiredConsts, isLocalMonoRoot, crossCrateInlinable, findFnById,
    BuildProfile.shouldCodegen, BuildProfile.optLevelAtLeast1,
    BuildProfile.mirOptInlineActive, BuildProfile.isBinaryCrate,
    BlockStage.survivesToMirPromoted, BlockStage.liveUnderKnownPanicsSwitchInt,
    ConstOutcome.isError, filterList, appendMap, mapList]

/-! ## Part 2: `&const { ... }` Promotion Eligibility vs `Cell` / `Drop` Stack Lifetime -/

/-- Type classification for promotion eligibility checks in `promote_consts.rs`. -/
inductive PromType where
  | scalar
  | cellInteriorMut
  | hasDropType
  | arrayOf (elem : PromType) (len : Nat)

noncomputable def PromType.needsDrop : PromType → Bool
  | .scalar => false
  | .cellInteriorMut => false
  | .hasDropType => true
  | .arrayOf elem len => (len != 0) && elem.needsDrop

noncomputable def PromType.hasMutInterior : PromType → Bool
  | .scalar => false
  | .cellInteriorMut => true
  | .hasDropType => false
  | .arrayOf elem len => (len != 0) && elem.hasMutInterior

noncomputable def PromType.isZeroLenArray : PromType → Bool
  | .arrayOf _ 0 => true
  | _ => false

noncomputable def PromType.byteSize : PromType → Nat
  | .scalar => 4
  | .cellInteriorMut => 4
  | .hasDropType => 4
  | .arrayOf elem len => len * elem.byteSize

noncomputable def PromType.expectedDropCount : PromType → Nat
  | .scalar => 0
  | .cellInteriorMut => 0
  | .hasDropType => 1
  | .arrayOf elem len => len * elem.expectedDropCount

inductive RefKind where
  | shared
  | mutable

/-- Origin expression being borrowed (`&...` / `&mut ...`). -/
inductive BorrowExprKind where
  | constBlockPure
  | literalAggregate
  | runtimeDivZeroExpr

noncomputable def BorrowExprKind.exprPromotable : BorrowExprKind → Bool
  | .constBlockPure => true
  | .literalAggregate => true
  | .runtimeDivZeroExpr => false

/-- Exact mirror of `Validator::validate_ref` + `Validator::validate_local` in `promote_consts.rs`:
    - Shared borrow promotes iff expression is promotable, `!NeedsDrop`, and `!HasMutInterior`.
    - Mutable borrow promotes ONLY for zero-length arrays `[T; 0]` (`promote_consts.rs:396-411`). -/
noncomputable def isPromotableBorrow (rk : RefKind) (ty : PromType) (expr : BorrowExprKind) : Bool :=
  if !expr.exprPromotable then
    false
  else if ty.needsDrop then
    false
  else
    match rk with
    | .shared => !(ty.hasMutInterior)
    | .mutable => ty.isZeroLenArray

inductive LifetimeCheckResult where
  | okStaticPromoted
  | errE0515TempValue

noncomputable def checkReturnStaticRef (rk : RefKind) (ty : PromType) (expr : BorrowExprKind) :
    LifetimeCheckResult :=
  if isPromotableBorrow rk ty expr then .okStaticPromoted else .errE0515TempValue

/-- Memory semantics of promoted vs stack-materialized allocations. -/
structure StoragePlacement where
  isStaticSegment : Bool
  isReadOnlyMemory : Bool
  runsDropOnScopeExit : Bool
  observedDrops : Nat
  zeroByteWriteOnly : Bool

noncomputable def materializeBorrow (rk : RefKind) (ty : PromType) (expr : BorrowExprKind) :
    StoragePlacement :=
  if isPromotableBorrow rk ty expr then
    { isStaticSegment := true
      isReadOnlyMemory := true
      runsDropOnScopeExit := false
      observedDrops := 0
      zeroByteWriteOnly := match rk with | .shared => false | .mutable => ty.byteSize == 0 }
  else
    { isStaticSegment := false
      isReadOnlyMemory := false
      runsDropOnScopeExit := ty.needsDrop
      observedDrops := ty.expectedDropCount
      zeroByteWriteOnly := false }

noncomputable def soundMemoryModel (rk : RefKind) (ty : PromType) (pl : StoragePlacement) : Prop :=
  -- 1. Static read-only allocations must not allow non-zero-byte interior or mutable writes.
  (pl.isStaticSegment = true →
    ty.hasMutInterior = false ∧ (rk = .mutable → ty.byteSize = 0)) ∧
  -- 2. Observed runtime drops match semantic drop count.
  pl.observedDrops = ty.expectedDropCount ∧
  -- 3. `Drop` types are never hoisted to `.rodata` (`isStaticSegment = false`).
  (ty.needsDrop = true → pl.isStaticSegment = false)

theorem emptyDropArray_zero_expected_drops (elem : PromType) :
    (PromType.arrayOf elem 0).needsDrop = false ∧
      (PromType.arrayOf elem 0).expectedDropCount = 0 ∧
      (PromType.arrayOf elem 0).byteSize = 0 := by
  simp [PromType.needsDrop, PromType.expectedDropCount, PromType.byteSize]

theorem zero_len_array_promotable_both_shared_and_mut (elem : PromType) :
    isPromotableBorrow .shared (.arrayOf elem 0) .constBlockPure = true ∧
      isPromotableBorrow .mutable (.arrayOf elem 0) .constBlockPure = true ∧
      isPromotableBorrow .shared (.arrayOf elem 0) .literalAggregate = true ∧
      isPromotableBorrow .mutable (.arrayOf elem 0) .literalAggregate = true := by
  simp [isPromotableBorrow, BorrowExprKind.exprPromotable, PromType.needsDrop,
    PromType.hasMutInterior, PromType.isZeroLenArray]

theorem cell_and_drop_non_zero_fail_e0515 :
    checkReturnStaticRef .shared .cellInteriorMut .constBlockPure = .errE0515TempValue ∧
      checkReturnStaticRef .shared .hasDropType .constBlockPure = .errE0515TempValue ∧
      checkReturnStaticRef .shared .hasDropType .literalAggregate = .errE0515TempValue ∧
      checkReturnStaticRef .mutable .scalar .constBlockPure = .errE0515TempValue ∧
      checkReturnStaticRef .mutable (.arrayOf .hasDropType 0) .constBlockPure = .okStaticPromoted := by
  simp [checkReturnStaticRef, isPromotableBorrow, BorrowExprKind.exprPromotable,
    PromType.needsDrop, PromType.hasMutInterior, PromType.isZeroLenArray]

theorem promType_expectedDrops_zero_of_not_needsDrop (e : PromType)
    (hnd : e.needsDrop = false) : e.expectedDropCount = 0 := by
  induction e with
  | scalar => rfl
  | cellInteriorMut => rfl
  | hasDropType => simp [PromType.needsDrop] at hnd
  | arrayOf e2 n2 ih2 =>
    cases n2 with
    | zero => simp [PromType.expectedDropCount]
    | succ k2 =>
      have hnz : (k2 + 1 != 0) = true := rfl
      rw [PromType.needsDrop, hnz, Bool.true_and] at hnd
      simp only [PromType.expectedDropCount, ih2 hnd, Nat.mul_zero]

theorem promoted_expectedDrops_zero (rk : RefKind) (ty : PromType) (expr : BorrowExprKind)
    (hprom : isPromotableBorrow rk ty expr = true) :
    ty.expectedDropCount = 0 := by
  unfold isPromotableBorrow at hprom
  have hnd : ty.needsDrop = false := by
    cases hex : expr.exprPromotable <;> cases h : ty.needsDrop <;>
      simp [hex, h] at hprom ⊢
  exact promType_expectedDrops_zero_of_not_needsDrop ty hnd

theorem materializeBorrow_sound (rk : RefKind) (ty : PromType) (expr : BorrowExprKind) :
    soundMemoryModel rk ty (materializeBorrow rk ty expr) := by
  cases hprom : isPromotableBorrow rk ty expr with
  | false =>
    simp [materializeBorrow, soundMemoryModel, hprom]
  | true =>
    unfold soundMemoryModel materializeBorrow
    simp only [hprom, ↓reduceIte]
    have hdrop0 : ty.expectedDropCount = 0 := promoted_expectedDrops_zero rk ty expr hprom
    have hnotdrop : ty.needsDrop = false := by
      unfold isPromotableBorrow at hprom
      cases hex : expr.exprPromotable with
      | false => simp [hex] at hprom
      | true =>
        cases hnd : ty.needsDrop with
        | false => rfl
        | true => simp [hex, hnd] at hprom
    have hmut_and_zero : ty.hasMutInterior = false ∧ (rk = .mutable → ty.byteSize = 0) := by
      unfold isPromotableBorrow at hprom
      cases rk with
      | shared =>
        cases hex : expr.exprPromotable <;> cases hnd : ty.needsDrop <;>
          cases hmi : ty.hasMutInterior <;> simp [hex, hnd, hmi] at hprom ⊢
      | mutable =>
        cases hex : expr.exprPromotable <;> cases hnd : ty.needsDrop <;>
          simp [hex, hnd] at hprom
        cases ty with
        | scalar | cellInteriorMut | hasDropType =>
          simp [PromType.isZeroLenArray] at hprom
        | arrayOf elem len =>
          cases len with
          | zero =>
            simp [PromType.hasMutInterior, PromType.byteSize]
          | succ k =>
            simp [PromType.isZeroLenArray] at hprom
    refine ⟨?_, hdrop0.symm, ?_⟩
    · intro _
      exact hmut_and_zero
    · intro hneed
      rw [hnotdrop] at hneed
      contradiction

/-- Concrete Counterexample (`CE-Promote-Cell`): promoting `&const { Cell::new(5) }` into
    read-only static storage violates `soundMemoryModel` because `hasMutInterior = true`. -/
theorem ce_promote_interiorMut_breaks_rodata_soundness :
    let unsafePromPlacement : StoragePlacement :=
      { isStaticSegment := true
        isReadOnlyMemory := true
        runsDropOnScopeExit := false
        observedDrops := 0
        zeroByteWriteOnly := false }
    ¬ soundMemoryModel .shared .cellInteriorMut unsafePromPlacement := by
  intro unsafePromPlacement hsound
  have h1 := hsound.1 rfl
  simp [PromType.hasMutInterior] at h1

/-- Concrete Counterexample (`CE-Promote-Drop`): promoting `&const { HasDrop(7) }` silently skips
    the runtime destructor (`observedDrops = 0 ≠ expectedDropCount = 1`). -/
theorem ce_promote_needsDrop_loses_destructor :
    let unsafeDropPlacement : StoragePlacement :=
      { isStaticSegment := true
        isReadOnlyMemory := true
        runsDropOnScopeExit := false
        observedDrops := 0
        zeroByteWriteOnly := false }
    ¬ soundMemoryModel .shared .hasDropType unsafeDropPlacement := by
  intro unsafeDropPlacement hsound
  have h2 := hsound.2.1
  simp [PromType.expectedDropCount] at h2

/-! ## Part 3: `TyKind::Pat` (`pattern_types`) Valtrees, Niche Layout, LLVM `range`, & `Unlistable` -/

/-- Pattern range over bit patterns `[0, modulus)` in unsigned two's-complement representation:
    - `start ≤ finish`: single contiguous range `[start, finish]`, e.g., `u32 is 1..=10` or
      `i8 is -128..=-1 | 1..=127` (`start = 1, finish = 255, modulus = 256`).
    - `finish < start` (wrapping / empty scalar pat `1..=0`): rejected by `layout_of`. -/
structure PatScalarSpec where
  modulus : Nat
  start : Nat
  finish : Nat

noncomputable def PatScalarSpec.inRange (p : PatScalarSpec) (w : Nat) : Bool :=
  (w < p.modulus) && (p.start <= p.finish) && (p.start <= w) && (w <= p.finish)

noncomputable def PatScalarSpec.validLayout (p : PatScalarSpec) : Bool :=
  (0 < p.modulus) && (p.start <= p.finish) && (p.finish < p.modulus)

/-- Concrete pattern types probed in Suite C. -/
noncomputable def smallU32Spec : PatScalarSpec :=
  { modulus := 4294967296, start := 1, finish := 10 }

noncomputable def oneTwoU8Spec : PatScalarSpec :=
  { modulus := 256, start := 1, finish := 2 }

noncomputable def nonZeroI8BitsSpec : PatScalarSpec :=
  { modulus := 256, start := 1, finish := 255 }

noncomputable def emptyPatU32Spec : PatScalarSpec :=
  { modulus := 4294967296, start := 1, finish := 0 }

/-- Valid inhabitant of a pattern type. -/
structure PatVal (p : PatScalarSpec) where
  raw : Nat
  inRange_pf : p.inRange raw = true

/-- Valtree leaves always store base scalar bits (`valtrees.rs:105-112, 298-301`), stripping `ty::Pat`. -/
inductive ValTree where
  | leaf (bits : Nat)

/-- Forgetful valtree projection (`const_to_valtree_inner` stripping `ty::Pat`). -/
noncomputable def patToBaseValTree {p : PatScalarSpec} (v : PatVal p) : ValTree :=
  ValTree.leaf v.raw

/-- Constructive `Option (PatVal p)` builder avoiding `Classical.propDecidable` completely. -/
noncomputable def mkPatValOpt (p : PatScalarSpec) (n : Nat) :
    (b : Bool) → (p.inRange n = b) → Option (PatVal p)
  | true, h => some ⟨n, h⟩
  | false, _ => none

theorem mkPatValOpt_eq_some (p : PatScalarSpec) (n : Nat) (hn : p.inRange n = true) :
    mkPatValOpt p n (p.inRange n) rfl = some ⟨n, hn⟩ := by
  have helper : ∀ (b : Bool) (h : p.inRange n = b), b = true →
      mkPatValOpt p n b h = some ⟨n, hn⟩ := by
    intro b h hb
    subst hb
    rfl
  exact helper (p.inRange n) rfl hn

/-- Exact reconstruction (`valtree_to_const_value`) when pre-checked validity holds. -/
noncomputable def reconstructPatFromBaseValTree (p : PatScalarSpec) (vt : ValTree) :
    Option (PatVal p) :=
  match vt with
  | ValTree.leaf b => mkPatValOpt p b (p.inRange b) rfl

theorem patVal_ext {p : PatScalarSpec} {a b : PatVal p} (h : a.raw = b.raw) : a = b := by
  cases a
  cases b
  simp only at h
  subst h
  rfl

theorem patInRange_elim {p : PatScalarSpec} {w : Nat} (h : p.inRange w = true) :
    w < p.modulus ∧ p.start ≤ p.finish ∧ p.start ≤ w ∧ w ≤ p.finish := by
  simp only [PatScalarSpec.inRange, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1.1, of_decide_eq_true h.1.1.2,
    of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩

theorem patValidLayout_elim {p : PatScalarSpec} (h : p.validLayout = true) :
    0 < p.modulus ∧ p.start ≤ p.finish ∧ p.finish < p.modulus := by
  simp only [PatScalarSpec.validLayout, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2, of_decide_eq_true h.2⟩

theorem patToBaseValTree_injective (p : PatScalarSpec) (v1 v2 : PatVal p)
    (h : patToBaseValTree v1 = patToBaseValTree v2) : v1 = v2 := by
  unfold patToBaseValTree at h
  injection h with hbits
  exact patVal_ext hbits

theorem valtree_roundtrip_iff_valid (p : PatScalarSpec) (v : PatVal p) :
    reconstructPatFromBaseValTree p (patToBaseValTree v) = some v := by
  dsimp only [reconstructPatFromBaseValTree, patToBaseValTree]
  rw [mkPatValOpt_eq_some p v.raw v.inRange_pf]

/-- Pre-valtree validity necessity (`ce_unvalidated_pat_bypass`): base `u32` valtree accepts `0`,
    which fails `reconstructPatFromBaseValTree smallU32Spec`. -/
theorem base_valtree_zero_invalid_for_smallU32 :
    reconstructPatFromBaseValTree smallU32Spec (ValTree.leaf 0) = none := by
  rfl

theorem base_valtree_eleven_invalid_for_smallU32 :
    reconstructPatFromBaseValTree smallU32Spec (ValTree.leaf 11) = none := by
  rfl

/-- Zero-niche `Option<Pat>` encoding (`start ≥ 1`, `noneTag = 0`, `Some v => v.raw`). -/
noncomputable def encodeOptionZeroNiche {p : PatScalarSpec} : Option (PatVal p) → Nat
  | none => 0
  | some v => v.raw

noncomputable def decodeOptionZeroNiche (p : PatScalarSpec) : Nat → Option (PatVal p)
  | 0 => none
  | n + 1 => mkPatValOpt p (n + 1) (p.inRange (n + 1)) rfl

theorem encodeOptionZeroNiche_lt_modulus (p : PatScalarSpec)
    (hvalid : p.validLayout = true) (o : Option (PatVal p)) :
    encodeOptionZeroNiche o < p.modulus := by
  cases o with
  | none =>
    simp only [encodeOptionZeroNiche]
    exact (patValidLayout_elim hvalid).1
  | some v =>
    exact (patInRange_elim v.inRange_pf).1

theorem patVal_nonzero_of_start_ge_one (p : PatScalarSpec) (hstart : 1 <= p.start)
    (v : PatVal p) : v.raw ≠ 0 := by
  have hv := (patInRange_elim v.inRange_pf).2.2.1
  have hge : 1 <= v.raw := Nat.le_trans hstart hv
  intro hz
  rw [hz] at hge
  cases hge

theorem encodeOptionZeroNiche_injective (p : PatScalarSpec) (hstart : 1 <= p.start)
    (o1 o2 : Option (PatVal p))
    (h : encodeOptionZeroNiche o1 = encodeOptionZeroNiche o2) : o1 = o2 := by
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some v2 =>
      simp only [encodeOptionZeroNiche] at h
      exfalso
      exact patVal_nonzero_of_start_ge_one p hstart v2 h.symm
  | some v1 =>
    cases o2 with
    | none =>
      simp only [encodeOptionZeroNiche] at h
      exfalso
      exact patVal_nonzero_of_start_ge_one p hstart v1 h
    | some v2 =>
      simp only [encodeOptionZeroNiche] at h
      congr 1
      exact patVal_ext h

theorem decode_encode_optionZeroNiche_roundtrip (p : PatScalarSpec) (hstart : 1 <= p.start)
    (o : Option (PatVal p)) :
    decodeOptionZeroNiche p (encodeOptionZeroNiche o) = o := by
  cases o with
  | none => rfl
  | some v =>
    have hnz : v.raw ≠ 0 := patVal_nonzero_of_start_ge_one p hstart v
    cases hraw : v.raw with
    | zero => exact absurd hraw hnz
    | succ k =>
      dsimp only [encodeOptionZeroNiche]
      rw [hraw]
      dsimp only [decodeOptionZeroNiche]
      have hk : p.inRange (k + 1) = true := hraw ▸ v.inRange_pf
      rw [mkPatValOpt_eq_some p (k + 1) hk]
      congr 1
      exact patVal_ext hraw.symm

/-- Double-nested `Option<Option<OneTwo>>` (`u8 is 1..=2`) 1-byte niche encoding (`0..256`).
    - `OuterSome (InnerSome v)` => `v.raw` (`1` or `2`)
    - `OuterSome None` => `0`
    - `OuterNone` => `3` -/
noncomputable def encodeOpt2OneTwo : Option (Option (PatVal oneTwoU8Spec)) → Nat
  | none => 3
  | some none => 0
  | some (some v) => v.raw

noncomputable def decodeOpt2OneTwo : Nat → Option (Option (PatVal oneTwoU8Spec))
  | 3 => none
  | 0 => some none
  | b =>
    match mkPatValOpt oneTwoU8Spec b (oneTwoU8Spec.inRange b) rfl with
    | some v => some (some v)
    | none => none

theorem oneTwo_raw_bounds (v : PatVal oneTwoU8Spec) : v.raw = 1 ∨ v.raw = 2 := by
  have hv := patInRange_elim v.inRange_pf
  have h1 : 1 <= v.raw := hv.2.2.1
  have h2 : v.raw <= 2 := hv.2.2.2
  cases hval : v.raw with
  | zero =>
    rw [hval] at h1
    cases h1
  | succ k =>
    cases k with
    | zero => exact Or.inl rfl
    | succ m =>
      cases m with
      | zero => exact Or.inr rfl
      | succ _ =>
        rw [hval] at h2
        contradiction

theorem encodeOpt2OneTwo_fits_u8 (oo : Option (Option (PatVal oneTwoU8Spec))) :
    encodeOpt2OneTwo oo < 256 := by
  cases oo with
  | none => decide
  | some inner =>
    cases inner with
    | none => decide
    | some v =>
      simp only [encodeOpt2OneTwo]
      cases oneTwo_raw_bounds v with
      | inl h1 => rw [h1]; decide
      | inr h2 => rw [h2]; decide

theorem decode_encode_opt2OneTwo_roundtrip (oo : Option (Option (PatVal oneTwoU8Spec))) :
    decodeOpt2OneTwo (encodeOpt2OneTwo oo) = oo := by
  cases oo with
  | none => rfl
  | some inner =>
    cases inner with
    | none => rfl
    | some v =>
      dsimp only [encodeOpt2OneTwo]
      cases oneTwo_raw_bounds v with
      | inl h1 =>
        rw [h1]
        have heval : decodeOpt2OneTwo 1 = some (some ⟨1, rfl⟩) := rfl
        rw [heval]
        congr 2
        exact patVal_ext h1.symm
      | inr h2 =>
        rw [h2]
        have heval : decodeOpt2OneTwo 2 = some (some ⟨2, rfl⟩) := rfl
        rw [heval]
        congr 2
        exact patVal_ext h2.symm

/-- Concrete round-trip + layout theorems for `Option<Small>` and `Option<NonZeroI8>`. -/
theorem option_small_and_nzi8_sound :
    (∀ o : Option (PatVal smallU32Spec),
      decodeOptionZeroNiche smallU32Spec (encodeOptionZeroNiche o) = o ∧
        encodeOptionZeroNiche o < 11) ∧
    (∀ o : Option (PatVal nonZeroI8BitsSpec),
      decodeOptionZeroNiche nonZeroI8BitsSpec (encodeOptionZeroNiche o) = o ∧
        encodeOptionZeroNiche o < 256) := by
  constructor
  · intro o
    constructor
    · exact decode_encode_optionZeroNiche_roundtrip smallU32Spec (by decide) o
    · cases o with
      | none => simp [encodeOptionZeroNiche]
      | some v =>
        exact Nat.lt_succ_of_le (patInRange_elim v.inRange_pf).2.2.2
  · intro o
    constructor
    · exact decode_encode_optionZeroNiche_roundtrip nonZeroI8BitsSpec (by decide) o
    · exact encodeOptionZeroNiche_lt_modulus nonZeroI8BitsSpec (by decide) o

/-- LLVM `-O2` metadata checks corresponding directly to `range_check_after_small`
    and `impossible_check_after_small` in Suite C. -/
noncomputable def llvmInRangeCheckSmall (raw : Nat) : Bool :=
  (1 <= raw) && (raw <= 10)

noncomputable def llvmImpossibleCheckSmall (raw : Nat) : Bool :=
  (raw == 0) || (raw == 11)

theorem llvm_range_metadata_sound_for_valid_small (v : PatVal smallU32Spec) :
    llvmInRangeCheckSmall v.raw = true ∧
      llvmImpossibleCheckSmall v.raw = false ∧
      v.raw < 11 := by
  have hv := patInRange_elim v.inRange_pf
  have hlo : 1 <= v.raw := hv.2.2.1
  have hhi : v.raw <= 10 := hv.2.2.2
  refine ⟨?_, ?_, Nat.lt_succ_of_le hhi⟩
  · simp [llvmInRangeCheckSmall, hlo, hhi]
  · simp only [llvmImpossibleCheckSmall, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    constructor
    · intro hz
      rw [hz] at hlo
      cases hlo
    · intro heq
      rw [heq] at hhi
      exact (by decide : ¬ (11 <= 10)) hhi

/-- CTFE / Miri stacked-borrows & tree-borrows validity oracle. -/
inductive InterpResult where
  | valid (bits : Nat)
  | ubRangeError (raw : Nat)

noncomputable def evalPatTransmute (p : PatScalarSpec) (raw : Nat) : InterpResult :=
  if p.inRange raw then .valid raw else .ubRangeError raw

/-- Concrete UB witness (`zero` and `eleven`) explaining why native `-O2` diverges silently
    whereas CTFE (`E0080`) and Miri (`SB`/`TB`) trap immediately on transmutes. -/
theorem ce_transmute_zero_eleven_ub_and_llvm_divergence :
    evalPatTransmute smallU32Spec 0 = .ubRangeError 0 ∧
      evalPatTransmute smallU32Spec 11 = .ubRangeError 11 ∧
      evalPatTransmute smallU32Spec 5 = .valid 5 ∧
      llvmImpossibleCheckSmall 0 = true ∧
      llvmImpossibleCheckSmall 11 = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Exhaustiveness representation matching `rustc_pattern_analysis/src/rustc.rs:423`
    (`ConstructorSet::Unlistable`). -/
inductive ConstructorSet where
  | finite (inhabitants : List Nat)
  | unlistable

inductive MatchArmPat where
  | lit (n : Nat)
  | wildcard

noncomputable def matchArmCovers (n : Nat) : MatchArmPat → Bool
  | .lit k => k == n
  | .wildcard => true

noncomputable def matchArmsCoverVal (arms : List MatchArmPat) (n : Nat) : Bool :=
  anyList (fun a => matchArmCovers n a) arms

noncomputable def patternAnalysisExhaustive (cs : ConstructorSet) (arms : List MatchArmPat) : Bool :=
  match cs with
  | .unlistable => anyList (fun a => match a with | .wildcard => true | .lit _ => false) arms
  | .finite xs => allList (fun x => matchArmsCoverVal arms x) xs

noncomputable def ctorSetForPatType (_p : PatScalarSpec) : ConstructorSet :=
  .unlistable

theorem unlistable_rejects_empty_match_and_literal_only_matches (p : PatScalarSpec)
    (arms : List MatchArmPat)
    (hnowild : ∀ a ∈ arms, match a with | .wildcard => False | .lit _ => True) :
    patternAnalysisExhaustive (ctorSetForPatType p) arms = false := by
  simp only [ctorSetForPatType, patternAnalysisExhaustive]
  induction arms with
  | nil => rfl
  | cons a rest ih =>
    simp only [anyList, Bool.or_eq_false_iff]
    constructor
    · cases a with
      | wildcard =>
        exfalso
        exact hnowild .wildcard (List.mem_cons_self ..)
      | lit _ => rfl
    · exact ih (fun x hx => hnowild x (List.mem_cons_of_mem _ hx))

theorem unlistable_accepts_wildcard_and_covers_all (p : PatScalarSpec)
    (arms : List MatchArmPat)
    (hw : .wildcard ∈ arms) :
    patternAnalysisExhaustive (ctorSetForPatType p) arms = true ∧
      ∀ n : Nat, matchArmsCoverVal arms n = true := by
  constructor
  · simp only [ctorSetForPatType, patternAnalysisExhaustive]
    induction arms with
    | nil => cases hw
    | cons a rest ih =>
      simp only [anyList, Bool.or_eq_true]
      cases hw with
      | head => exact Or.inl rfl
      | tail _ hrest => exact Or.inr (ih hrest)
  · intro n
    unfold matchArmsCoverVal
    induction arms with
    | nil => cases hw
    | cons a rest ih =>
      simp only [anyList, Bool.or_eq_true]
      cases hw with
      | head => exact Or.inl rfl
      | tail _ hrest => exact Or.inr (ih hrest)

theorem emptyPat_triggers_e0004_before_layout_error :
    patternAnalysisExhaustive (ctorSetForPatType emptyPatU32Spec) [] = false ∧
      emptyPatU32Spec.validLayout = false := by
  simp [ctorSetForPatType, patternAnalysisExhaustive, anyList,
    PatScalarSpec.validLayout, emptyPatU32Spec]

theorem finite_exhaustive_iff_all_covered (xs : List Nat) (arms : List MatchArmPat) :
    patternAnalysisExhaustive (.finite xs) arms = true ↔
      ∀ x ∈ xs, matchArmsCoverVal arms x = true := by
  simp only [patternAnalysisExhaustive]
  constructor
  · intro h x hx
    exact allList_of_mem _ xs h x hx
  · intro hall
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [allList, Bool.and_eq_true]
      exact ⟨hall a (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun y hy => hall y (List.mem_cons.mpr (Or.inr hy)))⟩

/-! ## Part 4: Integrated Cross-Feature Soundness & Anneal Admission Boundary -/

/-- Features encountered in MIR / types by Anneal's verified lowering (`Trusted/MirAst.lean`). -/
inductive RustMirFeature where
  | plainScalarConst (val : Nat)
  | unloweredConstBlockUneval (outcome : ConstOutcome)
  | promotedStaticScalarRef (val : Nat)
  | promotedOpaquePtrOrSlice
  | unreducedPatType (spec : PatScalarSpec)
  | erasedScalarAfterOpt (val : Nat)

inductive AnnealLowerResult where
  | admittedScalar (val : Nat)
  | unsupportedFailClosed

noncomputable def lowerFeatureToAnneal : RustMirFeature → AnnealLowerResult
  | .plainScalarConst v => .admittedScalar v
  | .erasedScalarAfterOpt v => .admittedScalar v
  | .unloweredConstBlockUneval _ => .unsupportedFailClosed
  | .promotedStaticScalarRef _ => .unsupportedFailClosed
  | .promotedOpaquePtrOrSlice => .unsupportedFailClosed
  | .unreducedPatType _ => .unsupportedFailClosed

noncomputable def featureSemanticsPreserved : RustMirFeature → AnnealLowerResult → Prop
  | _, .unsupportedFailClosed => True
  | .plainScalarConst v, .admittedScalar v' => v = v'
  | .erasedScalarAfterOpt v, .admittedScalar v' => v = v'
  | _, .admittedScalar _ => False

theorem anneal_lowering_fail_closed_sound (feat : RustMirFeature) :
    featureSemanticsPreserved feat (lowerFeatureToAnneal feat) := by
  cases feat <;> simp [lowerFeatureToAnneal, featureSemanticsPreserved]

theorem anneal_blocks_pat_valtree_and_unevaluated_const (p : PatScalarSpec) (o : ConstOutcome) :
    lowerFeatureToAnneal (.unreducedPatType p) = .unsupportedFailClosed ∧
      lowerFeatureToAnneal (.unloweredConstBlockUneval o) = .unsupportedFailClosed ∧
      lowerFeatureToAnneal .promotedOpaquePtrOrSlice = .unsupportedFailClosed := by
  simp [lowerFeatureToAnneal]

end InlineConstRequiredConstsAndPatValtreeSoundness
