/-!
# Soundness of `rustc` Crate-Type Export Thresholds, `.rmeta` MIR Encoding vs.
`cross_crate_inlinable` Decoupling, and `-Z share-generics` Instantiation Ownership

Standalone, kernel-checked Lean `v4.34.1` formalization modeling three
interacting cross-crate compilation mechanisms audited in `rust-lang/rust`
(revisions `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and
`bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`):

1. **Crate-Type Export-Threshold Semilattice & Two-Tier Filtering**
   (`compiler/rustc_codegen_ssa/src/back/symbol_export.rs`,
    `compiler/rustc_middle/src/middle/exported_symbols.rs`,
    `compiler/rustc_codegen_ssa/src/back/linker.rs`,
    `compiler/rustc_codegen_ssa/src/back/link.rs`).
2. **Two-Bit `.rmeta` Capability Model `(mirEncodedInRmeta, crossCrateInlinable)`**
   (`compiler/rustc_metadata/src/rmeta/encoder.rs`,
    `compiler/rustc_mir_transform/src/cross_crate_inline.rs`,
    `compiler/rustc_mir_transform/src/inline.rs`,
    `compiler/rustc_monomorphize/src/collector.rs`).
3. **`-Z share-generics` Ownership, v0 Instantiating-Crate Mangling, and
   Collision-Free Link-Resolution Completeness**
   (`compiler/rustc_monomorphize/src/partitioning.rs`,
    `compiler/rustc_middle/src/mono.rs`,
    `compiler/rustc_symbol_mangling/src/lib.rs`,
    `compiler/rustc_symbol_mangling/src/v0.rs`).

Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
zero `native_decide`, zero `partial def`, zero `axiom`.
-/

namespace RmetaExportShareGenerics

/-! ## Part 1: Crate-Type Export-Threshold Lattice and Two-Tier Export Filtering -/

/-- Rust crate output types (`rustc_session::config::CrateType`). -/
inductive CrateType where
  | executable
  | staticlib
  | procMacro
  | cdylib
  | rlib
  | dylib
  | sdylib
  deriving DecidableEq, Repr

/-- Symbol export tiers (`rustc_middle::middle::exported_symbols::SymbolExportLevel`).
    Ordered as `c ≤ rust` (`c` is exported by all dynamic/C-ABI boundaries;
    `rust` is exported only by Rust-ABI crate types). -/
inductive SymbolExportLevel where
  | c
  | rust
  deriving DecidableEq, Repr

/-- Mirrors `SymbolExportLevel::is_below_threshold(self, threshold)`:
    a symbol at level `lvl` passes a boundary at threshold `thresh` iff
    `thresh = .rust` or `lvl = .c`. -/
def exportLe (lvl thresh : SymbolExportLevel) : Bool :=
  match lvl, thresh with
  | .c, _ => true
  | .rust, .rust => true
  | .rust, .c => false

/-- Join (least upper bound) in the two-point export-level lattice (`c ≤ rust`). -/
def exportJoin (a b : SymbolExportLevel) : SymbolExportLevel :=
  match a, b with
  | .c, .c => .c
  | _, _ => .rust

theorem exportLe_refl (a : SymbolExportLevel) : exportLe a a = true := by
  cases a <;> rfl

theorem exportLe_antisymm {a b : SymbolExportLevel}
    (hab : exportLe a b = true) (hba : exportLe b a = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd hab (by decide) | exact absurd hba (by decide)

theorem exportLe_trans {a b z : SymbolExportLevel}
    (hab : exportLe a b = true) (hbz : exportLe b z = true) : exportLe a z = true := by
  cases a <;> cases b <;> cases z <;>
    first | rfl | exact absurd hab (by decide) | exact absurd hbz (by decide)

theorem exportJoin_comm (a b : SymbolExportLevel) : exportJoin a b = exportJoin b a := by
  cases a <;> cases b <;> rfl

theorem exportJoin_assoc (a b z : SymbolExportLevel) :
    exportJoin (exportJoin a b) z = exportJoin a (exportJoin b z) := by
  cases a <;> cases b <;> cases z <;> rfl

theorem exportJoin_idem (a : SymbolExportLevel) : exportJoin a a = a := by
  cases a <;> rfl

theorem exportJoin_lub_iff (a b t : SymbolExportLevel) :
    exportLe (exportJoin a b) t = true ↔ exportLe a t = true ∧ exportLe b t = true := by
  cases a <;> cases b <;> cases t <;> decide

/-- Mirrors `crate_export_threshold` in `rustc_codegen_ssa/src/back/symbol_export.rs`. -/
def crateExportThreshold : CrateType → SymbolExportLevel
  | .executable | .staticlib | .procMacro | .cdylib => .c
  | .rlib | .dylib | .sdylib => .rust

/-- Mirrors `crates_export_threshold` in `rustc_codegen_ssa/src/back/symbol_export.rs`:
    returns `.rust` iff any requested crate type has threshold `.rust`. -/
def cratesExportThreshold : List CrateType → SymbolExportLevel
  | [] => .c
  | ct :: rest => exportJoin (crateExportThreshold ct) (cratesExportThreshold rest)

theorem cratesExportThreshold_eq_rust_iff (cts : List CrateType) :
    cratesExportThreshold cts = .rust ↔ ∃ ct, ct ∈ cts ∧ crateExportThreshold ct = .rust := by
  induction cts with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨ct, hmem, _⟩; cases hmem
  | cons ct rest ih =>
    simp only [cratesExportThreshold, List.mem_cons]
    cases hct : crateExportThreshold ct with
    | rust =>
      constructor
      · intro _
        exact ⟨ct, Or.inl rfl, hct⟩
      · intro _
        cases cratesExportThreshold rest <;> rfl
    | c =>
      have hjoin : exportJoin .c (cratesExportThreshold rest) = cratesExportThreshold rest := by
        cases cratesExportThreshold rest <;> rfl
      rw [hjoin, ih]
      constructor
      · rintro ⟨x, hx, hxr⟩
        exact ⟨x, Or.inr hx, hxr⟩
      · rintro ⟨x, hx | hx, hxr⟩
        · subst hx
          rw [hct] at hxr
          cases hxr
        · exact ⟨x, hx, hxr⟩

/-- Join homomorphism of `cratesExportThreshold` over crate-type list concatenation. -/
theorem cratesExportThreshold_append (xs ys : List CrateType) :
    cratesExportThreshold (xs ++ ys) =
      exportJoin (cratesExportThreshold xs) (cratesExportThreshold ys) := by
  induction xs with
  | nil =>
    change cratesExportThreshold ys = exportJoin .c (cratesExportThreshold ys)
    cases cratesExportThreshold ys <;> rfl
  | cons x xs ih =>
    simp only [List.cons_append, cratesExportThreshold, ih, exportJoin_assoc]

/-- Every member of a session crate-type list has threshold bounded by the session join. -/
theorem cratesExportThreshold_upper_bound {ct : CrateType} {cts : List CrateType}
    (hmem : ct ∈ cts) :
    exportLe (crateExportThreshold ct) (cratesExportThreshold cts) = true := by
  induction cts with
  | nil => cases hmem
  | cons x rest ih =>
    cases hmem with
    | head =>
      change exportLe (crateExportThreshold ct)
        (exportJoin (crateExportThreshold ct) (cratesExportThreshold rest)) = true
      cases crateExportThreshold ct <;> cases cratesExportThreshold rest <;> rfl
    | tail _ hrest =>
      have hsub := ih hrest
      have hle : exportLe (cratesExportThreshold rest)
          (exportJoin (crateExportThreshold x) (cratesExportThreshold rest)) = true := by
        cases crateExportThreshold x <;> cases cratesExportThreshold rest <;> rfl
      exact exportLe_trans hsub hle

/-- Monotonicity of `cratesExportThreshold` under subset inclusion of crate-type lists. -/
theorem cratesExportThreshold_monotone {xs ys : List CrateType}
    (hsub : ∀ ct, ct ∈ xs → ct ∈ ys) :
    exportLe (cratesExportThreshold xs) (cratesExportThreshold ys) = true := by
  induction xs with
  | nil =>
    change exportLe .c (cratesExportThreshold ys) = true
    cases cratesExportThreshold ys <;> rfl
  | cons x rest ih =>
    have hx : exportLe (crateExportThreshold x) (cratesExportThreshold ys) = true :=
      cratesExportThreshold_upper_bound (hsub x (List.Mem.head _))
    have hrest : exportLe (cratesExportThreshold rest) (cratesExportThreshold ys) = true :=
      ih (fun ct hct => hsub ct (List.Mem.tail _ hct))
    exact (exportJoin_lub_iff (crateExportThreshold x) (cratesExportThreshold rest)
      (cratesExportThreshold ys)).mpr ⟨hx, hrest⟩

/-- Explicit symbol linkage attributes modeled after `rustc_hir::attrs::Linkage`. -/
inductive ExplicitLinkage where
  | internal
  | weak
  | external
  deriving DecidableEq, Repr

/-- Symbol codegen attributes relevant to `contains_extern_indicator` and
    `symbol_export_level` (`codegen_fn_attrs.rs`, `symbol_export.rs`). -/
structure CodegenAttrs where
  isForeignItem : Bool := false
  noMangle : Bool := false
  hasExportName : Bool := false
  explicitLinkage : Option ExplicitLinkage := none
  isStdInternal : Bool := false
  isEii : Bool := false
  isCompilerBuiltins : Bool := false
  isEmscriptenStatic : Bool := false
  customLinkSection : Option String := none
  deriving DecidableEq, Repr

/-- Mirrors `CodegenFnAttrs::contains_extern_indicator`
    (`compiler/rustc_middle/src/middle/codegen_fn_attrs.rs`). -/
def containsExternIndicator (a : CodegenAttrs) : Bool :=
  if a.isForeignItem then
    false
  else
    a.noMangle
      || a.isStdInternal
      || a.isEii
      || a.hasExportName
      || match a.explicitLinkage with
         | none | some .internal => false
         | some .weak | some .external => true

/-- Mirrors `reachable_non_generics_provider` + `symbol_export_level`
    (`compiler/rustc_codegen_ssa/src/back/symbol_export.rs`). -/
def symbolExportLevel (a : CodegenAttrs) : SymbolExportLevel :=
  if a.isCompilerBuiltins then
    .rust
  else if containsExternIndicator a && !a.isStdInternal && !a.isEii then
    if a.isEmscriptenStatic then .rust else .c
  else
    .rust

/-- A reachable non-generic symbol record emitted into `CrateInfo`. -/
structure ReachableSymbol where
  name : String
  attrs : CodegenAttrs
  deriving DecidableEq, Repr

/-- CGU-retention tier (CGU codegen retention, `is_reachable_non_generic_provider_local`):
    a reachable non-generic symbol is retained (not internalized) in CGU `.rcgu.o`
    files iff its level is below the session join `cratesExportThreshold sessionTypes`. -/
def cguRetained (sessionTypes : List CrateType) (s : ReachableSymbol) : Bool :=
  exportLe (symbolExportLevel s.attrs) (cratesExportThreshold sessionTypes)

/-- per-artifact linker-export tier (Per-artifact linker dynamic export list,
    `linker::exported_symbols_for_non_proc_macro`):
    filtered independently by `crateExportThreshold ct` and excluding
    `compiler_builtins`. -/
def artifactLinkerExported (ct : CrateType) (s : ReachableSymbol) : Bool :=
  exportLe (symbolExportLevel s.attrs) (crateExportThreshold ct) && !s.attrs.isCompilerBuiltins

def dynamicExportsForArtifact (ct : CrateType) (syms : List ReachableSymbol) :
    List ReachableSymbol :=
  syms.filter (artifactLinkerExported ct)

/-- Archive metadata packaging contract (`link_rlib` vs. `link_staticlib` in
    `compiler/rustc_codegen_ssa/src/back/link.rs`). -/
def archiveIncludesRmeta : CrateType → Bool
  | .rlib => true
  | _ => false

def archiveIncludesRmetaLink : CrateType → Bool
  | .rlib => true
  | _ => false

def dylibExportsMetadataSymbol : CrateType → Bool
  | .dylib | .procMacro => true
  | _ => false

/-- Characterization of `symbolExportLevel a = .c`. -/
theorem symbolExportLevel_eq_c_iff (a : CodegenAttrs) :
    symbolExportLevel a = .c ↔
      a.isCompilerBuiltins = false ∧
      containsExternIndicator a = true ∧
      a.isStdInternal = false ∧
      a.isEii = false ∧
      a.isEmscriptenStatic = false := by
  unfold symbolExportLevel
  cases hcb : a.isCompilerBuiltins <;>
    cases hext : containsExternIndicator a <;>
    cases hstd : a.isStdInternal <;>
    cases heii : a.isEii <;>
    cases hem : a.isEmscriptenStatic <;>
    decide

theorem containsExternIndicator_false_of_foreign {a : CodegenAttrs}
    (hf : a.isForeignItem = true) : containsExternIndicator a = false := by
  simp [containsExternIndicator, hf]

/-- **Theorem 1 (Soundness of `cdylib` Dynamic Export Minimality)**:
    Every symbol emitted into a `cdylib` dynamic export list has
    `symbolExportLevel = .c`, carries a non-foreign extern indicator
    (`#[no_mangle]`, `#[export_name]`, or non-internal `#[linkage]`), and is
    neither `RUSTC_STD_INTERNAL_SYMBOL`, `EXTERNALLY_IMPLEMENTABLE_ITEM`,
    `compiler_builtins`, nor an Emscripten static. -/
theorem cdylib_exports_only_c_level_symbols (syms : List ReachableSymbol)
    (s : ReachableSymbol) (hmem : s ∈ dynamicExportsForArtifact .cdylib syms) :
    symbolExportLevel s.attrs = .c ∧
    containsExternIndicator s.attrs = true ∧
    s.attrs.isForeignItem = false ∧
    s.attrs.isStdInternal = false ∧
    s.attrs.isEii = false ∧
    s.attrs.isCompilerBuiltins = false := by
  have hfilt := List.mem_filter.mp hmem
  have hpred : artifactLinkerExported .cdylib s = true := hfilt.2
  unfold artifactLinkerExported crateExportThreshold at hpred
  have hle : exportLe (symbolExportLevel s.attrs) .c = true := by
    cases h1 : exportLe (symbolExportLevel s.attrs) .c
    · rw [h1] at hpred; cases hpred
    · rfl
  have hlvl : symbolExportLevel s.attrs = .c := by
    cases hl : symbolExportLevel s.attrs with
    | c => rfl
    | rust => rw [hl] at hle; cases hle
  have hchar := (symbolExportLevel_eq_c_iff s.attrs).mp hlvl
  have hnotfor : s.attrs.isForeignItem = false := by
    cases hf : s.attrs.isForeignItem with
    | false => rfl
    | true =>
      have hcf := containsExternIndicator_false_of_foreign hf
      rw [hcf] at hchar
      exact absurd hchar.2.1 (by decide)
  exact ⟨hlvl, hchar.2.1, hnotfor, hchar.2.2.1, hchar.2.2.2.1, hchar.1⟩

/-- **Link-Closure Completeness Across Multi-Crate-Type Sessions**:
    Whenever `ct ∈ sessionTypes`, every symbol required in `ct`'s per-artifact linker-export tier
    export table is guaranteed to have been retained by CGU-retention tier CGU codegen
    (`cguRetained sessionTypes s = true`). -/
theorem cgu_retains_every_artifact_export (sessionTypes : List CrateType)
    (ct : CrateType) (hct : ct ∈ sessionTypes) (syms : List ReachableSymbol)
    (s : ReachableSymbol) (hmem : s ∈ dynamicExportsForArtifact ct syms) :
    cguRetained sessionTypes s = true := by
  have hpred : artifactLinkerExported ct s = true := (List.mem_filter.mp hmem).2
  unfold artifactLinkerExported at hpred
  have hle_ct : exportLe (symbolExportLevel s.attrs) (crateExportThreshold ct) = true := by
    cases h1 : exportLe (symbolExportLevel s.attrs) (crateExportThreshold ct)
    · rw [h1] at hpred; cases hpred
    · rfl
  have hbound : exportLe (crateExportThreshold ct) (cratesExportThreshold sessionTypes) = true :=
    cratesExportThreshold_upper_bound hct
  exact exportLe_trans hle_ct hbound

/-- **Combined `cdylib + rlib` Session Theorem**:
    Co-compiling `[.cdylib, .rlib]` raises the CGU-retention tier session join to `.rust`
    (retaining Rust-level symbols for the `rlib`), while per-artifact linker-export tier still restricts
    the `cdylib` dynamic symbol table exclusively to `SymbolExportLevel.c`. -/
theorem combined_cdylib_rlib_preserves_both_contracts (syms : List ReachableSymbol) :
    cratesExportThreshold [.cdylib, .rlib] = .rust ∧
    (∀ s ∈ syms, cguRetained [.cdylib, .rlib] s = true) ∧
    (∀ s ∈ dynamicExportsForArtifact .cdylib syms, symbolExportLevel s.attrs = .c) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro s _
    unfold cguRetained
    change exportLe (symbolExportLevel s.attrs) .rust = true
    cases symbolExportLevel s.attrs <;> rfl
  · intro s hs
    exact (cdylib_exports_only_c_level_symbols syms s hs).1

theorem staticlib_omits_rmeta_while_rlib_includes_both :
    archiveIncludesRmeta .rlib = true ∧
    archiveIncludesRmetaLink .rlib = true ∧
    archiveIncludesRmeta .staticlib = false ∧
    archiveIncludesRmetaLink .staticlib = false ∧
    dylibExportsMetadataSymbol .dylib = true ∧
    dylibExportsMetadataSymbol .cdylib = false := by
  decide

/-! ## Part 2: Two-Bit `.rmeta` Capability Model (`should_encode_mir` vs. `cross_crate_inlinable`) -/

/-- Subset of `rustc_hir::def::DefKind` relevant to `should_encode_mir` and
    `cross_crate_inlinable`. -/
inductive MirDefKind where
  | ctor
  | constItem
  | coroutine
  | syntheticCoroutineBody
  | fnItem
  | assocFn
  | closure
  | other
  deriving DecidableEq, Repr

/-- Mirrors `rustc_hir::attrs::InlineAttr`. -/
inductive InlineAttr where
  | none
  | hint
  | always
  | never
  deriving DecidableEq, Repr

/-- Mirrors `rustc_session::config::InliningThreshold`. -/
inductive InliningThreshold where
  | never
  | sometimes (limit : Nat)
  | always
  deriving DecidableEq, Repr

/-- Mirrors `CostChecker` counters in `rustc_mir_transform/src/cross_crate_inline.rs`. -/
structure CostMetrics where
  calls : Nat
  resumes : Nat
  landingPads : Nat
  statements : Nat
  deriving DecidableEq, Repr

/-- Session compilation options controlling `.rmeta` MIR encoding and
    cross-crate inlining inference. -/
structure CompileOpts where
  shouldCodegen : Bool
  incremental : Bool
  alwaysEncodeMir : Bool
  inlineThreshold : InliningThreshold
  optEnabled : Bool
  mirInlinerWillRun : Bool
  hintMostlyUnused : Bool := false
  deriving DecidableEq, Repr

/-- Per-item metadata profile in the upstream crate. -/
structure MirItem where
  kind : MirDefKind
  isConstFn : Bool := false
  isComptimeAlwaysConst : Bool := false
  reachable : Bool := true
  requiresMono : Bool := false
  hasExternIndicator : Bool := false
  isIntrinsic : Bool := false
  inlineAttr : InlineAttr := .none
  hasUnreliableF16OrF128 : Bool := false
  hasLocalMir : Bool := true
  cost : CostMetrics := { calls := 0, resumes := 0, landingPads := 0, statements := 3 }
  callsPrivateUpstreamHelper : Bool := false
  deriving DecidableEq, Repr

/-- Mirrors `cross_crate_inlinable` (`compiler/rustc_mir_transform/src/cross_crate_inline.rs`).
    Crucially, this predicate NEVER reads `opts.alwaysEncodeMir`. -/
def crossCrateInlinable (opts : CompileOpts) (item : MirItem) : Bool :=
  if item.hasExternIndicator then
    false
  else
    match item.kind with
    | .ctor | .closure | .syntheticCoroutineBody => true
    | .fnItem | .assocFn =>
      match opts.inlineThreshold with
      | .always => true
      | _ =>
        if item.isIntrinsic then
          true
        else if item.isComptimeAlwaysConst then
          false
        else
          match item.inlineAttr with
          | .never => false
          | .hint | .always => true
          | .none =>
            if opts.hintMostlyUnused then
              true
            else if item.hasUnreliableF16OrF128 then
              true
            else if opts.incremental then
              false
            else if !opts.optEnabled && !opts.mirInlinerWillRun then
              false
            else if !item.hasLocalMir then
              false
            else
              match opts.inlineThreshold with
              | .always => true
              | .never => false
              | .sometimes limit =>
                decide (item.cost.calls = 0 ∧ item.cost.resumes = 0 ∧
                        item.cost.landingPads = 0 ∧ item.cost.statements ≤ limit)
    | _ => false

/-- Mirrors `should_encode_mir` (`compiler/rustc_metadata/src/rmeta/encoder.rs`),
    returning `(encodeConstMir, encodeOptMir)`. -/
def shouldEncodeMir (opts : CompileOpts) (item : MirItem) : Bool × Bool :=
  match item.kind with
  | .ctor => (true, false)
  | .constItem => (true, false)
  | .coroutine => (false, true)
  | .syntheticCoroutineBody => (false, true)
  | .fnItem | .assocFn | .closure =>
    let rawOpt :=
      opts.alwaysEncodeMir
        || (opts.shouldCodegen
            && item.reachable
            && (item.requiresMono || crossCrateInlinable opts item))
    let opt := rawOpt && !item.isComptimeAlwaysConst
    (item.isConstFn, opt)
  | .other => (false, false)

/-- Two-bit `.rmeta` capability projection separating MIR availability from
    codegen cross-crate inlining eligibility. -/
structure RmetaCapabilities where
  mirEncodedInRmeta : Bool
  crossCrateInlinable : Bool
  deriving DecidableEq, Repr

def itemRmetaCapabilities (opts : CompileOpts) (item : MirItem) : RmetaCapabilities :=
  { mirEncodedInRmeta := (shouldEncodeMir opts item).2
  , crossCrateInlinable := crossCrateInlinable opts item }

/-- Mirrors `reachable_non_generics_provider` (`symbol_export.rs:81-96`) for
    non-generic functions: exported as a linkable upstream symbol iff reachable,
    non-generic, and NOT `cross_crate_inlinable`. -/
def inReachableNonGenerics (opts : CompileOpts) (item : MirItem) : Bool :=
  match item.kind with
  | .fnItem | .assocFn =>
    opts.shouldCodegen && item.reachable && !item.requiresMono && !crossCrateInlinable opts item
  | _ => false

/-- Mirrors `collector::should_codegen_locally` (`collector.rs:1070`) for an
    upstream non-generic function called from downstream: returns `false`
    (emitting an external `call`/`invoke` without local codegen) whenever the
    item is in `reachable_non_generics`, WITHOUT checking `mirEncodedInRmeta`. -/
def downstreamCodegensLocallyNonGeneric (opts : CompileOpts) (item : MirItem) : Bool :=
  !inReachableNonGenerics opts item

/-- Mirrors the MIR inliner eligibility gate (`inline.rs:731, 834-837`):
    even when `mirEncodedInRmeta = true`, non-generic cross-crate calls require
    `crossCrateInlinable = true`. -/
def downstreamMirInlinerEligible (opts : CompileOpts) (item : MirItem) : Bool :=
  (shouldEncodeMir opts item).2
    && (item.requiresMono || crossCrateInlinable opts item)

/-- Mirrors Miri / Anneal cross-crate MIR capture availability
    (`tcx.is_mir_available(def_id)`): depends strictly on `mirEncodedInRmeta`. -/
def verificationConsumerMirAvailable (opts : CompileOpts) (item : MirItem) : Bool :=
  (shouldEncodeMir opts item).2

/-- **Theorem 2a (Exact Invariance of `cross_crate_inlinable` Under `-Z always-encode-mir`)**:
    Toggling `alwaysEncodeMir` NEVER alters `crossCrateInlinable`. -/
theorem alwaysEncodeMir_preserves_crossCrateInlinable
    (opts : CompileOpts) (item : MirItem) (flag : Bool) :
    crossCrateInlinable { opts with alwaysEncodeMir := flag } item =
      crossCrateInlinable opts item := by
  unfold crossCrateInlinable
  rfl

/-- **Theorem 2b (Exact Codegen & MIR-Inliner Invariance Under `-Z always-encode-mir`)**:
    For every reachable non-generic upstream function with
    `crossCrateInlinable opts item = false`, toggling `-Z always-encode-mir`
    preserves `inReachableNonGenerics`, preserves
    `downstreamCodegensLocallyNonGeneric = false` (downstream still emits an
    external call without LTO), AND keeps `downstreamMirInlinerEligible = false`
    (even `-Z inline-mir=yes` refuses to inline it). -/
theorem alwaysEncodeMir_preserves_codegen_and_mir_inlining
    (opts : CompileOpts) (item : MirItem) (flag : Bool)
    (hnonmono : item.requiresMono = false)
    (hnotinline : crossCrateInlinable opts item = false) :
    let opts' := { opts with alwaysEncodeMir := flag }
    inReachableNonGenerics opts' item = inReachableNonGenerics opts item ∧
    downstreamCodegensLocallyNonGeneric opts' item =
      downstreamCodegensLocallyNonGeneric opts item ∧
    downstreamMirInlinerEligible opts' item = false := by
  intro opts'
  have hcci : crossCrateInlinable opts' item = false := by
    rw [alwaysEncodeMir_preserves_crossCrateInlinable]
    exact hnotinline
  refine ⟨?_, ?_, ?_⟩
  · unfold inReachableNonGenerics
    cases item.kind <;> simp [opts', hcci, hnotinline]
  · unfold downstreamCodegensLocallyNonGeneric inReachableNonGenerics
    cases item.kind <;> simp [opts', hcci, hnotinline]
  · unfold downstreamMirInlinerEligible
    simp [hnonmono, hcci]

/-- **Theorem 2c (`-Z always-encode-mir` Completeness for Verification Consumers)**:
    For every non-comptime function, associated function, or closure, enabling
    `alwaysEncodeMir = true` guarantees `verificationConsumerMirAvailable = true`
    regardless of `incremental`, `inlineThreshold`, `reachable`, or `optEnabled`. -/
theorem alwaysEncodeMir_guarantees_verification_mir_available
    (opts : CompileOpts) (item : MirItem)
    (hkind : item.kind = .fnItem ∨ item.kind = .assocFn ∨ item.kind = .closure)
    (hcomptime : item.isComptimeAlwaysConst = false) :
    verificationConsumerMirAvailable { opts with alwaysEncodeMir := true } item = true := by
  unfold verificationConsumerMirAvailable shouldEncodeMir
  rcases hkind with h | h | h <;> simp [h, hcomptime]

/-- **Theorem 2d (No `NoOptimizedMir` Gap for Reachable Cross-Crate-Inlinable Functions)**:
    Whenever `shouldCodegen = true`, `reachable = true`, and `isComptimeAlwaysConst = false`,
    any `fnItem`/`assocFn` with `crossCrateInlinable = true` automatically has
    `mirEncodedInRmeta = true`. Thus the capability pair `(false, true)` is uninhabited
    for reachable runtime functions under codegen. -/
theorem crossCrateInlinable_implies_mirEncoded_when_reachable_codegen
    (opts : CompileOpts) (item : MirItem)
    (hcg : opts.shouldCodegen = true)
    (hreach : item.reachable = true)
    (hcomptime : item.isComptimeAlwaysConst = false)
    (hkind : item.kind = .fnItem ∨ item.kind = .assocFn)
    (hcci : crossCrateInlinable opts item = true) :
    (itemRmetaCapabilities opts item).mirEncodedInRmeta = true := by
  unfold itemRmetaCapabilities shouldEncodeMir
  rcases hkind with h | h <;> simp [h, hcg, hreach, hcomptime, hcci]

/-- **Theorem 2e (Why `inline.rs` Must Gate on `crossCrateInlinable`, Not `mirEncodedInRmeta`)**:
    Suppose upstream exports a private helper only when its caller is
    `cross_crate_inlinable` (`privateHelperExported opts item = crossCrateInlinable opts item`).
    Then `downstreamMirInlinerEligible` (which gates on `crossCrateInlinable` for
    non-generic items) NEVER permits inlining a non-generic body that references
    an unexported private upstream helper. -/
def privateHelperExported (opts : CompileOpts) (item : MirItem) : Bool :=
  item.requiresMono || crossCrateInlinable opts item

theorem mir_inliner_gate_prevents_unexported_helper_reference
    (opts : CompileOpts) (item : MirItem)
    (helig : downstreamMirInlinerEligible opts item = true) :
    privateHelperExported opts item = true := by
  unfold downstreamMirInlinerEligible at helig
  unfold privateHelperExported
  cases h1 : (shouldEncodeMir opts item).2 <;>
    cases h2 : (item.requiresMono || crossCrateInlinable opts item) <;>
    simp_all

/-! ## Part 3: `-Z share-generics` Ownership, v0 Crate Disambiguation, and Link Safety -/

/-- Stable crate identifier (`CrateNum` / `StableCrateId`). -/
structure CrateId where
  id : Nat
  deriving DecidableEq, Repr

/-- A concrete monomorphization `(defCrate, itemId, typeArgId)` together with
    attributes affecting instantiation mode and exportability. -/
structure GenericInst where
  defCrate : CrateId
  itemId : Nat
  typeArgId : Nat
  inlineAttr : InlineAttr
  crossCrateInlinableAtOpt : Bool
  deriving DecidableEq, Repr

/-- Mirrors `rustc_middle::mono::InstantiationMode` for generic functions
    (`compiler/rustc_middle/src/mono.rs:192-235`). -/
inductive InstMode where
  | globallyShared
  | localCopy
  deriving DecidableEq, Repr

def genericInstantiationMode (optIsNo : Bool) (inst : GenericInst) : InstMode :=
  if !inst.crossCrateInlinableAtOpt then
    .globallyShared
  else if inst.inlineAttr == .always then
    .localCopy
  else if inst.inlineAttr == .never then
    .globallyShared
  else if optIsNo then
    .globallyShared
  else
    .localCopy

/-- Mirrors whether `upstream` exports an upstream-instantiated generic in
    `exported_generic_symbols_provider_local` (`symbol_export.rs:290-311`) and
    keeps it non-internalized in `partitioning.rs:213-214, 855-871`.
    Key invariant: `InlineAttr.never` is exported EVEN when `shareGenerics = false`. -/
def crateExportsGeneric (shareGenerics : Bool) (optIsNo : Bool) (inst : GenericInst) : Bool :=
  match genericInstantiationMode optIsNo inst with
  | .localCopy => false
  | .globallyShared => shareGenerics || (inst.inlineAttr == .never)

/-- LLVM / ELF linkage state of a symbol in a compiled object unit. -/
inductive ObjLinkage where
  | externalDef   -- `define ...` (global `T`, exported)
  | internalDef   -- `define internal ...` (local `t`, CGU-private)
  | externalDecl  -- `declare ...` (undefined reference `U`, resolved at link time)
  | omitted       -- not referenced/instantiated in this crate
  deriving DecidableEq, Repr

/-- v0 mangled symbol key with instantiating-crate disambiguation
    (`compiler/rustc_symbol_mangling/src/lib.rs:131-139, 259-261`, `v0.rs:81-83`). -/
structure MangledSym where
  defCrate : CrateId
  itemId : Nat
  typeArgId : Nat
  instantiatingCrate : CrateId
  deriving DecidableEq, Repr

structure EmittedSym where
  ownerCrate : CrateId
  sym : MangledSym
  linkage : ObjLinkage
  deriving DecidableEq, Repr

/-- Symbol emitted by `upstream` (crate `upId`) for `inst`. -/
def upstreamEmit (upId : CrateId) (shareGenerics optIsNo instantiatedUpstream : Bool)
    (inst : GenericInst) : EmittedSym :=
  let s : MangledSym :=
    { defCrate := inst.defCrate
    , itemId := inst.itemId
    , typeArgId := inst.typeArgId
    , instantiatingCrate := upId }
  if !instantiatedUpstream then
    { ownerCrate := upId, sym := s, linkage := .omitted }
  else if crateExportsGeneric shareGenerics optIsNo inst then
    { ownerCrate := upId, sym := s, linkage := .externalDef }
  else
    { ownerCrate := upId, sym := s, linkage := .internalDef }

/-- Symbol emitted by a downstream crate `dsId` referencing `inst`
    (`collector.rs:1070`, `partitioning.rs:840-853`, `symbol_mangling/src/lib.rs:134`). -/
def downstreamEmit (upId dsId : CrateId) (shareGenerics optIsNo instantiatedUpstream : Bool)
    (inst : GenericInst) : EmittedSym :=
  if instantiatedUpstream && crateExportsGeneric shareGenerics optIsNo inst then
    -- Reused from upstream: `should_codegen_locally = false`, `instantiatingCrate = upId` (`EB2_`)
    { ownerCrate := dsId
    , sym := { defCrate := inst.defCrate
             , itemId := inst.itemId
             , typeArgId := inst.typeArgId
             , instantiatingCrate := upId }
    , linkage := .externalDecl }
  else
    -- Instantiated locally in `dsId`: `instantiatingCrate = dsId` (`ECs..._2ds`)
    let link :=
      if crateExportsGeneric shareGenerics optIsNo inst then
        ObjLinkage.externalDef
      else
        ObjLinkage.internalDef
    { ownerCrate := dsId
    , sym := { defCrate := inst.defCrate
             , itemId := inst.itemId
             , typeArgId := inst.typeArgId
             , instantiatingCrate := dsId }
    , linkage := link }

/-- Two emitted symbols collide at link time iff both are global `externalDef`s
    with identical mangled symbol names. -/
def collides (a b : EmittedSym) : Prop :=
  a.linkage = .externalDef ∧ b.linkage = .externalDef ∧ a.sym = b.sym

/-- A linked object table is duplicate-global-symbol-free iff no two distinct
    list positions collide. -/
def NoDuplicateGlobalSymbols (objs : List EmittedSym) : Prop :=
  ∀ (i j : Nat) (hi : i < objs.length) (hj : j < objs.length),
    i ≠ j → ¬ collides (objs[i]'hi) (objs[j]'hj)

/-- A linked object table is link-complete iff every `externalDecl` resolves to
    at least one `externalDef` with the exact same `MangledSym`. -/
def AllExternalDeclsResolved (objs : List EmittedSym) : Prop :=
  ∀ e ∈ objs, e.linkage = .externalDecl →
    ∃ d ∈ objs, d.linkage = .externalDef ∧ d.sym = e.sym

/-- **Theorem 3a (`#[inline(never)]` Generics Stay Externally Shared in BOTH Modes)**:
    Regardless of `-Z share-generics={yes,no}` and regardless of `optIsNo`, an
    upstream-instantiated `#[inline(never)]` generic is ALWAYS defined externally
    by `upstream` (`EB2_`) and declared externally by `downstream` (`declare ...EB2_`). -/
theorem inline_never_generic_always_shared_regardless_of_shareGenerics
    (upId dsId : CrateId) (shareGenerics optIsNo : Bool) (inst : GenericInst)
    (hnever : inst.inlineAttr = .never) :
    (upstreamEmit upId shareGenerics optIsNo true inst).linkage = .externalDef ∧
    (downstreamEmit upId dsId shareGenerics optIsNo true inst).linkage = .externalDecl ∧
    (downstreamEmit upId dsId shareGenerics optIsNo true inst).sym.instantiatingCrate = upId := by
  have hexp : crateExportsGeneric shareGenerics optIsNo inst = true := by
    unfold crateExportsGeneric genericInstantiationMode
    cases inst.crossCrateInlinableAtOpt <;> simp [hnever]
  simp [upstreamEmit, downstreamEmit, hexp]

/-- **Theorem 3b (Unmarked Non-Inlinable Generic Flips Ownership on `-Z share-generics`)**:
    For an unmarked (`inlineAttr = .none`), non-inlinable
    (`crossCrateInlinableAtOpt = false`) generic instantiated in `upstream`:
    - under `shareGenerics = true`, downstream emits `.externalDecl` targeting `upId` (`EB2_`),
    - under `shareGenerics = false`, downstream emits `.internalDef` stamped with `dsId` (`ECs..._2ds`). -/
theorem unmarked_noninlinable_generic_flips_on_shareGenerics
    (upId dsId : CrateId) (optIsNo : Bool) (inst : GenericInst)
    (hnone : inst.inlineAttr = .none)
    (hnonin : inst.crossCrateInlinableAtOpt = false) :
    (downstreamEmit upId dsId true optIsNo true inst).linkage = .externalDecl ∧
    (downstreamEmit upId dsId true optIsNo true inst).sym.instantiatingCrate = upId ∧
    (downstreamEmit upId dsId false optIsNo true inst).linkage = .internalDef ∧
    (downstreamEmit upId dsId false optIsNo true inst).sym.instantiatingCrate = dsId := by
  have hyes : crateExportsGeneric true optIsNo inst = true := by
    simp [crateExportsGeneric, genericInstantiationMode, hnonin]
  have hno : crateExportsGeneric false optIsNo inst = false := by
    simp [crateExportsGeneric, genericInstantiationMode, hnonin, hnone]
  simp [downstreamEmit, hyes, hno]

private theorem noDup3 {a b c : EmittedSym}
    (hab : ¬ collides a b) (hac : ¬ collides a c) (hbc : ¬ collides b c) :
    NoDuplicateGlobalSymbols [a, b, c] := by
  intro i j hi hj hne
  match i, j with
  | 0, 0 => exact absurd rfl hne
  | 0, 1 => exact hab
  | 0, 2 => exact hac
  | 1, 0 => intro ⟨h1, h2, h3⟩; exact hab ⟨h2, h1, h3.symm⟩
  | 1, 1 => exact absurd rfl hne
  | 1, 2 => exact hbc
  | 2, 0 => intro ⟨h1, h2, h3⟩; exact hac ⟨h2, h1, h3.symm⟩
  | 2, 1 => intro ⟨h1, h2, h3⟩; exact hbc ⟨h2, h1, h3.symm⟩
  | 2, 2 => exact absurd rfl hne
  | n + 3, _ => cases hi with | step h => cases h with | step h => cases h with | step h => cases h
  | _, m + 3 => cases hj with | step h => cases h with | step h => cases h with | step h => cases h

/-- **Theorem 3c (`shareGenerics_link_safe_and_collision_free`)**:
    For ANY `shareGenerics : Bool`, ANY `optIsNo : Bool`, ANY `inst : GenericInst`,
    ANY `instantiatedUpstream : Bool`, and ANY three distinct crates
    `upId`, `ds1Id`, `ds2Id` (one upstream library plus two sibling downstream
    crates linked into the same final binary), the combined object symbol table
    satisfies BOTH:
    1. `NoDuplicateGlobalSymbols` (zero duplicate external definitions), AND
    2. `AllExternalDeclsResolved` (every `declare` resolves to an `externalDef`
       with identical `MangledSym`). -/
theorem shareGenerics_link_safe_and_collision_free
    (upId ds1Id ds2Id : CrateId)
    (h23 : ds1Id ≠ ds2Id)
    (shareGenerics optIsNo instantiatedUpstream : Bool) (inst : GenericInst) :
    let u := upstreamEmit upId shareGenerics optIsNo instantiatedUpstream inst
    let d1 := downstreamEmit upId ds1Id shareGenerics optIsNo instantiatedUpstream inst
    let d2 := downstreamEmit upId ds2Id shareGenerics optIsNo instantiatedUpstream inst
    NoDuplicateGlobalSymbols [u, d1, d2] ∧ AllExternalDeclsResolved [u, d1, d2] := by
  intro u d1 d2
  cases hinst : instantiatedUpstream <;> cases hexp : crateExportsGeneric shareGenerics optIsNo inst
  · -- instantiatedUpstream = false, crateExportsGeneric = false: u=omitted, d1=internalDef, d2=internalDef
    have hu : u.linkage = .omitted := by simp [u, upstreamEmit, hinst]
    have hd1 : d1.linkage = .internalDef := by simp [d1, downstreamEmit, hinst, hexp]
    have hd2 : d2.linkage = .internalDef := by simp [d2, downstreamEmit, hinst, hexp]
    constructor
    · refine noDup3 ?_ ?_ ?_
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨h1, _, _⟩; rw [hd1] at h1; cases h1
    · intro e he hdecl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [hu] at hdecl; cases hdecl
      · rw [hd1] at hdecl; cases hdecl
      · rw [hd2] at hdecl; cases hdecl
  · -- instantiatedUpstream = false, crateExportsGeneric = true: u=omitted, d1=externalDef(ds1), d2=externalDef(ds2)
    have hu : u.linkage = .omitted := by simp [u, upstreamEmit, hinst]
    have hd1l : d1.linkage = .externalDef := by simp [d1, downstreamEmit, hinst, hexp]
    have hd2l : d2.linkage = .externalDef := by simp [d2, downstreamEmit, hinst, hexp]
    have hd1c : d1.sym.instantiatingCrate = ds1Id := by simp [d1, downstreamEmit, hinst, hexp]
    have hd2c : d2.sym.instantiatingCrate = ds2Id := by simp [d2, downstreamEmit, hinst, hexp]
    constructor
    · refine noDup3 ?_ ?_ ?_
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨_, _, hsym⟩
        have hceq : d1.sym.instantiatingCrate = d2.sym.instantiatingCrate :=
          congrArg MangledSym.instantiatingCrate hsym
        rw [hd1c, hd2c] at hceq
        exact h23 hceq
    · intro e he hdecl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [hu] at hdecl; cases hdecl
      · rw [hd1l] at hdecl; cases hdecl
      · rw [hd2l] at hdecl; cases hdecl
  · -- instantiatedUpstream = true, crateExportsGeneric = false: u=internalDef, d1=internalDef, d2=internalDef
    have hu : u.linkage = .internalDef := by simp [u, upstreamEmit, hinst, hexp]
    have hd1 : d1.linkage = .internalDef := by simp [d1, downstreamEmit, hinst, hexp]
    have hd2 : d2.linkage = .internalDef := by simp [d2, downstreamEmit, hinst, hexp]
    constructor
    · refine noDup3 ?_ ?_ ?_
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨h1, _, _⟩; rw [hu] at h1; cases h1
      · intro ⟨h1, _, _⟩; rw [hd1] at h1; cases h1
    · intro e he hdecl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [hu] at hdecl; cases hdecl
      · rw [hd1] at hdecl; cases hdecl
      · rw [hd2] at hdecl; cases hdecl
  · -- instantiatedUpstream = true, crateExportsGeneric = true: u=externalDef(up), d1=externalDecl(up), d2=externalDecl(up)
    have hu : u.linkage = .externalDef := by simp [u, upstreamEmit, hinst, hexp]
    have hd1l : d1.linkage = .externalDecl := by simp [d1, downstreamEmit, hinst, hexp]
    have hd2l : d2.linkage = .externalDecl := by simp [d2, downstreamEmit, hinst, hexp]
    have hsym1 : u.sym = d1.sym := by simp [u, d1, upstreamEmit, downstreamEmit, hinst, hexp]
    have hsym2 : u.sym = d2.sym := by simp [u, d2, upstreamEmit, downstreamEmit, hinst, hexp]
    constructor
    · refine noDup3 ?_ ?_ ?_
      · intro ⟨_, h2, _⟩; rw [hd1l] at h2; cases h2
      · intro ⟨_, h2, _⟩; rw [hd2l] at h2; cases h2
      · intro ⟨h1, _, _⟩; rw [hd1l] at h1; cases h1
    · intro e he hdecl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · rw [hu] at hdecl; cases hdecl
      · exact ⟨u, List.Mem.head _, hu, hsym1⟩
      · exact ⟨u, List.Mem.head _, hu, hsym2⟩

/-! ## Part 4: Three Constructive Counterexamples -/

/-- Concrete upstream fixture matching `probe_rmeta_export_and_share_generics.py`:
    4 C-level symbols + 1 Rust-level function + 1 `#[rustc_std_internal_symbol]` hook. -/
def probeUpstreamSymbols : List ReachableSymbol :=
  [ { name := "CUSTOM_SEC_VAL"
    , attrs := { noMangle := true, customLinkSection := some ".my_custom_sec" } }
  , { name := "c_api_no_mangle"
    , attrs := { noMangle := true } }
  , { name := "custom_c_export_sym"
    , attrs := { hasExportName := true } }
  , { name := "weak_c_hook"
    , attrs := { noMangle := true, explicitLinkage := some .weak } }
  , { name := "upstream_instantiate_u32"
    , attrs := {} }
  , { name := "__rust_alloc"
    , attrs := { noMangle := true, isStdInternal := true } }
  ]

/-- Buggy cdylib exporter that mistakenly uses `SymbolExportLevel.rust` threshold. -/
def buggyCdylibDynamicExports (syms : List ReachableSymbol) : List ReachableSymbol :=
  syms.filter (fun s => exportLe (symbolExportLevel s.attrs) .rust && !s.attrs.isCompilerBuiltins)

/-- **Counterexample 1 (`ce1_exporting_rust_level_symbols_in_cdylib_leaks_unstable_abi`)**:
    A cdylib exporter that permits `SymbolExportLevel.rust` leaks both the
    mangled Rust symbol `upstream_instantiate_u32` and the `std`-internal
    allocator symbol `__rust_alloc` into `.dynsym`, whereas the sound
    `dynamicExportsForArtifact .cdylib` exports strictly the 4 C-ABI symbols. -/
theorem ce1_exporting_rust_level_symbols_in_cdylib_leaks_unstable_abi :
    let soundExports := dynamicExportsForArtifact .cdylib probeUpstreamSymbols
    let buggyExports := buggyCdylibDynamicExports probeUpstreamSymbols
    soundExports.length = 4 ∧
    (soundExports.map ReachableSymbol.name) =
      ["CUSTOM_SEC_VAL", "c_api_no_mangle", "custom_c_export_sym", "weak_c_hook"] ∧
    (∃ s ∈ buggyExports, s.name = "upstream_instantiate_u32" ∧ symbolExportLevel s.attrs = .rust) ∧
    (∃ s ∈ buggyExports, s.name = "__rust_alloc" ∧ s.attrs.isStdInternal = true) ∧
    (∀ s ∈ soundExports, s.name ≠ "upstream_instantiate_u32" ∧ s.name ≠ "__rust_alloc") := by
  decide

/-- Concrete `upstream::rust_unmarked_leaf` and `upstream::rust_marked_inline`
    compiled under `-C incremental=... -Z always-encode-mir -C opt-level=2`. -/
def incrAlwaysEncodeOpts : CompileOpts :=
  { shouldCodegen := true
  , incremental := true
  , alwaysEncodeMir := true
  , inlineThreshold := .sometimes 12
  , optEnabled := true
  , mirInlinerWillRun := true }

def unmarkedLeafItem : MirItem :=
  { kind := .fnItem
  , reachable := true
  , requiresMono := false
  , inlineAttr := .none
  , cost := { calls := 0, resumes := 0, landingPads := 0, statements := 3 } }

def markedInlineItem : MirItem :=
  { unmarkedLeafItem with inlineAttr := .hint }

/-- **Counterexample 2 (`ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental`)**:
    Under `-C incremental=... -Z always-encode-mir -C opt-level=2`, the unmarked
    small leaf function `rust_unmarked_leaf` HAS its optimized MIR encoded in
    `lib.rmeta` (`mirEncodedInRmeta = true`, available to Miri/Anneal), YET:
    1. `crossCrateInlinable = false`,
    2. `downstreamCodegensLocallyNonGeneric = false` (external call without LTO), and
    3. `downstreamMirInlinerEligible = false` (even `-Z inline-mir=yes` rejects it),
    whereas the explicit `#[inline]` sibling `rust_marked_inline` under the exact
    same flags satisfies `crossCrateInlinable = true` and `downstreamMirInlinerEligible = true`. -/
theorem ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental :
    let capsUnmarked := itemRmetaCapabilities incrAlwaysEncodeOpts unmarkedLeafItem
    let capsInline := itemRmetaCapabilities incrAlwaysEncodeOpts markedInlineItem
    capsUnmarked.mirEncodedInRmeta = true ∧
    capsUnmarked.crossCrateInlinable = false ∧
    downstreamCodegensLocallyNonGeneric incrAlwaysEncodeOpts unmarkedLeafItem = false ∧
    downstreamMirInlinerEligible incrAlwaysEncodeOpts unmarkedLeafItem = false ∧
    capsInline.mirEncodedInRmeta = true ∧
    capsInline.crossCrateInlinable = true ∧
    downstreamMirInlinerEligible incrAlwaysEncodeOpts markedInlineItem = true := by
  decide

/-- Buggy downstream emitter that forgets BOTH internalization AND
    instantiating-crate v0 disambiguation when instantiating an unshared
    downstream generic (`share-generics=no`): it stamps `inst.defCrate` instead
    of `dsId` and emits `externalDef` instead of `internalDef`. -/
def buggyUnsharedDownstreamEmit (dsId : CrateId) (inst : GenericInst) : EmittedSym :=
  { ownerCrate := dsId
  , sym := { defCrate := inst.defCrate
           , itemId := inst.itemId
           , typeArgId := inst.typeArgId
           , instantiatingCrate := inst.defCrate }
  , linkage := .externalDef }

/-- **Counterexample 3 (`ce3_emitting_external_linkage_for_unshared_downstream_generic_causes_duplicate_symbol_link_error`)**:
    When two crates (`ds1`, `ds2`, or `upstream` and `ds`) instantiate the same
    unshared generic (`generic_shared::<u32>`) and a buggy backend emits
    `externalDef` without instantiating-crate disambiguation, linking fails with
    a duplicate global symbol collision (`¬ NoDuplicateGlobalSymbols`). -/
theorem ce3_emitting_external_linkage_for_unshared_downstream_generic_causes_duplicate_symbol_link_error :
    let upId : CrateId := ⟨1⟩
    let ds1Id : CrateId := ⟨2⟩
    let ds2Id : CrateId := ⟨3⟩
    let inst : GenericInst :=
      { defCrate := upId
      , itemId := 14
      , typeArgId := 32
      , inlineAttr := .none
      , crossCrateInlinableAtOpt := false }
    let buggyObjs :=
      [ buggyUnsharedDownstreamEmit ds1Id inst
      , buggyUnsharedDownstreamEmit ds2Id inst ]
    ¬ NoDuplicateGlobalSymbols buggyObjs := by
  intro upId ds1Id ds2Id inst buggyObjs hnoDup
  have hcol : collides (buggyObjs[0]'(by decide)) (buggyObjs[1]'(by decide)) :=
    ⟨rfl, rfl, rfl⟩
  exact hnoDup 0 1 (by decide) (by decide) (by decide) hcol

/-! ## Axiom Audit -/

#print axioms cratesExportThreshold_monotone
#print axioms cratesExportThreshold_append
#print axioms cdylib_exports_only_c_level_symbols
#print axioms cgu_retains_every_artifact_export
#print axioms combined_cdylib_rlib_preserves_both_contracts
#print axioms alwaysEncodeMir_preserves_crossCrateInlinable
#print axioms alwaysEncodeMir_preserves_codegen_and_mir_inlining
#print axioms alwaysEncodeMir_guarantees_verification_mir_available
#print axioms crossCrateInlinable_implies_mirEncoded_when_reachable_codegen
#print axioms mir_inliner_gate_prevents_unexported_helper_reference
#print axioms inline_never_generic_always_shared_regardless_of_shareGenerics
#print axioms unmarked_noninlinable_generic_flips_on_shareGenerics
#print axioms shareGenerics_link_safe_and_collision_free
#print axioms ce1_exporting_rust_level_symbols_in_cdylib_leaks_unstable_abi
#print axioms ce2_assuming_always_encode_mir_enables_cross_crate_inlining_fails_under_incremental
#print axioms ce3_emitting_external_linkage_for_unshared_downstream_generic_causes_duplicate_symbol_link_error

end RmetaExportShareGenerics
