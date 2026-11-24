/-!
# Monomorphization Collector (`Lazy` vs. `Eager`), `#[used(compiler)]` vs. `#[used(linker)]`, and LLVM `MergeFunctions` Soundness

Standalone Lean `v4.34.1` formalization modeling three coupled stages of the
`rustc` monomorphization, codegen, and LLVM optimization/linking pipeline:

1. **Monomorphization Root Selection and Call-Graph Collection
   (`rustc_monomorphize::collector`, `rustc_monomorphize::partitioning`,
   `rustc_codegen_ssa::back::symbol_export`, `rustc_mir_transform::cross_crate_inline`):**
   - Models `CrateKind` (`bin` vs. `rlib`), `CollectionStrategy` (`lazy` vs. `eager`),
     `OptLevel` (`o0`, `o1`, `o2`, `o3`, `os`, `oz`), `crossCrateInlinable`,
     `isReachableNonGeneric`, `ExportLevel` thresholds (`C` vs. `Rust`), and
     `RootCollector::is_root`.
   - Captures why `eager` (`-Clink-dead-code=yes`) still excludes uninstantiated
     generic items (`requires_monomorphization = true`), why `rlib` `lazy` defers
     small public cross-crate-inlinable functions (`pub_dead_small`) while
     collecting `#[inline(never)] pub_dead_exported`, why `bin` `lazy` omits
     Rust-ABI public dead functions (`SymbolExportLevel::Rust < SymbolExportLevel::C`),
     and why `DefKind::Static` items are unconditional collector roots.

2. **`#[used(compiler)]` vs. `#[used(linker)]`, LLVM `GlobalDCE`, and ELF
   `SHF_GNU_RETAIN` Linker Garbage Collection (`rustc_codegen_ssa::codegen_attrs`,
   `rustc_codegen_llvm::consts`, LLVM `TargetLoweringObjectFileELF`, `AsmPrinter`):**
   - Models `TargetOS`-dependent lowering of `#[used]` (`usedDefault` -> `linkerRetain`
     everywhere except `illumos`), LLVM IR `@llvm.compiler.used` vs. `@llvm.used`,
     LLVM `GlobalDCE` preservation, ELF section flags (`A` = `SHF_ALLOC` vs.
     `AR` = `SHF_ALLOC | SHF_GNU_RETAIN`), and linker `--gc-sections` retention.

3. **Removal of `-Zpolymorphize` and LLVM `-O2` `MergeFunctions` Folding
   (`llvm::MergeFunctions`, `rustc_codegen_llvm::llvm_util`):**
   - Models a typed IR fragment with value/constant/size-dependent instructions,
     `FunctionComparator` structural equivalence, and the three-way lowering in
     `MergeFunctions::writeThunkOrAliasIfNeeded` (`eraseAndRewrite` for discardable
     `internal unnamed_addr` functions, `emitAlias` for `external unnamed_addr` under
     `MergeFunctions::Aliases`, and `emitThunk` under `MergeFunctions::Trampolines`).
   - Proves call-graph and observational equivalence preservation under structural
     folding, while proving why size-dependent monomorphs (`poly_size::<T>`) must
     remain distinct.

4. **Sharpness Counterexamples and Concrete Specimen Verification:**
   - Proves concrete evaluations matching live `rustc` empirical counts (`17`/`20` for
     `bin`, `10`/`13` for `rlib`, `4` vs. `6` IR definitions under `MergeFunctions`),
     and proves three sharpness counterexamples (`CE1`: incomplete `Lazy` collection
     omitting `#[used]` or exported roots, `CE2`: `#[used(compiler)]` stripped by
     `--gc-sections` while `#[used(linker)]` survives, `CE3`: unsound folding of
     `poly_size::<u8>` with `poly_size::<u64>`).

Constructive `Init`-only development: every definition is explicitly marked
`noncomputable`, with zero `Prop`-level choice axioms, zero unsafe recursion
helpers, zero unchecked proof placeholders, and only `{propext, Quot.sound}`
kernel axioms.
-/

namespace MonoCollectorUsedMerge

-- ============================================================================
-- Section 1: Primitive Identifiers, Enumerations, and Constructive Equalities
-- ============================================================================

abbrev ItemId := Nat
abbrev TypeId := Nat
abbrev SymId := Nat

/-- Constructive boolean equality on `Nat` using structural recursion. -/
noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | a + 1, b + 1 => natEq a b

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_true_iff (a b : Nat) : natEq a b = true ↔ a = b := by
  constructor
  · intro h
    induction a generalizing b with
    | zero =>
      cases b with
      | zero => rfl
      | succ b' => cases h
    | succ a' ih =>
      cases b with
      | zero => cases h
      | succ b' =>
        have heq : a' = b' := ih b' h
        subst heq
        rfl
  · intro h
    subst h
    exact natEq_refl a

theorem natEq_false_of_ne {a b : Nat} (hne : a ≠ b) : natEq a b = false := by
  cases h : natEq a b with
  | false => rfl
  | true =>
    have heq : a = b := (natEq_true_iff a b).mp h
    exact False.elim (hne heq)

/-- Constructive boolean equality on `Bool`. -/
noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_refl (b : Bool) : boolEq b b = true := by
  cases b <;> rfl

theorem boolEq_true_iff (a b : Bool) : boolEq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b
    · rfl
    · cases h
    · cases h
    · rfl
  · intro h
    subst h
    exact boolEq_refl a

/-- Constructive boolean less-than-or-equal on `Nat`. -/
noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLe a b

theorem natLe_true_iff (a b : Nat) : natLe a b = true ↔ a ≤ b := by
  constructor
  · intro h
    induction a generalizing b with
    | zero => exact Nat.zero_le b
    | succ a' ih =>
      cases b with
      | zero => cases h
      | succ b' =>
        have hle : a' ≤ b' := ih b' h
        exact Nat.succ_le_succ hle
  · intro h
    induction a generalizing b with
    | zero => rfl
    | succ a' ih =>
      cases b with
      | zero => cases h
      | succ b' => exact ih b' (Nat.le_of_succ_le_succ h)

/-- Crate artifact type (`rustc_session::config::CrateType`, simplified to the
    binary vs. Rust library distinction governing `SymbolExportLevel`). -/
inductive CrateKind where
  | bin
  | rlib

noncomputable def CrateKind.eq : CrateKind → CrateKind → Bool
  | .bin, .bin => true
  | .rlib, .rlib => true
  | _, _ => false

theorem CrateKind.eq_true_iff (a b : CrateKind) : CrateKind.eq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

/-- Monomorphization collector strategy (`MonoItemCollectionStrategy`). -/
inductive CollectionStrategy where
  | lazy
  | eager

noncomputable def CollectionStrategy.eq : CollectionStrategy → CollectionStrategy → Bool
  | .lazy, .lazy => true
  | .eager, .eager => true
  | _, _ => false

theorem CollectionStrategy.eq_true_iff (a b : CollectionStrategy) :
    CollectionStrategy.eq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

/-- Optimization level (`rustc_session::config::OptLevel`). -/
inductive OptLevel where
  | o0
  | o1
  | o2
  | o3
  | os
  | oz

noncomputable def OptLevel.isNoOpt : OptLevel → Bool
  | .o0 => true
  | _ => false

noncomputable def OptLevel.runsMergeFunctions : OptLevel → Bool
  | .o2 => true
  | .o3 => true
  | .os => true
  | .oz => true
  | _ => false

/-- Inline attribute on a Rust function (`rustc_hir::attrs::InlineAttr`). -/
inductive InlinePolicy where
  | default
  | hint
  | never
  | always

noncomputable def InlinePolicy.eq : InlinePolicy → InlinePolicy → Bool
  | .default, .default => true
  | .hint, .hint => true
  | .never, .never => true
  | .always, .always => true
  | _, _ => false

/-- Source-level `#[used]` spelling (`rustc_hir::attrs::UsedBy`). -/
inductive UsedAttr where
  | none
  | usedDefault
  | usedCompiler
  | usedLinker

/-- Lowered codegen `#[used]` classification (`CodegenFnAttrFlags::USED_*`). -/
inductive UsedKind where
  | none
  | compilerUsed
  | linkerRetain

noncomputable def UsedKind.eq : UsedKind → UsedKind → Bool
  | .none, .none => true
  | .compilerUsed, .compilerUsed => true
  | .linkerRetain, .linkerRetain => true
  | _, _ => false

theorem UsedKind.eq_true_iff (a b : UsedKind) : UsedKind.eq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

/-- Target OS class governing `#[used]` default lowering in `codegen_attrs.rs`. -/
inductive TargetOS where
  | linuxElf
  | illumos
  | machO
  | coff

/-- Mirrors `rustc_codegen_ssa::codegen_attrs` (`AttributeKind::Used`):
    bare `#[used]` lowers to `USED_LINKER` on all targets except `Os::Illumos`,
    where it downgrades to `USED_COMPILER`. -/
noncomputable def lowerUsedAttr (os : TargetOS) : UsedAttr → UsedKind
  | .none => .none
  | .usedCompiler => .compilerUsed
  | .usedLinker => .linkerRetain
  | .usedDefault =>
    match os with
    | .illumos => .compilerUsed
    | _ => .linkerRetain

theorem bare_used_is_linker_retain_except_illumos (os : TargetOS)
    (h_not_illumos : os ≠ .illumos) :
    lowerUsedAttr os .usedDefault = .linkerRetain := by
  cases os with
  | linuxElf => rfl
  | illumos => exact False.elim (h_not_illumos rfl)
  | machO => rfl
  | coff => rfl

theorem bare_used_illumos_is_compiler_used :
    lowerUsedAttr .illumos .usedDefault = .compilerUsed := rfl

/-- Symbol export threshold (`rustc_codegen_ssa::back::symbol_export::SymbolExportLevel`). -/
inductive ExportLevel where
  | none
  | rustExport
  | cExport

noncomputable def ExportLevel.meetsThreshold (lvl thresh : ExportLevel) : Bool :=
  match thresh, lvl with
  | .cExport, .cExport => true
  | .rustExport, .cExport => true
  | .rustExport, .rustExport => true
  | _, _ => false

/-- LLVM GlobalValue linkage relevant to `partitioning.rs` and `MergeFunctions`. -/
inductive Linkage where
  | internal
  | external

noncomputable def Linkage.eq : Linkage → Linkage → Bool
  | .internal, .internal => true
  | .external, .external => true
  | _, _ => false

noncomputable def Linkage.isDiscardableIfUnused : Linkage → Bool
  | .internal => true
  | .external => false

/-- `-Zmerge-functions` mode (`rustc_target::spec::MergeFunctions`). -/
inductive MergeFunctionsMode where
  | disabled
  | trampolines
  | aliases

noncomputable def MergeFunctionsMode.eq : MergeFunctionsMode → MergeFunctionsMode → Bool
  | .disabled, .disabled => true
  | .trampolines, .trampolines => true
  | .aliases, .aliases => true
  | _, _ => false

/-- Collected monomorphization item (`rustc_middle::mono::MonoItem`). -/
inductive MonoItem where
  | fnInst (defId : ItemId) (typeArg : TypeId)
  | staticItem (defId : ItemId)
  | globalAsm (defId : ItemId)

noncomputable def MonoItem.eq : MonoItem → MonoItem → Bool
  | .fnInst d1 t1, .fnInst d2 t2 => natEq d1 d2 && natEq t1 t2
  | .staticItem d1, .staticItem d2 => natEq d1 d2
  | .globalAsm d1, .globalAsm d2 => natEq d1 d2
  | _, _ => false

theorem MonoItem.eq_refl (m : MonoItem) : MonoItem.eq m m = true := by
  cases m with
  | fnInst d t =>
    change (natEq d d && natEq t t) = true
    rw [natEq_refl d, natEq_refl t]
    rfl
  | staticItem d => exact natEq_refl d
  | globalAsm d => exact natEq_refl d

theorem MonoItem.eq_true_iff (a b : MonoItem) : MonoItem.eq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a with
    | fnInst d1 t1 =>
      cases b with
      | fnInst d2 t2 =>
        cases hd : natEq d1 d2 <;> cases ht : natEq t1 t2
        · simp [MonoItem.eq, hd, ht] at h
        · simp [MonoItem.eq, hd, ht] at h
        · simp [MonoItem.eq, hd, ht] at h
        · have ed : d1 = d2 := (natEq_true_iff d1 d2).mp hd
          have et : t1 = t2 := (natEq_true_iff t1 t2).mp ht
          subst ed; subst et; rfl
      | staticItem _ => cases h
      | globalAsm _ => cases h
    | staticItem d1 =>
      cases b with
      | fnInst _ _ => cases h
      | staticItem d2 =>
        have ed : d1 = d2 := (natEq_true_iff d1 d2).mp h
        subst ed; rfl
      | globalAsm _ => cases h
    | globalAsm d1 =>
      cases b with
      | fnInst _ _ => cases h
      | staticItem _ => cases h
      | globalAsm d2 =>
        have ed : d1 = d2 := (natEq_true_iff d1 d2).mp h
        subst ed; rfl
  · intro h
    subst h
    exact MonoItem.eq_refl a

theorem MonoItem.eq_false_of_ne {a b : MonoItem} (hne : a ≠ b) : MonoItem.eq a b = false := by
  cases h : MonoItem.eq a b with
  | false => rfl
  | true => exact False.elim (hne ((MonoItem.eq_true_iff a b).mp h))

-- ============================================================================
-- Section 2: List Membership Helpers (Constructive, Zero `omega`)
-- ============================================================================

noncomputable def listMemMono (x : MonoItem) : List MonoItem → Bool
  | [] => false
  | y :: ys => MonoItem.eq x y || listMemMono x ys

theorem listMemMono_true_iff (x : MonoItem) (xs : List MonoItem) :
    listMemMono x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    constructor
    · intro h
      cases heq : MonoItem.eq x y with
      | true =>
        have hx : x = y := (MonoItem.eq_true_iff x y).mp heq
        subst hx
        exact List.Mem.head ys
      | false =>
        have htail : listMemMono x ys = true := by
          simp [listMemMono, heq] at h
          exact h
        exact List.Mem.tail y (ih.mp htail)
    · intro h
      cases h with
      | head _ =>
        simp [listMemMono, MonoItem.eq_refl]
      | tail _ hmem =>
        have htail : listMemMono x ys = true := ih.mpr hmem
        simp [listMemMono, htail]

noncomputable def listDedupAppend (acc : List MonoItem) : List MonoItem → List MonoItem
  | [] => acc
  | x :: xs =>
    if listMemMono x acc then listDedupAppend acc xs
    else listDedupAppend (x :: acc) xs

theorem mem_listDedupAppend_left (acc xs : List MonoItem) (m : MonoItem)
    (h : m ∈ acc) : m ∈ listDedupAppend acc xs := by
  induction xs generalizing acc with
  | nil => exact h
  | cons y ys ih =>
    dsimp [listDedupAppend]
    cases hmem : listMemMono y acc with
    | true => exact ih acc h
    | false => exact ih (y :: acc) (List.Mem.tail y h)

theorem mem_listDedupAppend_right (acc xs : List MonoItem) (m : MonoItem)
    (h : m ∈ xs) : m ∈ listDedupAppend acc xs := by
  induction xs generalizing acc with
  | nil => cases h
  | cons y ys ih =>
    dsimp [listDedupAppend]
    cases h with
    | head _ =>
      cases hmem : listMemMono m acc with
      | true =>
        have hm : m ∈ acc := (listMemMono_true_iff m acc).mp hmem
        exact mem_listDedupAppend_left acc ys m hm
      | false =>
        exact mem_listDedupAppend_left (m :: acc) ys m (List.Mem.head acc)
    | tail _ htail =>
      cases hmem : listMemMono y acc with
      | true => exact ih acc htail
      | false => exact ih (y :: acc) htail

-- ============================================================================
-- Section 3: Root Discovery (`RootCollector`, `cross_crate_inlinable`, `Lazy` vs `Eager`)
-- ============================================================================

/-- Declaration attributes governing root discovery and cross-crate deferral. -/
structure ItemDecl where
  id : ItemId
  isGeneric : Bool
  isPublic : Bool
  isExternC : Bool
  isEntryFn : Bool
  isStatic : Bool
  isGlobalAsm : Bool
  isForceInline : Bool
  inlinePolicy : InlinePolicy
  smallInlinable : Bool
  usedKind : UsedKind
  isStdInternal : Bool
  hasDefaultTraitImpl : Bool
  isDropGlue : Bool
  mirInlinableEnabled : Bool

/-- Mirrors `rustc_mir_transform::cross_crate_inline::cross_crate_inlinable`:
    - `extern` / C-ABI indicators return `false`;
    - `#[inline(never)]` returns `false`;
    - `#[inline]` / `#[inline(always)]` return `true`;
    - Without explicit `#[inline]`, small functions (`smallInlinable = true`) are
      inferred cross-crate-inlinable when optimizations / MIR inlining run
      (`!opt.isNoOpt || mirInlinableEnabled`). -/
noncomputable def crossCrateInlinable (opt : OptLevel) (d : ItemDecl) : Bool :=
  if d.isExternC || d.isStatic || d.isGlobalAsm then false
  else match d.inlinePolicy with
    | .never => false
    | .hint => true
    | .always => true
    | .default =>
      if !opt.isNoOpt || d.mirInlinableEnabled then d.smallInlinable
      else false

/-- Export threshold by crate type (`symbol_export.rs:25-47`). -/
noncomputable def crateExportThreshold : CrateKind → ExportLevel
  | .bin => .cExport
  | .rlib => .rustExport

/-- Effective export level of a non-generic declaration (`symbol_export.rs`). -/
noncomputable def itemExportLevel (d : ItemDecl) : ExportLevel :=
  if d.isExternC then .cExport
  else if d.isPublic then .rustExport
  else .none

/-- Mirrors `symbol_export::reachable_non_generics_provider` filtered by
    `is_reachable_non_generic_provider_local` (`symbol_export.rs:49-162`).
    Notice line 96: `if tcx.cross_crate_inlinable(def_id) { None } else { Some(def_id) }`. -/
noncomputable def isReachableNonGeneric (ck : CrateKind) (opt : OptLevel) (d : ItemDecl) : Bool :=
  if d.isGeneric || d.isStatic || d.isGlobalAsm then false
  else if crossCrateInlinable opt d then false
  else ExportLevel.meetsThreshold (itemExportLevel d) (crateExportThreshold ck)

/-- Mirrors `partitioning::collect_and_partition_mono_items` (`partitioning.rs:1131-1136`):
    selects `Eager` iff `linkDeadCode = true`, otherwise `Lazy`. -/
noncomputable def selectCollectionStrategy (linkDeadCode : Bool) : CollectionStrategy :=
  if linkDeadCode then .eager else .lazy

/-- Mirrors `RootCollector::process_item` and `RootCollector::is_root`
    (`collector.rs:1504-1671`):
    1. `Static` and `GlobalAsm` items are unconditional roots in BOTH `Lazy` and `Eager`.
    2. Generic items (`isGeneric = true`) are NEVER roots in EITHER `Lazy` or `Eager`.
    3. Non-generic functions under `Lazy` require being `entry_fn` (when `bin`),
       `isReachableNonGeneric`, or `isStdInternal`.
    4. Non-generic functions under `Eager` include every non-generic non-force-inline fn. -/
noncomputable def isDeclRoot (ck : CrateKind) (opt : OptLevel) (strat : CollectionStrategy)
    (d : ItemDecl) : Bool :=
  if d.isGeneric then false
  else if d.isStatic || d.isGlobalAsm then true
  else
    match strat with
    | .eager => !d.isForceInline
    | .lazy =>
      (ck.eq .bin && d.isEntryFn)
      || isReachableNonGeneric ck opt d
      || d.isStdInternal

/-- Initial `MonoItem` corresponding to a non-generic root declaration. -/
noncomputable def rootMonoItemOfDecl (d : ItemDecl) : MonoItem :=
  if d.isStatic then .staticItem d.id
  else if d.isGlobalAsm then .globalAsm d.id
  else .fnInst d.id 0

theorem eager_never_roots_generic (ck : CrateKind) (opt : OptLevel) (d : ItemDecl)
    (h : isDeclRoot ck opt .eager d = true) : d.isGeneric = false := by
  cases hg : d.isGeneric with
  | false => rfl
  | true =>
    simp [isDeclRoot, hg] at h

theorem lazy_never_roots_generic (ck : CrateKind) (opt : OptLevel) (d : ItemDecl)
    (h : isDeclRoot ck opt .lazy d = true) : d.isGeneric = false := by
  cases hg : d.isGeneric with
  | false => rfl
  | true =>
    simp [isDeclRoot, hg] at h

theorem static_always_root (ck : CrateKind) (opt : OptLevel) (strat : CollectionStrategy)
    (d : ItemDecl) (hg : d.isGeneric = false) (hs : d.isStatic = true) :
    isDeclRoot ck opt strat d = true := by
  simp [isDeclRoot, hg, hs]

theorem lazy_root_implies_eager_root (ck : CrateKind) (opt : OptLevel) (d : ItemDecl)
    (hnotforce : d.isForceInline = false)
    (h : isDeclRoot ck opt .lazy d = true) :
    isDeclRoot ck opt .eager d = true := by
  cases hg : d.isGeneric with
  | true => simp [isDeclRoot, hg] at h
  | false =>
    cases hs : d.isStatic with
    | true => simp [isDeclRoot, hg, hs]
    | false =>
      cases ha : d.isGlobalAsm with
      | true => simp [isDeclRoot, hg, hs, ha]
      | false => simp [isDeclRoot, hg, hs, ha, hnotforce]

theorem rlib_lazy_defers_small_pub_inline (opt : OptLevel) (d : ItemDecl)
    (h_noopt : opt.isNoOpt = false)
    (h_ng : d.isGeneric = false)
    (h_ns : d.isStatic = false)
    (h_na : d.isGlobalAsm = false)
    (h_ne : d.isExternC = false)
    (h_ni : d.isStdInternal = false)
    (h_pol : d.inlinePolicy = .default)
    (h_small : d.smallInlinable = true) :
    crossCrateInlinable opt d = true ∧ isDeclRoot .rlib opt .lazy d = false := by
  have hcci : crossCrateInlinable opt d = true := by
    simp [crossCrateInlinable, h_ne, h_ns, h_na, h_pol, h_noopt, h_small]
  have hrng : isReachableNonGeneric .rlib opt d = false := by
    simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci]
  have hroot : isDeclRoot .rlib opt .lazy d = false := by
    simp [isDeclRoot, h_ng, h_ns, h_na, CrateKind.eq, hrng, h_ni]
  exact ⟨hcci, hroot⟩

theorem rlib_lazy_collects_inline_never_pub (opt : OptLevel) (d : ItemDecl)
    (h_ng : d.isGeneric = false)
    (h_ns : d.isStatic = false)
    (h_na : d.isGlobalAsm = false)
    (h_pub : d.isPublic = true)
    (h_pol : d.inlinePolicy = .never) :
    crossCrateInlinable opt d = false ∧ isDeclRoot .rlib opt .lazy d = true := by
  have hcci : crossCrateInlinable opt d = false := by
    cases hext : d.isExternC <;> simp [crossCrateInlinable, h_ns, h_na, h_pol, hext]
  have hexp : ExportLevel.meetsThreshold (itemExportLevel d) (crateExportThreshold .rlib) = true := by
    cases hext : d.isExternC <;>
      simp [itemExportLevel, crateExportThreshold, h_pub, ExportLevel.meetsThreshold, hext]
  have hrng : isReachableNonGeneric .rlib opt d = true := by
    simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci, hexp]
  have hroot : isDeclRoot .rlib opt .lazy d = true := by
    simp [isDeclRoot, h_ng, h_ns, h_na, hrng]
  exact ⟨hcci, hroot⟩

theorem bin_lazy_omits_rust_abi_pub (opt : OptLevel) (d : ItemDecl)
    (h_ng : d.isGeneric = false)
    (h_ns : d.isStatic = false)
    (h_na : d.isGlobalAsm = false)
    (h_ne : d.isExternC = false)
    (h_nentry : d.isEntryFn = false)
    (h_ni : d.isStdInternal = false) :
    isDeclRoot .bin opt .lazy d = false := by
  have hrng : isReachableNonGeneric .bin opt d = false := by
    cases hcci : crossCrateInlinable opt d
    · cases hpub : d.isPublic <;>
      simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci, itemExportLevel, crateExportThreshold,
        h_ne, hpub, ExportLevel.meetsThreshold]
    · simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci]
  simp [isDeclRoot, h_ng, h_ns, h_na, CrateKind.eq, h_nentry, hrng, h_ni]

-- ============================================================================
-- Section 4: Monomorphization Graph Closure & Link Completeness
-- ============================================================================

/-- A crate's monomorphization dependency graph and emitted MIR metadata. -/
structure MonoGraph where
  decls : List ItemDecl
  callees : MonoItem → List MonoItem
  mentionedConsts : MonoItem → List MonoItem

noncomputable def lookupDecl : List ItemDecl → ItemId → Option ItemDecl
  | [], _ => none
  | d :: ds, id => if natEq d.id id then some d else lookupDecl ds id

/-- Predicate defining the root set of `G` under strategy `strat`. -/
noncomputable def GraphRoot (G : MonoGraph) (ck : CrateKind) (opt : OptLevel)
    (strat : CollectionStrategy) (m : MonoItem) : Prop :=
  ∃ d ∈ G.decls,
    d.isForceInline = false ∧
    isDeclRoot ck opt strat d = true ∧
    m = rootMonoItemOfDecl d

/-- One-step directed edge in the monomorphization call/reference graph. -/
noncomputable def MonoEdge (G : MonoGraph) (src dst : MonoItem) : Prop :=
  dst ∈ G.callees src

/-- Inductive transitive reachability closure from `roots` along `G.callees`. -/
inductive MonoReachable (G : MonoGraph) (roots : MonoItem → Prop) : MonoItem → Prop where
  | root {m : MonoItem} : roots m → MonoReachable G roots m
  | step {src dst : MonoItem} :
      MonoReachable G roots src → MonoEdge G src dst → MonoReachable G roots dst

theorem monoReachable_monotone_roots (G : MonoGraph) (r1 r2 : MonoItem → Prop)
    (hsub : ∀ m, r1 m → r2 m) :
    ∀ m, MonoReachable G r1 m → MonoReachable G r2 m := by
  intro m hm
  induction hm with
  | root hr => exact MonoReachable.root (hsub _ hr)
  | step _ hedge ih => exact MonoReachable.step ih hedge

theorem lazy_reachability_subset_eager (G : MonoGraph) (ck : CrateKind) (opt : OptLevel) :
    ∀ m, MonoReachable G (GraphRoot G ck opt .lazy) m →
         MonoReachable G (GraphRoot G ck opt .eager) m := by
  apply monoReachable_monotone_roots
  intro m ⟨d, hmem, hnf, hlazy, hmk⟩
  exact ⟨d, hmem, hnf, lazy_root_implies_eager_root ck opt d hnf hlazy, hmk⟩

theorem monoReachable_trans_edge (G : MonoGraph) (r : MonoItem → Prop)
    {a b : MonoItem} (ha : MonoReachable G r a) (hpath : MonoReachable G (fun x => x = a) b) :
    MonoReachable G r b := by
  induction hpath with
  | root heq =>
    subst heq
    exact ha
  | step _ hedge ih =>
    exact MonoReachable.step ih hedge

/-- Constructive finite list of initial root `MonoItem`s in `G`. -/
noncomputable def collectRootList (ck : CrateKind) (opt : OptLevel) (strat : CollectionStrategy) :
    List ItemDecl → List MonoItem
  | [] => []
  | d :: ds =>
    if !d.isForceInline && isDeclRoot ck opt strat d then
      rootMonoItemOfDecl d :: collectRootList ck opt strat ds
    else
      collectRootList ck opt strat ds

theorem collectRootList_sound (ck : CrateKind) (opt : OptLevel) (strat : CollectionStrategy)
    (ds : List ItemDecl) (m : MonoItem)
    (h : m ∈ collectRootList ck opt strat ds) :
    ∃ d ∈ ds, d.isForceInline = false ∧ isDeclRoot ck opt strat d = true ∧
      m = rootMonoItemOfDecl d := by
  induction ds with
  | nil => cases h
  | cons d ds ih =>
    dsimp [collectRootList] at h
    cases hnf : d.isForceInline with
    | true =>
      rw [hnf] at h
      dsimp at h
      rcases ih h with ⟨d', hd', hnf', hr', hm'⟩
      exact ⟨d', List.Mem.tail d hd', hnf', hr', hm'⟩
    | false =>
      cases hr : isDeclRoot ck opt strat d with
      | false =>
        rw [hnf, hr] at h
        dsimp at h
        rcases ih h with ⟨d', hd', hnf', hr', hm'⟩
        exact ⟨d', List.Mem.tail d hd', hnf', hr', hm'⟩
      | true =>
        rw [hnf, hr] at h
        dsimp at h
        cases h with
        | head _ =>
          exact ⟨d, List.Mem.head ds, hnf, hr, rfl⟩
        | tail _ htail =>
          rcases ih htail with ⟨d', hd', hnf', hr', hm'⟩
          exact ⟨d', List.Mem.tail d hd', hnf', hr', hm'⟩

theorem collectRootList_complete (ck : CrateKind) (opt : OptLevel) (strat : CollectionStrategy)
    (ds : List ItemDecl) (d : ItemDecl)
    (hmem : d ∈ ds) (hnf : d.isForceInline = false) (hr : isDeclRoot ck opt strat d = true) :
    rootMonoItemOfDecl d ∈ collectRootList ck opt strat ds := by
  induction ds with
  | nil => cases hmem
  | cons d0 ds ih =>
    dsimp [collectRootList]
    cases hmem with
    | head _ =>
      rw [hnf, hr]
      dsimp
      exact List.Mem.head _
    | tail _ htail =>
      have hin := ih htail
      cases hnf0 : d0.isForceInline with
      | true =>
        dsimp
        exact hin
      | false =>
        cases hr0 : isDeclRoot ck opt strat d0 with
        | false =>
          dsimp
          exact hin
        | true =>
          dsimp
          exact List.Mem.tail _ hin

/-- Bounded BFS/worklist expansion of `collectWorklist`. -/
noncomputable def expandOneStep (G : MonoGraph) : List MonoItem → List MonoItem
  | [] => []
  | m :: ms => listDedupAppend (expandOneStep G ms) (G.callees m)

noncomputable def collectFuel (G : MonoGraph) : Nat → List MonoItem → List MonoItem
  | 0, current => current
  | fuel + 1, current =>
    collectFuel G fuel (listDedupAppend (expandOneStep G current) current)

theorem expandOneStep_mem_left (G : MonoGraph) (ms : List MonoItem) (m dst : MonoItem)
    (hm : m ∈ ms) (hd : dst ∈ G.callees m) : dst ∈ expandOneStep G ms := by
  induction ms with
  | nil => cases hm
  | cons x xs ih =>
    dsimp [expandOneStep]
    cases hm with
    | head _ =>
      exact mem_listDedupAppend_right (expandOneStep G xs) (G.callees dst |> fun _ => G.callees m) dst hd
    | tail _ htail =>
      exact mem_listDedupAppend_left (expandOneStep G xs) (G.callees x) dst (ih htail)

theorem expandOneStep_sound (G : MonoGraph) (ms : List MonoItem) (dst : MonoItem)
    (h : dst ∈ expandOneStep G ms) :
    ∃ src ∈ ms, MonoEdge G src dst := by
  induction ms with
  | nil => cases h
  | cons x xs ih =>
    dsimp [expandOneStep] at h
    -- Case split on whether dst came from acc or G.callees x via dedup
    have hsplit : ∀ acc ys, dst ∈ listDedupAppend acc ys → dst ∈ acc ∨ dst ∈ ys := by
      intro acc ys hin
      induction ys generalizing acc with
      | nil => exact Or.inl hin
      | cons y ys' ihy =>
        dsimp [listDedupAppend] at hin
        cases hmem : listMemMono y acc with
        | true =>
          rw [hmem] at hin
          rcases ihy acc hin with ha | hb
          · exact Or.inl ha
          · exact Or.inr (List.Mem.tail y hb)
        | false =>
          rw [hmem] at hin
          rcases ihy (y :: acc) hin with ha | hb
          · cases ha with
            | head _ => exact Or.inr (List.Mem.head ys')
            | tail _ hacc => exact Or.inl hacc
          · exact Or.inr (List.Mem.tail y hb)
    rcases hsplit (expandOneStep G xs) (G.callees x) h with hprev | hhere
    · rcases ih hprev with ⟨s, hs, hedge⟩
      exact ⟨s, List.Mem.tail x hs, hedge⟩
    · exact ⟨x, List.Mem.head xs, hhere⟩

theorem collectFuel_sound (G : MonoGraph) (roots : MonoItem → Prop) (fuel : Nat)
    (init : List MonoItem) (hinit : ∀ m ∈ init, MonoReachable G roots m) :
    ∀ m ∈ collectFuel G fuel init, MonoReachable G roots m := by
  induction fuel generalizing init with
  | zero => exact hinit
  | succ f ih =>
    intro m hm
    apply ih (listDedupAppend (expandOneStep G init) init)
    · intro x hx
      have hsplit : ∀ acc ys, x ∈ listDedupAppend acc ys → x ∈ acc ∨ x ∈ ys := by
        intro acc ys hin
        induction ys generalizing acc with
        | nil => exact Or.inl hin
        | cons y ys' ihy =>
          dsimp [listDedupAppend] at hin
          cases hmem : listMemMono y acc with
          | true =>
            rw [hmem] at hin
            rcases ihy acc hin with ha | hb
            · exact Or.inl ha
            · exact Or.inr (List.Mem.tail y hb)
          | false =>
            rw [hmem] at hin
            rcases ihy (y :: acc) hin with ha | hb
            · cases ha with
              | head _ => exact Or.inr (List.Mem.head ys')
              | tail _ hacc => exact Or.inl hacc
            · exact Or.inr (List.Mem.tail y hb)
      rcases hsplit (expandOneStep G init) init hx with hexp | hbase
      · rcases expandOneStep_sound G init x hexp with ⟨src, hsrc, hedge⟩
        exact MonoReachable.step (hinit src hsrc) hedge
      · exact hinit x hbase
    · exact hm

/-- Operational call-graph execution outcome over a linked symbol table `emitted`. -/
inductive ExecOutcome where
  | ok (visitedCount : Nat)
  | missingSymbol (sym : MonoItem)

/-- Fuel-bounded execution stepping through callee chains (`step :: rest`) and
    checking that every called `MonoItem` is present in `emitted`. -/
noncomputable def execCallChain (G : MonoGraph) (emitted : MonoItem → Bool) :
    MonoItem → List MonoItem → ExecOutcome
  | cur, [] => if emitted cur then .ok 1 else .missingSymbol cur
  | cur, nxt :: rest =>
    if !emitted cur then .missingSymbol cur
    else if !listMemMono nxt (G.callees cur) then .ok 1
    else
      match execCallChain G emitted nxt rest with
      | .ok n => .ok (n + 1)
      | .missingSymbol s => .missingSymbol s

/-- Every item in a valid path from a root `r` is in `MonoReachable G roots`. -/
theorem execCallChain_no_missing_if_closed (G : MonoGraph) (roots : MonoItem → Prop)
    (emitted : MonoItem → Bool)
    (hclosed : ∀ m, MonoReachable G roots m → emitted m = true)
    (cur : MonoItem) (hcur : MonoReachable G roots cur)
    (trace : List MonoItem) :
    ∃ n, execCallChain G emitted cur trace = .ok n := by
  induction trace generalizing cur with
  | nil =>
    have hemit : emitted cur = true := hclosed cur hcur
    exact ⟨1, by simp [execCallChain, hemit]⟩
  | cons nxt rest ih =>
    have hemit : emitted cur = true := hclosed cur hcur
    cases hmem : listMemMono nxt (G.callees cur) with
    | false =>
      exact ⟨1, by simp [execCallChain, hemit, hmem]⟩
    | true =>
      have hedge : MonoEdge G cur nxt := (listMemMono_true_iff nxt (G.callees cur)).mp hmem
      have hnxt : MonoReachable G roots nxt := MonoReachable.step hcur hedge
      rcases ih nxt hnxt with ⟨n, hn⟩
      exact ⟨n + 1, by simp [execCallChain, hemit, hmem, hn]⟩

/-- **Main Collector Theorem (`Lazy` Reachability Closure Completeness):**
    For any crate (`bin` or `rlib`), if codegen + linker emit every item in
    `MonoReachable G (GraphRoot G ck opt .lazy)`, then ANY finite execution trace
    starting from a valid runtime root (`entry_fn`, exported `C`/`Rust` symbol,
    std internal item, or `#[used]` static) succeeds with ZERO `missingSymbol` faults. -/
theorem lazy_collection_link_complete (G : MonoGraph) (ck : CrateKind) (opt : OptLevel)
    (emitted : MonoItem → Bool)
    (hclosed : ∀ m, MonoReachable G (GraphRoot G ck opt .lazy) m → emitted m = true)
    (d : ItemDecl) (hd : d ∈ G.decls) (hnf : d.isForceInline = false)
    (hroot : isDeclRoot ck opt .lazy d = true)
    (trace : List MonoItem) :
    ∃ n, execCallChain G emitted (rootMonoItemOfDecl d) trace = .ok n := by
  have hr : MonoReachable G (GraphRoot G ck opt .lazy) (rootMonoItemOfDecl d) :=
    MonoReachable.root ⟨d, hd, hnf, hroot, rfl⟩
  exact execCallChain_no_missing_if_closed G (GraphRoot G ck opt .lazy) emitted hclosed
    (rootMonoItemOfDecl d) hr trace

/-- Cross-crate `rlib` deferral soundness: if upstream `rlib` emits all
    `MonoReachable G_up (GraphRoot G_up .rlib opt .lazy)` symbols and preserves
    MIR for every `crossCrateInlinable` public function in `rmeta`, then a
    downstream `bin` calling either `pub_dead_exported` (linked from upstream) or
    `pub_dead_small` (monomorphized locally via `should_codegen_locally = true`)
    resolves every symbol without missing-symbol faults. -/
noncomputable def hasDeclId : List ItemDecl → ItemId → Bool
  | [], _ => false
  | d :: ds, targetId => natEq d.id targetId || hasDeclId ds targetId

theorem mem_implies_hasDeclId (ds : List ItemDecl) (d : ItemDecl) (h : d ∈ ds) :
    hasDeclId ds d.id = true := by
  induction ds with
  | nil => cases h
  | cons x xs ih =>
    dsimp [hasDeclId]
    cases h with
    | head _ => simp [natEq_refl]
    | tail _ htail =>
      have hxs := ih htail
      simp [hxs]

noncomputable def shouldCodegenLocally (G_up : MonoGraph) (opt : OptLevel) (d : ItemDecl) : Bool :=
  if !(hasDeclId G_up.decls d.id) then true
  else !isReachableNonGeneric .rlib opt d

theorem rlib_deferral_downstream_link_complete (G_up : MonoGraph) (opt : OptLevel)
    (d : ItemDecl) (hd : d ∈ G_up.decls)
    (h_ng : d.isGeneric = false) (h_ns : d.isStatic = false) (h_na : d.isGlobalAsm = false)
    (h_pub : d.isPublic = true) (_h_nf : d.isForceInline = false) :
    isDeclRoot .rlib opt .lazy d = true ∨ shouldCodegenLocally G_up opt d = true := by
  have hhas : hasDeclId G_up.decls d.id = true := mem_implies_hasDeclId G_up.decls d hd
  cases hcci : crossCrateInlinable opt d with
  | false =>
    have hexp : ExportLevel.meetsThreshold (itemExportLevel d) (crateExportThreshold .rlib) = true := by
      cases hext : d.isExternC <;>
        simp [itemExportLevel, crateExportThreshold, h_pub, ExportLevel.meetsThreshold, hext]
    have hrng : isReachableNonGeneric .rlib opt d = true := by
      simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci, hexp]
    exact Or.inl (by simp [isDeclRoot, h_ng, h_ns, h_na, hrng])
  | true =>
    have hrng : isReachableNonGeneric .rlib opt d = false := by
      simp [isReachableNonGeneric, h_ng, h_ns, h_na, hcci]
    exact Or.inr (by simp [shouldCodegenLocally, hhas, hrng])

-- ============================================================================
-- Section 5: Linkage, `#[used(compiler)]` vs. `#[used(linker)]`, and Linker GC
-- ============================================================================

/-- ELF section header retention flags (`TargetLoweringObjectFileImpl.cpp:768-775`). -/
structure ElfSectionFlags where
  shfAlloc : Bool
  shfGnuRetain : Bool

/-- LLVM IR module emission state for a static global. -/
structure StaticLlvmState where
  defId : ItemId
  linkage : Linkage
  inLlvmUsed : Bool
  inLlvmCompilerUsed : Bool
  referencedByLiveCode : Bool

/-- Assigns initial LLVM IR global state from `codegen_static_item` (`consts.rs:511-538`)
    and `partitioning.rs` (`internalize_symbols`). -/
noncomputable def lowerStaticToLlvm (ck : CrateKind) (strat : CollectionStrategy)
    (d : ItemDecl) (liveRef : Bool) : StaticLlvmState :=
  let link :=
    match strat, ck with
    | .eager, _ => Linkage.external
    | .lazy, .rlib => Linkage.external
    | .lazy, .bin => if d.isExternC then Linkage.external else Linkage.internal
  { defId := d.id
    linkage := link
    inLlvmUsed := UsedKind.eq d.usedKind .linkerRetain
    inLlvmCompilerUsed := UsedKind.eq d.usedKind .compilerUsed
    referencedByLiveCode := liveRef }

/-- LLVM `GlobalDCE` pass survival predicate (`GlobalDCE.cpp` + `LangRef`):
    keeps external/referenced globals plus anything in `@llvm.used` OR `@llvm.compiler.used`. -/
noncomputable def survivesLlvmGlobalDCE (s : StaticLlvmState) : Bool :=
  !s.linkage.isDiscardableIfUnused || s.referencedByLiveCode || s.inLlvmUsed || s.inLlvmCompilerUsed

/-- ELF object section emission (`TargetLoweringObjectFileELF::SelectSectionForGlobal` +
    `AsmPrinter::emitSpecialLLVMGlobal`): ONLY `@llvm.used` sets `SHF_GNU_RETAIN` (`AR`);
    `@llvm.compiler.used` emits plain `SHF_ALLOC` (`A`). -/
noncomputable def emitElfSectionFlags (s : StaticLlvmState) : ElfSectionFlags :=
  { shfAlloc := true
    shfGnuRetain := s.inLlvmUsed }

/-- Linker `--gc-sections` survival (`ld.bfd >= 2.36` / `lld`):
    requires either live relocation / dynamic export (`external` in `rlib`/`cdylib` or `liveRef`),
    OR `SHF_GNU_RETAIN` (`AR`), OR `--gc-sections` disabled (`gcEnabled = false`). -/
noncomputable def survivesLinkerGC (gcEnabled : Bool) (exportDynamic : Bool)
    (s : StaticLlvmState) : Bool :=
  if !survivesLlvmGlobalDCE s then false
  else if !gcEnabled then true
  else
    let flags := emitElfSectionFlags s
    flags.shfGnuRetain || s.referencedByLiveCode || exportDynamic

theorem used_linker_survives_llvm_and_linker_gc (ck : CrateKind) (strat : CollectionStrategy)
    (d : ItemDecl) (liveRef gcEnabled exportDyn : Bool)
    (h_used : d.usedKind = .linkerRetain) :
    let s := lowerStaticToLlvm ck strat d liveRef
    survivesLlvmGlobalDCE s = true ∧
    (emitElfSectionFlags s).shfGnuRetain = true ∧
    survivesLinkerGC gcEnabled exportDyn s = true := by
  have hin : (lowerStaticToLlvm ck strat d liveRef).inLlvmUsed = true := by
    simp [lowerStaticToLlvm, h_used, UsedKind.eq]
  have hdce : survivesLlvmGlobalDCE (lowerStaticToLlvm ck strat d liveRef) = true := by
    simp [survivesLlvmGlobalDCE, hin]
  have hret : (emitElfSectionFlags (lowerStaticToLlvm ck strat d liveRef)).shfGnuRetain = true := by
    simp [emitElfSectionFlags, hin]
  have hgc : survivesLinkerGC gcEnabled exportDyn (lowerStaticToLlvm ck strat d liveRef) = true := by
    cases gcEnabled <;> simp [survivesLinkerGC, hdce, hret]
  exact ⟨hdce, hret, hgc⟩

theorem used_compiler_survives_llvm_but_stripped_by_gc (ck : CrateKind)
    (strat : CollectionStrategy) (d : ItemDecl)
    (h_used : d.usedKind = .compilerUsed) :
    let s := lowerStaticToLlvm ck strat d false
    survivesLlvmGlobalDCE s = true ∧
    (emitElfSectionFlags s).shfGnuRetain = false ∧
    survivesLinkerGC true false s = false ∧
    survivesLinkerGC false false s = true := by
  have hinU : (lowerStaticToLlvm ck strat d false).inLlvmUsed = false := by
    simp [lowerStaticToLlvm, h_used, UsedKind.eq]
  have hinC : (lowerStaticToLlvm ck strat d false).inLlvmCompilerUsed = true := by
    simp [lowerStaticToLlvm, h_used, UsedKind.eq]
  have hdce : survivesLlvmGlobalDCE (lowerStaticToLlvm ck strat d false) = true := by
    simp [survivesLlvmGlobalDCE, hinC]
  have hret : (emitElfSectionFlags (lowerStaticToLlvm ck strat d false)).shfGnuRetain = false := by
    simp [emitElfSectionFlags, hinU]
  have hlive : (lowerStaticToLlvm ck strat d false).referencedByLiveCode = false := by
    simp [lowerStaticToLlvm]
  have hgc_on : survivesLinkerGC true false (lowerStaticToLlvm ck strat d false) = false := by
    simp [survivesLinkerGC, hdce, hret, hlive]
  have hgc_off : survivesLinkerGC false false (lowerStaticToLlvm ck strat d false) = true := by
    simp [survivesLinkerGC, hdce]
  exact ⟨hdce, hret, hgc_on, hgc_off⟩

theorem unannotated_dead_internal_static_dropped_by_global_dce
    (d : ItemDecl) (h_used : d.usedKind = .none) (h_ne : d.isExternC = false) :
    survivesLlvmGlobalDCE (lowerStaticToLlvm .bin .lazy d false) = false := by
  simp [lowerStaticToLlvm, h_used, h_ne, UsedKind.eq, survivesLlvmGlobalDCE,
    Linkage.isDiscardableIfUnused]

-- ============================================================================
-- Section 6: LLVM `MergeFunctions` IR Model & Observational Equivalence
-- ============================================================================

/-- Lowered scalar LLVM IR instructions modeled for monomorphic functions
    (capturing arithmetic, `size_of::<T>()` constants, and direct calls). -/
inductive IrExpr where
  | arg
  | constNat (v : Nat)
  | add (a b : IrExpr)
  | mul (a b : IrExpr)
  | call (callee : SymId) (argExpr : IrExpr)

noncomputable def IrExpr.eq : IrExpr → IrExpr → Bool
  | .arg, .arg => true
  | .constNat a, .constNat b => natEq a b
  | .add a1 b1, .add a2 b2 => IrExpr.eq a1 a2 && IrExpr.eq b1 b2
  | .mul a1 b1, .mul a2 b2 => IrExpr.eq a1 a2 && IrExpr.eq b1 b2
  | .call f1 e1, .call f2 e2 => natEq f1 f2 && IrExpr.eq e1 e2
  | _, _ => false

theorem IrExpr.eq_refl (e : IrExpr) : IrExpr.eq e e = true := by
  induction e with
  | arg => rfl
  | constNat v => exact natEq_refl v
  | add a b iha ihb =>
    change (IrExpr.eq a a && IrExpr.eq b b) = true
    rw [iha, ihb]
    rfl
  | mul a b iha ihb =>
    change (IrExpr.eq a a && IrExpr.eq b b) = true
    rw [iha, ihb]
    rfl
  | call f e ihe =>
    change (natEq f f && IrExpr.eq e e) = true
    rw [natEq_refl f, ihe]
    rfl

theorem IrExpr.eq_true_iff (e1 e2 : IrExpr) : IrExpr.eq e1 e2 = true ↔ e1 = e2 := by
  constructor
  · intro h
    induction e1 generalizing e2 with
    | arg =>
      cases e2 with
      | arg => rfl
      | constNat _ => cases h
      | add _ _ => cases h
      | mul _ _ => cases h
      | call _ _ => cases h
    | constNat v1 =>
      cases e2 with
      | constNat v2 =>
        have hv : v1 = v2 := (natEq_true_iff v1 v2).mp h
        subst hv; rfl
      | arg => cases h
      | add _ _ => cases h
      | mul _ _ => cases h
      | call _ _ => cases h
    | add a1 b1 iha ihb =>
      cases e2 with
      | add a2 b2 =>
        cases ha : IrExpr.eq a1 a2 <;> cases hb : IrExpr.eq b1 b2
        · simp [IrExpr.eq, ha, hb] at h
        · simp [IrExpr.eq, ha, hb] at h
        · simp [IrExpr.eq, ha, hb] at h
        · have ea := iha a2 ha
          have eb := ihb b2 hb
          subst ea; subst eb; rfl
      | arg => cases h
      | constNat _ => cases h
      | mul _ _ => cases h
      | call _ _ => cases h
    | mul a1 b1 iha ihb =>
      cases e2 with
      | mul a2 b2 =>
        cases ha : IrExpr.eq a1 a2 <;> cases hb : IrExpr.eq b1 b2
        · simp [IrExpr.eq, ha, hb] at h
        · simp [IrExpr.eq, ha, hb] at h
        · simp [IrExpr.eq, ha, hb] at h
        · have ea := iha a2 ha
          have eb := ihb b2 hb
          subst ea; subst eb; rfl
      | arg => cases h
      | constNat _ => cases h
      | add _ _ => cases h
      | call _ _ => cases h
    | call f1 x1 ihx =>
      cases e2 with
      | call f2 x2 =>
        cases hf : natEq f1 f2 <;> cases hx : IrExpr.eq x1 x2
        · simp [IrExpr.eq, hf, hx] at h
        · simp [IrExpr.eq, hf, hx] at h
        · simp [IrExpr.eq, hf, hx] at h
        · have ef : f1 = f2 := (natEq_true_iff f1 f2).mp hf
          have ex : x1 = x2 := ihx x2 hx
          subst ef; subst ex; rfl
      | arg => cases h
      | constNat _ => cases h
      | add _ _ => cases h
      | mul _ _ => cases h
  · intro h
    subst h
    exact IrExpr.eq_refl e1

/-- Lowered LLVM function entry inside a module (`define`, `alias`, or `thunk`). -/
inductive IrEntryKind where
  | defined (body : IrExpr)
  | aliasTo (target : SymId)
  | thunkTo (target : SymId)

/-- Function declaration + metadata visible to `MergeFunctions`. -/
structure IrFunc where
  sym : SymId
  linkage : Linkage
  unnamedAddr : Bool
  inUsedList : Bool
  preserveDebugInfo : Bool
  kind : IrEntryKind

/-- LLVM IR module represented as a list of `IrFunc` entries. -/
structure IrModule where
  funcs : List IrFunc

noncomputable def lookupIrFunc : List IrFunc → SymId → Option IrFunc
  | [], _ => none
  | f :: fs, s => if natEq f.sym s then some f else lookupIrFunc fs s

theorem lookupIrFunc_map (fn : IrFunc → IrFunc) (fs : List IrFunc) (s : SymId)
    (hpres : ∀ f, (fn f).sym = f.sym) :
    lookupIrFunc (fs.map fn) s = (lookupIrFunc fs s).map fn := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    dsimp [List.map, lookupIrFunc]
    rw [hpres f]
    cases natEq f.sym s
    · exact ih
    · rfl

/-- Rewrite direct calls `oldSym -> newSym` in an `IrExpr` (`replaceDirectCallers`). -/
noncomputable def rewriteCallExpr (oldSym newSym : SymId) : IrExpr → IrExpr
  | .arg => .arg
  | .constNat v => .constNat v
  | .add a b => .add (rewriteCallExpr oldSym newSym a) (rewriteCallExpr oldSym newSym b)
  | .mul a b => .mul (rewriteCallExpr oldSym newSym a) (rewriteCallExpr oldSym newSym b)
  | .call f e =>
    let f' := if natEq f oldSym then newSym else f
    .call f' (rewriteCallExpr oldSym newSym e)

noncomputable def rewriteFuncBody (oldSym newSym : SymId) (f : IrFunc) : IrFunc :=
  match f.kind with
  | .defined body => { f with kind := .defined (rewriteCallExpr oldSym newSym body) }
  | .aliasTo t => { f with kind := .aliasTo (if natEq t oldSym then newSym else t) }
  | .thunkTo t => { f with kind := .thunkTo (if natEq t oldSym then newSym else t) }

theorem rewriteFuncBody_sym (oldSym newSym : SymId) (f : IrFunc) :
    (rewriteFuncBody oldSym newSym f).sym = f.sym := by
  cases h : f.kind <;> simp [rewriteFuncBody, h]

/-- Fuel-indexed big-step evaluator for an `IrModule` (purely structural on `fuel`). -/
noncomputable def evalIrExpr (M : IrModule) : Nat → Nat → IrExpr → Option Nat
  | 0, _, _ => none
  | fuel + 1, argVal, expr =>
    match expr with
    | .arg => some argVal
    | .constNat v => some v
    | .add a b =>
      match evalIrExpr M fuel argVal a, evalIrExpr M fuel argVal b with
      | some va, some vb => some (va + vb)
      | _, _ => none
    | .mul a b =>
      match evalIrExpr M fuel argVal a, evalIrExpr M fuel argVal b with
      | some va, some vb => some (va * vb)
      | _, _ => none
    | .call callee argExpr =>
      match evalIrExpr M fuel argVal argExpr with
      | none => none
      | some v =>
        match lookupIrFunc M.funcs callee with
        | none => none
        | some f =>
          match f.kind with
          | .defined body => evalIrExpr M fuel v body
          | .aliasTo target => evalIrExpr M fuel v (.call target .arg)
          | .thunkTo target => evalIrExpr M fuel v (.call target .arg)

noncomputable def evalIrCall (M : IrModule) (fuel : Nat) (entry : SymId) (argVal : Nat) :
    Option Nat :=
  evalIrExpr M fuel argVal (.call entry .arg)

/-- Outcome of `MergeFunctions::writeThunkOrAliasIfNeeded` (`MergeFunctions.cpp:914-938`). -/
inductive MergeAction where
  | keepDistinct
  | eraseAndRewrite
  | emitAlias
  | emitThunk

noncomputable def MergeAction.eq : MergeAction → MergeAction → Bool
  | .keepDistinct, .keepDistinct => true
  | .eraseAndRewrite, .eraseAndRewrite => true
  | .emitAlias, .emitAlias => true
  | .emitThunk, .emitThunk => true
  | _, _ => false

/-- Exact `MergeFunctions::mergeTwoFunctions` / `writeThunkOrAliasIfNeeded` decision
    when merging duplicate `G` into canonical `F` (`MergeFunctions.cpp:839-938, 1174-1205`). -/
noncomputable def decideMergeAction (opt : OptLevel) (mode : MergeFunctionsMode)
    (F G : IrFunc) : MergeAction :=
  if !opt.runsMergeFunctions || mode.eq .disabled then .keepDistinct
  else if F.inUsedList || G.inUsedList then .keepDistinct
  else
    match F.kind, G.kind with
    | .defined bF, .defined bG =>
      if !IrExpr.eq bF bG then .keepDistinct
      else if G.linkage.isDiscardableIfUnused && G.unnamedAddr && !G.preserveDebugInfo then
        .eraseAndRewrite
      else if mode.eq .aliases && G.unnamedAddr && F.unnamedAddr then
        .emitAlias
      else
        .emitThunk
    | _, _ => .keepDistinct

/-- Removes symbol `gSym` from the module list (`G->eraseFromParent()`). -/
noncomputable def eraseIrFunc (gSym : SymId) : List IrFunc → List IrFunc
  | [] => []
  | f :: fs => if natEq f.sym gSym then eraseIrFunc gSym fs else f :: eraseIrFunc gSym fs

/-- Replaces `gSym` entry with `aliasTo fSym` or `thunkTo fSym`. -/
noncomputable def replaceIrFuncKind (gSym : SymId) (newKind : IrEntryKind) :
    List IrFunc → List IrFunc
  | [] => []
  | f :: fs =>
    if natEq f.sym gSym then { f with kind := newKind } :: replaceIrFuncKind gSym newKind fs
    else f :: replaceIrFuncKind gSym newKind fs

/-- Applies a single `MergeFunctions` step merging `G` into `F`. -/
noncomputable def applyMergeTwo (opt : OptLevel) (mode : MergeFunctionsMode)
    (M : IrModule) (F G : IrFunc) : IrModule :=
  if natEq F.sym G.sym then M
  else
    match decideMergeAction opt mode F G with
    | .keepDistinct => M
    | .eraseAndRewrite =>
      let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
      { funcs := eraseIrFunc G.sym rewritten }
    | .emitAlias =>
      let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
      { funcs := replaceIrFuncKind G.sym (.aliasTo F.sym) rewritten }
    | .emitThunk =>
      let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
      { funcs := replaceIrFuncKind G.sym (.thunkTo F.sym) rewritten }

/-- Counts `define` entries in `IrModule`. -/
noncomputable def countDefines : List IrFunc → Nat
  | [] => 0
  | f :: fs =>
    match f.kind with
    | .defined _ => 1 + countDefines fs
    | _ => countDefines fs

/-- Counts `alias` entries in `IrModule`. -/
noncomputable def countAliases : List IrFunc → Nat
  | [] => 0
  | f :: fs =>
    match f.kind with
    | .aliasTo _ => 1 + countAliases fs
    | _ => countAliases fs

/-- Counts `thunk` entries in `IrModule`. -/
noncomputable def countThunks : List IrFunc → Nat
  | [] => 0
  | f :: fs =>
    match f.kind with
    | .thunkTo _ => 1 + countThunks fs
    | _ => countThunks fs

-- ============================================================================
-- Section 7: Simulation Proofs for `MergeFunctions` Equivalence Preservation
-- ============================================================================

theorem lookupIrFunc_erase_ne (gSym s : SymId) (fs : List IrFunc) (hne : s ≠ gSym) :
    lookupIrFunc (eraseIrFunc gSym fs) s = lookupIrFunc fs s := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    dsimp [eraseIrFunc]
    cases hfg : natEq f.sym gSym with
    | true =>
      have efg : f.sym = gSym := (natEq_true_iff f.sym gSym).mp hfg
      have hnefs : f.sym ≠ s := by
        intro heq
        apply hne
        rw [← heq, efg]
      have hfs : natEq f.sym s = false := natEq_false_of_ne hnefs
      simp [lookupIrFunc, hfs]
      exact ih
    | false =>
      dsimp [lookupIrFunc]
      cases natEq f.sym s
      · exact ih
      · rfl

theorem lookupIrFunc_replace_ne (gSym s : SymId) (nk : IrEntryKind) (fs : List IrFunc)
    (hne : s ≠ gSym) :
    lookupIrFunc (replaceIrFuncKind gSym nk fs) s = lookupIrFunc fs s := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    dsimp [replaceIrFuncKind]
    cases hfg : natEq f.sym gSym with
    | true =>
      have efg : f.sym = gSym := (natEq_true_iff f.sym gSym).mp hfg
      have hnefs : f.sym ≠ s := by
        intro heq
        apply hne
        rw [← heq, efg]
      have hfs : natEq f.sym s = false := natEq_false_of_ne hnefs
      simp [lookupIrFunc, hfs]
      exact ih
    | false =>
      dsimp [lookupIrFunc]
      cases natEq f.sym s
      · exact ih
      · rfl

theorem lookupIrFunc_replace_eq (gSym : SymId) (nk : IrEntryKind) (fs : List IrFunc)
    (f : IrFunc) (hf : lookupIrFunc fs gSym = some f) :
    lookupIrFunc (replaceIrFuncKind gSym nk fs) gSym = some { f with kind := nk } := by
  induction fs with
  | nil => cases hf
  | cons f0 rest ih =>
    dsimp [lookupIrFunc] at hf
    cases hfg : natEq f0.sym gSym with
    | true =>
      rw [hfg] at hf
      cases hf
      simp [replaceIrFuncKind, hfg, lookupIrFunc]
    | false =>
      rw [hfg] at hf
      simp [replaceIrFuncKind, hfg, lookupIrFunc]
      exact ih hf

/-- Shared simulation theorem parameterized by any post-merge module `M'` whose
    symbol lookup redirects `F.sym` to rewritten `F` and preserves all symbols
    distinct from `G.sym` under `rewriteFuncBody G.sym F.sym`. Covers both
    `eraseIrFunc` and `replaceIrFuncKind (.aliasTo / .thunkTo)`. -/
theorem eval_rewrite_lookup_sound (M M' : IrModule) (F G : IrFunc) (b : IrExpr)
    (hg_in : lookupIrFunc M.funcs G.sym = some G)
    (hfb : F.kind = .defined b) (hgb : G.kind = .defined b)
    (hlkF' : lookupIrFunc M'.funcs F.sym = some (rewriteFuncBody G.sym F.sym F))
    (hlkNe' : ∀ callee, callee ≠ G.sym →
      lookupIrFunc M'.funcs callee =
        (lookupIrFunc M.funcs callee).map (rewriteFuncBody G.sym F.sym))
    (fuel argVal : Nat) (e : IrExpr) :
    evalIrExpr M' fuel argVal (rewriteCallExpr G.sym F.sym e) = evalIrExpr M fuel argVal e := by
  induction fuel generalizing argVal e with
  | zero => rfl
  | succ f ih =>
    cases e with
    | arg => rfl
    | constNat _ => rfl
    | add x y =>
      simp only [rewriteCallExpr, evalIrExpr, ih]
    | mul x y =>
      simp only [rewriteCallExpr, evalIrExpr, ih]
    | call callee argExpr =>
      simp only [rewriteCallExpr, evalIrExpr]
      rw [ih argVal argExpr]
      cases evalIrExpr M f argVal argExpr with
      | none => rfl
      | some v =>
        dsimp
        cases hcg : natEq callee G.sym with
        | true =>
          have ecg : callee = G.sym := (natEq_true_iff callee G.sym).mp hcg
          subst ecg
          dsimp
          rw [hlkF', hg_in]
          dsimp [rewriteFuncBody]
          rw [hfb, hgb]
          exact ih v b
        | false =>
          have hne_cg : callee ≠ G.sym := by
            intro h
            have ht : natEq callee G.sym = true := (natEq_true_iff callee G.sym).mpr h
            rw [ht] at hcg
            cases hcg
          dsimp
          rw [hlkNe' callee hne_cg]
          cases lookupIrFunc M.funcs callee with
          | none => rfl
          | some targetFn =>
            dsimp
            cases htk : targetFn.kind with
            | defined tbody =>
              dsimp [rewriteFuncBody]
              rw [htk]
              exact ih v tbody
            | aliasTo t =>
              dsimp [rewriteFuncBody]
              rw [htk]
              dsimp
              have harg : rewriteCallExpr G.sym F.sym (.call t .arg) =
                  .call (if natEq t G.sym then F.sym else t) .arg := rfl
              rw [← harg]
              exact ih v (.call t .arg)
            | thunkTo t =>
              dsimp [rewriteFuncBody]
              rw [htk]
              dsimp
              have harg : rewriteCallExpr G.sym F.sym (.call t .arg) =
                  .call (if natEq t G.sym then F.sym else t) .arg := rfl
              rw [← harg]
              exact ih v (.call t .arg)

/-- Canonical function simulation under `eraseAndRewrite` (`G->eraseFromParent()`). -/
theorem eval_rewrite_erase_sound (M : IrModule) (F G : IrFunc) (b : IrExpr)
    (hf_in : lookupIrFunc M.funcs F.sym = some F)
    (hg_in : lookupIrFunc M.funcs G.sym = some G)
    (hfb : F.kind = .defined b) (hgb : G.kind = .defined b)
    (h_ne : F.sym ≠ G.sym)
    (fuel argVal : Nat) (e : IrExpr) :
    let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
    let M' : IrModule := { funcs := eraseIrFunc G.sym rewritten }
    evalIrExpr M' fuel argVal (rewriteCallExpr G.sym F.sym e) = evalIrExpr M fuel argVal e := by
  intro rewritten M'
  apply eval_rewrite_lookup_sound M M' F G b hg_in hfb hgb
  · dsimp [M']
    rw [lookupIrFunc_erase_ne G.sym F.sym rewritten h_ne]
    rw [lookupIrFunc_map (rewriteFuncBody G.sym F.sym) M.funcs F.sym (rewriteFuncBody_sym G.sym F.sym)]
    rw [hf_in]
    rfl
  · intro callee hne_cg
    dsimp [M']
    rw [lookupIrFunc_erase_ne G.sym callee rewritten hne_cg]
    exact lookupIrFunc_map (rewriteFuncBody G.sym F.sym) M.funcs callee
      (rewriteFuncBody_sym G.sym F.sym)

/-- Simulation under `emitAlias` / `emitThunk` for rewritten direct callers. -/
theorem eval_rewrite_alias_or_thunk_direct (M : IrModule) (F G : IrFunc) (b : IrExpr)
    (nk : IrEntryKind) (_hnk : nk = .aliasTo F.sym ∨ nk = .thunkTo F.sym)
    (hf_in : lookupIrFunc M.funcs F.sym = some F)
    (hg_in : lookupIrFunc M.funcs G.sym = some G)
    (hfb : F.kind = .defined b) (hgb : G.kind = .defined b)
    (h_ne : F.sym ≠ G.sym)
    (fuel argVal : Nat) (e : IrExpr) :
    let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
    let M' : IrModule := { funcs := replaceIrFuncKind G.sym nk rewritten }
    evalIrExpr M' fuel argVal (rewriteCallExpr G.sym F.sym e) = evalIrExpr M fuel argVal e := by
  intro rewritten M'
  apply eval_rewrite_lookup_sound M M' F G b hg_in hfb hgb
  · dsimp [M']
    rw [lookupIrFunc_replace_ne G.sym F.sym nk rewritten h_ne]
    rw [lookupIrFunc_map (rewriteFuncBody G.sym F.sym) M.funcs F.sym (rewriteFuncBody_sym G.sym F.sym)]
    rw [hf_in]
    rfl
  · intro callee hne_cg
    dsimp [M']
    rw [lookupIrFunc_replace_ne G.sym callee nk rewritten hne_cg]
    exact lookupIrFunc_map (rewriteFuncBody G.sym F.sym) M.funcs callee
      (rewriteFuncBody_sym G.sym F.sym)

/-- External-caller preservation when invoking the retained `GlobalAlias` or tail-call
    `thunk` symbol `G.sym` directly (e.g. from a downstream crate linking against an
    `rlib` compiled with `-Clink-dead-code=yes` / `-Zmerge-functions={aliases,trampolines}`):
    evaluation at `fuel + 1` through `G`'s alias/thunk produces the exact value of
    evaluating original `G` at `fuel`! -/
theorem eval_external_alias_or_thunk_entry_sound (M : IrModule) (F G : IrFunc) (b : IrExpr)
    (nk : IrEntryKind) (hnk : nk = .aliasTo F.sym ∨ nk = .thunkTo F.sym)
    (hf_in : lookupIrFunc M.funcs F.sym = some F)
    (hg_in : lookupIrFunc M.funcs G.sym = some G)
    (hfb : F.kind = .defined b) (hgb : G.kind = .defined b)
    (h_ne : F.sym ≠ G.sym)
    (fuel argVal : Nat) :
    let rewritten := M.funcs.map (rewriteFuncBody G.sym F.sym)
    let M' : IrModule := { funcs := replaceIrFuncKind G.sym nk rewritten }
    evalIrCall M' (fuel + 1) G.sym argVal = evalIrCall M fuel G.sym argVal := by
  intro rewritten M'
  have hlkG_rw : lookupIrFunc rewritten G.sym = some (rewriteFuncBody G.sym F.sym G) := by
    dsimp [rewritten]
    rw [lookupIrFunc_map (rewriteFuncBody G.sym F.sym) M.funcs G.sym (rewriteFuncBody_sym G.sym F.sym)]
    rw [hg_in]
    rfl
  have hlkG' : lookupIrFunc M'.funcs G.sym = some { rewriteFuncBody G.sym F.sym G with kind := nk } :=
    lookupIrFunc_replace_eq G.sym nk rewritten (rewriteFuncBody G.sym F.sym G) hlkG_rw
  cases fuel with
  | zero =>
    rfl
  | succ f =>
    -- At fuel = f + 1, calling G in M' hits alias/thunk -> .call F.sym .arg at fuel f + 1;
    -- wait: evalIrExpr M' ((f + 1) + 1) checks .arg at fuel f + 1 (= some argVal if f+1 >= 1),
    -- so we need f = f' + 1 (or evaluate one step inside alias/thunk). Wait:
    -- Notice evalIrCall M' (f + 2) argVal = evalIrExpr M' (f + 1) argVal (.call F.sym .arg)
    -- ONLY when evalIrExpr M' (f + 1) argVal .arg = some argVal, which holds when f + 1 >= 1 (true!).
    have hstepF :
        evalIrExpr M' (f + 1) argVal (.call F.sym .arg) =
          evalIrExpr M (f + 1) argVal (.call G.sym .arg) := by
      have hrw : rewriteCallExpr G.sym F.sym (.call G.sym .arg) = .call F.sym .arg := by
        simp [rewriteCallExpr, natEq_refl]
      rw [← hrw]
      exact eval_rewrite_alias_or_thunk_direct M F G b nk hnk hf_in hg_in hfb hgb h_ne
        (f + 1) argVal (.call G.sym .arg)
    change evalIrExpr M' ((f + 1) + 1) argVal (.call G.sym .arg) =
      evalIrExpr M (f + 1) argVal (.call G.sym .arg)
    have harg_ok : evalIrExpr M' (f + 1) argVal .arg = some argVal := rfl
    rw [evalIrExpr, harg_ok]
    dsimp
    rw [hlkG']
    dsimp
    cases hnk with
    | inl hA =>
      rw [hA]
      exact hstepF
    | inr hT =>
      rw [hT]
      exact hstepF

/-- **Unified `MergeFunctions` Observational Equivalence Theorem:**
    For ANY non-disabled `applyMergeTwo` transformation on structurally equal functions
    `F` and `G` (`decideMergeAction` returning `.eraseAndRewrite`, `.emitAlias`, or
    `.emitThunk`), any entry expression `e` (rewritten via `rewriteCallExpr G.sym F.sym`,
    or any non-`G` entry symbol) evaluates to the **exact same `Option Nat`** in `M'`
    as in `M` for every argument `argVal` and every execution `fuel`. -/
theorem applyMergeTwo_preserves_observational_equivalence
    (opt : OptLevel) (mode : MergeFunctionsMode)
    (M : IrModule) (F G : IrFunc) (b : IrExpr)
    (hf_in : lookupIrFunc M.funcs F.sym = some F)
    (hg_in : lookupIrFunc M.funcs G.sym = some G)
    (hfb : F.kind = .defined b) (hgb : G.kind = .defined b)
    (h_ne : F.sym ≠ G.sym)
    (fuel argVal : Nat) (e : IrExpr) :
    evalIrExpr (applyMergeTwo opt mode M F G) fuel argVal (rewriteCallExpr G.sym F.sym e) =
      evalIrExpr M fuel argVal e ∨
    applyMergeTwo opt mode M F G = M := by
  have hne_bool : natEq F.sym G.sym = false := natEq_false_of_ne h_ne
  cases hact : decideMergeAction opt mode F G with
  | keepDistinct =>
    exact Or.inr (by simp [applyMergeTwo, hne_bool, hact])
  | eraseAndRewrite =>
    apply Or.inl
    simp [applyMergeTwo, hne_bool, hact]
    exact eval_rewrite_erase_sound M F G b hf_in hg_in hfb hgb h_ne fuel argVal e
  | emitAlias =>
    apply Or.inl
    simp [applyMergeTwo, hne_bool, hact]
    exact eval_rewrite_alias_or_thunk_direct M F G b (.aliasTo F.sym) (Or.inl rfl)
      hf_in hg_in hfb hgb h_ne fuel argVal e
  | emitThunk =>
    apply Or.inl
    simp [applyMergeTwo, hne_bool, hact]
    exact eval_rewrite_alias_or_thunk_direct M F G b (.thunkTo F.sym) (Or.inr rfl)
      hf_in hg_in hfb hgb h_ne fuel argVal e

-- ============================================================================
-- Section 8: Concrete Empirical Specimen Verification & Sharpness Counterexamples
-- ============================================================================

-- Concrete ItemIds matching our live rustc specimen (`mono.rs` / `poly.rs`)
abbrev idMain : ItemId := 1
abbrev idExported : ItemId := 2
abbrev idPubDeadSmall : ItemId := 3
abbrev idPubDeadExported : ItemId := 4
abbrev idDead : ItemId := 5
abbrev idGenDead : ItemId := 6
abbrev idUsedComp : ItemId := 7
abbrev idUsedLink : ItemId := 8
abbrev idPolyConst : ItemId := 9
abbrev idPolySize : ItemId := 10

abbrev tyUnit : TypeId := 0
abbrev tyU8 : TypeId := 1
abbrev tyU16 : TypeId := 2
abbrev tyU64 : TypeId := 3

noncomputable def declMain : ItemDecl :=
  { id := idMain, isGeneric := false, isPublic := false, isExternC := false
    isEntryFn := true, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := true, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declExported : ItemDecl :=
  { id := idExported, isGeneric := false, isPublic := true, isExternC := true
    isEntryFn := false, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := false, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declPubDeadSmall : ItemDecl :=
  { id := idPubDeadSmall, isGeneric := false, isPublic := true, isExternC := false
    isEntryFn := false, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := true, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declPubDeadExported : ItemDecl :=
  { id := idPubDeadExported, isGeneric := false, isPublic := true, isExternC := false
    isEntryFn := false, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .never, smallInlinable := true, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declDead : ItemDecl :=
  { id := idDead, isGeneric := false, isPublic := false, isExternC := false
    isEntryFn := false, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .never, smallInlinable := true, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declGenDead : ItemDecl :=
  { id := idGenDead, isGeneric := true, isPublic := false, isExternC := false
    isEntryFn := false, isStatic := false, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := true, usedKind := .none
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declUsedComp : ItemDecl :=
  { id := idUsedComp, isGeneric := false, isPublic := false, isExternC := false
    isEntryFn := false, isStatic := true, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := false, usedKind := .compilerUsed
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def declUsedLink : ItemDecl :=
  { id := idUsedLink, isGeneric := false, isPublic := false, isExternC := false
    isEntryFn := false, isStatic := true, isGlobalAsm := false, isForceInline := false
    inlinePolicy := .default, smallInlinable := false, usedKind := .linkerRetain
    isStdInternal := false, hasDefaultTraitImpl := false, isDropGlue := false
    mirInlinableEnabled := true }

noncomputable def specimenDecls : List ItemDecl :=
  [declMain, declExported, declPubDeadSmall, declPubDeadExported,
   declDead, declGenDead, declUsedComp, declUsedLink]

noncomputable def specimenCallees : MonoItem → List MonoItem
  | .fnInst 1 0 => [.fnInst idExported 0]
  | .fnInst 2 0 =>
    [.fnInst idPolyConst tyU8, .fnInst idPolyConst tyU16, .fnInst idPolyConst tyU64,
     .fnInst idPolySize tyU8, .fnInst idPolySize tyU16, .fnInst idPolySize tyU64]
  | _ => []

noncomputable def specimenGraph : MonoGraph :=
  { decls := specimenDecls
    callees := specimenCallees
    mentionedConsts := fun _ => [] }

theorem specimen_bin_lazy_roots_exact :
    collectRootList .bin .o2 .lazy specimenDecls =
      [.fnInst idMain 0, .fnInst idExported 0, .staticItem idUsedComp, .staticItem idUsedLink] := rfl

theorem specimen_bin_eager_roots_exact :
    collectRootList .bin .o2 .eager specimenDecls =
      [.fnInst idMain 0, .fnInst idExported 0, .fnInst idPubDeadSmall 0,
       .fnInst idPubDeadExported 0, .fnInst idDead 0,
       .staticItem idUsedComp, .staticItem idUsedLink] := rfl

theorem specimen_rlib_lazy_roots_exact :
    collectRootList .rlib .o2 .lazy specimenDecls =
      [.fnInst idExported 0, .fnInst idPubDeadExported 0,
       .staticItem idUsedComp, .staticItem idUsedLink] := rfl

theorem specimen_rlib_eager_roots_exact :
    collectRootList .rlib .o2 .eager specimenDecls =
      [.fnInst idMain 0, .fnInst idExported 0, .fnInst idPubDeadSmall 0,
       .fnInst idPubDeadExported 0, .fnInst idDead 0,
       .staticItem idUsedComp, .staticItem idUsedLink] := rfl

theorem specimen_gen_dead_excluded_even_eager :
    isDeclRoot .bin .o2 .eager declGenDead = false ∧
    isDeclRoot .rlib .o2 .eager declGenDead = false := ⟨rfl, rfl⟩

theorem specimen_used_statics_gc_contrast :
    let sComp := lowerStaticToLlvm .bin .lazy declUsedComp false
    let sLink := lowerStaticToLlvm .bin .lazy declUsedLink false
    survivesLlvmGlobalDCE sComp = true ∧
    survivesLlvmGlobalDCE sLink = true ∧
    (emitElfSectionFlags sComp).shfGnuRetain = false ∧
    (emitElfSectionFlags sLink).shfGnuRetain = true ∧
    survivesLinkerGC true false sComp = false ∧
    survivesLinkerGC true false sLink = true ∧
    survivesLinkerGC false false sComp = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Concrete MergeFunctions specimen (`poly_const` vs `poly_size` across `u8`, `u16`, `u64`)
abbrev symDrive : SymId := 100
abbrev symPolyConstU8 : SymId := 101
abbrev symPolyConstU16 : SymId := 102
abbrev symPolyConstU64 : SymId := 103
abbrev symPolySizeU8 : SymId := 104
abbrev symPolySizeU16 : SymId := 105
abbrev symPolySizeU64 : SymId := 106

noncomputable def bodyPolyConst : IrExpr :=
  .add (.mul .arg (.constNat 3)) (.constNat 1)

noncomputable def bodyPolySize (sz : Nat) : IrExpr :=
  .add .arg (.constNat sz)

noncomputable def bodyDrive : IrExpr :=
  .add
    (.add
      (.add (.call symPolyConstU8 .arg) (.call symPolyConstU16 .arg))
      (.call symPolyConstU64 .arg))
    (.add
      (.add (.call symPolySizeU8 .arg) (.call symPolySizeU16 .arg))
      (.call symPolySizeU64 .arg))

noncomputable def mkIrFn (sym : SymId) (link : Linkage) (body : IrExpr) : IrFunc :=
  { sym := sym, linkage := link, unnamedAddr := true, inUsedList := false
    preserveDebugInfo := false, kind := .defined body }

noncomputable def preMergeFuncs (link : Linkage) : List IrFunc :=
  [ mkIrFn symPolyConstU8 link bodyPolyConst
  , mkIrFn symPolyConstU16 link bodyPolyConst
  , mkIrFn symPolyConstU64 link bodyPolyConst
  , mkIrFn symPolySizeU8 link (bodyPolySize 1)
  , mkIrFn symPolySizeU16 link (bodyPolySize 2)
  , mkIrFn symPolySizeU64 link (bodyPolySize 8)
  , mkIrFn symDrive .external bodyDrive
  ]

noncomputable def preMergeModule (link : Linkage) : IrModule :=
  { funcs := preMergeFuncs link }

noncomputable def postMergeModule (opt : OptLevel) (mode : MergeFunctionsMode)
    (link : Linkage) : IrModule :=
  let f0 := mkIrFn symPolyConstU8 link bodyPolyConst
  let f1 := mkIrFn symPolyConstU16 link bodyPolyConst
  let f2 := mkIrFn symPolyConstU64 link bodyPolyConst
  let m1 := applyMergeTwo opt mode (preMergeModule link) f0 f1
  applyMergeTwo opt mode m1 f0 f2

theorem specimen_merge_lazy_o2_gives_4_poly_defines :
    countDefines (postMergeModule .o2 .aliases .internal).funcs = 5 ∧
    countAliases (postMergeModule .o2 .aliases .internal).funcs = 0 ∧
    countThunks (postMergeModule .o2 .aliases .internal).funcs = 0 :=
  -- 4 poly defines (`poly_const::<u8>`, `poly_size::<u8,u16,u64>`) + 1 `drive` = 5 total defines
  ⟨rfl, rfl, rfl⟩

theorem specimen_merge_disabled_gives_6_poly_defines :
    countDefines (postMergeModule .o2 .disabled .internal).funcs = 7 ∧
    countAliases (postMergeModule .o2 .disabled .internal).funcs = 0 ∧
    countThunks (postMergeModule .o2 .disabled .internal).funcs = 0 :=
  -- 6 poly defines + 1 `drive` = 7 total defines
  ⟨rfl, rfl, rfl⟩

theorem specimen_merge_eager_aliases_gives_4_defines_2_aliases :
    countDefines (postMergeModule .o2 .aliases .external).funcs = 5 ∧
    countAliases (postMergeModule .o2 .aliases .external).funcs = 2 ∧
    countThunks (postMergeModule .o2 .aliases .external).funcs = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem specimen_merge_eager_trampolines_gives_4_defines_2_thunks :
    countDefines (postMergeModule .o2 .trampolines .external).funcs = 5 ∧
    countAliases (postMergeModule .o2 .trampolines .external).funcs = 0 ∧
    countThunks (postMergeModule .o2 .trampolines .external).funcs = 2 :=
  -- Note: at LLVM IR source level, `define ... thunk` is 2 thunk functions (total 6 LLVM IR `define`s including thunks)!
  ⟨rfl, rfl, rfl⟩

theorem specimen_merge_o1_inactive_gives_6_poly_defines :
    countDefines (postMergeModule .o1 .aliases .internal).funcs = 7 ∧
    countAliases (postMergeModule .o1 .aliases .internal).funcs = 0 :=
  ⟨rfl, rfl⟩

theorem specimen_drive_eval_11_equals_146_pre_and_post_merge :
    evalIrCall (preMergeModule .internal) 10 symDrive 11 = some 146 ∧
    evalIrCall (postMergeModule .o2 .aliases .internal) 10 symDrive 11 = some 146 ∧
    evalIrCall (postMergeModule .o2 .aliases .external) 10 symDrive 11 = some 146 ∧
    evalIrCall (postMergeModule .o2 .trampolines .external) 10 symDrive 11 = some 146 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

-- ============================================================================
-- Sharpness Counterexamples (CE1, CE2, CE3)
-- ============================================================================

/-- **Sharpness CE1 (Incomplete Root Set):**
    If a collector drops `exported_fn` (or `#[used(linker)]`) from emitted roots,
    executing `main -> exported_fn` hits a deterministic `missingSymbol` fault. -/
theorem ce1_incomplete_collector_missing_symbol :
    let emittedWithoutExported : MonoItem → Bool := fun m => MonoItem.eq m (.fnInst idMain 0)
    execCallChain specimenGraph emittedWithoutExported (.fnInst idMain 0) [.fnInst idExported 0] =
      .missingSymbol (.fnInst idExported 0) := rfl

/-- **Sharpness CE2 (`#[used(compiler)]` Stripped by `--gc-sections`):**
    Even though `USED_COMP` survives LLVM `GlobalDCE` (`survivesLlvmGlobalDCE = true`),
    its ELF section lacks `SHF_GNU_RETAIN` (`shfGnuRetain = false`) and is discarded by
    linker `--gc-sections`, whereas `USED_LINK` (`SHF_GNU_RETAIN`) survives. -/
theorem ce2_used_compiler_vs_linker_gc_divergence :
    let sComp := lowerStaticToLlvm .bin .lazy declUsedComp false
    let sLink := lowerStaticToLlvm .bin .lazy declUsedLink false
    survivesLinkerGC true false sComp ≠ survivesLinkerGC true false sLink := by
  dsimp
  intro h
  cases h

/-- **Sharpness CE3 (Unsound Merging of Size-Dependent Monomorphs):**
    `poly_size::<u8>` and `poly_size::<u64>` are NOT structurally equal under
    `IrExpr.eq` (`decideMergeAction` returns `.keepDistinct`), and forcibly
    redirecting `poly_size::<u64>` to `poly_size::<u8>` changes `drive(11)` from
    `146` to `139` (`12 + 13 + 12` instead of `12 + 13 + 19`). -/
theorem ce3_poly_size_not_structurally_equal_and_unsound_merge :
    IrExpr.eq (bodyPolySize 1) (bodyPolySize 8) = false ∧
    let forcedM : IrModule :=
      { funcs := eraseIrFunc symPolySizeU64
          ((preMergeModule .internal).funcs.map (rewriteFuncBody symPolySizeU64 symPolySizeU8)) }
    evalIrCall forcedM 10 symDrive 11 = some 139 ∧
    evalIrCall (preMergeModule .internal) 10 symDrive 11 = some 146 := by
  refine ⟨rfl, ?_⟩
  dsimp
  exact ⟨rfl, rfl⟩

/-- **Used-list protection in `MergeFunctions` (`MergeFunctions.cpp:1174`):**
    A function whose symbol appears in `@llvm.used` or `@llvm.compiler.used`
    (`inUsedList = true`) is never merged or erased (`decideMergeAction = .keepDistinct`). -/
theorem used_list_blocks_merge_functions (opt : OptLevel) (mode : MergeFunctionsMode)
    (F G : IrFunc) (hused : F.inUsedList = true ∨ G.inUsedList = true) :
    decideMergeAction opt mode F G = .keepDistinct := by
  cases hopt : opt.runsMergeFunctions <;> cases hmode : mode.eq .disabled
  · simp [decideMergeAction, hopt, hmode]
  · simp [decideMergeAction, hopt, hmode]
  · cases hused with
    | inl hf => simp [decideMergeAction, hopt, hmode, hf]
    | inr hg => simp [decideMergeAction, hopt, hmode, hg]
  · simp [decideMergeAction, hopt, hmode]

end MonoCollectorUsedMerge
