/-!
# Linkage, Interposability, `extern_weak`, and `#[eii]` Soundness Model

Kernel-checked Lean v4.34.1 formalization accompanying the reference report on
`rustc` `#![feature(linkage)]` and `#![feature(extern_item_impls)]` (`#[eii]`):

1. LLVM `GlobalValue::LinkageTypes` well-formedness, `AsmPrinter::emitLinkage`
   emittability, `llvm::Verifier` blind spot on `define extern_weak`, and the
   exact `↔` characterization of link-override-safe inlining
   (`inlining_sound_under_link_override_iff_non_interposable`).
2. Associative, commutative strong-over-weak ELF/linker symbol resolution
   (`linker_resolve_commutes_and_extern_weak_binds_strong_when_present`) and
   Miri's `extern_static_pointer` short-circuit divergence.
3. `#[eii]` same-crate default-alias suppression and unique explicit override
   determinism (`eii_resolution_deterministic_iff_at_most_one_explicit`), plus
   Miri's `lookup_exported_symbol` filter gap.
4. Constructive sharpness counterexamples (`ce1`–`ce4`) directly witnessing the
   four empirically reproduced `rustc` / LLVM / `Miri` behaviors.

Hygiene invariants enforced under `-DwarningAsError=true -DElab.async=false
-Ddebug.skipKernelTC=false`:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
- All recursive definitions are marked `noncomputable def` to prevent Lean from
  generating `._unsafe_rec` partial compiler helpers.
-/

namespace LinkageInterpositionAndEiiSoundness

/-! ## Part 1: LLVM Linkage Well-Formedness and Interposability Inlining Guard -/

/-- LLVM `GlobalValue::LinkageTypes` (matching `llvm/include/llvm/IR/GlobalValue.h`). -/
inductive LlvmLinkage where
  | external
  | availableExternally
  | linkOnceAny
  | linkOnceOdr
  | weakAny
  | weakOdr
  | appending
  | internal
  | private_
  | externalWeak
  | common

/-- Models `llvm::GlobalValue::isInterposableLinkage` (`GlobalValue.h:431-451`). -/
def isInterposableLinkage : LlvmLinkage → Bool
  | .weakAny => true
  | .linkOnceAny => true
  | .common => true
  | .externalWeak => true
  | .availableExternally => false
  | .linkOnceOdr => false
  | .weakOdr => false
  | .external => false
  | .appending => false
  | .internal => false
  | .private_ => false

/-- Models `llvm::GlobalValue::isValidDeclarationLinkage` (`GlobalValue.h:543-545`). -/
def isValidDeclarationLinkage : LlvmLinkage → Bool
  | .external => true
  | .externalWeak => true
  | _ => false

/-- Models LLVM IR validity for function definitions (`LLParser.cpp:7084-7098`,
`Verifier.cpp:3034`): neither `extern_weak`, `common`, nor `appending` is valid
on a function definition. -/
def isValidFnDefinitionLinkage : LlvmLinkage → Bool
  | .external => true
  | .availableExternally => true
  | .linkOnceAny => true
  | .linkOnceOdr => true
  | .weakAny => true
  | .weakOdr => true
  | .internal => true
  | .private_ => true
  | .externalWeak => false
  | .common => false
  | .appending => false

/-- Models `llvm::AsmPrinter::emitLinkage` (`AsmPrinter.cpp:723-761`):
`ExternalWeakLinkage`, `AvailableExternallyLinkage`, and `AppendingLinkage`
hit `llvm_unreachable("Should never emit this")`. -/
def isEmittableByAsmPrinter : LlvmLinkage → Bool
  | .externalWeak => false
  | .availableExternally => false
  | .appending => false
  | _ => true

/-- Minimal LLVM function item in a codegen unit. -/
structure LlvmFn where
  sym : Nat
  linkage : LlvmLinkage
  hasBody : Bool
  bodyVal : Nat
  alwaysInline : Bool

/-- Full LLVM IR well-formedness predicate for a function item (`LLParser` + LangRef). -/
def wfLlvmFn (f : LlvmFn) : Prop :=
  if f.hasBody = true then
    isValidFnDefinitionLinkage f.linkage = true
  else
    isValidDeclarationLinkage f.linkage = true

/-- Models the incomplete check actually performed by `llvm::Verifier::visitGlobalValue`
(`Verifier.cpp:569`) and `Verifier::visitFunction` (`Verifier.cpp:3034`), which omits
`!hasExternalWeakLinkage()` on function definitions (`hasBody = true`). -/
def llvmVerifierAcceptsFn (f : LlvmFn) : Prop :=
  (f.hasBody = false → isValidDeclarationLinkage f.linkage = true) ∧
  (f.linkage ≠ .common) ∧
  (f.linkage ≠ .appending)

/-- Models `rustc_codegen_llvm/src/consts.rs:226` unconditionally calling
`LLVMSetLinkage(actual_global, ExternalWeakLinkage)` without checking whether
`actual_global` is already a definition in the current CGU. -/
def applyExternWeakUnchecked (f : LlvmFn) : LlvmFn :=
  { f with linkage := .externalWeak }

/-- Guarded lowering: apply `ExternalWeakLinkage` only to declarations (`hasBody = false`);
preserve an existing same-CGU definition's linkage. -/
def applyExternWeakGuarded (f : LlvmFn) : LlvmFn :=
  if f.hasBody then f else { f with linkage := .externalWeak }

theorem applyExternWeakGuarded_preserves_wf (f : LlvmFn) (hwf : wfLlvmFn f) :
    wfLlvmFn (applyExternWeakGuarded f) := by
  unfold applyExternWeakGuarded wfLlvmFn at *
  cases hb : f.hasBody with
  | true =>
    simp [hb] at hwf
    simpa [hb] using hwf
  | false =>
    simp [isValidDeclarationLinkage]

/-- Abstract callee definition within a compilation unit, parameterized by its
LLVM linkage and CGU-local return value. -/
structure CalleeDef where
  linkage : LlvmLinkage
  localVal : Nat

/-- Admissibility of a link-time override `ov : Option Nat` for a callee with
linkage `l` and local body value `localVal`:
- Interposable linkages (`weakAny`, `linkOnceAny`, `common`, `externalWeak`)
  permit any strong link-time override `some v` (possibly `v ≠ localVal`).
- ODR linkages (`weakOdr`, `linkOnceOdr`, `availableExternally`) permit only
  semantically equivalent replacements (`v = localVal`).
- Non-interposable non-ODR linkages (`external`, `internal`, `private_`,
  `appending`) admit no external replacement (`ov = none`). -/
def AdmissibleOverride (l : LlvmLinkage) (localVal : Nat) (ov : Option Nat) : Prop :=
  match l with
  | .weakAny | .linkOnceAny | .common | .externalWeak => True
  | .weakOdr | .linkOnceOdr | .availableExternally =>
      match ov with
      | none => True
      | some v => v = localVal
  | .external | .internal | .private_ | .appending => ov = none

/-- Dynamic result of calling `d` through its symbol under link-time override `ov`. -/
def evalDirectCall (d : CalleeDef) (ov : Option Nat) : Nat :=
  match ov with
  | some v => v
  | none => d.localVal

/-- Dynamic result of inlining `d`'s CGU-local body into a caller. -/
def evalInlinedCall (d : CalleeDef) : Nat :=
  d.localVal

/-- Exact characterization of link-override-safe call-site inlining:
inlining a callee `d` preserves `evalDirectCall` across every admissible
link-time override if and only if `d.linkage` is non-interposable. -/
theorem inlining_sound_under_link_override_iff_non_interposable (d : CalleeDef) :
    (∀ ov : Option Nat,
      AdmissibleOverride d.linkage d.localVal ov →
      evalInlinedCall d = evalDirectCall d ov)
    ↔ isInterposableLinkage d.linkage = false := by
  constructor
  · intro hsound
    cases hl : d.linkage with
    | weakAny =>
      have hadm : AdmissibleOverride d.linkage d.localVal (some (d.localVal + 1)) := by
        rw [hl]; trivial
      have h : d.localVal = d.localVal + 1 := hsound (some (d.localVal + 1)) hadm
      exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self d.localVal) h)
    | linkOnceAny =>
      have hadm : AdmissibleOverride d.linkage d.localVal (some (d.localVal + 1)) := by
        rw [hl]; trivial
      have h : d.localVal = d.localVal + 1 := hsound (some (d.localVal + 1)) hadm
      exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self d.localVal) h)
    | common =>
      have hadm : AdmissibleOverride d.linkage d.localVal (some (d.localVal + 1)) := by
        rw [hl]; trivial
      have h : d.localVal = d.localVal + 1 := hsound (some (d.localVal + 1)) hadm
      exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self d.localVal) h)
    | externalWeak =>
      have hadm : AdmissibleOverride d.linkage d.localVal (some (d.localVal + 1)) := by
        rw [hl]; trivial
      have h : d.localVal = d.localVal + 1 := hsound (some (d.localVal + 1)) hadm
      exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self d.localVal) h)
    | availableExternally => rfl
    | linkOnceOdr => rfl
    | weakOdr => rfl
    | external => rfl
    | appending => rfl
    | internal => rfl
    | private_ => rfl
  · intro hni ov hadm
    cases hl : d.linkage with
    | weakAny => rw [hl] at hni; cases hni
    | linkOnceAny => rw [hl] at hni; cases hni
    | common => rw [hl] at hni; cases hni
    | externalWeak => rw [hl] at hni; cases hni
    | availableExternally =>
      rw [hl] at hadm
      cases ov with
      | none => rfl
      | some v => exact hadm.symm
    | linkOnceOdr =>
      rw [hl] at hadm
      cases ov with
      | none => rfl
      | some v => exact hadm.symm
    | weakOdr =>
      rw [hl] at hadm
      cases ov with
      | none => rfl
      | some v => exact hadm.symm
    | external =>
      rw [hl] at hadm
      cases hadm
      rfl
    | appending =>
      rw [hl] at hadm
      cases hadm
      rfl
    | internal =>
      rw [hl] at hadm
      cases hadm
      rfl
    | private_ =>
      rw [hl] at hadm
      cases hadm
      rfl

/-- Models `llvm::getAttributeBasedInliningDecision` (`InlineCost.cpp:3209-3239`):
`AlwaysInline` short-circuits to `true` BEFORE `Callee->isInterposable()` is checked. -/
def llvmInlineDecision (d : CalleeDef) (alwaysInline : Bool) : Bool :=
  if alwaysInline then true else !isInterposableLinkage d.linkage

/-- Interposability-first inlining guard: never inlines interposable symbols
even when `alwaysInline` is present. -/
def guardedInlineDecision (d : CalleeDef) (alwaysInline : Bool) : Bool :=
  if isInterposableLinkage d.linkage then false else alwaysInline

theorem guardedInlineDecision_sound (d : CalleeDef) (alwaysInline : Bool)
    (h_inline : guardedInlineDecision d alwaysInline = true)
    (ov : Option Nat) (hadm : AdmissibleOverride d.linkage d.localVal ov) :
    evalInlinedCall d = evalDirectCall d ov := by
  have hni : isInterposableLinkage d.linkage = false := by
    unfold guardedInlineDecision at h_inline
    cases hi : isInterposableLinkage d.linkage with
    | true => simp [hi] at h_inline
    | false => rfl
  exact (inlining_sound_under_link_override_iff_non_interposable d).mpr hni ov hadm


/-! ## Part 2: Order-Independent Strong-Over-Weak Linker and `extern_weak` Resolution -/

/-- Symbol definition strength in an object file / crate. -/
inductive SymStrength where
  | strong
  | weak

/-- One exported symbol definition in a compilation unit. -/
structure SymDef where
  sym : Nat
  strength : SymStrength
  val : Nat

/-- Outcome of merging all definitions of a single symbol across object files.
Models strong-over-weak dominance, duplicate-strong conflict, and ambiguous
multiple-weak definitions (matching both ELF strong-over-weak resolution and
Miri's `lookup_exported_symbol` duplicate-weak rejection in `foreign_items.rs:168-198`). -/
inductive LinkOutcome where
  | missing
  | resolved (st : SymStrength) (v : Nat)
  | conflictStrong
  | ambiguousWeak

/-- Commutative, associative monoid composition of two link outcomes for one symbol. -/
def mergeOutcome : LinkOutcome → LinkOutcome → LinkOutcome
  | .missing, y => y
  | x, .missing => x
  | .conflictStrong, _ => .conflictStrong
  | _, .conflictStrong => .conflictStrong
  | .resolved .strong _, .resolved .strong _ => .conflictStrong
  | .resolved .strong v, .resolved .weak _ => .resolved .strong v
  | .resolved .strong v, .ambiguousWeak => .resolved .strong v
  | .resolved .weak _, .resolved .strong v => .resolved .strong v
  | .ambiguousWeak, .resolved .strong v => .resolved .strong v
  | .resolved .weak _, .resolved .weak _ => .ambiguousWeak
  | .resolved .weak _, .ambiguousWeak => .ambiguousWeak
  | .ambiguousWeak, .resolved .weak _ => .ambiguousWeak
  | .ambiguousWeak, .ambiguousWeak => .ambiguousWeak

theorem mergeOutcome_missing_left (x : LinkOutcome) :
    mergeOutcome .missing x = x := by
  cases x <;> rfl

theorem mergeOutcome_missing_right (x : LinkOutcome) :
    mergeOutcome x .missing = x := by
  cases x <;> rfl

theorem mergeOutcome_comm (x y : LinkOutcome) :
    mergeOutcome x y = mergeOutcome y x := by
  cases x with
  | missing => cases y <;> rfl
  | conflictStrong => cases y <;> rfl
  | ambiguousWeak =>
    cases y with
    | missing => rfl
    | conflictStrong => rfl
    | ambiguousWeak => rfl
    | resolved sy _ => cases sy <;> rfl
  | resolved sx vx =>
    cases sx <;> cases y with
    | missing => rfl
    | conflictStrong => rfl
    | ambiguousWeak => rfl
    | resolved sy vy => cases sy <;> rfl

theorem mergeOutcome_assoc (x y z : LinkOutcome) :
    mergeOutcome (mergeOutcome x y) z = mergeOutcome x (mergeOutcome y z) := by
  cases x with
  | missing => simp [mergeOutcome_missing_left]
  | conflictStrong =>
    cases y with
    | missing => simp [mergeOutcome]
    | conflictStrong => cases z <;> rfl
    | ambiguousWeak =>
      cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz _ => cases sz <;> rfl
    | resolved sy _ =>
      cases sy <;> cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz _ => cases sz <;> rfl
  | ambiguousWeak =>
    cases y with
    | missing => simp [mergeOutcome_missing_left, mergeOutcome_missing_right]
    | conflictStrong => cases z <;> rfl
    | ambiguousWeak =>
      cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz _ => cases sz <;> rfl
    | resolved sy vy =>
      cases sy <;> cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz vz => cases sz <;> rfl
  | resolved sx vx =>
    cases sx <;> cases y with
    | missing => simp [mergeOutcome_missing_left, mergeOutcome_missing_right]
    | conflictStrong => cases z <;> rfl
    | ambiguousWeak =>
      cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz vz => cases sz <;> rfl
    | resolved sy vy =>
      cases sy <;> cases z with
      | missing => rfl
      | conflictStrong => rfl
      | ambiguousWeak => rfl
      | resolved sz vz => cases sz <;> rfl

/-- Single-definition contribution for target symbol `s`. -/
def symContrib (s : Nat) (d : SymDef) : LinkOutcome :=
  if d.sym = s then .resolved d.strength d.val else .missing

/-- Fold all symbol definitions in a list of object contributions for symbol `s`.
Marked `noncomputable` so Lean emits zero `._unsafe_rec` helpers. -/
noncomputable def resolveSym (s : Nat) : List SymDef → LinkOutcome
  | [] => .missing
  | d :: ds => mergeOutcome (symContrib s d) (resolveSym s ds)

theorem resolveSym_append (s : Nat) (xs ys : List SymDef) :
    resolveSym s (xs ++ ys) = mergeOutcome (resolveSym s xs) (resolveSym s ys) := by
  induction xs with
  | nil =>
    simp [resolveSym, mergeOutcome_missing_left]
  | cons d ds ih =>
    simp [resolveSym, ih, mergeOutcome_assoc]

theorem resolveSym_append_comm (s : Nat) (xs ys : List SymDef) :
    resolveSym s (xs ++ ys) = resolveSym s (ys ++ xs) := by
  rw [resolveSym_append, resolveSym_append, mergeOutcome_comm]

/-- A list of symbol definitions contains no strong definition for symbol `s`. -/
def AllWeakOrOther (s : Nat) (ds : List SymDef) : Prop :=
  ∀ d, d ∈ ds → d.sym = s → d.strength = .weak

theorem resolveSym_allWeak_form (s : Nat) (ws : List SymDef)
    (hw : AllWeakOrOther s ws) :
    resolveSym s ws = .missing ∨
    (∃ v, resolveSym s ws = .resolved .weak v) ∨
    resolveSym s ws = .ambiguousWeak := by
  induction ws with
  | nil =>
    left; rfl
  | cons d ds ih =>
    have hrest := ih (fun x hx => hw x (List.mem_cons_of_mem d hx))
    simp only [resolveSym]
    unfold symContrib
    by_cases hsym : d.sym = s
    · have hst : d.strength = .weak := hw d List.mem_cons_self hsym
      simp only [hsym, ite_true, hst]
      rcases hrest with hm | ⟨v, hw1⟩ | hamb
      · rw [hm]; right; left; exact ⟨d.val, rfl⟩
      · rw [hw1]; right; right; rfl
      · rw [hamb]; right; right; rfl
    · simp only [hsym, ite_false, mergeOutcome_missing_left]
      exact hrest

/-- Observable result of loading an `#[linkage = "extern_weak"]` reference. -/
inductive WeakRefResult where
  | null
  | bound (v : Nat)
  | linkError

/-- Native ELF evaluation of an `extern_weak` reference to symbol `s`, paired with
its per-symbol internal indirection slot (`_rust_extern_with_linkage_<crate>_<s>`). -/
noncomputable def elfExternWeakEval (s : Nat) (ds : List SymDef) : WeakRefResult :=
  match resolveSym s ds with
  | .missing => .null
  | .resolved _ v => .bound v
  | .conflictStrong => .linkError
  | .ambiguousWeak => .linkError

/-- Distinct per-symbol internal global slot address emitted by
`rustc_codegen_llvm/src/consts.rs:256-268` (`_rust_extern_with_linkage_<crate>_<s>`). -/
def elfExternWeakSlot (s : Nat) : Nat :=
  1000 + s

theorem elfExternWeakSlot_injective (s₁ s₂ : Nat)
    (h : elfExternWeakSlot s₁ = elfExternWeakSlot s₂) : s₁ = s₂ := by
  unfold elfExternWeakSlot at h
  exact Nat.add_left_cancel h

/-- **Main Theorem 2**: Strong-over-weak linker resolution commutes across any
concatenation order of object files, and whenever a unique strong definition of
`s` is present (with arbitrary weak definitions before or after it), resolution
binds the strong value `v` and an `extern_weak` reference evaluates to `.bound v`. -/
theorem linker_resolve_commutes_and_extern_weak_binds_strong_when_present :
    (∀ s xs ys, resolveSym s (xs ++ ys) = resolveSym s (ys ++ xs)) ∧
    (∀ s v xs ws,
      resolveSym s xs = .resolved .strong v →
      AllWeakOrOther s ws →
      resolveSym s (ws ++ xs) = .resolved .strong v ∧
      resolveSym s (xs ++ ws) = .resolved .strong v ∧
      elfExternWeakEval s (ws ++ xs) = .bound v) := by
  refine ⟨resolveSym_append_comm, ?_⟩
  intro s v xs ws hxs hws
  have hwf := resolveSym_allWeak_form s ws hws
  have hmerge : mergeOutcome (resolveSym s ws) (.resolved .strong v) = .resolved .strong v := by
    rcases hwf with hm | ⟨w, hw1⟩ | hamb
    · rw [hm]; rfl
    · rw [hw1]; rfl
    · rw [hamb]; rfl
  have h_l : resolveSym s (ws ++ xs) = .resolved .strong v := by
    rw [resolveSym_append, hxs, hmerge]
  have h_r : resolveSym s (xs ++ ws) = .resolved .strong v := by
    rw [resolveSym_append_comm, h_l]
  refine ⟨h_l, h_r, ?_⟩
  unfold elfExternWeakEval
  rw [h_l]

/-- Built-in lookup in Miri's `extern_statics_imports` table (`shims/extern_static.rs:52-99`). -/
noncomputable def lookupBuiltin (s : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest => if k = s then some v else lookupBuiltin s rest

/-- Fixed shared null slot address modeling Miri's single global
`extern_static_weak_import_default` allocation (`machine.rs:1502-1519`,
`shims/extern_static.rs:102-105`). -/
def miriSharedNullSlot : Nat := 0

/-- Models Miri's `extern_static_pointer` (`src/tools/miri/src/machine.rs:1463-1524`):
checks `extern_statics_imports` (`builtins`), then immediately short-circuits on
`import_linkage == Some(Linkage::ExternalWeak)` to `(miriSharedNullSlot, .null)`
BEFORE ever consulting exported Rust crate symbols (`crateExports`). -/
noncomputable def miriExternWeakLookup (builtins : List (Nat × Nat))
    (_crateExports : List SymDef) (s : Nat) : Nat × WeakRefResult :=
  match lookupBuiltin s builtins with
  | some v => (2000 + s, .bound v)
  | none => (miriSharedNullSlot, .null)


/-! ## Part 3: `#[eii]` Default-Alias Suppression and Unique Explicit Override Soundness -/

/-- One `#[eii]` implementation entry recorded in a crate's
`externally_implementable_items` table (`codegen_attrs.rs:224-265`, `eii.rs:44-162`). -/
structure EiiImplDecl where
  eiiSym : Nat
  isDefault : Bool
  val : Nat
  /-- Whether the implementing Rust item carries an explicit `symbol_name`
  (`#[no_mangle]` / `#[export_name]`) or `RUSTC_STD_INTERNAL_SYMBOL`.
  Standard `#[eii]` implementations have `hasExplicitSymName = false`. -/
  hasExplicitSymName : Bool := false

/-- A single crate containing zero or more EII implementations. -/
structure CrateUnit where
  crateId : Nat
  impls : List EiiImplDecl

/-- Whether a crate contains any non-default (explicit) implementation for `s`. -/
noncomputable def hasExplicitFor (s : Nat) : List EiiImplDecl → Bool
  | [] => false
  | imp :: rest =>
      if imp.eiiSym = s ∧ imp.isDefault = false then true else hasExplicitFor s rest

/-- Models `compiler/rustc_codegen_ssa/src/codegen_attrs.rs:246-265`:
if `imp.isDefault = true` and the same crate defines an explicit implementation
for `imp.eiiSym`, suppress emitting the weak default alias; otherwise emit
`Linkage::WeakAny` for default and `Linkage::External` for explicit. -/
noncomputable def lowerCrateEiiList (allInCrate : List EiiImplDecl) :
    List EiiImplDecl → List SymDef
  | [] => []
  | imp :: rest =>
      let tail := lowerCrateEiiList allInCrate rest
      if imp.isDefault = true ∧ hasExplicitFor imp.eiiSym allInCrate = true then
        tail
      else
        { sym := imp.eiiSym
          strength := if imp.isDefault then .weak else .strong
          val := imp.val } :: tail

noncomputable def lowerCrateEii (c : CrateUnit) : List SymDef :=
  lowerCrateEiiList c.impls c.impls

noncomputable def lowerAllCrates : List CrateUnit → List SymDef
  | [] => []
  | c :: cs => lowerCrateEii c ++ lowerAllCrates cs

/-- Count explicit implementations for `s` in a list of EII declarations. -/
noncomputable def countExplicitList (s : Nat) : List EiiImplDecl → Nat
  | [] => 0
  | imp :: rest =>
      (if imp.eiiSym = s ∧ imp.isDefault = false then 1 else 0) + countExplicitList s rest

/-- Count default implementations for `s` in a list of EII declarations. -/
noncomputable def countDefaultList (s : Nat) : List EiiImplDecl → Nat
  | [] => 0
  | imp :: rest =>
      (if imp.eiiSym = s ∧ imp.isDefault = true then 1 else 0) + countDefaultList s rest

noncomputable def countExplicit (s : Nat) : List CrateUnit → Nat
  | [] => 0
  | c :: cs => countExplicitList s c.impls + countExplicit s cs

noncomputable def countDefault (s : Nat) : List CrateUnit → Nat
  | [] => 0
  | c :: cs => countDefaultList s c.impls + countDefault s cs

/-- Count strong definitions of `s` in a lowered symbol list. -/
noncomputable def countStrongDefs (s : Nat) : List SymDef → Nat
  | [] => 0
  | d :: ds =>
      (match d.strength with
       | .strong => if d.sym = s then 1 else 0
       | .weak => 0) + countStrongDefs s ds

/-- Count weak definitions of `s` in a lowered symbol list. -/
noncomputable def countWeakDefs (s : Nat) : List SymDef → Nat
  | [] => 0
  | d :: ds =>
      (match d.strength with
       | .weak => if d.sym = s then 1 else 0
       | .strong => 0) + countWeakDefs s ds

theorem countStrongDefs_append (s : Nat) (xs ys : List SymDef) :
    countStrongDefs s (xs ++ ys) = countStrongDefs s xs + countStrongDefs s ys := by
  induction xs with
  | nil => simp [countStrongDefs]
  | cons d ds ih =>
    simp [countStrongDefs, ih, Nat.add_assoc]

theorem countWeakDefs_append (s : Nat) (xs ys : List SymDef) :
    countWeakDefs s (xs ++ ys) = countWeakDefs s xs + countWeakDefs s ys := by
  induction xs with
  | nil => simp [countWeakDefs]
  | cons d ds ih =>
    simp [countWeakDefs, ih, Nat.add_assoc]

/-- Exact characterization of `resolveSym` by strong and weak symbol counts. -/
theorem resolveSym_spec_by_counts (s : Nat) (ds : List SymDef) :
    (countStrongDefs s ds = 0 ∧ countWeakDefs s ds = 0 → resolveSym s ds = .missing) ∧
    (countStrongDefs s ds = 0 ∧ countWeakDefs s ds = 1 →
      ∃ v, resolveSym s ds = .resolved .weak v) ∧
    (countStrongDefs s ds = 0 ∧ 2 ≤ countWeakDefs s ds →
      resolveSym s ds = .ambiguousWeak) ∧
    (countStrongDefs s ds = 1 → ∃ v, resolveSym s ds = .resolved .strong v) ∧
    (2 ≤ countStrongDefs s ds → resolveSym s ds = .conflictStrong) := by
  induction ds with
  | nil =>
    refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro ⟨_, h⟩; simp [countWeakDefs] at h
    · intro ⟨_, h⟩; simp [countWeakDefs] at h
    · intro h; simp [countStrongDefs] at h
    · intro h; simp [countStrongDefs] at h
  | cons d ds ih =>
    rcases ih with ⟨ih00, ih01, ih02, ih1, ih2⟩
    by_cases hsym : d.sym = s
    · cases hst : d.strength with
      | strong =>
        have hcS : countStrongDefs s (d :: ds) = 1 + countStrongDefs s ds := by
          simp [countStrongDefs, hsym, hst]
        have hres : resolveSym s (d :: ds) =
            mergeOutcome (.resolved .strong d.val) (resolveSym s ds) := by
          simp [resolveSym, symContrib, hsym, hst]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro ⟨h0, _⟩
          rw [hcS, Nat.add_comm] at h0
          exact absurd h0 (Nat.succ_ne_zero _)
        · intro ⟨h0, _⟩
          rw [hcS, Nat.add_comm] at h0
          exact absurd h0 (Nat.succ_ne_zero _)
        · intro ⟨h0, _⟩
          rw [hcS, Nat.add_comm] at h0
          exact absurd h0 (Nat.succ_ne_zero _)
        · intro h1
          rw [hcS] at h1
          have hds0 : countStrongDefs s ds = 0 := Nat.add_left_cancel h1
          cases hw : countWeakDefs s ds with
          | zero =>
            rw [hres, ih00 ⟨hds0, hw⟩]; exact ⟨d.val, rfl⟩
          | succ k =>
            cases k with
            | zero =>
              rcases ih01 ⟨hds0, hw⟩ with ⟨v, hv⟩
              rw [hres, hv]; exact ⟨d.val, rfl⟩
            | succ m =>
              have hge2 : 2 ≤ countWeakDefs s ds := by
                rw [hw]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
              rw [hres, ih02 ⟨hds0, hge2⟩]; exact ⟨d.val, rfl⟩
        · intro hge2
          rw [hcS] at hge2
          have hds1 : 1 ≤ countStrongDefs s ds := Nat.le_of_add_le_add_left hge2
          cases hds : countStrongDefs s ds with
          | zero =>
            rw [hds] at hds1
            exact absurd hds1 (Nat.not_succ_le_zero 0)
          | succ k =>
            cases k with
            | zero =>
              rcases ih1 hds with ⟨v, hv⟩
              rw [hres, hv]; rfl
            | succ m =>
              have hds2 : 2 ≤ countStrongDefs s ds := by
                rw [hds]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
              rw [hres, ih2 hds2]; rfl
      | weak =>
        have hcS : countStrongDefs s (d :: ds) = countStrongDefs s ds := by
          simp [countStrongDefs, hst]
        have hcW : countWeakDefs s (d :: ds) = 1 + countWeakDefs s ds := by
          simp [countWeakDefs, hsym, hst]
        have hres : resolveSym s (d :: ds) =
            mergeOutcome (.resolved .weak d.val) (resolveSym s ds) := by
          simp [resolveSym, symContrib, hsym, hst]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro ⟨_, hw0⟩
          rw [hcW, Nat.add_comm] at hw0
          exact absurd hw0 (Nat.succ_ne_zero _)
        · intro ⟨hs0, hw1⟩
          rw [hcS] at hs0
          rw [hcW] at hw1
          have hdw0 : countWeakDefs s ds = 0 := Nat.add_left_cancel hw1
          rw [hres, ih00 ⟨hs0, hdw0⟩]
          exact ⟨d.val, rfl⟩
        · intro ⟨hs0, hw2⟩
          rw [hcS] at hs0
          rw [hcW] at hw2
          have hdw1 : 1 ≤ countWeakDefs s ds := Nat.le_of_add_le_add_left hw2
          cases hdw : countWeakDefs s ds with
          | zero =>
            rw [hdw] at hdw1
            exact absurd hdw1 (Nat.not_succ_le_zero 0)
          | succ k =>
            cases k with
            | zero =>
              rcases ih01 ⟨hs0, hdw⟩ with ⟨v, hv⟩
              rw [hres, hv]; rfl
            | succ m =>
              have hdw2 : 2 ≤ countWeakDefs s ds := by
                rw [hdw]; exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
              rw [hres, ih02 ⟨hs0, hdw2⟩]; rfl
        · intro hs1
          rw [hcS] at hs1
          rcases ih1 hs1 with ⟨v, hv⟩
          rw [hres, hv]
          exact ⟨v, rfl⟩
        · intro hs2
          rw [hcS] at hs2
          rw [hres, ih2 hs2]; rfl
    · have hcS : countStrongDefs s (d :: ds) = countStrongDefs s ds := by
        cases hst : d.strength <;> simp [countStrongDefs, hsym, hst]
      have hcW : countWeakDefs s (d :: ds) = countWeakDefs s ds := by
        cases hst : d.strength <;> simp [countWeakDefs, hsym, hst]
      have hres : resolveSym s (d :: ds) = resolveSym s ds := by
        simp [resolveSym, symContrib, hsym, mergeOutcome_missing_left]
      rw [hcS, hcW, hres]
      exact ⟨ih00, ih01, ih02, ih1, ih2⟩

/-- Lowering an EII crate preserves the exact count of explicit (strong) definitions. -/
theorem countStrongDefs_lowerCrateEiiList (s : Nat) (allInCrate xs : List EiiImplDecl) :
    countStrongDefs s (lowerCrateEiiList allInCrate xs) = countExplicitList s xs := by
  induction xs with
  | nil => rfl
  | cons imp rest ih =>
    simp only [lowerCrateEiiList, countExplicitList]
    cases hd : imp.isDefault with
    | true =>
      by_cases hsup : hasExplicitFor imp.eiiSym allInCrate = true
      · simp [hsup, ih]
      · simp [hsup, countStrongDefs, ih]
    | false =>
      by_cases hsym : imp.eiiSym = s
      · simp [hsym, countStrongDefs, ih]
      · simp [hsym, countStrongDefs, ih]

/-- Lowering an EII crate never increases the count of default (weak) definitions;
and when no explicit impl exists in the crate, it preserves the default count exactly. -/
theorem countWeakDefs_lowerCrateEiiList_le (s : Nat) (allInCrate xs : List EiiImplDecl) :
    countWeakDefs s (lowerCrateEiiList allInCrate xs) ≤ countDefaultList s xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons imp rest ih =>
    simp only [lowerCrateEiiList, countDefaultList]
    cases hd : imp.isDefault with
    | true =>
      by_cases hsup : hasExplicitFor imp.eiiSym allInCrate = true
      · simp only [hsup, and_self, ite_true]
        exact Nat.le_trans ih (Nat.le_add_left _ _)
      · by_cases hsym : imp.eiiSym = s
        · subst hsym
          simp [hsup, countWeakDefs]
          exact ih
        · simp [hsup, hsym, countWeakDefs]
          exact ih
    | false =>
      simp [countWeakDefs]
      exact ih

theorem hasExplicitFor_false_of_count_zero (s : Nat) (xs : List EiiImplDecl)
    (h0 : countExplicitList s xs = 0) : hasExplicitFor s xs = false := by
  induction xs with
  | nil => rfl
  | cons imp rest ih =>
    simp only [countExplicitList] at h0
    have hhead : (if imp.eiiSym = s ∧ imp.isDefault = false then 1 else 0) = 0 :=
      Nat.eq_zero_of_add_eq_zero_right h0
    have htail : countExplicitList s rest = 0 :=
      Nat.eq_zero_of_add_eq_zero_left h0
    simp only [hasExplicitFor]
    by_cases hc : imp.eiiSym = s ∧ imp.isDefault = false
    · simp [hc] at hhead
    · simp [hc, ih htail]

theorem countWeakDefs_lowerCrateEiiList_eq_when_no_explicit (s : Nat)
    (allInCrate xs : List EiiImplDecl) (h0 : countExplicitList s allInCrate = 0) :
    countWeakDefs s (lowerCrateEiiList allInCrate xs) = countDefaultList s xs := by
  have hno : hasExplicitFor s allInCrate = false :=
    hasExplicitFor_false_of_count_zero s allInCrate h0
  induction xs with
  | nil => rfl
  | cons imp rest ih =>
    simp only [lowerCrateEiiList, countDefaultList]
    cases hd : imp.isDefault with
    | true =>
      by_cases hsym : imp.eiiSym = s
      · subst hsym
        simp [hno, countWeakDefs, ih]
      · by_cases hsup : hasExplicitFor imp.eiiSym allInCrate = true
        · simp [hsup, hsym, ih]
        · simp [hsup, hsym, countWeakDefs, ih]
    | false =>
      simp [countWeakDefs, ih]

theorem countStrongDefs_lowerAllCrates (s : Nat) (crates : List CrateUnit) :
    countStrongDefs s (lowerAllCrates crates) = countExplicit s crates := by
  induction crates with
  | nil => rfl
  | cons c cs ih =>
    simp only [lowerAllCrates, countExplicit, countStrongDefs_append, lowerCrateEii]
    rw [countStrongDefs_lowerCrateEiiList, ih]

theorem countWeakDefs_lowerAllCrates_le (s : Nat) (crates : List CrateUnit) :
    countWeakDefs s (lowerAllCrates crates) ≤ countDefault s crates := by
  induction crates with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    simp only [lowerAllCrates, countDefault, countWeakDefs_append, lowerCrateEii]
    exact Nat.add_le_add (countWeakDefs_lowerCrateEiiList_le s c.impls c.impls) ih

theorem countWeakDefs_lowerAllCrates_eq_when_no_explicit (s : Nat) (crates : List CrateUnit)
    (h0 : countExplicit s crates = 0) :
    countWeakDefs s (lowerAllCrates crates) = countDefault s crates := by
  induction crates with
  | nil => rfl
  | cons c cs ih =>
    simp only [countExplicit] at h0
    have hc0 : countExplicitList s c.impls = 0 := Nat.eq_zero_of_add_eq_zero_right h0
    have hcs0 : countExplicit s cs = 0 := Nat.eq_zero_of_add_eq_zero_left h0
    simp only [lowerAllCrates, countDefault, countWeakDefs_append, lowerCrateEii]
    rw [countWeakDefs_lowerCrateEiiList_eq_when_no_explicit s c.impls c.impls hc0, ih hcs0]

/-- **Main Theorem 3**: Given at most one default implementation (`eii.rs:119-122`)
and at least one total implementation (`eii.rs:139-151`, `CheckExistence` root
mode), `#[eii]` lowering + ELF strong-over-weak linking resolves deterministically
to a unique `.resolved st v` if and only if there is at most one explicit
implementation across the crate graph (`eii.rs:99-117`, `DuplicateEiiImpls`). -/
theorem eii_resolution_deterministic_iff_at_most_one_explicit
    (s : Nat) (crates : List CrateUnit)
    (h_def_le1 : countDefault s crates ≤ 1)
    (h_exists : 1 ≤ countExplicit s crates + countDefault s crates) :
    (∃ st v, resolveSym s (lowerAllCrates crates) = .resolved st v) ↔
    countExplicit s crates ≤ 1 := by
  have hspec := resolveSym_spec_by_counts s (lowerAllCrates crates)
  rcases hspec with ⟨_, h01, _, h1, h2⟩
  have hS := countStrongDefs_lowerAllCrates s crates
  constructor
  · intro ⟨st, v, hres⟩
    cases he : countExplicit s crates with
    | zero => exact Nat.zero_le 1
    | succ k =>
      cases k with
      | zero => exact Nat.le_refl 1
      | succ m =>
        have hge2 : 2 ≤ countStrongDefs s (lowerAllCrates crates) := by
          rw [hS, he]
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))
        have hconf := h2 hge2
        rw [hconf] at hres
        cases hres
  · intro hle1
    cases he : countExplicit s crates with
    | zero =>
      have hS0 : countStrongDefs s (lowerAllCrates crates) = 0 := by
        rw [hS, he]
      have hdef_ge1 : 1 ≤ countDefault s crates := by
        rw [he, Nat.zero_add] at h_exists
        exact h_exists
      have hdef1 : countDefault s crates = 1 := Nat.le_antisymm h_def_le1 hdef_ge1
      have hW1 : countWeakDefs s (lowerAllCrates crates) = 1 := by
        rw [countWeakDefs_lowerAllCrates_eq_when_no_explicit s crates he, hdef1]
      rcases h01 ⟨hS0, hW1⟩ with ⟨v, hv⟩
      exact ⟨.weak, v, hv⟩
    | succ k =>
      cases k with
      | zero =>
        have hS1 : countStrongDefs s (lowerAllCrates crates) = 1 := by
          rw [hS, he]
        rcases h1 hS1 with ⟨v, hv⟩
        exact ⟨.strong, v, hv⟩
      | succ m =>
        rw [he] at hle1
        have hcontra : Nat.succ m ≤ 0 := Nat.le_of_succ_le_succ hle1
        exact absurd hcontra (Nat.not_succ_le_zero m)

/-- Models Miri's `lookup_exported_symbol` filter (`src/tools/miri/src/shims/foreign_items.rs:142-146`),
which skips any exported item lacking an explicit `symbol_name` (`#[no_mangle]`/`#[export_name]`)
or `RUSTC_STD_INTERNAL_SYMBOL` — thereby filtering out `#[eii]` implementations. -/
noncomputable def miriLookupEiiSymbol (s : Nat) : List EiiImplDecl → Option Nat
  | [] => none
  | imp :: rest =>
      if imp.hasExplicitSymName = true ∧ imp.eiiSym = s then
        some imp.val
      else
        miriLookupEiiSymbol s rest


/-! ## Part 4: Constructive Sharpness Counterexamples (`ce1`–`ce4`) -/

/-- **Sharpness Counterexample 1**:
Mutating a well-formed same-CGU function definition (`present_fn`, `ExternalLinkage`,
`hasBody = true`) via `consts.rs:226`'s unchecked `LLVMSetLinkage(..., ExternalWeakLinkage)`
produces an ill-formed `define extern_weak` function that:
1. violates `wfLlvmFn` (rejected by `LLParser` / `llvm-as`),
2. is NOT emittable by `AsmPrinter::emitLinkage` (hits `llvm_unreachable` → `SIGILL`),
3. yet is STILL accepted by LLVM's incomplete `Verifier` (`Verifier.cpp:569, 3034`). -/
theorem ce1_same_cgu_set_linkage_produces_ill_formed_define_extern_weak :
    ∃ f : LlvmFn,
      wfLlvmFn f ∧
      isEmittableByAsmPrinter f.linkage = true ∧
      ¬ wfLlvmFn (applyExternWeakUnchecked f) ∧
      isEmittableByAsmPrinter (applyExternWeakUnchecked f).linkage = false ∧
      llvmVerifierAcceptsFn (applyExternWeakUnchecked f) := by
  let f : LlvmFn :=
    { sym := 1, linkage := .external, hasBody := true, bodyVal := 77, alwaysInline := false }
  refine ⟨f, ?_, rfl, ?_, rfl, ?_⟩
  · simp [wfLlvmFn, isValidFnDefinitionLinkage, f]
  · intro hwf
    simp [wfLlvmFn, applyExternWeakUnchecked, isValidFnDefinitionLinkage, f] at hwf
  · refine ⟨?_, ?_, ?_⟩
    · intro hfalse; cases hfalse
    · intro h; cases h
    · intro h; cases h

/-- **Sharpness Counterexample 2**:
With `prov` exporting strong symbol `present_fn` (`sym = 1`, `val = 77`) and
`missing_fn` (`sym = 2`) undefined, and neither present in Miri's built-in
`extern_statics_imports`:
- Native ELF resolves `present_fn` to `.bound 77`, `missing_fn` to `.null`, with
  distinct indirection slots (`elfExternWeakSlot 1 ≠ elfExternWeakSlot 2`),
- Miri's `extern_static_pointer` short-circuits both to `.null` and returns the
  EXACT SAME shared slot address (`miriSharedNullSlot = miriSharedNullSlot`). -/
theorem ce2_miri_short_circuit_diverges_from_elf_linker_on_present_symbol :
    ∃ (builtins : List (Nat × Nat)) (crateExports : List SymDef) (symPresent symMissing : Nat),
      elfExternWeakEval symPresent crateExports = .bound 77 ∧
      elfExternWeakEval symMissing crateExports = .null ∧
      elfExternWeakSlot symPresent ≠ elfExternWeakSlot symMissing ∧
      (miriExternWeakLookup builtins crateExports symPresent).2 = .null ∧
      (miriExternWeakLookup builtins crateExports symMissing).2 = .null ∧
      (miriExternWeakLookup builtins crateExports symPresent).1 =
        (miriExternWeakLookup builtins crateExports symMissing).1 ∧
      elfExternWeakEval symPresent crateExports ≠
        (miriExternWeakLookup builtins crateExports symPresent).2 := by
  let builtins : List (Nat × Nat) := [(99, 5)] -- e.g. Linux built-in `strlen`
  let exports : List SymDef := [{ sym := 1, strength := .strong, val := 77 }]
  refine ⟨builtins, exports, 1, 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [elfExternWeakEval, resolveSym, symContrib, mergeOutcome, exports]
  · simp [elfExternWeakEval, resolveSym, symContrib, mergeOutcome, exports]
  · intro h; cases h
  · simp [miriExternWeakLookup, lookupBuiltin, builtins]
  · simp [miriExternWeakLookup, lookupBuiltin, builtins]
  · simp [miriExternWeakLookup, lookupBuiltin, builtins]
  · simp [elfExternWeakEval, miriExternWeakLookup, lookupBuiltin, resolveSym,
          symContrib, mergeOutcome, exports, builtins]

/-- **Sharpness Counterexample 3**:
On `#[inline(always)] #[linkage = "weak"]` (`weakAny`, local body `10`),
with admissible strong override `99`:
- LLVM's `getAttributeBasedInliningDecision` (`InlineCost.cpp:3209`) returns
  `true` when `alwaysInline = true`, baking in `10 ≠ 99` and breaking strong
  interposition;
- Without `alwaysInline` (`false`), LLVM checks `isInterposable()` (`InlineCost.cpp:3238`)
  and refuses to inline, preserving `99`;
- The fixed `guardedInlineDecision` refuses to inline even when `alwaysInline = true`. -/
theorem ce3_alwaysinline_on_weak_breaks_strong_interposition :
    ∃ (d : CalleeDef) (ov : Option Nat),
      AdmissibleOverride d.linkage d.localVal ov ∧
      llvmInlineDecision d true = true ∧
      llvmInlineDecision d false = false ∧
      guardedInlineDecision d true = false ∧
      evalInlinedCall d = 10 ∧
      evalDirectCall d ov = 99 ∧
      evalInlinedCall d ≠ evalDirectCall d ov := by
  let d : CalleeDef := { linkage := .weakAny, localVal := 10 }
  refine ⟨d, some 99, trivial, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h; cases h

/-- **Sharpness Counterexample 4**:
A two-crate `#[eii]` workspace (`hook_api` default `15`, `app_override` explicit `905`)
resolves natively to `.resolved .strong 905`, while Miri's `lookup_exported_symbol`
filter (`foreign_items.rs:142-146`) returns `none` because neither implementation
sets `hasExplicitSymName = true`. -/
theorem ce4_miri_eii_filter_misses_aliased_impl :
    ∃ (s : Nat) (hookApi appOverride : CrateUnit),
      resolveSym s (lowerAllCrates [hookApi, appOverride]) = .resolved .strong 905 ∧
      resolveSym s (lowerAllCrates [hookApi]) = .resolved .weak 15 ∧
      miriLookupEiiSymbol s (hookApi.impls ++ appOverride.impls) = none := by
  let hookApi : CrateUnit :=
    { crateId := 1
      impls := [{ eiiSym := 7, isDefault := true, val := 15, hasExplicitSymName := false }] }
  let appOverride : CrateUnit :=
    { crateId := 2
      impls := [{ eiiSym := 7, isDefault := false, val := 905, hasExplicitSymName := false }] }
  refine ⟨7, hookApi, appOverride, ?_, ?_, ?_⟩
  · simp [lowerAllCrates, lowerCrateEii, lowerCrateEiiList, hasExplicitFor,
          resolveSym, symContrib, mergeOutcome, hookApi, appOverride]
  · simp [lowerAllCrates, lowerCrateEii, lowerCrateEiiList, hasExplicitFor,
          resolveSym, symContrib, mergeOutcome, hookApi]
  · simp [miriLookupEiiSymbol, hookApi, appOverride]

/-- Same-crate default-alias suppression (`codegen_attrs.rs:246-258`) witness:
when a single crate defines BOTH default (`15`) and explicit (`705`), lowering
suppresses the weak default alias and emits only the strong override (`705`). -/
theorem eii_same_crate_suppresses_default_alias :
    ∃ (s : Nat) (c : CrateUnit),
      lowerCrateEii c = [{ sym := s, strength := .strong, val := 705 }] ∧
      resolveSym s (lowerCrateEii c) = .resolved .strong 705 := by
  let c : CrateUnit :=
    { crateId := 1
      impls :=
        [ { eiiSym := 7, isDefault := true, val := 15, hasExplicitSymName := false }
        , { eiiSym := 7, isDefault := false, val := 705, hasExplicitSymName := false } ] }
  refine ⟨7, c, ?_, ?_⟩
  · simp [lowerCrateEii, lowerCrateEiiList, hasExplicitFor, c]
  · simp [lowerCrateEii, lowerCrateEiiList, hasExplicitFor, resolveSym,
          symContrib, mergeOutcome, c]

end LinkageInterpositionAndEiiSoundness

#print axioms LinkageInterpositionAndEiiSoundness.applyExternWeakGuarded_preserves_wf
#print axioms LinkageInterpositionAndEiiSoundness.inlining_sound_under_link_override_iff_non_interposable
#print axioms LinkageInterpositionAndEiiSoundness.guardedInlineDecision_sound
#print axioms LinkageInterpositionAndEiiSoundness.linker_resolve_commutes_and_extern_weak_binds_strong_when_present
#print axioms LinkageInterpositionAndEiiSoundness.eii_resolution_deterministic_iff_at_most_one_explicit
#print axioms LinkageInterpositionAndEiiSoundness.ce1_same_cgu_set_linkage_produces_ill_formed_define_extern_weak
#print axioms LinkageInterpositionAndEiiSoundness.ce2_miri_short_circuit_diverges_from_elf_linker_on_present_symbol
#print axioms LinkageInterpositionAndEiiSoundness.ce3_alwaysinline_on_weak_breaks_strong_interposition
#print axioms LinkageInterpositionAndEiiSoundness.ce4_miri_eii_filter_misses_aliased_impl
#print axioms LinkageInterpositionAndEiiSoundness.eii_same_crate_suppresses_default_alias
