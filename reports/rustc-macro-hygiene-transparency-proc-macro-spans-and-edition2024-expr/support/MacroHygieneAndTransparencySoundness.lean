/-!
# Macro Hygiene, Transparency, Two-Pass Privacy, Expansion Fuel, and Determinism Soundness

Standalone Lean `v4.34.1` formalization modeling `rustc`'s macro hygiene and
privacy architecture as implemented in:
- `compiler/rustc_span/src/hygiene.rs` (`Transparency`, `SyntaxContext`,
  `normalize_to_macros_2_0`, `normalize_to_macro_rules`, `apply_mark`),
- `compiler/rustc_resolve/src/ident.rs` & `compiler/rustc_resolve/src/late.rs`
  (dual normalization for locals/labels/`$crate` vs. module items, and
  `IdentKey::new_adjusted` privacy-scope adjustment),
- `compiler/rustc_privacy/src/lib.rs` (`TypePrivacyVisitor` checking semantic
  `FnDef` and nominal types against the call-site module regardless of hygiene),
- `compiler/rustc_expand/src/expand.rs` (`recursion_limit.value_within_limit`),
- `compiler/rustc_expand/src/proc_macro.rs` (unsandboxed host `proc_macro`
  execution vs. pure/sealed expansion).

This module is constructive, total, and axiom-minimal (zero choice, reflection,
or incomplete-proof axioms).
-/

namespace MacroHygieneAndTransparencySoundness

/-! ## Section 1: Transparency, Expansion Marks, and SyntaxContext Normalization -/

/-- Three-tier macro hygiene transparency lattice matching `rustc_span::hygiene::Transparency`. -/
inductive Transparency where
  | transparent
  | semiOpaque
  | opaque
  deriving DecidableEq, Repr

/-- Macro expansion identifier (`0` = unexpanded root AST, `> 0` = macro expansion). -/
abbrev ExpnId := Nat

/-- Module identifier for lexical item resolution and privacy checks. -/
abbrev ModuleId := Nat

/-- Interned identifier symbol. -/
abbrev SymbolId := Nat

/-- Unique semantic target identifier (local binding ID, label ID, or item DefId). -/
abbrev TargetId := Nat

/-- A single hygiene mark pushed onto a `SyntaxContext` stack. -/
structure Mark where
  expnId : ExpnId
  transparency : Transparency
  deriving DecidableEq, Repr

/-- `SyntaxContext` represented as an outermost-first stack of expansion marks.
    The empty list `[]` is `SyntaxContext::root()`. -/
abbrev SyntaxContext := List Mark

/-- Push a fresh mark onto a `SyntaxContext`. -/
noncomputable def applyMark (ctxt : SyntaxContext) (e : ExpnId) (t : Transparency) : SyntaxContext :=
  { expnId := e, transparency := t } :: ctxt

/-- `SyntaxContext::normalize_to_macros_2_0`: retains only `Opaque` marks
    (`compiler/rustc_span/src/hygiene.rs`, `SyntaxContextData.opaque`). -/
noncomputable def normalizeToMacros20 : SyntaxContext → SyntaxContext
  | [] => []
  | m :: rest =>
    match m.transparency with
    | .opaque => m :: normalizeToMacros20 rest
    | .semiOpaque => normalizeToMacros20 rest
    | .transparent => normalizeToMacros20 rest

/-- `SyntaxContext::normalize_to_macro_rules`: retains `SemiOpaque` and `Opaque` marks,
    stripping `Transparent` (`compiler/rustc_span/src/hygiene.rs`, `opaque_and_semiopaque`). -/
noncomputable def normalizeToMacroRules : SyntaxContext → SyntaxContext
  | [] => []
  | m :: rest =>
    match m.transparency with
    | .opaque => m :: normalizeToMacroRules rest
    | .semiOpaque => m :: normalizeToMacroRules rest
    | .transparent => normalizeToMacroRules rest

/-- Predicate asserting that expansion ID `e` does not appear anywhere in `ctxt`. -/
noncomputable def FreshIn (e : ExpnId) : SyntaxContext → Prop
  | [] => True
  | m :: rest => m.expnId ≠ e ∧ FreshIn e rest

theorem normalizeToMacros20_idem (ctxt : SyntaxContext) :
    normalizeToMacros20 (normalizeToMacros20 ctxt) = normalizeToMacros20 ctxt := by
  induction ctxt with
  | nil => rfl
  | cons m rest ih =>
    cases h : m.transparency <;> simp [normalizeToMacros20, h, ih]

theorem normalizeToMacroRules_idem (ctxt : SyntaxContext) :
    normalizeToMacroRules (normalizeToMacroRules ctxt) = normalizeToMacroRules ctxt := by
  induction ctxt with
  | nil => rfl
  | cons m rest ih =>
    cases h : m.transparency <;> simp [normalizeToMacroRules, h, ih]

theorem normalizeToMacros20_of_macroRules (ctxt : SyntaxContext) :
    normalizeToMacros20 (normalizeToMacroRules ctxt) = normalizeToMacros20 ctxt := by
  induction ctxt with
  | nil => rfl
  | cons m rest ih =>
    cases h : m.transparency <;> simp [normalizeToMacros20, normalizeToMacroRules, h, ih]

theorem freshIn_normalizeToMacroRules {e : ExpnId} {ctxt : SyntaxContext}
    (h : FreshIn e ctxt) : FreshIn e (normalizeToMacroRules ctxt) := by
  induction ctxt with
  | nil => trivial
  | cons m rest ih =>
    cases h with
    | intro hne hrest =>
      cases ht : m.transparency with
      | transparent =>
        dsimp only [normalizeToMacroRules]
        rw [ht]
        exact ih hrest
      | semiOpaque =>
        dsimp only [normalizeToMacroRules]
        rw [ht]
        exact ⟨hne, ih hrest⟩
      | «opaque» =>
        dsimp only [normalizeToMacroRules]
        rw [ht]
        exact ⟨hne, ih hrest⟩

theorem head_mark_ne_of_freshIn {e : ExpnId} {t : Transparency} {xs ys : SyntaxContext}
    (hFresh : FreshIn e ys) :
    ({ expnId := e, transparency := t } :: xs) ≠ ys := by
  intro hEq
  cases ys with
  | nil => cases hEq
  | cons m rest =>
    injection hEq with hm _
    cases hFresh with
    | intro hne _ =>
      have hId : m.expnId = e := by
        rw [← hm]
      exact hne hId

/-- Under `SemiOpaque` or `Opaque`, applying a fresh expansion mark `e` yields a
    `normalizeToMacroRules` context strictly distinct from any context in which `e` is fresh. -/
theorem applyMark_semiOpaque_or_opaque_distinct_macroRules
    {e : ExpnId} {t : Transparency}
    (ht : t = .semiOpaque ∨ t = .opaque)
    (macroCtxt callerCtxt : SyntaxContext)
    (hFresh : FreshIn e callerCtxt) :
    normalizeToMacroRules (applyMark macroCtxt e t) ≠ normalizeToMacroRules callerCtxt := by
  have hFreshNorm : FreshIn e (normalizeToMacroRules callerCtxt) :=
    freshIn_normalizeToMacroRules hFresh
  cases ht with
  | inl hSemi =>
    rw [hSemi]
    exact head_mark_ne_of_freshIn hFreshNorm
  | inr hOp =>
    rw [hOp]
    exact head_mark_ne_of_freshIn hFreshNorm

theorem applyMark_transparent_eq_macroRules (ctxt : SyntaxContext) (e : ExpnId) :
    normalizeToMacroRules (applyMark ctxt e .transparent) = normalizeToMacroRules ctxt := rfl

theorem applyMark_semiOpaque_eq_macros20 (ctxt : SyntaxContext) (e : ExpnId) :
    normalizeToMacros20 (applyMark ctxt e .semiOpaque) = normalizeToMacros20 ctxt := rfl

theorem applyMark_opaque_cons_macros20 (ctxt : SyntaxContext) (e : ExpnId) :
    normalizeToMacros20 (applyMark ctxt e .opaque) =
      { expnId := e, transparency := .opaque } :: normalizeToMacros20 ctxt := rfl

/-! ## Section 2: Identifier Kinds, Two-Pass Name Resolution, and Type-Level Privacy -/

/-- Identifier syntactic/resolution categories distinguishing hygiene rules. -/
inductive IdentKind where
  | localVar
  | label
  | dollarCrate
  | itemFn
  | itemConst
  deriving DecidableEq, Repr

/-- An identifier carrying its symbol, category, and `SyntaxContext` mark stack. -/
structure Ident where
  name : SymbolId
  kind : IdentKind
  ctxt : SyntaxContext
  deriving DecidableEq, Repr

/-- Item visibility relative to its defining module. -/
inductive Visibility where
  | pubVis
  | privTo (ownerMod : ModuleId)
  deriving DecidableEq, Repr

/-- Semantic type checked by `rustc_privacy::TypePrivacyVisitor` after type inference.
    Note that `privFnDef` models Rust's zero-sized nominal `FnDef` type `fn(...) -> R {f}`,
    whereas `pubScalar` (e.g. `u32`) and `pubFnPtr` (e.g. `fn() -> u32`) carry no private DefId. -/
inductive SemTy where
  | pubScalar
  | pubFnPtr
  | privFnDef (ownerMod : ModuleId) (fnId : TargetId)
  | privAdt (ownerMod : ModuleId) (adtId : TargetId)
  deriving DecidableEq, Repr

/-- Visibility check `vis.is_accessible_from(fromMod)`. -/
noncomputable def isAccessibleFrom (vis : Visibility) (fromMod : ModuleId) : Bool :=
  match vis with
  | .pubVis => true
  | .privTo owner => owner == fromMod

/-- A lexical binding in a local variable or loop-label rib (normalized via `normalizeToMacroRules`). -/
structure LexicalEntry where
  name : SymbolId
  kind : IdentKind
  normCtxt : SyntaxContext
  target : TargetId
  deriving DecidableEq, Repr

/-- A module-level item declaration (`fn` or `const`). -/
structure ItemEntry where
  ownerMod : ModuleId
  name : SymbolId
  kind : IdentKind
  vis : Visibility
  semTy : SemTy
  target : TargetId
  deriving DecidableEq, Repr

/-- Complete resolution environment for a single compilation unit / cross-crate graph. -/
structure ResolveEnv where
  callSiteMod : ModuleId
  expnDefMod : ExpnId → ModuleId
  lexicalRibs : List LexicalEntry
  items : List ItemEntry

/-- Outcome of Pass 1 (name resolution) and Pass 2 (semantic type privacy). -/
inductive ResolveError where
  | notFoundE0425 (name : SymbolId)
  | privateItemE0603 (name : SymbolId) (ownerMod : ModuleId)
  | privateTypePrivacy (ownerMod : ModuleId) (typeDef : TargetId)
  deriving DecidableEq, Repr

/-- Resolved binding metadata passed from Pass 1 (`rustc_resolve`) to Pass 2 (`rustc_privacy`). -/
structure ResolvedBinding where
  target : TargetId
  semTy : SemTy
  resolvedInMod : ModuleId
  deriving DecidableEq, Repr

inductive CheckResult (α : Type) where
  | ok (val : α)
  | err (e : ResolveError)
  deriving DecidableEq, Repr

/-- Lookup in lexical ribs (locals and labels) using `macro_rules`-normalized `SyntaxContext`. -/
noncomputable def lookupLexical (ribs : List LexicalEntry) (name : SymbolId)
    (kind : IdentKind) (normCtxt : SyntaxContext) : Option TargetId :=
  match ribs with
  | [] => none
  | entry :: rest =>
    if entry.name == name && entry.kind == kind && entry.normCtxt == normCtxt then
      some entry.target
    else
      lookupLexical rest name kind normCtxt

/-- Lookup an item in a specific module `inMod`, checking name-resolution visibility from `privacyMod`. -/
noncomputable def lookupItemInMod (items : List ItemEntry) (inMod : ModuleId) (privacyMod : ModuleId)
    (name : SymbolId) (kind : IdentKind) : CheckResult ResolvedBinding :=
  match items with
  | [] => .err (.notFoundE0425 name)
  | item :: rest =>
    match item.ownerMod == inMod && item.name == name && item.kind == kind with
    | true =>
      match isAccessibleFrom item.vis privacyMod with
      | true => .ok { target := item.target, semTy := item.semTy, resolvedInMod := inMod }
      | false => .err (.privateItemE0603 name item.ownerMod)
    | false =>
      lookupItemInMod rest inMod privacyMod name kind

/-- Pass 1 (`rustc_resolve`): resolve an identifier according to its `IdentKind` and `SyntaxContext`.
    - `localVar` & `label`: resolved in `lexicalRibs` using `normalizeToMacroRules`.
    - `dollarCrate`: resolves crate root via outermost mark surviving `normalizeToMacroRules`.
    - `itemFn` & `itemConst`: normalized via `normalizeToMacros20` (`IdentKey::new_adjusted`);
      if an `Opaque` mark remains, both lookup module AND name-resolution privacy scope
      switch to `expnDefMod m.expnId`; otherwise both stay at `callSiteMod`. -/
noncomputable def resolveIdent (env : ResolveEnv) (id : Ident) : CheckResult ResolvedBinding :=
  match id.kind with
  | .localVar =>
    let nc := normalizeToMacroRules id.ctxt
    match lookupLexical env.lexicalRibs id.name .localVar nc with
    | some tid => .ok { target := tid, semTy := .pubScalar, resolvedInMod := env.callSiteMod }
    | none => .err (.notFoundE0425 id.name)
  | .label =>
    let nc := normalizeToMacroRules id.ctxt
    match lookupLexical env.lexicalRibs id.name .label nc with
    | some tid => .ok { target := tid, semTy := .pubScalar, resolvedInMod := env.callSiteMod }
    | none => .err (.notFoundE0425 id.name)
  | .dollarCrate =>
    let nc := normalizeToMacroRules id.ctxt
    let rootMod := match nc with
      | m :: _ => env.expnDefMod m.expnId
      | [] => env.callSiteMod
    .ok { target := rootMod, semTy := .pubScalar, resolvedInMod := rootMod }
  | .itemFn =>
    match normalizeToMacros20 id.ctxt with
    | m :: _ =>
      let defMod := env.expnDefMod m.expnId
      lookupItemInMod env.items defMod defMod id.name .itemFn
    | [] =>
      lookupItemInMod env.items env.callSiteMod env.callSiteMod id.name .itemFn
  | .itemConst =>
    match normalizeToMacros20 id.ctxt with
    | m :: _ =>
      let defMod := env.expnDefMod m.expnId
      lookupItemInMod env.items defMod defMod id.name .itemConst
    | [] =>
      lookupItemInMod env.items env.callSiteMod env.callSiteMod id.name .itemConst

/-- Pass 1 for explicit `$crate::member` paths:
    `$crate` locates the defining crate/module via `normalizeToMacroRules` (retaining
    `SemiOpaque` marks), while the member segment's name-resolution privacy scope is
    adjusted via `normalizeToMacros20` (`IdentKey::new_adjusted`) — stripping `SemiOpaque`
    marks so `macro_rules!` `$crate::private_item` fails with `E0603` at `callSiteMod`. -/
noncomputable def resolveDollarCrateMember (env : ResolveEnv) (dollarCrateCtxt : SyntaxContext)
    (memberName : SymbolId) (memberKind : IdentKind) (memberCtxt : SyntaxContext) :
    CheckResult ResolvedBinding :=
  let targetMod := match normalizeToMacroRules dollarCrateCtxt with
    | m :: _ => env.expnDefMod m.expnId
    | [] => env.callSiteMod
  let privacyMod := match normalizeToMacros20 memberCtxt with
    | m :: _ => env.expnDefMod m.expnId
    | [] => env.callSiteMod
  lookupItemInMod env.items targetMod privacyMod memberName memberKind

/-- Pass 2 (`rustc_privacy::TypePrivacyVisitor`): checks the semantic type of an
    expression against `callSiteMod`, completely ignoring `SyntaxContext` / macro hygiene
    (`compiler/rustc_privacy/src/lib.rs:1122`, "regardless of names and their hygiene"). -/
noncomputable def checkTypePrivacy (ty : SemTy) (callSiteMod : ModuleId) : CheckResult Unit :=
  match ty with
  | .pubScalar => .ok ()
  | .pubFnPtr => .ok ()
  | .privFnDef owner fnId =>
    match owner == callSiteMod with
    | true => .ok ()
    | false => .err (.privateTypePrivacy owner fnId)
  | .privAdt owner adtId =>
    match owner == callSiteMod with
    | true => .ok ()
    | false => .err (.privateTypePrivacy owner adtId)

/-- End-to-end two-pass identifier checking: Pass 1 name resolution followed by
    Pass 2 semantic type privacy. -/
noncomputable def checkIdentTwoPass (env : ResolveEnv) (id : Ident) : CheckResult ResolvedBinding :=
  match resolveIdent env id with
  | .err e => .err e
  | .ok binding =>
    match checkTypePrivacy binding.semTy env.callSiteMod with
    | .ok () => .ok binding
    | .err e => .err e

/-! ## Section 3: Core Hygiene & Two-Pass Privacy Soundness Theorems -/

/-- Helper: a lexical rib entry whose `normCtxt` differs from `nc` is skipped during lookup. -/
theorem lookupLexical_skip_ne_ctxt (entry : LexicalEntry) (rest : List LexicalEntry)
    (name : SymbolId) (kind : IdentKind) (nc : SyntaxContext)
    (hne : entry.normCtxt ≠ nc) :
    lookupLexical (entry :: rest) name kind nc = lookupLexical rest name kind nc := by
  have hbeq : (entry.normCtxt == nc) = false := by
    cases hb : (entry.normCtxt == nc) with
    | false => rfl
    | true =>
      exact False.elim (hne (eq_of_beq hb))
  change (if (entry.name == name && entry.kind == kind && entry.normCtxt == nc) = true
          then some entry.target else lookupLexical rest name kind nc) =
         lookupLexical rest name kind nc
  rw [hbeq]
  cases (entry.name == name) <;> cases (entry.kind == kind) <;> rfl

/-- Helper: if every entry in `ribs` has its `normCtxt` free of expansion ID `e`, then
    a lookup with a `SemiOpaque`/`Opaque` mark `e` cannot capture any binding in `ribs`. -/
noncomputable def AllRibsFreshIn (e : ExpnId) : List LexicalEntry → Prop
  | [] => True
  | entry :: rest => FreshIn e entry.normCtxt ∧ AllRibsFreshIn e rest

theorem lookupLexical_none_of_allRibsFreshIn {e : ExpnId} {t : Transparency}
    (ht : t = .semiOpaque ∨ t = .opaque)
    (ribs : List LexicalEntry) (name : SymbolId) (kind : IdentKind)
    (macroCtxt : SyntaxContext) (hFresh : AllRibsFreshIn e ribs) :
    lookupLexical ribs name kind (normalizeToMacroRules (applyMark macroCtxt e t)) = none := by
  induction ribs with
  | nil => rfl
  | cons entry rest ih =>
    cases hFresh with
    | intro hHead hTail =>
      have hNe : entry.normCtxt ≠ normalizeToMacroRules (applyMark macroCtxt e t) := by
        intro hEq
        cases ht with
        | inl hSemi =>
          rw [hSemi] at hEq
          exact head_mark_ne_of_freshIn hHead hEq.symm
        | inr hOp =>
          rw [hOp] at hEq
          exact head_mark_ne_of_freshIn hHead hEq.symm
      rw [lookupLexical_skip_ne_ctxt entry rest name kind _ hNe]
      exact ih hTail

/-- **Theorem 1 (Alpha-Equivalence / Capture-Avoidance for Locals & Labels Under
    `SemiOpaque` and `Opaque`):**
    For any expansion with fresh mark `e` and transparency `t ∈ {SemiOpaque, Opaque}`,
    and any identifier kind `k ∈ {localVar, label}`:
    1. A macro-introduced binder `(name, k, macroCtxt_marked)` prepended to caller ribs
       NEVER captures a caller use `(name, k, callerCtxt)` — the caller's lookup result
       is identical with or without the macro's binder in scope (alpha-equivalence).
    2. A macro-introduced reference `(name, k, macroCtxt_marked)` NEVER captures any
       caller-side binding in `callerRibs` (resolving to `E0425` if no macro-side
       binder with mark `e` is present). -/
theorem semiOpaque_opaque_avoid_local_and_label_capture
    (callSiteMod : ModuleId) (expnDefMod : ExpnId → ModuleId)
    (items : List ItemEntry) (callerRibs : List LexicalEntry)
    (e : ExpnId) (t : Transparency) (ht : t = .semiOpaque ∨ t = .opaque)
    (k : IdentKind) (hk : k = .localVar ∨ k = .label)
    (name : SymbolId) (macroTarget : TargetId)
    (macroCtxt callerCtxt : SyntaxContext)
    (hFreshCaller : FreshIn e callerCtxt)
    (hFreshRibs : AllRibsFreshIn e callerRibs) :
    let macroMarkNorm := normalizeToMacroRules (applyMark macroCtxt e t)
    let macroEntry : LexicalEntry :=
      { name := name, kind := k, normCtxt := macroMarkNorm, target := macroTarget }
    let envWithout : ResolveEnv :=
      { callSiteMod := callSiteMod, expnDefMod := expnDefMod,
        lexicalRibs := callerRibs, items := items }
    let envWith : ResolveEnv :=
      { callSiteMod := callSiteMod, expnDefMod := expnDefMod,
        lexicalRibs := macroEntry :: callerRibs, items := items }
    resolveIdent envWith { name := name, kind := k, ctxt := callerCtxt } =
      resolveIdent envWithout { name := name, kind := k, ctxt := callerCtxt } ∧
    resolveIdent envWithout { name := name, kind := k, ctxt := applyMark macroCtxt e t } =
      .err (.notFoundE0425 name) := by
  intro macroMarkNorm macroEntry envWithout envWith
  have hNe : macroMarkNorm ≠ normalizeToMacroRules callerCtxt :=
    applyMark_semiOpaque_or_opaque_distinct_macroRules ht macroCtxt callerCtxt hFreshCaller
  have hNoMacroCaptureCaller :=
    lookupLexical_none_of_allRibsFreshIn ht callerRibs name k macroCtxt hFreshRibs
  cases hk with
  | inl hLoc =>
    subst hLoc
    constructor
    · simp only [resolveIdent]
      rw [lookupLexical_skip_ne_ctxt macroEntry callerRibs name .localVar
            (normalizeToMacroRules callerCtxt) hNe]
    · simp only [resolveIdent]
      rw [hNoMacroCaptureCaller]
  | inr hLbl =>
    subst hLbl
    constructor
    · simp only [resolveIdent]
      rw [lookupLexical_skip_ne_ctxt macroEntry callerRibs name .label
            (normalizeToMacroRules callerCtxt) hNe]
    · simp only [resolveIdent]
      rw [hNoMacroCaptureCaller]

/-- **Theorem 2 (Item Resolution Split Between `SemiOpaque` and `Opaque`):**
    Given a macro defined in `defMod` invoked from `callMod` (`defMod ≠ callMod`),
    when an item identifier `name` (either `itemFn` or `itemConst`) is produced from
    an unexpanded base context `[]` with expansion mark `e` (`expnDefMod e = defMod`):
    - Under `SemiOpaque` (`macro_rules!`, `Span::mixed_site()`), `resolveIdent`
      strips the mark via `normalizeToMacros20` and resolves `name` in `callMod`
      with privacy checked against `callMod`.
    - Under `Opaque` (`decl_macro`, `Span::def_site()`), `resolveIdent` retains the
      mark and resolves `name` in `defMod` with name-resolution privacy adjusted to `defMod`. -/
theorem semiOpaque_resolves_item_at_callsite_vs_opaque_at_defsite
    (env : ResolveEnv) (e : ExpnId) (name : SymbolId)
    (k : IdentKind) (hk : k = .itemFn ∨ k = .itemConst) :
    resolveIdent env { name := name, kind := k, ctxt := applyMark [] e .semiOpaque } =
      lookupItemInMod env.items env.callSiteMod env.callSiteMod name k ∧
    resolveIdent env { name := name, kind := k, ctxt := applyMark [] e .opaque } =
      lookupItemInMod env.items (env.expnDefMod e) (env.expnDefMod e) name k := by
  cases hk with
  | inl hFn =>
    subst hFn
    exact ⟨rfl, rfl⟩
  | inr hConst =>
    subst hConst
    exact ⟨rfl, rfl⟩

/-- Axiom-free reflexivity of `Nat` boolean equality `(n == n) = true`. -/
private theorem nat_beq_self (n : Nat) : (n == n) = true := by
  change decide (n = n) = true
  exact decide_eq_true rfl

/-- Axiom-free soundness of `Nat` boolean equality `(a == b) = true → a = b`. -/
private theorem nat_eq_of_beq {a b : Nat} (h : (a == b) = true) : a = b :=
  of_decide_eq_true h

/-- **Theorem 3 (Two-Pass `FnDef` Type-Privacy Invariant):**
    Suppose `defMod ≠ callMod`, `env.expnDefMod e = defMod`, and `defMod` defines:
    - a private constant `constName` of public scalar type `SemTy.pubScalar`, and
    - a private function `fnName` of private zero-sized `FnDef` type `SemTy.privFnDef defMod fnTarget`.
    Then under `Opaque` (`decl_macro`) hygiene from `callMod`:
    1. Both `constName` and `fnName` **pass Pass 1 name resolution** (neither triggers `E0603`).
    2. In Pass 2 (`checkIdentTwoPass`), `constName` **succeeds** (`pubScalar` is accessible),
       while `fnName` is **rejected by type-level privacy** (`.err (.privateTypePrivacy defMod fnTarget)`).
    3. By contrast, a `SemiOpaque` `$crate::fnName` invocation fails earlier in **Pass 1**
       with `.err (.privateItemE0603 fnName defMod)`. -/
theorem opaque_priv_const_passes_while_priv_fn_rejected_by_type_privacy
    (defMod callMod : ModuleId) (hDiff : defMod ≠ callMod)
    (e : ExpnId) (constName fnName : SymbolId) (constTarget fnTarget : TargetId)
    (hNamesNe : constName ≠ fnName) :
    let constItem : ItemEntry :=
      { ownerMod := defMod, name := constName, kind := .itemConst,
        vis := .privTo defMod, semTy := .pubScalar, target := constTarget }
    let fnItem : ItemEntry :=
      { ownerMod := defMod, name := fnName, kind := .itemFn,
        vis := .privTo defMod, semTy := .privFnDef defMod fnTarget, target := fnTarget }
    let env : ResolveEnv :=
      { callSiteMod := callMod, expnDefMod := fun _ => defMod,
        lexicalRibs := [], items := [constItem, fnItem] }
    let constId : Ident := { name := constName, kind := .itemConst, ctxt := applyMark [] e .opaque }
    let fnId : Ident := { name := fnName, kind := .itemFn, ctxt := applyMark [] e .opaque }
    -- (1) Both pass Pass 1 name resolution (Opaque adjusts privacy scope to defMod)
    resolveIdent env constId =
      .ok { target := constTarget, semTy := .pubScalar, resolvedInMod := defMod } ∧
    resolveIdent env fnId =
      .ok { target := fnTarget, semTy := .privFnDef defMod fnTarget, resolvedInMod := defMod } ∧
    -- (2) Two-pass check: private const succeeds; private fn rejected by FnDef type privacy
    checkIdentTwoPass env constId =
      .ok { target := constTarget, semTy := .pubScalar, resolvedInMod := defMod } ∧
    checkIdentTwoPass env fnId =
      .err (.privateTypePrivacy defMod fnTarget) ∧
    -- (3) Contrast: SemiOpaque $crate::fnName rejected earlier in Pass 1 with E0603
    resolveDollarCrateMember env (applyMark [] e .semiOpaque) fnName .itemFn
      (applyMark [] e .semiOpaque) =
      .err (.privateItemE0603 fnName defMod) := by
  intro constItem fnItem env constId fnId
  have hModEq : (defMod == defMod) = true := nat_beq_self defMod
  have hModNe : (defMod == callMod) = false := by
    cases hb : (defMod == callMod) with
    | false => rfl
    | true => exact False.elim (hDiff (nat_eq_of_beq hb))
  have hConstEq : (constName == constName) = true := nat_beq_self constName
  have hFnEq : (fnName == fnName) = true := nat_beq_self fnName
  have hConstNeFn : (constName == fnName) = false := by
    cases hb : (constName == fnName) with
    | false => rfl
    | true => exact False.elim (hNamesNe (nat_eq_of_beq hb))
  have hResConst :
      resolveIdent env constId =
        .ok { target := constTarget, semTy := .pubScalar, resolvedInMod := defMod } := by
    dsimp only [resolveIdent, constId, applyMark, normalizeToMacros20, env,
                lookupItemInMod, constItem, isAccessibleFrom]
    rw [hModEq, hConstEq]
    rfl
  have hResFn :
      resolveIdent env fnId =
        .ok { target := fnTarget, semTy := .privFnDef defMod fnTarget, resolvedInMod := defMod } := by
    dsimp only [resolveIdent, fnId, applyMark, normalizeToMacros20, env,
                lookupItemInMod, constItem, fnItem, isAccessibleFrom]
    rw [hModEq, hConstNeFn, hFnEq]
    rfl
  refine ⟨hResConst, hResFn, ?_, ?_, ?_⟩
  · unfold checkIdentTwoPass
    rw [hResConst]
    rfl
  · unfold checkIdentTwoPass
    rw [hResFn]
    dsimp only [checkTypePrivacy]
    rw [hModNe]
  · dsimp only [resolveDollarCrateMember, applyMark, normalizeToMacroRules, normalizeToMacros20,
                env, lookupItemInMod, constItem, fnItem, isAccessibleFrom]
    rw [hModEq, hConstNeFn, hFnEq, hModNe]
    rfl

/-- Companion theorem: coercing a private function to a private `const` of public function
    pointer type `SemTy.pubFnPtr` (`const HELPER_PTR: fn() -> u32 = helper`) bypasses
    `TypePrivacyVisitor` under `Opaque` hygiene (matching the intra-crate empirical probe). -/
theorem opaque_priv_fnptr_const_passes_two_pass
    (defMod callMod : ModuleId) (e : ExpnId)
    (ptrConstName : SymbolId) (ptrTarget : TargetId) :
    let ptrItem : ItemEntry :=
      { ownerMod := defMod, name := ptrConstName, kind := .itemConst,
        vis := .privTo defMod, semTy := .pubFnPtr, target := ptrTarget }
    let env : ResolveEnv :=
      { callSiteMod := callMod, expnDefMod := fun _ => defMod,
        lexicalRibs := [], items := [ptrItem] }
    let ptrId : Ident := { name := ptrConstName, kind := .itemConst, ctxt := applyMark [] e .opaque }
    checkIdentTwoPass env ptrId =
      .ok { target := ptrTarget, semTy := .pubFnPtr, resolvedInMod := defMod } := by
  intro ptrItem env ptrId
  have hModEq : (defMod == defMod) = true := nat_beq_self defMod
  have hNameEq : (ptrConstName == ptrConstName) = true := nat_beq_self ptrConstName
  have hRes :
      resolveIdent env ptrId =
        .ok { target := ptrTarget, semTy := .pubFnPtr, resolvedInMod := defMod } := by
    dsimp only [resolveIdent, ptrId, applyMark, normalizeToMacros20, env,
                lookupItemInMod, ptrItem, isAccessibleFrom]
    rw [hModEq, hNameEq]
    rfl
  unfold checkIdentTwoPass
  rw [hRes]
  rfl

/-! ## Section 4: Expansion Fuel & `recursion_limit` Accounting (`compiler/rustc_expand`) -/

/-- Outcome of bounded macro expansion under `recursion_limit`. -/
inductive ExpandOutcome (α : Type) where
  | ok (val : α)
  | recursionLimitReached (atDepth : Nat)
  deriving DecidableEq, Repr

/-- Exact model of `rustc_expand::expand::MacroExpander::expand_invoc`
    (`compiler/rustc_expand/src/expand.rs:708,2139`) expanding recursive
    `count!(+^n)` starting from `depth = outerDepth + 1`:
    - Before each expansion, check `depth ≤ limit` (`value_within_limit`).
    - Base case `n = 0` (`count!()`) checks `depth ≤ limit` and returns `0`.
    - Inductive step `n + 1` checks `depth ≤ limit`, then recurses at `depth + 1`. -/
noncomputable def expandCountAt (limit : Nat) (depth : Nat) : Nat → ExpandOutcome Nat
  | 0 =>
    if depth ≤ limit then .ok 0
    else .recursionLimitReached depth
  | n + 1 =>
    if depth ≤ limit then
      match expandCountAt limit (depth + 1) n with
      | .ok v => .ok (v + 1)
      | .recursionLimitReached d => .recursionLimitReached d
    else
      .recursionLimitReached depth

/-- Expand `count!(+^n)` invoked inside `outerFrames` enclosing macro expansions
    (`outerFrames = 0` for top-level, `outerFrames = 2` inside `println!` -> `format_args_nl!`). -/
noncomputable def expandCount (limit : Nat) (outerFrames : Nat) (n : Nat) : ExpandOutcome Nat :=
  expandCountAt limit (outerFrames + 1) n

theorem nat_le_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c :=
  Nat.le_trans (Nat.le_add_right a b) h

/-- Exact closed-form soundness & completeness of `expandCountAt`:
    `expandCountAt limit depth n = .ok n` iff `depth + n ≤ limit`. -/
theorem expandCountAt_ok_iff (limit depth n : Nat) :
    expandCountAt limit depth n = .ok n ↔ depth + n ≤ limit := by
  induction n generalizing depth with
  | zero =>
    unfold expandCountAt
    by_cases h : depth ≤ limit
    · simp [h]
    · simp [h]
  | succ k ih =>
    unfold expandCountAt
    by_cases h : depth ≤ limit
    · simp only [h, ite_true]
      have hShift : depth + (k + 1) = (depth + 1) + k := by
        rw [Nat.add_comm k 1, ← Nat.add_assoc]
      cases hRec : expandCountAt limit (depth + 1) k with
      | ok v =>
        constructor
        · intro hOk
          injection hOk with hv
          have hkv : v = k := Nat.succ.inj hv
          subst hkv
          have hle := (ih (depth + 1)).mp hRec
          rw [hShift]
          exact hle
        · intro hLe
          rw [hShift] at hLe
          have hEq := (ih (depth + 1)).mpr hLe
          rw [hRec] at hEq
          injection hEq with hvk
          rw [hvk]
      | recursionLimitReached d =>
        constructor
        · intro hBad; cases hBad
        · intro hLe
          rw [hShift] at hLe
          have hEq := (ih (depth + 1)).mpr hLe
          rw [hRec] at hEq
          cases hEq
    · simp only [h, ite_false]
      constructor
      · intro hBad; cases hBad
      · intro hLe
        exact False.elim (h (nat_le_of_add_le hLe))

/-- Exact threshold law for `count!(+^n)` under `outerFrames` enclosing macro expansions:
    succeeds iff `outerFrames + 1 + n ≤ limit`. -/
theorem count_expansion_succeeds_iff (limit outerFrames n : Nat) :
    expandCount limit outerFrames n = .ok n ↔ outerFrames + 1 + n ≤ limit :=
  expandCountAt_ok_iff limit (outerFrames + 1) n

/-- Exact overflow depth law: whenever expansion starts at `depth ≤ limit + 1` and
    requires `depth + n > limit`, `expandCountAt` hits `recursionLimitReached (limit + 1)`. -/
theorem expandCountAt_overflow_exact (limit depth n : Nat)
    (hStart : depth ≤ limit + 1) (hOver : limit < depth + n) :
    expandCountAt limit depth n = .recursionLimitReached (limit + 1) := by
  induction n generalizing depth with
  | zero =>
    unfold expandCountAt
    have hGt : ¬ (depth ≤ limit) := Nat.not_le_of_gt hOver
    have hEq : depth = limit + 1 := Nat.le_antisymm hStart hOver
    simp only [hGt, ite_false]
    exact congrArg ExpandOutcome.recursionLimitReached hEq
  | succ k ih =>
    unfold expandCountAt
    by_cases h : depth ≤ limit
    · simp only [h, ite_true]
      have hNextStart : depth + 1 ≤ limit + 1 := Nat.add_le_add_right h 1
      have hShift : depth + (k + 1) = (depth + 1) + k := by
        rw [Nat.add_comm k 1, ← Nat.add_assoc]
      rw [hShift] at hOver
      rw [ih (depth + 1) hNextStart hOver]
    · simp only [h, ite_false]
      have hGt : limit + 1 ≤ depth := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
      have hEq : depth = limit + 1 := Nat.le_antisymm hStart hGt
      rw [hEq]

/-- Empirical boundary corollary (nested inside `println!` -> `format_args_nl!`,
    `outerFrames = 2`, default `limit = 128`): `n = 125` passes (`2 + 1 + 125 = 128`),
    `n = 126` overflows at `depth = 129`. -/
theorem count_nested_println_125_passes_126_overflows :
    expandCount 128 2 125 = .ok 125 ∧
    expandCount 128 2 126 = .recursionLimitReached 129 := by
  constructor
  · exact (count_expansion_succeeds_iff 128 2 125).mpr (Nat.le_refl 128)
  · exact expandCountAt_overflow_exact 128 3 126
      (Nat.le_of_ble_eq_true rfl) (Nat.le_refl 129)

/-- Empirical boundary corollary (top-level `let v = count!(...)`, `outerFrames = 0`,
    default `limit = 128`): `n = 127` passes (`0 + 1 + 127 = 128`), `n = 128` overflows at `129`. -/
theorem count_toplevel_127_passes_128_overflows :
    expandCount 128 0 127 = .ok 127 ∧
    expandCount 128 0 128 = .recursionLimitReached 129 := by
  constructor
  · exact (count_expansion_succeeds_iff 128 0 127).mpr (Nat.le_refl 128)
  · exact expandCountAt_overflow_exact 128 1 128
      (Nat.le_of_ble_eq_true rfl) (Nat.le_refl 129)

/-! ## Section 5: Pure vs. Host-Impure `proc_macro` Determinism & Sealed TCB Boundary -/

/-- Abstract host environment observable by an unsandboxed `proc_macro` dylib. -/
structure HostEnv where
  envNonce : Nat
  wallClockNs : Nat
  deriving DecidableEq, Repr

/-- Abstract token stream (e.g., list of interned token payloads). -/
abbrev TokenStream := List Nat

/-- Abstract compiled object artifact (e.g., byte sequence / hash digest). -/
abbrev ObjArtifact := List Nat

/-- A single-step macro expander (declarative or procedural) taking input tokens and host state. -/
abbrev MacroExpanderFn := TokenStream → HostEnv → Option TokenStream

/-- A macro expander is *pure* if its output tokens depend solely on input tokens,
    independent of host OS environment state. -/
noncomputable def IsPureExpander (f : MacroExpanderFn) : Prop :=
  ∀ (ts : TokenStream) (env1 env2 : HostEnv), f ts env1 = f ts env2

/-- Fuel-bounded iterative macro expansion pipeline (up to `fuel` rounds). -/
noncomputable def expandFuel (f : MacroExpanderFn) : Nat → TokenStream → HostEnv → ExpandOutcome TokenStream
  | 0, ts, _ => .ok ts
  | fuel + 1, ts, env =>
    match f ts env with
    | none => .ok ts
    | some ts' => expandFuel f fuel ts' env

/-- End-to-end compilation from source tokens through macro expansion and a deterministic backend. -/
noncomputable def compilePipeline (f : MacroExpanderFn) (backend : TokenStream → ObjArtifact)
    (fuel : Nat) (src : TokenStream) (env : HostEnv) : ExpandOutcome ObjArtifact :=
  match expandFuel f fuel src env with
  | .ok expanded => .ok (backend expanded)
  | .recursionLimitReached d => .recursionLimitReached d

/-- **Theorem 4 (Pure Macro Expansion & Build Determinism):**
    For any pure macro expander `f`, any deterministic backend `backend`, any fuel
    bound `fuel`, any source token stream `src`, and any two host environments
    `env1` and `env2`:
    1. Multi-step macro expansion produces identical expanded token streams.
    2. End-to-end compilation produces bit-identical object artifacts. -/
theorem pure_macro_expansion_deterministic
    (f : MacroExpanderFn) (hPure : IsPureExpander f)
    (backend : TokenStream → ObjArtifact)
    (fuel : Nat) (src : TokenStream) (env1 env2 : HostEnv) :
    expandFuel f fuel src env1 = expandFuel f fuel src env2 ∧
    compilePipeline f backend fuel src env1 = compilePipeline f backend fuel src env2 := by
  have hExp : ∀ (n : Nat) (ts : TokenStream),
      expandFuel f n ts env1 = expandFuel f n ts env2 := by
    intro n
    induction n with
    | zero =>
      intro ts
      rfl
    | succ k ih =>
      intro ts
      unfold expandFuel
      rw [hPure ts env1 env2]
      cases f ts env2 with
      | none => rfl
      | some ts' => exact ih ts'
  have hMain := hExp fuel src
  constructor
  · exact hMain
  · unfold compilePipeline
    rw [hMain]

/-! ## Section 5b: Edition 2021 vs. 2024 `expr`/`expr_2021` Fragment Drift (`rustc_ast/src/token.rs`) -/

/-- Rust edition relevant to `NtExprKind` fragment resolution. -/
inductive Edition where
  | ed2015
  | ed2018
  | ed2021
  | ed2024
  deriving DecidableEq, Repr

/-- Exact model of `rustc_ast::token::NtExprKind` (`compiler/rustc_ast/src/token.rs:1137-1145`). -/
inductive NtExprKind where
  | expr2024
  | expr2021 (inferred : Bool)
  deriving DecidableEq, Repr

/-- Exact model of `NonterminalKind::from_symbol` for `expr` and `expr_2021`, parameterized
    by the *definition-site* span edition (`compiler/rustc_ast/src/token.rs:1185-1192`). -/
inductive ExprSpecToken where
  | symExpr
  | symExpr2021
  deriving DecidableEq, Repr

noncomputable def resolveNtExprKind (spec : ExprSpecToken) (defEdition : Edition) : NtExprKind :=
  match spec with
  | .symExpr =>
    match defEdition with
    | .ed2024 => .expr2024
    | _ => .expr2021 true
  | .symExpr2021 => .expr2021 false

/-- Leading token classes distinguishing `NtExprKind::Expr` vs. `NtExprKind::Expr2021`
    in `Parser::nonterminal_may_begin_with` (`compiler/rustc_parse/src/parser/nonterminal.rs:45-64`). -/
inductive ExprLeadToken where
  | regularExpr   -- e.g., integer literal, ident, path, block
  | kwConst       -- `const { ... }`
  | kwUnderscore  -- `_` (assignee expression)
  | kwLet         -- `let` (excluded in both 2021 and 2024)
  deriving DecidableEq, Repr

noncomputable def exprMayBeginWith (kind : NtExprKind) (tok : ExprLeadToken) : Bool :=
  match kind, tok with
  | .expr2021 _, .regularExpr => true
  | .expr2021 _, .kwConst => false
  | .expr2021 _, .kwUnderscore => false
  | .expr2021 _, .kwLet => false
  | .expr2024, .regularExpr => true
  | .expr2024, .kwConst => true
  | .expr2024, .kwUnderscore => true
  | .expr2024, .kwLet => false

/-- Edition 2024 `$e:expr` is a strict superset of `$e:expr_2021`: every leading token
    accepted by `Expr2021` is accepted by `Expr2024`, while `const` and `_` are newly
    accepted only under `Expr2024` (and governed solely by `defEdition`, independent of
    `callEdition`). -/
theorem edition2024_expr_strict_superset_of_expr2021 :
    (∀ (tok : ExprLeadToken) (inf : Bool),
      exprMayBeginWith (.expr2021 inf) tok = true →
      exprMayBeginWith .expr2024 tok = true) ∧
    (exprMayBeginWith (resolveNtExprKind .symExpr .ed2021) .kwConst = false ∧
     exprMayBeginWith (resolveNtExprKind .symExpr .ed2024) .kwConst = true ∧
     exprMayBeginWith (resolveNtExprKind .symExpr .ed2021) .kwUnderscore = false ∧
     exprMayBeginWith (resolveNtExprKind .symExpr .ed2024) .kwUnderscore = true ∧
     exprMayBeginWith (resolveNtExprKind .symExpr2021 .ed2024) .kwConst = false ∧
     exprMayBeginWith (resolveNtExprKind .symExpr2021 .ed2024) .kwUnderscore = false) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro tok inf h
  cases tok <;> cases h <;> rfl

/-! ## Section 6: Three Constructive Counterexamples -/

/-- **Counterexample 1 (`Transparent` / `Span::call_site()` Captures Caller Local):**
    A `proc_macro` emitting `Ident::new("x", Span::call_site())` (mark `(e, .transparent)`)
    resolves directly to the caller's local variable `x` (`target = 77`), breaking
    lexical hygiene. -/
theorem ce1_transparent_call_site_captures_caller_local :
    ∃ (env : ResolveEnv) (e : ExpnId) (xName : SymbolId) (callerTarget : TargetId),
      resolveIdent env { name := xName, kind := .localVar, ctxt := applyMark [] e .transparent } =
        .ok { target := callerTarget, semTy := .pubScalar, resolvedInMod := env.callSiteMod } ∧
      resolveIdent env { name := xName, kind := .localVar, ctxt := applyMark [] e .semiOpaque } =
        .err (.notFoundE0425 xName) ∧
      resolveIdent env { name := xName, kind := .localVar, ctxt := applyMark [] e .opaque } =
        .err (.notFoundE0425 xName) := by
  let xName : SymbolId := 1
  let callerTarget : TargetId := 77
  let e : ExpnId := 1
  let callerEntry : LexicalEntry :=
    { name := xName, kind := .localVar, normCtxt := [], target := callerTarget }
  let env : ResolveEnv :=
    { callSiteMod := 0, expnDefMod := fun _ => 1,
      lexicalRibs := [callerEntry], items := [] }
  exact ⟨env, e, xName, callerTarget, rfl, rfl, rfl⟩

/-- **Counterexample 2 (`SemiOpaque` Item Hijacked by Caller Shadow):**
    A `macro_rules!` or `Span::mixed_site()` macro defined in `defMod = 1` (with
    `pub fn helper() -> u32 { 10 }`) invokes unqualified `helper()`. When called
    from `callMod = 0` where caller defines `fn helper() -> u32 { 999 }`, `SemiOpaque`
    resolves `helper` to the caller's shadow (`target = 999`), whereas `Opaque`
    (`decl_macro`) resolves `helper` to the def-site item (`target = 10`). -/
theorem ce2_semi_opaque_item_hijacked_by_caller_shadow :
    ∃ (env : ResolveEnv) (e : ExpnId) (helperName : SymbolId)
      (defTarget callerTarget : TargetId),
      defTarget ≠ callerTarget ∧
      resolveIdent env { name := helperName, kind := .itemFn, ctxt := applyMark [] e .semiOpaque } =
        .ok { target := callerTarget, semTy := .pubScalar, resolvedInMod := 0 } ∧
      resolveIdent env { name := helperName, kind := .itemFn, ctxt := applyMark [] e .opaque } =
        .ok { target := defTarget, semTy := .pubScalar, resolvedInMod := 1 } := by
  let helperName : SymbolId := 2
  let defTarget : TargetId := 10
  let callerTarget : TargetId := 999
  let e : ExpnId := 1
  let defItem : ItemEntry :=
    { ownerMod := 1, name := helperName, kind := .itemFn,
      vis := .pubVis, semTy := .pubScalar, target := defTarget }
  let callerItem : ItemEntry :=
    { ownerMod := 0, name := helperName, kind := .itemFn,
      vis := .pubVis, semTy := .pubScalar, target := callerTarget }
  let env : ResolveEnv :=
    { callSiteMod := 0, expnDefMod := fun _ => 1,
      lexicalRibs := [], items := [defItem, callerItem] }
  refine ⟨env, e, helperName, defTarget, callerTarget, ?_, rfl, rfl⟩
  exact (by decide : (10 : Nat) ≠ 999)

/-- **Counterexample 3 (Host-Impure `proc_macro` Breaks Build Determinism):**
    An unsandboxed `proc_macro` reading `HostEnv.envNonce` produces divergent
    expanded token streams and divergent compiled `.o` artifacts from identical
    Rust source tokens across two host environments differing only in `envNonce`. -/
theorem ce3_impure_proc_macro_breaks_build_determinism :
    ∃ (f : MacroExpanderFn) (backend : TokenStream → ObjArtifact)
      (src : TokenStream) (env1 env2 : HostEnv),
      ¬ IsPureExpander f ∧
      compilePipeline f backend 1 src env1 ≠ compilePipeline f backend 1 src env2 := by
  let f : MacroExpanderFn := fun _ts env => some [env.envNonce]
  let backend : TokenStream → ObjArtifact := fun ts => ts
  let src : TokenStream := [0]
  let env1 : HostEnv := { envNonce := 111111, wallClockNs := 1000 }
  let env2 : HostEnv := { envNonce := 222222, wallClockNs := 1000 }
  refine ⟨f, backend, src, env1, env2, ?_, ?_⟩
  · intro hPure
    have hEq := hPure src env1 env2
    cases hEq
  · intro hEq
    cases hEq

end MacroHygieneAndTransparencySoundness
