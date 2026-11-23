/-
  Kernel-Checked Mechanization of `rustc` Macro Hygiene, `SyntaxContext` /
  `Transparency` Resolution, Procedural-Macro Span Modes, `$crate` Resolution,
  and Edition 2024 `:expr` vs. `:expr_2021` Fragment Specifier Semantics.

  Primary-source anchors (`rust-lang/rust` HEAD `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`
  and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
  - `compiler/rustc_span/src/hygiene.rs`: `SyntaxContext`, `Transparency`,
    `Transparency::fallback`, `normalize_to_macros_2_0`, `normalize_to_macro_rules`,
    `apply_mark`, `adjust`, `hygienic_eq`.
  - `compiler/rustc_span/src/lib.rs`: `Span::{with_def_site_ctxt, with_call_site_ctxt, with_mixed_site_ctxt}`.
  - `compiler/rustc_expand/src/mbe/{macro_rules.rs, transcribe.rs}`:
    `MacroRulesMacroExpander`, `Marker::mark_span`, `is_in_follow`.
  - `compiler/rustc_resolve/src/{lib.rs, ident.rs, late.rs}`:
    `IdentKey`, `Macros20NormalizedSyntaxContext`, `resolve_crate_root`,
    `resolve_ident_in_lexical_scope`, `fresh_binding`, `resolve_label`.
  - `compiler/rustc_middle/src/ty/{mod.rs, assoc.rs}` &
    `compiler/rustc_hir_typeck/src/{expr.rs, method/probe.rs}`:
    `adjust_ident_and_get_scope`, `find_by_ident_and_namespace`, `find_adt_field`.
  - `compiler/rustc_ast/src/token.rs` & `compiler/rustc_parse/src/parser/nonterminal.rs`:
    `NtExprKind::{Expr, Expr2021}`, `NonterminalKind::from_symbol`,
    `Parser::nonterminal_may_begin_with`.

  Purity invariants (no `sorry`, no `Classical.choice`, no `omega`, no `bv_decide`,
  no `native_decide`, no `partial def`, no `let rec`, no `._unsafe_rec`, no `deriving`):
  every definition is marked `noncomputable def` and uses structural `match` rather than
  `Decidable` `if-then-else` so kernel reduction holds definitionally.
-/

namespace RustcMacroHygiene

/-! ## Part 1: Identifiers, Transparency Lattice, and Expansion Metadata -/

/-- Symbol identifier (interned `rustc_span::Symbol`). -/
abbrev SymId := Nat

/-- Crate identifier (`rustc_span::def_id::CrateNum`). -/
abbrev CrateId := Nat

/-- Module identifier (`rustc_span::def_id::ModId`). -/
abbrev ModId := Nat

/-- Macro definition identifier (`rustc_hir::def_id::DefId`). -/
abbrev MacroDefId := Nat

/-- Lexical local value (`Val`) for runtime alpha-invariance theorems. -/
abbrev Val := Nat

/-- `rustc_span::hygiene::Transparency` (`compiler/rustc_span/src/hygiene.rs:180-194`).
    Constructor `.opaq` represents `Transparency::Opaque` (avoiding Lean's `opaque` keyword). -/
inductive Transparency where
  | transparent : Transparency
  | semiOpaque : Transparency
  | opaq : Transparency

/-- Constructive boolean equality on `Transparency` (no `deriving`). -/
noncomputable def Transparency.beq : Transparency → Transparency → Bool
  | .transparent, .transparent => true
  | .semiOpaque, .semiOpaque => true
  | .opaq, .opaq => true
  | _, _ => false

/-- Lattice rank of `Transparency` (`0 < 1 < 2`). -/
noncomputable def Transparency.rank : Transparency → Nat
  | .transparent => 0
  | .semiOpaque => 1
  | .opaq => 2

/-- Lattice order `t₁ ≤ t₂` on `Transparency` (`Transparent ≤ SemiOpaque ≤ Opaque`). -/
noncomputable def Transparency.le : Transparency → Transparency → Bool
  | .transparent, _ => true
  | .semiOpaque, .transparent => false
  | .semiOpaque, _ => true
  | .opaq, .opaq => true
  | .opaq, _ => false

/-- Lattice join `t₁ ⊔ t₂` (more opaque). -/
noncomputable def Transparency.join : Transparency → Transparency → Transparency
  | .opaq, _ => .opaq
  | _, .opaq => .opaq
  | .semiOpaque, _ => .semiOpaque
  | _, .semiOpaque => .semiOpaque
  | .transparent, .transparent => .transparent

/-- Lattice meet `t₁ ⊓ t₂` (more transparent). -/
noncomputable def Transparency.meet : Transparency → Transparency → Transparency
  | .transparent, _ => .transparent
  | _, .transparent => .transparent
  | .semiOpaque, _ => .semiOpaque
  | _, .semiOpaque => .semiOpaque
  | .opaq, .opaq => .opaq

/-- `Transparency::fallback(macro_rules: bool)` (`compiler/rustc_span/src/hygiene.rs:196-200`). -/
noncomputable def Transparency.fallback (macroRules : Bool) : Transparency :=
  match macroRules with
  | true => .semiOpaque
  | false => .opaq

theorem transparency_beq_refl (t : Transparency) : Transparency.beq t t = true := by
  cases t <;> rfl

theorem transparency_beq_eq {t₁ t₂ : Transparency} :
    Transparency.beq t₁ t₂ = true → t₁ = t₂ := by
  cases t₁ <;> cases t₂ <;> intro h <;> first | rfl | exact Bool.noConfusion h

theorem transparency_le_refl (t : Transparency) : Transparency.le t t = true := by
  cases t <;> rfl

theorem transparency_le_antisym {t₁ t₂ : Transparency} :
    Transparency.le t₁ t₂ = true → Transparency.le t₂ t₁ = true → t₁ = t₂ := by
  cases t₁ <;> cases t₂ <;> intro h₁ h₂ <;>
    first | rfl | exact False.elim (Bool.noConfusion h₁) | exact False.elim (Bool.noConfusion h₂)

theorem transparency_le_trans {t₁ t₂ t₃ : Transparency} :
    Transparency.le t₁ t₂ = true → Transparency.le t₂ t₃ = true → Transparency.le t₁ t₃ = true := by
  cases t₁ <;> cases t₂ <;> cases t₃ <;> intro h₁ h₂ <;>
    first | rfl | exact False.elim (Bool.noConfusion h₁) | exact False.elim (Bool.noConfusion h₂)

theorem transparency_join_comm (t₁ t₂ : Transparency) :
    Transparency.join t₁ t₂ = Transparency.join t₂ t₁ := by
  cases t₁ <;> cases t₂ <;> rfl

theorem transparency_meet_comm (t₁ t₂ : Transparency) :
    Transparency.meet t₁ t₂ = Transparency.meet t₂ t₁ := by
  cases t₁ <;> cases t₂ <;> rfl

theorem transparency_fallback_macro_rules :
    Transparency.fallback true = .semiOpaque := rfl

theorem transparency_fallback_decl_macro :
    Transparency.fallback false = .opaq := rfl

/-- `rustc_span::hygiene::ExpnId` (`krate`, `local_id`). -/
structure ExpnId where
  krate : CrateId
  localId : Nat

/-- `ExpnId::root()` (`compiler/rustc_span/src/hygiene.rs:280-282`). -/
noncomputable def ExpnId.root : ExpnId := ⟨0, 0⟩

/-- Constructive boolean equality on `ExpnId`. -/
noncomputable def ExpnId.beq (a b : ExpnId) : Bool :=
  Nat.beq a.krate b.krate && Nat.beq a.localId b.localId

theorem expnId_beq_refl (e : ExpnId) : ExpnId.beq e e = true := by
  cases e with
  | mk k l =>
    unfold ExpnId.beq
    rw [Nat.beq_refl k, Nat.beq_refl l]
    rfl

theorem expnId_beq_eq {a b : ExpnId} : ExpnId.beq a b = true → a = b := by
  cases a with
  | mk k₁ l₁ =>
    cases b with
    | mk k₂ l₂ =>
      unfold ExpnId.beq
      intro h
      cases hk : Nat.beq k₁ k₂ with
      | false => rw [hk] at h; exact False.elim (Bool.noConfusion h)
      | true =>
        cases hl : Nat.beq l₁ l₂ with
        | false => rw [hk, hl] at h; exact False.elim (Bool.noConfusion h)
        | true =>
          have ek := Nat.eq_of_beq_eq_true hk
          have el := Nat.eq_of_beq_eq_true hl
          subst ek; subst el; rfl

theorem expnId_beq_comm (a b : ExpnId) : ExpnId.beq a b = ExpnId.beq b a := by
  cases a with
  | mk k₁ l₁ =>
    cases b with
    | mk k₂ l₂ =>
      unfold ExpnId.beq
      cases hk : Nat.beq k₁ k₂ with
      | false =>
        have hk2 : Nat.beq k₂ k₁ = false := by
          cases h2 : Nat.beq k₂ k₁ with
          | false => rfl
          | true =>
            have eqk := Nat.eq_of_beq_eq_true h2
            subst eqk
            rw [Nat.beq_refl] at hk
            exact False.elim (Bool.noConfusion hk)
        rw [hk2]
        rfl
      | true =>
        have eqk := Nat.eq_of_beq_eq_true hk
        subst eqk
        rw [Nat.beq_refl]
        cases hl : Nat.beq l₁ l₂ with
        | false =>
          have hl2 : Nat.beq l₂ l₁ = false := by
            cases h2 : Nat.beq l₂ l₁ with
            | false => rfl
            | true =>
              have eql := Nat.eq_of_beq_eq_true h2
              subst eql
              rw [Nat.beq_refl] at hl
              exact False.elim (Bool.noConfusion hl)
          rw [hl2]
        | true =>
          have eql := Nat.eq_of_beq_eq_true hl
          subst eql
          rw [Nat.beq_refl]

theorem expnId_eq_iff_beq (a b : ExpnId) : a = b ↔ ExpnId.beq a b = true :=
  ⟨fun h => h ▸ expnId_beq_refl a, expnId_beq_eq⟩

/-- `rustc_span::edition::Edition`. -/
inductive Edition where
  | ed2015 : Edition
  | ed2018 : Edition
  | ed2021 : Edition
  | ed2024 : Edition

/-- Constructive equality on `Edition`. -/
noncomputable def Edition.beq : Edition → Edition → Bool
  | .ed2015, .ed2015 => true
  | .ed2018, .ed2018 => true
  | .ed2021, .ed2021 => true
  | .ed2024, .ed2024 => true
  | _, _ => false

/-- `Edition::at_least_rust_2021`. -/
noncomputable def Edition.atLeast2021 : Edition → Bool
  | .ed2015 => false
  | .ed2018 => false
  | .ed2021 => true
  | .ed2024 => true

/-- `Edition::at_least_rust_2024`. -/
noncomputable def Edition.atLeast2024 : Edition → Bool
  | .ed2015 => false
  | .ed2018 => false
  | .ed2021 => false
  | .ed2024 => true

/-- Macro invocation kind (`compiler/rustc_span/src/hygiene.rs:1267-1303`). -/
inductive ExpnKind where
  | root : ExpnKind
  | macroBang : SymId → ExpnKind
  | macroAttr : SymId → ExpnKind
  | macroDerive : SymId → ExpnKind
  | desugaring : ExpnKind

/-- Subset of `rustc_span::hygiene::ExpnData` governing resolution & editions. -/
structure ExpnData where
  kind : ExpnKind
  parent : ExpnId
  edition : Edition
  defCrate : CrateId
  parentModule : Option ModId
  macroDefId : Option MacroDefId

/-! ## Part 2: `SyntaxContext` Mark Chain, Normalization, and Lattice Laws -/

/--
  Inductive mark-stack representation of `rustc_span::hygiene::SyntaxContext`
  (`compiler/rustc_span/src/hygiene.rs:53-103`).
  `push parent expn trans` corresponds to
  `SyntaxContextData { parent, outer_expn := expn, outer_transparency := trans, ... }`.
-/
inductive SyntaxContext where
  | root : SyntaxContext
  | push (parent : SyntaxContext) (expn : ExpnId) (trans : Transparency) : SyntaxContext

/-- Constructive boolean equality on `SyntaxContext`. -/
noncomputable def SyntaxContext.beq : SyntaxContext → SyntaxContext → Bool
  | .root, .root => true
  | .push p₁ e₁ t₁, .push p₂ e₂ t₂ =>
    SyntaxContext.beq p₁ p₂ && ExpnId.beq e₁ e₂ && Transparency.beq t₁ t₂
  | _, _ => false

theorem syntaxContext_beq_refl (c : SyntaxContext) : SyntaxContext.beq c c = true := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    unfold SyntaxContext.beq
    rw [ih, expnId_beq_refl, transparency_beq_refl]
    rfl

theorem syntaxContext_beq_eq {c₁ c₂ : SyntaxContext} :
    SyntaxContext.beq c₁ c₂ = true → c₁ = c₂ := by
  induction c₁ generalizing c₂ with
  | root =>
    cases c₂ with
    | root => intro _; rfl
    | push _ _ _ => intro h; exact False.elim (Bool.noConfusion h)
  | push p₁ e₁ t₁ ih =>
    cases c₂ with
    | root => intro h; exact False.elim (Bool.noConfusion h)
    | push p₂ e₂ t₂ =>
      unfold SyntaxContext.beq
      intro h
      cases hp : SyntaxContext.beq p₁ p₂ with
      | false => rw [hp] at h; exact False.elim (Bool.noConfusion h)
      | true =>
        cases he : ExpnId.beq e₁ e₂ with
        | false => rw [hp, he] at h; exact False.elim (Bool.noConfusion h)
        | true =>
          cases ht : Transparency.beq t₁ t₂ with
          | false => rw [hp, he, ht] at h; exact False.elim (Bool.noConfusion h)
          | true =>
            have ep := ih hp
            have ee := expnId_beq_eq he
            have et := transparency_beq_eq ht
            subst ep; subst ee; subst et; rfl

theorem syntaxContext_eq_iff_beq (c₁ c₂ : SyntaxContext) :
    c₁ = c₂ ↔ SyntaxContext.beq c₁ c₂ = true :=
  ⟨fun h => h ▸ syntaxContext_beq_refl c₁, syntaxContext_beq_eq⟩

/-- Check whether a `SyntaxContext` is `root`. -/
noncomputable def SyntaxContext.isRoot : SyntaxContext → Bool
  | .root => true
  | .push _ _ _ => false

/-- Outermost mark `(outer_expn, outer_transparency)` (`hygiene.rs:616-619`). -/
noncomputable def SyntaxContext.outerMark : SyntaxContext → ExpnId × Transparency
  | .root => (ExpnId.root, .opaq)
  | .push _ e t => (e, t)

/-- Outermost expansion ID (`hygiene.rs:610-612`). -/
noncomputable def SyntaxContext.outerExpn (c : SyntaxContext) : ExpnId :=
  (c.outerMark).1

/-- Parent context (`hygiene.rs:622-624`). -/
noncomputable def SyntaxContext.parentCtxt : SyntaxContext → SyntaxContext
  | .root => .root
  | .push p _ _ => p

/--
  `SyntaxContext::normalize_to_macros_2_0` (`compiler/rustc_span/src/hygiene.rs:599-601, 757-770`):
  filters away ALL `Transparent` and `SemiOpaque` marks, keeping ONLY `Opaque` (`.opaq`) marks.
-/
noncomputable def SyntaxContext.normalizeToMacros20 : SyntaxContext → SyntaxContext
  | .root => .root
  | .push p _ .transparent => p.normalizeToMacros20
  | .push p _ .semiOpaque => p.normalizeToMacros20
  | .push p e .opaq => .push p.normalizeToMacros20 e .opaq

/--
  `SyntaxContext::normalize_to_macro_rules` (`compiler/rustc_span/src/hygiene.rs:604-606, 757-770`):
  filters away ONLY `Transparent` marks, keeping BOTH `SemiOpaque` and `Opaque` (`.opaq`) marks.
-/
noncomputable def SyntaxContext.normalizeToMacroRules : SyntaxContext → SyntaxContext
  | .root => .root
  | .push p _ .transparent => p.normalizeToMacroRules
  | .push p e .semiOpaque => .push p.normalizeToMacroRules e .semiOpaque
  | .push p e .opaq => .push p.normalizeToMacroRules e .opaq

/-- Append a mark list `(e₁, t₁) :: ...` onto a base context (`alloc_ctxt` chain). -/
noncomputable def SyntaxContext.pushList (base : SyntaxContext) : List (ExpnId × Transparency) → SyntaxContext
  | [] => base
  | (e, t) :: rest => (SyntaxContext.push base e t).pushList rest

/-- Extract ordered list of marks from innermost to outermost (`hygiene.rs:632-641`). -/
noncomputable def SyntaxContext.marksAux : SyntaxContext → List (ExpnId × Transparency) → List (ExpnId × Transparency)
  | .root, acc => acc
  | .push p e t, acc => p.marksAux ((e, t) :: acc)

noncomputable def SyntaxContext.marks (c : SyntaxContext) : List (ExpnId × Transparency) :=
  c.marksAux []

/--
  `SyntaxContext::apply_mark` (`compiler/rustc_span/src/hygiene.rs:688-723`):
  - If `trans == .opaq`, directly pushes `(expn, .opaq)` onto `ctxt`.
  - Otherwise inspects the invocation call site's normalized context (`normalize_to_macros_2_0`
    for `semiOpaque`, `normalize_to_macro_rules` for `transparent`).
  - If that normalized call-site context is `.root`, pushes `(expn, trans)` onto `ctxt`.
  - Otherwise splices `ctxt.marks` atop the normalized call-site context before pushing `(expn, trans)`,
    preserving macros 2.0 hygiene when a legacy macro is invoked inside a macros 2.0 definition.
-/
noncomputable def SyntaxContext.applyMark
    (ctxt : SyntaxContext)
    (expn : ExpnId)
    (trans : Transparency)
    (callSiteCtxt : SyntaxContext) : SyntaxContext :=
  match trans with
  | .opaq => .push ctxt expn .opaq
  | .semiOpaque =>
    let normCall := callSiteCtxt.normalizeToMacros20
    match normCall with
    | .root => .push ctxt expn .semiOpaque
    | _ => .push (normCall.pushList ctxt.marks) expn .semiOpaque
  | .transparent =>
    let normCall := callSiteCtxt.normalizeToMacroRules
    match normCall with
    | .root => .push ctxt expn .transparent
    | _ => .push (normCall.pushList ctxt.marks) expn .transparent

/-- Span construction helpers (`compiler/rustc_span/src/lib.rs:1294-1315`). -/
noncomputable def withDefSiteCtxt (expn : ExpnId) : SyntaxContext :=
  .push .root expn .opaq

noncomputable def withCallSiteCtxt (expn : ExpnId) : SyntaxContext :=
  .push .root expn .transparent

noncomputable def withMixedSiteCtxt (expn : ExpnId) : SyntaxContext :=
  .push .root expn .semiOpaque

/--
  `SyntaxContext::adjust` (`compiler/rustc_span/src/hygiene.rs:680-686`):
  pops marks while `!isDescendant expnId ctxt.outerExpn`, returning the adjusted
  context and the last removed `ExpnId` (if any, used for privacy checking).
-/
noncomputable def SyntaxContext.adjustAux
    (isDescendant : ExpnId → ExpnId → Bool)
    (expnId : ExpnId)
    (lastRemoved : Option ExpnId) : SyntaxContext → SyntaxContext × Option ExpnId
  | .root => (.root, lastRemoved)
  | .push p e t =>
    match isDescendant expnId e with
    | true => (.push p e t, lastRemoved)
    | false => SyntaxContext.adjustAux isDescendant expnId (some e) p

noncomputable def SyntaxContext.adjust
    (isDescendant : ExpnId → ExpnId → Bool)
    (ctxt : SyntaxContext)
    (expnId : ExpnId) : SyntaxContext × Option ExpnId :=
  SyntaxContext.adjustAux isDescendant expnId none ctxt

/--
  `SyntaxContext::hygienic_eq` (`compiler/rustc_span/src/hygiene.rs:1019-1025`):
  normalizes `self` to macros 2.0, adjusts to `expnId`, and compares to `other`
  normalized to macros 2.0.
-/
noncomputable def SyntaxContext.hygienicEq
    (isDescendant : ExpnId → ExpnId → Bool)
    (c₁ c₂ : SyntaxContext)
    (expnId : ExpnId) : Bool :=
  let c₁Adj := (c₁.normalizeToMacros20.adjust isDescendant expnId).1
  SyntaxContext.beq c₁Adj c₂.normalizeToMacros20

/-! ### Algebraic Laws of `normalizeToMacros20` and `normalizeToMacroRules` -/

theorem normalizeToMacros20_idempotent (c : SyntaxContext) :
    c.normalizeToMacros20.normalizeToMacros20 = c.normalizeToMacros20 := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacros20, ih]

theorem normalizeToMacroRules_idempotent (c : SyntaxContext) :
    c.normalizeToMacroRules.normalizeToMacroRules = c.normalizeToMacroRules := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacroRules, ih]

theorem normalizeToMacros20_of_macroRules (c : SyntaxContext) :
    c.normalizeToMacroRules.normalizeToMacros20 = c.normalizeToMacros20 := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacroRules, SyntaxContext.normalizeToMacros20, ih]

theorem normalizeToMacroRules_of_macros20 (c : SyntaxContext) :
    c.normalizeToMacros20.normalizeToMacroRules = c.normalizeToMacros20 := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacros20, SyntaxContext.normalizeToMacroRules, ih]

/-- Predicate expressing that every mark in `c` has `Opaque` (`.opaq`) transparency. -/
noncomputable def SyntaxContext.allOpaque : SyntaxContext → Bool
  | .root => true
  | .push p _ .opaq => p.allOpaque
  | .push _ _ _ => false

/-- Predicate expressing that every mark in `c` has `SemiOpaque` or `Opaque` transparency. -/
noncomputable def SyntaxContext.noTransparent : SyntaxContext → Bool
  | .root => true
  | .push _ _ .transparent => false
  | .push p _ .semiOpaque => p.noTransparent
  | .push p _ .opaq => p.noTransparent

theorem normalizeToMacros20_allOpaque (c : SyntaxContext) :
    c.normalizeToMacros20.allOpaque = true := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacros20, SyntaxContext.allOpaque, ih]

theorem normalizeToMacroRules_noTransparent (c : SyntaxContext) :
    c.normalizeToMacroRules.noTransparent = true := by
  induction c with
  | root => rfl
  | push _ e t ih =>
    cases t <;> simp [SyntaxContext.normalizeToMacroRules, SyntaxContext.noTransparent, ih]

theorem allOpaque_implies_noTransparent {c : SyntaxContext} :
    c.allOpaque = true → c.noTransparent = true := by
  induction c with
  | root => intro _; rfl
  | push _ _ t ih =>
    cases t with
    | transparent => intro h; exact False.elim (Bool.noConfusion h)
    | semiOpaque => intro h; exact False.elim (Bool.noConfusion h)
    | opaq =>
      intro h
      exact ih h

theorem normalizeToMacroRules_preserves_semiOpaque (c : SyntaxContext) (e : ExpnId) :
    (SyntaxContext.push c e .semiOpaque).normalizeToMacroRules ≠ .root := by
  intro h
  cases h

theorem normalizeToMacros20_erases_semiOpaque (c : SyntaxContext) (e : ExpnId) :
    (SyntaxContext.push c e .semiOpaque).normalizeToMacros20 = c.normalizeToMacros20 := rfl

theorem normalizeToMacros20_erases_transparent (c : SyntaxContext) (e : ExpnId) :
    (SyntaxContext.push c e .transparent).normalizeToMacros20 = c.normalizeToMacros20 := rfl

theorem normalizeToMacroRules_erases_transparent (c : SyntaxContext) (e : ExpnId) :
    (SyntaxContext.push c e .transparent).normalizeToMacroRules = c.normalizeToMacroRules := rfl

theorem normalizeToMacros20_preserves_opaque (c : SyntaxContext) (e : ExpnId) :
    (SyntaxContext.push c e .opaq).normalizeToMacros20 ≠ .root := by
  intro h
  cases h

theorem semiOpaque_marks_distinct_invocations
    (c₁ c₂ : SyntaxContext) {e₁ e₂ : ExpnId} (hne : e₁ ≠ e₂) :
    (SyntaxContext.push c₁ e₁ .semiOpaque).normalizeToMacroRules ≠
    (SyntaxContext.push c₂ e₂ .semiOpaque).normalizeToMacroRules := by
  intro h
  unfold SyntaxContext.normalizeToMacroRules at h
  injection h with _ he _
  exact hne he

theorem opaque_marks_distinct_invocations
    (c₁ c₂ : SyntaxContext) {e₁ e₂ : ExpnId} (hne : e₁ ≠ e₂) :
    (SyntaxContext.push c₁ e₁ .opaq).normalizeToMacros20 ≠
    (SyntaxContext.push c₂ e₂ .opaq).normalizeToMacros20 := by
  intro h
  unfold SyntaxContext.normalizeToMacros20 at h
  injection h with _ he _
  exact hne he

/-! ## Part 3: Name-Role Normalization, Local Alpha-Invariance, `$crate`, and Method Privacy -/

/-- Identifier with hygiene context (`rustc_span::symbol::Ident`). -/
structure Ident where
  name : SymId
  ctxt : SyntaxContext

/-- Constructive boolean equality on `Ident`. -/
noncomputable def Ident.beq (a b : Ident) : Bool :=
  Nat.beq a.name b.name && SyntaxContext.beq a.ctxt b.ctxt

theorem ident_beq_refl (a : Ident) : Ident.beq a a = true := by
  cases a with
  | mk n _ =>
    unfold Ident.beq
    rw [syntaxContext_beq_refl, Nat.beq_refl n]
    rfl

theorem ident_beq_eq {a b : Ident} : Ident.beq a b = true → a = b := by
  cases a with
  | mk n₁ c₁ =>
    cases b with
    | mk n₂ c₂ =>
      unfold Ident.beq
      intro h
      cases hn : Nat.beq n₁ n₂ with
      | false => rw [hn] at h; exact False.elim (Bool.noConfusion h)
      | true =>
        cases hc : SyntaxContext.beq c₁ c₂ with
        | false => rw [hn, hc] at h; exact False.elim (Bool.noConfusion h)
        | true =>
          have en := Nat.eq_of_beq_eq_true hn
          have ec := syntaxContext_beq_eq hc
          subst en; subst ec; rfl

theorem ident_beq_false_of_ne {a b : Ident} (h : a ≠ b) : Ident.beq a b = false := by
  cases heq : Ident.beq a b with
  | false => rfl
  | true => exact False.elim (h (ident_beq_eq heq))

/--
  Name resolution role governing which normalization `rustc_resolve` / `rustc_hir_typeck`
  applies (`compiler/rustc_resolve/src/{ident.rs, late.rs, lib.rs}`,
  `compiler/rustc_hir_typeck/src/expr.rs`, `compiler/rustc_middle/src/ty/assoc.rs`).
-/
inductive NameRole where
  | localVar : NameRole     -- `fresh_binding` / lexical non-param rib (`normalize_to_macro_rules`)
  | label : NameRole        -- `resolve_label` / `with_resolved_label` (`normalize_to_macro_rules`)
  | dollarCrate : NameRole  -- `resolve_crate_root` (`normalize_to_macro_rules`)
  | itemDecl : NameRole     -- `IdentKey::new` / `TypeNS` (`normalize_to_macros_2_0`)
  | methodCall : NameRole   -- `find_by_ident_and_namespace` / `hygienic_eq` (`normalize_to_macros_2_0`)
  | fieldAccess : NameRole  -- `find_adt_field` (`normalize_to_macros_2_0`)

/-- Exact `rustc` normalization per `NameRole`. -/
noncomputable def Ident.normalizeForRole (role : NameRole) (id : Ident) : Ident :=
  match role with
  | .localVar | .label | .dollarCrate => ⟨id.name, id.ctxt.normalizeToMacroRules⟩
  | .itemDecl | .methodCall | .fieldAccess => ⟨id.name, id.ctxt.normalizeToMacros20⟩

/-- Helper predicate: `ctxt` has at least one `SemiOpaque` or `Opaque` mark. -/
noncomputable def SyntaxContext.hasNonTransparentMark : SyntaxContext → Bool
  | .root => false
  | .push _ _ .semiOpaque => true
  | .push _ _ .opaq => true
  | .push p _ .transparent => p.hasNonTransparentMark

theorem hasNonTransparentMark_implies_macroRules_ne_root {c : SyntaxContext} :
    c.hasNonTransparentMark = true → c.normalizeToMacroRules ≠ .root := by
  induction c with
  | root => intro h; exact False.elim (Bool.noConfusion h)
  | push p _ t ih =>
    cases t with
    | transparent =>
      intro h hEq
      exact ih h hEq
    | semiOpaque =>
      intro _ hEq
      cases hEq
    | opaq =>
      intro _ hEq
      cases hEq

theorem hasNonTransparentMark_separates_from_root
    (n₁ n₂ : SymId) {c : SyntaxContext} (hc : c.hasNonTransparentMark = true) :
    Ident.normalizeForRole .localVar ⟨n₁, c⟩ ≠
    Ident.normalizeForRole .localVar ⟨n₂, .root⟩ := by
  intro h
  unfold Ident.normalizeForRole at h
  injection h with _ hctxt
  exact hasNonTransparentMark_implies_macroRules_ne_root hc hctxt

theorem hasNonTransparentMark_label_separates_from_root
    (n₁ n₂ : SymId) {c : SyntaxContext} (hc : c.hasNonTransparentMark = true) :
    Ident.normalizeForRole .label ⟨n₁, c⟩ ≠
    Ident.normalizeForRole .label ⟨n₂, .root⟩ := by
  intro h
  unfold Ident.normalizeForRole at h
  injection h with _ hctxt
  exact hasNonTransparentMark_implies_macroRules_ne_root hc hctxt

/-! ### Lexical Rib Environment & Expression Evaluation for Alpha-Invariance -/

/-- A lexical rib stack mapping macro-rules-normalized identifiers to values. -/
abbrev RibEnv := List (Ident × Val)

/-- Bind a fresh local variable using `normalizeForRole .localVar` (`fresh_binding`, `late.rs:4697`). -/
noncomputable def RibEnv.bindLocal (ρ : RibEnv) (id : Ident) (v : Val) : RibEnv :=
  (id.normalizeForRole .localVar, v) :: ρ

/-- Lookup a local identifier using `normalizeForRole .localVar` (`ident.rs:328, 338`). -/
noncomputable def RibEnv.lookupLocal (id : Ident) : RibEnv → Option Val
  | [] => none
  | (k, v) :: rest =>
    match Ident.beq (id.normalizeForRole .localVar) k with
    | true => some v
    | false => RibEnv.lookupLocal id rest

/-- Unfolding helper for `RibEnv.lookupLocal` on a cons cell (keeps tail un-unfolded). -/
theorem RibEnv.lookupLocal_cons (id k : Ident) (v : Val) (rest : RibEnv) :
    RibEnv.lookupLocal id ((k, v) :: rest) =
    match Ident.beq (id.normalizeForRole .localVar) k with
    | true => some v
    | false => RibEnv.lookupLocal id rest := rfl

/-- Small operational expression AST for local-binding hygiene proofs. -/
inductive LocalExpr where
  | lit : Val → LocalExpr
  | var : Ident → LocalExpr
  | letIn : Ident → LocalExpr → LocalExpr → LocalExpr
  | add : LocalExpr → LocalExpr → LocalExpr

/-- Predicate asserting that every variable occurrence in `e` has root syntax context. -/
noncomputable def LocalExpr.allRootCtxt : LocalExpr → Bool
  | .lit _ => true
  | .var id => id.ctxt.isRoot
  | .letIn _ rhs body => rhs.allRootCtxt && body.allRootCtxt
  | .add a b => a.allRootCtxt && b.allRootCtxt

/-- Operational semantics for `LocalExpr` in lexical `RibEnv`. -/
noncomputable def evalLocalExpr (ρ : RibEnv) : LocalExpr → Option Val
  | .lit v => some v
  | .var id => RibEnv.lookupLocal id ρ
  | .letIn id rhs body =>
    match evalLocalExpr ρ rhs with
    | none => none
    | some v => evalLocalExpr (ρ.bindLocal id v) body
  | .add a b =>
    match evalLocalExpr ρ a, evalLocalExpr ρ b with
    | some va, some vb => some (va + vb)
    | _, _ => none

theorem lookupLocal_bind_macro_noncapture
    (ρ : RibEnv) (xMacro xCaller : Ident) (v : Val)
    (hMacro : xMacro.ctxt.hasNonTransparentMark = true)
    (hCaller : xCaller.ctxt.isRoot = true) :
    RibEnv.lookupLocal xCaller (ρ.bindLocal xMacro v) = RibEnv.lookupLocal xCaller ρ := by
  cases xCaller with
  | mk nCaller cCaller =>
    cases cCaller with
    | push _ _ _ => cases hCaller
    | root =>
      cases xMacro with
      | mk nMacro cMacro =>
        unfold RibEnv.bindLocal
        have hne :
            (⟨nCaller, .root⟩ : Ident).normalizeForRole .localVar ≠
            (⟨nMacro, cMacro⟩ : Ident).normalizeForRole .localVar := by
          intro heq
          exact hasNonTransparentMark_separates_from_root nMacro nCaller hMacro heq.symm
        rw [RibEnv.lookupLocal_cons, ident_beq_false_of_ne hne]

theorem lookupLocal_bind_caller_noncapture
    (ρ : RibEnv) (xMacro xCaller : Ident) (v : Val)
    (hMacro : xMacro.ctxt.hasNonTransparentMark = true)
    (hCaller : xCaller.ctxt.isRoot = true) :
    RibEnv.lookupLocal xMacro (ρ.bindLocal xCaller v) = RibEnv.lookupLocal xMacro ρ := by
  cases xCaller with
  | mk nCaller cCaller =>
    cases cCaller with
    | push _ _ _ => cases hCaller
    | root =>
      cases xMacro with
      | mk nMacro cMacro =>
        unfold RibEnv.bindLocal
        have hne :
            (⟨nMacro, cMacro⟩ : Ident).normalizeForRole .localVar ≠
            (⟨nCaller, .root⟩ : Ident).normalizeForRole .localVar :=
          hasNonTransparentMark_separates_from_root nMacro nCaller hMacro
        rw [RibEnv.lookupLocal_cons, ident_beq_false_of_ne hne]

/-- Agreement of two environments on all root-context identifiers. -/
noncomputable def agreesOnRoot (ρ₁ ρ₂ : RibEnv) : Prop :=
  ∀ id : Ident, id.ctxt = .root → RibEnv.lookupLocal id ρ₁ = RibEnv.lookupLocal id ρ₂

theorem agreesOnRoot_bind_caller {ρ₁ ρ₂ : RibEnv} (h : agreesOnRoot ρ₁ ρ₂)
    (id : Ident) (v : Val) :
    agreesOnRoot (ρ₁.bindLocal id v) (ρ₂.bindLocal id v) := by
  intro q hq
  unfold RibEnv.bindLocal RibEnv.lookupLocal
  cases Ident.beq (q.normalizeForRole .localVar) (id.normalizeForRole .localVar) with
  | true => rfl
  | false => exact h q hq

theorem agreesOnRoot_bind_macro (ρ : RibEnv) (xMacro : Ident) (v : Val)
    (hMacro : xMacro.ctxt.hasNonTransparentMark = true) :
    agreesOnRoot (ρ.bindLocal xMacro v) ρ := by
  intro q hq
  have hroot : q.ctxt.isRoot = true := by rw [hq]; rfl
  exact lookupLocal_bind_macro_noncapture ρ xMacro q v hMacro hroot

theorem evalLocalExpr_agreesOnRoot {e : LocalExpr} :
    e.allRootCtxt = true →
    ∀ {ρ₁ ρ₂ : RibEnv}, agreesOnRoot ρ₁ ρ₂ → evalLocalExpr ρ₁ e = evalLocalExpr ρ₂ e := by
  induction e with
  | lit _ =>
    intro _ _ _ _
    rfl
  | var id =>
    intro hid ρ₁ ρ₂ hAg
    unfold LocalExpr.allRootCtxt at hid
    cases hctxt : id.ctxt with
    | push _ _ _ => rw [hctxt] at hid; exact False.elim (Bool.noConfusion hid)
    | root => exact hAg id hctxt
  | letIn id rhs body ihr ihb =>
    intro hAll ρ₁ ρ₂ hAg
    unfold LocalExpr.allRootCtxt at hAll
    cases hr : rhs.allRootCtxt with
    | false => rw [hr] at hAll; exact False.elim (Bool.noConfusion hAll)
    | true =>
      cases hb : body.allRootCtxt with
      | false => rw [hr, hb] at hAll; exact False.elim (Bool.noConfusion hAll)
      | true =>
        unfold evalLocalExpr
        rw [ihr hr hAg]
        cases evalLocalExpr ρ₂ rhs with
        | none => rfl
        | some v => exact ihb hb (agreesOnRoot_bind_caller hAg id v)
  | add a b iha ihb =>
    intro hAll ρ₁ ρ₂ hAg
    unfold LocalExpr.allRootCtxt at hAll
    cases ha : a.allRootCtxt with
    | false => rw [ha] at hAll; exact False.elim (Bool.noConfusion hAll)
    | true =>
      cases hb : b.allRootCtxt with
      | false => rw [ha, hb] at hAll; exact False.elim (Bool.noConfusion hAll)
      | true =>
        unfold evalLocalExpr
        rw [iha ha hAg, ihb hb hAg]

/--
  **Main Theorem (Local-Variable Alpha-Invariance / Non-Capture Under `SemiOpaque` & `Opaque`)**:
  Evaluating any caller expression `e_caller` (with `allRootCtxt = true`) under an environment
  extended with ANY macro-introduced `SemiOpaque` (`macro_rules!` / `Span::mixed_site()`) or
  `Opaque` (`macro` 2.0 / `Span::def_site()`) local binding `(xMacro, v)` yields the exact same
  evaluation result as evaluating `e_caller` in the unextended caller environment `ρ`.
-/
theorem caller_eval_invariant_under_macro_local
    (ρ : RibEnv) (xMacro : Ident) (v : Val) (eCaller : LocalExpr)
    (hMacro : xMacro.ctxt.hasNonTransparentMark = true)
    (hCaller : eCaller.allRootCtxt = true) :
    evalLocalExpr (ρ.bindLocal xMacro v) eCaller = evalLocalExpr ρ eCaller :=
  evalLocalExpr_agreesOnRoot hCaller (agreesOnRoot_bind_macro ρ xMacro v hMacro)

/-- Dual preservation: extending caller environment never captures macro-introduced locals (`agreesOnCtxt`). -/
noncomputable def agreesOnCtxt (c : SyntaxContext) (ρ₁ ρ₂ : RibEnv) : Prop :=
  ∀ id : Ident, id.ctxt = c → RibEnv.lookupLocal id ρ₁ = RibEnv.lookupLocal id ρ₂

theorem agreesOnCtxt_bind_caller (ρ : RibEnv) (c : SyntaxContext) (xCaller : Ident) (v : Val)
    (hc : c.hasNonTransparentMark = true) (hCaller : xCaller.ctxt = .root) :
    agreesOnCtxt c (ρ.bindLocal xCaller v) ρ := by
  intro q hq
  have hMacro : q.ctxt.hasNonTransparentMark = true := by rw [hq]; exact hc
  have hRoot : xCaller.ctxt.isRoot = true := by rw [hCaller]; rfl
  exact lookupLocal_bind_caller_noncapture ρ q xCaller v hMacro hRoot

theorem lookupLocal_bind_different_semiOpaque_invocations
    (ρ : RibEnv) (n₁ n₂ : SymId) {e₁ e₂ : ExpnId} (hne : e₁ ≠ e₂) (v : Val) :
    RibEnv.lookupLocal ⟨n₁, .push .root e₁ .semiOpaque⟩
      (ρ.bindLocal ⟨n₂, .push .root e₂ .semiOpaque⟩ v) =
    RibEnv.lookupLocal ⟨n₁, .push .root e₁ .semiOpaque⟩ ρ := by
  unfold RibEnv.bindLocal
  have hneId :
      (⟨n₁, .push .root e₁ .semiOpaque⟩ : Ident).normalizeForRole .localVar ≠
      (⟨n₂, .push .root e₂ .semiOpaque⟩ : Ident).normalizeForRole .localVar := by
    intro h
    unfold Ident.normalizeForRole at h
    injection h with _ hc
    exact semiOpaque_marks_distinct_invocations .root .root hne hc
  rw [RibEnv.lookupLocal_cons, ident_beq_false_of_ne hneId]

/-! ### `$crate` Resolution Semantics (`rustc_resolve/src/lib.rs:2375-2446`) -/

/-- Expansion metadata table mapping `ExpnId` to `ExpnData`. -/
abbrev ExpnTable := ExpnId → Option ExpnData

/-- Trailing `SemiOpaque` scan used by `scanDollarCrateMarksRev` (top-level `noncomputable def`). -/
noncomputable def consumeSemiMarks (acc : Option ExpnId) : List (ExpnId × Transparency) → Option ExpnId
  | (m, .semiOpaque) :: rest => consumeSemiMarks (some m) rest
  | _ => acc

/-- Leading `Opaque` scan followed by `consumeSemiMarks` (`lib.rs:2393-2413`). -/
noncomputable def consumeOpaqueMarks (acc : Option ExpnId) : List (ExpnId × Transparency) → Option ExpnId
  | [] => acc
  | (m, .opaq) :: rest => consumeOpaqueMarks (some m) rest
  | rest => consumeSemiMarks acc rest

/-- Reverse mark scan matching `Resolver::resolve_crate_root` (`rustc_resolve/src/lib.rs:2390-2419`). -/
noncomputable def scanDollarCrateMarksRev (marksRev : List (ExpnId × Transparency)) : Option ExpnId :=
  consumeOpaqueMarks none marksRev

/-- Direct outermost-to-innermost `$crate` scan on `SyntaxContext`. -/
noncomputable def dollarCrateMarkAux :
    Option ExpnId → Bool → SyntaxContext → Option ExpnId
  | acc, _, .root => acc
  | _, true, .push p m .opaq => dollarCrateMarkAux (some m) true p
  | acc, false, .push _ _ .opaq => acc
  | _, _, .push p m .semiOpaque => dollarCrateMarkAux (some m) false p
  | acc, _, .push _ _ .transparent => acc

/-- Exact `$crate` expansion-mark resolution on a `macro_rules`-normalized `SyntaxContext`. -/
noncomputable def resolveDollarCrateMark (ctxt : SyntaxContext) : Option ExpnId :=
  dollarCrateMarkAux none true ctxt.normalizeToMacroRules

/-- Resolve `$crate` to defining crate (`lib.rs:2425-2437`). -/
noncomputable def resolveCrateRoot
    (tbl : ExpnTable) (localCrate : CrateId) (ctxt : SyntaxContext) : CrateId :=
  match resolveDollarCrateMark ctxt with
  | none => localCrate
  | some expn =>
    match tbl expn with
    | none => localCrate
    | some data => data.defCrate

theorem resolveDollarCrateMark_semiOpaque (c : SyntaxContext) (e : ExpnId)
    (hc : c = .root) :
    resolveDollarCrateMark (.push c e .semiOpaque) = some e := by
  subst hc
  rfl

theorem resolveDollarCrateMark_transparent_ignored (c : SyntaxContext) (e : ExpnId) :
    resolveDollarCrateMark (.push c e .transparent) = resolveDollarCrateMark c := rfl

theorem resolveDollarCrateMark_opaque_alone (e : ExpnId) :
    resolveDollarCrateMark (.push .root e .opaq) = some e := rfl

theorem resolveCrateRoot_bypasses_caller_shadow
    (tbl : ExpnTable) (localCrate defCrate : CrateId) (e : ExpnId) (data : ExpnData)
    (hData : tbl e = some data) (hDef : data.defCrate = defCrate) :
    resolveCrateRoot tbl localCrate (.push .root e .semiOpaque) = defCrate := by
  unfold resolveCrateRoot resolveDollarCrateMark
  simp [SyntaxContext.normalizeToMacroRules, dollarCrateMarkAux, hData, hDef]

theorem resolveCrateRoot_transparent_wrapper_invariant
    (tbl : ExpnTable) (localCrate : CrateId) (c : SyntaxContext) (eWrap : ExpnId) :
    resolveCrateRoot tbl localCrate (.push c eWrap .transparent) =
    resolveCrateRoot tbl localCrate c := rfl

/-! ### Module Item Table, Visibility, and Method Privacy Scope (`adjust_ident_and_get_scope`) -/

inductive Visibility where
  | pub : Visibility
  | priv (modId : ModId) : Visibility

noncomputable def Visibility.isAccessibleFrom (vis : Visibility) (scope : ModId) : Bool :=
  match vis with
  | .pub => true
  | .priv ownerMod => Nat.beq ownerMod scope

/-- Module item entry keyed by `IdentKey` (`normalizeForRole .itemDecl`, `lib.rs:619-621`). -/
structure ItemEntry where
  key : Ident
  vis : Visibility
  itemId : Nat

abbrev ModuleItems := List ItemEntry

noncomputable def insertItem (tbl : ModuleItems) (id : Ident) (vis : Visibility) (itemId : Nat) : ModuleItems :=
  ⟨id.normalizeForRole .itemDecl, vis, itemId⟩ :: tbl

noncomputable def lookupItem (id : Ident) : ModuleItems → Option ItemEntry
  | [] => none
  | entry :: rest =>
    match Ident.beq (id.normalizeForRole .itemDecl) entry.key with
    | true => some entry
    | false => lookupItem id rest

/--
  Method lookup + privacy resolution modeling `AssocItems::find_by_ident_and_namespace`
  (`assoc.rs:336-346`) + `adjust_ident_and_get_scope` (`ty/mod.rs:2344-2356`).
-/
structure MethodEntry where
  key : Ident
  vis : Visibility
  implExpn : ExpnId
  methodId : Nat

noncomputable def resolveMethodAccess
    (isDescendant : ExpnId → ExpnId → Bool)
    (expnTable : ExpnTable)
    (callerMod : ModId)
    (callSiteName : Ident)
    (m : MethodEntry) : Bool :=
  let nameOk := SyntaxContext.hygienicEq isDescendant callSiteName.ctxt m.key.ctxt m.implExpn &&
                Nat.beq callSiteName.name m.key.name
  let optActualExpn := (callSiteName.ctxt.normalizeToMacros20.adjust isDescendant m.implExpn).2
  let defScope :=
    match optActualExpn with
    | some actualExpn =>
      match expnTable actualExpn with
      | some data =>
        match data.parentModule with
        | some pm => pm
        | none => callerMod
      | none => callerMod
    | none => callerMod
  nameOk && m.vis.isAccessibleFrom defScope

/-! ### Concrete 3-Tier Separation Witnesses (`Transparent` vs `SemiOpaque` vs `Opaque`) -/

noncomputable def symX : SymId := 1
noncomputable def symStruct : SymId := 2
noncomputable def symMeth : SymId := 3
noncomputable def symHelper : SymId := 4
noncomputable def expn1 : ExpnId := ⟨1, 1⟩
noncomputable def expn2 : ExpnId := ⟨1, 2⟩
noncomputable def callerMod : ModId := 10
noncomputable def macroMod : ModId := 20
noncomputable def rootDescendant (a b : ExpnId) : Bool :=
  ExpnId.beq b ExpnId.root || ExpnId.beq a b

noncomputable def witnessExpnTable : ExpnTable
  | ⟨1, 1⟩ => some ⟨.macroBang symHelper, .root, .ed2024, 1, some macroMod, some 1⟩
  | _ => none

/--
  **Separation Witness 1 (`Transparent` vs `SemiOpaque`):**
  With caller `x = 42` (`root`), a `Transparent` (`Span::call_site()`) reference to `x`
  captures caller `42`, whereas a `SemiOpaque` (`macro_rules!` / `Span::mixed_site()`)
  reference to `x` fails (`none`, `E0425`) and isolates a macro-introduced `x = 10` (`MS=10`).
-/
theorem sep_transparent_captures_caller_semiOpaque_isolates :
    let callerEnv := RibEnv.bindLocal [] ⟨symX, .root⟩ 42
    let macroEnv := RibEnv.bindLocal callerEnv ⟨symX, withMixedSiteCtxt expn1⟩ 10
    (RibEnv.lookupLocal ⟨symX, withCallSiteCtxt expn1⟩ callerEnv = some 42) ∧
    (RibEnv.lookupLocal ⟨symX, withMixedSiteCtxt expn1⟩ callerEnv = none) ∧
    (RibEnv.lookupLocal ⟨symX, withMixedSiteCtxt expn1⟩ macroEnv = some 10) ∧
    (RibEnv.lookupLocal ⟨symX, .root⟩ macroEnv = some 42) :=
  ⟨rfl, rfl, rfl, rfl⟩

/--
  **Separation Witness 2 (`SemiOpaque` vs `Opaque` Item Leakage):**
  A struct item declared inside a `SemiOpaque` macro (`macro_rules!` / `Span::mixed_site()`)
  normalizes to `.root` and leaks to caller lookup (`some`), whereas the identical item declared
  inside an `Opaque` macro (`macro` 2.0 / `Span::def_site()`) retains its `expn1` mark and is
  isolated from caller lookup (`none`, `E0425`).
-/
theorem sep_semiOpaque_leaks_item_opaque_isolates :
    let semiTable := insertItem [] ⟨symStruct, withMixedSiteCtxt expn1⟩ .pub 100
    let opaqueTable := insertItem [] ⟨symStruct, withDefSiteCtxt expn1⟩ .pub 100
    (lookupItem ⟨symStruct, .root⟩ semiTable = some ⟨⟨symStruct, .root⟩, .pub, 100⟩) ∧
    (lookupItem ⟨symStruct, .root⟩ opaqueTable = none) :=
  ⟨rfl, rfl⟩

/--
  **Separation Witness 3 (`SemiOpaque` vs `Opaque` Private Method Scope, `E0624`):**
  Invoking a private method defined on a root-context caller struct (`callerMod = 10`) from a
  macro defined in `macroMod = 20`:
  - `SemiOpaque` (`macro_rules!` / `Span::mixed_site()`) strips the mark in `normalize_to_macros_2_0`,
    resolving privacy in `callerMod` (`true`).
  - `Opaque` (`macro` 2.0 / `Span::def_site()`) retains the `expn1` mark in `adjust`, resolving
    privacy in `macroMod = 20 ≠ 10` (`false`, `E0624`).
  - A `pub` method succeeds under BOTH (`true`).
-/
theorem sep_semiOpaque_vs_opaque_method_privacy :
    let privMethod : MethodEntry := ⟨⟨symMeth, .root⟩, .priv callerMod, ExpnId.root, 1⟩
    let pubMethod : MethodEntry := ⟨⟨symMeth, .root⟩, .pub, ExpnId.root, 2⟩
    (resolveMethodAccess rootDescendant witnessExpnTable callerMod ⟨symMeth, withMixedSiteCtxt expn1⟩ privMethod = true) ∧
    (resolveMethodAccess rootDescendant witnessExpnTable callerMod ⟨symMeth, withDefSiteCtxt expn1⟩ privMethod = false) ∧
    (resolveMethodAccess rootDescendant witnessExpnTable callerMod ⟨symMeth, withDefSiteCtxt expn1⟩ pubMethod = true) :=
  ⟨rfl, rfl, rfl⟩

/--
  **Witness 4 (`$crate` Visibility Orthogonality):**
  Cross-crate `$crate` resolution identifies crate `1` regardless of caller shadowing, yet
  private items (`Visibility.priv macroMod`) remain inaccessible from `callerMod ≠ macroMod` (`E0603`).
-/
theorem dollarCrate_resolves_crate_but_respects_visibility :
    let vis := Visibility.priv macroMod
    (resolveCrateRoot witnessExpnTable 2 (withMixedSiteCtxt expn1) = 1) ∧
    (vis.isAccessibleFrom callerMod = false) :=
  ⟨rfl, rfl⟩

/-! ## Part 4: Edition 2024 `:expr` vs. `:expr_2021` Fragment Grammar & Follow-Set Determinism -/

/-- `rustc_ast::token::NtExprKind` (`compiler/rustc_ast/src/token.rs:1137-1145`). -/
inductive NtExprKind where
  | expr2024 : NtExprKind
  | expr2021 (inferred : Bool) : NtExprKind

/-- `rustc_ast::token::NtPatKind` (`compiler/rustc_ast/src/token.rs:1127-1134`). -/
inductive NtPatKind where
  | patWithOr : NtPatKind
  | patParam (inferred : Bool) : NtPatKind

/-- `rustc_ast::token::NonterminalKind` (`compiler/rustc_ast/src/token.rs:1149-1164`).
    Constructor `.metaAttr` models `NonterminalKind::Meta` (avoiding Lean's `meta` keyword). -/
inductive NonterminalKind where
  | item : NonterminalKind
  | block : NonterminalKind
  | stmt : NonterminalKind
  | pat : NtPatKind → NonterminalKind
  | expr : NtExprKind → NonterminalKind
  | ty : NonterminalKind
  | ident : NonterminalKind
  | lifetime : NonterminalKind
  | literal : NonterminalKind
  | metaAttr : NonterminalKind
  | path : NonterminalKind
  | vis : NonterminalKind
  | tt : NonterminalKind

/-- Surface fragment specifier symbol written in `macro_rules!` matchers (`quoted.rs:16-18`). -/
inductive FragSpecSym where
  | exprSym | expr2021Sym | patSym | patParamSym
  | blockSym | stmtSym | tySym | identSym
  | lifetimeSym | literalSym | metaSym | pathSym
  | visSym | itemSym | ttSym

/--
  `NonterminalKind::from_symbol(sym, || def_edition)`
  (`compiler/rustc_ast/src/token.rs:1169-1204`, `compiler/rustc_expand/src/mbe/quoted.rs:154-165`):
  uses the **definition-site** edition (`defEdition`).
-/
noncomputable def resolveFragKind (defEdition : Edition) : FragSpecSym → NonterminalKind
  | .exprSym =>
    match defEdition.atLeast2024 with
    | true => .expr .expr2024
    | false => .expr (.expr2021 true)
  | .expr2021Sym => .expr (.expr2021 false)
  | .patSym =>
    match defEdition.atLeast2021 with
    | true => .pat .patWithOr
    | false => .pat (.patParam true)
  | .patParamSym => .pat (.patParam false)
  | .blockSym => .block
  | .stmtSym => .stmt
  | .tySym => .ty
  | .identSym => .ident
  | .lifetimeSym => .lifetime
  | .literalSym => .literal
  | .metaSym => .metaAttr
  | .pathSym => .path
  | .visSym => .vis
  | .itemSym => .item
  | .ttSym => .tt

/-- Abstract lexical token set covering expression starts, follow-set tokens, and delimiters. -/
inductive Tok where
  | ident : Tok
  | kwLet : Tok
  | kwConst : Tok
  | kwUnderscore : Tok
  | kwIf : Tok
  | kwLoop : Tok
  | kwMatch : Tok
  | kwAsync : Tok
  | kwUnsafe : Tok
  | kwTrue : Tok
  | kwPriv : Tok
  | kwAs : Tok
  | kwWhere : Tok
  | kwIn : Tok
  | litInt : Tok
  | openParen : Tok
  | closeParen : Tok
  | openBrace : Tok
  | closeBrace : Tok
  | openBracket : Tok
  | closeBracket : Tok
  | bang : Tok
  | minus : Tok
  | star : Tok
  | amp : Tok
  | pipe : Tok
  | pathSep : Tok
  | lifetime : Tok
  | pound : Tok
  | fatArrow : Tok
  | comma : Tok
  | semi : Tok
  | colon : Tok
  | eq : Tok
  | gt : Tok
  | shr : Tok
  | plus : Tok
  | eof : Tok

noncomputable def Tok.isCloseDelim : Tok → Bool
  | .closeParen | .closeBrace | .closeBracket => true
  | _ => false

/--
  `Token::can_begin_expr` + `ident_can_begin_expr`
  (`compiler/rustc_ast/src/token.rs:312-349, 680-711`).
  Crucially: `kwLet = true`, `kwConst = true`, and `kwUnderscore = false` (reserved ident).
-/
noncomputable def Tok.canBeginExpr : Tok → Bool
  | .ident | .kwLet | .kwConst | .kwIf | .kwLoop | .kwMatch | .kwAsync | .kwUnsafe
  | .kwTrue | .litInt | .openParen | .openBrace | .openBracket | .bang | .minus
  | .star | .amp | .pipe | .pathSep | .lifetime | .pound => true
  | _ => false

noncomputable def Tok.canBeginType : Tok → Bool
  | .ident | .kwUnderscore | .kwUnsafe | .openParen | .openBracket
  | .bang | .star | .amp | .pathSep | .lifetime => true
  | _ => false

noncomputable def Tok.canBeginPattern (pk : NtPatKind) : Tok → Bool
  | .ident | .kwTrue | .litInt | .openParen | .openBracket | .amp | .minus | .pathSep => true
  | .pipe => match pk with | .patWithOr => true | .patParam _ => false
  | _ => false

noncomputable def Tok.isKwLet : Tok → Bool
  | .kwLet => true
  | _ => false

noncomputable def Tok.isKwConst : Tok → Bool
  | .kwConst => true
  | _ => false

noncomputable def Tok.isKwUnderscore : Tok → Bool
  | .kwUnderscore => true
  | _ => false

/--
  `Parser::nonterminal_may_begin_with` (`compiler/rustc_parse/src/parser/nonterminal.rs:22-116`):
  exact encoding of `Expr2021` vs. `Expr` (`expr2024`) admission rules.
-/
noncomputable def nonterminalMayBeginWith (kind : NonterminalKind) (t : Tok) : Bool :=
  match kind with
  | .expr (.expr2021 _) => t.canBeginExpr && !t.isKwLet && !t.isKwConst
  | .expr .expr2024 => (t.canBeginExpr || t.isKwUnderscore) && !t.isKwLet
  | .ty => t.canBeginType
  | .ident =>
    match t with
    | .ident | .kwLet | .kwConst | .kwIf | .kwLoop | .kwMatch | .kwAsync
    | .kwUnsafe | .kwTrue | .kwPriv | .kwAs | .kwWhere | .kwIn => true
    | _ => false
  | .literal =>
    match t with | .litInt | .kwTrue | .minus => true | _ => false
  | .vis =>
    match t with | .comma | .ident => true | _ => t.canBeginType
  | .block =>
    match t with | .openBrace | .lifetime => true | _ => false
  | .path | .metaAttr =>
    match t with | .pathSep | .ident => true | _ => false
  | .pat pk => t.canBeginPattern pk
  | .lifetime =>
    match t with | .lifetime => true | _ => false
  | .tt | .item | .stmt =>
    (match t with | .eof => false | _ => true) && !t.isCloseDelim

/--
  `is_in_follow` (`compiler/rustc_expand/src/mbe/macro_rules.rs:1729-1850`):
  valid follow tokens immediately after a macro nonterminal in a `macro_rules!` matcher.
-/
noncomputable def isInFollow (kind : NonterminalKind) (t : Tok) : Bool :=
  match t.isCloseDelim with
  | true => true
  | false =>
    match kind with
    | .item | .block | .ident | .lifetime | .literal | .metaAttr | .tt => true
    | .stmt | .expr _ =>
      match t with | .fatArrow | .comma | .semi => true | _ => false
    | .pat (.patParam _) =>
      match t with | .fatArrow | .comma | .eq | .pipe | .kwIf | .kwIn => true | _ => false
    | .pat .patWithOr =>
      match t with | .fatArrow | .comma | .eq | .kwIf | .kwIn => true | _ => false
    | .path | .ty =>
      match t with
      | .openBrace | .openBracket | .comma | .fatArrow | .colon | .eq | .gt | .shr
      | .semi | .pipe | .kwAs | .kwWhere => true
      | _ => false
    | .vis =>
      match t with
      | .comma | .ident => true
      | .kwPriv => false
      | _ => t.canBeginType

/--
  Structured expression-token-stream grammar for top-level fragment admission:
  captures the distinction between top-level `const { ... }` / `_` vs. parenthesized `(const { ... })`.
-/
inductive ExprTerm where
  | constBlock : ExprTerm → ExprTerm
  | underscore : ExprTerm
  | parenthesized : ExprTerm → ExprTerm
  | letExpr : ExprTerm → ExprTerm
  | lit : Nat → ExprTerm
  | var : SymId → ExprTerm
  | binAdd : ExprTerm → ExprTerm → ExprTerm

/-- First token of an `ExprTerm`. -/
noncomputable def ExprTerm.firstTok : ExprTerm → Tok
  | .constBlock _ => .kwConst
  | .underscore => .kwUnderscore
  | .parenthesized _ => .openParen
  | .letExpr _ => .kwLet
  | .lit _ => .litInt
  | .var _ => .ident
  | .binAdd lhs _ => lhs.firstTok

/-- Well-formedness of an `ExprTerm` as a valid Rust expression (excluding bare `let`). -/
noncomputable def ExprTerm.isValidExpr : ExprTerm → Bool
  | .constBlock body => body.isValidExpr
  | .underscore => true
  | .parenthesized inner => inner.isValidExpr
  | .letExpr _ => false
  | .lit _ => true
  | .var _ => true
  | .binAdd a b => a.isValidExpr && b.isValidExpr

/-- Matcher acceptance predicate for `:expr` / `:expr_2021` (`nonterminal_may_begin_with` + valid expr). -/
noncomputable def acceptsExprFragment (ek : NtExprKind) (e : ExprTerm) : Bool :=
  nonterminalMayBeginWith (.expr ek) e.firstTok && e.isValidExpr

/-! ### Mechanized Edition 2024 `:expr` vs. `:expr_2021` Theorems -/

/--
  **Theorem (Token-Level Sublanguage Inclusion `Expr2021 ⊆ Expr2024`):**
  Every leading token admitted by `Expr2021` is also admitted by Edition 2024 `Expr`.
-/
theorem expr2021_tok_subset_expr2024 (b : Bool) (t : Tok) :
    nonterminalMayBeginWith (.expr (.expr2021 b)) t = true →
    nonterminalMayBeginWith (.expr .expr2024) t = true := by
  cases t <;> intro h <;> first | rfl | exact False.elim (Bool.noConfusion h)

/--
  **Theorem (Grammar-Level Sublanguage Inclusion `Expr2021 ⊆ Expr2024`):**
  Every `ExprTerm` accepted by `Expr2021` (including Edition 2021 `$e:expr` and Edition 2024
  `$e:expr_2021`) is also accepted by Edition 2024 `$e:expr`.
-/
theorem expr2021_subset_expr2024 (b : Bool) (e : ExprTerm) :
    acceptsExprFragment (.expr2021 b) e = true →
    acceptsExprFragment .expr2024 e = true := by
  unfold acceptsExprFragment
  intro h
  cases hf : nonterminalMayBeginWith (.expr (.expr2021 b)) e.firstTok with
  | false => rw [hf] at h; exact False.elim (Bool.noConfusion h)
  | true =>
    cases hv : e.isValidExpr with
    | false => rw [hf, hv] at h; exact False.elim (Bool.noConfusion h)
    | true =>
      rw [expr2021_tok_subset_expr2024 b e.firstTok hf]
      rfl

/--
  **Theorem (Strict Separation Witnesses `Expr2021 ⊊ Expr2024`):**
  1. `const { 1 }` (`ExprTerm.constBlock`) is accepted by `expr2024` (`= true`) and rejected by `expr2021` (`= false`).
  2. `_` (`ExprTerm.underscore`) is accepted by `expr2024` (`= true`) and rejected by `expr2021` (`= false`).
  3. Parenthesized `(const { 1 })` (`ExprTerm.parenthesized (.constBlock ...)`) is accepted by BOTH (`= true`).
  4. `let` (`ExprTerm.letExpr`) is rejected by BOTH (`= false`, `nonterminal.rs:48, 63`).
-/
theorem expr2021_strict_sublanguage_witnesses (b : Bool) :
    (acceptsExprFragment .expr2024 (.constBlock (.lit 3)) = true) ∧
    (acceptsExprFragment (.expr2021 b) (.constBlock (.lit 3)) = false) ∧
    (acceptsExprFragment .expr2024 .underscore = true) ∧
    (acceptsExprFragment (.expr2021 b) .underscore = false) ∧
    (acceptsExprFragment (.expr2021 b) (.parenthesized (.constBlock (.lit 3))) = true) ∧
    (acceptsExprFragment .expr2024 (.letExpr (.lit 1)) = false) ∧
    (acceptsExprFragment (.expr2021 b) (.letExpr (.lit 1)) = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
  **Theorem (Definition-Site Edition Capture, `quoted.rs:154-164` & `token.rs:1185-1192`):**
  - A macro defined in Edition 2021 using `$e:expr` compiles to `.expr (.expr2021 true)` and thus
    rejects `const { ... }` and `_` regardless of caller edition.
  - A macro defined in Edition 2024 using `$e:expr` compiles to `.expr .expr2024` and admits both.
  - `$e:expr_2021` compiles to `.expr (.expr2021 false)` in ALL editions (`2015..=2024`).
-/
theorem definition_site_edition_determines_expr_kind (ed : Edition) :
    (resolveFragKind .ed2021 .exprSym = .expr (.expr2021 true)) ∧
    (resolveFragKind .ed2024 .exprSym = .expr .expr2024) ∧
    (resolveFragKind ed .expr2021Sym = .expr (.expr2021 false)) := by
  cases ed <;> refine ⟨rfl, rfl, rfl⟩

/--
  **Theorem (Follow-Set Invariance Across `Expr2021` and `Expr2024`, `macro_rules.rs:1750`):**
  Both `Expr2021` and `Expr2024` enforce the exact same follow-set (`=>`, `,`, `;`, or closing delimiter).
-/
theorem expr_follow_set_invariant (b : Bool) (t : Tok) :
    isInFollow (.expr (.expr2021 b)) t = isInFollow (.expr .expr2024) t := by
  cases t <;> rfl

/--
  **Theorem (LL(1) Follow-Set Determinism / Boundary Disjointness):**
  No token in `FOLLOW(expr)` can start an `Expr2024` fragment (`FIRST(expr_2024) ∩ FOLLOW(expr) = ∅`).
  Consequently, admitting `const` and `_` in Edition 2024 introduces zero follow-set boundary
  ambiguities with `=>`, `,`, `;`, or closing delimiters.
-/
theorem expr2024_first_follow_disjoint (t : Tok) :
    isInFollow (.expr .expr2024) t = true →
    nonterminalMayBeginWith (.expr .expr2024) t = false := by
  cases t <;> intro h <;> first | rfl | exact False.elim (Bool.noConfusion h)

/-- Dual statement: any token starting an `Expr2024` fragment is forbidden in `FOLLOW(expr)`. -/
theorem expr2024_start_not_in_follow (t : Tok) :
    nonterminalMayBeginWith (.expr .expr2024) t = true →
    isInFollow (.expr .expr2024) t = false := by
  cases t <;> intro h <;> first | rfl | exact False.elim (Bool.noConfusion h)

/-! ## Part 5: End-to-End Composition (`Marker.mark_span` Transcription + Resolver + Proc-Macro Spans) -/

/--
  Token tree emitted during MBE transcription (`transcribe.rs:95-112, 288-295`)
  or proc-macro bridge (`proc_macro_server.rs:467-473`).
-/
inductive TranscribedNode where
  | ident : Ident → TranscribedNode
  | metavarIdent : Ident → TranscribedNode
  | invisibleExprGroup : NtExprKind → ExprTerm → TranscribedNode

/-- `Marker::mark_span` applies `(expand_id, transparency)` ONLY to macro-body tokens, NOT captured metavariable arguments. -/
noncomputable def markMacroBodyIdent
    (expandId : ExpnId) (t : Transparency) (callSiteCtxt : SyntaxContext) (id : Ident) : Ident :=
  ⟨id.name, id.ctxt.applyMark expandId t callSiteCtxt⟩

/--
  Full-pipeline soundness theorem connecting MBE transcription (`Marker::mark_span`) with
  `applyMark` and local alpha-invariance: when a `macro_rules!` (`SemiOpaque`) body transcribed
  at any root-normalized call site introduces a local `let` binding `id_body` (originally parsed
  in `.root`) and also forwards a caller metavariable expression `e_arg` (`allRootCtxt = true`),
  the macro-introduced binding NEVER captures any variable in `e_arg`!
-/
theorem mbe_transcription_preserves_caller_metavar_hygiene
    (ρ : RibEnv) (expandId : ExpnId) (idBody : Ident) (vBody : Val) (eArg : LocalExpr)
    (hBodyRoot : idBody.ctxt = .root)
    (hArgRoot : eArg.allRootCtxt = true) :
    let markedBody := markMacroBodyIdent expandId .semiOpaque .root idBody
    evalLocalExpr (ρ.bindLocal markedBody vBody) eArg = evalLocalExpr ρ eArg := by
  intro markedBody
  have hMark : markedBody.ctxt.hasNonTransparentMark = true := by
    unfold markedBody markMacroBodyIdent
    rw [hBodyRoot]
    rfl
  exact caller_eval_invariant_under_macro_local ρ markedBody vBody eArg hMark hArgRoot

/--
  Symmetric proc-macro soundness theorem: any proc-macro `TokenStream` whose introduced locals
  carry `Span::mixed_site()` (`withMixedSiteCtxt`) or `Span::def_site()` (`withDefSiteCtxt`)
  is alpha-invariant wrt. all caller expressions `eCaller` (`allRootCtxt = true`).
-/
theorem proc_macro_mixed_or_def_site_noncapture
    (ρ : RibEnv) (expandId : ExpnId) (isMixed : Bool) (nMacro : SymId) (vMacro : Val)
    (eCaller : LocalExpr) (hCaller : eCaller.allRootCtxt = true) :
    let ctxt := match isMixed with | true => withMixedSiteCtxt expandId | false => withDefSiteCtxt expandId
    evalLocalExpr (ρ.bindLocal ⟨nMacro, ctxt⟩ vMacro) eCaller = evalLocalExpr ρ eCaller := by
  intro ctxt
  have hc : ctxt.hasNonTransparentMark = true := by
    cases isMixed <;> rfl
  exact caller_eval_invariant_under_macro_local ρ ⟨nMacro, ctxt⟩ vMacro eCaller hc hCaller

/--
  Nested macro composition soundness (`hygiene.rs:719-722` + `lib.rs:2390-2419`):
  when a `macro_rules!` (`SemiOpaque`) invocation `eInner` occurs inside a `macro` 2.0 (`Opaque`)
  definition `eOuter` (`callSiteCtxt = .push .root eOuter .opaq`), `applyMark` splices the outer
  `Opaque` mark beneath `eInner`'s `SemiOpaque` mark:
  1. `normalizeToMacros20` yields `.push .root eOuter .opaq` (preserving outer macro 2.0 item isolation);
  2. `normalizeToMacroRules` yields `.push (.push .root eOuter .opaq) eInner .semiOpaque` (isolating inner `macro_rules!` locals);
  3. `resolveDollarCrateMark` walks outermost-to-innermost and resolves `$crate` to `some eInner` (the `macro_rules!` macro's defining crate!).
-/
theorem legacy_inside_macros_2_0_preserves_both_layers (eOuter eInner : ExpnId) :
    let c := SyntaxContext.applyMark .root eInner .semiOpaque (.push .root eOuter .opaq)
    (c.normalizeToMacros20 = .push .root eOuter .opaq) ∧
    (c.normalizeToMacroRules = .push (.push .root eOuter .opaq) eInner .semiOpaque) ∧
    (resolveDollarCrateMark c = some eInner) :=
  ⟨rfl, rfl, rfl⟩

/--
  Conversely, when an `Opaque` mark is OUTSIDE a `SemiOpaque` mark (`push (push root eSemi .semiOpaque) eOpq .opaq`),
  `consumeOpaqueMarks` / `dollarCrateMarkAux` skips the prepended outer `Opaque` mark and resolves
  `$crate` to `some eSemi` (`lib.rs:2393-2413`).
-/
theorem dollarCrate_skips_outer_opaque_to_semiOpaque (eSemi eOpq : ExpnId) :
    resolveDollarCrateMark (.push (.push .root eSemi .semiOpaque) eOpq .opaq) = some eSemi := rfl

/-! ## Part 6: Extended Equivalence, Determinism & Structural Properties -/

/-- `hygienicEq` on `.root` vs `.root` holds trivially. -/
theorem hygienicEq_root_self (isDescendant : ExpnId → ExpnId → Bool) :
    SyntaxContext.hygienicEq isDescendant .root .root ExpnId.root = true := rfl

/-- Two `Transparent` contexts are always hygienically equal under `hygienicEq` regardless of marks. -/
theorem hygienicEq_transparent_erasable
    (isDescendant : ExpnId → ExpnId → Bool) (e₁ e₂ target : ExpnId) :
    SyntaxContext.hygienicEq isDescendant (withCallSiteCtxt e₁) (withCallSiteCtxt e₂) target = true := rfl

/-- Two `SemiOpaque` contexts are hygienically equal for items/methods (`normalize_to_macros_2_0`). -/
theorem hygienicEq_semiOpaque_erasable
    (isDescendant : ExpnId → ExpnId → Bool) (e₁ e₂ target : ExpnId) :
    SyntaxContext.hygienicEq isDescendant (withMixedSiteCtxt e₁) (withMixedSiteCtxt e₂) target = true := rfl

/-- `Opaque` marks from non-root expansions are popped by `adjust` at `ExpnId.root`, returning `some e` for privacy checking. -/
theorem adjust_opaque_at_non_descendant_strips_mark
    (e : ExpnId) (hNotRoot : ExpnId.beq ExpnId.root e = false) :
    let res := (withDefSiteCtxt e).adjust rootDescendant ExpnId.root
    res.1 = .root ∧ res.2 = some e := by
  have hsym : ExpnId.beq e ExpnId.root = false := by
    rw [expnId_beq_comm]
    exact hNotRoot
  dsimp only [withDefSiteCtxt, SyntaxContext.adjust, SyntaxContext.adjustAux, rootDescendant]
  rw [hsym, hNotRoot]
  exact ⟨rfl, rfl⟩

/-- `SemiOpaque` marks strip to `.root` BEFORE `adjust`, so `adjust` reports `none` (fallback to caller `mod_id`)! -/
theorem adjust_after_norm20_semiOpaque_returns_none (e target : ExpnId)
    (isDescendant : ExpnId → ExpnId → Bool) :
    ((withMixedSiteCtxt e).normalizeToMacros20.adjust isDescendant target).2 = none := rfl

/-- `ExprTerm` forwarding invariance: wrapping `const { ... }` inside `(...)` makes it accepted even in `Expr2021`. -/
theorem paren_constBlock_admitted_in_2021 (b : Bool) (body : ExprTerm) (hValid : body.isValidExpr = true) :
    acceptsExprFragment (.expr2021 b) (.parenthesized (.constBlock body)) = true := by
  have h1 : nonterminalMayBeginWith (.expr (.expr2021 b)) (ExprTerm.parenthesized (.constBlock body)).firstTok = true := rfl
  have h2 : (ExprTerm.parenthesized (.constBlock body)).isValidExpr = true := hValid
  unfold acceptsExprFragment
  rw [h1, h2]
  rfl

/-- Both `Expr2021` and `Expr2024` preserve non-empty token-start determinism on `eof`. -/
theorem expr_rejects_eof (ek : NtExprKind) :
    nonterminalMayBeginWith (.expr ek) .eof = false := by
  cases ek <;> rfl

/-- Edition 2021 `pat` vs Edition 2024 `pat`: `patWithOr` admits leading `|`, while `patParam` rejects it. -/
theorem pat_edition_leading_pipe_separation (b : Bool) :
    (nonterminalMayBeginWith (.pat .patWithOr) .pipe = true) ∧
    (nonterminalMayBeginWith (.pat (.patParam b)) .pipe = false) ∧
    (isInFollow (.pat .patWithOr) .pipe = false) ∧
    (isInFollow (.pat (.patParam b)) .pipe = true) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `resolveFragKind` for `pat` vs `pat_param` mirrors Edition 2021 boundary (`token.rs:1177-1184`). -/
theorem pat_edition_2021_boundary (ed : Edition) :
    (resolveFragKind .ed2018 .patSym = .pat (.patParam true)) ∧
    (resolveFragKind .ed2021 .patSym = .pat .patWithOr) ∧
    (resolveFragKind .ed2024 .patSym = .pat .patWithOr) ∧
    (resolveFragKind ed .patParamSym = .pat (.patParam false)) := by
  cases ed <;> refine ⟨rfl, rfl, rfl, rfl⟩

/-- `SyntaxContext` mark count helper for induction & compositional bounds. -/
noncomputable def SyntaxContext.depth : SyntaxContext → Nat
  | .root => 0
  | .push p _ _ => p.depth + 1

theorem normalizeToMacros20_depth_le (c : SyntaxContext) :
    c.normalizeToMacros20.depth ≤ c.depth := by
  induction c with
  | root => exact Nat.le_refl 0
  | push p _ t ih =>
    cases t with
    | transparent =>
      unfold SyntaxContext.normalizeToMacros20
      exact Nat.le_trans ih (Nat.le_succ p.depth)
    | semiOpaque =>
      unfold SyntaxContext.normalizeToMacros20
      exact Nat.le_trans ih (Nat.le_succ p.depth)
    | opaq =>
      unfold SyntaxContext.normalizeToMacros20 SyntaxContext.depth
      exact Nat.succ_le_succ ih

theorem normalizeToMacroRules_depth_le (c : SyntaxContext) :
    c.normalizeToMacroRules.depth ≤ c.depth := by
  induction c with
  | root => exact Nat.le_refl 0
  | push p _ t ih =>
    cases t with
    | transparent =>
      unfold SyntaxContext.normalizeToMacroRules
      exact Nat.le_trans ih (Nat.le_succ p.depth)
    | semiOpaque =>
      unfold SyntaxContext.normalizeToMacroRules SyntaxContext.depth
      exact Nat.succ_le_succ ih
    | opaq =>
      unfold SyntaxContext.normalizeToMacroRules SyntaxContext.depth
      exact Nat.succ_le_succ ih

/-- Equivalence of `scanDollarCrateMarksRev` (list reverse order) with `resolveDollarCrateMark` on `root`-normalized stacks. -/
theorem scanDollarCrate_single_semi (e : ExpnId) :
    scanDollarCrateMarksRev [(e, .semiOpaque)] = resolveDollarCrateMark (.push .root e .semiOpaque) := rfl

theorem scanDollarCrate_single_opaq (e : ExpnId) :
    scanDollarCrateMarksRev [(e, .opaq)] = resolveDollarCrateMark (.push .root e .opaq) := rfl

theorem scanDollarCrate_semi_then_opaq (eSemi eOpq : ExpnId) :
    scanDollarCrateMarksRev [(eOpq, .opaq), (eSemi, .semiOpaque)] =
    resolveDollarCrateMark (.push (.push .root eSemi .semiOpaque) eOpq .opaq) := rfl

theorem scanDollarCrate_opaq_then_semi (eOpq eSemi : ExpnId) :
    scanDollarCrateMarksRev [(eSemi, .semiOpaque), (eOpq, .opaq)] =
    resolveDollarCrateMark (.push (.push .root eOpq .opaq) eSemi .semiOpaque) := rfl

/-- Complete structural separation summary theorem combining all three pillars. -/
theorem rustc_macro_hygiene_and_edition2024_soundness_summary
    (ρ : RibEnv) (xMacro : Ident) (v : Val) (eCaller : LocalExpr)
    (hMacro : xMacro.ctxt.hasNonTransparentMark = true)
    (hCaller : eCaller.allRootCtxt = true)
    (e : ExprTerm) (b : Bool) (t : Tok) :
    (evalLocalExpr (ρ.bindLocal xMacro v) eCaller = evalLocalExpr ρ eCaller) ∧
    (acceptsExprFragment (.expr2021 b) e = true → acceptsExprFragment .expr2024 e = true) ∧
    (isInFollow (.expr .expr2024) t = true → nonterminalMayBeginWith (.expr .expr2024) t = false) :=
  ⟨ caller_eval_invariant_under_macro_local ρ xMacro v eCaller hMacro hCaller,
    expr2021_subset_expr2024 b e,
    expr2024_first_follow_disjoint t ⟩

end RustcMacroHygiene
