/-!
# `rustc` Lint-Level Lattice, `forbid` Stickiness, `--cap-lints` / `--force-warn`, RFC 2383 `#[expect]`, and `--check-cfg` / `#[cfg_attr(false, ...)]` Expansion Soundness

Self-contained kernel-checked Lean `v4.34.1` formalization (core `Init` library only;
zero `sorry`, zero `partial def`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
zero `native_decide`, zero `deriving` on inductives/structures, every `def` marked
`noncomputable def`, yielding zero `._unsafe_rec` constants).

Mirrors `rust-lang/rust` (`compiler/rustc_lint_defs/src/lib.rs`,
`compiler/rustc_lint/src/{levels.rs, expect.rs, early.rs}`,
`compiler/rustc_middle/src/lint.rs`, `compiler/rustc_session/src/{session.rs, config.rs, config/cfg.rs}`,
`compiler/rustc_interface/src/interface.rs`, `compiler/rustc_attr_parsing/src/attributes/cfg.rs`,
`compiler/rustc_expand/src/{config.rs, expand.rs}`, and `compiler/rustc_errors/src/lib.rs`).
-/

namespace RustcLintAndCfgModel

/-! ## Part 1: Basic Equality & List Utilities (Pure, Total, Zero `._unsafe_rec`) -/

section Helpers

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolEq_eq_true_iff (a b : Bool) : boolEq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

noncomputable def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => natEq a b
  | _, _ => false

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_sound : ∀ {a b : Nat}, natEq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, Nat.succ _, h => Bool.noConfusion h
  | Nat.succ _, 0, h => Bool.noConfusion h
  | Nat.succ _, Nat.succ _, h => congrArg Nat.succ (natEq_sound h)

theorem natEq_eq_true_iff (a b : Nat) : natEq a b = true ↔ a = b :=
  ⟨natEq_sound, fun h => by subst h; exact natEq_refl a⟩

noncomputable def natLe : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => natLe a b

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLe_trans : ∀ {a b c : Nat}, natLe a b = true → natLe b c = true → natLe a c = true
  | 0, _, _, _, _ => rfl
  | Nat.succ _, 0, _, h1, _ => Bool.noConfusion h1
  | Nat.succ _, Nat.succ _, 0, _, h2 => Bool.noConfusion h2
  | Nat.succ a, Nat.succ b, Nat.succ c, h1, h2 => natLe_trans (a := a) (b := b) (c := c) h1 h2

theorem natLe_antisymm : ∀ {a b : Nat}, natLe a b = true → natLe b a = true → a = b
  | 0, 0, _, _ => rfl
  | 0, Nat.succ _, _, h2 => Bool.noConfusion h2
  | Nat.succ _, 0, h1, _ => Bool.noConfusion h1
  | Nat.succ _, Nat.succ _, h1, h2 => congrArg Nat.succ (natLe_antisymm h1 h2)

theorem natLe_total : ∀ a b : Nat, natLe a b = true ∨ natLe b a = true
  | 0, _ => Or.inl rfl
  | _, 0 => Or.inr rfl
  | Nat.succ a, Nat.succ b => natLe_total a b

noncomputable def strEq (a b : String) : Bool :=
  a == b

noncomputable def listAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || listAny p xs

noncomputable def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

noncomputable def listFilter {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: listFilter p xs else listFilter p xs

noncomputable def listFlatMap {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ listFlatMap f xs

theorem listAny_append {α : Type} (p : α → Bool) (xs ys : List α) :
    listAny p (xs ++ ys) = (listAny p xs || listAny p ys) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    show (p x || listAny p (rest ++ ys)) = ((p x || listAny p rest) || listAny p ys)
    rw [ih, Bool.or_assoc]

theorem listAll_append {α : Type} (p : α → Bool) (xs ys : List α) :
    listAll p (xs ++ ys) = (listAll p xs && listAll p ys) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    show (p x && listAll p (rest ++ ys)) = ((p x && listAll p rest) && listAll p ys)
    rw [ih, Bool.and_assoc]

theorem listAny_eq_false_of_all_false {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = false) : listAny p xs = false := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx : p x = false := h x (List.Mem.head rest)
    have hrest : listAny p rest = false := ih (fun y hy => h y (List.Mem.tail x hy))
    show (p x || listAny p rest) = false
    rw [hx, hrest]
    rfl

theorem listAny_eq_true_of_mem {α : Type} (p : α → Bool) {xs : List α} {x : α}
    (hx : x ∈ xs) (hp : p x = true) : listAny p xs = true := by
  induction hx with
  | head _ =>
    show (p x || listAny p _) = true
    rw [hp]
    rfl
  | tail y _ ih =>
    show (p y || listAny p _) = true
    rw [ih]
    cases p y <;> rfl

theorem listMem_of_listAny_true {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, listAny p xs = true → ∃ x, x ∈ xs ∧ p x = true
  | [], h => Bool.noConfusion h
  | x :: xs, h => by
    cases hpx : p x with
    | true => exact ⟨x, List.Mem.head xs, hpx⟩
    | false =>
      have hrest : listAny p xs = true := by
        have h1 : (p x || listAny p xs) = true := h
        rw [hpx] at h1
        exact h1
      match listMem_of_listAny_true p hrest with
      | ⟨y, hy, hpy⟩ => exact ⟨y, List.Mem.tail x hy, hpy⟩

end Helpers

/-! ## Part 2: `rustc_lint_defs::Level` — The 6-Level Total Order & Bounded Lattice -/

section LintLevelSection

/-- Mirrors `rustc_lint_defs::Level` (`compiler/rustc_lint_defs/src/lib.rs:154-185`).
Derived ordering: `Allow < Expect < Warn < ForceWarn < Deny < Forbid`. -/
inductive LintLevel where
  | allow
  | expect
  | warn
  | forceWarn
  | deny
  | forbid

noncomputable def LintLevel.rank : LintLevel → Nat
  | .allow     => 0
  | .expect    => 1
  | .warn      => 2
  | .forceWarn => 3
  | .deny      => 4
  | .forbid    => 5

noncomputable def LintLevel.beq : LintLevel → LintLevel → Bool
  | .allow,     .allow     => true
  | .expect,    .expect    => true
  | .warn,      .warn      => true
  | .forceWarn, .forceWarn => true
  | .deny,      .deny      => true
  | .forbid,    .forbid    => true
  | _,          _          => false

theorem LintLevel.beq_eq_true_iff (a b : LintLevel) : LintLevel.beq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => LintLevel.noConfusion h⟩

noncomputable def LintLevel.le (a b : LintLevel) : Prop :=
  natLe a.rank b.rank = true

noncomputable def LintLevel.leB (a b : LintLevel) : Bool :=
  natLe a.rank b.rank

noncomputable def LintLevel.min (a b : LintLevel) : LintLevel :=
  if natLe a.rank b.rank then a else b

noncomputable def LintLevel.isError : LintLevel → Bool
  | .allow | .expect | .warn | .forceWarn => false
  | .deny | .forbid => true

/-- Mirrors `Level::from_str` (`compiler/rustc_lint_defs/src/lib.rs:202-210`), used by
`--cap-lints`: accepts only `allow`, `warn`, `deny`, `forbid`, rejecting `expect` and `force-warn`. -/
noncomputable def LintLevel.fromCapStr? (s : String) : Option LintLevel :=
  if strEq s "allow" then some .allow
  else if strEq s "warn" then some .warn
  else if strEq s "deny" then some .deny
  else if strEq s "forbid" then some .forbid
  else none

noncomputable def LintLevel.isCapAdmissible : LintLevel → Bool
  | .allow | .warn | .deny | .forbid => true
  | .expect | .forceWarn => false

theorem LintLevel.rank_injective {a b : LintLevel} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem LintLevel.le_refl (a : LintLevel) : LintLevel.le a a :=
  natLe_refl a.rank

theorem LintLevel.le_trans {a b c : LintLevel} (h1 : LintLevel.le a b) (h2 : LintLevel.le b c) :
    LintLevel.le a c :=
  natLe_trans h1 h2

theorem LintLevel.le_antisymm {a b : LintLevel} (h1 : LintLevel.le a b) (h2 : LintLevel.le b a) :
    a = b :=
  LintLevel.rank_injective (natLe_antisymm h1 h2)

theorem LintLevel.le_total (a b : LintLevel) : LintLevel.le a b ∨ LintLevel.le b a :=
  natLe_total a.rank b.rank

theorem LintLevel.allow_le (a : LintLevel) : LintLevel.le .allow a := by
  cases a <;> rfl

theorem LintLevel.le_forbid (a : LintLevel) : LintLevel.le a .forbid := by
  cases a <;> rfl

theorem LintLevel.min_le_left (a b : LintLevel) : LintLevel.le (LintLevel.min a b) a := by
  cases a <;> cases b <;> rfl

theorem LintLevel.min_le_right (a b : LintLevel) : LintLevel.le (LintLevel.min a b) b := by
  cases a <;> cases b <;> rfl

theorem LintLevel.le_min {x a b : LintLevel} (ha : LintLevel.le x a) (hb : LintLevel.le x b) :
    LintLevel.le x (LintLevel.min a b) := by
  cases x <;> cases a <;> cases b <;> first | exact ha | exact hb | rfl

theorem LintLevel.min_comm (a b : LintLevel) : LintLevel.min a b = LintLevel.min b a := by
  cases a <;> cases b <;> rfl

theorem LintLevel.min_assoc (a b c : LintLevel) :
    LintLevel.min (LintLevel.min a b) c = LintLevel.min a (LintLevel.min b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem LintLevel.min_idem (a : LintLevel) : LintLevel.min a a = a := by
  cases a <;> rfl

theorem LintLevel.min_forbid_right (a : LintLevel) : LintLevel.min a .forbid = a := by
  cases a <;> rfl

theorem LintLevel.min_allow_right (a : LintLevel) : LintLevel.min a .allow = .allow := by
  cases a <;> rfl

theorem LintLevel.min_expect_warn : LintLevel.min .expect .warn = .expect := rfl

theorem LintLevel.fromCapStr_never_expect (s : String) :
    LintLevel.fromCapStr? s ≠ some .expect := by
  unfold LintLevel.fromCapStr?
  cases h1 : strEq s "allow"
  · cases h2 : strEq s "warn"
    · cases h3 : strEq s "deny"
      · cases h4 : strEq s "forbid" <;> intro h <;> cases h
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

theorem LintLevel.fromCapStr_never_forceWarn (s : String) :
    LintLevel.fromCapStr? s ≠ some .forceWarn := by
  unfold LintLevel.fromCapStr?
  cases h1 : strEq s "allow"
  · cases h2 : strEq s "warn"
    · cases h3 : strEq s "deny"
      · cases h4 : strEq s "forbid" <;> intro h <;> cases h
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

theorem LintLevel.isError_iff (a : LintLevel) :
    a.isError = true ↔ (a = .deny ∨ a = .forbid) := by
  cases a with
  | allow => exact ⟨fun h => Bool.noConfusion h, fun h => Or.elim h (fun h1 => LintLevel.noConfusion h1) (fun h1 => LintLevel.noConfusion h1)⟩
  | expect => exact ⟨fun h => Bool.noConfusion h, fun h => Or.elim h (fun h1 => LintLevel.noConfusion h1) (fun h1 => LintLevel.noConfusion h1)⟩
  | warn => exact ⟨fun h => Bool.noConfusion h, fun h => Or.elim h (fun h1 => LintLevel.noConfusion h1) (fun h1 => LintLevel.noConfusion h1)⟩
  | forceWarn => exact ⟨fun h => Bool.noConfusion h, fun h => Or.elim h (fun h1 => LintLevel.noConfusion h1) (fun h1 => LintLevel.noConfusion h1)⟩
  | deny => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | forbid => exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩

end LintLevelSection

/-! ## Part 3: Lint Identities, Sources, `LevelSpec`, and `LevelSpec.WF` -/

section LevelSpecSection

/-- Built-in and named lint identifiers modeled explicitly so `warnings`,
`unfulfilled_lint_expectations`, `forbidden_lint_groups`, `unexpected_cfgs`, `unsafe_code`,
and `dead_code` carry exact compiler flags. -/
inductive LintName where
  | warnings
  | unfulfilledLintExpectations
  | forbiddenLintGroups
  | unexpectedCfgs
  | unsafeCode
  | deadCode
  | unusedVariables
  | custom (id : Nat)

noncomputable def LintName.beq : LintName → LintName → Bool
  | .warnings, .warnings => true
  | .unfulfilledLintExpectations, .unfulfilledLintExpectations => true
  | .forbiddenLintGroups, .forbiddenLintGroups => true
  | .unexpectedCfgs, .unexpectedCfgs => true
  | .unsafeCode, .unsafeCode => true
  | .deadCode, .deadCode => true
  | .unusedVariables, .unusedVariables => true
  | .custom a, .custom b => natEq a b
  | _, _ => false

theorem LintName.beq_refl (l : LintName) : LintName.beq l l = true := by
  cases l with
  | custom id => exact natEq_refl id
  | _ => rfl

theorem LintName.beq_sound : ∀ {a b : LintName}, LintName.beq a b = true → a = b
  | .warnings, .warnings, _ => rfl
  | .unfulfilledLintExpectations, .unfulfilledLintExpectations, _ => rfl
  | .forbiddenLintGroups, .forbiddenLintGroups, _ => rfl
  | .unexpectedCfgs, .unexpectedCfgs, _ => rfl
  | .unsafeCode, .unsafeCode, _ => rfl
  | .deadCode, .deadCode, _ => rfl
  | .unusedVariables, .unusedVariables, _ => rfl
  | .custom _, .custom _, h => congrArg LintName.custom (natEq_sound h)
  | .warnings, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .warnings, .forbiddenLintGroups, h => Bool.noConfusion h
  | .warnings, .unexpectedCfgs, h => Bool.noConfusion h
  | .warnings, .unsafeCode, h => Bool.noConfusion h
  | .warnings, .deadCode, h => Bool.noConfusion h
  | .warnings, .unusedVariables, h => Bool.noConfusion h
  | .warnings, .custom _, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .warnings, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .forbiddenLintGroups, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .unexpectedCfgs, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .unsafeCode, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .deadCode, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .unusedVariables, h => Bool.noConfusion h
  | .unfulfilledLintExpectations, .custom _, h => Bool.noConfusion h
  | .forbiddenLintGroups, .warnings, h => Bool.noConfusion h
  | .forbiddenLintGroups, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .forbiddenLintGroups, .unexpectedCfgs, h => Bool.noConfusion h
  | .forbiddenLintGroups, .unsafeCode, h => Bool.noConfusion h
  | .forbiddenLintGroups, .deadCode, h => Bool.noConfusion h
  | .forbiddenLintGroups, .unusedVariables, h => Bool.noConfusion h
  | .forbiddenLintGroups, .custom _, h => Bool.noConfusion h
  | .unexpectedCfgs, .warnings, h => Bool.noConfusion h
  | .unexpectedCfgs, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .unexpectedCfgs, .forbiddenLintGroups, h => Bool.noConfusion h
  | .unexpectedCfgs, .unsafeCode, h => Bool.noConfusion h
  | .unexpectedCfgs, .deadCode, h => Bool.noConfusion h
  | .unexpectedCfgs, .unusedVariables, h => Bool.noConfusion h
  | .unexpectedCfgs, .custom _, h => Bool.noConfusion h
  | .unsafeCode, .warnings, h => Bool.noConfusion h
  | .unsafeCode, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .unsafeCode, .forbiddenLintGroups, h => Bool.noConfusion h
  | .unsafeCode, .unexpectedCfgs, h => Bool.noConfusion h
  | .unsafeCode, .deadCode, h => Bool.noConfusion h
  | .unsafeCode, .unusedVariables, h => Bool.noConfusion h
  | .unsafeCode, .custom _, h => Bool.noConfusion h
  | .deadCode, .warnings, h => Bool.noConfusion h
  | .deadCode, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .deadCode, .forbiddenLintGroups, h => Bool.noConfusion h
  | .deadCode, .unexpectedCfgs, h => Bool.noConfusion h
  | .deadCode, .unsafeCode, h => Bool.noConfusion h
  | .deadCode, .unusedVariables, h => Bool.noConfusion h
  | .deadCode, .custom _, h => Bool.noConfusion h
  | .unusedVariables, .warnings, h => Bool.noConfusion h
  | .unusedVariables, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .unusedVariables, .forbiddenLintGroups, h => Bool.noConfusion h
  | .unusedVariables, .unexpectedCfgs, h => Bool.noConfusion h
  | .unusedVariables, .unsafeCode, h => Bool.noConfusion h
  | .unusedVariables, .deadCode, h => Bool.noConfusion h
  | .unusedVariables, .custom _, h => Bool.noConfusion h
  | .custom _, .warnings, h => Bool.noConfusion h
  | .custom _, .unfulfilledLintExpectations, h => Bool.noConfusion h
  | .custom _, .forbiddenLintGroups, h => Bool.noConfusion h
  | .custom _, .unexpectedCfgs, h => Bool.noConfusion h
  | .custom _, .unsafeCode, h => Bool.noConfusion h
  | .custom _, .deadCode, h => Bool.noConfusion h
  | .custom _, .unusedVariables, h => Bool.noConfusion h

theorem LintName.beq_eq_true_iff (a b : LintName) : LintName.beq a b = true ↔ a = b :=
  ⟨LintName.beq_sound, fun h => by subst h; exact LintName.beq_refl a⟩

/-- Mirrors `rustc_lint_defs::Lint` metadata relevant to level resolution and emission. -/
structure LintMeta where
  defaultLevel : LintLevel
  ignoreDenyWarnings : Bool
  reportInExternalMacro : Bool
  futureCompatReportInDeps : Bool

noncomputable def builtinLintMeta : LintName → LintMeta
  | .warnings => ⟨.warn, false, false, false⟩
  | .unfulfilledLintExpectations => ⟨.warn, false, false, false⟩
  | .forbiddenLintGroups => ⟨.warn, true, false, true⟩
  | .unexpectedCfgs => ⟨.warn, false, true, false⟩
  | .unsafeCode => ⟨.allow, false, false, false⟩
  | .deadCode => ⟨.warn, false, false, false⟩
  | .unusedVariables => ⟨.warn, false, false, false⟩
  | .custom _ => ⟨.warn, false, false, false⟩

/-- Mirrors `LintGroup` names vs individual lint names (`LintStore::is_lint_group`). -/
inductive AttrOrCliTargetName where
  | lint (l : LintName)
  | groupUnused
  | groupWarnings
  | groupCustom (gid : Nat)

noncomputable def AttrOrCliTargetName.isLintGroup : AttrOrCliTargetName → Bool
  | .lint .warnings => true
  | .lint _ => false
  | .groupUnused => true
  | .groupWarnings => true
  | .groupCustom _ => true

noncomputable def expandTargetName : AttrOrCliTargetName → List LintName
  | .lint l => [l]
  | .groupUnused => [.deadCode, .unusedVariables]
  | .groupWarnings => [.warnings]
  | .groupCustom _ => [.deadCode]

/-- Mirrors `LintExpectationId` canonicalization (`compiler/rustc_lint/src/expect.rs:33-47`):
both AST `UnstableLintExpectationId` and HIR `StableLintExpectationId` project to `(attrId, lintIndex)`. -/
structure CanonExpectId where
  attrId : Nat
  lintIndex : Nat

noncomputable def CanonExpectId.beq (a b : CanonExpectId) : Bool :=
  natEq a.attrId b.attrId && natEq a.lintIndex b.lintIndex

theorem CanonExpectId.beq_refl (a : CanonExpectId) : CanonExpectId.beq a a = true := by
  unfold CanonExpectId.beq
  rw [natEq_refl a.attrId, natEq_refl a.lintIndex]
  rfl

theorem CanonExpectId.beq_sound {a b : CanonExpectId} (h : CanonExpectId.beq a b = true) : a = b := by
  unfold CanonExpectId.beq at h
  cases ha : natEq a.attrId b.attrId with
  | false => rw [ha] at h; exact Bool.noConfusion h
  | true =>
    cases hl : natEq a.lintIndex b.lintIndex with
    | false => rw [ha, hl] at h; exact Bool.noConfusion h
    | true =>
      have h1 : a.attrId = b.attrId := natEq_sound ha
      have h2 : a.lintIndex = b.lintIndex := natEq_sound hl
      cases a; cases b; cases h1; cases h2; rfl

theorem CanonExpectId.beq_eq_true_iff (a b : CanonExpectId) :
    CanonExpectId.beq a b = true ↔ a = b :=
  ⟨CanonExpectId.beq_sound, fun h => by subst h; exact CanonExpectId.beq_refl a⟩

inductive RawExpectId where
  | unstable (attrId : Nat) (lintIndex : Nat)
  | stable (hirId : Nat) (attrId : Nat) (lintIndex : Nat)

noncomputable def canonicalizeExpectId : RawExpectId → CanonExpectId
  | .unstable attrId lintIndex => ⟨attrId, lintIndex⟩
  | .stable _ attrId lintIndex => ⟨attrId, lintIndex⟩

theorem canonicalize_early_late_agree (hirId attrId lintIndex : Nat) :
    canonicalizeExpectId (.unstable attrId lintIndex) =
      canonicalizeExpectId (.stable hirId attrId lintIndex) := rfl

/-- Mirrors `rustc_middle::lint::LintLevelSource` (`lint.rs:21-37`). -/
inductive LintLevelSource where
  | defaultSrc
  | nodeSrc (name : AttrOrCliTargetName) (spanId : Nat) (reason : Option String)
  | commandLine (name : AttrOrCliTargetName) (flagLevel : LintLevel)

noncomputable def LintLevelSource.isCliForceWarn : LintLevelSource → Bool
  | .commandLine _ .forceWarn => true
  | _ => false

noncomputable def LintLevelSource.isLintGroupSource : LintLevelSource → Bool
  | .defaultSrc => false
  | .nodeSrc name _ _ => name.isLintGroup
  | .commandLine name _ => name.isLintGroup

/-- Mirrors `rustc_middle::lint::LevelSpec` (`lint.rs:59-90`). -/
structure LevelSpec where
  level : LintLevel
  lintId : Option CanonExpectId
  src : LintLevelSource

/-- Exact structural invariant enforced by `LevelSpec::new` (`lint.rs:82-90`). -/
noncomputable def LevelSpec.WF (spec : LevelSpec) : Prop :=
  match spec.level, spec.lintId with
  | .allow, none => True
  | .warn, none => True
  | .deny, none => True
  | .forbid, none => True
  | .expect, some _ => True
  | .forceWarn, _ => True
  | _, _ => False

theorem LevelSpec.wf_allow (src : LintLevelSource) :
    LevelSpec.WF ⟨.allow, none, src⟩ := trivial

theorem LevelSpec.wf_warn (src : LintLevelSource) :
    LevelSpec.WF ⟨.warn, none, src⟩ := trivial

theorem LevelSpec.wf_deny (src : LintLevelSource) :
    LevelSpec.WF ⟨.deny, none, src⟩ := trivial

theorem LevelSpec.wf_forbid (src : LintLevelSource) :
    LevelSpec.WF ⟨.forbid, none, src⟩ := trivial

theorem LevelSpec.wf_expect (id : CanonExpectId) (src : LintLevelSource) :
    LevelSpec.WF ⟨.expect, some id, src⟩ := trivial

theorem LevelSpec.wf_forceWarn (id? : Option CanonExpectId) (src : LintLevelSource) :
    LevelSpec.WF ⟨.forceWarn, id?, src⟩ := trivial

end LevelSpecSection

/-! ## Part 4: CLI Parsing, `add_command_line`, and `reveal_actual_level_spec` -/

section CliAndRevealSection

inductive CliFlag where
  | capLints (lvl : LintLevel)
  | lintOpt (target : AttrOrCliTargetName) (lvl : LintLevel)

/-- Mirrors `matches.opt_str("cap-lints")`: first valid `--cap-lints` argument wins. -/
noncomputable def parseCapLints : List CliFlag → Option LintLevel
  | [] => none
  | .capLints lvl :: rest =>
    if lvl.isCapAdmissible then some lvl else parseCapLints rest
  | .lintOpt _ _ :: rest => parseCapLints rest

noncomputable def parseLintOpts : List CliFlag → List (AttrOrCliTargetName × LintLevel)
  | [] => []
  | .capLints _ :: rest => parseLintOpts rest
  | .lintOpt target lvl :: rest => (target, lvl) :: parseLintOpts rest

theorem cap_flag_first_wins (pre post : List CliFlag) (c : LintLevel)
    (hc : c.isCapAdmissible = true)
    (hpre : ∀ f, f ∈ pre → ∀ lvl, f = .capLints lvl → lvl.isCapAdmissible = false) :
    parseCapLints (pre ++ .capLints c :: post) = some c := by
  induction pre with
  | nil =>
    show (if c.isCapAdmissible then some c else parseCapLints post) = some c
    rw [hc]
    rfl
  | cons f fs ih =>
    cases f with
    | capLints lvl =>
      have hfalse : lvl.isCapAdmissible = false := hpre (.capLints lvl) (List.Mem.head fs) lvl rfl
      show (if lvl.isCapAdmissible then some lvl else parseCapLints (fs ++ .capLints c :: post)) = some c
      rw [hfalse]
      exact ih (fun g hg => hpre g (List.Mem.tail (.capLints lvl) hg))
    | lintOpt t l =>
      exact ih (fun g hg => hpre g (List.Mem.tail (.lintOpt t l) hg))

theorem cap_flag_irrelevant_to_lintOpts (pre post : List CliFlag) (c : LintLevel) :
    parseLintOpts (pre ++ .capLints c :: post) = parseLintOpts (pre ++ post) := by
  induction pre with
  | nil => rfl
  | cons f fs ih =>
    cases f with
    | capLints lvl => exact ih
    | lintOpt t l =>
      show (t, l) :: parseLintOpts (fs ++ .capLints c :: post) = (t, l) :: parseLintOpts (fs ++ post)
      rw [ih]

/-- Command-line lint specification map (`LintStackIndex = COMMAND_LINE`). -/
noncomputable def CliMap := LintName → Option LevelSpec

noncomputable def emptyCliMap : CliMap := fun _ => none

noncomputable def CliMap.set (m : CliMap) (k : LintName) (v : LevelSpec) : CliMap :=
  fun x => if LintName.beq x k then some v else m x

theorem CliMap.set_self (m : CliMap) (k : LintName) (v : LevelSpec) :
    CliMap.set m k v k = some v := by
  unfold CliMap.set
  rw [LintName.beq_refl k]
  rfl

theorem CliMap.set_other (m : CliMap) {k x : LintName} (v : LevelSpec) (hne : x ≠ k) :
    CliMap.set m k v x = m x := by
  unfold CliMap.set
  cases h : LintName.beq x k with
  | false => rfl
  | true => exact False.elim (hne (LintName.beq_sound h))

/-- Mirrors `LintLevelsBuilder::add_command_line` (`compiler/rustc_lint/src/levels.rs:497-565`). -/
noncomputable def addCommandLineStepOne (m : CliMap) (flagName : AttrOrCliTargetName)
    (lvl : LintLevel) (id : LintName) : CliMap :=
  match m id with
  | some spec =>
    match spec.level with
    | .forceWarn | .forbid => m
    | _ => CliMap.set m id ⟨lvl, none, .commandLine flagName lvl⟩
  | none => CliMap.set m id ⟨lvl, none, .commandLine flagName lvl⟩

noncomputable def applyCliTargetList (m : CliMap) (flagName : AttrOrCliTargetName)
    (lvl : LintLevel) : List LintName → CliMap
  | [] => m
  | id :: ids => applyCliTargetList (addCommandLineStepOne m flagName lvl id) flagName lvl ids

noncomputable def buildCommandLineMap (opts : List (AttrOrCliTargetName × LintLevel)) : CliMap :=
  opts.foldl (fun m (t, lvl) =>
    if (match t, lvl with | .lint .warnings, .forceWarn => true | .groupWarnings, .forceWarn => true | _, _ => false) then
      m
    else
      applyCliTargetList m t lvl (expandTargetName t)) emptyCliMap

theorem addCmd_forceWarn_sticky (m : CliMap) (flagName : AttrOrCliTargetName)
    (lvl : LintLevel) (id : LintName) (src : LintLevelSource) (eid : Option CanonExpectId)
    (h : m id = some ⟨.forceWarn, eid, src⟩) :
    addCommandLineStepOne m flagName lvl id id = some ⟨.forceWarn, eid, src⟩ := by
  unfold addCommandLineStepOne
  rw [h]
  exact h

theorem addCmd_forbid_sticky (m : CliMap) (flagName : AttrOrCliTargetName)
    (lvl : LintLevel) (id : LintName) (src : LintLevelSource) (eid : Option CanonExpectId)
    (h : m id = some ⟨.forbid, eid, src⟩) :
    addCommandLineStepOne m flagName lvl id id = some ⟨.forbid, eid, src⟩ := by
  unfold addCommandLineStepOne
  rw [h]
  exact h

theorem addCmd_nonSticky_overridable (m : CliMap) (flagName : AttrOrCliTargetName)
    (lvl : LintLevel) (id : LintName) (oldLvl : LintLevel) (src : LintLevelSource)
    (eid : Option CanonExpectId) (h : m id = some ⟨oldLvl, eid, src⟩)
    (hnf : oldLvl ≠ .forceWarn) (hnfb : oldLvl ≠ .forbid) :
    addCommandLineStepOne m flagName lvl id id = some ⟨lvl, none, .commandLine flagName lvl⟩ := by
  unfold addCommandLineStepOne
  rw [h]
  cases oldLvl with
  | allow => exact CliMap.set_self m id _
  | expect => exact CliMap.set_self m id _
  | warn => exact CliMap.set_self m id _
  | deny => exact CliMap.set_self m id _
  | forceWarn => exact False.elim (hnf rfl)
  | forbid => exact False.elim (hnfb rfl)

/-- Session lint options relevant to `reveal_actual_level_spec` and `can_emit_warnings`. -/
structure LintSessionOpts where
  lintCap : Option LintLevel
  driverCaps : LintName → Option LintLevel
  cliWarningsAllow : Bool

noncomputable def LintSessionOpts.canEmitWarnings (opts : LintSessionOpts) : Bool :=
  !(opts.cliWarningsAllow || (match opts.lintCap with | some .allow => true | _ => false))

theorem ite_true_pf {α : Type} {p : Prop} [d : Decidable p] (hp : p) (t e : α) :
    @ite α p d t e = t := by
  cases d with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

theorem ite_false_pf {α : Type} {p : Prop} [d : Decidable p] (hnp : ¬ p) (t e : α) :
    @ite α p d t e = e := by
  cases d with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- Mirrors `rustc_middle::lint::reveal_actual_level_spec` (`compiler/rustc_middle/src/lint.rs:141-195`). -/
noncomputable def revealActualLevelSpec (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName) : LevelSpec :=
  let lmeta := builtinLintMeta lint
  let baseSpec : LevelSpec :=
    match probe lint with
    | some s => s
    | none => ⟨lmeta.defaultLevel, none, .defaultSrc⟩
  let afterWarnings : LevelSpec :=
    match baseSpec.level with
    | .warn =>
      match probe .warnings with
      | some wSpec =>
        let respect : Bool :=
          match wSpec.level with
          | .warn => false
          | .deny | .forbid => !lmeta.ignoreDenyWarnings
          | .allow | .expect => true
          | .forceWarn => false
        if respect then wSpec else baseSpec
      | none => baseSpec
    | _ => baseSpec
  let afterCap : LevelSpec :=
    if afterWarnings.src.isCliForceWarn then
      afterWarnings
    else
      let cap := match opts.lintCap with | some c => c | none => .forbid
      ⟨LintLevel.min afterWarnings.level cap, afterWarnings.lintId, afterWarnings.src⟩
  match opts.driverCaps lint with
  | some dCap => ⟨LintLevel.min afterCap.level dCap, afterCap.lintId, afterCap.src⟩
  | none => afterCap

/-- **Pillar 2 Theorem 1 (`--cap-lints` Upper Bound):**
Whenever `lint` does not resolve to a `CommandLine(_, ForceWarn)` source (either directly or
through `warnings`), `revealActualLevelSpec` is bounded above by `cap`. -/
theorem reveal_le_lintCap_unless_forceWarn (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName) (cap : LintLevel)
    (hcap : opts.lintCap = some cap)
    (hd : opts.driverCaps lint = none)
    (hnoFw : (probe lint).elim false (fun s => s.src.isCliForceWarn) = false)
    (hnoWarnFw : (probe .warnings).elim false (fun s => s.src.isCliForceWarn) = false) :
    LintLevel.le (revealActualLevelSpec opts probe lint).level cap := by
  unfold revealActualLevelSpec
  rw [hcap, hd]
  have h1 : ∀ afterW : LevelSpec, afterW.src.isCliForceWarn = false →
      LintLevel.le (if afterW.src.isCliForceWarn then afterW else ⟨LintLevel.min afterW.level cap, afterW.lintId, afterW.src⟩).level cap := by
    intro afterW hfw
    rw [hfw]
    exact LintLevel.min_le_right afterW.level cap
  apply h1
  cases hp : probe lint with
  | none =>
    dsimp only
    cases hl : (builtinLintMeta lint).defaultLevel <;> try rfl
    cases hw : probe .warnings with
    | none => rfl
    | some w =>
      rw [hw] at hnoWarnFw
      dsimp only
      cases hwl : w.level <;> (try rw [hwl]) <;> dsimp only <;> try rfl
      · rw [ite_true_pf rfl]; exact hnoWarnFw
      · rw [ite_true_pf rfl]; exact hnoWarnFw
      · cases !(builtinLintMeta lint).ignoreDenyWarnings <;> try dsimp only
        · rw [ite_false_pf Bool.false_ne_true]; rfl
        · rw [ite_true_pf rfl]; exact hnoWarnFw
      · cases !(builtinLintMeta lint).ignoreDenyWarnings <;> try dsimp only
        · rw [ite_false_pf Bool.false_ne_true]; rfl
        · rw [ite_true_pf rfl]; exact hnoWarnFw
  | some s =>
    rw [hp] at hnoFw
    cases hsl : s.level <;> (try dsimp only) <;> try exact hnoFw
    cases hw : probe .warnings with
    | none => exact hnoFw
    | some w =>
      rw [hw] at hnoWarnFw
      dsimp only
      cases hwl : w.level <;> (try rw [hwl]) <;> dsimp only <;> try exact hnoFw
      · rw [ite_true_pf rfl]; exact hnoWarnFw
      · rw [ite_true_pf rfl]; exact hnoWarnFw
      · cases !(builtinLintMeta lint).ignoreDenyWarnings <;> try dsimp only
        · rw [ite_false_pf Bool.false_ne_true]; exact hnoFw
        · rw [ite_true_pf rfl]; exact hnoWarnFw
      · cases !(builtinLintMeta lint).ignoreDenyWarnings <;> try dsimp only
        · rw [ite_false_pf Bool.false_ne_true]; exact hnoFw
        · rw [ite_true_pf rfl]; exact hnoWarnFw

/-- **Pillar 2 Theorem 2 (`--force-warn` Bypass of `--cap-lints=allow`):**
If `probe lint` holds `CommandLine(_, ForceWarn)` (whether overlaid by attributes or not),
then even under `--cap-lints=allow`, `revealActualLevelSpec` returns `ForceWarn`. -/
theorem reveal_forceWarn_bypasses_capLints_allow (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName)
    (t : AttrOrCliTargetName) (eid : Option CanonExpectId)
    (_hcap : opts.lintCap = some .allow)
    (hd : opts.driverCaps lint = none)
    (hprobe : probe lint = some ⟨.forceWarn, eid, .commandLine t .forceWarn⟩) :
    (revealActualLevelSpec opts probe lint).level = .forceWarn := by
  unfold revealActualLevelSpec
  rw [hprobe, hd]
  rfl

/-- **Pillar 2 Theorem 3 (`--cap-lints=allow` Silences Both `#![forbid]` and `-F`):**
For any non-`CommandLine(_, ForceWarn)` `forbid` spec (crate `#![forbid]` or CLI `-F`),
`--cap-lints=allow` lowers the revealed level all the way to `.allow`. -/
theorem reveal_capLints_allow_silences_forbid (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName) (src : LintLevelSource)
    (hcap : opts.lintCap = some .allow)
    (hd : opts.driverCaps lint = none)
    (hprobe : probe lint = some ⟨.forbid, none, src⟩)
    (hnotfw : src.isCliForceWarn = false) :
    (revealActualLevelSpec opts probe lint).level = .allow := by
  unfold revealActualLevelSpec
  rw [hprobe, hcap, hd]
  dsimp only
  rw [hnotfw]
  rfl

theorem reveal_driverCap_always_bounds (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName) (dCap : LintLevel)
    (hd : opts.driverCaps lint = some dCap) :
    LintLevel.le (revealActualLevelSpec opts probe lint).level dCap := by
  unfold revealActualLevelSpec
  rw [hd]
  exact LintLevel.min_le_right _ dCap

/-- `#[forbid(warnings)]` affects `Warn`-by-default lints (`dead_code`), promoting them to `Forbid`
with `src` pointing to `warnings`, whereas `Allow`-by-default lints (`unsafe_code`) are untouched! -/
theorem forbid_warnings_promotes_dead_code_but_not_unsafe_code (opts : LintSessionOpts)
    (hcap : opts.lintCap = none) (hdDead : opts.driverCaps .deadCode = none)
    (hdUnsafe : opts.driverCaps .unsafeCode = none)
    (wSrc : LintLevelSource) (hnotfw : wSrc.isCliForceWarn = false) :
    let probe : LintName → Option LevelSpec := fun l =>
      if LintName.beq l .warnings then some ⟨.forbid, none, wSrc⟩ else none
    (revealActualLevelSpec opts probe .deadCode).level = .forbid ∧
      (revealActualLevelSpec opts probe .unsafeCode).level = .allow := by
  constructor
  · let probe : LintName → Option LevelSpec := fun l =>
      if LintName.beq l .warnings then some ⟨.forbid, none, wSrc⟩ else none
    have h_step : revealActualLevelSpec opts probe .deadCode =
        (if wSrc.isCliForceWarn = true then (⟨.forbid, none, wSrc⟩ : LevelSpec)
         else ⟨LintLevel.min .forbid .forbid, none, wSrc⟩) := by
      unfold revealActualLevelSpec
      rw [hcap, hdDead]
      rfl
    rw [h_step, ite_false_pf (fun h => Bool.noConfusion (h.symm.trans hnotfw))]
    rfl
  · unfold revealActualLevelSpec
    rw [hcap, hdUnsafe]
    rfl

end CliAndRevealSection

/-! ## Part 5: `LintLevelsBuilder::insert_spec` & `Forbid` Un-Overridability (`E0453` vs FCW) -/

section InsertSpecSection

/-- Diagnostic errors and FCWs raised during `LintLevelsBuilder::insert_spec`. -/
inductive BuilderDiag where
  | overruledAttributeE0453 (lint : LintName) (attempted : LintLevel) (oldSrc : LintLevelSource)
  | forbiddenLintGroupsFCW (lint : LintName) (attempted : LintLevel) (oldSrc : LintLevelSource)

structure ScopeState where
  specs : LintName → Option LevelSpec
  diags : List BuilderDiag

noncomputable def ScopeState.setSpec (st : ScopeState) (id : LintName) (s : LevelSpec) : ScopeState :=
  ⟨fun x => if LintName.beq x id then some s else st.specs x, st.diags⟩

noncomputable def ScopeState.addDiag (st : ScopeState) (d : BuilderDiag) : ScopeState :=
  ⟨st.specs, st.diags ++ [d]⟩

theorem ScopeState.setSpec_self (st : ScopeState) (id : LintName) (s : LevelSpec) :
    (st.setSpec id s).specs id = some s := by
  unfold ScopeState.setSpec
  dsimp only
  rw [LintName.beq_refl id]
  rfl

theorem ScopeState.setSpec_other (st : ScopeState) {id x : LintName} (s : LevelSpec) (hne : x ≠ id) :
    (st.setSpec id s).specs x = st.specs x := by
  unfold ScopeState.setSpec
  dsimp only
  cases h : LintName.beq x id with
  | false => rfl
  | true => exact False.elim (hne (LintName.beq_sound h))

/-- Mirrors `LintLevelsBuilder::insert_spec` (`compiler/rustc_lint/src/levels.rs:570-668`).
`lintAddedLints = true` in post-expansion `early_lint_checks` and `late` lint checks;
`lintAddedLints = false` in `shallow_lint_levels_on` and `pre_expansion`. -/
noncomputable def insertSpec (opts : LintSessionOpts) (lintAddedLints : Bool)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec) : ScopeState :=
  let oldSpec := revealActualLevelSpec opts st.specs id
  let oldLevel := oldSpec.level
  let oldSrc := oldSpec.src
  let level := newSpec.level
  if lintAddedLints && LintLevel.beq level .deny && LintLevel.beq oldLevel .forbid then
    st
  else if lintAddedLints && (!LintLevel.beq level .forbid) && LintLevel.beq oldLevel .forbid then
    let fcw := oldSrc.isLintGroupSource
    if !fcw then
      st.addDiag (.overruledAttributeE0453 id level oldSrc)
    else
      let st1 := st.addDiag (.forbiddenLintGroupsFCW id level oldSrc)
      if LintLevel.beq level .expect && LintName.beq id .unfulfilledLintExpectations then
        st1
      else
        match oldLevel, level with
        | .forceWarn, .expect => st1.setSpec id ⟨.forceWarn, newSpec.lintId, oldSrc⟩
        | .forceWarn, _ => st1.setSpec id ⟨.forceWarn, none, oldSrc⟩
        | _, _ => st1.setSpec id newSpec
  else if LintLevel.beq level .expect && LintName.beq id .unfulfilledLintExpectations then
    st
  else
    match oldLevel, level with
    | .forceWarn, .expect => st.setSpec id ⟨.forceWarn, newSpec.lintId, oldSrc⟩
    | .forceWarn, _ => st.setSpec id ⟨.forceWarn, none, oldSrc⟩
    | _, _ => st.setSpec id newSpec

/-- `insertSpec` preserves `LevelSpec.WF` across every branch. -/
theorem insertSpec_preserves_WF (opts : LintSessionOpts) (lintAddedLints : Bool)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec)
    (hwfAll : ∀ k s, st.specs k = some s → LevelSpec.WF s)
    (hwfNew : LevelSpec.WF newSpec) :
    ∀ k s, (insertSpec opts lintAddedLints st id newSpec).specs k = some s → LevelSpec.WF s := by
  intro k s hs
  unfold insertSpec at hs
  dsimp only at hs
  cases h1 : (lintAddedLints && LintLevel.beq newSpec.level .deny &&
      LintLevel.beq (revealActualLevelSpec opts st.specs id).level .forbid)
  · rw [h1, ite_false_pf Bool.false_ne_true] at hs
    cases h2 : (lintAddedLints && (!LintLevel.beq newSpec.level .forbid) &&
        LintLevel.beq (revealActualLevelSpec opts st.specs id).level .forbid)
    · rw [h2, ite_false_pf Bool.false_ne_true] at hs
      cases h3 : (LintLevel.beq newSpec.level .expect && LintName.beq id .unfulfilledLintExpectations)
      · rw [h3, ite_false_pf Bool.false_ne_true] at hs
        cases hold : (revealActualLevelSpec opts st.specs id).level <;>
        cases hnew : newSpec.level <;>
        rw [hold, hnew] at hs <;>
        try dsimp only at hs <;>
        (try exact hwfAll k s hs)
        all_goals (
          unfold ScopeState.setSpec at hs
          dsimp only at hs
          cases hkx : LintName.beq k id with
          | false => rw [hkx, ite_false_pf Bool.false_ne_true] at hs; exact hwfAll k s hs
          | true =>
            rw [hkx, ite_true_pf rfl] at hs
            cases hs
            first
            | exact LevelSpec.wf_forceWarn _ _
            | exact hwfNew
        )
      · rw [h3, ite_true_pf rfl] at hs
        exact hwfAll k s hs
    · rw [h2, ite_true_pf rfl] at hs
      cases hfcw : (revealActualLevelSpec opts st.specs id).src.isLintGroupSource
      · rw [hfcw] at hs
        try dsimp only at hs
        rw [ite_true_pf (show (!false) = true from rfl)] at hs
        exact hwfAll k s hs
      · rw [hfcw] at hs
        try dsimp only at hs
        rw [ite_false_pf (show ¬ ((!true) = true) from Bool.noConfusion)] at hs
        cases h3 : (LintLevel.beq newSpec.level .expect && LintName.beq id .unfulfilledLintExpectations)
        · rw [h3, ite_false_pf Bool.false_ne_true] at hs
          cases hold : (revealActualLevelSpec opts st.specs id).level <;>
          cases hnew : newSpec.level <;>
          rw [hold, hnew] at hs <;>
          try dsimp only at hs
          all_goals (
            unfold ScopeState.setSpec ScopeState.addDiag at hs
            dsimp only at hs
            cases hkx : LintName.beq k id with
            | false => rw [hkx, ite_false_pf Bool.false_ne_true] at hs; exact hwfAll k s hs
            | true =>
              rw [hkx, ite_true_pf rfl] at hs
              cases hs
              first
              | exact LevelSpec.wf_forceWarn _ _
              | exact hwfNew
          )
        · rw [h3, ite_true_pf rfl] at hs
          exact hwfAll k s hs
  · rw [h1, ite_true_pf rfl] at hs
    exact hwfAll k s hs

/-- **Pillar 1 Theorem 1 (`Forbid` Monotonicity & Un-Overridability Invariant):**
When `lintAddedLints = true` and `id` currently reveals as `.forbid` from a **direct**
(non-group) source, ANY scoped attribute setting `newSpec`:
1. If `newSpec.level = .forbid`: raises/keeps `.forbid` with zero new diagnostics.
2. If `newSpec.level = .deny`: is silently ignored, leaving `st` completely unchanged (still `.forbid`).
3. If `newSpec.level ∈ {.allow, .expect, .warn, .forceWarn}`: emits `overruledAttributeE0453`,
   does NOT modify `st.specs`, and keeps `id` at `.forbid`! -/
theorem insertSpec_direct_forbid_unoverridable (opts : LintSessionOpts)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec)
    (hforbid : (revealActualLevelSpec opts st.specs id).level = .forbid)
    (hdirect : (revealActualLevelSpec opts st.specs id).src.isLintGroupSource = false) :
    let st' := insertSpec opts true st id newSpec
    (newSpec.level = .deny → st' = st) ∧
    (newSpec.level ≠ .forbid → newSpec.level ≠ .deny →
      st' = st.addDiag (.overruledAttributeE0453 id newSpec.level (revealActualLevelSpec opts st.specs id).src) ∧
      (revealActualLevelSpec opts st'.specs id).level = .forbid) ∧
    (newSpec.level = .forbid → st' = st.setSpec id newSpec) := by
  intro st'
  refine ⟨?_, ?_, ?_⟩
  · intro hdeny
    show insertSpec opts true st id newSpec = st
    unfold insertSpec
    dsimp only
    rw [hforbid, hdeny]
    rfl
  · intro hnf hnd
    have hneFb : LintLevel.beq newSpec.level .forbid = false := by
      cases hl : newSpec.level <;> first | rfl | exact False.elim (hnf hl)
    have hneDn : LintLevel.beq newSpec.level .deny = false := by
      cases hl : newSpec.level <;> first | rfl | exact False.elim (hnd hl)
    have hdiag : st' = st.addDiag (.overruledAttributeE0453 id newSpec.level (revealActualLevelSpec opts st.specs id).src) := by
      show insertSpec opts true st id newSpec = _
      unfold insertSpec
      dsimp only
      rw [hforbid, hneDn, hneFb, hdirect]
      rfl
    refine ⟨hdiag, ?_⟩
    rw [hdiag]
    exact hforbid
  · intro hfb
    show insertSpec opts true st id newSpec = st.setSpec id newSpec
    unfold insertSpec
    dsimp only
    rw [hforbid, hfb]
    rfl

/-- **Pillar 1 Theorem 2 (`forbidden_lint_groups` FCW Does Apply Inner Level):**
When `id` reveals as `.forbid` from a **lint group** (such as `unused` or `warnings`),
an inner `#[allow(id)]` or `#[expect(id)]` (for `id ≠ unfulfilled_lint_expectations`)
emits `forbiddenLintGroupsFCW` (NOT `E0453`) and **lowers** the stored spec to `newSpec`! -/
theorem insertSpec_group_forbid_emits_fcw_and_lowers (opts : LintSessionOpts)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec)
    (hforbid : (revealActualLevelSpec opts st.specs id).level = .forbid)
    (hgroup : (revealActualLevelSpec opts st.specs id).src.isLintGroupSource = true)
    (hnotfb : newSpec.level ≠ .forbid) (hnotdn : newSpec.level ≠ .deny)
    (hnotspecial : ¬ (newSpec.level = .expect ∧ id = .unfulfilledLintExpectations)) :
    let st' := insertSpec opts true st id newSpec
    st' = (st.addDiag (.forbiddenLintGroupsFCW id newSpec.level (revealActualLevelSpec opts st.specs id).src)).setSpec id newSpec ∧
    st'.specs id = some newSpec := by
  have hneFb : LintLevel.beq newSpec.level .forbid = false := by
    cases hl : newSpec.level <;> first | rfl | exact False.elim (hnotfb hl)
  have hneDn : LintLevel.beq newSpec.level .deny = false := by
    cases hl : newSpec.level <;> first | rfl | exact False.elim (hnotdn hl)
  have hnotSp : (LintLevel.beq newSpec.level .expect && LintName.beq id .unfulfilledLintExpectations) = false := by
    cases hl : newSpec.level <;> try rfl
    cases hid : LintName.beq id .unfulfilledLintExpectations with
    | false => rfl
    | true => exact False.elim (hnotspecial ⟨hl, LintName.beq_sound hid⟩)
  have hst : insertSpec opts true st id newSpec =
      (st.addDiag (.forbiddenLintGroupsFCW id newSpec.level (revealActualLevelSpec opts st.specs id).src)).setSpec id newSpec := by
    unfold insertSpec
    dsimp only
    rw [hforbid, hneDn, hneFb, hgroup, hnotSp]
    dsimp only
    cases hl : newSpec.level <;> first | rfl | exact False.elim (hnotfb hl)
  refine ⟨hst, ?_⟩
  rw [hst]
  exact ScopeState.setSpec_self _ id newSpec

/-- **Pillar 1 Theorem 3 (`--cap-lints <= deny` Eliminates `E0453`):**
Because `insert_spec` inspects the *revealed* `old_level` (post-`--cap-lints`),
whenever `--cap-lints` caps below `.forbid`, `old_level ≠ .forbid` and NO attribute emits `E0453`. -/
theorem insertSpec_cap_below_forbid_no_e0453 (opts : LintSessionOpts)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec)
    (hneForbid : (revealActualLevelSpec opts st.specs id).level ≠ .forbid)
    (hnoInitE0453 : ∀ d, d ∈ st.diags → match d with | .overruledAttributeE0453 _ _ _ => False | _ => True) :
    ∀ d, d ∈ (insertSpec opts true st id newSpec).diags →
      match d with | .overruledAttributeE0453 _ _ _ => False | _ => True := by
  intro d hd
  unfold insertSpec at hd
  dsimp only at hd
  have hbf : LintLevel.beq (revealActualLevelSpec opts st.specs id).level .forbid = false := by
    cases hl : (revealActualLevelSpec opts st.specs id).level <;>
      first | rfl | exact False.elim (hneForbid hl)
  rw [hbf] at hd
  cases hb1 : (true && LintLevel.beq newSpec.level .deny && false) <;> try rw [hb1] at hd
  all_goals (
    cases hb2 : (true && (!LintLevel.beq newSpec.level .forbid) && false)
    · rw [hb2] at hd
      cases hb3 : (LintLevel.beq newSpec.level .expect && LintName.beq id .unfulfilledLintExpectations)
      · rw [hb3] at hd
        try dsimp only at hd
        cases hold : (revealActualLevelSpec opts st.specs id).level <;>
        cases hnew : newSpec.level <;>
        rw [hold, hnew] at hd <;>
        try dsimp only at hd <;>
        exact hnoInitE0453 d hd
      · rw [hb3] at hd
        exact hnoInitE0453 d hd
    · rw [Bool.and_false] at hb2
      exact Bool.noConfusion hb2
  )

/-- **Pillar 1 Theorem 4 (`ForceWarn` Retains `Expect` ID Without Changing Level):**
Mirrors `levels.rs:658-664`: under `ForceWarn`, `#[expect(id)]` attaches `lintId` into
`ForceWarn`, whereas `#[allow(id)]` / `#[warn(id)]` / `#[forbid(id)]` drops `lintId` and keeps `ForceWarn`. -/
theorem insertSpec_under_forceWarn (opts : LintSessionOpts) (lintAddedLints : Bool)
    (st : ScopeState) (id : LintName) (newSpec : LevelSpec) (oldSrc : LintLevelSource)
    (oldEid : Option CanonExpectId)
    (hfw : revealActualLevelSpec opts st.specs id = ⟨.forceWarn, oldEid, oldSrc⟩)
    (hnotSelfExpect : ¬ (newSpec.level = .expect ∧ id = .unfulfilledLintExpectations)) :
    let st' := insertSpec opts lintAddedLints st id newSpec
    (newSpec.level = .expect → st'.specs id = some ⟨.forceWarn, newSpec.lintId, oldSrc⟩) ∧
    (newSpec.level ≠ .expect → st'.specs id = some ⟨.forceWarn, none, oldSrc⟩) := by
  have hneSp : (LintLevel.beq newSpec.level .expect && LintName.beq id .unfulfilledLintExpectations) = false := by
    cases hl : newSpec.level <;> try rfl
    cases hid : LintName.beq id .unfulfilledLintExpectations with
    | false => rfl
    | true => exact False.elim (hnotSelfExpect ⟨hl, LintName.beq_sound hid⟩)
  refine ⟨?_, ?_⟩
  · intro hexp
    show (insertSpec opts lintAddedLints st id newSpec).specs id = some ⟨.forceWarn, newSpec.lintId, oldSrc⟩
    unfold insertSpec
    dsimp only
    rw [hfw]
    rw [hexp] at hneSp
    rw [hexp]
    dsimp only
    rw [hneSp]
    cases lintAddedLints <;> exact ScopeState.setSpec_self st id _
  · intro hne
    show (insertSpec opts lintAddedLints st id newSpec).specs id = some ⟨.forceWarn, none, oldSrc⟩
    unfold insertSpec
    dsimp only
    rw [hfw]
    dsimp only
    cases hl : newSpec.level with
    | expect => exact False.elim (hne hl)
    | allow | warn | forceWarn | deny | forbid =>
      cases lintAddedLints <;> exact ScopeState.setSpec_self st id _

/-- **Pillar 1 Theorem 5 (Multi-Attribute SequenceStickiness):**
Over any list of inner attributes applied under a direct uncapped `Forbid`, the revealed level
of `id` remains `.forbid`! -/
noncomputable def applyAttrList (opts : LintSessionOpts) (lintAddedLints : Bool)
    (st : ScopeState) (attrs : List (LintName × LevelSpec)) : ScopeState :=
  attrs.foldl (fun acc (k, sp) => insertSpec opts lintAddedLints acc k sp) st

theorem applyAttrList_direct_forbid_invariant (opts : LintSessionOpts)
    (st : ScopeState) (id : LintName) (attrs : List (LintName × LevelSpec))
    (hcap : opts.lintCap = none ∨ opts.lintCap = some .forbid)
    (hd : opts.driverCaps id = none)
    (hattrs : ∀ k sp, (k, sp) ∈ attrs → k = id → sp.level = .forbid →
      sp.src.isLintGroupSource = false ∧ sp.src.isCliForceWarn = false)
    (hinit : ∃ s, st.specs id = some s ∧ s.level = .forbid ∧
      s.src.isLintGroupSource = false ∧ s.src.isCliForceWarn = false) :
    ∃ s, (applyAttrList opts true st attrs).specs id = some s ∧
      s.level = .forbid ∧ s.src.isLintGroupSource = false ∧ s.src.isCliForceWarn = false := by
  revert hattrs hinit
  induction attrs generalizing st with
  | nil => intro _ hinit'; exact hinit'
  | cons pair rest ih =>
    intro hattrs hinit'
    cases pair with
    | mk k sp =>
      have htail : ∀ k' sp', (k', sp') ∈ rest → k' = id → sp'.level = .forbid →
          sp'.src.isLintGroupSource = false ∧ sp'.src.isCliForceWarn = false :=
        fun k' sp' hm => hattrs k' sp' (List.Mem.tail (k, sp) hm)
      apply ih _ htail
      cases hk : LintName.beq k id with
      | false =>
        have hne : id ≠ k := fun heq => by
          subst heq
          rw [LintName.beq_refl id] at hk
          exact Bool.noConfusion hk
        unfold insertSpec
        dsimp only
        cases hb1 : (true && LintLevel.beq sp.level .deny && LintLevel.beq (revealActualLevelSpec opts st.specs k).level .forbid)
        · (try rw [hb1])
          rw [ite_false_pf Bool.false_ne_true]
          cases hb2 : (true && (!LintLevel.beq sp.level .forbid) && LintLevel.beq (revealActualLevelSpec opts st.specs k).level .forbid)
          · (try rw [hb2])
            rw [ite_false_pf Bool.false_ne_true]
            cases hb3 : (LintLevel.beq sp.level .expect && LintName.beq k .unfulfilledLintExpectations)
            · (try rw [hb3])
              rw [ite_false_pf Bool.false_ne_true]
              cases (revealActualLevelSpec opts st.specs k).level <;> cases sp.level <;> (try dsimp only) <;>
                (unfold ScopeState.setSpec; dsimp only; rw [ite_false_pf (fun h => hne (LintName.beq_sound h))]; exact hinit')
            · (try rw [hb3])
              rw [ite_true_pf rfl]; exact hinit'
          · (try rw [hb2])
            rw [ite_true_pf rfl]
            cases hfcw : (revealActualLevelSpec opts st.specs k).src.isLintGroupSource
            · (try rw [hfcw])
              (try dsimp only)
              rw [ite_true_pf (show (!false) = true from rfl)]
              exact hinit'
            · (try rw [hfcw])
              (try dsimp only)
              rw [ite_false_pf (show ¬ ((!true) = true) from Bool.noConfusion)]
              cases hb3 : (LintLevel.beq sp.level .expect && LintName.beq k .unfulfilledLintExpectations)
              · (try rw [hb3])
                rw [ite_false_pf Bool.false_ne_true]
                cases (revealActualLevelSpec opts st.specs k).level <;> cases sp.level <;> (try dsimp only) <;>
                  (unfold ScopeState.setSpec ScopeState.addDiag; dsimp only; rw [ite_false_pf (fun h => hne (LintName.beq_sound h))]; exact hinit')
              · (try rw [hb3])
                rw [ite_true_pf rfl]; exact hinit'
        · (try rw [hb1])
          rw [ite_true_pf rfl]; exact hinit'
      | true =>
        have heq : k = id := LintName.beq_sound hk
        subst heq
        rcases hinit' with ⟨s, hs, hsl, hsg, hsfw⟩
        have hrev : (revealActualLevelSpec opts st.specs k).level = .forbid ∧
                    (revealActualLevelSpec opts st.specs k).src.isLintGroupSource = false := by
          unfold revealActualLevelSpec
          rw [hs, hd]
          dsimp only
          rw [hsl]
          dsimp only
          rw [ite_false_pf (fun h => Bool.noConfusion (h.symm.trans hsfw))]
          dsimp only
          rw [hsl]
          cases hcap with
          | inl hnone => rw [hnone]; exact ⟨rfl, hsg⟩
          | inr hfb => rw [hfb]; exact ⟨rfl, hsg⟩
        have hdir := insertSpec_direct_forbid_unoverridable opts st k sp hrev.1 hrev.2
        dsimp only
        cases hspl : sp.level with
        | deny =>
          rw [hdir.1 hspl]
          exact ⟨s, hs, hsl, hsg, hsfw⟩
        | forbid =>
          have hpair := hattrs k sp (List.Mem.head rest) rfl hspl
          rw [hdir.2.2 hspl]
          exact ⟨sp, ScopeState.setSpec_self st k sp, hspl, hpair.1, hpair.2⟩
        | allow =>
          have hnotfb : sp.level ≠ .forbid := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          have hnotdn : sp.level ≠ .deny := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          rw [(hdir.2.1 hnotfb hnotdn).1]
          exact ⟨s, hs, hsl, hsg, hsfw⟩
        | expect =>
          have hnotfb : sp.level ≠ .forbid := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          have hnotdn : sp.level ≠ .deny := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          rw [(hdir.2.1 hnotfb hnotdn).1]
          exact ⟨s, hs, hsl, hsg, hsfw⟩
        | warn =>
          have hnotfb : sp.level ≠ .forbid := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          have hnotdn : sp.level ≠ .deny := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          rw [(hdir.2.1 hnotfb hnotdn).1]
          exact ⟨s, hs, hsl, hsg, hsfw⟩
        | forceWarn =>
          have hnotfb : sp.level ≠ .forbid := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          have hnotdn : sp.level ≠ .deny := fun h => by rw [hspl] at h; exact LintLevel.noConfusion h
          rw [(hdir.2.1 hnotfb hnotdn).1]
          exact ⟨s, hs, hsl, hsg, hsfw⟩

/-- **Compiler Quirk Witness (`#![forbid(dead_code)] #[forbid(unused)] #[allow(dead_code)]`):**
Because `insert_spec` overwrites a direct `old_src` with a group `forbid` source when `level == Forbid`,
a subsequent `#[allow(dead_code)]` hits the `forbidden_lint_groups` FCW path rather than `E0453` and
successfully lowers `dead_code` to `Allow`! -/
theorem direct_forbid_group_forbid_allow_loophole_witness :
    let opts : LintSessionOpts := ⟨none, fun _ => none, false⟩
    let init : ScopeState := ⟨fun _ => none, []⟩
    let directForbid : LevelSpec := ⟨.forbid, none, .nodeSrc (.lint .deadCode) 1 none⟩
    let groupForbid : LevelSpec := ⟨.forbid, none, .nodeSrc .groupUnused 2 none⟩
    let innerAllow : LevelSpec := ⟨.allow, none, .nodeSrc (.lint .deadCode) 3 none⟩
    let finalSt := applyAttrList opts true init
      [(.deadCode, directForbid), (.deadCode, groupForbid), (.deadCode, innerAllow)]
    (revealActualLevelSpec opts finalSt.specs .deadCode).level = .allow ∧
    finalSt.diags = [.forbiddenLintGroupsFCW .deadCode .allow (.nodeSrc .groupUnused 2 none)] := by
  exact ⟨rfl, rfl⟩

end InsertSpecSection

/-! ## Part 6: `emit_lint_base`, `DiagCtxt`, and RFC 2383 `#[expect]` Conservation -/

section EmitAndExpectSection

/-- Mirrors `rustc_errors::Level` outcomes produced by `emit_lint_base`. -/
inductive EmittedDiagLevel where
  | err
  | forceWarning
  | warning
  | expectSilent
  | futureCompatOnlyAllow

structure EmittedDiag where
  lint : LintName
  level : EmittedDiagLevel
  expectId : Option CanonExpectId

structure DeclaredExpectation where
  id : CanonExpectId
  lint : LintName
  reason : Option String
  isUnfulfilledLintExpectations : Bool

structure DiagCtxtState where
  emitted : List EmittedDiag
  fulfilled : List CanonExpectId
  futureBreakage : List LintName

noncomputable def emptyDiagCtxt : DiagCtxtState := ⟨[], [], []⟩

/-- Mirrors `emit_lint_base` (`compiler/rustc_middle/src/lint.rs:386-587`) combined with
`DiagCtxtInner::emit_diagnostic` (`compiler/rustc_errors/src/lib.rs:1197-1345`). -/
noncomputable def emitLintBase (opts : LintSessionOpts) (spec : LevelSpec)
    (lint : LintName) (inExternalMacro : Bool) (dcx : DiagCtxtState) : DiagCtxtState :=
  let lmeta := builtinLintMeta lint
  let hasFutureBreakage := lmeta.futureCompatReportInDeps
  let errLevelOpt : Option EmittedDiagLevel :=
    match spec.level with
    | .allow => if hasFutureBreakage then some .futureCompatOnlyAllow else none
    | .expect => some .expectSilent
    | .forceWarn => some .forceWarning
    | .warn => some .warning
    | .deny | .forbid => some .err
  match errLevelOpt with
  | none => dcx
  | some errLvl =>
    if inExternalMacro && !lmeta.reportInExternalMacro then
      dcx
    else
      let dcx1 : DiagCtxtState :=
        if hasFutureBreakage then ⟨dcx.emitted, dcx.fulfilled, dcx.futureBreakage ++ [lint]⟩ else dcx
      match errLvl with
      | .futureCompatOnlyAllow => dcx1
      | .warning =>
        if !opts.canEmitWarnings then dcx1
        else ⟨dcx1.emitted ++ [⟨lint, .warning, spec.lintId⟩], dcx1.fulfilled, dcx1.futureBreakage⟩
      | .expectSilent =>
        match spec.lintId with
        | some eid => ⟨dcx1.emitted, dcx1.fulfilled ++ [eid], dcx1.futureBreakage⟩
        | none => dcx1
      | .forceWarning =>
        let ful1 := match spec.lintId with | some eid => dcx1.fulfilled ++ [eid] | none => dcx1.fulfilled
        ⟨dcx1.emitted ++ [⟨lint, .forceWarning, spec.lintId⟩], ful1, dcx1.futureBreakage⟩
      | .err =>
        ⟨dcx1.emitted ++ [⟨lint, .err, spec.lintId⟩], dcx1.fulfilled, dcx1.futureBreakage⟩

noncomputable def isFulfilled (id : CanonExpectId) (fulfilled : List CanonExpectId) : Bool :=
  listAny (CanonExpectId.beq id) fulfilled

theorem isFulfilled_iff_mem (id : CanonExpectId) (fulfilled : List CanonExpectId) :
    isFulfilled id fulfilled = true ↔ id ∈ fulfilled := by
  constructor
  · intro h
    match listMem_of_listAny_true (CanonExpectId.beq id) h with
    | ⟨x, hx, hbeq⟩ =>
      have heq : id = x := CanonExpectId.beq_sound hbeq
      subst heq
      exact hx
  · intro h
    exact listAny_eq_true_of_mem (CanonExpectId.beq id) h (CanonExpectId.beq_refl id)

/-- Mirrors `check_expectations` (`compiler/rustc_lint/src/expect.rs:28-64`):
every declared expectation not in `fulfilled` emits `unfulfilled_lint_expectations`. -/
noncomputable def checkExpectations (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec)
    (declared : List DeclaredExpectation)
    (dcx : DiagCtxtState) : DiagCtxtState :=
  let unfulfilledSpec := revealActualLevelSpec opts probe .unfulfilledLintExpectations
  declared.foldl (fun acc exp =>
    if isFulfilled exp.id acc.fulfilled then
      acc
    else
      emitLintBase opts unfulfilledSpec .unfulfilledLintExpectations false acc) dcx

theorem emitLintBase_preserves_fulfilled_mem (opts : LintSessionOpts) (spec : LevelSpec)
    (lint : LintName) (ext : Bool) (dcx : DiagCtxtState) (id : CanonExpectId)
    (h : id ∈ dcx.fulfilled) :
    id ∈ (emitLintBase opts spec lint ext dcx).fulfilled := by
  unfold emitLintBase
  cases spec.level <;> (try dsimp only)
  · cases hfc : (builtinLintMeta lint).futureCompatReportInDeps
    · (try rw [hfc]); (repeat rw [ite_false_pf Bool.false_ne_true]); exact h
    · (try rw [hfc]); (repeat rw [ite_true_pf rfl]); (try dsimp only)
      cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
      · (try rw [hext])
        (repeat rw [ite_false_pf Bool.false_ne_true])
        (repeat rw [ite_true_pf rfl])
        (try dsimp only)
        exact h
      · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext]); (repeat rw [ite_false_pf Bool.false_ne_true]); (try dsimp only)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hsid : spec.lintId <;>
      (try rw [hfc]) <;> (try rw [hsid]) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true]) <;>
      (repeat rw [ite_true_pf rfl]) <;>
      (try dsimp only) <;>
      first | exact h | exact List.mem_append_left _ h
    · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext]); (repeat rw [ite_false_pf Bool.false_ne_true]); (try dsimp only)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hcw : opts.canEmitWarnings <;>
      (try rw [hfc]) <;> (try rw [hcw]) <;> (try dsimp only) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true]) <;>
      (repeat rw [ite_true_pf rfl]) <;>
      (repeat rw [ite_false_pf (show ¬ ((!true) = true) from Bool.noConfusion)]) <;>
      (repeat rw [ite_true_pf (show (!false) = true from rfl)]) <;>
      (try dsimp only) <;>
      exact h
    · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext]); (repeat rw [ite_false_pf Bool.false_ne_true]); (try dsimp only)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hsid : spec.lintId <;>
      (try rw [hfc]) <;> (try rw [hsid]) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true]) <;>
      (repeat rw [ite_true_pf rfl]) <;>
      (try dsimp only) <;>
      first | exact h | exact List.mem_append_left _ h
    · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext]); (repeat rw [ite_false_pf Bool.false_ne_true]); (try dsimp only)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      (try rw [hfc]) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true]) <;>
      (repeat rw [ite_true_pf rfl]) <;>
      (try dsimp only) <;>
      exact h
    · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext]); (repeat rw [ite_false_pf Bool.false_ne_true]); (try dsimp only)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      (try rw [hfc]) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true]) <;>
      (repeat rw [ite_true_pf rfl]) <;>
      (try dsimp only) <;>
      exact h
    · (try rw [hext]); (repeat rw [ite_true_pf rfl]); exact h

theorem emitLintBase_only_adds_spec_lintId (opts : LintSessionOpts) (spec : LevelSpec)
    (lint : LintName) (ext : Bool) (dcx : DiagCtxtState) (id : CanonExpectId)
    (h : id ∈ (emitLintBase opts spec lint ext dcx).fulfilled) :
    id ∈ dcx.fulfilled ∨ spec.lintId = some id := by
  unfold emitLintBase at h
  cases hsl : spec.level <;> (try rw [hsl] at h) <;> (try dsimp only at h)
  · cases hfc : (builtinLintMeta lint).futureCompatReportInDeps
    · (try rw [hfc] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; exact Or.inl h
    · (try rw [hfc] at h); repeat rw [ite_true_pf rfl] at h; (try dsimp only at h)
      cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
      · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h
        (try dsimp only at h)
        repeat rw [ite_true_pf rfl] at h
        (try dsimp only at h)
        exact Or.inl h
      · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; (try dsimp only at h)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hsid : spec.lintId <;>
      (try rw [hfc] at h) <;> (try rw [hsid] at h) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true] at h) <;>
      (repeat rw [ite_true_pf rfl] at h) <;>
      (try dsimp only at h)
      · exact Or.inl h
      · cases List.mem_append.mp h with
        | inl hl => exact Or.inl hl
        | inr hr => cases hr with | head _ => exact Or.inr rfl | tail _ hnil => nomatch hnil
      · exact Or.inl h
      · cases List.mem_append.mp h with
        | inl hl => exact Or.inl hl
        | inr hr => cases hr with | head _ => exact Or.inr rfl | tail _ hnil => nomatch hnil
    · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; (try dsimp only at h)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hcw : opts.canEmitWarnings <;>
      (try rw [hfc] at h) <;> (try rw [hcw] at h) <;> (try dsimp only at h) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true] at h) <;>
      (repeat rw [ite_true_pf rfl] at h) <;>
      (repeat rw [ite_false_pf (show ¬ ((!true) = true) from Bool.noConfusion)] at h) <;>
      (repeat rw [ite_true_pf (show (!false) = true from rfl)] at h) <;>
      (try dsimp only at h) <;>
      exact Or.inl h
    · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; (try dsimp only at h)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      cases hsid : spec.lintId <;>
      (try rw [hfc] at h) <;> (try rw [hsid] at h) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true] at h) <;>
      (repeat rw [ite_true_pf rfl] at h) <;>
      (try dsimp only at h)
      · exact Or.inl h
      · cases List.mem_append.mp h with
        | inl hl => exact Or.inl hl
        | inr hr => cases hr with | head _ => exact Or.inr rfl | tail _ hnil => nomatch hnil
      · exact Or.inl h
      · cases List.mem_append.mp h with
        | inl hl => exact Or.inl hl
        | inr hr => cases hr with | head _ => exact Or.inr rfl | tail _ hnil => nomatch hnil
    · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; (try dsimp only at h)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      (try rw [hfc] at h) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true] at h) <;>
      (repeat rw [ite_true_pf rfl] at h) <;>
      (try dsimp only at h) <;> exact Or.inl h
    · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h
  · cases hext : (ext && !(builtinLintMeta lint).reportInExternalMacro)
    · (try rw [hext] at h); repeat rw [ite_false_pf Bool.false_ne_true] at h; (try dsimp only at h)
      cases hfc : (builtinLintMeta lint).futureCompatReportInDeps <;>
      (try rw [hfc] at h) <;>
      (repeat rw [ite_false_pf Bool.false_ne_true] at h) <;>
      (repeat rw [ite_true_pf rfl] at h) <;>
      (try dsimp only at h) <;> exact Or.inl h
    · (try rw [hext] at h); repeat rw [ite_true_pf rfl] at h; exact Or.inl h

/-- **Pillar 3 Theorem 1 (Expectation Fulfillment Conservation — Exact Partition):**
For a single declared expectation `exp` evaluated after all lint passes finish (`dcx`),
assuming `unfulfilled_lint_expectations` is not suppressed to `Allow` (nor `Warn` with
`canEmitWarnings = false`):
- `exp` was fulfilled during the lint passes (`exp.id ∈ dcx.fulfilled`) **if and only if**
  `checkExpectations` emits ZERO `unfulfilled_lint_expectations` warning/error! -/
theorem expect_fulfillment_exact_conservation (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (exp : DeclaredExpectation) (dcx : DiagCtxtState)
    (hUnfulActive : (revealActualLevelSpec opts probe .unfulfilledLintExpectations).level = .warn)
    (hCanWarn : opts.canEmitWarnings = true)
    (hEmptyInit : dcx.emitted = []) :
    let finalDcx := checkExpectations opts probe [exp] dcx
    (exp.id ∈ dcx.fulfilled → finalDcx.emitted = []) ∧
    (exp.id ∉ dcx.fulfilled →
      finalDcx.emitted = [⟨.unfulfilledLintExpectations, .warning,
        (revealActualLevelSpec opts probe .unfulfilledLintExpectations).lintId⟩]) := by
  refine ⟨?_, ?_⟩
  · intro hmem
    have hful : isFulfilled exp.id dcx.fulfilled = true :=
      (isFulfilled_iff_mem exp.id dcx.fulfilled).mpr hmem
    show (if isFulfilled exp.id dcx.fulfilled then dcx else _).emitted = []
    rw [hful]
    exact hEmptyInit
  · intro hnmem
    have hnotful : isFulfilled exp.id dcx.fulfilled = false := by
      cases hf : isFulfilled exp.id dcx.fulfilled with
      | false => rfl
      | true => exact False.elim (hnmem ((isFulfilled_iff_mem exp.id dcx.fulfilled).mp hf))
    show (if isFulfilled exp.id dcx.fulfilled then dcx else
      emitLintBase opts (revealActualLevelSpec opts probe .unfulfilledLintExpectations)
        .unfulfilledLintExpectations false dcx).emitted = _
    rw [hnotful, ite_false_pf Bool.false_ne_true]
    unfold emitLintBase
    rw [hUnfulActive]
    dsimp only [builtinLintMeta]
    rw [ite_false_pf Bool.false_ne_true, hCanWarn]
    try dsimp only
    rw [ite_false_pf (fun h => Bool.noConfusion h)]
    rw [ite_false_pf (fun h => Bool.noConfusion h)]
    rw [hEmptyInit]
    rfl

/-- **Pillar 3 Theorem 2 (`--force-warn` + `#[expect]` Both Warns AND Fulfills):**
Under `--force-warn L` + `#[expect(L)]` (with `L ≠ unfulfilled_lint_expectations`),
emitting `L` once records `exp.id` in `fulfilled` AND emits a `forceWarning` diagnostic,
so `checkExpectations` emits no `unfulfilled_lint_expectations`! -/
theorem expect_under_forceWarn_fulfills_and_warns (opts : LintSessionOpts)
    (st : ScopeState) (lint : LintName) (expId : CanonExpectId)
    (flagTarget : AttrOrCliTargetName)
    (hnotSelf : lint ≠ .unfulfilledLintExpectations)
    (_hcap : opts.lintCap = some .allow) (hd : opts.driverCaps lint = none)
    (_hUnfulActive : (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).level = .warn)
    (_hCanWarn : opts.canEmitWarnings = true)
    (hfw : revealActualLevelSpec opts st.specs lint = ⟨.forceWarn, none, .commandLine flagTarget .forceWarn⟩) :
    let expectAttr : LevelSpec := ⟨.expect, some expId, .nodeSrc (.lint lint) 1 none⟩
    let st' := insertSpec opts true st lint expectAttr
    let effSpec := revealActualLevelSpec opts st'.specs lint
    let dcx1 := emitLintBase opts effSpec lint false emptyDiagCtxt
    let exp : DeclaredExpectation := ⟨expId, lint, none, false⟩
    let dcx2 := checkExpectations opts st'.specs [exp] dcx1
    expId ∈ dcx1.fulfilled ∧
    dcx1.emitted = [⟨lint, .forceWarning, some expId⟩] ∧
    dcx2.emitted = [⟨lint, .forceWarning, some expId⟩] := by
  let expectAttr : LevelSpec := ⟨.expect, some expId, .nodeSrc (.lint lint) 1 none⟩
  have hneSp : ¬ (expectAttr.level = .expect ∧ lint = .unfulfilledLintExpectations) :=
    fun ⟨_, h⟩ => hnotSelf h
  have hins := (insertSpec_under_forceWarn opts true st lint expectAttr
    (.commandLine flagTarget .forceWarn) none hfw hneSp).1 rfl
  have heff : revealActualLevelSpec opts (insertSpec opts true st lint expectAttr).specs lint =
      ⟨.forceWarn, some expId, .commandLine flagTarget .forceWarn⟩ := by
    unfold revealActualLevelSpec
    rw [hins, hd]
    rfl
  have hdcx1 : emitLintBase opts (revealActualLevelSpec opts (insertSpec opts true st lint expectAttr).specs lint)
      lint false emptyDiagCtxt =
      ⟨[⟨lint, .forceWarning, some expId⟩], [expId],
        if (builtinLintMeta lint).futureCompatReportInDeps then [lint] else []⟩ := by
    rw [heff]
    unfold emitLintBase
    dsimp only
    cases (builtinLintMeta lint).futureCompatReportInDeps <;> rfl
  have hmem : expId ∈ (emitLintBase opts (revealActualLevelSpec opts (insertSpec opts true st lint expectAttr).specs lint)
      lint false emptyDiagCtxt).fulfilled := by
    rw [hdcx1]
    exact List.Mem.head []
  have hful : isFulfilled expId (emitLintBase opts _ lint false emptyDiagCtxt).fulfilled = true :=
    (isFulfilled_iff_mem expId _).mpr hmem
  refine ⟨hmem, ?_, ?_⟩
  · rw [hdcx1]
  · show DiagCtxtState.emitted (if isFulfilled expId _ = true then _ else _) = _
    rw [hful, ite_true_pf rfl, hdcx1]

/-- **Pillar 3 Theorem 3 (`#[expect(L)] #[allow(L)]` Under `--force-warn L` Drops `lintId` -> Unfulfilled):**
Even though `--force-warn L` forces `L` to emit a `forceWarning`, an inner `#[allow(L)]` clears
`lintId` from `LevelSpec`, so `L`'s emission fails to record `expId` and `checkExpectations`
emits `unfulfilled_lint_expectations`! (Observed in probe `a45`.) -/
theorem expect_inner_allow_drops_id_under_forceWarn (opts : LintSessionOpts)
    (st : ScopeState) (lint : LintName) (expId : CanonExpectId)
    (flagTarget : AttrOrCliTargetName)
    (hnotSelf : lint ≠ .unfulfilledLintExpectations)
    (hd : opts.driverCaps lint = none)
    (hfw : revealActualLevelSpec opts st.specs lint = ⟨.forceWarn, none, .commandLine flagTarget .forceWarn⟩) :
    let expectAttr : LevelSpec := ⟨.expect, some expId, .nodeSrc (.lint lint) 1 none⟩
    let allowAttr : LevelSpec := ⟨.allow, none, .nodeSrc (.lint lint) 2 none⟩
    let st1 := insertSpec opts true st lint expectAttr
    let st2 := insertSpec opts true st1 lint allowAttr
    let effSpec := revealActualLevelSpec opts st2.specs lint
    let dcx1 := emitLintBase opts effSpec lint false emptyDiagCtxt
    effSpec.level = .forceWarn ∧
    effSpec.lintId = none ∧
    expId ∉ dcx1.fulfilled := by
  let expectAttr : LevelSpec := ⟨.expect, some expId, .nodeSrc (.lint lint) 1 none⟩
  let allowAttr : LevelSpec := ⟨.allow, none, .nodeSrc (.lint lint) 2 none⟩
  have hneSp : ¬ (expectAttr.level = .expect ∧ lint = .unfulfilledLintExpectations) :=
    fun ⟨_, h⟩ => hnotSelf h
  have hins1 := (insertSpec_under_forceWarn opts true st lint expectAttr
    (.commandLine flagTarget .forceWarn) none hfw hneSp).1 rfl
  have hfw1 : revealActualLevelSpec opts (insertSpec opts true st lint expectAttr).specs lint =
      ⟨.forceWarn, some expId, .commandLine flagTarget .forceWarn⟩ := by
    unfold revealActualLevelSpec
    rw [hins1, hd]
    rfl
  have hneAllow : ¬ (allowAttr.level = .expect ∧ lint = .unfulfilledLintExpectations) :=
    fun ⟨h, _⟩ => LintLevel.noConfusion h
  have hins2 : (insertSpec opts true (insertSpec opts true st lint expectAttr) lint allowAttr).specs lint =
      some ⟨.forceWarn, none, .commandLine flagTarget .forceWarn⟩ :=
    (insertSpec_under_forceWarn opts true (insertSpec opts true st lint expectAttr) lint allowAttr
      (.commandLine flagTarget .forceWarn) (some expId) hfw1 hneAllow).2
      (fun h => LintLevel.noConfusion h)
  have heff : revealActualLevelSpec opts
      (insertSpec opts true (insertSpec opts true st lint expectAttr) lint allowAttr).specs lint =
      ⟨.forceWarn, none, .commandLine flagTarget .forceWarn⟩ := by
    unfold revealActualLevelSpec
    rw [hins2, hd]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [heff]
  · rw [heff]
  · rw [heff]
    unfold emitLintBase
    dsimp only
    cases (builtinLintMeta lint).futureCompatReportInDeps <;> intro hmem <;> nomatch hmem

/-- **Pillar 3 Theorem 4 (`#[expect(unfulfilled_lint_expectations)]` Always Unfulfilled):**
`insertSpec` ignores `#[expect(unfulfilled_lint_expectations)]` (`levels.rs:650-654`), so no
`LevelSpec` ever carries `some eid` when `st.specs .unfulfilledLintExpectations` starts without `eid`.
Hence `eid` can never be fulfilled by `emitLintBase`, and `checkExpectations` always emits! -/
theorem expect_self_unfulfilled_ignored (opts : LintSessionOpts) (lintAddedLints : Bool)
    (st : ScopeState) (eid : CanonExpectId) (src : LintLevelSource) :
    insertSpec opts lintAddedLints st .unfulfilledLintExpectations ⟨.expect, some eid, src⟩ =
      if lintAddedLints && LintLevel.beq (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).level .forbid then
        if (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).src.isLintGroupSource then
          st.addDiag (.forbiddenLintGroupsFCW .unfulfilledLintExpectations .expect (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).src)
        else
          st.addDiag (.overruledAttributeE0453 .unfulfilledLintExpectations .expect (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).src)
      else st := by
  unfold insertSpec
  dsimp only
  cases lintAddedLints <;>
  cases (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).level <;>
  cases (revealActualLevelSpec opts st.specs .unfulfilledLintExpectations).src.isLintGroupSource <;>
  rfl

/-- **Pillar 3 Theorem 5 (`--cap-lints=allow` Silences Both `#[expect]` and `unfulfilled_lint_expectations`):** -/
theorem capLints_allow_silences_expect_and_unfulfilled (opts : LintSessionOpts)
    (probe : LintName → Option LevelSpec) (lint : LintName) (eid : CanonExpectId)
    (src : LintLevelSource) (exp : DeclaredExpectation)
    (hcap : opts.lintCap = some .allow)
    (hdLint : opts.driverCaps lint = none)
    (hdUnful : opts.driverCaps .unfulfilledLintExpectations = none)
    (hprobeLint : probe lint = some ⟨.expect, some eid, src⟩)
    (hnotfwLint : src.isCliForceWarn = false)
    (hnoUnfulFw : (probe .unfulfilledLintExpectations).elim false (fun s => s.src.isCliForceWarn) = false)
    (hnoWarnFw : (probe .warnings).elim false (fun s => s.src.isCliForceWarn) = false)
    (hnotFc : (builtinLintMeta lint).futureCompatReportInDeps = false) :
    let dcx1 := emitLintBase opts (revealActualLevelSpec opts probe lint) lint false emptyDiagCtxt
    let dcx2 := checkExpectations opts probe [exp] dcx1
    dcx1 = emptyDiagCtxt ∧ dcx2.emitted = [] := by
  have hrevLint : (revealActualLevelSpec opts probe lint).level = .allow := by
    unfold revealActualLevelSpec
    rw [hprobeLint, hcap, hdLint]
    dsimp only
    rw [hnotfwLint]
    rfl
  have hdcx1 : emitLintBase opts (revealActualLevelSpec opts probe lint) lint false emptyDiagCtxt = emptyDiagCtxt := by
    unfold emitLintBase
    dsimp only
    rw [hrevLint, hnotFc]
    rfl
  have hleUnful : LintLevel.le (revealActualLevelSpec opts probe .unfulfilledLintExpectations).level .allow :=
    reveal_le_lintCap_unless_forceWarn opts probe .unfulfilledLintExpectations .allow
      hcap hdUnful hnoUnfulFw hnoWarnFw
  have hrevUnful : (revealActualLevelSpec opts probe .unfulfilledLintExpectations).level = .allow :=
    LintLevel.le_antisymm hleUnful (LintLevel.allow_le _)
  refine ⟨hdcx1, ?_⟩
  rw [hdcx1]
  show (if isFulfilled exp.id emptyDiagCtxt.fulfilled then emptyDiagCtxt else
    emitLintBase opts (revealActualLevelSpec opts probe .unfulfilledLintExpectations)
      .unfulfilledLintExpectations false emptyDiagCtxt).emitted = []
  have hfnil : isFulfilled exp.id emptyDiagCtxt.fulfilled = false := rfl
  rw [hfnil]
  unfold emitLintBase
  rw [hrevUnful]
  rfl

/-- **Pillar 3 Theorem 6 (External-Macro Filter Blocks Expectation Fulfillment):**
Because `emit_lint_base` returns before recording `fulfilled_expectations` when
`inExternalMacro = true` and `reportInExternalMacro = false`, an `unsafe_code` violation
expanded from a foreign macro NEVER fulfills `#[expect(unsafe_code)]`. -/
theorem external_macro_never_fulfills_expect (opts : LintSessionOpts)
    (eid : CanonExpectId) (src : LintLevelSource) (dcx : DiagCtxtState) :
    emitLintBase opts ⟨.expect, some eid, src⟩ .unsafeCode true dcx = dcx := rfl

/-- **Pillar 3 Theorem 7 (`-A warnings` Session Global Latch vs `#![warn(warnings)]` vs `#[expect]`):**
`canEmitWarnings = false` permanently drops `Warning` diagnostics even if the crate writes
`#![warn(warnings)]`, yet does NOT suppress `#[expect]` fulfillment (because `revealActualLevelSpec`
only checks `warnings` when `baseSpec.level == .warn`) nor `Deny`/`Forbid` errors! -/
theorem cli_allow_warnings_suppresses_crate_warn_but_not_deny_or_expect
    (opts : LintSessionOpts) (warnSpec : LevelSpec) (eid : CanonExpectId) (dcx : DiagCtxtState)
    (hca : opts.cliWarningsAllow = true) :
    opts.canEmitWarnings = false ∧
    emitLintBase opts ⟨.warn, none, warnSpec.src⟩ .deadCode false dcx = dcx ∧
    (emitLintBase opts ⟨.deny, none, warnSpec.src⟩ .deadCode false dcx).emitted =
      dcx.emitted ++ [⟨.deadCode, .err, none⟩] ∧
    (emitLintBase opts ⟨.expect, some eid, warnSpec.src⟩ .deadCode false dcx).fulfilled =
      dcx.fulfilled ++ [eid] := by
  have hcw : opts.canEmitWarnings = false := by
    unfold LintSessionOpts.canEmitWarnings
    rw [hca]
    rfl
  refine ⟨hcw, ?_, ?_, ?_⟩
  · unfold emitLintBase
    rw [hcw]
    rfl
  · unfold emitLintBase
    rfl
  · unfold emitLintBase
    rfl

end EmitAndExpectSection

/-! ## Part 7: `--check-cfg` Validation & `#[cfg_attr(false, ...)]` Pre-Validation Erasure -/

section CheckCfgAndCfgAttrSection

/-- Mirrors `rustc_session::config::ExpectedValues<Symbol>`. -/
inductive ExpectedValues where
  | some (vals : List (Option String))
  | any

noncomputable def ExpectedValues.optStrEq (x y : Option String) : Bool :=
  match x, y with
  | none, none => true
  | Option.some a, Option.some b => strEq a b
  | _, _ => false

noncomputable def ExpectedValues.memOptStr (x : Option String) : List (Option String) → Bool
  | [] => false
  | y :: ys => ExpectedValues.optStrEq x y || ExpectedValues.memOptStr x ys

theorem ExpectedValues.memOptStr_append (x : Option String) (a b : List (Option String)) :
    ExpectedValues.memOptStr x (a ++ b) =
      (ExpectedValues.memOptStr x a || ExpectedValues.memOptStr x b) := by
  induction a with
  | nil => rfl
  | cons y ys ih =>
    change (ExpectedValues.optStrEq x y || ExpectedValues.memOptStr x (ys ++ b)) =
           ((ExpectedValues.optStrEq x y || ExpectedValues.memOptStr x ys) || ExpectedValues.memOptStr x b)
    rw [ih, Bool.or_assoc]

noncomputable def ExpectedValues.join : ExpectedValues → ExpectedValues → ExpectedValues
  | .some a, .some b => .some (a ++ b)
  | _, _ => .any

noncomputable def ExpectedValues.accepts : ExpectedValues → Option String → Bool
  | .some vals, v => ExpectedValues.memOptStr v vals
  | .any, _ => true

noncomputable def ExpectedValues.isAny : ExpectedValues → Bool
  | .any => true
  | .some _ => false

noncomputable def ExpectedValues.ObsEq (a b : ExpectedValues) : Prop :=
  a.isAny = b.isAny ∧ ∀ v, a.accepts v = b.accepts v

theorem ExpectedValues.join_assoc (a b c : ExpectedValues) :
    ExpectedValues.join (ExpectedValues.join a b) c =
      ExpectedValues.join a (ExpectedValues.join b c) := by
  cases a with
  | some x =>
    cases b with
    | some y =>
      cases c with
      | some z =>
        show ExpectedValues.some ((x ++ y) ++ z) = .some (x ++ (y ++ z))
        rw [List.append_assoc]
      | any => rfl
    | any => cases c <;> rfl
  | any => cases b <;> cases c <;> rfl

theorem ExpectedValues.accepts_join (a b : ExpectedValues) (v : Option String) :
    (ExpectedValues.join a b).accepts v = (a.accepts v || b.accepts v) := by
  cases a with
  | some x =>
    cases b with
    | some y => exact ExpectedValues.memOptStr_append v x y
    | any => exact (Bool.or_true _).symm
  | any => cases b <;> rfl

theorem ExpectedValues.join_comm_obs (a b : ExpectedValues) :
    ExpectedValues.ObsEq (ExpectedValues.join a b) (ExpectedValues.join b a) := by
  refine ⟨?_, fun v => ?_⟩
  · cases a <;> cases b <;> rfl
  · rw [ExpectedValues.accepts_join, ExpectedValues.accepts_join, Bool.or_comm]

theorem ExpectedValues.join_any_left (a : ExpectedValues) :
    ExpectedValues.join .any a = .any := by
  cases a <;> rfl

theorem ExpectedValues.join_any_right (a : ExpectedValues) :
    ExpectedValues.join a .any = .any := by
  cases a <;> rfl

/-- Mirrors `rustc_session::config::CheckCfg`. -/
structure CheckCfg where
  exhaustiveNames : Bool
  expecteds : String → Option ExpectedValues

noncomputable def CheckCfg.empty : CheckCfg := ⟨false, fun _ => none⟩

/-- Parsed `--check-cfg` CLI spec. -/
inductive CheckCfgSpec where
  | cfgAny
  | cfgEmpty
  | cfgName (name : String) (vals : ExpectedValues)

noncomputable def applyCheckCfgSpec (cc : CheckCfg) (spec : CheckCfgSpec) : CheckCfg :=
  match spec with
  | .cfgAny => ⟨false, cc.expecteds⟩
  | .cfgEmpty => cc
  | .cfgName name vals =>
    ⟨cc.exhaustiveNames, fun k =>
      if strEq k name then
        match cc.expecteds k with
        | some existing => some (ExpectedValues.join existing vals)
        | none => some vals
      else
        cc.expecteds k⟩

noncomputable def buildCheckCfg (specs : List CheckCfgSpec) : CheckCfg :=
  if specs.isEmpty then CheckCfg.empty
  else specs.foldl applyCheckCfgSpec ⟨true, fun _ => none⟩

/-- Mirrors `CfgEntry` predicates in `rustc_attr_parsing/src/attributes/cfg.rs`. -/
inductive CfgPred where
  | boolLit (b : Bool)
  | nameVal (name : String) (val : Option String)
  | not (p : CfgPred)
  | all (ps : List CfgPred)
  | any (ps : List CfgPred)

mutual
noncomputable def CfgPred.eval (env : String → Option String → Bool) : CfgPred → Bool
  | .boolLit b => b
  | .nameVal n v => env n v
  | .not p => !CfgPred.eval env p
  | .all ps => CfgPred.evalAll env ps
  | .any ps => CfgPred.evalAny env ps

noncomputable def CfgPred.evalAll (env : String → Option String → Bool) : List CfgPred → Bool
  | [] => true
  | p :: ps => CfgPred.eval env p && CfgPred.evalAll env ps

noncomputable def CfgPred.evalAny (env : String → Option String → Bool) : List CfgPred → Bool
  | [] => false
  | p :: ps => CfgPred.eval env p || CfgPred.evalAny env ps
end

inductive CheckCfgDiag where
  | unexpectedCfgName (name : String) (val : Option String)
  | unexpectedCfgValue (name : String) (val : Option String)

noncomputable def checkAtom (cc : CheckCfg) (name : String) (val : Option String) :
    List CheckCfgDiag :=
  match cc.expecteds name with
  | some ev => if ev.accepts val then [] else [.unexpectedCfgValue name val]
  | none => if cc.exhaustiveNames then [.unexpectedCfgName name val] else []

/- Mirrors `parse_cfg_entry` + `parse_name_value` validation against `CheckCfg`
(`compiler/rustc_attr_parsing/src/attributes/cfg.rs:81-236`). -/
mutual
noncomputable def validateCfgPred (cc : CheckCfg) : CfgPred → List CheckCfgDiag
  | .boolLit _ => []
  | .nameVal n v => checkAtom cc n v
  | .not p => validateCfgPred cc p
  | .all ps => validateCfgPredList cc ps
  | .any ps => validateCfgPredList cc ps

noncomputable def validateCfgPredList (cc : CheckCfg) : List CfgPred → List CheckCfgDiag
  | [] => []
  | p :: ps => validateCfgPred cc p ++ validateCfgPredList cc ps
end

mutual
noncomputable def predAtomWellTyped (cc : CheckCfg) : CfgPred → Prop
  | .boolLit _ => True
  | .nameVal n v =>
    match cc.expecteds n with
    | some ev => ev.accepts v = true
    | none => cc.exhaustiveNames = false
  | .not p => predAtomWellTyped cc p
  | .all ps => predAtomWellTypedList cc ps
  | .any ps => predAtomWellTypedList cc ps

noncomputable def predAtomWellTypedList (cc : CheckCfg) : List CfgPred → Prop
  | [] => True
  | p :: ps => predAtomWellTyped cc p ∧ predAtomWellTypedList cc ps
end

theorem predAtomWellTypedList_iff_forall (cc : CheckCfg) (ps : List CfgPred) :
    predAtomWellTypedList cc ps ↔ ∀ p, p ∈ ps → predAtomWellTyped cc p := by
  induction ps with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => trivial⟩
  | cons p rest ih =>
    constructor
    · intro ⟨hp, hrest⟩ q hq
      cases hq with
      | head _ => exact hp
      | tail _ hm => exact (ih.mp hrest) q hm
    · intro h
      exact ⟨h p (List.Mem.head rest), ih.mpr (fun q hq => h q (List.Mem.tail p hq))⟩

/- **Pillar 4 Theorem 1 (`--check-cfg` Validation Soundness & Completeness):**
`validateCfgPred cc p = []` (zero `unexpected_cfgs` diagnostics) if and only if every atomic
`(name, val)` predicate inside `p` satisfies `cc`'s expected-values/exhaustiveness schema. -/
mutual
theorem checkCfg_soundness (cc : CheckCfg) :
    ∀ p : CfgPred, validateCfgPred cc p = [] ↔ predAtomWellTyped cc p
  | .boolLit _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | .nameVal n v => by
    unfold validateCfgPred checkAtom predAtomWellTyped
    cases h : cc.expecteds n with
    | some ev =>
      dsimp only
      cases ha : ev.accepts v with
      | true => rw [ite_true_pf rfl]; exact ⟨fun _ => rfl, fun _ => rfl⟩
      | false =>
        rw [ite_false_pf Bool.false_ne_true]
        exact ⟨fun hnil => (nomatch hnil), fun htrue => (nomatch htrue)⟩
    | none =>
      dsimp only
      cases he : cc.exhaustiveNames with
      | false => rw [ite_false_pf Bool.false_ne_true]; exact ⟨fun _ => rfl, fun _ => rfl⟩
      | true =>
        rw [ite_true_pf rfl]
        exact ⟨fun hnil => (nomatch hnil), fun hfalse => (nomatch hfalse)⟩
  | .not p => checkCfg_soundness cc p
  | .all ps => checkCfg_soundness_list cc ps
  | .any ps => checkCfg_soundness_list cc ps

theorem checkCfg_soundness_list (cc : CheckCfg) :
    ∀ ps : List CfgPred, validateCfgPredList cc ps = [] ↔ predAtomWellTypedList cc ps
  | [] => ⟨fun _ => trivial, fun _ => rfl⟩
  | p :: ps => by
    have ihp := checkCfg_soundness cc p
    have ihps := checkCfg_soundness_list cc ps
    constructor
    · intro h
      have h1 : validateCfgPred cc p ++ validateCfgPredList cc ps = [] := h
      exact ⟨ihp.mp (List.append_eq_nil_iff.mp h1).1, ihps.mp (List.append_eq_nil_iff.mp h1).2⟩
    · intro ⟨hp, hps⟩
      show validateCfgPred cc p ++ validateCfgPredList cc ps = []
      rw [ihp.mpr hp, ihps.mpr hps]
      rfl
end

mutual
theorem predAtomWellTyped_empty : ∀ p : CfgPred, predAtomWellTyped CheckCfg.empty p
  | .boolLit _ => trivial
  | .nameVal _ _ => rfl
  | .not p => predAtomWellTyped_empty p
  | .all ps => predAtomWellTypedList_empty ps
  | .any ps => predAtomWellTypedList_empty ps

theorem predAtomWellTypedList_empty : ∀ ps : List CfgPred, predAtomWellTypedList CheckCfg.empty ps
  | [] => trivial
  | p :: ps => ⟨predAtomWellTyped_empty p, predAtomWellTypedList_empty ps⟩
end

theorem no_check_cfg_never_emits (p : CfgPred) :
    validateCfgPred CheckCfg.empty p = [] :=
  (checkCfg_soundness CheckCfg.empty p).mpr (predAtomWellTyped_empty p)

noncomputable def CheckCfg.ObsEq (a b : CheckCfg) : Prop :=
  a.exhaustiveNames = b.exhaustiveNames ∧
  ∀ k, match a.expecteds k, b.expecteds k with
    | some ea, some eb => ExpectedValues.ObsEq ea eb
    | none, none => True
    | _, _ => False

theorem CheckCfg.obsEq_refl (a : CheckCfg) : CheckCfg.ObsEq a a := by
  refine ⟨rfl, fun k => ?_⟩
  cases a.expecteds k with
  | none => trivial
  | some ea => exact ⟨rfl, fun _ => rfl⟩

theorem CheckCfg.obsEq_symm {a b : CheckCfg} (h : CheckCfg.ObsEq a b) : CheckCfg.ObsEq b a := by
  refine ⟨h.1.symm, fun k => ?_⟩
  have hk := h.2 k
  cases ha : a.expecteds k with
  | none =>
    rw [ha] at hk
    cases hb : b.expecteds k with
    | none => trivial
    | some _ => rw [hb] at hk; exact False.elim hk
  | some ea =>
    rw [ha] at hk
    cases hb : b.expecteds k with
    | none => rw [hb] at hk; exact False.elim hk
    | some eb =>
      rw [hb] at hk
      exact ⟨hk.1.symm, fun v => (hk.2 v).symm⟩

theorem CheckCfg.obsEq_trans {a b c : CheckCfg} (h1 : CheckCfg.ObsEq a b) (h2 : CheckCfg.ObsEq b c) :
    CheckCfg.ObsEq a c := by
  refine ⟨h1.1.trans h2.1, fun k => ?_⟩
  have hk1 := h1.2 k
  have hk2 := h2.2 k
  cases ha : a.expecteds k <;> rw [ha] at hk1 <;>
  cases hb : b.expecteds k <;> rw [hb] at hk1 hk2 <;>
  cases hc : c.expecteds k <;> rw [hc] at hk2
  · trivial
  · exact False.elim hk2
  · exact False.elim hk1
  · exact False.elim hk1
  · exact False.elim hk1
  · exact False.elim hk1
  · exact False.elim hk2
  · exact ⟨hk1.1.trans hk2.1, fun v => (hk1.2 v).trans (hk2.2 v)⟩

theorem checkAtom_congr {a b : CheckCfg} (h : CheckCfg.ObsEq a b) (name : String)
    (val : Option String) : checkAtom a name val = checkAtom b name val := by
  unfold checkAtom
  have hn := h.2 name
  cases ha : a.expecteds name with
  | none =>
    rw [ha] at hn
    cases hb : b.expecteds name with
    | none => rw [h.1]
    | some _ => rw [hb] at hn; exact False.elim hn
  | some ea =>
    rw [ha] at hn
    cases hb : b.expecteds name with
    | none => rw [hb] at hn; exact False.elim hn
    | some eb =>
      rw [hb] at hn
      dsimp only at hn ⊢
      rw [hn.2 val]

mutual
theorem validateCfgPred_congr {a b : CheckCfg} (h : CheckCfg.ObsEq a b) :
    ∀ p : CfgPred, validateCfgPred a p = validateCfgPred b p
  | .boolLit _ => rfl
  | .nameVal n v => checkAtom_congr h n v
  | .not p => validateCfgPred_congr h p
  | .all ps => validateCfgPredList_congr h ps
  | .any ps => validateCfgPredList_congr h ps

theorem validateCfgPredList_congr {a b : CheckCfg} (h : CheckCfg.ObsEq a b) :
    ∀ ps : List CfgPred, validateCfgPredList a ps = validateCfgPredList b ps
  | [] => rfl
  | p :: ps => by
    show validateCfgPred a p ++ validateCfgPredList a ps =
         validateCfgPred b p ++ validateCfgPredList b ps
    rw [validateCfgPred_congr h p, validateCfgPredList_congr h ps]
end

theorem applyCheckCfgSpec_comm_obs (cc : CheckCfg) (s1 s2 : CheckCfgSpec) :
    CheckCfg.ObsEq (applyCheckCfgSpec (applyCheckCfgSpec cc s1) s2)
                   (applyCheckCfgSpec (applyCheckCfgSpec cc s2) s1) := by
  cases s1 with
  | cfgAny =>
    cases s2 with
    | cfgAny => exact CheckCfg.obsEq_refl _
    | cfgEmpty => exact CheckCfg.obsEq_refl _
    | cfgName n v =>
      refine ⟨rfl, fun k => ?_⟩
      dsimp only [applyCheckCfgSpec]
      cases strEq k n <;> cases cc.expecteds k <;> try trivial
      all_goals exact ⟨rfl, fun _ => rfl⟩
  | cfgEmpty =>
    cases s2 <;> exact CheckCfg.obsEq_refl _
  | cfgName n1 v1 =>
    cases s2 with
    | cfgAny =>
      refine ⟨rfl, fun k => ?_⟩
      dsimp only [applyCheckCfgSpec]
      cases strEq k n1 <;> cases cc.expecteds k <;> try trivial
      all_goals exact ⟨rfl, fun _ => rfl⟩
    | cfgEmpty => exact CheckCfg.obsEq_refl _
    | cfgName n2 v2 =>
      refine ⟨rfl, fun k => ?_⟩
      dsimp only [applyCheckCfgSpec]
      cases h1 : strEq k n1 <;> cases h2 : strEq k n2 <;> try dsimp only
      · cases cc.expecteds k <;> try trivial
        exact ⟨rfl, fun _ => rfl⟩
      · cases cc.expecteds k <;> try trivial
        · exact ⟨rfl, fun _ => rfl⟩
        · exact ⟨rfl, fun _ => rfl⟩
      · cases cc.expecteds k <;> try trivial
        · exact ⟨rfl, fun _ => rfl⟩
        · exact ⟨rfl, fun _ => rfl⟩
      · cases cc.expecteds k with
        | none => exact ExpectedValues.join_comm_obs v1 v2
        | some ev =>
          refine ⟨?_, fun w => ?_⟩
          · cases ev <;> cases v1 <;> cases v2 <;> rfl
          · rw [ExpectedValues.accepts_join, ExpectedValues.accepts_join,
                ExpectedValues.accepts_join, ExpectedValues.accepts_join, Bool.or_assoc,
                Bool.or_comm (v1.accepts w) (v2.accepts w), Bool.or_assoc]

/-- AST attribute representation before and after `StripUnconfigured::expand_cfg_attr`
(`compiler/rustc_expand/src/config.rs:263-305`).
Notice `innerAttrItem` may carry semantically invalid attributes (like `#[inline(bogus_never_valid)]`),
nested `#[cfg(unknown)]`, or forbidden lint overrides (`#[allow(unsafe_code)]`). -/
inductive AstAttr where
  | cfg (pred : CfgPred)
  | cfgAttr (pred : CfgPred) (inners : List AstAttr)
  | cfgAttrTrace
  | lintAttr (lint : LintName) (spec : LevelSpec)
  | builtinAttr (name : String) (validInput : Bool)

inductive FrontEndError where
  | malformedAttrInput (name : String)
  | builderDiag (d : BuilderDiag)
  | checkCfgLint (d : CheckCfgDiag)

structure ExpandOutput where
  survivingAttrs : List AstAttr
  diags : List FrontEndError

/-- Mirrors `StripUnconfigured::expand_cfg_attr` (`config.rs:263-305`) +
`StripUnconfigured::configure` (`config.rs:170-176`) for one AST node.
Crucially:
1. `cfgAttr` validates `pred` via `validateCfgPred` BEFORE evaluating `pred`.
2. When `pred.eval env = false`, `inners` are discarded immediately leaving only `cfgAttrTrace`.
3. Only surviving `cfgAttr` children and unstripped nodes reach `AttributeParser` (`validInput`)
   and `LintLevelsBuilder` (`insertSpec`). -/
noncomputable def expandAttrList (env : String → Option String → Bool) (cc : CheckCfg)
    (fuel : Nat) (attrs : List AstAttr) : ExpandOutput :=
  match fuel with
  | 0 => ⟨attrs, []⟩
  | Nat.succ f =>
    attrs.foldl (fun acc attr =>
      match attr with
      | .cfgAttr pred inners =>
        let predDiags := (validateCfgPred cc pred).map FrontEndError.checkCfgLint
        if pred.eval env then
          let sub := expandAttrList env cc f inners
          ⟨acc.survivingAttrs ++ [.cfgAttrTrace] ++ sub.survivingAttrs,
           acc.diags ++ predDiags ++ sub.diags⟩
        else
          ⟨acc.survivingAttrs ++ [.cfgAttrTrace], acc.diags ++ predDiags⟩
      | other => ⟨acc.survivingAttrs ++ [other], acc.diags⟩
    ) ⟨[], []⟩

noncomputable def evalInCfg (env : String → Option String → Bool) (cc : CheckCfg) :
    List AstAttr → Bool × List FrontEndError
  | [] => (true, [])
  | .cfg pred :: rest =>
    let d := (validateCfgPred cc pred).map FrontEndError.checkCfgLint
    if pred.eval env then
      let r := evalInCfg env cc rest
      (r.1, d ++ r.2)
    else
      -- Rust's `Iterator::all` short-circuits immediately on the first `false` `#[cfg]`!
      (false, d)
  | _ :: rest => evalInCfg env cc rest

noncomputable def validateExpandedAttrs (opts : LintSessionOpts) (st : ScopeState)
    (attrs : List AstAttr) : ScopeState × List FrontEndError :=
  attrs.foldl (fun (curSt, errs) attr =>
    match attr with
    | .builtinAttr nm false => (curSt, errs ++ [.malformedAttrInput nm])
    | .lintAttr l sp =>
      let prevLen := curSt.diags.length
      let nextSt := insertSpec opts true curSt l sp
      let newErrs := (nextSt.diags.drop prevLen).map FrontEndError.builderDiag
      (nextSt, errs ++ newErrs)
    | _ => (curSt, errs)
  ) (st, [])

structure ItemCompileOutcome where
  keptInAst : Bool
  scopeState : ScopeState
  errors : List FrontEndError

/-- Full pre-HIR `StripUnconfigured::configure` + `AttributeParser` + `LintLevelsBuilder`
pipeline on one AST item (`config.rs:170-176`). -/
noncomputable def compileItemAttrs (env : String → Option String → Bool) (cc : CheckCfg)
    (opts : LintSessionOpts) (initSt : ScopeState) (fuel : Nat) (attrs : List AstAttr) :
    ItemCompileOutcome :=
  let exp := expandAttrList env cc fuel attrs
  let (kept, cfgErrs) := evalInCfg env cc exp.survivingAttrs
  if !kept then
    ⟨false, initSt, exp.diags ++ cfgErrs⟩
  else
    let (finalSt, valErrs) := validateExpandedAttrs opts initSt exp.survivingAttrs
    ⟨true, finalSt, exp.diags ++ cfgErrs ++ valErrs⟩

/-- **Pillar 4 Theorem 2 (`#[cfg_attr(false, ...)]` Pre-Validation Erasure Invariant):**
When `pred.eval env = false`, ANY list of inner attributes inside `#[cfg_attr(pred, ...)]`
(even malformed `#[inline(bogus)]`, nested `#[cfg(unknown)]`, or `#[allow(unsafe_code)]`
under `#![forbid(unsafe_code)]`) is erased into `[.cfgAttrTrace]` BEFORE `evalInCfg`,
`AttributeParser`, or `LintLevelsBuilder` runs!
Yet `pred` itself is STILL checked against `CheckCfg` (`validateCfgPred cc pred`)! -/
theorem cfgAttr_false_erases_inner_attrs_before_validation
    (env : String → Option String → Bool) (cc : CheckCfg) (opts : LintSessionOpts)
    (initSt : ScopeState) (f : Nat) (pred : CfgPred) (inners : List AstAttr)
    (hfalse : pred.eval env = false) :
    let exp := expandAttrList env cc (Nat.succ f) [.cfgAttr pred inners]
    let out := compileItemAttrs env cc opts initSt (Nat.succ f) [.cfgAttr pred inners]
    exp.survivingAttrs = [.cfgAttrTrace] ∧
    exp.diags = (validateCfgPred cc pred).map FrontEndError.checkCfgLint ∧
    out.keptInAst = true ∧
    out.scopeState = initSt ∧
    out.errors = (validateCfgPred cc pred).map FrontEndError.checkCfgLint := by
  have hexp : expandAttrList env cc (Nat.succ f) [.cfgAttr pred inners] =
      ⟨[.cfgAttrTrace], (validateCfgPred cc pred).map FrontEndError.checkCfgLint⟩ := by
    unfold expandAttrList
    dsimp only [List.foldl]
    rw [hfalse]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hexp]
  · rw [hexp]
  · unfold compileItemAttrs
    rw [hexp]
    rfl
  · unfold compileItemAttrs
    rw [hexp]
    rfl
  · unfold compileItemAttrs
    rw [hexp]
    dsimp only
    show ((validateCfgPred cc pred).map FrontEndError.checkCfgLint ++ []) ++ [] = _
    rw [List.append_nil, List.append_nil]

/-- **Pillar 4 Theorem 3 (`#[cfg_attr(false, ...)]` Zero Inner Errors When Outer Pred Valid):**
If `pred` evaluates to `false` AND `pred` is valid under `CheckCfg`, then even arbitrarily
malformed/forbidden `inners` compile with `errors = []` and leave `initSt` untouched. -/
theorem cfgAttr_false_zero_errors_when_pred_valid
    (env : String → Option String → Bool) (cc : CheckCfg) (opts : LintSessionOpts)
    (initSt : ScopeState) (f : Nat) (pred : CfgPred) (inners : List AstAttr)
    (hfalse : pred.eval env = false)
    (hvalid : predAtomWellTyped cc pred) :
    (compileItemAttrs env cc opts initSt (Nat.succ f) [.cfgAttr pred inners]).errors = [] := by
  have hc := cfgAttr_false_erases_inner_attrs_before_validation
    env cc opts initSt f pred inners hfalse
  rw [hc.2.2.2.2]
  rw [(checkCfg_soundness cc pred).mpr hvalid]
  rfl

/-- **Pillar 4 Theorem 4 (`#[cfg_attr(true, ...)]` Exposes Inner Malformed Attributes & `E0453`):**
Conversely, when `pred.eval env = true`, `#[cfg_attr(true, inline(bogus))]` exposes
`malformedAttrInput "inline"`, and `#[cfg_attr(true, allow(unsafe_code))]` under
`#![forbid(unsafe_code)]` exposes `overruledAttributeE0453`! -/
theorem cfgAttr_true_exposes_malformed_and_e0453
    (env : String → Option String → Bool) (cc : CheckCfg)
    (opts : LintSessionOpts) (st : ScopeState) (pred : CfgPred)
    (htrue : pred.eval env = true)
    (hvalid : predAtomWellTyped cc pred)
    (hforbid : (revealActualLevelSpec opts st.specs .unsafeCode).level = .forbid)
    (hdirect : (revealActualLevelSpec opts st.specs .unsafeCode).src.isLintGroupSource = false) :
    let allowUnsafe := AstAttr.lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩
    let outMalformed := compileItemAttrs env cc opts st 2 [.cfgAttr pred [.builtinAttr "inline" false]]
    let outForbid := compileItemAttrs env cc opts st 2 [.cfgAttr pred [allowUnsafe]]
    outMalformed.errors = [.malformedAttrInput "inline"] ∧
    outForbid.errors = [.builderDiag (.overruledAttributeE0453 .unsafeCode .allow (revealActualLevelSpec opts st.specs .unsafeCode).src)] := by
  have hv : validateCfgPred cc pred = [] := (checkCfg_soundness cc pred).mpr hvalid
  have hexpM : expandAttrList env cc 2 [.cfgAttr pred [.builtinAttr "inline" false]] =
      ⟨[.cfgAttrTrace, .builtinAttr "inline" false], []⟩ := by
    unfold expandAttrList
    dsimp only [List.foldl]
    rw [hv, htrue]
    rfl
  have hexpF : expandAttrList env cc 2
      [.cfgAttr pred [.lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩]] =
      ⟨[.cfgAttrTrace, .lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩], []⟩ := by
    unfold expandAttrList
    dsimp only [List.foldl]
    rw [hv, htrue]
    rfl
  refine ⟨?_, ?_⟩
  · unfold compileItemAttrs
    rw [hexpM]
    rfl
  · unfold compileItemAttrs
    rw [hexpF]
    dsimp only [evalInCfg, validateExpandedAttrs, List.foldl]
    have hdir := (insertSpec_direct_forbid_unoverridable opts st .unsafeCode
      ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩ hforbid hdirect).2.1
      (fun h => LintLevel.noConfusion h) (fun h => LintLevel.noConfusion h)
    have hstEq : insertSpec opts true st .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩ =
        st.addDiag (.overruledAttributeE0453 .unsafeCode .allow (revealActualLevelSpec opts st.specs .unsafeCode).src) :=
      hdir.1
    rw [hstEq]
    unfold ScopeState.addDiag
    dsimp only
    rw [List.drop_left]
    rfl

/-- **Pillar 4 Theorem 5 (`cfg_attr(true, allow(unsafe_code))` + `cfg_attr(true, cfg(falsePred))` Strips Item Before `E0453`):**
Mirrors `config.rs:171-172` and probe `b06b`: `process_cfg_attrs` runs BEFORE `in_cfg`, so a false
`cfg_attr(true, cfg(falsePred))` drops the entire item before `LintLevelsBuilder` ever processes the
expanded `#[allow(unsafe_code)]`, emitting ZERO `E0453`! -/
theorem cfgAttr_true_allow_plus_false_cfg_strips_before_e0453
    (env : String → Option String → Bool) (cc : CheckCfg) (opts : LintSessionOpts)
    (st : ScopeState) (predT predF : CfgPred)
    (htrue : predT.eval env = true) (hfalse : predF.eval env = false) :
    let allowUnsafe := AstAttr.lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩
    let out := compileItemAttrs env cc opts st 2 [.cfgAttr predT [allowUnsafe], .cfgAttr predT [.cfg predF]]
    out.keptInAst = false ∧
    out.scopeState = st ∧
    out.errors = (validateCfgPred cc predT).map FrontEndError.checkCfgLint ++
                 (validateCfgPred cc predT).map FrontEndError.checkCfgLint ++
                 (validateCfgPred cc predF).map FrontEndError.checkCfgLint := by
  have hexp : expandAttrList env cc 2
      [.cfgAttr predT [.lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩],
       .cfgAttr predT [.cfg predF]] =
      ⟨[.cfgAttrTrace, .lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩,
        .cfgAttrTrace, .cfg predF],
       (validateCfgPred cc predT).map FrontEndError.checkCfgLint ++
       (validateCfgPred cc predT).map FrontEndError.checkCfgLint⟩ := by
    unfold expandAttrList
    dsimp only [List.foldl]
    rw [htrue]
    repeat rw [ite_true_pf rfl]
    dsimp only [expandAttrList, List.foldl]
    simp only [List.nil_append, List.append_nil]
    rfl
  have hev : evalInCfg env cc
      [.cfgAttrTrace, .lintAttr .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 10 none⟩,
       .cfgAttrTrace, .cfg predF] =
      (false, (validateCfgPred cc predF).map FrontEndError.checkCfgLint) := by
    (repeat unfold evalInCfg)
    rw [ite_false_pf (fun h => Bool.noConfusion (h.symm.trans hfalse))]
  dsimp only
  unfold compileItemAttrs
  rw [hexp]
  dsimp only
  rw [hev]
  exact ⟨rfl, rfl, rfl⟩

/-- **Pillar 4 Theorem 6 (`InvocationCollector` `lint_node_id` Routing for `#[expect(unexpected_cfgs)]`):**
Models `compiler/rustc_expand/src/expand.rs:1231-1244` and `2304-2315`:
- An item's own `#[cfg(p)]` is checked BEFORE `assign_id!` updates `lint_node_id`, so its `unexpected_cfgs`
  diagnostic is buffered at `parentNodeId` (crate root `0` or enclosing `mod`).
- A body `cfg!(p)` is expanded AFTER `assign_id!` sets `lint_node_id = itemNodeId`.
Therefore, an item-level `#[expect(unexpected_cfgs)]` on `fn f()` (`itemNodeId ≠ parentNodeId`)
misses `fn f()`'s own `#[cfg(p)]` (both warnings emit, as in probe `b12b`), whereas crate-root `#![expect]`
or enclosing `mod`'s `#[expect]` catches and fulfills it (probes `b12a`, `b12d`)! -/
noncomputable def emitBufferedUnexpectedCfg (opts : LintSessionOpts) (scopeAt : Nat → ScopeState)
    (bufferedNodeId : Nat) (dcx : DiagCtxtState) : DiagCtxtState :=
  let spec := revealActualLevelSpec opts (scopeAt bufferedNodeId).specs .unexpectedCfgs
  emitLintBase opts spec .unexpectedCfgs false dcx

theorem item_expect_misses_own_cfg_while_parent_expect_catches
    (opts : LintSessionOpts) (parentId itemId : Nat) (eid : CanonExpectId)
    (hneq : parentId ≠ itemId) (hcap : opts.lintCap = none)
    (hdUnexp : opts.driverCaps .unexpectedCfgs = none)
    (_hdUnful : opts.driverCaps .unfulfilledLintExpectations = none)
    (hCanWarn : opts.canEmitWarnings = true) :
    let itemOnlyScopes : Nat → ScopeState := fun nid =>
      if natEq nid itemId then
        ⟨fun l => if LintName.beq l .unexpectedCfgs then some ⟨.expect, some eid, .nodeSrc (.lint .unexpectedCfgs) 1 none⟩ else none, []⟩
      else
        ⟨fun _ => none, []⟩
    let parentScopes : Nat → ScopeState := fun nid =>
      if natEq nid parentId then
        ⟨fun l => if LintName.beq l .unexpectedCfgs then some ⟨.expect, some eid, .nodeSrc (.lint .unexpectedCfgs) 1 none⟩ else none, []⟩
      else
        ⟨fun _ => none, []⟩
    let dcxItemMiss := emitBufferedUnexpectedCfg opts itemOnlyScopes parentId emptyDiagCtxt
    let dcxParentHit := emitBufferedUnexpectedCfg opts parentScopes parentId emptyDiagCtxt
    eid ∉ dcxItemMiss.fulfilled ∧
    dcxItemMiss.emitted = [⟨.unexpectedCfgs, .warning, none⟩] ∧
    eid ∈ dcxParentHit.fulfilled ∧
    dcxParentHit.emitted = [] := by
  have hpi : natEq parentId itemId = false := by
    cases h : natEq parentId itemId with
    | false => rfl
    | true => exact False.elim (hneq (natEq_sound h))
  have hpp : natEq parentId parentId = true := natEq_refl parentId
  have hSpecMiss : revealActualLevelSpec opts
      ((if natEq parentId itemId then
        (⟨fun l => if LintName.beq l .unexpectedCfgs then some ⟨.expect, some eid, .nodeSrc (.lint .unexpectedCfgs) 1 none⟩ else none, []⟩ : ScopeState)
        else (⟨fun _ => none, []⟩ : ScopeState)).specs) .unexpectedCfgs = ⟨.warn, none, .defaultSrc⟩ := by
    rw [hpi]
    unfold revealActualLevelSpec
    rw [hcap, hdUnexp]
    rfl
  have hSpecHit : revealActualLevelSpec opts
      ((if natEq parentId parentId then
        (⟨fun l => if LintName.beq l .unexpectedCfgs then some ⟨.expect, some eid, .nodeSrc (.lint .unexpectedCfgs) 1 none⟩ else none, []⟩ : ScopeState)
        else (⟨fun _ => none, []⟩ : ScopeState)).specs) .unexpectedCfgs = ⟨.expect, some eid, .nodeSrc (.lint .unexpectedCfgs) 1 none⟩ := by
    rw [hpp]
    unfold revealActualLevelSpec
    rw [hcap, hdUnexp]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold emitBufferedUnexpectedCfg
    dsimp only
    rw [hSpecMiss]
    unfold emitLintBase
    dsimp only
    rw [hCanWarn]
    intro hmem
    nomatch hmem
  · unfold emitBufferedUnexpectedCfg
    dsimp only
    rw [hSpecMiss]
    unfold emitLintBase
    dsimp only
    rw [hCanWarn]
    rfl
  · unfold emitBufferedUnexpectedCfg
    dsimp only
    rw [hSpecHit]
    exact List.Mem.head []
  · unfold emitBufferedUnexpectedCfg
    dsimp only
    rw [hSpecHit]
    rfl

end CheckCfgAndCfgAttrSection

/-! ## Part 8: Kernel-Checked Matrix Verification Witnesses -/

section MatrixWitnesses

noncomputable def defaultOpts : LintSessionOpts := ⟨none, fun _ => none, false⟩
noncomputable def capAllowOpts : LintSessionOpts := ⟨some .allow, fun _ => none, true⟩
noncomputable def capWarnOpts : LintSessionOpts := ⟨some .warn, fun _ => none, false⟩
noncomputable def capDenyOpts : LintSessionOpts := ⟨some .deny, fun _ => none, false⟩

/-- Witness 1 (`a01`): `#![forbid(unsafe_code)]` + `#[allow(unsafe_code)]` -> `E0453` and `forbid` kept. -/
theorem witness_a01_forbid_allow_e0453 :
    let init : ScopeState := ⟨fun _ => none, []⟩
    let st1 := insertSpec defaultOpts true init .unsafeCode ⟨.forbid, none, .nodeSrc (.lint .unsafeCode) 1 none⟩
    let st2 := insertSpec defaultOpts true st1 .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 2 none⟩
    st2.diags = [.overruledAttributeE0453 .unsafeCode .allow (.nodeSrc (.lint .unsafeCode) 1 none)] ∧
    (revealActualLevelSpec defaultOpts st2.specs .unsafeCode).level = .forbid := by
  exact ⟨rfl, rfl⟩

/-- Witness 2 (`a04`/`a05`): `#![forbid]` + `#[deny]` ignored, then `#[allow]` still emits `E0453`. -/
theorem witness_a05_forbid_deny_allow_e0453 :
    let init : ScopeState := ⟨fun _ => none, []⟩
    let st1 := insertSpec defaultOpts true init .unsafeCode ⟨.forbid, none, .nodeSrc (.lint .unsafeCode) 1 none⟩
    let st2 := insertSpec defaultOpts true st1 .unsafeCode ⟨.deny, none, .nodeSrc (.lint .unsafeCode) 2 none⟩
    let st3 := insertSpec defaultOpts true st2 .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 3 none⟩
    st2 = st1 ∧
    st3.diags = [.overruledAttributeE0453 .unsafeCode .allow (.nodeSrc (.lint .unsafeCode) 1 none)] := by
  exact ⟨rfl, rfl⟩

/-- Witness 3 (`a07`): `#![forbid(unused)]` + `#[allow(dead_code)]` -> FCW `#81670` and lowers to `Allow`. -/
theorem witness_a07_group_forbid_fcw_lowers :
    let init : ScopeState := ⟨fun _ => none, []⟩
    let st1 := insertSpec defaultOpts true init .deadCode ⟨.forbid, none, .nodeSrc .groupUnused 1 none⟩
    let st2 := insertSpec defaultOpts true st1 .deadCode ⟨.allow, none, .nodeSrc (.lint .deadCode) 2 none⟩
    st2.diags = [.forbiddenLintGroupsFCW .deadCode .allow (.nodeSrc .groupUnused 1 none)] ∧
    (revealActualLevelSpec defaultOpts st2.specs .deadCode).level = .allow := by
  exact ⟨rfl, rfl⟩

/-- Witness 4 (`a15`/`a17`/`a19`): `--cap-lints=deny` removes `E0453`; `--cap-lints=allow` silences `forbid`. -/
theorem witness_a17_a19_cap_lints_matrix :
    let init : ScopeState := ⟨fun _ => none, []⟩
    let stD1 := insertSpec capDenyOpts true init .unsafeCode ⟨.forbid, none, .nodeSrc (.lint .unsafeCode) 1 none⟩
    let stD2 := insertSpec capDenyOpts true stD1 .unsafeCode ⟨.allow, none, .nodeSrc (.lint .unsafeCode) 2 none⟩
    let stA1 := insertSpec capAllowOpts true init .unsafeCode ⟨.forbid, none, .nodeSrc (.lint .unsafeCode) 1 none⟩
    stD2.diags = [] ∧
    (revealActualLevelSpec capDenyOpts stD2.specs .unsafeCode).level = .allow ∧
    (revealActualLevelSpec capAllowOpts stA1.specs .unsafeCode).level = .allow := by
  exact ⟨rfl, rfl, rfl⟩

/-- Witness 5 (`a28`/`a29`/`a42`): `--force-warn dead_code` + `--cap-lints=allow` + `#[expect(dead_code)]`
emits `forceWarning` AND fulfills the expectation! -/
theorem witness_a28_a42_force_warn_cap_allow_expect :
    let cliSt : ScopeState := ⟨buildCommandLineMap [(.lint .deadCode, .forceWarn)], []⟩
    let eid : CanonExpectId := ⟨42, 0⟩
    let st1 := insertSpec capAllowOpts true cliSt .deadCode ⟨.expect, some eid, .nodeSrc (.lint .deadCode) 1 none⟩
    let eff := revealActualLevelSpec capAllowOpts st1.specs .deadCode
    let dcx1 := emitLintBase capAllowOpts eff .deadCode false emptyDiagCtxt
    let dcx2 := checkExpectations capAllowOpts st1.specs [⟨eid, .deadCode, none, false⟩] dcx1
    eff.level = .forceWarn ∧
    dcx1.fulfilled = [eid] ∧
    dcx2.emitted = [⟨.deadCode, .forceWarning, some eid⟩] := by
  exact ⟨rfl, rfl, rfl⟩

/-- Witness 6 (`a30`/`a31`): CLI `-F` vs `--force-warn` first-wins symmetry. -/
theorem witness_a30_a31_cli_symmetry :
    let mFwF := buildCommandLineMap [(.lint .deadCode, .forceWarn), (.lint .deadCode, .forbid)]
    let mFFw := buildCommandLineMap [(.lint .deadCode, .forbid), (.lint .deadCode, .forceWarn)]
    (revealActualLevelSpec defaultOpts mFwF .deadCode).level = .forceWarn ∧
    (revealActualLevelSpec defaultOpts mFFw .deadCode).level = .forbid := by
  exact ⟨rfl, rfl⟩

/-- Witness 7 (`b04`/`b05`): `#[cfg_attr(false, inline(bogus), cfg(unknown))]` compiles cleanly
with 0 inner diagnostics, whereas `#[cfg_attr(true, inline(bogus))]` errors `malformedAttrInput`. -/
theorem witness_b04_b05_cfg_attr_matrix :
    let cc := buildCheckCfg [.cfgName "feature" (.some [some "fast"])]
    let env : String → Option String → Bool := fun _ _ => false
    let envTrue : String → Option String → Bool := fun _ _ => true
    let outFalse := compileItemAttrs env cc defaultOpts ⟨fun _ => none, []⟩ 2
      [.cfgAttr (.boolLit false) [.builtinAttr "inline" false, .cfg (.nameVal "unknown" none)]]
    let outTrue := compileItemAttrs envTrue cc defaultOpts ⟨fun _ => none, []⟩ 2
      [.cfgAttr (.boolLit true) [.builtinAttr "inline" false]]
    outFalse.errors = [] ∧
    outTrue.errors = [.malformedAttrInput "inline"] := by
  exact ⟨rfl, rfl⟩

end MatrixWitnesses

end RustcLintAndCfgModel


