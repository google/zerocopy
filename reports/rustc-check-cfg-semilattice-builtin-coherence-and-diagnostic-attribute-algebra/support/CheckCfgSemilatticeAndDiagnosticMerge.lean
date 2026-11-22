/-!
# `--check-cfg` accumulation, builtin-cfg coherence, atomic cfgs, and `#[diagnostic::*]` merging

Self-contained Lean 4 development (core library only, checked with Lean v4.34.1).
It models four mechanisms of `rustc` and proves the algebraic facts stated in the
accompanying report.  Each definition names the compiler function it mirrors;
the mirrored Rust code is quoted in the report.

* Part A: `ExpectedValues`, `parse_check_cfg`, `CheckCfg::fill_well_known` and the
  `unexpected_cfgs` decision.
* Part B: `default_configuration` versus `disallow_cfgs` (lint
  `explicit_builtin_cfgs_in_flags`).
* Part C: the `target_has_atomic*` loop of `default_configuration`.
* Part D: `merge_directives`, `CustomDiagnostic::update` and
  `apply_do_not_recommend`.

Sets (`FxHashSet`) are modelled as lists observed only through membership, and
maps (`FxHashMap`) as lookup functions.  No statement is assumed: every
`theorem` below is proved, and the footer prints the axioms used.
-/

namespace CfgModel

/-! ## Part A: the `ExpectedValues` join-semilattice and `--check-cfg` accumulation -/

section PartA

variable {σ : Type} [DecidableEq σ]

/-- Membership in a list standing for an `FxHashSet<Option<Symbol>>`. -/
def memB (v : Option σ) : List (Option σ) → Bool
  | [] => false
  | x :: xs => decide (x = v) || memB v xs

theorem memB_append (v : Option σ) (a b : List (Option σ)) :
    memB v (a ++ b) = (memB v a || memB v b) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    show (decide (x = v) || memB v (xs ++ b)) = ((decide (x = v) || memB v xs) || memB v b)
    rw [ih, Bool.or_assoc]

/-- `rustc_session::config::ExpectedValues<T>`:
`Some(FxHashSet<Option<T>>)` (the listed values, `None` standing for the bare
`#[cfg(name)]` form) or `Any` (every value is expected). -/
inductive ExpectedValues (σ : Type) where
  | some (vals : List (Option σ))
  | any

namespace ExpectedValues

/-- The accumulation performed by `parse_check_cfg` on an existing entry:
`Some ∪ Some`, and `Any` as soon as either side is `Any`. -/
def join : ExpectedValues σ → ExpectedValues σ → ExpectedValues σ
  | .some a, .some b => .some (a ++ b)
  | _, _ => .any

/-- `Some(∅)`, produced by `cfg(name, values())`. -/
def bot : ExpectedValues σ := .some []

def isAny : ExpectedValues σ → Bool
  | .any => true
  | .some _ => false

/-- Does the entry make `#[cfg(name)]` / `#[cfg(name = "v")]` expected? -/
def accepts : ExpectedValues σ → Option σ → Bool
  | .some vals, v => memB v vals
  | .any, _ => true

/-- Observational equality: the same `Any` status and the same accepted values.
This is extensionality of the underlying hash set. -/
def Equiv (a b : ExpectedValues σ) : Prop :=
  a.isAny = b.isAny ∧ ∀ v, a.accepts v = b.accepts v

theorem Equiv.refl (a : ExpectedValues σ) : Equiv a a := ⟨rfl, fun _ => rfl⟩

theorem Equiv.symm {a b : ExpectedValues σ} (h : Equiv a b) : Equiv b a :=
  ⟨h.1.symm, fun v => (h.2 v).symm⟩

theorem Equiv.trans {a b c : ExpectedValues σ} (h₁ : Equiv a b) (h₂ : Equiv b c) : Equiv a c :=
  ⟨h₁.1.trans h₂.1, fun v => (h₁.2 v).trans (h₂.2 v)⟩

omit [DecidableEq σ] in
theorem isAny_join (a b : ExpectedValues σ) : (join a b).isAny = (a.isAny || b.isAny) := by
  cases a <;> cases b <;> rfl

theorem accepts_join (a b : ExpectedValues σ) (v : Option σ) :
    (join a b).accepts v = (a.accepts v || b.accepts v) := by
  cases a with
  | some x =>
    cases b with
    | some y => exact memB_append v x y
    | any => exact (Bool.or_true _).symm
  | any => cases b <;> rfl

omit [DecidableEq σ] in
/-- Associativity holds on the nose. -/
theorem join_assoc (a b c : ExpectedValues σ) : join (join a b) c = join a (join b c) := by
  cases a with
  | some x =>
    cases b with
    | some y =>
      cases c with
      | some z => show ExpectedValues.some (x ++ y ++ z) = .some (x ++ (y ++ z)); rw [List.append_assoc]
      | any => rfl
    | any => cases c <;> rfl
  | any => cases b <;> cases c <;> rfl

/-- Commutativity, up to set extensionality. -/
theorem join_comm (a b : ExpectedValues σ) : Equiv (join a b) (join b a) :=
  ⟨by rw [isAny_join, isAny_join, Bool.or_comm],
   fun v => by rw [accepts_join, accepts_join, Bool.or_comm]⟩

/-- Idempotence, up to set extensionality. -/
theorem join_idem (a : ExpectedValues σ) : Equiv (join a a) a :=
  ⟨by rw [isAny_join, Bool.or_self], fun v => by rw [accepts_join, Bool.or_self]⟩

omit [DecidableEq σ] in
/-- `Any` is absorbing (top) on both sides: this is why `values(any())` wins
regardless of whether it comes before or after `values("a", ...)`. -/
theorem join_any_left (a : ExpectedValues σ) : join .any a = .any := by cases a <;> rfl

omit [DecidableEq σ] in
theorem join_any_right (a : ExpectedValues σ) : join a .any = .any := by cases a <;> rfl

omit [DecidableEq σ] in
/-- `Some(∅)` is the identity (bottom). -/
theorem join_bot_left (a : ExpectedValues σ) : join bot a = a := by cases a <;> rfl

omit [DecidableEq σ] in
theorem join_bot_right (a : ExpectedValues σ) : join a bot = a := by
  cases a with
  | some x => show ExpectedValues.some (x ++ []) = .some x; rw [List.append_nil]
  | any => rfl

theorem join_congr {a a' b b' : ExpectedValues σ} (ha : Equiv a a') (hb : Equiv b b') :
    Equiv (join a b) (join a' b') :=
  ⟨by rw [isAny_join, isAny_join, ha.1, hb.1],
   fun v => by rw [accepts_join, accepts_join, ha.2 v, hb.2 v]⟩

/-- The induced order. -/
def le (a b : ExpectedValues σ) : Prop := Equiv (join a b) b

theorem bot_le (a : ExpectedValues σ) : le bot a := by
  show Equiv (join bot a) a
  rw [join_bot_left]; exact Equiv.refl a

theorem le_any (a : ExpectedValues σ) : le a .any := by
  show Equiv (join a .any) .any
  rw [join_any_right]; exact Equiv.refl _

theorem le_refl (a : ExpectedValues σ) : le a a := join_idem a

theorem le_antisymm {a b : ExpectedValues σ} (h₁ : le a b) (h₂ : le b a) : Equiv a b :=
  (h₂.symm.trans (join_comm b a)).trans h₁

theorem le_join_left (a b : ExpectedValues σ) : le a (join a b) := by
  show Equiv (join a (join a b)) (join a b)
  rw [← join_assoc]
  exact join_congr (join_idem a) (Equiv.refl b)

/-- `Any` and a `Some` set are never observationally equal, even if the set is large. -/
theorem any_ne_some (vals : List (Option σ)) : ¬ Equiv (.any : ExpectedValues σ) (.some vals) :=
  fun h => Bool.noConfusion h.1

end ExpectedValues

/-- The `values(...)` part of one `--check-cfg` argument. -/
inductive SpecValues (σ : Type) where
  | values (vs : List (Option σ))
  | anyValues

def SpecValues.toExpected : SpecValues σ → ExpectedValues σ
  | .values vs => .some vs
  | .anyValues => .any

/-- One `--check-cfg` argument: `cfg(n₁, …, nₖ, values(…))` or `cfg(any())`.
`cfg(n)` is `names [n] (values [none])`; `cfg()` is `names [] _`. -/
inductive Spec (σ : Type) where
  | names (ns : List σ) (vals : SpecValues σ)
  | anyNames

/-- `rustc_session::config::CheckCfg` restricted to the fields that drive the lint. -/
structure CheckCfg (σ : Type) where
  exhaustiveNames : Bool
  expecteds : σ → Option (ExpectedValues σ)

/-- The `.and_modify(..).or_insert_with(..)` chain of `parse_check_cfg`, arm by arm. -/
def mergeEntry : Option (ExpectedValues σ) → SpecValues σ → ExpectedValues σ
  | none, .values vs => .some vs
  | none, .anyValues => .any
  | some (.some old), .values vs => .some (old ++ vs)
  | some (.some _), .anyValues => .any
  | some .any, _ => .any

omit [DecidableEq σ] in
/-- The entry code is exactly the semilattice join with an adjoined "absent" bottom. -/
theorem mergeEntry_none (s : SpecValues σ) : mergeEntry none s = s.toExpected := by
  cases s <;> rfl

omit [DecidableEq σ] in
theorem mergeEntry_some (e : ExpectedValues σ) (s : SpecValues σ) :
    mergeEntry (some e) s = e.join s.toExpected := by
  cases e <;> cases s <;> rfl

def insertName (vals : SpecValues σ) (m : σ → Option (ExpectedValues σ)) (name : σ) :
    σ → Option (ExpectedValues σ) :=
  fun k => if k = name then some (mergeEntry (m k) vals) else m k

def applySpec (cc : CheckCfg σ) : Spec σ → CheckCfg σ
  | .names ns vals => { cc with expecteds := ns.foldl (insertName vals) cc.expecteds }
  | .anyNames => { cc with exhaustiveNames := false }

/-- State before the first argument: `exhaustive_names = !specs.is_empty()`. -/
def CheckCfg.init (enabled : Bool) : CheckCfg σ :=
  { exhaustiveNames := enabled, expecteds := fun _ => none }

/-- `rustc_interface::interface::parse_check_cfg`: a left fold over the arguments. -/
def parseCheckCfg (specs : List (Spec σ)) : CheckCfg σ :=
  specs.foldl applySpec (CheckCfg.init (!specs.isEmpty))

inductive Verdict where
  | ok
  | unexpectedName
  | unexpectedValue
  deriving DecidableEq, Repr

/-- The `unexpected_cfgs` decision in `parse_name_value`. -/
def lint (cc : CheckCfg σ) (name : σ) (value : Option σ) : Verdict :=
  match cc.expecteds name with
  | some (.some vals) => if memB value vals then .ok else .unexpectedValue
  | some .any => .ok
  | none => if cc.exhaustiveNames then .unexpectedName else .ok

/-! ### Observables of a lookup table -/

def present (m : σ → Option (ExpectedValues σ)) (k : σ) : Bool := (m k).isSome

def okAt (m : σ → Option (ExpectedValues σ)) (k : σ) (v : Option σ) : Bool :=
  match m k with
  | some e => e.accepts v
  | none => false

theorem lint_eq_obs (cc : CheckCfg σ) (name : σ) (value : Option σ) :
    lint cc name value =
      (if present cc.expecteds name then
        (if okAt cc.expecteds name value then Verdict.ok else Verdict.unexpectedValue)
      else if cc.exhaustiveNames then Verdict.unexpectedName else Verdict.ok) := by
  unfold lint present okAt
  cases cc.expecteds name with
  | none => rfl
  | some e =>
    cases e with
    | some vals => rfl
    | any => rfl

def memName (k : σ) : List σ → Bool
  | [] => false
  | n :: ns => decide (k = n) || memName k ns

def Spec.mentions : Spec σ → σ → Bool
  | .names ns _, k => memName k ns
  | .anyNames, _ => false

/-- The argument makes `(k, v)` expected. -/
def Spec.grants : Spec σ → σ → Option σ → Bool
  | .names ns vals, k, v => memName k ns && vals.toExpected.accepts v
  | .anyNames, _, _ => false

def Spec.isAnyNames : Spec σ → Bool
  | .anyNames => true
  | .names _ _ => false

theorem present_insertName (vals : SpecValues σ) (m : σ → Option (ExpectedValues σ))
    (name k : σ) :
    present (insertName vals m name) k = (present m k || decide (k = name)) := by
  unfold present insertName
  by_cases h : k = name
  · rw [ite_eq_left h, decide_eq_true h, Bool.or_true]; rfl
  · rw [ite_eq_right h, decide_eq_false h, Bool.or_false]

theorem okAt_insertName (vals : SpecValues σ) (m : σ → Option (ExpectedValues σ))
    (name k : σ) (v : Option σ) :
    okAt (insertName vals m name) k v
      = (okAt m k v || (decide (k = name) && vals.toExpected.accepts v)) := by
  unfold okAt insertName
  by_cases h : k = name
  · rw [ite_eq_left h, decide_eq_true h, Bool.true_and]
    cases m k with
    | none => rw [mergeEntry_none]; exact (Bool.false_or _).symm
    | some e => rw [mergeEntry_some]; exact ExpectedValues.accepts_join e _ v
  · rw [ite_eq_right h, decide_eq_false h, Bool.false_and, Bool.or_false]

theorem present_foldl_insertName (vals : SpecValues σ) (ns : List σ)
    (m : σ → Option (ExpectedValues σ)) (k : σ) :
    present (ns.foldl (insertName vals) m) k = (present m k || memName k ns) := by
  induction ns generalizing m with
  | nil => exact (Bool.or_false _).symm
  | cons n ns ih =>
    show present (ns.foldl (insertName vals) (insertName vals m n)) k
      = (present m k || (decide (k = n) || memName k ns))
    rw [ih, present_insertName, Bool.or_assoc]

theorem okAt_foldl_insertName (vals : SpecValues σ) (ns : List σ)
    (m : σ → Option (ExpectedValues σ)) (k : σ) (v : Option σ) :
    okAt (ns.foldl (insertName vals) m) k v
      = (okAt m k v || (memName k ns && vals.toExpected.accepts v)) := by
  induction ns generalizing m with
  | nil => exact (Bool.or_false _).symm
  | cons n ns ih =>
    show okAt (ns.foldl (insertName vals) (insertName vals m n)) k v
      = (okAt m k v || ((decide (k = n) || memName k ns) && vals.toExpected.accepts v))
    rw [ih, okAt_insertName]
    generalize okAt m k v = a
    generalize decide (k = n) = b
    generalize memName k ns = c
    generalize vals.toExpected.accepts v = d
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem present_applySpec (cc : CheckCfg σ) (s : Spec σ) (k : σ) :
    present (applySpec cc s).expecteds k = (present cc.expecteds k || s.mentions k) := by
  cases s with
  | names ns vals => exact present_foldl_insertName vals ns cc.expecteds k
  | anyNames => exact (Bool.or_false _).symm

theorem okAt_applySpec (cc : CheckCfg σ) (s : Spec σ) (k : σ) (v : Option σ) :
    okAt (applySpec cc s).expecteds k v = (okAt cc.expecteds k v || s.grants k v) := by
  cases s with
  | names ns vals => exact okAt_foldl_insertName vals ns cc.expecteds k v
  | anyNames => exact (Bool.or_false _).symm

theorem exhaustive_applySpec (cc : CheckCfg σ) (s : Spec σ) :
    (applySpec cc s).exhaustiveNames = (cc.exhaustiveNames && !s.isAnyNames) := by
  cases s with
  | names ns vals => exact (Bool.and_true _).symm
  | anyNames => exact (Bool.and_false _).symm

theorem present_foldl_applySpec (specs : List (Spec σ)) (cc : CheckCfg σ) (k : σ) :
    present (specs.foldl applySpec cc).expecteds k
      = (present cc.expecteds k || specs.any (fun s => s.mentions k)) := by
  induction specs generalizing cc with
  | nil => exact (Bool.or_false _).symm
  | cons s specs ih =>
    show present (specs.foldl applySpec (applySpec cc s)).expecteds k
      = (present cc.expecteds k || (s.mentions k || specs.any (fun s => s.mentions k)))
    rw [ih, present_applySpec, Bool.or_assoc]

theorem okAt_foldl_applySpec (specs : List (Spec σ)) (cc : CheckCfg σ) (k : σ) (v : Option σ) :
    okAt (specs.foldl applySpec cc).expecteds k v
      = (okAt cc.expecteds k v || specs.any (fun s => s.grants k v)) := by
  induction specs generalizing cc with
  | nil => exact (Bool.or_false _).symm
  | cons s specs ih =>
    show okAt (specs.foldl applySpec (applySpec cc s)).expecteds k v
      = (okAt cc.expecteds k v || (s.grants k v || specs.any (fun s => s.grants k v)))
    rw [ih, okAt_applySpec, Bool.or_assoc]

theorem exhaustive_foldl_applySpec (specs : List (Spec σ)) (cc : CheckCfg σ) :
    (specs.foldl applySpec cc).exhaustiveNames
      = (cc.exhaustiveNames && !specs.any Spec.isAnyNames) := by
  induction specs generalizing cc with
  | nil => exact (Bool.and_true _).symm
  | cons s specs ih =>
    show (specs.foldl applySpec (applySpec cc s)).exhaustiveNames
      = (cc.exhaustiveNames && !(s.isAnyNames || specs.any Spec.isAnyNames))
    rw [ih, exhaustive_applySpec]
    generalize cc.exhaustiveNames = a
    generalize s.isAnyNames = b
    generalize specs.any Spec.isAnyNames = c
    cases a <;> cases b <;> cases c <;> rfl

/-- `List.any` does not depend on the order of the list. -/
theorem any_perm {α : Type} (f : α → Bool) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    l₁.any f = l₂.any f := by
  induction h with
  | nil => rfl
  | @cons x t₁ t₂ _ ih =>
    show (f x || t₁.any f) = (f x || t₂.any f)
    rw [ih]
  | swap x y l =>
    show (f y || (f x || l.any f)) = (f x || (f y || l.any f))
    exact Bool.or_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem isEmpty_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) : l₁.isEmpty = l₂.isEmpty := by
  induction h with
  | nil => rfl
  | cons x _ _ => rfl
  | swap x y l => rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Denotation of `parse_check_cfg`: the verdict is a function of three
order-independent facts about the argument list. -/
theorem lint_parse (specs : List (Spec σ)) (name : σ) (value : Option σ) :
    lint (parseCheckCfg specs) name value =
      (if specs.any (fun s => s.mentions name) then
        (if specs.any (fun s => s.grants name value) then Verdict.ok else Verdict.unexpectedValue)
      else if (!specs.isEmpty && !specs.any Spec.isAnyNames) then Verdict.unexpectedName
      else Verdict.ok) := by
  rw [lint_eq_obs]
  unfold parseCheckCfg
  rw [present_foldl_applySpec, okAt_foldl_applySpec, exhaustive_foldl_applySpec]
  rfl

/-- **Order-independent CLI accumulation.**  Permuting the `--check-cfg`
arguments never changes any `unexpected_cfgs` verdict. -/
theorem checkCfg_fold_perm_invariant {l₁ l₂ : List (Spec σ)} (h : l₁.Perm l₂)
    (name : σ) (value : Option σ) :
    lint (parseCheckCfg l₁) name value = lint (parseCheckCfg l₂) name value := by
  rw [lint_parse, lint_parse,
    any_perm (fun s : Spec σ => s.mentions name) h,
    any_perm (fun s : Spec σ => s.grants name value) h,
    any_perm Spec.isAnyNames h, isEmpty_perm h]

/-- Repeating an argument is harmless (idempotence at the level of verdicts). -/
theorem checkCfg_duplicate_spec (s : Spec σ) (l : List (Spec σ)) (name : σ) (value : Option σ) :
    lint (parseCheckCfg (s :: s :: l)) name value = lint (parseCheckCfg (s :: l)) name value := by
  rw [lint_parse, lint_parse]
  show (if (s.mentions name || (s.mentions name || l.any fun s => s.mentions name)) = true then
        (if (s.grants name value || (s.grants name value || l.any fun s => s.grants name value)) = true
          then Verdict.ok else Verdict.unexpectedValue)
      else if (!(s :: s :: l).isEmpty &&
          !(s.isAnyNames || (s.isAnyNames || l.any Spec.isAnyNames))) = true
        then Verdict.unexpectedName else Verdict.ok) =
      (if (s.mentions name || l.any fun s => s.mentions name) = true then
        (if (s.grants name value || l.any fun s => s.grants name value) = true
          then Verdict.ok else Verdict.unexpectedValue)
      else if (!(s :: l).isEmpty && !(s.isAnyNames || l.any Spec.isAnyNames)) = true
        then Verdict.unexpectedName else Verdict.ok)
  rw [← Bool.or_assoc, Bool.or_self, ← Bool.or_assoc, Bool.or_self, ← Bool.or_assoc, Bool.or_self]
  rfl

/-! ### `CheckCfg::fill_well_known` -/

/-- One `ins!(name, init).extend(ext)` line of `fill_well_known`.
`no_values` is `init = [none]`; `empty_values` is `init = []`. -/
structure WellKnown (σ : Type) where
  name : σ
  init : List (Option σ)
  ext : List (Option σ)

/-- `self.expecteds.entry(name).or_insert_with(init)` followed by `.extend(ext)`
(`extend` is a no-op on `Any`).  A pre-existing user entry keeps its own values:
`init` is *not* added to it. -/
def fillOne (m : σ → Option (ExpectedValues σ)) (w : WellKnown σ) :
    σ → Option (ExpectedValues σ) :=
  fun k =>
    if k = w.name then
      some (match m k with
        | none => .some (w.init ++ w.ext)
        | some (.some old) => .some (old ++ w.ext)
        | some .any => .any)
    else m k

def fillWellKnown (wk : List (WellKnown σ)) (cc : CheckCfg σ) : CheckCfg σ :=
  { cc with expecteds := wk.foldl fillOne cc.expecteds }

/-- The configuration the lint consults.  `fill_well_known` returns early when
no `--check-cfg` argument was given. -/
def checkConfig (wk : List (WellKnown σ)) (specs : List (Spec σ)) : CheckCfg σ :=
  if specs.isEmpty then CheckCfg.init false else fillWellKnown wk (parseCheckCfg specs)

theorem present_fillOne (m : σ → Option (ExpectedValues σ)) (w : WellKnown σ) (k : σ) :
    present (fillOne m w) k = (present m k || decide (k = w.name)) := by
  unfold present fillOne
  by_cases h : k = w.name
  · rw [ite_eq_left h, decide_eq_true h, Bool.or_true]; rfl
  · rw [ite_eq_right h, decide_eq_false h, Bool.or_false]

theorem okAt_fillOne (m : σ → Option (ExpectedValues σ)) (w : WellKnown σ) (k : σ)
    (v : Option σ) :
    okAt (fillOne m w) k v =
      (okAt m k v || (decide (k = w.name) && (memB v w.ext || (!present m k && memB v w.init)))) := by
  unfold okAt fillOne present
  by_cases h : k = w.name
  · rw [ite_eq_left h, decide_eq_true h, Bool.true_and]
    cases m k with
    | none =>
      show memB v (w.init ++ w.ext) = (false || (memB v w.ext || (!false && memB v w.init)))
      rw [memB_append, Bool.false_or, Bool.not_false, Bool.true_and, Bool.or_comm]
    | some e =>
      cases e with
      | some old =>
        show memB v (old ++ w.ext) = (memB v old || (memB v w.ext || (!true && memB v w.init)))
        rw [memB_append, Bool.not_true, Bool.false_and, Bool.or_false]
      | any => rfl
  · rw [ite_eq_right h, decide_eq_false h, Bool.false_and, Bool.or_false]

/-- Two tables with the same observables. -/
def ObsEq (m₁ m₂ : σ → Option (ExpectedValues σ)) : Prop :=
  ∀ k, present m₁ k = present m₂ k ∧ ∀ v, okAt m₁ k v = okAt m₂ k v

theorem obsEq_fillOne {m₁ m₂ : σ → Option (ExpectedValues σ)} (h : ObsEq m₁ m₂)
    (w : WellKnown σ) : ObsEq (fillOne m₁ w) (fillOne m₂ w) := by
  intro k
  refine ⟨?_, fun v => ?_⟩
  · rw [present_fillOne, present_fillOne, (h k).1]
  · rw [okAt_fillOne, okAt_fillOne, (h k).1, (h k).2 v]

theorem obsEq_foldl_fillOne (wk : List (WellKnown σ)) {m₁ m₂ : σ → Option (ExpectedValues σ)}
    (h : ObsEq m₁ m₂) : ObsEq (wk.foldl fillOne m₁) (wk.foldl fillOne m₂) := by
  induction wk generalizing m₁ m₂ with
  | nil => exact h
  | cons w wk ih => exact ih (obsEq_fillOne h w)

theorem lint_congr {c₁ c₂ : CheckCfg σ} (he : c₁.exhaustiveNames = c₂.exhaustiveNames)
    (ho : ObsEq c₁.expecteds c₂.expecteds) (name : σ) (value : Option σ) :
    lint c₁ name value = lint c₂ name value := by
  rw [lint_eq_obs, lint_eq_obs, he, (ho name).1, (ho name).2 value]

theorem obsEq_parse_of_perm {l₁ l₂ : List (Spec σ)} (h : l₁.Perm l₂) :
    ObsEq (parseCheckCfg l₁).expecteds (parseCheckCfg l₂).expecteds := by
  intro k
  unfold parseCheckCfg
  refine ⟨?_, fun v => ?_⟩
  · rw [present_foldl_applySpec, present_foldl_applySpec,
      any_perm (fun s : Spec σ => s.mentions k) h]; rfl
  · rw [okAt_foldl_applySpec, okAt_foldl_applySpec,
      any_perm (fun s : Spec σ => s.grants k v) h]; rfl

theorem exhaustive_parse_of_perm {l₁ l₂ : List (Spec σ)} (h : l₁.Perm l₂) :
    (parseCheckCfg l₁).exhaustiveNames = (parseCheckCfg l₂).exhaustiveNames := by
  unfold parseCheckCfg
  rw [exhaustive_foldl_applySpec, exhaustive_foldl_applySpec,
    any_perm Spec.isAnyNames h, isEmpty_perm h]

/-- Order independence survives the well-known fill, for any well-known table. -/
theorem checkConfig_perm_invariant (wk : List (WellKnown σ)) {l₁ l₂ : List (Spec σ)}
    (h : l₁.Perm l₂) (name : σ) (value : Option σ) :
    lint (checkConfig wk l₁) name value = lint (checkConfig wk l₂) name value := by
  unfold checkConfig
  rw [isEmpty_perm h]
  cases l₂.isEmpty with
  | true => rfl
  | false =>
    exact lint_congr (c₁ := fillWellKnown wk (parseCheckCfg l₁))
      (c₂ := fillWellKnown wk (parseCheckCfg l₂)) (exhaustive_parse_of_perm h)
      (obsEq_foldl_fillOne wk (obsEq_parse_of_perm h)) name value

end PartA

/-! ### Concrete check-cfg facts (each matches a probe case in the report) -/

inductive Sym where
  | mode | lvl | unix | panic | alpha | beta | x | abort | unwind | zzz
  deriving DecidableEq, Repr

open Sym in
/-- `--check-cfg 'cfg(mode, values("alpha"))'` flags `mode="beta"` and bare `mode`. -/
theorem only_alpha_rejects_beta_and_bare :
    lint (parseCheckCfg [Spec.names [mode] (.values [some alpha])]) mode (some beta)
        = Verdict.unexpectedValue ∧
    lint (parseCheckCfg [Spec.names [mode] (.values [some alpha])]) mode none
        = Verdict.unexpectedValue ∧
    lint (parseCheckCfg [Spec.names [mode] (.values [some alpha])]) lvl none
        = Verdict.unexpectedName := by
  decide

open Sym in
/-- `values(any())` absorbs in either order. -/
theorem any_absorbs_both_orders :
    lint (parseCheckCfg [Spec.names [mode] .anyValues, Spec.names [mode] (.values [some alpha])])
        mode (some beta) = Verdict.ok ∧
    lint (parseCheckCfg [Spec.names [mode] (.values [some alpha]), Spec.names [mode] .anyValues])
        mode (some beta) = Verdict.ok := by
  decide

open Sym in
/-- No `--check-cfg` argument: the lint never fires. -/
theorem no_specs_no_lint (wk : List (WellKnown Sym)) (name : Sym) (value : Option Sym) :
    lint (checkConfig wk []) name value = Verdict.ok := rfl

open Sym in
/-- **`fill_well_known` is not a join for bare well-known names.**
With `--check-cfg 'cfg(unix, values("x"))'` the well-known `ins!(sym::unix, no_values)`
does not add `none()`, so bare `#[cfg(unix)]` becomes unexpected, although the join of
the user entry with the well-known entry would accept it. -/
theorem ce_wellKnown_fill_shadows_bare_form :
    lint (checkConfig [⟨unix, [none], []⟩] [Spec.names [unix] (.values [some x])]) unix none
        = Verdict.unexpectedValue ∧
    (ExpectedValues.join (.some [some x]) (.some [none])).accepts (none : Option Sym) = true ∧
    lint (checkConfig [⟨unix, [none], []⟩] [Spec.names [] (.values [none])]) unix none
        = Verdict.ok := by
  decide

open Sym in
/-- For valued well-known names (`ins!(name, empty_values).extend(..)`) the fill *is* a
union: a user value and the builtin values are all expected. -/
theorem wellKnown_fill_unions_valued_names :
    lint (checkConfig [⟨panic, [], [some abort, some unwind]⟩]
        [Spec.names [panic] (.values [some zzz])]) panic (some zzz) = Verdict.ok ∧
    lint (checkConfig [⟨panic, [], [some abort, some unwind]⟩]
        [Spec.names [panic] (.values [some zzz])]) panic (some abort) = Verdict.ok ∧
    lint (checkConfig [⟨panic, [], [some abort, some unwind]⟩]
        [Spec.names [] (.values [none])]) panic (some zzz) = Verdict.unexpectedValue := by
  decide

/-! ## Part B: flags, the crate configuration, and `disallow_cfgs` -/

inductive PanicStrategy where
  | unwind | abort | immediateAbort
  deriving DecidableEq, Repr

inductive Sanitizer where
  | address | kernelAddress | hwaddress | kernelHwaddress | leak
  deriving DecidableEq, Repr

/-- The compiler flags and target facts that `default_configuration` reads. -/
structure SessionFlags where
  debugAssertions : Bool
  overflowChecks : Bool
  ubChecks : Bool
  contractChecks : Bool
  panic : PanicStrategy
  sanitizers : List Sanitizer
  procMacroCrate : Bool
  testHarness : Bool
  familyUnix : Bool
  familyWindows : Bool
  /-- nightly build ∧ `atomic_cas` ∧ some width in range -/
  bareHasAtomic : Bool

/-- `(name, value)` pairs that `default_configuration` may insert. -/
inductive BuiltinCfg where
  | debugAssertions | overflowChecks | ubChecks | contractChecks
  | panicUnwind | panicAbort | panicImmediateAbort
  | sanitizeAddress | sanitizeHwaddress | sanitizeLeak
  | procMacro | unix | windows | test
  /-- bare `target_has_atomic` (no value) -/
  | targetHasAtomicBare
  deriving DecidableEq, Repr

/-- Membership in `default_configuration(sess)`. -/
def flagSets (f : SessionFlags) : BuiltinCfg → Bool
  | .debugAssertions => f.debugAssertions
  | .overflowChecks => f.overflowChecks
  | .ubChecks => f.ubChecks
  | .contractChecks => f.contractChecks
  | .panicUnwind => decide (f.panic = .unwind)
  | .panicAbort => decide (f.panic = .abort) || decide (f.panic = .immediateAbort)
  | .panicImmediateAbort => decide (f.panic = .immediateAbort)
  | .sanitizeAddress =>
    f.sanitizers.any (fun s => decide (s = .address) || decide (s = .kernelAddress))
  | .sanitizeHwaddress =>
    f.sanitizers.any (fun s => decide (s = .hwaddress) || decide (s = .kernelHwaddress))
  | .sanitizeLeak => f.sanitizers.any (fun s => decide (s = .leak))
  | .procMacro => f.procMacroCrate
  | .unix => f.familyUnix
  | .windows => f.familyWindows
  | .test => f.testHarness
  | .targetHasAtomicBare => f.bareHasAtomic

/-- The match arms of `disallow_cfgs`.  `test` is deliberately exempt, and the bare
form of `target_has_atomic` is not matched (only `(target_has_atomic, Some(_))` is). -/
def gated : BuiltinCfg → Bool
  | .test => false
  | .targetHasAtomicBare => false
  | _ => true

/-- A `--cfg` argument: a builtin pair or a user-space cfg (`feature="x"`, `miri`, …). -/
inductive Atom where
  | builtin (b : BuiltinCfg)
  | userSpace (n : Nat)
  deriving DecidableEq, Repr

/-- The crate configuration: `--cfg` entries together with `default_configuration`. -/
def cfgActive (f : SessionFlags) (user : List Atom) : Atom → Prop
  | .builtin b => flagSets f b = true ∨ Atom.builtin b ∈ user
  | .userSpace n => Atom.userSpace n ∈ user

def isGatedAtom : Atom → Bool
  | .builtin b => gated b
  | .userSpace _ => false

/-- `disallow_cfgs`: the `--cfg` entries reported by `explicit_builtin_cfgs_in_flags`. -/
def disallowBuiltinCfgs : List Atom → List Atom
  | [] => []
  | a :: rest => if isGatedAtom a then a :: disallowBuiltinCfgs rest else disallowBuiltinCfgs rest

theorem disallow_nil_iff (user : List Atom) :
    disallowBuiltinCfgs user = [] ↔ ∀ a, a ∈ user → isGatedAtom a = false := by
  induction user with
  | nil => exact ⟨fun _ a h => (nomatch h), fun _ => rfl⟩
  | cons a rest ih =>
    cases hg : isGatedAtom a with
    | true =>
      constructor
      · intro h
        have h' : a :: disallowBuiltinCfgs rest = [] := by
          have : disallowBuiltinCfgs (a :: rest) = a :: disallowBuiltinCfgs rest := by
            show (if isGatedAtom a then a :: disallowBuiltinCfgs rest else disallowBuiltinCfgs rest)
              = a :: disallowBuiltinCfgs rest
            rw [hg]; rfl
          rw [← this]; exact h
        exact nomatch h'
      · intro h
        have := h a (List.Mem.head _)
        rw [hg] at this
        exact nomatch this
    | false =>
      have hstep : disallowBuiltinCfgs (a :: rest) = disallowBuiltinCfgs rest := by
        show (if isGatedAtom a then a :: disallowBuiltinCfgs rest else disallowBuiltinCfgs rest)
          = disallowBuiltinCfgs rest
        rw [hg]; rfl
      rw [hstep, ih]
      constructor
      · intro h b hb
        cases hb with
        | head => exact hg
        | tail _ hb => exact h b hb
      · intro h b hb
        exact h b (List.Mem.tail _ hb)

/-- Coherence for the cfgs the gate is meant to protect: the cfg is active exactly
when the controlling flag (or target fact) says so. -/
def Coherent (f : SessionFlags) (user : List Atom) : Prop :=
  ∀ b, gated b = true → (cfgActive f user (.builtin b) ↔ flagSets f b = true)

/-- A gated builtin pair passed on the command line although the flags do not imply it. -/
def Spoofed (f : SessionFlags) (a : Atom) : Prop :=
  ∃ b, a = .builtin b ∧ gated b = true ∧ flagSets f b = false

/-- **Exact characterisation of coherence.** -/
theorem coherentSession_iff_no_spoofed_builtin_cfg (f : SessionFlags) (user : List Atom) :
    Coherent f user ↔ ∀ a, a ∈ user → ¬ Spoofed f a := by
  constructor
  · intro hc a ha hs
    cases hs with
    | intro b hb =>
      have hab := hb.1
      have hg := hb.2.1
      have hf := hb.2.2
      rw [hab] at ha
      have ht : flagSets f b = true := (hc b hg).mp (Or.inr ha)
      rw [hf] at ht
      exact nomatch ht
  · intro hns b hg
    constructor
    · intro h
      cases h with
      | inl h => exact h
      | inr h =>
        cases hfb : flagSets f b with
        | true => rfl
        | false => exact absurd ⟨b, rfl, hg, hfb⟩ (hns _ h)
    · intro h
      exact Or.inl h

/-- **Soundness of the gate.**  If `disallow_cfgs` reports nothing, the session is
coherent on every gated cfg, whatever the flags are. -/
theorem disallow_empty_implies_coherent (f : SessionFlags) (user : List Atom)
    (h : disallowBuiltinCfgs user = []) : Coherent f user := by
  rw [coherentSession_iff_no_spoofed_builtin_cfg]
  intro a ha hs
  cases hs with
  | intro b hb =>
    have hga := (disallow_nil_iff user).mp h a ha
    rw [hb.1] at hga
    have hg : gated b = true := hb.2.1
    have hga' : gated b = false := hga
    rw [hg] at hga'
    exact nomatch hga'

/-- The instance named in the report: `cfg(ub_checks)` follows `-Z ub-checks`. -/
theorem ubChecks_coherent_of_gate (f : SessionFlags) (user : List Atom)
    (h : disallowBuiltinCfgs user = []) :
    cfgActive f user (.builtin .ubChecks) ↔ f.ubChecks = true :=
  disallow_empty_implies_coherent f user h .ubChecks rfl

inductive LintLevel where
  | allow | warn | deny | forbid
  deriving DecidableEq, Repr

def LintLevel.isError : LintLevel → Bool
  | .deny => true
  | .forbid => true
  | _ => false

/-- The gate is a lint: the session is rejected only if the effective level of
`explicit_builtin_cfgs_in_flags` is an error level. -/
def sessionAccepted (lvl : LintLevel) (user : List Atom) : Prop :=
  lvl.isError = true → disallowBuiltinCfgs user = []

theorem accepted_at_deny_implies_coherent (f : SessionFlags) (user : List Atom)
    (h : sessionAccepted .deny user) : Coherent f user :=
  disallow_empty_implies_coherent f user (h rfl)

/-- What `core::intrinsics::ub_checks()` evaluates to in generated code: `sess.ub_checks()`. -/
def codegenUbChecks (f : SessionFlags) : Bool := f.ubChecks

def flagsAllOff : SessionFlags :=
  { debugAssertions := false, overflowChecks := false, ubChecks := false, contractChecks := false,
    panic := .unwind, sanitizers := [], procMacroCrate := false, testHarness := false,
    familyUnix := true, familyWindows := false, bareHasAtomic := false }

/-- **Counterexample 1.**  With the lint capped below `deny` (`-A`, `-W`,
`--cap-lints allow|warn`, or an in-source `#![allow]`), `--cfg ub_checks` is accepted:
`cfg(ub_checks)` is active while code generation runs with UB checks off, and the
session is not coherent. -/
theorem ce1_spoofed_cli_ub_checks_diverges_from_codegen :
    sessionAccepted .allow [.builtin .ubChecks] ∧
    sessionAccepted .warn [.builtin .ubChecks] ∧
    cfgActive flagsAllOff [.builtin .ubChecks] (.builtin .ubChecks) ∧
    codegenUbChecks flagsAllOff = false ∧
    ¬ Coherent flagsAllOff [.builtin .ubChecks] ∧
    ¬ sessionAccepted .deny [.builtin .ubChecks] := by
  refine ⟨fun h => (nomatch h), fun h => (nomatch h), Or.inr (List.Mem.head _), rfl, ?_, ?_⟩
  · intro hc
    have ht : flagSets flagsAllOff .ubChecks = true :=
      (hc .ubChecks rfl).mp (Or.inr (List.Mem.head _))
    exact nomatch ht
  · intro h
    have := h rfl
    exact nomatch this

/-- The gate is strictly conservative: `--cfg unix` on a `unix` target is coherent
but still rejected. -/
theorem gate_strictly_conservative :
    Coherent flagsAllOff [.builtin .unix] ∧ disallowBuiltinCfgs [.builtin .unix] ≠ [] := by
  constructor
  · rw [coherentSession_iff_no_spoofed_builtin_cfg]
    intro a ha hs
    cases hs with
    | intro b hb =>
      cases ha with
      | head =>
        have hbu : BuiltinCfg.unix = b := Atom.builtin.inj hb.1
        have hf := hb.2.2
        rw [← hbu] at hf
        exact nomatch hf
      | tail _ h => exact nomatch h
  · intro h
    exact nomatch h

/-- `--cfg test` without `--test` passes the gate at any lint level, by design. -/
theorem test_cfg_is_exempt :
    disallowBuiltinCfgs [.builtin .test] = [] ∧
    cfgActive flagsAllOff [.builtin .test] (.builtin .test) ∧
    flagSets flagsAllOff .test = false :=
  ⟨rfl, Or.inr (List.Mem.head _), rfl⟩

/-- A hole in the gate: bare `--cfg target_has_atomic` is not matched by
`disallow_cfgs`, so it is accepted at `deny` even where `default_configuration`
does not set it. -/
theorem ce_gate_gap_bare_target_has_atomic :
    sessionAccepted .deny [.builtin .targetHasAtomicBare] ∧
    cfgActive flagsAllOff [.builtin .targetHasAtomicBare] (.builtin .targetHasAtomicBare) ∧
    flagSets flagsAllOff .targetHasAtomicBare = false :=
  ⟨fun _ => rfl, Or.inr (List.Mem.head _), rfl⟩

/-- `-C panic=immediate-abort` sets both `panic="immediate-abort"` and `panic="abort"`. -/
theorem immediate_abort_sets_both_panic_cfgs (f : SessionFlags) (h : f.panic = .immediateAbort) :
    flagSets f .panicImmediateAbort = true ∧ flagSets f .panicAbort = true ∧
    flagSets f .panicUnwind = false := by
  refine ⟨?_, ?_, ?_⟩
  · show decide (f.panic = .immediateAbort) = true
    rw [h]; rfl
  · show (decide (f.panic = .abort) || decide (f.panic = .immediateAbort)) = true
    rw [h]; rfl
  · show decide (f.panic = .unwind) = false
    rw [h]; rfl

/-- Hence `cfg(panic = "abort")` does not determine the strategy. -/
theorem panic_abort_cfg_not_injective :
    flagSets { flagsAllOff with panic := .abort } .panicAbort
      = flagSets { flagsAllOff with panic := .immediateAbort } .panicAbort := rfl

/-- Kernel sanitizers fold into their user-space cfg values. -/
theorem kernel_sanitizers_fold :
    flagSets { flagsAllOff with sanitizers := [.kernelAddress] } .sanitizeAddress = true ∧
    flagSets { flagsAllOff with sanitizers := [.kernelHwaddress] } .sanitizeHwaddress = true ∧
    flagSets { flagsAllOff with sanitizers := [.kernelAddress] } .sanitizeAddress
      = flagSets { flagsAllOff with sanitizers := [.address] } .sanitizeAddress := by
  decide

/-! ## Part C: `target_has_atomic*` -/

inductive AKey where
  | cas          -- `target_has_atomic`
  | loadStore    -- `target_has_atomic_load_store`
  | primAlign    -- `target_has_atomic_primitive_alignment`
  deriving DecidableEq, Repr

inductive AVal where
  | bare
  | bits (n : Nat)
  | ptr
  deriving DecidableEq, Repr

inductive Cpu where
  | x86_64 | x86_64_v3 | penryn | pentium4 | generic | bpfV3 | bpfV4
  deriving DecidableEq, Repr

/-- The fields of a target specification that the atomic loop reads. -/
structure AtomicTarget where
  pointerWidth : Nat
  defaultCpu : Cpu
  minAtomicWidth : Option Nat
  maxAtomicWidth : Option Nat
  /-- `per_cpu_atomic_widths` (present from 2026-11-09; `[]` models earlier compilers) -/
  perCpuAtomicWidths : List (Cpu × (Nat × Nat))
  atomicCas : Bool
  /-- ABI alignment in bits of the integer of the given bit width -/
  intAlignBits : Nat → Nat
  pointerAlignBits : Nat

/-- The code generation options a user can pass.  `cmpxchg16b` stands for
`-C target-feature=+cmpxchg16b` (also implied by `-C target-cpu=x86-64-v3`). -/
structure CodegenOpts where
  targetCpu : Option Cpu
  cmpxchg16b : Bool

def lookupCpu (c : Cpu) : List (Cpu × (Nat × Nat)) → Option (Nat × Nat)
  | [] => none
  | (c', w) :: rest => if c = c' then some w else lookupCpu c rest

/-- `Target::atomic_widths(cpu)`; with an empty table this is the pair
`(min_atomic_width(), max_atomic_width())` of earlier compilers. -/
def atomicWidths (t : AtomicTarget) (cpu : Cpu) : Nat × Nat :=
  match lookupCpu cpu t.perCpuAtomicWidths with
  | some w => w
  | none => (t.minAtomicWidth.getD 8, t.maxAtomicWidth.getD t.pointerWidth)

/-- The `insert_atomic` closure. -/
def insertAtomic (t : AtomicTarget) (v : AVal) (i align : Nat) : List (AKey × AVal) :=
  (if t.atomicCas then [(AKey.cas, v)] else [])
    ++ (if align = i then [(AKey.primAlign, v)] else [])
    ++ [(AKey.loadStore, v)]

def perWidth (t : AtomicTarget) (lo hi i : Nat) : List (AKey × AVal) :=
  if lo ≤ i ∧ i ≤ hi then
    insertAtomic t (.bits i) i (t.intAlignBits i)
      ++ (if t.pointerWidth = i then insertAtomic t .ptr i t.pointerAlignBits else [])
  else []

/-- The `target_has_atomic*` part of `default_configuration`.  The option record is
consulted only through the CPU *name*; target features are never read. -/
def atomicCfgs (t : AtomicTarget) (nightly : Bool) (o : CodegenOpts) : List (AKey × AVal) :=
  let w := atomicWidths t (o.targetCpu.getD t.defaultCpu)
  let anyWidth := [8, 16, 32, 64, 128].any (fun i => decide (w.1 ≤ i ∧ i ≤ w.2))
  (if nightly && anyWidth then
      (if t.atomicCas then [(AKey.cas, AVal.bare)] else []) ++ [(AKey.loadStore, AVal.bare)]
    else [])
    ++ perWidth t w.1 w.2 8 ++ perWidth t w.1 w.2 16 ++ perWidth t w.1 w.2 32
    ++ perWidth t w.1 w.2 64 ++ perWidth t w.1 w.2 128

def naturalAlign : Nat → Nat := fun i => i

/-- `i686-unknown-linux-gnu`: `max_atomic_width = Some(64)`; the data layout does not
override `i64`, whose default ABI alignment is 32 bits. -/
def i686LinuxGnu : AtomicTarget :=
  { pointerWidth := 32, defaultCpu := .pentium4, minAtomicWidth := none, maxAtomicWidth := some 64,
    perCpuAtomicWidths := [], atomicCas := true,
    intAlignBits := fun i => if i = 64 then 32 else i, pointerAlignBits := 32 }

/-- `x86_64-unknown-linux-gnu`: `max_atomic_width = Some(64)`. -/
def x86_64LinuxGnu : AtomicTarget :=
  { pointerWidth := 64, defaultCpu := .x86_64, minAtomicWidth := none, maxAtomicWidth := some 64,
    perCpuAtomicWidths := [], atomicCas := true, intAlignBits := naturalAlign,
    pointerAlignBits := 64 }

/-- `x86_64-apple-darwin` and `x86_64-pc-windows-msvc`: `max_atomic_width = Some(128)`. -/
def x86_64Max128 : AtomicTarget :=
  { x86_64LinuxGnu with defaultCpu := .penryn, maxAtomicWidth := some 128 }

/-- `thumbv6m-none-eabi`: `atomic_cas = false`, default maximum (pointer width). -/
def thumbv6m : AtomicTarget :=
  { pointerWidth := 32, defaultCpu := .generic, minAtomicWidth := none, maxAtomicWidth := none,
    perCpuAtomicWidths := [], atomicCas := false, intAlignBits := naturalAlign,
    pointerAlignBits := 32 }

/-- `riscv32imc-unknown-none-elf`: `max_atomic_width = Some(32)`, `atomic_cas = false`. -/
def riscv32imc : AtomicTarget := { thumbv6m with maxAtomicWidth := some 32 }

/-- `m68k-unknown-linux-gnu`: 32-bit integers and pointers are 16-bit aligned. -/
def m68kLinuxGnu : AtomicTarget :=
  { pointerWidth := 32, defaultCpu := .generic, minAtomicWidth := none, maxAtomicWidth := some 32,
    perCpuAtomicWidths := [], atomicCas := true,
    intAlignBits := fun i => if i = 32 then 16 else if i = 64 then 16 else i,
    pointerAlignBits := 16 }

/-- BPF targets after 2026-11-09: `(8, 64)` by default, `(8, 0)` (an empty range)
for the CPU names `v1`, `v2`, `v3` and `generic`. -/
def bpfPerCpu : AtomicTarget :=
  { pointerWidth := 64, defaultCpu := .generic, minAtomicWidth := some 8, maxAtomicWidth := some 64,
    perCpuAtomicWidths := [(.bpfV3, (8, 0)), (.generic, (8, 0))], atomicCas := false,
    intAlignBits := naturalAlign, pointerAlignBits := 64 }

def baseOpts : CodegenOpts := { targetCpu := none, cmpxchg16b := false }

/-- Set equality of two finite lists. -/
def sameSet (a b : List (AKey × AVal)) : Bool :=
  a.all (fun e => decide (e ∈ b)) && b.all (fun e => decide (e ∈ a))

/-- The model reproduces the `rustc --print cfg` lines observed for `i686-unknown-linux-gnu`. -/
theorem i686_model_matches_print_cfg :
    sameSet (atomicCfgs i686LinuxGnu true baseOpts)
      [(.cas, .bare), (.cas, .bits 8), (.cas, .bits 16), (.cas, .bits 32), (.cas, .bits 64),
       (.cas, .ptr),
       (.loadStore, .bare), (.loadStore, .bits 8), (.loadStore, .bits 16), (.loadStore, .bits 32),
       (.loadStore, .bits 64), (.loadStore, .ptr),
       (.primAlign, .bits 8), (.primAlign, .bits 16), (.primAlign, .bits 32), (.primAlign, .ptr)]
      = true := by
  decide

theorem x86_64_linux_model_matches_print_cfg :
    sameSet (atomicCfgs x86_64LinuxGnu true baseOpts)
      [(.cas, .bare), (.cas, .bits 8), (.cas, .bits 16), (.cas, .bits 32), (.cas, .bits 64),
       (.cas, .ptr),
       (.loadStore, .bare), (.loadStore, .bits 8), (.loadStore, .bits 16), (.loadStore, .bits 32),
       (.loadStore, .bits 64), (.loadStore, .ptr),
       (.primAlign, .bits 8), (.primAlign, .bits 16), (.primAlign, .bits 32),
       (.primAlign, .bits 64), (.primAlign, .ptr)]
      = true := by
  decide

theorem thumbv6m_model_matches_print_cfg :
    sameSet (atomicCfgs thumbv6m true baseOpts)
      [(.loadStore, .bare), (.loadStore, .bits 8), (.loadStore, .bits 16), (.loadStore, .bits 32),
       (.loadStore, .ptr),
       (.primAlign, .bits 8), (.primAlign, .bits 16), (.primAlign, .bits 32), (.primAlign, .ptr)]
      = true := by
  decide

theorem m68k_model_matches_print_cfg :
    sameSet (atomicCfgs m68kLinuxGnu true baseOpts)
      [(.cas, .bare), (.cas, .bits 8), (.cas, .bits 16), (.cas, .bits 32), (.cas, .ptr),
       (.loadStore, .bare), (.loadStore, .bits 8), (.loadStore, .bits 16), (.loadStore, .bits 32),
       (.loadStore, .ptr),
       (.primAlign, .bits 8), (.primAlign, .bits 16)]
      = true := by
  decide

/-- **Counterexample 2.**  `i686-unknown-linux-gnu` has 64-bit compare-and-swap, but
`AtomicU64` (8-byte aligned) and `u64` (4-byte aligned) differ in alignment, so
`target_has_atomic_primitive_alignment = "64"` is absent. -/
theorem ce2_i686_atomic64_has_cas_without_primitive_align :
    (AKey.cas, AVal.bits 64) ∈ atomicCfgs i686LinuxGnu true baseOpts ∧
    (AKey.loadStore, AVal.bits 64) ∈ atomicCfgs i686LinuxGnu true baseOpts ∧
    (AKey.primAlign, AVal.bits 64) ∉ atomicCfgs i686LinuxGnu true baseOpts ∧
    (AKey.primAlign, AVal.bits 32) ∈ atomicCfgs i686LinuxGnu true baseOpts := by
  decide

/-- The same gap at pointer width on `m68k`. -/
theorem m68k_ptr_cas_without_primitive_align :
    (AKey.cas, AVal.ptr) ∈ atomicCfgs m68kLinuxGnu true baseOpts ∧
    (AKey.primAlign, AVal.ptr) ∉ atomicCfgs m68kLinuxGnu true baseOpts := by
  decide

/-- Load/store without compare-and-swap. -/
theorem load_store_without_cas :
    (AKey.loadStore, AVal.bits 32) ∈ atomicCfgs thumbv6m true baseOpts ∧
    (AKey.cas, AVal.bits 32) ∉ atomicCfgs thumbv6m true baseOpts ∧
    (AKey.cas, AVal.bare) ∉ atomicCfgs thumbv6m true baseOpts ∧
    (AKey.loadStore, AVal.bits 32) ∈ atomicCfgs riscv32imc true baseOpts ∧
    (AKey.cas, AVal.bits 32) ∉ atomicCfgs riscv32imc true baseOpts := by
  decide

/-- **Counterexample 3.**  On `x86_64-unknown-linux-gnu`, no choice of `-C target-cpu`
and no `cmpxchg16b` setting yields `target_has_atomic = "128"`: the width comes from the
target specification's static maximum (64), while targets whose specification says 128
have it with default options. -/
theorem ce3_x86_64_linux_cx16_still_lacks_atomic128_due_to_static_target_max :
    (∀ o : CodegenOpts, (AKey.cas, AVal.bits 128) ∉ atomicCfgs x86_64LinuxGnu true o) ∧
    (AKey.cas, AVal.bits 128) ∈ atomicCfgs x86_64Max128 true baseOpts := by
  constructor
  · intro o
    cases o with
    | mk cpu cx =>
      cases cpu with
      | none => cases cx <;> decide
      | some c => cases c <;> cases cx <;> decide
  · decide

/-- The target-feature bit is irrelevant for every target: the cfg list is the same
with and without `cmpxchg16b`. -/
theorem atomicCfgs_ignores_target_features (t : AtomicTarget) (nightly : Bool)
    (cpu : Option Cpu) (cx₁ cx₂ : Bool) :
    atomicCfgs t nightly { targetCpu := cpu, cmpxchg16b := cx₁ }
      = atomicCfgs t nightly { targetCpu := cpu, cmpxchg16b := cx₂ } := rfl

/-- With a per-CPU table (BPF from 2026-11-09), the CPU *name* does change the cfgs. -/
theorem per_cpu_table_changes_atomic_cfgs :
    atomicCfgs bpfPerCpu true baseOpts = [] ∧
    (AKey.loadStore, AVal.bits 64) ∈ atomicCfgs bpfPerCpu true { baseOpts with targetCpu := some .bpfV4 } ∧
    (AKey.loadStore, AVal.bits 8) ∈ atomicCfgs bpfPerCpu true { baseOpts with targetCpu := some .bpfV4 } := by
  decide

/-- On a non-nightly build the bare `target_has_atomic` / `target_has_atomic_load_store`
entries are not inserted. -/
theorem bare_entries_are_nightly_only :
    (AKey.cas, AVal.bare) ∈ atomicCfgs x86_64LinuxGnu true baseOpts ∧
    (AKey.cas, AVal.bare) ∉ atomicCfgs x86_64LinuxGnu false baseOpts ∧
    (AKey.cas, AVal.bits 64) ∈ atomicCfgs x86_64LinuxGnu false baseOpts := by
  decide

/-! ## Part D: `#[diagnostic::*]` directive merging and `do_not_recommend` -/

section PartD

/-- First-wins on optional fields: the behaviour of `merge` in the attribute parser
and of `CustomDiagnostic::update`. -/
def firstWins {α : Type} : Option α → Option α → Option α
  | some a, _ => some a
  | none, b => b

theorem firstWins_eq_or {α : Type} (a b : Option α) : firstWins a b = a.or b := by
  cases a <;> rfl

theorem firstWins_assoc {α : Type} (a b c : Option α) :
    firstWins (firstWins a b) c = firstWins a (firstWins b c) := by
  cases a <;> rfl

theorem firstWins_none_right {α : Type} (a : Option α) : firstWins a none = a := by
  cases a <;> rfl

theorem firstWins_idem {α : Type} (a : Option α) : firstWins a a = a := by
  cases a <;> rfl

/-- `rustc`'s `Directive` (format strings abstracted to `μ`, `on(..)` filters to `φ`). -/
structure Directive (μ φ : Type) where
  isRustcAttr : Bool
  filters : List φ
  message : Option μ
  label : Option μ
  notes : List μ
  parentLabel : Option μ
  deriving DecidableEq, Repr

variable {μ φ ρ : Type}

/-- `merge_directives(first, later)` when `first` is already present. -/
def Directive.merge (a b : Directive μ φ) : Directive μ φ :=
  { isRustcAttr := a.isRustcAttr || b.isRustcAttr
    filters := a.filters ++ b.filters
    message := firstWins a.message b.message
    label := firstWins a.label b.label
    notes := a.notes ++ b.notes
    parentLabel := firstWins a.parentLabel b.parentLabel }

/-- `Directive::default()`. -/
def emptyDirective : Directive μ φ :=
  { isRustcAttr := false, filters := [], message := none, label := none, notes := [],
    parentLabel := none }

/-- **Associativity of `Directive.merge`.** -/
theorem directiveMerge_assoc (a b c : Directive μ φ) :
    (a.merge b).merge c = a.merge (b.merge c) := by
  cases a with
  | mk r₁ f₁ m₁ l₁ n₁ p₁ =>
    cases b with
    | mk r₂ f₂ m₂ l₂ n₂ p₂ =>
      cases c with
      | mk r₃ f₃ m₃ l₃ n₃ p₃ =>
        show Directive.mk (r₁ || r₂ || r₃) (f₁ ++ f₂ ++ f₃) (firstWins (firstWins m₁ m₂) m₃)
            (firstWins (firstWins l₁ l₂) l₃) (n₁ ++ n₂ ++ n₃) (firstWins (firstWins p₁ p₂) p₃)
          = Directive.mk (r₁ || (r₂ || r₃)) (f₁ ++ (f₂ ++ f₃)) (firstWins m₁ (firstWins m₂ m₃))
            (firstWins l₁ (firstWins l₂ l₃)) (n₁ ++ (n₂ ++ n₃)) (firstWins p₁ (firstWins p₂ p₃))
        rw [Bool.or_assoc, List.append_assoc, firstWins_assoc, firstWins_assoc, List.append_assoc,
          firstWins_assoc]

theorem directiveMerge_empty_left (a : Directive μ φ) : emptyDirective.merge a = a := by
  cases a; rfl

theorem directiveMerge_empty_right (a : Directive μ φ) : a.merge emptyDirective = a := by
  cases a with
  | mk r f m l n p =>
    show Directive.mk (r || false) (f ++ []) (firstWins m none) (firstWins l none) (n ++ [])
        (firstWins p none) = Directive.mk r f m l n p
    rw [Bool.or_false, List.append_nil, firstWins_none_right, firstWins_none_right,
      List.append_nil, firstWins_none_right]

/-- **Non-commutativity.**  Messages 1 and 2, notes 10 and 20: the two orders differ
in the message that wins and in the order of the notes. -/
theorem ce_directiveMerge_noncomm :
    ∃ a b : Directive Nat Unit, a.merge b ≠ b.merge a ∧
      (a.merge b).message = some 1 ∧ (b.merge a).message = some 2 ∧
      (a.merge b).notes = [10, 20] ∧ (b.merge a).notes = [20, 10] :=
  ⟨{ isRustcAttr := false, filters := [], message := some 1, label := some 1, notes := [10],
     parentLabel := none },
   { isRustcAttr := false, filters := [], message := some 2, label := some 2, notes := [20],
     parentLabel := none },
   by decide⟩

/-- Merging is not idempotent either: identical notes are repeated. -/
theorem ce_directiveMerge_not_idempotent :
    ∃ a : Directive Nat Unit, a.merge a ≠ a ∧ (a.merge a).notes = [7, 7] :=
  ⟨{ isRustcAttr := false, filters := [], message := none, label := none, notes := [7],
     parentLabel := none }, by decide⟩

/-- Stacked attributes: a left fold from the identity. -/
def mergeAll (ds : List (Directive μ φ)) : Directive μ φ := ds.foldl Directive.merge emptyDirective

/-- The parser's accumulator `Option<(Span, Directive)>`, starting at `None`. -/
def mergeInto : Option (Directive μ φ) → Directive μ φ → Option (Directive μ φ)
  | none, d => some d
  | some a, d => some (a.merge d)

theorem foldl_mergeInto_some (ds : List (Directive μ φ)) (a : Directive μ φ) :
    ds.foldl mergeInto (some a) = some (ds.foldl Directive.merge a) := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih => exact ih (a.merge d)

/-- The `Option` accumulator computes the monoid fold (`None` is a freely adjoined
identity). -/
theorem foldl_mergeInto (d : Directive μ φ) (ds : List (Directive μ φ)) :
    (d :: ds).foldl mergeInto none = some (mergeAll (d :: ds)) := by
  show ds.foldl mergeInto (some d) = some (ds.foldl Directive.merge (emptyDirective.merge d))
  rw [directiveMerge_empty_left]
  exact foldl_mergeInto_some ds d

def firstMessage : List (Directive μ φ) → Option μ
  | [] => none
  | d :: ds => firstWins d.message (firstMessage ds)

def firstLabel : List (Directive μ φ) → Option μ
  | [] => none
  | d :: ds => firstWins d.label (firstLabel ds)

def allNotes : List (Directive μ φ) → List μ
  | [] => []
  | d :: ds => d.notes ++ allNotes ds

theorem foldl_merge_message (ds : List (Directive μ φ)) (a : Directive μ φ) :
    (ds.foldl Directive.merge a).message = firstWins a.message (firstMessage ds) := by
  induction ds generalizing a with
  | nil => exact (firstWins_none_right _).symm
  | cons d ds ih =>
    show (ds.foldl Directive.merge (a.merge d)).message
      = firstWins a.message (firstWins d.message (firstMessage ds))
    rw [ih, ← firstWins_assoc]; rfl

theorem foldl_merge_label (ds : List (Directive μ φ)) (a : Directive μ φ) :
    (ds.foldl Directive.merge a).label = firstWins a.label (firstLabel ds) := by
  induction ds generalizing a with
  | nil => exact (firstWins_none_right _).symm
  | cons d ds ih =>
    show (ds.foldl Directive.merge (a.merge d)).label
      = firstWins a.label (firstWins d.label (firstLabel ds))
    rw [ih, ← firstWins_assoc]; rfl

theorem foldl_merge_notes (ds : List (Directive μ φ)) (a : Directive μ φ) :
    (ds.foldl Directive.merge a).notes = a.notes ++ allNotes ds := by
  induction ds generalizing a with
  | nil => exact (List.append_nil _).symm
  | cons d ds ih =>
    show (ds.foldl Directive.merge (a.merge d)).notes = a.notes ++ (d.notes ++ allNotes ds)
    rw [ih, ← List.append_assoc]; rfl

/-- What a stack of attributes denotes: the first `message`, the first `label`, and
all notes in source order. -/
theorem mergeAll_spec (ds : List (Directive μ φ)) :
    (mergeAll ds).message = firstMessage ds ∧ (mergeAll ds).label = firstLabel ds ∧
    (mergeAll ds).notes = allNotes ds :=
  ⟨foldl_merge_message ds emptyDirective, foldl_merge_label ds emptyDirective,
   foldl_merge_notes ds emptyDirective⟩

/-- `CustomDiagnostic`: the evaluated directive. -/
structure CustomDiagnostic (ρ : Type) where
  message : Option ρ
  label : Option ρ
  notes : List ρ
  parentLabel : Option ρ

/-- `CustomDiagnostic::update`: fill unset fields, extend notes. -/
def CustomDiagnostic.update (fmt : μ → ρ) (cd : CustomDiagnostic ρ) (d : Directive μ φ) :
    CustomDiagnostic ρ :=
  { message := firstWins cd.message (d.message.map fmt)
    label := firstWins cd.label (d.label.map fmt)
    notes := cd.notes ++ d.notes.map fmt
    parentLabel := firstWins cd.parentLabel (d.parentLabel.map fmt) }

def CustomDiagnostic.empty : CustomDiagnostic ρ :=
  { message := none, label := none, notes := [], parentLabel := none }

/-- Formatting one directive. -/
def render (fmt : μ → ρ) (d : Directive μ φ) : CustomDiagnostic ρ :=
  { message := d.message.map fmt, label := d.label.map fmt, notes := d.notes.map fmt,
    parentLabel := d.parentLabel.map fmt }

theorem map_firstWins {α β : Type} (f : α → β) (a b : Option α) :
    (firstWins a b).map f = firstWins (a.map f) (b.map f) := by
  cases a <;> rfl

/-- Evaluation is a homomorphism: updating with `b` after rendering `a` equals
rendering the merged directive. -/
theorem update_render_eq_render_merge (fmt : μ → ρ) (a b : Directive μ φ) :
    (render fmt a).update fmt b = render fmt (a.merge b) := by
  cases a with
  | mk r₁ f₁ m₁ l₁ n₁ p₁ =>
    cases b with
    | mk r₂ f₂ m₂ l₂ n₂ p₂ =>
      show CustomDiagnostic.mk (firstWins (m₁.map fmt) (m₂.map fmt))
          (firstWins (l₁.map fmt) (l₂.map fmt)) (n₁.map fmt ++ n₂.map fmt)
          (firstWins (p₁.map fmt) (p₂.map fmt))
        = CustomDiagnostic.mk ((firstWins m₁ m₂).map fmt) ((firstWins l₁ l₂).map fmt)
          ((n₁ ++ n₂).map fmt) ((firstWins p₁ p₂).map fmt)
      rw [map_firstWins, map_firstWins, map_firstWins, List.map_append]

theorem render_empty (fmt : μ → ρ) :
    render fmt (emptyDirective : Directive μ φ) = CustomDiagnostic.empty := rfl

theorem foldl_update_render (fmt : μ → ρ) (ds : List (Directive μ φ)) (a : Directive μ φ) :
    ds.foldl (CustomDiagnostic.update fmt) (render fmt a)
      = render fmt (ds.foldl Directive.merge a) := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    show ds.foldl (CustomDiagnostic.update fmt) ((render fmt a).update fmt d)
      = render fmt (ds.foldl Directive.merge (a.merge d))
    rw [update_render_eq_render_merge, ih]

/-- Evaluating a sequence of directives one `update` at a time (matching filters first,
then the root directive) gives the rendering of their merge. -/
theorem eval_sequence_eq_render_mergeAll (fmt : μ → ρ) (ds : List (Directive μ φ)) :
    ds.foldl (CustomDiagnostic.update fmt) CustomDiagnostic.empty = render fmt (mergeAll ds) := by
  rw [← render_empty (φ := φ) fmt]
  exact foldl_update_render fmt ds emptyDirective

end PartD

/-! ### `#[diagnostic::do_not_recommend]` -/

section DoNotRecommend

variable {π ι : Type}

/-- One link of an obligation's derived-cause chain, listed from the failing leaf
towards the root.  `implDerived impl parent` is `ObligationCauseCode::ImplDerived`:
the obligation below was required by `impl` in order to prove `parent`. -/
inductive Cause (π ι : Type) where
  | implDerived (impl : ι) (parentPred : π)
  | otherDerived

/-- The loop of `TypeErrCtxt::apply_do_not_recommend`: walk the chain leaf → root and,
at every `ImplDerived` whose impl carries the attribute, replace the reported
obligation by that impl's parent predicate and the cause by the parent's cause. -/
def applyDnr (dnr : ι → Bool) : π × List (Cause π ι) → List (Cause π ι) → π × List (Cause π ι)
  | cur, [] => cur
  | cur, .implDerived impl parent :: rest =>
    if dnr impl then applyDnr dnr (parent, rest) rest else applyDnr dnr cur rest
  | cur, .otherDerived :: rest => applyDnr dnr cur rest

/-- The reported predicate and its remaining cause chain. -/
def report (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι)) : π × List (Cause π ι) :=
  applyDnr dnr (leaf, chain) chain

/-- The marked frame closest to the root, with the chain above it. -/
def lastDnr (dnr : ι → Bool) : List (Cause π ι) → Option (π × List (Cause π ι))
  | [] => none
  | c :: rest =>
    match lastDnr dnr rest with
    | some r => some r
    | none =>
      match c with
      | .implDerived impl parent => if dnr impl then some (parent, rest) else none
      | .otherDerived => none

theorem applyDnr_eq (dnr : ι → Bool) (cur : π × List (Cause π ι)) (chain : List (Cause π ι)) :
    applyDnr dnr cur chain = (lastDnr dnr chain).getD cur := by
  induction chain generalizing cur with
  | nil => rfl
  | cons c rest ih =>
    cases c with
    | implDerived impl parent =>
      cases hd : dnr impl with
      | true =>
        have h1 : applyDnr dnr cur (Cause.implDerived impl parent :: rest)
            = applyDnr dnr (parent, rest) rest := by
          show (if dnr impl then applyDnr dnr (parent, rest) rest else applyDnr dnr cur rest) = _
          rw [hd]; rfl
        have h2 : lastDnr dnr (Cause.implDerived impl parent :: rest)
            = (match lastDnr dnr rest with
                | some r => some r
                | none => some (parent, rest)) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => if dnr impl then some (parent, rest) else none) = _
          rw [hd]; rfl
        rw [h1, h2, ih]
        cases lastDnr dnr rest <;> rfl
      | false =>
        have h1 : applyDnr dnr cur (Cause.implDerived impl parent :: rest)
            = applyDnr dnr cur rest := by
          show (if dnr impl then applyDnr dnr (parent, rest) rest else applyDnr dnr cur rest) = _
          rw [hd]; rfl
        have h2 : lastDnr dnr (Cause.implDerived impl parent :: rest)
            = (match lastDnr dnr rest with
                | some r => some r
                | none => none) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => if dnr impl then some (parent, rest) else none) = _
          rw [hd]; rfl
        rw [h1, h2, ih]
        cases lastDnr dnr rest <;> rfl
    | otherDerived =>
      show applyDnr dnr cur rest = _
      rw [ih]
      show (lastDnr dnr rest).getD cur
        = (match lastDnr dnr rest with
            | some r => some r
            | none => none).getD cur
      cases lastDnr dnr rest <;> rfl

/-- **Specification of the loop.**  The report is the parent of the marked frame
closest to the root, or the original leaf if no frame is marked. -/
theorem report_eq (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι)) :
    report dnr leaf chain = (lastDnr dnr chain).getD (leaf, chain) :=
  applyDnr_eq dnr (leaf, chain) chain

/-- No marked impl frame in a chain. -/
def dnrFree (dnr : ι → Bool) : List (Cause π ι) → Bool
  | [] => true
  | .implDerived impl _ :: rest => !dnr impl && dnrFree dnr rest
  | .otherDerived :: rest => dnrFree dnr rest

theorem lastDnr_none_iff (dnr : ι → Bool) (chain : List (Cause π ι)) :
    lastDnr dnr chain = none ↔ dnrFree dnr chain = true := by
  induction chain with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons c rest ih =>
    cases c with
    | implDerived impl parent =>
      show (match lastDnr dnr rest with
            | some r => some r
            | none => if dnr impl then some (parent, rest) else none) = none
        ↔ (!dnr impl && dnrFree dnr rest) = true
      cases hl : lastDnr dnr rest with
      | some r =>
        have hf : dnrFree dnr rest = false := by
          cases hfr : dnrFree dnr rest with
          | false => rfl
          | true => rw [ih.mpr hfr] at hl; exact nomatch hl
        rw [hf, Bool.and_false]
        exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
      | none =>
        rw [ih.mp hl, Bool.and_true]
        cases dnr impl with
        | true => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
        | false => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | otherDerived =>
      show (match lastDnr dnr rest with
            | some r => some r
            | none => none) = none ↔ dnrFree dnr rest = true
      cases hl : lastDnr dnr rest with
      | some r =>
        have hf : dnrFree dnr rest = false := by
          cases hfr : dnrFree dnr rest with
          | false => rfl
          | true => rw [ih.mpr hfr] at hl; exact nomatch hl
        rw [hf]
        exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
      | none => exact ⟨fun _ => ih.mp hl, fun _ => rfl⟩

theorem lastDnr_some_rest_free (dnr : ι → Bool) (chain : List (Cause π ι))
    (p : π) (r : List (Cause π ι)) (h : lastDnr dnr chain = some (p, r)) :
    dnrFree dnr r = true := by
  induction chain with
  | nil => exact nomatch h
  | cons c rest ih =>
    cases hl : lastDnr dnr rest with
    | some q =>
      have hq : lastDnr dnr (c :: rest) = some q := by
        show (match lastDnr dnr rest with
              | some r => some r
              | none => _) = some q
        rw [hl]
      rw [hq] at h
      have hqe : q = (p, r) := Option.some.inj h
      rw [hqe] at hl
      exact ih hl
    | none =>
      cases c with
      | implDerived impl parent =>
        have hc : lastDnr dnr (Cause.implDerived impl parent :: rest)
            = (if dnr impl then some (parent, rest) else none) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => if dnr impl then some (parent, rest) else none) = _
          rw [hl]
        rw [hc] at h
        cases hd : dnr impl with
        | true =>
          rw [hd] at h
          have he : (parent, rest) = (p, r) := Option.some.inj h
          have hr : rest = r := congrArg Prod.snd he
          rw [← hr]
          exact (lastDnr_none_iff dnr rest).mp hl
        | false => rw [hd] at h; exact nomatch h
      | otherDerived =>
        have hc : lastDnr dnr (Cause.otherDerived :: rest) = (none : Option (π × List (Cause π ι))) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => none) = _
          rw [hl]
        rw [hc] at h
        exact nomatch h

/-- **Pruning is complete.**  The reported cause chain never mentions a marked impl. -/
theorem report_chain_dnrFree (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι)) :
    dnrFree dnr (report dnr leaf chain).2 = true := by
  rw [report_eq]
  cases hl : lastDnr dnr chain with
  | none => exact (lastDnr_none_iff dnr chain).mp hl
  | some q =>
    cases q with
    | mk p r => exact lastDnr_some_rest_free dnr chain p r hl

/-- Without marked impls the report is the original obligation. -/
theorem report_unchanged_of_dnrFree (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι))
    (h : dnrFree dnr chain = true) : report dnr leaf chain = (leaf, chain) := by
  rw [report_eq, (lastDnr_none_iff dnr chain).mpr h]
  rfl

/-- **Idempotence.**  Applying the pruning to its own output changes nothing. -/
theorem report_idempotent (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι)) :
    report dnr (report dnr leaf chain).1 (report dnr leaf chain).2 = report dnr leaf chain :=
  report_unchanged_of_dnrFree dnr _ _ (report_chain_dnrFree dnr leaf chain)

/-- The proof-tree walk of the next-generation solver, root → leaf: stop at the first
goal whose candidate is a marked impl and report that goal. -/
def firstDnrFromRoot (dnr : ι → Bool) : List (Cause π ι) → Option π
  | [] => none
  | .implDerived impl parent :: rest =>
    if dnr impl then some parent else firstDnrFromRoot dnr rest
  | .otherDerived :: rest => firstDnrFromRoot dnr rest

def headDnr (dnr : ι → Bool) : Cause π ι → Option π
  | .implDerived impl parent => if dnr impl then some parent else none
  | .otherDerived => none

theorem firstDnrFromRoot_append_single (dnr : ι → Bool) (l : List (Cause π ι)) (c : Cause π ι) :
    firstDnrFromRoot dnr (l ++ [c]) = firstWins (firstDnrFromRoot dnr l) (headDnr dnr c) := by
  induction l with
  | nil =>
    cases c with
    | implDerived impl parent =>
      show (if dnr impl then some parent else none)
        = firstWins none (if dnr impl then some parent else none)
      cases dnr impl <;> rfl
    | otherDerived => rfl
  | cons d l ih =>
    cases d with
    | implDerived impl parent =>
      show (if dnr impl then some parent else firstDnrFromRoot dnr (l ++ [c]))
        = firstWins (if dnr impl then some parent else firstDnrFromRoot dnr l) (headDnr dnr c)
      cases dnr impl with
      | true => rfl
      | false => exact ih
    | otherDerived => exact ih

theorem lastDnr_fst_eq_firstFromRoot (dnr : ι → Bool) (chain : List (Cause π ι)) :
    (lastDnr dnr chain).map Prod.fst = firstDnrFromRoot dnr chain.reverse := by
  induction chain with
  | nil => rfl
  | cons c rest ih =>
    rw [List.reverse_cons, firstDnrFromRoot_append_single, ← ih]
    cases hl : lastDnr dnr rest with
    | some r =>
      have : lastDnr dnr (c :: rest) = some r := by
        show (match lastDnr dnr rest with
              | some r => some r
              | none => _) = some r
        rw [hl]
      rw [this]; rfl
    | none =>
      cases c with
      | implDerived impl parent =>
        have : lastDnr dnr (Cause.implDerived impl parent :: rest)
            = (if dnr impl then some (parent, rest) else none) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => if dnr impl then some (parent, rest) else none) = _
          rw [hl]
        rw [this]
        show Option.map Prod.fst (if dnr impl then some (parent, rest) else none)
          = firstWins none (if dnr impl then some parent else none)
        cases dnr impl <;> rfl
      | otherDerived =>
        have : lastDnr dnr (Cause.otherDerived :: rest) = (none : Option (π × List (Cause π ι))) := by
          show (match lastDnr dnr rest with
                | some r => some r
                | none => none) = _
          rw [hl]
        rw [this]; rfl

/-- **The two solvers agree on the reported predicate**: the bottom-up overwrite loop
and the top-down first-hit walk select the same goal. -/
theorem report_pred_eq_topDown (dnr : ι → Bool) (leaf : π) (chain : List (Cause π ι)) :
    (report dnr leaf chain).1 = (firstDnrFromRoot dnr chain.reverse).getD leaf := by
  rw [report_eq, ← lastDnr_fst_eq_firstFromRoot]
  cases lastDnr dnr chain <;> rfl

end DoNotRecommend

/-! ### The two-impl chain used by the probe

`impl<T: A> B for T` (impl `ab`) and `impl<T: B> C for T` (impl `bc`); the failing leaf is
`u8: A`, the root obligation is `u8: C`. -/

inductive Pred where
  | u8A | u8B | u8C
  deriving DecidableEq, Repr

inductive Impl where
  | ab | bc
  deriving DecidableEq, Repr

def probeChain : List (Cause Pred Impl) := [.implDerived .ab .u8B, .implDerived .bc .u8C]

def markNone : Impl → Bool := fun _ => false
def markInner : Impl → Bool := fun i => decide (i = .ab)
def markOuter : Impl → Bool := fun i => decide (i = .bc)
def markBoth : Impl → Bool := fun _ => true

/-- The four attribute placements give the leaf predicates `A`, `B`, `C`, `C` and the
"required for" chains of length 2, 1, 0, 0. -/
theorem probe_chain_reports :
    (report markNone .u8A probeChain).1 = .u8A ∧ (report markNone .u8A probeChain).2.length = 2 ∧
    (report markInner .u8A probeChain).1 = .u8B ∧ (report markInner .u8A probeChain).2.length = 1 ∧
    (report markOuter .u8A probeChain).1 = .u8C ∧ (report markOuter .u8A probeChain).2.length = 0 ∧
    (report markBoth .u8A probeChain).1 = .u8C ∧ (report markBoth .u8A probeChain).2.length = 0 := by
  decide

end CfgModel

/-! ## Axiom audit (every theorem of this file) -/

#print axioms CfgModel.memB_append
#print axioms CfgModel.ExpectedValues.Equiv.refl
#print axioms CfgModel.ExpectedValues.Equiv.symm
#print axioms CfgModel.ExpectedValues.Equiv.trans
#print axioms CfgModel.ExpectedValues.isAny_join
#print axioms CfgModel.ExpectedValues.accepts_join
#print axioms CfgModel.ExpectedValues.join_assoc
#print axioms CfgModel.ExpectedValues.join_comm
#print axioms CfgModel.ExpectedValues.join_idem
#print axioms CfgModel.ExpectedValues.join_any_left
#print axioms CfgModel.ExpectedValues.join_any_right
#print axioms CfgModel.ExpectedValues.join_bot_left
#print axioms CfgModel.ExpectedValues.join_bot_right
#print axioms CfgModel.ExpectedValues.join_congr
#print axioms CfgModel.ExpectedValues.bot_le
#print axioms CfgModel.ExpectedValues.le_any
#print axioms CfgModel.ExpectedValues.le_refl
#print axioms CfgModel.ExpectedValues.le_antisymm
#print axioms CfgModel.ExpectedValues.le_join_left
#print axioms CfgModel.ExpectedValues.any_ne_some
#print axioms CfgModel.mergeEntry_none
#print axioms CfgModel.mergeEntry_some
#print axioms CfgModel.lint_eq_obs
#print axioms CfgModel.present_insertName
#print axioms CfgModel.okAt_insertName
#print axioms CfgModel.present_foldl_insertName
#print axioms CfgModel.okAt_foldl_insertName
#print axioms CfgModel.present_applySpec
#print axioms CfgModel.okAt_applySpec
#print axioms CfgModel.exhaustive_applySpec
#print axioms CfgModel.present_foldl_applySpec
#print axioms CfgModel.okAt_foldl_applySpec
#print axioms CfgModel.exhaustive_foldl_applySpec
#print axioms CfgModel.any_perm
#print axioms CfgModel.isEmpty_perm
#print axioms CfgModel.lint_parse
#print axioms CfgModel.checkCfg_fold_perm_invariant
#print axioms CfgModel.checkCfg_duplicate_spec
#print axioms CfgModel.present_fillOne
#print axioms CfgModel.okAt_fillOne
#print axioms CfgModel.obsEq_fillOne
#print axioms CfgModel.obsEq_foldl_fillOne
#print axioms CfgModel.lint_congr
#print axioms CfgModel.obsEq_parse_of_perm
#print axioms CfgModel.exhaustive_parse_of_perm
#print axioms CfgModel.checkConfig_perm_invariant
#print axioms CfgModel.only_alpha_rejects_beta_and_bare
#print axioms CfgModel.any_absorbs_both_orders
#print axioms CfgModel.no_specs_no_lint
#print axioms CfgModel.ce_wellKnown_fill_shadows_bare_form
#print axioms CfgModel.wellKnown_fill_unions_valued_names
#print axioms CfgModel.disallow_nil_iff
#print axioms CfgModel.coherentSession_iff_no_spoofed_builtin_cfg
#print axioms CfgModel.disallow_empty_implies_coherent
#print axioms CfgModel.ubChecks_coherent_of_gate
#print axioms CfgModel.accepted_at_deny_implies_coherent
#print axioms CfgModel.ce1_spoofed_cli_ub_checks_diverges_from_codegen
#print axioms CfgModel.gate_strictly_conservative
#print axioms CfgModel.test_cfg_is_exempt
#print axioms CfgModel.ce_gate_gap_bare_target_has_atomic
#print axioms CfgModel.immediate_abort_sets_both_panic_cfgs
#print axioms CfgModel.panic_abort_cfg_not_injective
#print axioms CfgModel.kernel_sanitizers_fold
#print axioms CfgModel.i686_model_matches_print_cfg
#print axioms CfgModel.x86_64_linux_model_matches_print_cfg
#print axioms CfgModel.thumbv6m_model_matches_print_cfg
#print axioms CfgModel.m68k_model_matches_print_cfg
#print axioms CfgModel.ce2_i686_atomic64_has_cas_without_primitive_align
#print axioms CfgModel.m68k_ptr_cas_without_primitive_align
#print axioms CfgModel.load_store_without_cas
#print axioms CfgModel.ce3_x86_64_linux_cx16_still_lacks_atomic128_due_to_static_target_max
#print axioms CfgModel.atomicCfgs_ignores_target_features
#print axioms CfgModel.per_cpu_table_changes_atomic_cfgs
#print axioms CfgModel.bare_entries_are_nightly_only
#print axioms CfgModel.firstWins_eq_or
#print axioms CfgModel.firstWins_assoc
#print axioms CfgModel.firstWins_none_right
#print axioms CfgModel.firstWins_idem
#print axioms CfgModel.directiveMerge_assoc
#print axioms CfgModel.directiveMerge_empty_left
#print axioms CfgModel.directiveMerge_empty_right
#print axioms CfgModel.ce_directiveMerge_noncomm
#print axioms CfgModel.ce_directiveMerge_not_idempotent
#print axioms CfgModel.foldl_mergeInto_some
#print axioms CfgModel.foldl_mergeInto
#print axioms CfgModel.foldl_merge_message
#print axioms CfgModel.foldl_merge_label
#print axioms CfgModel.foldl_merge_notes
#print axioms CfgModel.mergeAll_spec
#print axioms CfgModel.map_firstWins
#print axioms CfgModel.update_render_eq_render_merge
#print axioms CfgModel.render_empty
#print axioms CfgModel.foldl_update_render
#print axioms CfgModel.eval_sequence_eq_render_mergeAll
#print axioms CfgModel.applyDnr_eq
#print axioms CfgModel.report_eq
#print axioms CfgModel.lastDnr_none_iff
#print axioms CfgModel.lastDnr_some_rest_free
#print axioms CfgModel.report_chain_dnrFree
#print axioms CfgModel.report_unchanged_of_dnrFree
#print axioms CfgModel.report_idempotent
#print axioms CfgModel.firstDnrFromRoot_append_single
#print axioms CfgModel.lastDnr_fst_eq_firstFromRoot
#print axioms CfgModel.report_pred_eq_topDown
#print axioms CfgModel.probe_chain_reports
