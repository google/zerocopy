/-!
# Lint-level ceiling, `forbid`, the external-macro filter, and a post-expansion audit

A self-contained model (Lean core only, no imports) of four pieces of `rustc`
as read at `rust-lang/rust` commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`:

* `rustc_lint_defs::Level` and `rustc_middle::lint::reveal_actual_level_spec`
  (default level, the `warnings` group, `--cap-lints`, driver caps);
* `rustc_session::config::get_cmd_lint_options` and
  `LintLevelsBuilder::{add_command_line, insert_spec}` in
  `rustc_lint/src/levels.rs` (command-line levels, nested attributes, E0453);
* `SyntaxContext::in_external_macro` in `rustc_span/src/hygiene.rs` and the
  filter in `rustc_middle::lint::emit_lint_base`;
* the `UNSAFE_CODE` early lint pass on `unsafe` blocks, followed by a
  context-insensitive unsafety check and a lowering that erases spans.

Everything proved here is a statement about this model.  How each definition
follows the compiler source, and which compiler behaviours were also observed
by execution, is recorded in the accompanying report.

Modelling choices that narrow the model relative to the compiler:

* one lint at a time; lint groups other than `warnings` are absent, so the
  future-compatibility downgrade for `forbid(<group>)` is not represented;
* the builder runs with `lint_added_lints = true` (the post-expansion pass);
* nested attributes never change the `warnings` level;
* expectation identifiers are not represented: an `expect`-level emission is a
  distinct silent outcome, nothing more;
* programs are trees of safe operations, unsafe operations, `unsafe` blocks and
  lint-level attributes inside one safe function.

Every definition is marked `noncomputable`: nothing here is meant to be run,
all reasoning is by kernel reduction, and the modifier keeps the compiler from
generating executable helper copies of the recursive definitions, so that the
environment contains only kernel-checked constants.
-/

namespace LintCap

/-! ## 1. Levels -/

/-- `rustc_lint_defs::Level`; the derived `Ord` follows declaration order. -/
inductive LintLevel where
  | allow | expect | warn | forceWarn | deny | forbid
  deriving DecidableEq

namespace LintLevel

/-- Position in the declaration order. -/
noncomputable def rank : LintLevel → Nat
  | allow => 0
  | expect => 1
  | warn => 2
  | forceWarn => 3
  | deny => 4
  | forbid => 5

noncomputable instance : LE LintLevel := ⟨fun a b => a.rank ≤ b.rank⟩
noncomputable instance : LT LintLevel := ⟨fun a b => a.rank < b.rank⟩
noncomputable instance decLe (a b : LintLevel) : Decidable (a ≤ b) := Nat.decLe a.rank b.rank
noncomputable instance decLt (a b : LintLevel) : Decidable (a < b) := Nat.decLt a.rank b.rank

/-- `std::cmp::min` on levels. -/
noncomputable def min (a b : LintLevel) : LintLevel := if a ≤ b then a else b

theorem strict_chain :
    allow < expect ∧ expect < warn ∧ warn < forceWarn ∧ forceWarn < deny ∧ deny < forbid := by
  decide

theorem rank_injective {a b : LintLevel} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem le_refl (a : LintLevel) : a ≤ a := Nat.le_refl a.rank

theorem le_trans {a b c : LintLevel} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  Nat.le_trans hab hbc

theorem le_antisymm {a b : LintLevel} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  rank_injective (Nat.le_antisymm hab hba)

theorem le_total (a b : LintLevel) : a ≤ b ∨ b ≤ a := Nat.le_total a.rank b.rank

theorem allow_le (a : LintLevel) : allow ≤ a := Nat.zero_le a.rank

theorem le_forbid (a : LintLevel) : a ≤ forbid := by cases a <;> decide

theorem min_le_left (a b : LintLevel) : min a b ≤ a := by cases a <;> cases b <;> decide

theorem min_le_right (a b : LintLevel) : min a b ≤ b := by cases a <;> cases b <;> decide

/-- `min` is the greatest lower bound. -/
theorem le_min {a b c : LintLevel} (hca : c ≤ a) (hcb : c ≤ b) : c ≤ min a b := by
  unfold min
  split
  · exact hca
  · exact hcb

theorem min_comm (a b : LintLevel) : min a b = min b a := by cases a <;> cases b <;> decide

theorem min_assoc (a b c : LintLevel) : min (min a b) c = min a (min b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem min_self (a : LintLevel) : min a a = a := by cases a <;> decide

/-- `lint_cap.unwrap_or(Level::Forbid)` leaves a level unchanged when no cap is set. -/
theorem min_forbid (a : LintLevel) : min a forbid = a := by cases a <;> decide

theorem min_allow (a : LintLevel) : min a allow = allow := by cases a <;> decide

theorem allow_min (a : LintLevel) : min allow a = allow := by cases a <;> decide

theorem min_eq_forbid {a b : LintLevel} (h : min a b = forbid) : a = forbid ∧ b = forbid := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

end LintLevel

/-! ## 2. Level sources, sessions and `reveal_actual_level_spec` -/

/-- `rustc_middle::lint::LintLevelSource`, without names and spans. -/
inductive LevelSource where
  | default
  | node
  | commandLine (flag : LintLevel)
  deriving DecidableEq

/-- `matches!(src, LintLevelSource::CommandLine(_, Level::ForceWarn))`. -/
noncomputable def LevelSource.isCliForceWarn : LevelSource → Bool
  | .commandLine .forceWarn => true
  | _ => false

/-- `rustc_middle::lint::LevelSpec` without the expectation identifier. -/
structure LevelSpec where
  level : LintLevel
  src : LevelSource
  deriving DecidableEq

/-- The fields of `rustc_lint_defs::Lint` that the modelled functions read. -/
structure LintInfo where
  /-- `lint.default_level(edition)` -/
  defaultLevel : LintLevel
  ignoreDenyWarnings : Bool
  reportInExternalMacro : Bool
  /-- `future_incompatible.is_some_and(|f| f.reason.edition().is_none())` -/
  hardFutureIncompat : Bool

/-- `UNSAFE_CODE`: declared `Allow`, every other field at its macro default. -/
noncomputable def unsafeCode : LintInfo := ⟨.allow, false, false, false⟩

/-- `UNFULFILLED_LINT_EXPECTATIONS`: declared `Warn`. -/
noncomputable def unfulfilledLintExpectations : LintInfo := ⟨.warn, false, false, false⟩

/-- The session state read by `reveal_actual_level_spec` for one lint. -/
structure Session where
  /-- `sess.opts.lint_cap` -/
  lintCap : Option LintLevel
  /-- `sess.driver_lint_caps.get(&lint)` -/
  driverCap : Option LintLevel
  /-- what `probe_for_lint_level_spec(WARNINGS)` returns -/
  warnings : Option LevelSpec

/-- The `match configured_level_spec.level` table for the `warnings` group. -/
noncomputable def respectWarningsGroup (lint : LintInfo) : LintLevel → Bool
  | .warn => false
  | .deny => !lint.ignoreDenyWarnings
  | .forbid => !lint.ignoreDenyWarnings
  | .allow => true
  | .expect => true
  | .forceWarn => false

theorem respectWarningsGroup_forceWarn (lint : LintInfo) :
    respectWarningsGroup lint .forceWarn = false := rfl

/-- "If we're about to issue a warning, check ... the `warnings` lint group." -/
noncomputable def applyWarningsGroup (lint : LintInfo) (warnings : Option LevelSpec) (s : LevelSpec) :
    LevelSpec :=
  match warnings with
  | none => s
  | some w => if s.level = .warn ∧ respectWarningsGroup lint w.level = true then w else s

/-- "Ensure that we never exceed the `--cap-lints` argument unless the source
is a --force-warn". -/
noncomputable def applyCap (cap : Option LintLevel) (s : LevelSpec) : LevelSpec :=
  match s.src.isCliForceWarn with
  | true => s
  | false => { s with level := LintLevel.min s.level (cap.getD .forbid) }

/-- "Ensure that we never exceed driver level." -/
noncomputable def applyDriverCap (driverCap : Option LintLevel) (s : LevelSpec) : LevelSpec :=
  match driverCap with
  | some d => { s with level := LintLevel.min s.level d }
  | none => s

/-- `reveal_actual_level_spec`: `probe` is the raw spec found by walking the
attribute scopes outwards to the command line, if any. -/
noncomputable def revealActualLevelSpec (sess : Session) (lint : LintInfo) (probe : Option LevelSpec) :
    LevelSpec :=
  applyDriverCap sess.driverCap
    (applyCap sess.lintCap
      (applyWarningsGroup lint sess.warnings (probe.getD ⟨lint.defaultLevel, .default⟩)))

/-- No spec here was produced by a command-line `--force-warn`. -/
noncomputable def NotCliForceWarn (s : Option LevelSpec) : Prop :=
  ∀ x, s = some x → x.src.isCliForceWarn = false

theorem notCliForceWarn_none : NotCliForceWarn none := fun _ h => nomatch h

theorem notCliForceWarn_node (l : LintLevel) : NotCliForceWarn (some ⟨l, .node⟩) := by
  intro x h
  cases h
  rfl

theorem applyWarningsGroup_src (lint : LintInfo) (warnings : Option LevelSpec) (s : LevelSpec)
    (hs : s.src.isCliForceWarn = false) (hw : NotCliForceWarn warnings) :
    (applyWarningsGroup lint warnings s).src.isCliForceWarn = false := by
  cases warnings with
  | none => exact hs
  | some w =>
    show (if s.level = .warn ∧ respectWarningsGroup lint w.level = true then w else s).src.isCliForceWarn
      = false
    split
    · exact hw w rfl
    · exact hs

theorem getD_default_src (lint : LintInfo) (probe : Option LevelSpec)
    (hp : NotCliForceWarn probe) :
    (probe.getD ⟨lint.defaultLevel, .default⟩).src.isCliForceWarn = false := by
  cases probe with
  | none => rfl
  | some x => exact hp x rfl

theorem applyCap_of_not_fw (cap : Option LintLevel) (s : LevelSpec)
    (hs : s.src.isCliForceWarn = false) :
    applyCap cap s = { s with level := LintLevel.min s.level (cap.getD .forbid) } := by
  unfold applyCap
  rw [hs]

theorem applyDriverCap_le_left (d : Option LintLevel) (s : LevelSpec) :
    (applyDriverCap d s).level ≤ s.level := by
  cases d with
  | none => exact LintLevel.le_refl s.level
  | some d => exact LintLevel.min_le_left s.level d

/-- **Ceiling.** Unless the effective source is a command-line `--force-warn`,
the revealed level never exceeds the `--cap-lints` level. -/
theorem reveal_le_lintCap (sess : Session) (lint : LintInfo) (probe : Option LevelSpec)
    (cap : LintLevel) (hcap : sess.lintCap = some cap)
    (hp : NotCliForceWarn probe) (hw : NotCliForceWarn sess.warnings) :
    (revealActualLevelSpec sess lint probe).level ≤ cap := by
  unfold revealActualLevelSpec
  have hsrc := applyWarningsGroup_src lint sess.warnings _ (getD_default_src lint probe hp) hw
  rw [applyCap_of_not_fw _ _ hsrc, hcap]
  exact LintLevel.le_trans (applyDriverCap_le_left _ _) (LintLevel.min_le_right _ cap)

/-- The driver cap binds every source, including `--force-warn`. -/
theorem reveal_le_driverCap (sess : Session) (lint : LintInfo) (probe : Option LevelSpec)
    (d : LintLevel) (hd : sess.driverCap = some d) :
    (revealActualLevelSpec sess lint probe).level ≤ d := by
  unfold revealActualLevelSpec
  rw [hd]
  exact LintLevel.min_le_right _ d

/-- With `--cap-lints allow`, every level that is not a command-line
`--force-warn` is revealed as `allow`. -/
theorem reveal_allow_of_cap_allow (sess : Session) (lint : LintInfo) (probe : Option LevelSpec)
    (hcap : sess.lintCap = some .allow)
    (hp : NotCliForceWarn probe) (hw : NotCliForceWarn sess.warnings) :
    (revealActualLevelSpec sess lint probe).level = .allow :=
  LintLevel.le_antisymm (reveal_le_lintCap sess lint probe .allow hcap hp hw)
    (LintLevel.allow_le _)

/-- No `--cap-lints` below `forbid` and no driver cap below `forbid`. -/
noncomputable def Uncapped (sess : Session) : Prop :=
  sess.lintCap.getD .forbid = .forbid ∧ sess.driverCap.getD .forbid = .forbid

theorem applyDriverCap_uncapped (d : Option LintLevel) (s : LevelSpec)
    (h : d.getD .forbid = .forbid) : applyDriverCap d s = s := by
  cases d with
  | none => rfl
  | some d =>
    have hd : d = .forbid := h
    subst hd
    show ({ s with level := LintLevel.min s.level .forbid } : LevelSpec) = s
    rw [LintLevel.min_forbid]

theorem applyCap_uncapped (cap : Option LintLevel) (s : LevelSpec)
    (h : cap.getD .forbid = .forbid) : applyCap cap s = s := by
  unfold applyCap
  split
  · rfl
  · rw [h, LintLevel.min_forbid]

/-- Without caps, revealing only applies the `warnings` group. -/
theorem reveal_uncapped (sess : Session) (lint : LintInfo) (probe : Option LevelSpec)
    (h : Uncapped sess) :
    revealActualLevelSpec sess lint probe =
      applyWarningsGroup lint sess.warnings (probe.getD ⟨lint.defaultLevel, .default⟩) := by
  unfold revealActualLevelSpec
  rw [applyCap_uncapped _ _ h.1, applyDriverCap_uncapped _ _ h.2]

theorem applyWarningsGroup_of_ne_warn (lint : LintInfo) (warnings : Option LevelSpec)
    (s : LevelSpec) (hs : s.level ≠ .warn) : applyWarningsGroup lint warnings s = s := by
  cases warnings with
  | none => rfl
  | some w =>
    show (if s.level = .warn ∧ respectWarningsGroup lint w.level = true then w else s) = s
    split
    · next hc => exact absurd hc.1 hs
    · rfl

/-- An attribute-set `forbid` is revealed as `forbid` when nothing caps it. -/
theorem reveal_node_forbid (sess : Session) (lint : LintInfo) (h : Uncapped sess) :
    (revealActualLevelSpec sess lint (some ⟨.forbid, .node⟩)).level = .forbid := by
  rw [reveal_uncapped sess lint _ h]
  show (applyWarningsGroup lint sess.warnings ⟨.forbid, .node⟩).level = .forbid
  rw [applyWarningsGroup_of_ne_warn lint sess.warnings ⟨.forbid, .node⟩ (by decide)]

theorem applyWarningsGroup_ne_forceWarn (lint : LintInfo) (warnings : Option LevelSpec)
    (s : LevelSpec) (hs : s.level ≠ .forceWarn) :
    (applyWarningsGroup lint warnings s).level ≠ .forceWarn := by
  cases warnings with
  | none => exact hs
  | some w =>
    show (if s.level = .warn ∧ respectWarningsGroup lint w.level = true then w else s).level
      ≠ .forceWarn
    split
    · next hc =>
      intro hw
      have hr := hc.2
      rw [hw, respectWarningsGroup_forceWarn] at hr
      exact absurd hr (by decide)
    · exact hs

/-! ## 3. Command line: `get_cmd_lint_options` and `add_command_line` -/

/-- What a level flag names, from the point of view of one lint. -/
inductive LintTarget where
  | thisLint | warningsGroup | otherLint
  deriving DecidableEq

/-- Command-line arguments relevant to lint levels. `level l t` stands for
`-A`/`-W`/`--force-warn`/`-D`/`-F <name>`. -/
inductive CliArg where
  | level (lvl : LintLevel) (target : LintTarget)
  | capLints (lvl : LintLevel)
  | other
  deriving DecidableEq

/-- `lint_opts`: the level flags in argument order. -/
noncomputable def lintOpts : List CliArg → List (LintLevel × LintTarget)
  | [] => []
  | .level lvl t :: rest => (lvl, t) :: lintOpts rest
  | .capLints _ :: rest => lintOpts rest
  | .other :: rest => lintOpts rest

/-- `matches.opt_str("cap-lints")`: the first occurrence, wherever it is. -/
noncomputable def lintCapOf : List CliArg → Option LintLevel
  | [] => none
  | .capLints lvl :: _ => some lvl
  | .level _ _ :: rest => lintCapOf rest
  | .other :: rest => lintCapOf rest

theorem lintOpts_append_cap (pre post : List CliArg) (c : LintLevel) :
    lintOpts (pre ++ .capLints c :: post) = lintOpts (pre ++ post) := by
  induction pre with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | level lvl t => show (lvl, t) :: lintOpts (rest ++ .capLints c :: post) = _; rw [ih]; rfl
    | capLints l => exact ih
    | other => exact ih

theorem lintCapOf_append_cap (pre post : List CliArg) (c : LintLevel)
    (hpre : lintCapOf pre = none) : lintCapOf (pre ++ .capLints c :: post) = some c := by
  induction pre with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | level lvl t => exact ih hpre
    | capLints l => exact nomatch hpre
    | other => exact ih hpre

/-- **Flag order.** The cap that is read, and the level flags that are read,
do not depend on where the (first) `--cap-lints` sits among the other flags. -/
theorem cap_flag_position_irrelevant (pre post : List CliArg) (c : LintLevel)
    (hpre : lintCapOf pre = none) :
    (lintOpts (pre ++ .capLints c :: post), lintCapOf (pre ++ .capLints c :: post)) =
      (lintOpts (.capLints c :: (pre ++ post)), lintCapOf (.capLints c :: (pre ++ post))) := by
  rw [lintOpts_append_cap, lintCapOf_append_cap pre post c hpre]
  rfl

/-- One iteration of the loop in `add_command_line` for a flag naming the lint:
"ForceWarn and Forbid cannot be overridden". -/
noncomputable def addCommandLineStep (cur : Option LevelSpec) (lvl : LintLevel) : Option LevelSpec :=
  match cur with
  | some ⟨.forceWarn, src⟩ => some ⟨.forceWarn, src⟩
  | some ⟨.forbid, src⟩ => some ⟨.forbid, src⟩
  | _ => some ⟨lvl, .commandLine lvl⟩

/-- `add_command_line` restricted to the flags that name `target`. -/
noncomputable def addCommandLineFrom (target : LintTarget) (cur : Option LevelSpec) :
    List (LintLevel × LintTarget) → Option LevelSpec
  | [] => cur
  | (lvl, t) :: rest =>
    addCommandLineFrom target (if t = target then addCommandLineStep cur lvl else cur) rest

noncomputable def addCommandLine (target : LintTarget) (opts : List (LintLevel × LintTarget)) :
    Option LevelSpec :=
  addCommandLineFrom target none opts

/-- Session derived from the command line alone (no driver cap; the `warnings`
level comes only from flags). -/
noncomputable def sessionOf (args : List CliArg) : Session :=
  { lintCap := lintCapOf args
    driverCap := none
    warnings := addCommandLine .warningsGroup (lintOpts args) }

/-- The raw command-line spec for the lint. -/
noncomputable def cliSpec (args : List CliArg) : Option LevelSpec :=
  addCommandLine .thisLint (lintOpts args)

/-- No level flag is a `--force-warn`. -/
noncomputable def NoForceWarnFlag (args : List CliArg) : Prop :=
  ∀ t, CliArg.level .forceWarn t ∉ args

/-- Every spec here has a level other than `forceWarn`. -/
noncomputable def LevelNotForceWarn (s : Option LevelSpec) : Prop :=
  ∀ x, s = some x → x.level ≠ .forceWarn

theorem addCommandLineStep_notCliForceWarn (cur : Option LevelSpec) (lvl : LintLevel)
    (hcur : NotCliForceWarn cur) (hl : lvl ≠ .forceWarn) :
    NotCliForceWarn (addCommandLineStep cur lvl) := by
  have hnew : NotCliForceWarn (some ⟨lvl, .commandLine lvl⟩) := by
    intro x hx
    cases hx
    cases lvl <;> first | rfl | exact absurd rfl hl
  cases cur with
  | none => exact hnew
  | some s =>
    cases s with
    | mk level src =>
      cases level
      case forceWarn => exact hcur
      case forbid => exact hcur
      all_goals exact hnew

theorem addCommandLineStep_levelNotForceWarn (cur : Option LevelSpec) (lvl : LintLevel)
    (hcur : LevelNotForceWarn cur) (hl : lvl ≠ .forceWarn) :
    LevelNotForceWarn (addCommandLineStep cur lvl) := by
  have hnew : LevelNotForceWarn (some ⟨lvl, .commandLine lvl⟩) := by
    intro x hx
    cases hx
    exact hl
  cases cur with
  | none => exact hnew
  | some s =>
    cases s with
    | mk level src =>
      cases level
      case forceWarn => exact hcur
      case forbid => exact hcur
      all_goals exact hnew

theorem addCommandLineFrom_invariant (P : Option LevelSpec → Prop)
    (hstep : ∀ cur lvl, P cur → lvl ≠ .forceWarn → P (addCommandLineStep cur lvl))
    (target : LintTarget) :
    ∀ (args : List CliArg) (cur : Option LevelSpec), NoForceWarnFlag args → P cur →
      P (addCommandLineFrom target cur (lintOpts args)) := by
  intro args
  induction args with
  | nil => intro cur _ hcur; exact hcur
  | cons a rest ih =>
    intro cur hfw hcur
    have hrest : NoForceWarnFlag rest := fun t hm => hfw t (List.mem_cons_of_mem _ hm)
    cases a with
    | level lvl t =>
      have hl : lvl ≠ .forceWarn := by
        intro h
        subst h
        exact hfw t (List.mem_cons_self ..)
      show P (addCommandLineFrom target
        (if t = target then addCommandLineStep cur lvl else cur) (lintOpts rest))
      apply ih _ hrest
      split
      · exact hstep cur lvl hcur hl
      · exact hcur
    | capLints l => exact ih cur hrest hcur
    | other => exact ih cur hrest hcur

theorem cli_notCliForceWarn (target : LintTarget) (args : List CliArg)
    (hfw : NoForceWarnFlag args) :
    NotCliForceWarn (addCommandLine target (lintOpts args)) :=
  addCommandLineFrom_invariant NotCliForceWarn addCommandLineStep_notCliForceWarn target args none
    hfw notCliForceWarn_none

theorem cli_levelNotForceWarn (target : LintTarget) (args : List CliArg)
    (hfw : NoForceWarnFlag args) :
    LevelNotForceWarn (addCommandLine target (lintOpts args)) :=
  addCommandLineFrom_invariant LevelNotForceWarn addCommandLineStep_levelNotForceWarn target args
    none hfw (fun _ h => nomatch h)

/-! ## 4. Nested attributes: `insert_spec` and E0453 -/

/-- What `insert_spec` did with one lint-level attribute. -/
inductive AttrOutcome where
  | accepted
  | denyInsideForbidIgnored
  | overruledE0453
  deriving DecidableEq

/-- `insert_spec`, following the source's control flow, given the revealed spec
`old` of the enclosing scope and the attribute's level. `raw` is returned
unchanged where the source returns without inserting. -/
noncomputable def insertSpecLiteral (raw : Option LevelSpec) (old : LevelSpec) (level : LintLevel) :
    Option LevelSpec × AttrOutcome :=
  if level = .deny ∧ old.level = .forbid then
    (raw, .denyInsideForbidIgnored)
  else if level ≠ .forbid ∧ old.level = .forbid then
    (raw, .overruledE0453)
  else
    match old.level with
    | .forceWarn => (some ⟨.forceWarn, old.src⟩, .accepted)
    | _ => (some ⟨level, .node⟩, .accepted)

/-- The same function as a decision table on (old level, attribute level). -/
noncomputable def insertSpecTable (raw : Option LevelSpec) (old : LevelSpec) (level : LintLevel) :
    Option LevelSpec × AttrOutcome :=
  match old.level, level with
  | .forbid, .deny => (raw, .denyInsideForbidIgnored)
  | .forbid, .forbid => (some ⟨.forbid, .node⟩, .accepted)
  | .forbid, _ => (raw, .overruledE0453)
  | .forceWarn, _ => (some ⟨.forceWarn, old.src⟩, .accepted)
  | _, lvl => (some ⟨lvl, .node⟩, .accepted)

theorem insertSpecLiteral_eq_table (raw : Option LevelSpec) (old : LevelSpec)
    (level : LintLevel) : insertSpecLiteral raw old level = insertSpecTable raw old level := by
  cases old with
  | mk oldLevel oldSrc => cases oldLevel <;> cases level <;> rfl

/-- `insert_spec` for one attribute naming the lint. -/
noncomputable def insertSpec (sess : Session) (lint : LintInfo) (raw : Option LevelSpec) (level : LintLevel) :
    Option LevelSpec × AttrOutcome :=
  insertSpecLiteral raw (revealActualLevelSpec sess lint raw) level

/-- **`forbid` is sticky when nothing caps it.** An attribute below a revealed
`forbid` is either rejected with E0453 or leaves the revealed level at
`forbid`. -/
theorem insertSpec_of_forbid (sess : Session) (lint : LintInfo) (raw : Option LevelSpec)
    (level : LintLevel) (hunc : Uncapped sess)
    (hold : (revealActualLevelSpec sess lint raw).level = .forbid) :
    (insertSpec sess lint raw level).2 = .overruledE0453 ∨
      (revealActualLevelSpec sess lint (insertSpec sess lint raw level).1).level = .forbid := by
  unfold insertSpec
  rw [insertSpecLiteral_eq_table]
  generalize hrev : revealActualLevelSpec sess lint raw = old at hold
  cases old with
  | mk oldLevel oldSrc =>
    have ho : oldLevel = .forbid := hold
    subst ho
    cases level
    case deny =>
      right
      show (revealActualLevelSpec sess lint raw).level = .forbid
      rw [hrev]
    case forbid =>
      right
      exact reveal_node_forbid sess lint hunc
    all_goals exact Or.inl rfl

/-- With a revealed `allow`, any attribute is simply inserted. -/
theorem insertSpec_of_allow (sess : Session) (lint : LintInfo) (raw : Option LevelSpec)
    (level : LintLevel) (hold : (revealActualLevelSpec sess lint raw).level = .allow) :
    insertSpec sess lint raw level = (some ⟨level, .node⟩, .accepted) := by
  unfold insertSpec
  rw [insertSpecLiteral_eq_table]
  generalize revealActualLevelSpec sess lint raw = old at hold
  cases old with
  | mk oldLevel oldSrc =>
    have ho : oldLevel = .allow := hold
    subst ho
    cases level <;> rfl

/-! ## 5. Span provenance: `in_external_macro` -/

inductive MacroKind where
  | bang | attr | derive
  deriving DecidableEq

/-- `rustc_span::DesugaringKind`; `other` stands for every kind that
`in_external_macro` does not list by name. -/
inductive DesugaringKind where
  | forLoop | whileLoop | opaqueTy | async | await | other
  deriving DecidableEq

/-- `rustc_span::ExpnKind` without names. -/
inductive ExpnKind where
  | root
  | macro (kind : MacroKind)
  | astPass
  | desugaring (kind : DesugaringKind)
  deriving DecidableEq

/-- The fields of `ExpnData` that the lint machinery reads. -/
structure ExpnData where
  kind : ExpnKind
  /-- `expn_data.def_site.is_dummy()` -/
  defSiteDummy : Bool
  /-- `sm.is_imported(expn_data.def_site)` -/
  defSiteImported : Bool
  /-- `expn_data.allow_internal_unsafe` -/
  allowInternalUnsafe : Bool
  deriving DecidableEq

/-- A span's syntax context as the expansions that marked it, the most deeply
nested (`outer_expn`) first. The empty list is the root context. -/
abbrev SyntaxContext := List ExpnData

noncomputable def rootExpnData : ExpnData := ⟨.root, true, false, false⟩

/-- `ctxt.outer_expn_data()` -/
noncomputable def outerExpnData : SyntaxContext → ExpnData
  | [] => rootExpnData
  | e :: _ => e

/-- The `match expn_data.kind` of `SyntaxContext::in_external_macro`. -/
noncomputable def ExpnData.external (e : ExpnData) : Bool :=
  match e.kind with
  | .root => false
  | .desugaring .forLoop => false
  | .desugaring .whileLoop => false
  | .desugaring .opaqueTy => false
  | .desugaring .async => false
  | .desugaring .await => false
  | .desugaring .other => true
  | .astPass => true
  | .macro .bang => e.defSiteDummy || e.defSiteImported
  | .macro .attr => true
  | .macro .derive => true

/-- `Span::in_external_macro` -/
noncomputable def inExternalMacro (ctxt : SyntaxContext) : Bool := (outerExpnData ctxt).external

/-- `Span::allows_unsafe` -/
noncomputable def allowsUnsafe (ctxt : SyntaxContext) : Bool := (outerExpnData ctxt).allowInternalUnsafe

theorem root_not_external : inExternalMacro [] = false := rfl

/-- Only the most deeply nested expansion is consulted. -/
theorem inExternalMacro_cons (e : ExpnData) (callers : SyntaxContext) :
    inExternalMacro (e :: callers) = e.external := rfl

theorem bang_macro_external_iff (e : ExpnData) (hk : e.kind = .macro .bang) :
    e.external = (e.defSiteDummy || e.defSiteImported) := by
  cases e with
  | mk kind d i a =>
    have hk' : kind = .macro .bang := hk
    subst hk'
    rfl

/-- A function-like macro whose definition site is unavailable or comes from
another crate's metadata is external. -/
theorem foreign_bang_macro_external (e : ExpnData) (hk : e.kind = .macro .bang)
    (hd : e.defSiteDummy = true ∨ e.defSiteImported = true) : e.external = true := by
  rw [bang_macro_external_iff e hk]
  cases hd with
  | inl h => rw [h]; rfl
  | inr h => rw [h]; exact Bool.or_true _

/-- A function-like macro defined in the crate being compiled is not external. -/
theorem local_bang_macro_not_external (e : ExpnData) (hk : e.kind = .macro .bang)
    (hd : e.defSiteDummy = false) (hi : e.defSiteImported = false) : e.external = false := by
  rw [bang_macro_external_iff e hk, hd, hi]
  rfl

/-- Attribute and derive macros are external whatever their definition site. -/
theorem attr_or_derive_macro_external (e : ExpnData)
    (hk : e.kind = .macro .attr ∨ e.kind = .macro .derive) : e.external = true := by
  cases e with
  | mk kind d i a =>
    cases hk with
    | inl h => have h' : kind = .macro .attr := h; subst h'; rfl
    | inr h => have h' : kind = .macro .derive := h; subst h'; rfl

/-- `rustc_span::Transparency` -/
inductive Transparency where
  | transparent | semiOpaque | opaque
  deriving DecidableEq

/-- The context of `Span::call_site()` (`transparent`), `Span::mixed_site()`
(`semiOpaque`) and `Span::def_site()` (`opaque`) inside the proc-macro expansion
`e`: `SyntaxContext::root().apply_mark(e, t)`. Every branch of `apply_mark`
ends by allocating a context whose outer expansion is `e`; `callSite` is the
normalised context of the invocation. -/
noncomputable def procMacroSpanCtxt (e : ExpnData) (t : Transparency) (callSite : SyntaxContext) :
    SyntaxContext :=
  match t with
  | .opaque => [e]
  | .semiOpaque => e :: callSite
  | .transparent => e :: callSite

/-- **All three proc-macro span modes have the same provenance.** -/
theorem procMacro_span_modes_agree (e : ExpnData) (t : Transparency) (callSite : SyntaxContext) :
    inExternalMacro (procMacroSpanCtxt e t callSite) = e.external := by
  cases t <;> rfl

theorem foreign_proc_macro_span_external (e : ExpnData) (t : Transparency)
    (callSite : SyntaxContext) (hk : e.kind = .macro .bang)
    (hd : e.defSiteDummy = true ∨ e.defSiteImported = true) :
    inExternalMacro (procMacroSpanCtxt e t callSite) = true := by
  rw [procMacro_span_modes_agree]
  exact foreign_bang_macro_external e hk hd

/-! ## 6. Emission: `emit_lint_base` -/

/-- What `emit_lint_base` produces. -/
inductive Emission where
  | none
  /-- emitted at `Expect` level: silent, fulfils an expectation -/
  | expectation
  | warning
  | forceWarning
  | error
  deriving DecidableEq

/-- "Convert lint level to error level." -/
noncomputable def levelEmission : LintLevel → Emission
  | .allow => .none
  | .expect => .expectation
  | .warn => .warning
  | .forceWarn => .forceWarning
  | .deny => .error
  | .forbid => .error

/-- `emit_lint_base` for a lint without future-breakage reporting: return at
`Allow`; otherwise return early when the primary span is in an external macro
and the lint neither is a hard future incompatibility nor opted in with
`report_in_external_macro`. -/
noncomputable def emitLintBase (lint : LintInfo) (spec : LevelSpec) (spanInExternalMacro : Bool) : Emission :=
  match spec.level with
  | .allow => .none
  | lvl =>
    if (spanInExternalMacro && !lint.hardFutureIncompat && !lint.reportInExternalMacro) = true
    then .none
    else levelEmission lvl

theorem emitLintBase_allow (lint : LintInfo) (spec : LevelSpec) (ext : Bool)
    (h : spec.level = .allow) : emitLintBase lint spec ext = .none := by
  cases spec with
  | mk level src =>
    have h' : level = .allow := h
    subst h'
    rfl

/-- **External-macro filter.** For `unsafe_code`, a span in an external macro
yields no emission at any level, `forbid` and `--force-warn` included. -/
theorem emitLintBase_unsafeCode_external (spec : LevelSpec) :
    emitLintBase unsafeCode spec true = .none := by
  cases spec with
  | mk level src => cases level <;> rfl

theorem emitLintBase_unsafeCode_forbid_local (spec : LevelSpec) (h : spec.level = .forbid) :
    emitLintBase unsafeCode spec false = .error := by
  cases spec with
  | mk level src =>
    have h' : level = .forbid := h
    subst h'
    rfl

/-! ## 7. Programs, the `UNSAFE_CODE` pass, the unsafety check, and lowering -/

/-- A sample of `rustc_mir_build::check_unsafety::UnsafeOpKind`. -/
inductive UnsafeOp where
  | callUnsafeFn | derefRawPtr | useMutStatic | useExternStatic | accessUnionField | inlineAsm
  deriving DecidableEq

/-- The body of one safe function after macro expansion. -/
inductive Expr where
  /-- an operation that needs no unsafe context -/
  | safeOp
  /-- an operation that needs an unsafe context -/
  | unsafeOp (op : UnsafeOp)
  | seq (a b : Expr)
  /-- `unsafe { body }`; `ctxt` is the syntax context of the block's span -/
  | unsafeBlock (ctxt : SyntaxContext) (body : Expr)
  /-- `#[<level>(unsafe_code)] body`, wherever the attribute came from -/
  | withAttr (level : LintLevel) (body : Expr)

/-- A diagnostic of the lint-level builder or of the `UNSAFE_CODE` pass. -/
inductive Diag where
  | e0453
  | unsafeCode (emission : Emission)
  deriving DecidableEq

/-- Does this diagnostic fail the compilation? -/
noncomputable def Diag.isError : Diag → Bool
  | .e0453 => true
  | .unsafeCode .error => true
  | .unsafeCode _ => false

noncomputable def attrDiags : AttrOutcome → List Diag
  | .overruledE0453 => [.e0453]
  | .accepted => []
  | .denyInsideForbidIgnored => []

noncomputable def emissionDiags : Emission → List Diag
  | .none => []
  | e => [.unsafeCode e]

/-- `UnsafeCode::report_unsafe` on a block span. -/
noncomputable def reportUnsafe (sess : Session) (raw : Option LevelSpec) (ctxt : SyntaxContext) : List Diag :=
  match allowsUnsafe ctxt with
  | true => []
  | false =>
    emissionDiags
      (emitLintBase unsafeCode (revealActualLevelSpec sess unsafeCode raw) (inExternalMacro ctxt))

/-- The post-expansion early lint walk for `unsafe_code`. -/
noncomputable def lintWalk (sess : Session) (raw : Option LevelSpec) : Expr → List Diag
  | .safeOp => []
  | .unsafeOp _ => []
  | .seq a b => lintWalk sess raw a ++ lintWalk sess raw b
  | .unsafeBlock ctxt body => reportUnsafe sess raw ctxt ++ lintWalk sess raw body
  | .withAttr level body =>
    attrDiags (insertSpec sess unsafeCode raw level).2 ++
      lintWalk sess (insertSpec sess unsafeCode raw level).1 body

/-- The unsafety check: an unsafe operation outside every `unsafe` block is a
hard error that no lint level influences. -/
noncomputable def unsafeckOk (inUnsafe : Bool) : Expr → Bool
  | .safeOp => true
  | .unsafeOp _ => inUnsafe
  | .seq a b => unsafeckOk inUnsafe a && unsafeckOk inUnsafe b
  | .unsafeBlock _ body => unsafeckOk true body
  | .withAttr _ body => unsafeckOk inUnsafe body

/-- A lowered statement: no block structure, no spans, no lint levels. -/
inductive MirStmt where
  | safe
  | unsafeOp (op : UnsafeOp)
  deriving DecidableEq

noncomputable def MirStmt.isUnsafe : MirStmt → Bool
  | .safe => false
  | .unsafeOp _ => true

/-- Lowering keeps the operations and forgets everything else. -/
noncomputable def lower : Expr → List MirStmt
  | .safeOp => [.safe]
  | .unsafeOp op => [.unsafeOp op]
  | .seq a b => lower a ++ lower b
  | .unsafeBlock _ body => lower body
  | .withAttr _ body => lower body

/-- The post-expansion audit: is there an unsafe operation in the lowered body? -/
noncomputable def hasUnsafeMir (body : List MirStmt) : Bool := body.any MirStmt.isUnsafe

/-- The unsafe operations of a tree, in order. -/
noncomputable def unsafeOps : Expr → List UnsafeOp
  | .safeOp => []
  | .unsafeOp op => [op]
  | .seq a b => unsafeOps a ++ unsafeOps b
  | .unsafeBlock _ body => unsafeOps body
  | .withAttr _ body => unsafeOps body

/-- One crate: command line, crate-root `#![<level>(unsafe_code)]` attributes
in source order, and a body. -/
structure Crate where
  args : List CliArg
  crateAttrs : List LintLevel
  body : Expr

/-- Crate-root attributes scope over the whole body. -/
noncomputable def wrapAttrs : List LintLevel → Expr → Expr
  | [], e => e
  | l :: ls, e => .withAttr l (wrapAttrs ls e)

noncomputable def lintDiags (c : Crate) : List Diag :=
  lintWalk (sessionOf c.args) (cliSpec c.args) (wrapAttrs c.crateAttrs c.body)

/-- The crate compiles: no error from lint levels or `unsafe_code`, and the
unsafety check passes. -/
noncomputable def rustcAccepts (c : Crate) : Bool :=
  !(lintDiags c).any Diag.isError && unsafeckOk false c.body

/-! ### Boolean and list helpers -/

theorem any_append {α : Type} (p : α → Bool) :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).any p = (l₁.any p || l₂.any p)
  | [], _ => rfl
  | x :: xs, l₂ => by
    show (p x || (xs ++ l₂).any p) = ((p x || xs.any p) || l₂.any p)
    rw [any_append p xs l₂, Bool.or_assoc]

theorem or_false_split {x y : Bool} (h : (x || y) = false) : x = false ∧ y = false := by
  cases x <;> cases y <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem and_true_split {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x <;> cases y <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

/-! ## 8. Theorem 1: the cap is a ceiling over every forbid source -/

/-- Under `--cap-lints allow`, without `--force-warn`, the walk emits nothing:
no `unsafe_code` diagnostic at any nesting depth and no E0453. -/
theorem lintWalk_nil_of_cap_allow (sess : Session) (hcap : sess.lintCap = some .allow)
    (hw : NotCliForceWarn sess.warnings) :
    ∀ (e : Expr) (raw : Option LevelSpec), NotCliForceWarn raw → lintWalk sess raw e = [] := by
  intro e
  induction e with
  | safeOp => intro raw _; rfl
  | unsafeOp op => intro raw _; rfl
  | seq a b iha ihb =>
    intro raw hraw
    show lintWalk sess raw a ++ lintWalk sess raw b = []
    rw [iha raw hraw, ihb raw hraw]
    rfl
  | unsafeBlock ctxt body ih =>
    intro raw hraw
    show reportUnsafe sess raw ctxt ++ lintWalk sess raw body = []
    rw [ih raw hraw]
    have hlevel := reveal_allow_of_cap_allow sess unsafeCode raw hcap hraw hw
    have hrep : reportUnsafe sess raw ctxt = [] := by
      unfold reportUnsafe
      split
      · rfl
      · rw [emitLintBase_allow _ _ _ hlevel]
        rfl
    rw [hrep]
    rfl
  | withAttr level body ih =>
    intro raw hraw
    have hlevel := reveal_allow_of_cap_allow sess unsafeCode raw hcap hraw hw
    show attrDiags (insertSpec sess unsafeCode raw level).2 ++
      lintWalk sess (insertSpec sess unsafeCode raw level).1 body = []
    rw [insertSpec_of_allow sess unsafeCode raw level hlevel]
    show ([] : List Diag) ++ lintWalk sess (some ⟨level, .node⟩) body = []
    rw [ih _ (notCliForceWarn_node level)]
    rfl

/-- **Theorem 1 (lint-cap ceiling dominance).** Put `--cap-lints allow`
anywhere among the arguments (before, after or between `-A`, `-W`, `-D`, `-F`
flags, as the first `--cap-lints`), with no `--force-warn` flag. Then for every list of
crate-root attributes on `unsafe_code` (including `forbid`), every `-F
unsafe_code` on the command line and every body, the lint pipeline produces no
diagnostic at all, so compilation succeeds exactly when the unsafety check
does. -/
theorem capLints_allow_silences_forbid_and_cli_F (pre post : List CliArg)
    (crateAttrs : List LintLevel) (body : Expr)
    (hpre : lintCapOf pre = none) (hfw : NoForceWarnFlag (pre ++ post)) :
    lintDiags ⟨pre ++ .capLints .allow :: post, crateAttrs, body⟩ = [] ∧
      rustcAccepts ⟨pre ++ .capLints .allow :: post, crateAttrs, body⟩ =
        unsafeckOk false body := by
  have hcap : (sessionOf (pre ++ .capLints .allow :: post)).lintCap = some .allow :=
    lintCapOf_append_cap pre post .allow hpre
  have hw : NotCliForceWarn (sessionOf (pre ++ .capLints .allow :: post)).warnings := by
    show NotCliForceWarn (addCommandLine .warningsGroup (lintOpts (pre ++ .capLints .allow :: post)))
    rw [lintOpts_append_cap]
    exact cli_notCliForceWarn .warningsGroup (pre ++ post) hfw
  have hraw : NotCliForceWarn (cliSpec (pre ++ .capLints .allow :: post)) := by
    show NotCliForceWarn (addCommandLine .thisLint (lintOpts (pre ++ .capLints .allow :: post)))
    rw [lintOpts_append_cap]
    exact cli_notCliForceWarn .thisLint (pre ++ post) hfw
  have hnil : lintDiags ⟨pre ++ .capLints .allow :: post, crateAttrs, body⟩ = [] :=
    lintWalk_nil_of_cap_allow _ hcap hw _ _ hraw
  refine ⟨hnil, ?_⟩
  unfold rustcAccepts
  rw [hnil]
  rfl

/-! ## 9. Theorem 2: `forbid` is sound for local, uncapped code -/

/-- Every `unsafe` block's span is neither in an external macro nor inside a
macro that allows internal unsafe. -/
noncomputable def AllBlocksLocal : Expr → Prop
  | .safeOp => True
  | .unsafeOp _ => True
  | .seq a b => AllBlocksLocal a ∧ AllBlocksLocal b
  | .unsafeBlock ctxt body =>
    inExternalMacro ctxt = false ∧ allowsUnsafe ctxt = false ∧ AllBlocksLocal body
  | .withAttr _ body => AllBlocksLocal body

noncomputable def NoUnsafeBlock : Expr → Prop
  | .safeOp => True
  | .unsafeOp _ => True
  | .seq a b => NoUnsafeBlock a ∧ NoUnsafeBlock b
  | .unsafeBlock _ _ => False
  | .withAttr _ body => NoUnsafeBlock body

/-- Scope nesting cannot lower an uncapped `forbid`: if the walk reports no
error, the tree contains no local `unsafe` block at any depth. -/
theorem lint_clean_implies_no_block (sess : Session) (hunc : Uncapped sess) :
    ∀ (e : Expr) (raw : Option LevelSpec),
      (revealActualLevelSpec sess unsafeCode raw).level = .forbid → AllBlocksLocal e →
      (lintWalk sess raw e).any Diag.isError = false → NoUnsafeBlock e := by
  intro e
  induction e with
  | safeOp => intro _ _ _ _; exact True.intro
  | unsafeOp op => intro _ _ _ _; exact True.intro
  | seq a b iha ihb =>
    intro raw hforbid hlocal hclean
    have hclean' : ((lintWalk sess raw a).any Diag.isError ||
        (lintWalk sess raw b).any Diag.isError) = false := by
      rw [← any_append]
      exact hclean
    have hsplit := or_false_split hclean'
    exact ⟨iha raw hforbid hlocal.1 hsplit.1, ihb raw hforbid hlocal.2 hsplit.2⟩
  | unsafeBlock ctxt body _ =>
    intro raw hforbid hlocal hclean
    have hrep : reportUnsafe sess raw ctxt = [.unsafeCode .error] := by
      unfold reportUnsafe
      rw [hlocal.2.1, hlocal.1, emitLintBase_unsafeCode_forbid_local _ hforbid]
      rfl
    have hclean' : ((reportUnsafe sess raw ctxt).any Diag.isError ||
        (lintWalk sess raw body).any Diag.isError) = false := by
      rw [← any_append]
      exact hclean
    rw [hrep] at hclean'
    exact absurd hclean' (by intro h; exact absurd (or_false_split h).1 (by decide))
  | withAttr level body ih =>
    intro raw hforbid hlocal hclean
    have hclean' : ((attrDiags (insertSpec sess unsafeCode raw level).2).any Diag.isError ||
        (lintWalk sess (insertSpec sess unsafeCode raw level).1 body).any Diag.isError) = false := by
      rw [← any_append]
      exact hclean
    have hsplit := or_false_split hclean'
    cases insertSpec_of_forbid sess unsafeCode raw level hunc hforbid with
    | inl he =>
      rw [he] at hsplit
      exact absurd hsplit.1 (by decide)
    | inr hstill => exact ih _ hstill hlocal hsplit.2

/-- Without `unsafe` blocks, a body that passes the unsafety check lowers to a
body without unsafe operations. -/
theorem no_block_checked_implies_no_unsafe_mir :
    ∀ (e : Expr), NoUnsafeBlock e → unsafeckOk false e = true → hasUnsafeMir (lower e) = false := by
  intro e
  induction e with
  | safeOp => intro _ _; rfl
  | unsafeOp op =>
    intro _ hck
    have hfalse : false = true := hck
    exact absurd hfalse (by decide)
  | seq a b iha ihb =>
    intro hnb hck
    have hsplit := and_true_split hck
    show (lower a ++ lower b).any MirStmt.isUnsafe = false
    rw [any_append]
    have ha : (lower a).any MirStmt.isUnsafe = false := iha hnb.1 hsplit.1
    have hb : (lower b).any MirStmt.isUnsafe = false := ihb hnb.2 hsplit.2
    rw [ha, hb]
    rfl
  | unsafeBlock ctxt body _ => intro hnb _; exact absurd hnb (fun h => h)
  | withAttr level body ih => intro hnb hck; exact ih hnb hck

/-- **Theorem 2 (local-only `forbid` soundness).** Suppose nothing caps the
lint, the level in scope is revealed as `forbid`, and every `unsafe` block has
local provenance. If the lint walk reports no error and the unsafety check
passes, the lowered body contains no unsafe operation. -/
theorem forbid_catches_local_non_capped_unsafe (sess : Session) (raw : Option LevelSpec)
    (e : Expr) (hunc : Uncapped sess)
    (hforbid : (revealActualLevelSpec sess unsafeCode raw).level = .forbid)
    (hlocal : AllBlocksLocal e)
    (hclean : (lintWalk sess raw e).any Diag.isError = false)
    (hck : unsafeckOk false e = true) :
    hasUnsafeMir (lower e) = false :=
  no_block_checked_implies_no_unsafe_mir e
    (lint_clean_implies_no_block sess hunc e raw hforbid hlocal hclean) hck

theorem reveal_level_ne_forceWarn (sess : Session) (lint : LintInfo) (probe : Option LevelSpec)
    (hunc : Uncapped sess) (hdef : lint.defaultLevel ≠ .forceWarn)
    (hp : LevelNotForceWarn probe) :
    (revealActualLevelSpec sess lint probe).level ≠ .forceWarn := by
  rw [reveal_uncapped sess lint probe hunc]
  apply applyWarningsGroup_ne_forceWarn
  cases probe with
  | none => exact hdef
  | some x => exact hp x rfl

/-- A crate-root `#![forbid(unsafe_code)]` is revealed as `forbid` for the
body when the command line has neither a cap nor a `--force-warn`. -/
theorem crate_forbid_attr_revealed (args : List CliArg) (hcap : lintCapOf args = none)
    (hfw : NoForceWarnFlag args) :
    (insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid).2 = .accepted ∧
      (revealActualLevelSpec (sessionOf args) unsafeCode
        (insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid).1).level = .forbid := by
  have hunc : Uncapped (sessionOf args) := by
    constructor
    · show (lintCapOf args).getD .forbid = .forbid
      rw [hcap]
      rfl
    · rfl
  have hne := reveal_level_ne_forceWarn (sessionOf args) unsafeCode (cliSpec args) hunc
    (by decide) (cli_levelNotForceWarn .thisLint args hfw)
  have hins : insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid =
      (some ⟨.forbid, .node⟩, .accepted) := by
    unfold insertSpec
    rw [insertSpecLiteral_eq_table]
    generalize revealActualLevelSpec (sessionOf args) unsafeCode (cliSpec args) = old at hne
    cases old with
    | mk oldLevel oldSrc =>
      cases oldLevel
      case forceWarn => exact absurd rfl hne
      all_goals rfl
  rw [hins]
  exact ⟨rfl, reveal_node_forbid (sessionOf args) unsafeCode hunc⟩

/-- **Theorem 2, crate form.** A crate with `#![forbid(unsafe_code)]`, compiled
without `--cap-lints` and without `--force-warn`, whose `unsafe` blocks all
have local provenance: if it compiles, its lowered body has no unsafe
operation. -/
theorem forbid_attr_crate_sound (args : List CliArg) (body : Expr)
    (hcap : lintCapOf args = none) (hfw : NoForceWarnFlag args)
    (hlocal : AllBlocksLocal body)
    (hacc : rustcAccepts ⟨args, [.forbid], body⟩ = true) :
    hasUnsafeMir (lower body) = false := by
  have hunc : Uncapped (sessionOf args) := by
    constructor
    · show (lintCapOf args).getD .forbid = .forbid
      rw [hcap]
      rfl
    · rfl
  have hroot := crate_forbid_attr_revealed args hcap hfw
  have hsplit := and_true_split hacc
  have hclean : (lintDiags ⟨args, [.forbid], body⟩).any Diag.isError = false := by
    cases h : (lintDiags ⟨args, [.forbid], body⟩).any Diag.isError with
    | false => rfl
    | true =>
      have h1 := hsplit.1
      rw [h] at h1
      exact absurd h1 (by decide)
  have hwalk : (lintWalk (sessionOf args)
      (insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid).1 body).any
        Diag.isError = false := by
    have hunfold : lintDiags ⟨args, [.forbid], body⟩ =
        attrDiags (insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid).2 ++
          lintWalk (sessionOf args)
            (insertSpec (sessionOf args) unsafeCode (cliSpec args) .forbid).1 body := rfl
    rw [hunfold, any_append] at hclean
    exact (or_false_split hclean).2
  exact forbid_catches_local_non_capped_unsafe (sessionOf args) _ body hunc hroot.2 hlocal hwalk
    hsplit.2

/-! ## 10. Theorem 3: the post-expansion audit -/

theorem hasUnsafeMir_lower_of_mem :
    ∀ (e : Expr) (op : UnsafeOp), op ∈ unsafeOps e → hasUnsafeMir (lower e) = true := by
  intro e
  induction e with
  | safeOp => intro op h; exact nomatch h
  | unsafeOp o => intro _ _; rfl
  | seq a b iha ihb =>
    intro op h
    show (lower a ++ lower b).any MirStmt.isUnsafe = true
    rw [any_append]
    cases List.mem_append.mp h with
    | inl ha =>
      have : (lower a).any MirStmt.isUnsafe = true := iha op ha
      rw [this]
      rfl
    | inr hb =>
      have : (lower b).any MirStmt.isUnsafe = true := ihb op hb
      rw [this]
      exact Bool.or_true _
  | unsafeBlock ctxt body ih => intro op h; exact ih op h
  | withAttr level body ih => intro op h; exact ih op h

theorem unsafeOps_ne_nil_of_hasUnsafeMir :
    ∀ (e : Expr), hasUnsafeMir (lower e) = true → unsafeOps e ≠ [] := by
  intro e
  induction e with
  | safeOp => intro h; exact absurd h (by decide)
  | unsafeOp o => intro _ h; exact nomatch h
  | seq a b iha ihb =>
    intro h hnil
    have h' : ((lower a).any MirStmt.isUnsafe || (lower b).any MirStmt.isUnsafe) = true := by
      rw [← any_append]
      exact h
    have hboth : unsafeOps a = [] ∧ unsafeOps b = [] := List.append_eq_nil_iff.mp hnil
    cases ha : (lower a).any MirStmt.isUnsafe with
    | true => exact iha ha hboth.1
    | false =>
      rw [ha] at h'
      exact ihb h' hboth.2
  | unsafeBlock ctxt body ih => intro h; exact ih h
  | withAttr level body ih => intro h; exact ih h

/-- The audit flags a body exactly when it contains an unsafe operation. -/
theorem hasUnsafeMir_lower_iff (e : Expr) :
    hasUnsafeMir (lower e) = true ↔ unsafeOps e ≠ [] := by
  constructor
  · exact unsafeOps_ne_nil_of_hasUnsafeMir e
  · intro h
    cases hops : unsafeOps e with
    | nil => exact absurd hops h
    | cons op rest =>
      exact hasUnsafeMir_lower_of_mem e op (by rw [hops]; exact List.mem_cons_self ..)

/-- Replace every span context and every attribute level in a tree. -/
noncomputable def relabel (f : SyntaxContext → SyntaxContext) (g : LintLevel → LintLevel) : Expr → Expr
  | .safeOp => .safeOp
  | .unsafeOp op => .unsafeOp op
  | .seq a b => .seq (relabel f g a) (relabel f g b)
  | .unsafeBlock ctxt body => .unsafeBlock (f ctxt) (relabel f g body)
  | .withAttr level body => .withAttr (g level) (relabel f g body)

/-- The lowered body does not depend on span provenance or on lint attributes. -/
theorem lower_relabel (f : SyntaxContext → SyntaxContext) (g : LintLevel → LintLevel) :
    ∀ (e : Expr), lower (relabel f g e) = lower e := by
  intro e
  induction e with
  | safeOp => rfl
  | unsafeOp op => rfl
  | seq a b iha ihb =>
    show lower (relabel f g a) ++ lower (relabel f g b) = lower a ++ lower b
    rw [iha, ihb]
  | unsafeBlock ctxt body ih => exact ih
  | withAttr level body ih => exact ih

/-- **Theorem 3 (post-expansion audit completeness).** For every crate, with
any command line (capped or not), any crate attributes and any provenance of
its `unsafe` blocks, an unsafe operation in the expanded body is flagged by the
audit of the lowered body. The verdict is the same for every relabelling of
span contexts and lint attributes. -/
theorem mir_unsafe_audit_catches_all_macro_and_capped_unsafe (c : Crate) (op : UnsafeOp)
    (h : op ∈ unsafeOps c.body) :
    hasUnsafeMir (lower c.body) = true ∧
      ∀ (f : SyntaxContext → SyntaxContext) (g : LintLevel → LintLevel),
        hasUnsafeMir (lower (relabel f g c.body)) = true := by
  refine ⟨hasUnsafeMir_lower_of_mem c.body op h, ?_⟩
  intro f g
  rw [lower_relabel]
  exact hasUnsafeMir_lower_of_mem c.body op h

/-! ## 11. Counterexamples and worked instances -/

/-- A `macro_rules!` macro defined in another crate. -/
noncomputable def foreignMacroRules : ExpnData := ⟨.macro .bang, false, true, false⟩

/-- A `macro_rules!` macro defined in the crate being compiled. -/
noncomputable def localMacroRules : ExpnData := ⟨.macro .bang, false, false, false⟩

/-- A function-like procedural macro (always defined in another crate). -/
noncomputable def foreignProcMacro : ExpnData := ⟨.macro .bang, false, true, false⟩

/-- `unsafe { *p }` whose block span has context `ctxt`. -/
noncomputable def rawDerefBlock (ctxt : SyntaxContext) : Expr := .unsafeBlock ctxt (.unsafeOp .derefRawPtr)

noncomputable def flagForbid : CliArg := .level .forbid .thisLint
noncomputable def flagForceWarn : CliArg := .level .forceWarn .thisLint
noncomputable def flagCapAllow : CliArg := .capLints .allow
noncomputable def flagCapDeny : CliArg := .capLints .deny

/-- **Counterexample 1.** Without a cap, an attribute `forbid` and a
command-line `-F` each reject a local `unsafe` block. With `--cap-lints allow`
in either position, the crate carrying both is accepted without any
diagnostic, although its lowered body has an unsafe operation. -/
theorem ce1_cap_lints_allow_overrides_forbid_and_cli_F :
    rustcAccepts ⟨[], [.forbid], rawDerefBlock []⟩ = false ∧
    rustcAccepts ⟨[flagForbid], [], rawDerefBlock []⟩ = false ∧
    rustcAccepts ⟨[flagForbid, flagCapAllow], [.forbid], rawDerefBlock []⟩ = true ∧
    rustcAccepts ⟨[flagCapAllow, flagForbid], [.forbid], rawDerefBlock []⟩ = true ∧
    lintDiags ⟨[flagForbid, flagCapAllow], [.forbid], rawDerefBlock []⟩ = [] ∧
    lintDiags ⟨[flagCapAllow, flagForbid], [.forbid], rawDerefBlock []⟩ = [] ∧
    hasUnsafeMir (lower (rawDerefBlock [])) = true := by
  decide

/-- **Counterexample 2.** In an uncapped `#![forbid(unsafe_code)]` crate, an
`unsafe` block whose span is a foreign proc macro's `call_site`, `mixed_site`
or `def_site` span is accepted without any diagnostic; the same block with a
root-context span is rejected; the lowered bodies are identical. -/
theorem ce2_foreign_call_site_proc_macro_bypasses_forbid :
    rustcAccepts ⟨[], [.forbid],
      rawDerefBlock (procMacroSpanCtxt foreignProcMacro .transparent [])⟩ = true ∧
    lintDiags ⟨[], [.forbid],
      rawDerefBlock (procMacroSpanCtxt foreignProcMacro .transparent [])⟩ = [] ∧
    rustcAccepts ⟨[], [.forbid],
      rawDerefBlock (procMacroSpanCtxt foreignProcMacro .semiOpaque [])⟩ = true ∧
    rustcAccepts ⟨[], [.forbid],
      rawDerefBlock (procMacroSpanCtxt foreignProcMacro .opaque [])⟩ = true ∧
    rustcAccepts ⟨[], [.forbid], rawDerefBlock []⟩ = false ∧
    lower (rawDerefBlock (procMacroSpanCtxt foreignProcMacro .transparent [])) =
      lower (rawDerefBlock []) ∧
    hasUnsafeMir
      (lower (rawDerefBlock (procMacroSpanCtxt foreignProcMacro .transparent []))) = true := by
  decide

/-- **Counterexample 3.** In an uncapped `#![forbid(unsafe_code)]` crate, a
foreign macro that expands to a bare `unsafe` block is accepted silently, while
the same expansion preceded by `#[allow(unsafe_code)]` is rejected with exactly
one E0453; both lower to the same body. -/
theorem ce3_foreign_macro_bare_unsafe_passes_while_allow_attr_fails_e0453 :
    rustcAccepts ⟨[], [.forbid], rawDerefBlock [foreignMacroRules]⟩ = true ∧
    lintDiags ⟨[], [.forbid], rawDerefBlock [foreignMacroRules]⟩ = [] ∧
    rustcAccepts ⟨[], [.forbid], .withAttr .allow (rawDerefBlock [foreignMacroRules])⟩ = false ∧
    lintDiags ⟨[], [.forbid], .withAttr .allow (rawDerefBlock [foreignMacroRules])⟩ =
      [.e0453] ∧
    lower (.withAttr .allow (rawDerefBlock [foreignMacroRules])) =
      lower (rawDerefBlock [foreignMacroRules]) := by
  decide

/-- Under `--cap-lints deny` the outer level is revealed as `deny`, so an inner
`allow` is accepted and a local `unsafe` block passes; without the inner
attribute it is still an error. -/
theorem ce4_cap_lints_deny_makes_forbid_overridable :
    rustcAccepts ⟨[flagCapDeny], [.forbid], .withAttr .allow (rawDerefBlock [])⟩ = true ∧
    lintDiags ⟨[flagCapDeny], [.forbid], .withAttr .allow (rawDerefBlock [])⟩ = [] ∧
    rustcAccepts ⟨[flagCapDeny], [.forbid], rawDerefBlock []⟩ = false ∧
    rustcAccepts ⟨[], [.forbid], .withAttr .allow (rawDerefBlock [])⟩ = false := by
  decide

/-- A command-line `--force-warn` is exempt from `--cap-lints allow`, and it
also keeps a later `#![forbid]` attribute at warning strength. -/
theorem ce5_force_warn_is_neither_capped_nor_raised_by_forbid :
    lintDiags ⟨[flagForceWarn, flagCapAllow], [], rawDerefBlock []⟩ =
      [.unsafeCode .forceWarning] ∧
    lintDiags ⟨[flagForceWarn], [.forbid], rawDerefBlock []⟩ = [.unsafeCode .forceWarning] ∧
    rustcAccepts ⟨[flagForceWarn], [.forbid], rawDerefBlock []⟩ = true := by
  decide

/-- Nesting: a local macro that invokes a foreign macro yields an external
span; a foreign macro that invokes a local macro yields a local one. -/
theorem chain_only_outermost_expansion_counts :
    inExternalMacro [foreignMacroRules, localMacroRules] = true ∧
    inExternalMacro [localMacroRules, foreignMacroRules] = false ∧
    rustcAccepts ⟨[], [.forbid], rawDerefBlock [foreignMacroRules, localMacroRules]⟩ = true ∧
    rustcAccepts ⟨[], [.forbid], rawDerefBlock [localMacroRules, foreignMacroRules]⟩ = false := by
  decide

/-- The lint is about syntax, the audit about operations: an `unsafe` block
with no unsafe operation is rejected under `forbid` yet has nothing to audit. -/
theorem lint_and_audit_are_incomparable :
    rustcAccepts ⟨[], [.forbid], .unsafeBlock [] .safeOp⟩ = false ∧
    hasUnsafeMir (lower (.unsafeBlock [] .safeOp)) = false ∧
    rustcAccepts ⟨[], [.forbid], rawDerefBlock [foreignMacroRules]⟩ = true ∧
    hasUnsafeMir (lower (rawDerefBlock [foreignMacroRules])) = true := by
  decide

/-- `#[expect]` below an uncapped `forbid` is E0453; `deny` below it is ignored. -/
theorem expect_and_deny_below_forbid :
    lintDiags ⟨[], [.forbid], .withAttr .expect (rawDerefBlock [])⟩ =
      [.e0453, .unsafeCode .error] ∧
    lintDiags ⟨[], [.forbid], .withAttr .deny (rawDerefBlock [])⟩ = [.unsafeCode .error] := by
  decide

/-- Under `--cap-lints allow` an `expect` level is revealed as `allow`, and the
warn-by-default `unfulfilled_lint_expectations` lint emits nothing. -/
theorem expect_and_unfulfilled_expectations_under_cap_allow :
    (revealActualLevelSpec ⟨some .allow, none, none⟩ unsafeCode (some ⟨.expect, .node⟩)).level =
      .allow ∧
    emitLintBase unfulfilledLintExpectations
      (revealActualLevelSpec ⟨some .allow, none, none⟩ unfulfilledLintExpectations none) false =
        .none ∧
    emitLintBase unfulfilledLintExpectations
      (revealActualLevelSpec ⟨none, none, none⟩ unfulfilledLintExpectations none) false =
        .warning := by
  decide

end LintCap

#print axioms LintCap.LintLevel.min_assoc
#print axioms LintCap.LintLevel.le_min
#print axioms LintCap.reveal_le_lintCap
#print axioms LintCap.reveal_le_driverCap
#print axioms LintCap.cap_flag_position_irrelevant
#print axioms LintCap.insertSpecLiteral_eq_table
#print axioms LintCap.insertSpec_of_forbid
#print axioms LintCap.procMacro_span_modes_agree
#print axioms LintCap.foreign_proc_macro_span_external
#print axioms LintCap.emitLintBase_unsafeCode_external
#print axioms LintCap.capLints_allow_silences_forbid_and_cli_F
#print axioms LintCap.forbid_catches_local_non_capped_unsafe
#print axioms LintCap.forbid_attr_crate_sound
#print axioms LintCap.hasUnsafeMir_lower_iff
#print axioms LintCap.lower_relabel
#print axioms LintCap.mir_unsafe_audit_catches_all_macro_and_capped_unsafe
#print axioms LintCap.ce1_cap_lints_allow_overrides_forbid_and_cli_F
#print axioms LintCap.ce2_foreign_call_site_proc_macro_bypasses_forbid
#print axioms LintCap.ce3_foreign_macro_bare_unsafe_passes_while_allow_attr_fails_e0453
#print axioms LintCap.ce4_cap_lints_deny_makes_forbid_overridable
#print axioms LintCap.ce5_force_warn_is_neither_capped_nor_raised_by_forbid
#print axioms LintCap.chain_only_outermost_expansion_counts
#print axioms LintCap.lint_and_audit_are_incomparable
#print axioms LintCap.expect_and_deny_below_forbid
#print axioms LintCap.expect_and_unfulfilled_expectations_under_cap_allow

-- Definitions, to show where an axiom first appears.
#print axioms LintCap.insertSpecLiteral
#print axioms LintCap.insertSpecTable
#print axioms LintCap.emitLintBase
#print axioms LintCap.applyCap
#print axioms LintCap.lintWalk
#print axioms LintCap.levelEmission
#print axioms LintCap.lower
