/-
  NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean

  Kernel-checked Lean v4.34.1 formalization of:
    1. Rust pattern type inhabitedness, module privacy (`PrivateUninhabitedField`),
       and cross-crate `#[non_exhaustive]` empty enums (`rustc_pattern_analysis`).
    2. `PlaceValidity` tracking across `Ref` / `Deref` / `UnionField` projections
       and the `can_omit_empty_arms` / `is_toplevel_exception` predicate
       (`compiler/rustc_pattern_analysis/src/usefulness.rs`).
    3. Pattern matrix specialization, constructor splitting, never-pattern
       well-formedness (`check_never_pattern`, bodiless/guardless invariants),
       and exhaustiveness soundness (`exhaustiveMatrix_every_valid_value_matched_or_never_read`).
    4. Three-way operational place-evaluation semantics (`PlaceMention` wildcard
       vs. empty match vs. explicit `!` never-pattern place-validity read vs.
       uninhabited enum discriminant read).
    5. Sub-pattern guard opacity for exhaustiveness
       (`guardPattern_must_stay_opaque_for_exhaustiveness`) contrasted with the
       incomplete `rustc` unguarded lowering (`rustc.rs:471-472`) and MIR
       builder stub (`match_pair.rs:457-460`).
    6. Postfix match (`expr.match { ... }`) temporary drop-scope equivalence with
       prefix `match`.
    7. Connection to Anneal `MirTy.never` vacuous-entry admission (`BodyStaticAdmitted`).
    8. Constructive sharpness counterexamples (`ce1`–`ce6`).

  Purity contract:
    - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
      zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
    - No `deriving` clauses on any inductive type.
-/

namespace NeverPatternsSoundness

/-! ## Part 1: Types, Visibility, and Semantic vs. Module-Visible Inhabitedness -/

/-- Visibility of a struct field relative to the match site's defining module,
    modeling `field.vis.is_accessible_from(cx.module, cx.tcx)` in
    `compiler/rustc_pattern_analysis/src/rustc.rs`. -/
inductive FieldVis : Type where
  | pubVis : FieldVis
  | privVis : FieldVis

def FieldVis.beq : FieldVis → FieldVis → Bool
  | .pubVis, .pubVis => true
  | .privVis, .privVis => true
  | _, _ => false

theorem FieldVis.beq_refl (v : FieldVis) : FieldVis.beq v v = true := by
  cases v <;> rfl

theorem FieldVis.eq_of_beq {a b : FieldVis} (h : FieldVis.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- Core Rust pattern-matching type fragment modeled for `rustc_pattern_analysis`
    and `rustc_mir_build` lowering.
    Every constructor has non-nested inductive fields (no `List`/`Option` inside
    the inductive) so Lean generates a pure structural recursor with zero
    `_unsafe_rec` auxiliary constants. -/
inductive Ty : Type where
  | never : Ty
  | unit : Ty
  | bool : Ty
  | emptyEnum : Bool → Ty                        -- `true` = foreign `#[non_exhaustive]`
  | opt : Ty → Ty                                -- `Option<T>`
  | result : Ty → Ty → Ty                        -- `Result<T, E>`
  | pair : FieldVis → Ty → FieldVis → Ty → Ty    -- 2-field struct with per-field visibility
  | ref : Ty → Ty                                -- `&T`
  | rawPtr : Ty → Ty                             -- `*const T`
  | union : Ty → Ty → Ty                         -- `union { a: T1, b: T2 }`

noncomputable def Ty.beq (a : Ty) : Ty → Bool :=
  Ty.rec
    (fun b => match b with | .never => true | _ => false)
    (fun b => match b with | .unit => true | _ => false)
    (fun b => match b with | .bool => true | _ => false)
    (fun f1 b => match b with | .emptyEnum f2 => f1 == f2 | _ => false)
    (fun _ ih b => match b with | .opt b' => ih b' | _ => false)
    (fun _ _ ih1 ih2 b => match b with | .result a2 b2 => ih1 a2 && ih2 b2 | _ => false)
    (fun v1 _ v2 _ ih1 ih2 b => match b with
      | .pair w1 a2 w2 b2 => FieldVis.beq v1 w1 && ih1 a2 && FieldVis.beq v2 w2 && ih2 b2
      | _ => false)
    (fun _ ih b => match b with | .ref b' => ih b' | _ => false)
    (fun _ ih b => match b with | .rawPtr b' => ih b' | _ => false)
    (fun _ _ ih1 ih2 b => match b with | .union a2 b2 => ih1 a2 && ih2 b2 | _ => false)
    a

theorem Ty.beq_result (a1 b1 a2 b2 : Ty) :
    Ty.beq (.result a1 b1) (.result a2 b2) = (Ty.beq a1 a2 && Ty.beq b1 b2) := rfl

theorem Ty.beq_pair (v1 v2 w1 w2 : FieldVis) (a1 b1 a2 b2 : Ty) :
    Ty.beq (.pair v1 a1 v2 b1) (.pair w1 a2 w2 b2) =
      (FieldVis.beq v1 w1 && Ty.beq a1 a2 && FieldVis.beq v2 w2 && Ty.beq b1 b2) := rfl

theorem Ty.beq_union (a1 b1 a2 b2 : Ty) :
    Ty.beq (.union a1 b1) (.union a2 b2) = (Ty.beq a1 a2 && Ty.beq b1 b2) := rfl

theorem Ty.beq_refl : ∀ t : Ty, Ty.beq t t = true
  | .never => rfl
  | .unit => rfl
  | .bool => rfl
  | .emptyEnum f => by cases f <;> rfl
  | .opt a => Ty.beq_refl a
  | .result a b => by rw [Ty.beq_result, Ty.beq_refl a, Ty.beq_refl b]; rfl
  | .pair v1 a v2 b => by
      rw [Ty.beq_pair, FieldVis.beq_refl v1, FieldVis.beq_refl v2, Ty.beq_refl a, Ty.beq_refl b]; rfl
  | .ref a => Ty.beq_refl a
  | .rawPtr a => Ty.beq_refl a
  | .union a b => by rw [Ty.beq_union, Ty.beq_refl a, Ty.beq_refl b]; rfl

/-- Size measure on types for total fuel bounds in pattern analysis. -/
noncomputable def Ty.size : Ty → Nat :=
  Ty.rec 1 1 1 (fun _ => 1) (fun _ ih => 1 + ih) (fun _ _ ih1 ih2 => 1 + ih1 + ih2)
    (fun _ _ _ _ ih1 ih2 => 1 + ih1 + ih2) (fun _ ih => 1 + ih) (fun _ ih => 1 + ih)
    (fun _ _ ih1 ih2 => 1 + ih1 + ih2)

theorem Ty.size_pos : ∀ t : Ty, 1 ≤ Ty.size t
  | .never => Nat.le_refl 1
  | .unit => Nat.le_refl 1
  | .bool => Nat.le_refl 1
  | .emptyEnum _ => Nat.le_refl 1
  | .opt _ => Nat.le_add_right 1 _
  | .result _ _ => Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  | .pair _ _ _ _ => Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  | .ref _ => Nat.le_add_right 1 _
  | .rawPtr _ => Nat.le_add_right 1 _
  | .union _ _ => Nat.le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)

/-- Whether a field with visibility `v` is accessible from match site `inDefiningMod`. -/
def fieldAccessible (inDefiningMod : Bool) (v : FieldVis) : Bool :=
  match v with
  | .pubVis => true
  | .privVis => inDefiningMod

/-- Semantic well-typed valid values (`ValidVal t`). -/
inductive ValidVal : Ty → Type where
  | unit : ValidVal .unit
  | bool : Bool → ValidVal .bool
  | foreignExt : ValidVal (.emptyEnum true)
  | none : {t : Ty} → ValidVal (.opt t)
  | some : {t : Ty} → ValidVal t → ValidVal (.opt t)
  | ok : {t1 t2 : Ty} → ValidVal t1 → ValidVal (.result t1 t2)
  | err : {t1 t2 : Ty} → ValidVal t2 → ValidVal (.result t1 t2)
  | pair : {v1 v2 : FieldVis} → {t1 t2 : Ty} →
      ValidVal t1 → ValidVal t2 → ValidVal (.pair v1 t1 v2 t2)
  | refVal : {t : Ty} → ValidVal t → ValidVal (.ref t)
  | rawPtrAddr : {t : Ty} → Nat → ValidVal (.rawPtr t)
  | unionF1 : {t1 t2 : Ty} → ValidVal t1 → ValidVal (.union t1 t2)
  | unionF2 : {t1 t2 : Ty} → ValidVal t2 → ValidVal (.union t1 t2)
  | unionRaw : {t1 t2 : Ty} → Nat → ValidVal (.union t1 t2)

def SemInhabited (t : Ty) : Prop := Nonempty (ValidVal t)

theorem not_semInhabited_never : ¬ SemInhabited .never := by
  intro h
  cases h with
  | intro v => cases v

theorem not_semInhabited_localEmptyEnum : ¬ SemInhabited (.emptyEnum false) := by
  intro h
  cases h with
  | intro v => cases v

theorem semInhabited_foreignNonExhaustiveEmptyEnum : SemInhabited (.emptyEnum true) :=
  ⟨.foreignExt⟩

/-- Module-scoped visible uninhabitedness, mirroring
    `RustcPatCtxt::is_uninhabited` (`compiler/rustc_pattern_analysis/src/rustc.rs:157-164`). -/
noncomputable def visiblyUninhabited (inDefiningMod : Bool) : Ty → Bool :=
  Ty.rec
    true
    false
    false
    (fun isForeignNonExh => if isForeignNonExh then inDefiningMod else true)
    (fun _ _ => false)
    (fun _ _ ih1 ih2 => ih1 && ih2)
    (fun v1 _ v2 _ ih1 ih2 =>
      (fieldAccessible inDefiningMod v1 && ih1) ||
      (fieldAccessible inDefiningMod v2 && ih2))
    (fun _ _ => false)
    (fun _ _ => false)
    (fun _ _ _ _ => false)

theorem visiblyUninhabited_result (inMod : Bool) (t1 t2 : Ty) :
    visiblyUninhabited inMod (.result t1 t2) =
      (visiblyUninhabited inMod t1 && visiblyUninhabited inMod t2) := rfl

theorem visiblyUninhabited_pair (inMod : Bool) (v1 v2 : FieldVis) (t1 t2 : Ty) :
    visiblyUninhabited inMod (.pair v1 t1 v2 t2) =
      ((fieldAccessible inMod v1 && visiblyUninhabited inMod t1) ||
       (fieldAccessible inMod v2 && visiblyUninhabited inMod t2)) := rfl

theorem visiblyUninhabited_false_implies_no_validVal :
    ∀ (t : Ty), visiblyUninhabited false t = true → ValidVal t → False := by
  intro t h v
  induction v with
  | unit => cases h
  | bool _ => cases h
  | foreignExt => cases h
  | none => cases h
  | some _ => cases h
  | ok _ ih =>
      rw [visiblyUninhabited_result, Bool.and_eq_true] at h
      exact ih h.1
  | err _ ih =>
      rw [visiblyUninhabited_result, Bool.and_eq_true] at h
      exact ih h.2
  | pair _ _ ih1 ih2 =>
      rw [visiblyUninhabited_pair, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      cases h with
      | inl h1 => exact ih1 h1.2
      | inr h2 => exact ih2 h2.2
  | refVal _ => cases h
  | rawPtrAddr _ => cases h
  | unionF1 _ => cases h
  | unionF2 _ => cases h
  | unionRaw _ => cases h

theorem fieldAccessible_mono (v : FieldVis) :
    fieldAccessible false v = true → fieldAccessible true v = true := by
  cases v <;> intro _ <;> rfl

theorem visiblyUninhabited_mono :
    ∀ t : Ty, visiblyUninhabited false t = true → visiblyUninhabited true t = true
  | .never, _ => rfl
  | .unit, h => h
  | .bool, h => h
  | .emptyEnum false, _ => rfl
  | .emptyEnum true, h => by cases h
  | .opt _, h => h
  | .result t1 t2, h => by
      rw [visiblyUninhabited_result, Bool.and_eq_true] at h ⊢
      exact ⟨visiblyUninhabited_mono t1 h.1, visiblyUninhabited_mono t2 h.2⟩
  | .pair v1 t1 v2 t2, h => by
      rw [visiblyUninhabited_pair, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
      cases h with
      | inl h1 => exact Or.inl ⟨fieldAccessible_mono v1 h1.1, visiblyUninhabited_mono t1 h1.2⟩
      | inr h2 => exact Or.inr ⟨fieldAccessible_mono v2 h2.1, visiblyUninhabited_mono t2 h2.2⟩
  | .ref _, h => h
  | .rawPtr _, h => h
  | .union _ _, h => h

def isNoConstructors (inDefiningMod : Bool) : Ty → Bool
  | .never => true
  | .emptyEnum isForeignNonExh => if isForeignNonExh then inDefiningMod else true
  | _ => false

theorem isNoConstructors_implies_visiblyUninhabited (inMod : Bool) (t : Ty) :
    isNoConstructors inMod t = true → visiblyUninhabited inMod t = true := by
  cases t with
  | never => intro _; rfl
  | emptyEnum f => cases f <;> intro h <;> exact h
  | unit => intro h; cases h
  | bool => intro h; cases h
  | opt _ => intro h; cases h
  | result _ _ => intro h; cases h
  | pair _ _ _ _ => intro h; cases h
  | ref _ => intro h; cases h
  | rawPtr _ => intro h; cases h
  | union _ _ => intro h; cases h

/-! ## Part 2: `PlaceValidity` and Operational Place States (`RawPlace`) -/

inductive PlaceValidity : Type where
  | validOnly : PlaceValidity
  | maybeInvalid : PlaceValidity

def PlaceValidity.isKnownValid : PlaceValidity → Bool
  | .validOnly => true
  | .maybeInvalid => false

def PlaceValidity.specialize (pv : PlaceValidity) (crossesRefOrUnion : Bool) : PlaceValidity :=
  if crossesRefOrUnion then .maybeInvalid else pv

theorem PlaceValidity.specialize_ref_resets (pv : PlaceValidity) :
    pv.specialize true = .maybeInvalid := rfl

theorem PlaceValidity.specialize_struct_preserves (pv : PlaceValidity) :
    pv.specialize false = pv := rfl

inductive ScrutineeKind : Type where
  | byValueLocal : ScrutineeKind
  | derefRawPtr : ScrutineeKind
  | derefSharedRef : ScrutineeKind
  | unionFieldAccess : ScrutineeKind

def scrutineeValidity : ScrutineeKind → PlaceValidity
  | .byValueLocal => .validOnly
  | .derefRawPtr => .maybeInvalid
  | .derefSharedRef => .maybeInvalid
  | .unionFieldAccess => .maybeInvalid

inductive RawPlace : Ty → Type where
  | valid : {t : Ty} → ValidVal t → RawPlace t
  | nullRawDeref : {t : Ty} → RawPlace t
  | uninitLocal : {t : Ty} → RawPlace t
  | rogueErrTag : {t1 t2 : Ty} → RawPlace (.result t1 t2)
  | roguePair : {v1 v2 : FieldVis} → {t1 t2 : Ty} →
      RawPlace t1 → RawPlace t2 → RawPlace (.pair v1 t1 v2 t2)
  | rogueRef : {t : Ty} → RawPlace t → RawPlace (.ref t)

def PlaceRespectsValidity {t : Ty} (pv : PlaceValidity) (p : RawPlace t) : Prop :=
  match pv with
  | .validOnly => ∃ v : ValidVal t, p = .valid v
  | .maybeInvalid => True

theorem validOnly_never_absurd (p : RawPlace .never)
    (h : PlaceRespectsValidity .validOnly p) : False := by
  rcases h with ⟨v, _⟩
  cases v

theorem validOnly_localEmpty_absurd (p : RawPlace (.emptyEnum false))
    (h : PlaceRespectsValidity .validOnly p) : False := by
  rcases h with ⟨v, _⟩
  cases v

theorem validOnly_visiblyUninhabited_absurd {t : Ty} (p : RawPlace t)
    (hu : visiblyUninhabited false t = true)
    (hv : PlaceRespectsValidity .validOnly p) : False := by
  rcases hv with ⟨v, _⟩
  exact visiblyUninhabited_false_implies_no_validVal t hu v

inductive DiscrReadResult (t1 t2 : Ty) : Type where
  | isOk : RawPlace t1 → DiscrReadResult t1 t2
  | isErr : RawPlace t2 → DiscrReadResult t1 t2
  | faultUninhabitedVariant : DiscrReadResult t1 t2
  | faultUninit : DiscrReadResult t1 t2

noncomputable def readResultDiscr {t1 t2 : Ty} (inMod : Bool) (p : RawPlace (.result t1 t2)) :
    DiscrReadResult t1 t2 :=
  match p with
  | .valid (.ok v) => .isOk (.valid v)
  | .valid (.err v) => .isErr (.valid v)
  | .rogueErrTag =>
      if visiblyUninhabited inMod t2 then
        .faultUninhabitedVariant
      else
        .isErr .nullRawDeref
  | .nullRawDeref => .faultUninit
  | .uninitLocal => .faultUninit

def derefRefPlace {t : Ty} : RawPlace (.ref t) → Option (RawPlace t)
  | .valid (.refVal v) => some (.valid v)
  | .rogueRef inner => some inner
  | .nullRawDeref => none
  | .uninitLocal => none

def projectPairPlace {v1 v2 : FieldVis} {t1 t2 : Ty} :
    RawPlace (.pair v1 t1 v2 t2) → Option (RawPlace t1 × RawPlace t2)
  | .valid (.pair a b) => some (.valid a, .valid b)
  | .roguePair a b => some (a, b)
  | .nullRawDeref => none
  | .uninitLocal => none

/-! ## Part 3: Pattern AST, Never-Pattern Well-Formedness, and Guard Semantics -/

abbrev GuardId := Nat

inductive Pat : Type where
  | wild : Pat
  | never : Pat
  | unit : Pat
  | boolLit : Bool → Pat
  | none : Pat
  | some : Pat → Pat
  | ok : Pat → Pat
  | err : Pat → Pat
  | pair : Pat → Pat → Pat
  | ref : Pat → Pat
  | or : Pat → Pat → Pat
  | subGuard : Pat → GuardId → Pat

noncomputable def Pat.isNeverPattern : Pat → Bool :=
  Pat.rec false true false (fun _ => false) false
    (fun _ ih => ih) (fun _ ih => ih) (fun _ ih => ih)
    (fun _ _ ih1 ih2 => ih1 || ih2) (fun _ ih => ih)
    (fun _ _ ih1 ih2 => ih1 && ih2) (fun _ _ ih => ih)

noncomputable def Pat.containsSubGuard : Pat → Bool :=
  Pat.rec false false false (fun _ => false) false
    (fun _ ih => ih) (fun _ ih => ih) (fun _ ih => ih)
    (fun _ _ ih1 ih2 => ih1 || ih2) (fun _ ih => ih)
    (fun _ _ ih1 ih2 => ih1 || ih2) (fun _ _ _ => true)

noncomputable def checkPatWellFormed (inMod : Bool) (t : Ty) (p : Pat) : Bool :=
  Pat.rec
    (fun _ => true)
    (fun t => visiblyUninhabited inMod t)
    (fun t => match t with | .unit => true | _ => false)
    (fun _ t => match t with | .bool => true | _ => false)
    (fun t => match t with | .opt _ => true | _ => false)
    (fun _ ih t => match t with | .opt inner => ih inner | _ => false)
    (fun _ ih t => match t with | .result t1 _ => ih t1 | _ => false)
    (fun _ ih t => match t with | .result _ t2 => ih t2 | _ => false)
    (fun p1 p2 ih1 ih2 t => match t with
      | .pair v1 t1 v2 t2 =>
          let ok1 := if fieldAccessible inMod v1 then ih1 t1
                     else match p1 with | .wild => true | _ => false
          let ok2 := if fieldAccessible inMod v2 then ih2 t2
                     else match p2 with | .wild => true | _ => false
          ok1 && ok2
      | _ => false)
    (fun _ ih t => match t with | .ref inner => ih inner | _ => false)
    (fun _ _ ih1 ih2 t => ih1 t && ih2 t)
    (fun _ _ ih t => ih t)
    p t

structure Arm : Type where
  pat : Pat
  armGuard : Option GuardId
  hasBody : Bool

noncomputable def armWellFormed (inMod : Bool) (t : Ty) (a : Arm) : Bool :=
  checkPatWellFormed inMod t a.pat &&
  if a.pat.isNeverPattern then
    (!a.hasBody) && (match a.armGuard with | none => true | some _ => false)
  else
    a.hasBody

inductive GuardLoweringMode : Type where
  | soundOpaque : GuardLoweringMode
  | rustcBuggyUnguarded : GuardLoweringMode

noncomputable def armCountsAsGuarded (mode : GuardLoweringMode) (a : Arm) : Bool :=
  let topGuarded := match a.armGuard with | some _ => true | none => false
  match mode with
  | .soundOpaque => topGuarded || a.pat.containsSubGuard
  | .rustcBuggyUnguarded => topGuarded

/-! ## Part 4: Operational Pattern Matching & Three-Way Place Semantics -/

abbrev GuardOracle := GuardId → Bool

inductive PatMatchRes : Type where
  | matched : PatMatchRes
  | mismatch : PatMatchRes
  | ubNeverRead : PatMatchRes
  | ubDiscrRead : PatMatchRes
  | ubPlaceDeref : PatMatchRes

noncomputable def evalPat (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (p : Pat) (pl : RawPlace t) : PatMatchRes :=
  @Pat.rec (fun _ => {t : Ty} → RawPlace t → PatMatchRes)
    (fun {_} _ => .matched)
    (fun {_} _ => .ubNeverRead)
    (fun {t} pl => match t, pl with
      | .unit, .valid .unit => .matched
      | .unit, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun b {t} pl => match t, pl with
      | .bool, .valid (.bool v) => if b == v then .matched else .mismatch
      | .bool, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun {t} pl => match t, pl with
      | .opt _, .valid .none => .matched
      | .opt _, .valid (.some _) => .mismatch
      | .opt _, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .opt _, .valid (.some v) => ih (.valid v)
      | .opt _, .valid .none => .mismatch
      | .opt _, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .result _ _, pl =>
          match readResultDiscr inMod pl with
          | .isOk p1 => ih p1
          | .isErr _ => .mismatch
          | .faultUninhabitedVariant => .ubDiscrRead
          | .faultUninit => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .result _ _, pl =>
          match readResultDiscr inMod pl with
          | .isOk _ => .mismatch
          | .isErr p2 => ih p2
          | .faultUninhabitedVariant => .ubDiscrRead
          | .faultUninit => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ _ ih1 ih2 {t} pl => match t, pl with
      | .pair _ _ _ _, pl =>
          match projectPairPlace pl with
          | none => .ubPlaceDeref
          | some (pl1, pl2) =>
              match ih1 pl1 with
              | .matched => ih2 pl2
              | other => other
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .ref _, pl =>
          match derefRefPlace pl with
          | none => .ubPlaceDeref
          | some inner => ih inner
      | _, _ => .mismatch)
    (fun _ _ ih1 ih2 {_} pl =>
      match ih1 pl with
      | .mismatch => ih2 pl
      | other => other)
    (fun _ gid ih {_} pl =>
      match ih pl with
      | .matched => if gOracle gid then .matched else .mismatch
      | other => other)
    p t pl

/-- Live `rustc` `match_pair.rs:457-460` stub semantics for `PatKind::Guard`. -/
noncomputable def evalPatRustcStub (inMod : Bool) (_gOracle : GuardOracle) {t : Ty}
    (p : Pat) (pl : RawPlace t) : PatMatchRes :=
  @Pat.rec (fun _ => {t : Ty} → RawPlace t → PatMatchRes)
    (fun {_} _ => .matched)
    (fun {_} _ => .ubNeverRead)
    (fun {t} pl => match t, pl with
      | .unit, .valid .unit => .matched
      | .unit, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun b {t} pl => match t, pl with
      | .bool, .valid (.bool v) => if b == v then .matched else .mismatch
      | .bool, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun {t} pl => match t, pl with
      | .opt _, .valid .none => .matched
      | .opt _, .valid (.some _) => .mismatch
      | .opt _, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .opt _, .valid (.some v) => ih (.valid v)
      | .opt _, .valid .none => .mismatch
      | .opt _, _ => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .result _ _, pl =>
          match readResultDiscr inMod pl with
          | .isOk p1 => ih p1
          | .isErr _ => .mismatch
          | .faultUninhabitedVariant => .ubDiscrRead
          | .faultUninit => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .result _ _, pl =>
          match readResultDiscr inMod pl with
          | .isOk _ => .mismatch
          | .isErr p2 => ih p2
          | .faultUninhabitedVariant => .ubDiscrRead
          | .faultUninit => .ubPlaceDeref
      | _, _ => .mismatch)
    (fun _ _ ih1 ih2 {t} pl => match t, pl with
      | .pair _ _ _ _, pl =>
          match projectPairPlace pl with
          | none => .ubPlaceDeref
          | some (pl1, pl2) =>
              match ih1 pl1 with
              | .matched => ih2 pl2
              | other => other
      | _, _ => .mismatch)
    (fun _ ih {t} pl => match t, pl with
      | .ref _, pl =>
          match derefRefPlace pl with
          | none => .ubPlaceDeref
          | some inner => ih inner
      | _, _ => .mismatch)
    (fun _ _ ih1 ih2 {_} pl =>
      match ih1 pl with
      | .mismatch => ih2 pl
      | other => other)
    (fun _ _ _ {_} _ => .matched)
    p t pl

inductive MatchOutcome : Type where
  | matchedArm : Nat → MatchOutcome
  | ubUnreachable : MatchOutcome
  | ubInvalidDiscrRead : MatchOutcome
  | ubInvalidPlaceDeref : MatchOutcome
  | missingArmTrap : MatchOutcome

noncomputable def evalArmsLoop (inMod : Bool) (gOracle : GuardOracle) {t : Ty} (p : RawPlace t)
    (idx : Nat) (arms : List Arm) : MatchOutcome :=
  (arms.foldr
    (fun a rec i =>
      match evalPat inMod gOracle a.pat p with
      | .matched =>
          match a.armGuard with
          | none => .matchedArm i
          | some gid =>
              if gOracle gid then .matchedArm i
              else rec (i + 1)
      | .mismatch => rec (i + 1)
      | .ubNeverRead => .ubUnreachable
      | .ubDiscrRead => .ubInvalidDiscrRead
      | .ubPlaceDeref => .ubInvalidPlaceDeref)
    (fun _ => .missingArmTrap)) idx

noncomputable def evalMatchPlace (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (arms : List Arm) (p : RawPlace t) : MatchOutcome :=
  match arms with
  | [] => .ubUnreachable
  | _ :: _ => evalArmsLoop inMod gOracle p 0 arms

noncomputable def evalArmsLoopRustcStub (inMod : Bool) (gOracle : GuardOracle) {t : Ty} (p : RawPlace t)
    (idx : Nat) (arms : List Arm) : MatchOutcome :=
  (arms.foldr
    (fun a rec i =>
      match evalPatRustcStub inMod gOracle a.pat p with
      | .matched =>
          match a.armGuard with
          | none => .matchedArm i
          | some gid =>
              if gOracle gid then .matchedArm i
              else rec (i + 1)
      | .mismatch => rec (i + 1)
      | .ubNeverRead => .ubUnreachable
      | .ubDiscrRead => .ubInvalidDiscrRead
      | .ubPlaceDeref => .ubInvalidPlaceDeref)
    (fun _ => .missingArmTrap)) idx

noncomputable def evalMatchPlaceRustcStub (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (arms : List Arm) (p : RawPlace t) : MatchOutcome :=
  match arms with
  | [] => .ubUnreachable
  | _ :: _ => evalArmsLoopRustcStub inMod gOracle p 0 arms

theorem Pat.isNeverPattern_pair (p1 p2 : Pat) :
    (Pat.pair p1 p2).isNeverPattern = (p1.isNeverPattern || p2.isNeverPattern) := rfl

theorem Pat.isNeverPattern_or (p1 p2 : Pat) :
    (Pat.or p1 p2).isNeverPattern = (p1.isNeverPattern && p2.isNeverPattern) := rfl

theorem Pat.containsSubGuard_pair (p1 p2 : Pat) :
    (Pat.pair p1 p2).containsSubGuard = (p1.containsSubGuard || p2.containsSubGuard) := rfl

theorem Pat.containsSubGuard_or (p1 p2 : Pat) :
    (Pat.or p1 p2).containsSubGuard = (p1.containsSubGuard || p2.containsSubGuard) := rfl

theorem checkPatWellFormed_some (inMod : Bool) (t : Ty) (p : Pat) :
    checkPatWellFormed inMod (.opt t) (.some p) = checkPatWellFormed inMod t p := rfl

theorem checkPatWellFormed_ok (inMod : Bool) (t1 t2 : Ty) (p : Pat) :
    checkPatWellFormed inMod (.result t1 t2) (.ok p) = checkPatWellFormed inMod t1 p := rfl

theorem checkPatWellFormed_err (inMod : Bool) (t1 t2 : Ty) (p : Pat) :
    checkPatWellFormed inMod (.result t1 t2) (.err p) = checkPatWellFormed inMod t2 p := rfl

theorem checkPatWellFormed_pair (inMod : Bool) (v1 v2 : FieldVis) (t1 t2 : Ty) (p1 p2 : Pat) :
    checkPatWellFormed inMod (.pair v1 t1 v2 t2) (.pair p1 p2) =
      ((if fieldAccessible inMod v1 then checkPatWellFormed inMod t1 p1
        else match p1 with | .wild => true | _ => false) &&
       (if fieldAccessible inMod v2 then checkPatWellFormed inMod t2 p2
        else match p2 with | .wild => true | _ => false)) := rfl

theorem checkPatWellFormed_ref (inMod : Bool) (t : Ty) (p : Pat) :
    checkPatWellFormed inMod (.ref t) (.ref p) = checkPatWellFormed inMod t p := rfl

theorem checkPatWellFormed_or (inMod : Bool) (t : Ty) (p1 p2 : Pat) :
    checkPatWellFormed inMod t (.or p1 p2) =
      (checkPatWellFormed inMod t p1 && checkPatWellFormed inMod t p2) := rfl

theorem checkPatWellFormed_subGuard (inMod : Bool) (t : Ty) (p : Pat) (gid : GuardId) :
    checkPatWellFormed inMod t (.subGuard p gid) = checkPatWellFormed inMod t p := rfl

theorem evalPat_boolLit (inMod : Bool) (gOracle : GuardOracle) (b bv : Bool) :
    evalPat inMod gOracle (.boolLit b) (.valid (.bool bv)) =
      (if b == bv then .matched else .mismatch) := rfl

theorem evalPat_pair_valid (inMod : Bool) (gOracle : GuardOracle)
    {v1 v2 : FieldVis} {t1 t2 : Ty} (p1 p2 : Pat) (x1 : ValidVal t1) (x2 : ValidVal t2) :
    evalPat inMod gOracle (.pair p1 p2) (.valid (@ValidVal.pair v1 v2 t1 t2 x1 x2)) =
      (match evalPat inMod gOracle p1 (.valid x1) with
       | .matched => evalPat inMod gOracle p2 (.valid x2)
       | other => other) := rfl

theorem evalPat_or (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (p1 p2 : Pat) (pl : RawPlace t) :
    evalPat inMod gOracle (.or p1 p2) pl =
      (match evalPat inMod gOracle p1 pl with
       | .mismatch => evalPat inMod gOracle p2 pl
       | other => other) := rfl

theorem evalPat_subGuard (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (p : Pat) (gid : GuardId) (pl : RawPlace t) :
    evalPat inMod gOracle (.subGuard p gid) pl =
      (match evalPat inMod gOracle p pl with
       | .matched => if gOracle gid then .matched else .mismatch
       | other => other) := rfl

theorem evalArmsLoop_cons (inMod : Bool) (gOracle : GuardOracle) {t : Ty}
    (p : RawPlace t) (idx : Nat) (a : Arm) (rest : List Arm) :
    evalArmsLoop inMod gOracle p idx (a :: rest) =
      (match evalPat inMod gOracle a.pat p with
       | .matched =>
           match a.armGuard with
           | none => .matchedArm idx
           | some gid =>
               if gOracle gid then .matchedArm idx
               else evalArmsLoop inMod gOracle p (idx + 1) rest
       | .mismatch => evalArmsLoop inMod gOracle p (idx + 1) rest
       | .ubNeverRead => .ubUnreachable
       | .ubDiscrRead => .ubInvalidDiscrRead
       | .ubPlaceDeref => .ubInvalidPlaceDeref) := rfl

theorem checkPatWellFormed_pair_fields {inMod : Bool} {fv1 fv2 : FieldVis} {t1 t2 : Ty}
    {p1 p2 : Pat}
    (hwf : checkPatWellFormed inMod (.pair fv1 t1 fv2 t2) (.pair p1 p2) = true) :
    checkPatWellFormed inMod t1 p1 = true ∧ checkPatWellFormed inMod t2 p2 = true := by
  rw [checkPatWellFormed_pair, Bool.and_eq_true] at hwf
  constructor
  · cases hacc : fieldAccessible inMod fv1
    · rw [hacc] at hwf
      simp only [Bool.false_eq_true, ↓reduceIte] at hwf
      cases p1 <;> first | rfl | cases hwf.1
    · rw [hacc] at hwf
      simp only [↓reduceIte] at hwf
      exact hwf.1
  · cases hacc : fieldAccessible inMod fv2
    · rw [hacc] at hwf
      simp only [Bool.false_eq_true, ↓reduceIte] at hwf
      cases p2 <;> first | rfl | cases hwf.2
    · rw [hacc] at hwf
      simp only [↓reduceIte] at hwf
      exact hwf.2

/-- On any valid value `v : ValidVal t` and well-formed pattern (`inMod = false`),
    `evalPat` NEVER faults (`ubNeverRead`, `ubDiscrRead`, `ubPlaceDeref`). -/
theorem evalPat_validVal_never_faults :
    ∀ {t : Ty} (p : Pat) (v : ValidVal t) (gOracle : GuardOracle),
      checkPatWellFormed false t p = true →
      evalPat false gOracle p (.valid v) = .matched ∨
      evalPat false gOracle p (.valid v) = .mismatch := by
  intro t p
  induction p generalizing t with
  | wild => intro _ _ _; exact Or.inl rfl
  | never =>
      intro v _ hwf
      exact False.elim (visiblyUninhabited_false_implies_no_validVal t hwf v)
  | unit =>
      intro v _ hwf
      cases v with
      | unit => exact Or.inl rfl
      | _ => cases hwf
  | boolLit b =>
      intro v _ hwf
      cases v with
      | bool bv =>
          rw [evalPat_boolLit]
          cases (b == bv)
          · exact Or.inr rfl
          · exact Or.inl rfl
      | _ => cases hwf
  | none =>
      intro v _ hwf
      cases v with
      | none => exact Or.inl rfl
      | some _ => exact Or.inr rfl
      | _ => cases hwf
  | some p ih =>
      intro v gOracle hwf
      cases v with
      | none => exact Or.inr rfl
      | some inner =>
          rw [checkPatWellFormed_some] at hwf
          exact ih inner gOracle hwf
      | _ => cases hwf
  | ok p ih =>
      intro v gOracle hwf
      cases v with
      | ok inner =>
          rw [checkPatWellFormed_ok] at hwf
          exact ih inner gOracle hwf
      | err _ => exact Or.inr rfl
      | _ => cases hwf
  | err p ih =>
      intro v gOracle hwf
      cases v with
      | ok _ => exact Or.inr rfl
      | err inner =>
          rw [checkPatWellFormed_err] at hwf
          exact ih inner gOracle hwf
      | _ => cases hwf
  | pair p1 p2 ih1 ih2 =>
      intro v gOracle hwf
      cases v with
      | pair v1 v2 =>
          rcases checkPatWellFormed_pair_fields hwf with ⟨hwf1, hwf2⟩
          rw [evalPat_pair_valid]
          cases ih1 v1 gOracle hwf1 with
          | inl hm1 => rw [hm1]; exact ih2 v2 gOracle hwf2
          | inr hmm1 => rw [hmm1]; exact Or.inr rfl
      | _ => cases hwf
  | ref p ih =>
      intro v gOracle hwf
      cases v with
      | refVal inner =>
          rw [checkPatWellFormed_ref] at hwf
          exact ih inner gOracle hwf
      | _ => cases hwf
  | or p1 p2 ih1 ih2 =>
      intro v gOracle hwf
      rw [checkPatWellFormed_or, Bool.and_eq_true] at hwf
      rw [evalPat_or]
      cases ih1 v gOracle hwf.1 with
      | inl hm1 => rw [hm1]; exact Or.inl rfl
      | inr hmm1 => rw [hmm1]; exact ih2 v gOracle hwf.2
  | subGuard p gid ih =>
      intro v gOracle hwf
      rw [checkPatWellFormed_subGuard] at hwf
      rw [evalPat_subGuard]
      cases ih v gOracle hwf with
      | inl hm =>
          rw [hm]
          cases gOracle gid
          · exact Or.inr rfl
          · exact Or.inl rfl
      | inr hmm => rw [hmm]; exact Or.inr rfl

/-- A well-formed never pattern can NEVER match a valid value (`ValidVal t`). -/
theorem neverPattern_cannot_match_validVal :
    ∀ {t : Ty} (p : Pat) (v : ValidVal t) (gOracle : GuardOracle),
      checkPatWellFormed false t p = true →
      p.isNeverPattern = true →
      evalPat false gOracle p (.valid v) = .mismatch := by
  intro t p
  induction p generalizing t with
  | wild => intro _ _ _ hnev; cases hnev
  | unit => intro _ _ _ hnev; cases hnev
  | boolLit _ => intro _ _ _ hnev; cases hnev
  | none => intro _ _ _ hnev; cases hnev
  | never =>
      intro v _ hwf _
      exact False.elim (visiblyUninhabited_false_implies_no_validVal t hwf v)
  | some p ih =>
      intro v gOracle hwf hnev
      cases v with
      | none => rfl
      | some iv =>
          rw [checkPatWellFormed_some] at hwf
          exact ih iv gOracle hwf hnev
      | _ => cases hwf
  | ok p ih =>
      intro v gOracle hwf hnev
      cases v with
      | err _ => rfl
      | ok iv =>
          rw [checkPatWellFormed_ok] at hwf
          exact ih iv gOracle hwf hnev
      | _ => cases hwf
  | err p ih =>
      intro v gOracle hwf hnev
      cases v with
      | ok _ => rfl
      | err iv =>
          rw [checkPatWellFormed_err] at hwf
          exact ih iv gOracle hwf hnev
      | _ => cases hwf
  | pair p1 p2 ih1 ih2 =>
      intro v gOracle hwf hnev
      cases v with
      | pair v1 v2 =>
          rw [Pat.isNeverPattern_pair, Bool.or_eq_true] at hnev
          rcases checkPatWellFormed_pair_fields hwf with ⟨hwf1, hwf2⟩
          rw [evalPat_pair_valid]
          cases hnev with
          | inl hn1 => rw [ih1 v1 gOracle hwf1 hn1]
          | inr hn2 =>
              cases evalPat_validVal_never_faults p1 v1 gOracle hwf1 with
              | inl hm1 => rw [hm1]; exact ih2 v2 gOracle hwf2 hn2
              | inr hmm1 => rw [hmm1]
      | _ => cases hwf
  | ref p ih =>
      intro v gOracle hwf hnev
      cases v with
      | refVal iv =>
          rw [checkPatWellFormed_ref] at hwf
          exact ih iv gOracle hwf hnev
      | _ => cases hwf
  | or p1 p2 ih1 ih2 =>
      intro v gOracle hwf hnev
      rw [Pat.isNeverPattern_or, Bool.and_eq_true] at hnev
      rw [checkPatWellFormed_or, Bool.and_eq_true] at hwf
      rw [evalPat_or]
      rw [ih1 v gOracle hwf.1 hnev.1]
      exact ih2 v gOracle hwf.2 hnev.2
  | subGuard p gid ih =>
      intro v gOracle hwf hnev
      rw [checkPatWellFormed_subGuard] at hwf
      rw [evalPat_subGuard]
      rw [ih v gOracle hwf hnev]

/-! ## Part 5: `rustc_pattern_analysis` Matrix Exhaustiveness Checker -/

structure PlaceCol : Type where
  ty : Ty
  privateUninhabited : Bool
  validity : PlaceValidity
  isScrutinee : Bool

/-- Exact formula from `PlaceInfo::split_column_ctors` (`usefulness.rs:947-960`):
    `can_omit_empty_arms = validity.is_known_valid() || is_toplevel_exception || exhFeat`. -/
def PlaceCol.canOmitEmptyArms (inMod : Bool) (exhFeat : Bool) (col : PlaceCol) : Bool :=
  let isToplevelException := col.isScrutinee && isNoConstructors inMod col.ty
  col.validity.isKnownValid || isToplevelException || exhFeat

structure MatrixRow : Type where
  pats : List Pat
  isUnderGuard : Bool

/-- Lower a pattern for `rustc_pattern_analysis` (`rustc.rs:464-711`). -/
noncomputable def lowerPatForAnalysis : Pat → Pat :=
  Pat.rec .wild .wild .unit .boolLit .none
    (fun _ ih => .some ih)
    (fun _ ih => .ok ih)
    (fun _ ih => .err ih)
    (fun _ _ ih1 ih2 => .pair ih1 ih2)
    (fun _ ih => .ref ih)
    (fun _ _ ih1 ih2 => .or ih1 ih2)
    (fun _ _ ih => ih)

noncomputable def expandOrHead (p : Pat) (tail : List Pat) (guarded : Bool) : List MatrixRow :=
  @Pat.rec (fun _ => List MatrixRow)
    [{ pats := .wild :: tail, isUnderGuard := guarded }]
    [{ pats := .never :: tail, isUnderGuard := guarded }]
    [{ pats := .unit :: tail, isUnderGuard := guarded }]
    (fun b => [{ pats := .boolLit b :: tail, isUnderGuard := guarded }])
    [{ pats := .none :: tail, isUnderGuard := guarded }]
    (fun p _ => [{ pats := .some p :: tail, isUnderGuard := guarded }])
    (fun p _ => [{ pats := .ok p :: tail, isUnderGuard := guarded }])
    (fun p _ => [{ pats := .err p :: tail, isUnderGuard := guarded }])
    (fun p1 p2 _ _ => [{ pats := .pair p1 p2 :: tail, isUnderGuard := guarded }])
    (fun p _ => [{ pats := .ref p :: tail, isUnderGuard := guarded }])
    (fun _ _ ih1 ih2 => ih1 ++ ih2)
    (fun p g _ => [{ pats := .subGuard p g :: tail, isUnderGuard := guarded }])
    p

noncomputable def expandOrColumn (rows : List MatrixRow) : List MatrixRow :=
  rows.foldr
    (fun r acc =>
      match r.pats with
      | [] => r :: acc
      | h :: t => expandOrHead h t r.isUnderGuard ++ acc)
    []

inductive SpecCtor : Type where
  | skipPrivateUninhabited : SpecCtor
  | unit : SpecCtor
  | boolLit : Bool → SpecCtor
  | foreignExt : SpecCtor
  | none : SpecCtor
  | some : SpecCtor
  | ok : SpecCtor
  | err : SpecCtor
  | pair : SpecCtor
  | ref : SpecCtor
  | opaqueMissing : SpecCtor

def specializePat (c : SpecCtor) (p : Pat) : Option (List Pat) :=
  match c, p with
  | .skipPrivateUninhabited, _ => some []
  | .unit, .wild => some []
  | .unit, .unit => some []
  | .boolLit _, .wild => some []
  | .boolLit b1, .boolLit b2 => if b1 == b2 then some [] else none
  | .foreignExt, .wild => some []
  | .none, .wild => some []
  | .none, .none => some []
  | .some, .wild => some [.wild]
  | .some, .some sub => some [sub]
  | .ok, .wild => some [.wild]
  | .ok, .ok sub => some [sub]
  | .err, .wild => some [.wild]
  | .err, .err sub => some [sub]
  | .pair, .wild => some [.wild, .wild]
  | .pair, .pair p1 p2 => some [p1, p2]
  | .ref, .wild => some [.wild]
  | .ref, .ref sub => some [sub]
  | .opaqueMissing, .wild => some []
  | _, _ => none

def specializeRows (c : SpecCtor) (rows : List MatrixRow) : List MatrixRow :=
  rows.foldr
    (fun r acc =>
      match r.pats with
      | [] => acc
      | h :: t =>
          match specializePat c h with
          | some sub => { pats := sub ++ t, isUnderGuard := r.isUnderGuard } :: acc
          | none => acc)
    []

/-- Pattern-matching on `c` FIRST ensures zero-arity constructors reduce
    definitionally to `[]` for any abstract `col`. -/
noncomputable def specializeCol (inMod : Bool) (col : PlaceCol) (c : SpecCtor) : List PlaceCol :=
  match c, col.ty with
  | .skipPrivateUninhabited, _ => []
  | .unit, _ => []
  | .boolLit _, _ => []
  | .foreignExt, _ => []
  | .none, _ => []
  | .opaqueMissing, _ => []
  | .some, .opt t =>
      [{ ty := t, privateUninhabited := false, validity := col.validity, isScrutinee := false }]
  | .ok, .result t1 _ =>
      [{ ty := t1, privateUninhabited := false, validity := col.validity, isScrutinee := false }]
  | .err, .result _ t2 =>
      [{ ty := t2, privateUninhabited := false, validity := col.validity, isScrutinee := false }]
  | .pair, .pair v1 t1 v2 t2 =>
      let skip1 := visiblyUninhabited inMod t1 && !fieldAccessible inMod v1
      let skip2 := visiblyUninhabited inMod t2 && !fieldAccessible inMod v2
      [ { ty := t1, privateUninhabited := skip1, validity := col.validity, isScrutinee := false }
      , { ty := t2, privateUninhabited := skip2, validity := col.validity, isScrutinee := false } ]
  | .ref, .ref t =>
      [{ ty := t, privateUninhabited := false, validity := col.validity.specialize true, isScrutinee := false }]
  | _, _ => []

/-- Enumerate the constructors that MUST be covered for `col` to be exhaustive
    (`constructor.rs:1044-1203` & `usefulness.rs:924-1000`). -/
noncomputable def requiredCtors (inMod : Bool) (exhFeat : Bool) (col : PlaceCol) : List SpecCtor :=
  if col.privateUninhabited then
    [.skipPrivateUninhabited]
  else
    let canOmit := col.canOmitEmptyArms inMod exhFeat
    match col.ty with
    | .never =>
        if canOmit then [] else [.opaqueMissing]
    | .emptyEnum isForeignNonExh =>
        if isForeignNonExh && !inMod then
          [.foreignExt]
        else
          if canOmit then [] else [.opaqueMissing]
    | .unit => [.unit]
    | .bool => [.boolLit true, .boolLit false]
    | .opt t =>
        let someEmpty := visiblyUninhabited inMod t
        if someEmpty && canOmit then [.none] else [.none, .some]
    | .result t1 t2 =>
        let okEmpty := visiblyUninhabited inMod t1
        let errEmpty := visiblyUninhabited inMod t2
        let okList := if okEmpty && canOmit then [] else [.ok]
        let errList := if errEmpty && canOmit then [] else [.err]
        okList ++ errList
    | .pair v1 t1 v2 t2 =>
        let emptyStruct := visiblyUninhabited inMod (.pair v1 t1 v2 t2)
        if emptyStruct && canOmit then [] else [.pair]
    | .ref _ => [.ref]
    | .rawPtr _ => [.opaqueMissing]
    | .union _ _ => [.opaqueMissing]

/-- Total fuel-indexed pattern matrix exhaustiveness checker mirroring
    `compute_exhaustiveness_and_usefulness` (`usefulness.rs:1698-1790`). -/
noncomputable def checkMatrixFuel (inMod : Bool) (exhFeat : Bool)
    (fuel : Nat) (cols : List PlaceCol) (rows : List MatrixRow) : Bool :=
  @Nat.rec (fun _ => List PlaceCol → List MatrixRow → Bool)
    (fun _ _ => false)
    (fun _ rec cols rows =>
      match cols with
      | [] => rows.any (fun r => !r.isUnderGuard)
      | col :: restCols =>
          let expanded := expandOrColumn rows
          (requiredCtors inMod exhFeat col).all (fun c =>
            rec (specializeCol inMod col c ++ restCols) (specializeRows c expanded)))
    fuel cols rows

noncomputable def colsFuel (cols : List PlaceCol) : Nat :=
  cols.foldr (fun c acc => Ty.size c.ty + acc + 1) 1

noncomputable def checkMatchExhaustive (inMod : Bool) (exhFeat : Bool) (gMode : GuardLoweringMode)
    (t : Ty) (scrutVal : PlaceValidity) (arms : List Arm) : Bool :=
  let initCol : PlaceCol :=
    { ty := t, privateUninhabited := false, validity := scrutVal, isScrutinee := true }
  let rows : List MatrixRow :=
    arms.map (fun a =>
      { pats := [lowerPatForAnalysis a.pat]
      , isUnderGuard := armCountsAsGuarded gMode a })
  checkMatrixFuel inMod exhFeat (colsFuel [initCol]) [initCol] rows

/-! ## Part 6: Full Inductive Soundness Proof of Pattern Matrix Exhaustiveness -/

inductive ValStack : List PlaceCol → Type where
  | nil : ValStack []
  | cons : {col : PlaceCol} → {cols : List PlaceCol} →
      ValidVal col.ty → ValStack cols → ValStack (col :: cols)

noncomputable def loweredMatchesVal {t : Ty} (p : Pat) (v : ValidVal t) : Bool :=
  @Pat.rec (fun _ => {t : Ty} → ValidVal t → Bool)
    (fun {_} _ => true)
    (fun {_} _ => true)
    (fun {t} v => match t, v with | .unit, .unit => true | _, _ => false)
    (fun b {t} v => match t, v with | .bool, .bool bv => b == bv | _, _ => false)
    (fun {t} v => match t, v with | .opt _, .none => true | _, _ => false)
    (fun _ ih {t} v => match t, v with | .opt _, .some iv => ih iv | _, _ => false)
    (fun _ ih {t} v => match t, v with | .result _ _, .ok iv => ih iv | _, _ => false)
    (fun _ ih {t} v => match t, v with | .result _ _, .err iv => ih iv | _, _ => false)
    (fun _ _ ih1 ih2 {t} v => match t, v with
      | .pair _ _ _ _, .pair v1 v2 => ih1 v1 && ih2 v2
      | _, _ => false)
    (fun _ ih {t} v => match t, v with | .ref _, .refVal iv => ih iv | _, _ => false)
    (fun _ _ ih1 ih2 {_} v => ih1 v || ih2 v)
    (fun _ _ ih {_} v => ih v)
    p t v

noncomputable def rowMatchesStack {cols : List PlaceCol} (pats : List Pat) (vs : ValStack cols) : Bool :=
  @ValStack.rec (fun _ _ => List Pat → Bool)
    (fun ps => match ps with | [] => true | _ => false)
    (fun {_ _} v _ ih ps => match ps with | p :: rest => loweredMatchesVal p v && ih rest | [] => false)
    cols vs pats

theorem rowMatchesStack_cons {col : PlaceCol} {cols : List PlaceCol}
    (p : Pat) (ps : List Pat) (v : ValidVal col.ty) (vs : ValStack cols) :
    rowMatchesStack (p :: ps) (.cons v vs) = (loweredMatchesVal p v && rowMatchesStack ps vs) := rfl

theorem rowMatchesStack_singleton {col : PlaceCol} (p : Pat) (v : ValidVal col.ty) :
    rowMatchesStack [p] (.cons v .nil) = loweredMatchesVal p v := by
  change (loweredMatchesVal p v && true) = loweredMatchesVal p v
  exact Bool.and_true _

def patRespectsPrivacy (inMod : Bool) (t : Ty) (p : Pat) : Prop :=
  @Pat.rec (fun _ => Ty → Prop)
    (fun _ => True)
    (fun _ => True)
    (fun _ => True)
    (fun _ _ => True)
    (fun _ => True)
    (fun _ ih t => match t with | .opt inner => ih inner | _ => True)
    (fun _ ih t => match t with | .result t1 _ => ih t1 | _ => True)
    (fun _ ih t => match t with | .result _ t2 => ih t2 | _ => True)
    (fun p1 p2 ih1 ih2 t => match t with
      | .pair v1 t1 v2 t2 =>
          (if fieldAccessible inMod v1 then ih1 t1 else p1 = .wild) ∧
          (if fieldAccessible inMod v2 then ih2 t2 else p2 = .wild)
      | _ => True)
    (fun _ ih t => match t with | .ref inner => ih inner | _ => True)
    (fun _ _ ih1 ih2 t => ih1 t ∧ ih2 t)
    (fun _ _ ih t => ih t)
    p t

def rowColsWf (inMod : Bool) (cols : List PlaceCol) (pats : List Pat) : Prop :=
  @List.rec PlaceCol (fun _ => List Pat → Prop)
    (fun ps => match ps with | [] => True | _ => False)
    (fun col _ ih ps =>
      match ps with
      | p :: rest =>
          (col.privateUninhabited = true → p = .wild) ∧
          patRespectsPrivacy inMod col.ty p ∧
          ih rest
      | [] => False)
    cols pats

theorem expandOrHead_or (p1 p2 : Pat) (tl : List Pat) (g : Bool) :
    expandOrHead (.or p1 p2) tl g = expandOrHead p1 tl g ++ expandOrHead p2 tl g := rfl

theorem expandOrColumn_cons (r : MatrixRow) (rs : List MatrixRow) :
    expandOrColumn (r :: rs) =
      (match r.pats with
       | [] => r :: expandOrColumn rs
       | h :: t => expandOrHead h t r.isUnderGuard ++ expandOrColumn rs) := rfl

theorem specializeRows_cons (c : SpecCtor) (r : MatrixRow) (rs : List MatrixRow) :
    specializeRows c (r :: rs) =
      (match r.pats with
       | [] => specializeRows c rs
       | h :: t =>
           match specializePat c h with
           | some sub => { pats := sub ++ t, isUnderGuard := r.isUnderGuard } :: specializeRows c rs
           | none => specializeRows c rs) := rfl

theorem checkMatrixFuel_succ_nil (inMod exhFeat : Bool) (n : Nat) (rows : List MatrixRow) :
    checkMatrixFuel inMod exhFeat (n + 1) [] rows = rows.any (fun r => !r.isUnderGuard) := rfl

theorem checkMatrixFuel_succ_cons (inMod exhFeat : Bool) (n : Nat)
    (col : PlaceCol) (restCols : List PlaceCol) (rows : List MatrixRow) :
    checkMatrixFuel inMod exhFeat (n + 1) (col :: restCols) rows =
      (requiredCtors inMod exhFeat col).all (fun c =>
        checkMatrixFuel inMod exhFeat n
          (specializeCol inMod col c ++ restCols)
          (specializeRows c (expandOrColumn rows))) := rfl

theorem loweredMatchesVal_boolLit (b bv : Bool) :
    loweredMatchesVal (.boolLit b) (.bool bv) = (b == bv) := rfl

theorem loweredMatchesVal_some {t : Ty} (p : Pat) (v : ValidVal t) :
    loweredMatchesVal (.some p) (.some v) = loweredMatchesVal p v := rfl

theorem loweredMatchesVal_ok {t1 t2 : Ty} (p : Pat) (v : ValidVal t1) :
    loweredMatchesVal (.ok p) (@ValidVal.ok t1 t2 v) = loweredMatchesVal p v := rfl

theorem loweredMatchesVal_err {t1 t2 : Ty} (p : Pat) (v : ValidVal t2) :
    loweredMatchesVal (.err p) (@ValidVal.err t1 t2 v) = loweredMatchesVal p v := rfl

theorem loweredMatchesVal_pair {v1 v2 : FieldVis} {t1 t2 : Ty}
    (p1 p2 : Pat) (x1 : ValidVal t1) (x2 : ValidVal t2) :
    loweredMatchesVal (.pair p1 p2) (@ValidVal.pair v1 v2 t1 t2 x1 x2) =
      (loweredMatchesVal p1 x1 && loweredMatchesVal p2 x2) := rfl

theorem loweredMatchesVal_ref {t : Ty} (p : Pat) (v : ValidVal t) :
    loweredMatchesVal (.ref p) (.refVal v) = loweredMatchesVal p v := rfl

theorem loweredMatchesVal_or {t : Ty} (p1 p2 : Pat) (v : ValidVal t) :
    loweredMatchesVal (.or p1 p2) v = (loweredMatchesVal p1 v || loweredMatchesVal p2 v) := rfl

theorem patRespectsPrivacy_pair (inMod : Bool) (v1 v2 : FieldVis) (t1 t2 : Ty) (p1 p2 : Pat) :
    patRespectsPrivacy inMod (.pair v1 t1 v2 t2) (.pair p1 p2) =
      ((if fieldAccessible inMod v1 then patRespectsPrivacy inMod t1 p1 else p1 = .wild) ∧
       (if fieldAccessible inMod v2 then patRespectsPrivacy inMod t2 p2 else p2 = .wild)) := rfl

theorem rowColsWf_nil (inMod : Bool) : rowColsWf inMod [] [] = True := rfl

theorem rowColsWf_cons (inMod : Bool) (col : PlaceCol) (cols : List PlaceCol)
    (p : Pat) (ps : List Pat) :
    rowColsWf inMod (col :: cols) (p :: ps) =
      ((col.privateUninhabited = true → p = .wild) ∧
       patRespectsPrivacy inMod col.ty p ∧
       rowColsWf inMod cols ps) := rfl

def matrixWf (inMod : Bool) (cols : List PlaceCol) (rows : List MatrixRow) : Prop :=
  ∀ r, r ∈ rows → rowColsWf inMod cols r.pats

def ctorValidForCol (col : PlaceCol) : SpecCtor → Prop
  | .skipPrivateUninhabited => True
  | .unit => True
  | .boolLit _ => True
  | .foreignExt => True
  | .none => True
  | .opaqueMissing => True
  | .some => ∃ t, col.ty = .opt t
  | .ok => ∃ t1 t2, col.ty = .result t1 t2
  | .err => ∃ t1 t2, col.ty = .result t1 t2
  | .pair => ∃ v1 t1 v2 t2, col.ty = .pair v1 t1 v2 t2
  | .ref => ∃ t, col.ty = .ref t

theorem checkPatWellFormed_implies_loweredPrivacy (inMod : Bool) :
    ∀ (t : Ty) (p : Pat),
      checkPatWellFormed inMod t p = true →
      patRespectsPrivacy inMod t (lowerPatForAnalysis p) := by
  intro t p
  induction p generalizing t with
  | wild => intro _; trivial
  | never => intro _; trivial
  | unit => intro _; cases t <;> trivial
  | boolLit _ => intro _; cases t <;> trivial
  | none => intro _; cases t <;> trivial
  | some p ih =>
      intro h
      cases t with
      | opt inner => exact ih inner h
      | _ => cases h
  | ok p ih =>
      intro h
      cases t with
      | result t1 _ => exact ih t1 h
      | _ => cases h
  | err p ih =>
      intro h
      cases t with
      | result _ t2 => exact ih t2 h
      | _ => cases h
  | pair p1 p2 ih1 ih2 =>
      intro h
      cases t with
      | pair v1 t1 v2 t2 =>
          rw [checkPatWellFormed_pair, Bool.and_eq_true] at h
          change (if fieldAccessible inMod v1 then patRespectsPrivacy inMod t1 (lowerPatForAnalysis p1)
                  else lowerPatForAnalysis p1 = .wild) ∧
                 (if fieldAccessible inMod v2 then patRespectsPrivacy inMod t2 (lowerPatForAnalysis p2)
                  else lowerPatForAnalysis p2 = .wild)
          constructor
          · cases hacc : fieldAccessible inMod v1
            · rw [hacc] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases p1 <;> first | rfl | cases h.1
            · rw [hacc] at h
              simp only [↓reduceIte] at h ⊢
              exact ih1 t1 h.1
          · cases hacc : fieldAccessible inMod v2
            · rw [hacc] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
              cases p2 <;> first | rfl | cases h.2
            · rw [hacc] at h
              simp only [↓reduceIte] at h ⊢
              exact ih2 t2 h.2
      | _ => cases h
  | ref p ih =>
      intro h
      cases t with
      | ref inner => exact ih inner h
      | _ => cases h
  | or p1 p2 ih1 ih2 =>
      intro h
      rw [checkPatWellFormed_or, Bool.and_eq_true] at h
      exact ⟨ih1 t h.1, ih2 t h.2⟩
  | subGuard p _ ih =>
      intro h
      exact ih t h

theorem list_all_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hall : xs.all p = true) (hmem : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      cases hmem with
      | head => exact hall.1
      | tail _ ht => exact ih hall.2 ht

theorem list_any_exists {α : Type} {p : α → Bool} {xs : List α}
    (hany : xs.any p = true) : ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => cases hany
  | cons y ys ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hany
      cases hany with
      | inl hy => exact ⟨y, List.Mem.head _, hy⟩
      | inr hys =>
          rcases ih hys with ⟨x, hmem, hpx⟩
          exact ⟨x, List.Mem.tail _ hmem, hpx⟩

theorem expandOrHead_wf {inMod : Bool} {col : PlaceCol} {cols : List PlaceCol}
    (p : Pat) (tl : List Pat) (g : Bool)
    (hwf : rowColsWf inMod (col :: cols) (p :: tl)) :
    ∀ r, r ∈ expandOrHead p tl g → rowColsWf inMod (col :: cols) r.pats := by
  induction p with
  | or p1 p2 ih1 ih2 =>
      rcases hwf with ⟨hpriv, ⟨hp1, hp2⟩, htl⟩
      intro r hmem
      rw [expandOrHead_or, List.mem_append] at hmem
      have hprivFalse : col.privateUninhabited = true → False := by
        intro hp; cases hpriv hp
      cases hmem with
      | inl h1 => exact ih1 ⟨fun hp => False.elim (hprivFalse hp), hp1, htl⟩ r h1
      | inr h2 => exact ih2 ⟨fun hp => False.elim (hprivFalse hp), hp2, htl⟩ r h2
  | wild | never | unit | boolLit _ | none | some _ | ok _ | err _
  | pair _ _ | ref _ | subGuard _ _ =>
      intro r hmem
      change r ∈ [{ pats := _ :: tl, isUnderGuard := g }] at hmem
      rw [List.mem_singleton] at hmem
      subst hmem
      exact hwf

theorem expandOrColumn_wf {inMod : Bool} {col : PlaceCol} {cols : List PlaceCol}
    (rows : List MatrixRow) (hwf : matrixWf inMod (col :: cols) rows) :
    matrixWf inMod (col :: cols) (expandOrColumn rows) := by
  induction rows with
  | nil => intro r hm; cases hm
  | cons row rest ih =>
      intro r hmem
      have hrow : rowColsWf inMod (col :: cols) row.pats := hwf row (List.Mem.head _)
      have hrest : matrixWf inMod (col :: cols) rest :=
        fun x hx => hwf x (List.Mem.tail _ hx)
      rw [expandOrColumn_cons] at hmem
      cases hp : row.pats with
      | nil => rw [hp] at hrow; cases hrow
      | cons hd tl =>
          rw [hp] at hrow hmem
          dsimp only at hmem
          rw [List.mem_append] at hmem
          cases hmem with
          | inl h1 => exact expandOrHead_wf hd tl row.isUnderGuard hrow r h1
          | inr h2 => exact ih hrest r h2

theorem specializeRows_wf {inMod : Bool} {col : PlaceCol} {cols : List PlaceCol}
    (c : SpecCtor) (hvalid : ctorValidForCol col c) (rows : List MatrixRow)
    (hwf : matrixWf inMod (col :: cols) rows) :
    matrixWf inMod (specializeCol inMod col c ++ cols) (specializeRows c rows) := by
  induction rows with
  | nil => intro r hm; cases hm
  | cons row rest ih =>
      intro r hmem
      have hrow : rowColsWf inMod (col :: cols) row.pats := hwf row (List.Mem.head _)
      have hrest : matrixWf inMod (col :: cols) rest :=
        fun x hx => hwf x (List.Mem.tail _ hx)
      rw [specializeRows_cons] at hmem
      cases hp : row.pats with
      | nil => rw [hp] at hrow; cases hrow
      | cons hd tl =>
          rw [hp] at hrow hmem
          dsimp only at hmem
          rcases hrow with ⟨_, hprivPat, htl⟩
          cases hs : specializePat c hd with
          | none =>
              rw [hs] at hmem
              exact ih hrest r hmem
          | some sub =>
              rw [hs] at hmem
              cases hmem with
              | tail _ ht => exact ih hrest r ht
              | head =>
                  cases c with
                  | skipPrivateUninhabited =>
                      simp only [specializePat, Option.some.injEq] at hs
                      subst hs
                      exact htl
                  | unit =>
                      cases hd <;> simp only [specializePat, Option.some.injEq] at hs <;> try cases hs
                      all_goals exact htl
                  | boolLit b =>
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs; exact htl
                      | boolLit b2 =>
                          simp only [specializePat] at hs
                          cases hcmp : (b == b2)
                          · rw [hcmp] at hs; cases hs
                          · rw [hcmp] at hs
                            simp only [↓reduceIte, Option.some.injEq] at hs
                            subst hs; exact htl
                      | _ => cases hs
                  | foreignExt =>
                      cases hd <;> simp only [specializePat, Option.some.injEq] at hs <;> try cases hs
                      exact htl
                  | none =>
                      cases hd <;> simp only [specializePat, Option.some.injEq] at hs <;> try cases hs
                      all_goals exact htl
                  | opaqueMissing =>
                      cases hd <;> simp only [specializePat, Option.some.injEq] at hs <;> try cases hs
                      exact htl
                  | some =>
                      rcases hvalid with ⟨inner, hty⟩
                      rw [hty] at hprivPat
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), trivial, htl⟩
                      | some p =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), hprivPat, htl⟩
                      | _ => cases hs
                  | ok =>
                      rcases hvalid with ⟨t1, t2, hty⟩
                      rw [hty] at hprivPat
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), trivial, htl⟩
                      | ok p =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), hprivPat, htl⟩
                      | _ => cases hs
                  | err =>
                      rcases hvalid with ⟨t1, t2, hty⟩
                      rw [hty] at hprivPat
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), trivial, htl⟩
                      | err p =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), hprivPat, htl⟩
                      | _ => cases hs
                  | ref =>
                      rcases hvalid with ⟨inner, hty⟩
                      rw [hty] at hprivPat
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), trivial, htl⟩
                      | ref p =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨(fun hc => by cases hc), hprivPat, htl⟩
                      | _ => cases hs
                  | pair =>
                      rcases hvalid with ⟨v1, t1, v2, t2, hty⟩
                      rw [hty] at hprivPat
                      cases hd with
                      | wild =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          exact ⟨fun _ => trivial, trivial, fun _ => trivial, trivial, htl⟩
                      | pair p1 p2 =>
                          simp only [specializePat, Option.some.injEq] at hs
                          subst hs
                          simp only [specializeCol, hty, List.cons_append, List.nil_append, rowColsWf_cons]
                          rcases hprivPat with ⟨hp1, hp2⟩
                          refine ⟨?_, ?_, ?_, ?_, htl⟩
                          · intro hskip1
                            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hskip1
                            rw [hskip1.2] at hp1
                            exact hp1
                          · cases hacc1 : fieldAccessible inMod v1
                            · rw [hacc1] at hp1
                              simp only [Bool.false_eq_true, ↓reduceIte] at hp1
                              subst hp1; trivial
                            · rw [hacc1] at hp1
                              simp only [↓reduceIte] at hp1
                              exact hp1
                          · intro hskip2
                            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hskip2
                            rw [hskip2.2] at hp2
                            exact hp2
                          · cases hacc2 : fieldAccessible inMod v2
                            · rw [hacc2] at hp2
                              simp only [Bool.false_eq_true, ↓reduceIte] at hp2
                              subst hp2; trivial
                            · rw [hacc2] at hp2
                              simp only [↓reduceIte] at hp2
                              exact hp2
                      | _ => cases hs

theorem expandOrHead_sound {col : PlaceCol} {cols : List PlaceCol}
    (p : Pat) (tail : List Pat) (g : Bool) (v : ValidVal col.ty) (vs : ValStack cols)
    {r : MatrixRow} (hmem : r ∈ expandOrHead p tail g)
    (hm : rowMatchesStack r.pats (.cons v vs) = true) :
    r.isUnderGuard = g ∧ rowMatchesStack (p :: tail) (.cons v vs) = true := by
  induction p generalizing r with
  | or p1 p2 ih1 ih2 =>
      rw [expandOrHead_or, List.mem_append] at hmem
      cases hmem with
      | inl h1 =>
          rcases ih1 h1 hm with ⟨hg, hrow⟩
          rw [rowMatchesStack_cons, Bool.and_eq_true] at hrow
          rw [rowMatchesStack_cons, loweredMatchesVal_or, Bool.and_eq_true, Bool.or_eq_true]
          exact ⟨hg, Or.inl hrow.1, hrow.2⟩
      | inr h2 =>
          rcases ih2 h2 hm with ⟨hg, hrow⟩
          rw [rowMatchesStack_cons, Bool.and_eq_true] at hrow
          rw [rowMatchesStack_cons, loweredMatchesVal_or, Bool.and_eq_true, Bool.or_eq_true]
          exact ⟨hg, Or.inr hrow.1, hrow.2⟩
  | wild | never | unit | boolLit _ | none | some _ | ok _ | err _
  | pair _ _ | ref _ | subGuard _ _ =>
      change r ∈ [{ pats := _ :: tail, isUnderGuard := g }] at hmem
      rw [List.mem_singleton] at hmem
      subst hmem
      exact ⟨rfl, hm⟩

theorem expandOrColumn_sound (col : PlaceCol) {cols : List PlaceCol}
    (rows : List MatrixRow) (v : ValidVal col.ty) (vs : ValStack cols)
    {r : MatrixRow} (hmem : r ∈ expandOrColumn rows)
    (hm : rowMatchesStack r.pats (.cons v vs) = true) :
    ∃ r0, r0 ∈ rows ∧ r0.isUnderGuard = r.isUnderGuard ∧
      rowMatchesStack r0.pats (.cons v vs) = true := by
  induction rows with
  | nil => cases hmem
  | cons row rest ih =>
      rw [expandOrColumn_cons] at hmem
      cases hp : row.pats with
      | nil =>
          rw [hp] at hmem
          dsimp only at hmem
          cases hmem with
          | head => rw [hp] at hm; cases hm
          | tail _ ht =>
              rcases ih ht with ⟨r0, hmem0, hg0, hm0⟩
              exact ⟨r0, List.Mem.tail _ hmem0, hg0, hm0⟩
      | cons hd tl =>
          rw [hp] at hmem
          dsimp only at hmem
          rw [List.mem_append] at hmem
          cases hmem with
          | inl hhead =>
              rcases expandOrHead_sound hd tl row.isUnderGuard v vs hhead hm with ⟨hg, hrow⟩
              exact ⟨row, List.Mem.head _, hg.symm, by rw [hp]; exact hrow⟩
          | inr hrest =>
              rcases ih hrest with ⟨r0, hmem0, hg0, hm0⟩
              exact ⟨r0, List.Mem.tail _ hmem0, hg0, hm0⟩

theorem specializeRows_sound {inMod : Bool} (col : PlaceCol) {cols : List PlaceCol}
    (c : SpecCtor) (rows : List MatrixRow)
    (v : ValidVal col.ty) (vs : ValStack cols)
    (subStack : ValStack (specializeCol inMod col c ++ cols))
    (hSpec : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
      row ∈ rows →
      row.pats = hd :: tl →
      specializePat c hd = some sub →
      rowMatchesStack (sub ++ tl) subStack = true →
      loweredMatchesVal hd v = true ∧ rowMatchesStack tl vs = true)
    {r : MatrixRow} (hmem : r ∈ specializeRows c rows)
    (hm : rowMatchesStack r.pats subStack = true) :
    ∃ r0, r0 ∈ rows ∧ r0.isUnderGuard = r.isUnderGuard ∧
      rowMatchesStack r0.pats (.cons v vs) = true := by
  induction rows with
  | nil => cases hmem
  | cons row rest ih =>
      have ih' : r ∈ specializeRows c rest →
          ∃ r0, r0 ∈ rest ∧ r0.isUnderGuard = r.isUnderGuard ∧
            rowMatchesStack r0.pats (.cons v vs) = true :=
        ih (fun r1 hd tl sub hm1 => hSpec r1 hd tl sub (List.Mem.tail _ hm1))
      rw [specializeRows_cons] at hmem
      cases hp : row.pats with
      | nil =>
          rw [hp] at hmem
          rcases ih' hmem with ⟨r0, h0, hg0, hm0⟩
          exact ⟨r0, List.Mem.tail _ h0, hg0, hm0⟩
      | cons hd tl =>
          rw [hp] at hmem
          dsimp only at hmem
          cases hs : specializePat c hd with
          | none =>
              rw [hs] at hmem
              rcases ih' hmem with ⟨r0, h0, hg0, hm0⟩
              exact ⟨r0, List.Mem.tail _ h0, hg0, hm0⟩
          | some sub =>
              rw [hs] at hmem
              cases hmem with
              | head =>
                  rcases hSpec row hd tl sub (List.Mem.head _) hp hs hm with ⟨hhd, htl⟩
                  refine ⟨row, List.Mem.head _, rfl, ?_⟩
                  rw [hp, rowMatchesStack_cons, Bool.and_eq_true]
                  exact ⟨hhd, htl⟩
              | tail _ ht =>
                  rcases ih' ht with ⟨r0, h0, hg0, hm0⟩
                  exact ⟨r0, List.Mem.tail _ h0, hg0, hm0⟩

theorem evalPat_of_loweredMatchesVal :
    ∀ {t : Ty} (p : Pat) (v : ValidVal t) (gOracle : GuardOracle),
      checkPatWellFormed false t p = true →
      p.containsSubGuard = false →
      loweredMatchesVal (lowerPatForAnalysis p) v = true →
      evalPat false gOracle p (.valid v) = .matched := by
  intro t p
  induction p generalizing t with
  | wild => intro _ _ _ _ _; rfl
  | never =>
      intro v _ hwf _ _
      exact False.elim (visiblyUninhabited_false_implies_no_validVal t hwf v)
  | unit =>
      intro v _ hwf _ _
      cases v with
      | unit => rfl
      | _ => cases hwf
  | boolLit b =>
      intro v _ hwf _ hm
      cases v with
      | bool bv =>
          change (b == bv) = true at hm
          rw [evalPat_boolLit, hm]; rfl
      | _ => cases hwf
  | none =>
      intro v _ hwf _ hm
      cases v with
      | none => rfl
      | some _ => cases hm
      | _ => cases hwf
  | some p ih =>
      intro v gOracle hwf hng hm
      cases v with
      | none => cases hm
      | some iv =>
          rw [checkPatWellFormed_some] at hwf
          change loweredMatchesVal (lowerPatForAnalysis p) iv = true at hm
          exact ih iv gOracle hwf hng hm
      | _ => cases hwf
  | ok p ih =>
      intro v gOracle hwf hng hm
      cases v with
      | ok iv =>
          rw [checkPatWellFormed_ok] at hwf
          change loweredMatchesVal (lowerPatForAnalysis p) iv = true at hm
          exact ih iv gOracle hwf hng hm
      | err _ => cases hm
      | _ => cases hwf
  | err p ih =>
      intro v gOracle hwf hng hm
      cases v with
      | ok _ => cases hm
      | err iv =>
          rw [checkPatWellFormed_err] at hwf
          change loweredMatchesVal (lowerPatForAnalysis p) iv = true at hm
          exact ih iv gOracle hwf hng hm
      | _ => cases hwf
  | pair p1 p2 ih1 ih2 =>
      intro v gOracle hwf hng hm
      cases v with
      | pair v1 v2 =>
          rw [Pat.containsSubGuard_pair, Bool.or_eq_false_iff] at hng
          change (loweredMatchesVal (lowerPatForAnalysis p1) v1 &&
                  loweredMatchesVal (lowerPatForAnalysis p2) v2) = true at hm
          rw [Bool.and_eq_true] at hm
          rcases checkPatWellFormed_pair_fields hwf with ⟨hwf1, hwf2⟩
          rw [evalPat_pair_valid]
          rw [ih1 v1 gOracle hwf1 hng.1 hm.1]
          exact ih2 v2 gOracle hwf2 hng.2 hm.2
      | _ => cases hwf
  | ref p ih =>
      intro v gOracle hwf hng hm
      cases v with
      | refVal iv =>
          rw [checkPatWellFormed_ref] at hwf
          change loweredMatchesVal (lowerPatForAnalysis p) iv = true at hm
          exact ih iv gOracle hwf hng hm
      | _ => cases hwf
  | or p1 p2 ih1 ih2 =>
      intro v gOracle hwf hng hm
      rw [checkPatWellFormed_or, Bool.and_eq_true] at hwf
      rw [Pat.containsSubGuard_or, Bool.or_eq_false_iff] at hng
      change (loweredMatchesVal (lowerPatForAnalysis p1) v ||
              loweredMatchesVal (lowerPatForAnalysis p2) v) = true at hm
      rw [Bool.or_eq_true] at hm
      rw [evalPat_or]
      cases hm with
      | inl hm1 => rw [ih1 v gOracle hwf.1 hng.1 hm1]
      | inr hm2 =>
          cases evalPat_validVal_never_faults p1 v gOracle hwf.1 with
          | inl h1 => rw [h1]
          | inr h1 => rw [h1]; exact ih2 v gOracle hwf.2 hng.2 hm2
  | subGuard _ _ =>
      intro _ _ _ hng _
      cases hng

/-- Core inductive soundness theorem for `checkMatrixFuel`:
    If `checkMatrixFuel false exhFeat fuel cols rows = true` and `matrixWf false cols rows`,
    then for EVERY valid value stack `vs : ValStack cols`, there exists an
    UN-GUARDED row `r ∈ rows` (`r.isUnderGuard = false`) matching `vs`. -/
theorem checkMatrixFuel_sound_valid :
    ∀ (fuel : Nat) (exhFeat : Bool) (cols : List PlaceCol) (rows : List MatrixRow),
      matrixWf false cols rows →
      checkMatrixFuel false exhFeat fuel cols rows = true →
      ∀ (vs : ValStack cols),
        ∃ r, r ∈ rows ∧ r.isUnderGuard = false ∧ rowMatchesStack r.pats vs = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ _ _ _ hCheck
      cases hCheck
  | succ n ih =>
      intro exhFeat cols rows hwf hCheck vs
      cases cols with
      | nil =>
          cases vs with
          | nil =>
              rw [checkMatrixFuel_succ_nil] at hCheck
              rcases list_any_exists hCheck with ⟨r, hmem, hng⟩
              have hrow : rowColsWf false [] r.pats := hwf r hmem
              cases hp : r.pats with
              | cons _ _ => rw [hp] at hrow; cases hrow
              | nil =>
                  cases hg : r.isUnderGuard with
                  | true => rw [hg] at hng; cases hng
                  | false => exact ⟨r, hmem, hg, by rw [hp]; rfl⟩
      | cons col restCols =>
          cases vs with
          | cons v restVs =>
              rw [checkMatrixFuel_succ_cons] at hCheck
              let exp := expandOrColumn rows
              have hexpWf : matrixWf false (col :: restCols) exp :=
                expandOrColumn_wf rows hwf
              cases hpriv : col.privateUninhabited with
              | true =>
                  have hMemC : SpecCtor.skipPrivateUninhabited ∈ requiredCtors false exhFeat col := by
                    simp only [requiredCtors, hpriv, ↓reduceIte]
                    exact List.Mem.head _
                  have hSubCheck := list_all_mem hCheck hMemC
                  have hSubWf := specializeRows_wf .skipPrivateUninhabited trivial exp hexpWf
                  rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                  have hSpecLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                      row ∈ exp → row.pats = hd :: tl →
                      specializePat .skipPrivateUninhabited hd = some sub →
                      rowMatchesStack (sub ++ tl) restVs = true →
                      loweredMatchesVal hd v = true ∧ rowMatchesStack tl restVs = true := by
                    intro row hd tl sub hrowMem hrowPats hsp hmSub
                    simp only [specializePat, Option.some.injEq] at hsp
                    subst hsp
                    have hrowWf := hexpWf row hrowMem
                    rw [hrowPats] at hrowWf
                    have hhdWild : hd = .wild := hrowWf.1 hpriv
                    subst hhdWild
                    exact ⟨rfl, hmSub⟩
                  rcases specializeRows_sound col .skipPrivateUninhabited exp v restVs restVs
                      hSpecLift hmem' hm' with ⟨r1, hmem1, hg1, hm1⟩
                  rcases expandOrColumn_sound col rows v restVs hmem1 hm1 with ⟨r0, hmem0, hg0, hm0⟩
                  exact ⟨r0, hmem0, by rw [hg0, hg1, hng'], hm0⟩
              | false =>
                  cases col with
                  | mk cty cpriv cval cscrut =>
                      simp only at hpriv
                      subst hpriv
                      cases v with
                      | unit =>
                          let c0 : PlaceCol := ⟨.unit, false, cval, cscrut⟩
                          have hMemC : SpecCtor.unit ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .unit trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .unit hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd .unit = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            all_goals exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .unit exp .unit restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows .unit restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | bool bv =>
                          let c0 : PlaceCol := ⟨.bool, false, cval, cscrut⟩
                          have hMemC : SpecCtor.boolLit bv ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]
                            cases bv
                            · exact List.Mem.tail _ (List.Mem.head _)
                            · exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf (.boolLit bv) trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat (.boolLit bv) hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (.bool bv) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp; exact ⟨rfl, hmSub⟩
                            | boolLit b2 =>
                                simp only [specializePat] at hsp
                                cases hcmp : (bv == b2)
                                · rw [hcmp] at hsp; cases hsp
                                · rw [hcmp] at hsp
                                  simp only [↓reduceIte, Option.some.injEq] at hsp
                                  subst hsp
                                  have heq : b2 = bv := by
                                    cases bv <;> cases b2 <;> first | rfl | cases hcmp
                                  subst heq
                                  exact ⟨by cases b2 <;> rfl, hmSub⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 (.boolLit bv) exp (.bool bv) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (.bool bv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | foreignExt =>
                          let c0 : PlaceCol := ⟨.emptyEnum true, false, cval, cscrut⟩
                          have hMemC : SpecCtor.foreignExt ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .foreignExt trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .foreignExt hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd .foreignExt = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .foreignExt exp .foreignExt restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows .foreignExt restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | none =>
                          rename_i inner
                          let c0 : PlaceCol := ⟨.opt inner, false, cval, cscrut⟩
                          have hMemC : SpecCtor.none ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]
                            cases (visiblyUninhabited false inner && PlaceCol.canOmitEmptyArms false exhFeat c0)
                            · exact List.Mem.head _
                            · exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .none trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .none hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (@ValidVal.none inner) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            all_goals exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .none exp (@ValidVal.none inner) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.none inner) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | some iv =>
                          rename_i inner
                          let c0 : PlaceCol := ⟨.opt inner, false, cval, cscrut⟩
                          have hNotUninh : visiblyUninhabited false inner = false := by
                            cases hu : visiblyUninhabited false inner with
                            | false => rfl
                            | true => exact False.elim (visiblyUninhabited_false_implies_no_validVal inner hu iv)
                          have hMemC : SpecCtor.some ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte, hNotUninh, Bool.false_and]
                            exact List.Mem.tail _ (List.Mem.head _)
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .some ⟨inner, rfl⟩ exp hexpWf
                          let subVs : ValStack (specializeCol false c0 .some ++ restCols) :=
                            .cons iv restVs
                          rcases ih exhFeat _ _ hSubWf hSubCheck subVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .some hd = some sub →
                              rowMatchesStack (sub ++ tl) subVs = true →
                              loweredMatchesVal hd (ValidVal.some iv) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change rowMatchesStack tl restVs = true at hmSub
                                exact ⟨rfl, hmSub⟩
                            | some p =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change (loweredMatchesVal p iv && rowMatchesStack tl restVs) = true at hmSub
                                rw [Bool.and_eq_true] at hmSub
                                exact ⟨hmSub.1, hmSub.2⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 .some exp (ValidVal.some iv) restVs subVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (ValidVal.some iv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | ok iv =>
                          rename_i t1 t2
                          let c0 : PlaceCol := ⟨.result t1 t2, false, cval, cscrut⟩
                          have hNotUninh : visiblyUninhabited false t1 = false := by
                            cases hu : visiblyUninhabited false t1 with
                            | false => rfl
                            | true => exact False.elim (visiblyUninhabited_false_implies_no_validVal t1 hu iv)
                          have hMemC : SpecCtor.ok ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte, hNotUninh, Bool.false_and]
                            exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .ok ⟨t1, t2, rfl⟩ exp hexpWf
                          let subVs : ValStack (specializeCol false c0 .ok ++ restCols) :=
                            .cons iv restVs
                          rcases ih exhFeat _ _ hSubWf hSubCheck subVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .ok hd = some sub →
                              rowMatchesStack (sub ++ tl) subVs = true →
                              loweredMatchesVal hd (@ValidVal.ok t1 t2 iv) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change rowMatchesStack tl restVs = true at hmSub
                                exact ⟨rfl, hmSub⟩
                            | ok p =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change (loweredMatchesVal p iv && rowMatchesStack tl restVs) = true at hmSub
                                rw [Bool.and_eq_true] at hmSub
                                exact ⟨hmSub.1, hmSub.2⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 .ok exp (@ValidVal.ok t1 t2 iv) restVs subVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.ok t1 t2 iv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | err iv =>
                          rename_i t1 t2
                          let c0 : PlaceCol := ⟨.result t1 t2, false, cval, cscrut⟩
                          have hNotUninh : visiblyUninhabited false t2 = false := by
                            cases hu : visiblyUninhabited false t2 with
                            | false => rfl
                            | true => exact False.elim (visiblyUninhabited_false_implies_no_validVal t2 hu iv)
                          have hMemC : SpecCtor.err ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte, hNotUninh, Bool.false_and]
                            rw [List.mem_append]
                            exact Or.inr (List.Mem.head _)
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .err ⟨t1, t2, rfl⟩ exp hexpWf
                          let subVs : ValStack (specializeCol false c0 .err ++ restCols) :=
                            .cons iv restVs
                          rcases ih exhFeat _ _ hSubWf hSubCheck subVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .err hd = some sub →
                              rowMatchesStack (sub ++ tl) subVs = true →
                              loweredMatchesVal hd (@ValidVal.err t1 t2 iv) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change rowMatchesStack tl restVs = true at hmSub
                                exact ⟨rfl, hmSub⟩
                            | err p =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change (loweredMatchesVal p iv && rowMatchesStack tl restVs) = true at hmSub
                                rw [Bool.and_eq_true] at hmSub
                                exact ⟨hmSub.1, hmSub.2⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 .err exp (@ValidVal.err t1 t2 iv) restVs subVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.err t1 t2 iv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | pair v1 v2 =>
                          rename_i fv1 fv2 t1 t2
                          let c0 : PlaceCol := ⟨.pair fv1 t1 fv2 t2, false, cval, cscrut⟩
                          have hNotUninh : visiblyUninhabited false (.pair fv1 t1 fv2 t2) = false := by
                            cases hu : visiblyUninhabited false (.pair fv1 t1 fv2 t2) with
                            | false => rfl
                            | true =>
                                exact False.elim (visiblyUninhabited_false_implies_no_validVal _ hu (.pair v1 v2))
                          have hMemC : SpecCtor.pair ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte, hNotUninh, Bool.false_and]
                            exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .pair ⟨fv1, t1, fv2, t2, rfl⟩ exp hexpWf
                          let subVs : ValStack (specializeCol false c0 .pair ++ restCols) :=
                            .cons v1 (.cons v2 restVs)
                          rcases ih exhFeat _ _ hSubWf hSubCheck subVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .pair hd = some sub →
                              rowMatchesStack (sub ++ tl) subVs = true →
                              loweredMatchesVal hd (@ValidVal.pair fv1 fv2 t1 t2 v1 v2) = true ∧
                                rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change rowMatchesStack tl restVs = true at hmSub
                                exact ⟨rfl, hmSub⟩
                            | pair p1 p2 =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change (loweredMatchesVal p1 v1 &&
                                  (loweredMatchesVal p2 v2 && rowMatchesStack tl restVs)) = true at hmSub
                                rw [Bool.and_eq_true, Bool.and_eq_true] at hmSub
                                rw [loweredMatchesVal_pair, Bool.and_eq_true]
                                exact ⟨⟨hmSub.1, hmSub.2.1⟩, hmSub.2.2⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 .pair exp (@ValidVal.pair fv1 fv2 t1 t2 v1 v2) restVs subVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.pair fv1 fv2 t1 t2 v1 v2) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | refVal iv =>
                          rename_i inner
                          let c0 : PlaceCol := ⟨.ref inner, false, cval, cscrut⟩
                          have hMemC : SpecCtor.ref ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .ref ⟨inner, rfl⟩ exp hexpWf
                          let subVs : ValStack (specializeCol false c0 .ref ++ restCols) :=
                            .cons iv restVs
                          rcases ih exhFeat _ _ hSubWf hSubCheck subVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .ref hd = some sub →
                              rowMatchesStack (sub ++ tl) subVs = true →
                              loweredMatchesVal hd (ValidVal.refVal iv) = true ∧ rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd with
                            | wild =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change rowMatchesStack tl restVs = true at hmSub
                                exact ⟨rfl, hmSub⟩
                            | ref p =>
                                simp only [specializePat, Option.some.injEq] at hsp
                                subst hsp
                                change (loweredMatchesVal p iv && rowMatchesStack tl restVs) = true at hmSub
                                rw [Bool.and_eq_true] at hmSub
                                exact ⟨hmSub.1, hmSub.2⟩
                            | _ => cases hsp
                          rcases specializeRows_sound c0 .ref exp (ValidVal.refVal iv) restVs subVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (ValidVal.refVal iv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | rawPtrAddr addr =>
                          rename_i inner
                          let c0 : PlaceCol := ⟨.rawPtr inner, false, cval, cscrut⟩
                          have hMemC : SpecCtor.opaqueMissing ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .opaqueMissing trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .opaqueMissing hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (@ValidVal.rawPtrAddr inner addr) = true ∧
                                rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .opaqueMissing exp (@ValidVal.rawPtrAddr inner addr) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.rawPtrAddr inner addr) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | unionF1 uv =>
                          rename_i t1 t2
                          let c0 : PlaceCol := ⟨.union t1 t2, false, cval, cscrut⟩
                          have hMemC : SpecCtor.opaqueMissing ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .opaqueMissing trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .opaqueMissing hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (@ValidVal.unionF1 t1 t2 uv) = true ∧
                                rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .opaqueMissing exp (@ValidVal.unionF1 t1 t2 uv) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.unionF1 t1 t2 uv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | unionF2 uv =>
                          rename_i t1 t2
                          let c0 : PlaceCol := ⟨.union t1 t2, false, cval, cscrut⟩
                          have hMemC : SpecCtor.opaqueMissing ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .opaqueMissing trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .opaqueMissing hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (@ValidVal.unionF2 t1 t2 uv) = true ∧
                                rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .opaqueMissing exp (@ValidVal.unionF2 t1 t2 uv) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.unionF2 t1 t2 uv) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩
                      | unionRaw rawN =>
                          rename_i t1 t2
                          let c0 : PlaceCol := ⟨.union t1 t2, false, cval, cscrut⟩
                          have hMemC : SpecCtor.opaqueMissing ∈ requiredCtors false exhFeat c0 := by
                            simp only [requiredCtors, c0, Bool.false_eq_true, ↓reduceIte]; exact List.Mem.head _
                          have hSubCheck := list_all_mem hCheck hMemC
                          have hSubWf := specializeRows_wf .opaqueMissing trivial exp hexpWf
                          rcases ih exhFeat _ _ hSubWf hSubCheck restVs with ⟨r', hmem', hng', hm'⟩
                          have hLift : ∀ (row : MatrixRow) (hd : Pat) (tl sub : List Pat),
                              row ∈ exp → row.pats = hd :: tl → specializePat .opaqueMissing hd = some sub →
                              rowMatchesStack (sub ++ tl) restVs = true →
                              loweredMatchesVal hd (@ValidVal.unionRaw t1 t2 rawN) = true ∧
                                rowMatchesStack tl restVs = true := by
                            intro _ hd tl sub _ _ hsp hmSub
                            cases hd <;> simp only [specializePat, Option.some.injEq] at hsp <;> try cases hsp
                            exact ⟨rfl, hmSub⟩
                          rcases specializeRows_sound c0 .opaqueMissing exp (@ValidVal.unionRaw t1 t2 rawN) restVs restVs hLift hmem' hm' with ⟨r1, hm1, hg1, hmr1⟩
                          rcases expandOrColumn_sound c0 rows (@ValidVal.unionRaw t1 t2 rawN) restVs hm1 hmr1 with ⟨r0, hm0, hg0, hmr0⟩
                          exact ⟨r0, hm0, by rw [hg0, hg1, hng'], hmr0⟩

theorem evalArmsLoop_matches_of_unguarded_hit {t : Ty} (v : ValidVal t)
    (gOracle : GuardOracle) (idx : Nat) (arms : List Arm)
    (hwf : ∀ a, a ∈ arms → armWellFormed false t a = true)
    (hhit : ∃ a, a ∈ arms ∧ armCountsAsGuarded .soundOpaque a = false ∧
      loweredMatchesVal (lowerPatForAnalysis a.pat) v = true) :
    ∃ k, evalArmsLoop false gOracle (.valid v) idx arms = .matchedArm k := by
  induction arms generalizing idx with
  | nil =>
      rcases hhit with ⟨_, hm, _, _⟩
      cases hm
  | cons a rest ih =>
      have hwfA : armWellFormed false t a = true := hwf a (List.Mem.head _)
      simp only [armWellFormed, Bool.and_eq_true] at hwfA
      have hpatWf : checkPatWellFormed false t a.pat = true := hwfA.1
      have hwfRest : ∀ b, b ∈ rest → armWellFormed false t b = true :=
        fun b hb => hwf b (List.Mem.tail _ hb)
      rcases hhit with ⟨hitArm, hitMem, hitNg, hitMatch⟩
      rw [evalArmsLoop_cons]
      cases evalPat_validVal_never_faults a.pat v gOracle hpatWf with
      | inl hMatchA =>
          rw [hMatchA]
          cases hguardA : a.armGuard with
          | none => exact ⟨idx, rfl⟩
          | some gid =>
              dsimp only
              cases hgVal : gOracle gid with
              | true =>
                  simp only [↓reduceIte]
                  exact ⟨idx, rfl⟩
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  cases hitMem with
                  | head =>
                      simp only [armCountsAsGuarded, hguardA, Bool.true_or] at hitNg
                      cases hitNg
                  | tail _ hInRest =>
                      exact ih (idx + 1) hwfRest ⟨hitArm, hInRest, hitNg, hitMatch⟩
      | inr hMismatchA =>
          rw [hMismatchA]
          cases hitMem with
          | head =>
              simp only [armCountsAsGuarded, Bool.or_eq_false_iff] at hitNg
              have hEq : evalPat false gOracle a.pat (.valid v) = .matched :=
                evalPat_of_loweredMatchesVal a.pat v gOracle hpatWf hitNg.2 hitMatch
              rw [hMismatchA] at hEq
              cases hEq
          | tail _ hInRest =>
              exact ih (idx + 1) hwfRest ⟨hitArm, hInRest, hitNg, hitMatch⟩

/-- Flagship Exhaustiveness Soundness Theorem:
    **`exhaustiveMatrix_every_valid_value_matched_or_never_read`**
    For EVERY well-formed match over type `t` accepted by `checkMatchExhaustive`
    under `GuardLoweringMode.soundOpaque`, for EVERY guard oracle `gOracle` and
    EVERY valid scrutinee `v : ValidVal t`:
      1. `evalMatchPlace false gOracle arms (.valid v)` deterministically enters
         a concrete reachable arm `.matchedArm k` (NEVER hits `missingArmTrap`,
         NEVER enters `ubUnreachable`, NEVER faults on discriminant or deref), AND
      2. For any `RawPlace t` satisfying `PlaceRespectsValidity .validOnly p`,
         if `t` is visibly uninhabited (`visiblyUninhabited false t = true`),
         no valid execution can ever reach the match (`False`). -/
theorem exhaustiveMatrix_every_valid_value_matched_or_never_read
    {t : Ty} (exhFeat : Bool) (scrutVal : PlaceValidity) (arms : List Arm)
    (hwf : ∀ a, a ∈ arms → armWellFormed false t a = true)
    (hExh : checkMatchExhaustive false exhFeat .soundOpaque t scrutVal arms = true) :
    (∀ (gOracle : GuardOracle) (v : ValidVal t),
      ∃ k, evalMatchPlace false gOracle arms (.valid v) = .matchedArm k) ∧
    (∀ (p : RawPlace t),
      visiblyUninhabited false t = true →
      PlaceRespectsValidity .validOnly p →
      False) := by
  constructor
  · intro gOracle v
    let initCol : PlaceCol :=
      { ty := t, privateUninhabited := false, validity := scrutVal, isScrutinee := true }
    let rows : List MatrixRow :=
      arms.map (fun a =>
        { pats := [lowerPatForAnalysis a.pat]
        , isUnderGuard := armCountsAsGuarded .soundOpaque a })
    have hMatWf : matrixWf false [initCol] rows := by
      intro r hr
      simp only [rows, List.mem_map] at hr
      rcases hr with ⟨a, haMem, rfl⟩
      have haWf := hwf a haMem
      simp only [armWellFormed, Bool.and_eq_true] at haWf
      rw [rowColsWf_cons, rowColsWf_nil]
      refine ⟨(fun h => by cases h), ?_, trivial⟩
      exact checkPatWellFormed_implies_loweredPrivacy false t a.pat haWf.1
    have hFound := checkMatrixFuel_sound_valid (colsFuel [initCol]) exhFeat [initCol] rows
      hMatWf hExh (.cons v .nil)
    rcases hFound with ⟨r, hrMem, hrNg, hrMatch⟩
    simp only [rows, List.mem_map] at hrMem
    rcases hrMem with ⟨a, haMem, rfl⟩
    rw [rowMatchesStack_singleton] at hrMatch
    cases arms with
    | nil => cases haMem
    | cons a0 rest0 =>
        simp only [evalMatchPlace]
        exact evalArmsLoop_matches_of_unguarded_hit v gOracle 0 (a0 :: rest0) hwf
          ⟨a, haMem, hrNg, hrMatch⟩
  · intro p hu hv
    exact validOnly_visiblyUninhabited_absurd p hu hv

/-! ## Part 7: Guard Opacity, Three-Way Place Semantics, Postfix Match, and Anneal Bridge -/

theorem expandOrHead_filter (p : Pat) (tl : List Pat) (g : Bool) :
    (expandOrHead p tl g).filter (fun r => !r.isUnderGuard) =
      if g then [] else expandOrHead p tl false := by
  induction p with
  | or p1 p2 ih1 ih2 =>
      rw [expandOrHead_or, List.filter_append, ih1, ih2]
      cases g <;> rfl
  | wild | never | unit | boolLit _ | none | some _ | ok _ | err _
  | pair _ _ | ref _ | subGuard _ _ =>
      cases g <;> rfl

theorem expandOrColumn_filter (rows : List MatrixRow) :
    (expandOrColumn rows).filter (fun r => !r.isUnderGuard) =
      expandOrColumn (rows.filter (fun r => !r.isUnderGuard)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      rw [expandOrColumn_cons]
      cases hp : r.pats with
      | nil =>
          dsimp only
          cases hg : r.isUnderGuard with
          | true =>
              simp only [List.filter_cons, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ih
          | false =>
              simp only [List.filter_cons, hg, Bool.not_false, ↓reduceIte]
              rw [expandOrColumn_cons, hp]
              dsimp only
              rw [ih]
      | cons hd tl =>
          dsimp only
          rw [List.filter_append, expandOrHead_filter, ih]
          cases hg : r.isUnderGuard with
          | true =>
              simp only [↓reduceIte, List.nil_append, List.filter_cons, hg,
                Bool.not_true, Bool.false_eq_true]
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, hg, Bool.not_false]
              rw [expandOrColumn_cons, hp]
              dsimp only
              rw [hg]

theorem specializeRows_filter (c : SpecCtor) (rows : List MatrixRow) :
    (specializeRows c rows).filter (fun r => !r.isUnderGuard) =
      specializeRows c (rows.filter (fun r => !r.isUnderGuard)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      rw [specializeRows_cons]
      cases hp : r.pats with
      | nil =>
          dsimp only
          cases hg : r.isUnderGuard with
          | true =>
              simp only [List.filter_cons, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ih
          | false =>
              simp only [List.filter_cons, hg, Bool.not_false, ↓reduceIte]
              rw [specializeRows_cons, hp]
              exact ih
      | cons hd tl =>
          dsimp only
          cases hs : specializePat c hd with
          | none =>
              cases hg : r.isUnderGuard with
              | true =>
                  simp only [List.filter_cons, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  exact ih
              | false =>
                  simp only [List.filter_cons, hg, Bool.not_false, ↓reduceIte]
                  rw [specializeRows_cons, hp]
                  dsimp only
                  rw [hs]
                  exact ih
          | some sub =>
              cases hg : r.isUnderGuard with
              | true =>
                  simp only [List.filter_cons, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                  exact ih
              | false =>
                  simp only [List.filter_cons, hg, Bool.not_false, ↓reduceIte]
                  rw [specializeRows_cons, hp]
                  dsimp only
                  rw [hs]
                  dsimp only
                  rw [hg, ih]

theorem list_any_not_guard_eq_filter (rows : List MatrixRow) :
    rows.any (fun r => !r.isUnderGuard) =
      (rows.filter (fun r => !r.isUnderGuard)).any (fun r => !r.isUnderGuard) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
      cases hg : r.isUnderGuard with
      | true =>
          simp only [List.any_cons, List.filter_cons, hg, Bool.not_true, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte]
          exact ih
      | false =>
          simp only [List.any_cons, List.filter_cons, hg, Bool.not_false, Bool.true_or, ↓reduceIte]

theorem checkMatrixFuel_filter_guarded (inMod : Bool) (exhFeat : Bool) :
    ∀ (fuel : Nat) (cols : List PlaceCol) (rows : List MatrixRow),
      checkMatrixFuel inMod exhFeat fuel cols rows =
      checkMatrixFuel inMod exhFeat fuel cols (rows.filter (fun r => !r.isUnderGuard)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ n ih =>
      intro cols rows
      cases cols with
      | nil =>
          rw [checkMatrixFuel_succ_nil, checkMatrixFuel_succ_nil]
          exact list_any_not_guard_eq_filter rows
      | cons col restCols =>
          rw [checkMatrixFuel_succ_cons, checkMatrixFuel_succ_cons]
          have hAllEq : ∀ cs : List SpecCtor,
              cs.all (fun c => checkMatrixFuel inMod exhFeat n
                (specializeCol inMod col c ++ restCols) (specializeRows c (expandOrColumn rows))) =
              cs.all (fun c => checkMatrixFuel inMod exhFeat n
                (specializeCol inMod col c ++ restCols)
                (specializeRows c (expandOrColumn (rows.filter (fun r => !r.isUnderGuard))))) := by
            intro cs
            induction cs with
            | nil => rfl
            | cons c cs ihCs =>
                simp only [List.all_cons, ihCs]
                congr 1
                rw [ih (specializeCol inMod col c ++ restCols) (specializeRows c (expandOrColumn rows))]
                rw [specializeRows_filter, expandOrColumn_filter]
          exact hAllEq (requiredCtors inMod exhFeat col)

theorem map_filter_guarded (gMode : GuardLoweringMode) (arms : List Arm) :
    (arms.map (fun a =>
      { pats := [lowerPatForAnalysis a.pat]
      , isUnderGuard := armCountsAsGuarded gMode a : MatrixRow })).filter
        (fun r => !r.isUnderGuard) =
    (arms.filter (fun a => !armCountsAsGuarded gMode a)).map (fun a =>
      { pats := [lowerPatForAnalysis a.pat]
      , isUnderGuard := armCountsAsGuarded gMode a : MatrixRow }) := by
  induction arms with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.map_cons, List.filter_cons]
      cases hg : armCountsAsGuarded gMode a with
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          exact ih
      | false =>
          simp only [Bool.not_false, ↓reduceIte, List.map_cons, hg]
          rw [ih]

/-- Sub-Pattern Guard Opacity Theorem:
    **`guardPattern_must_stay_opaque_for_exhaustiveness`**
    Under `GuardLoweringMode.soundOpaque`, ANY arm carrying a top-level arm guard
    OR a `#![feature(guard_patterns)]` sub-pattern guard (`Pat.subGuard`)
    contributes EXACTLY ZERO coverage to exhaustiveness: removing all guarded
    arms leaves `checkMatchExhaustive` identically unchanged. -/
theorem guardPattern_must_stay_opaque_for_exhaustiveness
    (inMod : Bool) (exhFeat : Bool) (t : Ty) (scrutVal : PlaceValidity) (arms : List Arm) :
    checkMatchExhaustive inMod exhFeat .soundOpaque t scrutVal arms =
    checkMatchExhaustive inMod exhFeat .soundOpaque t scrutVal
      (arms.filter (fun a => !armCountsAsGuarded .soundOpaque a)) := by
  simp only [checkMatchExhaustive]
  rw [checkMatrixFuel_filter_guarded]
  rw [map_filter_guarded]

/-- Three-Way Null `*const !` Operational Split Theorem. -/
theorem threeWay_null_raw_never_split (gOracle : GuardOracle) :
    let p : RawPlace .never := .nullRawDeref
    let wildArm : Arm := { pat := .wild, armGuard := none, hasBody := true }
    let neverArm : Arm := { pat := .never, armGuard := none, hasBody := false }
    evalMatchPlace false gOracle [wildArm] p = .matchedArm 0 ∧
    evalMatchPlace false gOracle [] p = .ubUnreachable ∧
    evalMatchPlace false gOracle [neverArm] p = .ubUnreachable := by
  exact ⟨rfl, rfl, rfl⟩

/-- Postfix Match (`#![feature(postfix_match)]`) Temporary Drop-Scope Equivalence. -/
inductive MatchSyntaxKind : Type where
  | prefixNormal : MatchSyntaxKind
  | postfixDotMatch : MatchSyntaxKind

inductive HirMatchSource : Type where
  | normal : HirMatchSource
  | postfix : HirMatchSource

def lowerMatchSource : MatchSyntaxKind → HirMatchSource
  | .prefixNormal => .normal
  | .postfixDotMatch => .postfix

inductive DropEvent : Type where
  | makeScrutinee : DropEvent
  | armBody : DropEvent
  | dropInnerTemp : DropEvent
  | afterMatch : DropEvent

def evalMatchTempDropTrace (_src : HirMatchSource) : List DropEvent :=
  [.makeScrutinee, .armBody, .dropInnerTemp, .afterMatch]

theorem postfixMatch_temp_drop_order_eq_prefix :
    evalMatchTempDropTrace (lowerMatchSource .postfixDotMatch) =
      evalMatchTempDropTrace (lowerMatchSource .prefixNormal) ∧
    evalMatchTempDropTrace (lowerMatchSource .postfixDotMatch) =
      [.makeScrutinee, .armBody, .dropInnerTemp, .afterMatch] := by
  exact ⟨rfl, rfl⟩

/-- Anneal Trusted MIR Bridge (`joshlf/anneal@c131b320e`,
    `Trusted/MirSemantics.lean:1724-1748, 2513-2600`):
    Because `MirTy.never` has an empty `ValidEntryArgs` set, any body judgment
    defined ONLY by universal quantification over valid entry arguments is
    vacuously satisfied even by ill-formed bodies (`storageInBounds = false`).
    Conjoining `BodyStaticAdmitted` closes this vacuity gap. -/
structure MiniMirBody : Type where
  paramTy : Ty
  storageInBounds : Bool
  terminatesUnreachable : Bool

def miniValidEntryArgs (b : MiniMirBody) : Type := ValidVal b.paramTy

def miniBodyStaticAdmitted (b : MiniMirBody) : Bool := b.storageInBounds

def miniBodySafe (_b : MiniMirBody) (_arg : ValidVal _b.paramTy) : Prop :=
  _b.terminatesUnreachable = false

def miniBodyVerifiedNaive (b : MiniMirBody) : Prop :=
  ∀ arg : miniValidEntryArgs b, miniBodySafe b arg

def miniBodyVerifiedAnneal (b : MiniMirBody) : Prop :=
  miniBodyStaticAdmitted b = true ∧ ∀ arg : miniValidEntryArgs b, miniBodySafe b arg

theorem anneal_never_param_vacuity_requires_static_admission :
    let badNeverBody : MiniMirBody :=
      { paramTy := .never, storageInBounds := false, terminatesUnreachable := true }
    let goodNeverBody : MiniMirBody :=
      { paramTy := .never, storageInBounds := true, terminatesUnreachable := true }
    miniBodyVerifiedNaive badNeverBody ∧
    ¬ miniBodyVerifiedAnneal badNeverBody ∧
    miniBodyVerifiedAnneal goodNeverBody := by
  refine ⟨?_, ?_, ?_⟩
  · intro arg; cases arg
  · intro h; cases h.1
  · exact ⟨rfl, fun arg => by cases arg⟩

/-! ## Part 8: Constructive Sharpness Counterexamples (`ce1`–`ce6`) -/

/-- **Counterexample 1 (`ce1_guard_pattern_treated_as_exhaustive_causes_missing_arm`):**
    Demonstrates the exact live `rustc` `#![feature(guard_patterns)]` defect
    (`rustc.rs:471-472` + `match_pair.rs:457-460`). -/
theorem ce1_guard_pattern_treated_as_exhaustive_causes_missing_arm :
    let t : Ty := .opt .bool
    let guardedArms : List Arm :=
      [ { pat := .some (.subGuard .wild 0), armGuard := none, hasBody := true }
      , { pat := .none, armGuard := none, hasBody := true } ]
    let gFalse : GuardOracle := fun _ => false
    let scrut : ValidVal t := .some (.bool false)
    checkMatchExhaustive false false .rustcBuggyUnguarded t .validOnly guardedArms = true ∧
    checkMatchExhaustive false false .soundOpaque t .validOnly guardedArms = false ∧
    evalMatchPlace false gFalse guardedArms (.valid scrut) = .missingArmTrap ∧
    evalMatchPlaceRustcStub false gFalse guardedArms (.valid scrut) = .matchedArm 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Counterexample 2 (`ce2_uninhabited_behind_raw_ptr_without_read_unsound_unreachable`):**
    Demonstrates why `PlaceValidity.maybeInvalid` forbids omitting uninhabited
    arms behind raw pointers (`HasNever`) and references (`&Result<bool, !>`). -/
theorem ce2_uninhabited_behind_raw_ptr_without_read_unsound_unreachable :
    let hasNeverTy : Ty := .pair .pubVis .bool .pubVis .never
    let rogueHasNever : RawPlace hasNeverTy := .roguePair (.valid (.bool true)) .nullRawDeref
    let wildPairArm : Arm := { pat := .pair .wild .wild, armGuard := none, hasBody := true }
    let refResTy : Ty := .ref (.result .bool .never)
    let okOnlyArms : List Arm :=
      [{ pat := .ref (.ok .wild), armGuard := none, hasBody := true }]
    let okAndNeverArms : List Arm :=
      [ { pat := .ref (.ok .wild), armGuard := none, hasBody := true }
      , { pat := .ref (.err .never), armGuard := none, hasBody := false } ]
    let rogueRefErr : RawPlace refResTy := .rogueRef .rogueErrTag
    let gConst : GuardOracle := fun _ => true
    checkMatchExhaustive false false .soundOpaque hasNeverTy .maybeInvalid [] = false ∧
    checkMatchExhaustive false true .soundOpaque hasNeverTy .maybeInvalid [] = true ∧
    evalMatchPlace false gConst [wildPairArm] rogueHasNever = .matchedArm 0 ∧
    evalMatchPlace false gConst [] rogueHasNever = .ubUnreachable ∧
    checkMatchExhaustive false false .soundOpaque refResTy .validOnly okOnlyArms = false ∧
    checkMatchExhaustive false false .soundOpaque refResTy .validOnly okAndNeverArms = true ∧
    (okAndNeverArms.all (armWellFormed false refResTy)) = true ∧
    evalMatchPlace false gConst okAndNeverArms rogueRefErr = .ubInvalidDiscrRead := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Counterexample 3 (`ce3_wildcard_star_null_never_succeeds_while_empty_match_faults`):**
    Exact three-way Miri/MIR separation on `p: *const ! = null()`. -/
theorem ce3_wildcard_star_null_never_succeeds_while_empty_match_faults :
    let p : RawPlace .never := .nullRawDeref
    let wildArm : Arm := { pat := .wild, armGuard := none, hasBody := true }
    let neverArm : Arm := { pat := .never, armGuard := none, hasBody := false }
    let gConst : GuardOracle := fun _ => true
    checkMatchExhaustive false false .soundOpaque .never .maybeInvalid [] = true ∧
    evalMatchPlace false gConst [wildArm] p = .matchedArm 0 ∧
    evalMatchPlace false gConst [] p = .ubUnreachable ∧
    evalMatchPlace false gConst [neverArm] p = .ubUnreachable ∧
    evalMatchPlace false gConst [wildArm] p ≠ evalMatchPlace false gConst [] p := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- **Counterexample 4 (`ce4_never_pattern_on_inhabited_variant_rejected`):**
    `Some(!)` on `Option<bool>` is REJECTED by `checkPatWellFormed`, AND if
    wrongly admitted, evaluating `Some(!)` on `Some(true)` faults `.ubUnreachable`. -/
theorem ce4_never_pattern_on_inhabited_variant_rejected :
    let optBool : Ty := .opt .bool
    let badNeverArm : Arm := { pat := .some .never, armGuard := none, hasBody := false }
    let badBodyArm : Arm := { pat := .err .never, armGuard := none, hasBody := true }
    let gConst : GuardOracle := fun _ => true
    visiblyUninhabited false .bool = false ∧
    checkPatWellFormed false optBool (.some .never) = false ∧
    armWellFormed false optBool badNeverArm = false ∧
    armWellFormed false (.result .bool .never) badBodyArm = false ∧
    evalMatchPlace false gConst [badNeverArm] (.valid (.some (.bool true))) = .ubUnreachable := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Counterexample 5 (`ce5_private_uninhabited_field_hidden_outside_module`):**
    `struct PrivEmpty { _priv: !, pub x: bool }` in `Result<bool, PrivEmpty>`:
    omitting `Err` is ACCEPTED inside the defining module (`inMod = true`) and
    REJECTED outside (`inMod = false`). -/
theorem ce5_private_uninhabited_field_hidden_outside_module :
    let privEmpty : Ty := .pair .privVis .never .pubVis .bool
    let resTy : Ty := .result .bool privEmpty
    let okOnly : List Arm := [{ pat := .ok .wild, armGuard := none, hasBody := true }]
    visiblyUninhabited true privEmpty = true ∧
    visiblyUninhabited false privEmpty = false ∧
    checkMatchExhaustive true false .soundOpaque resTy .validOnly okOnly = true ∧
    checkMatchExhaustive false false .soundOpaque resTy .validOnly okOnly = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Counterexample 6 (`ce6_foreign_non_exhaustive_empty_enum_blocks_empty_match`):**
    `#[non_exhaustive] pub enum ForeignEmpty {}`:
    `match x {}` is ACCEPTED inside its defining crate (`inMod = true`) and
    REJECTED in downstream crates (`inMod = false`). -/
theorem ce6_foreign_non_exhaustive_empty_enum_blocks_empty_match :
    let foreignEmpty : Ty := .emptyEnum true
    isNoConstructors true foreignEmpty = true ∧
    isNoConstructors false foreignEmpty = false ∧
    checkMatchExhaustive true false .soundOpaque foreignEmpty .validOnly [] = true ∧
    checkMatchExhaustive false false .soundOpaque foreignEmpty .validOnly [] = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end NeverPatternsSoundness
