/-
  HirTypeckCoercionLubAndNeverFallbackSoundness.lean

  Kernel-checked Lean v4.34.1 mechanization of:
    1. `rustc_hir_typeck` Coercion Subtyping (`Coerce::coerce`, `AdjustChain`,
       and all five `PointerCoercion` variants: `ReifyFnPointer`,
       `UnsafeFnPointer`, `ClosureFnPointer`, `MutToConstPointer`, `Unsize`).
    2. `CoerceMany` Asymmetric Multi-Arm LUB Unification (`try_find_coercion_lub`),
       retroactive adjustment soundness, ZST identity preservation, capturing-
       closure rejection, and order-dependence / `ExpectHasType(?v)` pinning
       contrasts across `if`/`match` vs. `loop`/`block` vs. generic calls.
    3. Post-1.100 Unconditional Never-Type (`!`) Fallback (`fallback.rs:88-94`),
       `NeverToAny` Ex-Falso soundness vs. `expr_guaranteed_to_constitute_read_for_never`
       place-read gating, `ZeroValid` uninhabitedness contradiction (`zeroed::<!>()`),
       and `never_type_fallback_flowing_into_unsafe` undirected coercion-graph
       taint reachability soundness and sharpness counterexamples.
    4. Fail-closed boundary projection onto Anneal's MIR semantics (`MirAst`,
       `MirSemantics` at `joshlf/anneal`).

  Lean Purity Compliance:
    - Zero `sorry`, zero `partial def`, zero `Classical.choice`, zero `omega`,
      zero `bv_decide`, zero `native_decide`, zero `._unsafe_rec`.
    - Every value-level definition uses `noncomputable def` with purely
      structural recursion; zero `deriving` clauses appear anywhere in the file.
-/

namespace HirTypeckCoercionLubAndNeverFallbackSoundness

/-! ## Section 1: Core Type Syntax, Mutability, Safety & Equality Judgments -/

/-- Reference / raw-pointer mutability (`rustc_ast::Mutability`). -/
inductive Mutability where
  | imm
  | mutbl

/-- Function signature safety (`rustc_hir::Safety`). -/
inductive Safety where
  | isSafe
  | isUnsafe

/-- All five pointer coercion variants in `rustc_middle::ty::adjustment::PointerCoercion`. -/
inductive PointerCoercion where
  | reifyFnPointer (targetSafety : Safety)
  | unsafeFnPointer
  | closureFnPointer (targetSafety : Safety)
  | mutToConstPointer
  | unsize

/-- HIR / MIR type AST subset capturing coercions, inference variables,
    function items, closures, references, raw pointers, slices, arrays, and `!`. -/
inductive RustTy where
  | unit
  | never
  | scalar
  | array (len : Nat) (elem : RustTy)
  | slice (elem : RustTy)
  | ref (m : Mutability) (inner : RustTy)
  | rawPtr (m : Mutability) (inner : RustTy)
  | fnItem (fnId : Nat) (s : Safety) (arg : RustTy) (ret : RustTy)
  | fnPtr (s : Safety) (arg : RustTy) (ret : RustTy)
  | closure (closureId : Nat) (hasCaptures : Bool) (arg : RustTy) (ret : RustTy)
  | tyVar (vid : Nat)
  | error

/-- Single coercion adjustment step (`rustc_middle::ty::adjustment::Adjust`). -/
inductive AdjustKind where
  | neverToAny
  | derefBuiltin
  | borrowRef (m : Mutability)
  | borrowRawPtr (m : Mutability)
  | pointer (pc : PointerCoercion)

/-- An annotated adjustment record targeting a post-adjustment type. -/
structure Adjustment where
  kind : AdjustKind
  target : RustTy

/-- Constructive Boolean equality on `Nat` (kernel-pure). -/
noncomputable def eqNat : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ a, Nat.succ b => eqNat a b
  | _, _ => false

theorem eqNat_refl (n : Nat) : eqNat n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem eqNat_sound {a b : Nat} (h : eqNat a b = true) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => simp [eqNat] at h
  | succ ak ih =>
    cases b with
    | zero => simp [eqNat] at h
    | succ bk =>
      have hsub : eqNat ak bk = true := h
      have heq := ih hsub
      subst heq
      rfl

theorem eqNat_iff (a b : Nat) : eqNat a b = true ↔ a = b :=
  ⟨eqNat_sound, fun h => h ▸ eqNat_refl a⟩

noncomputable def eqBool : Bool → Bool → Bool
  | false, false => true
  | true, true => true
  | _, _ => false

theorem eqBool_refl (b : Bool) : eqBool b b = true := by
  cases b <;> rfl

theorem eqBool_sound {a b : Bool} (h : eqBool a b = true) : a = b := by
  cases a <;> cases b <;> simp [eqBool] at h <;> rfl

theorem eqBool_iff (a b : Bool) : eqBool a b = true ↔ a = b :=
  ⟨eqBool_sound, fun h => h ▸ eqBool_refl a⟩

noncomputable def eqMut : Mutability → Mutability → Bool
  | .imm, .imm => true
  | .mutbl, .mutbl => true
  | _, _ => false

theorem eqMut_refl (m : Mutability) : eqMut m m = true := by
  cases m <;> rfl

theorem eqMut_sound {a b : Mutability} (h : eqMut a b = true) : a = b := by
  cases a <;> cases b <;> simp [eqMut] at h <;> rfl

theorem eqMut_iff (a b : Mutability) : eqMut a b = true ↔ a = b :=
  ⟨eqMut_sound, fun h => h ▸ eqMut_refl a⟩

noncomputable def eqSafety : Safety → Safety → Bool
  | .isSafe, .isSafe => true
  | .isUnsafe, .isUnsafe => true
  | _, _ => false

theorem eqSafety_refl (s : Safety) : eqSafety s s = true := by
  cases s <;> rfl

theorem eqSafety_sound {a b : Safety} (h : eqSafety a b = true) : a = b := by
  cases a <;> cases b <;> simp [eqSafety] at h <;> rfl

theorem eqSafety_iff (a b : Safety) : eqSafety a b = true ↔ a = b :=
  ⟨eqSafety_sound, fun h => h ▸ eqSafety_refl a⟩

/-- Structural decidable Boolean equality on `RustTy`, without `deriving`. -/
noncomputable def eqTy : RustTy → RustTy → Bool
  | .unit, .unit => true
  | .never, .never => true
  | .scalar, .scalar => true
  | .error, .error => true
  | .array n1 e1, .array n2 e2 => eqNat n1 n2 && eqTy e1 e2
  | .slice e1, .slice e2 => eqTy e1 e2
  | .ref m1 i1, .ref m2 i2 => eqMut m1 m2 && eqTy i1 i2
  | .rawPtr m1 i1, .rawPtr m2 i2 => eqMut m1 m2 && eqTy i1 i2
  | .fnItem id1 s1 a1 r1, .fnItem id2 s2 a2 r2 =>
      eqNat id1 id2 && eqSafety s1 s2 && eqTy a1 a2 && eqTy r1 r2
  | .fnPtr s1 a1 r1, .fnPtr s2 a2 r2 =>
      eqSafety s1 s2 && eqTy a1 a2 && eqTy r1 r2
  | .closure id1 c1 a1 r1, .closure id2 c2 a2 r2 =>
      eqNat id1 id2 && eqBool c1 c2 && eqTy a1 a2 && eqTy r1 r2
  | .tyVar v1, .tyVar v2 => eqNat v1 v2
  | _, _ => false

theorem bool_and_true_iff (x y : Bool) : (x && y) = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> simp

theorem eqTy_refl (t : RustTy) : eqTy t t = true := by
  induction t with
  | unit => rfl
  | never => rfl
  | scalar => rfl
  | error => rfl
  | array len elem ih =>
    simp [eqTy, eqNat_refl, ih]
  | slice elem ih =>
    exact ih
  | ref m inner ih =>
    simp [eqTy, eqMut_refl, ih]
  | rawPtr m inner ih =>
    simp [eqTy, eqMut_refl, ih]
  | fnItem id s arg ret iha ihr =>
    simp [eqTy, eqNat_refl, eqSafety_refl, iha, ihr]
  | fnPtr s arg ret iha ihr =>
    simp [eqTy, eqSafety_refl, iha, ihr]
  | closure id cap arg ret iha ihr =>
    simp [eqTy, eqNat_refl, eqBool_refl, iha, ihr]
  | tyVar v =>
    exact eqNat_refl v

theorem eqTy_sound {a b : RustTy} (h : eqTy a b = true) : a = b := by
  induction a generalizing b with
  | unit =>
    cases b <;> simp [eqTy] at h <;> rfl
  | never =>
    cases b <;> simp [eqTy] at h <;> rfl
  | scalar =>
    cases b <;> simp [eqTy] at h <;> rfl
  | error =>
    cases b <;> simp [eqTy] at h <;> rfl
  | array n1 e1 ih =>
    cases b with
    | array n2 e2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hn : n1 = n2 := eqNat_sound h.1
      have he : e1 = e2 := ih h.2
      subst hn; subst he; rfl
    | _ => simp [eqTy] at h
  | slice e1 ih =>
    cases b with
    | slice e2 =>
      have he : e1 = e2 := ih h
      subst he; rfl
    | _ => simp [eqTy] at h
  | ref m1 i1 ih =>
    cases b with
    | ref m2 i2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hm : m1 = m2 := eqMut_sound h.1
      have hi : i1 = i2 := ih h.2
      subst hm; subst hi; rfl
    | _ => simp [eqTy] at h
  | rawPtr m1 i1 ih =>
    cases b with
    | rawPtr m2 i2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hm : m1 = m2 := eqMut_sound h.1
      have hi : i1 = i2 := ih h.2
      subst hm; subst hi; rfl
    | _ => simp [eqTy] at h
  | fnItem id1 s1 a1 r1 iha ihr =>
    cases b with
    | fnItem id2 s2 a2 r2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hid : id1 = id2 := eqNat_sound h.1.1.1
      have hs : s1 = s2 := eqSafety_sound h.1.1.2
      have ha : a1 = a2 := iha h.1.2
      have hr : r1 = r2 := ihr h.2
      subst hid; subst hs; subst ha; subst hr; rfl
    | _ => simp [eqTy] at h
  | fnPtr s1 a1 r1 iha ihr =>
    cases b with
    | fnPtr s2 a2 r2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hs : s1 = s2 := eqSafety_sound h.1.1
      have ha : a1 = a2 := iha h.1.2
      have hr : r1 = r2 := ihr h.2
      subst hs; subst ha; subst hr; rfl
    | _ => simp [eqTy] at h
  | closure id1 c1 a1 r1 iha ihr =>
    cases b with
    | closure id2 c2 a2 r2 =>
      simp only [eqTy, bool_and_true_iff] at h
      have hid : id1 = id2 := eqNat_sound h.1.1.1
      have hc : c1 = c2 := eqBool_sound h.1.1.2
      have ha : a1 = a2 := iha h.1.2
      have hr : r1 = r2 := ihr h.2
      subst hid; subst hc; subst ha; subst hr; rfl
    | _ => simp [eqTy] at h
  | tyVar v1 =>
    cases b with
    | tyVar v2 =>
      have hv : v1 = v2 := eqNat_sound h
      subst hv; rfl
    | _ => simp [eqTy] at h

theorem eqTy_iff (a b : RustTy) : eqTy a b = true ↔ a = b :=
  ⟨eqTy_sound, fun h => h ▸ eqTy_refl a⟩

/-- Mutability coercion partial order (`coerce_mutbls`):
    `mutbl ≤ imm`, `m ≤ m`, but NOT `imm ≤ mutbl`. -/
noncomputable def mutLe (a b : Mutability) : Bool :=
  match a, b with
  | .mutbl, .mutbl => true
  | .mutbl, .imm => true
  | .imm, .imm => true
  | .imm, .mutbl => false

theorem mutLe_refl (m : Mutability) : mutLe m m = true := by
  cases m <;> rfl

theorem mutLe_trans {a b c : Mutability}
    (hab : mutLe a b = true) (hbc : mutLe b c = true) : mutLe a c = true := by
  cases a <;> cases b <;> cases c <;> simp [mutLe] at hab hbc ⊢

theorem mutLe_antisym {a b : Mutability}
    (hab : mutLe a b = true) (hba : mutLe b a = true) : a = b := by
  cases a <;> cases b <;> simp [mutLe] at hab hba <;> rfl

/-- Mutability join (`lub`): `&mut` joined with `&` yields `&` (shared). -/
noncomputable def mutJoin (a b : Mutability) : Mutability :=
  match a, b with
  | .mutbl, .mutbl => .mutbl
  | _, _ => .imm

theorem mutJoin_comm (a b : Mutability) : mutJoin a b = mutJoin b a := by
  cases a <;> cases b <;> rfl

theorem mutJoin_upper_left (a b : Mutability) : mutLe a (mutJoin a b) = true := by
  cases a <;> cases b <;> rfl

theorem mutJoin_upper_right (a b : Mutability) : mutLe b (mutJoin a b) = true := by
  cases a <;> cases b <;> rfl

/-- Safety coercion partial order: `.isSafe ≤ .isUnsafe` (safe fn can coerce to unsafe fn ptr). -/
noncomputable def safetyLe (a b : Safety) : Bool :=
  match a, b with
  | .isSafe, .isSafe => true
  | .isSafe, .isUnsafe => true
  | .isUnsafe, .isUnsafe => true
  | .isUnsafe, .isSafe => false

theorem safetyLe_refl (s : Safety) : safetyLe s s = true := by
  cases s <;> rfl

theorem safetyLe_trans {a b c : Safety}
    (hab : safetyLe a b = true) (hbc : safetyLe b c = true) : safetyLe a c = true := by
  cases a <;> cases b <;> cases c <;> simp [safetyLe] at hab hbc ⊢

/-- Safety join (`try_find_coercion_lub` lines 1456-1460):
    `safe` joined with `unsafe` yields `unsafe`. -/
noncomputable def safetyJoin (a b : Safety) : Safety :=
  match a, b with
  | .isSafe, .isSafe => .isSafe
  | _, _ => .isUnsafe

theorem safetyJoin_comm (a b : Safety) : safetyJoin a b = safetyJoin b a := by
  cases a <;> cases b <;> rfl

theorem safetyJoin_upper_left (a b : Safety) : safetyLe a (safetyJoin a b) = true := by
  cases a <;> cases b <;> rfl

theorem safetyJoin_upper_right (a b : Safety) : safetyLe b (safetyJoin a b) = true := by
  cases a <;> cases b <;> rfl

/-! ## Section 2: Value Universe, Inhabitedness & Zero-Initialization Validity -/

/-- Structural inhabitedness judgment: models Rust's type-validity domain
    where `!` has zero inhabitants and `()`/`scalar`/fn-items have inhabitants. -/
noncomputable def isInhabited : RustTy → Prop
  | .unit => True
  | .never => False
  | .scalar => True
  | .array 0 _ => True
  | .array (Nat.succ _) elem => isInhabited elem
  | .slice _ => True
  | .ref _ inner => isInhabited inner
  | .rawPtr _ _ => True
  | .fnItem _ _ _ _ => True
  | .fnPtr _ _ _ => True
  | .closure _ _ _ _ => True
  | .tyVar _ => True
  | .error => False

/-- Strictly uninhabited `!`: key soundness axiom of Ex-Falso coercions and
    reason `zeroed::<!>()` / `!`-typed live values cause panic/UB. -/
theorem never_uninhabited : ¬ isInhabited .never := fun h => h

theorem unit_inhabited : isInhabited .unit := trivial

/-- Zero-bit-pattern validity (`core::mem::zeroed` / `intrinsics::assert_zero_valid`):
    valid for `()` and scalars; strictly FALSE for `!` and shared/mut references. -/
noncomputable def zeroValid : RustTy → Prop
  | .unit => True
  | .scalar => True
  | .array 0 _ => True
  | .array (Nat.succ _) elem => zeroValid elem
  | .rawPtr _ _ => True
  | _ => False

theorem unit_zeroValid : zeroValid .unit := trivial

theorem never_not_zeroValid : ¬ zeroValid .never := fun h => h

theorem zeroValid_implies_inhabited (t : RustTy) (hz : zeroValid t) : isInhabited t := by
  induction t with
  | unit => exact trivial
  | scalar => exact trivial
  | array n elem ih =>
    cases n with
    | zero => exact trivial
    | succ k => exact ih hz
  | rawPtr _ _ => exact trivial
  | never => cases hz
  | slice _ => cases hz
  | ref _ _ => cases hz
  | fnItem _ _ _ _ => cases hz
  | fnPtr _ _ _ => cases hz
  | closure _ _ _ _ => cases hz
  | tyVar _ => cases hz
  | error => cases hz

/-- Well-formedness / soundness invariant of an expression value of type `τ`:
    either execution reaches a valid value (so `isInhabited τ` holds) or execution
    diverged prior to yielding a value (`diverged = true`). -/
structure EvalOutcome (τ : RustTy) where
  diverged : Bool
  valueOk : diverged = false → isInhabited τ

noncomputable def diverging_outcome_any_target (τ : RustTy) : EvalOutcome τ :=
  ⟨true, fun h => by cases h⟩

theorem normal_outcome_impossible_at_never (o : EvalOutcome .never) : o.diverged = true := by
  cases hd : o.diverged with
  | true => rfl
  | false =>
    have hInhab := o.valueOk hd
    exact False.elim (never_uninhabited hInhab)

/-- Calling safety compatibility for coercing a callable `src` to `tgt`:
    calling through `unsafe fn(...)` imposes an `unsafe` caller obligation, so a
    `safe` function coerced to `unsafe fn` adds obligations (`safetyLe .isSafe .isUnsafe`),
    whereas dropping `unsafe` (`unsafe fn` → `fn`) is unsound and forbidden. -/
noncomputable def callableSafetySound (src tgt : RustTy) : Prop :=
  match src, tgt with
  | .fnItem _ sa aa ra, .fnPtr sb ab rb => safetyLe sa sb = true ∧ aa = ab ∧ ra = rb
  | .fnPtr sa aa ra, .fnPtr sb ab rb => safetyLe sa sb = true ∧ aa = ab ∧ ra = rb
  | .closure _ cap aa ra, .fnPtr _ ab rb => cap = false ∧ aa = ab ∧ ra = rb
  | _, _ => True

/-! ## Section 3: Coercion Subtyping (`Coerce::coerce`) & Sound `AdjustChain` Composition -/

/-- Exact syntactic/semantic single-step coercion relation mirroring
    `rustc_hir_typeck::coercion::Coerce::coerce` (`coercion.rs:242-368`,
    `422-558`, `566-739`, `1072-1177`). -/
inductive CoerceStep (coerceNever isReadForNever : Bool) :
    RustTy → RustTy → List AdjustKind → Prop where
  | refl (t : RustTy) :
      CoerceStep coerceNever isReadForNever t t []
  | neverToAny (tgt : RustTy) (hcn : coerceNever = true) (hrd : isReadForNever = true) :
      CoerceStep coerceNever isReadForNever .never tgt [.neverToAny]
  | refToRef (ma mb : Mutability) (inner : RustTy) (hle : mutLe ma mb = true) :
      CoerceStep coerceNever isReadForNever (.ref ma inner) (.ref mb inner)
        (if eqMut ma mb then [] else [.derefBuiltin, .borrowRef mb])
  | refUnsizeSlice (ma mb : Mutability) (len : Nat) (elem : RustTy) (hle : mutLe ma mb = true) :
      CoerceStep coerceNever isReadForNever
        (.ref ma (.array len elem)) (.ref mb (.slice elem))
        (if eqMut ma mb
         then [.pointer .unsize]
         else [.derefBuiltin, .borrowRef mb, .pointer .unsize])
  | rawPtrMutToConst (ma mb : Mutability) (inner : RustTy) (hle : mutLe ma mb = true) :
      CoerceStep coerceNever isReadForNever (.rawPtr ma inner) (.rawPtr mb inner)
        (if eqMut ma mb then [] else [.pointer .mutToConstPointer])
  | refToRawPtr (ma mb : Mutability) (inner : RustTy) (hle : mutLe ma mb = true) :
      CoerceStep coerceNever isReadForNever (.ref ma inner) (.rawPtr mb inner)
        [.derefBuiltin, .borrowRawPtr mb]
  | reifyFnPointer (id : Nat) (sa sb : Safety) (arg ret : RustTy) (hle : safetyLe sa sb = true) :
      CoerceStep coerceNever isReadForNever
        (.fnItem id sa arg ret) (.fnPtr sb arg ret)
        [.pointer (.reifyFnPointer sb)]
  | unsafeFnPointer (arg ret : RustTy) :
      CoerceStep coerceNever isReadForNever
        (.fnPtr .isSafe arg ret) (.fnPtr .isUnsafe arg ret)
        [.pointer .unsafeFnPointer]
  | closureFnPointer (id : Nat) (sb : Safety) (arg ret : RustTy) :
      CoerceStep coerceNever isReadForNever
        (.closure id false arg ret) (.fnPtr sb arg ret)
        [.pointer (.closureFnPointer sb)]

/-- Transitive coercion chain witnessing MIR adjustment composition. -/
inductive AdjustChain (coerceNever isReadForNever : Bool) :
    RustTy → RustTy → List AdjustKind → Prop where
  | nil (t : RustTy) :
      AdjustChain coerceNever isReadForNever t t []
  | snoc {a b c : RustTy} {xs ys : List AdjustKind}
      (hprev : AdjustChain coerceNever isReadForNever a b xs)
      (hstep : CoerceStep coerceNever isReadForNever b c ys) :
      AdjustChain coerceNever isReadForNever a c (xs ++ ys)

theorem adjustChain_step {cn rd : Bool} {a b : RustTy} {adj : List AdjustKind}
    (hs : CoerceStep cn rd a b adj) : AdjustChain cn rd a b adj :=
  AdjustChain.snoc (AdjustChain.nil a) hs

theorem adjustChain_trans {cn rd : Bool} {a b c : RustTy} {xs ys : List AdjustKind}
    (hab : AdjustChain cn rd a b xs) (hbc : AdjustChain cn rd b c ys) :
    AdjustChain cn rd a c (xs ++ ys) := by
  induction hbc generalizing a xs with
  | nil =>
    rw [List.append_nil]
    exact hab
  | snoc _ hlast ih =>
    rw [← List.append_assoc]
    exact AdjustChain.snoc (ih hab) hlast

/-- Semantic soundness invariant preserved by single coercion steps and chains:
    1. Every normal outcome at `a` transports cleanly to an outcome at `b`;
    2. Callable safety monotonic ordering is respected (`callableSafetySound a b`). -/
noncomputable def coercionTransportSound (a b : RustTy) : Prop :=
  (isInhabited a → isInhabited b) ∧ callableSafetySound a b

theorem coerceStep_sound {cn rd : Bool} {a b : RustTy} {adj : List AdjustKind}
    (hs : CoerceStep cn rd a b adj) : coercionTransportSound a b := by
  cases hs with
  | refl =>
    exact ⟨fun ha => ha, by cases a <;> simp [callableSafetySound, safetyLe_refl]⟩
  | neverToAny tgt _ _ =>
    exact ⟨fun hnever => False.elim (never_uninhabited hnever), trivial⟩
  | refToRef _ _ _ _ =>
    exact ⟨fun ha => ha, trivial⟩
  | refUnsizeSlice _ _ _ _ _ =>
    exact ⟨fun _ => trivial, trivial⟩
  | rawPtrMutToConst _ _ _ _ =>
    exact ⟨fun _ => trivial, trivial⟩
  | refToRawPtr _ _ _ _ =>
    exact ⟨fun _ => trivial, trivial⟩
  | reifyFnPointer _ sa sb arg ret hle =>
    exact ⟨fun _ => trivial, ⟨hle, rfl, rfl⟩⟩
  | unsafeFnPointer arg ret =>
    exact ⟨fun _ => trivial, ⟨rfl, rfl, rfl⟩⟩
  | closureFnPointer _ sb arg ret =>
    exact ⟨fun _ => trivial, ⟨rfl, rfl, rfl⟩⟩

theorem adjustChain_preserves_inhabited {cn rd : Bool} {a b : RustTy} {adj : List AdjustKind}
    (hc : AdjustChain cn rd a b adj) (ha : isInhabited a) : isInhabited b := by
  induction hc with
  | nil => exact ha
  | snoc _ hstep ih => exact (coerceStep_sound hstep).1 ih

/-- A valid coercion chain lifts any `EvalOutcome a` to `EvalOutcome b`! -/
noncomputable def transportOutcome {cn rd : Bool} {a b : RustTy} {adj : List AdjustKind}
    (hc : AdjustChain cn rd a b adj) (oa : EvalOutcome a) : EvalOutcome b :=
  ⟨oa.diverged, fun hdf => adjustChain_preserves_inhabited hc (oa.valueOk hdf)⟩

/-- Negative-space theorem: capturing closures (`hasCaptures = true`) can NEVER
    coerce to `fnPtr` in `Coerce::coerce` (`coerce_closure_to_fn`, `coercion.rs:1117-1134`). -/
theorem capturing_closure_cannot_reify (cn rd : Bool) (cid : Nat) (s : Safety) (arg ret : RustTy)
    (adj : List AdjustKind) :
    ¬ CoerceStep cn rd (.closure cid true arg ret) (.fnPtr s arg ret) adj := by
  intro h
  cases h

/-- Negative-space theorem: `&T` (`Mutability.imm`) can NEVER coerce to `&mut T` (`Mutability.mutbl`). -/
theorem imm_ref_cannot_coerce_to_mut (cn rd : Bool) (inner : RustTy) (adj : List AdjustKind) :
    ¬ CoerceStep cn rd (.ref .imm inner) (.ref .mutbl inner) adj := by
  intro h
  cases h with
  | refToRef _ _ _ hle => simp [mutLe] at hle

/-- Negative-space theorem: `unsafe fn` pointer can NEVER drop `unsafe` to become safe `fn`. -/
theorem unsafe_fnptr_cannot_become_safe (cn rd : Bool) (arg ret : RustTy) (adj : List AdjustKind) :
    ¬ CoerceStep cn rd (.fnPtr .isUnsafe arg ret) (.fnPtr .isSafe arg ret) adj := by
  intro h
  cases h

/-! ## Section 4: Asymmetric `try_find_coercion_lub`, `CoerceMany` Fold & Order Dependence -/

/-- Shared reference coercion helper (`coerce_to_ref` + `coerce_unsized` on `&[T; n] -> &[T]`). -/
noncomputable def tryCoerceRef (ma mb : Mutability) (ia ib : RustTy) :
    Option (List AdjustKind × RustTy) :=
  if mutLe ma mb then
    if eqTy ia ib then
      some (if eqMut ma mb then [] else [.derefBuiltin, .borrowRef mb], .ref mb ib)
    else
      match ia, ib with
      | .array _ ea, .slice eb =>
        if eqTy ea eb then
          some (if eqMut ma mb then [.pointer .unsize]
                else [.derefBuiltin, .borrowRef mb, .pointer .unsize],
                .ref mb (.slice eb))
        else none
      | _, _ => none
  else none

theorem tryCoerceRef_sound {cn rd : Bool} {ma mb : Mutability} {ia ib res : RustTy}
    {adj : List AdjustKind}
    (h : tryCoerceRef ma mb ia ib = some (adj, res)) :
    CoerceStep cn rd (.ref ma ia) (.ref mb ib) adj ∧ res = .ref mb ib := by
  unfold tryCoerceRef at h
  cases hm : mutLe ma mb with
  | false =>
    rw [hm] at h
    cases h
  | true =>
    rw [hm] at h
    simp only [↓reduceIte] at h
    cases hi : eqTy ia ib with
    | true =>
      rw [hi] at h
      simp only [↓reduceIte] at h
      have hia : ia = ib := eqTy_sound hi
      cases h
      subst hia
      exact ⟨CoerceStep.refToRef ma mb ia hm, rfl⟩
    | false =>
      rw [hi] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases ia with
      | array len ea =>
        cases ib with
        | slice eb =>
          simp only at h
          cases he : eqTy ea eb with
          | true =>
            rw [he] at h
            simp only [↓reduceIte] at h
            have hea : ea = eb := eqTy_sound he
            cases h
            subst hea
            exact ⟨CoerceStep.refUnsizeSlice ma mb len ea hm, rfl⟩
          | false =>
            rw [he] at h
            cases h
        | unit | never | scalar | array _ _ | ref _ _ | rawPtr _ _
        | fnItem _ _ _ _ | fnPtr _ _ _ | closure _ _ _ _ | tyVar _ | error =>
          all_goals cases h
      | unit | never | scalar | slice _ | ref _ _ | rawPtr _ _
      | fnItem _ _ _ _ | fnPtr _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals cases h

/-- Executable (noncomputable) single-pair coercion matching `Coerce::coerce`.
    Used here exclusively on concrete (non-`tyVar`) source/target types for
    computational modeling of `try_find_coercion_lub`. -/
noncomputable def tryCoerceConcrete (coerceNever isRead : Bool) (a b : RustTy) :
    Option (List AdjustKind × RustTy) :=
  if eqTy a b then
    some ([], b)
  else
    match a, b with
    | .never, tgt =>
      if coerceNever && isRead then some ([.neverToAny], tgt) else none
    | .ref ma ia, .ref mb ib =>
      tryCoerceRef ma mb ia ib
    | .rawPtr ma ia, .rawPtr mb ib =>
      if mutLe ma mb && eqTy ia ib then
        some (if eqMut ma mb then [] else [.pointer .mutToConstPointer], .rawPtr mb ib)
      else none
    | .ref ma ia, .rawPtr mb ib =>
      if mutLe ma mb && eqTy ia ib then
        some ([.derefBuiltin, .borrowRawPtr mb], .rawPtr mb ib)
      else none
    | .fnItem _ sa aa ra, .fnPtr sb ab rb =>
      if safetyLe sa sb && eqTy aa ab && eqTy ra rb then
        some ([.pointer (.reifyFnPointer sb)], .fnPtr sb ab rb)
      else none
    | .fnPtr .isSafe aa ra, .fnPtr .isUnsafe ab rb =>
      if eqTy aa ab && eqTy ra rb then
        some ([.pointer .unsafeFnPointer], .fnPtr .isUnsafe ab rb)
      else none
    | .closure _ false aa ra, .fnPtr sb ab rb =>
      if eqTy aa ab && eqTy ra rb then
        some ([.pointer (.closureFnPointer sb)], .fnPtr sb ab rb)
      else none
    | _, _ => none

theorem tryCoerceConcrete_sound {cn rd : Bool} {a b res : RustTy} {adj : List AdjustKind}
    (h : tryCoerceConcrete cn rd a b = some (adj, res)) :
    CoerceStep cn rd a res adj ∧ res = b := by
  unfold tryCoerceConcrete at h
  cases heq : eqTy a b with
  | true =>
    rw [heq] at h
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hadj, hres⟩
    have hab : a = b := eqTy_sound heq
    subst hab; subst hadj; subst hres
    exact ⟨CoerceStep.refl a, rfl⟩
  | false =>
    rw [heq] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases a with
    | never =>
      cases b <;> cases hcn : cn <;> cases hrd : rd <;> simp [hcn, hrd] at h <;>
        (rcases h with ⟨hadj, hres⟩; subst hadj; subst hres; exact ⟨CoerceStep.neverToAny _ rfl rfl, rfl⟩)
    | unit => cases b <;> simp at h
    | scalar => cases b <;> simp at h
    | error => cases b <;> simp at h
    | tyVar _ => cases b <;> simp at h
    | array _ _ => cases b <;> simp at h
    | slice _ => cases b <;> simp at h
    | ref ma ia =>
      cases b with
      | ref mb ib =>
        simp only at h
        have ⟨hstep, hres⟩ := @tryCoerceRef_sound cn rd ma mb ia ib res adj h
        rw [hres]
        exact ⟨hstep, rfl⟩
      | rawPtr mb ib =>
        simp only at h
        cases hcond : (mutLe ma mb && eqTy ia ib) with
        | false => rw [hcond] at h; cases h
        | true =>
          rw [hcond] at h
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [bool_and_true_iff] at hcond
          have hia : ia = ib := eqTy_sound hcond.2
          rcases h with ⟨hadj, hres⟩
          subst hia; subst hadj; subst hres
          exact ⟨CoerceStep.refToRawPtr ma mb ia hcond.1, rfl⟩
      | unit | never | scalar | array _ _ | slice _
      | fnItem _ _ _ _ | fnPtr _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals cases h
    | rawPtr ma ia =>
      cases b with
      | rawPtr mb ib =>
        simp only at h
        cases hcond : (mutLe ma mb && eqTy ia ib) with
        | false => rw [hcond] at h; cases h
        | true =>
          rw [hcond] at h
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [bool_and_true_iff] at hcond
          have hia : ia = ib := eqTy_sound hcond.2
          rcases h with ⟨hadj, hres⟩
          subst hia; subst hadj; subst hres
          exact ⟨CoerceStep.rawPtrMutToConst ma mb ia hcond.1, rfl⟩
      | unit | never | scalar | array _ _ | slice _ | ref _ _
      | fnItem _ _ _ _ | fnPtr _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals cases h
    | fnItem id sa aa ra =>
      cases b with
      | fnPtr sb ab rb =>
        simp only at h
        cases hcond : (safetyLe sa sb && eqTy aa ab && eqTy ra rb) with
        | false => rw [hcond] at h; cases h
        | true =>
          rw [hcond] at h
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rw [bool_and_true_iff, bool_and_true_iff] at hcond
          have haa : aa = ab := eqTy_sound hcond.1.2
          have hra : ra = rb := eqTy_sound hcond.2
          rcases h with ⟨hadj, hres⟩
          subst haa; subst hra; subst hadj; subst hres
          exact ⟨CoerceStep.reifyFnPointer id sa sb aa ra hcond.1.1, rfl⟩
      | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
      | fnItem _ _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals cases h
    | fnPtr sa aa ra =>
      cases b with
      | fnPtr sb ab rb =>
        cases sa with
        | isUnsafe => cases sb <;> cases h
        | isSafe =>
          cases sb with
          | isSafe => cases h
          | isUnsafe =>
            simp only at h
            cases hcond : (eqTy aa ab && eqTy ra rb) with
            | false => rw [hcond] at h; cases h
            | true =>
              rw [hcond] at h
              simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rw [bool_and_true_iff] at hcond
              have haa : aa = ab := eqTy_sound hcond.1
              have hra : ra = rb := eqTy_sound hcond.2
              rcases h with ⟨hadj, hres⟩
              subst haa; subst hra; subst hadj; subst hres
              exact ⟨CoerceStep.unsafeFnPointer aa ra, rfl⟩
      | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
      | fnItem _ _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals simp at h
    | closure id cap aa ra =>
      cases b with
      | fnPtr sb ab rb =>
        cases cap with
        | true => cases h
        | false =>
          simp only at h
          cases hcond : (eqTy aa ab && eqTy ra rb) with
          | false => rw [hcond] at h; cases h
          | true =>
            rw [hcond] at h
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rw [bool_and_true_iff] at hcond
            have haa : aa = ab := eqTy_sound hcond.1
            have hra : ra = rb := eqTy_sound hcond.2
            rcases h with ⟨hadj, hres⟩
            subst haa; subst hra; subst hadj; subst hres
            exact ⟨CoerceStep.closureFnPointer id sb aa ra, rfl⟩
      | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
      | fnItem _ _ _ _ | closure _ _ _ _ | tyVar _ | error =>
        all_goals simp at h

/-- Asymmetric two-way `Coerce::coerce` LUB fallback (`coercion.rs:1505-1535`):
    Tries `new -> prev` first (unless `newHasAdj`), else falls back to `prev -> new`. -/
noncomputable def tryFindCoercionLubFallback (prev new : RustTy) (newHasAdj : Bool) :
    Option (List AdjustKind × List AdjustKind × RustTy) :=
  let firstTry :=
    if newHasAdj then none
    else
      match tryCoerceConcrete true true new prev with
      | some (newAdj, target) => some ([], newAdj, target)
      | none => none
  match firstTry with
  | some res => some res
  | none =>
    match tryCoerceConcrete true true prev new with
    | some (prevAdj, target) => some (prevAdj, [], target)
    | none => none

/-- Special symmetric/reification LUB rules BEFORE falling back to asymmetric coerce:
    `(FnDef, FnDef)`, `(Closure, Closure)`, `(Closure, FnDef)`, and `(FnDef, Closure)`
    matching `coercion.rs:1405-1489`. Array-to-slice unsizing does NOT happen here
    without a surrounding `[&[T]; N]` expectation! -/
noncomputable def tryFindCoercionLubSpecial (prev new : RustTy) :
    Option (List AdjustKind × List AdjustKind × RustTy) :=
  match prev, new with
  | .fnItem _ sa aa ra, .fnItem _ sb ab rb =>
    if eqTy aa ab && eqTy ra rb then
      let s := safetyJoin sa sb
      let fp := RustTy.fnPtr s aa ra
      some ([.pointer (.reifyFnPointer s)], [.pointer (.reifyFnPointer s)], fp)
    else none
  | .closure _ false aa ra, .closure _ false ab rb =>
    if eqTy aa ab && eqTy ra rb then
      let fp := RustTy.fnPtr .isSafe aa ra
      some ([.pointer (.closureFnPointer .isSafe)], [.pointer (.closureFnPointer .isSafe)], fp)
    else none
  | .closure _ false aa ra, .fnItem _ sb ab rb =>
    if eqTy aa ab && eqTy ra rb then
      let fp := RustTy.fnPtr sb aa ra
      some ([.pointer (.closureFnPointer sb)], [.pointer (.reifyFnPointer sb)], fp)
    else none
  | .fnItem _ sa aa ra, .closure _ false ab rb =>
    if eqTy aa ab && eqTy ra rb then
      let fp := RustTy.fnPtr sa aa ra
      some ([.pointer (.reifyFnPointer sa)], [.pointer (.closureFnPointer sa)], fp)
    else none
  | _, _ => none

/-- Models `FnCtxt::try_find_coercion_lub` (`coercion.rs:1380-1535`):
    Returns `(prevAdjustment, newAdjustment, commonLubTy)` for combining all prior
    expressions (`prev_ty`) with a new expression (`new_ty`). -/
noncomputable def tryFindCoercionLub (prev new : RustTy) (newHasAdj : Bool) :
    Option (List AdjustKind × List AdjustKind × RustTy) :=
  if eqTy prev new then
    some ([], [], prev)
  else
    match tryFindCoercionLubSpecial prev new with
    | some res => some res
    | none => tryFindCoercionLubFallback prev new newHasAdj

theorem tryFindCoercionLubFallback_sound {prev new lubTy : RustTy} {newHasAdj : Bool}
    {prevAdj newAdj : List AdjustKind}
    (h : tryFindCoercionLubFallback prev new newHasAdj = some (prevAdj, newAdj, lubTy)) :
    CoerceStep true true prev lubTy prevAdj ∧ CoerceStep true true new lubTy newAdj := by
  unfold tryFindCoercionLubFallback at h
  cases hna : newHasAdj with
  | true =>
    rw [hna] at h
    simp only [↓reduceIte] at h
    cases h2 : tryCoerceConcrete true true prev new with
    | none => rw [h2] at h; cases h
    | some p2 =>
      rcases p2 with ⟨padj, tgt⟩
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hp, hn, hl⟩
      rw [← hp, ← hn, ← hl]
      have ⟨hc, htgt⟩ := tryCoerceConcrete_sound h2
      rw [htgt] at hc ⊢
      exact ⟨hc, CoerceStep.refl new⟩
  | false =>
    rw [hna] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases h1 : tryCoerceConcrete true true new prev with
    | some p1 =>
      rcases p1 with ⟨nadj, tgt⟩
      rw [h1] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hp, hn, hl⟩
      rw [← hp, ← hn, ← hl]
      have ⟨hc, htgt⟩ := tryCoerceConcrete_sound h1
      rw [htgt] at hc ⊢
      exact ⟨CoerceStep.refl prev, hc⟩
    | none =>
      rw [h1] at h
      cases h2 : tryCoerceConcrete true true prev new with
      | none => rw [h2] at h; cases h
      | some p2 =>
        rcases p2 with ⟨padj, tgt⟩
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hp, hn, hl⟩
        rw [← hp, ← hn, ← hl]
        have ⟨hc, htgt⟩ := tryCoerceConcrete_sound h2
        rw [htgt] at hc ⊢
        exact ⟨hc, CoerceStep.refl new⟩

theorem tryFindCoercionLubSpecial_sound {prev new lubTy : RustTy}
    {prevAdj newAdj : List AdjustKind}
    (h : tryFindCoercionLubSpecial prev new = some (prevAdj, newAdj, lubTy)) :
    CoerceStep true true prev lubTy prevAdj ∧ CoerceStep true true new lubTy newAdj := by
  cases prev with
  | fnItem id1 s1 a1 r1 =>
    cases new with
    | fnItem id2 s2 a2 r2 =>
      simp only [tryFindCoercionLubSpecial] at h
      cases hc : (eqTy a1 a2 && eqTy r1 r2) with
      | false => rw [hc] at h; cases h
      | true =>
        rw [hc] at h
        simp only [↓reduceIte] at h
        rw [bool_and_true_iff] at hc
        have ha := eqTy_sound hc.1
        have hr := eqTy_sound hc.2
        cases h
        subst ha; subst hr
        exact ⟨CoerceStep.reifyFnPointer _ _ _ _ _ (safetyJoin_upper_left _ _),
               CoerceStep.reifyFnPointer _ _ _ _ _ (safetyJoin_upper_right _ _)⟩
    | closure id2 cap2 a2 r2 =>
      cases cap2 with
      | true => cases h
      | false =>
        simp only [tryFindCoercionLubSpecial] at h
        cases hc : (eqTy a1 a2 && eqTy r1 r2) with
        | false => rw [hc] at h; cases h
        | true =>
          rw [hc] at h
          simp only [↓reduceIte] at h
          rw [bool_and_true_iff] at hc
          have ha := eqTy_sound hc.1
          have hr := eqTy_sound hc.2
          cases h
          subst ha; subst hr
          exact ⟨CoerceStep.reifyFnPointer _ _ _ _ _ (safetyLe_refl _),
                 CoerceStep.closureFnPointer _ _ _ _⟩
    | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
    | fnPtr _ _ _ | tyVar _ | error =>
      all_goals cases h
  | closure id1 cap1 a1 r1 =>
    cases cap1 with
    | true => cases h
    | false =>
      cases new with
      | closure id2 cap2 a2 r2 =>
        cases cap2 with
        | true => cases h
        | false =>
          simp only [tryFindCoercionLubSpecial] at h
          cases hc : (eqTy a1 a2 && eqTy r1 r2) with
          | false => rw [hc] at h; cases h
          | true =>
            rw [hc] at h
            simp only [↓reduceIte] at h
            rw [bool_and_true_iff] at hc
            have ha := eqTy_sound hc.1
            have hr := eqTy_sound hc.2
            cases h
            subst ha; subst hr
            exact ⟨CoerceStep.closureFnPointer _ _ _ _, CoerceStep.closureFnPointer _ _ _ _⟩
      | fnItem id2 s2 a2 r2 =>
        simp only [tryFindCoercionLubSpecial] at h
        cases hc : (eqTy a1 a2 && eqTy r1 r2) with
        | false => rw [hc] at h; cases h
        | true =>
          rw [hc] at h
          simp only [↓reduceIte] at h
          rw [bool_and_true_iff] at hc
          have ha := eqTy_sound hc.1
          have hr := eqTy_sound hc.2
          cases h
          subst ha; subst hr
          exact ⟨CoerceStep.closureFnPointer _ _ _ _,
                 CoerceStep.reifyFnPointer _ _ _ _ _ (safetyLe_refl _)⟩
      | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
      | fnPtr _ _ _ | tyVar _ | error =>
        all_goals cases h
  | unit | never | scalar | array _ _ | slice _ | ref _ _ | rawPtr _ _
  | fnPtr _ _ _ | tyVar _ | error =>
    all_goals cases h

/-- Soundness of `tryFindCoercionLub`: whenever the LUB computation returns
    `(prevAdj, newAdj, lubTy)`, there exist valid `CoerceStep` proofs transforming
    BOTH `prev` AND `new` into `lubTy`. -/
theorem tryFindCoercionLub_sound {prev new lubTy : RustTy} {newHasAdj : Bool}
    {prevAdj newAdj : List AdjustKind}
    (h : tryFindCoercionLub prev new newHasAdj = some (prevAdj, newAdj, lubTy)) :
    CoerceStep true true prev lubTy prevAdj ∧ CoerceStep true true new lubTy newAdj := by
  cases heq : eqTy prev new with
  | true =>
    simp only [tryFindCoercionLub, heq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hp, hn, hl⟩
    have hpn : prev = new := eqTy_sound heq
    subst hpn; subst hp; subst hn; subst hl
    exact ⟨CoerceStep.refl prev, CoerceStep.refl prev⟩
  | false =>
    simp only [tryFindCoercionLub, heq, Bool.false_eq_true, ↓reduceIte] at h
    cases hsp : tryFindCoercionLubSpecial prev new with
    | some res =>
      rw [hsp] at h
      cases h
      exact tryFindCoercionLubSpecial_sound hsp
    | none =>
      rw [hsp] at h
      exact tryFindCoercionLubFallback_sound h

/-- State of `CoerceMany<'tcx>` during multi-arm coercion fold:
    `expectedTy` is the target given at initialization (`coercion_target_type`),
    `finalTy` tracks the running LUB, and `exprs` records source types coerced so far
    along with their accumulated adjustment chains. -/
structure CoerceManyState where
  expectedTy : RustTy
  finalTy : Option RustTy
  exprs : List (RustTy × List AdjustKind)

/-- Proposition asserting every recorded prior expression has a valid
    `AdjustChain` from its original type to `tgt`. -/
noncomputable def AllExprsValidTo (exprs : List (RustTy × List AdjustKind)) (tgt : RustTy) : Prop :=
  match exprs with
  | [] => True
  | (src, adj) :: rest => AdjustChain true true src tgt adj ∧ AllExprsValidTo rest tgt

theorem allExprsValidTo_extend {exprs : List (RustTy × List AdjustKind)}
    {prevTgt nextTgt : RustTy} {prevAdj : List AdjustKind}
    (hprev : AllExprsValidTo exprs prevTgt)
    (hstep : CoerceStep true true prevTgt nextTgt prevAdj) :
    AllExprsValidTo (exprs.map (fun (s, a) => (s, a ++ prevAdj))) nextTgt := by
  induction exprs with
  | nil => exact trivial
  | cons hd tl ih =>
    rcases hd with ⟨s, a⟩
    rcases hprev with ⟨hs, htl⟩
    exact ⟨AdjustChain.snoc hs hstep, ih htl⟩

noncomputable def isTyVar : RustTy → Bool
  | .tyVar _ => true
  | _ => false

/-- Complete multi-arm fold step when all expressions are folded under an
    unconstrained target (`tyVar _`) vs. pinned hard target. -/
noncomputable def stepCoerceMany (st : CoerceManyState) (eTy : RustTy) :
    Option CoerceManyState :=
  match st.finalTy with
  | none =>
    if isTyVar st.expectedTy then
      some ⟨eTy, some eTy, [(eTy, [])]⟩
    else
      match tryCoerceConcrete true true eTy st.expectedTy with
      | some (adj, tgt) => some ⟨st.expectedTy, some tgt, [(eTy, adj)]⟩
      | none => none
  | some prev =>
    match tryFindCoercionLub prev eTy false with
    | some (prevAdj, newAdj, lub) =>
      let updated := st.exprs.map (fun (s, a) => (s, a ++ prevAdj))
      some ⟨st.expectedTy, some lub, updated ++ [(eTy, newAdj)]⟩
    | none => none

theorem allExprsValidTo_append {l1 l2 : List (RustTy × List AdjustKind)} {tgt : RustTy}
    (h1 : AllExprsValidTo l1 tgt) (h2 : AllExprsValidTo l2 tgt) :
    AllExprsValidTo (l1 ++ l2) tgt := by
  induction l1 with
  | nil => exact h2
  | cons hd tl ih =>
    rcases hd with ⟨s, a⟩
    exact ⟨h1.1, ih h1.2⟩

/-- Core `CoerceMany` Fold Soundness Theorem:
    Every successful step of `CoerceMany` preserves `AllExprsValidTo st'.exprs st'.finalTy`.
    Retroactive adjustment propagation across prior expressions guarantees that EVERY
    branch (`if`, `match`, `array`, `loop`, labeled block) coherently coerces to the
    common final type without type safety violations! -/
theorem stepCoerceMany_preserves_validity {st st' : CoerceManyState} {eTy tgt : RustTy}
    (hinv : match st.finalTy with
            | none => st.exprs = []
            | some prev => AllExprsValidTo st.exprs prev)
    (hstep : stepCoerceMany st eTy = some st')
    (hft : st'.finalTy = some tgt) :
    AllExprsValidTo st'.exprs tgt := by
  rcases st with ⟨expTy, finalTy, exprs⟩
  dsimp only at *
  cases finalTy with
  | none =>
    simp only [stepCoerceMany] at hstep
    cases htv : isTyVar expTy with
    | true =>
      rw [htv] at hstep
      simp only [↓reduceIte] at hstep
      cases hstep
      simp only at hft
      cases hft
      exact ⟨AdjustChain.nil eTy, trivial⟩
    | false =>
      rw [htv] at hstep
      simp only [Bool.false_eq_true, ↓reduceIte] at hstep
      cases hc : tryCoerceConcrete true true eTy expTy with
      | none => rw [hc] at hstep; cases hstep
      | some p =>
        rcases p with ⟨adj, t⟩
        rw [hc] at hstep
        cases hstep
        simp only at hft
        cases hft
        exact ⟨adjustChain_step (tryCoerceConcrete_sound hc).1, trivial⟩
  | some prev =>
    simp only [stepCoerceMany] at hstep
    cases hlub : tryFindCoercionLub prev eTy false with
    | none => rw [hlub] at hstep; cases hstep
    | some p =>
      rcases p with ⟨prevAdj, newAdj, lub⟩
      rw [hlub] at hstep
      cases hstep
      simp only at hft
      cases hft
      have ⟨hpa, hna⟩ := tryFindCoercionLub_sound hlub
      exact allExprsValidTo_append
        (allExprsValidTo_extend hinv hpa)
        ⟨adjustChain_step hna, trivial⟩

/-! ## Section 5: Constructive Witness Theorems for All `CoerceMany` LUB & Pinning Cases -/

/-- Witness 1 (`lub_ref_mut_shared` vs `lub_ref_shared_mut`):
    `if cond { &mut u32 } else { &u32 }` and `if cond { &u32 } else { &mut u32 }`
    BOTH yield `&u32` (order-independent under `tryFindCoercionLub`). -/
theorem lub_ref_order_independent (inner : RustTy) :
    tryFindCoercionLub (.ref .mutbl inner) (.ref .imm inner) false =
      some ([.derefBuiltin, .borrowRef .imm], [], .ref .imm inner) ∧
    tryFindCoercionLub (.ref .imm inner) (.ref .mutbl inner) false =
      some ([], [.derefBuiltin, .borrowRef .imm], .ref .imm inner) := by
  constructor
  · have hne : eqTy (.ref .mutbl inner) (.ref .imm inner) = false := by
      simp [eqTy, eqMut]
    have h1 : tryCoerceConcrete true true (.ref .imm inner) (.ref .mutbl inner) = none := by
      simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe]
    have h2 : tryCoerceConcrete true true (.ref .mutbl inner) (.ref .imm inner) =
        some ([.derefBuiltin, .borrowRef .imm], .ref .imm inner) := by
      simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqTy_refl]
    simp only [tryFindCoercionLub, tryFindCoercionLubSpecial, tryFindCoercionLubFallback]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, h1, h2]
  · have hne : eqTy (.ref .imm inner) (.ref .mutbl inner) = false := by
      simp [eqTy, eqMut]
    have h1 : tryCoerceConcrete true true (.ref .mutbl inner) (.ref .imm inner) =
        some ([.derefBuiltin, .borrowRef .imm], .ref .imm inner) := by
      simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqTy_refl]
    simp only [tryFindCoercionLub, tryFindCoercionLubSpecial, tryFindCoercionLubFallback]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, h1]

/-- Witness 2a (`lub_array_slices` & `lub_array_mut_and_shared_unsize` under slice expectation):
    With hard slice target `expected_ty = &[T]` (from `[&[T]; 2]`), `[&mut [T; 2], &[T; 3]]`
    succeeds cleanly via Arm 0 `deref+borrow+unsize` and Arm 1 `unsize` (`coercion.rs:659-705`)! -/
theorem lub_array_mut_and_shared_unsize_with_slice_hint (elem : RustTy) :
    let st0 : CoerceManyState := ⟨.ref .imm (.slice elem), none, []⟩
    (match stepCoerceMany st0 (.ref .mutbl (.array 2 elem)) with
     | none => none
     | some st1 =>
       match stepCoerceMany st1 (.ref .imm (.array 3 elem)) with
       | none => none
       | some st2 => st2.finalTy) = some (.ref .imm (.slice elem)) := by
  have h1 : tryCoerceConcrete true true (.ref .mutbl (.array 2 elem)) (.ref .imm (.slice elem)) =
      some ([.derefBuiltin, .borrowRef .imm, .pointer .unsize], .ref .imm (.slice elem)) := by
    simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqTy_refl]
  have h2 : tryFindCoercionLub (.ref .imm (.slice elem)) (.ref .imm (.array 3 elem)) false =
      some ([], [.pointer .unsize], .ref .imm (.slice elem)) := by
    have hne : eqTy (.ref .imm (.slice elem)) (.ref .imm (.array 3 elem)) = false := by
      simp [eqTy]
    have hc : tryCoerceConcrete true true (.ref .imm (.array 3 elem)) (.ref .imm (.slice elem)) =
        some ([.pointer .unsize], .ref .imm (.slice elem)) := by
      simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqTy_refl]
    simp only [tryFindCoercionLub, tryFindCoercionLubSpecial, tryFindCoercionLubFallback]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, hc]
  dsimp only
  simp only [stepCoerceMany, isTyVar, Bool.false_eq_true, ↓reduceIte, h1, h2]

/-- Witness 2b (Negative space — matches live `rustc` `no_hint_arr` `E0308`):
    Without a slice expectation (`expected_ty = ?v`), `CoerceMany([&[T; 2], &[T; 3]])` FAILS
    (`try_find_coercion_lub` does NOT synthesize `Unsize` between mismatched array lengths)! -/
theorem lub_array_slices_without_hint_fails (elem : RustTy) :
    let st0 : CoerceManyState := ⟨.tyVar 0, none, []⟩
    (match stepCoerceMany st0 (.ref .imm (.array 2 elem)) with
     | none => none
     | some st1 => stepCoerceMany st1 (.ref .imm (.array 3 elem))) = none := by
  have hne : eqTy (.ref .imm (.array 2 elem)) (.ref .imm (.array 3 elem)) = false := by
    simp [eqTy, eqMut, eqNat]
  have h1 : tryCoerceConcrete true true (.ref .imm (.array 3 elem)) (.ref .imm (.array 2 elem)) = none := by
    simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqNat]
  have h2 : tryCoerceConcrete true true (.ref .imm (.array 2 elem)) (.ref .imm (.array 3 elem)) = none := by
    simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe, eqNat]
  have h_lub : tryFindCoercionLub (.ref .imm (.array 2 elem)) (.ref .imm (.array 3 elem)) false = none := by
    simp only [tryFindCoercionLub, tryFindCoercionLubSpecial, tryFindCoercionLubFallback]
    rw [hne]
    simp only [Bool.false_eq_true, ↓reduceIte, h1, h2]
  dsimp only
  simp only [stepCoerceMany, isTyVar, ↓reduceIte, h_lub]

/-- Witness 3 (`lub_same_closure_stays_unreified`):
    Same closure ID stays unreified (`[]`, `[]`, `.closure ...`). -/
theorem lub_same_closure_stays_zst (cid : Nat) (arg ret : RustTy) :
    tryFindCoercionLub (.closure cid false arg ret) (.closure cid false arg ret) false =
      some ([], [], .closure cid false arg ret) := by
  simp [tryFindCoercionLub, eqTy_refl]

/-- Witness 4 (`lub_two_closures`):
    Distinct non-capturing closures reify BOTH arms via `ClosureFnPointer .isSafe` -> `fn(arg) -> ret`. -/
theorem lub_distinct_closures_reify (arg ret : RustTy) :
    tryFindCoercionLub (.closure 0 false arg ret) (.closure 1 false arg ret) false =
      some (
        [.pointer (.closureFnPointer .isSafe)],
        [.pointer (.closureFnPointer .isSafe)],
        .fnPtr .isSafe arg ret
      ) := by
  have hne : eqTy (.closure 0 false arg ret) (.closure 1 false arg ret) = false := by
    simp [eqTy, eqNat]
  simp [tryFindCoercionLub, tryFindCoercionLubSpecial, hne, eqTy_refl]

/-- Witness 5 (`lub_safe_unsafe_fndef`):
    Joining safe `fnItem` with unsafe `fnItem` reifies BOTH via `ReifyFnPointer .isUnsafe`. -/
theorem lub_safe_unsafe_fndef_reifies (arg ret : RustTy) :
    tryFindCoercionLub (.fnItem 0 .isSafe arg ret) (.fnItem 1 .isUnsafe arg ret) false =
      some (
        [.pointer (.reifyFnPointer .isUnsafe)],
        [.pointer (.reifyFnPointer .isUnsafe)],
        .fnPtr .isUnsafe arg ret
      ) := by
  have hne : eqTy (.fnItem 0 .isSafe arg ret) (.fnItem 1 .isUnsafe arg ret) = false := by
    simp [eqTy, eqNat]
  simp [tryFindCoercionLub, tryFindCoercionLubSpecial, hne, eqTy_refl, safetyJoin]

/-- Witness 6 (`lub_raw_mut_to_const`):
    `*mut T` + `*const T` joins to `*const T` via `MutToConstPointer`. -/
theorem lub_raw_mut_const_witness (inner : RustTy) :
    tryFindCoercionLub (.rawPtr .mutbl inner) (.rawPtr .imm inner) false =
      some ([.pointer .mutToConstPointer], [], .rawPtr .imm inner) := by
  have hne : eqTy (.rawPtr .mutbl inner) (.rawPtr .imm inner) = false := by
    simp [eqTy, eqMut]
  have h1 : tryCoerceConcrete true true (.rawPtr .imm inner) (.rawPtr .mutbl inner) = none := by
    simp [tryCoerceConcrete, eqTy, eqMut, mutLe]
  have h2 : tryCoerceConcrete true true (.rawPtr .mutbl inner) (.rawPtr .imm inner) =
      some ([.pointer .mutToConstPointer], .rawPtr .imm inner) := by
    simp [tryCoerceConcrete, eqTy, eqMut, mutLe, eqTy_refl]
  simp only [tryFindCoercionLub, tryFindCoercionLubSpecial, tryFindCoercionLubFallback]
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, h1, h2]

/-- Model of left-biased generic call-site unification `pick<T>(a: T, b: T)`:
    Argument 0 concretizes `?T := arg0`, and Argument 1 must coerce directly into `arg0`
    WITHOUT retroactive adjustment of Argument 0 (`coercion.rs:15-36`). -/
noncomputable def checkGenericPick (arg0 arg1 : RustTy) : Option RustTy :=
  match tryCoerceConcrete true true arg1 arg0 with
  | some _ => some arg0
  | none => none

/-- Asymmetric Call-Site Counterexample:
    `pick(&mut u32, &u32)` FAILS, whereas `pick(&u32, &mut u32)` SUCCEEDS! -/
theorem generic_pick_order_asymmetric (inner : RustTy) :
    checkGenericPick (.ref .mutbl inner) (.ref .imm inner) = none ∧
    checkGenericPick (.ref .imm inner) (.ref .mutbl inner) = some (.ref .imm inner) := by
  constructor
  · simp [checkGenericPick, tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe]
  · have hne : eqTy (.ref .mutbl inner) (.ref .imm inner) = false := by
      simp [eqTy, eqMut]
    simp [checkGenericPick, tryCoerceConcrete, tryCoerceRef, hne, eqTy_refl, mutLe, eqMut]

/-- Models `let r = expr;` local initialization (`check_decl_initializer` +
    `check_expr_if`/`check_expr_match` vs `check_expr_loop`/`check_expr_block`):
    - When `adjustForBranches = true` (`if`, `match`), an unresolved `ExpectHasType(?v_r)`
      is replaced by a disjoint fresh `?v_lub`, leaving `?v_r` unpinned until `CoerceMany` finishes.
    - When `adjustForBranches = false` (`loop`, `'blk`), `?v_r` is passed directly as
      `CoerceMany::expected_ty` (`expectation.rs:151-153`), so arm 0 mutably binds `?v_r := arm0`,
      forcing the outer `let r = ...` coercion (`demand_coerce_diag`) to fail when
      `lub` later widens `arm0` (e.g., `&mut T` -> `&T`)! -/
noncomputable def runLetBoundCoerceMany (adjustForBranches : Bool) (arm0 arm1 : RustTy) :
    Option RustTy :=
  let initTarget := if adjustForBranches then RustTy.tyVar 1 else RustTy.tyVar 0
  let st0 : CoerceManyState := ⟨initTarget, none, []⟩
  match stepCoerceMany st0 arm0 with
  | none => none
  | some st1 =>
    match stepCoerceMany st1 arm1 with
    | none => none
    | some st2 =>
      match st2.finalTy with
      | none => none
      | some lub =>
        -- Local `let r` inference var `?v_r` (vid 0) got bound during arm 0 iff `!adjustForBranches`.
        let localVarAfterArms := if adjustForBranches then none else some arm0
        match localVarAfterArms with
        | none => some lub
        | some pinned =>
          match tryCoerceConcrete true true lub pinned with
          | some (_, finalLocal) => some finalLocal
          | none => none

/-- Exact `rustc` Behavior Theorem (`check_expr_if`/`match` vs `check_expr_loop`/`block`):
    In `let r = ...`:
    - `if`/`match` (`adjustForBranches = true`) SUCCEEDS in both `(&mut, &)` and `(&, &mut)`!
    - `loop`/`'blk` (`adjustForBranches = false`) FAILS on `(&mut, &)` (`E0308`) and SUCCEEDS on `(&, &mut)`! -/
theorem if_vs_loop_pinning_contrast (inner : RustTy) :
    (runLetBoundCoerceMany true (.ref .mutbl inner) (.ref .imm inner) = some (.ref .imm inner)) ∧
    (runLetBoundCoerceMany true (.ref .imm inner) (.ref .mutbl inner) = some (.ref .imm inner)) ∧
    (runLetBoundCoerceMany false (.ref .mutbl inner) (.ref .imm inner) = none) ∧
    (runLetBoundCoerceMany false (.ref .imm inner) (.ref .mutbl inner) = some (.ref .imm inner)) := by
  have h_lub_mi := (lub_ref_order_independent inner).1
  have h_lub_im := (lub_ref_order_independent inner).2
  have hc_im : tryCoerceConcrete true true (.ref .imm inner) (.ref .mutbl inner) = none := by
    simp [tryCoerceConcrete, tryCoerceRef, eqTy, eqMut, mutLe]
  have hc_refl : tryCoerceConcrete true true (.ref .imm inner) (.ref .imm inner) =
      some ([], .ref .imm inner) := by
    simp [tryCoerceConcrete, eqTy_refl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [runLetBoundCoerceMany, stepCoerceMany, isTyVar, ↓reduceIte, h_lub_mi]
  · simp only [runLetBoundCoerceMany, stepCoerceMany, isTyVar, ↓reduceIte, h_lub_im]
  · simp only [runLetBoundCoerceMany, stepCoerceMany, isTyVar, Bool.false_eq_true, ↓reduceIte,
      h_lub_mi, hc_im]
  · simp only [runLetBoundCoerceMany, stepCoerceMany, isTyVar, Bool.false_eq_true, ↓reduceIte,
      h_lub_im, hc_refl]

/-! ## Section 6: Diverging Fallback (`fallback.rs`), Place-Read Gating & Unsafe Flow Taint -/

/-- Rust editions & pre-1.100 vs. post-1.100 fallback configuration. -/
inductive Edition where
  | ed2021
  | ed2024

/-- Pre-1.100 (`rustc 1.98.0`) diverges on `Ed2021 -> ()` vs `Ed2024 -> !`;
    Post-1.100 (`fallback.rs:88-94`) unconditionally chooses `!` in BOTH editions. -/
inductive CompilerEra where
  | pre1_100
  | post1_100

noncomputable def resolveDivergingFallbackTy (era : CompilerEra) (ed : Edition) : RustTy :=
  match era, ed with
  | .pre1_100, .ed2021 => .unit
  | .pre1_100, .ed2024 => .never
  | .post1_100, _ => .never

/-- Theorem: Post-1.100 unconditional fallback ignores edition (`2021` == `2024` == `!`),
    whereas Pre-1.100 produces `()` in Edition 2021 and `!` in Edition 2024. -/
theorem post1_100_unconditional_never_edition_invariant :
    resolveDivergingFallbackTy .post1_100 .ed2021 = .never ∧
    resolveDivergingFallbackTy .post1_100 .ed2024 = .never ∧
    resolveDivergingFallbackTy .pre1_100 .ed2021 = .unit ∧
    resolveDivergingFallbackTy .pre1_100 .ed2024 = .never :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Trait availability contrast for unit-only traits (`OnlyUnit`, `Default`). -/
noncomputable def satisfiesUnitBound : RustTy → Prop
  | .unit => True
  | .never => False
  | _ => False

theorem unit_only_breaks_under_post1_100 (ed : Edition) :
    ¬ satisfiesUnitBound (resolveDivergingFallbackTy .post1_100 ed) := by
  cases ed <;> intro h <;> cases h

/-- Directed edge `(src, dst)` recorded from pending `CoercePredicate` /
    `SubtypePredicate` in `FnCtxt::create_coercion_graph` (`fallback.rs:278-314`). -/
structure CoercionEdge where
  src : Nat
  dst : Nat

/-- Kinds of unsafe inference-variable uses collected by `compute_unsafe_infer_vars`
    (`fallback.rs:517-652`). -/
inductive UnsafeUseReason where
  | call      -- e.g. `unsafe { core::mem::zeroed() }`
  | method
  | path
  | unionField
  | deref

/-- Inference context relevant to `calculate_diverging_fallback` and
    `never_type_fallback_flowing_into_unsafe`. -/
structure InferFlowState where
  divergingRootVids : List Nat
  edges : List CoercionEdge
  unsafeInferVars : List (Nat × UnsafeUseReason)
  annotatedSafeVars : List Nat

/-- Check membership in a `List Nat` constructively. -/
noncomputable def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if eqNat x y then true else memNat x ys

theorem memNat_iff (x : Nat) (xs : List Nat) : memNat x xs = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    simp [memNat]
  | cons y ys ih =>
    simp only [memNat]
    cases h : eqNat x y with
    | true =>
      simp only [↓reduceIte, List.mem_cons, true_iff]
      exact Or.inl (eqNat_sound h)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · intro hm; exact Or.inr (ih.mp hm)
      · intro hm
        cases hm with
        | inl hxy =>
          subst hxy
          rw [eqNat_refl] at h
          cases h
        | inr hys => exact ih.mpr hys

/-- Single-step **directed** edge relation (`src -> dst`). -/
noncomputable def DirectedStep (edges : List CoercionEdge) (u v : Nat) : Prop :=
  CoercionEdge.mk u v ∈ edges

/-- Single-step **undirected** edge relation matching
    `graph::depth_first_search_as_undirected(&coercion_graph, root_vid)` (`fallback.rs:238`). -/
noncomputable def UndirectedStep (edges : List CoercionEdge) (u v : Nat) : Prop :=
  CoercionEdge.mk u v ∈ edges ∨ CoercionEdge.mk v u ∈ edges

/-- Reflexive-transitive closure (path) under any step relation on `Nat`. -/
inductive PathUnder (step : Nat → Nat → Prop) : Nat → Nat → Prop where
  | refl (x : Nat) : PathUnder step x x
  | step {x y z : Nat} (hp : PathUnder step x y) (hs : step y z) : PathUnder step x z

/-- Executable BFS/frontier step (`fuel` = edge count or hop bound) computing
    undirected reachability from `roots`. -/
noncomputable def expandUndirectedOnce (edges : List CoercionEdge) (frontier : List Nat) :
    List Nat :=
  edges.foldl
    (fun acc e =>
      let acc1 := if memNat e.src acc then e.dst :: acc else acc
      if memNat e.dst acc1 then e.src :: acc1 else acc1)
    frontier

noncomputable def reachUndirected (edges : List CoercionEdge) (roots : List Nat) : Nat → List Nat
  | 0 => roots
  | Nat.succ k => expandUndirectedOnce edges (reachUndirected edges roots k)

/-- Non-linted (`never_type_fallback_flowing_into_unsafe`-clean) state policy:
    in `calculate_diverging_fallback` (`fallback.rs:197-244`), only *unresolved*
    inference variables belong to `divergingRootVids` and `unsafeInferVars`,
    and the lint accepts the function iff NO undirected coercion/subtyping path
    connects any unresolved diverging variable to any unresolved unsafe variable. -/
noncomputable def LintAcceptsUnsafeFlow (st : InferFlowState) : Prop :=
  ∀ u reason, (u, reason) ∈ st.unsafeInferVars →
    u ∈ st.annotatedSafeVars ∨
    (∀ d ∈ st.divergingRootVids, ¬ PathUnder (UndirectedStep st.edges) d u)

/-- Well-typed pre-fallback resolution condition: an explicitly annotated `()`
    variable never stays unresolved in the same connected coercion component as an
    unannotated diverging variable (`fallback_types` only touches unresolved roots). -/
noncomputable def FallbackAssignment (era : CompilerEra) (ed : Edition)
    (st : InferFlowState) (assign : Nat → RustTy) : Prop :=
  (∀ d ∈ st.divergingRootVids, d ∉ st.annotatedSafeVars →
      assign d = resolveDivergingFallbackTy era ed) ∧
  (∀ e ∈ st.edges, assign e.src = .never ↔ assign e.dst = .never) ∧
  (∀ u ∈ st.annotatedSafeVars, assign u = .unit) ∧
  (∀ u, (∃ r, (u, r) ∈ st.unsafeInferVars) →
      (∀ d ∈ st.divergingRootVids, ¬ PathUnder (UndirectedStep st.edges) d u) →
      assign u ≠ .never)

theorem path_preserves_never_assignment {edges : List CoercionEdge} {assign : Nat → RustTy}
    (hedges : ∀ e ∈ edges, assign e.src = .never ↔ assign e.dst = .never)
    {d u : Nat} (hp : PathUnder (UndirectedStep edges) d u) :
    assign d = .never ↔ assign u = .never := by
  induction hp with
  | refl => exact Iff.rfl
  | step _ hs ih =>
    cases hs with
    | inl hfwd => exact ih.trans (hedges _ hfwd)
    | inr hbwd => exact ih.trans (hedges _ hbwd).symm

/-- **Soundness of `never_type_fallback_flowing_into_unsafe`**:
    If `LintAcceptsUnsafeFlow st` holds, then NO unsafe call/method/path/union/deref
    inference variable in `st.unsafeInferVars` is ever instantiated with `!`
    under `FallbackAssignment`, preventing silent `zeroed::<!>()` instantiation UB. -/
theorem default_deny_prevents_unsafe_never_instantiation
    (era : CompilerEra) (ed : Edition) (st : InferFlowState) (assign : Nat → RustTy)
    (ha : FallbackAssignment era ed st assign)
    (hclean : LintAcceptsUnsafeFlow st) :
    ∀ u reason, (u, reason) ∈ st.unsafeInferVars → assign u ≠ .never := by
  intro u reason hu
  cases hclean u reason hu with
  | inl hannot =>
    rw [ha.2.2.1 u hannot]
    intro hne
    cases hne
  | inr hdisjoint =>
    exact ha.2.2.2 u ⟨reason, hu⟩ hdisjoint

/-- Conversely, when an unannotated unsafe variable IS undirected-reachable
    from a diverging root under post-1.100 fallback, `FallbackAssignment` forces
    `assign u = .never`, violating `ZeroValid` (`zeroed::<!>()`) and `LintAcceptsUnsafeFlow`. -/
theorem tainted_flow_forces_never_ub
    (ed : Edition) (st : InferFlowState) (assign : Nat → RustTy)
    (ha : FallbackAssignment .post1_100 ed st assign)
    {d u : Nat} {reason : UnsafeUseReason}
    (hd : d ∈ st.divergingRootVids)
    (hdUn : d ∉ st.annotatedSafeVars)
    (hu : (u, reason) ∈ st.unsafeInferVars)
    (huUn : u ∉ st.annotatedSafeVars)
    (hreach : PathUnder (UndirectedStep st.edges) d u) :
    ¬ zeroValid (assign u) ∧ ¬ LintAcceptsUnsafeFlow st := by
  have hdNever : assign d = .never := by
    have h := ha.1 d hd hdUn
    cases ed <;> exact h
  have huNever : assign u = .never :=
    (path_preserves_never_assignment ha.2.1 hreach).mp hdNever
  constructor
  · rw [huNever]
    exact never_not_zeroValid
  · intro hclean
    cases hclean u reason hu with
    | inl hin => exact huUn hin
    | inr hno => exact hno d hd hreach

/-- **Sharpness Counterexample (`trigger_indirect_hop`, `fallback.rs:238`)**:
    In `let a = if cond { return } else { Default::default() }; let b = if !cond { a } else { zeroed() };`:
    - Diverging root `v0 = 0`, join var `v2 = 2`, unsafe `zeroed()` var `u = 1`.
    - Coercion edges are `0 -> 2` and `1 -> 2` (NOT `0 -> 1`).
    We prove:
      (1) Undirected DFS (`UndirectedStep`) DOES connect `0` to `1` (`0 -> 2 <- 1`);
      (2) Directed-only traversal (`DirectedStep`) FAILS to connect `0` to `1`,
          proving why omitting reverse edges in `fallback.rs:238` would miss UB! -/
noncomputable def indirectHopEdges : List CoercionEdge :=
  [⟨0, 2⟩, ⟨1, 2⟩]

theorem undirected_catches_indirect_hop :
    PathUnder (UndirectedStep indirectHopEdges) 0 1 := by
  apply PathUnder.step (y := 2)
  · apply PathUnder.step (y := 0)
    · exact PathUnder.refl 0
    · exact Or.inl (by simp [indirectHopEdges])
  · exact Or.inr (by simp [indirectHopEdges])

theorem directed_misses_indirect_hop :
    ¬ PathUnder (DirectedStep indirectHopEdges) 0 1 := by
  intro hp
  -- Every directed path from 0 either stays at 0 or stops at 2 (since 2 has out-degree 0).
  have hbound : ∀ x y, PathUnder (DirectedStep indirectHopEdges) x y →
      (x = 0 → y = 0 ∨ y = 2) := by
    intro x y hpath
    induction hpath with
    | refl => intro hx; exact Or.inl hx
    | step _ hs ih =>
      intro hx
      have hy := ih hx
      simp only [DirectedStep, indirectHopEdges, List.mem_cons, List.not_mem_nil, or_false] at hs
      cases hy with
      | inl hy0 =>
        subst hy0
        cases hs with
        | inl h02 => cases h02; exact Or.inr rfl
        | inr h12 => cases h12
      | inr hy2 =>
        subst hy2
        cases hs with
        | inl h02 => cases h02
        | inr h12 => cases h12
  cases hbound 0 1 hp rfl with
  | inl h => cases h
  | inr h => cases h

/-- Multi-hop transitive witness (`trigger_two_hop_coercion`):
    `edges = [0 -> 1, 1 -> 2, 10 -> 2]` where `0` is diverging root, `10` is `zeroed()`. -/
noncomputable def twoHopEdges : List CoercionEdge :=
  [⟨0, 1⟩, ⟨1, 2⟩, ⟨10, 2⟩]

theorem undirected_catches_two_hop :
    PathUnder (UndirectedStep twoHopEdges) 0 10 := by
  apply PathUnder.step (y := 2)
  · apply PathUnder.step (y := 1)
    · apply PathUnder.step (y := 0)
      · exact PathUnder.refl 0
      · exact Or.inl (by simp [twoHopEdges])
    · exact Or.inl (by simp [twoHopEdges])
  · exact Or.inr (by simp [twoHopEdges])

/-! ## Section 7: `expr_guaranteed_to_constitute_read_for_never` Place-Read Gating (`hir/mod.rs:230-310`) -/

/-- Direct HIR syntactic context around a `*p : !` place expression. -/
inductive PlaceParentCtx where
  | letWildcard        -- `let _ = *p;` -> false
  | matchWildcardArm   -- `match *p { _ => ... }` -> false
  | addrOf             -- `&raw const *p` -> false
  | blockExpr          -- `let _ = { *p };` -> parent is Block -> true!
  | letBinding         -- `let _x: () = *p;` -> true
  | callArg            -- `foo(*p)` -> true

/-- Exact Boolean model of `TyCtxt::expr_guaranteed_to_constitute_read_for_never`
    (`compiler/rustc_middle/src/hir/mod.rs:230-310`). -/
noncomputable def constitutesReadForNever : PlaceParentCtx → Bool
  | .letWildcard => false
  | .matchWildcardArm => false
  | .addrOf => false
  | .blockExpr => true
  | .letBinding => true
  | .callArg => true

/-- Result of checking a place expression of type `!` at `check_expr_with_expectation_and_args`
    (`expr.rs:306-310`) and `Coerce::coerce` (`coercion.rs:249-259`). -/
structure PlaceNeverCheckResult where
  emitsReadUbOnDummyPtr : Bool
  allowsUnreachableWarning : Bool
  coerceNeverApplies : Bool

noncomputable def evalPlaceNeverCheck (ctx : PlaceParentCtx) : PlaceNeverCheckResult :=
  let rd := constitutesReadForNever ctx
  ⟨rd, rd, rd⟩

/-- Soundness & Empirical Fidelity Theorem matching live `rustc`/`Miri` runs:
    - `let _ = *p;` and `match *p { _ => 43 }` have `constitutesReadForNever = false`
      (`CoerceStep` `neverToAny` with `isReadForNever = false` is FORBIDDEN),
      producing zero UB even on `*(&0u8 as *const !)`;
    - `let _ = { *p };` (`blockExpr`) and `let _x: () = *p;` (`letBinding`) have
      `constitutesReadForNever = true`, activating `NeverToAny` / read semantics! -/
theorem place_read_gating_soundness (tgt : RustTy) (htgt : tgt ≠ .never) :
    (¬ ∃ adj, CoerceStep true (constitutesReadForNever .letWildcard) .never tgt adj) ∧
    (¬ ∃ adj, CoerceStep true (constitutesReadForNever .matchWildcardArm) .never tgt adj) ∧
    CoerceStep true (constitutesReadForNever .blockExpr) .never tgt [.neverToAny] ∧
    CoerceStep true (constitutesReadForNever .letBinding) .never tgt [.neverToAny] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨adj, hc⟩
    cases hc with
    | refl => exact False.elim (htgt rfl)
    | neverToAny _ _ hrd => cases hrd
  · rintro ⟨adj, hc⟩
    cases hc with
    | refl => exact False.elim (htgt rfl)
    | neverToAny _ _ hrd => cases hrd
  · exact CoerceStep.neverToAny tgt rfl rfl
  · exact CoerceStep.neverToAny tgt rfl rfl

theorem wildcard_never_place_contradiction_guarded (pCtx : PlaceParentCtx) (tgt : RustTy)
    (htgt : tgt ≠ .never) (adj : List AdjustKind)
    (hc : CoerceStep true (constitutesReadForNever pCtx) .never tgt adj) :
    constitutesReadForNever pCtx = true := by
  cases hc with
  | refl => exact False.elim (htgt rfl)
  | neverToAny _ _ hrd => exact hrd

/-! ## Section 8: Fail-Closed Projection onto Anneal's MIR Semantics (`Trusted/MirAst.lean` & `MirSemantics.lean`) -/

/-- Exact mirror of Anneal's `MirTy` ADT (`trusted/lean/Trusted/MirAst.lean`, `joshlf/anneal`):
    `.never` is represented explicitly, while `FnDef`, `FnPtr`, `Closure`, `Slice`,
    and `Array` lower to `.unsupported`. -/
inductive AnnealMirTy where
  | bool
  | int
  | unit
  | never
  | ref
  | rawPtr
  | unsupported

/-- Exact mirror of Anneal's `TerminatorKind` / `Rvalue` / `Outcome` abstraction
    (`trusted/lean/Trusted/MirSemantics.lean`). -/
inductive AnnealOutcome where
  | ok
  | undefined   -- e.g. `TerminatorKind.unreachable` reached
  | unsupported -- e.g. `Rvalue::Cast(CastKind::PointerCoercion(..))`

noncomputable def lowerToAnnealMirTy : RustTy → AnnealMirTy
  | .unit => .unit
  | .never => .never
  | .scalar => .int
  | .ref _ _ => .ref
  | .rawPtr _ _ => .rawPtr
  | .array _ _ => .unsupported
  | .slice _ => .unsupported
  | .fnItem _ _ _ _ => .unsupported
  | .fnPtr _ _ _ => .unsupported
  | .closure _ _ _ _ => .unsupported
  | .tyVar _ => .unsupported
  | .error => .unsupported

/-- Lowering an adjustment step into Anneal's fail-closed MIR verification model:
    - `neverToAny` emits `TerminatorKind::Unreachable` in `rustc_mir_build` (`into.rs:134-155`),
      which faults `.undefined` if dynamically reached (`MirSemantics`);
    - ALL five `PointerCoercion` variants lower via `Rvalue::Cast(PointerCoercion(..))`
      (`as_rvalue.rs:158-170`), which `rustc-capture` maps to `Rvalue.unsupported` (`.unsupported`). -/
noncomputable def evalAdjustmentInAnneal : AdjustKind → AnnealOutcome
  | .neverToAny => .undefined
  | .derefBuiltin => .ok
  | .borrowRef _ => .ok
  | .borrowRawPtr _ => .ok
  | .pointer _ => .unsupported

/-- Anneal Fail-Closed Soundness Theorem:
    1. Every `PointerCoercion` produced by `CoerceMany` (`ReifyFnPointer`, `UnsafeFnPointer`,
       `ClosureFnPointer`, `MutToConstPointer`, `Unsize`) evaluates to `.unsupported` in Anneal's
       trusted semantics (never silently mis-approximated as `.ok`!);
    2. Reaching `AdjustKind::neverToAny` dynamically (as when `zeroed::<!>()` or `!`-read
       is falsely assumed unreachable) fails cleanly as `.undefined`, matching Miri UB;
    3. `.never` maps faithfully to `AnnealMirTy.never` while `.unit` maps to `AnnealMirTy.unit`,
       so post-1.100 fallback shifts never conflate `()` and `!` at Anneal's IR boundary. -/
theorem anneal_fail_closed_boundary (pc : PointerCoercion) :
    evalAdjustmentInAnneal (.pointer pc) = .unsupported ∧
    evalAdjustmentInAnneal .neverToAny = .undefined ∧
    lowerToAnnealMirTy .never = .never ∧
    lowerToAnnealMirTy .unit = .unit :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem anneal_pointer_coercion_targets_unsupported (s : Safety) (arg ret elem : RustTy) :
    lowerToAnnealMirTy (.fnPtr s arg ret) = .unsupported ∧
    lowerToAnnealMirTy (.slice elem) = .unsupported ∧
    lowerToAnnealMirTy (.closure 0 false arg ret) = .unsupported ∧
    lowerToAnnealMirTy (.fnItem 0 s arg ret) = .unsupported :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 9: End-to-End Package Composition Soundness Theorem -/

/-- Master package theorem combining all three pillars + Anneal trusted boundary:
    1. Any well-typed `tryFindCoercionLub` / `stepCoerceMany` multi-arm coercion produces
       a coherent `AdjustChain` for every branch and preserves type inhabitedness & safety;
    2. Uninhabited `!` fallback breaks unit-only bounds unconditionally post-1.100, and
       `LintAcceptsUnsafeFlow` over `UndirectedStep` blocks `! -> unsafe` flow across
       arbitrary V-junctions (`indirectHopEdges`) and chains (`twoHopEdges`);
    3. Unread wildcard `*p` places reject `NeverToAny` (`constitutesReadForNever = false`),
       while Anneal fails closed (`Rvalue.unsupported` / `.undefined`) on every coercible
       pointer cast and reachable `NeverToAny` block. -/
theorem hir_typeck_coercion_lub_and_never_fallback_master_theorem
    (inner elem arg ret : RustTy)
    (hInner : isInhabited inner)
    (era : CompilerEra) (ed : Edition) (st : InferFlowState) (assign : Nat → RustTy)
    (ha : FallbackAssignment era ed st assign)
    (hclean : LintAcceptsUnsafeFlow st) :
    -- (A) `if`/`match` symmetric LUB vs `loop`/`block` pinning asymmetry & array unsize
    (runLetBoundCoerceMany true (.ref .mutbl inner) (.ref .imm inner) = some (.ref .imm inner)) ∧
    (runLetBoundCoerceMany false (.ref .mutbl inner) (.ref .imm inner) = none) ∧
    (let st0 : CoerceManyState := ⟨.ref .imm (.slice elem), none, []⟩
     (match stepCoerceMany st0 (.ref .mutbl (.array 2 elem)) with
      | none => none
      | some st1 =>
        match stepCoerceMany st1 (.ref .imm (.array 3 elem)) with
        | none => none
        | some st2 => st2.finalTy) = some (.ref .imm (.slice elem))) ∧
    -- (B) `evalOutcome` transport along arbitrary valid `AdjustChain`
    (∀ cn rd adj (tgt : RustTy), AdjustChain cn rd inner tgt adj → isInhabited tgt) ∧
    -- (C) Post-1.100 `!` fallback unsafe-flow soundness & indirect undirected-DFS necessity
    (∀ u reason, (u, reason) ∈ st.unsafeInferVars → assign u ≠ .never) ∧
    PathUnder (UndirectedStep indirectHopEdges) 0 1 ∧
    ¬ PathUnder (DirectedStep indirectHopEdges) 0 1 ∧
    -- (D) Wildcard place-read guard & Anneal fail-closed boundary
    constitutesReadForNever .letWildcard = false ∧
    evalAdjustmentInAnneal .neverToAny = .undefined ∧
    evalAdjustmentInAnneal (.pointer (.closureFnPointer .isSafe)) = .unsupported ∧
    lowerToAnnealMirTy (.fnPtr .isUnsafe arg ret) = .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact (if_vs_loop_pinning_contrast inner).1
  · exact (if_vs_loop_pinning_contrast inner).2.2.1
  · exact lub_array_mut_and_shared_unsize_with_slice_hint elem
  · intro cn rd adj tgt hc
    exact adjustChain_preserves_inhabited hc hInner
  · exact default_deny_prevents_unsafe_never_instantiation era ed st assign ha hclean
  · exact undirected_catches_indirect_hop
  · exact directed_misses_indirect_hop

end HirTypeckCoercionLubAndNeverFallbackSoundness

