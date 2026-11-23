/-
  HirMethodResolutionAutoderefSoundness.lean

  Kernel-checked Lean v4.34.1 mechanization of `rustc_hir_typeck` method
  resolution, autoderef-step-first precedence, `E0034` ambiguity vs. cross-step
  shadowing, `#![feature(arbitrary_self_types)]` (`Receiver` vs. `Deref` and
  asymmetric anti-shadowing), `zerocopy` (`Ptr` / `Unalign` / `ReadOnly`)
  receiver dispatch, and Anneal's fail-closed MIR semantics boundary.

  Pure Constructive Lean 4 Discipline:
    - Zero `import` outside Lean 4 core prelude (`Init`).
    - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
      zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
    - Every value-level definition is explicitly marked `noncomputable def`
      using purely structural recursion; zero `deriving` clauses appear.
-/

namespace HirMethodResolutionAutoderefSoundness

/-! ## Section 1: Core Syntax, Structural Equality, and Lexicographic Order -/

/-- Reference / raw-pointer mutability (`rustc_ast::Mutability`). -/
inductive Mutability where
  | imm
  | mutbl

/-- Model of Rust receiver / pointee types in method resolution. -/
inductive Ty where
  | unit
  | scalar
  | array (len : Nat) (elem : Ty)
  | slice (elem : Ty)
  | ref (m : Mutability) (inner : Ty)
  | rawPtr (m : Mutability) (inner : Ty)
  | adt (id : Nat)
  | smartReceiver (id : Nat) (target : Ty)
  | smartDeref (id : Nat) (target : Ty)
  | pin (inner : Ty)
  | param (id : Nat)
  | dynObj (traitId : Nat)
  | inferVar (vid : Nat)
  | err

/-- How a single autoderef hop was obtained (`rustc_hir_analysis::autoderef`). -/
inductive AutoderefKind where
  | builtin
  | overloadedDeref
  | overloadedReceiver

/-- Candidate bucket inside `ProbeContext`:
    `inherent` covers `InherentImplCandidate`, `ObjectCandidate`, and `WhereClauseCandidate`;
    `extension` covers `TraitCandidate` (`probe.rs:118-123, 888-892, 1750-1764`). -/
inductive CandidateBucket where
  | inherent
  | extension

/-- Exact pick origin (`rustc_hir_typeck::method::probe::PickKind`). -/
inductive PickKind where
  | inherentImplPick
  | objectPick
  | traitPick (isAmbiguouslyImported : Bool)
  | whereClausePick (traitId : Nat)

/-- Per-step receiver adjustment stages (`probe.rs:1375-1478`), in exact search order. -/
inductive AdjustmentStage where
  | byValue
  | autorefImm
  | autorefMut
  | constPtr
  | reborrowPin

/-- Concrete receiver adjustment recorded on a winning `Pick` (`probe.rs:145-160`). -/
inductive AutorefOrPtrAdjustment where
  | autoref (m : Mutability) (unsize : Bool)
  | toConstPtr
  | reborrowPin (m : Mutability)

/-- Pure constructive Boolean equality on `Nat`. -/
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
      have heq := ih h
      subst heq
      rfl

theorem eqNat_iff (a b : Nat) : eqNat a b = true ↔ a = b :=
  ⟨eqNat_sound, fun h => h ▸ eqNat_refl a⟩

/-- Pure constructive Boolean `≤` on `Nat`. -/
noncomputable def leNat : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ a, Nat.succ b => leNat a b

/-- Pure constructive Boolean `<` on `Nat`. -/
noncomputable def ltNat (a b : Nat) : Bool :=
  leNat (Nat.succ a) b

theorem leNat_sound {a b : Nat} (h : leNat a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le b
  | succ ak ih =>
    cases b with
    | zero => simp [leNat] at h
    | succ bk => exact Nat.succ_le_succ (ih h)

theorem leNat_complete {a b : Nat} (h : a ≤ b) : leNat a b = true := by
  induction a generalizing b with
  | zero => rfl
  | succ ak ih =>
    cases b with
    | zero => cases h
    | succ bk => exact ih (Nat.le_of_succ_le_succ h)

theorem ltNat_sound {a b : Nat} (h : ltNat a b = true) : a < b :=
  leNat_sound h

theorem ltNat_complete {a b : Nat} (h : a < b) : ltNat a b = true :=
  leNat_complete h

noncomputable def eqBool : Bool → Bool → Bool
  | false, false => true
  | true, true => true
  | _, _ => false

theorem eqBool_refl (b : Bool) : eqBool b b = true := by
  cases b <;> rfl

theorem eqBool_sound {a b : Bool} (h : eqBool a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [eqBool] at h

theorem eqBool_iff (a b : Bool) : eqBool a b = true ↔ a = b :=
  ⟨eqBool_sound, fun h => h ▸ eqBool_refl a⟩

noncomputable def eqMut : Mutability → Mutability → Bool
  | .imm, .imm => true
  | .mutbl, .mutbl => true
  | _, _ => false

theorem eqMut_refl (m : Mutability) : eqMut m m = true := by
  cases m <;> rfl

theorem eqMut_sound {a b : Mutability} (h : eqMut a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [eqMut] at h

theorem eqMut_iff (a b : Mutability) : eqMut a b = true ↔ a = b :=
  ⟨eqMut_sound, fun h => h ▸ eqMut_refl a⟩

noncomputable def eqTy : Ty → Ty → Bool
  | .unit, .unit => true
  | .scalar, .scalar => true
  | .array n1 e1, .array n2 e2 => eqNat n1 n2 && eqTy e1 e2
  | .slice e1, .slice e2 => eqTy e1 e2
  | .ref m1 i1, .ref m2 i2 => eqMut m1 m2 && eqTy i1 i2
  | .rawPtr m1 i1, .rawPtr m2 i2 => eqMut m1 m2 && eqTy i1 i2
  | .adt id1, .adt id2 => eqNat id1 id2
  | .smartReceiver id1 t1, .smartReceiver id2 t2 => eqNat id1 id2 && eqTy t1 t2
  | .smartDeref id1 t1, .smartDeref id2 t2 => eqNat id1 id2 && eqTy t1 t2
  | .pin i1, .pin i2 => eqTy i1 i2
  | .param id1, .param id2 => eqNat id1 id2
  | .dynObj id1, .dynObj id2 => eqNat id1 id2
  | .inferVar id1, .inferVar id2 => eqNat id1 id2
  | .err, .err => true
  | _, _ => false

theorem eqTy_refl (t : Ty) : eqTy t t = true := by
  induction t with
  | unit => rfl
  | scalar => rfl
  | array n e ih => simp [eqTy, eqNat_refl, ih]
  | slice e ih => simp [eqTy, ih]
  | ref m i ih => simp [eqTy, eqMut_refl, ih]
  | rawPtr m i ih => simp [eqTy, eqMut_refl, ih]
  | adt id => simp [eqTy, eqNat_refl]
  | smartReceiver id t ih => simp [eqTy, eqNat_refl, ih]
  | smartDeref id t ih => simp [eqTy, eqNat_refl, ih]
  | pin i ih => simp [eqTy, ih]
  | param id => simp [eqTy, eqNat_refl]
  | dynObj id => simp [eqTy, eqNat_refl]
  | inferVar id => simp [eqTy, eqNat_refl]
  | err => rfl

theorem eqTy_sound {a b : Ty} (h : eqTy a b = true) : a = b := by
  induction a generalizing b with
  | unit => cases b <;> first | rfl | simp [eqTy] at h
  | scalar => cases b <;> first | rfl | simp [eqTy] at h
  | array n1 e1 ih =>
    cases b with
    | array n2 e2 =>
      simp only [eqTy, Bool.and_eq_true] at h
      have hn := eqNat_sound h.1
      have he := ih h.2
      subst hn; subst he; rfl
    | _ => simp [eqTy] at h
  | slice e1 ih =>
    cases b with
    | slice e2 => have he := ih h; subst he; rfl
    | _ => simp [eqTy] at h
  | ref m1 i1 ih =>
    cases b with
    | ref m2 i2 =>
      simp only [eqTy, Bool.and_eq_true] at h
      have hm := eqMut_sound h.1
      have hi := ih h.2
      subst hm; subst hi; rfl
    | _ => simp [eqTy] at h
  | rawPtr m1 i1 ih =>
    cases b with
    | rawPtr m2 i2 =>
      simp only [eqTy, Bool.and_eq_true] at h
      have hm := eqMut_sound h.1
      have hi := ih h.2
      subst hm; subst hi; rfl
    | _ => simp [eqTy] at h
  | adt id1 =>
    cases b with
    | adt id2 => have hid := eqNat_sound h; subst hid; rfl
    | _ => simp [eqTy] at h
  | smartReceiver id1 t1 ih =>
    cases b with
    | smartReceiver id2 t2 =>
      simp only [eqTy, Bool.and_eq_true] at h
      have hid := eqNat_sound h.1
      have ht := ih h.2
      subst hid; subst ht; rfl
    | _ => simp [eqTy] at h
  | smartDeref id1 t1 ih =>
    cases b with
    | smartDeref id2 t2 =>
      simp only [eqTy, Bool.and_eq_true] at h
      have hid := eqNat_sound h.1
      have ht := ih h.2
      subst hid; subst ht; rfl
    | _ => simp [eqTy] at h
  | pin i1 ih =>
    cases b with
    | pin i2 => have hi := ih h; subst hi; rfl
    | _ => simp [eqTy] at h
  | param id1 =>
    cases b with
    | param id2 => have hid := eqNat_sound h; subst hid; rfl
    | _ => simp [eqTy] at h
  | dynObj id1 =>
    cases b with
    | dynObj id2 => have hid := eqNat_sound h; subst hid; rfl
    | _ => simp [eqTy] at h
  | inferVar id1 =>
    cases b with
    | inferVar id2 => have hid := eqNat_sound h; subst hid; rfl
    | _ => simp [eqTy] at h
  | err => cases b <;> first | rfl | simp [eqTy] at h

theorem eqTy_iff (a b : Ty) : eqTy a b = true ↔ a = b :=
  ⟨eqTy_sound, fun h => h ▸ eqTy_refl a⟩

noncomputable def eqBucket : CandidateBucket → CandidateBucket → Bool
  | .inherent, .inherent => true
  | .extension, .extension => true
  | _, _ => false

theorem eqBucket_refl (b : CandidateBucket) : eqBucket b b = true := by
  cases b <;> rfl

theorem eqBucket_sound {a b : CandidateBucket} (h : eqBucket a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [eqBucket] at h

noncomputable def eqStage : AdjustmentStage → AdjustmentStage → Bool
  | .byValue, .byValue => true
  | .autorefImm, .autorefImm => true
  | .autorefMut, .autorefMut => true
  | .constPtr, .constPtr => true
  | .reborrowPin, .reborrowPin => true
  | _, _ => false

theorem eqStage_refl (s : AdjustmentStage) : eqStage s s = true := by
  cases s <;> rfl

theorem eqStage_sound {a b : AdjustmentStage} (h : eqStage a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [eqStage] at h

noncomputable def stageRank : AdjustmentStage → Nat
  | .byValue => 0
  | .autorefImm => 1
  | .autorefMut => 2
  | .constPtr => 3
  | .reborrowPin => 4

noncomputable def bucketRank : CandidateBucket → Nat
  | .inherent => 0
  | .extension => 1

theorem stageRank_inj {s₁ s₂ : AdjustmentStage} (h : stageRank s₁ = stageRank s₂) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | rfl | cases h

theorem bucketRank_inj {b₁ b₂ : CandidateBucket} (h : bucketRank b₁ = bucketRank b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> first | rfl | cases h

/-- Strict lexicographic ordering `(stepIdx, stageRank, bucketRank)` matching
    `probe.rs` `pick_all_method` (`1351-1478`) and `pick_method` (`1750-1764`). -/
noncomputable def ProbeKeyLt (i₁ : Nat) (s₁ : AdjustmentStage) (b₁ : CandidateBucket)
    (i₂ : Nat) (s₂ : AdjustmentStage) (b₂ : CandidateBucket) : Prop :=
  i₁ < i₂ ∨
  (i₁ = i₂ ∧ (stageRank s₁ < stageRank s₂ ∨
              (stageRank s₁ = stageRank s₂ ∧ bucketRank b₁ < bucketRank b₂)))

/-- Weak lexicographic ordering `(stepIdx, stageRank, bucketRank)`. -/
noncomputable def ProbeKeyLe (i₁ : Nat) (s₁ : AdjustmentStage) (b₁ : CandidateBucket)
    (i₂ : Nat) (s₂ : AdjustmentStage) (b₂ : CandidateBucket) : Prop :=
  i₁ < i₂ ∨
  (i₁ = i₂ ∧ (stageRank s₁ < stageRank s₂ ∨
              (stageRank s₁ = stageRank s₂ ∧ bucketRank b₁ ≤ bucketRank b₂)))

theorem probeKeyLt_implies_le {i₁ i₂ : Nat} {s₁ s₂ : AdjustmentStage} {b₁ b₂ : CandidateBucket}
    (h : ProbeKeyLt i₁ s₁ b₁ i₂ s₂ b₂) : ProbeKeyLe i₁ s₁ b₁ i₂ s₂ b₂ := by
  rcases h with hLt | ⟨hEqI, hStage | ⟨hEqS, hB⟩⟩
  · exact Or.inl hLt
  · exact Or.inr ⟨hEqI, Or.inl hStage⟩
  · exact Or.inr ⟨hEqI, Or.inr ⟨hEqS, Nat.le_of_lt hB⟩⟩

theorem probeKeyLe_refl (i : Nat) (s : AdjustmentStage) (b : CandidateBucket) :
    ProbeKeyLe i s b i s b :=
  Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.le_refl _⟩⟩

theorem probeKeyLe_trans {i₁ i₂ i₃ : Nat} {s₁ s₂ s₃ : AdjustmentStage}
    {b₁ b₂ b₃ : CandidateBucket}
    (h₁₂ : ProbeKeyLe i₁ s₁ b₁ i₂ s₂ b₂)
    (h₂₃ : ProbeKeyLe i₂ s₂ b₂ i₃ s₃ b₃) :
    ProbeKeyLe i₁ s₁ b₁ i₃ s₃ b₃ := by
  rcases h₁₂ with hI12 | ⟨hEqI12, hS12 | ⟨hEqS12, hB12⟩⟩
  · rcases h₂₃ with hI23 | ⟨hEqI23, _⟩
    · exact Or.inl (Nat.lt_trans hI12 hI23)
    · subst hEqI23; exact Or.inl hI12
  · rcases h₂₃ with hI23 | ⟨hEqI23, hS23 | ⟨hEqS23, _⟩⟩
    · subst hEqI12; exact Or.inl hI23
    · subst hEqI12; subst hEqI23; exact Or.inr ⟨rfl, Or.inl (Nat.lt_trans hS12 hS23)⟩
    · subst hEqI12; subst hEqI23; exact Or.inr ⟨rfl, Or.inl (hEqS23 ▸ hS12)⟩
  · rcases h₂₃ with hI23 | ⟨hEqI23, hS23 | ⟨hEqS23, hB23⟩⟩
    · subst hEqI12; exact Or.inl hI23
    · subst hEqI12; subst hEqI23; exact Or.inr ⟨rfl, Or.inl (hEqS12 ▸ hS23)⟩
    · subst hEqI12; subst hEqI23
      exact Or.inr ⟨rfl, Or.inr ⟨Eq.trans hEqS12 hEqS23, Nat.le_trans hB12 hB23⟩⟩

theorem probeKeyLt_irrefl (i : Nat) (s : AdjustmentStage) (b : CandidateBucket) :
    ¬ ProbeKeyLt i s b i s b := by
  intro h
  rcases h with hI | ⟨_, hS | ⟨_, hB⟩⟩
  · exact Nat.lt_irrefl i hI
  · exact Nat.lt_irrefl _ hS
  · exact Nat.lt_irrefl _ hB

theorem probeKeyLe_antisymm {i₁ i₂ : Nat} {s₁ s₂ : AdjustmentStage} {b₁ b₂ : CandidateBucket}
    (h₁₂ : ProbeKeyLe i₁ s₁ b₁ i₂ s₂ b₂)
    (h₂₁ : ProbeKeyLe i₂ s₂ b₂ i₁ s₁ b₁) :
    i₁ = i₂ ∧ s₁ = s₂ ∧ b₁ = b₂ := by
  have hI : i₁ = i₂ := by
    rcases h₁₂ with hLt12 | ⟨hEqI12, _⟩
    · rcases h₂₁ with hLt21 | ⟨hEqI21, _⟩
      · exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hLt12 hLt21))
      · rw [hEqI21] at hLt12
        exact False.elim (Nat.lt_irrefl _ hLt12)
    · exact hEqI12
  subst hI
  have hSR : stageRank s₁ = stageRank s₂ := by
    rcases h₁₂ with hLt | ⟨_, hS12 | ⟨hEqS12, _⟩⟩
    · exact False.elim (Nat.lt_irrefl _ hLt)
    · rcases h₂₁ with hLt | ⟨_, hS21 | ⟨hEqS21, _⟩⟩
      · exact False.elim (Nat.lt_irrefl _ hLt)
      · exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hS12 hS21))
      · rw [hEqS21] at hS12
        exact False.elim (Nat.lt_irrefl _ hS12)
    · exact hEqS12
  have hS : s₁ = s₂ := stageRank_inj hSR
  subst hS
  have hBR : bucketRank b₁ = bucketRank b₂ := by
    rcases h₁₂ with hLt | ⟨_, hSLt | ⟨_, hB12⟩⟩
    · exact False.elim (Nat.lt_irrefl _ hLt)
    · exact False.elim (Nat.lt_irrefl _ hSLt)
    · rcases h₂₁ with hLt | ⟨_, hSLt2 | ⟨_, hB21⟩⟩
      · exact False.elim (Nat.lt_irrefl _ hLt)
      · exact False.elim (Nat.lt_irrefl _ hSLt2)
      · exact Nat.le_antisymm hB12 hB21
  exact ⟨rfl, rfl, bucketRank_inj hBR⟩

/-! ## Section 2: `Autoderef` Chains, `method_autoderef_steps`, and Termination -/

/-- One step emitted by `rustc_hir_typeck::method::probe::method_autoderef_steps`
    (`rustc_middle::traits::query::CandidateStep`, `query.rs:144-169`). -/
structure CandidateStep where
  selfTy : Ty
  autoderefs : Nat
  fromUnsafeDeref : Bool
  unsize : Bool
  reachableViaDeref : Bool

/-- Environment capturing overloaded `Deref` and `Receiver` implementations for ADTs
    and smart-pointer constructors. -/
structure DerefEnv where
  derefTarget : Nat → Option Ty
  receiverTarget : Nat → Option Ty

/-- Mode of `Autoderef` traversal (`use_receiver_trait = false` vs `true` in `autoderef.rs:241`). -/
inductive ChainMode where
  | viaDeref
  | viaReceiver

/-- Single-step builtin or overloaded deref (`autoderef.rs:88-96, 137-175`).
    Built-in derefs apply uniformly to `&T`, `&mut T`, `*const T`, `*mut T`
    (since `include_raw_pointers()` is always enabled in `method_autoderef_steps`),
    and `smartDeref` / `smartReceiver` follow `Deref` vs. `Receiver` chains. -/
noncomputable def stepAutoderef (env : DerefEnv) (mode : ChainMode) (ty : Ty) :
    Option (Ty × AutoderefKind) :=
  match ty with
  | .ref _ inner => some (inner, .builtin)
  | .rawPtr _ inner => some (inner, .builtin)
  | .smartDeref _ inner => some (inner, .overloadedDeref)
  | .smartReceiver id inner =>
    match mode with
    | .viaDeref =>
      match env.derefTarget id with
      | some tgt => some (tgt, .overloadedDeref)
      | none => none
    | .viaReceiver =>
      match env.receiverTarget id with
      | some tgt => some (tgt, .overloadedReceiver)
      | none =>
        -- Blanket `impl<P: Deref> Receiver for P` (`core/src/ops/deref.rs:380-385`)
        match env.derefTarget id with
        | some tgt => some (tgt, .overloadedDeref)
        | none => some (inner, .overloadedReceiver)
  | .adt id =>
    match mode with
    | .viaDeref =>
      match env.derefTarget id with
      | some tgt => some (tgt, .overloadedDeref)
      | none => none
    | .viaReceiver =>
      match env.receiverTarget id with
      | some tgt => some (tgt, .overloadedReceiver)
      | none =>
        match env.derefTarget id with
        | some tgt => some (tgt, .overloadedDeref)
        | none => none
  | _ => none

noncomputable def isRawPtrTy : Ty → Bool
  | .rawPtr _ _ => true
  | _ => false

noncomputable def isTyErrOrInfer : Ty → Bool
  | .err => true
  | .inferVar _ => true
  | _ => false

/-- Raw entry produced by the `Autoderef` iterator: `(ty, depth, fromUnsafeDeref)`. -/
structure RawDerefEntry where
  ty : Ty
  depth : Nat
  fromUnsafeDeref : Bool

/-- Structurally recursive bounded `Autoderef` iterator (`autoderef.rs:49-108`)
    governed by `tcx.recursion_limit()` (`fuel : Nat`).
    Returns `(entries, finalTy, reachedRawPtrAtEnd, reachedLimit)`. -/
noncomputable def runAutoderefAux (env : DerefEnv) (mode : ChainMode) :
    Nat → Ty → Nat → Bool → List RawDerefEntry × Ty × Bool × Bool
  | 0, curTy, depth, rawFlag =>
    let rawNext := rawFlag || isRawPtrTy curTy
    if eqNat depth 0 then
      ([{ ty := curTy, depth := 0, fromUnsafeDeref := false }], curTy, rawNext, true)
    else
      ([], curTy, rawFlag, true)
  | Nat.succ fuel, curTy, depth, rawFlag =>
    let entry : RawDerefEntry := { ty := curTy, depth := depth, fromUnsafeDeref := rawFlag }
    let nextRawFlag := rawFlag || isRawPtrTy curTy
    if isTyErrOrInfer curTy then
      ([entry], curTy, nextRawFlag, false)
    else
      match stepAutoderef env mode curTy with
      | none => ([entry], curTy, nextRawFlag, false)
      | some (nextTy, _) =>
        let (rest, finalTy, endRaw, lim) :=
          runAutoderefAux env mode fuel nextTy (Nat.succ depth) nextRawFlag
        (entry :: rest, finalTy, endRaw, lim)

theorem runAutoderefAux_succ (env : DerefEnv) (mode : ChainMode)
    (fuel : Nat) (curTy : Ty) (depth : Nat) (rawFlag : Bool) :
    runAutoderefAux env mode (Nat.succ fuel) curTy depth rawFlag =
      let entry : RawDerefEntry := { ty := curTy, depth := depth, fromUnsafeDeref := rawFlag }
      let nextRawFlag := rawFlag || isRawPtrTy curTy
      if isTyErrOrInfer curTy then
        ([entry], curTy, nextRawFlag, false)
      else
        match stepAutoderef env mode curTy with
        | none => ([entry], curTy, nextRawFlag, false)
        | some (nextTy, _) =>
          let (rest, finalTy, endRaw, lim) :=
            runAutoderefAux env mode fuel nextTy (Nat.succ depth) nextRawFlag
          (entry :: rest, finalTy, endRaw, lim) := rfl

/-- Zip the `Receiver` chain with the `Deref` reachability boolean stream
    (`probe.rs:715-746`). Every prefix item present in `derefEntries` has
    `reachableViaDeref = true`, and strictly deeper `Receiver`-only entries
    have `reachableViaDeref = false`. -/
noncomputable def zipReceiverAndDeref :
    List RawDerefEntry → List RawDerefEntry → List CandidateStep
  | [], _ => []
  | r :: rs, [] =>
    { selfTy := r.ty
      autoderefs := r.depth
      fromUnsafeDeref := r.fromUnsafeDeref
      unsize := false
      reachableViaDeref := false } :: zipReceiverAndDeref rs []
  | r :: rs, _ :: ds =>
    { selfTy := r.ty
      autoderefs := r.depth
      fromUnsafeDeref := r.fromUnsafeDeref
      unsize := false
      reachableViaDeref := true } :: zipReceiverAndDeref rs ds

noncomputable def countReachableDeref : List CandidateStep → Nat
  | [] => 0
  | s :: ss =>
    if s.reachableViaDeref then Nat.succ (countReachableDeref ss)
    else countReachableDeref ss

/-- Exact model of `method_autoderef_steps` (`probe.rs:655-820`), appending at most one
    trailing `unsize: true` step (`[T; N] -> [T]`) when `autoderef_via_deref.final_ty()`
    is `Ty.array elem _` (`probe.rs:790-809`). -/
noncomputable def buildMethodAutoderefSteps (env : DerefEnv) (limit : Nat)
    (arbitrarySelfTypes : Bool) (startTy : Ty) :
    List CandidateStep × Bool :=
  let derefRes := runAutoderefAux env .viaDeref limit startTy 0 false
  let derefEntries := derefRes.1
  let finalDerefTy := derefRes.2.1
  let rawAtEnd := derefRes.2.2.1
  let limDeref := derefRes.2.2.2
  let baseSteps : List CandidateStep :=
    if arbitrarySelfTypes then
      zipReceiverAndDeref
        (runAutoderefAux env .viaReceiver limit startTy 0 false).1
        derefEntries
    else
      zipReceiverAndDeref derefEntries derefEntries
  let limTotal : Bool :=
    if arbitrarySelfTypes then
      (runAutoderefAux env .viaReceiver limit startTy 0 false).2.2.2
    else
      limDeref
  match finalDerefTy with
  | .array _ elem =>
    let derefCount := countReachableDeref baseSteps
    let unsizeAutoderefs := match derefCount with | 0 => 0 | Nat.succ k => k
    let unsizeStep : CandidateStep :=
      { selfTy := .slice elem
        autoderefs := unsizeAutoderefs
        fromUnsafeDeref := rawAtEnd
        unsize := true
        reachableViaDeref := true }
    (baseSteps ++ [unsizeStep], limTotal)
  | _ => (baseSteps, limTotal)

/-- Count how many steps in a list carry `unsize = true`. -/
noncomputable def countUnsizeSteps : List CandidateStep → Nat
  | [] => 0
  | s :: ss => if s.unsize then Nat.succ (countUnsizeSteps ss) else countUnsizeSteps ss

theorem runAutoderefAux_len_le (env : DerefEnv) (mode : ChainMode) :
    ∀ (fuel : Nat) (curTy : Ty) (depth : Nat) (rawFlag : Bool),
      (runAutoderefAux env mode fuel curTy depth rawFlag).1.length ≤ Nat.succ fuel
  | 0, curTy, depth, rawFlag => by
    unfold runAutoderefAux
    cases eqNat depth 0 <;> simp
  | Nat.succ fuel, curTy, depth, rawFlag => by
    unfold runAutoderefAux
    cases isTyErrOrInfer curTy with
    | true => simp
    | false =>
      cases stepAutoderef env mode curTy with
      | none => simp
      | some p =>
        have ih := runAutoderefAux_len_le env mode fuel p.1 (Nat.succ depth) (rawFlag || isRawPtrTy curTy)
        dsimp only
        exact Nat.succ_le_succ ih

theorem zipReceiverAndDeref_len_le :
    ∀ (rs ds : List RawDerefEntry), (zipReceiverAndDeref rs ds).length = rs.length
  | [], _ => rfl
  | _ :: rs, [] => by simp [zipReceiverAndDeref, zipReceiverAndDeref_len_le rs []]
  | _ :: rs, _ :: ds => by simp [zipReceiverAndDeref, zipReceiverAndDeref_len_le rs ds]

theorem zipReceiverAndDeref_no_unsize :
    ∀ (rs ds : List RawDerefEntry), countUnsizeSteps (zipReceiverAndDeref rs ds) = 0
  | [], _ => rfl
  | _ :: rs, [] => by
    simp [zipReceiverAndDeref, countUnsizeSteps, zipReceiverAndDeref_no_unsize rs []]
  | _ :: rs, _ :: ds => by
    simp [zipReceiverAndDeref, countUnsizeSteps, zipReceiverAndDeref_no_unsize rs ds]

theorem countUnsizeSteps_append (xs ys : List CandidateStep) :
    countUnsizeSteps (xs ++ ys) = countUnsizeSteps xs + countUnsizeSteps ys := by
  induction xs with
  | nil => simp [countUnsizeSteps]
  | cons x xs ih =>
    cases hU : x.unsize with
    | true => simp [countUnsizeSteps, hU, ih, Nat.succ_add]
    | false => simp [countUnsizeSteps, hU, ih]

/-- **Unsize-Step Termination & At-Most-Once Theorem (`probe.rs:790-809`):**
    For any `DerefEnv`, any recursion limit `limit`, any `arbitrarySelfTypes` flag,
    and any receiver type `startTy`:
    1. `buildMethodAutoderefSteps` always terminates with total step count `≤ limit + 2`;
    2. It emits at most ONE `unsize = true` step (`countUnsizeSteps ≤ 1`), occurring
       exclusively at the tail when `finalDerefTy` is an array `[T; N]`, and never
       iterating unsizing recursively;
    3. Every emitted `unsize = true` step has `reachableViaDeref = true` and a slice type. -/
theorem unsize_step_termination_and_uniqueness (env : DerefEnv) (limit : Nat)
    (arbitrarySelfTypes : Bool) (startTy : Ty) :
    let (steps, _) := buildMethodAutoderefSteps env limit arbitrarySelfTypes startTy
    steps.length ≤ Nat.succ (Nat.succ limit) ∧
    countUnsizeSteps steps ≤ 1 ∧
    (∀ s ∈ steps, s.unsize = true → s.reachableViaDeref = true ∧ ∃ e, s.selfTy = .slice e) := by
  unfold buildMethodAutoderefSteps
  dsimp only
  have hLenRecv :
      (runAutoderefAux env .viaReceiver limit startTy 0 false).1.length ≤ Nat.succ limit :=
    runAutoderefAux_len_le env .viaReceiver limit startTy 0 false
  have hLenDeref :
      (runAutoderefAux env .viaDeref limit startTy 0 false).1.length ≤ Nat.succ limit :=
    runAutoderefAux_len_le env .viaDeref limit startTy 0 false
  have hBaseLen :
      (if arbitrarySelfTypes then
        zipReceiverAndDeref
          (runAutoderefAux env .viaReceiver limit startTy 0 false).1
          (runAutoderefAux env .viaDeref limit startTy 0 false).1
       else
        zipReceiverAndDeref
          (runAutoderefAux env .viaDeref limit startTy 0 false).1
          (runAutoderefAux env .viaDeref limit startTy 0 false).1).length ≤ Nat.succ limit := by
    cases arbitrarySelfTypes with
    | true =>
      simp only [↓reduceIte, zipReceiverAndDeref_len_le]
      exact hLenRecv
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, zipReceiverAndDeref_len_le]
      exact hLenDeref
  have hBaseNoUnsize :
      countUnsizeSteps
        (if arbitrarySelfTypes then
          zipReceiverAndDeref
            (runAutoderefAux env .viaReceiver limit startTy 0 false).1
            (runAutoderefAux env .viaDeref limit startTy 0 false).1
         else
          zipReceiverAndDeref
            (runAutoderefAux env .viaDeref limit startTy 0 false).1
            (runAutoderefAux env .viaDeref limit startTy 0 false).1) = 0 := by
    cases arbitrarySelfTypes <;> simp [zipReceiverAndDeref_no_unsize]
  have hBaseMemNoUnsize :
      ∀ s, s ∈ (if arbitrarySelfTypes then
          zipReceiverAndDeref
            (runAutoderefAux env .viaReceiver limit startTy 0 false).1
            (runAutoderefAux env .viaDeref limit startTy 0 false).1
         else
          zipReceiverAndDeref
            (runAutoderefAux env .viaDeref limit startTy 0 false).1
            (runAutoderefAux env .viaDeref limit startTy 0 false).1) →
        s.unsize = false := by
    intro s hMem
    have hZero :
        ∀ (rs ds : List RawDerefEntry), ∀ x ∈ zipReceiverAndDeref rs ds, x.unsize = false := by
      intro rs ds x hx
      induction rs generalizing ds with
      | nil => cases hx
      | cons r rs ih =>
        cases ds with
        | nil =>
          simp only [zipReceiverAndDeref, List.mem_cons] at hx
          rcases hx with rfl | htl
          · rfl
          · exact ih [] htl
        | cons d ds =>
          simp only [zipReceiverAndDeref, List.mem_cons] at hx
          rcases hx with rfl | htl
          · rfl
          · exact ih ds htl
    cases arbitrarySelfTypes with
    | true =>
      simp only [↓reduceIte] at hMem
      exact hZero _ _ s hMem
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hMem
      exact hZero _ _ s hMem
  cases hFinal : (runAutoderefAux env .viaDeref limit startTy 0 false).2.1 with
  | array n elem =>
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      exact Nat.succ_le_succ hBaseLen
    · rw [countUnsizeSteps_append, hBaseNoUnsize]
      simp [countUnsizeSteps]
    · intro s hMem hU
      simp only [List.mem_append, List.mem_singleton] at hMem
      rcases hMem with hInBase | rfl
      · have hF := hBaseMemNoUnsize s hInBase
        rw [hF] at hU; cases hU
      · exact ⟨rfl, elem, rfl⟩
  | unit | scalar | slice _ | ref _ _ | rawPtr _ _ | adt _ | smartReceiver _ _
  | smartDeref _ _ | pin _ | param _ | dynObj _ | inferVar _ | err =>
    all_goals
      refine ⟨Nat.le_trans hBaseLen (Nat.le_succ _), ?_, ?_⟩
      · rw [hBaseNoUnsize]; exact Nat.zero_le 1
      · intro s hMem hU
        have hF := hBaseMemNoUnsize s hMem
        rw [hF] at hU; cases hU

/-! ## Section 3: Exact 2-Level Method Probe State Machine (`probe.rs`) -/

/-- A method candidate collected by `assemble_inherent_candidates` /
    `assemble_extension_candidates_for_traits_in_scope`. -/
structure MethodCandidate where
  id : Nat
  bucket : CandidateBucket
  pickKind : PickKind
  traitId : Nat
  supertraits : List Nat
  expectedTy : Ty
  expectedStage : AdjustmentStage
  receiverSteps : Nat
  isUnstable : Bool
  hasBadReturnType : Bool

/-- Configuration flags matching `rustc` nightly / feature gates. -/
structure ProbeConfig where
  arbitrarySelfTypes : Bool
  supertraitItemShadowing : Bool
  pinErgonomics : Bool

/-- Whether a `CandidateStep` admits a given `AdjustmentStage`
    (`probe.rs:1596, 1679, 1721-1725`). -/
noncomputable def stepAllowsStage (cfg : ProbeConfig) (step : CandidateStep) :
    AdjustmentStage → Bool
  | .byValue => !step.unsize
  | .autorefImm => true
  | .autorefMut => true
  | .constPtr =>
    if step.unsize then false
    else match step.selfTy with
      | .rawPtr .mutbl _ => true
      | _ => false
  | .reborrowPin =>
    if !cfg.pinErgonomics then false
    else match step.selfTy with
      | .pin (.ref .mutbl _) => true
      | _ => false

/-- Type after applying `stage` to `step.selfTy` (`probe.rs:1589-1739`),
    used to match `candidate.expectedTy`. -/
noncomputable def stageSelfTy (step : CandidateStep) : AdjustmentStage → Option Ty
  | .byValue =>
    if step.unsize then none else some step.selfTy
  | .autorefImm => some (.ref .imm step.selfTy)
  | .autorefMut => some (.ref .mutbl step.selfTy)
  | .constPtr =>
    if step.unsize then none
    else match step.selfTy with
      | .rawPtr .mutbl inner => some (.rawPtr .imm inner)
      | _ => none
  | .reborrowPin =>
    match step.selfTy with
    | .pin (.ref .mutbl inner) => some (.pin (.ref .imm inner))
    | _ => none

/-- Exact `candidateMatches` predicate (`consider_probe`, `probe.rs:2020-2298`). -/
noncomputable def candidateMatches (cfg : ProbeConfig) (step : CandidateStep)
    (stage : AdjustmentStage) (bucket : CandidateBucket)
    (c : MethodCandidate) : Bool :=
  if stepAllowsStage cfg step stage then
    if eqBucket c.bucket bucket && eqStage c.expectedStage stage then
      match stageSelfTy step stage with
      | some ty => eqTy c.expectedTy ty
      | none => false
    else false
  else false

/-- `PickConstraintsForShadowed::candidate_may_shadow` (`probe.rs:190-215`):
    matches inherent candidates with distinct `id` and strictly larger `receiver_steps`. -/
noncomputable def candidateMayShadow (shadower : MethodCandidate) (c : MethodCandidate) : Bool :=
  !(eqNat c.id shadower.id) &&
  eqBucket c.bucket .inherent &&
  ltNat shadower.receiverSteps c.receiverSteps

/-- Selected pick carrying its exact probe coordinates and synthesized adjustment. -/
structure MethodPick where
  stepIdx : Nat
  step : CandidateStep
  stage : AdjustmentStage
  autoderefs : Nat
  adjustment : Option AutorefOrPtrAdjustment
  cand : MethodCandidate

/-- Outcome of probing (`PickResult` in `probe.rs:259` and `MethodError`). -/
inductive ProbeOutcome where
  | picked (pick : MethodPick)
  | ambiguity (candIds : List Nat)
  | badReturnType
  | noMatch

noncomputable def filterList {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterList p xs else filterList p xs

theorem mem_filterList {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ filterList p xs ↔ x ∈ xs ∧ p x = true
  | [] => by simp [filterList]
  | a :: xs => by
    unfold filterList
    cases hPa : p a with
    | true =>
      simp only [↓reduceIte, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | htl
        · exact ⟨Or.inl rfl, hPa⟩
        · have ⟨hm, hp⟩ := (mem_filterList (xs := xs)).mp htl
          exact ⟨Or.inr hm, hp⟩
      · intro ⟨hm, hp⟩
        rcases hm with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ((mem_filterList (xs := xs)).mpr ⟨htl, hp⟩)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · intro h
        have ⟨hm, hp⟩ := (mem_filterList (xs := xs)).mp h
        exact ⟨Or.inr hm, hp⟩
      · intro ⟨hm, hp⟩
        rcases hm with rfl | htl
        · rw [hPa] at hp; cases hp
        · exact (mem_filterList (xs := xs)).mpr ⟨htl, hp⟩

noncomputable def allSameTrait (tid : Nat) : List MethodCandidate → Bool
  | [] => true
  | c :: cs =>
    match c.pickKind with
    | .traitPick _ => eqNat c.traitId tid && allSameTrait tid cs
    | _ => false

/-- `collapse_candidates_to_trait_pick` (`probe.rs:2391-2428`):
    if `>= 2` applicable candidates all belong to the exact same trait (`TraitCandidate`),
    collapse them into a single `TraitPick` immediately (before unstable filtering,
    matching `probe.rs:1814-1820`). -/
noncomputable def tryCollapseSameTrait : List MethodCandidate → Option MethodCandidate
  | [] => none
  | [_] => none
  | c :: cs =>
    match c.pickKind with
    | .traitPick _ =>
      if allSameTrait c.traitId cs then some c else none
    | _ => none

noncomputable def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if eqNat x y then true else memNat x ys

noncomputable def dominatesAll (dom : MethodCandidate) : List MethodCandidate → Bool
  | [] => true
  | c :: cs =>
    if eqNat c.id dom.id then dominatesAll dom cs
    else memNat c.traitId dom.supertraits && dominatesAll dom cs

noncomputable def findDominantSubtraitAux (allCands : List MethodCandidate) :
    List MethodCandidate → Option MethodCandidate
  | [] => none
  | c :: cs =>
    match c.pickKind with
    | .traitPick _ =>
      if dominatesAll c allCands then some c else findDominantSubtraitAux allCands cs
    | _ => findDominantSubtraitAux allCands cs

/-- `collapse_candidates_to_subtrait_pick` (`probe.rs:2439-2514`, RFC #3624). -/
noncomputable def tryCollapseSubtrait (allCands : List MethodCandidate) : Option MethodCandidate :=
  findDominantSubtraitAux allCands allCands

/-- Adjustment synthesized by `pick_by_value_method` / `pick_autorefd_method` /
    `pick_const_ptr_method` / `pick_reborrow_pin_method` (`probe.rs:1589-1739`). -/
noncomputable def synthesizeAdjustment (step : CandidateStep) (stage : AdjustmentStage) :
    Nat × Option AutorefOrPtrAdjustment :=
  match stage with
  | .byValue =>
    match step.selfTy with
    | .ref m _ => (Nat.succ step.autoderefs, some (.autoref m false))
    | .pin (.ref m _) => (step.autoderefs, some (.reborrowPin m))
    | _ => (step.autoderefs, none)
  | .autorefImm => (step.autoderefs, some (.autoref .imm step.unsize))
  | .autorefMut => (step.autoderefs, some (.autoref .mutbl step.unsize))
  | .constPtr => (step.autoderefs, some .toConstPtr)
  | .reborrowPin => (step.autoderefs, some (.reborrowPin .imm))

noncomputable def mkMethodPick (stepIdx : Nat) (step : CandidateStep)
    (stage : AdjustmentStage) (c : MethodCandidate) : MethodPick :=
  let (ad, adj) := synthesizeAdjustment step stage
  { stepIdx := stepIdx
    step := step
    stage := stage
    autoderefs := ad
    adjustment := adj
    cand := c }

noncomputable def candIdsOf : List MethodCandidate → List Nat
  | [] => []
  | c :: cs => c.id :: candIdsOf cs

/-- Exact model of `consider_candidates` (`probe.rs:1783-1858`). -/
noncomputable def considerCandidatesList (cfg : ProbeConfig) (step : CandidateStep)
    (stage : AdjustmentStage) (bucket : CandidateBucket) (stepIdx : Nat)
    (trackUnstable : Bool) (cands : List MethodCandidate) : ProbeOutcome :=
  let matching := filterList (candidateMatches cfg step stage bucket) cands
  match matching with
  | [] => .noMatch
  | [c] =>
    if trackUnstable && c.isUnstable then .noMatch
    else if c.hasBadReturnType then .badReturnType
    else .picked (mkMethodPick stepIdx step stage c)
  | _ :: _ :: _ =>
    match tryCollapseSameTrait matching with
    | some c =>
      .picked (mkMethodPick stepIdx step stage c)
    | none =>
      let retained :=
        if trackUnstable then filterList (fun c => !c.isUnstable) matching
        else matching
      match retained with
      | [] => .noMatch
      | [c] =>
        if c.hasBadReturnType then .badReturnType
        else .picked (mkMethodPick stepIdx step stage c)
      | _ :: _ :: _ =>
        if cfg.supertraitItemShadowing then
          match tryCollapseSubtrait retained with
          | some c => .picked (mkMethodPick stepIdx step stage c)
          | none => .ambiguity (candIdsOf retained)
        else .ambiguity (candIdsOf retained)

/-- `pick_method` (`probe.rs:1741-1781`): checks `.inherent` strictly before `.extension`.
    Notice that `.ambiguity` or `.badReturnType` in `.inherent` immediately aborts
    without searching `.extension`. -/
noncomputable def pickMethod (cfg : ProbeConfig) (step : CandidateStep)
    (stage : AdjustmentStage) (stepIdx : Nat) (trackUnstable : Bool)
    (cands : List MethodCandidate) : ProbeOutcome :=
  match considerCandidatesList cfg step stage .inherent stepIdx trackUnstable cands with
  | .noMatch => considerCandidatesList cfg step stage .extension stepIdx trackUnstable cands
  | res => res

/-- Check whether `shadower` shadows an inherent autoref'd method at `targetStage`
    (`check_for_shadowed_autorefd_method`, `probe.rs:1496-1581`), including the
    exact `autoderefs` equality check (`may_shadow_based_on_autoderefs`) that creates
    the documented double-ref bypass (`probe.rs:1534-1562`). -/
noncomputable def findShadowedAutoref (cfg : ProbeConfig) (shadower : MethodPick)
    (step : CandidateStep) (targetStage : AdjustmentStage)
    (trackUnstable : Bool) (cands : List MethodCandidate) : Option (List Nat) :=
  if !eqNat step.autoderefs shadower.autoderefs then none
  else
    let matching := filterList
      (fun c =>
        candidateMatches cfg step targetStage .inherent c &&
        candidateMayShadow shadower.cand c &&
        (!trackUnstable || !c.isUnstable))
      cands
    match matching with
    | [] => none
    | _ => some (shadower.cand.id :: candIdsOf matching)

/-- Exact per-step probe order (`pick_all_method`, `probe.rs:1375-1478`). -/
noncomputable def pickAtStep (cfg : ProbeConfig) (step : CandidateStep)
    (stepIdx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate) : ProbeOutcome :=
  match pickMethod cfg step .byValue stepIdx trackUnstable cands with
  | .picked p =>
    if cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent then
      match findShadowedAutoref cfg p step .autorefImm trackUnstable cands with
      | some ids => .ambiguity ids
      | none =>
        match findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
        | some ids => .ambiguity ids
        | none => .picked p
    else .picked p
  | .ambiguity ids => .ambiguity ids
  | .badReturnType => .badReturnType
  | .noMatch =>
    match pickMethod cfg step .autorefImm stepIdx trackUnstable cands with
    | .picked p =>
      if cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent then
        match findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
        | some ids => .ambiguity ids
        | none => .picked p
      else .picked p
    | .ambiguity ids => .ambiguity ids
    | .badReturnType => .badReturnType
    | .noMatch =>
      match pickMethod cfg step .autorefMut stepIdx trackUnstable cands with
      | .noMatch =>
        match pickMethod cfg step .constPtr stepIdx trackUnstable cands with
        | .noMatch => pickMethod cfg step .reborrowPin stepIdx trackUnstable cands
        | res => res
      | res => res

/-- Step eligibility (`probe.rs:1356, 1361`):
    must be `reachableViaDeref`, not `fromUnsafeDeref`, and not `Ty.err`. -/
noncomputable def stepEligible (step : CandidateStep) : Bool :=
  step.reachableViaDeref && !step.fromUnsafeDeref &&
  match step.selfTy with
  | .err => false
  | _ => true

/-- Single pass of `pick_all_method` over `steps` starting at index `baseIdx`. -/
noncomputable def probePassAux (cfg : ProbeConfig) (trackUnstable : Bool)
    (cands : List MethodCandidate) : Nat → List CandidateStep → ProbeOutcome
  | _, [] => .noMatch
  | idx, step :: rest =>
    if stepEligible step then
      match pickAtStep cfg step idx trackUnstable cands with
      | .noMatch => probePassAux cfg trackUnstable cands (Nat.succ idx) rest
      | res => res
    else
      probePassAux cfg trackUnstable cands (Nat.succ idx) rest

/-- Full `pick_core` two-pass search (`probe.rs:1319-1344`):
    stable candidates first (`trackUnstable = true`), falling back to including
    unstable candidates (`trackUnstable = false`) only on `.noMatch`. -/
noncomputable def probeMethod (cfg : ProbeConfig) (steps : List CandidateStep)
    (cands : List MethodCandidate) : ProbeOutcome :=
  match probePassAux cfg true cands 0 steps with
  | .noMatch => probePassAux cfg false cands 0 steps
  | res => res

/-! ## Section 4: Core Soundness, Determinism, and Lexicographic Minimality Theorems -/

noncomputable def listGetOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOpt xs n

theorem considerCandidatesList_noMatch_for_stable
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (bucket : CandidateBucket) (stepIdx : Nat) (trackUnstable : Bool)
    (cands : List MethodCandidate)
    (hNF : considerCandidatesList cfg step stage bucket stepIdx trackUnstable cands = .noMatch)
    (c : MethodCandidate) (hMem : c ∈ cands) (hSt : trackUnstable = false ∨ c.isUnstable = false) :
    candidateMatches cfg step stage bucket c = false := by
  unfold considerCandidatesList at hNF
  cases hM : filterList (candidateMatches cfg step stage bucket) cands with
  | nil =>
    cases hCM : candidateMatches cfg step stage bucket c with
    | false => rfl
    | true =>
      have hIn := mem_filterList.mpr ⟨hMem, hCM⟩
      rw [hM] at hIn; cases hIn
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [hM] at hNF
      cases hT : (trackUnstable && a.isUnstable) with
      | false =>
        simp only [hT, Bool.false_eq_true, ↓reduceIte] at hNF
        cases hBad : a.hasBadReturnType <;> simp [hBad] at hNF
      | true =>
        cases hCM : candidateMatches cfg step stage bucket c with
        | false => rfl
        | true =>
          have hIn := mem_filterList.mpr ⟨hMem, hCM⟩
          rw [hM, List.mem_singleton] at hIn
          subst hIn
          simp only [Bool.and_eq_true] at hT
          rcases hSt with hF | hCSt
          · rw [hF] at hT; cases hT.1
          · rw [hCSt] at hT; cases hT.2
    | cons b tl2 =>
      simp only [hM] at hNF
      cases hCol : tryCollapseSameTrait (a :: b :: tl2) with
      | some d => simp [hCol] at hNF
      | none =>
        simp only [hCol] at hNF
        cases hRet : (if trackUnstable then filterList (fun x => !x.isUnstable) (a :: b :: tl2)
                      else a :: b :: tl2) with
        | nil =>
          cases hCM : candidateMatches cfg step stage bucket c with
          | false => rfl
          | true =>
            have hIn : c ∈ a :: b :: tl2 := by
              rw [← hM]; exact mem_filterList.mpr ⟨hMem, hCM⟩
            cases trackUnstable with
            | false => simp only [Bool.false_eq_true, ↓reduceIte] at hRet; rw [hRet] at hIn; cases hIn
            | true =>
              simp only [↓reduceIte] at hRet
              rcases hSt with hF | hCSt
              · cases hF
              · have hInR : c ∈ filterList (fun x => !x.isUnstable) (a :: b :: tl2) :=
                  mem_filterList.mpr ⟨hIn, by simp [hCSt]⟩
                rw [hRet] at hInR; cases hInR
        | cons r1 rrest =>
          cases rrest with
          | nil =>
            simp only [hRet] at hNF
            cases hBad : r1.hasBadReturnType <;> simp [hBad] at hNF
          | cons r2 rrest2 =>
            simp only [hRet] at hNF
            cases hSh : cfg.supertraitItemShadowing with
            | false => simp [hSh] at hNF
            | true =>
              simp only [hSh, ↓reduceIte] at hNF
              cases hSub : tryCollapseSubtrait (r1 :: r2 :: rrest2) <;> simp [hSub] at hNF

theorem considerCandidatesList_picked_spec
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (bucket : CandidateBucket) (stepIdx : Nat) (trackUnstable : Bool)
    (cands : List MethodCandidate) (p : MethodPick)
    (hP : considerCandidatesList cfg step stage bucket stepIdx trackUnstable cands = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧ p.stage = stage ∧ p.cand.bucket = bucket ∧
    p.cand ∈ cands ∧ candidateMatches cfg step stage bucket p.cand = true := by
  unfold considerCandidatesList at hP
  cases hM : filterList (candidateMatches cfg step stage bucket) cands with
  | nil => rw [hM] at hP; cases hP
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [hM] at hP
      cases hT : (trackUnstable && a.isUnstable) with
      | true => simp [hT] at hP
      | false =>
        simp only [hT, Bool.false_eq_true, ↓reduceIte] at hP
        cases hBad : a.hasBadReturnType with
        | true => simp [hBad] at hP
        | false =>
          simp only [hBad, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
          subst hP
          have hIn : a ∈ filterList (candidateMatches cfg step stage bucket) cands := by
            rw [hM]; exact List.mem_cons_self
          have ⟨hMem, hMatch⟩ := mem_filterList.mp hIn
          have hB : a.bucket = bucket := by
            unfold candidateMatches at hMatch
            cases hAllow : stepAllowsStage cfg step stage <;> simp [hAllow] at hMatch
            exact eqBucket_sound hMatch.1.1
          exact ⟨rfl, rfl, rfl, hB, hMem, hMatch⟩
    | cons b tl2 =>
      simp only [hM] at hP
      cases hCol : tryCollapseSameTrait (a :: b :: tl2) with
      | some d =>
        simp only [hCol, ProbeOutcome.picked.injEq] at hP
        subst hP
        have hMemD : d ∈ a :: b :: tl2 := by
          unfold tryCollapseSameTrait at hCol
          cases hPK : a.pickKind with
          | inherentImplPick | objectPick | whereClausePick _ => simp [hPK] at hCol
          | traitPick _ =>
            simp only [hPK] at hCol
            cases hAll : allSameTrait a.traitId (b :: tl2) with
            | false => simp [hAll] at hCol
            | true =>
              simp only [hAll, ↓reduceIte, Option.some.injEq] at hCol
              subst hCol
              exact List.mem_cons_self
        have hIn : d ∈ filterList (candidateMatches cfg step stage bucket) cands := by
          rw [hM]; exact hMemD
        have ⟨hMem, hMatch⟩ := mem_filterList.mp hIn
        have hB : d.bucket = bucket := by
          unfold candidateMatches at hMatch
          cases hAllow : stepAllowsStage cfg step stage <;> simp [hAllow] at hMatch
          exact eqBucket_sound hMatch.1.1
        exact ⟨rfl, rfl, rfl, hB, hMem, hMatch⟩
      | none =>
        simp only [hCol] at hP
        have hRetSub :
            ∀ x, x ∈ (if trackUnstable then filterList (fun c => !c.isUnstable) (a :: b :: tl2)
                      else a :: b :: tl2) →
              x ∈ filterList (candidateMatches cfg step stage bucket) cands := by
          intro x hx
          rw [hM]
          cases trackUnstable with
          | true => simp only [↓reduceIte] at hx; exact (mem_filterList.mp hx).1
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hx; exact hx
        cases hRet : (if trackUnstable then filterList (fun c => !c.isUnstable) (a :: b :: tl2)
                      else a :: b :: tl2) with
        | nil => simp [hRet] at hP
        | cons r1 rrest =>
          cases rrest with
          | nil =>
            simp only [hRet] at hP
            cases hBad : r1.hasBadReturnType with
            | true => simp [hBad] at hP
            | false =>
              simp only [hBad, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
              subst hP
              have hIn := hRetSub r1 (by rw [hRet]; exact List.mem_cons_self)
              have ⟨hMem, hMatch⟩ := mem_filterList.mp hIn
              have hB : r1.bucket = bucket := by
                unfold candidateMatches at hMatch
                cases hAllow : stepAllowsStage cfg step stage <;> simp [hAllow] at hMatch
                exact eqBucket_sound hMatch.1.1
              exact ⟨rfl, rfl, rfl, hB, hMem, hMatch⟩
          | cons r2 rrest2 =>
            simp only [hRet] at hP
            cases hShad : cfg.supertraitItemShadowing with
            | false => simp [hShad] at hP
            | true =>
              simp only [hShad, ↓reduceIte] at hP
              cases hSub : tryCollapseSubtrait (r1 :: r2 :: rrest2) with
              | none => simp [hSub] at hP
              | some dom =>
                simp only [hSub, ProbeOutcome.picked.injEq] at hP
                subst hP
                have hDomIn : dom ∈ r1 :: r2 :: rrest2 := by
                  unfold tryCollapseSubtrait at hSub
                  have hAux :
                      ∀ (allC xs : List MethodCandidate),
                        findDominantSubtraitAux allC xs = some dom → dom ∈ xs := by
                    intro allC xs hF
                    induction xs with
                    | nil => cases hF
                    | cons x xs ih =>
                      unfold findDominantSubtraitAux at hF
                      cases hPK : x.pickKind with
                      | inherentImplPick | objectPick | whereClausePick _ =>
                        simp only [hPK] at hF
                        exact List.mem_cons_of_mem x (ih hF)
                      | traitPick _ =>
                        simp only [hPK] at hF
                        cases hD : dominatesAll x allC with
                        | true =>
                          simp only [hD, ↓reduceIte, Option.some.injEq] at hF
                          subst hF
                          exact List.mem_cons_self
                        | false =>
                          simp only [hD, Bool.false_eq_true, ↓reduceIte] at hF
                          exact List.mem_cons_of_mem x (ih hF)
                  exact hAux (r1 :: r2 :: rrest2) (r1 :: r2 :: rrest2) hSub
                have hIn := hRetSub dom (by rw [hRet]; exact hDomIn)
                have ⟨hMem, hMatch⟩ := mem_filterList.mp hIn
                have hB : dom.bucket = bucket := by
                  unfold candidateMatches at hMatch
                  cases hAllow : stepAllowsStage cfg step stage <;> simp [hAllow] at hMatch
                  exact eqBucket_sound hMatch.1.1
                exact ⟨rfl, rfl, rfl, hB, hMem, hMatch⟩

theorem pickMethod_noMatch_for_stable
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (stepIdx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate)
    (hNF : pickMethod cfg step stage stepIdx trackUnstable cands = .noMatch)
    (c : MethodCandidate) (hMem : c ∈ cands) (hSt : trackUnstable = false ∨ c.isUnstable = false) :
    candidateMatches cfg step stage c.bucket c = false := by
  unfold pickMethod at hNF
  cases hInh : considerCandidatesList cfg step stage .inherent stepIdx trackUnstable cands with
  | noMatch =>
    rw [hInh] at hNF
    cases hB : c.bucket with
    | inherent =>
      exact considerCandidatesList_noMatch_for_stable cfg step stage .inherent stepIdx trackUnstable cands hInh c hMem hSt
    | extension =>
      exact considerCandidatesList_noMatch_for_stable cfg step stage .extension stepIdx trackUnstable cands hNF c hMem hSt
  | picked _ => rw [hInh] at hNF; cases hNF
  | ambiguity _ => rw [hInh] at hNF; cases hNF
  | badReturnType => rw [hInh] at hNF; cases hNF

theorem pickMethod_picked_spec
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (stepIdx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate) (p : MethodPick)
    (hP : pickMethod cfg step stage stepIdx trackUnstable cands = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧ p.stage = stage ∧
    p.cand ∈ cands ∧ candidateMatches cfg step stage p.cand.bucket p.cand = true ∧
    (∀ c ∈ cands, (trackUnstable = false ∨ c.isUnstable = false) →
      candidateMatches cfg step stage c.bucket c = true →
      bucketRank p.cand.bucket ≤ bucketRank c.bucket) := by
  unfold pickMethod at hP
  cases hInh : considerCandidatesList cfg step stage .inherent stepIdx trackUnstable cands with
  | picked q =>
    rw [hInh] at hP
    cases hP
    have ⟨hI, hS, hSt, hB, hMem, hMatch⟩ :=
      considerCandidatesList_picked_spec cfg step stage .inherent stepIdx trackUnstable cands p hInh
    refine ⟨hI, hS, hSt, hMem, by rw [hB]; exact hMatch, ?_⟩
    intro c _ _ _
    rw [hB]; exact Nat.zero_le _
  | ambiguity _ => rw [hInh] at hP; cases hP
  | badReturnType => rw [hInh] at hP; cases hP
  | noMatch =>
    rw [hInh] at hP
    have ⟨hI, hS, hSt, hB, hMem, hMatch⟩ :=
      considerCandidatesList_picked_spec cfg step stage .extension stepIdx trackUnstable cands p hP
    refine ⟨hI, hS, hSt, hMem, by rw [hB]; exact hMatch, ?_⟩
    intro c hCMem hCSt hCMatch
    cases hCB : c.bucket with
    | inherent =>
      rw [hCB] at hCMatch
      have hNo := considerCandidatesList_noMatch_for_stable
        cfg step stage .inherent stepIdx trackUnstable cands hInh c hCMem hCSt
      rw [hNo] at hCMatch; cases hCMatch
    | extension =>
      rw [hB]; exact Nat.le_refl _

theorem pickAtStep_noMatch_for_stable
    (cfg : ProbeConfig) (step : CandidateStep) (stepIdx : Nat)
    (trackUnstable : Bool) (cands : List MethodCandidate)
    (hNF : pickAtStep cfg step stepIdx trackUnstable cands = .noMatch)
    (stage : AdjustmentStage) (c : MethodCandidate) (hMem : c ∈ cands)
    (hSt : trackUnstable = false ∨ c.isUnstable = false) :
    candidateMatches cfg step stage c.bucket c = false := by
  unfold pickAtStep at hNF
  cases h0 : pickMethod cfg step .byValue stepIdx trackUnstable cands with
  | picked p =>
    simp only [h0] at hNF
    cases hA : (cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent) with
    | false => simp [hA] at hNF
    | true =>
      simp only [hA, ↓reduceIte] at hNF
      cases hS1 : findShadowedAutoref cfg p step .autorefImm trackUnstable cands with
      | some _ => simp [hS1] at hNF
      | none =>
        simp only [hS1] at hNF
        cases hS2 : findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
        | some _ => simp [hS2] at hNF
        | none => simp [hS2] at hNF
  | ambiguity _ => simp [h0] at hNF
  | badReturnType => simp [h0] at hNF
  | noMatch =>
    simp only [h0] at hNF
    cases h1 : pickMethod cfg step .autorefImm stepIdx trackUnstable cands with
    | picked p =>
      simp only [h1] at hNF
      cases hA : (cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent) with
      | false => simp [hA] at hNF
      | true =>
        simp only [hA, ↓reduceIte] at hNF
        cases hS : findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
        | some _ => simp [hS] at hNF
        | none => simp [hS] at hNF
    | ambiguity _ => simp [h1] at hNF
    | badReturnType => simp [h1] at hNF
    | noMatch =>
      simp only [h1] at hNF
      cases h2 : pickMethod cfg step .autorefMut stepIdx trackUnstable cands with
      | picked _ => simp [h2] at hNF
      | ambiguity _ => simp [h2] at hNF
      | badReturnType => simp [h2] at hNF
      | noMatch =>
        simp only [h2] at hNF
        cases h3 : pickMethod cfg step .constPtr stepIdx trackUnstable cands with
        | picked _ => simp [h3] at hNF
        | ambiguity _ => simp [h3] at hNF
        | badReturnType => simp [h3] at hNF
        | noMatch =>
          simp only [h3] at hNF
          cases stage with
          | byValue     => exact pickMethod_noMatch_for_stable cfg step .byValue stepIdx trackUnstable cands h0 c hMem hSt
          | autorefImm  => exact pickMethod_noMatch_for_stable cfg step .autorefImm stepIdx trackUnstable cands h1 c hMem hSt
          | autorefMut  => exact pickMethod_noMatch_for_stable cfg step .autorefMut stepIdx trackUnstable cands h2 c hMem hSt
          | constPtr    => exact pickMethod_noMatch_for_stable cfg step .constPtr stepIdx trackUnstable cands h3 c hMem hSt
          | reborrowPin => exact pickMethod_noMatch_for_stable cfg step .reborrowPin stepIdx trackUnstable cands hNF c hMem hSt

theorem pickAtStep_picked_spec
    (cfg : ProbeConfig) (step : CandidateStep) (stepIdx : Nat)
    (trackUnstable : Bool) (cands : List MethodCandidate) (p : MethodPick)
    (hP : pickAtStep cfg step stepIdx trackUnstable cands = .picked p) :
    p.stepIdx = stepIdx ∧ p.step = step ∧
    p.cand ∈ cands ∧ candidateMatches cfg step p.stage p.cand.bucket p.cand = true ∧
    (∀ stage c, c ∈ cands → (trackUnstable = false ∨ c.isUnstable = false) →
      candidateMatches cfg step stage c.bucket c = true →
      stageRank p.stage < stageRank stage ∨
      (stageRank p.stage = stageRank stage ∧ bucketRank p.cand.bucket ≤ bucketRank c.bucket)) := by
  unfold pickAtStep at hP
  cases h0 : pickMethod cfg step .byValue stepIdx trackUnstable cands with
  | ambiguity _ => simp [h0] at hP
  | badReturnType => simp [h0] at hP
  | picked q =>
    simp only [h0] at hP
    have hEqQ : q = p := by
      cases hA : (cfg.arbitrarySelfTypes && eqBucket q.cand.bucket .inherent) with
      | false =>
        simp only [hA, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
        exact hP
      | true =>
        simp only [hA, ↓reduceIte] at hP
        cases hS1 : findShadowedAutoref cfg q step .autorefImm trackUnstable cands with
        | some _ => simp [hS1] at hP
        | none =>
          simp only [hS1] at hP
          cases hS2 : findShadowedAutoref cfg q step .autorefMut trackUnstable cands with
          | some _ => simp [hS2] at hP
          | none =>
            simp only [hS2, ProbeOutcome.picked.injEq] at hP
            exact hP
    subst hEqQ
    have ⟨hI, hS, hSt, hMem, hMatch, hMin⟩ :=
      pickMethod_picked_spec cfg step .byValue stepIdx trackUnstable cands q h0
    refine ⟨hI, hS, hMem, hSt ▸ hMatch, ?_⟩
    intro stage c hCMem hCSt hCMatch
    cases stage with
    | byValue => exact Or.inr ⟨by rw [hSt], hMin c hCMem hCSt hCMatch⟩
    | autorefImm => exact Or.inl (by rw [hSt]; exact Nat.zero_lt_succ 0)
    | autorefMut => exact Or.inl (by rw [hSt]; exact Nat.zero_lt_succ 1)
    | constPtr => exact Or.inl (by rw [hSt]; exact Nat.zero_lt_succ 2)
    | reborrowPin => exact Or.inl (by rw [hSt]; exact Nat.zero_lt_succ 3)
  | noMatch =>
    simp only [h0] at hP
    cases h1 : pickMethod cfg step .autorefImm stepIdx trackUnstable cands with
    | ambiguity _ => simp [h1] at hP
    | badReturnType => simp [h1] at hP
    | picked q =>
      simp only [h1] at hP
      have hEqQ : q = p := by
        cases hA : (cfg.arbitrarySelfTypes && eqBucket q.cand.bucket .inherent) with
        | false =>
          simp only [hA, Bool.false_eq_true, ↓reduceIte, ProbeOutcome.picked.injEq] at hP
          exact hP
        | true =>
          simp only [hA, ↓reduceIte] at hP
          cases hS : findShadowedAutoref cfg q step .autorefMut trackUnstable cands with
          | some _ => simp [hS] at hP
          | none =>
            simp only [hS, ProbeOutcome.picked.injEq] at hP
            exact hP
      subst hEqQ
      have ⟨hI, hS, hSt, hMem, hMatch, hMin⟩ :=
        pickMethod_picked_spec cfg step .autorefImm stepIdx trackUnstable cands q h1
      refine ⟨hI, hS, hMem, hSt ▸ hMatch, ?_⟩
      intro stage c hCMem hCSt hCMatch
      cases stage with
      | byValue =>
        have hNo := pickMethod_noMatch_for_stable cfg step .byValue stepIdx trackUnstable cands h0 c hCMem hCSt
        rw [hNo] at hCMatch; cases hCMatch
      | autorefImm => exact Or.inr ⟨by rw [hSt], hMin c hCMem hCSt hCMatch⟩
      | autorefMut => exact Or.inl (by rw [hSt]; exact Nat.lt_succ_self 1)
      | constPtr => exact Or.inl (by rw [hSt]; exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2))
      | reborrowPin =>
        exact Or.inl (by rw [hSt]; exact Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)) (Nat.lt_succ_self 3))
    | noMatch =>
      simp only [h1] at hP
      cases h2 : pickMethod cfg step .autorefMut stepIdx trackUnstable cands with
      | ambiguity _ => simp [h2] at hP
      | badReturnType => simp [h2] at hP
      | picked q =>
        simp only [h2, ProbeOutcome.picked.injEq] at hP; subst hP
        have ⟨hI, hS, hSt, hMem, hMatch, hMin⟩ :=
          pickMethod_picked_spec cfg step .autorefMut stepIdx trackUnstable cands q h2
        refine ⟨hI, hS, hMem, hSt ▸ hMatch, ?_⟩
        intro stage c hCMem hCSt hCMatch
        cases stage with
        | byValue =>
          have hNo := pickMethod_noMatch_for_stable cfg step .byValue stepIdx trackUnstable cands h0 c hCMem hCSt
          rw [hNo] at hCMatch; cases hCMatch
        | autorefImm =>
          have hNo := pickMethod_noMatch_for_stable cfg step .autorefImm stepIdx trackUnstable cands h1 c hCMem hCSt
          rw [hNo] at hCMatch; cases hCMatch
        | autorefMut => exact Or.inr ⟨by rw [hSt], hMin c hCMem hCSt hCMatch⟩
        | constPtr => exact Or.inl (by rw [hSt]; exact Nat.lt_succ_self 2)
        | reborrowPin => exact Or.inl (by rw [hSt]; exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3))
      | noMatch =>
        simp only [h2] at hP
        cases h3 : pickMethod cfg step .constPtr stepIdx trackUnstable cands with
        | ambiguity _ => simp [h3] at hP
        | badReturnType => simp [h3] at hP
        | picked q =>
          simp only [h3, ProbeOutcome.picked.injEq] at hP; subst hP
          have ⟨hI, hS, hSt, hMem, hMatch, hMin⟩ :=
            pickMethod_picked_spec cfg step .constPtr stepIdx trackUnstable cands q h3
          refine ⟨hI, hS, hMem, hSt ▸ hMatch, ?_⟩
          intro stage c hCMem hCSt hCMatch
          cases stage with
          | byValue =>
            have hNo := pickMethod_noMatch_for_stable cfg step .byValue stepIdx trackUnstable cands h0 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | autorefImm =>
            have hNo := pickMethod_noMatch_for_stable cfg step .autorefImm stepIdx trackUnstable cands h1 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | autorefMut =>
            have hNo := pickMethod_noMatch_for_stable cfg step .autorefMut stepIdx trackUnstable cands h2 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | constPtr => exact Or.inr ⟨by rw [hSt], hMin c hCMem hCSt hCMatch⟩
          | reborrowPin => exact Or.inl (by rw [hSt]; exact Nat.lt_succ_self 3)
        | noMatch =>
          simp only [h3] at hP
          have ⟨hI, hS, hSt, hMem, hMatch, hMin⟩ :=
            pickMethod_picked_spec cfg step .reborrowPin stepIdx trackUnstable cands p hP
          refine ⟨hI, hS, hMem, hSt ▸ hMatch, ?_⟩
          intro stage c hCMem hCSt hCMatch
          cases stage with
          | byValue =>
            have hNo := pickMethod_noMatch_for_stable cfg step .byValue stepIdx trackUnstable cands h0 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | autorefImm =>
            have hNo := pickMethod_noMatch_for_stable cfg step .autorefImm stepIdx trackUnstable cands h1 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | autorefMut =>
            have hNo := pickMethod_noMatch_for_stable cfg step .autorefMut stepIdx trackUnstable cands h2 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | constPtr =>
            have hNo := pickMethod_noMatch_for_stable cfg step .constPtr stepIdx trackUnstable cands h3 c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | reborrowPin => exact Or.inr ⟨by rw [hSt], hMin c hCMem hCSt hCMatch⟩

theorem probePassAux_picked_spec (cfg : ProbeConfig) (trackUnstable : Bool)
    (cands : List MethodCandidate) :
    ∀ (steps : List CandidateStep) (baseIdx : Nat) (p : MethodPick),
      probePassAux cfg trackUnstable cands baseIdx steps = .picked p →
      stepEligible p.step = true ∧
      baseIdx ≤ p.stepIdx ∧
      listGetOpt steps (p.stepIdx - baseIdx) = some p.step ∧
      p.cand ∈ cands ∧
      candidateMatches cfg p.step p.stage p.cand.bucket p.cand = true ∧
      (∀ (offset : Nat) (s : CandidateStep) (stage : AdjustmentStage) (c : MethodCandidate),
        listGetOpt steps offset = some s →
        stepEligible s = true →
        c ∈ cands →
        (trackUnstable = false ∨ c.isUnstable = false) →
        candidateMatches cfg s stage c.bucket c = true →
        ProbeKeyLe p.stepIdx p.stage p.cand.bucket (baseIdx + offset) stage c.bucket)
  | [], _, _, h => by cases h
  | step :: rest, baseIdx, p, h => by
    unfold probePassAux at h
    cases hElig : stepEligible step with
    | false =>
      simp only [hElig, Bool.false_eq_true, ↓reduceIte] at h
      have ⟨hPElig, hGe, hGet, hMem, hMatch, hMin⟩ :=
        probePassAux_picked_spec cfg trackUnstable cands rest (Nat.succ baseIdx) p h
      have hGe0 : baseIdx ≤ p.stepIdx := Nat.le_trans (Nat.le_succ baseIdx) hGe
      have hSub : p.stepIdx - baseIdx = Nat.succ (p.stepIdx - Nat.succ baseIdx) := by
        cases hEq : p.stepIdx - baseIdx with
        | zero =>
          have hLe : p.stepIdx ≤ baseIdx := Nat.le_of_sub_eq_zero hEq
          exact False.elim (Nat.not_lt_of_ge hLe hGe)
        | succ k =>
          have hK : p.stepIdx - Nat.succ baseIdx = k := by
            rw [Nat.sub_succ, hEq, Nat.pred_succ]
          rw [hK]
      refine ⟨hPElig, hGe0, ?_, hMem, hMatch, ?_⟩
      · rw [hSub]; exact hGet
      · intro offset s stage c hOff hSElig hCMem hCSt hCMatch
        cases offset with
        | zero =>
          simp only [listGetOpt, Option.some.injEq] at hOff
          subst hOff
          rw [hElig] at hSElig; cases hSElig
        | succ k =>
          have hRes := hMin k s stage c hOff hSElig hCMem hCSt hCMatch
          have hIdx : Nat.succ baseIdx + k = baseIdx + Nat.succ k := by
            rw [Nat.succ_add, Nat.add_succ]
          rw [hIdx] at hRes
          exact hRes
    | true =>
      simp only [hElig, ↓reduceIte] at h
      cases hStep : pickAtStep cfg step baseIdx trackUnstable cands with
      | ambiguity _ => rw [hStep] at h; cases h
      | badReturnType => rw [hStep] at h; cases h
      | picked q =>
        rw [hStep] at h
        cases h
        have ⟨hI, hS, hMem, hMatch, hMin⟩ :=
          pickAtStep_picked_spec cfg step baseIdx trackUnstable cands p hStep
        refine ⟨by rw [hS]; exact hElig, by rw [hI]; exact Nat.le_refl _, ?_, hMem, by rw [hS]; exact hMatch, ?_⟩
        · rw [hI, Nat.sub_self, hS]; rfl
        · intro offset s stage c hOff _ hCMem hCSt hCMatch
          cases offset with
          | zero =>
            simp only [listGetOpt, Option.some.injEq] at hOff
            subst hOff
            rw [hI, Nat.add_zero]
            exact Or.inr ⟨rfl, hMin stage c hCMem hCSt hCMatch⟩
          | succ k =>
            rw [hI]
            exact Or.inl (Nat.lt_add_of_pos_right (Nat.succ_pos k))
      | noMatch =>
        rw [hStep] at h
        have ⟨hPElig, hGe, hGet, hMem, hMatch, hMin⟩ :=
          probePassAux_picked_spec cfg trackUnstable cands rest (Nat.succ baseIdx) p h
        have hGe0 : baseIdx ≤ p.stepIdx := Nat.le_trans (Nat.le_succ baseIdx) hGe
        have hSub : p.stepIdx - baseIdx = Nat.succ (p.stepIdx - Nat.succ baseIdx) := by
          cases hEq : p.stepIdx - baseIdx with
          | zero =>
            have hLe : p.stepIdx ≤ baseIdx := Nat.le_of_sub_eq_zero hEq
            exact False.elim (Nat.not_lt_of_ge hLe hGe)
          | succ k =>
            have hK : p.stepIdx - Nat.succ baseIdx = k := by
              rw [Nat.sub_succ, hEq, Nat.pred_succ]
            rw [hK]
        refine ⟨hPElig, hGe0, ?_, hMem, hMatch, ?_⟩
        · rw [hSub]; exact hGet
        · intro offset s stage c hOff hSElig hCMem hCSt hCMatch
          cases offset with
          | zero =>
            simp only [listGetOpt, Option.some.injEq] at hOff
            subst hOff
            have hNo := pickAtStep_noMatch_for_stable cfg step baseIdx trackUnstable cands hStep stage c hCMem hCSt
            rw [hNo] at hCMatch; cases hCMatch
          | succ k =>
            have hRes := hMin k s stage c hOff hSElig hCMem hCSt hCMatch
            have hIdx : Nat.succ baseIdx + k = baseIdx + Nat.succ k := by
              rw [Nat.succ_add, Nat.add_succ]
            rw [hIdx] at hRes
            exact hRes

/-- **Theorem 1 (Determinism & Outcome Trichotomy):**
    When all candidates have compatible return types (`hasBadReturnType = false`),
    `probeMethod` yields a unique deterministic outcome in the three-way partition
    `Picked | Ambiguity | NoMatch`, never producing `.badReturnType`. -/
theorem considerCandidatesList_no_bad_ret
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (bucket : CandidateBucket) (stepIdx : Nat) (trackUnstable : Bool)
    (cands : List MethodCandidate)
    (hGood : ∀ c ∈ cands, c.hasBadReturnType = false) :
    considerCandidatesList cfg step stage bucket stepIdx trackUnstable cands ≠ .badReturnType := by
  unfold considerCandidatesList
  have hGoodMatch : ∀ c ∈ filterList (candidateMatches cfg step stage bucket) cands,
      c.hasBadReturnType = false := fun c hc => hGood c (mem_filterList.mp hc).1
  cases hM : filterList (candidateMatches cfg step stage bucket) cands with
  | nil => intro h; cases h
  | cons a tl =>
    cases tl with
    | nil =>
      have hBa : a.hasBadReturnType = false := hGoodMatch a (by rw [hM]; exact List.mem_cons_self)
      simp only
      cases trackUnstable && a.isUnstable with
      | true => simp
      | false => simp [hBa]
    | cons b tl2 =>
      simp only
      cases tryCollapseSameTrait (a :: b :: tl2) with
      | some _ => simp
      | none =>
        simp only
        have hGoodRet : ∀ c ∈ (if trackUnstable then filterList (fun c => !c.isUnstable) (a :: b :: tl2)
                               else a :: b :: tl2), c.hasBadReturnType = false := by
          intro c hc
          apply hGoodMatch c
          rw [hM]
          cases trackUnstable with
          | true => simp only [↓reduceIte] at hc; exact (mem_filterList.mp hc).1
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at hc; exact hc
        cases hRet : (if trackUnstable then filterList (fun c => !c.isUnstable) (a :: b :: tl2)
                      else a :: b :: tl2) with
        | nil => simp
        | cons r1 rrest =>
          cases rrest with
          | nil =>
            have hBr1 := hGoodRet r1 (by rw [hRet]; exact List.mem_cons_self)
            simp [hBr1]
          | cons r2 rrest2 =>
            simp only
            cases cfg.supertraitItemShadowing with
            | false => simp
            | true =>
              cases tryCollapseSubtrait (r1 :: r2 :: rrest2) <;> simp

theorem probeMethod_trichotomy (cfg : ProbeConfig) (steps : List CandidateStep)
    (cands : List MethodCandidate) (hGood : ∀ c ∈ cands, c.hasBadReturnType = false) :
    (∃ p, probeMethod cfg steps cands = .picked p) ∨
    (∃ ids, probeMethod cfg steps cands = .ambiguity ids) ∨
    probeMethod cfg steps cands = .noMatch := by
  have hNotBadPass :
      ∀ (trackUnstable : Bool) (baseIdx : Nat) (stps : List CandidateStep),
        probePassAux cfg trackUnstable cands baseIdx stps ≠ .badReturnType := by
    intro trackUnstable baseIdx stps
    induction stps generalizing baseIdx with
    | nil => unfold probePassAux; intro h; cases h
    | cons step rest ih =>
      unfold probePassAux
      cases stepEligible step with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ih (Nat.succ baseIdx)
      | true =>
        simp only [↓reduceIte]
        have hPickNotBad :
            ∀ (st : AdjustmentStage),
              pickMethod cfg step st baseIdx trackUnstable cands ≠ .badReturnType := by
          intro st
          unfold pickMethod
          have h1 := considerCandidatesList_no_bad_ret cfg step st .inherent baseIdx trackUnstable cands hGood
          have h2 := considerCandidatesList_no_bad_ret cfg step st .extension baseIdx trackUnstable cands hGood
          cases hInh : considerCandidatesList cfg step st .inherent baseIdx trackUnstable cands with
          | noMatch => exact h2
          | picked _ => intro h; cases h
          | ambiguity _ => intro h; cases h
          | badReturnType => exact False.elim (h1 hInh)
        have hAtStepNotBad :
            pickAtStep cfg step baseIdx trackUnstable cands ≠ .badReturnType := by
          unfold pickAtStep
          cases h0 : pickMethod cfg step .byValue baseIdx trackUnstable cands with
          | picked p =>
            simp only
            cases cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent with
            | false => simp
            | true =>
              simp only [↓reduceIte]
              cases findShadowedAutoref cfg p step .autorefImm trackUnstable cands with
              | some _ => simp
              | none =>
                cases findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
                | some _ => simp
                | none => simp
          | ambiguity _ => simp
          | badReturnType => exact False.elim (hPickNotBad .byValue h0)
          | noMatch =>
            simp only
            cases h1 : pickMethod cfg step .autorefImm baseIdx trackUnstable cands with
            | picked p =>
              simp only
              cases cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent with
              | false => simp
              | true =>
                simp only [↓reduceIte]
                cases findShadowedAutoref cfg p step .autorefMut trackUnstable cands with
                | some _ => simp
                | none => simp
            | ambiguity _ => simp
            | badReturnType => exact False.elim (hPickNotBad .autorefImm h1)
            | noMatch =>
              simp only
              cases h2 : pickMethod cfg step .autorefMut baseIdx trackUnstable cands with
              | picked _ => simp
              | ambiguity _ => simp
              | badReturnType => exact False.elim (hPickNotBad .autorefMut h2)
              | noMatch =>
                simp only
                cases h3 : pickMethod cfg step .constPtr baseIdx trackUnstable cands with
                | picked _ => simp
                | ambiguity _ => simp
                | badReturnType => exact False.elim (hPickNotBad .constPtr h3)
                | noMatch => simp only; exact hPickNotBad .reborrowPin
        cases hAt : pickAtStep cfg step baseIdx trackUnstable cands with
        | noMatch => simp only; exact ih (Nat.succ baseIdx)
        | picked _ => simp
        | ambiguity _ => simp
        | badReturnType => exact False.elim (hAtStepNotBad hAt)
  unfold probeMethod
  cases hPass1 : probePassAux cfg true cands 0 steps with
  | picked p => exact Or.inl ⟨p, rfl⟩
  | ambiguity ids => exact Or.inr (Or.inl ⟨ids, rfl⟩)
  | badReturnType => exact False.elim (hNotBadPass true 0 steps hPass1)
  | noMatch =>
    simp only
    cases hPass2 : probePassAux cfg false cands 0 steps with
    | picked p => exact Or.inl ⟨p, rfl⟩
    | ambiguity ids => exact Or.inr (Or.inl ⟨ids, rfl⟩)
    | noMatch => exact Or.inr (Or.inr rfl)
    | badReturnType => exact False.elim (hNotBadPass false 0 steps hPass2)

/-- **Theorem 2 (Step-Lexicographic Optimality & Stability Priority):**
    Whenever `probeMethod cfg steps cands = .picked p`:
    1. `p.step` is an eligible step at `steps[p.stepIdx]`, `p.cand ∈ cands`, and
       `p.cand` matches `(p.step, p.stage, p.cand.bucket)`;
    2. If `probeMethod` succeeded in Pass 1 (stable), then for EVERY eligible step `s`
       at index `idx`, every adjustment stage, and every stable candidate `c`,
       `ProbeKeyLe (p.stepIdx, p.stage, p.cand.bucket) (idx, stage, c.bucket)`;
    3. If `probeMethod` fell through to Pass 2 (`trackUnstable = false`), then EVERY
       candidate (stable or unstable) satisfies `ProbeKeyLe`. -/
theorem probeMethod_lexicographic_optimality
    (cfg : ProbeConfig) (steps : List CandidateStep)
    (cands : List MethodCandidate) (p : MethodPick)
    (hP : probeMethod cfg steps cands = .picked p) :
    stepEligible p.step = true ∧
    listGetOpt steps p.stepIdx = some p.step ∧
    p.cand ∈ cands ∧
    candidateMatches cfg p.step p.stage p.cand.bucket p.cand = true ∧
    (∀ (idx : Nat) (s : CandidateStep) (stage : AdjustmentStage) (c : MethodCandidate),
      listGetOpt steps idx = some s →
      stepEligible s = true →
      c ∈ cands →
      c.isUnstable = false →
      candidateMatches cfg s stage c.bucket c = true →
      ProbeKeyLe p.stepIdx p.stage p.cand.bucket idx stage c.bucket) := by
  unfold probeMethod at hP
  cases hPass1 : probePassAux cfg true cands 0 steps with
  | ambiguity _ => rw [hPass1] at hP; cases hP
  | badReturnType => rw [hPass1] at hP; cases hP
  | noMatch =>
    rw [hPass1] at hP
    have ⟨hElig, _, hGet, hMem, hMatch, hMin⟩ :=
      probePassAux_picked_spec cfg false cands steps 0 p hP
    rw [Nat.sub_zero] at hGet
    refine ⟨hElig, hGet, hMem, hMatch, ?_⟩
    intro idx s stage c hIdx hSElig hCMem _ hCMatch
    have hRes := hMin idx s stage c hIdx hSElig hCMem (Or.inl rfl) hCMatch
    rw [Nat.zero_add] at hRes
    exact hRes
  | picked q =>
    rw [hPass1] at hP
    cases hP
    have ⟨hElig, _, hGet, hMem, hMatch, hMin⟩ :=
      probePassAux_picked_spec cfg true cands steps 0 p hPass1
    rw [Nat.sub_zero] at hGet
    refine ⟨hElig, hGet, hMem, hMatch, ?_⟩
    intro idx s stage c hIdx hSElig hCMem hCStable hCMatch
    have hRes := hMin idx s stage c hIdx hSElig hCMem (Or.inr hCStable) hCMatch
    rw [Nat.zero_add] at hRes
    exact hRes

/-! ## Section 5: Parametric Precedence, Ambiguity vs. Shadowing, and `Receiver` Theorems -/

/-- **Theorem 3a (Step-0 Extension Beats Step-1 Inherent & Early Termination):**
    Suppose `step0 :: step1 :: rest` is probed, `stepEligible step0 = true`, and
    `pickAtStep cfg step0 0 true cands = .picked p` (for instance, an `.extension` trait
    method matching `step0` at `.autorefImm`). Then `probeMethod` ALWAYS returns `.picked p`
    at step 0 and NEVER inspects `step1` even if `step1` has an `.inherent` match! -/
theorem step0_pick_beats_step1_inherent
    (cfg : ProbeConfig) (step0 step1 : CandidateStep) (rest : List CandidateStep)
    (cands : List MethodCandidate) (p : MethodPick)
    (hElig0 : stepEligible step0 = true)
    (hPick0 : pickAtStep cfg step0 0 true cands = .picked p) :
    probeMethod cfg (step0 :: step1 :: rest) cands = .picked p ∧ p.stepIdx = 0 := by
  have hPass1 : probePassAux cfg true cands 0 (step0 :: step1 :: rest) = .picked p := by
    unfold probePassAux
    simp [hElig0, hPick0]
  have hSpec := pickAtStep_picked_spec cfg step0 0 true cands p hPick0
  refine ⟨?_, hSpec.1⟩
  unfold probeMethod
  simp [hPass1]

/-- **Theorem 3b (Per-Step Precedence Order — Step-0 `&self` Beats Step-0 `&mut self`):**
    If at an eligible step `step` (at index `idx`) there is no `.byValue` match,
    `pickMethod cfg step .autorefImm idx trackUnstable cands = .picked p` (whether `.inherent`
    or `.extension`), and no `arbitrary_self_types` anti-shadowing error triggers, then
    `pickAtStep` selects `p` (`.autorefImm`) strictly before probing `.autorefMut`,
    even if `.inherent` candidates exist at `.autorefMut`! -/
theorem step_autoref_imm_beats_autoref_mut
    (cfg : ProbeConfig) (step : CandidateStep) (idx : Nat) (trackUnstable : Bool)
    (cands : List MethodCandidate) (p : MethodPick)
    (hNoByVal : pickMethod cfg step .byValue idx trackUnstable cands = .noMatch)
    (hImm : pickMethod cfg step .autorefImm idx trackUnstable cands = .picked p)
    (hNoAntiShadow :
      cfg.arbitrarySelfTypes = false ∨ p.cand.bucket = .extension ∨
      findShadowedAutoref cfg p step .autorefMut trackUnstable cands = none) :
    pickAtStep cfg step idx trackUnstable cands = .picked p ∧ p.stage = .autorefImm := by
  have hSt := (pickMethod_picked_spec cfg step .autorefImm idx trackUnstable cands p hImm).2.2.1
  refine ⟨?_, hSt⟩
  unfold pickAtStep
  simp only [hNoByVal, hImm]
  rcases hNoAntiShadow with hArbF | hExt | hNone
  · simp [hArbF]
  · simp [hExt, eqBucket]
  · cases hA : (cfg.arbitrarySelfTypes && eqBucket p.cand.bucket .inherent) with
    | false => simp
    | true => simp [hNone]

/-- **Theorem 3c (Same-Slot Bucket Priority — Inherent / WhereClause Beats Extension):**
    If at `(step, stage)` the `.inherent` bucket (`InherentImplCandidate`, `ObjectCandidate`,
    or `WhereClauseCandidate`) produces `.picked p` (and is not rejected by anti-shadowing),
    `pickMethod` returns `p` directly without consulting `.extension` (`TraitCandidate`). -/
theorem inherent_bucket_beats_extension_same_slot
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (idx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate) (p : MethodPick)
    (hInh : considerCandidatesList cfg step stage .inherent idx trackUnstable cands = .picked p) :
    pickMethod cfg step stage idx trackUnstable cands = .picked p := by
  unfold pickMethod
  simp [hInh]

/-- **Theorem 3d (Inherent Ambiguity Short-Circuits Before Extension):**
    If at `(step, stage)` the `.inherent` bucket yields `.ambiguity ids`, `pickMethod`
    immediately yields `.ambiguity ids` (`E0034`) and never falls back to `.extension`. -/
theorem inherent_ambiguity_short_circuits_extension
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage)
    (idx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate) (ids : List Nat)
    (hAmbig : considerCandidatesList cfg step stage .inherent idx trackUnstable cands = .ambiguity ids) :
    pickMethod cfg step stage idx trackUnstable cands = .ambiguity ids := by
  unfold pickMethod
  simp [hAmbig]

/-- **Theorem 3e (Raw-Pointer Safety Filter & Non-Unsizing of `byValue` / `constPtr`):**
    1. Any step with `fromUnsafeDeref = true` is rejected by `stepEligible`, so
       raw pointers `*const T` / `*mut T` never autoderef to pointee methods;
    2. An `unsize = true` step (`[T; N] -> [T]`) never admits `.byValue` or `.constPtr`
       candidates (blocking `p: *mut [u8; 4]` from unsizing via `ToConstPtr`). -/
theorem raw_ptr_never_autoderefed_and_unsize_blocks_val_const_ptr
    (cfg : ProbeConfig) (s : CandidateStep) (b : CandidateBucket) (c : MethodCandidate) :
    (s.fromUnsafeDeref = true → stepEligible s = false) ∧
    (s.unsize = true →
      candidateMatches cfg s .byValue b c = false ∧
      candidateMatches cfg s .constPtr b c = false) := by
  refine ⟨?_, ?_⟩
  · intro hRaw
    unfold stepEligible
    simp [hRaw]
  · intro hU
    unfold candidateMatches stepAllowsStage
    simp [hU]

/-- **Theorem 4 (Same-Step Multi-Trait `E0034` Ambiguity vs. Cross-Step Shadowing Dichotomy):**
    1. If `probePassAux` reaches an eligible step `step0` and `pickAtStep` hits
       `.ambiguity ids` (`E0034`), `probeMethod` IMMEDIATELY aborts with `.ambiguity ids`
       even if `step1` in `rest` has a unique unambiguous match;
    2. If `c1` and `c2` belong to distinct traits (`c1.traitId ≠ c2.traitId`) matching
       the exact same `(step, stage, .extension)` slot (`inherent = .noMatch`), with
       `supertraitItemShadowing = false` and `cands = [c1, c2]` stable, then `pickMethod`
       returns `.ambiguity [c1.id, c2.id]` (`E0034`);
    3. Conversely, if `c1` matches strictly earlier `(idx1, stage1, b1)` (`ProbeKeyLt`) than
       `c2` at `(idx2, stage2, b2)`, `c1` wins silently and `probeMethod` NEVER emits `E0034`! -/
theorem ambiguity_propagates_across_steps
    (cfg : ProbeConfig) (step0 : CandidateStep) (rest : List CandidateStep)
    (cands : List MethodCandidate) (ids : List Nat)
    (hElig0 : stepEligible step0 = true)
    (hAmb0 : pickAtStep cfg step0 0 true cands = .ambiguity ids) :
    probeMethod cfg (step0 :: rest) cands = .ambiguity ids := by
  unfold probeMethod probePassAux
  simp [hElig0, hAmb0]

theorem same_step_two_distinct_traits_collide_e0034
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage) (idx : Nat)
    (c1 c2 : MethodCandidate)
    (hShadOff : cfg.supertraitItemShadowing = false)
    (hM1 : candidateMatches cfg step stage .extension c1 = true)
    (hM2 : candidateMatches cfg step stage .extension c2 = true)
    (hSt1 : c1.isUnstable = false) (hSt2 : c2.isUnstable = false)
    (hNotTrait1 : ∀ a, c1.pickKind = .traitPick a → False) :
    considerCandidatesList cfg step stage .extension idx true [c1, c2] =
      .ambiguity [c1.id, c2.id] := by
  unfold considerCandidatesList
  have hFilt : filterList (candidateMatches cfg step stage .extension) [c1, c2] = [c1, c2] := by
    simp [filterList, hM1, hM2]
  have hCol : tryCollapseSameTrait [c1, c2] = none := by
    unfold tryCollapseSameTrait
    cases hPK : c1.pickKind with
    | inherentImplPick | objectPick | whereClausePick _ => simp [hPK]
    | traitPick a => exact False.elim (hNotTrait1 a hPK)
  have hRet : filterList (fun c => !c.isUnstable) [c1, c2] = [c1, c2] := by
    simp [filterList, hSt1, hSt2]
  simp [hFilt, hCol, hRet, hShadOff, candIdsOf]

theorem same_step_two_trait_picks_distinct_traits_e0034
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage) (idx : Nat)
    (c1 c2 : MethodCandidate) (a1 a2 : Bool)
    (hShadOff : cfg.supertraitItemShadowing = false)
    (hM1 : candidateMatches cfg step stage .extension c1 = true)
    (hM2 : candidateMatches cfg step stage .extension c2 = true)
    (hPK1 : c1.pickKind = .traitPick a1) (hPK2 : c2.pickKind = .traitPick a2)
    (hSt1 : c1.isUnstable = false) (hSt2 : c2.isUnstable = false)
    (hDistinct : eqNat c2.traitId c1.traitId = false) :
    considerCandidatesList cfg step stage .extension idx true [c1, c2] =
      .ambiguity [c1.id, c2.id] := by
  unfold considerCandidatesList
  have hFilt : filterList (candidateMatches cfg step stage .extension) [c1, c2] = [c1, c2] := by
    simp [filterList, hM1, hM2]
  have hCol : tryCollapseSameTrait [c1, c2] = none := by
    unfold tryCollapseSameTrait allSameTrait
    simp [hPK1, hPK2, hDistinct]
  have hRet : filterList (fun c => !c.isUnstable) [c1, c2] = [c1, c2] := by
    simp [filterList, hSt1, hSt2]
  simp [hFilt, hCol, hRet, hShadOff, candIdsOf]

theorem same_trait_candidates_collapse_without_e0034
    (cfg : ProbeConfig) (step : CandidateStep) (stage : AdjustmentStage) (idx : Nat)
    (c1 c2 : MethodCandidate) (a1 a2 : Bool)
    (hM1 : candidateMatches cfg step stage .extension c1 = true)
    (hM2 : candidateMatches cfg step stage .extension c2 = true)
    (hPK1 : c1.pickKind = .traitPick a1) (hPK2 : c2.pickKind = .traitPick a2)
    (hSame : c2.traitId = c1.traitId) :
    considerCandidatesList cfg step stage .extension idx true [c1, c2] =
      .picked (mkMethodPick idx step stage c1) := by
  unfold considerCandidatesList
  have hFilt : filterList (candidateMatches cfg step stage .extension) [c1, c2] = [c1, c2] := by
    simp [filterList, hM1, hM2]
  have hCol : tryCollapseSameTrait [c1, c2] = some c1 := by
    unfold tryCollapseSameTrait allSameTrait
    simp [hPK1, hPK2, hSame, eqNat_refl, allSameTrait]
  simp [hFilt, hCol]

theorem cross_step_shadowing_no_e0034
    (cfg : ProbeConfig) (step0 step1 : CandidateStep) (rest : List CandidateStep)
    (cands : List MethodCandidate) (p : MethodPick)
    (hElig0 : stepEligible step0 = true)
    (hPick0 : pickAtStep cfg step0 0 true cands = .picked p) :
    (∀ ids, probeMethod cfg (step0 :: step1 :: rest) cands ≠ .ambiguity ids) ∧
    probeMethod cfg (step0 :: step1 :: rest) cands = .picked p := by
  have hEq := (step0_pick_beats_step1_inherent cfg step0 step1 rest cands p hElig0 hPick0).1
  refine ⟨?_, hEq⟩
  intro ids hAmb
  rw [hEq] at hAmb
  cases hAmb

/-- **Theorem 4b (Step-0 Extension `&self` Beats Step-0 Inherent `&mut self`):**
    Even when `.inherent` has a mutable-receiver candidate at `.autorefMut`, an
    `.extension` trait candidate at `.autorefImm` on the same step strictly wins
    because adjustment stage rank (`1 < 2`) dominates bucket rank (`probe.rs:1405-1461`). -/
theorem step0_extension_imm_beats_step0_inherent_mut
    (cfg : ProbeConfig) (step : CandidateStep) (cExtImm cInhMut : MethodCandidate)
    (hNoArb : cfg.arbitrarySelfTypes = false)
    (hNoByVal : pickMethod cfg step .byValue 0 true [cExtImm, cInhMut] = .noMatch)
    (hM1 : candidateMatches cfg step .autorefImm .extension cExtImm = true)
    (hM2 : candidateMatches cfg step .autorefImm .inherent cInhMut = false)
    (hNotInh1 : candidateMatches cfg step .autorefImm .inherent cExtImm = false)
    (hNotExt2 : candidateMatches cfg step .autorefImm .extension cInhMut = false)
    (hSt1 : cExtImm.isUnstable = false) (hBad1 : cExtImm.hasBadReturnType = false) :
    pickAtStep cfg step 0 true [cExtImm, cInhMut] =
      .picked (mkMethodPick 0 step .autorefImm cExtImm) := by
  have hPickImm :
      pickMethod cfg step .autorefImm 0 true [cExtImm, cInhMut] =
      .picked (mkMethodPick 0 step .autorefImm cExtImm) := by
    simp [pickMethod, considerCandidatesList, filterList, hNotInh1, hM2, hM1, hNotExt2, hSt1, hBad1]
  unfold pickAtStep
  simp [hNoByVal, hPickImm, hNoArb]

/-- **Theorem 4c (`supertrait_item_shadowing` Splits Subtrait/Supertrait Collision):**
    When two distinct traits `[sub, sup]` match the same slot and `sup.traitId ∈ sub.supertraits`,
    `considerCandidatesList` yields `.ambiguity [sub.id, sup.id]` (`E0034`) when
    `cfg.supertraitItemShadowing = false`, and collapses to `.picked ... sub` when
    `cfg.supertraitItemShadowing = true` (`probe.rs:1834-1850, 2439-2514`). -/
theorem subtrait_item_shadowing_collapses_when_enabled
    (step : CandidateStep) (stage : AdjustmentStage) (idx : Nat)
    (sub sup : MethodCandidate) (a1 a2 : Bool)
    (hMatchSub : candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := true, pinErgonomics := false } step stage .extension sub = true)
    (hMatchSup : candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := true, pinErgonomics := false } step stage .extension sup = true)
    (hPK1 : sub.pickKind = .traitPick a1) (hPK2 : sup.pickKind = .traitPick a2)
    (hSt1 : sub.isUnstable = false) (hSt2 : sup.isUnstable = false)
    (hDistinct : eqNat sup.traitId sub.traitId = false)
    (hNotEqId : eqNat sup.id sub.id = false)
    (hSuper : memNat sup.traitId sub.supertraits = true) :
    let cfgOff : ProbeConfig := { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false }
    let cfgOn : ProbeConfig := { arbitrarySelfTypes := false, supertraitItemShadowing := true, pinErgonomics := false }
    considerCandidatesList cfgOff step stage .extension idx true [sub, sup] = .ambiguity [sub.id, sup.id] ∧
    considerCandidatesList cfgOn step stage .extension idx true [sub, sup] = .picked (mkMethodPick idx step stage sub) := by
  have hCfgEq : ∀ c,
      candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false } step stage .extension c =
      candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := true, pinErgonomics := false } step stage .extension c := by
    intro c
    cases stage <;> simp [candidateMatches, stepAllowsStage]
  have hMatchSubOff : candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false } step stage .extension sub = true := by
    rw [hCfgEq]; exact hMatchSub
  have hMatchSupOff : candidateMatches { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false } step stage .extension sup = true := by
    rw [hCfgEq]; exact hMatchSup
  refine ⟨?_, ?_⟩
  · exact same_step_two_trait_picks_distinct_traits_e0034
      { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false }
      step stage idx sub sup a1 a2 rfl hMatchSubOff hMatchSupOff hPK1 hPK2 hSt1 hSt2 hDistinct
  · have hColSame : tryCollapseSameTrait [sub, sup] = none := by
      unfold tryCollapseSameTrait allSameTrait
      simp [hPK1, hPK2, hDistinct]
    have hDom : tryCollapseSubtrait [sub, sup] = some sub := by
      unfold tryCollapseSubtrait findDominantSubtraitAux
      simp [hPK1, dominatesAll, eqNat_refl, hNotEqId, hSuper]
    unfold considerCandidatesList
    simp [filterList, hMatchSub, hMatchSup, hColSame, hSt1, hSt2, hDom]

/-- **Theorem 4d (Const-Pointer Coercion, `&mut -> *mut` Isolation, & `Pin` Reborrow Gating):**
    1. On `*mut inner`, `.constPtr` matches `cConst` (`*const inner`) when earlier stages
       find no match, producing `adjustment = some .toConstPtr`;
    2. When `cImmRef` (`&*mut inner`) competes on the same step, `.autorefImm` wins (`rank 1 < 3`);
    3. On `Pin<&mut inner>`, `pinErgonomics = true` picks `.reborrowPin`, whereas
       `pinErgonomics = false` returns `.noMatch`. -/
theorem const_ptr_coercion_and_pin_reborrow_precedence (inner : Ty) :
    let mutPtrStep : CandidateStep :=
      { selfTy := .rawPtr .mutbl inner, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }
    let pinStep : CandidateStep :=
      { selfTy := .pin (.ref .mutbl inner), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }
    let cConst : MethodCandidate :=
      { id := 10, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := .rawPtr .imm inner, expectedStage := .constPtr, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cExtImm : MethodCandidate :=
      { id := 11, bucket := .extension, pickKind := .traitPick false, traitId := 99, supertraits := [],
        expectedTy := .ref .imm (.rawPtr .mutbl inner), expectedStage := .autorefImm, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cPinReborrow : MethodCandidate :=
      { id := 12, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := .pin (.ref .imm inner), expectedStage := .reborrowPin, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let baseCfg : ProbeConfig := { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false }
    let pinCfg : ProbeConfig := { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := true }
    probeMethod baseCfg [mutPtrStep] [cConst] = .picked (mkMethodPick 0 mutPtrStep .constPtr cConst) ∧
    probeMethod baseCfg [mutPtrStep] [cConst, cExtImm] = .picked (mkMethodPick 0 mutPtrStep .autorefImm cExtImm) ∧
    probeMethod pinCfg [pinStep] [cPinReborrow] = .picked (mkMethodPick 0 pinStep .reborrowPin cPinReborrow) ∧
    probeMethod baseCfg [pinStep] [cPinReborrow] = .noMatch := by
  have hEqConst : eqTy (.rawPtr .imm inner) (.rawPtr .imm inner) = true := eqTy_refl _
  have hEqExt : eqTy (.ref .imm (.rawPtr .mutbl inner)) (.ref .imm (.rawPtr .mutbl inner)) = true := eqTy_refl _
  have hEqPin : eqTy (.pin (.ref .imm inner)) (.pin (.ref .imm inner)) = true := eqTy_refl _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [probeMethod, probePassAux, stepEligible, pickAtStep, pickMethod, considerCandidatesList,
          filterList, candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, hEqConst]
  · simp [probeMethod, probePassAux, stepEligible, pickAtStep, pickMethod, considerCandidatesList,
          filterList, candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, hEqExt]
  · simp [probeMethod, probePassAux, stepEligible, pickAtStep, pickMethod, considerCandidatesList,
          filterList, candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, hEqPin]
  · simp [probeMethod, probePassAux, stepEligible, pickAtStep, pickMethod, considerCandidatesList,
          filterList, candidateMatches, stepAllowsStage, eqStage]

/-! ## Section 6: `Receiver`-Only Chain Soundness & Anti-Shadowing Asymmetry -/

/-- **Theorem 5 (`Receiver`-Only Chain Soundness & Zero-Deref Isolation):**
    Let `smartId : Nat` implement `Receiver<Target = targetTy>` WITHOUT `Deref`
    (`env.derefTarget smartId = none`, `env.receiverTarget smartId = some targetTy`),
    where `targetTy` is an ADT (`Ty.adt tgtId`) with no `Deref`/`Receiver` targets.
    1. `buildMethodAutoderefSteps env 4 true (.smartReceiver smartId (.adt tgtId))` emits
       exactly two steps:
       - Step 0: `.smartReceiver smartId (.adt tgtId)` with `reachableViaDeref = true`,
       - Step 1: `.adt tgtId` with `reachableViaDeref = false` (present for candidate assembly,
         skipped by `stepEligible` during method picking!);
    2. Calling a method `m(&targetTy)` on `SmartReceiver` yields `.noMatch` (`E0599`);
    3. Calling `m(self: &SmartReceiver<Target>)` defined on `Target` resolves cleanly at
       Step 0 (`autorefImm`)! -/
theorem receiver_only_chain_soundness (smartId tgtId : Nat)
    (hNoDerefS : ∀ (x : Nat), x = smartId → True)
    (env : DerefEnv)
    (hEnvDerefS : env.derefTarget smartId = none)
    (hEnvRecvS : env.receiverTarget smartId = some (.adt tgtId))
    (hEnvDerefT : env.derefTarget tgtId = none)
    (hEnvRecvT : env.receiverTarget tgtId = none) :
    let startTy : Ty := .smartReceiver smartId (.adt tgtId)
    let step0 : CandidateStep :=
      { selfTy := startTy, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }
    let step1 : CandidateStep :=
      { selfTy := .adt tgtId, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := false }
    let stepsRes := buildMethodAutoderefSteps env 4 true startTy
    stepsRes = ([step0, step1], false) ∧
    stepEligible step1 = false ∧
    (∀ (cTargetRef : MethodCandidate),
      cTargetRef.expectedTy = .ref .imm (.adt tgtId) →
      cTargetRef.expectedStage = .autorefImm →
      probeMethod { arbitrarySelfTypes := true, supertraitItemShadowing := false, pinErgonomics := false }
        stepsRes.1 [cTargetRef] = .noMatch) ∧
    (∀ (cSmartMethod : MethodCandidate),
      cSmartMethod.bucket = .inherent →
      cSmartMethod.expectedStage = .autorefImm →
      cSmartMethod.expectedTy = .ref .imm startTy →
      cSmartMethod.isUnstable = false →
      cSmartMethod.hasBadReturnType = false →
      probeMethod { arbitrarySelfTypes := true, supertraitItemShadowing := false, pinErgonomics := false }
        stepsRes.1 [cSmartMethod] =
        .picked (mkMethodPick 0 step0 .autorefImm cSmartMethod)) := by
  have _ := hNoDerefS smartId rfl
  have hStep0Deref : stepAutoderef env .viaDeref (.smartReceiver smartId (.adt tgtId)) = none := by
    simp [stepAutoderef, hEnvDerefS]
  have hStep0Recv : stepAutoderef env .viaReceiver (.smartReceiver smartId (.adt tgtId)) =
      some (.adt tgtId, .overloadedReceiver) := by
    simp [stepAutoderef, hEnvRecvS]
  have hStep1Recv : stepAutoderef env .viaReceiver (.adt tgtId) = none := by
    simp [stepAutoderef, hEnvRecvT, hEnvDerefT]
  have hDerefRun :
      runAutoderefAux env .viaDeref 4 (.smartReceiver smartId (.adt tgtId)) 0 false =
      ([{ ty := .smartReceiver smartId (.adt tgtId), depth := 0, fromUnsafeDeref := false }],
        .smartReceiver smartId (.adt tgtId), false, false) := by
    rw [show (4 : Nat) = Nat.succ 3 from rfl, runAutoderefAux_succ]
    simp [isTyErrOrInfer, isRawPtrTy, hStep0Deref]
  have hRecvRun :
      runAutoderefAux env .viaReceiver 4 (.smartReceiver smartId (.adt tgtId)) 0 false =
      ([{ ty := .smartReceiver smartId (.adt tgtId), depth := 0, fromUnsafeDeref := false },
        { ty := .adt tgtId, depth := 1, fromUnsafeDeref := false }],
        .adt tgtId, false, false) := by
    rw [show (4 : Nat) = Nat.succ 3 from rfl, runAutoderefAux_succ]
    simp only [isTyErrOrInfer, isRawPtrTy, hStep0Recv]
    rw [show (3 : Nat) = Nat.succ 2 from rfl, runAutoderefAux_succ]
    simp [isTyErrOrInfer, isRawPtrTy, hStep1Recv]
  have hSteps :
      buildMethodAutoderefSteps env 4 true (.smartReceiver smartId (.adt tgtId)) =
      ([{ selfTy := .smartReceiver smartId (.adt tgtId), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true },
        { selfTy := .adt tgtId, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := false }], false) := by
    unfold buildMethodAutoderefSteps
    rw [hDerefRun, hRecvRun]
    simp [zipReceiverAndDeref]
  refine ⟨hSteps, rfl, ?_, ?_⟩
  · intro cTargetRef hTy hStg
    rw [hSteps]
    let arbCfg : ProbeConfig := { arbitrarySelfTypes := true, supertraitItemShadowing := false, pinErgonomics := false }
    let step0 : CandidateStep :=
      { selfTy := .smartReceiver smartId (.adt tgtId), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }
    let step1 : CandidateStep :=
      { selfTy := .adt tgtId, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := false }
    change probeMethod arbCfg [step0, step1] [cTargetRef] = .noMatch
    have hNeqRef : eqTy (.ref .imm (.adt tgtId)) (.ref .imm (.smartReceiver smartId (.adt tgtId))) = false := by
      simp [eqTy, eqMut]
    have hNoMatchAll : ∀ (st : AdjustmentStage) (bk : CandidateBucket),
        candidateMatches arbCfg step0 st bk cTargetRef = false := by
      intro st bk
      cases st <;> cases bk <;> cases hBk : cTargetRef.bucket <;>
        simp [arbCfg, step0, candidateMatches, stepAllowsStage, stageSelfTy,
              eqBucket, eqStage, hStg, hTy, hNeqRef]
    have hAt0 : pickAtStep arbCfg step0 0 true [cTargetRef] = .noMatch := by
      simp [pickAtStep, pickMethod, considerCandidatesList, filterList, hNoMatchAll]
    have hAt0F : pickAtStep arbCfg step0 0 false [cTargetRef] = .noMatch := by
      simp [pickAtStep, pickMethod, considerCandidatesList, filterList, hNoMatchAll]
    have hElig0 : stepEligible step0 = true := rfl
    have hElig1 : stepEligible step1 = false := rfl
    simp [probeMethod, probePassAux, hElig0, hElig1, hAt0, hAt0F]
  · intro cSmartMethod hBk hStg hTy hSt hBad
    rw [hSteps]
    let arbCfg : ProbeConfig := { arbitrarySelfTypes := true, supertraitItemShadowing := false, pinErgonomics := false }
    let step0 : CandidateStep :=
      { selfTy := .smartReceiver smartId (.adt tgtId), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }
    let step1 : CandidateStep :=
      { selfTy := .adt tgtId, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := false }
    change probeMethod arbCfg [step0, step1] [cSmartMethod] =
      .picked (mkMethodPick 0 step0 .autorefImm cSmartMethod)
    have hEqImm : eqTy (.ref .imm (.smartReceiver smartId (.adt tgtId)))
        (.ref .imm (.smartReceiver smartId (.adt tgtId))) = true := eqTy_refl _
    have hByValInh : candidateMatches arbCfg step0 .byValue .inherent cSmartMethod = false := by
      simp [step0, candidateMatches, stepAllowsStage, eqStage, hStg]
    have hByValExt : candidateMatches arbCfg step0 .byValue .extension cSmartMethod = false := by
      simp [step0, candidateMatches, stepAllowsStage, eqBucket, hBk]
    have hImmInh : candidateMatches arbCfg step0 .autorefImm .inherent cSmartMethod = true := by
      simp [step0, candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, hBk, hStg, hTy, hEqImm]
    have hMutInh : candidateMatches arbCfg step0 .autorefMut .inherent cSmartMethod = false := by
      simp [candidateMatches, stepAllowsStage, eqStage, hStg]
    have hShadNone :
        findShadowedAutoref arbCfg (mkMethodPick 0 step0 .autorefImm cSmartMethod) step0 .autorefMut true [cSmartMethod] = none := by
      simp [findShadowedAutoref, mkMethodPick, synthesizeAdjustment, eqNat_refl, filterList, hMutInh]
    have hPickImm :
        pickMethod arbCfg step0 .autorefImm 0 true [cSmartMethod] =
        .picked (mkMethodPick 0 step0 .autorefImm cSmartMethod) := by
      simp [pickMethod, considerCandidatesList, filterList, hImmInh, hSt, hBad]
    have hNoByVal : pickMethod arbCfg step0 .byValue 0 true [cSmartMethod] = .noMatch := by
      simp [pickMethod, considerCandidatesList, filterList, hByValInh, hByValExt]
    have hAt0 : pickAtStep arbCfg step0 0 true [cSmartMethod] = .picked (mkMethodPick 0 step0 .autorefImm cSmartMethod) := by
      simp [pickAtStep, hNoByVal, hPickImm, arbCfg, eqBucket, hShadNone]
    have hElig0 : stepEligible step0 = true := rfl
    change probeMethod arbCfg [step0, step1] [cSmartMethod] =
      .picked (mkMethodPick 0 step0 .autorefImm cSmartMethod)
    simp [probeMethod, probePassAux, hElig0, hAt0]

/-- **Theorem 6 (Anti-Shadowing Soundness, Asymmetry, Double-Ref Bypass, & `*mut` Exemption):**
    Exact verification of `check_for_shadowed_autorefd_method` (`probe.rs:1383-1453, 1496-1581`):
    1. **Positive Protection (ByVal shadows Ref):** `SmartPtr::m(self)` (`receiverSteps = 0`)
       shadowing `Target::m(self: &SmartPtr<Self>)` (`receiverSteps = 1`) triggers `.ambiguity` (`E0034`);
    2. **Positive Protection (`&self` shadows `&mut self`):** `SmartPtr::m(&self)` (`receiverSteps = 0`)
       shadowing `Target::m(self: &mut SmartPtr<Self>)` (`receiverSteps = 1`) triggers `.ambiguity` (`E0034`);
    3. **Asymmetry:** `Target::m(self: SmartPtr<Self>)` (`receiverSteps = 1`) silently shadows
       `SmartPtr::m(&self)` (`receiverSteps = 0`) because `1 < 0` is false;
    4. **Double-Ref Niche Bypass (`probe.rs:1534-1562`):** On receiver `&SmartPtr<Target>`,
       `SmartPtr::m(&self)` increments `pick.autoderefs` from `0` to `1` while `step.autoderefs = 0`,
       so `!eqNat 0 1` short-circuits anti-shadowing and silently shadows `Target::m(self: &&SmartPtr<Self>)`;
    5. **Raw-Pointer `*mut` Exemption (`probe.rs:1431-1451`):** `RawWrap::m(self: *mut Self)`
       silently shadows `Target::m(self: *const RawWrap<Self>)` without `E0034`. -/
noncomputable def arbShadowCfg : ProbeConfig :=
  { arbitrarySelfTypes := true, supertraitItemShadowing := false, pinErgonomics := false }

noncomputable def mkSimpleStep (ty : Ty) : CandidateStep :=
  { selfTy := ty, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }

noncomputable def mkInhCand (id : Nat) (ty : Ty) (stg : AdjustmentStage) (recvSteps : Nat) : MethodCandidate :=
  { id := id, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
    expectedTy := ty, expectedStage := stg, receiverSteps := recvSteps, isUnstable := false, hasBadReturnType := false }

theorem probeMethod_single_picked (cfg : ProbeConfig) (s : CandidateStep)
    (cands : List MethodCandidate) (p : MethodPick)
    (hElig : stepEligible s = true)
    (hAt : pickAtStep cfg s 0 true cands = .picked p) :
    probeMethod cfg [s] cands = .picked p := by
  have hPass : probePassAux cfg true cands 0 [s] = .picked p := by
    unfold probePassAux
    simp [hElig, hAt]
  unfold probeMethod
  rw [hPass]

theorem probeMethod_single_ambiguity (cfg : ProbeConfig) (s : CandidateStep)
    (cands : List MethodCandidate) (ids : List Nat)
    (hElig : stepEligible s = true)
    (hAt : pickAtStep cfg s 0 true cands = .ambiguity ids) :
    probeMethod cfg [s] cands = .ambiguity ids := by
  have hPass : probePassAux cfg true cands 0 [s] = .ambiguity ids := by
    unfold probePassAux
    simp [hElig, hAt]
  unfold probeMethod
  rw [hPass]

theorem pickAtStep_byVal_arb_ambig (cfg : ProbeConfig) (s : CandidateStep)
    (idx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate)
    (p : MethodPick) (ids : List Nat)
    (hArb : cfg.arbitrarySelfTypes = true)
    (hBk : p.cand.bucket = .inherent)
    (hPick : pickMethod cfg s .byValue idx trackUnstable cands = .picked p)
    (hShad : findShadowedAutoref cfg p s .autorefImm trackUnstable cands = some ids) :
    pickAtStep cfg s idx trackUnstable cands = .ambiguity ids := by
  unfold pickAtStep
  rw [hPick]
  simp [hArb, hBk, eqBucket, hShad]

theorem pickAtStep_byVal_arb_picked (cfg : ProbeConfig) (s : CandidateStep)
    (idx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate) (p : MethodPick)
    (hArb : cfg.arbitrarySelfTypes = true)
    (hBk : p.cand.bucket = .inherent)
    (hPick : pickMethod cfg s .byValue idx trackUnstable cands = .picked p)
    (hShadImm : findShadowedAutoref cfg p s .autorefImm trackUnstable cands = none)
    (hShadMut : findShadowedAutoref cfg p s .autorefMut trackUnstable cands = none) :
    pickAtStep cfg s idx trackUnstable cands = .picked p := by
  unfold pickAtStep
  rw [hPick]
  simp [hArb, hBk, eqBucket, hShadImm, hShadMut]

theorem pickAtStep_imm_arb_ambig (cfg : ProbeConfig) (s : CandidateStep)
    (idx : Nat) (trackUnstable : Bool) (cands : List MethodCandidate)
    (p : MethodPick) (ids : List Nat)
    (hArb : cfg.arbitrarySelfTypes = true)
    (hBk : p.cand.bucket = .inherent)
    (hNoVal : pickMethod cfg s .byValue idx trackUnstable cands = .noMatch)
    (hPick : pickMethod cfg s .autorefImm idx trackUnstable cands = .picked p)
    (hShad : findShadowedAutoref cfg p s .autorefMut trackUnstable cands = some ids) :
    pickAtStep cfg s idx trackUnstable cands = .ambiguity ids := by
  unfold pickAtStep
  rw [hNoVal, hPick]
  simp [hArb, hBk, eqBucket, hShad]

theorem antiShadow_byVal_triggers_e0034 (smartId tgtId : Nat) :
    let ty : Ty := .smartReceiver smartId (.adt tgtId)
    probeMethod arbShadowCfg [mkSimpleStep ty]
      [mkInhCand 1 ty .byValue 0, mkInhCand 2 (.ref .imm ty) .autorefImm 1] =
      .ambiguity [1, 2] := by
  intro ty
  let step0 := mkSimpleStep ty
  let c1 := mkInhCand 1 ty .byValue 0
  let c2 := mkInhCand 2 (.ref .imm ty) .autorefImm 1
  have hM1 : candidateMatches arbShadowCfg step0 .byValue .inherent c1 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c1, mkSimpleStep, mkInhCand, eqTy_refl]
  have hM2 : candidateMatches arbShadowCfg step0 .byValue .inherent c2 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c2, mkSimpleStep, mkInhCand]
  have hFiltPick : filterList (candidateMatches arbShadowCfg step0 .byValue .inherent) [c1, c2] = [c1] := by
    simp only [filterList, hM1, hM2]; rfl
  have hPick : pickMethod arbShadowCfg step0 .byValue 0 true [c1, c2] =
      .picked (mkMethodPick 0 step0 .byValue c1) := by
    unfold pickMethod considerCandidatesList
    rw [hFiltPick]; rfl
  have hS1 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c1 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c1, mkInhCand]
  have hS2 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c2 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c2, mkSimpleStep, mkInhCand, eqTy_refl]
  have hShadFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefImm .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .byValue c1).cand c && (!true || !c.isUnstable)) [c1, c2] = [c2] := by
    simp only [filterList, hS1, hS2]; rfl
  have hShad : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c1) step0 .autorefImm true [c1, c2] = some [1, 2] := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .byValue c1).autoderefs = true := by
      simp [step0, ty, mkMethodPick, synthesizeAdjustment, mkSimpleStep, eqNat]
    rw [hEqA, hShadFilt]; rfl
  exact probeMethod_single_ambiguity arbShadowCfg step0 [c1, c2] [1, 2] rfl
    (pickAtStep_byVal_arb_ambig arbShadowCfg step0 0 true [c1, c2] (mkMethodPick 0 step0 .byValue c1) [1, 2] rfl rfl hPick hShad)

theorem antiShadow_ref_triggers_e0034 (smartId tgtId : Nat) :
    let ty : Ty := .smartReceiver smartId (.adt tgtId)
    probeMethod arbShadowCfg [mkSimpleStep ty]
      [mkInhCand 3 (.ref .imm ty) .autorefImm 0, mkInhCand 4 (.ref .mutbl ty) .autorefMut 1] =
      .ambiguity [3, 4] := by
  intro ty
  let step0 := mkSimpleStep ty
  let c3 := mkInhCand 3 (.ref .imm ty) .autorefImm 0
  let c4 := mkInhCand 4 (.ref .mutbl ty) .autorefMut 1
  have hV1 : candidateMatches arbShadowCfg step0 .byValue .inherent c3 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c3, mkSimpleStep, mkInhCand]
  have hV2 : candidateMatches arbShadowCfg step0 .byValue .inherent c4 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c4, mkSimpleStep, mkInhCand]
  have hE1 : candidateMatches arbShadowCfg step0 .byValue .extension c3 = false := by
    simp [candidateMatches, stepAllowsStage, eqBucket, step0, c3, mkSimpleStep, mkInhCand]
  have hE2 : candidateMatches arbShadowCfg step0 .byValue .extension c4 = false := by
    simp [candidateMatches, stepAllowsStage, eqBucket, step0, c4, mkSimpleStep, mkInhCand]
  have hFiltV : filterList (candidateMatches arbShadowCfg step0 .byValue .inherent) [c3, c4] = [] := by
    simp only [filterList, hV1, hV2, Bool.false_eq_true, ↓reduceIte]
  have hFiltE : filterList (candidateMatches arbShadowCfg step0 .byValue .extension) [c3, c4] = [] := by
    simp only [filterList, hE1, hE2, Bool.false_eq_true, ↓reduceIte]
  have hNoVal : pickMethod arbShadowCfg step0 .byValue 0 true [c3, c4] = .noMatch := by
    unfold pickMethod considerCandidatesList
    rw [hFiltV, hFiltE]
  have hM1 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c3 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c3, mkSimpleStep, mkInhCand, eqTy_refl]
  have hM2 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c4 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c4, mkInhCand]
  have hFiltImm : filterList (candidateMatches arbShadowCfg step0 .autorefImm .inherent) [c3, c4] = [c3] := by
    simp only [filterList, hM1, hM2]; rfl
  have hPick : pickMethod arbShadowCfg step0 .autorefImm 0 true [c3, c4] =
      .picked (mkMethodPick 0 step0 .autorefImm c3) := by
    unfold pickMethod considerCandidatesList
    rw [hFiltImm]; rfl
  have hS1 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c3 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c3, mkInhCand]
  have hS2 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c4 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c4, mkSimpleStep, mkInhCand, eqTy_refl]
  have hShadFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefMut .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .autorefImm c3).cand c && (!true || !c.isUnstable)) [c3, c4] = [c4] := by
    simp only [filterList, hS1, hS2]; rfl
  have hShad : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .autorefImm c3) step0 .autorefMut true [c3, c4] = some [3, 4] := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .autorefImm c3).autoderefs = true := rfl
    rw [hEqA, hShadFilt]; rfl
  exact probeMethod_single_ambiguity arbShadowCfg step0 [c3, c4] [3, 4] rfl
    (pickAtStep_imm_arb_ambig arbShadowCfg step0 0 true [c3, c4] (mkMethodPick 0 step0 .autorefImm c3) [3, 4] rfl rfl hNoVal hPick hShad)

theorem antiShadow_targetVal_shadows_smartRef (smartId tgtId : Nat) :
    let ty : Ty := .smartReceiver smartId (.adt tgtId)
    probeMethod arbShadowCfg [mkSimpleStep ty]
      [mkInhCand 5 ty .byValue 1, mkInhCand 3 (.ref .imm ty) .autorefImm 0] =
      .picked (mkMethodPick 0 (mkSimpleStep ty) .byValue (mkInhCand 5 ty .byValue 1)) := by
  intro ty
  let step0 := mkSimpleStep ty
  let c5 := mkInhCand 5 ty .byValue 1
  let c3 := mkInhCand 3 (.ref .imm ty) .autorefImm 0
  have hM1 : candidateMatches arbShadowCfg step0 .byValue .inherent c5 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c5, mkSimpleStep, mkInhCand, eqTy_refl]
  have hM2 : candidateMatches arbShadowCfg step0 .byValue .inherent c3 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c3, mkSimpleStep, mkInhCand]
  have hFilt : filterList (candidateMatches arbShadowCfg step0 .byValue .inherent) [c5, c3] = [c5] := by
    simp only [filterList, hM1, hM2]; rfl
  have hPick : pickMethod arbShadowCfg step0 .byValue 0 true [c5, c3] =
      .picked (mkMethodPick 0 step0 .byValue c5) := by
    unfold pickMethod considerCandidatesList
    rw [hFilt]; rfl
  have hI1 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c5 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c5, mkInhCand]
  have hMs2 : candidateMayShadow (mkMethodPick 0 step0 .byValue c5).cand c3 = false := rfl
  have hImmFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefImm .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .byValue c5).cand c && (!true || !c.isUnstable)) [c5, c3] = [] := by
    simp only [filterList, hI1, hMs2, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hShadImm : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c5) step0 .autorefImm true [c5, c3] = none := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .byValue c5).autoderefs = true := by
      simp [step0, ty, mkMethodPick, synthesizeAdjustment, mkSimpleStep, eqNat]
    rw [hEqA, hImmFilt]; rfl
  have hU1 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c5 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c5, mkInhCand]
  have hU2 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c3 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c3, mkInhCand]
  have hMutFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefMut .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .byValue c5).cand c && (!true || !c.isUnstable)) [c5, c3] = [] := by
    simp only [filterList, hU1, hU2]; rfl
  have hShadMut : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c5) step0 .autorefMut true [c5, c3] = none := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .byValue c5).autoderefs = true := by
      simp [step0, ty, mkMethodPick, synthesizeAdjustment, mkSimpleStep, eqNat]
    rw [hEqA, hMutFilt]; rfl
  exact probeMethod_single_picked arbShadowCfg step0 [c5, c3] (mkMethodPick 0 step0 .byValue c5) rfl
    (pickAtStep_byVal_arb_picked arbShadowCfg step0 0 true [c5, c3] (mkMethodPick 0 step0 .byValue c5) rfl rfl hPick hShadImm hShadMut)

theorem antiShadow_doubleRef_bypass (ty : Ty) :
    probeMethod arbShadowCfg [mkSimpleStep (.ref .imm ty)]
      [mkInhCand 6 (.ref .imm ty) .byValue 0, mkInhCand 7 (.ref .imm (.ref .imm ty)) .autorefImm 1] =
      .picked (mkMethodPick 0 (mkSimpleStep (.ref .imm ty)) .byValue (mkInhCand 6 (.ref .imm ty) .byValue 0)) := by
  let step0 := mkSimpleStep (.ref .imm ty)
  let c6 := mkInhCand 6 (.ref .imm ty) .byValue 0
  let c7 := mkInhCand 7 (.ref .imm (.ref .imm ty)) .autorefImm 1
  have hM1 : candidateMatches arbShadowCfg step0 .byValue .inherent c6 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c6, mkSimpleStep, mkInhCand, eqTy_refl]
  have hM2 : candidateMatches arbShadowCfg step0 .byValue .inherent c7 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c7, mkSimpleStep, mkInhCand]
  have hFilt : filterList (candidateMatches arbShadowCfg step0 .byValue .inherent) [c6, c7] = [c6] := by
    simp only [filterList, hM1, hM2]; rfl
  have hPick : pickMethod arbShadowCfg step0 .byValue 0 true [c6, c7] =
      .picked (mkMethodPick 0 step0 .byValue c6) := by
    unfold pickMethod considerCandidatesList
    rw [hFilt]; rfl
  have hShadImm : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c6) step0 .autorefImm true [c6, c7] = none := rfl
  have hShadMut : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c6) step0 .autorefMut true [c6, c7] = none := rfl
  exact probeMethod_single_picked arbShadowCfg step0 [c6, c7] (mkMethodPick 0 step0 .byValue c6) rfl
    (pickAtStep_byVal_arb_picked arbShadowCfg step0 0 true [c6, c7] (mkMethodPick 0 step0 .byValue c6) rfl rfl hPick hShadImm hShadMut)

theorem antiShadow_mutPtr_exempt (ty : Ty) :
    probeMethod arbShadowCfg [mkSimpleStep (.rawPtr .mutbl ty)]
      [mkInhCand 8 (.rawPtr .mutbl ty) .byValue 0, mkInhCand 9 (.rawPtr .imm ty) .constPtr 1] =
      .picked (mkMethodPick 0 (mkSimpleStep (.rawPtr .mutbl ty)) .byValue (mkInhCand 8 (.rawPtr .mutbl ty) .byValue 0)) := by
  let step0 := mkSimpleStep (.rawPtr .mutbl ty)
  let c8 := mkInhCand 8 (.rawPtr .mutbl ty) .byValue 0
  let c9 := mkInhCand 9 (.rawPtr .imm ty) .constPtr 1
  have hM1 : candidateMatches arbShadowCfg step0 .byValue .inherent c8 = true := by
    simp [candidateMatches, stepAllowsStage, stageSelfTy, eqBucket, eqStage, step0, c8, mkSimpleStep, mkInhCand, eqTy_refl]
  have hM2 : candidateMatches arbShadowCfg step0 .byValue .inherent c9 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, step0, c9, mkSimpleStep, mkInhCand]
  have hFilt : filterList (candidateMatches arbShadowCfg step0 .byValue .inherent) [c8, c9] = [c8] := by
    simp only [filterList, hM1, hM2]; rfl
  have hPick : pickMethod arbShadowCfg step0 .byValue 0 true [c8, c9] =
      .picked (mkMethodPick 0 step0 .byValue c8) := by
    unfold pickMethod considerCandidatesList
    rw [hFilt]; rfl
  have hI1 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c8 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c8, mkInhCand]
  have hI2 : candidateMatches arbShadowCfg step0 .autorefImm .inherent c9 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c9, mkInhCand]
  have hImmFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefImm .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .byValue c8).cand c && (!true || !c.isUnstable)) [c8, c9] = [] := by
    simp only [filterList, hI1, hI2]; rfl
  have hShadImm : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c8) step0 .autorefImm true [c8, c9] = none := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .byValue c8).autoderefs = true := rfl
    rw [hEqA, hImmFilt]; rfl
  have hU1 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c8 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c8, mkInhCand]
  have hU2 : candidateMatches arbShadowCfg step0 .autorefMut .inherent c9 = false := by
    simp [candidateMatches, stepAllowsStage, eqStage, eqBucket, c9, mkInhCand]
  have hMutFilt : filterList
      (fun c => candidateMatches arbShadowCfg step0 .autorefMut .inherent c &&
        candidateMayShadow (mkMethodPick 0 step0 .byValue c8).cand c && (!true || !c.isUnstable)) [c8, c9] = [] := by
    simp only [filterList, hU1, hU2]; rfl
  have hShadMut : findShadowedAutoref arbShadowCfg (mkMethodPick 0 step0 .byValue c8) step0 .autorefMut true [c8, c9] = none := by
    unfold findShadowedAutoref
    have hEqA : eqNat step0.autoderefs (mkMethodPick 0 step0 .byValue c8).autoderefs = true := rfl
    rw [hEqA, hMutFilt]; rfl
  exact probeMethod_single_picked arbShadowCfg step0 [c8, c9] (mkMethodPick 0 step0 .byValue c8) rfl
    (pickAtStep_byVal_arb_picked arbShadowCfg step0 0 true [c8, c9] (mkMethodPick 0 step0 .byValue c8) rfl rfl hPick hShadImm hShadMut)

theorem arbitrary_self_anti_shadowing_asymmetry_soundness (smartId tgtId : Nat) :
    let smartTy : Ty := .smartReceiver smartId (.adt tgtId)
    let stepSmart := mkSimpleStep smartTy
    let cSmartVal := mkInhCand 1 smartTy .byValue 0
    let cTargetRef := mkInhCand 2 (.ref .imm smartTy) .autorefImm 1
    let cSmartRef := mkInhCand 3 (.ref .imm smartTy) .autorefImm 0
    let cTargetMut := mkInhCand 4 (.ref .mutbl smartTy) .autorefMut 1
    let cTargetVal := mkInhCand 5 smartTy .byValue 1
    let refSmartTy : Ty := .ref .imm smartTy
    let stepRefSmart := mkSimpleStep refSmartTy
    let cSmartRefByVal := mkInhCand 6 refSmartTy .byValue 0
    let cTargetDoubleRef := mkInhCand 7 (.ref .imm refSmartTy) .autorefImm 1
    let mutPtrTy : Ty := .rawPtr .mutbl smartTy
    let stepMutPtr := mkSimpleStep mutPtrTy
    let cSmartMutPtr := mkInhCand 8 mutPtrTy .byValue 0
    let cTargetConstPtr := mkInhCand 9 (.rawPtr .imm smartTy) .constPtr 1
    probeMethod arbShadowCfg [stepSmart] [cSmartVal, cTargetRef] = .ambiguity [1, 2] ∧
    probeMethod arbShadowCfg [stepSmart] [cSmartRef, cTargetMut] = .ambiguity [3, 4] ∧
    probeMethod arbShadowCfg [stepSmart] [cTargetVal, cSmartRef] = .picked (mkMethodPick 0 stepSmart .byValue cTargetVal) ∧
    probeMethod arbShadowCfg [stepRefSmart] [cSmartRefByVal, cTargetDoubleRef] =
      .picked (mkMethodPick 0 stepRefSmart .byValue cSmartRefByVal) ∧
    probeMethod arbShadowCfg [stepMutPtr] [cSmartMutPtr, cTargetConstPtr] =
      .picked (mkMethodPick 0 stepMutPtr .byValue cSmartMutPtr) :=
  ⟨antiShadow_byVal_triggers_e0034 smartId tgtId,
   antiShadow_ref_triggers_e0034 smartId tgtId,
   antiShadow_targetVal_shadows_smartRef smartId tgtId,
   antiShadow_doubleRef_bypass _,
   antiShadow_mutPtr_exempt _⟩

/-! ## Section 7: `zerocopy` (`Ptr` / `Unalign` / `ReadOnly`) Verification & Anneal Boundary -/

/-- Exact `zerocopy` first-customer receiver dispatch invariants:
    1. `Ptr<'a, T, I>` (`ptrId`, no `Deref`):
       - `Ptr::as_ref(self)` wins at `(step 0, .byValue, .inherent)` over extension `InnerConflict::as_ref(&self)`,
       - `Ptr::reborrow(&mut self)` resolves at `(step 0, .autorefMut, .inherent)`,
       - referent `[u8]::len` fails closed `.noMatch` (`E0599`).
    2. `Unalign<[u8; N]>` (`unalignAlignedId`, `Deref<Target = [u8; N]>`):
       - `Unalign::get(&self)` wins at `(step 0, .autorefImm, .inherent)` over `[u8; N]::get`,
       - `.len()` walks `step 0 (Unalign) -> step 1 ([u8; 4] via Deref) -> step 2 ([u8] via unsize = true)`
         and resolves with `Autoref { mutbl: .imm, unsize: true }`!
       - `Unalign<[u32; N]>` (`unalignUnalignedId`, `!Unaligned` -> no `Deref`) stops at step 0, so `.len()` yields `.noMatch`.
    3. `ReadOnly<T>` (`readOnlyImmId`, `Deref<Target = T>` + `AsRef<T>`, zero `&self` inherent methods):
       - `ro.as_ref()` resolves cleanly to `<ReadOnly<T> as AsRef<T>>::as_ref(&self)` at `(step 0, .autorefImm, .extension)`,
       - `ReadOnly<Cell<u8>>` (`readOnlyInteriorMutId`, `!Immutable`) fails `.noMatch`. -/
theorem zerocopy_first_customer_dispatch_soundness :
    let cfg : ProbeConfig := { arbitrarySelfTypes := false, supertraitItemShadowing := false, pinErgonomics := false }
    let arrTy : Ty := .array 4 .scalar
    let sliceTy : Ty := .slice .scalar
    let ptrTy : Ty := .adt 10
    let unalignAlignedTy : Ty := .smartDeref 20 arrTy
    let unalignBadTy : Ty := .adt 21
    let readOnlyImmTy : Ty := .smartDeref 30 arrTy
    let readOnlyBadTy : Ty := .adt 31
    let env : DerefEnv :=
      { derefTarget := fun id =>
          if eqNat id 20 then some arrTy
          else if eqNat id 30 then some arrTy
          else none
        receiverTarget := fun _ => none }
    -- Steps constructed by `method_autoderef_steps`
    let ptrSteps := (buildMethodAutoderefSteps env 8 false ptrTy).1
    let unalignSteps := (buildMethodAutoderefSteps env 8 false unalignAlignedTy).1
    let unalignBadSteps := (buildMethodAutoderefSteps env 8 false unalignBadTy).1
    let readOnlySteps := (buildMethodAutoderefSteps env 8 false readOnlyImmTy).1
    let readOnlyBadSteps := (buildMethodAutoderefSteps env 8 false readOnlyBadTy).1
    -- Candidates
    let cPtrAsRef : MethodCandidate :=
      { id := 101, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := ptrTy, expectedStage := .byValue, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cTraitAsRefConflict : MethodCandidate :=
      { id := 102, bucket := .extension, pickKind := .traitPick false, traitId := 50, supertraits := [],
        expectedTy := .ref .imm ptrTy, expectedStage := .autorefImm, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cPtrReborrow : MethodCandidate :=
      { id := 103, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := .ref .mutbl ptrTy, expectedStage := .autorefMut, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cSliceLen : MethodCandidate :=
      { id := 201, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := .ref .imm sliceTy, expectedStage := .autorefImm, receiverSteps := 2, isUnstable := false, hasBadReturnType := false }
    let cUnalignGet : MethodCandidate :=
      { id := 202, bucket := .inherent, pickKind := .inherentImplPick, traitId := 0, supertraits := [],
        expectedTy := .ref .imm unalignAlignedTy, expectedStage := .autorefImm, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    let cArrGet : MethodCandidate :=
      { id := 203, bucket := .extension, pickKind := .traitPick false, traitId := 51, supertraits := [],
        expectedTy := .ref .imm arrTy, expectedStage := .autorefImm, receiverSteps := 1, isUnstable := false, hasBadReturnType := false }
    let cReadOnlyAsRef : MethodCandidate :=
      { id := 301, bucket := .extension, pickKind := .traitPick false, traitId := 52, supertraits := [],
        expectedTy := .ref .imm readOnlyImmTy, expectedStage := .autorefImm, receiverSteps := 0, isUnstable := false, hasBadReturnType := false }
    -- (A) `Ptr::as_ref(self)` beats extension `&self`, `Ptr::reborrow(&mut self)` resolves at step 0, `Ptr.len()` fails
    (∃ p, probeMethod cfg ptrSteps [cPtrAsRef, cTraitAsRefConflict] = .picked p ∧ p.cand.id = 101 ∧ p.stage = .byValue ∧ p.adjustment = none) ∧
    (∃ p, probeMethod cfg ptrSteps [cPtrReborrow] = .picked p ∧ p.cand.id = 103 ∧ p.adjustment = some (.autoref .mutbl false)) ∧
    (probeMethod cfg ptrSteps [cSliceLen] = .noMatch) ∧
    -- (B) `Unalign`: step-0 `get(&self)` shadows referent; `.len()` walks Deref + Unsize (`unsize = true`) at stepIdx = 2; `!Unaligned` -> `.noMatch`
    (∃ p, probeMethod cfg unalignSteps [cUnalignGet, cArrGet] = .picked p ∧ p.cand.id = 202 ∧ p.stepIdx = 0) ∧
    (∃ p, probeMethod cfg unalignSteps [cSliceLen] = .picked p ∧ p.cand.id = 201 ∧ p.stepIdx = 2 ∧ p.autoderefs = 1 ∧ p.adjustment = some (.autoref .imm true)) ∧
    (probeMethod cfg unalignBadSteps [cSliceLen] = .noMatch) ∧
    -- (C) `ReadOnly`: `AsRef::as_ref` resolves at step 0 `.extension`, `.len()` unsizes at stepIdx = 2, `!Immutable` -> `.noMatch`
    (∃ p, probeMethod cfg readOnlySteps [cReadOnlyAsRef] = .picked p ∧ p.cand.id = 301 ∧ p.cand.pickKind = .traitPick false ∧ p.stepIdx = 0) ∧
    (∃ p, probeMethod cfg readOnlySteps [cSliceLen] = .picked p ∧ p.cand.id = 201 ∧ p.stepIdx = 2 ∧ p.adjustment = some (.autoref .imm true)) ∧
    (probeMethod cfg readOnlyBadSteps [cSliceLen] = .noMatch) := by
  dsimp only
  have hPtrSteps :
      (buildMethodAutoderefSteps
        { derefTarget := fun id => if eqNat id 20 then some (.array 4 .scalar) else if eqNat id 30 then some (.array 4 .scalar) else none,
          receiverTarget := fun _ => none }
        8 false (.adt 10)).1 =
      [{ selfTy := .adt 10, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }] := by
    rfl
  have hUnalignSteps :
      (buildMethodAutoderefSteps
        { derefTarget := fun id => if eqNat id 20 then some (.array 4 .scalar) else if eqNat id 30 then some (.array 4 .scalar) else none,
          receiverTarget := fun _ => none }
        8 false (.smartDeref 20 (.array 4 .scalar))).1 =
      [{ selfTy := .smartDeref 20 (.array 4 .scalar), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true },
       { selfTy := .array 4 .scalar, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true },
       { selfTy := .slice .scalar, autoderefs := 1, fromUnsafeDeref := false, unsize := true, reachableViaDeref := true }] := by
    rfl
  have hUnalignBadSteps :
      (buildMethodAutoderefSteps
        { derefTarget := fun id => if eqNat id 20 then some (.array 4 .scalar) else if eqNat id 30 then some (.array 4 .scalar) else none,
          receiverTarget := fun _ => none }
        8 false (.adt 21)).1 =
      [{ selfTy := .adt 21, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }] := by
    rfl
  have hReadOnlySteps :
      (buildMethodAutoderefSteps
        { derefTarget := fun id => if eqNat id 20 then some (.array 4 .scalar) else if eqNat id 30 then some (.array 4 .scalar) else none,
          receiverTarget := fun _ => none }
        8 false (.smartDeref 30 (.array 4 .scalar))).1 =
      [{ selfTy := .smartDeref 30 (.array 4 .scalar), autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true },
       { selfTy := .array 4 .scalar, autoderefs := 1, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true },
       { selfTy := .slice .scalar, autoderefs := 1, fromUnsafeDeref := false, unsize := true, reachableViaDeref := true }] := by
    rfl
  have hReadOnlyBadSteps :
      (buildMethodAutoderefSteps
        { derefTarget := fun id => if eqNat id 20 then some (.array 4 .scalar) else if eqNat id 30 then some (.array 4 .scalar) else none,
          receiverTarget := fun _ => none }
        8 false (.adt 31)).1 =
      [{ selfTy := .adt 31, autoderefs := 0, fromUnsafeDeref := false, unsize := false, reachableViaDeref := true }] := by
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hPtrSteps]
    refine ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [hPtrSteps]
    refine ⟨_, rfl, rfl, rfl⟩
  · rw [hPtrSteps]; rfl
  · rw [hUnalignSteps]
    refine ⟨_, rfl, rfl, rfl⟩
  · rw [hUnalignSteps]
    refine ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hUnalignBadSteps]; rfl
  · rw [hReadOnlySteps]
    refine ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [hReadOnlySteps]
    refine ⟨_, rfl, rfl, rfl, rfl⟩
  · rw [hReadOnlyBadSteps]; rfl

/-! ## Section 8: Fail-Closed Projection onto Anneal's Trusted MIR Semantics (`joshlf/anneal`) -/

/-- Exact MIR support status in `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean` and
    `Trusted/MirSemantics.lean` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`). -/
inductive AnnealMirSupport where
  | scalarDirectCallOk
  | unsupported

/-- Lowering a resolved `MethodPick` (plus its autoderef chain kind and receiver type)
    into Anneal's fail-closed MIR capture & interpreter boundary:
    - `ObjectPick` lowers via `TerminatorKind::Call` with non-`FnDef` indirect callee -> `.unsupported` (`MirAst.lean:780-784`);
    - `Autoref { unsize: true }` (`[T; N] -> [T]`) and `ToConstPtr` (`*mut T -> *const T`) lower via
      `Rvalue::Cast(PointerCoercion(..))` -> `.unsupported` (`MirAst.lean:613`);
    - Any `autoderefs > 0` or `Reborrow` / `Rvalue::Use(_, WithRetag::Yes)` on reference/box types
      lowers to `ProjectionElem::Deref` / `Rvalue::unsupported` -> `.unsupported` (`MirAst.lean:472, 596-617`);
    - Even a 0-autoderef scalar value call requires `callerMem = ∅` and scalar/bool/unit/fieldless-enum
      value types (`MirSemantics.lean:803, 1686-1693`, and `.call` itself halts with `.fault .unsupported`
      in the single-body evaluator unless inlined/discharged by interprocedural spec). -/
noncomputable def classifyPickInAnneal (p : MethodPick) : AnnealMirSupport :=
  match p.cand.pickKind with
  | .objectPick => .unsupported
  | _ =>
    if !eqNat p.autoderefs 0 then .unsupported
    else
      match p.adjustment with
      | some (.autoref _ true) => .unsupported
      | some .toConstPtr => .unsupported
      | some (.reborrowPin _) => .unsupported
      | some (.autoref _ false) => .unsupported
      | none =>
        match p.step.selfTy with
        | .unit | .scalar => .scalarDirectCallOk
        | _ => .unsupported

/-- **Anneal Fail-Closed MIR Boundary Theorem:**
    Every method dispatch involving `ObjectPick`, `autoderefs > 0` (`Deref`/`DerefMut`/reborrow),
    array-to-slice unsizing (`unsize = true`), raw-pointer const coercion (`toConstPtr`),
    `Pin` reborrowing, or `&self`/`&mut self` autoref borrowing classifies as `.unsupported`
    at Anneal's current MIR boundary (`MirAst.lean` / `MirSemantics.lean`). -/
theorem anneal_mir_boundary_soundness (p : MethodPick) :
    (p.cand.pickKind = .objectPick → classifyPickInAnneal p = .unsupported) ∧
    (0 < p.autoderefs → classifyPickInAnneal p = .unsupported) ∧
    (∀ m, p.adjustment = some (.autoref m true) → classifyPickInAnneal p = .unsupported) ∧
    (p.adjustment = some .toConstPtr → classifyPickInAnneal p = .unsupported) ∧
    (∀ m, p.adjustment = some (.reborrowPin m) → classifyPickInAnneal p = .unsupported) ∧
    (∀ m, p.adjustment = some (.autoref m false) → classifyPickInAnneal p = .unsupported) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hObj
    unfold classifyPickInAnneal
    simp [hObj]
  · intro hPos
    unfold classifyPickInAnneal
    have hNeq : eqNat p.autoderefs 0 = false := by
      cases hD : p.autoderefs with
      | zero => rw [hD] at hPos; cases hPos
      | succ _ => rfl
    cases hPK : p.cand.pickKind <;> simp [hNeq]
  · intro m hAdj
    unfold classifyPickInAnneal
    cases hPK : p.cand.pickKind <;> cases hD : p.autoderefs <;> simp [eqNat, hAdj]
  · intro hAdj
    unfold classifyPickInAnneal
    cases hPK : p.cand.pickKind <;> cases hD : p.autoderefs <;> simp [eqNat, hAdj]
  · intro m hAdj
    unfold classifyPickInAnneal
    cases hPK : p.cand.pickKind <;> cases hD : p.autoderefs <;> simp [eqNat, hAdj]
  · intro m hAdj
    unfold classifyPickInAnneal
    cases hPK : p.cand.pickKind <;> cases hD : p.autoderefs <;> simp [eqNat, hAdj]

/-! ## Section 9: Master Composition Theorem -/

/-- Master soundness composition across all four pillars of the study:
    1. Outcome trichotomy (`Picked | Ambiguity | NoMatch`) and lexicographic optimality;
    2. Bounded `Autoderef`/`Receiver` chain construction with at-most-once `unsize` termination;
    3. `Receiver`-only isolation (`E0599` on non-`Deref` targets) and asymmetric anti-shadowing;
    4. Exact `zerocopy` (`Ptr`/`Unalign`/`ReadOnly`) dispatch invariants and Anneal fail-closed boundary. -/
theorem hir_method_resolution_autoderef_master_soundness
    (cfg : ProbeConfig) (env : DerefEnv) (limit : Nat) (startTy : Ty)
    (steps : List CandidateStep) (cands : List MethodCandidate) (p : MethodPick)
    (hGood : ∀ c ∈ cands, c.hasBadReturnType = false)
    (hPick : probeMethod cfg steps cands = .picked p) :
    ((∃ q, probeMethod cfg steps cands = .picked q) ∨
     (∃ ids, probeMethod cfg steps cands = .ambiguity ids) ∨
     probeMethod cfg steps cands = .noMatch) ∧
    (stepEligible p.step = true ∧
     (∀ idx s stage c,
       listGetOpt steps idx = some s →
       stepEligible s = true →
       c ∈ cands →
       c.isUnstable = false →
       candidateMatches cfg s stage c.bucket c = true →
       ProbeKeyLe p.stepIdx p.stage p.cand.bucket idx stage c.bucket)) ∧
    countUnsizeSteps (buildMethodAutoderefSteps env limit cfg.arbitrarySelfTypes startTy).1 ≤ 1 ∧
    (0 < p.autoderefs → classifyPickInAnneal p = .unsupported) := by
  have hTri := probeMethod_trichotomy cfg steps cands hGood
  have hOpt := probeMethod_lexicographic_optimality cfg steps cands p hPick
  have hTerm := unsize_step_termination_and_uniqueness env limit cfg.arbitrarySelfTypes startTy
  have hAnneal := (anneal_mir_boundary_soundness p).2.1
  exact ⟨hTri, ⟨hOpt.1, hOpt.2.2.2.2⟩, hTerm.2.1, hAnneal⟩

end HirMethodResolutionAutoderefSoundness
