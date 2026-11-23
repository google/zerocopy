/-
  TargetFeatureInliningBoundaryAndSimdAbiSoundness.lean

  Kernel-checked Lean v4.34.1 formalization of:
  1. Rust `#[target_feature]` 1.1 (`target_feature_11`) feature lattice, safe-call and
     safe function-pointer coercion typing (`E0133`/`E0308`), closure inheritance, and
     trait/main attribute constraints;
  2. MIR `Inline` strict ordered-sequence equality (`callee_feature_names.ne(this_feature_names)`)
     vs. LLVM `areInlineCompatible` monotone subset inlining (`callee <= caller`) and
     `2026-09` vs. `2026-11` `#[inline(always)]` + `#[target_feature]` gating;
  3. Baseline-caller illegal inlining `SIGILL` counterexamples vs. `SIGILL`-freedom under
     `SafeTf11Typed` + superset inlining (`callee <= caller`);
  4. SIMD vector register ABI (`AbiErrorDisabledVectorType`, `extern "C"` `PassMode::Cast` vs.
     `extern "Rust"` `PassMode::Indirect` / `<= 128`-bit `Direct`).

  Purity constraints enforced throughout:
  - Pure `prelude` + `Init.Core` + `Init.NotationExtra` + `Init.Data.List.Basic` + `Init.Data.Nat.Basic`
  - Every value/function `def` carries `noncomputable def` (zero `._unsafe_rec`)
  - Zero `noncomputable section`, zero `deriving`, zero `partial def`
  - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`
-/

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace TargetFeatureInliningAndSimdAbi

/-! ## Section 1: CPU Target Feature Lattice and Implication Closure -/

/-- Representative x86-64 ISA target features audited in `compiler/rustc_target/src/target_features.rs`
    (`X86_FEATURES`). -/
inductive Feature where
  | sse
  | sse2
  | sse3
  | ssse3
  | sse41
  | sse42
  | avx
  | avx2
  | bmi1
  | fma
  | f16c
  | avx512f
  | aes
  | pclmulqdq

/-- Ordered feature list modeling `codegen_fn_attrs.target_features` and CPU capability bitsets. -/
abbrev FeatureSet := List Feature

/-- Structural equality on `Feature` written explicitly without `deriving`. -/
noncomputable def Feature.beq (a b : Feature) : Bool :=
  match a, b with
  | .sse, .sse => true
  | .sse2, .sse2 => true
  | .sse3, .sse3 => true
  | .ssse3, .ssse3 => true
  | .sse41, .sse41 => true
  | .sse42, .sse42 => true
  | .avx, .avx => true
  | .avx2, .avx2 => true
  | .bmi1, .bmi1 => true
  | .fma, .fma => true
  | .f16c, .f16c => true
  | .avx512f, .avx512f => true
  | .aes, .aes => true
  | .pclmulqdq, .pclmulqdq => true
  | _, _ => false

theorem Feature.beq_refl (a : Feature) : Feature.beq a a = true := by
  cases a <;> rfl

theorem Feature.eq_of_beq_true {a b : Feature} (h : Feature.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem Feature.beq_iff_eq (a b : Feature) : Feature.beq a b = true ↔ a = b := by
  constructor
  · exact Feature.eq_of_beq_true
  · intro h
    subst h
    exact Feature.beq_refl a

theorem Feature.beq_symm (a b : Feature) : Feature.beq a b = Feature.beq b a := by
  cases a <;> cases b <;> rfl

/-- Boolean membership test in a `FeatureSet`. -/
noncomputable def memFeatB (f : Feature) (fs : FeatureSet) : Bool :=
  match fs with
  | [] => false
  | x :: xs =>
    match Feature.beq f x with
    | true => true
    | false => memFeatB f xs

/-- Propositional membership in a `FeatureSet`. -/
noncomputable def MemFeat (f : Feature) (fs : FeatureSet) : Prop :=
  memFeatB f fs = true

/-- Boolean subset check (`sub ⊆ sup`). -/
noncomputable def subsetFeatsB (sub sup : FeatureSet) : Bool :=
  match sub with
  | [] => true
  | x :: xs =>
    match memFeatB x sup with
    | true => subsetFeatsB xs sup
    | false => false

/-- Propositional subset relation (`sub ⊆ sup`). -/
noncomputable def SubsetFeats (sub sup : FeatureSet) : Prop :=
  ∀ f : Feature, MemFeat f sub → MemFeat f sup

/-- Exact ordered sequence equality modeling `callee_feature_names.ne(this_feature_names)`
    in `compiler/rustc_mir_transform/src/inline.rs:840-842`. -/
noncomputable def seqEqFeatsB (a b : FeatureSet) : Bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys =>
    match Feature.beq x y with
    | true => seqEqFeatsB xs ys
    | false => false
  | _, _ => false

/-- Propositional sequence equality on `FeatureSet`. -/
noncomputable def SeqEqFeats (a b : FeatureSet) : Prop :=
  seqEqFeatsB a b = true

/-- Set equivalence on `FeatureSet` (`a ⊆ b ∧ b ⊆ a`). -/
noncomputable def SetEqFeats (a b : FeatureSet) : Prop :=
  SubsetFeats a b ∧ SubsetFeats b a

/-- Boolean set equivalence on `FeatureSet`. -/
noncomputable def setEqFeatsB (a b : FeatureSet) : Bool :=
  match subsetFeatsB a b with
  | true => subsetFeatsB b a
  | false => false

theorem memFeatB_cons_eq (x : Feature) (xs : FeatureSet) :
    memFeatB x (x :: xs) = true := by
  dsimp only [memFeatB]
  rw [Feature.beq_refl x]

theorem memFeatB_cons_true {f x : Feature} {xs : FeatureSet}
    (h : memFeatB f xs = true) : memFeatB f (x :: xs) = true := by
  dsimp only [memFeatB]
  cases Feature.beq f x
  · exact h
  · rfl

theorem memFeatB_cons_cases {f x : Feature} {xs : FeatureSet}
    (h : memFeatB f (x :: xs) = true) : f = x ∨ memFeatB f xs = true := by
  dsimp only [memFeatB] at h
  cases heq : Feature.beq f x
  · rw [heq] at h
    exact Or.inr h
  · exact Or.inl (Feature.eq_of_beq_true heq)

theorem memFeatB_append_left {f : Feature} (a b : FeatureSet)
    (h : memFeatB f a = true) : memFeatB f (a ++ b) = true := by
  induction a with
  | nil => cases h
  | cons x xs ih =>
    change memFeatB f (x :: (xs ++ b)) = true
    dsimp only [memFeatB]
    cases heq : Feature.beq f x
    · exact ih (by
        dsimp only [memFeatB] at h
        rw [heq] at h
        exact h)
    · rfl

theorem memFeatB_append_right {f : Feature} (a b : FeatureSet)
    (h : memFeatB f b = true) : memFeatB f (a ++ b) = true := by
  induction a with
  | nil => exact h
  | cons x xs ih =>
    change memFeatB f (x :: (xs ++ b)) = true
    dsimp only [memFeatB]
    cases Feature.beq f x
    · exact ih
    · rfl

theorem memFeatB_append_cases {f : Feature} (a b : FeatureSet)
    (h : memFeatB f (a ++ b) = true) : memFeatB f a = true ∨ memFeatB f b = true := by
  induction a with
  | nil => exact Or.inr h
  | cons x xs ih =>
    change memFeatB f (x :: (xs ++ b)) = true at h
    dsimp only [memFeatB] at h
    cases heq : Feature.beq f x
    · rw [heq] at h
      cases ih h with
      | inl ha =>
        dsimp only [memFeatB]
        rw [heq]
        exact Or.inl ha
      | inr hb => exact Or.inr hb
    · dsimp only [memFeatB]
      rw [heq]
      exact Or.inl rfl

theorem subsetFeatsB_sound (sub sup : FeatureSet) :
    subsetFeatsB sub sup = true → SubsetFeats sub sup := by
  intro h f hf
  induction sub with
  | nil => cases hf
  | cons x xs ih =>
    dsimp only [subsetFeatsB] at h
    cases hx : memFeatB x sup
    · rw [hx] at h
      cases h
    · rw [hx] at h
      cases memFeatB_cons_cases hf with
      | inl hfx =>
        subst hfx
        exact hx
      | inr hfxs =>
        exact ih h hfxs

theorem subsetFeatsB_complete (sub sup : FeatureSet) :
    SubsetFeats sub sup → subsetFeatsB sub sup = true := by
  intro h
  induction sub with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [subsetFeatsB]
    have hx : memFeatB x sup = true := h x (memFeatB_cons_eq x xs)
    rw [hx]
    apply ih
    intro f hf
    exact h f (memFeatB_cons_true hf)

theorem subsetFeats_iff_bool (sub sup : FeatureSet) :
    SubsetFeats sub sup ↔ subsetFeatsB sub sup = true :=
  ⟨subsetFeatsB_complete sub sup, subsetFeatsB_sound sub sup⟩

theorem SubsetFeats.refl (a : FeatureSet) : SubsetFeats a a := by
  intro f hf
  exact hf

theorem SubsetFeats.trans {a b c : FeatureSet}
    (hab : SubsetFeats a b) (hbc : SubsetFeats b c) : SubsetFeats a c := by
  intro f hf
  exact hbc f (hab f hf)

theorem SubsetFeats.append_left (a b : FeatureSet) : SubsetFeats a (a ++ b) := by
  intro f hf
  exact memFeatB_append_left a b hf

theorem SubsetFeats.append_right (a b : FeatureSet) : SubsetFeats b (a ++ b) := by
  intro f hf
  exact memFeatB_append_right a b hf

theorem SubsetFeats.append_intro {a b c : FeatureSet}
    (hac : SubsetFeats a c) (hbc : SubsetFeats b c) : SubsetFeats (a ++ b) c := by
  intro f hf
  cases memFeatB_append_cases a b hf with
  | inl ha => exact hac f ha
  | inr hb => exact hbc f hb

theorem SubsetFeats.append_mono_left {a b c : FeatureSet}
    (hab : SubsetFeats a b) : SubsetFeats (a ++ c) (b ++ c) :=
  SubsetFeats.append_intro
    (SubsetFeats.trans hab (SubsetFeats.append_left b c))
    (SubsetFeats.append_right b c)

theorem eq_of_seqEqFeatsB_true {a b : FeatureSet} (h : seqEqFeatsB a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases b with
    | nil => cases h
    | cons y ys =>
      dsimp only [seqEqFeatsB] at h
      cases hxy : Feature.beq x y
      · rw [hxy] at h
        cases h
      · rw [hxy] at h
        have hxeq := Feature.eq_of_beq_true hxy
        have hxseq := ih h
        subst hxeq
        subst hxseq
        rfl

theorem seqEqFeatsB_refl (a : FeatureSet) : seqEqFeatsB a a = true := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [seqEqFeatsB]
    rw [Feature.beq_refl x]
    exact ih

theorem seqEqFeats_implies_setEq {a b : FeatureSet} (h : SeqEqFeats a b) : SetEqFeats a b := by
  have heq := eq_of_seqEqFeatsB_true h
  subst heq
  exact ⟨SubsetFeats.refl a, SubsetFeats.refl a⟩

theorem seqEqFeats_implies_subset {a b : FeatureSet} (h : SeqEqFeats a b) : SubsetFeats a b :=
  (seqEqFeats_implies_setEq h).1

/-- Direct implication edges from `X86_FEATURES` (`compiler/rustc_target/src/target_features.rs:447-583`). -/
noncomputable def directImplied (f : Feature) : FeatureSet :=
  match f with
  | .sse => []
  | .sse2 => [.sse]
  | .sse3 => [.sse2]
  | .ssse3 => [.sse3]
  | .sse41 => [.ssse3]
  | .sse42 => [.sse41]
  | .avx => [.sse42]
  | .avx2 => [.avx]
  | .bmi1 => []
  | .fma => [.avx]
  | .f16c => [.avx]
  | .avx512f => [.avx2, .fma, .f16c]
  | .aes => [.sse2]
  | .pclmulqdq => [.sse2]

/-- Insert `f` into `fs` only if not already present (keeping closure sets bounded to `<= 14`). -/
noncomputable def insertUnique (f : Feature) (fs : FeatureSet) : FeatureSet :=
  match memFeatB f fs with
  | true => fs
  | false => f :: fs

theorem memFeatB_insertUnique_self (f : Feature) (fs : FeatureSet) :
    memFeatB f (insertUnique f fs) = true := by
  dsimp only [insertUnique]
  cases hm : memFeatB f fs
  · exact memFeatB_cons_eq f fs
  · exact hm

theorem memFeatB_insertUnique_old {g : Feature} (f : Feature) {fs : FeatureSet}
    (hg : memFeatB g fs = true) : memFeatB g (insertUnique f fs) = true := by
  dsimp only [insertUnique]
  cases memFeatB f fs
  · exact memFeatB_cons_true hg
  · exact hg

theorem memFeatB_insertUnique_cases {g f : Feature} {fs : FeatureSet}
    (hg : memFeatB g (insertUnique f fs) = true) : g = f ∨ memFeatB g fs = true := by
  dsimp only [insertUnique] at hg
  cases hm : memFeatB f fs <;> rw [hm] at hg
  · exact memFeatB_cons_cases hg
  · exact Or.inr hg

/-- Deduplicating union of two feature sets. -/
noncomputable def unionFeats (a b : FeatureSet) : FeatureSet :=
  match a with
  | [] => b
  | x :: xs => insertUnique x (unionFeats xs b)

theorem memFeatB_unionFeats_left {f : Feature} (a b : FeatureSet)
    (h : memFeatB f a = true) : memFeatB f (unionFeats a b) = true := by
  induction a with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [unionFeats]
    cases memFeatB_cons_cases h with
    | inl hfx =>
      subst hfx
      exact memFeatB_insertUnique_self f (unionFeats xs b)
    | inr hfxs =>
      exact memFeatB_insertUnique_old x (ih hfxs)

theorem memFeatB_unionFeats_right {f : Feature} (a b : FeatureSet)
    (h : memFeatB f b = true) : memFeatB f (unionFeats a b) = true := by
  induction a with
  | nil => exact h
  | cons x xs ih =>
    dsimp only [unionFeats]
    exact memFeatB_insertUnique_old x ih

theorem memFeatB_unionFeats_cases {f : Feature} (a b : FeatureSet)
    (h : memFeatB f (unionFeats a b) = true) :
    memFeatB f a = true ∨ memFeatB f b = true := by
  induction a with
  | nil => exact Or.inr h
  | cons x xs ih =>
    dsimp only [unionFeats] at h
    cases memFeatB_insertUnique_cases h with
    | inl hfx =>
      subst hfx
      exact Or.inl (memFeatB_cons_eq f xs)
    | inr hu =>
      cases ih hu with
      | inl hxs => exact Or.inl (memFeatB_cons_true hxs)
      | inr hb => exact Or.inr hb

/-- Expand one step of feature implications across a `FeatureSet` without duplicate blowup. -/
noncomputable def expandStep (fs : FeatureSet) : FeatureSet :=
  match fs with
  | [] => []
  | f :: rest => unionFeats (f :: directImplied f) (expandStep rest)

/-- Fuel-bounded transitive implication closure (`rustc_target::Target::implied_target_features`). -/
noncomputable def expandImpliedFuel (fuel : Nat) (fs : FeatureSet) : FeatureSet :=
  match fuel with
  | 0 => fs
  | k + 1 => expandImpliedFuel k (expandStep fs)

/-- Complete x86-64 transitive implication closure (longest chain `avx512f -> ... -> sse` has depth 9). -/
noncomputable def impliedClosure (fs : FeatureSet) : FeatureSet :=
  expandImpliedFuel 10 fs

theorem mem_self_expandStep (f : Feature) (fs : FeatureSet) :
    memFeatB f fs = true → memFeatB f (expandStep fs) = true := by
  intro h
  induction fs with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [expandStep]
    cases memFeatB_cons_cases h with
    | inl hfx =>
      subst hfx
      exact memFeatB_unionFeats_left (f :: directImplied f) (expandStep xs)
        (memFeatB_cons_eq f (directImplied f))
    | inr hfxs =>
      exact memFeatB_unionFeats_right (x :: directImplied x) (expandStep xs) (ih hfxs)

theorem subsetFeats_expandStep (fs : FeatureSet) : SubsetFeats fs (expandStep fs) := by
  intro f hf
  exact mem_self_expandStep f fs hf

theorem expandStep_monotone {a b : FeatureSet} (hab : SubsetFeats a b) :
    SubsetFeats (expandStep a) (expandStep b) := by
  intro f hf
  induction a with
  | nil => cases hf
  | cons x xs ih =>
    dsimp only [expandStep] at hf
    cases memFeatB_unionFeats_cases (x :: directImplied x) (expandStep xs) hf with
    | inl hxd =>
      cases memFeatB_cons_cases hxd with
      | inl hfx =>
        subst hfx
        exact mem_self_expandStep f b (hab f (memFeatB_cons_eq f xs))
      | inr hdir =>
        have hxb : memFeatB x b = true := hab x (memFeatB_cons_eq x xs)
        clear hf hxd ih hab xs
        induction b with
        | nil => cases hxb
        | cons y ys ihy =>
          dsimp only [expandStep]
          cases memFeatB_cons_cases hxb with
          | inl hxy =>
            subst hxy
            exact memFeatB_unionFeats_left (x :: directImplied x) (expandStep ys)
              (memFeatB_cons_true hdir)
          | inr hxys =>
            exact memFeatB_unionFeats_right (y :: directImplied y) (expandStep ys) (ihy hxys)
    | inr hexp =>
      have hxsb : SubsetFeats xs b := fun g hg => hab g (memFeatB_cons_true hg)
      exact ih hxsb hexp

theorem expandImpliedFuel_monotone (fuel : Nat) {a b : FeatureSet}
    (hab : SubsetFeats a b) :
    SubsetFeats (expandImpliedFuel fuel a) (expandImpliedFuel fuel b) := by
  induction fuel generalizing a b with
  | zero => exact hab
  | succ k ih =>
    dsimp only [expandImpliedFuel]
    exact ih (expandStep_monotone hab)

theorem impliedClosure_monotone {a b : FeatureSet} (hab : SubsetFeats a b) :
    SubsetFeats (impliedClosure a) (impliedClosure b) :=
  expandImpliedFuel_monotone 10 hab

theorem expandImpliedFuel_extensive (fuel : Nat) (fs : FeatureSet) :
    SubsetFeats fs (expandImpliedFuel fuel fs) := by
  induction fuel generalizing fs with
  | zero => exact SubsetFeats.refl fs
  | succ k ih =>
    dsimp only [expandImpliedFuel]
    exact SubsetFeats.trans (subsetFeats_expandStep fs) (ih (expandStep fs))

theorem impliedClosure_extensive (fs : FeatureSet) : SubsetFeats fs (impliedClosure fs) :=
  expandImpliedFuel_extensive 10 fs

/-- Concrete separation between MIR ordered-sequence equality and set equality (`#[target_feature(enable = "avx2,bmi1")]` vs `"bmi1,avx2"`). -/
theorem mirSeqEq_strictly_stronger_than_setEq :
    SetEqFeats [.avx2, .bmi1] [.bmi1, .avx2] ∧
    seqEqFeatsB [.avx2, .bmi1] [.bmi1, .avx2] = false := by
  constructor
  · constructor
    · apply subsetFeatsB_sound
      rfl
    · apply subsetFeatsB_sound
      rfl
  · rfl

/-- Implication containment witness: `avx2` implies `avx`, `sse4.2`, `sse2`, and `sse`. -/
theorem avx2_implies_avx_and_sse2 :
    SubsetFeats [.sse, .sse2, .sse42, .avx, .avx2] (impliedClosure [.avx2]) := by
  apply subsetFeatsB_sound
  rfl

/-- Implication containment witness: `avx512f` implies `avx2`, `fma`, `f16c`, `avx`, and `sse2`. -/
theorem avx512f_implies_avx2_fma_f16c :
    SubsetFeats [.sse2, .avx, .avx2, .fma, .f16c, .avx512f] (impliedClosure [.avx512f]) := by
  apply subsetFeatsB_sound
  rfl

/-! ## Section 2: SIMD Vector ABI Lowering, `AbiErrorDisabledVectorType`, and Register Compatibility -/

/-- Fixed SIMD vector bit-widths supported in x86-64 ABI lowering. -/
inductive VecWidth where
  | w128
  | w256
  | w512

/-- Concrete SIMD vector or transparent/C-aggregate argument shapes. -/
inductive VecTy where
  | m128
  | m256
  | m512
  | wrap256

/-- Rust calling conventions relevant to vector ABI lowering. -/
inductive AbiConv where
  | externRust
  | externC

/-- `rustc_target::callconv::PassMode` slice for SIMD values. -/
inductive PassMode where
  | direct
  | cast (w : VecWidth) (opaqueBytes : Bool)
  | indirect (alignBytes : Nat)

/-- Physical register or memory-passing class selected by LLVM SelectionDAG / `x86_64.rs`. -/
inductive RegClass where
  | xmm128
  | ymm256
  | zmm512
  | opaqueVec256
  | splitOrStack (w : VecWidth)
  | memPtr (alignBytes : Nat)

noncomputable def RegClass.beq (a b : RegClass) : Bool :=
  match a, b with
  | .xmm128, .xmm128 => true
  | .ymm256, .ymm256 => true
  | .zmm512, .zmm512 => true
  | .opaqueVec256, .opaqueVec256 => true
  | .splitOrStack .w128, .splitOrStack .w128 => true
  | .splitOrStack .w256, .splitOrStack .w256 => true
  | .splitOrStack .w512, .splitOrStack .w512 => true
  | .memPtr n1, .memPtr n2 => Nat.beq n1 n2
  | _, _ => false

theorem RegClass.beq_refl (a : RegClass) : RegClass.beq a a = true := by
  cases a with
  | xmm128 => rfl
  | ymm256 => rfl
  | zmm512 => rfl
  | opaqueVec256 => rfl
  | splitOrStack w => cases w <;> rfl
  | memPtr n =>
    dsimp only [RegClass.beq]
    exact Nat.beq_refl n

theorem RegClass.eq_of_beq_true {a b : RegClass} (h : RegClass.beq a b = true) : a = b := by
  cases a with
  | xmm128 =>
    cases b <;> dsimp only [RegClass.beq] at h <;> (first | rfl | cases h)
  | ymm256 =>
    cases b <;> dsimp only [RegClass.beq] at h <;> (first | rfl | cases h)
  | zmm512 =>
    cases b <;> dsimp only [RegClass.beq] at h <;> (first | rfl | cases h)
  | opaqueVec256 =>
    cases b <;> dsimp only [RegClass.beq] at h <;> (first | rfl | cases h)
  | splitOrStack w1 =>
    cases w1 <;> cases b with
    | splitOrStack w2 =>
      cases w2 <;> dsimp only [RegClass.beq] at h <;> (first | rfl | cases h)
    | xmm128 => dsimp only [RegClass.beq] at h; cases h
    | ymm256 => dsimp only [RegClass.beq] at h; cases h
    | zmm512 => dsimp only [RegClass.beq] at h; cases h
    | opaqueVec256 => dsimp only [RegClass.beq] at h; cases h
    | memPtr _ => dsimp only [RegClass.beq] at h; cases h
  | memPtr n1 =>
    cases b with
    | memPtr n2 =>
      dsimp only [RegClass.beq] at h
      exact congrArg RegClass.memPtr (Nat.eq_of_beq_eq_true h)
    | xmm128 | ymm256 | zmm512 | opaqueVec256 | splitOrStack _ =>
      dsimp only [RegClass.beq] at h
      cases h

theorem RegClass.beq_iff_eq (a b : RegClass) : RegClass.beq a b = true ↔ a = b := by
  constructor
  · exact RegClass.eq_of_beq_true
  · intro h
    subst h
    exact RegClass.beq_refl a

/-- Target ABI configuration distinguishing `2026-09` (`rustSimdPassDirect128 = false`,
    matching `rustc 1.98.0` / `49d73453`) from `2026-11` (`rustSimdPassDirect128 = true`,
    `can_pass_simd_directly` in `3ef0c22cd`). -/
structure TargetSpec where
  baselineFeats : FeatureSet
  abiRequiredFeats : FeatureSet
  rustSimdPassDirect128 : Bool

noncomputable def x86_64Spec2026_09 : TargetSpec :=
  { baselineFeats := [.sse, .sse2]
    abiRequiredFeats := [.sse2]
    rustSimdPassDirect128 := false }

noncomputable def x86_64Spec2026_11 : TargetSpec :=
  { baselineFeats := [.sse, .sse2]
    abiRequiredFeats := [.sse2]
    rustSimdPassDirect128 := true }

/-- `X86_FEATURES_FOR_CORRECT_FIXED_LENGTH_VECTOR_ABI` (`target_features.rs:1172-1173`). -/
noncomputable def vecRequiredFeature (v : VecTy) : Feature :=
  match v with
  | .m128 => .sse
  | .m256 => .avx
  | .m512 => .avx512f
  | .wrap256 => .avx

/-- Hardware width gate for a `RegClass` (`xmm` requires `sse`, `ymm`/`opaqueVec256` requires `avx`,
    `zmm` requires `avx512f`). -/
noncomputable def regClassHardwareReq (rc : RegClass) : FeatureSet :=
  match rc with
  | .xmm128 => [.sse]
  | .ymm256 => [.avx]
  | .zmm512 => [.avx512f]
  | .opaqueVec256 => [.avx]
  | .splitOrStack _ => []
  | .memPtr _ => []

/-- `PassMode` chosen by `rustc_target::callconv::{mod, x86_64}.rs`. -/
noncomputable def passModeFor (spec : TargetSpec) (conv : AbiConv) (v : VecTy) : PassMode :=
  match conv with
  | .externC =>
    match v with
    | .m128 => .cast .w128 false
    | .m256 => .cast .w256 false
    | .m512 => .cast .w512 false
    | .wrap256 => .cast .w256 true
  | .externRust =>
    match v with
    | .m128 =>
      match spec.rustSimdPassDirect128 with
      | true => .direct
      | false => .indirect 16
    | .m256 => .indirect 32
    | .m512 => .indirect 64
    | .wrap256 => .indirect 32

/-- Physical `RegClass` selected on one side of a call under `passModeFor` and `sideFeats`. -/
noncomputable def regClassFor (spec : TargetSpec) (conv : AbiConv)
    (sideFeats : FeatureSet) (v : VecTy) : RegClass :=
  match passModeFor spec conv v with
  | .indirect al => .memPtr al
  | .direct => .xmm128
  | .cast .w128 _ =>
    match memFeatB .sse sideFeats with
    | true => .xmm128
    | false => .splitOrStack .w128
  | .cast .w256 opaqueBytes =>
    match memFeatB .avx sideFeats with
    | true =>
      match opaqueBytes with
      | true => .opaqueVec256
      | false => .ymm256
    | false => .splitOrStack .w256
  | .cast .w512 _ =>
    match memFeatB .avx512f sideFeats with
    | true => .zmm512
    | false => .splitOrStack .w512

/-- Whether `rustc_monomorphize::mono_checks::abi_check` (`do_check_simd_vector_abi`) accepts
    passing/defining `v` with `conv` on a function with effective features `sideFeats`. -/
noncomputable def abiCheckSide (conv : AbiConv) (sideFeats : FeatureSet) (v : VecTy) : Bool :=
  match conv with
  | .externC => memFeatB (vecRequiredFeature v) sideFeats
  | .externRust => true

/-- Whether caller and callee lower `v` to identical physical `RegClass`es. -/
noncomputable def CallAbiMatch (spec : TargetSpec) (conv : AbiConv)
    (callerFeats calleeFeats : FeatureSet) (v : VecTy) : Prop :=
  regClassFor spec conv callerFeats v = regClassFor spec conv calleeFeats v

/-- Whether the selected physical register classes are legal on CPU `cpu`. -/
noncomputable def RegHardwareLegal (spec : TargetSpec) (conv : AbiConv)
    (callerFeats calleeFeats cpu : FeatureSet) (v : VecTy) : Prop :=
  SubsetFeats (regClassHardwareReq (regClassFor spec conv callerFeats v)) cpu ∧
  SubsetFeats (regClassHardwareReq (regClassFor spec conv calleeFeats v)) cpu

/-- `extern "C"` `PassMode::Cast` uses the intended SIMD vector register class cleanly iff
    the required vector feature is enabled on BOTH caller and callee (and supported by CPU). -/
theorem passModeCast_safe_iff_vector_feature_both_sides
    (spec : TargetSpec) (callerFeats calleeFeats cpu : FeatureSet) (v : VecTy) :
    (CallAbiMatch spec .externC callerFeats calleeFeats v ∧
     (regClassFor spec .externC callerFeats v ≠ .splitOrStack .w128 ∧
      regClassFor spec .externC callerFeats v ≠ .splitOrStack .w256 ∧
      regClassFor spec .externC callerFeats v ≠ .splitOrStack .w512) ∧
     RegHardwareLegal spec .externC callerFeats calleeFeats cpu v) ↔
    (MemFeat (vecRequiredFeature v) callerFeats ∧
     MemFeat (vecRequiredFeature v) calleeFeats ∧
     MemFeat (vecRequiredFeature v) cpu) := by
  constructor
  · intro ⟨hMatch, hNotSplit, hHw⟩
    cases v
    · dsimp only [vecRequiredFeature]
      dsimp only [CallAbiMatch, regClassFor, passModeFor] at hMatch
      dsimp only [regClassFor, passModeFor] at hNotSplit
      dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq] at hHw
      cases h1 : memFeatB .sse callerFeats
      · rw [h1] at hNotSplit
        exact absurd rfl hNotSplit.1
      · cases h2 : memFeatB .sse calleeFeats
        · rw [h1, h2] at hMatch
          cases hMatch
        · rw [h1] at hHw
          have hcpu := hHw.1 .sse (memFeatB_cons_eq .sse [])
          exact ⟨h1, h2, hcpu⟩
    · dsimp only [vecRequiredFeature]
      dsimp only [CallAbiMatch, regClassFor, passModeFor] at hMatch
      dsimp only [regClassFor, passModeFor] at hNotSplit
      dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq] at hHw
      cases h1 : memFeatB .avx callerFeats
      · rw [h1] at hNotSplit
        exact absurd rfl hNotSplit.2.1
      · cases h2 : memFeatB .avx calleeFeats
        · rw [h1, h2] at hMatch
          cases hMatch
        · rw [h1] at hHw
          have hcpu := hHw.1 .avx (memFeatB_cons_eq .avx [])
          exact ⟨h1, h2, hcpu⟩
    · dsimp only [vecRequiredFeature]
      dsimp only [CallAbiMatch, regClassFor, passModeFor] at hMatch
      dsimp only [regClassFor, passModeFor] at hNotSplit
      dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq] at hHw
      cases h1 : memFeatB .avx512f callerFeats
      · rw [h1] at hNotSplit
        exact absurd rfl hNotSplit.2.2
      · cases h2 : memFeatB .avx512f calleeFeats
        · rw [h1, h2] at hMatch
          cases hMatch
        · rw [h1] at hHw
          have hcpu := hHw.1 .avx512f (memFeatB_cons_eq .avx512f [])
          exact ⟨h1, h2, hcpu⟩
    · dsimp only [vecRequiredFeature]
      dsimp only [CallAbiMatch, regClassFor, passModeFor] at hMatch
      dsimp only [regClassFor, passModeFor] at hNotSplit
      dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq] at hHw
      cases h1 : memFeatB .avx callerFeats
      · rw [h1] at hNotSplit
        exact absurd rfl hNotSplit.2.1
      · cases h2 : memFeatB .avx calleeFeats
        · rw [h1, h2] at hMatch
          cases hMatch
        · rw [h1] at hHw
          have hcpu := hHw.1 .avx (memFeatB_cons_eq .avx [])
          exact ⟨h1, h2, hcpu⟩
  · intro ⟨hc1, hc2, hcpu⟩
    cases v <;>
    · dsimp only [vecRequiredFeature] at hc1 hc2 hcpu
      dsimp only [MemFeat] at hc1 hc2
      dsimp only [CallAbiMatch, RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq, SubsetFeats]
      rw [hc1, hc2]
      dsimp only []
      refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · intro f hf
        cases memFeatB_cons_cases hf with
        | inl hfeq => subst hfeq; exact hcpu
        | inr hemp => cases hemp
      · intro f hf
        cases memFeatB_cons_cases hf with
        | inl hfeq => subst hfeq; exact hcpu
        | inr hemp => cases hemp

/-- `rustc_monomorphize::mono_checks::abi_check` enforces `extern "C"` register compatibility
    iff both sides enable `vecRequiredFeature v` (assuming CPU supports caller/callee). -/
theorem abiCheckExternC_sound_and_complete
    (spec : TargetSpec) (callerFeats calleeFeats cpu : FeatureSet) (v : VecTy)
    (hCpuCaller : SubsetFeats callerFeats cpu) :
    (abiCheckSide .externC callerFeats v = true ∧ abiCheckSide .externC calleeFeats v = true) ↔
    (CallAbiMatch spec .externC callerFeats calleeFeats v ∧
     (regClassFor spec .externC callerFeats v ≠ .splitOrStack .w128 ∧
      regClassFor spec .externC callerFeats v ≠ .splitOrStack .w256 ∧
      regClassFor spec .externC callerFeats v ≠ .splitOrStack .w512) ∧
     RegHardwareLegal spec .externC callerFeats calleeFeats cpu v) := by
  constructor
  · intro ⟨h1, h2⟩
    have h1' : MemFeat (vecRequiredFeature v) callerFeats := h1
    have h2' : MemFeat (vecRequiredFeature v) calleeFeats := h2
    have hcpu : MemFeat (vecRequiredFeature v) cpu := hCpuCaller (vecRequiredFeature v) h1'
    exact (passModeCast_safe_iff_vector_feature_both_sides spec callerFeats calleeFeats cpu v).2
      ⟨h1', h2', hcpu⟩
  · intro h
    have h' := (passModeCast_safe_iff_vector_feature_both_sides spec callerFeats calleeFeats cpu v).1 h
    exact ⟨h'.1, h'.2.1⟩

/-- Under `extern "Rust"`, wide SIMD types (`__m256`, `__m512`, `Wrap256`) unconditionally lower
    to `PassMode::Indirect` (`sret` + pointer), matching across arbitrary feature mismatches. -/
theorem externRust_wide_simd_indirect_unconditional
    (spec : TargetSpec) (callerFeats calleeFeats cpu : FeatureSet)
    (v : VecTy) (hWide : v = .m256 ∨ v = .m512 ∨ v = .wrap256) :
    CallAbiMatch spec .externRust callerFeats calleeFeats v ∧
    RegHardwareLegal spec .externRust callerFeats calleeFeats cpu v := by
  cases hWide with
  | inl hm256 =>
    subst hm256
    refine ⟨rfl, ?_, ?_⟩ <;> intro f hf <;> cases hf
  | inr hrest =>
    cases hrest with
    | inl hm512 =>
      subst hm512
      refine ⟨rfl, ?_, ?_⟩ <;> intro f hf <;> cases hf
    | inr hwrap =>
      subst hwrap
      refine ⟨rfl, ?_, ?_⟩ <;> intro f hf <;> cases hf

/-- Under `2026-09` (`1.98.0` / `49d73453`), even `__m128` lowers to `PassMode::Indirect`
    (`sret([16 x i8]) align 16`) under `extern "Rust"`. -/
theorem externRust_2026_09_m128_indirect
    (callerFeats calleeFeats cpu : FeatureSet) :
    regClassFor x86_64Spec2026_09 .externRust callerFeats .m128 = .memPtr 16 ∧
    CallAbiMatch x86_64Spec2026_09 .externRust callerFeats calleeFeats .m128 ∧
    RegHardwareLegal x86_64Spec2026_09 .externRust callerFeats calleeFeats cpu .m128 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> intro f hf <;> cases hf

/-- Under `2026-11` (`3ef0c22cd` `can_pass_simd_directly`), `extern "Rust"` passes `__m128`
    via `PassMode::Direct` (`xmm128`), which remains sound across arbitrary `#[target_feature]`
    callers/callees provided baseline `sse` is enabled on the CPU (via `abiRequiredFeats = [sse2]`). -/
theorem externRust_2026_11_m128_direct_sound
    (callerFeats calleeFeats cpu : FeatureSet) (hSse : MemFeat .sse cpu) :
    regClassFor x86_64Spec2026_11 .externRust callerFeats .m128 = .xmm128 ∧
    CallAbiMatch x86_64Spec2026_11 .externRust callerFeats calleeFeats .m128 ∧
    RegHardwareLegal x86_64Spec2026_11 .externRust callerFeats calleeFeats cpu .m128 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  · intro f hf
    cases memFeatB_cons_cases hf with
    | inl hfe => subst hfe; exact hSse
    | inr hnil => cases hnil

/-- Counterexample: baseline (`[sse, sse2]`) calling `avx2` (`[sse, sse2, avx, avx2]`) under
    `extern "C"` with `__m256` suffers a register-class mismatch (`splitOrStack ≠ ymm256`) and is
    rejected by `abiCheckSide`. -/
theorem externC_mismatched_avx_abi_corruption :
    regClassFor x86_64Spec2026_11 .externC [.sse, .sse2] .m256 = .splitOrStack .w256 ∧
    regClassFor x86_64Spec2026_11 .externC [.sse, .sse2, .avx, .avx2] .m256 = .ymm256 ∧
    ¬ CallAbiMatch x86_64Spec2026_11 .externC [.sse, .sse2] [.sse, .sse2, .avx, .avx2] .m256 ∧
    abiCheckSide .externC [.sse, .sse2] .m256 = false := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro h
  dsimp only [CallAbiMatch, regClassFor, passModeFor] at h
  cases h

/-! ## Section 3: CPU-Capability-Indexed Semantics & `target_feature_11` Discipline -/

/-- `#[inline]` attribute variants. -/
inductive AttrInline where
  | none
  | hint
  | always
  | force

/-- Function header safety (`fn` vs `unsafe fn`). -/
inductive SafetyMode where
  | safe
  | unsafeFn

/-- Compiler attribute policy modeling the `2026-09` vs `2026-11` `#145574` change. -/
structure AttrPolicy where
  rejectTargetFeatureAlwaysInline : Bool

noncomputable def policy2026_09 : AttrPolicy :=
  { rejectTargetFeatureAlwaysInline := true }

noncomputable def policy2026_11 : AttrPolicy :=
  { rejectTargetFeatureAlwaysInline := false }

/-- Function-body instructions modeling capability-gated vector ops, safe/unsafe calls,
    safe/unsafe `fn` pointer coercions, ABI-sensitive calls, and runtime feature branches. -/
inductive Inst where
  | nop
  | alu
  | vecOp (req : FeatureSet) (w : VecWidth)
  | safeCall (callee : Nat)
  | unsafeCall (callee : Nat)
  | reifySafeFnPtr (target : Nat)
  | reifyUnsafeFnPtr (target : Nat)
  | abiCall (conv : AbiConv) (v : VecTy) (callee : Nat)
  | seq (first : Inst) (second : Inst)
  | guardedBranch (guardReq : FeatureSet) (thenBody : Inst) (elseBody : Inst)

/-- Function definition in a compiled crate. `declaredFeats` preserves the user-written list order
    (affecting MIR `Inline` via `SeqEqFeats`), while `effectiveFeats` is its `impliedClosure` merged
    with baseline target features. -/
structure FnDef where
  id : Nat
  safety : SafetyMode
  declaredFeats : FeatureSet
  effectiveFeats : FeatureSet
  inlineAttr : AttrInline
  isMain : Bool
  isTraitSafe : Bool
  body : List Inst

/-- Program table of functions plus entry point ID. -/
structure Program where
  fns : List FnDef
  entryId : Nat

noncomputable def lookupFn (fns : List FnDef) (fid : Nat) : Option FnDef :=
  match fns with
  | [] => none
  | f :: rest =>
    match Nat.beq f.id fid with
    | true => some f
    | false => lookupFn rest fid

/-- Runtime fault kinds. -/
inductive FaultKind where
  | sigill
  | abiMismatch
  | missingCallee
  | fuelExhausted

/-- Program execution outcome. -/
inductive ExecOutcome where
  | ok (steps : Nat)
  | fault (k : FaultKind)

/-- Fuel-bounded operational execution indexed by CPU hardware capabilities `cpu` and
    enclosing feature context `callerFeats`. -/
noncomputable def evalInsts (spec : TargetSpec) (prog : Program) (cpu : FeatureSet)
    (callerFeats : FeatureSet) (fuel : Nat) (insts : List Inst) : ExecOutcome :=
  match fuel with
  | 0 => .fault .fuelExhausted
  | fuel' + 1 =>
    match insts with
    | [] => .ok 0
    | inst :: rest =>
      let resHead : ExecOutcome :=
        match inst with
        | .nop => .ok 1
        | .alu => .ok 1
        | .vecOp req _ =>
          match subsetFeatsB req cpu with
          | true => .ok 1
          | false => .fault .sigill
        | .safeCall cid =>
          match lookupFn prog.fns cid with
          | none => .fault .missingCallee
          | some callee =>
            evalInsts spec prog cpu callee.effectiveFeats fuel' callee.body
        | .unsafeCall cid =>
          match lookupFn prog.fns cid with
          | none => .fault .missingCallee
          | some callee =>
            evalInsts spec prog cpu callee.effectiveFeats fuel' callee.body
        | .reifySafeFnPtr tid =>
          match lookupFn prog.fns tid with
          | none => .fault .missingCallee
          | some _ => .ok 1
        | .reifyUnsafeFnPtr tid =>
          match lookupFn prog.fns tid with
          | none => .fault .missingCallee
          | some _ => .ok 1
        | .abiCall conv v cid =>
          match lookupFn prog.fns cid with
          | none => .fault .missingCallee
          | some callee =>
            match RegClass.beq (regClassFor spec conv callerFeats v)
                (regClassFor spec conv callee.effectiveFeats v) with
            | false => .fault .abiMismatch
            | true =>
              let hreq := regClassHardwareReq (regClassFor spec conv callerFeats v)
              match subsetFeatsB hreq cpu with
              | false => .fault .sigill
              | true => evalInsts spec prog cpu callee.effectiveFeats fuel' callee.body
        | .seq first second =>
          evalInsts spec prog cpu callerFeats fuel' [first, second]
        | .guardedBranch guardReq thenB elseB =>
          match subsetFeatsB guardReq cpu with
          | true => evalInsts spec prog cpu (callerFeats ++ guardReq) fuel' [thenB]
          | false => evalInsts spec prog cpu callerFeats fuel' [elseB]
      match resHead with
      | .fault k => .fault k
      | .ok s1 =>
        match evalInsts spec prog cpu callerFeats fuel' rest with
        | .fault k => .fault k
        | .ok s2 => .ok (s1 + s2)

/-- Top-level program execution starting from `prog.entryId`. -/
noncomputable def evalProgram (spec : TargetSpec) (prog : Program)
    (cpu : FeatureSet) (fuel : Nat) : ExecOutcome :=
  match lookupFn prog.fns prog.entryId with
  | none => .fault .missingCallee
  | some entry => evalInsts spec prog cpu entry.effectiveFeats fuel entry.body

/-! ## Section 4: `target_feature_11` Static Typing & `AttrPolicy` (`2026-09` vs `2026-11`) -/

/-- Attribute-level legality mirroring `codegen_attrs.rs`, `target_features.rs:176`, and `entry.rs:108`. -/
noncomputable def AttrValid (pol : AttrPolicy) (fn : FnDef) : Prop :=
  (fn.isMain = true → fn.declaredFeats = []) ∧
  (fn.isTraitSafe = true → fn.declaredFeats = []) ∧
  (pol.rejectTargetFeatureAlwaysInline = true →
    fn.declaredFeats ≠ [] → fn.inlineAttr ≠ .always)

/-- Function effective features must match `spec.baselineFeats ++ impliedClosure fn.declaredFeats`. -/
noncomputable def EffectiveFeatsConsistent (spec : TargetSpec) (fn : FnDef) : Prop :=
  SetEqFeats fn.effectiveFeats (spec.baselineFeats ++ impliedClosure fn.declaredFeats)

/-- Static `target_feature_11` + `abi_check` typing for a single instruction.
    `headerFeats` tracks the function's static `#[target_feature]` set (checked by `safeCall` and
    `reifySafeFnPtr`, per `rustc_middle/src/ty/context.rs:1326-1357` and `coercion.rs:1324`),
    while `branchFeats` tracks runtime-checked `guardedBranch` capabilities (`is_x86_feature_detected!`). -/
noncomputable def InstWellTyped (spec : TargetSpec) (prog : Program)
    (headerFeats branchFeats : FeatureSet) : Inst → Prop
  | .nop => True
  | .alu => True
  | .vecOp req _ => SubsetFeats req (headerFeats ++ branchFeats)
  | .safeCall cid =>
    ∃ callee : FnDef, lookupFn prog.fns cid = some callee ∧
      SubsetFeats callee.effectiveFeats headerFeats
  | .unsafeCall cid =>
    ∃ callee : FnDef, lookupFn prog.fns cid = some callee ∧
      SubsetFeats callee.effectiveFeats (headerFeats ++ branchFeats)
  | .reifySafeFnPtr tid =>
    ∃ target : FnDef, lookupFn prog.fns tid = some target ∧
      SubsetFeats target.effectiveFeats headerFeats
  | .reifyUnsafeFnPtr tid =>
    ∃ _target : FnDef, lookupFn prog.fns tid = some _target
  | .abiCall conv v cid =>
    ∃ callee : FnDef, lookupFn prog.fns cid = some callee ∧
      SubsetFeats callee.effectiveFeats (headerFeats ++ branchFeats) ∧
      (conv = .externC →
        abiCheckSide .externC (headerFeats ++ branchFeats) v = true ∧
        abiCheckSide .externC callee.effectiveFeats v = true) ∧
      (conv = .externRust → v = .m128 → spec.rustSimdPassDirect128 = true →
        MemFeat .sse (headerFeats ++ branchFeats))
  | .seq first second =>
    InstWellTyped spec prog headerFeats branchFeats first ∧
    InstWellTyped spec prog headerFeats branchFeats second
  | .guardedBranch guardReq thenB elseB =>
    InstWellTyped spec prog headerFeats (branchFeats ++ guardReq) thenB ∧
    InstWellTyped spec prog headerFeats branchFeats elseB

/-- Well-typedness of a list of instructions under `(headerFeats, branchFeats)`. -/
noncomputable def InstsWellTyped (spec : TargetSpec) (prog : Program)
    (headerFeats branchFeats : FeatureSet) (insts : List Inst) : Prop :=
  ∀ i : Inst, i ∈ insts → InstWellTyped spec prog headerFeats branchFeats i

/-- Whole-program `SafeTf11Typed` predicate. -/
noncomputable def SafeTf11Typed (spec : TargetSpec) (pol : AttrPolicy) (prog : Program) : Prop :=
  (∃ entry : FnDef, lookupFn prog.fns prog.entryId = some entry ∧
    SubsetFeats entry.effectiveFeats spec.baselineFeats) ∧
  (∀ fn : FnDef, fn ∈ prog.fns →
    AttrValid pol fn ∧
    EffectiveFeatsConsistent spec fn ∧
    InstsWellTyped spec prog fn.effectiveFeats [] fn.body)

theorem lookupFn_mem {fns : List FnDef} {fid : Nat} {fn : FnDef}
    (h : lookupFn fns fid = some fn) : fn ∈ fns := by
  induction fns with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [lookupFn] at h
    cases hb : Nat.beq x.id fid
    · rw [hb] at h
      exact List.Mem.tail x (ih h)
    · rw [hb] at h
      cases h
      exact List.Mem.head xs

/-- Monotonicity of `InstWellTyped` under enlarging `headerFeats` and `branchFeats`. -/
theorem instWellTyped_mono {spec : TargetSpec} {prog : Program} {inst : Inst} :
    ∀ {h1 h2 b1 b2 : FeatureSet},
      SubsetFeats h1 h2 → SubsetFeats b1 b2 →
      InstWellTyped spec prog h1 b1 inst → InstWellTyped spec prog h2 b2 inst := by
  induction inst with
  | nop => intros; trivial
  | alu => intros; trivial
  | vecOp req w =>
    intro h1 h2 b1 b2 hh hb hwt
    dsimp only [InstWellTyped] at hwt ⊢
    exact SubsetFeats.trans hwt
      (SubsetFeats.append_intro
        (SubsetFeats.trans hh (SubsetFeats.append_left h2 b2))
        (SubsetFeats.trans hb (SubsetFeats.append_right h2 b2)))
  | safeCall cid =>
    intro h1 h2 b1 b2 hh _ hwt
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c hrest =>
      cases hrest with
      | intro hc hce =>
        exact ⟨c, hc, SubsetFeats.trans hce hh⟩
  | unsafeCall cid =>
    intro h1 h2 b1 b2 hh hb hwt
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c hrest =>
      cases hrest with
      | intro hc hce =>
        refine ⟨c, hc, SubsetFeats.trans hce ?_⟩
        exact SubsetFeats.append_intro
          (SubsetFeats.trans hh (SubsetFeats.append_left h2 b2))
          (SubsetFeats.trans hb (SubsetFeats.append_right h2 b2))
  | reifySafeFnPtr tid =>
    intro h1 h2 b1 b2 hh _ hwt
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro t hrest =>
      cases hrest with
      | intro ht hte =>
        exact ⟨t, ht, SubsetFeats.trans hte hh⟩
  | reifyUnsafeFnPtr tid =>
    intro _ _ _ _ _ _ hwt
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro t ht =>
      exact ⟨t, ht⟩
  | abiCall conv v cid =>
    intro h1 h2 b1 b2 hh hb hwt
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c h1c =>
      cases h1c with
      | intro hc h2c =>
        cases h2c with
        | intro hce h3c =>
          cases h3c with
          | intro hcExtC hcRust =>
            have hctx : SubsetFeats (h1 ++ b1) (h2 ++ b2) :=
              SubsetFeats.append_intro
                (SubsetFeats.trans hh (SubsetFeats.append_left h2 b2))
                (SubsetFeats.trans hb (SubsetFeats.append_right h2 b2))
            refine ⟨c, hc, SubsetFeats.trans hce hctx, ?_, ?_⟩
            · intro hExtC
              have hBoth := hcExtC hExtC
              refine ⟨?_, hBoth.2⟩
              dsimp only [abiCheckSide] at hBoth ⊢
              exact hctx (vecRequiredFeature v) hBoth.1
            · intro hRust hm128 hDirect
              exact hctx .sse (hcRust hRust hm128 hDirect)
  | seq first second ihFirst ihSecond =>
    intro h1 h2 b1 b2 hh hb hwt
    dsimp only [InstWellTyped] at hwt ⊢
    exact ⟨ihFirst hh hb hwt.1, ihSecond hh hb hwt.2⟩
  | guardedBranch guardReq thenB elseB ihThen ihElse =>
    intro h1 h2 b1 b2 hh hb hwt
    dsimp only [InstWellTyped] at hwt ⊢
    exact ⟨ihThen hh (SubsetFeats.append_mono_left hb) hwt.1, ihElse hh hb hwt.2⟩

theorem instsWellTyped_mono {spec : TargetSpec} {prog : Program} {insts : List Inst}
    {h1 h2 b1 b2 : FeatureSet} (hh : SubsetFeats h1 h2) (hb : SubsetFeats b1 b2)
    (hwt : InstsWellTyped spec prog h1 b1 insts) : InstsWellTyped spec prog h2 b2 insts := by
  intro i hi
  exact instWellTyped_mono hh hb (hwt i hi)

theorem instsWellTyped_append {spec : TargetSpec} {prog : Program}
    {h b : FeatureSet} {a1 a2 : List Inst}
    (ha1 : InstsWellTyped spec prog h b a1)
    (ha2 : InstsWellTyped spec prog h b a2) :
    InstsWellTyped spec prog h b (a1 ++ a2) := by
  intro i hi
  induction a1 with
  | nil => exact ha2 i hi
  | cons x xs ih =>
    change i ∈ x :: (xs ++ a2) at hi
    cases hi with
    | head _ => exact ha1 _ (List.Mem.head _)
    | tail _ htail =>
      exact ih (fun j hj => ha1 j (List.Mem.tail _ hj)) htail

/-- Core runtime `SIGILL` and ABI-mismatch freedom over `evalInsts`:
    whenever `InstsWellTyped spec prog headerFeats branchFeats insts` and
    `SubsetFeats (headerFeats ++ branchFeats) cpu`, execution at any fuel
    never faults with `.sigill`, `.abiMismatch`, or `.missingCallee`. -/
theorem evalInsts_no_sigill_or_abi_fault
    (spec : TargetSpec) (pol : AttrPolicy) (prog : Program)
    (hTyped : SafeTf11Typed spec pol prog) :
    ∀ (fuel : Nat) (headerFeats branchFeats cpu : FeatureSet) (insts : List Inst),
      SubsetFeats (headerFeats ++ branchFeats) cpu →
      InstsWellTyped spec prog headerFeats branchFeats insts →
      evalInsts spec prog cpu (headerFeats ++ branchFeats) fuel insts ≠ .fault .sigill ∧
      evalInsts spec prog cpu (headerFeats ++ branchFeats) fuel insts ≠ .fault .abiMismatch ∧
      evalInsts spec prog cpu (headerFeats ++ branchFeats) fuel insts ≠ .fault .missingCallee := by
  intro fuel
  induction fuel with
  | zero =>
    intro headerFeats branchFeats cpu insts _ _
    dsimp only [evalInsts]
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
  | succ f' ih =>
    intro headerFeats branchFeats cpu insts hCpu hWt
    cases insts with
    | nil =>
      dsimp only [evalInsts]
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
    | cons inst rest =>
      have hInstWt : InstWellTyped spec prog headerFeats branchFeats inst :=
        hWt inst (List.Mem.head rest)
      have hRestWt : InstsWellTyped spec prog headerFeats branchFeats rest :=
        fun j hj => hWt j (List.Mem.tail inst hj)
      have hTail := ih headerFeats branchFeats cpu rest hCpu hRestWt
      have hHeadSafe : ∀ (k : FaultKind),
          (k = .sigill ∨ k = .abiMismatch ∨ k = .missingCallee) →
          (match inst with
          | .nop => ExecOutcome.ok 1
          | .alu => .ok 1
          | .vecOp req _ =>
            match subsetFeatsB req cpu with | true => .ok 1 | false => .fault .sigill
          | .safeCall cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .unsafeCall cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .reifySafeFnPtr tid =>
            match lookupFn prog.fns tid with | none => .fault .missingCallee | some _ => .ok 1
          | .reifyUnsafeFnPtr tid =>
            match lookupFn prog.fns tid with | none => .fault .missingCallee | some _ => .ok 1
          | .abiCall conv v cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee =>
              match RegClass.beq (regClassFor spec conv (headerFeats ++ branchFeats) v)
                  (regClassFor spec conv callee.effectiveFeats v) with
              | false => .fault .abiMismatch
              | true =>
                let hreq := regClassHardwareReq (regClassFor spec conv (headerFeats ++ branchFeats) v)
                match subsetFeatsB hreq cpu with
                | false => .fault .sigill
                | true => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .seq first second =>
            evalInsts spec prog cpu (headerFeats ++ branchFeats) f' [first, second]
          | .guardedBranch guardReq thenB elseB =>
            match subsetFeatsB guardReq cpu with
            | true => evalInsts spec prog cpu ((headerFeats ++ branchFeats) ++ guardReq) f' [thenB]
            | false => evalInsts spec prog cpu (headerFeats ++ branchFeats) f' [elseB]) ≠ .fault k := by
        intro k hk hEq
        cases inst with
        | nop => cases hEq
        | alu => cases hEq
        | vecOp req w =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          have hSubB : subsetFeatsB req cpu = true :=
            subsetFeatsB_complete req cpu (SubsetFeats.trans hInstWt hCpu)
          rw [hSubB] at hEq
          cases hEq
        | safeCall cid =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          cases hInstWt with
          | intro callee hrest =>
            cases hrest with
            | intro hLook hSub =>
              rw [hLook] at hEq
              dsimp only [] at hEq
              have hMem := lookupFn_mem hLook
              have hTyped2 := hTyped
              dsimp only [SafeTf11Typed] at hTyped2
              have hCalleeWt := (hTyped2.2 callee hMem).2.2
              have hCalleeCpu : SubsetFeats (callee.effectiveFeats ++ []) cpu := by
                intro f hf
                cases memFeatB_append_cases callee.effectiveFeats [] hf with
                | inl ha => exact hCpu f (memFeatB_append_left headerFeats branchFeats (hSub f ha))
                | inr hb => cases hb
              have hRec := ih callee.effectiveFeats [] cpu callee.body hCalleeCpu hCalleeWt
              have hEq' : evalInsts spec prog cpu (callee.effectiveFeats ++ []) f' callee.body = .fault k := by
                rw [List.append_nil]
                exact hEq
              cases hk with
              | inl hk1 => subst hk1; exact hRec.1 hEq'
              | inr hk23 =>
                cases hk23 with
                | inl hk2 => subst hk2; exact hRec.2.1 hEq'
                | inr hk3 => subst hk3; exact hRec.2.2 hEq'
        | unsafeCall cid =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          cases hInstWt with
          | intro callee hrest =>
            cases hrest with
            | intro hLook hSub =>
              rw [hLook] at hEq
              dsimp only [] at hEq
              have hMem := lookupFn_mem hLook
              have hTyped2 := hTyped
              dsimp only [SafeTf11Typed] at hTyped2
              have hCalleeWt := (hTyped2.2 callee hMem).2.2
              have hCalleeCpu : SubsetFeats (callee.effectiveFeats ++ []) cpu := by
                intro f hf
                cases memFeatB_append_cases callee.effectiveFeats [] hf with
                | inl ha => exact hCpu f (hSub f ha)
                | inr hb => cases hb
              have hRec := ih callee.effectiveFeats [] cpu callee.body hCalleeCpu hCalleeWt
              have hEq' : evalInsts spec prog cpu (callee.effectiveFeats ++ []) f' callee.body = .fault k := by
                rw [List.append_nil]
                exact hEq
              cases hk with
              | inl hk1 => subst hk1; exact hRec.1 hEq'
              | inr hk23 =>
                cases hk23 with
                | inl hk2 => subst hk2; exact hRec.2.1 hEq'
                | inr hk3 => subst hk3; exact hRec.2.2 hEq'
        | reifySafeFnPtr tid =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          cases hInstWt with
          | intro t hrest =>
            cases hrest with
            | intro hLook _ =>
              rw [hLook] at hEq
              cases hEq
        | reifyUnsafeFnPtr tid =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          cases hInstWt with
          | intro t hLook =>
            rw [hLook] at hEq
            cases hEq
        | abiCall conv v cid =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          cases hInstWt with
          | intro callee h1c =>
            cases h1c with
            | intro hLook h2c =>
              cases h2c with
              | intro hSub h3c =>
                cases h3c with
                | intro hExtC hRust =>
                  rw [hLook] at hEq
                  dsimp only [] at hEq
                  have hCalleeCpu : SubsetFeats callee.effectiveFeats cpu := SubsetFeats.trans hSub hCpu
                  have hMatch : CallAbiMatch spec conv (headerFeats ++ branchFeats) callee.effectiveFeats v ∧
                      RegHardwareLegal spec conv (headerFeats ++ branchFeats) callee.effectiveFeats cpu v := by
                    cases conv with
                    | externRust =>
                      cases v with
                      | m128 =>
                        cases hd : spec.rustSimdPassDirect128
                        · exact ⟨by dsimp only [CallAbiMatch, regClassFor, passModeFor]; rw [hd],
                            by dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq]
                               rw [hd]; constructor <;> intro f hf <;> cases hf⟩
                        · have hSseCtx := hRust rfl rfl hd
                          have hSseCpu := hCpu .sse hSseCtx
                          exact ⟨by dsimp only [CallAbiMatch, regClassFor, passModeFor]; rw [hd],
                            by dsimp only [RegHardwareLegal, regClassFor, passModeFor, regClassHardwareReq]
                               rw [hd]; constructor <;> intro f hf <;>
                               · cases memFeatB_cons_cases hf with
                                 | inl he => subst he; exact hSseCpu
                                 | inr hn => cases hn⟩
                      | m256 =>
                        exact externRust_wide_simd_indirect_unconditional spec _ _ cpu .m256 (Or.inl rfl)
                      | m512 =>
                        exact externRust_wide_simd_indirect_unconditional spec _ _ cpu .m512 (Or.inr (Or.inl rfl))
                      | wrap256 =>
                        exact externRust_wide_simd_indirect_unconditional spec _ _ cpu .wrap256 (Or.inr (Or.inr rfl))
                    | externC =>
                      have hCheck := hExtC rfl
                      have hAbi := (abiCheckExternC_sound_and_complete spec (headerFeats ++ branchFeats)
                        callee.effectiveFeats cpu v hCpu).1 hCheck
                      exact ⟨hAbi.1, hAbi.2.2⟩
                  have hBeq : RegClass.beq (regClassFor spec conv (headerFeats ++ branchFeats) v)
                      (regClassFor spec conv callee.effectiveFeats v) = true :=
                    (RegClass.beq_iff_eq _ _).2 hMatch.1
                  rw [hBeq] at hEq
                  dsimp only [] at hEq
                  have hReqSubB : subsetFeatsB (regClassHardwareReq (regClassFor spec conv (headerFeats ++ branchFeats) v)) cpu = true :=
                    subsetFeatsB_complete _ _ hMatch.2.1
                  rw [hReqSubB] at hEq
                  dsimp only [] at hEq
                  have hMem := lookupFn_mem hLook
                  have hTyped2 := hTyped
                  dsimp only [SafeTf11Typed] at hTyped2
                  have hCalleeWt := (hTyped2.2 callee hMem).2.2
                  have hCalleeCpuNil : SubsetFeats (callee.effectiveFeats ++ []) cpu := by
                    intro f hf
                    cases memFeatB_append_cases callee.effectiveFeats [] hf with
                    | inl ha => exact hCalleeCpu f ha
                    | inr hb => cases hb
                  have hRec := ih callee.effectiveFeats [] cpu callee.body hCalleeCpuNil hCalleeWt
                  have hEq' : evalInsts spec prog cpu (callee.effectiveFeats ++ []) f' callee.body = .fault k := by
                    rw [List.append_nil]
                    exact hEq
                  cases hk with
                  | inl hk1 => subst hk1; exact hRec.1 hEq'
                  | inr hk23 =>
                    cases hk23 with
                    | inl hk2 => subst hk2; exact hRec.2.1 hEq'
                    | inr hk3 => subst hk3; exact hRec.2.2 hEq'
        | seq first second =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          have hSeqWt : InstsWellTyped spec prog headerFeats branchFeats [first, second] := by
            intro j hj
            cases hj with
            | head _ => exact hInstWt.1
            | tail _ hj' =>
              cases hj' with
              | head _ => exact hInstWt.2
              | tail _ hj'' => cases hj''
          have hRec := ih headerFeats branchFeats cpu [first, second] hCpu hSeqWt
          cases hk with
          | inl hk1 => subst hk1; exact hRec.1 hEq
          | inr hk23 =>
            cases hk23 with
            | inl hk2 => subst hk2; exact hRec.2.1 hEq
            | inr hk3 => subst hk3; exact hRec.2.2 hEq
        | guardedBranch guardReq thenB elseB =>
          dsimp only [] at hEq
          dsimp only [InstWellTyped] at hInstWt
          have hElseWt : InstsWellTyped spec prog headerFeats branchFeats [elseB] := by
            intro j hj
            cases hj with
            | head _ => exact hInstWt.2
            | tail _ hj' => cases hj'
          have hThenWt : InstsWellTyped spec prog headerFeats (branchFeats ++ guardReq) [thenB] := by
            intro j hj
            cases hj with
            | head _ => exact hInstWt.1
            | tail _ hj' => cases hj'
          cases hG : subsetFeatsB guardReq cpu
          · rw [hG] at hEq
            dsimp only [] at hEq
            have hRec := ih headerFeats branchFeats cpu [elseB] hCpu hElseWt
            cases hk with
            | inl hk1 => subst hk1; exact hRec.1 hEq
            | inr hk23 =>
              cases hk23 with
              | inl hk2 => subst hk2; exact hRec.2.1 hEq
              | inr hk3 => subst hk3; exact hRec.2.2 hEq
          · rw [hG] at hEq
            dsimp only [] at hEq
            have hGProp : SubsetFeats guardReq cpu := subsetFeatsB_sound guardReq cpu hG
            have hThenCpu : SubsetFeats (headerFeats ++ (branchFeats ++ guardReq)) cpu :=
              SubsetFeats.append_intro
                (SubsetFeats.trans (SubsetFeats.append_left headerFeats branchFeats) hCpu)
                (SubsetFeats.append_intro
                  (SubsetFeats.trans (SubsetFeats.append_right headerFeats branchFeats) hCpu)
                  hGProp)
            have hRec := ih headerFeats (branchFeats ++ guardReq) cpu [thenB] hThenCpu hThenWt
            have hEq' : evalInsts spec prog cpu (headerFeats ++ (branchFeats ++ guardReq)) f' [thenB] = .fault k := by
              rw [← List.append_assoc]
              exact hEq
            cases hk with
            | inl hk1 => subst hk1; exact hRec.1 hEq'
            | inr hk23 =>
              cases hk23 with
              | inl hk2 => subst hk2; exact hRec.2.1 hEq'
              | inr hk3 => subst hk3; exact hRec.2.2 hEq'
      -- Lift head + tail fault-freedom to `evalInsts` on `inst :: rest`.
      dsimp only [evalInsts]
      cases hRes :
          (match inst with
          | .nop => ExecOutcome.ok 1
          | .alu => .ok 1
          | .vecOp req _ =>
            match subsetFeatsB req cpu with | true => .ok 1 | false => .fault .sigill
          | .safeCall cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .unsafeCall cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .reifySafeFnPtr tid =>
            match lookupFn prog.fns tid with | none => .fault .missingCallee | some _ => .ok 1
          | .reifyUnsafeFnPtr tid =>
            match lookupFn prog.fns tid with | none => .fault .missingCallee | some _ => .ok 1
          | .abiCall conv v cid =>
            match lookupFn prog.fns cid with
            | none => .fault .missingCallee
            | some callee =>
              match RegClass.beq (regClassFor spec conv (headerFeats ++ branchFeats) v)
                  (regClassFor spec conv callee.effectiveFeats v) with
              | false => .fault .abiMismatch
              | true =>
                let hreq := regClassHardwareReq (regClassFor spec conv (headerFeats ++ branchFeats) v)
                match subsetFeatsB hreq cpu with
                | false => .fault .sigill
                | true => evalInsts spec prog cpu callee.effectiveFeats f' callee.body
          | .seq first second =>
            evalInsts spec prog cpu (headerFeats ++ branchFeats) f' [first, second]
          | .guardedBranch guardReq thenB elseB =>
            match subsetFeatsB guardReq cpu with
            | true => evalInsts spec prog cpu ((headerFeats ++ branchFeats) ++ guardReq) f' [thenB]
            | false => evalInsts spec prog cpu (headerFeats ++ branchFeats) f' [elseB]) with
      | fault kf =>
        refine ⟨?_, ?_, ?_⟩ <;> intro hEq <;> cases hEq
        · exact hHeadSafe .sigill (Or.inl rfl) hRes
        · exact hHeadSafe .abiMismatch (Or.inr (Or.inl rfl)) hRes
        · exact hHeadSafe .missingCallee (Or.inr (Or.inr rfl)) hRes
      | ok s1 =>
        cases hTailRes : evalInsts spec prog cpu (headerFeats ++ branchFeats) f' rest with
        | fault kt =>
          refine ⟨?_, ?_, ?_⟩ <;> intro hEq <;> cases hEq
          · exact hTail.1 hTailRes
          · exact hTail.2.1 hTailRes
          · exact hTail.2.2 hTailRes
        | ok s2 =>
          refine ⟨?_, ?_, ?_⟩ <;> intro hEq <;> cases hEq

/-- Soundness of splicing a callee body `callee.body` into a caller at context
    `(headerFeats, branchFeats)`: when `SubsetFeats callee.effectiveFeats headerFeats` (superset
    inlining, preserving both `vecOp` legality AND safe-call/coercion checks), the spliced body
    remains `InstsWellTyped spec prog headerFeats branchFeats`! -/
theorem superset_inline_splice_preserves_well_typed
    (spec : TargetSpec) (pol : AttrPolicy) (prog : Program)
    (hTyped : SafeTf11Typed spec pol prog)
    (headerFeats branchFeats : FeatureSet) (callee : FnDef)
    (hMem : callee ∈ prog.fns)
    (hSuperset : SubsetFeats callee.effectiveFeats headerFeats) :
    InstsWellTyped spec prog headerFeats branchFeats callee.body := by
  have hTyped2 := hTyped
  dsimp only [SafeTf11Typed] at hTyped2
  have hCalleeWt := (hTyped2.2 callee hMem).2.2
  exact instsWellTyped_mono hSuperset (fun f hf => by cases hf) hCalleeWt

/-- Helper splicing a callee body at call index `n` when `callee.effectiveFeats ⊆ caller.effectiveFeats`. -/
noncomputable def inlineOneTopCallGo (prog : Program) (caller : FnDef) :
    List Inst → Nat → List Inst
  | [], _ => []
  | inst :: rest, 0 =>
    match inst with
    | .safeCall cid =>
      match lookupFn prog.fns cid with
      | some callee =>
        match subsetFeatsB callee.effectiveFeats caller.effectiveFeats with
        | true => callee.body ++ rest
        | false => inst :: rest
      | none => inst :: rest
    | .unsafeCall cid =>
      match lookupFn prog.fns cid with
      | some callee =>
        match subsetFeatsB callee.effectiveFeats caller.effectiveFeats with
        | true => callee.body ++ rest
        | false => inst :: rest
      | none => inst :: rest
    | _ => inst :: rest
  | inst :: rest, n + 1 => inst :: inlineOneTopCallGo prog caller rest n

/-- Replace a single `safeCall` or `unsafeCall` in a top-level instruction list with `callee.body`
    when `callee.effectiveFeats ⊆ caller.effectiveFeats` (modeling LLVM-style superset inlining). -/
noncomputable def inlineOneTopCall (prog : Program) (caller : FnDef) (targetIdx : Nat) : List Inst :=
  inlineOneTopCallGo prog caller caller.body targetIdx

/-- Apply `inlineOneTopCall` to function `callerId` in `prog`. -/
noncomputable def inlineProgramStep (prog : Program) (callerId callIdx : Nat) : Program :=
  { prog with
    fns := prog.fns.map fun fn =>
      match Nat.beq fn.id callerId with
      | true =>
        { fn with body := inlineOneTopCall prog fn callIdx }
      | false => fn }

theorem lookupFn_map_preserve_id (fns : List FnDef) (callerId callIdx : Nat) (prog : Program)
    (fid : Nat) (fn : FnDef)
    (h : lookupFn fns fid = some fn) :
    ∃ fn' : FnDef,
      lookupFn (fns.map fun f =>
        match Nat.beq f.id callerId with
        | true => { f with body := inlineOneTopCall prog f callIdx }
        | false => f) fid = some fn' ∧
      fn'.id = fn.id ∧
      fn'.safety = fn.safety ∧
      fn'.declaredFeats = fn.declaredFeats ∧
      fn'.effectiveFeats = fn.effectiveFeats ∧
      fn'.inlineAttr = fn.inlineAttr ∧
      fn'.isMain = fn.isMain ∧
      fn'.isTraitSafe = fn.isTraitSafe := by
  induction fns with
  | nil => cases h
  | cons x xs ih =>
    dsimp only [lookupFn] at h
    dsimp only [List.map, lookupFn]
    cases hEqId : Nat.beq x.id fid
    · rw [hEqId] at h
      have hSub : (match Nat.beq x.id callerId with
          | true => { x with body := inlineOneTopCall prog x callIdx }
          | false => x).id = x.id := by
        cases Nat.beq x.id callerId <;> rfl
      rw [hSub, hEqId]
      exact ih h
    · rw [hEqId] at h
      cases h
      have hSub : (match Nat.beq fn.id callerId with
          | true => { fn with body := inlineOneTopCall prog fn callIdx }
          | false => fn).id = fn.id := by
        cases Nat.beq fn.id callerId <;> rfl
      rw [hSub, hEqId]
      cases Nat.beq fn.id callerId
      · exact ⟨fn, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨{ fn with body := inlineOneTopCall prog fn callIdx },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem instWellTyped_map_inlined_fns (spec : TargetSpec) (prog : Program)
    (callerId callIdx : Nat) (h b : FeatureSet) (inst : Inst)
    (hwt : InstWellTyped spec prog h b inst) :
    InstWellTyped spec (inlineProgramStep prog callerId callIdx) h b inst := by
  induction inst generalizing b with
  | nop => trivial
  | alu => trivial
  | vecOp _ _ => exact hwt
  | safeCall cid =>
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c hrest =>
      cases hrest with
      | intro hc hce =>
        cases lookupFn_map_preserve_id prog.fns callerId callIdx prog cid c hc with
        | intro c' hc1 =>
          cases hc1 with
          | intro hc' hc2 =>
            cases hc2 with
            | intro _ hc3 =>
              cases hc3 with
              | intro _ hc4 =>
                cases hc4 with
                | intro _ hc5 =>
                  cases hc5 with
                  | intro heff _ =>
                    exact ⟨c', hc', by rw [heff]; exact hce⟩
  | unsafeCall cid =>
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c hrest =>
      cases hrest with
      | intro hc hce =>
        cases lookupFn_map_preserve_id prog.fns callerId callIdx prog cid c hc with
        | intro c' hc1 =>
          cases hc1 with
          | intro hc' hc2 =>
            cases hc2 with
            | intro _ hc3 =>
              cases hc3 with
              | intro _ hc4 =>
                cases hc4 with
                | intro _ hc5 =>
                  cases hc5 with
                  | intro heff _ =>
                    exact ⟨c', hc', by rw [heff]; exact hce⟩
  | reifySafeFnPtr tid =>
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro t hrest =>
      cases hrest with
      | intro ht hte =>
        cases lookupFn_map_preserve_id prog.fns callerId callIdx prog tid t ht with
        | intro t' ht1 =>
          cases ht1 with
          | intro ht' ht2 =>
            cases ht2 with
            | intro _ ht3 =>
              cases ht3 with
              | intro _ ht4 =>
                cases ht4 with
                | intro _ ht5 =>
                  cases ht5 with
                  | intro heff _ =>
                    exact ⟨t', ht', by rw [heff]; exact hte⟩
  | reifyUnsafeFnPtr tid =>
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro t ht =>
      cases lookupFn_map_preserve_id prog.fns callerId callIdx prog tid t ht with
      | intro t' ht1 =>
        cases ht1 with
        | intro ht' _ =>
          exact ⟨t', ht'⟩
  | abiCall conv v cid =>
    dsimp only [InstWellTyped] at hwt ⊢
    cases hwt with
    | intro c h1c =>
      cases h1c with
      | intro hc h2c =>
        cases h2c with
        | intro hce h3c =>
          cases h3c with
          | intro hcExtC hcRust =>
            cases lookupFn_map_preserve_id prog.fns callerId callIdx prog cid c hc with
            | intro c' hc1 =>
              cases hc1 with
              | intro hc' hc2 =>
                cases hc2 with
                | intro _ hc3 =>
                  cases hc3 with
                  | intro _ hc4 =>
                    cases hc4 with
                    | intro _ hc5 =>
                      cases hc5 with
                      | intro heff _ =>
                        refine ⟨c', hc', by rw [heff]; exact hce, ?_, hcRust⟩
                        intro hExt
                        rw [heff]
                        exact hcExtC hExt
  | seq first second ihF ihS =>
    dsimp only [InstWellTyped] at hwt ⊢
    exact ⟨ihF b hwt.1, ihS b hwt.2⟩
  | guardedBranch guardReq thenB elseB ihT ihE =>
    dsimp only [InstWellTyped] at hwt ⊢
    exact ⟨ihT (b ++ guardReq) hwt.1, ihE b hwt.2⟩

theorem inlineOneTopCall_go_preserves_well_typed
    (spec : TargetSpec) (pol : AttrPolicy) (prog : Program)
    (hTyped : SafeTf11Typed spec pol prog)
    (caller : FnDef) (insts : List Inst) (idx : Nat)
    (hWt : InstsWellTyped spec prog caller.effectiveFeats [] insts) :
    InstsWellTyped spec prog caller.effectiveFeats [] (inlineOneTopCallGo prog caller insts idx) := by
  induction insts generalizing idx with
  | nil =>
    cases idx <;> exact hWt
  | cons inst rest ih =>
    have hHead : InstWellTyped spec prog caller.effectiveFeats [] inst :=
      hWt inst (List.Mem.head rest)
    have hRest : InstsWellTyped spec prog caller.effectiveFeats [] rest :=
      fun j hj => hWt j (List.Mem.tail inst hj)
    cases idx with
    | zero =>
      dsimp only [inlineOneTopCallGo]
      cases inst with
      | safeCall cid =>
        dsimp only []
        cases hLook : lookupFn prog.fns cid with
        | none => exact hWt
        | some callee =>
          dsimp only []
          cases hSub : subsetFeatsB callee.effectiveFeats caller.effectiveFeats with
          | false => exact hWt
          | true =>
            dsimp only []
            have hCalleeMem := lookupFn_mem hLook
            have hCalleeWt := superset_inline_splice_preserves_well_typed
              spec pol prog hTyped caller.effectiveFeats [] callee hCalleeMem
              (subsetFeatsB_sound _ _ hSub)
            exact instsWellTyped_append hCalleeWt hRest
      | unsafeCall cid =>
        dsimp only []
        cases hLook : lookupFn prog.fns cid with
        | none => exact hWt
        | some callee =>
          dsimp only []
          cases hSub : subsetFeatsB callee.effectiveFeats caller.effectiveFeats with
          | false => exact hWt
          | true =>
            dsimp only []
            have hCalleeMem := lookupFn_mem hLook
            have hCalleeWt := superset_inline_splice_preserves_well_typed
              spec pol prog hTyped caller.effectiveFeats [] callee hCalleeMem
              (subsetFeatsB_sound _ _ hSub)
            exact instsWellTyped_append hCalleeWt hRest
      | nop | alu | vecOp _ _ | reifySafeFnPtr _ | reifyUnsafeFnPtr _
      | abiCall _ _ _ | seq _ _ | guardedBranch _ _ _ => exact hWt
    | succ k =>
      dsimp only [inlineOneTopCallGo]
      intro i hi
      cases hi with
      | head _ => exact hHead
      | tail _ htail => exact ih k hRest i htail

/-- One superset-inlining step preserves `SafeTf11Typed` across the entire program. -/
theorem inlineProgramStep_preserves_safe_tf11
    (spec : TargetSpec) (pol : AttrPolicy) (prog : Program)
    (hTyped : SafeTf11Typed spec pol prog)
    (callerId callIdx : Nat) :
    SafeTf11Typed spec pol (inlineProgramStep prog callerId callIdx) := by
  have hTyped0 := hTyped
  dsimp only [SafeTf11Typed] at hTyped0 ⊢
  constructor
  · cases hTyped0.1 with
    | intro entry hrest =>
      cases hrest with
      | intro hEntry hEntryBase =>
        cases lookupFn_map_preserve_id prog.fns callerId callIdx prog prog.entryId entry hEntry with
        | intro entry' he1 =>
          cases he1 with
          | intro hEntry' he2 =>
            cases he2 with
            | intro _ he3 =>
              cases he3 with
              | intro _ he4 =>
                cases he4 with
                | intro _ he5 =>
                  cases he5 with
                  | intro heff _ =>
                    exact ⟨entry', hEntry', by rw [heff]; exact hEntryBase⟩
  · intro fn' hMem'
    dsimp only [inlineProgramStep] at hMem'
    have hMap : ∀ (fns : List FnDef), fn' ∈ fns.map (fun f =>
        match Nat.beq f.id callerId with
        | true => { f with body := inlineOneTopCall prog f callIdx }
        | false => f) →
        (∀ x, x ∈ fns → AttrValid pol x ∧ EffectiveFeatsConsistent spec x ∧
          InstsWellTyped spec prog x.effectiveFeats [] x.body) →
        AttrValid pol fn' ∧ EffectiveFeatsConsistent spec fn' ∧
          InstsWellTyped spec (inlineProgramStep prog callerId callIdx) fn'.effectiveFeats [] fn'.body := by
      intro fns hmf hfwt
      induction fns with
      | nil => cases hmf
      | cons x xs ih =>
        dsimp only [List.map] at hmf
        cases hmf with
        | head _ =>
          have hx := hfwt x (List.Mem.head xs)
          cases hxid : Nat.beq x.id callerId
          · refine ⟨hx.1, hx.2.1, fun i hi =>
              instWellTyped_map_inlined_fns spec prog callerId callIdx x.effectiveFeats [] i (hx.2.2 i hi)⟩
          · dsimp only []
            refine ⟨hx.1, hx.2.1, ?_⟩
            intro i hi
            have hInl := inlineOneTopCall_go_preserves_well_typed spec pol prog hTyped x x.body callIdx hx.2.2
            exact instWellTyped_map_inlined_fns spec prog callerId callIdx x.effectiveFeats [] i (hInl i hi)
        | tail _ htail =>
          exact ih htail (fun z hz => hfwt z (List.Mem.tail x hz))
    exact hMap prog.fns hMem' hTyped0.2

/-- **Theorem 1 (`sigill_freedom_under_safe_tf11_and_superset_inline`):**
    Under `SafeTf11Typed spec pol prog` and baseline hardware support `SubsetFeats spec.baselineFeats cpu`,
    both `prog` and the transformed program after arbitrary finite superset-inlining steps
    never trigger `.sigill` or `.abiMismatch` at any execution fuel! -/
theorem sigill_freedom_under_safe_tf11_and_superset_inline
    (spec : TargetSpec) (pol : AttrPolicy) (prog : Program)
    (cpu : FeatureSet) (hCpuBase : SubsetFeats spec.baselineFeats cpu)
    (hTyped : SafeTf11Typed spec pol prog)
    (inlineSteps : List (Nat × Nat)) (fuel : Nat) :
    let prog' := inlineSteps.foldl (fun p st => inlineProgramStep p st.1 st.2) prog
    evalProgram spec prog' cpu fuel ≠ .fault .sigill ∧
    evalProgram spec prog' cpu fuel ≠ .fault .abiMismatch := by
  have hFoldTyped : ∀ (steps : List (Nat × Nat)) (p : Program),
      SafeTf11Typed spec pol p →
      SafeTf11Typed spec pol (steps.foldl (fun q st => inlineProgramStep q st.1 st.2) p) := by
    intro steps
    induction steps with
    | nil =>
      intro p hp
      exact hp
    | cons st rest ih =>
      intro p hp
      dsimp only [List.foldl]
      exact ih (inlineProgramStep p st.1 st.2)
        (inlineProgramStep_preserves_safe_tf11 spec pol p hp st.1 st.2)
  have hTyped' := hFoldTyped inlineSteps prog hTyped
  have hTyped2' := hTyped'
  dsimp only [SafeTf11Typed] at hTyped2'
  dsimp only [evalProgram]
  cases hTyped2'.1 with
  | intro entry hrest =>
    cases hrest with
    | intro hEntry hEntryBase =>
      rw [hEntry]
      have hMem := lookupFn_mem hEntry
      have hEntryWt := (hTyped2'.2 entry hMem).2.2
      have hEntryCpu : SubsetFeats (entry.effectiveFeats ++ []) cpu := by
        intro f hf
        cases memFeatB_append_cases entry.effectiveFeats [] hf with
        | inl ha => exact hCpuBase f (hEntryBase f ha)
        | inr hb => cases hb
      have hSafe := evalInsts_no_sigill_or_abi_fault spec pol
        (inlineSteps.foldl (fun p st => inlineProgramStep p st.1 st.2) prog)
        hTyped' fuel entry.effectiveFeats [] cpu entry.body hEntryCpu hEntryWt
      have hSafe' : evalInsts spec (inlineSteps.foldl (fun p st => inlineProgramStep p st.1 st.2) prog)
          cpu entry.effectiveFeats fuel entry.body ≠ .fault .sigill ∧
          evalInsts spec (inlineSteps.foldl (fun p st => inlineProgramStep p st.1 st.2) prog)
          cpu entry.effectiveFeats fuel entry.body ≠ .fault .abiMismatch := by
        constructor
        · intro he; exact hSafe.1 (by rw [List.append_nil]; exact he)
        · intro he; exact hSafe.2.1 (by rw [List.append_nil]; exact he)
      exact hSafe'

/-! ## Section 5: Constructive `target_feature_11` Rejections, MIR vs. LLVM Inlining, and `SIGILL` Counterexample -/

/-- Canonical leaf function with `#[target_feature(enable = "avx2")]` executing a 256-bit AVX2 op. -/
noncomputable def avx2LeafFn : FnDef :=
  { id := 1
    safety := .safe
    declaredFeats := [.avx2]
    effectiveFeats := [.sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx, .avx2]
    inlineAttr := .hint
    isMain := false
    isTraitSafe := false
    body := [.vecOp [.avx2] .w256] }

/-- Canonical leaf function with `#[target_feature(enable = "avx")]`. -/
noncomputable def avxLeafFn : FnDef :=
  { id := 2
    safety := .safe
    declaredFeats := [.avx]
    effectiveFeats := [.sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx]
    inlineAttr := .hint
    isMain := false
    isTraitSafe := false
    body := [.vecOp [.avx] .w256] }

/-- Baseline `#[inline(always)]` helper function (`declaredFeats = []`). -/
noncomputable def baselineAlwaysHelperFn : FnDef :=
  { id := 3
    safety := .safe
    declaredFeats := []
    effectiveFeats := [.sse, .sse2]
    inlineAttr := .always
    isMain := false
    isTraitSafe := false
    body := [.alu] }

/-- Reordered equal-set functions (`#[target_feature(enable = "avx2,bmi1")]` vs `"bmi1,avx2"`). -/
noncomputable def avx2Bmi1HelperFn : FnDef :=
  { id := 4
    safety := .safe
    declaredFeats := [.avx2, .bmi1]
    effectiveFeats := [.sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx, .avx2, .bmi1]
    inlineAttr := .hint
    isMain := false
    isTraitSafe := false
    body := [.vecOp [.avx2, .bmi1] .w256] }

noncomputable def bmi1Avx2CallerFn : FnDef :=
  { id := 5
    safety := .safe
    declaredFeats := [.bmi1, .avx2]
    effectiveFeats := [.sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx, .avx2, .bmi1]
    inlineAttr := .none
    isMain := false
    isTraitSafe := false
    body := [.safeCall 4] }

/-- Safe `#[target_feature(enable = "avx2")]` caller safely calling `avx2LeafFn`, `avxLeafFn`,
    `baselineAlwaysHelperFn`, and coercing `avx2LeafFn` to a safe `fn` pointer. -/
noncomputable def avx2CallerFn : FnDef :=
  { id := 6
    safety := .safe
    declaredFeats := [.avx2]
    effectiveFeats := [.sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx, .avx2]
    inlineAttr := .none
    isMain := false
    isTraitSafe := false
    body := [.safeCall 1, .safeCall 2, .safeCall 3, .reifySafeFnPtr 1] }

/-- Baseline `main` function safely guarding `avx2CallerFn` behind `is_x86_feature_detected!("avx2")`. -/
noncomputable def guardedMainFn : FnDef :=
  { id := 0
    safety := .safe
    declaredFeats := []
    effectiveFeats := [.sse, .sse2]
    inlineAttr := .none
    isMain := true
    isTraitSafe := false
    body := [.guardedBranch (impliedClosure [.avx2]) (.unsafeCall 6) .alu, .reifyUnsafeFnPtr 1] }

noncomputable def validTf11Prog : Program :=
  { fns := [guardedMainFn, avx2LeafFn, avxLeafFn, baselineAlwaysHelperFn,
            avx2Bmi1HelperFn, bmi1Avx2CallerFn, avx2CallerFn]
    entryId := 0 }

private theorem guardedMainFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 guardedMainFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem avx2LeafFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 avx2LeafFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem avxLeafFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 avxLeafFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem baselineAlwaysHelperFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 baselineAlwaysHelperFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem avx2Bmi1HelperFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 avx2Bmi1HelperFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem bmi1Avx2CallerFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 bmi1Avx2CallerFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem avx2CallerFn_eff :
    EffectiveFeatsConsistent x86_64Spec2026_11 avx2CallerFn :=
  ⟨subsetFeatsB_sound _ _ rfl, subsetFeatsB_sound _ _ rfl⟩

private theorem attrValid_mk {pol : AttrPolicy} {fn : FnDef}
    (h1 : fn.isMain = true → fn.declaredFeats = [])
    (h2 : fn.isTraitSafe = true → fn.declaredFeats = [])
    (h3 : pol.rejectTargetFeatureAlwaysInline = true → fn.declaredFeats ≠ [] → fn.inlineAttr ≠ .always) :
    AttrValid pol fn :=
  ⟨h1, h2, h3⟩

/-- Witness that `validTf11Prog` is `SafeTf11Typed` under `x86_64Spec2026_11` and `policy2026_11`! -/
theorem validTf11Prog_is_well_typed :
    SafeTf11Typed x86_64Spec2026_11 policy2026_11 validTf11Prog := by
  dsimp only [SafeTf11Typed]
  constructor
  · refine ⟨guardedMainFn, rfl, subsetFeatsB_sound _ _ rfl⟩
  · intro fn hMem
    cases hMem with
    | head _ =>
      refine ⟨attrValid_mk (fun _ => rfl) (fun h => by cases h) (fun h => by cases h),
        guardedMainFn_eff, ?_⟩
      intro i hi
      cases hi with
      | head _ =>
        dsimp only [InstWellTyped]
        exact ⟨⟨avx2CallerFn, rfl, subsetFeatsB_sound _ _ rfl⟩, trivial⟩
      | tail _ hi' => cases hi' with
        | head _ =>
          dsimp only [InstWellTyped]
          exact ⟨avx2LeafFn, rfl⟩
        | tail _ hi'' => cases hi''
    | tail _ h1 => cases h1 with
      | head _ =>
        refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
          avx2LeafFn_eff, ?_⟩
        intro i hi; cases hi with
        | head _ => exact subsetFeatsB_sound _ _ rfl
        | tail _ hi' => cases hi'
      | tail _ h2 => cases h2 with
        | head _ =>
          refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
            avxLeafFn_eff, ?_⟩
          intro i hi; cases hi with
          | head _ => exact subsetFeatsB_sound _ _ rfl
          | tail _ hi' => cases hi'
        | tail _ h3 => cases h3 with
          | head _ =>
            refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
              baselineAlwaysHelperFn_eff, ?_⟩
            intro i hi; cases hi with
            | head _ => trivial
            | tail _ hi' => cases hi'
          | tail _ h4 => cases h4 with
            | head _ =>
              refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
                avx2Bmi1HelperFn_eff, ?_⟩
              intro i hi; cases hi with
              | head _ => exact subsetFeatsB_sound _ _ rfl
              | tail _ hi' => cases hi'
            | tail _ h5 => cases h5 with
              | head _ =>
                refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
                  bmi1Avx2CallerFn_eff, ?_⟩
                intro i hi; cases hi with
                | head _ => exact ⟨avx2Bmi1HelperFn, rfl, subsetFeatsB_sound _ _ rfl⟩
                | tail _ hi' => cases hi'
              | tail _ h6 => cases h6 with
                | head _ =>
                  refine ⟨attrValid_mk (fun h => by cases h) (fun h => by cases h) (fun h => by cases h),
                    avx2CallerFn_eff, ?_⟩
                  intro i hi; cases hi with
                  | head _ => exact ⟨avx2LeafFn, rfl, subsetFeatsB_sound _ _ rfl⟩
                  | tail _ hi' => cases hi' with
                    | head _ => exact ⟨avxLeafFn, rfl, subsetFeatsB_sound _ _ rfl⟩
                    | tail _ hi'' => cases hi'' with
                      | head _ => exact ⟨baselineAlwaysHelperFn, rfl, subsetFeatsB_sound _ _ rfl⟩
                      | tail _ hi''' => cases hi''' with
                        | head _ => exact ⟨avx2LeafFn, rfl, subsetFeatsB_sound _ _ rfl⟩
                        | tail _ hi4 => cases hi4
                | tail _ h7 => cases h7

/-- Negative `target_feature_11` witnesses matching `E0133`, `E0308`, `main`, trait, and `#145574`. -/
theorem e0133_baseline_safe_call_avx2_rejected :
    ¬ InstWellTyped x86_64Spec2026_11 validTf11Prog [.sse, .sse2] [] (.safeCall 1) := by
  intro h
  dsimp only [InstWellTyped] at h
  cases h with
  | intro c hrest =>
    cases hrest with
    | intro hc hsub =>
      dsimp only [validTf11Prog, lookupFn] at hc
      cases hc
      have hmem := hsub .avx2 (by rfl)
      cases hmem

theorem e0308_baseline_safe_fn_ptr_coercion_rejected :
    ¬ InstWellTyped x86_64Spec2026_11 validTf11Prog [.sse, .sse2] [] (.reifySafeFnPtr 1) := by
  intro h
  dsimp only [InstWellTyped] at h
  cases h with
  | intro t hrest =>
    cases hrest with
    | intro ht hsub =>
      dsimp only [validTf11Prog, lookupFn] at ht
      cases ht
      have hmem := hsub .avx2 (by rfl)
      cases hmem

theorem non_subset_sse42_calls_avx2_rejected :
    ¬ InstWellTyped x86_64Spec2026_11 validTf11Prog [.sse, .sse2, .sse42] [] (.safeCall 1) := by
  intro h
  dsimp only [InstWellTyped] at h
  cases h with
  | intro c hrest =>
    cases hrest with
    | intro hc hsub =>
      dsimp only [validTf11Prog, lookupFn] at hc
      cases hc
      have hmem := hsub .avx2 (by rfl)
      cases hmem

theorem trait_and_main_target_feature_rejected :
    ¬ AttrValid policy2026_11 { avx2LeafFn with isMain := true } ∧
    ¬ AttrValid policy2026_11 { avx2LeafFn with isTraitSafe := true } := by
  constructor
  · intro h
    dsimp only [AttrValid] at h
    have he := h.1 rfl
    cases he
  · intro h
    dsimp only [AttrValid] at h
    have he := h.2.1 rfl
    cases he

/-- `2026-09` (`policy2026_09`) vs `2026-11` (`policy2026_11`) on `#[inline(always)]` + `#[target_feature]`. -/
noncomputable def tfInlineAlwaysFn : FnDef :=
  { avx2LeafFn with id := 7, inlineAttr := .always }

theorem attr_policy_2026_09_rejects_inline_always_2026_11_accepts :
    ¬ AttrValid policy2026_09 tfInlineAlwaysFn ∧
    AttrValid policy2026_11 tfInlineAlwaysFn := by
  constructor
  · intro h
    dsimp only [AttrValid] at h
    have hne : tfInlineAlwaysFn.declaredFeats ≠ [] := fun hc => by cases hc
    exact h.2.2 rfl hne rfl
  · exact attrValid_mk (fun hc => by cases hc) (fun hc => by cases hc) (fun hc => by cases hc)

/-! ### MIR `Inline` vs LLVM `areInlineCompatible` Refinement & Counterexamples -/

/-- Whether MIR `Inline` (`compiler/rustc_mir_transform/src/inline.rs:840-842`) permits inlining
    `callee` into `caller`: checks strict ordered sequence equality `seqEqFeatsB` on
    `declaredFeats` (when `inlineAttr ≠ .never` and caller/callee match). -/
noncomputable def mirCanInline (caller callee : FnDef) : Bool :=
  seqEqFeatsB callee.declaredFeats caller.declaredFeats

/-- Whether a single instruction contains any internal `abiCall` whose `RegClass` changes
    when relocated from `calleeFeats` to `callerFeats` (modeling `X86TTIImpl::areTypesABICompatible`
    in `llvm/lib/Target/X86/X86TargetTransformInfo.cpp:6808-6855`). -/
noncomputable def allInternalCallsAbiCompatInst (spec : TargetSpec)
    (callerFeats calleeFeats : FeatureSet) : Inst → Bool
  | .abiCall conv v _ =>
    RegClass.beq (regClassFor spec conv callerFeats v) (regClassFor spec conv calleeFeats v)
  | .seq first second =>
    allInternalCallsAbiCompatInst spec callerFeats calleeFeats first &&
    allInternalCallsAbiCompatInst spec callerFeats calleeFeats second
  | .guardedBranch _ thenB elseB =>
    allInternalCallsAbiCompatInst spec callerFeats calleeFeats thenB &&
    allInternalCallsAbiCompatInst spec callerFeats calleeFeats elseB
  | _ => true

/-- Whether an instruction list `body` passes internal-call ABI compatibility checking. -/
noncomputable def allInternalCallsAbiCompat (spec : TargetSpec)
    (callerFeats calleeFeats : FeatureSet) : List Inst → Bool
  | [] => true
  | inst :: rest =>
    allInternalCallsAbiCompatInst spec callerFeats calleeFeats inst &&
    allInternalCallsAbiCompat spec callerFeats calleeFeats rest

/-- LLVM `X86TTIImpl::areInlineCompatible` (`X86TargetTransformInfo.cpp:6782-6833` +
    `InlineCost.cpp:3203-3206`): requires monotone subset `callee.effectiveFeats ⊆ caller.effectiveFeats`
    AND internal-call ABI compatibility (enforced even on `alwaysinline`!). -/
noncomputable def llvmCanInline (spec : TargetSpec) (caller callee : FnDef) : Bool :=
  subsetFeatsB callee.effectiveFeats caller.effectiveFeats &&
  allInternalCallsAbiCompat spec caller.effectiveFeats callee.effectiveFeats callee.body

theorem allInternalCallsAbiCompatInst_of_setEq (spec : TargetSpec)
    (f1 f2 : FeatureSet) (hEq : SetEqFeats f1 f2) (inst : Inst) :
    allInternalCallsAbiCompatInst spec f1 f2 inst = true := by
  induction inst with
  | nop | alu | vecOp _ _ | safeCall _ | unsafeCall _
  | reifySafeFnPtr _ | reifyUnsafeFnPtr _ => rfl
  | abiCall conv v _ =>
    dsimp only [allInternalCallsAbiCompatInst]
    apply (RegClass.beq_iff_eq _ _).2
    cases conv with
    | externRust =>
      cases v with
      | m128 =>
        cases spec with
        | mk _ _ r => cases r <;> rfl
      | m256 => rfl
      | m512 => rfl
      | wrap256 => rfl
    | externC =>
      have hsse : memFeatB .sse f1 = memFeatB .sse f2 := by
        cases h1 : memFeatB .sse f1 <;> cases h2 : memFeatB .sse f2
        · rfl
        · have c := hEq.2 .sse h2; dsimp only [MemFeat] at c; rw [h1] at c; cases c
        · have c := hEq.1 .sse h1; dsimp only [MemFeat] at c; rw [h2] at c; cases c
        · rfl
      have havx : memFeatB .avx f1 = memFeatB .avx f2 := by
        cases h1 : memFeatB .avx f1 <;> cases h2 : memFeatB .avx f2
        · rfl
        · have c := hEq.2 .avx h2; dsimp only [MemFeat] at c; rw [h1] at c; cases c
        · have c := hEq.1 .avx h1; dsimp only [MemFeat] at c; rw [h2] at c; cases c
        · rfl
      have havx512 : memFeatB .avx512f f1 = memFeatB .avx512f f2 := by
        cases h1 : memFeatB .avx512f f1 <;> cases h2 : memFeatB .avx512f f2
        · rfl
        · have c := hEq.2 .avx512f h2; dsimp only [MemFeat] at c; rw [h1] at c; cases c
        · have c := hEq.1 .avx512f h1; dsimp only [MemFeat] at c; rw [h2] at c; cases c
        · rfl
      cases v <;> dsimp only [regClassFor, passModeFor]
      · rw [hsse]
      · rw [havx]
      · rw [havx512]
      · rw [havx]
  | seq first second ihF ihS =>
    dsimp only [allInternalCallsAbiCompatInst]
    rw [ihF, ihS]
    rfl
  | guardedBranch _ thenB elseB ihT ihE =>
    dsimp only [allInternalCallsAbiCompatInst]
    rw [ihT, ihE]
    rfl

theorem allInternalCallsAbiCompat_of_setEq (spec : TargetSpec)
    (f1 f2 : FeatureSet) (hEq : SetEqFeats f1 f2) (body : List Inst) :
    allInternalCallsAbiCompat spec f1 f2 body = true := by
  induction body with
  | nil => rfl
  | cons inst rest ih =>
    dsimp only [allInternalCallsAbiCompat]
    rw [allInternalCallsAbiCompatInst_of_setEq spec f1 f2 hEq inst, ih]
    rfl

/-- **Theorem 3 (`mir_inline_refines_llvm_subset_inline`):**
    Whenever MIR `Inline` admits inlining `callee` into `caller` (`mirCanInline = true`) and
    both functions satisfy `EffectiveFeatsConsistent`, LLVM `areInlineCompatible` also admits
    the inline (`llvmCanInline = true`) — even when `callee.body` contains ABI-sensitive calls! -/
theorem mir_inline_refines_llvm_subset_inline
    (spec : TargetSpec) (caller callee : FnDef)
    (hCallerEff : EffectiveFeatsConsistent spec caller)
    (hCalleeEff : EffectiveFeatsConsistent spec callee)
    (hMir : mirCanInline caller callee = true) :
    llvmCanInline spec caller callee = true := by
  have hDeclEq : callee.declaredFeats = caller.declaredFeats := eq_of_seqEqFeatsB_true hMir
  have hEffEq : SetEqFeats caller.effectiveFeats callee.effectiveFeats := by
    have hImpEq : impliedClosure callee.declaredFeats = impliedClosure caller.declaredFeats := by
      rw [hDeclEq]
    constructor
    · exact SubsetFeats.trans hCallerEff.1 (by rw [← hImpEq]; exact hCalleeEff.2)
    · exact SubsetFeats.trans hCalleeEff.1 (by rw [hImpEq]; exact hCallerEff.2)
  dsimp only [llvmCanInline]
  have hSubB : subsetFeatsB callee.effectiveFeats caller.effectiveFeats = true :=
    subsetFeatsB_complete _ _ hEffEq.2
  have hCompatB : allInternalCallsAbiCompat spec caller.effectiveFeats callee.effectiveFeats callee.body = true :=
    allInternalCallsAbiCompat_of_setEq spec caller.effectiveFeats callee.effectiveFeats hEffEq callee.body
  rw [hSubB, hCompatB]
  rfl

/-- Three constructive strictness separations where LLVM inlines cleanly while MIR `Inline` refuses:
    (a) proper feature subset (`avx` into `avx2`),
    (b) baseline helper (`[]`) into `avx2`,
    (c) equal feature set in reversed attribute order (`"avx2,bmi1"` into `"bmi1,avx2"`). -/
theorem llvm_strictly_coarser_than_mir_three_witnesses :
    (mirCanInline avx2CallerFn avxLeafFn = false ∧
     llvmCanInline x86_64Spec2026_11 avx2CallerFn avxLeafFn = true) ∧
    (mirCanInline avx2CallerFn baselineAlwaysHelperFn = false ∧
     llvmCanInline x86_64Spec2026_11 avx2CallerFn baselineAlwaysHelperFn = true) ∧
    (mirCanInline bmi1Avx2CallerFn avx2Bmi1HelperFn = false ∧
     llvmCanInline x86_64Spec2026_11 bmi1Avx2CallerFn avx2Bmi1HelperFn = true) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- In `2026-11` (`policy2026_11`), `tfInlineAlwaysFn` (`#[inline(always)]` + `avx2`) is inlined by
    LLVM into `avx2CallerFn` while blocked in `guardedMainFn` (keeping `tail call` in baseline). -/
theorem llvm_2026_11_alwaysinline_subset_gate :
    llvmCanInline x86_64Spec2026_11 avx2CallerFn tfInlineAlwaysFn = true ∧
    llvmCanInline x86_64Spec2026_11 guardedMainFn tfInlineAlwaysFn = false := by
  exact ⟨rfl, rfl⟩

/-- Mechanization of `compiler/rustc_mir_transform/src/inline.rs:843-847` and
    `X86TTIImpl::areTypesABICompatible` (`X86TargetTransformInfo.cpp:6808-6855`):
    if a baseline callee contains an `extern "C"` call passing `__m256`, moving that call into
    an `+avx2` caller changes its `RegClass` (`splitOrStack .w256` -> `ymm256`), so LLVM
    rejects even that subset-inlining (`llvmCanInline = false`)! -/
noncomputable def baselineAbiSensitiveHelperFn : FnDef :=
  { id := 8
    safety := .unsafeFn
    declaredFeats := []
    effectiveFeats := [.sse, .sse2]
    inlineAttr := .hint
    isMain := false
    isTraitSafe := false
    body := [.abiCall .externC .m256 99] }

theorem llvm_rejects_abi_shifting_subset_inline :
    SubsetFeats baselineAbiSensitiveHelperFn.effectiveFeats avx2CallerFn.effectiveFeats ∧
    allInternalCallsAbiCompat x86_64Spec2026_11
      avx2CallerFn.effectiveFeats baselineAbiSensitiveHelperFn.effectiveFeats
      baselineAbiSensitiveHelperFn.body = false ∧
    llvmCanInline x86_64Spec2026_11 avx2CallerFn baselineAbiSensitiveHelperFn = false := by
  refine ⟨subsetFeatsB_sound _ _ rfl, rfl, rfl⟩

/-- **Theorem 2 (`baseline_caller_inlining_violates_sigill_freedom`):**
    Unsoundly inlining (or hoisting) `avx2LeafFn` (`#[target_feature(enable = "avx2")]`) into
    baseline `guardedMainFn` (e.g., if `alwaysinline` ignored `areInlineCompatible` and hoisted
    `.vecOp [.avx2] .w256` before the runtime CPU guard) breaks `InstsWellTyped` and triggers
    `.fault .sigill` when executed on a baseline x86-64 CPU (`[.sse, .sse2]`) — whereas the
    un-inlined source program `validTf11Prog` executes cleanly to `.ok`! -/
noncomputable def unsafeUnconditionallyInlinedMainFn : FnDef :=
  { guardedMainFn with
    body := avx2LeafFn.body ++ guardedMainFn.body }

noncomputable def unsoundlyInlinedProg : Program :=
  { fns := [unsafeUnconditionallyInlinedMainFn, avx2LeafFn]
    entryId := 0 }

theorem baseline_caller_inlining_violates_sigill_freedom :
    (evalProgram x86_64Spec2026_11 validTf11Prog [.sse, .sse2] 16 = .ok 2) ∧
    (¬ InstsWellTyped x86_64Spec2026_11 unsoundlyInlinedProg
      unsafeUnconditionallyInlinedMainFn.effectiveFeats [] unsafeUnconditionallyInlinedMainFn.body) ∧
    (evalProgram x86_64Spec2026_11 unsoundlyInlinedProg [.sse, .sse2] 16 = .fault .sigill) := by
  refine ⟨rfl, ?_, rfl⟩
  intro hwt
  have hHead := hwt (.vecOp [.avx2] .w256) (List.Mem.head _)
  have hmem := hHead .avx2 (by rfl)
  cases hmem

end TargetFeatureInliningAndSimdAbi
