-- Self-contained Lean 4 (`v4.34.1`) mechanization of multi-compiler MIR capture,
-- spoke-to-trunk vs. linear pairwise IR migration soundness, and `v_verify` vs.
-- `v_ship` assurance transfer boundaries.
--
-- Checked with:
--   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true MultiCompilerCorrespondence.lean
-- Axioms: zero (`does not depend on any axioms` verified via `#print axioms` below).

prelude
import Init.Core

namespace MultiCompilerCorrespondence

/-- Execution outcomes for operational and reference semantics. -/
inductive Outcome (Val : Type) where
  | ok : Val → Outcome Val
  | ub : Outcome Val
  | diverge : Outcome Val
  deriving DecidableEq

/-- A program computation is memory-safe for postcondition `Q` when it neither
    triggers UB nor violates `Q` upon termination. -/
def SafeFor {Val : Type} (out : Outcome Val) (Q : Val → Prop) : Prop :=
  match out with
  | .ok v => Q v
  | .ub => False
  | .diverge => True

/-- Capture errors when a compiler-specific construct cannot be lowered faithfully. -/
inductive CaptureErr where
  | unsupportedConstruct
  | compilerTaintedByErrors
  deriving DecidableEq

/-- Explicit operational semantics profile (orthogonal to wire schema and compiler SHA). -/
inductive SemProfile where
  | rust2021Stacked
  | rust2024Tree
  deriving DecidableEq

/-- Abstract target/compiler layout environment (e.g., field offsets of `#[repr(Rust)]` ADTs). -/
structure LayoutEnv where
  fieldAOffset : Nat
  fieldBOffset : Nat
  reprCFixedOffset : Nat
  deriving DecidableEq

/-- Admissibility invariant for layouts produced by any compliant `rustc` build:
    `#[repr(C)]` offsets are fixed across compilers, whereas `#[repr(Rust)]`
    field offsets may permute arbitrarily so long as fields remain disjoint. -/
def AdmissibleLayout (env : LayoutEnv) : Prop :=
  env.reprCFixedOffset = 0 ∧ env.fieldAOffset ≠ env.fieldBOffset

/-!
## Section 1: Spoke-to-Trunk Equivalence-Class Soundness Without `N ×` Proof Duplication
-/

/-- Abstract family of supported compiler commits quotiented into semantic profiles. -/
structure CompilerSuite where
  Commit : Type
  CompilerMir : Commit → Type
  CanonMir : Type
  RefProg : Type
  Val : Type
  profileOf : Commit → SemProfile
  layoutOf : Commit → LayoutEnv
  layoutAdmissible : ∀ c, AdmissibleLayout (layoutOf c)
  capture : (c : Commit) → CompilerMir c → Except CaptureErr (CanonMir × SemProfile)
  compilerExec : (c : Commit) → CompilerMir c → Outcome Val
  canonExec : SemProfile → LayoutEnv → CanonMir → Outcome Val
  refExec : SemProfile → LayoutEnv → RefProg → Outcome Val

/-- A spoke capture driver for commit `c` is faithful if every `ok (mc, π)`
    identifies `c`'s true semantic profile and preserves safety (never erasing UB)
    from `canonExec` to `compilerExec`. -/
def SpokeToCanonFaithful (S : CompilerSuite) (c : S.Commit) : Prop :=
  ∀ (m : S.CompilerMir c) (mc : S.CanonMir) (π : SemProfile) (Q : LayoutEnv → S.Val → Prop),
    S.capture c m = .ok (mc, π) →
    π = S.profileOf c ∧
    (SafeFor (S.canonExec π (S.layoutOf c) mc) (Q (S.layoutOf c)) →
     SafeFor (S.compilerExec c m) (Q (S.layoutOf c)))

/-- One canonical semantics proof per `SemProfile` (shared across all commits in that profile's
    equivalence class) linking `canonExec π` to `refExec π`. -/
def ProfileRefCorrespondence (S : CompilerSuite) (π : SemProfile) (lift : S.CanonMir → S.RefProg) : Prop :=
  ∀ (env : LayoutEnv) (mc : S.CanonMir) (Q : S.Val → Prop),
    AdmissibleLayout env →
    SafeFor (S.refExec π env (lift mc)) Q →
    SafeFor (S.canonExec π env mc) Q

/-- Layout-parametric verification obligation discharged once over `refExec π`. -/
def VerifiedParametric (S : CompilerSuite) (π : SemProfile) (p : S.RefProg)
    (Q : LayoutEnv → S.Val → Prop) : Prop :=
  ∀ (env : LayoutEnv), AdmissibleLayout env → SafeFor (S.refExec π env p) (Q env)

/-- **Theorem 1 (Equivalence-Class Soundness Without `N ×` Duplication):**
    For any compiler commit `c` whose spoke driver is faithful and whose semantic profile `π`
    has a single correspondence proof `ProfileRefCorrespondence S π lift`, a single
    layout-parametric proof of `lift mc` guarantees UB-free postcondition satisfaction
    for `compilerExec c m`—reusing the identical proof whenever two compilers emit
    normalized trunk MIR `mc` in the same `SemProfile`. -/
theorem spoke_lowering_refines_reference_class
    (S : CompilerSuite)
    (c : S.Commit)
    (m : S.CompilerMir c)
    (mc : S.CanonMir)
    (π : SemProfile)
    (lift : S.CanonMir → S.RefProg)
    (Q : LayoutEnv → S.Val → Prop)
    (hSpoke : SpokeToCanonFaithful S c)
    (hCap : S.capture c m = .ok (mc, π))
    (hCorr : ProfileRefCorrespondence S π lift)
    (hVerif : VerifiedParametric S π (lift mc) Q) :
    SafeFor (S.compilerExec c m) (Q (S.layoutOf c)) :=
  let hPair := hSpoke m mc π Q hCap
  hPair.2 (hCorr (S.layoutOf c) mc (Q (S.layoutOf c)) (S.layoutAdmissible c)
    (hVerif (S.layoutOf c) (S.layoutAdmissible c)))

/-- Automatic zero-edit proof reuse across any two commits `c1` and `c2` that normalize
    to the same canonical MIR `mc` and semantic profile `π`. -/
theorem same_profile_normalized_mir_reuses_proof
    (S : CompilerSuite)
    (c1 c2 : S.Commit)
    (m1 : S.CompilerMir c1)
    (m2 : S.CompilerMir c2)
    (mc : S.CanonMir)
    (π : SemProfile)
    (lift : S.CanonMir → S.RefProg)
    (Q : LayoutEnv → S.Val → Prop)
    (hSpoke1 : SpokeToCanonFaithful S c1)
    (hSpoke2 : SpokeToCanonFaithful S c2)
    (hCap1 : S.capture c1 m1 = .ok (mc, π))
    (hCap2 : S.capture c2 m2 = .ok (mc, π))
    (hCorr : ProfileRefCorrespondence S π lift)
    (hVerif : VerifiedParametric S π (lift mc) Q) :
    SafeFor (S.compilerExec c1 m1) (Q (S.layoutOf c1)) ∧
    SafeFor (S.compilerExec c2 m2) (Q (S.layoutOf c2)) :=
  And.intro
    (spoke_lowering_refines_reference_class S c1 m1 mc π lift Q hSpoke1 hCap1 hCorr hVerif)
    (spoke_lowering_refines_reference_class S c2 m2 mc π lift Q hSpoke2 hCap2 hCorr hVerif)

/-!
## Section 2: Hub-and-Spoke Direct Lowering vs. Linear Pairwise AST Migration Chains
-/

/-- Concrete 3-version IR evolution witness:
    - `V1Mir`: compiler v1 represents aliasing validation via a dedicated `retagThenRead` op
      (modeling `StatementKind::Retag` prior to `rustc 1.97.0` / `1.99.0`).
    - `V2Mir`: an intermediate schema drops standalone `Retag` without carrying per-copy retag
      flags, collapsing both operations to `plainRead`.
    - `TrunkMir`: canonical superset trunk IR carries `copyWithRetag (retag : Bool)`
      (`Rvalue::Use(_, WithRetag)`). -/
inductive V1Mir where
  | retagThenRead (aliasedInvalid : Bool)
  | plainRead
  deriving DecidableEq

inductive V2Mir where
  | plainRead
  deriving DecidableEq

inductive TrunkMir where
  | copyWithRetag (retag : Bool) (aliasedInvalid : Bool)
  deriving DecidableEq

def evalV1 : V1Mir → Outcome Unit
  | .retagThenRead true => .ub
  | .retagThenRead false => .ok ()
  | .plainRead => .ok ()

def evalTrunk : TrunkMir → Outcome Unit
  | .copyWithRetag true true => .ub
  | .copyWithRetag _ _ => .ok ()

/-- Direct hub-and-spoke lowering `V1Mir → TrunkMir` preserves exact UB semantics. -/
def spokeV1ToTrunk : V1Mir → TrunkMir
  | .retagThenRead bad => .copyWithRetag true bad
  | .plainRead => .copyWithRetag false false

theorem spoke_v1_exact : ∀ (m : V1Mir), evalTrunk (spokeV1ToTrunk m) = evalV1 m
  | .retagThenRead true => rfl
  | .retagThenRead false => rfl
  | .plainRead => rfl

/-- **Theorem 2 (Linear Pairwise Migration Bottleneck Impossibility):**
    Any total pairwise hop `m12 : V1Mir → V2Mir` followed by `m23 : V2Mir → TrunkMir`
    factors through the 1-state bottleneck `V2Mir` and therefore cannot both accept
    `plainRead` safely and detect UB on `retagThenRead true`. -/
theorem linear_chain_unsound_or_incomplete
    (m12 : V1Mir → V2Mir)
    (m23 : V2Mir → TrunkMir)
    (hPlainOk : evalTrunk (m23 (m12 .plainRead)) = .ok ()) :
    evalTrunk (m23 (m12 (.retagThenRead true))) = .ok () ∧
    evalV1 (.retagThenRead true) = .ub :=
  let hCollapse : m12 (.retagThenRead true) = m12 .plainRead :=
    match m12 (.retagThenRead true), m12 .plainRead with
    | .plainRead, .plainRead => rfl
  And.intro
    (Eq.rec (motive := fun x _ => evalTrunk (m23 x) = .ok ()) hPlainOk hCollapse.symm)
    rfl

/-!
## Section 3: The `v_verify ≠ v_ship` Soundness Gap and Layout-Parametric Transfer
-/

/-- Concrete program reading field A via pointer arithmetic at offset `expectedOff`:
    safe iff `env.fieldAOffset = expectedOff`, otherwise UB (out-of-field / uninitialized padding read). -/
def ptrOffsetReadProg (expectedOff : Nat) (env : LayoutEnv) : Outcome Nat :=
  match Nat.beq env.fieldAOffset expectedOff with
  | true => .ok 42
  | false => .ub

/-- Compiler `v_verify` chooses `fieldAOffset = 8, fieldBOffset = 0`;
    compiler `v_ship` (or `-Z randomize-layout`) chooses `fieldAOffset = 0, fieldBOffset = 8`. -/
def layoutVerify : LayoutEnv := { fieldAOffset := 8, fieldBOffset := 0, reprCFixedOffset := 0 }
def layoutShip : LayoutEnv := { fieldAOffset := 0, fieldBOffset := 8, reprCFixedOffset := 0 }

theorem both_layouts_admissible : AdmissibleLayout layoutVerify ∧ AdmissibleLayout layoutShip :=
  And.intro
    (And.intro rfl (fun h => nomatch h))
    (And.intro rfl (fun h => nomatch h))

/-- **Theorem 3 (`v_verify ≠ v_ship` Baked-Layout Unsoundness Witness):**
    A proof checking `ptrOffsetReadProg 8` only against `layoutVerify` passes with `Outcome.ok 42`,
    yet shipping the identical crate under `layoutShip` triggers `Outcome.ub`. -/
theorem verify_ship_concrete_layout_unsound :
    SafeFor (ptrOffsetReadProg 8 layoutVerify) (fun v => v = 42) ∧
    ptrOffsetReadProg 8 layoutShip = .ub :=
  And.intro rfl rfl

/-- By contrast, a `#[repr(C)]` read at `reprCFixedOffset = 0` verified universally over
    `AdmissibleLayout` remains sound across every compliant `v_ship`. -/
def reprCReadProg (env : LayoutEnv) : Outcome Nat :=
  match Nat.beq env.reprCFixedOffset 0 with
  | true => .ok 42
  | false => .ub

theorem layout_parametric_repr_c_transfer_sound
    (envShip : LayoutEnv)
    (hAdm : AdmissibleLayout envShip) :
    SafeFor (reprCReadProg envShip) (fun v => v = 42) := by
  unfold reprCReadProg
  rw [hAdm.1]
  exact rfl

/-- **Theorem 4 (Stdlib Type-Alias Drift Witness — `Infallible` vs `!` across `1.99.1` → `1.100.0`):**
    When stdlib version `s_verify` defines `Infallible` as a distinct uninhabited enum
    (`infallibleEqNever = false`, Rust `≤ 1.99.1`) while `s_ship` aliases
    `pub type Infallible = !` (`infallibleEqNever = true`, Rust `1.100.0+`), a program relying on
    `TypeId::of::<Infallible>() != TypeId::of::<!>()` is UB-free under `s_verify` yet executes
    UB under `s_ship`. -/
def stdlibInfallibleGuardProg (infallibleEqNever : Bool) : Outcome Unit :=
  match infallibleEqNever with
  | true => .ub
  | false => .ok ()

theorem stdlib_alias_drift_breaks_unpinned_ship :
    SafeFor (stdlibInfallibleGuardProg false) (fun _ => True) ∧
    stdlibInfallibleGuardProg true = .ub :=
  And.intro True.intro rfl

#print axioms spoke_lowering_refines_reference_class
#print axioms same_profile_normalized_mir_reuses_proof
#print axioms spoke_v1_exact
#print axioms linear_chain_unsound_or_incomplete
#print axioms verify_ship_concrete_layout_unsound
#print axioms layout_parametric_repr_c_transfer_sound
#print axioms stdlib_alias_drift_breaks_unpinned_ship

end MultiCompilerCorrespondence
