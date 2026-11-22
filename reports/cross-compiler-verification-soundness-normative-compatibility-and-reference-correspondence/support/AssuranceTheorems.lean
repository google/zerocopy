-- Self-contained Lean 4 (`v4.34.1`) mechanization of multi-compiler reference
-- correspondence, target/machdep parameterization, `v_verify != v_ship` soundness
-- boundaries, and two-tier compiler-identity provenance gating (`pinnedVerified` vs.
-- `unverifiedCompiler`).
--
-- Checked with:
--   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true AssuranceTheorems.lean
-- Axioms: zero (`does not depend on any axioms` verified via `#print axioms` below).

prelude
import Init.Core

namespace AssuranceTheorems

/-- Execution outcomes for operational, canonical, and reference semantics. -/
inductive Outcome (Val : Type) where
  | ok : Val → Outcome Val
  | ub : Outcome Val
  | diverge : Outcome Val
  deriving DecidableEq

/-- Partial-correctness safety with mandatory UB exclusion (nonfailure reflection). -/
def SafeFor {Val : Type} (out : Outcome Val) (Q : Val → Prop) : Prop :=
  match out with
  | .ok v => Q v
  | .ub => False
  | .diverge => True

/-- Capture errors when a compiler-specific construct or compiler error state is rejected. -/
inductive CaptureErr where
  | unsupportedConstruct
  | compilerTaintedByErrors
  deriving DecidableEq

/-- Explicit operational semantics profile (quotienting compiler versions into `K << N` classes). -/
inductive SemProfile where
  | rust2021InfallibleEnumStacked
  | rust2021InfallibleNeverStacked
  | rust2024InfallibleNeverTree
  deriving DecidableEq

/-- Exact compiler/toolchain identity tuple `(compilerCommit, binarySha256, sysrootSha256,
    targetTriple, flagsDigest)` required to bind `v_verify` to `v_ship`. -/
structure ToolchainIdentity (Hash : Type) where
  compilerCommit : Hash
  binarySha256 : Hash
  sysrootSha256 : Hash
  targetTriple : Hash
  flagsDigest : Hash
  deriving DecidableEq

/-- Target + compiler ABI/layout parameterization (`Archi` / `machdep` / `.atp` / `LayoutEnv`). -/
structure TargetLayoutEnv where
  ptrWidthBits : Nat
  littleEndian : Bool
  reprCFixedOffset : Nat
  reprRustFieldAOffset : Nat
  reprRustFieldBOffset : Nat
  infallibleEqNever : Bool
  deriving DecidableEq

/-- Admissibility contract for a fixed target (`x86_64`, little-endian) under a given
    `SemProfile`: target ABI constants and `#[repr(C)]` offsets are fixed, `#[repr(Rust)]`
    fields remain disjoint but may permute across compilers/seeds, and stdlib type-identity
    matches the declared `SemProfile`. -/
def AdmissibleEnvForProfile (π : SemProfile) (env : TargetLayoutEnv) : Prop :=
  env.ptrWidthBits = 64 ∧
  env.littleEndian = true ∧
  env.reprCFixedOffset = 0 ∧
  env.reprRustFieldAOffset ≠ env.reprRustFieldBOffset ∧
  env.infallibleEqNever =
    match π with
    | .rust2021InfallibleEnumStacked => false
    | .rust2021InfallibleNeverStacked => true
    | .rust2024InfallibleNeverTree => true

/-- Abstract multi-compiler verification suite across exact toolchain identities. -/
structure CompilerSuite where
  Hash : Type
  CompilerMir : ToolchainIdentity Hash → Type
  CanonMir : Type
  RefProg : Type
  Val : Type
  isRegisteredVerifiedToolchain : ToolchainIdentity Hash → Bool
  profileOf : ToolchainIdentity Hash → SemProfile
  envOf : ToolchainIdentity Hash → TargetLayoutEnv
  envAdmissible : ∀ tc, isRegisteredVerifiedToolchain tc = true →
    AdmissibleEnvForProfile (profileOf tc) (envOf tc)
  capture : (tc : ToolchainIdentity Hash) → CompilerMir tc → Except CaptureErr (CanonMir × SemProfile)
  compilerExec : (tc : ToolchainIdentity Hash) → CompilerMir tc → Outcome Val
  canonExec : SemProfile → TargetLayoutEnv → CanonMir → Outcome Val
  refExec : SemProfile → TargetLayoutEnv → RefProg → Outcome Val

/-- Spoke-to-canonical lowering faithfulness for a registered toolchain `tc`. -/
def SpokeFaithful (S : CompilerSuite) (tc : ToolchainIdentity S.Hash) : Prop :=
  ∀ (m : S.CompilerMir tc) (mc : S.CanonMir) (π : SemProfile) (Q : TargetLayoutEnv → S.Val → Prop),
    S.capture tc m = .ok (mc, π) →
    π = S.profileOf tc ∧
    (SafeFor (S.canonExec π (S.envOf tc) mc) (Q (S.envOf tc)) →
     SafeFor (S.compilerExec tc m) (Q (S.envOf tc)))

/-- Single canonical-to-reference correspondence theorem per `SemProfile` (`O(1)` per profile
    rather than `O(N)` per compiler version). -/
def ProfileRefCorrespondence (S : CompilerSuite) (π : SemProfile) (lift : S.CanonMir → S.RefProg) : Prop :=
  ∀ (env : TargetLayoutEnv) (mc : S.CanonMir) (Q : S.Val → Prop),
    AdmissibleEnvForProfile π env →
    SafeFor (S.refExec π env (lift mc)) Q →
    SafeFor (S.canonExec π env mc) Q

/-- Universal obligation over all admissible target/compiler layouts in profile `π`. -/
def VerifiedForProfile (S : CompilerSuite) (π : SemProfile) (p : S.RefProg)
    (Q : TargetLayoutEnv → S.Val → Prop) : Prop :=
  ∀ (env : TargetLayoutEnv), AdmissibleEnvForProfile π env → SafeFor (S.refExec π env p) (Q env)

/-- Two-tier receipt provenance lattice distinguishing audited pinned equivalence-class
    toolchains from unmapped or mismatched deployment compilers. -/
inductive ReceiptProvenance (Hash : Type) where
  | pinnedVerified (tc : ToolchainIdentity Hash) (profile : SemProfile)
  | unverifiedCompiler (tc : ToolchainIdentity Hash) (profile : SemProfile)
  deriving DecidableEq

/-- Strict auditor check: accepts ONLY `pinnedVerified` receipts whose full 5-tuple
    `(compilerCommit, binarySha256, sysrootSha256, targetTriple, flagsDigest)` belongs to
    the audited registry `isRegisteredVerifiedToolchain`. -/
def strictAuditAccepts (S : CompilerSuite) : ReceiptProvenance S.Hash → Bool
  | .pinnedVerified tc _ => S.isRegisteredVerifiedToolchain tc
  | .unverifiedCompiler _ _ => false

/-- Deployment compiler gate: discharging a compiler-pinned safety claim on `tcShip`
    additionally requires exact toolchain identity equality `tcVerify = tcShip`. -/
def strictShipGate (S : CompilerSuite) [DecidableEq S.Hash]
    (r : ReceiptProvenance S.Hash) (tcShip : ToolchainIdentity S.Hash) : Bool :=
  match r with
  | .pinnedVerified tcVerify _ =>
    match S.isRegisteredVerifiedToolchain tcVerify with
    | true => decide (tcVerify = tcShip)
    | false => false
  | .unverifiedCompiler _ _ => false

theorem unverified_compiler_rejected_by_strict_audit
    (S : CompilerSuite) (tc : ToolchainIdentity S.Hash) (π : SemProfile) :
    strictAuditAccepts S (.unverifiedCompiler tc π) = false :=
  rfl

theorem mismatched_ship_toolchain_rejected
    (S : CompilerSuite) [DecidableEq S.Hash]
    (tcVerify tcShip : ToolchainIdentity S.Hash) (π : SemProfile)
    (hNe : tcVerify ≠ tcShip) :
    strictShipGate S (.pinnedVerified tcVerify π) tcShip = false := by
  change
    (match S.isRegisteredVerifiedToolchain tcVerify with
     | true => decide (tcVerify = tcShip)
     | false => false) = false
  cases hReg : S.isRegisteredVerifiedToolchain tcVerify with
  | false => exact rfl
  | true => exact decide_eq_false hNe

/-- **Theorem 1 (Two-Tier Receipt Provenance & Profile-Shared Correspondence Soundness):**
    If strict audit accepts receipt `r = .pinnedVerified tc π`, spoke capture succeeds,
    all registered toolchains have faithful spoke drivers, and profile `S.profileOf tc` has ONE
    reference correspondence proof `ProfileRefCorrespondence S (S.profileOf tc) lift`, then a
    single layout-parametric verification proof over `refExec` guarantees UB-free execution
    under `compilerExec tc m`. -/
theorem strict_receipt_implies_compiler_safety
    (S : CompilerSuite)
    (tc : ToolchainIdentity S.Hash)
    (π : SemProfile)
    (m : S.CompilerMir tc)
    (mc : S.CanonMir)
    (lift : S.CanonMir → S.RefProg)
    (Q : TargetLayoutEnv → S.Val → Prop)
    (hAudit : strictAuditAccepts S (.pinnedVerified tc π) = true)
    (hRegFaithful : ∀ tc', S.isRegisteredVerifiedToolchain tc' = true → SpokeFaithful S tc')
    (hCap : S.capture tc m = .ok (mc, π))
    (hCorr : ProfileRefCorrespondence S (S.profileOf tc) lift)
    (hVerif : VerifiedForProfile S (S.profileOf tc) (lift mc) Q) :
    SafeFor (S.compilerExec tc m) (Q (S.envOf tc)) :=
  let hReg : S.isRegisteredVerifiedToolchain tc = true := hAudit
  let hSpoke := hRegFaithful tc hReg
  let hPair := hSpoke m mc π Q hCap
  let hTransfer :
      SafeFor (S.canonExec (S.profileOf tc) (S.envOf tc) mc) (Q (S.envOf tc)) →
      SafeFor (S.compilerExec tc m) (Q (S.envOf tc)) :=
    Eq.rec
      (motive := fun prof _ =>
        SafeFor (S.canonExec prof (S.envOf tc) mc) (Q (S.envOf tc)) →
        SafeFor (S.compilerExec tc m) (Q (S.envOf tc)))
      hPair.2
      hPair.1
  hTransfer
    (hCorr (S.envOf tc) mc (Q (S.envOf tc)) (S.envAdmissible tc hReg)
      (hVerif (S.envOf tc) (S.envAdmissible tc hReg)))

/-- **Theorem 2 (Target/Machdep Mismatch Unsoundness — CompCert/Frama-C/SPARK Host Disconnect):**
    A program reading pointer width (`sizeof(void*) == 8`) verified under a 64-bit `Archi`/`machdep`
    (`ptrWidthBits = 64`) triggers UB when compiled by an unpinned 32-bit target/compiler
    (`ptrWidthBits = 32`). -/
def ptrWidthGuardProg (env : TargetLayoutEnv) : Outcome Nat :=
  match Nat.beq env.ptrWidthBits 64 with
  | true => .ok 64
  | false => .ub

def env64 : TargetLayoutEnv :=
  { ptrWidthBits := 64, littleEndian := true, reprCFixedOffset := 0,
    reprRustFieldAOffset := 14, reprRustFieldBOffset := 0, infallibleEqNever := false }

def env32 : TargetLayoutEnv :=
  { ptrWidthBits := 32, littleEndian := true, reprCFixedOffset := 0,
    reprRustFieldAOffset := 14, reprRustFieldBOffset := 0, infallibleEqNever := false }

theorem target_machdep_mismatch_unsound :
    SafeFor (ptrWidthGuardProg env64) (fun v => v = 64) ∧
    ptrWidthGuardProg env32 = .ub :=
  And.intro rfl rfl

/-- **Theorem 3 (Same-Profile `#[repr(Rust)]` Baked-Offset Unsoundness vs Parametric Soundness):**
    Even within the same `SemProfile` (`rust2021InfallibleNeverStacked`) and fixed 64-bit target,
    two admissible environments (`envStd1100` and `envRandSeed7`, modeling `ReprRustMixed` offsets
    `14,0` vs `16,0` under `-Z randomize-layout -Z layout-seed=7`) break any proof that bakes
    concrete `#[repr(Rust)]` field offsets, while `#[repr(C)]` proofs transfer soundly. -/
def envStd1100 : TargetLayoutEnv :=
  { ptrWidthBits := 64, littleEndian := true, reprCFixedOffset := 0,
    reprRustFieldAOffset := 14, reprRustFieldBOffset := 0, infallibleEqNever := true }

def envRandSeed7 : TargetLayoutEnv :=
  { ptrWidthBits := 64, littleEndian := true, reprCFixedOffset := 0,
    reprRustFieldAOffset := 16, reprRustFieldBOffset := 0, infallibleEqNever := true }

theorem both_1100_envs_admissible :
    AdmissibleEnvForProfile .rust2021InfallibleNeverStacked envStd1100 ∧
    AdmissibleEnvForProfile .rust2021InfallibleNeverStacked envRandSeed7 :=
  And.intro
    (And.intro rfl (And.intro rfl (And.intro rfl (And.intro (fun h => nomatch h) rfl))))
    (And.intro rfl (And.intro rfl (And.intro rfl (And.intro (fun h => nomatch h) rfl))))

def bakedReprRustProg (env : TargetLayoutEnv) : Outcome Nat :=
  match Nat.beq env.reprRustFieldAOffset 14 with
  | true => .ok 1
  | false => .ub

theorem baked_repr_rust_breaks_under_ship_layout :
    SafeFor (bakedReprRustProg envStd1100) (fun v => v = 1) ∧
    bakedReprRustProg envRandSeed7 = .ub :=
  And.intro rfl rfl

/-- **Theorem 4 (Cross-Profile `Infallible = !` Drift Requires Explicit `SemProfile` Switch):**
    `envStd991` (`1.99.1`, `infallibleEqNever = false`) is admissible for
    `rust2021InfallibleEnumStacked`, whereas `envStd1100` (`1.100.0`, `infallibleEqNever = true`)
    is not admissible for `rust2021InfallibleEnumStacked` and flips `infallibleCheckProg` to `.ub`. -/
def envStd991 : TargetLayoutEnv :=
  { ptrWidthBits := 64, littleEndian := true, reprCFixedOffset := 0,
    reprRustFieldAOffset := 14, reprRustFieldBOffset := 0, infallibleEqNever := false }

def infallibleCheckProg (env : TargetLayoutEnv) : Outcome Unit :=
  match env.infallibleEqNever with
  | true => .ub
  | false => .ok ()

theorem profile_blocks_unsound_infallible_transfer :
    AdmissibleEnvForProfile .rust2021InfallibleEnumStacked envStd991 ∧
    (¬ AdmissibleEnvForProfile .rust2021InfallibleEnumStacked envStd1100) ∧
    SafeFor (infallibleCheckProg envStd991) (fun _ => True) ∧
    infallibleCheckProg envStd1100 = .ub :=
  And.intro
    (And.intro rfl (And.intro rfl (And.intro rfl (And.intro (fun h => nomatch h) rfl))))
    (And.intro
      (fun hBad => nomatch hBad.2.2.2.2)
      (And.intro True.intro rfl))

#print axioms unverified_compiler_rejected_by_strict_audit
#print axioms mismatched_ship_toolchain_rejected
#print axioms strict_receipt_implies_compiler_safety
#print axioms target_machdep_mismatch_unsound
#print axioms baked_repr_rust_breaks_under_ship_layout
#print axioms profile_blocks_unsound_infallible_transfer

end AssuranceTheorems
