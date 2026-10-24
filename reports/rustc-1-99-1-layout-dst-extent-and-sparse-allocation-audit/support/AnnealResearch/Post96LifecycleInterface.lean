-- Generated from archived actual Cargo bundles; no live-path or host-process proof.
import AnnealResearch.Post96NativeConsumer
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 3200000
namespace AnnealResearch.Post96LifecycleInterface
open AnnealResearch.Post96NativeConsumer
open AnnealResearch.SemanticVerticalSlice
structure ArchivedFileIdentity where
  role : String
  label : String
  sha256 : String
  size : Nat
  deriving DecidableEq, Repr
structure ArchivedBinding where
  bundleKey : String
  requestKey : String
  generation : String
  manifestSha256 : String
  rawSha256 : String
  receiptSha256 : String
  status : String
  cargoExitCode : Nat
  files : List ArchivedFileIdentity
  deriving DecidableEq, Repr
structure LifecycleSubject where
  binding : ArchivedBinding
  native : NativeEnvelope
  deriving DecidableEq, Repr
structure ExpectedLifecycle where
  binding : ArchivedBinding
  native : ExpectedNative
  deriving DecidableEq, Repr
structure AcceptedLifecycle where
  binding : ArchivedBinding
  native : AcceptedNative
  deriving DecidableEq, Repr
/-- This checks the recorded outer report and byte identities. It does not prove OS events,
    original current-host source validation, SHA correctness, or unverified adapter fidelity. -/
def checkArchivedBinding (expected : ExpectedLifecycle) (e : LifecycleSubject) : Bool :=
  (e.binding == expected.binding) && (e.binding.status == "complete") &&
  (e.binding.cargoExitCode == 0) && (e.binding.rawSha256 == e.native.rawSha256) &&
  (e.binding.rawSha256 == expected.native.rawSha256)
def checkLifecycle (expected : ExpectedLifecycle) (e : LifecycleSubject) : Bool :=
  checkArchivedBinding expected e && checkNative expected.native e.native
def acceptLifecycle (expected : ExpectedLifecycle) (e : LifecycleSubject) : Option AcceptedLifecycle :=
  bif checkLifecycle expected e then
    some { binding := e.binding, native := { envelope := e.native, bodies := e.native.bodies } }
  else none
theorem acceptLifecycle_sound (expected : ExpectedLifecycle) (e : LifecycleSubject) (a : AcceptedLifecycle)
    (h : acceptLifecycle expected e = some a) :
    a.binding = e.binding ∧ a.native.envelope = e.native ∧ a.native.bodies = e.native.bodies ∧
    checkArchivedBinding expected e = true ∧ acceptNative expected.native e.native = some a.native := by
  unfold acceptLifecycle at h
  cases hc : checkLifecycle expected e with
  | false => rw [hc] at h; contradiction
  | true =>
      rw [hc] at h
      injection h with hh
      subst a
      have hg := hc
      unfold checkLifecycle at hg
      simp only [Bool.and_eq_true] at hg
      refine ⟨rfl, rfl, rfl, hg.1, ?_⟩
      unfold acceptNative
      rw [hg.2]
      rfl

#print axioms acceptLifecycle_sound
end AnnealResearch.Post96LifecycleInterface
