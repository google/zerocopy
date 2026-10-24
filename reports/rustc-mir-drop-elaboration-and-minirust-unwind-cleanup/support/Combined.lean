import AnnealResearch.Execution
import AnnealResearch.Memory

/-!
An owned control/memory composition probe. Every copy read, copy write, and
cleanup read is an operational step. `Bad` marks toy model faults, including
representation errors; it is not a Rust UB classifier. The unwind protocol is
explicitly just one cleanup read, not Rust panic/drop elaboration.
-/
namespace AnnealResearch.Combined

open Memory Execution

inductive Config (m : Model) where
  | copying (memory : m.State) (jobs : List Job)
  | writing (memory : m.State) (job : Job) (value : Byte) (tail : List Job)
  | unwinding (memory : m.State)
  | cleanup (memory : m.State)
  | done (memory : m.State)
  | fault (memory : m.State) (error : Error)
  | spin (memory : m.State)

inductive Step (m : Model) (cleanupPtr : Ptr) : Config m → Config m → Prop where
  | beginUnwind {s} : Step m cleanupPtr (.copying s []) (.unwinding s)
  | readOk {s j js b r} : m.read s j.src = .ok (b, r) →
      Step m cleanupPtr (.copying s (j :: js)) (.writing r j b js)
  | readError {s j js e} : m.read s j.src = .error e →
      Step m cleanupPtr (.copying s (j :: js)) (.fault s e)
  | writeOk {s j b js w} : m.write s j.dst b = .ok w →
      Step m cleanupPtr (.writing s j b js) (.copying w js)
  | writeError {s j b js e} : m.write s j.dst b = .error e →
      Step m cleanupPtr (.writing s j b js) (.fault s e)
  | scheduleCleanup {s} : Step m cleanupPtr (.unwinding s) (.cleanup s)
  | cleanupOk {s b r} : m.read s cleanupPtr = .ok (b, r) →
      Step m cleanupPtr (.cleanup s) (.done r)
  | cleanupError {s e} : m.read s cleanupPtr = .error e →
      Step m cleanupPtr (.cleanup s) (.fault s e)
  | faultContinues {s e} : Step m cleanupPtr (.fault s e) (.spin s)
  | spin {s} : Step m cleanupPtr (.spin s) (.spin s)

def Bad (m : Model) : Config m → Prop
  | .fault _ _ => True
  | _ => False

def Allowed (m : Model) : Config m → Prop
  | .done _ => True
  | _ => False

/- A finite successful suffix is used as an invariant over the small-step
   machine. Error edges are present regardless of whether this invariant holds.
   Thus the success witness must be shown to exclude every error transition. -/
inductive Successful (m : Model) (cleanupPtr : Ptr) : Config m → Prop where
  | copyNil {s} : Successful m cleanupPtr (.unwinding s) →
      Successful m cleanupPtr (.copying s [])
  | copyCons {s j js b r} : m.read s j.src = .ok (b, r) →
      Successful m cleanupPtr (.writing r j b js) →
      Successful m cleanupPtr (.copying s (j :: js))
  | write {s j b js w} : m.write s j.dst b = .ok w →
      Successful m cleanupPtr (.copying w js) →
      Successful m cleanupPtr (.writing s j b js)
  | unwind {s} : Successful m cleanupPtr (.cleanup s) →
      Successful m cleanupPtr (.unwinding s)
  | cleanup {s b r} : m.read s cleanupPtr = .ok (b, r) →
      Successful m cleanupPtr (.cleanup s)
  | done {s} : Successful m cleanupPtr (.done s)

theorem successful_preserved {m : Model} {cleanupPtr : Ptr} {c d : Config m}
    (successful : Successful m cleanupPtr c) (edge : Step m cleanupPtr c d) :
    Successful m cleanupPtr d := by
  cases edge with
  | beginUnwind =>
    cases successful with
    | copyNil suffix => exact suffix
  | readOk actual =>
    cases successful with
    | copyCons expected suffix =>
      have same := Except.ok.inj (expected.symm.trans actual)
      rcases Prod.mk.inj same with ⟨hb, hr⟩
      cases hb
      cases hr
      exact suffix
  | readError actual =>
    cases successful with
    | copyCons expected suffix =>
      have impossible := expected.symm.trans actual
      cases impossible
  | writeOk actual =>
    cases successful with
    | write expected suffix =>
      have same := Except.ok.inj (expected.symm.trans actual)
      cases same
      exact suffix
  | writeError actual =>
    cases successful with
    | write expected suffix =>
      have impossible := expected.symm.trans actual
      cases impossible
  | scheduleCleanup =>
    cases successful with
    | unwind suffix => exact suffix
  | cleanupOk actual => exact Successful.done
  | cleanupError actual =>
    cases successful with
    | cleanup expected =>
      have impossible := expected.symm.trans actual
      cases impossible
  | faultContinues => cases successful
  | spin => cases successful

theorem successful_verified {m : Model} {cleanupPtr : Ptr} {c : Config m}
    (successful : Successful m cleanupPtr c) :
    Verified (Step m cleanupPtr) (Bad m) (Allowed m) c := by
  apply invariant_verified successful
  · intro s t hs edge
    exact successful_preserved hs edge
  · intro s hs
    cases hs <;> exact False.elim
  · intro s hs
    cases hs with
    | copyNil suffix => exact Or.inr ⟨_, Step.beginUnwind⟩
    | copyCons readOk suffix => exact Or.inr ⟨_, Step.readOk readOk⟩
    | write writeOk suffix => exact Or.inr ⟨_, Step.writeOk writeOk⟩
    | unwind suffix => exact Or.inr ⟨_, Step.scheduleCleanup⟩
    | cleanup readOk => exact Or.inr ⟨_, Step.cleanupOk readOk⟩
    | done => exact Or.inl True.intro

/- The evaluator's successful equation is connected to *separate* operational
   reads/writes. This lemma needs no memory laws: contradictory errors cannot
   be admitted by the same actual read/write equation. -/
theorem copy_suffix_and_steps (m : Model) (cleanupPtr : Ptr)
    {s t : m.State} {js : List Job}
    (copyOk : Memory.copy m s js = .ok t)
    (suffix : Successful m cleanupPtr (.unwinding t)) :
    Successful m cleanupPtr (.copying s js) ∧
      Reach (Step m cleanupPtr) (.copying s js) (.unwinding t) := by
  induction js generalizing s with
  | nil =>
    have same : s = t := Except.ok.inj (by simpa only [Memory.copy] using copyOk)
    cases same
    exact ⟨Successful.copyNil suffix, Reach.tail (Reach.refl _) Step.beginUnwind⟩
  | cons j js ih =>
    cases hr : m.read s j.src with
    | error e => simp [Memory.copy, hr] at copyOk
    | ok result =>
      rcases result with ⟨b, r⟩
      cases hw : m.write r j.dst b with
      | error e => simp [Memory.copy, hr, hw] at copyOk
      | ok w =>
        have tailOk : Memory.copy m w js = .ok t := by
          simpa only [Memory.copy, hr, hw] using copyOk
        obtain ⟨tailSuffix, tailSteps⟩ := ih tailOk
        refine ⟨Successful.copyCons hr (Successful.write hw tailSuffix), ?_⟩
        exact (Reach.tail (Reach.tail (Reach.refl _) (Step.readOk hr))
          (Step.writeOk hw)).trans tailSteps

def CleanupApart (cleanupPtr : Ptr) (js : List Job) : Prop :=
  ∀ j ∈ js, cleanupPtr.loc ≠ j.src.loc ∧ cleanupPtr.loc ≠ j.dst.loc

def CleanupReady (m : Model) (s : m.State) (cleanupPtr : Ptr) (value : Byte) : Prop :=
  m.Readable s cleanupPtr ∧ m.peek s cleanupPtr.loc = .byte value

/- Own-location authority persistence is deliberately not assumed. Cleanup
   authority is framed only across accesses to different locations. -/
theorem copy_preserves_disjoint_readable (m : Model) (laws : Laws m)
    (cleanupPtr : Ptr) {s t : m.State} {js : List Job}
    (copyOk : Memory.copy m s js = .ok t)
    (readable : m.Readable s cleanupPtr) (apart : CleanupApart cleanupPtr js) :
    m.Readable t cleanupPtr := by
  induction js generalizing s with
  | nil =>
    have same : s = t := Except.ok.inj (by simpa only [Memory.copy] using copyOk)
    cases same
    exact readable
  | cons j js ih =>
    cases hr : m.read s j.src with
    | error e => simp [Memory.copy, hr] at copyOk
    | ok result =>
      rcases result with ⟨b, r⟩
      cases hw : m.write r j.dst b with
      | error e => simp [Memory.copy, hr, hw] at copyOk
      | ok w =>
        have hj := apart j (by simp)
        have readableR := laws.read_readable s j.src b r hr cleanupPtr hj.1 readable
        have readableW := laws.write_readable r j.dst b w hw cleanupPtr hj.2 readableR
        have tailOk : Memory.copy m w js = .ok t := by
          simpa only [Memory.copy, hr, hw] using copyOk
        exact ih tailOk readableW (by intro k hk; exact apart k (by simp [hk]))

/-- Arbitrary admitted separated byte plans, followed by an explicit unwind
    and a cleanup read on a third disjoint location. No success premise is
    assumed: readiness, separation, and cleanup authority/storage imply it. -/
theorem copy_then_cleanup_verified (m : Model) (laws : Laws m)
    (s : m.State) (js : List Job) (cleanupPtr : Ptr) (cleanupValue : Byte)
    (ready : Ready m s js) (separated : Separated js)
    (cleanupReady : CleanupReady m s cleanupPtr cleanupValue)
    (apart : CleanupApart cleanupPtr js) :
    Verified (Step m cleanupPtr) (Bad m) (Allowed m) (.copying s js) ∧
      ∃ final, Reach (Step m cleanupPtr) (.copying s js) (.done final) ∧
        Finished m final js ∧ Frame m s final js := by
  obtain ⟨t, copyOk, finished, frame⟩ := Memory.copy_safe m laws s js ready separated
  have cleanupReadable := copy_preserves_disjoint_readable m laws cleanupPtr
    copyOk cleanupReady.1 apart
  have cleanupCell : m.peek t cleanupPtr.loc = .byte cleanupValue := by
    rw [frame cleanupPtr.loc (by intro j hj; exact (apart j hj).2)]
    exact cleanupReady.2
  obtain ⟨final, cleanupOk⟩ := laws.read_success t cleanupPtr cleanupValue
    cleanupReadable cleanupCell
  obtain ⟨successful, copySteps⟩ := copy_suffix_and_steps m cleanupPtr copyOk
    (Successful.unwind (Successful.cleanup cleanupOk))
  refine ⟨successful_verified successful, final, ?_, ?_, ?_⟩
  · exact copySteps.trans (Reach.tail (Reach.tail (Reach.refl _) Step.scheduleCleanup)
      (Step.cleanupOk cleanupOk))
  · intro j hj
    rw [laws.read_storage t cleanupPtr cleanupValue final cleanupOk j.dst.loc]
    exact finished j hj
  · intro l hl
    rw [laws.read_storage t cleanupPtr cleanupValue final cleanupOk l]
    exact frame l hl

/-- Failure is rejected at its finite prefix, even though this machine admits
    a later spin. This conclusion does not depend on eventual termination. -/
theorem cleanup_failure_then_spin (m : Model) (cleanupPtr : Ptr)
    (s : m.State) (e : Error) (failed : m.read s cleanupPtr = .error e) :
    Reach (Step m cleanupPtr) (.cleanup s) (.spin s) ∧
      ¬ NoUB (Step m cleanupPtr) (Bad m) (.cleanup s) := by
  have badPrefix : Reach (Step m cleanupPtr) (.cleanup s) (.fault s e) :=
    Reach.tail (Reach.refl _) (Step.cleanupError failed)
  exact ⟨Reach.tail badPrefix Step.faultContinues,
    bad_prefix_not_noUB badPrefix True.intro⟩

theorem reachable_cleanup_failure_unsafe (m : Model) (cleanupPtr : Ptr)
    (initial : Config m) (s : m.State) (e : Error)
    (path : Reach (Step m cleanupPtr) initial (.cleanup s))
    (failed : m.read s cleanupPtr = .error e) :
    ¬ NoUB (Step m cleanupPtr) (Bad m) initial := by
  exact bad_prefix_not_noUB (Reach.tail path (Step.cleanupError failed)) True.intro

/- Concrete nonvacuity and alias-sensitive discriminator. These are deliberately
   small storage-slot models, not physical layout or Rust aliasing claims. -/
namespace Examples

def cleanupPtr : Ptr := ⟨2, 0, 0⟩

def demoStore (value cleanupValue : Byte) : Store where
  cells := fun l => if l = (srcPtr 0).loc then .byte value
    else if l = cleanupPtr.loc then .byte cleanupValue else .uninit
  live := fun _ => true
  size := fun _ => 1
  readGrant := fun _ => true
  writeGrant := fun _ => true

theorem demo_copy_and_cleanup (policy : Policy) (value cleanupValue : Byte) :
    Verified (Step (concrete policy) cleanupPtr) (Bad (concrete policy))
      (Allowed (concrete policy))
      (.copying (demoStore value cleanupValue) [byteJob 0 value]) := by
  apply (copy_then_cleanup_verified (concrete policy) (concrete_laws policy)
    (demoStore value cleanupValue) [byteJob 0 value] cleanupPtr cleanupValue ?_ ?_ ?_ ?_).1
  · intro j hj
    have hj' : j = byteJob 0 value := List.mem_singleton.mp hj
    subst j
    simp [concrete, CanRead, CanWrite, demoStore, byteJob, srcPtr, dstPtr, Ptr.loc]
  · simp [Separated, byteJob, srcPtr, dstPtr, Ptr.loc]
  · simp [CleanupReady, concrete, CanRead, demoStore, cleanupPtr, srcPtr, Ptr.loc]
  · intro j hj
    have hj' : j = byteJob 0 value := List.mem_singleton.mp hj
    subst j
    simp [cleanupPtr, byteJob, srcPtr, dstPtr, Ptr.loc]

def aliasSource : Ptr := ⟨0, 0, 0⟩
def aliasSibling : Ptr := ⟨0, 0, 1⟩
def aliasJob : Job := ⟨aliasSource, aliasSibling, 7⟩

def aliasStore : Store where
  cells := fun _ => .byte 7
  live := fun _ => true
  size := fun _ => 1
  readGrant := fun _ => true
  writeGrant := fun _ => true

theorem alias_read_then_sibling_write_faults :
    ¬ NoUB (Step (concrete .siblingRevoking) cleanupPtr)
      (Bad (concrete .siblingRevoking)) (.copying aliasStore [aliasJob]) := by
  have readOk : (concrete .siblingRevoking).read aliasStore aliasSource =
      .ok (7, afterRead .siblingRevoking aliasStore aliasSource) := by rfl
  have writeFailed : (concrete .siblingRevoking).write
      (afterRead .siblingRevoking aliasStore aliasSource) aliasSibling 7 =
      .error .authority := by rfl
  have path : Reach (Step (concrete .siblingRevoking) cleanupPtr)
      (.copying aliasStore [aliasJob])
      (.fault (afterRead .siblingRevoking aliasStore aliasSource) .authority) :=
    Reach.tail (Reach.tail (Reach.refl _) (Step.readOk readOk)) (Step.writeError writeFailed)
  exact bad_prefix_not_noUB path True.intro

def missingCleanupPtr : Ptr := ⟨3, 0, 0⟩
def failedCleanupInitial : Store := demoStore 7 9
def failedCleanupRead : Store :=
  afterRead .siblingRevoking failedCleanupInitial (srcPtr 0)
def failedCleanupWritten : Store :=
  afterWrite .siblingRevoking failedCleanupRead (dstPtr 0) 7

/-- The copy itself succeeds and writes its byte. Cleanup then reads an
    uninitialized third allocation and faults before the admitted later spin.
    Every premise of the generic bad-prefix theorem is discharged here. -/
theorem copy_then_failed_cleanup_then_spin :
    Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7]) (.spin failedCleanupWritten) ∧
    failedCleanupWritten.cells (dstPtr 0).loc = .byte 7 ∧
    ¬ NoUB (Step (concrete .siblingRevoking) missingCleanupPtr)
      (Bad (concrete .siblingRevoking))
      (.copying failedCleanupInitial [byteJob 0 7]) := by
  have readOk : (concrete .siblingRevoking).read failedCleanupInitial (srcPtr 0) =
      .ok (7, failedCleanupRead) := by rfl
  have writeOk : (concrete .siblingRevoking).write failedCleanupRead (dstPtr 0) 7 =
      .ok failedCleanupWritten := by rfl
  have cleanupFailed : (concrete .siblingRevoking).read
      failedCleanupWritten missingCleanupPtr = .error .uninitialized := by rfl
  have readPrefix : Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7])
      (.writing failedCleanupRead (byteJob 0 7) 7 []) :=
    Reach.tail (Reach.refl _) (Step.readOk readOk)
  have writePrefix : Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7]) (.copying failedCleanupWritten []) :=
    Reach.tail readPrefix (Step.writeOk writeOk)
  have unwindPrefix : Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7]) (.unwinding failedCleanupWritten) :=
    Reach.tail writePrefix Step.beginUnwind
  have cleanupPrefix : Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7]) (.cleanup failedCleanupWritten) :=
    Reach.tail unwindPrefix Step.scheduleCleanup
  have badPrefix : Reach (Step (concrete .siblingRevoking) missingCleanupPtr)
      (.copying failedCleanupInitial [byteJob 0 7])
      (.fault failedCleanupWritten .uninitialized) :=
    Reach.tail cleanupPrefix (Step.cleanupError cleanupFailed)
  exact ⟨Reach.tail badPrefix Step.faultContinues, rfl,
    bad_prefix_not_noUB badPrefix True.intro⟩

end Examples

#print axioms successful_preserved
#print axioms successful_verified
#print axioms copy_suffix_and_steps
#print axioms copy_preserves_disjoint_readable
#print axioms copy_then_cleanup_verified
#print axioms cleanup_failure_then_spin
#print axioms reachable_cleanup_failure_unsafe
#print axioms Examples.demo_copy_and_cleanup
#print axioms Examples.alias_read_then_sibling_write_faults
#print axioms Examples.copy_then_failed_cleanup_then_spin

end AnnealResearch.Combined
