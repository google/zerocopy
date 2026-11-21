import Toy.Capture.Basic

/-!
# Fail-closed flag admission (toy)

A build configuration requests properties through flags (for example, "instrument
the artifact with checker X"). A toy backend responds to each flag by admitting it
(and then must establish its property), rejecting it (the build fails), or
silently omitting it (the build succeeds without establishing the property).
Backend behaviour is a parameter of the model; nothing here describes a real
backend.
-/

namespace Toy.Capture

/-- A backend's response to a requested flag. -/
inductive Response where
  | admitted
  | rejected
  | omitted
  deriving DecidableEq, Repr

/-- A toy backend over flags `F` and artifacts `A`: a response per flag, and a
builder that produces an artifact from the list of admitted flags. -/
structure Backend (F A : Type) where
  respond : F → Response
  build : List F → A

/-- Run a configuration (the list of requested flags): fail with the first rejected
flag, if any; otherwise build from the admitted flags. Omitted flags are dropped
without any error. -/
def Backend.run {F A : Type} (be : Backend F A) (cfg : List F) : Except F A :=
  match cfg.find? (fun f => be.respond f == .rejected) with
  | some f => .error f
  | none => .ok (be.build (cfg.filter (fun f => be.respond f == .admitted)))

/-- Admitted flags are honoured: if every flag of `fs` is admitted, the artifact
built from `fs` has the property of each flag in `fs`. -/
def HonoursAdmitted {F A : Type} (Holds : F → A → Prop) (be : Backend F A) : Prop :=
  ∀ fs f, (∀ g ∈ fs, be.respond g = .admitted) → f ∈ fs → Holds f (be.build fs)

/-- Omission is observable in some admitted context: for every omitted flag `f`
there is a list `fs` of admitted flags (possibly empty) such that the artifact
`be.build fs` does not have `f`'s property. -/
def OmissionObservableOnAdmitted {F A : Type} (Holds : F → A → Prop) (be : Backend F A) :
    Prop :=
  ∀ f, be.respond f = .omitted →
    ∃ fs, (∀ g ∈ fs, be.respond g = .admitted) ∧ ¬ Holds f (be.build fs)

/-- The configuration contract "flag set ⇒ property holds of the artifact", for
every configuration: whenever the build succeeds, every requested flag's property
holds of the artifact. -/
def FlagContractSound {F A : Type} (Holds : F → A → Prop) (be : Backend F A) : Prop :=
  ∀ cfg a, be.run cfg = .ok a → ∀ f ∈ cfg, Holds f a

/-- The backend never silently omits a flag. -/
def NeverOmits {F A : Type} (be : Backend F A) : Prop :=
  ∀ f, be.respond f ≠ .omitted

/-- Running an omitted flag followed by admitted flags builds from the admitted
flags. -/
theorem Backend.run_omitted_cons {F A : Type} (be : Backend F A) {f : F} {fs : List F}
    (hf : be.respond f = .omitted) (hfs : ∀ g ∈ fs, be.respond g = .admitted) :
    be.run (f :: fs) = .ok (be.build fs) := by
  have hnoRej : (f :: fs).find? (fun g => be.respond g == .rejected) = none := by
    apply List.find?_eq_none.2
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg'
    · simp [hf]
    · simp [hfs g hg']
  have hfilt : (f :: fs).filter (fun g => be.respond g == .admitted) = fs := by
    rw [List.filter_cons_of_neg (by simp [hf])]
    exact List.filter_eq_self.2 (fun g hg => by simp [hfs g hg])
  simp [Backend.run, hnoRej, hfilt]

/-- **Sufficiency.** A backend that honours admitted flags and never omits a flag
satisfies the flag contract. -/
theorem flagContractSound_of_neverOmits {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hAdm : HonoursAdmitted Holds be) (hno : NeverOmits be) :
    FlagContractSound Holds be := by
  intro cfg a hrun f hf
  unfold Backend.run at hrun
  cases hfind : cfg.find? (fun f => be.respond f == .rejected) with
  | some g => simp [hfind] at hrun
  | none =>
    simp only [hfind, Except.ok.injEq] at hrun
    subst hrun
    have hnr : ∀ g ∈ cfg, be.respond g ≠ .rejected := by
      intro g hg hr
      have := List.find?_eq_none.1 hfind g hg
      simp [hr] at this
    have hadm : ∀ g ∈ cfg, be.respond g = .admitted := by
      intro g hg
      cases hr : be.respond g with
      | admitted => rfl
      | rejected => exact absurd hr (hnr g hg)
      | omitted => exact absurd hr (hno g)
    apply hAdm
    · intro g hg
      simp only [List.mem_filter] at hg
      exact hadm g hg.1
    · simp [List.mem_filter, hf, hadm f hf]

/-- **Necessity.** If every omission is observable in some admitted context, a
backend satisfying the flag contract never omits a flag. -/
theorem neverOmits_of_flagContractSound {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hObs : OmissionObservableOnAdmitted Holds be)
    (hS : FlagContractSound Holds be) : NeverOmits be := by
  intro f hf
  obtain ⟨fs, hfs, hnot⟩ := hObs f hf
  exact hnot (hS (f :: fs) _ (be.run_omitted_cons hf hfs) f (by simp))

/-- **The flag contract is sound iff the backend never silently omits.** For every
toy backend that honours admitted flags and whose omissions are observable in some
admitted context, the contract "flag set ⇒ property holds of the artifact" holds
for every configuration iff no flag is silently omitted. -/
theorem flagContractSound_iff_neverOmits {F A : Type} (Holds : F → A → Prop)
    (be : Backend F A) (hAdm : HonoursAdmitted Holds be)
    (hObs : OmissionObservableOnAdmitted Holds be) :
    FlagContractSound Holds be ↔ NeverOmits be :=
  ⟨neverOmits_of_flagContractSound Holds be hObs, flagContractSound_of_neverOmits Holds be hAdm⟩

/-- **Exact condition under `HonoursAdmitted` alone.** For every toy backend that
honours admitted flags, the flag contract holds iff the property of every omitted
flag holds of the artifact built from every list of admitted flags. -/
theorem flagContractSound_iff_omitted_hold_in_admitted_contexts {F A : Type}
    (Holds : F → A → Prop) (be : Backend F A) (hAdm : HonoursAdmitted Holds be) :
    FlagContractSound Holds be ↔
      ∀ f, be.respond f = .omitted →
        ∀ fs, (∀ g ∈ fs, be.respond g = .admitted) → Holds f (be.build fs) := by
  constructor
  · intro hS f hf fs hfs
    exact hS (f :: fs) _ (be.run_omitted_cons hf hfs) f (by simp)
  · intro hom cfg a hrun f hf
    unfold Backend.run at hrun
    cases hfind : cfg.find? (fun g => be.respond g == .rejected) with
    | some g => simp [hfind] at hrun
    | none =>
      simp only [hfind, Except.ok.injEq] at hrun
      subst hrun
      cases hrf : be.respond f with
      | admitted =>
        exact hAdm _ f (fun g hg => of_decide_eq_true (List.mem_filter.1 hg).2)
          (List.mem_filter.2 ⟨hf, by simp [hrf]⟩)
      | rejected =>
        have := List.find?_eq_none.1 hfind f hf
        simp [hrf] at this
      | omitted =>
        exact hom f hrf _ (fun g hg => of_decide_eq_true (List.mem_filter.1 hg).2)

/-! ## Examples, counterexamples and non-vacuity -/

/-- A backend whose artifact is the list of flags it instrumented; flag `0` is
admitted, flag `1` rejected, every other flag omitted. -/
def beOmit : Backend Nat (List Nat) :=
  ⟨fun f => if f = 0 then .admitted else if f = 1 then .rejected else .omitted, id⟩

/-- `beOmit` with omission replaced by admission. -/
def beFC : Backend Nat (List Nat) :=
  ⟨fun f => if f = 1 then .rejected else .admitted, id⟩

/-- The property of flag `f`: the artifact instruments `f`. -/
def instruments (f : Nat) (a : List Nat) : Prop := f ∈ a

theorem beOmit_honours : HonoursAdmitted instruments beOmit := fun _ _ _ hf => hf
theorem beFC_honours : HonoursAdmitted instruments beFC := fun _ _ _ hf => hf
theorem beOmit_observable : OmissionObservableOnAdmitted instruments beOmit :=
  fun _ _ => ⟨[], (fun _ h => nomatch h), by simp [instruments, beOmit]⟩
theorem beFC_observable : OmissionObservableOnAdmitted instruments beFC := by
  intro f h
  simp only [beFC] at h
  split at h <;> cases h

/-- `Backend.run` examples: rejection fails the build; omission drops the flag. -/
theorem run_example :
    beOmit.run [0, 1] = .error 1 ∧ beOmit.run [0, 2] = .ok [0] ∧ beFC.run [0, 2] = .ok [0, 2] := by
  decide

/-- **Counterexample: silent omission.** `beOmit` builds successfully for the
configuration `[2]`, and the artifact does not instrument flag `2`. -/
theorem silent_omission_breaks_contract :
    beOmit.run [2] = .ok [] ∧ ¬ instruments 2 [] ∧ ¬ FlagContractSound instruments beOmit := by
  refine ⟨by decide, by simp [instruments], ?_⟩
  intro h
  exact absurd (h [2] [] (by decide) 2 (by simp)) (by simp [instruments])

/-- Non-vacuity of `flagContractSound_iff_neverOmits`: both hypotheses hold for
`beFC` and for `beOmit`; both sides hold for `beFC` and both fail for `beOmit`. -/
theorem flag_nonvacuous :
    HonoursAdmitted instruments beFC ∧ OmissionObservableOnAdmitted instruments beFC ∧
    NeverOmits beFC ∧ FlagContractSound instruments beFC ∧
    HonoursAdmitted instruments beOmit ∧ OmissionObservableOnAdmitted instruments beOmit ∧
    ¬ NeverOmits beOmit ∧ ¬ FlagContractSound instruments beOmit := by
  have hno : NeverOmits beFC := by
    intro f
    simp only [beFC]
    split <;> simp
  exact ⟨beFC_honours, beFC_observable, hno,
    flagContractSound_of_neverOmits _ _ beFC_honours hno,
    beOmit_honours, beOmit_observable, fun h => h 2 (by decide),
    silent_omission_breaks_contract.2.2⟩

/-- A two-flag backend: flag `false` ("instrument") is admitted, flag `true`
("instrumented code is also checked") is omitted. The artifact records which of the
two were built in. -/
def beSan : Backend Bool (Bool × Bool) :=
  ⟨fun b => if b then .omitted else .admitted, fun fs => (fs.contains false, fs.contains true)⟩

/-- `false` holds iff instrumentation is present; `true` holds iff instrumentation,
when present, is checked. -/
def sanHolds (f : Bool) (a : Bool × Bool) : Prop :=
  if f then (a.1 = true → a.2 = true) else a.1 = true

/-- `OmissionObservableOnAdmitted`, positive example with a non-empty context: the
omitted flag `true` holds of the artifact built from no flags, and fails in the
admitted context `[false]`. For `beSan` both hypotheses of
`flagContractSound_iff_neverOmits` hold and both sides fail. -/
theorem beSan_instance :
    sanHolds true (beSan.build []) ∧ ¬ sanHolds true (beSan.build [false]) ∧
    HonoursAdmitted sanHolds beSan ∧ OmissionObservableOnAdmitted sanHolds beSan ∧
    ¬ NeverOmits beSan ∧ ¬ FlagContractSound sanHolds beSan := by
  have hadm : HonoursAdmitted sanHolds beSan := by
    intro fs f hfs hf
    cases f with
    | false => simp [sanHolds, beSan, hf]
    | true =>
      have := hfs true hf
      simp [beSan] at this
  have hobs : OmissionObservableOnAdmitted sanHolds beSan := by
    intro f hf
    cases f with
    | false => simp [beSan] at hf
    | true =>
      refine ⟨[false], ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        rfl
      · simp [sanHolds, beSan]
  refine ⟨by simp [sanHolds, beSan], by simp [sanHolds, beSan], hadm, hobs,
    fun h => h true rfl, ?_⟩
  intro hS
  have hrun : beSan.run [false, true] = .ok (true, false) := by decide
  have hprop := hS [false, true] (true, false) hrun true (by simp)
  simp [sanHolds] at hprop

/-- Tightness of `hAdm`: a backend that admits every flag but never establishes
any property (`Holds` is always false) never omits, its omissions are observable
(vacuously), the property of every omitted flag holds in every admitted context
(vacuously), and the contract fails. -/
theorem cex_flag_hAdm :
    let be : Backend Unit Unit := ⟨fun _ => .admitted, fun _ => ()⟩
    let H : Unit → Unit → Prop := fun _ _ => False
    OmissionObservableOnAdmitted H be ∧ NeverOmits be ∧
      (∀ f, be.respond f = .omitted →
        ∀ fs, (∀ g ∈ fs, be.respond g = .admitted) → H f (be.build fs)) ∧
      ¬ HonoursAdmitted H be ∧ ¬ FlagContractSound H be := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ h
    cases h
  · intro _ h
    cases h
  · intro _ h
    cases h
  · intro h
    exact h [()] () (by simp) (by simp)
  · intro h
    exact h [()] () rfl () (by simp)

/-- Tightness of `hObs`: a backend that omits every flag whose property holds
anyway (`Holds` is always true) honours admitted flags, omits, and the contract
holds. -/
theorem cex_flag_hObs :
    let be : Backend Unit Unit := ⟨fun _ => .omitted, fun _ => ()⟩
    let H : Unit → Unit → Prop := fun _ _ => True
    HonoursAdmitted H be ∧ ¬ OmissionObservableOnAdmitted H be ∧ ¬ NeverOmits be ∧
      FlagContractSound H be :=
  ⟨fun _ _ _ _ => trivial, fun h => (h () rfl).elim fun _ hfs => hfs.2 trivial,
    fun h => h () rfl, fun _ _ _ _ _ => trivial⟩

/-- Tightness of `hno` in `flagContractSound_of_neverOmits`: `beOmit` honours admitted
flags, omits a flag, and the contract fails. -/
theorem cex_flag_hno :
    HonoursAdmitted instruments beOmit ∧ ¬ NeverOmits beOmit ∧
      ¬ FlagContractSound instruments beOmit :=
  ⟨beOmit_honours, fun h => h 2 (by decide), silent_omission_breaks_contract.2.2⟩

/-- Tightness of `hS` in `neverOmits_of_flagContractSound`: `beOmit`'s omissions are
observable, the contract fails, and `beOmit` omits a flag. -/
theorem cex_flag_hS :
    OmissionObservableOnAdmitted instruments beOmit ∧ ¬ FlagContractSound instruments beOmit ∧
      ¬ NeverOmits beOmit :=
  ⟨beOmit_observable, silent_omission_breaks_contract.2.2, fun h => h 2 (by decide)⟩

/-! ## A check of the produced artifact -/

/-- Run the backend, then check the property of every requested flag on the
artifact with `check`; fail with the first flag whose check fails. -/
def checkedRun {F A : Type} (be : Backend F A) (check : F → A → Bool) (cfg : List F) :
    Except F A :=
  match be.run cfg with
  | .error f => .error f
  | .ok a =>
    match cfg.find? (fun f => !check f a) with
    | some f => .error f
    | none => .ok a

/-- **Checking every requested flag on the artifact restores the contract shape.**
If `check f a = true` implies `Holds f a`, then every artifact that the checked run
returns has the property of every requested flag, for every backend, including one
that silently omits. `checkedRun` is a function `List F → Except F A` around
`Backend.run`, not a `Backend`: the conclusion has the shape of `FlagContractSound`
with `checkedRun` in place of `Backend.run`. -/
theorem checkedRun_contractSound {F A : Type} (Holds : F → A → Prop) (be : Backend F A)
    (check : F → A → Bool) (hcheck : ∀ f a, check f a = true → Holds f a) :
    ∀ cfg a, checkedRun be check cfg = .ok a → ∀ f ∈ cfg, Holds f a := by
  intro cfg a h f hf
  unfold checkedRun at h
  cases hr : be.run cfg with
  | error g => simp [hr] at h
  | ok a' =>
    simp only [hr] at h
    cases hfind : cfg.find? (fun f => !check f a') with
    | some g => simp [hfind] at h
    | none =>
      simp only [hfind, Except.ok.injEq] at h
      subst h
      apply hcheck
      have := List.find?_eq_none.1 hfind f hf
      simpa using this

/-- If, in addition, `Holds f a` implies `check f a = true`, the checked run accepts
every successful build whose artifact has every requested property (it adds no
false rejections). -/
theorem checkedRun_eq_run_of_holds {F A : Type} (Holds : F → A → Prop) (be : Backend F A)
    (check : F → A → Bool) (hcomp : ∀ f a, Holds f a → check f a = true) (cfg : List F)
    (a : A) (hrun : be.run cfg = .ok a) (hall : ∀ f ∈ cfg, Holds f a) :
    checkedRun be check cfg = .ok a := by
  unfold checkedRun
  rw [hrun]
  have : cfg.find? (fun f => !check f a) = none := by
    apply List.find?_eq_none.2
    intro f hf
    simp [hcomp f a (hall f hf)]
  simp [this]

/-- The checked run detects the omission of `silent_omission_breaks_contract`. -/
theorem checkedRun_detects_omission :
    checkedRun beOmit (fun f a => decide (f ∈ a)) [2] = .error 2 := by decide

/-- Tightness of `hcheck` in `checkedRun_contractSound`: with the check that
accepts everything, the checked run of `beOmit` on `[2]` succeeds with an artifact
that does not instrument `2`. -/
theorem cex_checkedRun_hcheck :
    ¬ (∀ f a, (fun (_ : Nat) (_ : List Nat) => true) f a = true → instruments f a) ∧
    checkedRun beOmit (fun _ _ => true) [2] = .ok [] ∧ ¬ instruments 2 [] := by
  refine ⟨fun h => absurd (h 2 [] rfl) (by simp [instruments]), by decide,
    by simp [instruments]⟩

/-- Tightness of `hcomp` in `checkedRun_eq_run_of_holds`: with the check that
rejects everything, `beFC` builds `[0]` for `[0]`, the artifact instruments `0`,
and the checked run still fails. -/
theorem cex_checkedRun_hcomp :
    ¬ (∀ f a, instruments f a → (fun (_ : Nat) (_ : List Nat) => false) f a = true) ∧
    beFC.run [0] = .ok [0] ∧ (∀ f ∈ [0], instruments f [0]) ∧
    checkedRun beFC (fun _ _ => false) [0] = .error 0 := by
  refine ⟨fun h => absurd (h 0 [0] (by simp [instruments])) (by simp), by decide, ?_, by decide⟩
  intro f hf
  simp only [List.mem_singleton] at hf
  subst hf
  simp [instruments]

/-- Non-vacuity of `checkedRun_contractSound` and `checkedRun_eq_run_of_holds`: the
membership check is sound and complete for `instruments`; the checked run of
`beOmit` on `[0]` succeeds with an artifact that instruments `0`; the checked run of
`beFC` on `[0, 2]` succeeds with an artifact that instruments both flags. -/
theorem checkedRun_nonvacuous :
    (∀ (f : Nat) (a : List Nat), (fun f a => decide (f ∈ a)) f a = true → instruments f a) ∧
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [0] = .ok [0] ∧ (∀ f ∈ ([0] : List Nat), instruments f [0]) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [0] = .ok [0] ∧
    beFC.run [0, 2] = .ok [0, 2] ∧ (∀ f ∈ ([0, 2] : List Nat), instruments f [0, 2]) ∧
    checkedRun beFC (fun f a => decide (f ∈ a)) [0, 2] = .ok [0, 2] := by
  refine ⟨fun f a h => by simpa [instruments] using h, fun f a h => by simpa [instruments] using h,
    by decide, ?_,
    by decide, by decide, ?_, by decide⟩
  · intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    simp [instruments]
  · intro f hf
    simp only [instruments]
    exact hf

/-- Tightness of `hrun` in `checkedRun_eq_run_of_holds`: with the sound and complete
membership check, `beOmit` rejects `[1]`, the artifact `[1]` instruments `1`, and
the checked run does not return `[1]`. -/
theorem cex_checkedRun_hrun :
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [1] ≠ .ok [1] ∧ (∀ f ∈ ([1] : List Nat), instruments f [1]) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [1] ≠ .ok [1] := by
  refine ⟨fun f a h => by simpa [instruments] using h, by decide, ?_, by decide⟩
  intro f hf
  simp only [List.mem_singleton] at hf
  subst hf
  simp [instruments]

/-- Tightness of `hall` in `checkedRun_eq_run_of_holds`: with the sound and complete
membership check, `beOmit` builds `[]` for `[2]`, the artifact does not instrument
`2`, and the checked run does not return `[]`. -/
theorem cex_checkedRun_hall :
    (∀ (f : Nat) (a : List Nat), instruments f a → (fun f a => decide (f ∈ a)) f a = true) ∧
    beOmit.run [2] = .ok [] ∧ ¬ (∀ f ∈ ([2] : List Nat), instruments f []) ∧
    checkedRun beOmit (fun f a => decide (f ∈ a)) [2] ≠ .ok [] := by
  refine ⟨fun f a h => by simpa [instruments] using h, by decide, ?_, by decide⟩
  intro h
  exact absurd (h 2 (by simp)) (by simp [instruments])

/-! ## A source-level audit that exempts external macro expansions -/

/-- A toy source item: plain code (flagged `isUnsafe` if it contains an unsafe
operation), or a macro invocation whose expansion is a list of such flags;
`external` marks a macro defined outside the audited source. -/
inductive Item where
  | plain (isUnsafe : Bool)
  | macro (external : Bool) (expansion : List Bool)
  deriving DecidableEq, Repr

/-- The post-expansion IR: the unsafe flags of all code after macro expansion. -/
def expand : List Item → List Bool
  | [] => []
  | .plain u :: rest => u :: expand rest
  | .macro _ e :: rest => e ++ expand rest

/-- A source-level audit that exempts external macro expansions: it accepts iff no
plain item is unsafe and no expansion of a non-external macro contains an unsafe
item. -/
def srcAuditExemptExternal : List Item → Bool
  | [] => true
  | .plain u :: rest => !u && srcAuditExemptExternal rest
  | .macro ext e :: rest => (ext || !e.any id) && srcAuditExemptExternal rest

/-- The post-expansion IR audit: it accepts iff the expanded IR contains no unsafe
item. -/
def irAudit (prog : List Item) : Bool := !(expand prog).any id

/-- **Every program the post-expansion IR audit accepts, the exempting source audit
accepts.** -/
theorem srcAudit_of_irAudit : ∀ prog, irAudit prog = true → srcAuditExemptExternal prog = true
  | [], _ => rfl
  | .plain u :: rest, h => by
    have h0 : (!u && irAudit rest) = true := by
      simpa [irAudit, expand] using h
    have hr : irAudit rest = true := by cases u <;> simp_all
    have hu : u = false := by cases u <;> simp_all
    simp [srcAuditExemptExternal, hu, srcAudit_of_irAudit rest hr]
  | .macro ext e :: rest, h => by
    have h0 : (!e.any id && irAudit rest) = true := by
      simpa [irAudit, expand, List.any_append] using h
    have hr : irAudit rest = true := by
      cases he : e.any id <;> simp_all
    have he : e.any id = false := by
      cases he : e.any id <;> simp_all
    simp [srcAuditExemptExternal, he, srcAudit_of_irAudit rest hr]

/-- **The converse fails: an exempted external expansion containing `unsafe`.** The
exempting source audit accepts `[.macro true [true]]` while the post-expansion IR
audit rejects it. -/
theorem srcAudit_misses_external_unsafe :
    srcAuditExemptExternal [.macro true [true]] = true ∧ irAudit [.macro true [true]] = false := by
  decide

/-- A program on which both audits accept: plain safe code, a safe expansion of a
non-external macro, and a safe expansion of an external macro. -/
def progAuditOk : List Item := [.plain false, .macro false [false], .macro true [false]]

/-- Non-vacuity of `srcAudit_of_irAudit`: the post-expansion IR audit accepts
`progAuditOk`, and so does the exempting source audit. -/
theorem srcAudit_of_irAudit_nonvacuous :
    irAudit progAuditOk = true ∧ srcAuditExemptExternal progAuditOk = true := by
  decide

/-- **The exempting source audit is strictly weaker than the post-expansion IR
audit.** Every program the IR audit accepts, the exempting source audit accepts,
and there is a program (one external macro whose expansion is unsafe) that the
exempting source audit accepts and the IR audit rejects. -/
theorem exemptingSrcAudit_strictlyWeaker_than_irAudit :
    (∀ prog, irAudit prog = true → srcAuditExemptExternal prog = true) ∧
    ∃ prog, srcAuditExemptExternal prog = true ∧ irAudit prog = false :=
  ⟨srcAudit_of_irAudit, ⟨[.macro true [true]], srcAudit_misses_external_unsafe⟩⟩

end Toy.Capture
