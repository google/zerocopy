/- Original generic specimen. It has no Rust, Charon or Aeneas semantics. -/
namespace PrefixCertificate

universe u v w

inductive Reach {S : Type u} (step : S → S → Prop) (s0 : S) : S → Prop where
  | refl : Reach step s0 s0
  | tail {s t : S} : Reach step s0 s → step s t → Reach step s0 t

theorem Reach.trans {S : Type u} {step : S → S → Prop} {a b c : S}
    (hab : Reach step a b) (hbc : Reach step b c) : Reach step a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact Reach.tail ih hstep

def Safe {S : Type u} (step : S → S → Prop) (bad : S → Prop) (s0 : S) : Prop :=
  ∀ s, Reach step s0 s → ¬ bad s

structure Certificate {S : Type u} {M : Type v}
    (sStep : S → S → Prop) (mStep : M → M → Prop)
    (sBad : S → Prop) (mBad : M → Prop) (rel : S → M → Prop) where
  stepMatch : ∀ s m s', rel s m → sStep s s' →
    ∃ m', Reach mStep m m' ∧ rel s' m'
  badReflect : ∀ s m, rel s m → sBad s →
    ∃ m', Reach mStep m m' ∧ mBad m'

theorem Certificate.mapReach {S : Type u} {M : Type v}
    {sStep : S → S → Prop} {mStep : M → M → Prop}
    {sBad : S → Prop} {mBad : M → Prop} {rel : S → M → Prop}
    (cert : Certificate sStep mStep sBad mBad rel) {s0 s : S} {m0 : M}
    (hrel : rel s0 m0) (hr : Reach sStep s0 s) :
    ∃ m, Reach mStep m0 m ∧ rel s m := by
  induction hr with
  | refl => exact ⟨m0, Reach.refl, hrel⟩
  | @tail s t hprev hstep ih =>
    obtain ⟨m, hreach, hsm⟩ := ih
    obtain ⟨m', hnext, htm⟩ := cert.stepMatch s m t hsm hstep
    exact ⟨m', hreach.trans hnext, htm⟩

theorem Certificate.reflectSafety {S : Type u} {M : Type v}
    {sStep : S → S → Prop} {mStep : M → M → Prop}
    {sBad : S → Prop} {mBad : M → Prop} {rel : S → M → Prop}
    (cert : Certificate sStep mStep sBad mBad rel) {s0 : S} {m0 : M}
    (hrel : rel s0 m0) (hsafe : Safe mStep mBad m0) : Safe sStep sBad s0 := by
  intro s hreach hbad
  obtain ⟨m, hmreach, hsm⟩ := cert.mapReach hrel hreach
  obtain ⟨m', hnext, hmbad⟩ := cert.badReflect s m hsm hbad
  exact hsafe m' (hmreach.trans hnext) hmbad

def Certificate.compose {S : Type u} {M : Type v} {T : Type w}
    {sStep : S → S → Prop} {mStep : M → M → Prop} {tStep : T → T → Prop}
    {sBad : S → Prop} {mBad : M → Prop} {tBad : T → Prop}
    {rSM : S → M → Prop} {rMT : M → T → Prop}
    (cSM : Certificate sStep mStep sBad mBad rSM)
    (cMT : Certificate mStep tStep mBad tBad rMT) :
    Certificate sStep tStep sBad tBad (fun s t => ∃ m, rSM s m ∧ rMT m t) where
  stepMatch := by
    intro s t s' hrel hstep
    obtain ⟨m, hsm, hmt⟩ := hrel
    obtain ⟨m', hmreach, hsm'⟩ := cSM.stepMatch s m s' hsm hstep
    obtain ⟨t', htreach, hmt'⟩ := cMT.mapReach hmt hmreach
    exact ⟨t', htreach, m', hsm', hmt'⟩
  badReflect := by
    intro s t hrel hbad
    obtain ⟨m, hsm, hmt⟩ := hrel
    obtain ⟨m', hmreach, hmbad⟩ := cSM.badReflect s m hsm hbad
    obtain ⟨t', htreach, hmt'⟩ := cMT.mapReach hmt hmreach
    obtain ⟨t'', htbadreach, htbad⟩ := cMT.badReflect m' t' hmt' hmbad
    exact ⟨t'', htreach.trans htbadreach, htbad⟩

theorem Certificate.coverAllInputs {S : Type u} {M : Type v}
    {sStep : S → S → Prop} {mStep : M → M → Prop}
    {sBad : S → Prop} {mBad : M → Prop} {rel : S → M → Prop}
    (cert : Certificate sStep mStep sBad mBad rel)
    (sInitial : S → Prop) (mInitial : M → Prop)
    (cover : ∀ s, sInitial s → ∃ m, mInitial m ∧ rel s m)
    (modelSafe : ∀ m, mInitial m → Safe mStep mBad m) :
    ∀ s, sInitial s → Safe sStep sBad s := by
  intro s hs
  obtain ⟨m, hm, hrel⟩ := cover s hs
  exact cert.reflectSafety hrel (modelSafe m hm)

/- A finite-prefix certificate can stutter forever: safety does not imply progress. -/
def spinning : Nat → Nat → Prop := fun n n' => n' = n + 1
def stuck : Unit → Unit → Prop := fun _ _ => False
def neverBad {S : Type u} : S → Prop := fun _ => False

def stutteringCertificate :
    Certificate spinning stuck neverBad neverBad (fun _ _ => True) where
  stepMatch := by
    intro _ m _ _ _
    exact ⟨m, Reach.refl, True.intro⟩
  badReflect := by
    intro _ _ _ hbad
    exact False.elim hbad

theorem sourceHasInfiniteChain : ∃ f : Nat → Nat, ∀ n, spinning (f n) (f (n + 1)) := by
  exact ⟨id, fun _ => rfl⟩

theorem targetHasNoStep : ∀ m m', ¬ stuck m m' := by
  intro _ _ h
  exact h

/- Successful-value agreement without bad reflection cannot discharge this case. -/
theorem cannotHideInitialBad :
    ¬ Nonempty (Certificate stuck stuck (fun _ => True) neverBad (fun _ _ => True)) := by
  intro hcert
  obtain ⟨cert⟩ := hcert
  obtain ⟨_, _, hbad⟩ := cert.badReflect () () True.intro True.intro
  exact hbad

#print axioms Certificate.reflectSafety
#print axioms Certificate.compose
#print axioms Certificate.coverAllInputs
#print axioms sourceHasInfiniteChain
#print axioms cannotHideInitialBad

end PrefixCertificate
