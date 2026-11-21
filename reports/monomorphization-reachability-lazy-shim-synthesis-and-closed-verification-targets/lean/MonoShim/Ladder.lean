import MonoShim.Pipeline

/-!
# The tuple-like clone ladder is exact
-/

namespace Toy.MonoShim

/-- The cleanup an enclosing ladder level contributes once the inner part has finished:
if the inner part is unwinding, drop the already-cloned fields `done` (most recent first). -/
def postClean (c : Call) (done : List Ty) : Res × St → Res × St
  | (.unwind, st) => cleanupDrops c done st
  | r => r

theorem ladder_post (sig : Sig) (c : Call) : ∀ (ts done : List Ty) (fr : Frame) (st : St),
    postClean c done ((execS sig c (ladder ts) fr st).1, (execS sig c (ladder ts) fr st).2.2)
      = aggClone c done ts st ∧ (execS sig c (ladder ts) fr st).2.1 = fr := by
  intro ts
  induction ts with
  | nil => intro done fr st; simp [ladder, execS, aggClone, postClean]
  | cons t ts ih =>
    intro done fr st
    rcases h1 : c (cloneKey t) st with ⟨r1, st1⟩
    cases r1 with
    | ok =>
      obtain ⟨ihp, ihf⟩ := ih (t :: done) fr st1
      rcases h2 : execS sig c (ladder ts) fr st1 with ⟨r2, fr2, st2⟩
      rw [h2] at ihp ihf
      simp only at ihf
      subst ihf
      cases r2 with
      | unwind =>
        rcases h3 : c (.dropGlue t) st2 with ⟨r3, st3⟩
        simp only [postClean, cleanupDrops, h3] at ihp
        cases r3 <;> simp [ladder, execS, h1, h2, h3, aggClone, postClean, ← ihp]
      | _ =>
        simp only [postClean] at ihp
        simp [ladder, execS, h1, h2, aggClone, postClean, ← ihp]
    | _ => simp_all [ladder, execS, aggClone, postClean]

end Toy.MonoShim

namespace Toy.MonoShim

/-- **Clone-ladder exactness.** For every call oracle, field list, frame and state, the explicit
ladder statement behaves exactly like the source aggregate clone `cloneAgg`. -/
theorem ladder_exec_eq_cloneAgg (sig : Sig) (c : Call) (fs : List Ty) (fr : Frame) (st : St) :
    execS sig c (ladder fs) fr st = execS sig c (.cloneAgg fs) fr st := by
  obtain ⟨hp, hf⟩ := ladder_post sig c fs [] fr st
  rcases h : execS sig c (ladder fs) fr st with ⟨r, fr', st'⟩
  rw [h] at hp hf
  simp only at hf
  subst hf
  have hp' : (r, st') = aggClone c [] fs st := by
    cases r <;> simpa [postClean, cleanupDrops] using hp
  simp only [execS, ← hp']

theorem ladder_bodyEquiv_cloneAgg (sig : Sig) (fs : List Ty) :
    BodyEquiv sig (ladder fs) (.cloneAgg fs) := by
  intro c st
  rw [ladder_exec_eq_cloneAgg]

/-- The standard synthesizer agrees with the source on every shim key. -/
theorem synthStd_optEquiv (P : Program) (k : Key) (hk : k.isShim = true) :
    OptEquiv P.sig (synthStd P k) (srcDef0 P k) := by
  cases k with
  | dropGlue t =>
    simp only [synthStd, srcDef0]
    cases glueSrc P t <;> simp [OptEquiv, BodyEquiv]
  | cloneShim t =>
    cases t with
    | pair a b => exact ladder_bodyEquiv_cloneAgg P.sig [a, b]
    | fnPtr => simp [synthStd, srcDef0, cloneSrc, OptEquiv, BodyEquiv]
    | _ => simp [synthStd, srcDef0, cloneSrc, OptEquiv]
  | reifyShim f τs =>
    simp only [synthStd, srcDef0]
    cases (P.fns[f]?) <;> simp [OptEquiv, BodyEquiv]
  | _ => simp [Key.isShim] at hk

theorem synthStd_agrees (P : Program) (T : List Key) : SynthAgrees P (stdCfg P) T :=
  fun k _ hk => synthStd_optEquiv P k hk

end Toy.MonoShim
