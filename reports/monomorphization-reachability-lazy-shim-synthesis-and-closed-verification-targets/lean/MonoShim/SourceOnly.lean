import MonoShim.Worklist

/-!
# Why verifying source definitions alone is unsound, and what suffices
-/

namespace Toy.MonoShim

/-- A specification relates the state a key is called in to its outcome. -/
abbrev Spec := St → Res × St → Prop

/-- Partial correctness: an outcome that ran out of fuel satisfies every spec. -/
def SatOut (Q : Spec) (st : St) (o : Res × St) : Prop := o.1 = .outOfFuel ∨ Q st o

/-- A key meets a spec in a resolver when every run of it, at every fuel and state, does. -/
def MeetsAt (sig : Sig) (R : Key → Option Stmt) (Q : Spec) (k : Key) : Prop :=
  ∀ n st, SatOut Q st (runKey sig R n k st)

/-- Modular verification of one body: under every call oracle that satisfies the assumed specs
`A` on the keys the body may request, the body satisfies `Q`. -/
def VerifiedBody (sig : Sig) (A : Key → Spec) (b : Stmt) (Q : Spec) : Prop :=
  ∀ c : Call, (∀ k ∈ refs sig b, ∀ st, SatOut (A k) st (c k st)) →
    ∀ st, SatOut Q st ((execS sig c b [] st).1, (execS sig c b [] st).2.2)

/-- Keys whose bodies come from user impls: trait methods and user `Drop`/`Clone`. -/
def Key.isImpl : Key → Bool
  | .meth _ _ _ => true
  | .userDrop _ => true
  | .userClone _ => true
  | _ => false

/-- Generic verification: every generic function body, at every instantiation (substitution
followed by normalization, as in `srcDef0`), verifies against the spec of that instance, assuming
the specs `Q` of the keys it requests (for method keys these are the trait-method specs). The
quantifier ranges over every concrete type-argument list `τs`; this is per-instantiation
verification, not a single parametric proof. -/
def GenericVerified (P : Program) (Q : Key → Spec) : Prop :=
  ∀ f fd τs, P.fns[f]? = some fd →
    VerifiedBody P.sig Q ((fd.body.subst τs).norm P) (Q (.inst f τs))

/-- Impl conformance: every user impl body (trait method, user `Drop`, user `Clone`) of a key in
`T` verifies against its spec. -/
def ImplsConform (P : Program) (Q : Key → Spec) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isImpl = true → ∀ b ∈ (srcDef0 P k).toList, VerifiedBody P.sig Q b (Q k)

/-- Synthesizer verification: every synthesized body for a shim key of `T` verifies against the
stated spec of that shim. -/
def SynthVerified (P : Program) (cfg : MonoCfg) (Q : Key → Spec) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → ∀ b ∈ (cfg.synth k).toList, VerifiedBody P.sig Q b (Q k)

/-- **Positive theorem.** In a closed target, generic verification plus impl conformance plus a
verified synthesizer imply that every key of the target meets its spec (partial correctness). -/
theorem closed_target_meets_specs_of_generic_impl_synth_verified (P : Program) (cfg : MonoCfg)
    (T : List Key) (Q : Key → Spec) (hC : Closed P.sig (tableM P cfg T) T)
    (hG : GenericVerified P Q) (hI : ImplsConform P Q T) (hS : SynthVerified P cfg Q T) :
    ∀ k ∈ T, MeetsAt P.sig (tableM P cfg T) (Q k) k := by
  have main : ∀ n, ∀ k ∈ T, ∀ st, SatOut (Q k) st (runKey P.sig (tableM P cfg T) n k st) := by
    intro n
    induction n with
    | zero => intro k _ st; exact Or.inl rfl
    | succ n ih =>
      intro k hk st
      obtain ⟨hsome, hrefs⟩ := hC k hk
      rcases hb : tableM P cfg T k with _ | b
      · rw [hb] at hsome; simp at hsome
      · have hrefs' : ∀ k' ∈ refs P.sig b, k' ∈ T := hrefs b (by simp [hb])
        have hbM : bodyM P cfg k = some b := by simpa [tableM, hk] using hb
        have hver : VerifiedBody P.sig Q b (Q k) := by
          unfold bodyM at hbM
          by_cases hs : k.isShim = true
          · simp only [hs, ite_true] at hbM
            exact hS k hk hs b (by simp [hbM])
          · have hs' : k.isShim = false := by simpa using hs
            simp only [hs', Bool.false_eq_true, ite_false] at hbM
            cases k with
            | inst f τs =>
              simp only [srcDef0] at hbM
              rcases hf : P.fns[f]? with _ | fd
              · rw [hf] at hbM; simp at hbM
              · rw [hf] at hbM
                simp at hbM
                subst hbM
                exact hG f fd τs hf
            | meth tr m t => exact hI _ hk rfl b (by simp [hbM])
            | userDrop n => exact hI _ hk rfl b (by simp [hbM])
            | userClone n => exact hI _ hk rfl b (by simp [hbM])
            | _ => simp [Key.isShim] at hs'
        have := hver (runKey P.sig (tableM P cfg T) n)
          (fun k' hk' st' => ih k' (hrefs' k' hk') st') st
        simpa [runKey, hb] using this
  intro k hk n st
  exact main n k hk st

/-- Under the hypotheses of the adequacy theorem (without the roots hypothesis), a key of `T`
meets a spec in the monomorphic table exactly when it meets it in the source semantics. -/
theorem meetsAt_tableM_iff_srcDef_of_adequacy (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E) (h2 : SynthAgrees P cfg T)
    (h3a : CanonicalKeys P T) (h3b : CanonicalRefs P cfg T) (Q : Spec) :
    ∀ k ∈ T, (MeetsAt P.sig (tableM P cfg T) Q k ↔ MeetsAt P.sig (srcDef P) Q k) := by
  intro k hk
  have e : ∀ n st, runKey P.sig (tableM P cfg T) n k st = runKey P.sig (srcDef P) n k st :=
    fun n st => runM_eq_runS_on_target P cfg T hE h1 h2 h3a h3b n k hk st
  constructor
  · intro h n st; rw [← e]; exact h n st
  · intro h n st; rw [e]; exact h n st

/-- (H3b) is derivable on a closed target: if the table restricted to `T` is closed and every key
of `T` is in normal form (H3a), then every key referenced by a body emitted for a key of `T` is in
normal form. -/
theorem canonicalRefs_of_closed_canonicalKeys (P : Program) (cfg : MonoCfg) (T : List Key)
    (hC : Closed P.sig (tableM P cfg T) T) (h3a : CanonicalKeys P T) :
    CanonicalRefs P cfg T := by
  intro k hk b hb k' hk'
  have hb' : b ∈ (tableM P cfg T k).toList := by simpa [tableM, hk] using hb
  exact h3a k' ((hC k hk).2 b hb' k' hk')

/-- On a closed target, (H2) and (H3a) suffice for a key of `T` to meet a spec in the monomorphic
table exactly when it meets it in the source semantics. Edge-closure, (H1) and (H3b) are not
assumed: the edge function `cfg.E` does not occur in `tableM`, and (H3b) follows from closedness
and (H3a) (`canonicalRefs_of_closed_canonicalKeys`). -/
theorem meetsAt_tableM_iff_srcDef_of_closed (P : Program) (cfg : MonoCfg) (T : List Key)
    (hC : Closed P.sig (tableM P cfg T) T) (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T)
    (Q : Spec) :
    ∀ k ∈ T, (MeetsAt P.sig (tableM P cfg T) Q k ↔ MeetsAt P.sig (srcDef P) Q k) := by
  let cfg' : MonoCfg := ⟨refs P.sig, cfg.synth⟩
  have htbl : tableM P cfg' T = tableM P cfg T := by
    funext k; simp [tableM, bodyM, cfg']
  have hC' : Closed P.sig (tableM P cfg' T) T := htbl ▸ hC
  have h2' : SynthAgrees P cfg' T := h2
  have h1' : CoversRefs P.sig cfg'.E := fun _ _ h => h
  have h3b' : CanonicalRefs P cfg' T := canonicalRefs_of_closed_canonicalKeys P cfg' T hC' h3a
  have hE' : EdgesIn (edgesM P cfg') T := by
    intro k hk k' hk'
    simp only [edgesM] at hk'
    rcases hb : bodyM P cfg' k with _ | b
    · rw [hb] at hk'; simp at hk'
    · rw [hb] at hk'
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk'
      have hb' : b ∈ (tableM P cfg' T k).toList := by simp [tableM, hk, hb]
      have hk0T : k0 ∈ T := (hC' k hk).2 b hb' k0 hk0
      rwa [h3a k0 hk0T]
  have e := meetsAt_tableM_iff_srcDef_of_adequacy P cfg' T hE' h1' h2' h3a h3b' Q
  rw [htbl] at e
  exact e

/-- **Spec transfer to the source semantics.** If the hypotheses of the positive theorem hold
(closedness, generic verification, impl conformance, synthesizer verification) and, in addition,
(H2) synthesizer agreement and (H3a) canonical target keys, then every key of `T` meets its spec in
the source semantics `runS`. -/
theorem closed_target_meets_specs_in_source_semantics (P : Program) (cfg : MonoCfg)
    (T : List Key) (Q : Key → Spec) (hC : Closed P.sig (tableM P cfg T) T)
    (hG : GenericVerified P Q) (hI : ImplsConform P Q T) (hS : SynthVerified P cfg Q T)
    (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T) :
    ∀ k ∈ T, MeetsAt P.sig (srcDef P) (Q k) k := by
  intro k hk
  exact (meetsAt_tableM_iff_srcDef_of_closed P cfg T hC h2 h3a (Q k) k hk).mp
    (closed_target_meets_specs_of_generic_impl_synth_verified P cfg T Q hC hG hI hS k hk)

end Toy.MonoShim
