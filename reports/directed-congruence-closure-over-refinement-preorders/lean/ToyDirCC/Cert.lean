import ToyDirCC.Basic

/-!
# Certificates and the profile-respecting checker

A certificate is a finite proof tree for a directed fact `s ≤ t` ("`t` refines `s`") built
from

* `refl t` — `t ≤ t`;
* `fact i` — the `i`-th entry of a list of directed facts (ground rewrite instances);
* `trans p q` — chaining `a ≤ b` and `b ≤ c`;
* `cong f pre post p` — one-sided congruence: from `s ≤ t` conclude
  `f(pre, s, post) ≤ f(pre, t, post)` at position `pre.length`;
* `congEq f pre post p q` — two-sided congruence: from `s ≤ t` and `t ≤ s` conclude
  `f(pre, s, post) ≤ f(pre, t, post)` at position `pre.length`.

`concl pol P facts c` computes the fact a certificate proves, or `none` if it is malformed
or uses a congruence step the policy `pol` forbids at that position's modality.
`check` compares the computed fact with a claimed one; it is a `Bool`-valued function.
The standard policy permits `cong` only at `mono` positions and `congEq` at `mono` and
`eqOnly` positions.

Main results: `check_sound_of_admissible` — for every policy admissible for
`P` (one-sided congruence only at `mono` positions, two-sided congruence only at
non-`opaqueArg` positions), in every model satisfying `LeRefl`, `LeTrans`, `MonoAt P`,
`KerAt P` in which the facts hold, every accepted certificate proves a true refinement;
`check_sound` is its specialization to the standard policy.

Certificates are unshared trees: a sub-certificate needed twice is written twice, and
`congEq` takes separate certificates for both directions.
-/

namespace Toy.DirCC

variable {Op : Type}

/-- Proof certificates for directed facts (finite trees). -/
inductive Cert (Op : Type) where
  | refl (t : Term Op)
  | fact (i : Nat)
  | trans (p q : Cert Op)
  | cong (f : Op) (pre post : List (Term Op)) (p : Cert Op)
  | congEq (f : Op) (pre post : List (Term Op)) (p q : Cert Op)

/-- Which congruence rules a checker permits, as a function of the modality of the
position being rewritten under. -/
structure Policy where
  /-- one-sided congruence (`Cert.cong`) permitted at this modality -/
  cong : Modality → Bool
  /-- two-sided congruence (`Cert.congEq`) permitted at this modality -/
  congEq : Modality → Bool

/-- The standard policy: `cong` only at `mono`; `congEq` at `mono` and `eqOnly`. -/
def Policy.standard : Policy where
  cong m := decide (m = .mono)
  congEq m := decide (m ≠ .opaqueArg)

/-- The fact a certificate proves (`some (s, t)` for `s ≤ t`), or `none`. -/
def concl [DecidableEq Op] (pol : Policy) (P : Profile Op) (facts : List (Term Op × Term Op)) :
    Cert Op → Option (Term Op × Term Op)
  | .refl t => some (t, t)
  | .fact i => facts[i]?
  | .trans p q =>
    match concl pol P facts p, concl pol P facts q with
    | some (a, b), some (b', c) => if b = b' then some (a, c) else none
    | _, _ => none
  | .cong f pre post p =>
    match concl pol P facts p with
    | some (s, t) =>
      if pol.cong (P f pre.length) = true then
        some (.app f (pre ++ s :: post), .app f (pre ++ t :: post))
      else none
    | none => none
  | .congEq f pre post p q =>
    match concl pol P facts p, concl pol P facts q with
    | some (s, t), some (t', s') =>
      if t' = t ∧ s' = s ∧ pol.congEq (P f pre.length) = true then
        some (.app f (pre ++ s :: post), .app f (pre ++ t :: post))
      else none
    | _, _ => none

/-- The checker: does certificate `c` prove `s ≤ t` under policy `pol`, profile `P` and the
fact list `facts`? A total `Bool`-valued function. -/
def check [DecidableEq Op] (pol : Policy) (P : Profile Op) (facts : List (Term Op × Term Op))
    (c : Cert Op) (s t : Term Op) : Bool :=
  decide (concl pol P facts c = some (s, t))

/-- All facts of the list are true refinements in `M` under the valuation `ρ`. -/
def FactsHold (M : Model Op) (ρ : Nat → M.C) (facts : List (Term Op × Term Op)) : Prop :=
  ∀ s t, (s, t) ∈ facts → M.le (eval M ρ s) (eval M ρ t)

/-- A policy is admissible for a profile if it permits one-sided congruence only at
positions the profile declares `mono`, and two-sided congruence only at positions that are
not `opaqueArg`. -/
def Policy.AdmissibleFor (pol : Policy) (P : Profile Op) : Prop :=
  (∀ f i, pol.cong (P f i) = true → P f i = .mono) ∧
  (∀ f i, pol.congEq (P f i) = true → P f i ≠ .opaqueArg)

theorem Policy.standard_admissibleFor (P : Profile Op) : Policy.standard.AdmissibleFor P :=
  ⟨fun _ _ h => of_decide_eq_true h, fun _ _ h => of_decide_eq_true h⟩

/-- Evaluating an application whose argument list is `pre ++ s :: post`. -/
theorem eval_app_hole (M : Model Op) (ρ : Nat → M.C) (f : Op) (pre post : List (Term Op))
    (s : Term Op) :
    eval M ρ (.app f (pre ++ s :: post)) =
      M.interp f (pre.map (eval M ρ) ++ eval M ρ s :: post.map (eval M ρ)) := by
  rw [eval_app, List.map_append, List.map_cons]

/-- Soundness of `concl` for every admissible policy. -/
theorem concl_sound_of_admissible [DecidableEq Op] {pol : Policy} {P : Profile Op}
    {M : Model Op} (hA : pol.AdmissibleFor P) (hR : LeRefl M) (hT : LeTrans M)
    (hMono : MonoAt P M) (hKer : KerAt P M) {ρ : Nat → M.C}
    {facts : List (Term Op × Term Op)} (hF : FactsHold M ρ facts) :
    ∀ (c : Cert Op) {s t : Term Op}, concl pol P facts c = some (s, t) →
      M.le (eval M ρ s) (eval M ρ t) := by
  intro c
  induction c with
  | refl u =>
    intro s t h
    simp only [concl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hR _
  | fact i =>
    intro s t h
    exact hF s t (List.mem_of_getElem? h)
  | trans p q ihp ihq =>
    intro s t h
    simp only [concl] at h
    split at h
    · rename_i a b b' c hp hq
      split at h
      · rename_i hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hb
        exact hT _ _ _ (ihp hp) (ihq hq)
      · cases h
    · cases h
  | cong f pre post p ihp =>
    intro s t h
    simp only [concl] at h
    split at h
    · rename_i a b hp
      split at h
      · rename_i hpol
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [eval_app_hole, eval_app_hole]
        have hm : P f (pre.map (eval M ρ)).length = .mono := by
          rw [List.length_map]; exact hA.1 _ _ hpol
        exact hMono f _ _ _ _ hm (ihp hp)
      · cases h
    · cases h
  | congEq f pre post p q ihp ihq =>
    intro s t h
    simp only [concl] at h
    split at h
    · rename_i a b b' a' hp hq
      split at h
      · rename_i hc
        obtain ⟨hb, ha, hpol⟩ := hc
        subst hb; subst ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [eval_app_hole, eval_app_hole]
        have hne := hA.2 _ _ hpol
        have h1 := ihp hp
        have h2 := ihq hq
        cases hmod : P f pre.length with
        | mono =>
          have hm : P f (pre.map (eval M ρ)).length = .mono := by rw [List.length_map]; exact hmod
          exact hMono f _ _ _ _ hm h1
        | eqOnly =>
          have hm : P f (pre.map (eval M ρ)).length = .eqOnly := by
            rw [List.length_map]; exact hmod
          exact hKer f _ _ _ _ hm h1 h2
        | opaqueArg => exact absurd hmod hne
      · cases h
    · cases h

/-- **Soundness of the checker for admissible policies.** For every policy `pol` admissible
for `P`, in every model whose relation is reflexive and transitive, whose operators are
monotone at the positions `P` declares `mono` and respect mutual refinement at the positions
`P` declares `eqOnly`, and in which every listed fact holds under `ρ`, every certificate
accepted by `check pol P facts` proves a true refinement under `ρ`. -/
theorem check_sound_of_admissible [DecidableEq Op] {pol : Policy} {P : Profile Op}
    {M : Model Op} (hA : pol.AdmissibleFor P) (hR : LeRefl M) (hT : LeTrans M)
    (hMono : MonoAt P M) (hKer : KerAt P M) {ρ : Nat → M.C}
    {facts : List (Term Op × Term Op)} (hF : FactsHold M ρ facts) {c : Cert Op}
    {s t : Term Op} (hc : check pol P facts c s t = true) :
    M.le (eval M ρ s) (eval M ρ t) :=
  concl_sound_of_admissible hA hR hT hMono hKer hF c (of_decide_eq_true hc)

/-- **Soundness of directed congruence closure (standard checker).** In every model whose
relation is reflexive and transitive, whose operators are monotone at the positions `P`
declares `mono` and respect mutual refinement at the positions `P` declares `eqOnly`, and in
which every listed fact holds under `ρ`, every certificate accepted by
`check Policy.standard P facts` proves a true refinement under `ρ`. -/
theorem check_sound [DecidableEq Op] {P : Profile Op} {M : Model Op} (hR : LeRefl M)
    (hT : LeTrans M) (hMono : MonoAt P M) (hKer : KerAt P M) {ρ : Nat → M.C}
    {facts : List (Term Op × Term Op)} (hF : FactsHold M ρ facts) {c : Cert Op}
    {s t : Term Op} (hc : check Policy.standard P facts c s t = true) :
    M.le (eval M ρ s) (eval M ρ t) :=
  check_sound_of_admissible (Policy.standard_admissibleFor P) hR hT hMono hKer hF hc

end Toy.DirCC
