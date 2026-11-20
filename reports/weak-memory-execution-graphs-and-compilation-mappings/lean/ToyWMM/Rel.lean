/-!
# Boolean relations on a finite carrier and decidable acyclicity

Relations on the events `Fin n` of an execution are Boolean matrices `Fin n → Fin n → Bool`.
`Acyclic r` is the standard notion: no event reaches itself by a non-empty `r`-path
(`Relation.TransGen`). Acyclicity is decided by a Floyd–Warshall style closure whose
correctness (`acyclicB_eq_true_iff`) is proved below, so `decide` can evaluate `Acyclic` on
concrete executions.
-/

namespace Toy.WMM

/-- A binary relation on `Fin n`, as a Boolean matrix. -/
abbrev Rel (n : Nat) := Fin n → Fin n → Bool

namespace Rel

variable {n : Nat}

/-- Union of relations. -/
def union (r s : Rel n) : Rel n := fun a b => r a b || s a b

/-- Inclusion of relations. -/
def Sub (r s : Rel n) : Prop := ∀ a b, r a b = true → s a b = true

/-- Non-empty `r`-paths: the transitive closure of `r`, as a `Prop`. -/
def Path (r : Rel n) : Fin n → Fin n → Prop := Relation.TransGen (fun a b => r a b = true)

/-- `r` is acyclic: no element reaches itself by a non-empty `r`-path. -/
def Acyclic (r : Rel n) : Prop := ∀ a, ¬ Path r a a

theorem Path.single {r : Rel n} {a b : Fin n} (h : r a b = true) : Path r a b :=
  Relation.TransGen.single h

theorem Path.tail {r : Rel n} {a b c : Fin n} (h₁ : Path r a b) (h₂ : r b c = true) :
    Path r a c :=
  Relation.TransGen.tail h₁ h₂

theorem Path.trans {r : Rel n} {a b c : Fin n} (h₁ : Path r a b) (h₂ : Path r b c) :
    Path r a c :=
  Relation.TransGen.trans h₁ h₂

/-- Paths are monotone in the relation. -/
theorem Path.mono {r s : Rel n} (hrs : Sub r s) {a b : Fin n} (h : Path r a b) : Path s a b := by
  induction h with
  | single hab => exact Path.single (hrs _ _ hab)
  | tail _ hbc ih => exact Path.tail ih (hrs _ _ hbc)

/-- Acyclicity is antitone in the relation. -/
theorem Acyclic.mono {r s : Rel n} (hrs : Sub r s) (hs : Acyclic s) : Acyclic r :=
  fun a h => hs a (Path.mono hrs h)

/-- A relation whose edges are contained in the paths of an acyclic relation is acyclic. -/
theorem Acyclic.of_sub_path {r s : Rel n} (hrs : ∀ a b, r a b = true → Path s a b)
    (hs : Acyclic s) : Acyclic r := by
  have key : ∀ a b, Path r a b → Path s a b := by
    intro a b h
    induction h with
    | single hab => exact hrs _ _ hab
    | tail _ hbc ih => exact Path.trans ih (hrs _ _ hbc)
  exact fun a h => hs a (key a a h)

/-! ## Floyd–Warshall closure and its correctness -/

/-- `PathBelow r k a b`: an `r`-path from `a` to `b` all of whose intermediate vertices have
index `< k`. -/
inductive PathBelow (r : Rel n) (k : Nat) : Fin n → Fin n → Prop
  | edge {a b : Fin n} : r a b = true → PathBelow r k a b
  | trans {a c b : Fin n} : PathBelow r k a c → c.val < k → PathBelow r k c b → PathBelow r k a b

/-- Stage `k` of the Floyd–Warshall closure: paths through intermediates `< k`. -/
def warshall (r : Rel n) : Nat → Rel n
  | 0 => r
  | k + 1 => fun a b =>
      warshall r k a b ||
        (if h : k < n then warshall r k a ⟨k, h⟩ && warshall r k ⟨k, h⟩ b else false)

/-- Boolean acyclicity test: no vertex reaches itself in the full closure. -/
def acyclicB (r : Rel n) : Bool := (List.finRange n).all fun a => !warshall r n a a

theorem PathBelow.mono {r : Rel n} {k k' : Nat} (hk : k ≤ k') {a b : Fin n}
    (h : PathBelow r k a b) : PathBelow r k' a b := by
  induction h with
  | edge hab => exact PathBelow.edge hab
  | trans _ hc _ ih₁ ih₂ => exact PathBelow.trans ih₁ (Nat.lt_of_lt_of_le hc hk) ih₂

theorem PathBelow.toPath {r : Rel n} {k : Nat} {a b : Fin n} (h : PathBelow r k a b) :
    Path r a b := by
  induction h with
  | edge hab => exact Path.single hab
  | trans _ _ _ ih₁ ih₂ => exact Path.trans ih₁ ih₂

theorem Path.toPathBelow {r : Rel n} {a b : Fin n} (h : Path r a b) : PathBelow r n a b := by
  induction h with
  | single hab => exact PathBelow.edge hab
  | @tail b' c _ hbc ih => exact PathBelow.trans ih b'.isLt (PathBelow.edge hbc)

/-- Splitting a path through intermediates `< k+1` at the vertex `k`. -/
theorem PathBelow.split {r : Rel n} {k : Nat} (hk : k < n) {a b : Fin n}
    (h : PathBelow r (k + 1) a b) :
    PathBelow r k a b ∨ (PathBelow r k a ⟨k, hk⟩ ∧ PathBelow r k ⟨k, hk⟩ b) := by
  induction h with
  | edge hab => exact Or.inl (PathBelow.edge hab)
  | @trans a c b _ hc _ ih₁ ih₂ =>
    by_cases hck : c.val = k
    · have hcK : c = ⟨k, hk⟩ := Fin.ext hck
      subst hcK
      refine Or.inr ⟨?_, ?_⟩
      · rcases ih₁ with h | ⟨h, _⟩ <;> exact h
      · rcases ih₂ with h | ⟨_, h⟩ <;> exact h
    · have hc' : c.val < k := by omega
      rcases ih₁ with h₁ | ⟨h₁, h₁'⟩ <;> rcases ih₂ with h₂ | ⟨h₂, h₂'⟩
      · exact Or.inl (PathBelow.trans h₁ hc' h₂)
      · exact Or.inr ⟨PathBelow.trans h₁ hc' h₂, h₂'⟩
      · exact Or.inr ⟨h₁, PathBelow.trans h₁' hc' h₂⟩
      · exact Or.inr ⟨h₁, h₂'⟩

/-- Past `n`, raising the bound adds no paths. -/
theorem PathBelow.of_succ_of_le {r : Rel n} {k : Nat} (hk : n ≤ k) {a b : Fin n}
    (h : PathBelow r (k + 1) a b) : PathBelow r k a b := by
  induction h with
  | edge hab => exact PathBelow.edge hab
  | @trans a c b _ _ _ ih₁ ih₂ => exact PathBelow.trans ih₁ (Nat.lt_of_lt_of_le c.isLt hk) ih₂

theorem warshall_sound {r : Rel n} {k : Nat} {a b : Fin n} (h : warshall r k a b = true) :
    PathBelow r k a b := by
  induction k generalizing a b with
  | zero => exact PathBelow.edge h
  | succ k ih =>
    simp only [warshall, Bool.or_eq_true] at h
    rcases h with h | h
    · exact PathBelow.mono (Nat.le_succ k) (ih h)
    · by_cases hk : k < n
      · simp only [hk, ↓reduceDIte, Bool.and_eq_true] at h
        exact PathBelow.trans (PathBelow.mono (Nat.le_succ k) (ih h.1)) (Nat.lt_succ_self k)
          (PathBelow.mono (Nat.le_succ k) (ih h.2))
      · simp [hk] at h

theorem warshall_complete {r : Rel n} {k : Nat} {a b : Fin n} (h : PathBelow r k a b) :
    warshall r k a b = true := by
  induction k generalizing a b with
  | zero =>
    cases h with
    | edge hab => exact hab
    | trans _ hc _ => exact absurd hc (Nat.not_lt_zero _)
  | succ k ih =>
    simp only [warshall, Bool.or_eq_true]
    by_cases hk : k < n
    · rcases PathBelow.split hk h with h' | ⟨h₁, h₂⟩
      · exact Or.inl (ih h')
      · refine Or.inr ?_
        simp only [hk, ↓reduceDIte, Bool.and_eq_true]
        exact ⟨ih h₁, ih h₂⟩
    · exact Or.inl (ih (PathBelow.of_succ_of_le (by omega) h))

theorem warshall_iff_path {r : Rel n} {a b : Fin n} : warshall r n a b = true ↔ Path r a b :=
  ⟨fun h => (warshall_sound h).toPath, fun h => warshall_complete h.toPathBelow⟩

/-- Correctness of the Boolean acyclicity test. -/
theorem acyclicB_eq_true_iff {r : Rel n} : acyclicB r = true ↔ Acyclic r := by
  simp only [acyclicB, List.all_eq_true, Bool.not_eq_true']
  constructor
  · intro h a ha
    have := h a (List.mem_finRange a)
    rw [warshall_iff_path.mpr ha] at this
    exact absurd this (by decide)
  · intro h a _
    cases hw : warshall r n a a with
    | false => rfl
    | true => exact absurd (warshall_iff_path.mp hw) (h a)

instance instDecidableAcyclic (r : Rel n) : Decidable (Acyclic r) :=
  decidable_of_iff _ acyclicB_eq_true_iff

/-! ## Erasure of a vertex class (cycle shortening through `po`)

If every edge touching a vertex of class `E` is an edge of a strict order `p ⊆ s`, then cycles
of `s` can be shortened to avoid `E`: acyclicity of `s` restricted to `¬E` gives acyclicity of
`s`. This is used to erase fence events, and events on thread-local locations, from cycles. -/

/-- Restriction of `s` to vertices satisfying `keep`. -/
def restrict (keep : Fin n → Bool) (s : Rel n) : Rel n := fun a b => s a b && keep a && keep b

/-- Reflexive-transitive closure, as a `Prop`. -/
def Star (r : Rel n) (a b : Fin n) : Prop := a = b ∨ Path r a b

theorem Star.path_of_star_of_edge {r : Rel n} {a b c : Fin n} (h₁ : Star r a b)
    (h₂ : r b c = true) : Path r a c := by
  rcases h₁ with rfl | h₁
  · exact Path.single h₂
  · exact Path.tail h₁ h₂

theorem Star.of_path {r : Rel n} {a b : Fin n} (h : Path r a b) : Star r a b := Or.inr h

/-- The core shortening lemma (path form). For a path of `s` starting at a kept vertex `x`:
if it ends at a kept vertex it is a path of the restriction; if it ends at an erased vertex `y`,
some kept `z` is reachable in the restriction with `p z y`. -/
theorem restrict_path_aux {s p : Rel n} {keep : Fin n → Bool}
    (hps : Sub p s) (hptrans : ∀ a b c, p a b = true → p b c = true → p a c = true)
    (hE : ∀ a b, s a b = true → (keep a = false ∨ keep b = false) → p a b = true)
    {x y : Fin n} (hx : keep x = true) (h : Path s x y) :
    (keep y = true → Path (restrict keep s) x y) ∧
      (keep y = false → ∃ z, keep z = true ∧ Star (restrict keep s) x z ∧ p z y = true) := by
  induction h with
  | @single b hxb =>
    constructor
    · intro hb
      exact Path.single (by simp [restrict, hxb, hx, hb])
    · intro hb
      exact ⟨x, hx, Or.inl rfl, hE _ _ hxb (Or.inr hb)⟩
  | @tail c b _ hcb ih =>
    cases hc : keep c with
    | true =>
      have hxc := ih.1 hc
      constructor
      · intro hb
        exact Path.tail hxc (by simp [restrict, hcb, hc, hb])
      · intro hb
        exact ⟨c, hc, Star.of_path hxc, hE _ _ hcb (Or.inr hb)⟩
    | false =>
      obtain ⟨z, hz, hxz, hzc⟩ := ih.2 hc
      have hcb' : p c b = true := hE _ _ hcb (Or.inl hc)
      have hzb : p z b = true := hptrans _ _ _ hzc hcb'
      constructor
      · intro hb
        exact Star.path_of_star_of_edge hxz (by simp [restrict, hps _ _ hzb, hz, hb])
      · intro hb
        exact ⟨z, hz, hxz, hzb⟩

/-- Paths leaving an erased vertex: either they reach `y` through erased vertices only, giving
`p x y`, or they meet a first kept vertex `z` with `p x z`. -/
theorem path_from_erased {s p : Rel n} {keep : Fin n → Bool}
    (hptrans : ∀ a b c, p a b = true → p b c = true → p a c = true)
    (hE : ∀ a b, s a b = true → (keep a = false ∨ keep b = false) → p a b = true)
    {x y : Fin n} (hx : keep x = false) (h : Path s x y) :
    p x y = true ∨ ∃ z, keep z = true ∧ p x z = true ∧ Star s z y := by
  induction h with
  | @single b hxb => exact Or.inl (hE _ _ hxb (Or.inl hx))
  | @tail c b _ hcb ih =>
    rcases ih with hxc | ⟨z, hz, hxz, hzc⟩
    · cases hc : keep c with
      | false => exact Or.inl (hptrans _ _ _ hxc (hE _ _ hcb (Or.inl hc)))
      | true => exact Or.inr ⟨c, hc, hxc, Star.of_path (Path.single hcb)⟩
    · exact Or.inr ⟨z, hz, hxz, Star.of_path (Star.path_of_star_of_edge hzc hcb)⟩

/-- **Cycle shortening.** If every `s`-edge touching an erased vertex (`keep = false`) is an edge
of a transitive, irreflexive `p ⊆ s`, then `s` is acyclic as soon as its restriction to kept
vertices is. -/
theorem acyclic_of_acyclic_restrict {s p : Rel n} {keep : Fin n → Bool}
    (hps : Sub p s) (hptrans : ∀ a b c, p a b = true → p b c = true → p a c = true)
    (hpirr : ∀ a, p a a = false)
    (hE : ∀ a b, s a b = true → (keep a = false ∨ keep b = false) → p a b = true)
    (hres : Acyclic (restrict keep s)) : Acyclic s := by
  intro a ha
  cases hk : keep a with
  | true => exact hres a ((restrict_path_aux hps hptrans hE hk ha).1 hk)
  | false =>
    rcases path_from_erased hptrans hE hk ha with haa | ⟨z, hz, haz, hza⟩
    · rw [hpirr a] at haa; exact absurd haa (by decide)
    · have hzz : Path s z z := by
        rcases hza with rfl | hza
        · rw [hz] at hk; exact absurd hk (by decide)
        · exact Path.tail hza (hps _ _ haz)
      exact hres z ((restrict_path_aux hps hptrans hE hz hzz).1 hz)

/-- If every edge of `s` ends at a kept vertex, every cycle of `s` stays among kept vertices:
acyclicity of the restriction gives acyclicity of `s`. -/
theorem acyclic_of_acyclic_restrict_of_targets {s : Rel n} {keep : Fin n → Bool}
    (htgt : ∀ a b, s a b = true → keep b = true) (hres : Acyclic (restrict keep s)) :
    Acyclic s := by
  have tgt : ∀ {x y}, Path s x y → keep y = true := by
    intro x y h
    cases h with
    | single hxy => exact htgt _ _ hxy
    | tail _ hcy => exact htgt _ _ hcy
  have key : ∀ {x y}, Path s x y → keep x = true → Path (restrict keep s) x y := by
    intro x y h hx
    induction h with
    | single hxy => exact Path.single (by simp [restrict, hxy, hx, htgt _ _ hxy])
    | @tail c b hxc hcb ih =>
      exact Path.tail ih (by simp [restrict, hcb, tgt hxc, htgt _ _ hcb])
  intro a ha
  exact hres a (key ha (tgt ha))

end Rel

end Toy.WMM
