import ToySsa.Cfg

/-!
Boolean checkers with soundness lemmas, used to discharge facts about concrete graphs by
`decide`. Each checker is only claimed sound in the direction stated by its lemma.
-/
namespace Toy.Ssa

variable {n : Nat}

/-- Boolean walk check. -/
def isWalkB (G : Cfg n) : Fin n → Fin n → List (Fin n) → Bool
  | _, _, [] => false
  | a, b, [c] => decide (a = c) && decide (c = b)
  | a, b, c :: d :: rest => decide (a = c) && G.edge c d && isWalkB G d b (d :: rest)

theorem walk_of_isWalkB {G : Cfg n} : ∀ {a b : Fin n} {p : List (Fin n)},
    isWalkB G a b p = true → Walk G a b p
  | _, _, [] => by simp [isWalkB]
  | a, b, [c] => by
      simp only [isWalkB, Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨rfl, rfl⟩; exact Walk.single _
  | a, b, c :: d :: rest => by
      simp only [isWalkB, Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨⟨rfl, he⟩, hw⟩
      exact Walk.cons he (walk_of_isWalkB hw)

/-- One round of "reachable from the entry while avoiding `a`". -/
def stepAvoid (G : Cfg n) (a : Fin n) (R : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => R.contains v || (!decide (v = a) && R.any (fun u => G.edge u v)))

/-- Nodes reached from the entry while avoiding `a`, after `k` rounds. -/
def reachAvoid (G : Cfg n) (a : Fin n) : Nat → List (Fin n)
  | 0 => if G.entry = a then [] else [G.entry]
  | k + 1 => stepAvoid G a (reachAvoid G a k)

/-- Characteristic function of `reachAvoid G a n`. -/
def avoidSet (G : Cfg n) (a : Fin n) (v : Fin n) : Bool := (reachAvoid G a n).contains v

theorem walk_of_mem_reachAvoid {G : Cfg n} {a : Fin n} :
    ∀ (k : Nat) {v : Fin n}, v ∈ reachAvoid G a k → ∃ p, Walk G G.entry v p ∧ a ∉ p
  | 0, v, h => by
      unfold reachAvoid at h
      split at h
      · simp at h
      · rename_i hne
        simp at h; subst h
        exact ⟨[G.entry], Walk.single _, by simpa [eq_comm] using hne⟩
  | k + 1, v, h => by
      simp only [reachAvoid, stepAvoid, List.mem_filter, Bool.or_eq_true, Bool.and_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true, List.contains_iff_mem] at h
      rcases h.2 with h1 | ⟨hva, u, hu, he⟩
      · exact walk_of_mem_reachAvoid k h1
      · obtain ⟨p, hp, hap⟩ := walk_of_mem_reachAvoid k hu
        refine ⟨p ++ [v], hp.append_edge he, ?_⟩
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hap, fun h => hva h.symm⟩

/-- Nodes in `avoidSet G a` are not dominated by `a`. -/
theorem not_dom_of_avoidSet {G : Cfg n} {a b : Fin n} (h : avoidSet G a b = true) :
    ¬ Dom G a b := by
  obtain ⟨p, hp, hap⟩ := walk_of_mem_reachAvoid n (by simpa [avoidSet] using h)
  exact not_dom_of_walk hp hap

/-- Boolean dominance certificate check: `avoidSet G a` contains the entry (unless it is `a`),
is closed under edges except into `a`, and excludes `b`. -/
def domCheck (G : Cfg n) (a b : Fin n) : Bool :=
  (decide (G.entry = a) || avoidSet G a G.entry) &&
  (List.finRange n).all (fun u => (List.finRange n).all (fun v =>
    !(avoidSet G a u && G.edge u v) || decide (v = a) || avoidSet G a v)) &&
  !avoidSet G a b

theorem dom_of_domCheck {G : Cfg n} {a b : Fin n} (h : domCheck G a b = true) : Dom G a b := by
  simp only [domCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies, Bool.not_eq_true'] at h
  obtain ⟨⟨hentry, hcl⟩, hb⟩ := h
  refine dom_of_cert G a b (avoidSet G a) hentry ?_ hb
  intro u v hu he
  have := hcl u v
  simp [hu, he] at this
  exact this

/-- Decides dominance on concrete graphs (sound in both directions by the two lemmas above
whenever it returns a definite answer through `domCheck` or `avoidSet`). -/
theorem dom_iff_check {G : Cfg n} {a b : Fin n} (h : domCheck G a b = true ∨ avoidSet G a b = true) :
    (Dom G a b ↔ domCheck G a b = true) := by
  rcases h with h | h
  · exact ⟨fun _ => h, fun _ => dom_of_domCheck h⟩
  · constructor
    · intro hd; exact absurd hd (not_dom_of_avoidSet h)
    · intro hc; exact dom_of_domCheck hc

/-- Refutes `DF G x y`: every predecessor of `y` avoids domination by `x`, or `x` strictly
dominates `y`. -/
def notDFCheck (G : Cfg n) (x y : Fin n) : Bool :=
  (List.finRange n).all (fun p => !G.edge p y || avoidSet G x p) ||
  (domCheck G x y && !decide (x = y))

theorem not_df_of_check {G : Cfg n} {x y : Fin n} (h : notDFCheck G x y = true) : ¬ DF G x y := by
  rintro ⟨⟨p, hp, hdom⟩, hns⟩
  simp only [notDFCheck, Bool.or_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h with h | ⟨hd, hne⟩
  · have := h p
    simp [hp] at this
    exact not_dom_of_avoidSet this hdom
  · exact hns ⟨dom_of_domCheck hd, hne⟩

/-- Establishes `DF G x y` via a predecessor `p`. -/
def dfCheck (G : Cfg n) (x y p : Fin n) : Bool :=
  G.edge p y && domCheck G x p && (decide (x = y) || avoidSet G x y)

theorem df_of_check {G : Cfg n} {x y p : Fin n} (h : dfCheck G x y p = true) : DF G x y := by
  simp only [dfCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨he, hd⟩, hxy⟩ := h
  refine ⟨⟨p, he, dom_of_domCheck hd⟩, ?_⟩
  rintro ⟨hdom, hne⟩
  rcases hxy with h | h
  · exact hne h
  · exact not_dom_of_avoidSet h hdom

/-- `DF⁺(S)` is contained in every set `T` that is closed in the sense `DF(S ∪ T) ⊆ T`;
the closure is checked through `notDFCheck`. -/
def idfSubsetCheck (G : Cfg n) (S T : Fin n → Bool) : Bool :=
  (List.finRange n).all (fun x => (List.finRange n).all (fun y =>
    !(S x || T x) || T y || notDFCheck G x y))

theorem idf_subset_of_check {G : Cfg n} {S T : Fin n → Bool} (h : idfSubsetCheck G S T = true) :
    ∀ {y : Fin n}, IDF G (fun x => S x = true) y → T y = true := by
  have hc : ∀ x y, (S x = true ∨ T x = true) → DF G x y → T y = true := by
    intro x y hx hdf
    simp only [idfSubsetCheck, List.all_eq_true, List.mem_finRange, true_implies] at h
    have := h x y
    have hx' : (S x || T x) = true := by simpa [Bool.or_eq_true] using hx
    simp only [hx', Bool.not_true, Bool.false_or, Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd hdf (not_df_of_check h1)
  intro y hy
  induction hy with
  | base hx hdf => exact hc _ _ (Or.inl hx) hdf
  | step _ hdf ih => exact hc _ _ (Or.inr ih) hdf

/-- Nodes reachable from the successors of `u` through nodes outside `Defs`, after `k` rounds
(nodes in `Defs` are recorded but not expanded). -/
def clearSet (G : Cfg n) (Defs : Fin n → Bool) (u : Fin n) : Nat → List (Fin n)
  | 0 => (List.finRange n).filter (fun v => G.edge u v)
  | k + 1 =>
    let R := clearSet G Defs u k
    (List.finRange n).filter (fun w => R.contains w || R.any (fun v => !Defs v && G.edge v w))

/-- Refutes `ReachesTop G Defs u b` via the closure certificate `clearSet G Defs u n`. -/
def notRTCheck (G : Cfg n) (Defs : Fin n → Bool) (u b : Fin n) : Bool :=
  let R := clearSet G Defs u n
  !Defs u ||
  ((List.finRange n).all (fun v => !G.edge u v || R.contains v) &&
   (List.finRange n).all (fun v => (List.finRange n).all (fun w =>
      !(R.contains v && !Defs v && G.edge v w) || R.contains w)) &&
   !R.contains b)

theorem not_reachesTop_of_check {G : Cfg n} {Defs : Fin n → Bool} {u b : Fin n}
    (h : notRTCheck G Defs u b = true) : ¬ ReachesTop G (fun w => Defs w = true) u b := by
  simp only [notRTCheck, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  rcases h with h | ⟨⟨hs, hcl⟩, hb⟩
  · rintro ⟨hu, _⟩; simp_all
  · refine not_reachesTop_of_cert G _ u b (fun v => (clearSet G Defs u n).contains v) ?_ ?_ ?_
    · intro v he; have := hs v; simp_all
    · intro v w hv hnd he
      have := hcl v w
      simp only [Bool.not_eq_true] at hnd
      simp_all
    · simpa using hb

/-- Single-reaching-definition check: for every non-entry block without a φ and every pair of
distinct definition points, one of them is refuted by `notRTCheck`. -/
def srdCheck (G : Cfg n) (D P : Fin n → Bool) : Bool :=
  (List.finRange n).all (fun b => P b || decide (b = G.entry) ||
    (List.finRange n).all (fun u => (List.finRange n).all (fun v =>
      decide (u = v) || notRTCheck G (fun w => D w || P w) u b ||
        notRTCheck G (fun w => D w || P w) v b)))

theorem srd_of_check {G : Cfg n} {D P : Fin n → Bool} (h : srdCheck G D P = true) :
    SingleReachingDef G (fun w => D w = true) (fun w => P w = true) := by
  intro b hb hbe u v hu hv
  simp only [srdCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h b with (h1 | h1) | h1
  · exact absurd h1 hb
  · exact absurd h1 hbe
  · have hDefs : (fun w => D w = true ∨ P w = true) = (fun w => (D w || P w) = true) := by
      funext w; simp [Bool.or_eq_true]
    rw [hDefs] at hu hv
    rcases h1 u v with (h2 | h2) | h2
    · exact h2
    · exact absurd hu (not_reachesTop_of_check h2)
    · exact absurd hv (not_reachesTop_of_check h2)

end Toy.Ssa
