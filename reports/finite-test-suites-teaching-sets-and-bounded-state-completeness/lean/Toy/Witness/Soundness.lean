/-
Operational meaning of passing a finite test suite: exact characterization of
certification via `PassingInClass` (with `SubClass` as a strictly stronger
sufficient corollary), and the off-suite splicing converse showing that without
class membership, every off-suite behavior differing from `h` at an untested
input is realized by some passing function outside `H`.
-/
import Toy.Witness.Core
import Toy.Witness.Unrestricted
import Toy.Witness.Conjunctions

namespace Toy.Witness

universe u v

/-- `SubClass C H` holds when every implementation in class `C` belongs to
hypothesis class `H`. Captures an independent guarantee (such as a static
analysis, language restriction, or state bound) confining all candidate
implementations to `H`. -/
def SubClass {X : Type u} {Y : Type v}
    (C H : HypothesisClass X Y) : Prop :=
  ∀ f : X → Y, C f → H f

/-- `PassingInClass C H S` holds when every implementation in `C` that passes
labeled sample `S` belongs to hypothesis class `H`. Strictly weaker than
`SubClass C H` (failing implementations in `C` need not lie in `H`), and exact
as the class-membership condition characterizing when passing `S` certifies
equality with `h`. -/
def PassingInClass {X : Type u} {Y : Type v}
    (C H : HypothesisClass X Y) (S : List (X × Y)) : Prop :=
  ∀ f : X → Y, C f → Consistent S f → H f

/-- Every subclass containment `SubClass C H` implies `PassingInClass C H S`. -/
theorem subClass_implies_passingInClass {X : Type u} {Y : Type v}
    {C H : HypothesisClass X Y} {S : List (X × Y)}
    (hSub : SubClass C H) : PassingInClass C H S :=
  fun f hC _ => hSub f hC

/-- Splice of `h` on the inputs tested by `S` with an arbitrary off-suite
behavior `outside` on every untested input. -/
noncomputable def spliceOutside {X : Type u} {Y : Type v}
    (h outside : X → Y) (S : List (X × Y)) : X → Y :=
  open Classical in
  fun x => if x ∈ S.map Prod.fst then h x else outside x

theorem spliceOutside_of_mem {X : Type u} {Y : Type v}
    (h outside : X → Y) (S : List (X × Y)) {x : X}
    (hx : x ∈ S.map Prod.fst) :
    spliceOutside h outside S x = h x := by
  classical
  simp [spliceOutside, hx]

theorem spliceOutside_of_not_mem {X : Type u} {Y : Type v}
    (h outside : X → Y) (S : List (X × Y)) {x : X}
    (hx : x ∉ S.map Prod.fst) :
    spliceOutside h outside S x = outside x := by
  classical
  simp [spliceOutside, hx]

theorem spliceOutside_consistent {X : Type u} {Y : Type v}
    (h outside : X → Y) (S : List (X × Y))
    (hcon : Consistent S h) :
    Consistent S (spliceOutside h outside S) := by
  intro p hp
  have hmem : p.1 ∈ S.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [spliceOutside_of_mem h outside S hmem]
  exact hcon p hp

/-! ### Definition Positive and Negative Examples -/

theorem subClass_pos_example :
    SubClass ConstBoolClass (fun (_ : Bool → Bool) => True) :=
  fun _ _ => trivial

theorem subClass_neg_example :
    ¬ SubClass (fun (_ : Bool → Bool) => True) ConstBoolClass := by
  intro hSub
  exact isUnrestricted_neg_example (fun f => hSub f trivial)

/-- Positive example for `PassingInClass` that simultaneously proves
`PassingInClass` is strictly weaker than `SubClass`: adding `id` to
`ConstBoolClass` violates `SubClass C ConstBoolClass`, yet every member of `C`
passing `[(false, true)]` belongs to `ConstBoolClass`. -/
theorem passingInClass_pos_example :
    let C : HypothesisClass Bool Bool := fun f => ConstBoolClass f ∨ f = id
    let S : List (Bool × Bool) := [(false, true)]
    PassingInClass C ConstBoolClass S ∧ ¬ SubClass C ConstBoolClass := by
  refine ⟨?_, ?_⟩
  · intro f hC hcon
    rcases hC with hH | rfl
    · exact hH
    · have := hcon (false, true) (by simp); cases this
  · intro hSub
    rcases hSub id (Or.inr rfl) with heq | heq
    · have := congrFun heq true; cases this
    · have := congrFun heq false; cases this

theorem passingInClass_neg_example :
    ¬ PassingInClass (fun (_ : Bool → Bool) => True) ConstBoolClass [(false, true)] := by
  intro hPass
  have hcon : Consistent [(false, true)] Bool.not := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  rcases hPass Bool.not trivial hcon with heq | heq
  · have := congrFun heq false; cases this
  · have := congrFun heq true; cases this

/-- Explicit witness that certification can hold even when `SubClass C H` fails. -/
theorem certification_holds_although_C_escapes_H :
    let C : HypothesisClass Bool Bool := fun f => ConstBoolClass f ∨ f = id
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    ¬ SubClass C ConstBoolClass ∧
    Teaches ConstBoolClass h S ∧
    (∀ impl : Bool → Bool, C impl → Consistent S impl → impl = h) := by
  refine ⟨passingInClass_pos_example.2, teaches_pos_example, ?_⟩
  intro impl hC hcon
  exact teaches_pos_example.2.2 impl (passingInClass_pos_example.1 impl hC hcon) hcon

/-! ### Result 17: Exact Operational Meaning of a Passed Suite (Reference Point) -/

/-- Exact certification characterization: whenever `h ∈ H` is the unique member
of `H` consistent with labeled suite `S` (in particular whenever `Teaches H h S`),
every implementation `impl ∈ C` passing `S` equals `h` if and only if every
`S`-passing member of `C` lies in `H` (`PassingInClass C H S`). -/
theorem passed_suite_certifies_iff_passingInClass
    {X : Type u} {Y : Type v}
    (C H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hh : H h)
    (huniq : UniqueConsistent H h S) :
    (∀ impl : X → Y, C impl → Consistent S impl → impl = h) ↔ PassingInClass C H S := by
  constructor
  · intro hCert f hC hPass
    rw [hCert f hC hPass]
    exact hh
  · intro hPassIn impl hC hPass
    exact huniq impl (hPassIn impl hC hPass) hPass

/-- Immediate corollary taking `Teaches H h S` (note: only the `H h` and
`UniqueConsistent H h S` conjuncts of `Teaches` are used). -/
theorem passed_teaching_suite_certifies_iff_passingInClass
    {X : Type u} {Y : Type v}
    (C H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hTeach : Teaches H h S) :
    (∀ impl : X → Y, C impl → Consistent S impl → impl = h) ↔ PassingInClass C H S :=
  passed_suite_certifies_iff_passingInClass C H h S hTeach.1 hTeach.2.2

/-- Sufficient-condition corollary: if `SubClass C H` and `Teaches H h S`, then
every implementation `impl ∈ C` passing `S` equals `h`. (`SubClass C H` is
sufficient, not necessary: see `certification_holds_although_C_escapes_H`.) -/
theorem passed_teaching_suite_certifies_subclass
    {X : Type u} {Y : Type v}
    (C H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hSub : SubClass C H)
    (hTeach : Teaches H h S) :
    ∀ impl : X → Y, C impl → Consistent S impl → impl = h :=
  (passed_teaching_suite_certifies_iff_passingInClass C H h S hTeach).mpr
    (subClass_implies_passingInClass hSub)

/-- Non-vacuity witness for `passed_suite_certifies_iff_passingInClass`. -/
theorem passed_suite_certifies_iff_passingInClass_nonvacuity :
    ConstBoolClass (fun _ => true) ∧
    UniqueConsistent ConstBoolClass (fun _ => true) [(false, true)] :=
  ⟨Or.inr rfl, uniqueConsistent_pos_example⟩

/-- Canonical tightness counterexample for `hh : H h` in
`passed_suite_certifies_iff_passingInClass`: when `H` is empty, `UniqueConsistent`
holds vacuously and `C = {const true}` satisfies certification trivially, yet
`PassingInClass C H S` fails because `h ∉ H`. -/
theorem passed_suite_certifies_iff_ce_not_in_H :
    let C : HypothesisClass Bool Bool := fun f => f = (fun _ => true)
    let H : HypothesisClass Bool Bool := fun _ => False
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    ¬ H h ∧
    UniqueConsistent H h S ∧
    ¬ ((∀ impl : Bool → Bool, C impl → Consistent S impl → impl = h) ↔
       PassingInClass C H S) := by
  refine ⟨fun hf => hf, fun _ hg _ => hg.elim, ?_⟩
  intro hiff
  have hCert : ∀ impl : Bool → Bool,
      impl = (fun _ => true) → Consistent [(false, true)] impl → impl = (fun _ => true) :=
    fun _ hC _ => hC
  exact (hiff.mp hCert) (fun _ => true) rfl teaches_pos_example.2.1

/-- Canonical tightness counterexample for `huniq : UniqueConsistent H h S` in
`passed_suite_certifies_iff_passingInClass`: when `H` is unrestricted and
`C = H`, `PassingInClass C H S` holds trivially, yet `Bool.not` passes `S` and
differs from `const true`. -/
theorem passed_suite_certifies_iff_ce_not_unique :
    let H : HypothesisClass Bool Bool := fun _ => True
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    H h ∧
    ¬ UniqueConsistent H h S ∧
    ¬ ((∀ impl : Bool → Bool, H impl → Consistent S impl → impl = h) ↔
       PassingInClass H H S) := by
  refine ⟨trivial, uniqueConsistent_neg_example, ?_⟩
  intro hiff
  have hCert := hiff.mpr (fun _ hC _ => hC)
  have hcon : Consistent [(false, true)] Bool.not := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  have heq := hCert Bool.not trivial hcon
  have := congrFun heq true
  cases this

/-- Counterexample showing `SubClass C H` cannot be dropped unconditionally in
`passed_teaching_suite_certifies_subclass` (here `C` is unrestricted and
`H = MonotoneConjunctions 2`). -/
theorem passed_teaching_suite_ce_not_subclass :
    let C : HypothesisClass (BoolAssignment 2) Bool := fun _ => True
    let H : HypothesisClass (BoolAssignment 2) Bool := MonotoneConjunctions 2
    let V : Fin 2 → Bool := fun _ => true
    let h : BoolAssignment 2 → Bool := evalMonotoneConj V
    let S : List (BoolAssignment 2 × Bool) := monotoneConjTeachingSet V
    ¬ SubClass C H ∧
    Teaches H h S ∧
    ¬ (∀ impl : BoolAssignment 2 → Bool, C impl → Consistent S impl → impl = h) := by
  let C : HypothesisClass (BoolAssignment 2) Bool := fun _ => True
  let H : HypothesisClass (BoolAssignment 2) Bool := MonotoneConjunctions 2
  let V : Fin 2 → Bool := fun _ => true
  let h : BoolAssignment 2 → Bool := evalMonotoneConj V
  let S : List (BoolAssignment 2 × Bool) := monotoneConjTeachingSet V
  have hT : Teaches H h S := monotone_conj_m2_all_teaches.1
  refine ⟨?_, hT, ?_⟩
  · intro hSub
    exact monotoneConjunctions_neg_example_const_false (hSub (fun _ => false) trivial)
  · intro hall
    let x₀ : BoolAssignment 2 := fun _ => false
    have hnotmem : x₀ ∉ S.map Prod.fst := by
      intro hmem
      simp only [S, V, monotoneConjTeachingSet_m2_all, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with heq | heq
      · have h1 := congrFun heq 1
        cases h1
      · have h0 := congrFun heq 0
        cases h0
    let impl := spliceOutside h (fun _ => true) S
    have hcon : Consistent S impl := spliceOutside_consistent h (fun _ => true) S hT.2.1
    have heq := hall impl trivial hcon
    have hval := congrFun heq x₀
    dsimp only [impl] at hval
    rw [spliceOutside_of_not_mem h (fun _ => true) S hnotmem] at hval
    have hx0 : evalMonotoneConj (fun _ : Fin 2 => true) x₀ = false := by decide
    rw [hx0] at hval
    cases hval

/-! ### Result 18: Off-Suite Splicing Converse (Minimal Hypotheses) -/

/-- Whenever `S` is consistent with `h` and `h` is the unique member of `H`
consistent with `S` (in particular whenever `Teaches H h S`), for any
off-suite function `outside` disagreeing with `h` at an untested input `x₀`,
the explicit splice `spliceOutside h outside S` passes `S`, matches `outside`
on every untested input, differs from `h`, and lies outside `H`. (Note: does
not assume `H h` and does not mention an external implementation class `C`.) -/
theorem splice_consistent_escapes_class_of_unique
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h outside : X → Y) (S : List (X × Y))
    (x₀ : X)
    (hcon : Consistent S h)
    (huniq : UniqueConsistent H h S)
    (hUntested : x₀ ∉ S.map Prod.fst)
    (hDiff : outside x₀ ≠ h x₀) :
    let impl := spliceOutside h outside S
    Consistent S impl ∧
    (∀ x : X, x ∉ S.map Prod.fst → impl x = outside x) ∧
    impl ≠ h ∧
    ¬ H impl := by
  let impl := spliceOutside h outside S
  have hconImpl : Consistent S impl := spliceOutside_consistent h outside S hcon
  have hoff : ∀ x : X, x ∉ S.map Prod.fst → impl x = outside x :=
    fun x hx => spliceOutside_of_not_mem h outside S hx
  have hne : impl ≠ h := by
    intro heq
    have hval := congrFun heq x₀
    rw [hoff x₀ hUntested] at hval
    exact hDiff hval
  have hnotH : ¬ H impl := fun hH => hne (huniq impl hH hconImpl)
  exact ⟨hconImpl, hoff, hne, hnotH⟩

/-- Corollary taking `Teaches H h S` (note: only `hTeach.2.1` and `hTeach.2.2`
are used, not `hTeach.1`). -/
theorem passed_teaching_suite_without_class_bound_escapes_class
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h outside : X → Y) (S : List (X × Y))
    (x₀ : X)
    (hTeach : Teaches H h S)
    (hUntested : x₀ ∉ S.map Prod.fst)
    (hDiff : outside x₀ ≠ h x₀) :
    let impl := spliceOutside h outside S
    Consistent S impl ∧
    (∀ x : X, x ∉ S.map Prod.fst → impl x = outside x) ∧
    impl ≠ h ∧
    ¬ H impl :=
  splice_consistent_escapes_class_of_unique H h outside S x₀
    hTeach.2.1 hTeach.2.2 hUntested hDiff

/-- Non-vacuity witness for `splice_consistent_escapes_class_of_unique`. -/
theorem splice_consistent_escapes_class_of_unique_nonvacuity :
    Consistent [(false, true)] (fun (_ : Bool) => true) ∧
    UniqueConsistent ConstBoolClass (fun _ => true) [(false, true)] ∧
    (true : Bool) ∉ ([(false, true)] : List (Bool × Bool)).map Prod.fst ∧
    (fun (_ : Bool) => false) true ≠ (fun (_ : Bool) => true) true :=
  ⟨teaches_pos_example.2.1, uniqueConsistent_pos_example, by simp, by decide⟩

/-- Canonical tightness counterexample for `hcon : Consistent S h` in
`splice_consistent_escapes_class_of_unique`: with `H` empty, `UniqueConsistent`
holds vacuously, yet `S = [(false, false)]` is inconsistent with `const true`
and therefore also inconsistent with `spliceOutside`. -/
theorem splice_consistent_escapes_class_ce_inconsistent :
    let H : HypothesisClass Bool Bool := fun _ => False
    let h : Bool → Bool := fun _ => true
    let outside : Bool → Bool := fun _ => false
    let S : List (Bool × Bool) := [(false, false)]
    ¬ Consistent S h ∧
    UniqueConsistent H h S ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    outside true ≠ h true ∧
    ¬ (let impl := spliceOutside h outside S
       Consistent S impl ∧
       (∀ x : Bool, x ∉ S.map Prod.fst → impl x = outside x) ∧
       impl ≠ h ∧
       ¬ H impl) := by
  refine ⟨?_, fun _ hg _ => hg.elim, by simp, by decide, ?_⟩
  · intro hcon
    have := hcon (false, false) (by simp)
    cases this
  · intro ⟨hconImpl, _, _, _⟩
    have hval := hconImpl (false, false) (by simp)
    rw [spliceOutside_of_mem _ _ _ (by simp)] at hval
    cases hval

/-- Canonical tightness counterexample for `huniq : UniqueConsistent H h S` in
`splice_consistent_escapes_class_of_unique`: when `H` is unrestricted, the
spliced implementation belongs to `H`, so `¬ H impl` fails. -/
theorem splice_consistent_escapes_class_ce_not_unique :
    let H : HypothesisClass Bool Bool := fun _ => True
    let h : Bool → Bool := fun _ => true
    let outside : Bool → Bool := fun _ => false
    let S : List (Bool × Bool) := [(false, true)]
    Consistent S h ∧
    ¬ UniqueConsistent H h S ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    outside true ≠ h true ∧
    ¬ (let impl := spliceOutside h outside S
       Consistent S impl ∧
       (∀ x : Bool, x ∉ S.map Prod.fst → impl x = outside x) ∧
       impl ≠ h ∧
       ¬ H impl) := by
  refine ⟨teaches_pos_example.2.1, uniqueConsistent_neg_example, by simp, by decide, ?_⟩
  intro ⟨_, _, _, hnotH⟩
  exact hnotH trivial

/-- Canonical tightness counterexample for `hUntested : x₀ ∉ S.map Prod.fst` in
`splice_consistent_escapes_class_of_unique`: when `S` tests every input in
`Bool`, `spliceOutside h outside S = h`, so `impl ≠ h` and `¬ H impl` fail. -/
theorem splice_consistent_escapes_class_ce_tested :
    let h : Bool → Bool := fun _ => true
    let outside : Bool → Bool := fun _ => false
    let S : List (Bool × Bool) := [(false, true), (true, true)]
    Consistent S h ∧
    UniqueConsistent ConstBoolClass h S ∧
    ¬ ((true : Bool) ∉ S.map Prod.fst) ∧
    outside true ≠ h true ∧
    ¬ (let impl := spliceOutside h outside S
       Consistent S impl ∧
       (∀ x : Bool, x ∉ S.map Prod.fst → impl x = outside x) ∧
       impl ≠ h ∧
       ¬ ConstBoolClass impl) := by
  have hcon : Consistent [(false, true), (true, true)] (fun _ => true) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  have huniq : UniqueConsistent ConstBoolClass (fun _ => true) [(false, true), (true, true)] := by
    intro g hg hcg
    rcases hg with rfl | rfl
    · have := hcg (false, true) (by simp); cases this
    · rfl
  refine ⟨hcon, huniq, by simp, by decide, ?_⟩
  intro ⟨_, _, hne, _⟩
  apply hne
  funext b
  cases b
  · exact spliceOutside_of_mem _ _ _ (by simp)
  · exact spliceOutside_of_mem _ _ _ (by simp)

/-- Canonical tightness counterexample for `hDiff : outside x₀ ≠ h x₀` in
`splice_consistent_escapes_class_of_unique`: when `outside = h`,
`spliceOutside h h S = h`, so `impl ≠ h` and `¬ H impl` fail. -/
theorem splice_consistent_escapes_class_ce_agrees :
    let h : Bool → Bool := fun _ => true
    let outside : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    Consistent S h ∧
    UniqueConsistent ConstBoolClass h S ∧
    (true : Bool) ∉ S.map Prod.fst ∧
    ¬ (outside true ≠ h true) ∧
    ¬ (let impl := spliceOutside h outside S
       Consistent S impl ∧
       (∀ x : Bool, x ∉ S.map Prod.fst → impl x = outside x) ∧
       impl ≠ h ∧
       ¬ ConstBoolClass impl) := by
  refine ⟨teaches_pos_example.2.1, uniqueConsistent_pos_example, by simp, fun h => h rfl, ?_⟩
  intro ⟨_, _, hne, _⟩
  apply hne
  funext b
  classical
  simp [spliceOutside]

end Toy.Witness
