import ToyDirCC.Cert
import ToyDirCC.Outcome

/-!
# Extraction from a directed e-graph: orientation and well-foundedness

A directed e-graph assigns to each class id a list of e-nodes (a variable, or an operator
applied to child class ids). Its intended meaning is given by a *class denotation*
`den : Nat → M.C` (in practice: the value of the source term the class was created for) and
the invariant `Oriented`: every e-node of class `c`, read with its children replaced by
their class denotations, **refines** `den c`.

An extractor is a partial choice `ch : Nat → Option (ENode Op)` of one e-node per class.
`extract ch fuel c` unfolds the choice from class `c` into a term, or returns `none` if it
runs out of fuel or meets a class without a choice.

Results:
* `extract_refines_of_chosenOriented_mono`: if every chosen e-node refines its class
  denotation (`ChosenOriented`, implied by `Oriented` plus `ChoiceIn`) and extraction returns
  a term, the term refines the class denotation — provided the model is transitive and every
  argument position of every chosen e-node is declared `mono` and is monotone.
  `extract_refines_of_oriented_mono` is the e-graph form.
  `extract_unoriented_counterexample`: relating e-nodes to their class in
  *either* direction (as a symmetric e-class does) is not enough.
* `extract_total_and_sound_of_wfBelow_oriented_mono`: if the choice is well-founded below
  `c` (`WFBelow`), extraction terminates and the result refines `den c`. Termination holds
  exactly for well-founded choices (`extract_isSome_iff_wfBelow`).
  `extract_cycle_counterexample`: in a cyclic class with `x ≤ f x` and
  `f x ≤ x`, the choice that follows the cycle never terminates, and no finite term solves
  the cycle equation.

`extract` produces an unshared tree: a class chosen below several parents is unfolded once
per use, and the tree can be exponentially larger than the choice graph.
-/

namespace Toy.DirCC

variable {Op : Type}

/-- An e-node: a variable, or an operator applied to child class ids. -/
inductive ENode (Op : Type) where
  | var (x : Nat)
  | app (f : Op) (kids : List Nat)
deriving Repr, DecidableEq

/-- A directed e-graph: the e-nodes of each class id. -/
structure EGraph (Op : Type) where
  nodes : Nat → List (ENode Op)

/-- An extractor's choice: at most one e-node per class. -/
abbrev Choice (Op : Type) := Nat → Option (ENode Op)

/-- All entries are `some`: collect them; otherwise `none`. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some a :: rest => (allSome rest).map (a :: ·)

/-- Unfold the choice from class `c` with at most `fuel` nested steps. -/
def extract (ch : Choice Op) : Nat → Nat → Option (Term Op)
  | 0, _ => none
  | fuel + 1, c =>
    match ch c with
    | none => none
    | some (.var x) => some (.var x)
    | some (.app f ks) => (allSome (ks.map (extract ch fuel))).map (.app f)

/-- The value of an e-node when each child is read as its class denotation. -/
def nodeVal (M : Model Op) (ρ : Nat → M.C) (den : Nat → M.C) : ENode Op → M.C
  | .var x => ρ x
  | .app f ks => M.interp f (ks.map den)

/-- Orientation invariant: every e-node of class `c` refines the class denotation. -/
def Oriented (M : Model Op) (ρ : Nat → M.C) (G : EGraph Op) (den : Nat → M.C) : Prop :=
  ∀ c n, n ∈ G.nodes c → M.le (den c) (nodeVal M ρ den n)

/-- Weakened invariant: every e-node is related to its class denotation in *some*
direction (what a symmetric e-class guarantees about a mixture of directed facts). -/
def RelatedEitherWay (M : Model Op) (ρ : Nat → M.C) (G : EGraph Op) (den : Nat → M.C) :
    Prop :=
  ∀ c n, n ∈ G.nodes c → M.le (den c) (nodeVal M ρ den n) ∨ M.le (nodeVal M ρ den n) (den c)

/-- The choice only picks e-nodes of the class. -/
def ChoiceIn (G : EGraph Op) (ch : Choice Op) : Prop := ∀ c n, ch c = some n → n ∈ G.nodes c

/-- Every argument position of every chosen e-node is declared `mono`. -/
def ChosenMono (P : Profile Op) (ch : Choice Op) : Prop :=
  ∀ c f ks, ch c = some (.app f ks) → ∀ i, i < ks.length → P f i = .mono

/-- The choice is well-founded below `c` (accessibility in the choice graph): unfolding it
from `c` reaches only classes with a choice and has no infinite descending path. Class ids
are unbounded, so "no cycle" is not enough: `chInf_acyclic_total_not_wfBelow` is a choice
with no cycle and a choice at every class that is not well-founded. In a choice graph with
finitely many classes reachable from `c`, the two notions agree. -/
inductive WFBelow (ch : Choice Op) : Nat → Prop
  | var {c x : Nat} : ch c = some (.var x) → WFBelow ch c
  | app {c : Nat} {f : Op} {ks : List Nat} :
      ch c = some (.app f ks) → (∀ k, k ∈ ks → WFBelow ch k) → WFBelow ch c

/-- Weakest orientation hypothesis used by extraction: every *chosen* e-node refines the
denotation of its class. -/
def ChosenOriented (M : Model Op) (ρ : Nat → M.C) (den : Nat → M.C) (ch : Choice Op) : Prop :=
  ∀ c n, ch c = some n → M.le (den c) (nodeVal M ρ den n)

/-- An oriented e-graph and a choice inside it give a chosen-oriented choice. -/
theorem chosenOriented_of_oriented {M : Model Op} {ρ : Nat → M.C} {G : EGraph Op}
    {den : Nat → M.C} {ch : Choice Op} (hO : Oriented M ρ G den) (hC : ChoiceIn G ch) :
    ChosenOriented M ρ den ch :=
  fun c n h => hO c n (hC c n h)

/-! ## Termination of extraction -/

theorem allSome_eq_some_iff {α : Type} :
    ∀ {xs : List (Option α)} {ys : List α}, allSome xs = some ys ↔ xs = ys.map some
  | [], [] => by simp [allSome]
  | [], _ :: _ => by simp [allSome]
  | none :: _, ys => by cases ys <;> simp [allSome]
  | some a :: rest, [] => by simp [allSome]
  | some a :: rest, b :: bs => by
    simp only [allSome, Option.map_eq_some_iff, List.cons.injEq, Option.some.injEq, List.map_cons]
    constructor
    · rintro ⟨ts, hts, rfl, rfl⟩
      exact ⟨rfl, (allSome_eq_some_iff.mp hts)⟩
    · rintro ⟨rfl, hrest⟩
      exact ⟨bs, allSome_eq_some_iff.mpr hrest, rfl, rfl⟩

/-- More fuel never changes a successful extraction. -/
theorem extract_fuel_mono (ch : Choice Op) :
    ∀ {fuel fuel' c : Nat} {t : Term Op},
      fuel ≤ fuel' → extract ch fuel c = some t → extract ch fuel' c = some t
  | 0, _, _, _, _, h => by cases h
  | n + 1, 0, _, _, hle, _ => absurd hle (Nat.not_succ_le_zero _)
  | n + 1, m + 1, c, t, hle, h => by
    simp only [extract] at h ⊢
    cases hc : ch c with
    | none => simp [hc] at h
    | some nd =>
      rw [hc] at h
      cases nd with
      | var x => exact h
      | app f ks =>
        simp only [Option.map_eq_some_iff] at h ⊢
        obtain ⟨ts, hts, rfl⟩ := h
        refine ⟨ts, ?_, rfl⟩
        rw [allSome_eq_some_iff] at hts ⊢
        apply List.ext_getElem?
        intro i
        have heq := congrArg (fun l => l[i]?) hts
        by_cases hi : i < ks.length
        · have ht : i < ts.length := by
            have hl := congrArg List.length hts; simp at hl; omega
          simp [hi, ht] at heq ⊢
          exact extract_fuel_mono ch (Nat.le_of_succ_le_succ hle) heq
        · have ht : ¬ i < ts.length := by
            have hl := congrArg List.length hts; simp at hl; omega
          simp [hi, ht]

/-- Extraction terminates (for some fuel) exactly on choices that are well-founded below the
class. -/
theorem extract_isSome_iff_wfBelow (ch : Choice Op) (c : Nat) :
    (∃ fuel t, extract ch fuel c = some t) ↔ WFBelow ch c := by
  constructor
  · rintro ⟨fuel, t, h⟩
    induction fuel generalizing c t with
    | zero => cases h
    | succ n ih =>
      simp only [extract] at h
      cases hc : ch c with
      | none => simp [hc] at h
      | some nd =>
        rw [hc] at h
        cases nd with
        | var x => exact .var hc
        | app f ks =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ts, hts, rfl⟩ := h
          rw [allSome_eq_some_iff] at hts
          refine .app hc (fun k hk => ?_)
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
          have ht : i < ts.length := by
            have hl := congrArg List.length hts; simp at hl; omega
          have heq := congrArg (fun l => l[i]?) hts
          simp [hi, ht] at heq
          exact ih _ _ heq
  · intro hW
    induction hW with
    | @var _ x hc => exact ⟨1, .var x, by simp [extract, hc]⟩
    | @app c f ks hc _ ih =>
      have hlist : ∀ (l : List Nat), (∀ k ∈ l, ∃ fuel t, extract ch fuel k = some t) →
          ∃ (fuel : Nat) (ts : List (Term Op)), l.map (extract ch fuel) = ts.map some := by
        intro l
        induction l with
        | nil => intro _; exact ⟨0, [], rfl⟩
        | cons k rest ihr =>
          intro hall
          obtain ⟨f1, t1, h1⟩ := hall k (List.mem_cons_self ..)
          obtain ⟨f2, ts, h2⟩ := ihr (fun j hj => hall j (List.mem_cons_of_mem _ hj))
          refine ⟨max f1 f2, t1 :: ts, ?_⟩
          simp only [List.map_cons, List.cons.injEq]
          refine ⟨extract_fuel_mono ch (Nat.le_max_left _ _) h1, ?_⟩
          apply List.ext_getElem?
          intro i
          have heq := congrArg (fun m => m[i]?) h2
          by_cases hi : i < rest.length
          · have ht : i < ts.length := by
              have hl := congrArg List.length h2; simp at hl; omega
            simp [hi, ht] at heq ⊢
            exact extract_fuel_mono ch (Nat.le_max_right _ _) heq
          · have ht : ¬ i < ts.length := by
              have hl := congrArg List.length h2; simp at hl; omega
            simp [hi, ht]
      obtain ⟨fuel, ts, hts⟩ := hlist ks ih
      refine ⟨fuel + 1, .app f ts, ?_⟩
      simp [extract, hc, allSome_eq_some_iff.mpr hts]

/-! ## Proof infrastructure -/

/-- Monotone positions propagate a lower bound through an operator applied to argument
lists that agree pointwise up to refinement, one position at a time. -/
private theorem interp_mono_chain {P : Profile Op} {M : Model Op}
    (hT : LeTrans M) (hMono : MonoAt P M) (f : Op) :
    ∀ (pre : List M.C) (xs ys : List M.C),
      xs.length = ys.length →
      (∀ i < xs.length, P f (pre.length + i) = .mono) →
      (∀ i (hx : i < xs.length) (hy : i < ys.length), M.le xs[i] ys[i]) →
      ∀ (base : M.C), M.le base (M.interp f (pre ++ xs)) →
      M.le base (M.interp f (pre ++ ys)) := by
  intro pre xs
  induction xs generalizing pre with
  | nil =>
    intro ys hlen _ _ base hbase
    cases ys with
    | nil => exact hbase
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    intro ys hlen hP hle base hbase
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hP0 : P f pre.length = .mono := by simpa using hP 0 (Nat.zero_lt_succ _)
      have h0 : M.le x y := hle 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have hstep : M.le (M.interp f (pre ++ x :: xs)) (M.interp f (pre ++ y :: xs)) :=
        hMono f pre xs x y hP0 h0
      have hbase' : M.le base (M.interp f ((pre ++ [y]) ++ xs)) := by
        simpa [List.append_assoc] using hT _ _ _ hbase hstep
      have hres := ih (pre ++ [y]) ys (by simpa using hlen)
        (fun i hi => by
          have := hP (i + 1) (Nat.succ_lt_succ hi)
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
        (fun i hx hy => hle (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy))
        base hbase'
      simpa [List.append_assoc] using hres

/-! ## Main statements -/

/-- **Oriented extraction through monotone positions is sound.** If the model is transitive
and monotone at the positions `P` declares `mono`, every chosen e-node refines its class
denotation (`ChosenOriented`), and every argument position of every chosen e-node is
declared `mono` (`ChosenMono`), then every term returned by `extract ch fuel c` refines
`den c`. -/
theorem extract_refines_of_chosenOriented_mono {P : Profile Op} {M : Model Op}
    {ρ : Nat → M.C} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M)
    (hCO : ChosenOriented M ρ den ch) (hCM : ChosenMono P ch) {fuel c : Nat}
    {t : Term Op} (h : extract ch fuel c = some t) : M.le (den c) (eval M ρ t) := by
  induction fuel generalizing c t with
  | zero => cases h
  | succ n ih =>
    simp only [extract] at h
    cases hc : ch c with
    | none => simp [hc] at h
    | some nd =>
      rw [hc] at h
      cases nd with
      | var x =>
        simp only [Option.some.injEq] at h
        subst h
        exact hCO c (.var x) hc
      | app f ks =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨ts, hts, rfl⟩ := h
        rw [allSome_eq_some_iff] at hts
        have hlen : ks.length = ts.length := by
          have := congrArg List.length hts; simp at this; exact this
        have hbase : M.le (den c) (M.interp f ([] ++ ks.map den)) := by
          simpa [nodeVal] using hCO c (.app f ks) hc
        rw [eval_app]
        have hfin := interp_mono_chain hT hMono f [] (ks.map den) (ts.map (eval M ρ))
          (by simp [hlen])
          (fun i hi => by simp at hi; simpa using hCM c f ks hc i hi)
          (fun i hx hy => by
            simp only [List.length_map] at hx hy
            simp only [List.getElem_map]
            have heq := congrArg (fun l => l[i]?) hts
            simp [hx, hy] at heq
            exact ih heq)
          (den c) hbase
        simpa using hfin

/-- **E-graph form of oriented extraction.** An oriented e-graph (`Oriented`), a choice of
e-nodes inside their classes (`ChoiceIn`) descending only through `mono` positions
(`ChosenMono`), in a transitive model monotone at the `mono` positions: every extracted term
refines the denotation of its class. -/
theorem extract_refines_of_oriented_mono {P : Profile Op} {M : Model Op} {ρ : Nat → M.C}
    {G : EGraph Op} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M)
    (hO : Oriented M ρ G den) (hC : ChoiceIn G ch) (hCM : ChosenMono P ch) {fuel c : Nat}
    {t : Term Op} (h : extract ch fuel c = some t) : M.le (den c) (eval M ρ t) :=
  extract_refines_of_chosenOriented_mono hT hMono (chosenOriented_of_oriented hO hC) hCM h

/-- **Well-founded extraction terminates and is sound.** Under the hypotheses of
`extract_refines_of_chosenOriented_mono`, if the choice is well-founded below `c`, then for
some fuel `extract ch fuel c` returns a term, and that term refines `den c`. -/
theorem extract_total_and_sound_of_wfBelow_oriented_mono {P : Profile Op} {M : Model Op}
    {ρ : Nat → M.C} {den : Nat → M.C} {ch : Choice Op} (hT : LeTrans M) (hMono : MonoAt P M)
    (hCO : ChosenOriented M ρ den ch) (hCM : ChosenMono P ch) {c : Nat}
    (hW : WFBelow ch c) :
    ∃ fuel t, extract ch fuel c = some t ∧ M.le (den c) (eval M ρ t) := by
  obtain ⟨fuel, t, h⟩ := (extract_isSome_iff_wfBelow ch c).mpr hW
  exact ⟨fuel, t, h, extract_refines_of_chosenOriented_mono hT hMono hCO hCM h⟩

/-! ## Examples for the definitions -/

/-- Literal e-node in the outcome signature. -/
abbrev litN (n : Nat) : ENode OOp := .app (.lit n) []

/-- Class 0: `{0, choose(class 1, class 2)}`; class 1: `{0}`; class 2: `{1}`. -/
def egUnoriented : EGraph OOp where
  nodes
    | 0 => [litN 0, .app .choose [1, 2]]
    | 1 => [litN 0]
    | 2 => [litN 1]
    | _ => []

/-- Class 0: `{0}`; class 1: `{0}`; class 2: `{1}` (the oriented part of `egUnoriented`). -/
def egOriented : EGraph OOp where
  nodes
    | 0 => [litN 0]
    | 1 => [litN 0]
    | 2 => [litN 1]
    | _ => []

/-- Class denotations `[0], [0], [1]` (others empty). -/
def denLit : Nat → List Nat := fun c => [[0], [0], [1]].getD c []

/-- Choice picking `choose(1, 2)` in class 0. -/
def chChoose : Choice OOp
  | 0 => some (.app .choose [1, 2])
  | 1 => some (litN 0)
  | 2 => some (litN 1)
  | _ => none

/-- Choice picking the literal in class 0. -/
def chLit : Choice OOp
  | 0 => some (litN 0)
  | 1 => some (litN 0)
  | 2 => some (litN 1)
  | _ => none

theorem nodes_egUnoriented (c : Nat) (n : ENode OOp) (h : n ∈ egUnoriented.nodes c) :
    (c = 0 ∧ (n = litN 0 ∨ n = .app .choose [1, 2])) ∨ (c = 1 ∧ n = litN 0) ∨
      (c = 2 ∧ n = litN 1) := by
  match c, h with
  | 0, h => simp [egUnoriented] at h; exact Or.inl ⟨rfl, h⟩
  | 1, h => simp [egUnoriented] at h; exact Or.inr (Or.inl ⟨rfl, h⟩)
  | 2, h => simp [egUnoriented] at h; exact Or.inr (Or.inr ⟨rfl, h⟩)
  | _ + 3, h => simp [egUnoriented] at h

theorem nodes_egOriented (c : Nat) (n : ENode OOp) (h : n ∈ egOriented.nodes c) :
    (c = 0 ∧ n = litN 0) ∨ (c = 1 ∧ n = litN 0) ∨ (c = 2 ∧ n = litN 1) := by
  match c, h with
  | 0, h => simp [egOriented] at h; exact Or.inl ⟨rfl, h⟩
  | 1, h => simp [egOriented] at h; exact Or.inr (Or.inl ⟨rfl, h⟩)
  | 2, h => simp [egOriented] at h; exact Or.inr (Or.inr ⟨rfl, h⟩)
  | _ + 3, h => simp [egOriented] at h

/-- Positive example (`Oriented`). -/
theorem egOriented_oriented : Oriented oModel (fun _ => []) egOriented denLit := by
  intro c n h
  rcases nodes_egOriented c n h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Negative example (`Oriented`): `choose(0, 1)` (outcomes `[0, 1]`) does not refine
class 0's denotation `[0]`. -/
theorem egUnoriented_not_oriented : ¬ Oriented oModel (fun _ => []) egUnoriented denLit := by
  intro h
  have := h 0 (.app .choose [1, 2]) (by simp [egUnoriented])
  exact absurd this (by decide)

/-- Positive example (`RelatedEitherWay`): every node of `egUnoriented` is related to its
class in some direction (`choose(0, 1)` is refined *by* `[0]`). -/
theorem egUnoriented_relatedEitherWay :
    RelatedEitherWay oModel (fun _ => []) egUnoriented denLit := by
  intro c n h
  rcases nodes_egUnoriented c n h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Negative example (`RelatedEitherWay`): a class whose node is unrelated to it. -/
theorem not_relatedEitherWay_example :
    ¬ RelatedEitherWay oModel (fun _ => []) ⟨fun _ => [litN 1]⟩ (fun _ => [0]) := by
  intro h
  have := h 0 (litN 1) (by simp)
  exact absurd this (by decide)

/-- Positive example (`ChoiceIn`). -/
theorem chChoose_in_egUnoriented : ChoiceIn egUnoriented chChoose := by
  intro c n h
  match c, h with
  | 0, h => simp [chChoose] at h; subst h; simp [egUnoriented]
  | 1, h => simp [chChoose] at h; subst h; simp [egUnoriented]
  | 2, h => simp [chChoose] at h; subst h; simp [egUnoriented]
  | _ + 3, h => simp [chChoose] at h

/-- Negative example (`ChoiceIn`): `choose(1, 2)` is not an e-node of `egOriented`'s class 0. -/
theorem chChoose_not_in_egOriented : ¬ ChoiceIn egOriented chChoose := by
  intro h
  have := h 0 _ rfl
  simp [egOriented] at this

/-- Positive example (`ChosenMono`). -/
theorem chChoose_chosenMono : ChosenMono oProfile chChoose := by
  intro c f ks h i hi
  match c, h with
  | 0, h =>
    simp [chChoose] at h; obtain ⟨rfl, rfl⟩ := h; simp [oProfile]
  | 1, h => simp [chChoose] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | 2, h => simp [chChoose] at h; obtain ⟨rfl, rfl⟩ := h; simp at hi
  | _ + 3, h => simp [chChoose] at h

/-- A choice descending through `pickMin` (declared `eqOnly`). -/
def chPick : Choice OOp
  | 0 => some (.app .pickMin [1])
  | 1 => some (.var 1)
  | _ => none

/-- Negative example (`ChosenMono`). -/
theorem chPick_not_chosenMono : ¬ ChosenMono oProfile chPick := by
  intro h
  have := h 0 .pickMin [1] rfl 0 (by decide)
  simp [oProfile] at this

/-- Example (`extract`): extracting class 0 with `chChoose` gives `choose(0, 1)`. -/
theorem extract_chChoose :
    extract chChoose 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 1) []]) := by
  decide

/-- The cyclic class: class 0 is `{x₀, choose(class 0, class 0)}` (`choose(S, S)` has the
outcomes of `S`, so `x₀ ≤ f x₀` and `f x₀ ≤ x₀` for `f x = choose(x, x)`). -/
def egCycle : EGraph OOp where
  nodes
    | 0 => [.var 0, .app .choose [0, 0]]
    | _ => []

/-- The choice that follows the cycle. -/
def chCycle : Choice OOp
  | 0 => some (.app .choose [0, 0])
  | _ => none

/-- The acyclic choice. -/
def chAcyclic : Choice OOp
  | 0 => some (.var 0)
  | _ => none

/-- Positive example (`WFBelow`). -/
theorem wfBelow_chAcyclic : WFBelow chAcyclic 0 := .var (x := 0) rfl

/-- Negative example (`WFBelow`): the cyclic choice is not well-founded. -/
theorem not_wfBelow_chCycle : ¬ WFBelow chCycle 0 := by
  suffices ∀ c, WFBelow chCycle c → c ≠ 0 by exact fun h => this 0 h rfl
  intro c h
  induction h with
  | var hc => intro e; subst e; simp [chCycle] at hc
  | app hc _ ih =>
    intro e; subst e
    simp [chCycle] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ih 0 (by simp) rfl

/-- An infinite choice with no cycle: class `c` chooses `succ(class c+1)`. -/
def chInf : Choice UOp := fun c => some (.app .succ [c + 1])

/-- Negative example (`WFBelow`): `chInf` chooses an e-node at every class and every child
id is larger than its parent's (so the choice graph has no cycle), yet it is not
well-founded below `0` and extraction from `0` never terminates. -/
theorem chInf_acyclic_total_not_wfBelow :
    (∀ c, ∃ n, chInf c = some n) ∧
    (∀ c f ks d, chInf c = some (.app f ks) → d ∈ ks → c < d) ∧
    ¬ WFBelow chInf 0 ∧
    (∀ fuel, extract chInf fuel 0 = none) := by
  refine ⟨fun c => ⟨_, rfl⟩, fun c f ks d h hd => ?_, ?_, ?_⟩
  · simp [chInf] at h
    obtain ⟨_, rfl⟩ := h
    simp at hd
    omega
  · suffices ∀ c, ¬ WFBelow chInf c from this 0
    intro c h
    induction h with
    | var hc => simp [chInf] at hc
    | @app c' _ _ hc _ ih =>
      simp [chInf] at hc
      obtain ⟨_, rfl⟩ := hc
      exact ih (c' + 1) (by simp)
  · suffices ∀ fuel c, extract chInf fuel c = none from fun fuel => this fuel 0
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ n ih => intro c; simp [extract, chInf, allSome, ih]


/-! ## Counterexamples -/

/-- **Unoriented extraction is unsound.** In the outcome model (transitive, monotone at the
`mono` positions of `oProfile`), class 0 of `egUnoriented` has denotation `[0]` (source
program `0`) and contains `choose(0, 1)`, which is related to it only in the opposite
direction. Every node is related to its class in some direction, the choice picks e-nodes of
their classes through `mono` positions only, extraction returns `choose(0, 1)`, and that term
does not refine `[0]`. -/
theorem extract_unoriented_counterexample :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    RelatedEitherWay oModel (fun _ => []) egUnoriented denLit ∧
    ChoiceIn egUnoriented chChoose ∧
    ¬ ChosenOriented oModel (fun _ => []) denLit chChoose ∧ ChosenMono oProfile chChoose ∧
    extract chChoose 2 0 = some (.app .choose [.app (.lit 0) [], .app (.lit 1) []]) ∧
    ¬ oModel.le (denLit 0)
      (eval oModel (fun _ => []) (.app .choose [.app (.lit 0) [], .app (.lit 1) []])) :=
  ⟨oModel_trans, oModel_monoAt, egUnoriented_relatedEitherWay, chChoose_in_egUnoriented,
    fun h => absurd (h 0 _ rfl) (by decide), chChoose_chosenMono, extract_chChoose, by decide⟩

theorem extract_chCycle_none (fuel : Nat) : extract chCycle fuel 0 = none := by
  induction fuel with
  | zero => rfl
  | succ n ih => simp [extract, chCycle, allSome, ih]

/-- No finite term is a fixed point of `t ↦ f(t, t)`. -/
theorem term_ne_app_self_self {Op : Type} (f : Op) (t : Term Op) : t ≠ .app f [t, t] := by
  intro h
  have := congrArg sizeOf h
  simp at this
  omega

/-- Example (`extract_isSome_iff_wfBelow`, both sides): the acyclic choice is well-founded and
extraction terminates; the cyclic choice is neither. -/
theorem extract_isSome_iff_wfBelow_examples :
    (WFBelow chAcyclic 0 ∧ ∃ fuel t, extract chAcyclic fuel 0 = some t) ∧
    (¬ WFBelow chCycle 0 ∧ ¬ ∃ fuel t, extract chCycle fuel 0 = some t) := by
  refine ⟨⟨wfBelow_chAcyclic, 1, .var 0, rfl⟩, not_wfBelow_chCycle, ?_⟩
  rintro ⟨fuel, t, h⟩
  rw [extract_chCycle_none fuel] at h
  cases h

/-- **Following a cycle does not terminate.** In the outcome model, the cyclic class of
`egCycle` (with denotation `x₀`) is oriented — both `x₀` and `choose(x₀, x₀)` refine `x₀`,
and `x₀` refines `choose(x₀, x₀)` — and the cyclic choice picks an e-node of the class
through `mono` positions; yet `extract chCycle fuel 0 = none` for every fuel, the choice is
not well-founded, and no finite term `t` satisfies the cycle equation `t = choose(t, t)`. -/
theorem extract_cycle_counterexample (ρ : Nat → List Nat) :
    LeTrans oModel ∧ MonoAt oProfile oModel ∧
    Oriented oModel ρ egCycle (fun _ => ρ 0) ∧
    ChosenOriented oModel ρ (fun _ => ρ 0) chCycle ∧
    oModel.le (nodeVal oModel ρ (fun _ => ρ 0) (.app .choose [0, 0])) (ρ 0) ∧
    ChoiceIn egCycle chCycle ∧ ChosenMono oProfile chCycle ∧
    ¬ WFBelow chCycle 0 ∧
    (∀ fuel, extract chCycle fuel 0 = none) ∧
    (∀ t : Term OOp, t ≠ .app .choose [t, t]) := by
  have hO : Oriented oModel ρ egCycle (fun _ => ρ 0) := by
    intro c n h
    match c, h with
    | 0, h =>
      simp [egCycle] at h
      rcases h with rfl | rfl
      · exact fun _ hv => hv
      · intro v hv; simpa [nodeVal, oInterp] using hv
    | _ + 1, h => simp [egCycle] at h
  have hC : ChoiceIn egCycle chCycle := by
    intro c n h
    match c, h with
    | 0, h => simp [chCycle] at h; subst h; simp [egCycle]
    | _ + 1, h => simp [chCycle] at h
  refine ⟨oModel_trans, oModel_monoAt, hO, chosenOriented_of_oriented hO hC, ?_, hC, ?_,
    not_wfBelow_chCycle, extract_chCycle_none, fun t => term_ne_app_self_self _ t⟩
  · intro v hv; simpa [nodeVal, oInterp] using hv
  · intro c f ks h i hi
    match c, h with
    | 0, h => simp [chCycle] at h; obtain ⟨rfl, rfl⟩ := h; simp [oProfile]
    | _ + 1, h => simp [chCycle] at h

end Toy.DirCC
