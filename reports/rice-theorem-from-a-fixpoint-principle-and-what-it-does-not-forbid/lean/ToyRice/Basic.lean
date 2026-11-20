/-
# Rice's theorem from a fixpoint principle: core definitions

Everything here is abstract and Mathlib-free. A *programming system* is a type of codes,
a type of behaviours, a semantics map, and a class of *admissible* code transformers.
No law is bundled into the structure: every law is a separately named `Prop`, so each
theorem names exactly the laws it uses.
-/

namespace Toy.Rice

universe u v w

/-- A *programming system*.

* `Code` models program texts (for example Gödel numbers, syntax trees, byte strings).
* `Beh` models behaviours (for example partial functions `ℕ → ℕ`, denotations).
* `sem c` is the behaviour of code `c`. It need not be injective: many codes may share a
  behaviour, and in realistic systems they do.
* `Adm f` says that the code-to-code map `f` is one the system can itself carry out
  (in a computability model: `f` is total computable). This is where *all* effectiveness
  assumptions live; nothing else in this package mentions computability.

The structure carries data only; laws such as `FixpointPrinciple` are separate `Prop`s. -/
structure System where
  /-- Codes (program texts). -/
  Code : Type u
  /-- Behaviours (what a program means). -/
  Beh : Type v
  /-- Semantics: the behaviour of each code. -/
  sem : Code → Beh
  /-- Admissible code transformers: the maps on codes that the system itself can perform. -/
  Adm : (Code → Code) → Prop

variable (S : System.{u, v})

/-- **Fixpoint principle** (an abstract recursion theorem): every admissible transformer `f`
has a *semantic* fixed point, a code `c` such that `f c` and `c` have the same behaviour.

This is the conclusion of Kleene's second recursion theorem when `Code` is the indices of an
acceptable numbering of the partial computable functions, `sem` is the numbering, and `Adm` is
the total computable functions. It is an *assumption* in this package, never derived for a
real language. -/
def FixpointPrinciple : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∃ c, S.sem (f c) = S.sem c

/-- A predicate on codes is **extensional** (a *semantic* or *behavioural* property) if it
cannot distinguish two codes with the same behaviour. Predicates that are not extensional are
*syntactic*: they look at the text, not only at the behaviour. -/
def Extensional (P : S.Code → Prop) : Prop :=
  ∀ c d, S.sem c = S.sem d → (P c ↔ P d)

/-- A predicate is **nontrivial** if some element satisfies it and some element does not. -/
def NontrivialPred {α : Type w} (P : α → Prop) : Prop :=
  (∃ a, P a) ∧ (∃ b, ¬ P b)

/-- A Boolean checker `chk` **decides** `P`: it answers `true` exactly on the elements
satisfying `P`. This is a purely set-theoretic statement; it says nothing about whether `chk`
is computable. Effectiveness is expressed by `SwitchAdmissible`. -/
def Decides {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, chk c = true ↔ P c

/-- The **switch** on checker `chk` with branches `a` and `b`: the code transformer
`c ↦ if chk c then a else b`. Both branches are fixed codes. -/
def switch {α : Type w} (chk : α → Bool) (a b : α) : α → α :=
  fun c => cond (chk c) a b

/-- The checker `chk` is **switch-admissible** if every switch on it is an admissible
transformer: for all codes `a b`, the map `c ↦ if chk c then a else b` is in `S.Adm`.

In a computability model this is what "the checker is computable" buys: computable functions
are closed under definition by cases on a computable Boolean with constant branches. -/
def SwitchAdmissible (chk : S.Code → Bool) : Prop :=
  ∀ a b, S.Adm (switch chk a b)

/-- `P` is **decided inside the system**: some checker decides `P` and every switch on that
checker is admissible. Equivalently (`decidedInside_iff_ite_admissible`), for all codes `a b`
the transformer `c ↦ if P c then a else b` is admissible. -/
def DecidedInside (P : S.Code → Prop) : Prop :=
  ∃ chk : S.Code → Bool, Decides chk P ∧ SwitchAdmissible S chk

/-- A checker is **sound** for `P` if everything it accepts satisfies `P`. -/
def SoundFor {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, chk c = true → P c

/-- A checker is **complete** for `P` if it accepts everything satisfying `P`. -/
def CompleteFor {α : Type w} (chk : α → Bool) (P : α → Prop) : Prop :=
  ∀ c, P c → chk c = true

/-- Closure law: every constant transformer `fun _ => k` is admissible. -/
def ConstClosed : Prop :=
  ∀ k : S.Code, S.Adm (fun _ => k)

/-- Closure law: admissible transformers are closed under composition. -/
def CompClosed : Prop :=
  ∀ f g : S.Code → S.Code, S.Adm f → S.Adm g → S.Adm (f ∘ g)

/-- Closure law relating a class `K` of *internal checkers* to admissible transformers:
every switch on every checker in `K` is admissible. In a computability model with `K` the
computable Boolean functions on codes and `Adm` the total computable transformers, this is
closure under definition by cases with constant branches. -/
def SwitchClosed (K : (S.Code → Bool) → Prop) : Prop :=
  ∀ chk, K chk → SwitchAdmissible S chk

/-- `P` is **decided by a checker in the class `K`**. -/
def DecidedBy (K : (S.Code → Bool) → Prop) (P : S.Code → Prop) : Prop :=
  ∃ chk, K chk ∧ Decides chk P

/-! ## Basic lemmas about the definitions -/

@[simp] theorem switch_apply {α : Type w} (chk : α → Bool) (a b c : α) :
    switch chk a b c = cond (chk c) a b := rfl

theorem switch_of_true {α : Type w} {chk : α → Bool} {a b c : α} (h : chk c = true) :
    switch chk a b c = a := by simp [switch, h]

theorem switch_of_false {α : Type w} {chk : α → Bool} {a b c : α} (h : chk c = false) :
    switch chk a b c = b := by simp [switch, h]

/-- For a checker that decides `P`, the switch is the `if P c then a else b` transformer
(with any decidability instance). -/
theorem switch_eq_ite_of_decides {α : Type w} {chk : α → Bool} {P : α → Prop}
    (h : Decides chk P) [DecidablePred P] (a b : α) :
    switch chk a b = fun c => if P c then a else b := by
  funext c
  by_cases hc : P c
  · have : chk c = true := (h c).2 hc
    simp [switch, this, hc]
  · have : chk c = false := by
      cases hchk : chk c with
      | false => rfl
      | true => exact absurd ((h c).1 hchk) hc
    simp [switch, this, hc]

/-- `decide ∘ P` decides `P`, for any decidability instance. -/
theorem decides_decide {α : Type w} (P : α → Prop) [DecidablePred P] :
    Decides (fun c => decide (P c)) P := by
  intro c; simp

/-- **Definition adequacy.** `DecidedInside S P` says exactly what the informal definition
says: for all codes `a b`, the transformer `c ↦ if P c then a else b` is admissible. The `if`
uses classical decidability, so no computability is smuggled in through the Boolean checker:
all effectiveness lives in `S.Adm`. -/
theorem decidedInside_iff_ite_admissible (P : S.Code → Prop) :
    DecidedInside S P ↔
      ∀ a b : S.Code,
        S.Adm (fun c => @ite _ (P c) (Classical.propDecidable (P c)) a b) := by
  constructor
  · rintro ⟨chk, hdec, hsw⟩ a b
    have := @switch_eq_ite_of_decides _ _ _ hdec (fun c => Classical.propDecidable (P c)) a b
    rw [← this]
    exact hsw a b
  · intro h
    refine ⟨fun c => @decide (P c) (Classical.propDecidable (P c)), ?_, ?_⟩
    · intro c; simp
    · intro a b
      have := @switch_eq_ite_of_decides _ (fun c => @decide (P c) (Classical.propDecidable (P c)))
        P (by intro c; simp) (fun c => Classical.propDecidable (P c)) a b
      rw [this]
      exact h a b

/-- A checker that decides `P` is sound and complete for `P`, and conversely. -/
theorem decides_iff_sound_complete {α : Type w} (chk : α → Bool) (P : α → Prop) :
    Decides chk P ↔ SoundFor chk P ∧ CompleteFor chk P := by
  constructor
  · intro h; exact ⟨fun c hc => (h c).1 hc, fun c hc => (h c).2 hc⟩
  · rintro ⟨hs, hc⟩ c; exact ⟨hs c, hc c⟩

/-- `DecidedInside` is `DecidedBy` for the class of switch-admissible checkers. -/
theorem decidedInside_iff_decidedBy_switchAdmissible (P : S.Code → Prop) :
    DecidedInside S P ↔ DecidedBy S (SwitchAdmissible S) P := by
  constructor
  · rintro ⟨chk, h1, h2⟩; exact ⟨chk, h2, h1⟩
  · rintro ⟨chk, h1, h2⟩; exact ⟨chk, h2, h1⟩

/-- Restriction of a system to a fragment `F` of its codes (a sublanguage). A transformer of
the fragment is admissible when it agrees *literally* (as a code-to-code map) on the fragment with
some admissible transformer of the full system; outside the fragment that full-system transformer
is unconstrained. The fixpoint principle need not survive restriction: the full system's fixed
point may lie outside the fragment. Whether restriction helps at all depends on the full system:
see `not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial`. -/
def System.restrict (S : System.{u, v}) (F : S.Code → Prop) : System.{u, v} :=
  ⟨{c // F c}, S.Beh, fun x => S.sem x.val,
    fun g => ∃ f, S.Adm f ∧ ∀ x, (g x).val = f x.val⟩

/-- Restricting an extensional predicate to a fragment gives an extensional predicate. -/
theorem extensional_restrict {F : S.Code → Prop} {P : S.Code → Prop} (h : Extensional S P) :
    Extensional (S.restrict F) (fun x => P x.val) :=
  fun c d hcd => h c.val d.val hcd

/-- A switch-admissible checker of the full system that decides `P` on the fragment `F` decides
`P` inside the restricted system: the full-system switch agrees with the fragment switch on the
fragment, literally. -/
theorem decidedInside_restrict_of_switchAdmissible {F : S.Code → Prop} {P : S.Code → Prop}
    {chk : S.Code → Bool} (hsw : SwitchAdmissible S chk) (hdec : ∀ c, F c → (chk c = true ↔ P c)) :
    DecidedInside (S.restrict F) (fun x => P x.val) := by
  refine ⟨fun x => chk x.val, fun x => hdec x.val x.2, fun a b => ⟨switch chk a.val b.val, hsw _ _,
    fun x => ?_⟩⟩
  show (cond (chk x.val) a b).val = cond (chk x.val) a.val b.val
  cases chk x.val <;> rfl

/-- Closure law: an admissible transformer may be followed by a test for *literal equality* of its
output with a fixed code, branching to fixed codes: for admissible `f` and codes `k a b`, the
transformer `c ↦ if f c = k then a else b` is admissible. The test uses classical decidability; in
a computability model, codes are finite objects with decidable equality, and total computable
transformers are closed under this operation. -/
def EqTestClosed : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∀ k a b : S.Code,
    S.Adm (fun c => @ite _ (f c = k) (Classical.propDecidable _) a b)

end Toy.Rice
