/-!
# Duplication, hash-consing and the unique-instance discipline

A small expression language with a nondeterministic `freeze` (`frz`) over poison values.

* `Tm`: variables, literals, `add`, `frz k a` (freeze with an *instance tag* `k`), and
  `letE x e b` (evaluate `e` once, bind its value to `x`).
* `indep ρ t v` — the intended set-of-outcomes semantics: every *evaluation* of a `frz`
  node whose argument is poison chooses a natural number afresh; `letE` shares one value.
  Tags are ignored by `indep`.
* `Refines tgt src` — `tgt` refines `src`: every outcome of `tgt` refines some outcome of
  `src` (poison is refined by everything), in every environment.
* `inline` — substitute every `letE`-bound expression into its body (what representing a
  program as a term DAG without binders amounts to).
* `hashcons` — insert a let-free term into a node table, merging syntactically identical
  nodes (including identical `frz k a` nodes); `dagSem` evaluates a node table with one
  choice per *node*.
* `tagSem ρ t v` — one choice per *tag*: all `frz` nodes carrying the same tag share their
  choice.

Results:
* `dup_vs_let_hashcons_counterexample`: `let a := frz x; a + a` inlines to
  `frz x + frz x`, whose hash-consed table merges the two `frz` nodes; reading that table
  back as the duplicated tree asserts that `frz x + frz x` refines `let a := frz x; a + a`,
  which is false (the former can produce `1` when `x` is poison). The converse refinement
  holds for this pair (`refines_letProg_dupProg`).
* `hashcons_inline_sound_of_uniqueTags`: if every `frz` occurrence of the source program
  carries a distinct tag, the hash-consed table of the inlined program has exactly the
  intended outcomes. It factors through `hcSem_iff_tagSem_of_letFree_wellTagged` and
  `tagSem_iff_indep_of_uniqueTags` and the inlining lemmas `letFree_inline`,
  `evalT_inline`, `wellTagged_inline_of_uniqueTags`.
* Limits of the discipline: `copy_rewrite_breaks_hashcons` (rewriting one
  copy of an inlined tagged freeze by an exact identity defeats hash-consing) and
  `one_copy_refinement_breaks_tagged_sharing` (refining the argument of one copy only is
  not sound under the per-tag reading).

This language shares no definitions with `Term`, `Model`, `Profile`, `Cert` or `EGraph`.
-/

namespace Toy.DirCC.Dup

/-- Values: `none` is poison, `some n` a defined natural number. -/
abbrev Val := Option Nat

/-- Expressions with an instance-tagged nondeterministic `freeze`. -/
inductive Tm where
  | var (x : Nat)
  | lit (n : Nat)
  | add (a b : Tm)
  | frz (k : Nat) (a : Tm)
  | letE (x : Nat) (e b : Tm)
deriving Repr, DecidableEq

/-- Addition, strict in poison. -/
def addV : Val → Val → Val
  | some a, some b => some (a + b)
  | _, _ => none

/-- Environment update. -/
def update (ρ : Nat → Val) (x : Nat) (v : Val) : Nat → Val := fun y => if y = x then v else ρ y

/-- Possible results of freezing `u`: a defined value is kept; poison becomes any defined
value. -/
def FrzOut : Val → Val → Prop
  | none, some _ => True
  | none, none => False
  | some m, w => w = some m

/-- Intended (independent-choice) semantics: `indep ρ t v` iff `v` is a possible outcome
of `t` in environment `ρ`. Each evaluation of a `frz` node chooses independently; `letE`
evaluates its bound expression once. -/
def indep : (Nat → Val) → Tm → Val → Prop
  | ρ, .var x, v => v = ρ x
  | _, .lit n, v => v = some n
  | ρ, .add a b, v => ∃ u w, indep ρ a u ∧ indep ρ b w ∧ v = addV u w
  | ρ, .frz _ a, v => ∃ u, indep ρ a u ∧ FrzOut u v
  | ρ, .letE x e b, v => ∃ u, indep ρ e u ∧ indep (update ρ x u) b v

/-- Value refinement: `ValLe u w` iff `w` refines `u` (poison is refined by everything). -/
def ValLe : Val → Val → Prop
  | none, _ => True
  | some a, w => w = some a

/-- Program refinement: in every environment, every outcome of `tgt` refines some outcome
of `src`. Note the argument order: target first, source second (`Refines tgt src` reads
"`tgt` refines `src`"), whereas `ValLe`, `OLe` and `Model.le` take the source first. -/
def Refines (tgt src : Tm) : Prop :=
  ∀ ρ v, indep ρ tgt v → ∃ u, indep ρ src u ∧ ValLe u v

/-! ## Tagged semantics -/

/-- Freeze under a per-tag choice function `σ`. -/
def frzT (σ : Nat → Nat) (k : Nat) : Val → Val
  | none => some (σ k)
  | some m => some m

/-- Deterministic evaluation given one choice per tag. -/
def evalT (σ : Nat → Nat) : (Nat → Val) → Tm → Val
  | ρ, .var x => ρ x
  | _, .lit n => some n
  | ρ, .add a b => addV (evalT σ ρ a) (evalT σ ρ b)
  | ρ, .frz k a => frzT σ k (evalT σ ρ a)
  | ρ, .letE x e b => evalT σ (update ρ x (evalT σ ρ e)) b

/-- Tagged semantics: outcomes over all per-tag choice functions. -/
def tagSem (ρ : Nat → Val) (t : Tm) (v : Val) : Prop := ∃ σ : Nat → Nat, evalT σ ρ t = v

/-! ## Syntax predicates -/

/-- The `frz` occurrences of a term, as (tag, argument) pairs, in syntactic order. -/
def frzOccs : Tm → List (Nat × Tm)
  | .var _ => []
  | .lit _ => []
  | .add a b => frzOccs a ++ frzOccs b
  | .frz k a => (k, a) :: frzOccs a
  | .letE _ e b => frzOccs e ++ frzOccs b

/-- Unique-instance discipline: distinct `frz` occurrences carry distinct tags. -/
def UniqueTags (t : Tm) : Prop := ((frzOccs t).map Prod.fst).Nodup

instance (t : Tm) : Decidable (UniqueTags t) := inferInstanceAs (Decidable (List.Nodup _))

/-- Well-tagged: `frz` occurrences with the same tag have the same argument (they are copies
of one instance). -/
def WellTagged (t : Tm) : Prop :=
  ∀ p, p ∈ frzOccs t → ∀ q, q ∈ frzOccs t → p.1 = q.1 → p.2 = q.2

instance (t : Tm) : Decidable (WellTagged t) :=
  inferInstanceAs (Decidable (∀ p, p ∈ frzOccs t → ∀ q, q ∈ frzOccs t → p.1 = q.1 → p.2 = q.2))

/-- The term contains no `letE`. -/
def LetFree : Tm → Bool
  | .var _ => true
  | .lit _ => true
  | .add a b => LetFree a && LetFree b
  | .frz _ a => LetFree a
  | .letE _ _ _ => false

/-! ## Inlining -/

/-- Substitution of `s` for the variable `x`. Not capture-avoiding; it is only applied by
`inline` to let-free terms, where no capture can occur. -/
def subst (x : Nat) (s : Tm) : Tm → Tm
  | .var y => if y = x then s else .var y
  | .lit n => .lit n
  | .add a b => .add (subst x s a) (subst x s b)
  | .frz k a => .frz k (subst x s a)
  | .letE y e b => .letE y (subst x s e) (if y = x then b else subst x s b)

/-- Inline every `letE`: the result is let-free, and each bound expression is copied to
every use (copies keep their tags). -/
def inline : Tm → Tm
  | .var y => .var y
  | .lit n => .lit n
  | .add a b => .add (inline a) (inline b)
  | .frz k a => .frz k (inline a)
  | .letE x e b => subst x (inline e) (inline b)

/-! ## Hash-consing into a node table -/

/-- A node of a hash-consed term DAG; children are indices of earlier nodes. -/
inductive DNode where
  | var (x : Nat)
  | lit (n : Nat)
  | add (i j : Nat)
  | frz (k : Nat) (i : Nat)
deriving Repr, DecidableEq

/-- Index of the first node equal to `n`, if any. -/
def findNode : List DNode → DNode → Nat → Option Nat
  | [], _, _ => none
  | m :: rest, n, i => if m = n then some i else findNode rest n (i + 1)

/-- Insert a node, reusing an identical existing node (the hash-consing step). -/
def hcInsert (tbl : List DNode) (n : DNode) : List DNode × Nat :=
  match findNode tbl n 0 with
  | some i => (tbl, i)
  | none => (tbl ++ [n], tbl.length)

/-- Hash-cons a let-free term into a table, returning the new table and the root index.
(`letE` is outside the domain and is mapped to the literal `0`.) -/
def hashcons : List DNode → Tm → List DNode × Nat
  | tbl, .var x => hcInsert tbl (.var x)
  | tbl, .lit n => hcInsert tbl (.lit n)
  | tbl, .add a b =>
    let r1 := hashcons tbl a
    let r2 := hashcons r1.1 b
    hcInsert r2.1 (.add r1.2 r2.2)
  | tbl, .frz k a =>
    let r1 := hashcons tbl a
    hcInsert r1.1 (.frz k r1.2)
  | tbl, .letE _ _ _ => hcInsert tbl (.lit 0)

/-- Evaluate a node table front to back with one choice `c i` per node index `i`
(out-of-range children read as poison). Returns the value of every node. -/
def evalTbl (c : Nat → Nat) (ρ : Nat → Val) : List DNode → List Val → List Val
  | [], acc => acc
  | n :: rest, acc =>
    let v : Val :=
      match n with
      | .var x => ρ x
      | .lit m => some m
      | .add i j => addV (acc.getD i none) (acc.getD j none)
      | .frz _ i => frzT c acc.length (acc.getD i none)
    evalTbl c ρ rest (acc ++ [v])

/-- Semantics of a node table with root `r`: one choice per node. -/
def dagSem (ρ : Nat → Val) (tbl : List DNode) (r : Nat) (v : Val) : Prop :=
  ∃ c : Nat → Nat, (evalTbl c ρ tbl []).getD r none = v

/-- The DAG reading of a let-free term: hash-cons it into the empty table. -/
def hcSem (ρ : Nat → Val) (t : Tm) (v : Val) : Prop :=
  dagSem ρ (hashcons [] t).1 (hashcons [] t).2 v

/-! ## Examples for the definitions -/

/-- `let a := frz x₀; a + a` (tag `0`). -/
def letProg : Tm := .letE 1 (.frz 0 (.var 0)) (.add (.var 1) (.var 1))

/-- `frz x₀ + frz x₀`, both occurrences tagged `0` (an untagged duplicate). -/
def dupProg : Tm := .add (.frz 0 (.var 0)) (.frz 0 (.var 0))

/-- `frz₀ x₀ + frz₁ x₀`: the duplicate under the unique-instance discipline. -/
def dupProgTagged : Tm := .add (.frz 0 (.var 0)) (.frz 1 (.var 0))

/-- The all-poison environment. -/
def poisonEnv : Nat → Val := fun _ => none

/-- Positive example (`indep`): `frz x + frz x` with `x` poison can produce `1`. -/
theorem indep_dupProg_one : indep poisonEnv dupProg (some 1) :=
  ⟨some 0, some 1, ⟨none, rfl, trivial⟩, ⟨none, rfl, trivial⟩, rfl⟩

/-- Negative example (`indep`): `let a := frz x; a + a` with `x` poison cannot produce `1`. -/
theorem not_indep_letProg_one : ¬ indep poisonEnv letProg (some 1) := by
  intro h
  obtain ⟨u, ⟨u0, hu0, hfr⟩, w, w', hw, hw', hv⟩ := h
  have e0 : u0 = none := hu0
  have ew : w = u := by rw [hw]; simp [update]
  have ew' : w' = u := by rw [hw']; simp [update]
  subst e0
  rw [ew, ew'] at hv
  cases u with
  | none => exact hfr
  | some n => simp [addV] at hv; omega

/-- Positive example (`Refines`): the shared program refines the duplicated one. -/
theorem refines_letProg_dupProg : Refines letProg dupProg := by
  intro ρ v h
  obtain ⟨u, ⟨u0, hu0, hfr⟩, w, w', hw, hw', hv⟩ := h
  have ew : w = u := by rw [hw]; simp [update]
  have ew' : w' = u := by rw [hw']; simp [update]
  rw [ew, ew'] at hv
  refine ⟨v, ⟨u, u, ⟨u0, hu0, hfr⟩, ⟨u0, hu0, hfr⟩, hv⟩, ?_⟩
  cases v with
  | none => trivial
  | some _ => rfl

/-- Negative example (`Refines`): the duplicated program does not refine the shared one. -/
theorem not_refines_dupProg_letProg : ¬ Refines dupProg letProg := by
  intro h
  obtain ⟨u, hu, hle⟩ := h poisonEnv (some 1) indep_dupProg_one
  cases u with
  | none =>
    obtain ⟨u1, ⟨u0, hu0, hfr⟩, w, w', hw, hw', hv⟩ := hu
    have e0 : u0 = none := hu0
    have ew : w = u1 := by rw [hw]; simp [update]
    have ew' : w' = u1 := by rw [hw']; simp [update]
    subst e0
    rw [ew, ew'] at hv
    cases u1 with
    | none => exact hfr
    | some n => simp [addV] at hv
  | some a =>
    have ha : some 1 = some a := hle
    rw [← ha] at hu
    exact not_indep_letProg_one hu

/-- Positive example (`UniqueTags`): the tagged duplicate and the shared program. -/
theorem uniqueTags_examples : UniqueTags dupProgTagged ∧ UniqueTags letProg := by decide

/-- Negative example (`UniqueTags`): the untagged duplicate. -/
theorem not_uniqueTags_dupProg : ¬ UniqueTags dupProg := by decide

/-- Positive example (`WellTagged`): copies of one instance (`frz₀ x + frz₀ x`). -/
theorem wellTagged_dupProg : WellTagged dupProg := by decide

/-- Negative example (`WellTagged`): one tag on two different arguments. -/
theorem not_wellTagged_mixed : ¬ WellTagged (.add (.frz 0 (.var 0)) (.frz 0 (.var 1))) := by
  decide

/-- Example (`inline`): inlining the shared program yields the untagged duplicate. -/
theorem inline_letProg : inline letProg = dupProg := by decide

/-- Example (`LetFree`): inlined programs are let-free; `letProg` is not. -/
theorem letFree_examples : LetFree (inline letProg) = true ∧ LetFree letProg = false := by
  decide

/-- Positive example (`hashcons`): the two identical `frz₀ x₀` nodes are merged. -/
theorem hashcons_dupProg : hashcons [] dupProg = ([.var 0, .frz 0 0, .add 1 1], 2) := by decide

/-- Negative example (`hashcons`): differently tagged `frz` nodes are not merged. -/
theorem hashcons_dupProgTagged :
    hashcons [] dupProgTagged = ([.var 0, .frz 0 0, .frz 1 0, .add 1 2], 3) := by decide

/-- Example (`dagSem`): the hash-consed table of `frz x + frz x` cannot produce `1` when
`x` is poison (one choice for the shared `frz` node). -/
theorem not_hcSem_dupProg_one : ¬ hcSem poisonEnv dupProg (some 1) := by
  rintro ⟨c, hc⟩
  rw [hashcons_dupProg] at hc
  simp [evalTbl, poisonEnv, frzT, addV] at hc
  omega

/-- Example (`dagSem`): the hash-consed table of the tagged duplicate can produce `1`. -/
theorem hcSem_dupProgTagged_one : hcSem poisonEnv dupProgTagged (some 1) := by
  refine ⟨fun i => if i = 1 then 0 else 1, ?_⟩
  decide

/-- Example (`tagSem`): one choice per tag, so `frz₀ x + frz₀ x` cannot produce `1`. -/
theorem not_tagSem_dupProg_one : ¬ tagSem poisonEnv dupProg (some 1) := by
  rintro ⟨σ, hσ⟩
  simp [dupProg, evalT, poisonEnv, frzT, addV] at hσ
  omega

/-- Example (`tagSem`): one choice per tag, so the tagged duplicate `frz₀ x + frz₁ x` can
produce `1`. -/
theorem tagSem_dupProgTagged_one : tagSem poisonEnv dupProgTagged (some 1) :=
  ⟨fun k => if k = 0 then 0 else 1, by decide⟩

/-! ## Inlining lemmas -/

theorem letFree_subst (x : Nat) (s b : Tm) (hs : LetFree s = true) (hb : LetFree b = true) :
    LetFree (subst x s b) = true := by
  induction b with
  | var y =>
    simp only [subst]
    split
    · exact hs
    · rfl
  | lit _ => rfl
  | add a b iha ihb =>
    simp only [LetFree, Bool.and_eq_true] at hb
    simp [subst, LetFree, iha hb.1, ihb hb.2]
  | frz k a iha => simp [subst, LetFree, iha hb]
  | letE _ _ _ => simp [LetFree] at hb

/-- Inlining yields a let-free term. -/
theorem letFree_inline (t : Tm) : LetFree (inline t) = true := by
  induction t with
  | var _ => rfl
  | lit _ => rfl
  | add a b iha ihb => simp [inline, LetFree, iha, ihb]
  | frz _ a iha => simp [inline, LetFree, iha]
  | letE x e b ihe ihb => exact letFree_subst x _ _ ihe ihb

theorem evalT_subst (σ : Nat → Nat) (ρ : Nat → Val) (x : Nat) (s b : Tm)
    (hb : LetFree b = true) :
    evalT σ ρ (subst x s b) = evalT σ (update ρ x (evalT σ ρ s)) b := by
  induction b with
  | var y =>
    simp only [subst, evalT, update]
    split <;> rfl
  | lit _ => rfl
  | add a b iha ihb =>
    simp only [LetFree, Bool.and_eq_true] at hb
    simp [subst, evalT, iha hb.1, ihb hb.2]
  | frz k a iha => simp [subst, evalT, iha hb]
  | letE _ _ _ => simp [LetFree] at hb

/-- Inlining preserves evaluation under every per-tag choice function. -/
theorem evalT_inline (σ : Nat → Nat) (ρ : Nat → Val) (t : Tm) :
    evalT σ ρ (inline t) = evalT σ ρ t := by
  induction t generalizing ρ with
  | var _ => rfl
  | lit _ => rfl
  | add a b iha ihb => simp [inline, evalT, iha, ihb]
  | frz k a iha => simp [inline, evalT, iha]
  | letE x e b ihe ihb =>
    simp only [inline, evalT]
    rw [evalT_subst σ ρ x (inline e) (inline b) (letFree_inline b), ihe, ihb]

theorem mem_frzOccs_subst {x : Nat} {s b : Tm} (hb : LetFree b = true)
    {p : Nat × Tm} (hp : p ∈ frzOccs (subst x s b)) :
    p ∈ frzOccs s ∨ ∃ a, (p.1, a) ∈ frzOccs b ∧ p.2 = subst x s a := by
  induction b with
  | var y =>
    simp only [subst] at hp
    split at hp
    · exact Or.inl hp
    · simp [frzOccs] at hp
  | lit _ => simp [subst, frzOccs] at hp
  | add a b iha ihb =>
    simp only [LetFree, Bool.and_eq_true] at hb
    simp only [subst, frzOccs, List.mem_append] at hp ⊢
    rcases hp with h | h
    · rcases iha hb.1 h with h | ⟨arg, harg, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨arg, Or.inl harg, h2⟩
    · rcases ihb hb.2 h with h | ⟨arg, harg, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨arg, Or.inr harg, h2⟩
  | frz k a iha =>
    simp only [subst, frzOccs, List.mem_cons] at hp ⊢
    rcases hp with rfl | h
    · exact Or.inr ⟨a, Or.inl rfl, rfl⟩
    · rcases iha hb h with h | ⟨arg, harg, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨arg, Or.inr harg, h2⟩
  | letE _ _ _ => simp [LetFree] at hb

theorem tags_inline_subset (t : Tm) :
    ∀ k, k ∈ (frzOccs (inline t)).map Prod.fst → k ∈ (frzOccs t).map Prod.fst := by
  induction t with
  | var _ => intro k hk; exact hk
  | lit _ => intro k hk; exact hk
  | add a b iha ihb =>
    intro k hk
    simp only [inline, frzOccs, List.map_append, List.mem_append] at hk ⊢
    rcases hk with h | h
    · exact Or.inl (iha k h)
    · exact Or.inr (ihb k h)
  | frz j a iha =>
    intro k hk
    simp only [inline, frzOccs, List.map_cons, List.mem_cons] at hk ⊢
    rcases hk with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (iha k h)
  | letE x e b ihe ihb =>
    intro k hk
    simp only [inline, List.mem_map] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    simp only [frzOccs, List.map_append, List.mem_append]
    rcases mem_frzOccs_subst (letFree_inline b) hp with h | ⟨arg, harg, _⟩
    · exact Or.inl (ihe p.1 (List.mem_map.mpr ⟨p, h, rfl⟩))
    · exact Or.inr (ihb p.1 (List.mem_map.mpr ⟨(p.1, arg), harg, rfl⟩))

/-- Inlining a program with unique tags yields a well-tagged term. -/
theorem wellTagged_inline_of_uniqueTags (t : Tm) (hu : UniqueTags t) :
    WellTagged (inline t) := by
  induction t with
  | var _ => intro _ h; simp [inline, frzOccs] at h
  | lit _ => intro _ h; simp [inline, frzOccs] at h
  | add a b iha ihb =>
    simp only [UniqueTags, frzOccs, List.map_append, List.nodup_append] at hu
    intro p hp q hq heq
    simp only [inline, frzOccs, List.mem_append] at hp hq
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact iha hu.1 p hp q hq heq
    · exfalso
      have h1 := tags_inline_subset a p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have h2 := tags_inline_subset b q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      exact hu.2.2 p.1 h1 q.1 h2 heq
    · exfalso
      have h1 := tags_inline_subset b p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have h2 := tags_inline_subset a q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      exact hu.2.2 q.1 h2 p.1 h1 heq.symm
    · exact ihb hu.2.1 p hp q hq heq
  | frz k a iha =>
    simp only [UniqueTags, frzOccs, List.map_cons, List.nodup_cons] at hu
    intro p hp q hq heq
    simp only [inline, frzOccs, List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exfalso
      have h2 := tags_inline_subset a q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have heq' : k = q.1 := heq
      exact hu.1 (heq' ▸ h2)
    · exfalso
      have h1 := tags_inline_subset a p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have heq' : p.1 = k := heq
      exact hu.1 (heq'.symm ▸ h1)
    · exact iha hu.2 p hp q hq heq
  | letE x e b ihe ihb =>
    simp only [UniqueTags, frzOccs, List.map_append, List.nodup_append] at hu
    intro p hp q hq heq
    simp only [inline] at hp hq
    have hpe := mem_frzOccs_subst (letFree_inline b) hp
    have hqe := mem_frzOccs_subst (letFree_inline b) hq
    rcases hpe with hp' | ⟨ap, hap, hp2⟩ <;> rcases hqe with hq' | ⟨aq, haq, hq2⟩
    · exact ihe hu.1 p hp' q hq' heq
    · exfalso
      have h1 := tags_inline_subset e p.1 (List.mem_map.mpr ⟨p, hp', rfl⟩)
      have h2 := tags_inline_subset b q.1 (List.mem_map.mpr ⟨(q.1, aq), haq, rfl⟩)
      exact hu.2.2 p.1 h1 q.1 h2 heq
    · exfalso
      have h1 := tags_inline_subset b p.1 (List.mem_map.mpr ⟨(p.1, ap), hap, rfl⟩)
      have h2 := tags_inline_subset e q.1 (List.mem_map.mpr ⟨q, hq', rfl⟩)
      exact hu.2.2 q.1 h2 p.1 h1 heq.symm
    · have harg : ap = aq := ihb hu.2.1 (p.1, ap) hap (q.1, aq) haq heq
      rw [hp2, hq2, harg]

/-! ## Proof infrastructure for the hash-consing theorems

Private lemmas used only inside the proofs below: tag-congruence of `evalT`, the
invariant maintained by `hashcons` (`TableInv`: the table is duplicate-free, every slot
decodes injectively to a let-free term, and children precede parents), and step-by-step
agreement of `evalTbl` with `evalT`. -/

/-- Two tag-choice functions agreeing on all tags of `t` yield the same `evalT`. -/
private theorem evalT_congr_tags {σ₁ σ₂ : Nat → Nat} {ρ : Nat → Val} {t : Tm}
    (h : ∀ k ∈ (frzOccs t).map Prod.fst, σ₁ k = σ₂ k) :
    evalT σ₁ ρ t = evalT σ₂ ρ t := by
  induction t generalizing ρ with
  | var _ => rfl
  | lit _ => rfl
  | add a b iha ihb =>
    simp only [frzOccs, List.map_append, List.mem_append] at h
    simp only [evalT]
    rw [iha (fun k hk => h k (Or.inl hk)), ihb (fun k hk => h k (Or.inr hk))]
  | frz k a iha =>
    simp only [frzOccs, List.map_cons, List.mem_cons] at h
    simp only [evalT]
    rw [iha (fun j hj => h j (Or.inr hj))]
    cases evalT σ₂ ρ a with
    | none => simp [frzT, h k (Or.inl rfl)]
    | some _ => rfl
  | letE x e b ihe ihb =>
    simp only [frzOccs, List.map_append, List.mem_append] at h
    simp only [evalT]
    rw [ihe (fun k hk => h k (Or.inl hk)), ihb (fun k hk => h k (Or.inr hk))]

private theorem evalT_implies_indep (σ : Nat → Nat) (ρ : Nat → Val) (t : Tm) :
    indep ρ t (evalT σ ρ t) := by
  induction t generalizing ρ with
  | var _ => rfl
  | lit _ => rfl
  | add a b iha ihb => exact ⟨evalT σ ρ a, evalT σ ρ b, iha ρ, ihb ρ, rfl⟩
  | frz k a iha =>
    refine ⟨evalT σ ρ a, iha ρ, ?_⟩
    simp only [evalT]
    cases evalT σ ρ a <;> simp [frzT, FrzOut]
  | letE x e b ihe ihb => exact ⟨evalT σ ρ e, ihe ρ, ihb _⟩

private theorem node_lt_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  cases Nat.lt_or_ge i l.length with
  | inl hlt => exact hlt
  | inr hge =>
    rw [List.getElem?_eq_none hge] at h
    cases h

private def decodeNode (dec : Nat → Tm) : DNode → Tm
  | DNode.var x => Tm.var x
  | DNode.lit n => Tm.lit n
  | DNode.add a b => Tm.add (dec a) (dec b)
  | DNode.frz k a => Tm.frz k (dec a)

private def nodeKidsLt (bound : Nat) : DNode → Prop
  | DNode.var _ => True
  | DNode.lit _ => True
  | DNode.add a b => a < bound ∧ b < bound
  | DNode.frz _ a => a < bound

private theorem findNode_eq_some_iff (tbl : List DNode) (n : DNode) :
    ∀ (base i : Nat), findNode tbl n base = some i ↔
      ∃ off, i = base + off ∧ tbl[off]? = some n ∧ ∀ j < off, tbl[j]? ≠ some n := by
  induction tbl with
  | nil =>
    intro base i
    simp [findNode]
  | cons m rest ih =>
    intro base i
    simp only [findNode]
    split
    · rename_i hm
      subst hm
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        exact ⟨0, h.symm.trans (Nat.add_zero base).symm, rfl, fun j hj => by omega⟩
      · rintro ⟨off, rfl, _, hmin⟩
        cases off with
        | zero => simp
        | succ k => exact absurd rfl (hmin 0 (Nat.zero_lt_succ k))
    · rename_i hne
      rw [ih (base + 1) i]
      constructor
      · rintro ⟨off, rfl, hget, hmin⟩
        refine ⟨off + 1, by omega, hget, fun j hj => ?_⟩
        cases j with
        | zero => simp [hne]
        | succ j' => exact hmin j' (Nat.lt_of_succ_lt_succ hj)
      · rintro ⟨off, rfl, hget, hmin⟩
        cases off with
        | zero => simp at hget; exact absurd hget hne
        | succ off' =>
          exact ⟨off', by omega, hget, fun j hj => hmin (j + 1) (Nat.succ_lt_succ hj)⟩

private theorem findNode_eq_none_iff (tbl : List DNode) (n : DNode) :
    ∀ base, findNode tbl n base = none ↔ n ∉ tbl := by
  induction tbl with
  | nil => intro _; simp [findNode]
  | cons m rest ih =>
    intro base
    simp only [findNode, List.mem_cons, not_or]
    split
    · rename_i h; subst h; simp
    · rename_i h; rw [ih (base + 1)]; exact ⟨fun hr => ⟨Ne.symm h, hr⟩, fun ⟨_, hr⟩ => hr⟩

private theorem hcInsert_spec (tbl : List DNode) (n : DNode) :
    let r := hcInsert tbl n
    (∃ rest, r.1 = tbl ++ rest) ∧
    r.2 < r.1.length ∧
    r.1[r.2]? = some n ∧
    (tbl.Nodup → r.1.Nodup) := by
  simp only [hcInsert]
  cases hf : findNode tbl n 0 with
  | some i =>
    obtain ⟨off, rfl, hget, _⟩ := (findNode_eq_some_iff tbl n 0 i).mp hf
    have hlt : off < tbl.length := node_lt_of_getElem? hget
    refine ⟨⟨[], by simp⟩, by simpa using hlt, by simpa using hget, id⟩
  | none =>
    have hnot : n ∉ tbl := (findNode_eq_none_iff tbl n 0).mp hf
    refine ⟨⟨[n], rfl⟩, by simp, by simp, ?_⟩
    intro hnd
    rw [List.nodup_append]
    exact ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb => by
      simp at hb; subst hb; intro heq; subst heq; exact hnot ha⟩

/-- Well-formedness of a hash-cons table `tbl` relative to a decoder `dec : Nat → Tm`. -/
private structure TableInv (tbl : List DNode) (dec : Nat → Tm) : Prop where
  nodup : tbl.Nodup
  lf : ∀ i, i < tbl.length → LetFree (dec i) = true
  kids_lt : ∀ (i : Nat) (nd : DNode), tbl[i]? = some nd → nodeKidsLt i nd
  node_dec : ∀ (i : Nat) (nd : DNode), tbl[i]? = some nd → dec i = decodeNode dec nd
  inj : ∀ i j, i < tbl.length → j < tbl.length → dec i = dec j → i = j

private theorem tableInv_nil : TableInv [] (fun _ => .lit 0) where
  nodup := List.nodup_nil
  lf _ h := by simp at h
  kids_lt _ _ h := by simp at h
  node_dec _ _ h := by simp at h
  inj _ _ h := by simp at h

private theorem decodeNode_congr {dec₁ dec₂ : Nat → Tm} {b : Nat} {nd : DNode}
    (hk : nodeKidsLt b nd) (h : ∀ i < b, dec₁ i = dec₂ i) :
    decodeNode dec₁ nd = decodeNode dec₂ nd := by
  cases nd with
  | var _ => rfl
  | lit _ => rfl
  | add a c => simp [decodeNode, h a hk.1, h c hk.2]
  | frz k a => simp [decodeNode, h a hk]

private theorem tableInv_extend {tbl : List DNode} {dec : Nat → Tm}
    (hinv : TableInv tbl dec) (nd : DNode) (hnd_wf : nodeKidsLt tbl.length nd) :
    let r := hcInsert tbl nd
    ∃ dec', TableInv r.1 dec' ∧
      (∀ i < tbl.length, dec' i = dec i) ∧
      dec' r.2 = decodeNode dec nd ∧
      (∀ i < r.1.length, i < tbl.length ∨ i = r.2) := by
  simp only [hcInsert]
  cases hf : findNode tbl nd 0 with
  | some idx =>
    obtain ⟨off, rfl, hget, _⟩ := (findNode_eq_some_iff tbl nd 0 idx).mp hf
    simp only [Nat.zero_add] at hget ⊢
    exact ⟨dec, hinv, fun _ _ => rfl, hinv.node_dec off nd hget, fun i hi => Or.inl hi⟩
  | none =>
    have hnot : nd ∉ tbl := (findNode_eq_none_iff tbl nd 0).mp hf
    let dec' : Nat → Tm := fun i => if i = tbl.length then decodeNode dec nd else dec i
    have hdec'_old : ∀ i < tbl.length, dec' i = dec i := fun i hi => by
      simp [dec', Nat.ne_of_lt hi]
    have ht_lf : LetFree (decodeNode dec nd) = true := by
      cases nd with
      | var _ => rfl
      | lit _ => rfl
      | add a b => simp [decodeNode, LetFree, hinv.lf a hnd_wf.1, hinv.lf b hnd_wf.2]
      | frz k a => simp [decodeNode, LetFree, hinv.lf a hnd_wf]
    have ht_fresh : ∀ i < tbl.length, dec i ≠ decodeNode dec nd := by
      intro i hi heq
      have hgi : tbl[i]? = some tbl[i] := List.getElem?_eq_getElem hi
      have hki := hinv.kids_lt i tbl[i] hgi
      have hdi := hinv.node_dec i tbl[i] hgi
      rw [hdi] at heq
      have hsame : tbl[i] = nd := by
        cases hnd_i : tbl[i] with
        | var x' =>
          rw [hnd_i] at heq
          cases nd <;> simp [decodeNode] at heq
          subst heq; rfl
        | lit n' =>
          rw [hnd_i] at heq
          cases nd <;> simp [decodeNode] at heq
          subst heq; rfl
        | add a' b' =>
          rw [hnd_i] at hki heq
          cases nd <;> simp [decodeNode] at heq
          rename_i a b
          have e1 := hinv.inj a' a (Nat.lt_trans hki.1 hi) hnd_wf.1 heq.1
          have e2 := hinv.inj b' b (Nat.lt_trans hki.2 hi) hnd_wf.2 heq.2
          subst e1; subst e2; rfl
        | frz k' a' =>
          rw [hnd_i] at hki heq
          cases nd <;> simp [decodeNode] at heq
          rename_i k a
          obtain ⟨rfl, h1⟩ := heq
          have e1 := hinv.inj a' a (Nat.lt_trans hki hi) hnd_wf h1
          subst e1; rfl
      rw [hsame] at hgi
      exact hnot (List.mem_of_getElem? hgi)
    refine ⟨dec', ?_, hdec'_old, by simp [dec'], fun i hi => by simp at hi ⊢; omega⟩
    refine
      { nodup := by
          rw [List.nodup_append]
          exact ⟨hinv.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb heq => by
            simp at hb; subst hb; subst heq; exact hnot ha⟩
        lf := fun i hi => by
          simp at hi
          by_cases h : i < tbl.length
          · rw [hdec'_old i h]; exact hinv.lf i h
          · have : i = tbl.length := by omega
            subst this; simp [dec', ht_lf]
        kids_lt := fun i m hget => by
          by_cases h : i < tbl.length
          · rw [List.getElem?_append_left h] at hget
            exact hinv.kids_lt i m hget
          · have hlt := node_lt_of_getElem? hget
            simp at hlt
            have hi : i = tbl.length := by omega
            subst hi
            simp at hget
            subst hget
            exact hnd_wf
        node_dec := fun i m hget => by
          by_cases h : i < tbl.length
          · rw [List.getElem?_append_left h] at hget
            have hki := hinv.kids_lt i m hget
            rw [hdec'_old i h, hinv.node_dec i m hget]
            exact (decodeNode_congr hki (fun j hj => hdec'_old j (Nat.lt_trans hj h))).symm
          · have hlt := node_lt_of_getElem? hget
            simp at hlt
            have hi : i = tbl.length := by omega
            subst hi
            simp at hget
            subst hget
            simp only [dec', ↓reduceIte]
            exact (decodeNode_congr hnd_wf hdec'_old).symm
        inj := fun i j hi hj heq => by
          simp at hi hj
          by_cases h1 : i < tbl.length <;> by_cases h2 : j < tbl.length
          · rw [hdec'_old i h1, hdec'_old j h2] at heq
            exact hinv.inj i j h1 h2 heq
          · have : j = tbl.length := by omega
            subst this; rw [hdec'_old i h1] at heq; simp [dec'] at heq
            exact absurd heq (ht_fresh i h1)
          · have : i = tbl.length := by omega
            subst this; rw [hdec'_old j h2] at heq; simp [dec'] at heq
            exact absurd heq.symm (ht_fresh j h2)
          · omega }

/-- `hashcons` preserves `TableInv`, extends `tbl` as a prefix, decodes the root to `t`,
and every newly added `frz` node comes from `frzOccs t`. -/
private theorem hashcons_spec (t : Tm) (hlf : LetFree t = true) :
    ∀ (tbl : List DNode) (dec : Nat → Tm), TableInv tbl dec →
      let r := hashcons tbl t
      ∃ dec', TableInv r.1 dec' ∧
        (∃ rest, r.1 = tbl ++ rest) ∧
        (∀ i < tbl.length, dec' i = dec i) ∧
        r.2 < r.1.length ∧
        dec' r.2 = t ∧
        (∀ i k a, tbl.length ≤ i → r.1[i]? = some (DNode.frz k a) →
          (k, dec' a) ∈ frzOccs t) := by
  induction t with
  | var x =>
    intro tbl dec hinv
    obtain ⟨dec', hinv', hold, hroot, hnew⟩ := tableInv_extend hinv (.var x) trivial
    have hsp := hcInsert_spec tbl (.var x)
    refine ⟨dec', hinv', hsp.1, hold, hsp.2.1, hroot, fun i k a hge hgi => ?_⟩
    simp only [hashcons] at hgi
    have hlt := node_lt_of_getElem? hgi
    rcases hnew i hlt with hi | rfl
    · omega
    · rw [hsp.2.2.1] at hgi; cases hgi
  | lit n =>
    intro tbl dec hinv
    obtain ⟨dec', hinv', hold, hroot, hnew⟩ := tableInv_extend hinv (.lit n) trivial
    have hsp := hcInsert_spec tbl (.lit n)
    refine ⟨dec', hinv', hsp.1, hold, hsp.2.1, hroot, fun i k a hge hgi => ?_⟩
    simp only [hashcons] at hgi
    have hlt := node_lt_of_getElem? hgi
    rcases hnew i hlt with hi | rfl
    · omega
    · rw [hsp.2.2.1] at hgi; cases hgi
  | add a b iha ihb =>
    intro tbl dec hinv
    simp only [LetFree, Bool.and_eq_true] at hlf
    obtain ⟨dec1, hinv1, ⟨rest1, hpre1⟩, hold1, hr1_lt, hroot1, hfrz1⟩ := iha hlf.1 tbl dec hinv
    obtain ⟨dec2, hinv2, ⟨rest2, hpre2⟩, hold2, hr2_lt, hroot2, hfrz2⟩ := ihb hlf.2 (hashcons tbl a).1 dec1 hinv1
    have hr1_lt2 : (hashcons tbl a).2 < (hashcons (hashcons tbl a).1 b).1.length := by
      rw [hpre2]; simp; omega
    obtain ⟨dec3, hinv3, hold3, hroot3, hnew3⟩ :=
      tableInv_extend hinv2 (.add (hashcons tbl a).2 (hashcons (hashcons tbl a).1 b).2) ⟨hr1_lt2, hr2_lt⟩
    have hsp := hcInsert_spec (hashcons (hashcons tbl a).1 b).1 (.add (hashcons tbl a).2 (hashcons (hashcons tbl a).1 b).2)
    obtain ⟨rest3, hpre3⟩ := hsp.1
    have hlen1 : tbl.length ≤ (hashcons tbl a).1.length := by rw [hpre1]; simp
    have hlen2 : (hashcons tbl a).1.length ≤ (hashcons (hashcons tbl a).1 b).1.length := by rw [hpre2]; simp
    refine ⟨dec3, hinv3, ⟨rest1 ++ rest2 ++ rest3, ?_⟩,
      fun i hi => by
        rw [hold3 i (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi hlen1) hlen2),
            hold2 i (Nat.lt_of_lt_of_le hi hlen1), hold1 i hi],
      hsp.2.1, ?_, fun i k c hge hgi => ?_⟩
    · simp only [hashcons]
      rw [hpre3, hpre2, hpre1]; simp [List.append_assoc]
    · simp only [hashcons]
      rw [hroot3]; simp [decodeNode, hold2 _ hr1_lt, hroot1, hroot2]
    · simp only [hashcons] at hgi ⊢
      have hlt3 := node_lt_of_getElem? hgi
      rcases hnew3 i hlt3 with hlt2 | rfl
      · rw [hpre3, List.getElem?_append_left hlt2] at hgi
        have hc_lt : c < i := hinv2.kids_lt i (.frz k c) hgi
        rw [hold3 c (Nat.lt_trans hc_lt hlt2)]
        by_cases hlt1 : i < (hashcons tbl a).1.length
        · rw [hpre2, List.getElem?_append_left hlt1] at hgi
          rw [hold2 c (Nat.lt_trans hc_lt hlt1)]
          exact List.mem_append_left _ (hfrz1 i k c hge hgi)
        · exact List.mem_append_right _ (hfrz2 i k c (Nat.le_of_not_lt hlt1) hgi)
      · rw [hsp.2.2.1] at hgi; cases hgi
  | frz k a iha =>
    intro tbl dec hinv
    obtain ⟨dec1, hinv1, ⟨rest1, hpre1⟩, hold1, hr1_lt, hroot1, hfrz1⟩ := iha hlf tbl dec hinv
    obtain ⟨dec2, hinv2, hold2, hroot2, hnew2⟩ :=
      tableInv_extend hinv1 (.frz k (hashcons tbl a).2) hr1_lt
    have hsp := hcInsert_spec (hashcons tbl a).1 (.frz k (hashcons tbl a).2)
    obtain ⟨rest2, hpre2⟩ := hsp.1
    have hlen1 : tbl.length ≤ (hashcons tbl a).1.length := by rw [hpre1]; simp
    refine ⟨dec2, hinv2, ⟨rest1 ++ rest2, ?_⟩,
      fun i hi => by rw [hold2 i (Nat.lt_of_lt_of_le hi hlen1), hold1 i hi],
      hsp.2.1, ?_, fun i j c hge hgi => ?_⟩
    · simp only [hashcons]; rw [hpre2, hpre1, List.append_assoc]
    · simp only [hashcons]; rw [hroot2]; simp [decodeNode, hroot1]
    · simp only [hashcons] at hgi ⊢
      have hlt2 := node_lt_of_getElem? hgi
      rcases hnew2 i hlt2 with hlt1 | rfl
      · rw [hpre2, List.getElem?_append_left hlt1] at hgi
        have hc_lt : c < i := hinv1.kids_lt i (.frz j c) hgi
        rw [hold2 c (Nat.lt_trans hc_lt hlt1)]
        exact List.mem_cons_of_mem _ (hfrz1 i j c hge hgi)
      · rw [hsp.2.2.1] at hgi
        injection hgi with heq
        injection heq with hj hc
        subst hj; subst hc
        rw [hold2 _ hr1_lt, hroot1]
        exact List.mem_cons_self ..
  | letE _ _ _ => simp [LetFree] at hlf

/-- Step-by-step evaluation agreement between `evalTbl c ρ tbl acc` and `evalT σ ρ (dec i)`. -/
private theorem evalTbl_prefix_agree (c σ : Nat → Nat) (ρ : Nat → Val) (dec : Nat → Tm) :
    ∀ (rest : List DNode) (pref : List DNode) (acc : List Val),
      acc.length = pref.length →
      TableInv (pref ++ rest) dec →
      (∀ i < pref.length, acc.getD i none = evalT σ ρ (dec i)) →
      (∀ i k a, pref.length ≤ i → (pref ++ rest)[i]? = some (DNode.frz k a) → c i = σ k) →
      ∀ i < (pref ++ rest).length,
        (evalTbl c ρ rest acc).getD i none = evalT σ ρ (dec i) := by
  intro rest
  induction rest with
  | nil =>
    intro pref acc _ _ hacc _ i hi
    simp only [List.append_nil, evalTbl] at hi ⊢
    exact hacc i hi
  | cons nd rest ih =>
    intro pref acc hlen hinv hacc hmatch
    let v : Val :=
      match nd with
      | .var x => ρ x
      | .lit m => some m
      | .add a b => addV (acc.getD a none) (acc.getD b none)
      | .frz _ a => frzT c acc.length (acc.getD a none)
    have hassoc : pref ++ nd :: rest = (pref ++ [nd]) ++ rest := by simp
    have hinv' : TableInv ((pref ++ [nd]) ++ rest) dec := hassoc ▸ hinv
    have hnd_get : (pref ++ nd :: rest)[pref.length]? = some nd := by simp
    have hki := hinv.kids_lt pref.length nd hnd_get
    have hdi := hinv.node_dec pref.length nd hnd_get
    have hv_eq : v = evalT σ ρ (dec pref.length) := by
      cases nd with
      | var x => simp [v, hdi, decodeNode, evalT]
      | lit m => simp [v, hdi, decodeNode, evalT]
      | add a b =>
        show addV (acc.getD a none) (acc.getD b none) = evalT σ ρ (dec pref.length)
        rw [hdi, decodeNode, evalT, hacc a hki.1, hacc b hki.2]
      | frz k a =>
        show frzT c acc.length (acc.getD a none) = evalT σ ρ (dec pref.length)
        have hck : c pref.length = σ k := hmatch pref.length k a (Nat.le_refl _) hnd_get
        rw [hdi, decodeNode, evalT, hacc a hki, hlen]
        cases evalT σ ρ (dec a) with
        | none => simp [frzT, hck]
        | some _ => rfl
    have hacc' : ∀ i < (pref ++ [nd]).length, (acc ++ [v]).getD i none = evalT σ ρ (dec i) := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases h : i < pref.length
      · have h' : i < acc.length := hlen ▸ h
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h']
        simpa [List.getD_eq_getElem?_getD] using hacc i h
      · have hi_eq : i = pref.length := by omega
        subst hi_eq
        simp only [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (Nat.le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [hlen]; exact hv_eq
    have hmatch' : ∀ i k a, (pref ++ [nd]).length ≤ i →
        ((pref ++ [nd]) ++ rest)[i]? = some (DNode.frz k a) → c i = σ k := by
      intro i k a hge hgi
      rw [← hassoc] at hgi
      exact hmatch i k a (by simp at hge; omega) hgi
    have hstep_eq : evalTbl c ρ (nd :: rest) acc = evalTbl c ρ rest (acc ++ [v]) := by
      cases nd <;> rfl
    intro i hi
    rw [hassoc] at hi
    rw [hstep_eq]
    exact ih (pref ++ [nd]) (acc ++ [v]) (by simp [hlen]) hinv' hacc' hmatch' i hi

/-- Constructive tag-to-slot lookup: returns the first index holding `DNode.frz k _`, if any. -/
private def findTagSlotAux : List DNode → Nat → Nat → Option Nat
  | [], _, _ => none
  | .frz k' _ :: rest, k, i => if k' = k then some i else findTagSlotAux rest k (i + 1)
  | _ :: rest, k, i => findTagSlotAux rest k (i + 1)

private theorem findTagSlotAux_sound (tbl : List DNode) (k : Nat) :
    ∀ (base i : Nat), findTagSlotAux tbl k base = some i →
      ∃ off a, i = base + off ∧ tbl[off]? = some (DNode.frz k a) := by
  induction tbl with
  | nil => intro _ _ h; simp [findTagSlotAux] at h
  | cons nd rest ih =>
    intro base i h
    cases nd with
    | frz k' a =>
      simp only [findTagSlotAux] at h
      split at h
      · rename_i hk; subst hk
        injection h with hi
        exact ⟨0, a, hi.symm.trans (Nat.add_zero base).symm, rfl⟩
      · obtain ⟨off, a', rfl, hget⟩ := ih (base + 1) i h
        exact ⟨off + 1, a', by omega, hget⟩
    | var _ =>
      obtain ⟨off, a', rfl, hget⟩ := ih (base + 1) i h
      exact ⟨off + 1, a', by omega, hget⟩
    | lit _ =>
      obtain ⟨off, a', rfl, hget⟩ := ih (base + 1) i h
      exact ⟨off + 1, a', by omega, hget⟩
    | add _ _ =>
      obtain ⟨off, a', rfl, hget⟩ := ih (base + 1) i h
      exact ⟨off + 1, a', by omega, hget⟩

private theorem findTagSlotAux_complete (tbl : List DNode) (k : Nat) :
    ∀ (base off a : Nat), tbl[off]? = some (DNode.frz k a) →
      ∃ i, findTagSlotAux tbl k base = some i := by
  induction tbl with
  | nil => intro _ _ _ h; simp at h
  | cons nd rest ih =>
    intro base off a h
    cases off with
    | zero =>
      simp at h; subst h
      exact ⟨base, by simp [findTagSlotAux]⟩
    | succ off' =>
      simp at h
      cases nd with
      | frz k' a' =>
        simp only [findTagSlotAux]
        split
        · exact ⟨base, rfl⟩
        · exact ih (base + 1) off' a h
      | var _ => exact ih (base + 1) off' a h
      | lit _ => exact ih (base + 1) off' a h
      | add _ _ => exact ih (base + 1) off' a h


/-! ## Results -/

/-- **Identifying a hash-consed nondeterministic node with its duplicated tree is a false
refinement.** `let a := frz x; a + a` inlines to `frz x + frz x`; that term's hash-consed
table merges the two `frz` nodes into one; the table's semantics cannot produce `1` when `x`
is poison, while the duplicated tree (read with independent choices) can; so reading the
merged node back as the duplicated tree asserts that `frz x + frz x` refines
`let a := frz x; a + a`, which is false. The other direction is a true refinement for this
pair (`refines_letProg_dupProg`). -/
theorem dup_vs_let_hashcons_counterexample :
    inline letProg = dupProg ∧
    hashcons [] dupProg = ([.var 0, .frz 0 0, .add 1 1], 2) ∧
    indep poisonEnv dupProg (some 1) ∧
    ¬ hcSem poisonEnv dupProg (some 1) ∧
    ¬ indep poisonEnv letProg (some 1) ∧
    ¬ Refines dupProg letProg ∧
    Refines letProg dupProg :=
  ⟨inline_letProg, hashcons_dupProg, indep_dupProg_one, not_hcSem_dupProg_one,
    not_indep_letProg_one, not_refines_dupProg_letProg, refines_letProg_dupProg⟩

/-- **Hash-consing is faithful to the tagged semantics on let-free, well-tagged terms.** For
every let-free, well-tagged term `t` and environment `ρ`, the hash-consed table of `t` has
exactly the outcomes of `t` under one choice per tag. -/
theorem hcSem_iff_tagSem_of_letFree_wellTagged (ρ : Nat → Val) (t : Tm)
    (hlf : LetFree t = true) (hwt : WellTagged t) (v : Val) : hcSem ρ t v ↔ tagSem ρ t v := by
  obtain ⟨dec, hinv, _, _, hr_lt, hroot, hfrz⟩ := hashcons_spec t hlf [] (fun _ => .lit 0) tableInv_nil
  let tbl := (hashcons [] t).1
  let r := (hashcons [] t).2
  constructor
  · rintro ⟨c, hc⟩
    have huniq : ∀ (i j k a b : Nat), tbl[i]? = some (DNode.frz k a) → tbl[j]? = some (DNode.frz k b) → i = j := by
      intro i j k a b hi hj
      have hfa : (k, dec a) ∈ frzOccs t := hfrz i k a (Nat.zero_le _) hi
      have hfb : (k, dec b) ∈ frzOccs t := hfrz j k b (Nat.zero_le _) hj
      have hdec_eq : dec a = dec b := hwt (k, dec a) hfa (k, dec b) hfb rfl
      have hi_lt := node_lt_of_getElem? hi
      have hj_lt := node_lt_of_getElem? hj
      have ha_lt : a < i := hinv.kids_lt i (DNode.frz k a) hi
      have hb_lt : b < j := hinv.kids_lt j (DNode.frz k b) hj
      have hab : a = b := hinv.inj a b (Nat.lt_trans ha_lt hi_lt) (Nat.lt_trans hb_lt hj_lt) hdec_eq
      subst hab
      have hdi : dec i = Tm.frz k (dec a) := hinv.node_dec i (DNode.frz k a) hi
      have hdj : dec j = Tm.frz k (dec a) := hinv.node_dec j (DNode.frz k a) hj
      exact hinv.inj i j hi_lt hj_lt (hdi.trans hdj.symm)
    let σ : Nat → Nat := fun k =>
      match findTagSlotAux tbl k 0 with
      | some idx => c idx
      | none => 0
    refine ⟨σ, ?_⟩
    have hmatch : ∀ i k a, 0 ≤ i → tbl[i]? = some (DNode.frz k a) → c i = σ k := by
      intro i k a _ hi
      obtain ⟨idx, hidx⟩ := findTagSlotAux_complete tbl k 0 i a hi
      obtain ⟨off, a', rfl, hoff⟩ := findTagSlotAux_sound tbl k 0 idx hidx
      have heq : i = off := huniq i off k a a' hi hoff
      dsimp only [σ]
      rw [hidx, Nat.zero_add, heq]
    have hagree := evalTbl_prefix_agree c σ ρ dec tbl [] [] rfl hinv (fun _ h => by simp at h) hmatch r hr_lt
    rw [← hroot, ← hagree]
    exact hc
  · rintro ⟨σ, hσ⟩
    let c : Nat → Nat := fun i =>
      match tbl[i]? with
      | some (DNode.frz k _) => σ k
      | _ => 0
    refine ⟨c, ?_⟩
    have hmatch : ∀ i k a, 0 ≤ i → tbl[i]? = some (DNode.frz k a) → c i = σ k := by
      intro i k a _ hi
      simp [c, hi]
    have hagree := evalTbl_prefix_agree c σ ρ dec tbl [] [] rfl hinv (fun _ h => by simp at h) hmatch r hr_lt
    rw [hagree, hroot]
    exact hσ

/-- **Unique tags make the tagged semantics the intended one.** For every term `t` whose
`frz` occurrences carry distinct tags, one choice per tag yields exactly the
independent-choice outcomes. -/
theorem tagSem_iff_indep_of_uniqueTags (ρ : Nat → Val) (t : Tm) (hu : UniqueTags t)
    (v : Val) : tagSem ρ t v ↔ indep ρ t v := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact evalT_implies_indep σ ρ t
  · intro hi
    induction t generalizing ρ v with
    | var x => exact ⟨fun _ => 0, hi.symm⟩
    | lit n => exact ⟨fun _ => 0, hi.symm⟩
    | add a b iha ihb =>
      simp only [UniqueTags, frzOccs, List.map_append, List.nodup_append] at hu
      obtain ⟨u, w, hua, hwb, rfl⟩ := hi
      obtain ⟨σ₁, hσ₁⟩ := iha ρ hu.1 u hua
      obtain ⟨σ₂, hσ₂⟩ := ihb ρ hu.2.1 w hwb
      let σ : Nat → Nat := fun k => if k ∈ (frzOccs a).map Prod.fst then σ₁ k else σ₂ k
      refine ⟨σ, ?_⟩
      simp only [evalT]
      have ha : evalT σ ρ a = evalT σ₁ ρ a :=
        evalT_congr_tags (fun k hk => by simp [σ, hk])
      have hb : evalT σ ρ b = evalT σ₂ ρ b :=
        evalT_congr_tags (fun k hk => by
          have hna : k ∉ (frzOccs a).map Prod.fst := fun hka => hu.2.2 k hka k hk rfl
          simp [σ, hna])
      rw [ha, hb, hσ₁, hσ₂]
    | frz k a iha =>
      simp only [UniqueTags, frzOccs, List.map_cons, List.nodup_cons] at hu
      obtain ⟨u, hua, hfr⟩ := hi
      obtain ⟨σ₁, hσ₁⟩ := iha ρ hu.2 u hua
      cases u with
      | none =>
        cases v with
        | none => exact False.elim hfr
        | some n =>
          let σ : Nat → Nat := fun j => if j = k then n else σ₁ j
          refine ⟨σ, ?_⟩
          have ha : evalT σ ρ a = evalT σ₁ ρ a :=
            evalT_congr_tags (fun j hj => by
              have hne : j ≠ k := fun h => hu.1 (h ▸ hj)
              simp [σ, hne])
          simp [evalT, ha, hσ₁, frzT, σ]
      | some m =>
        have hv : v = some m := hfr
        subst hv
        exact ⟨σ₁, by simp [evalT, hσ₁, frzT]⟩
    | letE x e b ihe ihb =>
      simp only [UniqueTags, frzOccs, List.map_append, List.nodup_append] at hu
      obtain ⟨u, hue, hvb⟩ := hi
      obtain ⟨σ₁, hσ₁⟩ := ihe ρ hu.1 u hue
      obtain ⟨σ₂, hσ₂⟩ := ihb (update ρ x u) hu.2.1 v hvb
      let σ : Nat → Nat := fun k => if k ∈ (frzOccs e).map Prod.fst then σ₁ k else σ₂ k
      refine ⟨σ, ?_⟩
      simp only [evalT]
      have he : evalT σ ρ e = evalT σ₁ ρ e :=
        evalT_congr_tags (fun k hk => by simp [σ, hk])
      have hb : evalT σ (update ρ x u) b = evalT σ₂ (update ρ x u) b :=
        evalT_congr_tags (fun k hk => by
          have hne : k ∉ (frzOccs e).map Prod.fst := fun hke => hu.2.2 k hke k hk rfl
          simp [σ, hne])
      rw [he, hσ₁, hb, hσ₂]

/-- **Soundness of hash-consing under the unique-instance discipline.** For every program
`t` whose `frz` occurrences carry distinct tags, the hash-consed table of the inlined
program has exactly the intended (independent-choice) outcomes of `t`. -/
theorem hashcons_inline_sound_of_uniqueTags (ρ : Nat → Val) (t : Tm) (hu : UniqueTags t)
    (v : Val) : hcSem ρ (inline t) v ↔ indep ρ t v := by
  rw [hcSem_iff_tagSem_of_letFree_wellTagged ρ (inline t) (letFree_inline t)
      (wellTagged_inline_of_uniqueTags t hu) v]
  have htag : tagSem ρ (inline t) v ↔ tagSem ρ t v := by
    simp only [tagSem, evalT_inline]
  rw [htag, tagSem_iff_indep_of_uniqueTags ρ t hu v]

/-! ## Limits of the unique-instance discipline -/

/-- `x₀ + 0`, equal to `x₀` under every choice and environment. -/
def xPlus0 : Tm := .add (.var 0) (.lit 0)

/-- `let x₁ := frz₀ (x₀ + 0); x₁ + x₁`. -/
def letProgPlus0 : Tm := .letE 1 (.frz 0 xPlus0) (.add (.var 1) (.var 1))

/-- The inlined `letProgPlus0` with only the second copy's argument rewritten by the exact
identity `x₀ + 0 ⇝ x₀`: `frz₀ (x₀ + 0) + frz₀ x₀`. -/
def copyRewritten : Tm := .add (.frz 0 xPlus0) (.frz 0 (.var 0))

theorem not_indep_letProgPlus0_one : ¬ indep poisonEnv letProgPlus0 (some 1) := by
  intro h
  obtain ⟨u, ⟨u0, ⟨a, b, ha, hb, hab⟩, hfr⟩, w, w', hw, hw', hv⟩ := h
  have ew : w = u := by rw [hw]; simp [update]
  have ew' : w' = u := by rw [hw']; simp [update]
  have e0 : u0 = none := by rw [hab, ha, hb]; rfl
  subst e0
  rw [ew, ew'] at hv
  cases u with
  | none => exact hfr
  | some n => simp [addV] at hv; omega

/-- **Rewriting one copy of an inlined tagged freeze defeats hash-consing.** The rewrite
`x₀ + 0 ⇝ x₀` preserves evaluation exactly, but applied to one copy of the inlined
`let x₁ := frz₀ (x₀ + 0); x₁ + x₁` it yields a term that is not well-tagged; `hashcons`
keys nodes syntactically (and `evalTbl` keys choices by table slot, ignoring the tag), so the
two copies get separate `frz` slots and the table can produce `1` when `x₀` is poison, which
neither the per-tag reading nor the source program can. -/
theorem copy_rewrite_breaks_hashcons :
    (∀ σ ρ, evalT σ ρ xPlus0 = evalT σ ρ (.var 0)) ∧
    inline letProgPlus0 = .add (.frz 0 xPlus0) (.frz 0 xPlus0) ∧
    ¬ WellTagged copyRewritten ∧
    hashcons [] copyRewritten =
      ([.var 0, .lit 0, .add 0 1, .frz 0 2, .frz 0 0, .add 3 4], 5) ∧
    hcSem poisonEnv copyRewritten (some 1) ∧
    ¬ tagSem poisonEnv copyRewritten (some 1) ∧
    ¬ indep poisonEnv letProgPlus0 (some 1) := by
  refine ⟨fun σ ρ => ?_, by decide, by decide, by decide,
    ⟨fun i => if i = 3 then 0 else 1, by decide⟩, ?_, not_indep_letProgPlus0_one⟩
  · simp only [xPlus0, evalT]
    cases ρ 0 <;> rfl
  · rintro ⟨σ, hσ⟩
    simp [copyRewritten, xPlus0, evalT, poisonEnv, frzT, addV] at hσ
    omega

/-- `frz₀ 1 + frz₀ x₀`: the inlined `letProg` with the argument of the first copy only
refined from `x₀` to `1`. -/
def oneCopyRefined : Tm := .add (.frz 0 (.lit 1)) (.frz 0 (.var 0))

theorem indep_oneCopyRefined_one : indep poisonEnv oneCopyRefined (some 1) :=
  ⟨some 1, some 0, ⟨some 1, rfl, rfl⟩, ⟨none, rfl, trivial⟩, rfl⟩

/-- **Refining the argument of one copy of a tagged freeze is not sound.** With `x₀`
poison, `1` refines the value of `x₀`; under the per-tag reading the inlined `letProg`
(`frz₀ x₀ + frz₀ x₀`) cannot produce `1`, but after refining the argument of its first copy
only, both the per-tag reading and the hash-consed table can produce `1`, and the result does
not refine `letProg`. -/
theorem one_copy_refinement_breaks_tagged_sharing :
    ValLe (poisonEnv 0) (some 1) ∧
    inline letProg = .add (.frz 0 (.var 0)) (.frz 0 (.var 0)) ∧
    ¬ tagSem poisonEnv (inline letProg) (some 1) ∧
    tagSem poisonEnv oneCopyRefined (some 1) ∧
    hcSem poisonEnv oneCopyRefined (some 1) ∧
    ¬ Refines oneCopyRefined letProg := by
  refine ⟨trivial, by decide, ?_, ⟨fun _ => 0, by decide⟩, ⟨fun _ => 0, by decide⟩, ?_⟩
  · rw [inline_letProg]; exact not_tagSem_dupProg_one
  · intro h
    obtain ⟨u, hu, hle⟩ := h poisonEnv (some 1) indep_oneCopyRefined_one
    cases u with
    | none =>
      obtain ⟨u1, ⟨u0, hu0, hfr⟩, w, w', hw, hw', hv⟩ := hu
      have e0 : u0 = none := hu0
      have ew : w = u1 := by rw [hw]; simp [update]
      have ew' : w' = u1 := by rw [hw']; simp [update]
      subst e0
      rw [ew, ew'] at hv
      cases u1 with
      | none => exact hfr
      | some n => simp [addV] at hv
    | some a =>
      have ha : some 1 = some a := hle
      rw [← ha] at hu
      exact not_indep_letProg_one hu

end Toy.DirCC.Dup
