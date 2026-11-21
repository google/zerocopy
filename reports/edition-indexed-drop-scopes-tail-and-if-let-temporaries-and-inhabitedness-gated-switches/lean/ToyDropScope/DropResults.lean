import ToyDropScope.Examples

/-!
Results about edition-indexed drop scopes. Main theorems, counterexamples and non-vacuity
witnesses are fully proved.

These are statements about the toy model; they neither establish nor refute the corresponding
claims about Rust's 2021 or 2024 editions or any Rust compiler. Model–system relation: none proved.
-/

namespace Toy.DropScope

/-! ## Single-site program shapes and named programs -/

/-- `letsFrom k ls b`: declare one local per entry of `ls` (names `k, k+1, …`, initializers
`unit`), each with the listed destructor events, followed by the block `b`. -/
def letsFrom (k : Nat) : List (List Ev) → Block → Block
  | [], b => b
  | dl :: ls, b => .letS k dl .unit (letsFrom (k + 1) ls b)

/-- `tempsSeq ds`: create one temporary per entry of `ds` (in list order) within one expression. -/
def tempsSeq : List (List Ev) → Expr
  | [] => .unit
  | d :: ds => .seq (.temp d []) (tempsSeq ds)

/-- `outsSeq ns`: emit `Ev.out n` for each `n` in order. -/
def outsSeq : List Nat → Expr
  | [] => .unit
  | n :: ns => .seq (.out n) (outsSeq ns)

/-- The events of a list of destructors run in reverse list order (the drop order of locals in
declaration order, and of temporaries in creation order). -/
def dropOrderEvents (xs : List (List Ev)) : List Ev := xs.reverse.flatten

/-- One tail site as a whole program: a block declaring locals with destructor events `ls`
whose tail expression creates temporaries with destructor events `ds`. -/
def tailSiteProg (ls ds : List (List Ev)) : Expr := .block (letsFrom 0 ls (.tail (tempsSeq ds)))

/-- One `if let` else site as a whole program: an `if let` whose scrutinee creates temporaries
with destructor events `ds`, whose pattern does not match, and whose `else` block emits `es`. -/
def elseSiteProg (ds : List (List Ev)) (es : List Nat) : Expr :=
  .ifLet false (tempsSeq ds) .unit (outsSeq es)

/-- A `match` in tail position: `{ let x = ..; match temp_with_dtor(1) { _ => () } }`. -/
def matchInTailProg : Expr :=
  .block (.letS 0 [.dtor 0] .unit (.tail (.matchE true (.temp [.dtor 1] []) .unit .unit)))

/-- An `if let` in tail position: `{ let x = ..; if let P = temp_with_dtor(1) { } else { } }`
with the pattern matching. -/
def ifLetInTailProg : Expr :=
  .block (.letS 0 [.dtor 0] .unit (.tail (.ifLet true (.temp [.dtor 1] []) .unit .unit)))

/-- Two locals and two tail temporaries whose drops spell the same word under both editions. -/
def ababProg : Expr := tailSiteProg [[.dtor 1], [.dtor 0]] [[.dtor 1], [.dtor 0]]

/-- A tail temporary created in the tail of an inner block that has no locals, where the inner
block is itself the tail of an outer block with one local. -/
def nestedTailProg : Expr :=
  .block (.letS 0 [.dtor 1] .unit (.tail (.block (.tail (.temp [.dtor 0] [])))))

/-- An `if let` whose pattern matches, followed in the same expression by an output. -/
def thenBranchProg : Expr := .seq (.ifLet true (.temp [.dtor 0] []) .unit .unit) (.out 1)

/-- One local and one tail temporary whose destructors emit the same event. -/
def commutingTailProg : Expr := tailSiteProg [[.dtor 0]] [[.dtor 0]]

/-- The `match` combinator: how a `match` combines its scrutinee's result with the selected arm.
It does not depend on the rule settings. -/
def matchStep (hit : Bool) (rs ra rb : List Act × List Pending) : List Act × List Pending :=
  (rs.1 ++ (if hit then closeScope ra else closeScope rb), rs.2)

/-! ## Proof infrastructure (module-private lemmas) -/

mutual
private theorem eval_snd_nil (R : Rules) (p : Tag) :
    (e : Expr) → noEscape e = true → (eval R p e).2 = []
  | .unit, _ => rfl
  | .out _, _ => rfl
  | .temp _ _, h => by simp [noEscape] at h
  | .seq a b, h => by
    simp [noEscape] at h
    simp [eval, eval_snd_nil R (0 :: p) a h.1, eval_snd_nil R (1 :: p) b h.2]
  | .block b, h => evalBlock_snd_nil R (0 :: p) b h
  | .ifLet hit s a b, h => by
    simp [noEscape] at h
    simp only [eval]
    split <;> simp [eval_snd_nil R (0 :: p) s h]
  | .matchE hit s a b, h => by
    simp [noEscape] at h
    simp [eval, eval_snd_nil R (0 :: p) s h]

private theorem evalBlock_snd_nil (R : Rules) (p : Tag) :
    (b : Block) → noEscapeBlock b = true → (evalBlock R p b).2 = []
  | .tail e, h => by
    simp [noEscapeBlock] at h
    simp only [evalBlock]
    split <;> simp [eval_snd_nil R (0 :: p) e h]
  | .letS _ _ _ r, h => evalBlock_snd_nil R (1 :: p) r h
  | .exprS _ r, h => evalBlock_snd_nil R (1 :: p) r h
end

mutual
private theorem eval_tail2024_eq (b : Bool) (p : Tag) : (e : Expr) → tailsClean e = true →
    eval ⟨true, b⟩ p e = eval ⟨false, b⟩ p e
  | .unit, _ => rfl
  | .out _, _ => rfl
  | .temp _ _, _ => rfl
  | .seq a c, h => by
    simp [tailsClean] at h
    simp [eval, eval_tail2024_eq b (0 :: p) a h.1, eval_tail2024_eq b (1 :: p) c h.2]
  | .block bl, h => evalBlock_tail2024_eq b (0 :: p) bl h
  | .ifLet hit s a c, h => by
    simp [tailsClean] at h
    simp [eval, eval_tail2024_eq b (0 :: p) s h.1.1, eval_tail2024_eq b (1 :: p) a h.1.2,
          eval_tail2024_eq b (2 :: p) c h.2]
  | .matchE hit s a c, h => by
    simp [tailsClean] at h
    simp [eval, eval_tail2024_eq b (0 :: p) s h.1.1, eval_tail2024_eq b (1 :: p) a h.1.2,
          eval_tail2024_eq b (2 :: p) c h.2]

private theorem evalBlock_tail2024_eq (b : Bool) (p : Tag) :
    (bl : Block) → tailsCleanBlock bl = true →
    evalBlock ⟨true, b⟩ p bl = evalBlock ⟨false, b⟩ p bl
  | .tail e, h => by
    simp [tailsCleanBlock] at h
    have he := eval_tail2024_eq b (0 :: p) e h.2
    have hnil := eval_snd_nil ⟨false, b⟩ (0 :: p) e h.1
    simp only [evalBlock, he, ↓reduceIte, Bool.false_eq_true, closeScope, hnil, dropAll,
      List.reverse_nil, List.map_nil, List.append_nil]
    cases hr : eval ⟨false, b⟩ (0 :: p) e with
    | mk fst snd => simp [hr] at hnil; subst hnil; rfl
  | .letS x dl i r, h => by
    simp [tailsCleanBlock] at h
    simp [evalBlock, eval_tail2024_eq b (0 :: p) i h.1, evalBlock_tail2024_eq b (1 :: p) r h.2]
  | .exprS e r, h => by
    simp [tailsCleanBlock] at h
    simp [evalBlock, eval_tail2024_eq b (0 :: p) e h.1, evalBlock_tail2024_eq b (1 :: p) r h.2]
end

mutual
private theorem eval_ifLet2024_eq (b : Bool) (p : Tag) : (e : Expr) → ifLetsClean e = true →
    eval ⟨b, true⟩ p e = eval ⟨b, false⟩ p e
  | .unit, _ => rfl
  | .out _, _ => rfl
  | .temp _ _, _ => rfl
  | .seq a c, h => by
    simp [ifLetsClean] at h
    simp [eval, eval_ifLet2024_eq b (0 :: p) a h.1, eval_ifLet2024_eq b (1 :: p) c h.2]
  | .block bl, h => evalBlock_ifLet2024_eq b (0 :: p) bl h
  | .ifLet hit s a c, h => by
    simp [ifLetsClean] at h
    have hs := eval_ifLet2024_eq b (0 :: p) s h.1.1.2
    have ha := eval_ifLet2024_eq b (1 :: p) a h.1.2
    have hc := eval_ifLet2024_eq b (2 :: p) c h.2
    have hnil := eval_snd_nil ⟨b, false⟩ (0 :: p) s h.1.1.1
    simp only [eval, hs, ha, hc, ↓reduceIte, Bool.false_eq_true, hnil, dropAll,
      List.reverse_nil, List.map_nil, List.append_nil]
    cases hit <;> rfl
  | .matchE hit s a c, h => by
    simp [ifLetsClean] at h
    simp [eval, eval_ifLet2024_eq b (0 :: p) s h.1.1, eval_ifLet2024_eq b (1 :: p) a h.1.2,
          eval_ifLet2024_eq b (2 :: p) c h.2]

private theorem evalBlock_ifLet2024_eq (b : Bool) (p : Tag) :
    (bl : Block) → ifLetsCleanBlock bl = true →
    evalBlock ⟨b, true⟩ p bl = evalBlock ⟨b, false⟩ p bl
  | .tail e, h => by
    simp [ifLetsCleanBlock] at h
    simp [evalBlock, eval_ifLet2024_eq b (0 :: p) e h]
  | .letS x dl i r, h => by
    simp [ifLetsCleanBlock] at h
    simp [evalBlock, eval_ifLet2024_eq b (0 :: p) i h.1, evalBlock_ifLet2024_eq b (1 :: p) r h.2]
  | .exprS e r, h => by
    simp [ifLetsCleanBlock] at h
    simp [evalBlock, eval_ifLet2024_eq b (0 :: p) e h.1, evalBlock_ifLet2024_eq b (1 :: p) r h.2]
end

mutual
private theorem eval_toMatch_eq (R : Rules) (p : Tag) : (e : Expr) →
    eval R p (toMatch e) = eval { R with ifLet2024 := false } p e
  | .unit => rfl
  | .out _ => rfl
  | .temp _ _ => rfl
  | .seq a c => by simp [toMatch, eval, eval_toMatch_eq R (0 :: p) a, eval_toMatch_eq R (1 :: p) c]
  | .block bl => evalBlock_toMatch_eq R (0 :: p) bl
  | .ifLet hit s a c => by
    simp [toMatch, eval, eval_toMatch_eq R (0 :: p) s, eval_toMatch_eq R (1 :: p) a,
          eval_toMatch_eq R (2 :: p) c]
  | .matchE hit s a c => by
    simp [toMatch, eval, eval_toMatch_eq R (0 :: p) s, eval_toMatch_eq R (1 :: p) a,
          eval_toMatch_eq R (2 :: p) c]

private theorem evalBlock_toMatch_eq (R : Rules) (p : Tag) : (bl : Block) →
    evalBlock R p (toMatchBlock bl) = evalBlock { R with ifLet2024 := false } p bl
  | .tail e => by simp [toMatchBlock, evalBlock, eval_toMatch_eq R (0 :: p) e]
  | .letS x dl i r => by
    simp [toMatchBlock, evalBlock, eval_toMatch_eq R (0 :: p) i, evalBlock_toMatch_eq R (1 :: p) r]
  | .exprS e r => by
    simp [toMatchBlock, evalBlock, eval_toMatch_eq R (0 :: p) e, evalBlock_toMatch_eq R (1 :: p) r]
end

private theorem eval_tempsSeq (R : Rules) (ds : List (List Ev)) (p : Tag) :
    (eval R p (tempsSeq ds)).1.flatMap Act.events = [] ∧
    ((eval R p (tempsSeq ds)).2.map (·.dt)) = ds := by
  induction ds generalizing p with
  | nil => simp [tempsSeq, eval]
  | cons d ds ih =>
    rcases ih (1 :: p) with ⟨h1, h2⟩
    simp [tempsSeq, eval, Act.events, h1, h2]

private theorem eval_outsSeq (R : Rules) (es : List Nat) (p : Tag) :
    (eval R p (outsSeq es)).1.flatMap Act.events = es.map Ev.out ∧
    (eval R p (outsSeq es)).2 = [] := by
  induction es generalizing p with
  | nil => simp [outsSeq, eval]
  | cons n ns ih =>
    rcases ih (1 :: p) with ⟨h1, h2⟩
    simp [outsSeq, eval, Act.events, h1, h2]

private theorem dropAll_events (ps : List Pending) :
    (dropAll ps).flatMap Act.events = (ps.map (·.dt)).reverse.flatten := by
  unfold dropAll
  induction ps with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, Act.events, List.append_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, ih]

private theorem evalBlock_letsFrom (R : Rules) (ls : List (List Ev)) (k : Nat) (b : Block)
    (p : Tag) :
    (evalBlock R p (letsFrom k ls b)).1.flatMap Act.events =
      (evalBlock R (List.replicate ls.length 1 ++ p) b).1.flatMap Act.events ++ dropOrderEvents ls ∧
    (evalBlock R p (letsFrom k ls b)).2 =
      (evalBlock R (List.replicate ls.length 1 ++ p) b).2 := by
  induction ls generalizing k p with
  | nil => simp [letsFrom, dropOrderEvents]
  | cons dl ls ih =>
    rcases ih (k + 1) (1 :: p) with ⟨h1, h2⟩
    have hrep : List.replicate (ls.length + 1) 1 ++ p = List.replicate ls.length 1 ++ (1 :: p) := by
      simp [List.replicate_succ', List.append_assoc]
    constructor
    · simp only [letsFrom, evalBlock, eval, closeScope, dropAll, List.reverse_nil, List.map_nil,
        List.append_nil, List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        Act.events, h1, List.length_cons, hrep, dropOrderEvents, List.reverse_cons,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_assoc]
    · simp only [letsFrom, evalBlock, h2, List.length_cons, hrep]

/-- The syntax position (tag) of an action. -/
private def actTag : Act → Tag
  | .out t _ => t
  | .mkLocal t _ => t
  | .dropLocal t _ _ => t
  | .mkTemp t _ => t
  | .dropTemp t _ _ => t

private theorem dropAll_append (ps qs : List Pending) :
    dropAll (ps ++ qs) = dropAll qs ++ dropAll ps := by
  simp [dropAll, List.reverse_append, List.map_append]

private theorem nodup_append_disjoint {α : Type} {l₁ l₂ : List α}
    (h1 : l₁.Nodup) (h2 : l₂.Nodup) (hd : ∀ x ∈ l₁, x ∉ l₂) :
    (l₁ ++ l₂).Nodup := by
  rw [List.nodup_append]
  exact ⟨h1, h2, fun a ha b hb hab => hd a ha (hab ▸ hb)⟩

private theorem suffix_disjoint {k₁ k₂ : Nat} {p t : Tag} (hne : k₁ ≠ k₂)
    (h1 : (k₁ :: p) <:+ t) (h2 : (k₂ :: p) <:+ t) : False := by
  rcases h1 with ⟨u₁, hu₁⟩
  rcases h2 with ⟨u₂, hu₂⟩
  have hrev := congrArg List.reverse (hu₁.trans hu₂.symm)
  simp [List.reverse_append] at hrev
  exact hne hrev.1

private theorem suffix_ne_self {k : Nat} {p t : Tag} (h : (k :: p) <:+ t) : t ≠ p := by
  rcases h with ⟨u, rfl⟩
  intro heq
  have := congrArg List.length heq
  simp at this
  omega

private theorem perm_mid_swap {α : Type} (a b c d : List α) :
    ((a ++ b) ++ (c ++ d)).Perm ((a ++ d) ++ (b ++ c)) := by
  have h1 : (b ++ (c ++ d)).Perm ((d ++ b) ++ c) := by
    have ha : (b ++ (c ++ d)).Perm (b ++ (d ++ c)) := List.Perm.append_left _ List.perm_append_comm
    have hb : (b ++ (d ++ c)).Perm ((d ++ b) ++ c) := by
      rw [← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
    exact ha.trans hb
  have h2 := List.Perm.append_left a h1
  simpa [List.append_assoc] using h2

private theorem perm_pull_right {α : Type} (a b c : List α) :
    ((a ++ b) ++ c).Perm ((a ++ c) ++ b) := by
  have h := List.Perm.append_left a (@List.perm_append_comm α b c)
  simpa [List.append_assoc] using h

mutual
private theorem eval_perm_nodup_suffix (R₁ R₂ : Rules) (p : Tag) : (e : Expr) →
    (closeScope (eval R₁ p e)).Perm (closeScope (eval R₂ p e)) ∧
    (closeScope (eval R₁ p e)).Nodup ∧
    (∀ a ∈ closeScope (eval R₁ p e), p <:+ actTag a)
  | .unit => ⟨List.Perm.refl _, List.nodup_nil, by simp [eval, closeScope, dropAll]⟩
  | .out n => ⟨List.Perm.refl _, by simp [eval, closeScope, dropAll],
      by intro a ha; simp [eval, closeScope, dropAll] at ha; subst ha; exact List.suffix_refl p⟩
  | .temp dt bs =>
    ⟨List.Perm.refl _,
     by simp [eval, closeScope, dropAll],
     by
      intro a ha; simp [eval, closeScope, dropAll] at ha
      rcases ha with rfl | rfl <;> exact List.suffix_refl p⟩
  | .seq a b => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) a with ⟨hpa, hna, hsa⟩
    rcases eval_perm_nodup_suffix R₁ R₂ (1 :: p) b with ⟨hpb, hnb, hsb⟩
    have hperm : ∀ R, (closeScope (eval R p (.seq a b))).Perm
        (closeScope (eval R (0 :: p) a) ++ closeScope (eval R (1 :: p) b)) := by
      intro R; simp only [eval, closeScope, dropAll_append]; exact perm_mid_swap _ _ _ _
    have hnd_app : (closeScope (eval R₁ (0 :: p) a) ++ closeScope (eval R₁ (1 :: p) b)).Nodup :=
      nodup_append_disjoint hna hnb fun x hx hy => suffix_disjoint (by decide) (hsa x hx) (hsb x hy)
    refine ⟨(hperm R₁).trans ((hpa.append hpb).trans (hperm R₂).symm),
      (hperm R₁).nodup_iff.mpr hnd_app, ?_⟩
    intro x hx
    rcases List.mem_append.mp ((hperm R₁).subset hx) with h | h
    · exact (List.suffix_cons 0 p).trans (hsa x h)
    · exact (List.suffix_cons 1 p).trans (hsb x h)
  | .block bl => by
    rcases evalBlock_perm_nodup_suffix R₁ R₂ (0 :: p) bl with ⟨hp, hn, hs⟩
    exact ⟨hp, hn, fun x hx => (List.suffix_cons 0 p).trans (hs x hx)⟩
  | .ifLet hit s a b => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) s with ⟨hps, hns, hss⟩
    rcases eval_perm_nodup_suffix R₁ R₂ (1 :: p) a with ⟨hpa, hna, hsa⟩
    rcases eval_perm_nodup_suffix R₁ R₂ (2 :: p) b with ⟨hpb, hnb, hsb⟩
    have hstep : ∀ R, (closeScope (eval R p (.ifLet hit s a b))).Perm
        (closeScope (eval R (0 :: p) s) ++
          (if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b))) := by
      intro R; simp only [eval, closeScope]
      cases R.ifLet2024 with
      | true =>
        cases hit with
        | true =>
          simp only [↓reduceIte, dropAll, List.reverse_nil, List.map_nil, List.append_nil]
          exact perm_pull_right _ _ _
        | false => simp [dropAll, List.append_assoc]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact perm_pull_right _ _ _
    have hbody_p : (if hit then closeScope (eval R₁ (1 :: p) a)
        else closeScope (eval R₁ (2 :: p) b)).Perm
        (if hit then closeScope (eval R₂ (1 :: p) a) else closeScope (eval R₂ (2 :: p) b)) := by
      cases hit <;> assumption
    have hnd_app : (closeScope (eval R₁ (0 :: p) s) ++
        (if hit then closeScope (eval R₁ (1 :: p) a)
          else closeScope (eval R₁ (2 :: p) b))).Nodup := by
      cases hit
      · exact nodup_append_disjoint hns hnb fun x hx hy =>
          suffix_disjoint (by decide) (hss x hx) (hsb x hy)
      · exact nodup_append_disjoint hns hna fun x hx hy =>
          suffix_disjoint (by decide) (hss x hx) (hsa x hy)
    refine ⟨(hstep R₁).trans ((hps.append hbody_p).trans (hstep R₂).symm),
      (hstep R₁).nodup_iff.mpr hnd_app, ?_⟩
    intro x hx
    rcases List.mem_append.mp ((hstep R₁).subset hx) with h | h
    · exact (List.suffix_cons 0 p).trans (hss x h)
    · cases hit
      · simp at h; exact (List.suffix_cons 2 p).trans (hsb x h)
      · simp at h; exact (List.suffix_cons 1 p).trans (hsa x h)
  | .matchE hit s a b => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) s with ⟨hps, hns, hss⟩
    rcases eval_perm_nodup_suffix R₁ R₂ (1 :: p) a with ⟨hpa, hna, hsa⟩
    rcases eval_perm_nodup_suffix R₁ R₂ (2 :: p) b with ⟨hpb, hnb, hsb⟩
    have hstep : ∀ R, (closeScope (eval R p (.matchE hit s a b))).Perm
        (closeScope (eval R (0 :: p) s) ++
          (if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b))) := by
      intro R; simp only [eval, closeScope]; exact perm_pull_right _ _ _
    have hbody_p : (if hit then closeScope (eval R₁ (1 :: p) a)
        else closeScope (eval R₁ (2 :: p) b)).Perm
        (if hit then closeScope (eval R₂ (1 :: p) a) else closeScope (eval R₂ (2 :: p) b)) := by
      cases hit <;> assumption
    have hnd_app : (closeScope (eval R₁ (0 :: p) s) ++
        (if hit then closeScope (eval R₁ (1 :: p) a)
          else closeScope (eval R₁ (2 :: p) b))).Nodup := by
      cases hit
      · exact nodup_append_disjoint hns hnb fun x hx hy =>
          suffix_disjoint (by decide) (hss x hx) (hsb x hy)
      · exact nodup_append_disjoint hns hna fun x hx hy =>
          suffix_disjoint (by decide) (hss x hx) (hsa x hy)
    refine ⟨(hstep R₁).trans ((hps.append hbody_p).trans (hstep R₂).symm),
      (hstep R₁).nodup_iff.mpr hnd_app, ?_⟩
    intro x hx
    rcases List.mem_append.mp ((hstep R₁).subset hx) with h | h
    · exact (List.suffix_cons 0 p).trans (hss x h)
    · cases hit
      · simp at h; exact (List.suffix_cons 2 p).trans (hsb x h)
      · simp at h; exact (List.suffix_cons 1 p).trans (hsa x h)

private theorem evalBlock_perm_nodup_suffix (R₁ R₂ : Rules) (p : Tag) : (bl : Block) →
    (closeScope (evalBlock R₁ p bl)).Perm (closeScope (evalBlock R₂ p bl)) ∧
    (closeScope (evalBlock R₁ p bl)).Nodup ∧
    (∀ a ∈ closeScope (evalBlock R₁ p bl), p <:+ actTag a)
  | .tail e => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) e with ⟨hp, hn, hs⟩
    have hcl : ∀ R, closeScope (evalBlock R p (.tail e)) = closeScope (eval R (0 :: p) e) := by
      intro R; simp only [evalBlock]; cases R.tail2024 <;> simp [closeScope, dropAll]
    rw [hcl R₁, hcl R₂]
    exact ⟨hp, hn, fun x hx => (List.suffix_cons 0 p).trans (hs x hx)⟩
  | .letS x dl i r => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) i with ⟨hpi, hni, hsi⟩
    rcases evalBlock_perm_nodup_suffix R₁ R₂ (1 :: p) r with ⟨hpr, hnr, hsr⟩
    have hstep : ∀ R, (closeScope (evalBlock R p (.letS x dl i r))).Perm
        (closeScope (eval R (0 :: p) i) ++
          ([.mkLocal p x, .dropLocal p x dl] ++ closeScope (evalBlock R (1 :: p) r))) := by
      intro R; simp only [evalBlock, closeScope]
      have h1 : (([Act.mkLocal p x] ++ (evalBlock R (1 :: p) r).1) ++ [Act.dropLocal p x dl]).Perm
          ([Act.mkLocal p x, Act.dropLocal p x dl] ++ (evalBlock R (1 :: p) r).1) :=
        perm_pull_right [Act.mkLocal p x] (evalBlock R (1 :: p) r).1 [Act.dropLocal p x dl]
      have h2 := h1.append_right (dropAll (evalBlock R (1 :: p) r).2)
      have h3 := List.Perm.append_left (closeScope (eval R (0 :: p) i)) h2
      simpa [closeScope, List.append_assoc] using h3
    have hloc_nd : ([Act.mkLocal p x, Act.dropLocal p x dl] ++
        closeScope (evalBlock R₁ (1 :: p) r)).Nodup := by
      refine nodup_append_disjoint (by simp) hnr fun a ha hb => ?_
      simp at ha
      rcases ha with rfl | rfl
      · exact suffix_ne_self (hsr _ hb) rfl
      · exact suffix_ne_self (hsr _ hb) rfl
    have hnd_app : (closeScope (eval R₁ (0 :: p) i) ++ ([Act.mkLocal p x, Act.dropLocal p x dl] ++
        closeScope (evalBlock R₁ (1 :: p) r))).Nodup := by
      refine nodup_append_disjoint hni hloc_nd fun a ha hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · simp at hb
        rcases hb with rfl | rfl
        · exact suffix_ne_self (hsi _ ha) rfl
        · exact suffix_ne_self (hsi _ ha) rfl
      · exact suffix_disjoint (by decide) (hsi a ha) (hsr a hb)
    refine ⟨(hstep R₁).trans ((hpi.append (List.Perm.append_left _ hpr)).trans (hstep R₂).symm),
            (hstep R₁).nodup_iff.mpr hnd_app, ?_⟩
    intro a ha
    rcases List.mem_append.mp ((hstep R₁).subset ha) with h | h
    · exact (List.suffix_cons 0 p).trans (hsi a h)
    · rcases List.mem_append.mp h with h | h
      · simp at h; rcases h with rfl | rfl <;> exact List.suffix_refl p
      · exact (List.suffix_cons 1 p).trans (hsr a h)
  | .exprS e r => by
    rcases eval_perm_nodup_suffix R₁ R₂ (0 :: p) e with ⟨hpe, hne, hse⟩
    rcases evalBlock_perm_nodup_suffix R₁ R₂ (1 :: p) r with ⟨hpr, hnr, hsr⟩
    have hstep : ∀ R, closeScope (evalBlock R p (.exprS e r)) =
        closeScope (eval R (0 :: p) e) ++ closeScope (evalBlock R (1 :: p) r) := by
      intro R; simp [evalBlock, closeScope, List.append_assoc]
    rw [hstep R₁, hstep R₂]
    refine ⟨hpe.append hpr,
            nodup_append_disjoint hne hnr fun x hx hy =>
              suffix_disjoint (by decide) (hse x hx) (hsr x hy), ?_⟩
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact (List.suffix_cons 0 p).trans (hse a h)
    · exact (List.suffix_cons 1 p).trans (hsr a h)
end

private theorem dropAll_filter_not_dropTemp (ps : List Pending) :
    (dropAll ps).filter (fun a => !a.isDropTemp) = [] := by
  unfold dropAll
  induction ps with
  | nil => rfl
  | cons q qs _ =>
    simp [List.reverse_cons, List.filter_append, Act.isDropTemp]

private theorem filterMap_perm {α β : Type} (f : α → Option β) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : (l₁.filterMap f).Perm (l₂.filterMap f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih =>
    cases hf : f x <;> simp [hf, ih]
  | swap x y l =>
    cases hfx : f x <;> cases hfy : f y <;> simp [hfx, hfy]
    exact List.Perm.swap _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem dropTemps_perm {l₁ l₂ : List Act} (h : l₁.Perm l₂) :
    (dropTemps l₁).Perm (dropTemps l₂) :=
  filterMap_perm _ h

private theorem mkTemps_perm {l₁ l₂ : List Act} (h : l₁.Perm l₂) :
    (mkTemps l₁).Perm (mkTemps l₂) :=
  filterMap_perm _ h

private theorem dropTemps_append (l₁ l₂ : List Act) :
    dropTemps (l₁ ++ l₂) = dropTemps l₁ ++ dropTemps l₂ := by
  simp [dropTemps, List.filterMap_append]

private theorem mkTemps_append (l₁ l₂ : List Act) :
    mkTemps (l₁ ++ l₂) = mkTemps l₁ ++ mkTemps l₂ := by
  simp [mkTemps, List.filterMap_append]

mutual
private theorem eval_dropTemps_perm_mkTemps (R : Rules) (p : Tag) : (e : Expr) →
    (dropTemps (closeScope (eval R p e))).Perm (mkTemps (closeScope (eval R p e)))
  | .unit => by simp [eval, closeScope, dropAll, dropTemps, mkTemps]
  | .out _ => by show List.Perm [] []; exact List.Perm.nil
  | .temp _ bs => by show List.Perm [(p, bs)] [(p, bs)]; exact List.Perm.refl _
  | .seq a b => by
    have hperm : (closeScope (eval R p (.seq a b))).Perm
        (closeScope (eval R (0 :: p) a) ++ closeScope (eval R (1 :: p) b)) := by
      simp only [eval, closeScope, dropAll_append]; exact perm_mid_swap _ _ _ _
    have hd := dropTemps_perm hperm
    have hm := mkTemps_perm hperm
    rw [dropTemps_append] at hd
    rw [mkTemps_append] at hm
    exact hd.trans (((eval_dropTemps_perm_mkTemps R (0 :: p) a).append
      (eval_dropTemps_perm_mkTemps R (1 :: p) b)).trans hm.symm)
  | .block bl => evalBlock_dropTemps_perm_mkTemps R (0 :: p) bl
  | .ifLet hit s a b => by
    have hstep : (closeScope (eval R p (.ifLet hit s a b))).Perm
        (closeScope (eval R (0 :: p) s) ++
          (if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b))) := by
      simp only [eval, closeScope]
      cases R.ifLet2024 with
      | true =>
        cases hit with
        | true =>
          simp only [↓reduceIte, dropAll, List.reverse_nil, List.map_nil, List.append_nil]
          exact perm_pull_right _ _ _
        | false => simp [dropAll, List.append_assoc]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]; exact perm_pull_right _ _ _
    have hd := dropTemps_perm hstep
    have hm := mkTemps_perm hstep
    rw [dropTemps_append] at hd
    rw [mkTemps_append] at hm
    have ihs := eval_dropTemps_perm_mkTemps R (0 :: p) s
    have ihbody : (dropTemps (if hit then closeScope (eval R (1 :: p) a)
        else closeScope (eval R (2 :: p) b))).Perm
        (mkTemps (if hit then closeScope (eval R (1 :: p) a)
          else closeScope (eval R (2 :: p) b))) := by
      cases hit
      · exact eval_dropTemps_perm_mkTemps R (2 :: p) b
      · exact eval_dropTemps_perm_mkTemps R (1 :: p) a
    exact hd.trans ((ihs.append ihbody).trans hm.symm)
  | .matchE hit s a b => by
    have hstep : (closeScope (eval R p (.matchE hit s a b))).Perm
        (closeScope (eval R (0 :: p) s) ++
          (if hit then closeScope (eval R (1 :: p) a) else closeScope (eval R (2 :: p) b))) := by
      simp only [eval, closeScope]; exact perm_pull_right _ _ _
    have hd := dropTemps_perm hstep
    have hm := mkTemps_perm hstep
    rw [dropTemps_append] at hd
    rw [mkTemps_append] at hm
    have ihs := eval_dropTemps_perm_mkTemps R (0 :: p) s
    have ihbody : (dropTemps (if hit then closeScope (eval R (1 :: p) a)
        else closeScope (eval R (2 :: p) b))).Perm
        (mkTemps (if hit then closeScope (eval R (1 :: p) a)
          else closeScope (eval R (2 :: p) b))) := by
      cases hit
      · exact eval_dropTemps_perm_mkTemps R (2 :: p) b
      · exact eval_dropTemps_perm_mkTemps R (1 :: p) a
    exact hd.trans ((ihs.append ihbody).trans hm.symm)

private theorem evalBlock_dropTemps_perm_mkTemps (R : Rules) (p : Tag) : (bl : Block) →
    (dropTemps (closeScope (evalBlock R p bl))).Perm (mkTemps (closeScope (evalBlock R p bl)))
  | .tail e => by
    have hcl : closeScope (evalBlock R p (.tail e)) = closeScope (eval R (0 :: p) e) := by
      simp only [evalBlock]; cases R.tail2024 <;> simp [closeScope, dropAll]
    rw [hcl]; exact eval_dropTemps_perm_mkTemps R (0 :: p) e
  | .letS x dl i r => by
    have hstep : (closeScope (evalBlock R p (.letS x dl i r))).Perm
        (closeScope (eval R (0 :: p) i) ++
          ([.mkLocal p x, .dropLocal p x dl] ++ closeScope (evalBlock R (1 :: p) r))) := by
      simp only [evalBlock, closeScope]
      have h1 : (([Act.mkLocal p x] ++ (evalBlock R (1 :: p) r).1) ++ [Act.dropLocal p x dl]).Perm
          ([Act.mkLocal p x, Act.dropLocal p x dl] ++ (evalBlock R (1 :: p) r).1) :=
        perm_pull_right [Act.mkLocal p x] (evalBlock R (1 :: p) r).1 [Act.dropLocal p x dl]
      have h2 := h1.append_right (dropAll (evalBlock R (1 :: p) r).2)
      have h3 := List.Perm.append_left (closeScope (eval R (0 :: p) i)) h2
      simpa [closeScope, List.append_assoc] using h3
    have hd := dropTemps_perm hstep
    have hm := mkTemps_perm hstep
    rw [dropTemps_append, dropTemps_append] at hd
    rw [mkTemps_append, mkTemps_append] at hm
    have hloc_d : dropTemps [.mkLocal p x, .dropLocal p x dl] = [] := rfl
    have hloc_m : mkTemps [.mkLocal p x, .dropLocal p x dl] = [] := rfl
    rw [hloc_d, List.nil_append] at hd
    rw [hloc_m, List.nil_append] at hm
    exact hd.trans (((eval_dropTemps_perm_mkTemps R (0 :: p) i).append
      (evalBlock_dropTemps_perm_mkTemps R (1 :: p) r)).trans hm.symm)
  | .exprS e r => by
    have hstep : closeScope (evalBlock R p (.exprS e r)) =
        closeScope (eval R (0 :: p) e) ++ closeScope (evalBlock R (1 :: p) r) := by
      simp [evalBlock, closeScope, List.append_assoc]
    rw [hstep, dropTemps_append, mkTemps_append]
    exact (eval_dropTemps_perm_mkTemps R (0 :: p) e).append
      (evalBlock_dropTemps_perm_mkTemps R (1 :: p) r)
end

mutual
private theorem eval_nonDropTemp_eq (R₁ R₂ : Rules) (p : Tag) : (e : Expr) →
    (eval R₁ p e).1.filter (fun a => !a.isDropTemp) =
      (eval R₂ p e).1.filter (fun a => !a.isDropTemp)
  | .unit => rfl
  | .out _ => rfl
  | .temp _ _ => rfl
  | .seq a b => by
    simp [eval, List.filter_append, eval_nonDropTemp_eq R₁ R₂ (0 :: p) a,
      eval_nonDropTemp_eq R₁ R₂ (1 :: p) b]
  | .block bl => evalBlock_nonDropTemp_eq R₁ R₂ (0 :: p) bl
  | .ifLet hit s a b => by
    have hs := eval_nonDropTemp_eq R₁ R₂ (0 :: p) s
    have ha := eval_nonDropTemp_eq R₁ R₂ (1 :: p) a
    have hb := eval_nonDropTemp_eq R₁ R₂ (2 :: p) b
    simp only [eval]
    cases R₁.ifLet2024 <;> cases R₂.ifLet2024 <;> cases hit <;>
      simp [closeScope, List.filter_append, dropAll_filter_not_dropTemp, hs, ha, hb]
  | .matchE hit s a b => by
    have hs := eval_nonDropTemp_eq R₁ R₂ (0 :: p) s
    have ha := eval_nonDropTemp_eq R₁ R₂ (1 :: p) a
    have hb := eval_nonDropTemp_eq R₁ R₂ (2 :: p) b
    simp only [eval]
    cases hit <;> simp [closeScope, List.filter_append, dropAll_filter_not_dropTemp, hs, ha, hb]

private theorem evalBlock_nonDropTemp_eq (R₁ R₂ : Rules) (p : Tag) : (bl : Block) →
    (evalBlock R₁ p bl).1.filter (fun a => !a.isDropTemp) =
      (evalBlock R₂ p bl).1.filter (fun a => !a.isDropTemp)
  | .tail e => by
    have he := eval_nonDropTemp_eq R₁ R₂ (0 :: p) e
    simp only [evalBlock]
    cases R₁.tail2024 <;> cases R₂.tail2024 <;>
      simp [closeScope, List.filter_append, dropAll_filter_not_dropTemp, he]
  | .letS x dl i r => by
    simp only [evalBlock, closeScope, List.filter_append, dropAll_filter_not_dropTemp,
      eval_nonDropTemp_eq R₁ R₂ (0 :: p) i, evalBlock_nonDropTemp_eq R₁ R₂ (1 :: p) r]
  | .exprS e r => by
    simp [evalBlock, closeScope, List.filter_append, dropAll_filter_not_dropTemp,
          eval_nonDropTemp_eq R₁ R₂ (0 :: p) e, evalBlock_nonDropTemp_eq R₁ R₂ (1 :: p) r]
end

private theorem flatMap_comm_left (pre : List Act) (x : Act) (h : ∀ a ∈ pre, Commute a x) :
    pre.flatMap Act.events ++ x.events = x.events ++ pre.flatMap Act.events := by
  induction pre with
  | nil => simp
  | cons a rest ih =>
    have ha : a.events ++ x.events = x.events ++ a.events := h a (List.mem_cons_self ..)
    have hr := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.flatMap_cons, List.append_assoc, hr]
    rw [← List.append_assoc, ha, List.append_assoc]

private theorem before_of_split {l₁ l₂ : List Act} {a b : Act} (ha : a ∈ l₁) (hb : b ∈ l₂) :
    Before (l₁ ++ l₂) a b := by
  rcases List.getElem_of_mem ha with ⟨i, hi, rfl⟩
  rcases List.getElem_of_mem hb with ⟨j, hj, rfl⟩
  refine ⟨i, l₁.length + j, by omega, ?_, ?_⟩
  · rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  · rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp [Nat.add_sub_cancel_left, hj]

private theorem before_of_sublist_remove {pre post : List Act} {x a b : Act}
    (h : Before (pre ++ post) a b) : Before (pre ++ x :: post) a b := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  by_cases hi' : i < pre.length
  · by_cases hj' : j < pre.length
    · refine ⟨i, j, hij, ?_, ?_⟩
      · rw [List.getElem?_append_left hi'] at hi ⊢; exact hi
      · rw [List.getElem?_append_left hj'] at hj ⊢; exact hj
    · refine ⟨i, j + 1, by omega, ?_, ?_⟩
      · rw [List.getElem?_append_left hi'] at hi ⊢; exact hi
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hj')] at hj
        rw [List.getElem?_append_right (by omega)]
        have : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        rw [this]; exact hj
  · have hj' : ¬ j < pre.length := by omega
    refine ⟨i + 1, j + 1, by omega, ?_, ?_⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi')] at hi
      rw [List.getElem?_append_right (by omega)]
      have : i + 1 - pre.length = (i - pre.length) + 1 := by omega
      rw [this]; exact hi
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj')] at hj
      rw [List.getElem?_append_right (by omega)]
      have : j + 1 - pre.length = (j - pre.length) + 1 := by omega
      rw [this]; exact hj

private theorem before_cons_of_before {x a b : Act} {l : List Act} (h : Before l a b) :
    Before (x :: l) a b := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  exact ⟨i + 1, j + 1, by omega, hi, hj⟩

private theorem flatMap_eq_of_perm_nodup_comm :
    ∀ (l₂ l₁ : List Act), l₁.Perm l₂ → l₁.Nodup →
      (∀ a b, Before l₁ a b → Before l₂ b a → Commute a b) →
      l₁.flatMap Act.events = l₂.flatMap Act.events
  | [], l₁, hperm, _, _ => by
    have := hperm.eq_nil; subst this; rfl
  | x :: l₂', l₁, hperm, hnd, hcomm => by
    have hx : x ∈ l₁ := hperm.mem_iff.mpr (List.mem_cons_self ..)
    rcases List.append_of_mem hx with ⟨pre, post, rfl⟩
    have hperm' : (pre ++ post).Perm l₂' := by
      have : (x :: (pre ++ post)).Perm (x :: l₂') :=
        (List.perm_middle.symm).trans hperm
      exact (List.perm_cons x).mp this
    have hnd' : (pre ++ post).Nodup := by
      have := (List.perm_middle.nodup_iff).mp hnd
      exact (List.nodup_cons.mp this).2
    have hpre_comm : ∀ a ∈ pre, Commute a x := by
      intro a ha
      have hb1 : Before (pre ++ x :: post) a x :=
        before_of_split ha (List.mem_cons_self ..)
      have ha_l₂ : a ∈ l₂' := hperm'.mem_iff.mp (List.mem_append_left post ha)
      have hb2 : Before (x :: l₂') x a :=
        before_of_split (l₁ := [x]) (l₂ := l₂') (List.mem_cons_self ..) ha_l₂
      exact hcomm a x hb1 hb2
    have hsub : ∀ a b, Before (pre ++ post) a b → Before l₂' b a → Commute a b :=
      fun a b h1 h2 => hcomm a b (before_of_sublist_remove h1) (before_cons_of_before h2)
    have ih := flatMap_eq_of_perm_nodup_comm l₂' (pre ++ post) hperm' hnd' hsub
    simp only [List.flatMap_append, List.flatMap_cons] at ih ⊢
    rw [← List.append_assoc, flatMap_comm_left pre x hpre_comm, List.append_assoc, ih]

/-! ## R1: edition invariance of the core -/

/-- R1-tail. With the `if let` rule held fixed at either setting, the tail rule does not change
the executed actions of a program with `NoTailEscapingTemps`. -/
theorem run_tail2024_eq_of_noTailEscapingTemps (e : Expr) (b : Bool) (ht : NoTailEscapingTemps e) :
    run ⟨true, b⟩ e = run ⟨false, b⟩ e := by
  unfold run; rw [eval_tail2024_eq b [] e ht]

/-- R1-ifLet. With the tail rule held fixed at either setting, the `if let` rule does not change
the executed actions of a program with `NoIfLetEscapingTemps`. -/
theorem run_ifLet2024_eq_of_noIfLetEscapingTemps (e : Expr) (b : Bool) (hi : NoIfLetEscapingTemps e) :
    run ⟨b, true⟩ e = run ⟨b, false⟩ e := by
  unfold run; rw [eval_ifLet2024_eq b [] e hi]

/-- R1. On programs in which no temporary escapes a block tail expression
(`NoTailEscapingTemps`) and no temporary escapes an `if let` scrutinee
(`NoIfLetEscapingTemps`), the 2021 and 2024 rules execute the same action list. (Corollary of
R1-tail and R1-ifLet.) -/
theorem run_e2021_eq_run_e2024_of_noTailEscapingTemps_of_noIfLetEscapingTemps (e : Expr)
    (ht : NoTailEscapingTemps e) (hi : NoIfLetEscapingTemps e) :
    run Edition.e2021.rules e = run Edition.e2024.rules e :=
  (run_tail2024_eq_of_noTailEscapingTemps e false ht).symm.trans
    (run_ifLet2024_eq_of_noIfLetEscapingTemps e true hi).symm

/-- R1, consequences. Under the hypotheses of R1, the 2021 and 2024 event traces, toy borrow-check
verdicts and behaviours agree. -/
theorem trace_accepts_beh_eq_of_noTailEscapingTemps_of_noIfLetEscapingTemps (e : Expr)
    (ht : NoTailEscapingTemps e) (hi : NoIfLetEscapingTemps e) :
    trace Edition.e2021.rules e = trace Edition.e2024.rules e ∧
    accepts Edition.e2021.rules e = accepts Edition.e2024.rules e ∧
    beh Edition.e2021.rules e = beh Edition.e2024.rules e := by
  have h := run_e2021_eq_run_e2024_of_noTailEscapingTemps_of_noIfLetEscapingTemps e ht hi
  exact ⟨by simp only [trace, h], by simp only [accepts, h], by unfold beh trace accepts; rw [h]⟩

/-- R1-perm. For any two rule settings `R₁` and `R₂`: the executed action lists of a program are
permutations of each other; the list under `R₁` contains no action twice; under `R₁` the
temporaries dropped (tag and borrow list of every `dropTemp`) are a permutation of the temporaries
created (every `mkTemp`); and the actions other than temporary drops occur in the same order under
both settings. -/
theorem run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq (R₁ R₂ : Rules) (e : Expr) :
    (run R₁ e).Perm (run R₂ e) ∧ (run R₁ e).Nodup ∧
    (dropTemps (run R₁ e)).Perm (mkTemps (run R₁ e)) ∧
    (run R₁ e).filter (fun a => !a.isDropTemp) = (run R₂ e).filter (fun a => !a.isDropTemp) := by
  refine ⟨(eval_perm_nodup_suffix R₁ R₂ [] e).1, (eval_perm_nodup_suffix R₁ R₂ [] e).2.1,
    eval_dropTemps_perm_mkTemps R₁ [] e, ?_⟩
  simp only [run, closeScope, List.filter_append, dropAll_filter_not_dropTemp, List.append_nil]
  exact eval_nonDropTemp_eq R₁ R₂ [] e

private theorem nodup_mkTemps_of_nodup : ∀ (l : List Act), l.Nodup → (mkTemps l).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have ⟨ha, hl⟩ := List.nodup_cons.mp h
    have ih := nodup_mkTemps_of_nodup l hl
    cases a with
    | mkTemp t bs =>
      show ((t, bs) :: mkTemps l).Nodup
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hmem
      rcases List.mem_filterMap.mp hmem with ⟨a', ha', hk⟩
      cases a' <;> simp [Act.mkTempKey?] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ha ha'
    | out _ _ => exact ih
    | mkLocal _ _ => exact ih
    | dropLocal _ _ _ => exact ih
    | dropTemp _ _ _ => exact ih

/-- R1-perm, consequence: under every rule setting `R`, each temporary created during the run of
`e` (each entry of `mkTemps (run R e)`) occurs exactly once among the temporaries dropped
(`dropTemps (run R e)`). -/
theorem run_each_created_temp_dropped_exactly_once (R : Rules) (e : Expr) :
    ∀ k ∈ mkTemps (run R e), (dropTemps (run R e)).count k = 1 := by
  intro k hk
  have ⟨_, hnd, hperm, _⟩ := run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq R R e
  rw [hperm.count_eq k]
  exact (nodup_mkTemps_of_nodup _ hnd).count_of_mem hk

/-- The `match` construct's own rule is the same under every rule setting: `eval` of a `match`
is the setting-independent combinator `matchStep` applied to its scrutinee's and arms' results
(in particular its pending temporaries are its scrutinee's). This holds by definition of `eval`. -/
theorem eval_matchE_eq_matchStep (R : Rules) (p : Tag) (hit : Bool) (s a b : Expr) :
    eval R p (.matchE hit s a b) =
      matchStep hit (eval R (0 :: p) s) (eval R (1 :: p) a) (eval R (2 :: p) b) := by
  simp only [eval, matchStep]

/-- R1-match-tail. A `match` in tail position: its scrutinee temporary is dropped after the block's
local under the 2021 rules and before it under the 2024 rules; switching the tail rule alone
produces each order, and switching the `if let` rule alone produces neither change. -/
theorem matchInTailProg_scrutinee_drop_moves_by_tail_rule :
    trace Edition.e2021.rules matchInTailProg = [.dtor 0, .dtor 1] ∧
    trace Edition.e2024.rules matchInTailProg = [.dtor 1, .dtor 0] ∧
    trace ⟨true, false⟩ matchInTailProg = [.dtor 1, .dtor 0] ∧
    trace ⟨false, true⟩ matchInTailProg = [.dtor 0, .dtor 1] := by decide

/-- Refutation of the reading "outside block tail positions a `match` scrutinee temporary has the
same drop point in both editions": `matchInIfLetScrutProg` has no block at all (so it satisfies
`NoTailEscapingTemps`), yet its `match` scrutinee temporary, which escapes into an enclosing
`if let` scrutinee, is dropped at different points under the 2021 and 2024 rules. -/
theorem refuted_match_outside_blockTail_same_drop_point :
    NoTailEscapingTemps matchInIfLetScrutProg ∧ ¬ NoIfLetEscapingTemps matchInIfLetScrutProg ∧
    trace Edition.e2021.rules matchInIfLetScrutProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules matchInIfLetScrutProg = [.dtor 0, .out 1] := by decide

/-- R1 non-vacuity: `stmtTempsProg` satisfies both hypotheses; it executes exactly two temporary
drops (a third syntactic temporary sits in the `if let` branch that does not run). -/
theorem stmtTempsProg_noTailEscapingTemps_noIfLetEscapingTemps :
    NoTailEscapingTemps stmtTempsProg ∧ NoIfLetEscapingTemps stmtTempsProg ∧
    trace Edition.e2021.rules stmtTempsProg = [.dtor 1, .out 0, .dtor 3, .out 1, .dtor 0] ∧
    (dropTemps (run Edition.e2021.rules stmtTempsProg)).length = 2 := by
  decide

/-- Refutation of the reading "`stmtTempsProg` executes three temporary drops": under the 2021 rules
it executes two (its third syntactic temporary is in the `if let` branch that does not run). -/
theorem refuted_stmtTempsProg_three_temp_drops :
    (dropTemps (run Edition.e2021.rules stmtTempsProg)).length ≠ 3 := by decide

/-- R1 tightness (`NoTailEscapingTemps`): `tailProg` satisfies `NoIfLetEscapingTemps`, violates
`NoTailEscapingTemps`, and its 2021 and 2024 action lists differ. -/
theorem tailProg_noIfLetEscapingTemps_and_run_ne :
    NoIfLetEscapingTemps tailProg ∧ ¬ NoTailEscapingTemps tailProg ∧
    run Edition.e2021.rules tailProg ≠ run Edition.e2024.rules tailProg := by decide

/-- R1 tightness (`NoIfLetEscapingTemps`): `ifLetElseProg` satisfies `NoTailEscapingTemps`, violates
`NoIfLetEscapingTemps`, and its 2021 and 2024 action lists differ. -/
theorem ifLetElseProg_noTailEscapingTemps_and_run_ne :
    NoTailEscapingTemps ifLetElseProg ∧ ¬ NoIfLetEscapingTemps ifLetElseProg ∧
    run Edition.e2021.rules ifLetElseProg ≠ run Edition.e2024.rules ifLetElseProg := by decide

/-- R1, R1-split and R3-migration: the hypotheses are not necessary for equal action lists.
`topLevelTailTempProg` violates `NoTailEscapingTemps`, satisfies `NoIfLetEscapingTemps`, and the
tail rule leaves its action list unchanged at both settings of the `if let` rule (so its 2021 and
2024 action lists are equal and the `match` rewrite under the 2024 rules reproduces the 2021 action
list); `bareIfLetThenProg` violates `NoIfLetEscapingTemps`, satisfies `NoTailEscapingTemps`, and the
`if let` rule leaves its action list unchanged at both settings of the tail rule. -/
theorem noEscape_hypotheses_not_necessary_for_run_eq :
    (¬ NoTailEscapingTemps topLevelTailTempProg ∧ NoIfLetEscapingTemps topLevelTailTempProg ∧
      (∀ b, run ⟨true, b⟩ topLevelTailTempProg = run ⟨false, b⟩ topLevelTailTempProg) ∧
      run Edition.e2021.rules topLevelTailTempProg = run Edition.e2024.rules topLevelTailTempProg ∧
      run Edition.e2024.rules (toMatch topLevelTailTempProg) =
        run Edition.e2021.rules topLevelTailTempProg) ∧
    (NoTailEscapingTemps bareIfLetThenProg ∧ ¬ NoIfLetEscapingTemps bareIfLetThenProg ∧
      ∀ b, run ⟨b, true⟩ bareIfLetThenProg = run ⟨b, false⟩ bareIfLetThenProg) := by
  decide

/-- Equal traces with different action lists: in `commutingTailProg` the 2021 and 2024 action lists
differ while the event traces are equal. -/
theorem commutingTailProg_run_ne_and_trace_eq :
    run Edition.e2021.rules commutingTailProg ≠ run Edition.e2024.rules commutingTailProg ∧
    trace Edition.e2021.rules commutingTailProg = trace Edition.e2024.rules commutingTailProg := by
  decide

/-- R1-tail tightness: `ifLetInTailProg` violates `NoTailEscapingTemps` and, with the `if let` rule
held at the 2021 setting, the tail rule changes its actions. -/
theorem ifLetInTailProg_tail_rule_changes_run :
    ¬ NoTailEscapingTemps ifLetInTailProg ∧
    run ⟨true, false⟩ ifLetInTailProg ≠ run ⟨false, false⟩ ifLetInTailProg := by decide

/-- R1-ifLet tightness: `ifLetElseProg` violates `NoIfLetEscapingTemps` and, with the tail rule held
at the 2024 setting, the `if let` rule changes its actions. -/
theorem ifLetElseProg_not_noIfLetEscapingTemps_and_ifLet_rule_changes_run :
    ¬ NoIfLetEscapingTemps ifLetElseProg ∧
    run ⟨true, true⟩ ifLetElseProg ≠ run ⟨true, false⟩ ifLetElseProg := by decide

/-- The two rules interact outside both clean classes: for `ifLetInTailProg` the tail rule changes
the action list when the `if let` rule is off, and does not change it when the `if let` rule is
on. -/
theorem ifLetInTailProg_rules_interact :
    run ⟨true, true⟩ ifLetInTailProg = run ⟨false, true⟩ ifLetInTailProg ∧
    run ⟨true, false⟩ ifLetInTailProg ≠ run ⟨false, false⟩ ifLetInTailProg := by decide

/-! ## R2: tail-expression reversal -/

/-- R2. `tailProg` (a local with a destructor event and a tail temporary with a destructor event)
is accepted under both editions and its destructor events occur in opposite orders. -/
theorem tailProg_accepted_and_traces_reversed :
    accepts Edition.e2021.rules tailProg = true ∧ accepts Edition.e2024.rules tailProg = true ∧
    trace Edition.e2021.rules tailProg = [.dtor 0, .dtor 1] ∧
    trace Edition.e2024.rules tailProg = [.dtor 1, .dtor 0] := by decide

/-- R2-incomparable. Neither edition's behaviour is included in the other's: `tailProg` is a
single witness for both directions. -/
theorem not_behIncl_e2021_e2024_and_not_behIncl_e2024_e2021 :
    ¬ BehIncl Edition.e2021.rules Edition.e2024.rules ∧
    ¬ BehIncl Edition.e2024.rules Edition.e2021.rules := by
  obtain ⟨h21, h24⟩ := not_behIncl_e2021_e2024_at_tailProg
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h tailProg _ h21
    rw [h24] at this
    exact absurd this (by decide)
  · have := h tailProg _ h24
    rw [h21] at this
    exact absurd this (by decide)

/-- R2-accept. The toy borrow check accepts the `RefCell` tail-borrow shape under the 2024 rules
and rejects it under the 2021 rules. -/
theorem refCellTailProg_accepted_e2024_rejected_e2021 :
    accepts Edition.e2024.rules refCellTailProg = true ∧
    accepts Edition.e2021.rules refCellTailProg = false := by decide

/-! ## R3: `if let` rescoping and the `match` migration -/

/-- `ifLetElseProg`: the scrutinee temporary's destructor event moves from after the `else`
block's output (2021) to before it (2024). -/
theorem ifLetElseProg_traces_differ :
    trace Edition.e2021.rules ifLetElseProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules ifLetElseProg = [.dtor 0, .out 1] := by decide

/-- R3-match. Under any rule settings `R`, rewriting every `if let` to a `match` gives exactly the
actions of the original program under `R` with the `if let` rule switched to its 2021 setting
(the tail rule is unchanged). -/
theorem run_toMatch_eq_run_ifLet2021 (R : Rules) (e : Expr) :
    run R (toMatch e) = run { R with ifLet2024 := false } e := by
  unfold run; rw [eval_toMatch_eq]

/-- R3-migration. On programs with `NoTailEscapingTemps`, running the `match`-rewritten program
under the 2024 rules executes exactly the actions of the original program under the 2021 rules.
(Corollary of R3-match and R1-tail.) -/
theorem run_e2024_toMatch_eq_run_e2021_of_noTailEscapingTemps (e : Expr) (ht : NoTailEscapingTemps e) :
    run Edition.e2024.rules (toMatch e) = run Edition.e2021.rules e :=
  (run_toMatch_eq_run_ifLet2021 Edition.e2024.rules e).trans
    (run_tail2024_eq_of_noTailEscapingTemps e false ht)

/-- R3-migration non-vacuity: `ifLetElseProg` satisfies `NoTailEscapingTemps` and its 2021 and 2024
traces differ, so the rewrite changes something there. -/
theorem ifLetElseProg_noTailEscapingTemps_and_traces_differ :
    NoTailEscapingTemps ifLetElseProg ∧
    trace Edition.e2021.rules ifLetElseProg ≠ trace Edition.e2024.rules ifLetElseProg := by decide

/-- R3-migration tightness: for `ifLetInTailProg` (an `if let` in a block's tail position, which
violates `NoTailEscapingTemps`), the `match`-rewritten program under the 2024 rules does not
reproduce the 2021 action list (nor the 2021 trace). -/
theorem ifLetInTailProg_toMatch_e2024_ne_e2021 :
    ¬ NoTailEscapingTemps ifLetInTailProg ∧
    run Edition.e2024.rules (toMatch ifLetInTailProg) ≠ run Edition.e2021.rules ifLetInTailProg ∧
    trace Edition.e2024.rules (toMatch ifLetInTailProg) = [.dtor 1, .dtor 0] ∧
    trace Edition.e2021.rules ifLetInTailProg = [.dtor 0, .dtor 1] := by decide

/-- Refutation of the reading "when tail temporaries' destructors emit no events, the `match`
rewrite under the 2024 rules reproduces the 2021 behaviour without `NoTailEscapingTemps`": for
`silentTailProg` the traces agree but the action lists differ; for `silentRefCellTailProg` the
traces agree but the toy borrow-check verdicts differ. -/
theorem refuted_emptyTailDtors_give_run_eq :
    ¬ NoTailEscapingTemps silentTailProg ∧
    trace Edition.e2024.rules (toMatch silentTailProg) = trace Edition.e2021.rules silentTailProg ∧
    run Edition.e2024.rules (toMatch silentTailProg) ≠ run Edition.e2021.rules silentTailProg ∧
    ¬ NoTailEscapingTemps silentRefCellTailProg ∧
    trace Edition.e2024.rules (toMatch silentRefCellTailProg) =
      trace Edition.e2021.rules silentRefCellTailProg ∧
    accepts Edition.e2024.rules (toMatch silentRefCellTailProg) = true ∧
    accepts Edition.e2021.rules silentRefCellTailProg = false := by decide

/-! ## R4: when migration preserves the trace -/

/-- R4-if. If every pair of actions executed in opposite orders under the 2021 and 2024 rules has
commuting event lists, the 2021 and 2024 event traces are equal. -/
theorem trace_e2021_eq_trace_e2024_of_flipped_commute (e : Expr)
    (h : ∀ a b, Flipped e a b → Commute a b) :
    trace Edition.e2021.rules e = trace Edition.e2024.rules e := by
  have ⟨hperm, hnd, _, _⟩ :=
    run_perm_nodup_and_dropTemps_perm_mkTemps_and_nonDropTemps_eq
      Edition.e2021.rules Edition.e2024.rules e
  exact flatMap_eq_of_perm_nodup_comm _ _ hperm hnd (fun a b h1 h2 => h a b ⟨h1, h2⟩)

/-- R4-if non-vacuity: in `commutingTailProg` some pair of actions is flipped and every flipped
pair commutes. -/
theorem commutingTailProg_flipped_and_all_commute :
    (∃ a b, Flipped commutingTailProg a b) ∧
    (∀ a b, Flipped commutingTailProg a b → Commute a b) := by
  have h21 : run Edition.e2021.rules commutingTailProg =
      [.mkLocal [0] 0, .mkTemp [0, 0, 1, 0] [], .dropLocal [0] 0 [.dtor 0],
       .dropTemp [0, 0, 1, 0] [] [.dtor 0]] := by decide
  have h24 : run Edition.e2024.rules commutingTailProg =
      [.mkLocal [0] 0, .mkTemp [0, 0, 1, 0] [], .dropTemp [0, 0, 1, 0] [] [.dtor 0],
       .dropLocal [0] 0 [.dtor 0]] := by decide
  refine ⟨⟨.dropLocal [0] 0 [.dtor 0], .dropTemp [0, 0, 1, 0] [] [.dtor 0],
    ⟨2, 3, by decide, by simp [h21], by simp [h21]⟩,
    ⟨2, 3, by decide, by simp [h24], by simp [h24]⟩⟩, ?_⟩
  have hall : ∀ a ∈ run Edition.e2021.rules commutingTailProg,
      ∀ b ∈ run Edition.e2021.rules commutingTailProg, Commute a b := by
    rw [h21]; decide
  rintro a b ⟨⟨i, j, _, hi, hj⟩, _⟩
  exact hall a (List.mem_of_getElem? hi) b (List.mem_of_getElem? hj)

/-- R4-if tightness: in `tailProg` a flipped pair does not commute and the traces differ. -/
theorem tailProg_flipped_not_commute_and_traces_differ :
    Flipped tailProg tailProgLocalDrop tailProgTempDrop ∧
    ¬ Commute tailProgLocalDrop tailProgTempDrop ∧
    trace Edition.e2021.rules tailProg ≠ trace Edition.e2024.rules tailProg :=
  ⟨flipped_tailProg, not_commute_tailProg, by decide⟩

/-- R4-if and R4-site boundary: equal traces do not give equal toy borrow-check verdicts. In
`refCellTailProg` every flipped pair commutes and the 2021 and 2024 traces are equal, yet the
verdicts of `accepts` differ. -/
theorem refCellTailProg_flipped_commute_and_trace_eq_and_accepts_ne :
    (∀ a b, Flipped refCellTailProg a b → Commute a b) ∧
    trace Edition.e2021.rules refCellTailProg = trace Edition.e2024.rules refCellTailProg ∧
    accepts Edition.e2021.rules refCellTailProg ≠ accepts Edition.e2024.rules refCellTailProg := by
  have hall : ∀ a ∈ run Edition.e2021.rules refCellTailProg,
      ∀ b ∈ run Edition.e2021.rules refCellTailProg, Commute a b := by decide
  refine ⟨?_, by decide, by decide⟩
  rintro a b ⟨⟨i, j, _, hi, hj⟩, _⟩
  exact hall a (List.mem_of_getElem? hi) b (List.mem_of_getElem? hj)

/-- R4-tail-site. For one tail site (`tailSiteProg ls ds`), the 2021 and 2024 traces are equal iff
the locals' destructor events (in drop order) commute, as one word, with the tail temporaries'
destructor events (in drop order). -/
theorem tailSiteProg_trace_eq_iff_commute (ls ds : List (List Ev)) :
    trace Edition.e2021.rules (tailSiteProg ls ds) = trace Edition.e2024.rules (tailSiteProg ls ds) ↔
      dropOrderEvents ls ++ dropOrderEvents ds = dropOrderEvents ds ++ dropOrderEvents ls := by
  unfold trace run tailSiteProg Edition.rules eval closeScope
  rcases evalBlock_letsFrom ⟨false, false⟩ ls 0 (.tail (tempsSeq ds)) [0] with ⟨h21a, h21b⟩
  rcases evalBlock_letsFrom ⟨true, true⟩ ls 0 (.tail (tempsSeq ds)) [0] with ⟨h24a, h24b⟩
  rcases eval_tempsSeq ⟨false, false⟩ ds (0 :: (List.replicate ls.length 1 ++ [0])) with
    ⟨ht21a, ht21b⟩
  rcases eval_tempsSeq ⟨true, true⟩ ds (0 :: (List.replicate ls.length 1 ++ [0])) with
    ⟨ht24a, ht24b⟩
  simp only [List.flatMap_append, h21a, h21b, h24a, h24b, evalBlock, Bool.false_eq_true,
    ↓reduceIte, closeScope, dropAll_events, ht21a, ht21b, ht24a, ht24b, List.nil_append,
    List.map_nil, List.reverse_nil, List.flatten_nil, List.append_nil, dropOrderEvents]

/-- R4-else-site. For one `if let` else site (`elseSiteProg ds es`), the 2021 and 2024 traces are
equal iff the `else` block's events commute, as one word, with the scrutinee temporaries'
destructor events (in drop order). -/
theorem elseSiteProg_trace_eq_iff_commute (ds : List (List Ev)) (es : List Nat) :
    trace Edition.e2021.rules (elseSiteProg ds es) = trace Edition.e2024.rules (elseSiteProg ds es) ↔
      es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out := by
  unfold trace run elseSiteProg Edition.rules eval closeScope
  rcases eval_tempsSeq ⟨false, false⟩ ds [0] with ⟨ht21a, ht21b⟩
  rcases eval_tempsSeq ⟨true, true⟩ ds [0] with ⟨ht24a, ht24b⟩
  rcases eval_outsSeq ⟨false, false⟩ es [2] with ⟨he21a, he21b⟩
  rcases eval_outsSeq ⟨true, true⟩ es [2] with ⟨he24a, he24b⟩
  simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_append, ht21a, ht24a,
    he21a, he21b, he24a, he24b, dropAll_events, ht21b, ht24b, List.nil_append, List.append_nil,
    List.map_nil, List.reverse_nil, List.flatten_nil, dropOrderEvents]

/-- R4-else-site specialized to destructors that emit `dtor` events only: then the commutation
condition holds iff the `else` block emits nothing or the scrutinee temporaries' destructors emit
nothing. -/
theorem elseSite_commute_iff_of_dtorOnly (ds : List (List Ev)) (es : List Nat)
    (hd : ∀ ev ∈ dropOrderEvents ds, ∃ n, ev = .dtor n) :
    es.map Ev.out ++ dropOrderEvents ds = dropOrderEvents ds ++ es.map Ev.out ↔
      es = [] ∨ dropOrderEvents ds = [] := by
  constructor
  · intro h
    cases es with
    | nil => exact Or.inl rfl
    | cons n ns =>
      right
      cases hD : dropOrderEvents ds with
      | nil => rfl
      | cons ev evs =>
        exfalso
        rw [hD] at h hd
        obtain ⟨m, hm⟩ := hd ev (List.mem_cons_self ..)
        simp only [List.map_cons, List.cons_append] at h
        have hhead := (List.cons.inj h).1
        rw [hm] at hhead
        exact absurd hhead (by simp)
  · rintro (h | h) <;> simp [h]

/-- Non-vacuity of `elseSite_commute_iff_of_dtorOnly`: a scrutinee temporary whose destructor emits
`dtor 0` satisfies its hypothesis. -/
theorem elseSite_dtorOnly_hypothesis_holds :
    ∀ ev ∈ dropOrderEvents [[.dtor 0]], ∃ n, ev = .dtor n := by
  intro ev hev
  simp [dropOrderEvents] at hev
  exact ⟨0, hev⟩

/-- Tightness of the hypothesis of `elseSite_commute_iff_of_dtorOnly`: with a destructor that emits
`out 1` the hypothesis fails and the equivalence fails (both sides of the commutation are non-empty
and commute). -/
theorem elseSite_commute_iff_of_dtorOnly_hypothesis_tight :
    ¬ (∀ ev ∈ dropOrderEvents [[.out 1]], ∃ n, ev = .dtor n) ∧
    ¬ ([1].map Ev.out ++ dropOrderEvents [[.out 1]] = dropOrderEvents [[.out 1]] ++ [1].map Ev.out ↔
        [1] = [] ∨ dropOrderEvents [[.out 1]] = []) := by
  refine ⟨fun h => ?_, by decide⟩
  obtain ⟨n, hn⟩ := h (.out 1) (by decide)
  exact Ev.noConfusion hn

/-- R4-site non-vacuity: instances of both sides of the two site characterizations, including an
`else` site whose scrutinee temporary's destructor emits an `out` event that commutes with the
`else` block's output. -/
theorem site_examples :
    trace Edition.e2021.rules commutingTailProg = trace Edition.e2024.rules commutingTailProg ∧
    trace Edition.e2021.rules (tailSiteProg [[.dtor 0]] [[.dtor 1]]) ≠
      trace Edition.e2024.rules (tailSiteProg [[.dtor 0]] [[.dtor 1]]) ∧
    trace Edition.e2021.rules (elseSiteProg [[]] [1]) = trace Edition.e2024.rules (elseSiteProg [[]] [1]) ∧
    trace Edition.e2021.rules (elseSiteProg [[.dtor 0]] [1]) ≠
      trace Edition.e2024.rules (elseSiteProg [[.dtor 0]] [1]) ∧
    trace Edition.e2021.rules (elseSiteProg [[.out 1]] [1]) = [.out 1, .out 1] ∧
    trace Edition.e2024.rules (elseSiteProg [[.out 1]] [1]) = [.out 1, .out 1] := by decide

/-- The second-created tail temporary of `ababProg` (its destructor emits `dtor 0`). -/
def ababTempDrop : Act := .dropTemp [0, 1, 0, 1, 1, 0] [] [.dtor 0]
/-- The first-declared local of `ababProg` (its destructor emits `dtor 1`). -/
def ababLocalDrop : Act := .dropLocal [0] 0 [.dtor 1]

/-- R4-not-necessary. Per-action commutation is not necessary for trace preservation: `ababProg`
has equal 2021 and 2024 traces, yet the tail temporary `ababTempDrop` is executed in opposite
orders relative to the local drop `ababLocalDrop` under the two editions and their event lists do
not commute. -/
theorem ababProg_trace_eq_and_flipped_not_commute :
    trace Edition.e2021.rules ababProg = trace Edition.e2024.rules ababProg ∧
    Flipped ababProg ababLocalDrop ababTempDrop ∧ ¬ Commute ababLocalDrop ababTempDrop := by
  have h21 : run Edition.e2021.rules ababProg =
      [.mkLocal [0] 0, .mkLocal [1, 0] 1, .mkTemp [0, 0, 1, 1, 0] [], .mkTemp [0, 1, 0, 1, 1, 0] [],
       .dropLocal [1, 0] 1 [.dtor 0], ababLocalDrop, ababTempDrop,
       .dropTemp [0, 0, 1, 1, 0] [] [.dtor 1]] := by decide
  have h24 : run Edition.e2024.rules ababProg =
      [.mkLocal [0] 0, .mkLocal [1, 0] 1, .mkTemp [0, 0, 1, 1, 0] [], .mkTemp [0, 1, 0, 1, 1, 0] [],
       ababTempDrop, .dropTemp [0, 0, 1, 1, 0] [] [.dtor 1],
       .dropLocal [1, 0] 1 [.dtor 0], ababLocalDrop] := by decide
  refine ⟨by decide, ⟨⟨5, 6, by decide, by simp [h21], by simp [h21]⟩,
    ⟨4, 7, by decide, by simp [h24], by simp [h24]⟩⟩, by decide⟩

/-- R4-window counterexample (nested tails). In `nestedTailProg` the tail temporary's owning
block has no locals, yet the 2021 and 2024 traces differ: under 2021 the temporary is also
dropped after the outer block's local. -/
theorem nestedTailProg_traces_differ :
    trace Edition.e2021.rules nestedTailProg = [.dtor 1, .dtor 0] ∧
    trace Edition.e2024.rules nestedTailProg = [.dtor 0, .dtor 1] := by decide

/-- R4-window counterexample (then branch). In `thenBranchProg` no `else` block runs, yet the 2021
and 2024 traces differ: under 2021 the scrutinee temporary is dropped after the output that follows
the `if let` in the same expression. -/
theorem thenBranchProg_traces_differ :
    trace Edition.e2021.rules thenBranchProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules thenBranchProg = [.dtor 0, .out 1] := by decide

/-- R4-window counterexample (sibling subexpression). In `siblingTailProg` no block declares a
local, yet the 2021 and 2024 traces differ: under 2021 the tail temporary of the block is dropped
after the output that follows the block in the same expression. -/
theorem siblingTailProg_traces_differ :
    trace Edition.e2021.rules siblingTailProg = [.out 1, .dtor 0] ∧
    trace Edition.e2024.rules siblingTailProg = [.dtor 0, .out 1] := by decide

/-- `Commute` is word equality: two actions whose event lists are distinct and non-empty can
commute, here `[dtor 0]` and `[dtor 0, dtor 0]` (both powers of the word `[dtor 0]`). -/
theorem commute_distinct_nonempty_event_lists :
    (Act.dropLocal [] 0 [.dtor 0]).events ≠ [] ∧
    (Act.dropTemp [1] [] [.dtor 0, .dtor 0]).events ≠ [] ∧
    (Act.dropLocal [] 0 [.dtor 0]).events ≠ (Act.dropTemp [1] [] [.dtor 0, .dtor 0]).events ∧
    Commute (.dropLocal [] 0 [.dtor 0]) (.dropTemp [1] [] [.dtor 0, .dtor 0]) := by decide

end Toy.DropScope
