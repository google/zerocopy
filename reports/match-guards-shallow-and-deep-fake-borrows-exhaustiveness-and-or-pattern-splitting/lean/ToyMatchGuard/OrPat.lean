/-
Or-patterns with guards: splitting into sub-branches, guard re-evaluation and binding drop
order.

These are definitions of a toy model. `runSrc` is meant to capture the documented source-level
behaviour of a `match` whose arms may contain (nested) or-patterns: alternatives are tried in
left-to-right order, and a guard is evaluated once for every alternative that matches, with that
alternative's bindings. `runSplit` is meant to capture a lowering that expands each arm into
or-free sub-branches with their own bindings and their own copy of the guard. Drop order of the
bindings after the arm body is a parameter (`DropPolicy`). These are not Rust's definitions.
-/

namespace Toy.MatchGuard.OrPat

/-- Values: integers, pairs, and the two variants of a two-variant enum (`Ok`/`Err`-like). -/
inductive PV where
  | int (n : Int)
  | pair (a b : PV)
  | inl (a : PV)
  | inr (a : PV)
  deriving DecidableEq, Repr

/-- Patterns: wildcard, binding (by name), integer literal, pair, the two variants, and
or-patterns (`or p q` is `p | q`), which may nest anywhere. -/
inductive Pat where
  | wild
  | bind (x : Nat)
  | int (n : Int)
  | pair (p q : Pat)
  | inl (p : Pat)
  | inr (p : Pat)
  | or (p q : Pat)
  deriving DecidableEq, Repr

/-- Binding environments, in declaration (left-to-right) order of the alternative that matched. -/
abbrev Env := List (Nat × PV)

/-- All the ways a pattern matches a value, in left-to-right alternative order. -/
def matchAll : Pat → PV → List Env
  | .wild, _ => [[]]
  | .bind x, v => [[(x, v)]]
  | .int n, v => match v with
    | .int m => if n = m then [[]] else []
    | _ => []
  | .pair p q, v => match v with
    | .pair a b => (matchAll p a).flatMap (fun e1 => (matchAll q b).map (fun e2 => e1 ++ e2))
    | _ => []
  | .inl p, v => match v with
    | .inl a => matchAll p a
    | _ => []
  | .inr p, v => match v with
    | .inr a => matchAll p a
    | _ => []
  | .or p q, v => matchAll p v ++ matchAll q v

/-- Whether a pattern contains no or-pattern. -/
def OrFree : Pat → Prop
  | .wild | .bind _ | .int _ => True
  | .pair p q => OrFree p ∧ OrFree q
  | .inl p | .inr p => OrFree p
  | .or _ _ => False

/-- Or-pattern expansion: the or-free alternatives of a pattern, in left-to-right order (nested
alternatives are expanded lexicographically). -/
def expand : Pat → List Pat
  | .wild => [.wild]
  | .bind x => [.bind x]
  | .int n => [.int n]
  | .pair p q => (expand p).flatMap (fun p' => (expand q).map (fun q' => .pair p' q'))
  | .inl p => (expand p).map .inl
  | .inr p => (expand p).map .inr
  | .or p q => expand p ++ expand q

/-- Declaration order of a pattern's bindings. For an or-pattern it is the order of its first
alternative. -/
def declOrder : Pat → List Nat
  | .wild | .int _ => []
  | .bind x => [x]
  | .pair p q => declOrder p ++ declOrder q
  | .inl p | .inr p => declOrder p
  | .or p _ => declOrder p

/-- Observable events. `guard i e`: one evaluation of the guard of arm `i`, with bindings `e`;
`body i e`: the body of arm `i` runs with bindings `e`; `drop v`: a binding's destructor runs
on `v`; `unreachable`: no arm matched. -/
inductive Ev where
  | guard (arm : Nat) (env : Env)
  | body (arm : Nat) (env : Env)
  | drop (v : PV)
  | unreachable
  deriving DecidableEq, Repr

/-- Binding drop order after the arm body.
* `firstAlternative`: reverse declaration order of the arm pattern's first alternative,
  whichever alternative matched.
* `matchedAlternative`: reverse declaration order of the alternative that matched. -/
inductive DropPolicy where
  | firstAlternative
  | matchedAlternative
  deriving DecidableEq, Repr

/-- Drops in reverse order of the names `order`, reading each value from `e`. -/
def dropsInOrder (order : List Nat) (e : Env) : List Ev :=
  ((order.filterMap (fun x => e.lookup x)).reverse).map Ev.drop

/-- Drops in reverse order of the environment's own entries. -/
def dropsMatched (e : Env) : List Ev := ((e.map Prod.snd).reverse).map Ev.drop

/-- The drops of an arm with pattern `P` after its body ran with bindings `e`. -/
def armDrops : DropPolicy → Pat → Env → List Ev
  | .firstAlternative, P, e => dropsInOrder (declOrder P) e
  | .matchedAlternative, _, e => dropsMatched e

/-- A source arm: a pattern (possibly with or-patterns) and an optional guard reading bindings. -/
structure SArm where
  pat : Pat
  guard : Option (Env → Bool) := none

/-- Tries the binding environments of one arm in order. -/
def tryEnvs (drops : Env → List Ev) (i : Nat) (g : Option (Env → Bool)) (rest : List Ev) :
    List Env → List Ev
  | [] => rest
  | e :: es =>
    match g with
    | none => .body i e :: drops e
    | some g => .guard i e :: (if g e then .body i e :: drops e else tryEnvs drops i g rest es)

/-- Source semantics: arms in order; within an arm, every way its pattern matches, in
left-to-right order, with the guard evaluated for each. -/
def runSrc (pol : DropPolicy) (v : PV) : Nat → List SArm → List Ev
  | _, [] => [.unreachable]
  | i, a :: as => tryEnvs (armDrops pol a.pat) i a.guard (runSrc pol v (i + 1) as) (matchAll a.pat v)

/-- A sub-branch: an or-free pattern, the guard of its arm, the arm index, and its drop order
(`some order`: fixed names; `none`: the sub-branch's own bindings). -/
structure SubBranch where
  pat : Pat
  guard : Option (Env → Bool)
  arm : Nat
  order : Option (List Nat)

/-- The drops of a sub-branch. -/
def SubBranch.drops (sb : SubBranch) (e : Env) : List Ev :=
  match sb.order with
  | some order => dropsInOrder order e
  | none => dropsMatched e

/-- Splitting one arm into sub-branches, one per or-free alternative, each with its own copy of
the guard; the drop order follows the policy. -/
def splitArm (pol : DropPolicy) (i : Nat) (a : SArm) : List SubBranch :=
  (expand a.pat).map (fun p' =>
    { pat := p', guard := a.guard, arm := i,
      order := match pol with
        | .firstAlternative => some (declOrder a.pat)
        | .matchedAlternative => none })

/-- Splitting all arms. -/
def splitArms (pol : DropPolicy) : Nat → List SArm → List SubBranch
  | _, [] => []
  | i, a :: as => splitArm pol i a ++ splitArms pol (i + 1) as

/-- The split lowering: sub-branches tried in order; each is matched on its own (an or-free
pattern matches in at most one way) and, if it has a guard, evaluates its own copy of it. -/
def runSplit (v : PV) : List SubBranch → List Ev
  | [] => [.unreachable]
  | sb :: sbs =>
    match (matchAll sb.pat v).head? with
    | none => runSplit v sbs
    | some e =>
      match sb.guard with
      | none => .body sb.arm e :: sb.drops e
      | some g => .guard sb.arm e :: (if g e then .body sb.arm e :: sb.drops e else runSplit v sbs)

/-- A lowering that evaluates an arm's guard at most once: with the bindings of the first
alternative that matches, reusing the result for the later alternatives of that arm. -/
def runGuardOnce (pol : DropPolicy) (v : PV) : Nat → List SArm → List Ev
  | _, [] => [.unreachable]
  | i, a :: as =>
    match matchAll a.pat v with
    | [] => runGuardOnce pol v (i + 1) as
    | e :: _ =>
      match a.guard with
      | none => .body i e :: armDrops pol a.pat e
      | some g =>
        .guard i e :: (if g e then .body i e :: armDrops pol a.pat e
          else runGuardOnce pol v (i + 1) as)

/-- Every alternative of the pattern declares its bindings in the same order as the first
alternative (in particular, every alternative binds the same names). -/
def SameDeclOrder (P : Pat) : Prop :=
  ∀ p' ∈ expand P, declOrder p' = declOrder P

/-- No alternative of the pattern binds a name twice. -/
def NoDupBindings (P : Pat) : Prop :=
  ∀ p' ∈ expand P, (declOrder p').Nodup

instance (P : Pat) : Decidable (SameDeclOrder P) := by unfold SameDeclOrder; infer_instance
instance (P : Pat) : Decidable (NoDupBindings P) := by unfold NoDupBindings; infer_instance

/-! ### Lemmas -/

theorem orFree_length_le_one : ∀ (p : Pat) (v : PV), OrFree p → (matchAll p v).length ≤ 1
  | .wild, _, _ => by simp [matchAll]
  | .bind _, _, _ => by simp [matchAll]
  | .int n, v, _ => by cases v <;> simp [matchAll]; split <;> simp
  | .pair p q, v, h => by
    cases v with
    | pair a b =>
      simp only [matchAll]
      have h1 := orFree_length_le_one p a h.1
      have h2 := orFree_length_le_one q b h.2
      match hp : matchAll p a, hq : matchAll q b with
      | [], _ => simp
      | [_], [] => simp
      | [_], [_] => simp
      | _ :: _ :: _, _ => rw [hp] at h1; simp at h1
      | [_], _ :: _ :: _ => rw [hq] at h2; simp at h2
    | _ => simp [matchAll]
  | .inl p, v, h => by
    cases v with
    | inl a => simpa [matchAll] using orFree_length_le_one p a h
    | _ => simp [matchAll]
  | .inr p, v, h => by
    cases v with
    | inr a => simpa [matchAll] using orFree_length_le_one p a h
    | _ => simp [matchAll]
  | .or _ _, _, h => h.elim

theorem orFree_of_mem_expand : ∀ (P p' : Pat), p' ∈ expand P → OrFree p'
  | .wild, _, h => by simp [expand] at h; subst h; trivial
  | .bind _, _, h => by simp [expand] at h; subst h; trivial
  | .int _, _, h => by simp [expand] at h; subst h; trivial
  | .pair p q, _, h => by
    simp only [expand, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact ⟨orFree_of_mem_expand p a ha, orFree_of_mem_expand q b hb⟩
  | .inl p, _, h => by
    simp only [expand, List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact orFree_of_mem_expand p a ha
  | .inr p, _, h => by
    simp only [expand, List.mem_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact orFree_of_mem_expand p a ha
  | .or p q, p', h => by
    simp only [expand, List.mem_append] at h
    rcases h with h | h
    · exact orFree_of_mem_expand p p' h
    · exact orFree_of_mem_expand q p' h

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem flatMap_comm_of_length_le_one {α β γ : Type} (l : List α) (m : List β)
    (f : α → β → List γ) (h : l.length ≤ 1) :
    l.flatMap (fun x => m.flatMap (fun y => f x y)) =
      m.flatMap (fun y => l.flatMap (fun x => f x y)) := by
  match l, h with
  | [], _ => simp
  | [x], _ => simp
  | _ :: _ :: _, h => simp at h

theorem matchAll_eq_flatMap_expand_aux : ∀ (P : Pat) (v : PV),
    matchAll P v = (expand P).flatMap (fun p' => matchAll p' v)
  | .wild, _ => by simp [expand]
  | .bind _, _ => by simp [expand]
  | .int _, _ => by simp [expand]
  | .pair p q, v => by
    cases v with
    | pair a b =>
      simp only [matchAll, expand]
      rw [matchAll_eq_flatMap_expand_aux p a, matchAll_eq_flatMap_expand_aux q b]
      simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap]
      apply flatMap_congr_mem
      intro p' hp'
      exact flatMap_comm_of_length_le_one _ _ _
        (orFree_length_le_one p' a (orFree_of_mem_expand p p' hp'))
    | _ => simp [matchAll, expand]; intro x x1 _ x2 _ h; subst h; rfl
  | .inl p, v => by
    cases v with
    | inl a =>
      simp only [matchAll, expand, List.flatMap_map]
      exact matchAll_eq_flatMap_expand_aux p a
    | _ => simp [matchAll, expand, List.flatMap_map]
  | .inr p, v => by
    cases v with
    | inr a =>
      simp only [matchAll, expand, List.flatMap_map]
      exact matchAll_eq_flatMap_expand_aux p a
    | _ => simp [matchAll, expand, List.flatMap_map]
  | .or p q, v => by
    simp only [matchAll, expand, List.flatMap_append]
    rw [matchAll_eq_flatMap_expand_aux p v, matchAll_eq_flatMap_expand_aux q v]

/-- Or-pattern matching enumerates the matches of the expanded alternatives, in order: for every
pattern `P` and value `v`, `matchAll P v` is the concatenation, over the alternatives of
`expand P` in order, of their matches. -/
theorem matchAll_eq_flatMap_expand (P : Pat) (v : PV) :
    matchAll P v = (expand P).flatMap (fun p' => matchAll p' v) :=
  matchAll_eq_flatMap_expand_aux P v

theorem runSplit_map_append (v : PV) (drops : Env → List Ev) (i : Nat) (g : Option (Env → Bool))
    (mk : Pat → SubBranch) (hmk : ∀ p', (mk p').guard = g ∧ (mk p').arm = i ∧ (mk p').pat = p')
    (hdrops : ∀ p' e, (mk p').drops e = drops e) (R : List SubBranch) :
    ∀ (L : List Pat), (∀ p' ∈ L, OrFree p') →
      runSplit v (L.map mk ++ R) = tryEnvs drops i g (runSplit v R) (L.flatMap (fun p' => matchAll p' v))
  | [], _ => by simp [tryEnvs]
  | p' :: L, hL => by
    have hlen := orFree_length_le_one p' v (hL p' (by simp))
    have ih := runSplit_map_append v drops i g mk hmk hdrops R L (fun x hx => hL x (by simp [hx]))
    obtain ⟨hg, ha, hp⟩ := hmk p'
    simp only [List.map_cons, List.cons_append, List.flatMap_cons]
    match hm : matchAll p' v, hlen with
    | [], _ =>
      simp only [runSplit, hp, hm, List.head?_nil, List.nil_append]
      exact ih
    | [e], _ =>
      simp only [runSplit, hp, hm, List.head?_cons, List.cons_append, List.nil_append, hg, ha]
      cases g with
      | none => simp [tryEnvs, hdrops]
      | some g =>
        simp only [tryEnvs, hdrops]
        split
        · rfl
        · rw [ih]
    | _ :: _ :: _, h => simp at h

/-! ### Results -/

/-- **Or-pattern splitting (trace equivalence).** For every drop policy `pol`, every value `v`,
every list of arms `arms` (patterns may contain nested or-patterns; guards may read bindings) and
every starting arm index `i`, the source semantics `runSrc pol v i arms`, which re-evaluates an
arm's guard for each matching alternative with that alternative's bindings, produces the same
event trace as the split lowering `runSplit v (splitArms pol i arms)`. -/
theorem runSrc_eq_runSplit_splitArms (pol : DropPolicy) (v : PV) :
    ∀ (arms : List SArm) (i : Nat), runSrc pol v i arms = runSplit v (splitArms pol i arms) := by
  intro arms
  induction arms with
  | nil => intro i; rfl
  | cons a as ih =>
    intro i
    simp only [runSrc, splitArms, splitArm]
    rw [matchAll_eq_flatMap_expand a.pat v, ih (i + 1)]
    symm
    apply runSplit_map_append v (armDrops pol a.pat) i a.guard
    · intro p'; exact ⟨rfl, rfl, rfl⟩
    · intro p' e
      cases pol <;> rfl
    · exact fun p' hp' => orFree_of_mem_expand a.pat p' hp'

theorem keys_of_mem_matchAll_orFree : ∀ (p : Pat) (v : PV) (e : Env), OrFree p →
    e ∈ matchAll p v → e.map Prod.fst = declOrder p
  | .wild, _, e, _, h => by simp [matchAll] at h; subst h; rfl
  | .bind x, v, e, _, h => by simp [matchAll] at h; subst h; rfl
  | .int n, v, e, _, h => by
    cases v <;> simp [matchAll] at h
    obtain ⟨_, rfl⟩ := h; rfl
  | .pair p q, v, e, hf, h => by
    cases v with
    | pair a b =>
      simp only [matchAll, List.mem_flatMap, List.mem_map] at h
      obtain ⟨e1, h1, e2, h2, rfl⟩ := h
      simp [declOrder, keys_of_mem_matchAll_orFree p a e1 hf.1 h1,
        keys_of_mem_matchAll_orFree q b e2 hf.2 h2]
    | _ => simp [matchAll] at h
  | .inl p, v, e, hf, h => by
    cases v with
    | inl a => simp only [matchAll] at h; exact keys_of_mem_matchAll_orFree p a e hf h
    | _ => simp [matchAll] at h
  | .inr p, v, e, hf, h => by
    cases v with
    | inr a => simp only [matchAll] at h; exact keys_of_mem_matchAll_orFree p a e hf h
    | _ => simp [matchAll] at h
  | .or _ _, _, _, hf, _ => hf.elim

theorem filterMap_congr_mem {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem filterMap_lookup_keys : ∀ (e : Env), (e.map Prod.fst).Nodup →
    (e.map Prod.fst).filterMap (fun x => e.lookup x) = e.map Prod.snd
  | [], _ => rfl
  | (x, w) :: e, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    simp only [List.map_cons, List.filterMap_cons, List.lookup_cons, beq_self_eq_true]
    simp only [List.cons.injEq, true_and]
    rw [← filterMap_lookup_keys e hnd]
    apply filterMap_congr_mem
    intro y hy
    have : (y == x) = false := by
      simp only [beq_eq_false_iff_ne]; intro hyx; subst hyx; exact hx hy
    simp [this]

/-- **Drop policies agree when alternatives bind distinct names in the same order.** For every
value `v`, arm list `arms` and arm index `i` such that no alternative of any arm's pattern binds a
name twice (`NoDupBindings`) and every alternative of every arm's pattern declares its bindings in
the order of that pattern's first alternative (`SameDeclOrder`), the source traces under the
`firstAlternative` and `matchedAlternative` drop policies are equal. -/
theorem runSrc_firstAlternative_eq_matchedAlternative_of_noDupBindings_of_sameDeclOrder (v : PV) :
    ∀ (arms : List SArm) (i : Nat), (∀ a ∈ arms, NoDupBindings a.pat) →
      (∀ a ∈ arms, SameDeclOrder a.pat) →
      runSrc .firstAlternative v i arms = runSrc .matchedAlternative v i arms := by
  intro arms
  induction arms with
  | nil => intro i _ _; rfl
  | cons a as ih =>
    intro i hn h
    simp only [runSrc]
    rw [ih (i + 1) (fun a' ha' => hn a' (by simp [ha'])) (fun a' ha' => h a' (by simp [ha']))]
    have hd : ∀ e ∈ matchAll a.pat v, armDrops .firstAlternative a.pat e =
        armDrops .matchedAlternative a.pat e := by
      intro e he
      rw [matchAll_eq_flatMap_expand, List.mem_flatMap] at he
      obtain ⟨p', hp', he'⟩ := he
      have hk := keys_of_mem_matchAll_orFree p' v e (orFree_of_mem_expand _ _ hp') he'
      have hord := h a (by simp) p' hp'
      have hnd := hn a (by simp) p' hp'
      simp only [armDrops, dropsInOrder, dropsMatched]
      rw [← hord, ← hk, filterMap_lookup_keys e (hk ▸ hnd)]
    generalize matchAll a.pat v = envs at hd
    generalize a.guard = g0
    induction envs with
    | nil => rfl
    | cons e es ihe =>
      cases g0 with
      | none => simp [tryEnvs, hd e (by simp)]
      | some g =>
        simp only [tryEnvs]
        rw [hd e (by simp), ihe (fun e' he' => hd e' (by simp [he']))]

/-! ### Instances -/

/-- `(x, _) | (_, x) if x == 2 => .., _ => ..` with `x` named `0`: the guard reads the binding. -/
def bindingGuardArms : List SArm :=
  [ { pat := .or (.pair (.bind 0) .wild) (.pair .wild (.bind 0)),
      guard := some (fun e => decide (e.lookup 0 = some (.int 2))) },
    { pat := .wild } ]

/-- Toy form of the Reference's `1 | _ if { i.set(i.get() + 1); false } => {}, _ => {}`: a guard
that ignores bindings and is false; each evaluation is an observable event. -/
def constGuardArms : List SArm :=
  [ { pat := .or (.int 1) .wild, guard := some (fun _ => false) },
    { pat := .wild } ]

/-- Toy form of the Reference's `Ok([x, y]) | Err([y, x])` with `x` named `0`, `y` named `1`. -/
def refDropArms : List SArm :=
  [ { pat := .or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0))) } ]

/-- `(x, y) | (y, x) => ..` with `x` named `0`, `y` named `1`, unguarded: the first alternative
matches every pair, so the second (order-reversing) alternative is never used. -/
def shadowedSwapArms : List SArm :=
  [ { pat := .or (.pair (.bind 0) (.bind 1)) (.pair (.bind 1) (.bind 0)) } ]

/-- `Ok(x) | Err(x) if x == 2 => .., _ => ..` with `x` named `0`: mutually exclusive alternatives
with a guard that reads the binding. -/
def okErrGuardArms : List SArm :=
  [ { pat := .or (.inl (.bind 0)) (.inr (.bind 0)),
      guard := some (fun e => decide (e.lookup 0 = some (.int 2))) },
    { pat := .wild } ]

/-- The or-free pattern `(x, x)` (both named `0`), which Rust rejects (a name bound twice). -/
def dupBindArms : List SArm := [ { pat := .pair (.bind 0) (.bind 0) } ]

/-- `Ok(_) | Err(x) => ..` with `x` named `0`, which Rust rejects (the alternatives bind different
names). -/
def unbalancedOrArms : List SArm := [ { pat := .or (.inl .wild) (.inr (.bind 0)) } ]

/-- **Counterexample (guard evaluated once).** For every drop policy `pol`: on `(1, 2)`, for
`bindingGuardArms` (whose guard reads its binding), the source semantics evaluates the guard with
`x = 1`, then with `x = 2`, and runs the body of arm `0` with `x = 2`, while the guard-once
lowering evaluates the guard once (with `x = 1`) and runs the body of arm `1`; and on `1`, for
`constGuardArms` (whose guard returns `false` for every binding environment), the source
semantics evaluates the guard twice and the guard-once lowering once, both then running the body
of arm `1`. In both cases the traces differ. -/
theorem runGuardOnce_ne_runSrc_bindingGuardArms_constGuardArms (pol : DropPolicy) :
    runSrc pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms =
        [.guard 0 [(0, .int 1)], .guard 0 [(0, .int 2)], .body 0 [(0, .int 2)], .drop (.int 2)] ∧
      runGuardOnce pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms =
        [.guard 0 [(0, .int 1)], .body 1 []] ∧
      runGuardOnce pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms ≠
        runSrc pol (.pair (.int 1) (.int 2)) 0 bindingGuardArms ∧
      (∃ g, constGuardArms[0].guard = some g ∧ ∀ e, g e = false) ∧
      runSrc pol (.int 1) 0 constGuardArms = [.guard 0 [], .guard 0 [], .body 1 []] ∧
      runGuardOnce pol (.int 1) 0 constGuardArms = [.guard 0 [], .body 1 []] ∧
      runGuardOnce pol (.int 1) 0 constGuardArms ≠ runSrc pol (.int 1) 0 constGuardArms := by
  refine ⟨?_, ?_, ?_, ⟨fun _ => false, rfl, fun _ => rfl⟩, ?_, ?_, ?_⟩ <;> cases pol <;> decide

/-- **Positive control (at most one matching alternative).** For every drop policy `pol`, value
`v`, arm list `arms` and arm index `i` such that every arm's pattern matches `v` in at most one
way, the guard-once lowering produces the same trace as the source semantics. -/
theorem runGuardOnce_eq_runSrc_of_matchAll_length_le_one (pol : DropPolicy) (v : PV) :
    ∀ (arms : List SArm) (i : Nat), (∀ a ∈ arms, (matchAll a.pat v).length ≤ 1) →
      runGuardOnce pol v i arms = runSrc pol v i arms := by
  intro arms
  induction arms with
  | nil => intro i _; rfl
  | cons a as ih =>
    intro i h
    have hrest := ih (i + 1) (fun a' ha' => h a' (by simp [ha']))
    have hlen := h a (by simp)
    simp only [runGuardOnce, runSrc]
    match hm : matchAll a.pat v, hlen with
    | [], _ => simp only [tryEnvs]; exact hrest
    | [e], _ =>
      cases a.guard with
      | none => rfl
      | some g =>
        simp only [tryEnvs]
        split
        · rfl
        · rw [hrest]
    | _ :: _ :: _, h2 => simp at h2

/-- `okErrGuardArms` matches every value in at most one way per arm, so the positive control
`runGuardOnce_eq_runSrc_of_matchAll_length_le_one` applies to it on every value. -/
theorem okErrGuardArms_matchAll_length_le_one :
    ∀ v, ∀ a ∈ okErrGuardArms, (matchAll a.pat v).length ≤ 1 := by
  intro v a ha
  unfold okErrGuardArms at ha
  simp at ha
  rcases ha with rfl | rfl
  · cases v <;> simp [matchAll]
  · simp [matchAll]

/-- **Counterexample (order hypothesis of the drop-policy theorem).** `refDropArms` has no
alternative binding a name twice, its pattern's second alternative declares its bindings in the
opposite order (`SameDeclOrder` fails), and on `Err((10, 20))` (so `y = 10`, `x = 20`) the
`firstAlternative` policy drops `10` then `20` while the `matchedAlternative` policy drops `20`
then `10`. -/
theorem refDropArms_noDupBindings_not_sameDeclOrder_and_policies_differ :
    (∀ a ∈ refDropArms, NoDupBindings a.pat) ∧ ¬ (∀ a ∈ refDropArms, SameDeclOrder a.pat) ∧
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms =
        [.body 0 [(1, .int 10), (0, .int 20)], .drop (.int 10), .drop (.int 20)] ∧
      runSrc .matchedAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms =
        [.body 0 [(1, .int 10), (0, .int 20)], .drop (.int 20), .drop (.int 10)] ∧
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms ≠
        runSrc .matchedAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · intro a ha
    unfold refDropArms at ha
    simp at ha
    subst ha
    decide
  · intro h
    have := h refDropArms[0] (by unfold refDropArms; simp)
    revert this; decide

/-- **Counterexample (split with each sub-branch's own drop order).** The split lowering whose
sub-branches drop in their own declaration order does not reproduce the `firstAlternative`
source trace of `refDropArms` on `Err((10, 20))`. -/
theorem runSplit_matchedAlternative_ne_runSrc_firstAlternative_refDropArms :
    runSplit (.inr (.pair (.int 10) (.int 20))) (splitArms .matchedAlternative 0 refDropArms) ≠
      runSrc .firstAlternative (.inr (.pair (.int 10) (.int 20))) 0 refDropArms := by decide

/-- **Counterexample (no-duplicate hypothesis of the drop-policy theorem).** `dupBindArms`
(the or-free pattern `(x, x)`) satisfies `SameDeclOrder`, binds the name `0` twice
(`NoDupBindings` fails), and on `(1, 2)` the `firstAlternative` policy drops `1` twice (it looks
names up in the environment, finding the first entry for `0` both times) while the
`matchedAlternative` policy drops `2` then `1`. -/
theorem dupBindArms_sameDeclOrder_not_noDupBindings_and_policies_differ :
    (∀ a ∈ dupBindArms, SameDeclOrder a.pat) ∧ ¬ (∀ a ∈ dupBindArms, NoDupBindings a.pat) ∧
      runSrc .firstAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms =
        [.body 0 [(0, .int 1), (0, .int 2)], .drop (.int 1), .drop (.int 1)] ∧
      runSrc .matchedAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms =
        [.body 0 [(0, .int 1), (0, .int 2)], .drop (.int 2), .drop (.int 1)] ∧
      runSrc .firstAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms ≠
        runSrc .matchedAlternative (.pair (.int 1) (.int 2)) 0 dupBindArms := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · intro a ha
    unfold dupBindArms at ha
    simp at ha
    subst ha
    decide
  · intro h
    have := h dupBindArms[0] (by unfold dupBindArms; simp)
    revert this; decide

/-- **Drop events on a pattern whose alternatives bind different names.** On `Err(5)`,
`unbalancedOrArms` (`Ok(_) | Err(x)`) runs its body with `x = 5`; the `firstAlternative` policy
emits no drop event (the first alternative binds nothing), while the `matchedAlternative` policy
drops `5`. -/
theorem unbalancedOrArms_firstAlternative_omits_drop :
    runSrc .firstAlternative (.inr (.int 5)) 0 unbalancedOrArms = [.body 0 [(0, .int 5)]] ∧
      runSrc .matchedAlternative (.inr (.int 5)) 0 unbalancedOrArms =
        [.body 0 [(0, .int 5)], .drop (.int 5)] := by
  decide

/-- **Positive control (the order hypothesis is not necessary).** `shadowedSwapArms` has no
alternative binding a name twice and violates `SameDeclOrder`, yet for every value `v` the two
drop policies give the same trace (its order-reversing alternative is never used). -/
theorem shadowedSwapArms_not_sameDeclOrder_and_policies_agree :
    (∀ a ∈ shadowedSwapArms, NoDupBindings a.pat) ∧
      ¬ (∀ a ∈ shadowedSwapArms, SameDeclOrder a.pat) ∧
      ∀ v, runSrc .firstAlternative v 0 shadowedSwapArms =
        runSrc .matchedAlternative v 0 shadowedSwapArms := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    unfold shadowedSwapArms at ha
    simp at ha
    subst ha
    decide
  · intro h
    have := h shadowedSwapArms[0] (by unfold shadowedSwapArms; simp)
    revert this; decide
  · intro v
    cases v with
    | pair a b =>
      simp [runSrc, shadowedSwapArms, matchAll, tryEnvs, armDrops, dropsInOrder, dropsMatched,
        declOrder, List.lookup]
    | _ => simp [runSrc, shadowedSwapArms, matchAll, tryEnvs]

/-- **Non-vacuity (splitting and policy agreement).** Every arm of `bindingGuardArms` satisfies
`NoDupBindings` and `SameDeclOrder`; its first arm is a guarded or-pattern whose guard reads the
binding. -/
theorem bindingGuardArms_noDupBindings_sameDeclOrder :
    (∀ a ∈ bindingGuardArms, NoDupBindings a.pat) ∧ (∀ a ∈ bindingGuardArms, SameDeclOrder a.pat) := by
  refine ⟨?_, ?_⟩ <;> intro a ha <;> unfold bindingGuardArms at ha <;> simp at ha <;>
    rcases ha with rfl | rfl <;> decide

/-! ### Definition examples -/

/-- Positive example (`matchAll`): `(x, _) | (_, x)` matches `(1, 2)` in two ways, in order. -/
theorem matchAll_example :
    matchAll (.or (.pair (.bind 0) .wild) (.pair .wild (.bind 0))) (.pair (.int 1) (.int 2)) =
      [[(0, .int 1)], [(0, .int 2)]] := by decide

/-- Negative example (`matchAll`): `Ok(_)` does not match `Err(1)`. -/
theorem matchAll_example_none : matchAll (.inl .wild) (.inr (.int 1)) = [] := by decide

/-- Positive example (`expand`): nested alternatives expand lexicographically. -/
theorem expand_example :
    expand (.pair (.or (.int 0) (.int 1)) (.or (.int 2) (.int 3))) =
      [.pair (.int 0) (.int 2), .pair (.int 0) (.int 3), .pair (.int 1) (.int 2),
        .pair (.int 1) (.int 3)] := by decide

/-- Positive example (`declOrder`): an or-pattern declares in its first alternative's order. -/
theorem declOrder_example : declOrder (refDropArms[0]).pat = [0, 1] := by decide

/-- Positive example (`OrFree`). -/
theorem orFree_example : OrFree (.pair (.bind 0) .wild) := ⟨trivial, trivial⟩

/-- Negative example (`OrFree`). -/
theorem not_orFree_example : ¬ OrFree (.or .wild .wild) := id

/-- Positive example (`SameDeclOrder`): `Ok(x) | Err(x)`. -/
theorem sameDeclOrder_example : SameDeclOrder (.or (.inl (.bind 0)) (.inr (.bind 0))) := by
  decide

/-- Negative example (`SameDeclOrder`): `Ok((x, y)) | Err((y, x))`. -/
theorem not_sameDeclOrder_example :
    ¬ SameDeclOrder (.or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0)))) := by
  decide

/-- Positive example (`NoDupBindings`): `Ok((x, y)) | Err((y, x))`. -/
theorem noDupBindings_example :
    NoDupBindings (.or (.inl (.pair (.bind 0) (.bind 1))) (.inr (.pair (.bind 1) (.bind 0)))) := by
  decide

/-- Negative example (`NoDupBindings`): `(x, x)`. -/
theorem not_noDupBindings_example : ¬ NoDupBindings (.pair (.bind 0) (.bind 0)) := by decide

end Toy.MatchGuard.OrPat
