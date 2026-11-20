import ToyAlias.Optimizations

/-!
# A toy tree model, and where it disagrees with the toy stack model

A deliberately small tree-structured permission model in the style of Tree Borrows
(Villani, Hostert, Dreyer, Jung; PLDI 2025), for one location. Each tag is a node with
a parent and a permission. An access through tag `t` is *local* for a node `u` if `t`
is `u` itself or derived from `u` (a descendant), and *foreign* otherwise. The
permission states and transitions follow the paper's default state machine
(its Fig. 1) restricted to `Reserved`, `Unique`, `Frozen`, `Disabled`; the Miri
implementation also names the active state `Unique` (`rust-lang/miri` commit
`0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/borrow_tracker/tree_borrows/perms.rs`).
Reborrows perform an implicit
read; a new mutable reference starts `Reserved`, a new shared reference `Frozen`; the
root starts `Unique`.

Raw pointers do not get a node of their own: as in Tree Borrows, an access through a
raw pointer is an access through the tag of the reference it was created from.

Omitted (this is not Tree Borrows): protectors (hence also the conflicted `Reserved`
behaviour and protector-end accesses), `ReservedIM` for interior mutability, ranges and
lazily initialized permissions, multiple locations.

`TMem` is unconstrained: a node list may contain duplicate tags, parent cycles, or
dangling parent links (`parentOf` takes the first match and `derivedFrom` stops after
`ns.length` parent steps), and `tretag` accepts any initial permission. Well-formed trees
arise from `initTMem` and `runTree`. The general theorem `tree_read_read_commute` holds
on every `TMem`, because locality depends only on the tags and parent links, which reads
do not change.

Contents: concrete programs whose verdicts differ between the toy stack model and this
toy tree model, in both directions (`stack_ub_tree_defined_parentReadThenChildWrite`,
`stack_defined_tree_ub_rawWriteAroundParentRead`), and the general theorem that two
reads commute in the toy tree model (`tree_read_read_commute`).
-/

namespace Toy.Alias.Tree

open Toy.Alias

/-- Per-node permission in the toy tree model. -/
inductive TPerm where
  | reserved
  | unique
  | frozen
  | disabled
  deriving DecidableEq, Repr

/-- Transition of a node's permission under an access of kind `k` that is local
(`loc = true`) or foreign for that node; `none` is UB. Local read: allowed except on
`disabled`. Local write: `reserved`/`unique` become `unique`; UB on `frozen`/`disabled`.
Foreign read: `unique` becomes `frozen`; others unchanged. Foreign write: everything
becomes `disabled`. -/
def TPerm.step : AccessKind → Bool → TPerm → Option TPerm
  | .read, true, .disabled => none
  | .read, true, q => some q
  | .read, false, .unique => some .frozen
  | .read, false, q => some q
  | .write, true, .reserved => some .unique
  | .write, true, .unique => some .unique
  | .write, true, .frozen => none
  | .write, true, .disabled => none
  | .write, false, _ => some .disabled

/-- Positive example: a not-yet-written mutable reference tolerates a foreign read. -/
theorem TPerm.step_reserved_foreign_read : TPerm.step .read false .reserved = some .reserved := rfl

/-- Positive example: a foreign read freezes an active (`unique`) reference instead of
disabling it. -/
theorem TPerm.step_unique_foreign_read : TPerm.step .read false .unique = some .frozen := rfl

/-- Negative example: a local write to a `frozen` node is UB. -/
theorem TPerm.step_frozen_local_write : TPerm.step .write true .frozen = none := rfl

/-- A node of the borrow tree. -/
structure Node where
  tag : Tag
  parent : Option Tag
  perm : TPerm
  deriving DecidableEq, Repr

/-- Tree-model machine state for one location: value, nodes, next fresh tag. -/
structure TMem where
  val : Nat
  nodes : List Node
  next : Tag
  deriving DecidableEq, Repr

/-- The parent of tag `t`, if `t` is a node with a parent. -/
def parentOf (ns : List Node) (t : Tag) : Option Tag :=
  (ns.find? (fun n => n.tag == t)).bind (·.parent)

/-- `derivedFrom ns fuel t u`: `t` equals `u` or is a descendant of `u`, following at most
`fuel` parent links. -/
def derivedFrom (ns : List Node) : Nat → Tag → Tag → Bool
  | 0, t, u => t == u
  | fuel + 1, t, u =>
    t == u ||
      match parentOf ns t with
      | some q => derivedFrom ns fuel q u
      | none => false

/-- `isLocal ns acc u`: an access through `acc` is local for node `u`. -/
def isLocal (ns : List Node) (acc u : Tag) : Bool := derivedFrom ns ns.length acc u

/-- A two-node tree: root `0` and its child `1`. -/
def twoNodes : List Node := [⟨0, none, .unique⟩, ⟨1, some 0, .reserved⟩]

/-- Positive example: an access through the child is local for the root. -/
theorem isLocal_child_for_root : isLocal twoNodes 1 0 = true := by decide

/-- Negative example: an access through the root is foreign for the child. -/
theorem not_isLocal_root_for_child : isLocal twoNodes 0 1 = false := by decide

/-- Apply a partial function to every element, failing if any application fails. -/
def mapOpt {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a, mapOpt f as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- An access of kind `k` through tag `t`: UB if `t` is not a node; otherwise every node
takes its local or foreign transition, and UB if any transition is UB. -/
def treeAccess (k : AccessKind) (t : Tag) (ns : List Node) : Option (List Node) :=
  if ns.any (fun n => n.tag == t) then
    mapOpt (fun n => (TPerm.step k (isLocal ns t n.tag) n.perm).map fun q => { n with perm := q }) ns
  else none

/-- Positive example: a read through the root freezes nothing here and leaves the
`reserved` child readable. -/
theorem treeAccess_example_pos :
    treeAccess .read 0 twoNodes = some twoNodes := by decide

/-- Negative example: after a foreign write disables the child, a write through the child
is UB. -/
theorem treeAccess_example_neg :
    ((treeAccess .write 0 twoNodes).bind fun ns => treeAccess .write 1 ns) = none := by decide

/-- Read through `t` in the tree model. -/
def tread (t : Tag) (m : TMem) : Option (Nat × TMem) :=
  (treeAccess .read t m.nodes).map fun ns => (m.val, { m with nodes := ns })

/-- Write `v` through `t` in the tree model. -/
def twrite (t : Tag) (v : Nat) (m : TMem) : Option TMem :=
  (treeAccess .write t m.nodes).map fun ns => { m with val := v, nodes := ns }

/-- Positive example: a read through the root of a two-node tree returns the value. -/
theorem tread_example_pos : tread 0 ⟨7, twoNodes, 2⟩ = some (7, ⟨7, twoNodes, 2⟩) := by
  decide

/-- Negative example: a read through a tag that is not a node is UB. -/
theorem tread_example_neg : tread 5 ⟨7, twoNodes, 2⟩ = none := by decide

/-- Positive example: a write through the `reserved` child activates it (`unique`). -/
theorem twrite_example_pos :
    twrite 1 9 ⟨7, twoNodes, 2⟩ =
      some ⟨9, [⟨0, none, .unique⟩, ⟨1, some 0, .unique⟩], 2⟩ := by decide

/-- Negative example: a write through a `disabled` node is UB. -/
theorem twrite_example_neg :
    twrite 1 9 ⟨7, [⟨0, none, .unique⟩, ⟨1, some 0, .disabled⟩], 2⟩ = none := by decide

/-- Reborrow from `parent` with initial permission `init`: an implicit read through the
parent, then a fresh child node `m.next`. -/
def tretag (parent : Tag) (init : TPerm) (m : TMem) : Option (Tag × TMem) :=
  (treeAccess .read parent m.nodes).map fun ns =>
    (m.next, { m with nodes := ns ++ [⟨m.next, some parent, init⟩], next := m.next + 1 })

/-- Initial tree state: value `0`, a single root node `0` in state `unique`. -/
def initTMem : TMem := ⟨0, [⟨0, none, .unique⟩], 1⟩

/-- Positive example: a mutable reborrow of the root adds a `reserved` child. -/
theorem tretag_example_pos :
    tretag 0 .reserved initTMem = some (1, ⟨0, twoNodes, 2⟩) := by decide

/-- Negative example: reborrowing from a tag that is not a node is UB. -/
theorem tretag_example_neg : tretag 5 .reserved initTMem = none := by decide

/-! ## A common straight-line program language for both toy models -/

/-- Straight-line operations, interpreted in both toy models. Indices refer to a tag
environment that reborrows extend. -/
inductive Op where
  /-- Create a mutable reference from the `i`-th tag. -/
  | reborrowMut (i : Nat)
  /-- Create a (read-only) shared reference from the `i`-th tag. -/
  | reborrowShared (i : Nat)
  /-- Create a raw pointer from the `i`-th tag. The two toy models treat this differently.
  `runStack` performs `retag t .sharedRW false`, modelling a `*mut` pointer: it needs an
  item carrying the parent tag that grants writes (so it is UB when every item carrying the
  parent tag is `sharedRO`), and inserts a fresh tagged `sharedRW` item. `runTree` creates no node and performs no
  access: it appends the parent tag itself to the environment, without checking that tag's
  permission or even that it is a node; later accesses through the raw pointer are
  accesses through the parent tag. -/
  | reborrowRaw (i : Nat)
  /-- Read through the `i`-th tag; the value is observed. -/
  | read (i : Nat)
  /-- Write `v` through the `i`-th tag. -/
  | write (i : Nat) (v : Nat)
  deriving DecidableEq, Repr

/-- Run a program in the toy stack model (unprotected reborrows: `unique` for mutable,
`sharedRO` for shared, a tagged `sharedRW` item for a raw pointer). Returns observations
and final state, or `none` (UB). -/
def runStack : List Tag → List Op → Mem → Option (List Nat × Mem)
  | _, [], m => some ([], m)
  | env, .reborrowMut i :: ops, m =>
    env[i]?.bind fun t => (retag t .unique false m).bind fun (t', m') => runStack (env ++ [t']) ops m'
  | env, .reborrowShared i :: ops, m =>
    env[i]?.bind fun t => (retag t .sharedRO false m).bind fun (t', m') => runStack (env ++ [t']) ops m'
  | env, .reborrowRaw i :: ops, m =>
    env[i]?.bind fun t => (retag t .sharedRW false m).bind fun (t', m') => runStack (env ++ [t']) ops m'
  | env, .read i :: ops, m =>
    env[i]?.bind fun t => (read t m).bind fun (v, m') =>
      (runStack env ops m').map fun (obs, m'') => (v :: obs, m'')
  | env, .write i v :: ops, m =>
    env[i]?.bind fun t => (write t v m).bind fun m' => runStack env ops m'

/-- Run a program in the toy tree model (`reserved` for mutable, `frozen` for shared; a raw
pointer reuses the tag it is created from). -/
def runTree : List Tag → List Op → TMem → Option (List Nat × TMem)
  | _, [], m => some ([], m)
  | env, .reborrowMut i :: ops, m =>
    env[i]?.bind fun t => (tretag t .reserved m).bind fun (t', m') => runTree (env ++ [t']) ops m'
  | env, .reborrowShared i :: ops, m =>
    env[i]?.bind fun t => (tretag t .frozen m).bind fun (t', m') => runTree (env ++ [t']) ops m'
  | env, .reborrowRaw i :: ops, m =>
    env[i]?.bind fun t => runTree (env ++ [t]) ops m
  | env, .read i :: ops, m =>
    env[i]?.bind fun t => (tread t m).bind fun (v, m') =>
      (runTree env ops m').map fun (obs, m'') => (v :: obs, m'')
  | env, .write i v :: ops, m =>
    env[i]?.bind fun t => (twrite t v m).bind fun m' => runTree env ops m'

/-- Positive example: both models accept writing through a fresh mutable reference and
reading it back. -/
theorem run_example_pos :
    (runStack [0] [.reborrowMut 0, .write 1 3, .read 1] initMem).map Prod.fst = some [3] ∧
      (runTree [0] [.reborrowMut 0, .write 1 3, .read 1] initTMem).map Prod.fst = some [3] := by
  decide

/-- Negative example: both models reject writing through a shared reference. -/
theorem run_example_neg :
    runStack [0] [.reborrowShared 0, .write 1 3] initMem = none ∧
      runTree [0] [.reborrowShared 0, .write 1 3] initTMem = none := by decide

/-! ## Verdicts that differ between the two toy models -/

/-- The program `let x = &mut *root; read root; *x = 5; read x`. -/
def parentReadThenChildWrite : List Op := [.reborrowMut 0, .read 0, .write 1 5, .read 1]

/-- **Parent read before the first child write: stack UB, tree defined.** A read through
the parent before the first write through a fresh mutable reference: UB in the toy
stack model (the parent read removes the child's `unique` item), defined in the toy
tree model (the child is `reserved` and tolerates the foreign read), where it observes
`[0, 5]`. -/
theorem stack_ub_tree_defined_parentReadThenChildWrite :
    runStack [0] parentReadThenChildWrite initMem = none ∧
      (runTree [0] parentReadThenChildWrite initTMem).map Prod.fst = some [0, 5] := by decide

/-- Source of a read-read swap: `let x = &mut *root; *x = 42; read x; read root`. -/
def readReadSrc : List Op := [.reborrowMut 0, .write 1 42, .read 1, .read 0]

/-- Target of the read-read swap: `let x = &mut *root; *x = 42; read root; read x`. -/
def readReadTgt : List Op := [.reborrowMut 0, .write 1 42, .read 0, .read 1]

/-- **Read-read swap on a concrete program: stack rejects, tree agrees.** Swapping two
adjacent reads (through a written mutable reference and through its parent): in the toy
stack model the source is defined and the target is UB; in the toy tree model source
and target have the same defined outcome (observations and final tree). This is a
reachable instance of `tree_read_read_commute` and of `stack_read_read_not_commute`. -/
theorem readRead_swap_stack_rejects_tree_agrees :
    (runStack [0] readReadSrc initMem).isSome = true ∧
      runStack [0] readReadTgt initMem = none ∧
      (runTree [0] readReadSrc initTMem).isSome = true ∧
      runTree [0] readReadTgt initTMem = runTree [0] readReadSrc initTMem := by decide

/-- The program `let tmp = &mut *root; let ptr = tmp as *mut _; *ptr = 1; read root;
*ptr = 2`. -/
def rawWriteAroundParentRead : List Op :=
  [.reborrowMut 0, .reborrowRaw 1, .write 2 1, .read 0, .write 2 2]

/-- **Raw-pointer writes around a parent read: stack defined, tree UB.** In the toy stack
model the raw pointer is a `sharedRW` item above `tmp`; the read through `root` removes
`tmp` but not the raw pointer, so the second write is allowed and the program observes
`[1]`. In the toy tree model the raw pointer uses `tmp`'s tag, the first write activates
`tmp`, the foreign read through `root` freezes it, and the second write is UB. -/
theorem stack_defined_tree_ub_rawWriteAroundParentRead :
    (runStack [0] rawWriteAroundParentRead initMem).map Prod.fst = some [1] ∧
      runTree [0] rawWriteAroundParentRead initTMem = none := by decide

/-! ## In the toy tree model, any two reads commute -/

/-- The structural part of a node list: tags and parents (not permissions). -/
def shape (ns : List Node) : List (Tag × Option Tag) := ns.map fun n => (n.tag, n.parent)

theorem parentOf_congr {ns' ns : List Node} (h : shape ns' = shape ns) (t : Tag) :
    parentOf ns' t = parentOf ns t := by
  induction ns generalizing ns' with
  | nil =>
    cases ns' with
    | nil => rfl
    | cons _ _ => simp [shape] at h
  | cons n ns ih =>
    cases ns' with
    | nil => simp [shape] at h
    | cons n' ns' =>
      simp only [shape, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨htag, hpar⟩, hrest⟩ := h
      have hih := ih (ns' := ns') hrest
      unfold parentOf at hih ⊢
      simp only [List.find?_cons, htag]
      cases hc : (n.tag == t) with
      | true => simp [hpar]
      | false => simpa using hih

theorem derivedFrom_congr {ns' ns : List Node} (h : shape ns' = shape ns) :
    ∀ fuel t u, derivedFrom ns' fuel t u = derivedFrom ns fuel t u := by
  intro fuel
  induction fuel with
  | zero => intro t u; rfl
  | succ k ih =>
    intro t u
    simp only [derivedFrom, parentOf_congr h]
    cases parentOf ns t with
    | none => rfl
    | some q => simp [ih]

theorem length_congr {ns' ns : List Node} (h : shape ns' = shape ns) : ns'.length = ns.length := by
  have := congrArg List.length h
  simpa [shape] using this

theorem isLocal_congr {ns' ns : List Node} (h : shape ns' = shape ns) (acc u : Tag) :
    isLocal ns' acc u = isLocal ns acc u := by
  unfold isLocal
  rw [length_congr h, derivedFrom_congr h]

theorem any_tag_congr {ns' ns : List Node} (h : shape ns' = shape ns) (t : Tag) :
    ns'.any (fun n => n.tag == t) = ns.any (fun n => n.tag == t) := by
  have h1 : ∀ l : List Node, l.any (fun n => n.tag == t) = (shape l).any (fun p => p.1 == t) := by
    intro l; simp [shape, List.any_map, Function.comp_def]
  rw [h1, h1, h]

/-- Per-node effect of a read that is local (`l = true`) or foreign for the node. -/
def rd (l : Bool) (n : Node) : Option Node :=
  (TPerm.step .read l n.perm).map fun q => { n with perm := q }

theorem rd_comm (l₁ l₂ : Bool) (n : Node) : (rd l₁ n).bind (rd l₂) = (rd l₂ n).bind (rd l₁) := by
  obtain ⟨tag, par, q⟩ := n
  cases l₁ <;> cases l₂ <;> cases q <;> rfl

theorem rd_bind_tag (l : Bool) (n : Node) (L : Tag → Bool) :
    (rd l n).bind (fun n' => rd (L n'.tag) n') = (rd l n).bind (rd (L n.tag)) := by
  unfold rd
  cases TPerm.step .read l n.perm <;> rfl

theorem shape_mapOpt_rd (L : Tag → Bool) :
    ∀ {ns ns' : List Node}, mapOpt (fun n => rd (L n.tag) n) ns = some ns' → shape ns' = shape ns
  | [], ns', h => by simp [mapOpt] at h; subst h; rfl
  | n :: ns, ns', h => by
    simp only [mapOpt] at h
    cases hn : rd (L n.tag) n with
    | none => simp [hn] at h
    | some b =>
      cases hr : mapOpt (fun n => rd (L n.tag) n) ns with
      | none => simp [hn, hr] at h
      | some bs =>
        simp only [hn, hr, Option.some.injEq] at h
        subst h
        have hb : b.tag = n.tag ∧ b.parent = n.parent := by
          unfold rd at hn
          cases hs : TPerm.step .read (L n.tag) n.perm <;> simp [hs] at hn
          subst hn; exact ⟨rfl, rfl⟩
        simp only [shape, List.map_cons, hb.1, hb.2]
        exact congrArg _ (shape_mapOpt_rd L hr)

theorem mapOpt_bind {f g : Node → Option Node} :
    ∀ (xs : List Node), (mapOpt f xs).bind (mapOpt g) = mapOpt (fun x => (f x).bind g) xs
  | [] => rfl
  | x :: xs => by
    have ih := mapOpt_bind (f := f) (g := g) xs
    simp only [mapOpt]
    cases hf : f x with
    | none => rfl
    | some b =>
      cases hr : mapOpt f xs with
      | none =>
        rw [hr] at ih
        simp only [Option.bind_none] at ih
        simp only [Option.bind_some, ← ih]
        cases g b <;> rfl
      | some bs =>
        rw [hr] at ih
        simp only [Option.bind_some] at ih
        simp only [Option.bind_some, mapOpt, ← ih]

theorem mapOpt_congr {f g : Node → Option Node} (h : ∀ x, f x = g x) :
    ∀ xs, mapOpt f xs = mapOpt g xs
  | [] => rfl
  | x :: xs => by simp only [mapOpt, h x, mapOpt_congr h xs]

theorem treeAccess_read_eq (t : Tag) (ns : List Node) :
    treeAccess .read t ns =
      if ns.any (fun n => n.tag == t) then mapOpt (fun n => rd (isLocal ns t n.tag) n) ns else none :=
  rfl

/-- After a read through `t₁`, a read through `t₂` behaves as it would have on the original
nodes (locality and node existence depend only on the unchanged tree shape). -/
theorem treeAccess_read_after_read (t₁ t₂ : Tag) (ns ns' : List Node)
    (h : treeAccess .read t₁ ns = some ns') :
    treeAccess .read t₂ ns' =
      if ns.any (fun n => n.tag == t₂) then
        mapOpt (fun n => rd (isLocal ns t₂ n.tag) n) ns' else none := by
  rw [treeAccess_read_eq] at h
  split at h
  · have hs := shape_mapOpt_rd (fun tag => isLocal ns t₁ tag) h
    rw [treeAccess_read_eq, any_tag_congr hs]
    congr 1
    exact mapOpt_congr (fun n => by rw [isLocal_congr hs]) ns'
  · simp at h

theorem treeAccess_read_comm (t₁ t₂ : Tag) (ns : List Node) :
    (treeAccess .read t₁ ns).bind (treeAccess .read t₂) =
      (treeAccess .read t₂ ns).bind (treeAccess .read t₁) := by
  have key : ∀ a b : Tag, (treeAccess .read a ns).bind (treeAccess .read b) =
      if ns.any (fun n => n.tag == a) && ns.any (fun n => n.tag == b) then
        mapOpt (fun n => (rd (isLocal ns a n.tag) n).bind (rd (isLocal ns b n.tag))) ns
      else none := by
    intro a b
    have hcongr : (treeAccess .read a ns).bind (treeAccess .read b) =
        (treeAccess .read a ns).bind (fun ns' =>
          if ns.any (fun n => n.tag == b) then
            mapOpt (fun n => rd (isLocal ns b n.tag) n) ns' else none) := by
      cases h : treeAccess .read a ns with
      | none => rfl
      | some ns' => exact treeAccess_read_after_read a b ns ns' h
    rw [hcongr, treeAccess_read_eq]
    cases ha : ns.any (fun n => n.tag == a) <;> cases hb : ns.any (fun n => n.tag == b)
    · rfl
    · rfl
    · simp only [ite_true, ite_false, Bool.true_and, Bool.false_eq_true]
      cases mapOpt (fun n => rd (isLocal ns a n.tag) n) ns <;> rfl
    · simp only [ite_true, Bool.true_and]
      rw [mapOpt_bind]
      exact mapOpt_congr (fun n => rd_bind_tag _ n (isLocal ns b)) ns
  rw [key t₁ t₂, key t₂ t₁, Bool.and_comm]
  split
  · exact mapOpt_congr (fun n => rd_comm _ _ n) ns
  · rfl

/-- **Reads commute in the toy tree model.** Reading through `t₁` then
`t₂` yields the same observed values and the same final state as reading through `t₂`
then `t₁`, and one order is UB exactly when the other is. This holds for every tree
state (no well-formedness hypothesis). -/
theorem tree_read_read_commute (t₁ t₂ : Tag) (m : TMem) :
    ((tread t₁ m).bind fun (v₁, m₁) => (tread t₂ m₁).map fun (v₂, m₂) => ((v₁, v₂), m₂)) =
      ((tread t₂ m).bind fun (v₂, m₁) => (tread t₁ m₁).map fun (v₁, m₂) => ((v₁, v₂), m₂)) := by
  have hc := treeAccess_read_comm t₁ t₂ m.nodes
  unfold tread
  cases h1 : treeAccess .read t₁ m.nodes <;> cases h2 : treeAccess .read t₂ m.nodes <;>
    simp only [h1, h2, Option.bind_none, Option.bind_some, Option.map_none, Option.map_some] at hc ⊢
  · -- t₁ UB, t₂ defined: the other order is UB too
    rename_i ns₂
    simp only [Option.map] at hc ⊢
    rw [← hc]
  · rename_i ns₁
    simp only [Option.map] at hc ⊢
    rw [hc]
  · rename_i ns₁ ns₂
    simp only [Option.map] at hc ⊢
    cases h3 : treeAccess .read t₂ ns₁ <;> cases h4 : treeAccess .read t₁ ns₂ <;>
      simp_all

/-- Non-vacuity of `tree_read_read_commute`: with `t₁ = 0` (the root) and `t₂ = 1` (an
active child), reading in the order `t₁, t₂` is defined and changes the tree (the read
through the root freezes the child). -/
theorem tree_read_read_commute_nonvacuous :
    let m0 : TMem := ⟨42, [⟨0, none, .unique⟩, ⟨1, some 0, .unique⟩], 2⟩
    let lhs := (tread 0 m0).bind fun (v₁, m₁) =>
      (tread 1 m₁).map fun (v₂, m₂) => ((v₁, v₂), m₂)
    lhs = some ((42, 42), ⟨42, [⟨0, none, .unique⟩, ⟨1, some 0, .frozen⟩], 2⟩) ∧
      lhs.map Prod.snd ≠ some m0 := by decide

/-- Positive control for `tree_read_read_commute` (the stack model is not like this): in the
toy stack model two reads need not commute; reading through a mutable child then its
parent is defined, reading through the parent then the child is UB. -/
theorem stack_read_read_not_commute :
    ((read 1 ⟨42, [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩).bind fun (_, m) => read 0 m).isSome
        = true ∧
      ((read 0 ⟨42, [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩).bind fun (_, m) => read 1 m)
        = none := by decide

end Toy.Alias.Tree
