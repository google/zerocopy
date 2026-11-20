/-
Toy.SCT.Graph
=============

Size-change graphs, their composition, and the composition closure of a program's graphs.

Model. A program has `nf` functions, named by `Fin nf`, and every function has the same number `k`
of parameter slots, named by `Fin k`. A function with fewer real parameters is modelled by leaving
the extra slots without arcs; such slots do not affect the closure `InClosure`, the criterion
`ClosureCriterion`, size-change termination, consistent runs, or the checker `checkSCT`. They do
affect lexicographic projection measures (`LexProjDecreases` in `Toy.SCT.Semantics`): a projection
onto an arc-free slot is unconstrained on every call into that function.

A size-change graph describes one call site from function `src` to function `dst`. Its label
`lab i j` describes the relation between the value of caller parameter `i` and the value passed as
callee argument `j`:
* `Label.strict`    : the callee argument is strictly smaller than the caller parameter;
* `Label.nonstrict` : the callee argument is smaller than or equal to the caller parameter;
* `Label.absent`    : no information.
This is the "size-change graph" of Lee, Jones and Ben-Amram (POPL 2001), represented as a total
labelling (at most one label per pair, the strongest known).

The model is unrooted: every function is a possible entry point, and the closure contains the
composites of all call paths, as in Ben-Amram (LMCS 2010). Lee, Jones and Ben-Amram (POPL 2001)
restrict call sequences and the closure to functions reachable from a designated initial function,
so a recursive function that is unreachable from it is ignored there but tested here.
-/

namespace Toy.SCT

/-- The label of a size-change arc from a caller parameter to a callee argument.
`strict` means "callee argument < caller parameter", `nonstrict` means "≤", `absent` means no
information. -/
inductive Label where
  | absent
  | nonstrict
  | strict
  deriving DecidableEq, Repr

namespace Label

/-- Sequencing two arcs along a thread `i → m → j` (first arc, then second arc): absent if either
arc is absent; otherwise strict if either arc is strict; otherwise nonstrict.
This is the strictness bookkeeping of size-change composition: `≤ ; < = <`, `< ; ≤ = <`,
`≤ ; ≤ = ≤`. -/
def seq : Label → Label → Label
  | absent, _ => absent
  | _, absent => absent
  | strict, _ => strict
  | _, strict => strict
  | nonstrict, nonstrict => nonstrict

/-- An alternative, deliberately wrong sequencing that over-claims strictness: any two present
arcs sequence to `strict` (so `≤ ; ≤ = <`). Used only to show that composition must track
strictness exactly. -/
def seqOverStrict : Label → Label → Label
  | absent, _ => absent
  | _, absent => absent
  | _, _ => strict

/-- An alternative, deliberately lossy sequencing that forgets strictness when a nonstrict arc is
followed by a strict one (`≤ ; < = ≤`), and is otherwise `seq` (`< ; ≤ = <`, `< ; < = <`,
`≤ ; ≤ = ≤`). Used only to show that composition must track strictness exactly. -/
def seqForgetLeft : Label → Label → Label
  | absent, _ => absent
  | _, absent => absent
  | strict, _ => strict
  | nonstrict, _ => nonstrict

/-- An alternative, deliberately lossy sequencing that forgets strictness when a strict arc is
followed by a nonstrict one (`< ; ≤ = ≤`), and is otherwise `seq` (`≤ ; < = <`, `< ; < = <`,
`≤ ; ≤ = ≤`). Used only to show that composition must track strictness exactly. -/
def seqForgetRight : Label → Label → Label
  | absent, _ => absent
  | _, absent => absent
  | _, strict => strict
  | _, nonstrict => nonstrict

/-- Join (maximum) in the order `absent < nonstrict < strict`. It combines the alternative
intermediate parameters of a composition: the composite arc is as strong as the strongest
thread through any intermediate parameter. -/
def join : Label → Label → Label
  | strict, _ => strict
  | _, strict => strict
  | nonstrict, _ => nonstrict
  | _, nonstrict => nonstrict
  | absent, absent => absent

end Label

/-- A size-change graph for a call site from function `src` to function `dst`, over `k` parameter
slots. `lab i j` labels the arc from caller parameter `i` to callee argument `j`
(see `Label`). -/
structure SCG (nf k : Nat) where
  src : Fin nf
  dst : Fin nf
  lab : Fin k → Fin k → Label

/-- First-match lookup of the label of arc `(i, j)` in an arc list; `absent` if the arc is not
listed. Only used to write concrete graphs readably. -/
def lookupArc (arcs : List (Nat × Nat × Label)) (i j : Nat) : Label :=
  match arcs.find? (fun a => a.1 == i && a.2.1 == j) with
  | some a => a.2.2
  | none => Label.absent

/-- The size-change graph from `src` to `dst` whose arcs are listed as
`(caller parameter, callee argument, label)`; unlisted arcs are `absent`. -/
def arcsG {nf k : Nat} (src dst : Fin nf) (arcs : List (Nat × Nat × Label)) : SCG nf k where
  src := src
  dst := dst
  lab i j := lookupArc arcs i.val j.val

namespace SCG

variable {nf k : Nat}

/-- Composition of size-change graphs, parameterised by the arc-sequencing operation `sq`.
`G.compWith sq H` describes "a call described by `G` followed by a call described by `H`": its arc
`(i, j)` is the join over all intermediate parameters `m` of `sq (G.lab i m) (H.lab m j)`.
Composition is total: it does not check `G.dst = H.src` (in Lee, Jones and Ben-Amram, Definition 14,
composition is defined only for such pairs); the closure below only composes such pairs. Because
of totality a non-loop graph can satisfy `G ; G = G` as a label matrix, which is why the criterion
tests only loops (`G.src = G.dst`). -/
def compWith (sq : Label → Label → Label) (G H : SCG nf k) : SCG nf k where
  src := G.src
  dst := H.dst
  lab i j := (List.finRange k).foldl (fun acc m => Label.join acc (sq (G.lab i m) (H.lab m j)))
    Label.absent

/-- The standard size-change composition `G ; H` (Lee, Jones and Ben-Amram), i.e. `compWith` with
the strictness-tracking sequencing `Label.seq`. -/
def comp (G H : SCG nf k) : SCG nf k := compWith Label.seq G H

theorem ext_iff' {G H : SCG nf k} :
    G = H ↔ G.src = H.src ∧ G.dst = H.dst ∧ ∀ i j, G.lab i j = H.lab i j := by
  constructor
  · intro e; subst e; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  · intro ⟨h1, h2, h3⟩
    cases G with
    | mk s d l =>
      cases H with
      | mk s' d' l' =>
        simp only at h1 h2 h3
        subst h1; subst h2
        have : l = l' := funext fun i => funext fun j => h3 i j
        subst this; rfl

/-- Decidable equality of size-change graphs (componentwise, labels compared pointwise). -/
instance instDecidableEq : DecidableEq (SCG nf k) := fun G H =>
  if h : G.src = H.src ∧ G.dst = H.dst ∧ ∀ i j, G.lab i j = H.lab i j then
    isTrue (ext_iff'.mpr h)
  else
    isFalse (fun e => h (ext_iff'.mp e))

/-- `G` has a strict self-arc `(i, i, <)`: some parameter strictly decreases from the caller to
the callee position of the same name. -/
def HasStrictSelfArc (G : SCG nf k) : Prop := ∃ i : Fin k, G.lab i i = Label.strict

instance (G : SCG nf k) : Decidable G.HasStrictSelfArc :=
  inferInstanceAs (Decidable (∃ i : Fin k, G.lab i i = Label.strict))

/-- `G` has some self-arc `(i, i)`, strict or nonstrict. -/
def HasSelfArc (G : SCG nf k) : Prop := ∃ i : Fin k, G.lab i i ≠ Label.absent

instance (G : SCG nf k) : Decidable G.HasSelfArc :=
  inferInstanceAs (Decidable (∃ i : Fin k, G.lab i i ≠ Label.absent))

end SCG

/-- An abstract program: the list of its call sites, each described by a size-change graph.
(Several call sites may connect the same pair of functions.) -/
structure Prog (nf k : Nat) where
  calls : List (SCG nf k)

/-- The composition closure of a program's graphs with respect to the sequencing `sq`: the least
set containing every call-site graph and closed under composing `G` with `H` whenever
`G.dst = H.src`. With `sq = Label.seq` this is the closure of Lee, Jones and Ben-Amram. -/
inductive InClosureWith {nf k : Nat} (sq : Label → Label → Label) (P : Prog nf k) :
    SCG nf k → Prop where
  | gen {G : SCG nf k} : G ∈ P.calls → InClosureWith sq P G
  | comp {G H : SCG nf k} : InClosureWith sq P G → InClosureWith sq P H → G.dst = H.src →
      InClosureWith sq P (G.compWith sq H)

/-- The standard composition closure (with strictness-tracking composition). -/
abbrev InClosure {nf k : Nat} (P : Prog nf k) : SCG nf k → Prop := InClosureWith Label.seq P

/-- The closure criterion relative to a sequencing `sq`: every graph `G` in the closure that is a
loop (`G.src = G.dst`) and idempotent (`G ; G = G`, composition taken with `sq`) has a strict
self-arc. -/
def CriterionWith {nf k : Nat} (sq : Label → Label → Label) (P : Prog nf k) : Prop :=
  ∀ G : SCG nf k, InClosureWith sq P G → G.src = G.dst → G.compWith sq G = G → G.HasStrictSelfArc

/-- **The size-change closure criterion** (Lee, Jones and Ben-Amram): every idempotent loop graph
`G = G ; G` in the composition closure of the program's graphs has a strict self-arc
`(i, i, <)`. -/
def ClosureCriterion {nf k : Nat} (P : Prog nf k) : Prop := CriterionWith Label.seq P

/-- The closure criterion weakened to accept nonstrict self-arcs: every idempotent loop graph in
the closure has some self-arc `(i, i, ≤ or <)`. Not sufficient for termination
(see `stall_weakSelfArcCriterion_counterexample`). -/
def WeakSelfArcCriterion {nf k : Nat} (P : Prog nf k) : Prop :=
  ∀ G : SCG nf k, InClosure P G → G.src = G.dst → G.comp G = G → G.HasSelfArc

/-- The closure criterion checked on the call-site graphs only, without forming the closure:
every idempotent loop among the generators has a strict self-arc. Not sufficient for termination
(see `alt_generatorCriterion_counterexample`). -/
def GeneratorCriterion {nf k : Nat} (P : Prog nf k) : Prop :=
  ∀ G ∈ P.calls, G.src = G.dst → G.comp G = G → G.HasStrictSelfArc

/-- The closure criterion without the loop guard: every idempotent graph in the closure, loop or
not, has a strict self-arc. Rejects the non-recursive `acycProg` (see
`loop_guard_needed_for_converse`). -/
def NoLoopGuardCriterion {nf k : Nat} (P : Prog nf k) : Prop :=
  ∀ G : SCG nf k, InClosure P G → G.comp G = G → G.HasStrictSelfArc

/-- The closure criterion without the idempotence condition: every loop graph in the closure has a
strict self-arc. Rejects the size-change terminating `swapDec` (see
`idempotence_needed_for_converse`). -/
def AllLoopsCriterion {nf k : Nat} (P : Prog nf k) : Prop :=
  ∀ G : SCG nf k, InClosure P G → G.src = G.dst → G.HasStrictSelfArc

/-- A finite list of graphs that contains the generators and is closed under composition of
composable pairs contains the whole closure. (Helper; used to compute concrete closures.) -/
theorem inClosureWith_mem_of_closed {nf k : Nat} {sq : Label → Label → Label} {P : Prog nf k}
    {S : List (SCG nf k)} (hgen : ∀ G ∈ P.calls, G ∈ S)
    (hcl : ∀ G ∈ S, ∀ H ∈ S, G.dst = H.src → G.compWith sq H ∈ S) :
    ∀ {G : SCG nf k}, InClosureWith sq P G → G ∈ S := by
  intro G hG
  induction hG with
  | gen h => exact hgen _ h
  | comp _ _ hdst ihG ihH => exact hcl _ ihG _ ihH hdst

/-- A criterion relative to `sq` holds as soon as every loop in a composition-closed list that
contains the generators passes the idempotent test. (Helper for concrete programs.) -/
theorem criterionWith_of_closed {nf k : Nat} {sq : Label → Label → Label} {P : Prog nf k}
    (S : List (SCG nf k)) (hgen : ∀ G ∈ P.calls, G ∈ S)
    (hcl : ∀ G ∈ S, ∀ H ∈ S, G.dst = H.src → G.compWith sq H ∈ S)
    (hS : ∀ G ∈ S, G.src = G.dst → G.compWith sq G = G → G.HasStrictSelfArc) :
    CriterionWith sq P :=
  fun _ hG => hS _ (inClosureWith_mem_of_closed hgen hcl hG)

end Toy.SCT
