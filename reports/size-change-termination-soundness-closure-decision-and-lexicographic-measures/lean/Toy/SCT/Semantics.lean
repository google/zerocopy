/-
Toy.SCT.Semantics
=================

What a size-change graph says about real calls, infinite call sequences, the thread-based
size-change termination property, and lexicographic measures built from parameter projections.
-/
import Toy.SCT.Graph

namespace Toy.SCT

variable {nf k : Nat}

/-- `RespectsIn G u v`: passing argument vector `v` to the callee, from a caller whose parameter
vector is `u`, is consistent with every arc of `G`: a strict arc `(i, j)` forces `v j < u i` and a
nonstrict arc forces `v j ≤ u i`. Values live in any type `α` with `<` and `≤`; the termination
results use `α = Nat`. No axioms relating `<` and `≤` on `α` are assumed; soundness over another
type would need well-foundedness and the compatibility laws (`a < b ≤ c → a < c`, `a ≤ b < c →
a < c`) that hold in `Nat`. -/
def RespectsIn {α : Type} [LT α] [LE α] (G : SCG nf k) (u v : Fin k → α) : Prop :=
  ∀ i j : Fin k, (G.lab i j = Label.strict → v j < u i) ∧ (G.lab i j = Label.nonstrict → v j ≤ u i)

/-- `RespectsIn` over natural-number argument values. -/
abbrev Respects (G : SCG nf k) (u v : Fin k → Nat) : Prop := RespectsIn G u v

instance instDecidableRespectsNat {G : SCG nf k} {u v : Fin k → Nat} :
    Decidable (RespectsIn G u v) :=
  inferInstanceAs (Decidable (∀ i j : Fin k,
    (G.lab i j = Label.strict → v j < u i) ∧ (G.lab i j = Label.nonstrict → v j ≤ u i)))

/-- An infinite call sequence consistent with the program's graphs, with argument values in `α`:
functions `fs n`, argument vectors `vs n`, and for each step a call-site graph `Gs n` of the
program going from `fs n` to `fs (n+1)` that the step respects. -/
def ConsistentRunIn (α : Type) [LT α] [LE α] (P : Prog nf k) : Prop :=
  ∃ (fs : Nat → Fin nf) (vs : Nat → Fin k → α) (Gs : Nat → SCG nf k),
    ∀ n, Gs n ∈ P.calls ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧
      RespectsIn (Gs n) (vs n) (vs (n + 1))

/-- A consistent call sequence over `Nat` of `len` steps starting in function `f` with argument
vector `u`. -/
def FiniteRunFrom (P : Prog nf k) (f : Fin nf) (u : Fin k → Nat) (len : Nat) : Prop :=
  ∃ (fs : Nat → Fin nf) (vs : Nat → Fin k → Nat) (Gs : Nat → SCG nf k),
    fs 0 = f ∧ vs 0 = u ∧
    ∀ n, n < len → Gs n ∈ P.calls ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧
      Respects (Gs n) (vs n) (vs (n + 1))

/-- A program state: the current function and its argument vector over `Nat`. -/
abbrev State (nf k : Nat) := Fin nf × (Fin k → Nat)

/-- A semantic model of calls (`step s t`: state `s` calls state `t`) is described by the program's
graphs: every call it makes is justified by some call-site graph with matching endpoints that the
call respects. This is the "graphs are sound for the real calls" obligation. -/
def StepRespects (P : Prog nf k) (step : State nf k → State nf k → Prop) : Prop :=
  ∀ s t, step s t → ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧ Respects G s.2 t.2

/-- A call relation terminates: there is no infinite sequence of states each calling the next. -/
def Terminates {σ : Type} (step : σ → σ → Prop) : Prop :=
  ¬ ∃ s : Nat → σ, ∀ n, step (s n) (s (n + 1))

/-- The most permissive semantic model described by the program's graphs: a state may call any
state that some call-site graph with matching endpoints justifies. -/
def runStep (P : Prog nf k) : State nf k → State nf k → Prop :=
  fun s t => ∃ G ∈ P.calls, G.src = s.1 ∧ G.dst = t.1 ∧ Respects G s.2 t.2

/-- An infinite path through the program's call sites: each graph is a call-site graph and the
callee of each is the caller of the next. (No values are involved.) -/
def IsCallPath (P : Prog nf k) (Gs : Nat → SCG nf k) : Prop :=
  ∀ n, Gs n ∈ P.calls ∧ (Gs n).dst = (Gs (n + 1)).src

/-- An infinitely descending thread in a sequence of graphs: from some position `n0` on, a choice
of parameter `p n` at each position such that every arc `(p n, p (n+1))` of `Gs n` is present, and
infinitely many of these arcs are strict. -/
def HasInfDescThread (Gs : Nat → SCG nf k) : Prop :=
  ∃ (n0 : Nat) (p : Nat → Fin k),
    (∀ n, n0 ≤ n → (Gs n).lab (p n) (p (n + 1)) ≠ Label.absent) ∧
    (∀ N, ∃ n, N ≤ n ∧ n0 ≤ n ∧ (Gs n).lab (p n) (p (n + 1)) = Label.strict)

/-- **Size-change termination** (Lee, Jones and Ben-Amram, Definition 11, in the unrooted form of
Ben-Amram, LMCS 2010): every infinite path through the program's call sites, starting at any
function, has an infinitely descending thread. -/
def SizeChangeTerminating (P : Prog nf k) : Prop :=
  ∀ Gs : Nat → SCG nf k, IsCallPath P Gs → HasInfDescThread Gs

/-- Strict lexicographic order on `L`-tuples of naturals: at the first differing position the
left tuple is smaller. -/
def LexLt {L : Nat} (a b : Fin L → Nat) : Prop :=
  ∃ l : Fin L, (∀ i : Fin L, i.val < l.val → a i = b i) ∧ a l < b l

instance instDecidableLexLt {L : Nat} {a b : Fin L → Nat} : Decidable (LexLt a b) :=
  inferInstanceAs (Decidable (∃ l : Fin L, (∀ i : Fin L, i.val < l.val → a i = b i) ∧ a l < b l))

/-- A lexicographic measure built from parameter projections decreases on every call: the measure
of function `f` is the tuple `(u (ord f 0), …, u (ord f (L-1)))` of its argument values, and for
every call-site graph `G` and all argument vectors `u` (caller) and `v` (callee) that respect `G`,
the callee's measure is lexicographically smaller than the caller's. All functions use tuples of
the same length `L`; components may repeat parameters. The decrease is required on every single
call site (not only around cycles), and a projection onto an arc-free padding slot of the callee
is unconstrained. -/
def LexProjDecreases (P : Prog nf k) {L : Nat} (ord : Fin nf → Fin L → Fin k) : Prop :=
  ∀ G ∈ P.calls, ∀ u v : Fin k → Nat, Respects G u v →
    LexLt (fun l => v (ord G.dst l)) (fun l => u (ord G.src l))

end Toy.SCT
