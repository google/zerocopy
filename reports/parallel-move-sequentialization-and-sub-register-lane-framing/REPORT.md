# Parallel-move sequentialization and sub-register lane framing (Lean 4 toy models)

## Summary

This package mechanizes in Lean 4 (core library and `Std` only) two small theories used when a
compiler turns a *parallel move* into machine instructions. The first is the parallel move
itself: a list of `(destination, source)` copies between locations of a store `Loc → V` that
are meant to happen simultaneously, its readings when a destination repeats, its sequential
realizations (topological orders, one scratch location, swaps, xor-swaps), and lower bounds and
impossibility results for an isolated cycle. The second is sub-register *lanes*: bit ranges of an
`n`-bit word, written either by a preserve-upper write (`putLane`, the other bits are kept) or by
a zero-extending write (`writeZext`, the whole word is replaced), with their lens laws,
commutation and framing conditions, and parallel moves between lanes. There are 21 results.
Model–system relation: none proved (no theorem relates these models to CompCert's or CakeML's
parallel-move definitions or to x86-64 or AArch64 register semantics). All are theorems about
these toy models; these theorems neither establish nor refute the corresponding claims about a
production compiler or about x86-64 or AArch64 hardware, and every connection to them is a
separately labelled modeling bridge under **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The results (the plain-language claim of each card, verbatim):

1. **`pmove-readings-disagree-on-repeated-destination`** (T0, counterexample). For the move list [(0,1),(0,2)] (destination 0 listed twice with sources 1 and 2) and the identity store on Nat, the first-entry reading of the parallel move puts the old value of 1 at 0 and the last-entry reading puts the old value of 2 at 0, so the two readings disagree; the package adopts the first-entry reading pmove and intends it only for well-formed (distinct-destination) moves.

2. **`pmove-order-independent-iff-functional`** (T1, characterization). (a) Over a value type with two distinct values a ≠ b, the parallel-move semantics pmove M is unchanged on every store by every reordering of M if and only if M is functional (entries with the same destination have the same source location). (b) The direction 'functional implies order-independent' needs no hypothesis on the value type: if M is functional and M' is a reordering of M, then pmove M σ = pmove M' σ for every store σ; in particular the first-entry and last-entry readings coincide on functional M. (c) For one fixed store σ, pmove M σ is unchanged by every reordering of M if and only if entries with the same destination read equal values in σ (FunctionalAt σ M), with no hypothesis on the value type.

3. **`sequentialize-sound-off-scratch`** (T1, theorem). For a functional parallel move M (in particular a well-formed one) and a scratch location tmp that is not simultaneously a destination and a source of M, running the move list sequentialize tmp M from any store σ gives, at every location other than tmp, exactly the value pmove M σ prescribes.

4. **`sequential-composition-of-move-blocks`** (T1, theorem). If a move list ms1 realizes the parallel move M1 and ms2 realizes M2 (each at every location other than one shared scratch location tmp, from every store), the two blocks have disjoint destinations, no source of M2 is a destination of M1, and tmp is not a source of M2, then ms1 ++ ms2 realizes M1 ++ M2 at every location other than tmp, from every store.

5. **`topological-order-realizes-parallel-move`** (T1, theorem). A functional list of moves in which no move overwrites the source of a later move (a topological order), executed left to right with no scratch location, produces exactly, at every location and from every store, the parallel reading of the same list.

6. **`cycle-with-scratch-upper-bound`** (T0, theorem). For a nonempty duplicate-free cycle l0, ..., l(k-1) with k ≥ 1 (each l(i+1) receives the old value of l(i), and l0 receives the old value of l(k-1)) and a scratch location tmp outside it, the k + 1 moves tmp := l(k-1); l(k-1) := l(k-2); ...; l1 := l0; l0 := tmp realize the cycle at every location other than tmp, from every store.

7. **`cycle-with-scratch-lower-bound`** (T1, theorem). Let ls be an isolated duplicate-free cycle of length k ≥ 2 (the parallel move consists of exactly the cycle's moves cycleMoves ls) and tmp a location outside it. (a) Every sequence of plain moves (over any locations) that, from a given injective store σ, produces the cycle's target at every location other than tmp has at least k + 1 moves. (b) Over any value type with two distinct values, every sequence of plain moves that produces the cycle's target at every location other than tmp from every store has at least k + 1 moves.

8. **`cycle-without-scratch-impossible`** (T1, impossibility). Let ls be an isolated duplicate-free cycle of length k ≥ 2, that is, the parallel move consists of exactly the cycle's moves cycleMoves ls, so its target leaves every location outside ls unchanged (for example a parallel swap [(a,b),(b,a)] with a ≠ b). (a) For a given injective store σ, no sequence of plain moves, over any locations, turns σ exactly (at every location) into the cycle's target. (b) Over any location type and any value type with two distinct values, no single sequence of plain moves turns every store exactly into the cycle's target.

9. **`cycle-with-swaps-upper-bound`** (T0, theorem). For a duplicate-free cycle l0, ..., l(k-1), the swaps (l0,l1), (l0,l2), ..., (l0,l(k-1)), executed in order, realize the cycle exactly at every location, from every store; there are ls.length - 1 of them, which is k - 1 for k ≥ 1 and 0 for the empty list (truncated subtraction).

10. **`cycle-with-swaps-lower-bound`** (T0, theorem). Let ls be an isolated duplicate-free cycle of length k (the parallel move consists of exactly the cycle's moves cycleMoves ls). (a) Every list of swaps (over any locations) that turns a given injective store σ exactly into the cycle's target has at least ls.length - 1 swaps. (b) Over a value type with two distinct values, every list of swaps that turns every store exactly into the cycle's target has at least ls.length - 1 swaps. (ls.length - 1 is k - 1 for k ≥ 1 and 0 for k = 0.)

11. **`xor-swap-correct-iff-distinct-or-zero`** (T0, characterization). Over w-bit words, the sequence a ^= b; b ^= a; a ^= b exchanges the contents of locations a and b when a ≠ b, and when a = b it sets that location to zero and leaves all others unchanged; hence it equals the true swap exactly when a ≠ b or the aliased (common) operand holds zero.

12. **`xor-swap-sequences-sound-without-self-swaps`** (T0, theorem). A list of swaps none of which is a self-swap behaves the same, on every store of w-bit words, whether each swap is a true exchange or the xor-swap idiom; in particular the xor-swap implementation of the cycle swaps cycleSwaps ls realizes a duplicate-free cycle ls exactly.

13. **`preserve-upper-lane-write-is-very-well-behaved-lens`** (T1, theorem). For a lane (off, wid) that fits in an n-bit register (off + wid ≤ n), reading the lane (getLane) and writing it while preserving all other bits (putLane) form a very well-behaved lens: GetPut, PutGet and PutPut hold. GetPut and PutPut hold even without the fit condition; only PutGet (and hence very-well-behavedness) uses it.

14. **`disjoint-lane-writes-commute-and-frame`** (T1, theorem). Writes to two lanes with disjoint bit ranges (one of them empty, or one ending before the other begins) commute, and writing one of them does not change what the other reads; neither statement needs the lanes to fit in the register.

15. **`lane-writes-commute-iff-disjoint`** (T1, characterization). (a) For any two lanes and any register width n, all pairs of preserve-upper writes to the two lanes commute if and only if the lanes share no bit position below n. (b) If at least one of the two lanes fits in the n-bit register, all pairs of writes commute if and only if the lanes are Disjoint (disjoint bit ranges).

16. **`zero-extend-write-not-a-narrow-lens`** (T1, impossibility). If wid < n, no getter whatsoever from n-bit words to wid-bit values makes the zero-extending write (which replaces the whole word by the zero-extended value) satisfy GetPut; in particular it is not a lens on the full word with a wid-bit view.

17. **`zero-extend-write-getput-iff-upper-bits-zero`** (T1, characterization). Writing back the low wid bits of an n-bit word w with a zero-extending write leaves w unchanged if and only if every bit of w at a position ≥ wid is zero.

18. **`zero-extend-write-is-full-word-replacement`** (T0, theorem). A zero-extending write writeZext n v of a wid-bit value equals the full-width lane write (0, n) of v.setWidth n (the zero-extended value when wid ≤ n, the truncated value when wid > n), and the full-width lane is a very well-behaved lens; with the low-lane getter (0, wid), the zero-extending write satisfies PutGet when wid ≤ n and PutPut always.

19. **`distinct-lane-destinations-not-enough`** (T0, counterexample). With registers indexed by Nat, 16-bit words, and the register file regs16 (register 0 holds 0x1234, register 1 holds 0xABCD, all others 0), the parallel lane move M = [lm 0 0 1 0 8, lm 0 0 2 0 16] (write register 1's low byte into register 0's low byte, and register 2's low 16 bits into register 0's low 16 bits) has distinct (register, lane) destinations, violates LaneWF, and its two orders give different values in register 0. This one instance shows that distinct (register, lane) destinations (DistinctDstLanes) do not imply LaneWF and do not make the parallel lane move independent of the order of the list; it does not show which condition suffices (see the non-claims).

20. **`lane-parallel-move-order-independent-for-disjoint-lanes`** (T1, theorem). If the destination lanes of lane moves into the same register are pairwise disjoint (LaneWF M) and M' is a reordering of M, then the parallel lane-move semantics (all sources read from the old register file, then all destination lanes written) of M and M' agree on every register file.

21. **`lane-parallel-move-sound-for-disjoint-lanes-topological-order`** (T1, theorem). If a parallel lane move M has pairwise disjoint destination lanes per register (LaneWF M) and ms is a reordering of M in which no move writes bits that a later move reads (LaneTopological ms), then executing ms sequentially yields exactly the parallel lane move M, on every register file.

The non-claims of every result are listed first under **Boundaries**; read them before relying
on a result. In particular: no move-count formula for general parallel moves is proved (only one
isolated cycle is analysed); the injective-store statements are vacuous when the location type
is larger than the value type, and the uniform (all-stores) statements are the ones to use there;
the lane results model only preserve-upper and whole-word zero-extending writes, with no operand
encodability, flags, or timing.

## Applicability

**What is modeled.** Toy models throughout, in namespace `Toy.ParMove`:

- *Stores and moves.* Locations are an arbitrary type `Loc` with decidable equality; a store is a
  total function `Loc → V`. A move is a pair `(dst, src)`. CompCert's `lib/Parmov.v`,
  Rideau–Serpette–Leroy and Boissinot et al. write moves source first, `(src, dst)`; CakeML's
  `parmoveScript.sml` writes `(dst, src)` as here. A sequential move `dst := src` reads the
  current store; the parallel move `pmove` reads the old store for every destination, and for a
  repeated destination the first entry wins (a competing last-entry reading `pmoveLast` is also
  defined).
- *Registers and lanes.* A register is a word `BitVec n`; a lane is a contiguous bit range
  `(off, wid)`. A preserve-upper write replaces exactly the lane's bits below `n`; a
  zero-extending write replaces the whole word by `v.setWidth n` (zero-extension when `wid ≤ n`,
  truncation when `wid > n`). Lane moves copy `wid` bits between lanes of registers indexed by an
  arbitrary type with decidable equality, always with preserve-upper writes.
- *Lens laws.* GetPut, PutGet, PutPut and "very well-behaved" are defined locally for total
  functions, following Foster et al. (TOPLAS 2007, Section 3). General lens frame laws, lens
  independence and product decompositions are outside the scope of this package; only the
  instances for bit-lane reads and writes are studied.

**What real systems the definitions are meant to capture.** (1) The parallel copies that register
allocators and out-of-SSA translation must sequentialize (phi-resolution copies, calling-convention
shuffles), as treated by Rideau–Serpette–Leroy (JAR 2008), CompCert's `lib/Parmov.v`, CakeML's
`parmoveScript.sml`, and Boissinot et al. (CGO 2009). (2) Partial writes to general-purpose
sub-registers on x86-64 (8-bit and 16-bit writes keep the other bits; 32-bit writes zero-extend
into the 64-bit register) and AArch64 (a `W`-register write zeroes the top 32 bits of the 64-bit
register). These correspondences are modeling bridges (`derived`), stated under **Findings**
with their reasoning; they are not kernel-checked.

**Known gaps.** No register classes (integer versus floating-point) and a single untyped scratch
location; no memory operands, stack slots of different sizes, flags, liveness, timing,
partial-register stalls, vector registers, or cost model; no instruction encodability (which
lanes of which registers exist as operands, REX restrictions, which combinations one instruction
can encode); overlap between distinct whole-register names (for example `al` and `ax` as separate
locations) is not modeled in the whole-register part, only in the lane part; no production
compiler's algorithm is modeled (the sequentialization studied is the ready-first strategy
credited to May, not the stack-based algorithm verified by Rideau–Serpette–Leroy and not Boissinot
et al.'s Algorithm 1); no sequentialization algorithm for lane moves is given.

**How the subjects relate.** The Lean toolchain is the checker of every theorem. All other
subjects are prior art or targets of the modeling bridges: the three papers (Rideau–Serpette–Leroy,
Boissinot et al., Foster et al.), the two proof-assistant sources (CompCert, CakeML), Warren's
*Hacker's Delight* (2nd edition, Section 2-20; the prior art of the xor-swap results 11 and 12),
the Archive of Formal Proofs entry *Optics* (general lens theory in Isabelle/HOL, compared with the
lane-lens results 13 to 15), and the two architecture documents. The results are compared with
them, not derived from them, and nothing in them is re-verified here beyond the quoted passages.
The *Optics* entry is a maintained archive entry first published on May 25, 2017; only its entry
page and abstract were read, and no fixed revision of it is relied on. The Intel manual is
identified by order number and section title only: its section body was not retrieved, and the
behaviour relied on is a paraphrase (see **Evidence**).

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib and no other Lake dependency. The Lake
project is `lean/` (library `ToyParMove`, 11 modules).

## Findings

**Evidence roles.** Each result below is a set of theorems checked by the Lean kernel under the
toolchain named in **Applicability**; this is recorded as `Basis: execution (Lean kernel check)`.
Any statement connecting a result to a compiler or to x86-64 or AArch64 is a separate claim
recorded as `Basis: derived (modeling bridge)`, with its reasoning; it is not kernel-checked and
holds only to the extent that the toy definitions capture the real systems (see the gaps listed in
**Applicability**). "Proved" in this report never means "true of a real compiler or processor".

**How to read a card.** *Tier* is `T0` (a known result restated for the toy) or `T1` (folklore
made precise); no result is claimed novel. The *Lean statement* is quoted verbatim from the source
(proofs omitted); section variables `{Loc V : Type} [DecidableEq Loc]` (in the lane-move file
`{R : Type} [DecidableEq R] {n : Nat}`, in the lane file `{n : Nat}` and, for the lens laws,
`{S A : Type}`, in the xor file `{Loc : Type} [DecidableEq Loc] {w : Nat}`) are implicit binders of every statement that mentions them. The *reading with key
definitions unfolded* restates all theorems of the card compactly. The *hypothesis ledger* lists
every hypothesis with its purpose and tightness; `tight` means a named Lean counterexample proves
that all other hypotheses hold and the conclusion fails (the counterexample statements are quoted
verbatim after the cards). Bundled cards record which theorems a hypothesis applies to. *Depth* is
`definitional`, `shallow` or `substantive`. The *non-vacuity witness* is a proved instance
satisfying all hypotheses. For impossibility results, *positive controls* are proved nearby
settings where the conclusion fails. Each card's non-claims are listed under **Boundaries**.

Moves are written `(dst, src)` throughout; a list `[(1,2),(2,1)]` exchanges locations 1 and 2.

### Definitions (key definitions unfolded)

Core definitions in simplified notation (the exact source is in `lean/ToyParMove/`; each definition has proved positive and negative examples, whose statements are quoted verbatim after each block).

#### Stores and moves (`lean/ToyParMove/Basic.lean`, `lean/ToyParMove/Readings.lean`)

```lean
def upd (σ : Loc → V) (d : Loc) (v : V) : Loc → V := fun l => if l = d then v else σ l
def dsts (M : List (Loc × Loc)) : List Loc := M.map Prod.fst
def srcs (M : List (Loc × Loc)) : List Loc := M.map Prod.snd

-- first-match source lookup
def lookupSrc : List (Loc × Loc) → Loc → Option Loc
  | [], _ => none
  | m :: M, l => if l = m.1 then some m.2 else lookupSrc M l

-- adopted parallel-move semantics: every destination gets the OLD value of its source;
-- for a repeated destination the first entry wins (intended only for well-formed moves)
def pmove (M) (σ : Loc → V) : Loc → V :=
  fun l => match lookupSrc M l with | some s => σ s | none => σ l

def pmoveLast (M) (σ) := pmove M.reverse σ          -- competing "last entry wins" reading
def WellFormed (M) : Prop := (dsts M).Nodup           -- distinct destinations
def Functional (M) : Prop := ∀ d s₁ s₂, (d, s₁) ∈ M → (d, s₂) ∈ M → s₁ = s₂
def FunctionalAt (σ : Loc → V) (M) : Prop :=          -- equal source VALUES at one store
  ∀ d s₁ s₂, (d, s₁) ∈ M → (d, s₂) ∈ M → σ s₁ = σ s₂

def seqStep (σ) (m : Loc × Loc) := upd σ m.1 (σ m.2)  -- dst := src, reading the CURRENT store
def runSeq (ms) (σ) := ms.foldl seqStep σ              -- left-to-right execution
```

Examples (each proved; statements quoted verbatim, proofs omitted):

```lean
-- lean/ToyParMove/Readings.lean:18-21
-- lean/ToyParMove/Readings.lean — Positive example (pmove)
theorem pmove_swap_example :
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 0 = 1 ∧
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 1 = 0 ∧
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 2 = 2

-- lean/ToyParMove/Readings.lean:25-27
-- lean/ToyParMove/Readings.lean — Negative example (pmove)
theorem pmove_rejects_sequential_reading :
    pmove [(1, 0), (2, 1)] (id : Nat → Nat) 2 = 1 ∧
    runSeq [(1, 0), (2, 1)] (id : Nat → Nat) 2 = 0

-- lean/ToyParMove/Readings.lean:30
-- lean/ToyParMove/Readings.lean — Positive example (WellFormed)
theorem wellFormed_swap_example : WellFormed [((0 : Nat), (1 : Nat)), (1, 0)]

-- lean/ToyParMove/Readings.lean:33-34
-- lean/ToyParMove/Readings.lean — Negative example (WellFormed)
theorem not_wellFormed_repeated_destination :
    ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 2)]

-- lean/ToyParMove/Readings.lean:38-39
-- lean/ToyParMove/Readings.lean — Positive example (Functional)
theorem functional_duplicate_not_wellFormed :
    Functional [((0 : Nat), (1 : Nat)), (0, 1)] ∧ ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 1)]

-- lean/ToyParMove/Readings.lean:46
-- lean/ToyParMove/Readings.lean — Negative example (Functional)
theorem not_functional_two_sources : ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)]

-- lean/ToyParMove/Readings.lean:80-82
-- lean/ToyParMove/Readings.lean — Positive example (FunctionalAt)
theorem functionalAt_equal_values_example :
    FunctionalAt (fun l : Nat => if l = 2 then 1 else l) [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)]

-- lean/ToyParMove/Readings.lean:90-91
-- lean/ToyParMove/Readings.lean — Negative example (FunctionalAt)
theorem not_functionalAt_id_example :
    ¬ FunctionalAt (id : Nat → Nat) [((0 : Nat), (1 : Nat)), (0, 2)]

-- lean/ToyParMove/Readings.lean:52-54
-- lean/ToyParMove/Readings.lean — Positive example (runSeq)
theorem runSeq_swap_via_scratch_example :
    runSeq [(2, 0), (0, 1), (1, 2)] (id : Nat → Nat) 0 = 1 ∧
    runSeq [(2, 0), (0, 1), (1, 2)] (id : Nat → Nat) 1 = 0

-- lean/ToyParMove/Readings.lean:58-59
-- lean/ToyParMove/Readings.lean — Negative example (runSeq)
theorem runSeq_naive_swap_fails :
    runSeq [(0, 1), (1, 0)] (id : Nat → Nat) 1 = 1
```

Plain moves and parallel moves only relocate values: `runSeq ms (f ∘ τ) = f ∘ runSeq ms τ` and
`pmove M (f ∘ τ) = f ∘ pmove M τ` (`runSeq_comp`, `pmove_comp`). Hence a realization checked on
the identity store on locations holds on every store (`runSeq_eq_pmove_of_id`), and over a value
type with two distinct values a realization on every store holds on the identity store
(`runSeq_eq_pmove_at_id_of_forall`); this is how the uniform (all-stores) bounds reduce to the
injective-store bounds. The four lemmas, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Basic.lean:163-164
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_comp {W : Type} (f : V → W) : ∀ (ms : List (Loc × Loc)) (τ : Loc → V),
    runSeq ms (f ∘ τ) = f ∘ runSeq ms τ

-- lean/ToyParMove/Basic.lean:169-170
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem pmove_comp {W : Type} (f : V → W) (M : List (Loc × Loc)) (τ : Loc → V) :
    pmove M (f ∘ τ) = f ∘ pmove M τ

-- lean/ToyParMove/Basic.lean:187-188
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_eq_pmove_of_id {ms M : List (Loc × Loc)}
    (h : runSeq ms (id : Loc → Loc) = pmove M id) (σ : Loc → V) : runSeq ms σ = pmove M σ

-- lean/ToyParMove/Basic.lean:203-205
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_eq_pmove_at_id_of_forall {ms M : List (Loc × Loc)} {l : Loc} (a b : V)
    (hab : a ≠ b) (h : ∀ σ : Loc → V, runSeq ms σ l = pmove M σ l) :
    runSeq ms (id : Loc → Loc) l = pmove M id l
```

#### The sequentialization (`lean/ToyParMove/Sequentialize.lean`)

```lean
def renameSrc (d t) (P) := P.map fun m => (m.1, if m.2 = d then t else m.2)
def isReady (P) (m) : Bool := decide (m.1 ∉ srcs P)    -- nobody pending reads m's destination

def seqLoop (tmp : Loc) : List (Loc × Loc) → List (Loc × Loc)
  | [] => []
  | m :: rest =>
    match (m :: rest).find? (isReady (m :: rest)) with
    | some r => r :: seqLoop tmp ((m :: rest).erase r)                      -- emit a ready move
    | none   => (tmp, m.1) :: m :: seqLoop tmp (renameSrc m.1 tmp rest)    -- break a cycle
  -- terminates: the pending list shrinks by one each step

def sequentialize (tmp : Loc) (M) := seqLoop tmp (M.filter fun m => decide (m.1 ≠ m.2))
```

This is the strategy credited to May (1989) by Rideau–Serpette–Leroy and by Boissinot et al.
(emit moves whose destination is no longer read; break each remaining cycle with one temporary),
not the stack-based algorithm verified by Rideau–Serpette–Leroy and not Boissinot et al.'s
Algorithm 1 (which reuses an existing copy of a cycle value when there is one).

Examples (each proved; statements quoted verbatim, proofs omitted):

```lean
-- lean/ToyParMove/Sequentialize.lean:294
-- lean/ToyParMove/Sequentialize.lean — Positive example (isReady)
theorem isReady_example : isReady [((1 : Nat), (2 : Nat)), (3, 0)] (3, 0) = true

-- lean/ToyParMove/Sequentialize.lean:297
-- lean/ToyParMove/Sequentialize.lean — Negative example (isReady)
theorem not_isReady_example : isReady [((1 : Nat), (2 : Nat)), (2, 1)] (1, 2) = false

-- lean/ToyParMove/Sequentialize.lean:301-302
-- lean/ToyParMove/Sequentialize.lean — Positive example (sequentialize)
theorem sequentialize_swap_example :
    sequentialize (9 : Nat) [(1, 2), (2, 1)] = [(9, 1), (1, 2), (2, 9)]

-- lean/ToyParMove/Sequentialize.lean:306-307
-- lean/ToyParMove/Sequentialize.lean — Positive example (sequentialize)
theorem sequentialize_chain_example :
    sequentialize (9 : Nat) [(0, 0), (1, 0), (2, 1)] = [(2, 1), (1, 0)]

-- lean/ToyParMove/Sequentialize.lean:311-312
-- lean/ToyParMove/Sequentialize.lean — Non-claim witness (sequentialize does not deduplicate)
theorem sequentialize_emits_duplicates_example :
    sequentialize (9 : Nat) [(0, 1), (0, 1), (1, 0)] = [(9, 0), (0, 1), (0, 1), (1, 9)]
```

#### Order, cycles, swaps, xor-swap (`lean/ToyParMove/Necessity.lean`, `lean/ToyParMove/Cycles.lean`, `lean/ToyParMove/Swaps.lean`, `lean/ToyParMove/XorSwap.lean`)

```lean
def Topological (ms) : Prop := ms.Pairwise fun earlier later => earlier.1 ≠ later.2

def chain : Loc → List Loc → List (Loc × Loc)          -- [(y₁,h),(y₂,y₁),…]
  | _, [] => []
  | h, y :: ys => (y, h) :: chain y ys
def cycleMoves : List Loc → List (Loc × Loc)           -- l(i+1) ← l(i), l₀ ← l(k-1)
  | [] => []
  | l₀ :: rest => (l₀, rest.getLastD l₀) :: chain l₀ rest
def cycleSeqScratch (tmp) : List Loc → List (Loc × Loc)
  | [] => []
  | l₀ :: rest => (tmp, rest.getLastD l₀) :: (chain l₀ rest).reverse ++ [(l₀, tmp)]

def swapStore (σ) (a b) := fun l => if l = a then σ b else if l = b then σ a else σ l
def runSwaps (ss) (σ) := ss.foldl (fun τ p => swapStore τ p.1 p.2) σ
def cycleSwaps : List Loc → List (Loc × Loc)
  | [] => [] | l₀ :: rest => rest.map fun x => (l₀, x)

def xorAssign (σ : Loc → BitVec w) (a b) := upd σ a (σ a ^^^ σ b)              -- a ^= b
def xorSwap (σ) (a b) := xorAssign (xorAssign (xorAssign σ a b) b a) a b       -- a^=b; b^=a; a^=b
def runXorSwaps (ss) (σ) := ss.foldl (fun τ p => xorSwap τ p.1 p.2) σ
```

Examples (each proved; statements quoted verbatim, proofs omitted):

```lean
-- lean/ToyParMove/Necessity.lean:293
-- lean/ToyParMove/Necessity.lean — Positive example (Topological)
theorem topological_example : Topological [((2 : Nat), (1 : Nat)), (1, 0)]

-- lean/ToyParMove/Necessity.lean:296
-- lean/ToyParMove/Necessity.lean — Negative example (Topological)
theorem not_topological_example : ¬ Topological [((1 : Nat), (0 : Nat)), (2, 1)]

-- lean/ToyParMove/Cycles.lean:434-437
-- lean/ToyParMove/Cycles.lean — Positive example (cycleMoves)
theorem cycleMoves_example :
    cycleMoves ([0, 1, 2] : List Nat) = [(0, 2), (1, 0), (2, 1)] ∧
    pmove (cycleMoves ([0, 1, 2] : List Nat)) (id : Nat → Nat) 1 = 0 ∧
    pmove (cycleMoves ([0, 1, 2] : List Nat)) (id : Nat → Nat) 1 ≠ 2

-- lean/ToyParMove/Cycles.lean:441-442
-- lean/ToyParMove/Cycles.lean — Negative example (cycleMoves)
theorem cycleMoves_repeated_not_cycle :
    pmove (cycleMoves ([0, 1, 0] : List Nat)) (id : Nat → Nat) 0 = 0

-- lean/ToyParMove/Cycles.lean:445-446
-- lean/ToyParMove/Cycles.lean — Positive example (cycleSeqScratch)
theorem cycleSeqScratch_example :
    cycleSeqScratch (9 : Nat) [0, 1, 2] = [(9, 2), (2, 1), (1, 0), (0, 9)]

-- lean/ToyParMove/Swaps.lean:292-295
-- lean/ToyParMove/Swaps.lean — Positive example (swapStore)
theorem swapStore_example :
    swapStore (id : Nat → Nat) 0 1 0 = 1 ∧ swapStore (id : Nat → Nat) 0 1 1 = 0 ∧
    swapStore (id : Nat → Nat) 0 1 2 = 2 ∧
    swapStore (id : Nat → Nat) 0 1 1 ≠ upd (id : Nat → Nat) 0 1 1

-- lean/ToyParMove/Swaps.lean:299-303
-- lean/ToyParMove/Swaps.lean — Positive example (cycleSwaps, runSwaps)
theorem cycleSwaps_example :
    cycleSwaps ([0, 1, 2] : List Nat) = [(0, 1), (0, 2)] ∧
    (runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 0 = 2 ∧
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 1 = 0 ∧
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 2 = 1)

-- lean/ToyParMove/Swaps.lean:307-309
-- lean/ToyParMove/Swaps.lean — Negative example (runSwaps)
theorem runSwaps_order_matters :
    runSwaps [((0 : Nat), (2 : Nat)), (0, 1)] (id : Nat → Nat) 0 ≠
      runSwaps [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) 0

-- lean/ToyParMove/XorSwap.lean:169-172
-- lean/ToyParMove/XorSwap.lean — Positive example (xorSwap, runXorSwaps)
theorem xorSwap_examples :
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 0 = 0xC3#8 ∧
    runXorSwaps [((0 : Nat), (1 : Nat)), (0, 2)]
      (fun l : Nat => if l = 0 then 1#8 else if l = 1 then 2#8 else 3#8) 0 = 3#8

-- lean/ToyParMove/XorSwap.lean:176-177
-- lean/ToyParMove/XorSwap.lean — Negative example (xorSwap)
theorem xorSwap_alias_example :
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 0#8
```

#### Lanes (`lean/ToyParMove/Lanes.lean`)

```lean
def GetPut (get : S → A) (put : A → S → S) := ∀ s, put (get s) s = s
def PutGet (get) (put) := ∀ a s, get (put a s) = a
def PutPut (_get) (put) := ∀ a a' s, put a' (put a s) = put a' s
def VeryWellBehaved get put := GetPut get put ∧ PutGet get put ∧ PutPut get put

structure Lane where off : Nat; wid : Nat
def Lane.Fits (L) (n) := L.off + L.wid ≤ n
-- disjoint bit sets [off, off+wid) (Lane.disjoint_iff_bits); bits beyond the register count
def Lane.Disjoint (L₁ L₂) :=
  L₁.wid = 0 ∨ L₂.wid = 0 ∨ L₁.off + L₁.wid ≤ L₂.off ∨ L₂.off + L₂.wid ≤ L₁.off
-- no shared bit position below n
def Lane.DisjointIn (n) (L₁ L₂) :=
  ∀ i, i < n → ¬ (L₁.off ≤ i ∧ i < L₁.off + L₁.wid ∧ L₂.off ≤ i ∧ i < L₂.off + L₂.wid)
def laneMask (n) (L) : BitVec n := ((BitVec.allOnes L.wid).setWidth n) <<< L.off
def getLane (L) (w : BitVec n) : BitVec L.wid := w.extractLsb' L.off L.wid
-- preserveUpper write: bit i < n of the result is v[i-off] inside the lane, w[i] outside
def putLane (L) (v : BitVec L.wid) (w : BitVec n) : BitVec n :=
  (w &&& ~~~(laneMask n L)) ||| ((v.setWidth n) <<< L.off)
-- zeroExtend write: the whole word becomes v.setWidth n (zero-extension when wid ≤ n,
-- truncation when wid > n); the old word is ignored
def writeZext (n) (v : BitVec wid) (_w : BitVec n) : BitVec n := v.setWidth n
def laneLow8 : Lane := ⟨0, 8⟩   def laneHigh8 : Lane := ⟨8, 8⟩   def laneLow16 : Lane := ⟨0, 16⟩
def laneLow32 : Lane := ⟨0, 32⟩
```

Bitwise unfolding used throughout (`getLsbD_putLane`), and the bit-set reading of `Lane.Disjoint`
(`Lane.disjoint_iff_bits`), verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:110-112
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem getLsbD_putLane (L : Lane) (v : BitVec L.wid) (w : BitVec n) {i : Nat} (hi : i < n) :
    (putLane L v w).getLsbD i =
      if L.off ≤ i ∧ i < L.off + L.wid then v.getLsbD (i - L.off) else w.getLsbD i

-- lean/ToyParMove/Lanes.lean:67-69
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem Lane.disjoint_iff_bits (L₁ L₂ : Lane) :
    L₁.Disjoint L₂ ↔
      ∀ i, ¬ (L₁.off ≤ i ∧ i < L₁.off + L₁.wid ∧ L₂.off ≤ i ∧ i < L₂.off + L₂.wid)
```

Examples (each proved; statements quoted verbatim, proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:31-32
-- lean/ToyParMove/Lanes.lean — Positive example (VeryWellBehaved)
theorem veryWellBehaved_fst :
    VeryWellBehaved (fun s : Nat × Nat => s.1) (fun a s => (a, s.2))

-- lean/ToyParMove/Lanes.lean:36-37
-- lean/ToyParMove/Lanes.lean — Negative example (VeryWellBehaved, PutGet fails)
theorem not_putGet_constant_put :
    ¬ PutGet (fun s : Nat => s) (fun _ _ => 0)

-- lean/ToyParMove/Lanes.lean:41-42
-- lean/ToyParMove/Lanes.lean — Negative example (VeryWellBehaved)
theorem not_veryWellBehaved_constant_put :
    ¬ VeryWellBehaved (fun s : Nat => s) (fun _ _ => 0)

-- lean/ToyParMove/Lanes.lean:317-318
-- lean/ToyParMove/Lanes.lean — Positive example (putLane)
theorem putLane_low8_example :
    putLane laneLow8 0xFF#8 (0x1122334455667788#64) = 0x11223344556677FF#64

-- lean/ToyParMove/Lanes.lean:321-322
-- lean/ToyParMove/Lanes.lean — Positive example (putLane)
theorem putLane_high8_example :
    putLane laneHigh8 0xAB#8 (0x1122334455667788#64) = 0x112233445566AB88#64

-- lean/ToyParMove/Lanes.lean:325-327
-- lean/ToyParMove/Lanes.lean — Negative example (putLane is not a zero-extending write)
theorem putLane_low32_not_zext :
    putLane laneLow32 0xDEADBEEF#32 (0x1122334455667788#64) ≠
      writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64)

-- lean/ToyParMove/Lanes.lean:330-331
-- lean/ToyParMove/Lanes.lean — Positive example (writeZext)
theorem writeZext_example :
    writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64) = 0x00000000DEADBEEF#64

-- lean/ToyParMove/Lanes.lean:351-352
-- lean/ToyParMove/Lanes.lean — Negative example (writeZext)
theorem writeZext_not_preserve_upper :
    writeZext 64 0xDEADBEEF#32 (0x1122334455667788#64) ≠ 0x11223344DEADBEEF#64

-- lean/ToyParMove/Lanes.lean:355
-- lean/ToyParMove/Lanes.lean — Non-claim witness (writeZext truncates a value wider than the register)
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8

-- lean/ToyParMove/Lanes.lean:345-347
-- lean/ToyParMove/Lanes.lean — Positive / negative examples (getLane)
theorem getLane_examples :
    getLane (n := 64) ⟨8, 8⟩ (0x1122334455667788#64) = (0x77#8 : BitVec 8) ∧
    getLane (n := 64) ⟨60, 8⟩ (BitVec.allOnes 64) = (0x0F#8 : BitVec 8)

-- lean/ToyParMove/Lanes.lean:335-336
-- lean/ToyParMove/Lanes.lean — Positive / negative examples (Lane.Disjoint)
theorem disjoint_examples :
    laneLow8.Disjoint laneHigh8 ∧ ¬ laneLow8.Disjoint laneLow16 ∧ Lane.Disjoint ⟨4, 0⟩ ⟨0, 8⟩

-- lean/ToyParMove/Lanes.lean:341-342
-- lean/ToyParMove/Lanes.lean — Positive / negative examples (Lane.DisjointIn)
theorem disjointIn_examples :
    Lane.DisjointIn 8 ⟨6, 4⟩ ⟨8, 4⟩ ∧ ¬ Lane.DisjointIn 16 ⟨6, 4⟩ ⟨8, 4⟩

-- lean/ToyParMove/Lanes.lean:358
-- lean/ToyParMove/Lanes.lean — Positive / negative examples (Lane.Fits)
theorem fits_examples : laneLow32.Fits 64 ∧ ¬ (Lane.Fits ⟨60, 8⟩ 64)
```

#### Lane moves (`lean/ToyParMove/LaneMoves.lean`)

```lean
structure LaneMove (R) where dreg : R; doff : Nat; sreg : R; soff : Nat; wid : Nat
def LaneMove.dst m : Lane := ⟨m.doff, m.wid⟩;  def LaneMove.src m : Lane := ⟨m.soff, m.wid⟩
def laneWrite (reads τ : R → BitVec n) (m) :=
  upd τ m.dreg (putLane m.dst (getLane m.src (reads m.sreg)) (τ m.dreg))
def runLanes (ms) (ρ) := ms.foldl (fun ρ m => laneWrite ρ ρ m) ρ   -- reads the current file
def lanePMove (M) (ρ) := M.foldl (laneWrite ρ) ρ                    -- reads the OLD file ρ;
                                                                    -- later entry wins on overlap
def LaneWF (M) := M.Pairwise fun m₁ m₂ => m₁.dreg = m₂.dreg → m₁.dst.Disjoint m₂.dst
def DistinctDstLanes (M) := (M.map fun m => (m.dreg, m.dst)).Nodup
def LaneTopological (ms) := ms.Pairwise fun e l => e.dreg = l.sreg → e.dst.Disjoint l.src

-- concrete notation used in examples (registers Nat, 16-bit words)
def lm (dreg doff sreg soff wid : Nat) : LaneMove Nat := ⟨dreg, doff, sreg, soff, wid⟩
def regs16 : Nat → BitVec 16 :=
  fun r => if r = 0 then 0x1234#16 else if r = 1 then 0xABCD#16 else 0#16
```

Examples (each proved; statements quoted verbatim, proofs omitted):

```lean
-- lean/ToyParMove/LaneMoves.lean:211-212
-- lean/ToyParMove/LaneMoves.lean — Positive example (lanePMove)
theorem lanePMove_byte_swap_example :
    lanePMove [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 0 = 0x3412#16

-- lean/ToyParMove/LaneMoves.lean:216-217
-- lean/ToyParMove/LaneMoves.lean — Negative example (runLanes is not the parallel reading)
theorem runLanes_byte_swap_naive :
    runLanes [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 0 = 0x1212#16

-- lean/ToyParMove/LaneMoves.lean:220-221
-- lean/ToyParMove/LaneMoves.lean — Positive / negative examples (LaneWF)
theorem laneWF_examples :
    LaneWF [lm 0 0 1 0 8, lm 0 8 1 8 8] ∧ ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 16]

-- lean/ToyParMove/LaneMoves.lean:225-226
-- lean/ToyParMove/LaneMoves.lean — Positive / negative examples (DistinctDstLanes)
theorem distinctDstLanes_examples :
    DistinctDstLanes [lm 0 0 1 0 8, lm 0 8 2 0 8] ∧ ¬ DistinctDstLanes [lm 0 0 1 0 8, lm 0 0 2 0 8]

-- lean/ToyParMove/LaneMoves.lean:230-231
-- lean/ToyParMove/LaneMoves.lean — Positive / negative examples (LaneTopological)
theorem laneTopological_examples :
    LaneTopological [lm 2 0 1 0 8, lm 1 0 0 0 8] ∧ ¬ LaneTopological [lm 1 0 0 0 8, lm 2 0 1 0 8]
```

### Modeling bridges (shared reasoning for every `Basis: derived (modeling bridge)` line)

* x86-64: Intel SDM Vol. 1 (Order No. 253665-060US), Section 3.4.1.1 "General-Purpose Registers
  in 64-Bit Mode", p. 3-12. Only the section number, title and page were confirmed at the
  primary source (its table of contents); the section text was not retrieved and is paraphrased,
  not quoted: in 64-bit mode a 32-bit-operand write zero-extends into the 64-bit register, and
  8-bit and 16-bit writes leave the other bits unchanged. Modeled as: 32-bit writes behave like
  `writeZext 64` (with `wid = 32`); 8-bit and 16-bit writes behave like `putLane` on lanes `(0,8)`
  (`al`), `(8,8)` (`ah`), `(0,16)` (`ax`).
* AArch64: Arm "Learn the architecture - A64 Instruction Set Architecture Guide" (document
  102374, version 1.4), page "Registers in AArch64 - general-purpose registers": "When a W register
  is written, as seen in the example above, the top 32 bits of the 64-bit register are zeroed."
  Modeled as: a `W`-register write behaves like `writeZext 64` with `wid = 32`.
* Which lanes of which registers exist as instruction operands, and which combinations one
  instruction can encode, is not modeled.
* None of these bridges is kernel-checked; they are claims about documentation, not theorems.

### Results

#### 1. `pmove-readings-disagree-on-repeated-destination`

- **Kind and tier:** counterexample; T0. Known: a repeated destination makes a parallel move ambiguous (Rideau-Serpette-Leroy Section 2; CompCert's is_mill excludes it). Restated here as a concrete kernel-checked instance.
- **Plain claim:** For the move list [(0,1),(0,2)] (destination 0 listed twice with sources 1 and 2) and the identity store on Nat, the first-entry reading of the parallel move puts the old value of 1 at 0 and the last-entry reading puts the old value of 2 at 0, so the two readings disagree; the package adopts the first-entry reading pmove and intends it only for well-formed (distinct-destination) moves.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.pmove_readings_disagree_on_repeated_destination`.

```lean
-- lean/ToyParMove/Readings.lean:101-103
theorem pmove_readings_disagree_on_repeated_destination :
    pmove [(0, 1), (0, 2)] (id : Nat → Nat) 0 = 1 ∧
    pmoveLast [(0, 1), (0, 2)] (id : Nat → Nat) 0 = 2
```

- **Reading with key definitions unfolded:**

```lean
pmove [(0,1),(0,2)] (id : Nat → Nat) 0 = 1 ∧ pmoveLast [(0,1),(0,2)] (id : Nat → Nat) 0 = 2
```

- **Hypothesis ledger:** none (a concrete instance; no hypotheses).
- **Depth:** definitional
- **Non-vacuity witness:** The statement is itself a concrete instance.
- **Prior art:**
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - CompCert, file lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861 (github.com/AbsInt/CompCert; file contents at that commit). exec_par gives the parallel semantics; parmove_correctness assumes is_mill (no destination appears twice) and move_no_temp (no temporary occurs as a source or a destination). Moves there are written (source, destination), the reverse of this package's (destination, source).
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 1).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy `pmove` reads the old store for every destination, and for a repeated destination the first entry wins; this is the parallel semantics `exec_par` of CompCert's `lib/Parmov.v` at the cited commit (`(s, d) :: m' => update d (e s) (exec_par m' e)`, moves written source first), and `runSeq` is ordinary left-to-right execution of register-to-register copies. CompCert (`is_mill`) and Rideau–Serpette–Leroy (Section 2, 'windmills') require pairwise-distinct destinations; the instance shows concretely the ambiguity those preconditions exclude. The transfer assumes whole, non-overlapping locations (no sub-registers), one plain copy instruction per move, and no register classes; it is not a statement about any compiler's implementation.

#### 2. `pmove-order-independent-iff-functional`

- **Kind and tier:** characterization; T1. Order independence for distinct destinations is mechanized in HOL4 (CakeML parsem_perm); the exact characterizations here (Functional for all stores when the value type has two distinct values; FunctionalAt for one store) were not found in the sources cited here; no novelty is claimed.
- **Plain claim:** (a) Over a value type with two distinct values a ≠ b, the parallel-move semantics pmove M is unchanged on every store by every reordering of M if and only if M is functional (entries with the same destination have the same source location). (b) The direction 'functional implies order-independent' needs no hypothesis on the value type: if M is functional and M' is a reordering of M, then pmove M σ = pmove M' σ for every store σ; in particular the first-entry and last-entry readings coincide on functional M. (c) For one fixed store σ, pmove M σ is unchanged by every reordering of M if and only if entries with the same destination read equal values in σ (FunctionalAt σ M), with no hypothesis on the value type.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.pmove_perm_invariant_iff_functional_of_two_values`, `Toy.ParMove.pmove_perm_invariant_of_functional`, `Toy.ParMove.functional_of_pmove_perm_invariant_of_two_values`, `Toy.ParMove.pmove_perm_invariant_at_iff_functionalAt`, `Toy.ParMove.pmove_eq_pmoveLast_of_functional`.

```lean
-- lean/ToyParMove/Readings.lean:142-145
theorem pmove_perm_invariant_iff_functional_of_two_values {M : List (Loc × Loc)} (a b : V)
    (hab : a ≠ b) :
    (∀ M' : List (Loc × Loc), M'.Perm M → ∀ σ : Loc → V, pmove M' σ = pmove M σ) ↔
      Functional M

-- lean/ToyParMove/Readings.lean:110-111
theorem pmove_perm_invariant_of_functional {M M' : List (Loc × Loc)} (hF : Functional M)
    (hp : M.Perm M') (σ : Loc → V) : pmove M σ = pmove M' σ

-- lean/ToyParMove/Readings.lean:125-128
theorem functional_of_pmove_perm_invariant_of_two_values {M : List (Loc × Loc)} (a b : V)
    (hab : a ≠ b)
    (h : ∀ M' : List (Loc × Loc), M'.Perm M → ∀ σ : Loc → V, pmove M' σ = pmove M σ) :
    Functional M

-- lean/ToyParMove/Readings.lean:152-153
theorem pmove_perm_invariant_at_iff_functionalAt {M : List (Loc × Loc)} (σ : Loc → V) :
    (∀ M' : List (Loc × Loc), M'.Perm M → pmove M' σ = pmove M σ) ↔ FunctionalAt σ M

-- lean/ToyParMove/Readings.lean:183-184
theorem pmove_eq_pmoveLast_of_functional {M : List (Loc × Loc)} (hF : Functional M)
    (σ : Loc → V) : pmove M σ = pmoveLast M σ
```

- **Reading with key definitions unfolded (prose):**

```text
(a) (a b : V) (hab : a ≠ b) : (∀ M', M'.Perm M → ∀ σ, pmove M' σ = pmove M σ) ↔ Functional M;  (b) Functional M → M.Perm M' → ∀ σ, pmove M σ = pmove M' σ;  (a→) (a b : V) → a ≠ b → (∀ M', M'.Perm M → ∀ σ, pmove M' σ = pmove M σ) → Functional M;  (c) ∀ σ, (∀ M', M'.Perm M → pmove M' σ = pmove M σ) ↔ FunctionalAt σ M;  (b') Functional M → ∀ σ, pmove M σ = pmoveLast M σ.   Here Functional M := ∀ d s₁ s₂, (d,s₁) ∈ M → (d,s₂) ∈ M → s₁ = s₂ and FunctionalAt σ M := ∀ d s₁ s₂, (d,s₁) ∈ M → (d,s₂) ∈ M → σ s₁ = σ s₂.
```

- **Hypothesis ledger:**
  - `hab : a ≠ b (two distinct values)` [applies to `pmove_perm_invariant_iff_functional_of_two_values`, `functional_of_pmove_perm_invariant_of_two_values`]: lets a store distinguish two different sources of the same destination; without it a non-functional list can be order-independent (over Unit, [(0,1),(0,2)] is). Tightness: **tight (counterexample `Toy.ParMove.functional_of_pmove_perm_invariant_needs_two_values`)**.
  - `h : ∀ M', M'.Perm M → ∀ σ, pmove M' σ = pmove M σ (order independence on every store)` [applies to `functional_of_pmove_perm_invariant_of_two_values`]: the premise of the 'order independence forces functionality' direction. Tightness: **tight (counterexample `Toy.ParMove.functional_of_pmove_perm_invariant_needs_perm_invariance`)**.
  - `hF : Functional M (direction b)` [applies to `pmove_perm_invariant_of_functional`]: a destination with two different sources can make the result depend on which entry comes first. Tightness: **tight (counterexample `Toy.ParMove.pmove_perm_invariant_needs_functional`)**.
  - `hp : M.Perm M' (direction b)` [applies to `pmove_perm_invariant_of_functional`]: the other list must consist of the same moves. Tightness: **tight (counterexample `Toy.ParMove.pmove_perm_invariant_needs_perm`)**.
  - `hF : Functional M (corollary b')` [applies to `pmove_eq_pmoveLast_of_functional`]: with two different sources for one destination the first-entry and last-entry readings can differ. Tightness: **tight (counterexample `Toy.ParMove.pmove_eq_pmoveLast_needs_functional`)**.
- **Depth:** shallow
- **Non-vacuity witness:** Bool (true ≠ false), the functional swap [(0,1),(1,0)], its reordering [(1,0),(0,1)], and its order independence on every Bool store; for (c), the store with σ 1 = σ 2 = 1 and the non-functional [(0,1),(0,2)] (FunctionalAt holds) and the identity store (FunctionalAt fails). (`Toy.ParMove.nonvacuity_pmove_perm_invariant_all`, `Toy.ParMove.functionalAt_equal_values_example`, `Toy.ParMove.not_functionalAt_id_example`)
- **Prior art:**
  - CakeML, file compiler/backend/reg_alloc/parmoveScript.sml at commit 4777c4b7c0aa4661994e29f97b9501c3f0b7d602 (github.com/CakeML/cakeml): a HOL4 formalisation of the Rideau-Serpette-Leroy algorithm, with moves written (destination, source) as in this package. Theorem parsem_perm: 'windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2' (order independence for distinct destinations, the WellFormed special case of Functional here); parmove_correct states correctness of the compiled move sequence for windmills.
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - CompCert, file lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861 (github.com/AbsInt/CompCert; file contents at that commit). exec_par gives the parallel semantics; parmove_correctness assumes is_mill (no destination appears twice) and move_no_temp (no temporary occurs as a source or a destination). Moves there are written (source, destination), the reverse of this package's (destination, source).
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 2).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy `pmove` reads the old store for every destination, and for a repeated destination the first entry wins; this is the parallel semantics `exec_par` of CompCert's `lib/Parmov.v` at the cited commit (`(s, d) :: m' => update d (e s) (exec_par m' e)`, moves written source first), and `runSeq` is ordinary left-to-right execution of register-to-register copies. Order independence is what lets a compiler treat a parallel copy as a set of copies rather than a list; the card says that, for this semantics, the exact syntactic condition is functionality (CakeML's `parsem_perm` covers the distinct-destination case). The transfer assumes whole, non-overlapping locations (no sub-registers), one plain copy instruction per move, and no register classes; it is not a statement about any compiler's implementation.

#### 3. `sequentialize-sound-off-scratch`

- **Kind and tier:** theorem; T1. The strategy (emit ready moves, break each remaining cycle through one scratch location) is May's, as credited by Rideau-Serpette-Leroy and Boissinot et al.; Rideau-Serpette-Leroy call one-temporary serialization 'a folklore result'. The side conditions used here (Functional instead of distinct destinations; scratch only required not to be both a destination and a source) were not found in the sources cited here; no novelty is claimed.
- **Plain claim:** For a functional parallel move M (in particular a well-formed one) and a scratch location tmp that is not simultaneously a destination and a source of M, running the move list sequentialize tmp M from any store σ gives, at every location other than tmp, exactly the value pmove M σ prescribes.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.sequentialize_agrees_off_tmp`.

```lean
-- lean/ToyParMove/Sequentialize.lean:271-273
theorem sequentialize_agrees_off_tmp {M : List (Loc × Loc)} {tmp : Loc} (hF : Functional M)
    (htmp : tmp ∉ dsts M ∨ tmp ∉ srcs M) (σ : Loc → V) :
    ∀ l, l ≠ tmp → runSeq (sequentialize tmp M) σ l = pmove M σ l
```

- **Reading with key definitions unfolded (prose):**

```text
Functional M → (tmp ∉ dsts M ∨ tmp ∉ srcs M) → ∀ σ, ∀ l ≠ tmp, runSeq (sequentialize tmp M) σ l = pmove M σ l
```

- **Hypothesis ledger:**
  - `hF : Functional M`: a destination with two different sources has no order-independent meaning; the algorithm can then follow neither reading. Tightness: **tight (counterexample `Toy.ParMove.sequentialize_needs_functional`)**.
  - `htmp : tmp ∉ dsts M ∨ tmp ∉ srcs M`: if tmp is both a destination and a source it can lie on a cycle and be clobbered before it is read. Tightness: **tight (counterexample `Toy.ParMove.sequentialize_needs_tmp_not_dst_or_not_src`)**.
- **Depth:** substantive
- **Non-vacuity witness:** [(1,2),(2,1),(3,0)] with tmp = 0 (tmp is read by 3 := 0 and is not a destination; emitted sequence 3:=0; 0:=1; 1:=2; 2:=0), and [(0,3),(1,2),(2,1)] with tmp = 0 (tmp is a destination, not a source). (`Toy.ParMove.nonvacuity_sequentialize_tmp_is_source`, `Toy.ParMove.nonvacuity_sequentialize_tmp_is_destination`)
- **Prior art:**
  - May. "The Parallel Assignment Problem Redefined." IEEE Transactions on Software Engineering 15(6):821-824, 1989, DOI 10.1109/32.24735 (bibliographic record from dblp). Cited through the descriptions in Rideau-Serpette-Leroy Section 3 and Boissinot et al. Section III-C, which credit it with the strategy that sequentialize follows: emit moves whose destination is no longer read, then break each remaining cycle with one temporary.
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - CompCert, file lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861 (github.com/AbsInt/CompCert; file contents at that commit). exec_par gives the parallel semantics; parmove_correctness assumes is_mill (no destination appears twice) and move_no_temp (no temporary occurs as a source or a destination). Moves there are written (source, destination), the reverse of this package's (destination, source).
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - CakeML, file compiler/backend/reg_alloc/parmoveScript.sml at commit 4777c4b7c0aa4661994e29f97b9501c3f0b7d602 (github.com/CakeML/cakeml): a HOL4 formalisation of the Rideau-Serpette-Leroy algorithm, with moves written (destination, source) as in this package. Theorem parsem_perm: 'windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2' (order independence for distinct destinations, the WellFormed special case of Functional here); parmove_correct states correctness of the compiled move sequence for windmills.
  - Briggs, Cooper, Harvey, Simpson. "Practical Improvements to the Construction and Destruction of Static Single Assignment Form." Software: Practice and Experience 28(8):859-881, 1998 (bibliographic record from dblp). Cited, as described in Boissinot et al. Section II, for identifying the 'lost copy problem' and the 'swap problem' that parallel copies cause in out-of-SSA translation.
  - Sethi. "A Note on Implementing Parallel Assignment Instructions." Information Processing Letters 2(4):91-95, 1973, DOI 10.1016/0020-0190(73)90024-0; Welch. "Parallel Assignment Revisited." Software: Practice and Experience 13(12):1175-1180, 1983, DOI 10.1002/spe.4380131208 (bibliographic records from dblp). Background, cited through Rideau-Serpette-Leroy Section 1: Sethi shows that compiling general parallel assignments with a constant number of temporaries is NP-hard; Welch outlines the trivial scheme with n temporaries.
  - Sreedhar, Ju, Gillies, Santhanam. "Translating Out of Static Single Assignment Form." SAS 1999, LNCS 1694, pp. 194-210, DOI 10.1007/3-540-48294-6_13 (bibliographic record from dblp). Background only: out-of-SSA translation by copy insertion; its content is not relied on.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 3).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy `pmove` reads the old store for every destination, and for a repeated destination the first entry wins; this is the parallel semantics `exec_par` of CompCert's `lib/Parmov.v` at the cited commit (`(s, d) :: m' => update d (e s) (exec_par m' e)`, moves written source first), and `runSeq` is ordinary left-to-right execution of register-to-register copies. The scratch location models a reserved temporary register. The card suggests that a compiler using the same ready-first strategy needs a temporary that is not both read and written by the parallel move and whose old value is dead afterwards (liveness is not modeled); it is about this algorithm only. The transfer assumes whole, non-overlapping locations (no sub-registers), one plain copy instruction per move, and no register classes; it is not a statement about any compiler's implementation.

#### 4. `sequential-composition-of-move-blocks`

- **Kind and tier:** theorem; T1. Folklore reasoning about emitting independent sub-problems one after the other, made precise.
- **Plain claim:** If a move list ms1 realizes the parallel move M1 and ms2 realizes M2 (each at every location other than one shared scratch location tmp, from every store), the two blocks have disjoint destinations, no source of M2 is a destination of M1, and tmp is not a source of M2, then ms1 ++ ms2 realizes M1 ++ M2 at every location other than tmp, from every store.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runSeq_append_realizes_off_tmp`.

```lean
-- lean/ToyParMove/Necessity.lean:135-141
theorem runSeq_append_realizes_off_tmp {M₁ M₂ ms₁ ms₂ : List (Loc × Loc)} {tmp : Loc}
    (h₁ : ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq ms₁ τ l = pmove M₁ τ l)
    (h₂ : ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq ms₂ τ l = pmove M₂ τ l)
    (hdisj : ∀ x ∈ dsts M₁, x ∉ dsts M₂)
    (hread : ∀ x ∈ srcs M₂, x ∉ dsts M₁)
    (htmp : tmp ∉ srcs M₂) :
    ∀ τ : Loc → V, ∀ l, l ≠ tmp → runSeq (ms₁ ++ ms₂) τ l = pmove (M₁ ++ M₂) τ l
```

- **Reading with key definitions unfolded (prose):**

```text
(h₁ : ∀ τ, ∀ l ≠ tmp, runSeq ms₁ τ l = pmove M₁ τ l) → (h₂ : ∀ τ, ∀ l ≠ tmp, runSeq ms₂ τ l = pmove M₂ τ l) → (hdisj : ∀ x ∈ dsts M₁, x ∉ dsts M₂) → (hread : ∀ x ∈ srcs M₂, x ∉ dsts M₁) → (htmp : tmp ∉ srcs M₂) → ∀ τ, ∀ l ≠ tmp, runSeq (ms₁ ++ ms₂) τ l = pmove (M₁ ++ M₂) τ l
```

- **Hypothesis ledger:**
  - `h₁ (first block realized off tmp)`: premise about the first block. Tightness: **tight (counterexample `Toy.ParMove.runSeq_append_needs_first_realization`)**.
  - `h₂ (second block realized off tmp)`: premise about the second block. Tightness: **tight (counterexample `Toy.ParMove.runSeq_append_needs_second_realization`)**.
  - `hdisj : destinations of M₁ and M₂ are disjoint`: otherwise the second block can overwrite the first block's result. Tightness: **tight (counterexample `Toy.ParMove.runSeq_append_needs_disjoint_dsts`)**.
  - `hread : no source of M₂ is a destination of M₁`: the first block must not overwrite what the second reads (topological emission). Tightness: **tight (counterexample `Toy.ParMove.runSeq_append_needs_sources_not_overwritten`)**.
  - `htmp : tmp ∉ srcs M₂`: the first block may clobber tmp; breaking a cycle before draining a reader of tmp can be wrong. Tightness: **tight (counterexample `Toy.ParMove.runSeq_append_needs_tmp_not_src`)**.
- **Depth:** shallow
- **Non-vacuity witness:** Emit 3 := 0 first, then break the cycle [(1,2),(2,1)] through 0. (`Toy.ParMove.nonvacuity_runSeq_append_realizes_off_tmp`)
- **Prior art:**
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - CompCert, file lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861 (github.com/AbsInt/CompCert; file contents at that commit). exec_par gives the parallel semantics; parmove_correctness assumes is_mill (no destination appears twice) and move_no_temp (no temporary occurs as a source or a destination). Moves there are written (source, destination), the reverse of this package's (destination, source).
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 4).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy `pmove` reads the old store for every destination, and for a repeated destination the first entry wins; this is the parallel semantics `exec_par` of CompCert's `lib/Parmov.v` at the cited commit (`(s, d) :: m' => update d (e s) (exec_par m' e)`, moves written source first), and `runSeq` is ordinary left-to-right execution of register-to-register copies. The card supports emitting independent sub-problems of a parallel copy one block after another, provided the side conditions hold; the counterexample for `htmp` shows a hazard for any emission strategy that breaks a cycle through the temporary before a pending copy has read the temporary. The transfer assumes whole, non-overlapping locations (no sub-registers), one plain copy instruction per move, and no register classes; it is not a statement about any compiler's implementation.

#### 5. `topological-order-realizes-parallel-move`

- **Kind and tier:** theorem; T1. Folklore (Rideau-Serpette-Leroy Section 3: a tree is serialized 'in a bottom-up topological order'), made precise.
- **Plain claim:** A functional list of moves in which no move overwrites the source of a later move (a topological order), executed left to right with no scratch location, produces exactly, at every location and from every store, the parallel reading of the same list.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runSeq_eq_pmove_of_topological`.

```lean
-- lean/ToyParMove/Necessity.lean:268-269
theorem runSeq_eq_pmove_of_topological {ms : List (Loc × Loc)} (hF : Functional ms)
    (htop : Topological ms) (σ : Loc → V) : runSeq ms σ = pmove ms σ
```

- **Reading with key definitions unfolded (prose):**

```text
Functional ms → ms.Pairwise (fun e l => e.1 ≠ l.2) → ∀ σ, runSeq ms σ = pmove ms σ
```

- **Hypothesis ledger:**
  - `hF : Functional ms`: sequential execution lets the last write win, the adopted parallel reading lets the first entry win; they can differ on a repeated destination with two sources. Tightness: **tight (counterexample `Toy.ParMove.runSeq_eq_pmove_needs_functional`)**.
  - `htop : Topological ms`: a move that overwrites a later move's source makes the later move read the new value. Tightness: **tight (counterexample `Toy.ParMove.runSeq_eq_pmove_needs_topological`)**.
- **Depth:** shallow
- **Non-vacuity witness:** The chain [(2,1),(1,0)] (copy 1 into 2 before overwriting 1). (`Toy.ParMove.nonvacuity_runSeq_eq_pmove_of_topological`)
- **Prior art:**
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - Briggs, Cooper, Harvey, Simpson. "Practical Improvements to the Construction and Destruction of Static Single Assignment Form." Software: Practice and Experience 28(8):859-881, 1998 (bibliographic record from dblp). Cited, as described in Boissinot et al. Section II, for identifying the 'lost copy problem' and the 'swap problem' that parallel copies cause in out-of-SSA translation.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 5).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — The toy `pmove` reads the old store for every destination, and for a repeated destination the first entry wins; this is the parallel semantics `exec_par` of CompCert's `lib/Parmov.v` at the cited commit (`(s, d) :: m' => update d (e s) (exec_par m' e)`, moves written source first), and `runSeq` is ordinary left-to-right execution of register-to-register copies. The card supports emitting the copies of an acyclic parallel copy in an order in which no copy overwrites a register still to be read, with no temporary. The transfer assumes whole, non-overlapping locations (no sub-registers), one plain copy instruction per move, and no register classes; it is not a statement about any compiler's implementation.

#### 6. `cycle-with-scratch-upper-bound`

- **Kind and tier:** theorem; T0. Classical (Rideau-Serpette-Leroy Section 3): save one value, shift the cycle, restore.
- **Plain claim:** For a nonempty duplicate-free cycle l0, ..., l(k-1) with k ≥ 1 (each l(i+1) receives the old value of l(i), and l0 receives the old value of l(k-1)) and a scratch location tmp outside it, the k + 1 moves tmp := l(k-1); l(k-1) := l(k-2); ...; l1 := l0; l0 := tmp realize the cycle at every location other than tmp, from every store.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runSeq_cycleSeqScratch`, `Toy.ParMove.length_cycleSeqScratch`.

```lean
-- lean/ToyParMove/Cycles.lean:178-181
theorem runSeq_cycleSeqScratch {l₀ : Loc} {rest : List Loc} {tmp : Loc}
    (hn : (l₀ :: rest).Nodup) (htmp : tmp ∉ l₀ :: rest) (σ : Loc → V) :
    ∀ l, l ≠ tmp →
      runSeq (cycleSeqScratch tmp (l₀ :: rest)) σ l = pmove (cycleMoves (l₀ :: rest)) σ l

-- lean/ToyParMove/Cycles.lean:171-172
theorem length_cycleSeqScratch (tmp l₀ : Loc) (rest : List Loc) :
    (cycleSeqScratch tmp (l₀ :: rest)).length = (l₀ :: rest).length + 1
```

- **Reading with key definitions unfolded (prose):**

```text
(l₀ :: rest).Nodup → tmp ∉ l₀ :: rest → ∀ σ, ∀ l ≠ tmp, runSeq (cycleSeqScratch tmp (l₀ :: rest)) σ l = pmove (cycleMoves (l₀ :: rest)) σ l;  (cycleSeqScratch tmp (l₀ :: rest)).length = (l₀ :: rest).length + 1
```

- **Hypothesis ledger:**
  - `hn : (l₀ :: rest).Nodup` [applies to `runSeq_cycleSeqScratch`]: a repeated location can make cycleMoves a different (non-cyclic) move. Tightness: **tight (counterexample `Toy.ParMove.runSeq_cycleSeqScratch_needs_nodup`)**.
  - `htmp : tmp ∉ l₀ :: rest` [applies to `runSeq_cycleSeqScratch`]: the scratch must not be a cycle location. Tightness: **tight (counterexample `Toy.ParMove.runSeq_cycleSeqScratch_needs_tmp_fresh`)**.
- **Depth:** shallow
- **Non-vacuity witness:** The 3-cycle [0,1,2] with scratch 3 (4 moves). (`Toy.ParMove.nonvacuity_runSeq_cycleSeqScratch`)
- **Prior art:**
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - May. "The Parallel Assignment Problem Redefined." IEEE Transactions on Software Engineering 15(6):821-824, 1989, DOI 10.1109/32.24735 (bibliographic record from dblp). Cited through the descriptions in Rideau-Serpette-Leroy Section 3 and Boissinot et al. Section III-C, which credit it with the strategy that sequentialize follows: emit moves whose destination is no longer read, then break each remaining cycle with one temporary.
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 6).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — A rotation of registers (for example a calling-convention shuffle that permutes argument registers cyclically) is the parallel move `cycleMoves ls`, and the toy move or swap counts become instruction counts if each move is one register copy and each swap one exchange instruction. The card then says one temporary and k + 1 copies suffice for a k-cycle. The transfer assumes whole, non-overlapping locations (no sub-registers), one instruction per move or swap, and no register classes; it is not a statement about any compiler's implementation.

#### 7. `cycle-with-scratch-lower-bound`

- **Kind and tier:** theorem; T1. Boissinot et al. state that their sequentialization 'requires the minimum number of copies' (without proof); this mechanizes the isolated-cycle lower bound with explicit hypotheses, per injective store and uniformly over all stores.
- **Plain claim:** Let ls be an isolated duplicate-free cycle of length k ≥ 2 (the parallel move consists of exactly the cycle's moves cycleMoves ls) and tmp a location outside it. (a) Every sequence of plain moves (over any locations) that, from a given injective store σ, produces the cycle's target at every location other than tmp has at least k + 1 moves. (b) Over any value type with two distinct values, every sequence of plain moves that produces the cycle's target at every location other than tmp from every store has at least k + 1 moves.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.cycle_length_add_one_le_of_injective_of_realizes_off_tmp`, `Toy.ParMove.cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`.

```lean
-- lean/ToyParMove/Cycles.lean:337-341
theorem cycle_length_add_one_le_of_injective_of_realizes_off_tmp {ls : List Loc} {tmp : Loc}
    {σ : Loc → V} {ms : List (Loc × Loc)} (hn : ls.Nodup) (hk : 2 ≤ ls.length) (htmp : tmp ∉ ls)
    (hσ : Function.Injective σ)
    (hreal : ∀ l, l ≠ tmp → runSeq ms σ l = pmove (cycleMoves ls) σ l) :
    ls.length + 1 ≤ ms.length

-- lean/ToyParMove/Cycles.lean:411-415
theorem cycle_length_add_one_le_of_two_values_of_realizes_off_tmp {ls : List Loc} {tmp : Loc}
    {ms : List (Loc × Loc)} (a b : V) (hab : a ≠ b) (hn : ls.Nodup) (hk : 2 ≤ ls.length)
    (htmp : tmp ∉ ls)
    (hreal : ∀ σ : Loc → V, ∀ l, l ≠ tmp → runSeq ms σ l = pmove (cycleMoves ls) σ l) :
    ls.length + 1 ≤ ms.length
```

- **Reading with key definitions unfolded (prose):**

```text
(a) ls.Nodup → 2 ≤ ls.length → tmp ∉ ls → Function.Injective σ → (∀ l ≠ tmp, runSeq ms σ l = pmove (cycleMoves ls) σ l) → ls.length + 1 ≤ ms.length;  (b) (a b : V) → a ≠ b → ls.Nodup → 2 ≤ ls.length → tmp ∉ ls → (∀ σ : Loc → V, ∀ l ≠ tmp, runSeq ms σ l = pmove (cycleMoves ls) σ l) → ls.length + 1 ≤ ms.length
```

- **Hypothesis ledger:**
  - `hn : ls.Nodup`: a repeated location can change the target into a non-cyclic move. Tightness: **tight (counterexamples `Toy.ParMove.cycle_lower_bound_needs_nodup`, `Toy.ParMove.cycle_lower_bound_uniform_needs_nodup`)**.
  - `hk : 2 ≤ ls.length`: a 1-cycle is the identity and needs no move. Tightness: **tight (counterexamples `Toy.ParMove.cycle_lower_bound_needs_two`, `Toy.ParMove.cycle_lower_bound_uniform_needs_two`)**.
  - `htmp : tmp ∉ ls`: if the excluded location is on the cycle, its value need not be produced. Tightness: **tight (counterexamples `Toy.ParMove.cycle_lower_bound_needs_tmp_fresh`, `Toy.ParMove.cycle_lower_bound_uniform_needs_tmp_fresh`)**.
  - `hσ : Function.Injective σ (statement a)` [applies to `cycle_length_add_one_le_of_injective_of_realizes_off_tmp`]: with equal values no move is needed (constant store); injectivity on the cycle and the scratch alone is not enough, since an untouched location holding a copy of a cycle value can serve as a backup (cycle_lower_bound_needs_global_injectivity). Tightness: **tight (counterexamples `Toy.ParMove.cycle_lower_bound_needs_injective`, `Toy.ParMove.cycle_lower_bound_needs_global_injectivity`)**.
  - `hreal (statement a: ms realizes the cycle off tmp from σ)` [applies to `cycle_length_add_one_le_of_injective_of_realizes_off_tmp`]: premise. Tightness: **tight (counterexample `Toy.ParMove.cycle_lower_bound_needs_realization`)**.
  - `hab : a ≠ b (statement b)` [applies to `cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`]: over a one-element value type every store is the same and the empty sequence realizes the cycle. Tightness: **tight (counterexample `Toy.ParMove.cycle_lower_bound_uniform_needs_two_values`)**.
  - `hreal (statement b: ms realizes the cycle off tmp on every store)` [applies to `cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`]: premise. Tightness: **tight (counterexample `Toy.ParMove.cycle_lower_bound_uniform_needs_realization`)**.
- **Depth:** substantive
- **Non-vacuity witness:** (a) The 2-cycle [0,1], tmp = 2, σ = id on Nat, ms = cycleSeqScratch 2 [0,1] (3 moves: the bound is attained). (b) The same with V = Bool, realized on every Bool store. (`Toy.ParMove.nonvacuity_cycle_lower_bound`, `Toy.ParMove.nonvacuity_cycle_lower_bound_uniform`)
- **Prior art:**
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - May. "The Parallel Assignment Problem Redefined." IEEE Transactions on Software Engineering 15(6):821-824, 1989, DOI 10.1109/32.24735 (bibliographic record from dblp). Cited through the descriptions in Rideau-Serpette-Leroy Section 3 and Boissinot et al. Section III-C, which credit it with the strategy that sequentialize follows: emit moves whose destination is no longer read, then break each remaining cycle with one temporary.
  - Sethi. "A Note on Implementing Parallel Assignment Instructions." Information Processing Letters 2(4):91-95, 1973, DOI 10.1016/0020-0190(73)90024-0; Welch. "Parallel Assignment Revisited." Software: Practice and Experience 13(12):1175-1180, 1983, DOI 10.1002/spe.4380131208 (bibliographic records from dblp). Background, cited through Rideau-Serpette-Leroy Section 1: Sethi shows that compiling general parallel assignments with a constant number of temporaries is NP-hard; Welch outlines the trivial scheme with n temporaries.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 7).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — A rotation of registers (for example a calling-convention shuffle that permutes argument registers cyclically) is the parallel move `cycleMoves ls`, and the toy move or swap counts become instruction counts if each move is one register copy and each swap one exchange instruction. The card then says that, when only the temporary may be clobbered and register values can be arbitrary, fewer than k + 1 copies cannot work for an isolated k-cycle; it does not cover cycles with an outgoing copy, where fewer copies or no temporary can suffice. The transfer assumes whole, non-overlapping locations (no sub-registers), one instruction per move or swap, and no register classes; it is not a statement about any compiler's implementation.

#### 8. `cycle-without-scratch-impossible`

- **Kind and tier:** impossibility; T1. Folklore ('a swap needs a temporary or an exchange instruction'; Rideau-Serpette-Leroy Section 1: (x1, x2) := (x2, x1) cannot operate in place), mechanized for all cycle lengths k ≥ 2 with a value-loss argument, per injective store and uniformly over all stores.
- **Plain claim:** Let ls be an isolated duplicate-free cycle of length k ≥ 2, that is, the parallel move consists of exactly the cycle's moves cycleMoves ls, so its target leaves every location outside ls unchanged (for example a parallel swap [(a,b),(b,a)] with a ≠ b). (a) For a given injective store σ, no sequence of plain moves, over any locations, turns σ exactly (at every location) into the cycle's target. (b) Over any location type and any value type with two distinct values, no single sequence of plain moves turns every store exactly into the cycle's target.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runSeq_ne_pmove_cycle_of_injective`, `Toy.ParMove.runSeq_ne_pmove_swap_of_injective`, `Toy.ParMove.runSeq_ne_pmove_cycle_of_two_values`.

```lean
-- lean/ToyParMove/Cycles.lean:354-356
theorem runSeq_ne_pmove_cycle_of_injective {ls : List Loc} {σ : Loc → V} (hn : ls.Nodup)
    (hk : 2 ≤ ls.length) (hσ : Function.Injective σ) :
    ∀ ms : List (Loc × Loc), runSeq ms σ ≠ pmove (cycleMoves ls) σ

-- lean/ToyParMove/Cycles.lean:373-374
theorem runSeq_ne_pmove_swap_of_injective {a b : Loc} {σ : Loc → V} (hab : a ≠ b)
    (hσ : Function.Injective σ) : ∀ ms : List (Loc × Loc), runSeq ms σ ≠ pmove [(a, b), (b, a)] σ

-- lean/ToyParMove/Cycles.lean:400-402
theorem runSeq_ne_pmove_cycle_of_two_values {ls : List Loc} (a b : V) (hab : a ≠ b)
    (hn : ls.Nodup) (hk : 2 ≤ ls.length) :
    ¬ ∃ ms : List (Loc × Loc), ∀ σ : Loc → V, runSeq ms σ = pmove (cycleMoves ls) σ
```

- **Reading with key definitions unfolded (prose):**

```text
(a) ls.Nodup → 2 ≤ ls.length → Function.Injective σ → ∀ ms, runSeq ms σ ≠ pmove (cycleMoves ls) σ;  (a') a ≠ b → Function.Injective σ → ∀ ms, runSeq ms σ ≠ pmove [(a,b),(b,a)] σ;  (b) (a b : V) → a ≠ b → ls.Nodup → 2 ≤ ls.length → ¬ ∃ ms, ∀ σ : Loc → V, runSeq ms σ = pmove (cycleMoves ls) σ
```

- **Hypothesis ledger:**
  - `hn : ls.Nodup` [applies to `runSeq_ne_pmove_cycle_of_injective`, `runSeq_ne_pmove_cycle_of_two_values`]: a repeated location can change the target into a realizable non-cyclic move. Tightness: **tight (counterexamples `Toy.ParMove.cycle_impossibility_needs_nodup`, `Toy.ParMove.cycle_impossibility_uniform_needs_nodup`)**.
  - `hk : 2 ≤ ls.length` [applies to `runSeq_ne_pmove_cycle_of_injective`, `runSeq_ne_pmove_cycle_of_two_values`]: a 1-cycle is the identity. Tightness: **tight (counterexamples `Toy.ParMove.cycle_impossibility_needs_two`, `Toy.ParMove.cycle_impossibility_uniform_needs_two`)**.
  - `hσ : Function.Injective σ (statements a, a')` [applies to `runSeq_ne_pmove_cycle_of_injective`, `runSeq_ne_pmove_swap_of_injective`]: with equal values the empty sequence works; injectivity on the cycle alone is not enough, since two equal values elsewhere can let one location be borrowed and restored (cycle_impossibility_needs_global_injectivity). Tightness: **tight (counterexamples `Toy.ParMove.cycle_impossibility_needs_injective`, `Toy.ParMove.swap_impossibility_needs_injective`, `Toy.ParMove.cycle_impossibility_needs_global_injectivity`)**.
  - `hab : a ≠ b (swap corollary a'; a, b are locations)` [applies to `runSeq_ne_pmove_swap_of_injective`]: a 'swap' of a location with itself is the identity. Tightness: **tight (counterexample `Toy.ParMove.swap_impossibility_needs_distinct`)**.
  - `hab : a ≠ b (statement b; a, b are values)` [applies to `runSeq_ne_pmove_cycle_of_two_values`]: over a one-element value type the empty sequence works on every store. Tightness: **tight (counterexample `Toy.ParMove.cycle_impossibility_uniform_needs_two_values`)**.
- **Depth:** substantive
- **Non-vacuity witness:** ls = [0,1] (and a = 0, b = 1) with σ = id on Nat; for (b), V = Bool. (`Toy.ParMove.nonvacuity_cycle_impossibility`, `Toy.ParMove.nonvacuity_swap_impossibility`, `Toy.ParMove.nonvacuity_cycle_impossibility_uniform`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.ParMove.cycle_impossibility_positive_control`, `Toy.ParMove.cycle_with_outgoing_copy_realized_without_scratch`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
  - Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
  - Briggs, Cooper, Harvey, Simpson. "Practical Improvements to the Construction and Destruction of Static Single Assignment Form." Software: Practice and Experience 28(8):859-881, 1998 (bibliographic record from dblp). Cited, as described in Boissinot et al. Section II, for identifying the 'lost copy problem' and the 'swap problem' that parallel copies cause in out-of-SSA translation.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 8).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — A rotation of registers (for example a calling-convention shuffle that permutes argument registers cyclically) is the parallel move `cycleMoves ls`, and the toy move or swap counts become instruction counts if each move is one register copy and each swap one exchange instruction. The card then says that plain register copies alone, with no temporary and no exchange or xor instruction, cannot realize an isolated register cycle for arbitrary register contents; instructions that combine values are outside the model. The transfer assumes whole, non-overlapping locations (no sub-registers), one instruction per move or swap, and no register classes; it is not a statement about any compiler's implementation.

#### 9. `cycle-with-swaps-upper-bound`

- **Kind and tier:** theorem; T0. Classical decomposition of a cycle into transpositions.
- **Plain claim:** For a duplicate-free cycle l0, ..., l(k-1), the swaps (l0,l1), (l0,l2), ..., (l0,l(k-1)), executed in order, realize the cycle exactly at every location, from every store; there are ls.length - 1 of them, which is k - 1 for k ≥ 1 and 0 for the empty list (truncated subtraction).
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runSwaps_cycleSwaps`, `Toy.ParMove.length_cycleSwaps`.

```lean
-- lean/ToyParMove/Swaps.lean:124-125
theorem runSwaps_cycleSwaps {ls : List Loc} (hn : ls.Nodup) (σ : Loc → V) :
    runSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ

-- lean/ToyParMove/Swaps.lean:40
theorem length_cycleSwaps (ls : List Loc) : (cycleSwaps ls).length = ls.length - 1
```

- **Reading with key definitions unfolded (prose):**

```text
ls.Nodup → ∀ σ, runSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ;  (cycleSwaps ls).length = ls.length - 1
```

- **Hypothesis ledger:**
  - `hn : ls.Nodup` [applies to `runSwaps_cycleSwaps`]: with a repeated location the swap list and the target can diverge. Tightness: **tight (counterexample `Toy.ParMove.runSwaps_cycleSwaps_needs_nodup`)**.
- **Depth:** shallow
- **Non-vacuity witness:** [0,1,2] (2 swaps). (`Toy.ParMove.nonvacuity_runSwaps_cycleSwaps`)
- **Prior art:**
  - Standard fact about permutations: a k-cycle is a product of k - 1 transpositions and of no fewer. No single reference is relied on; the package proves both directions for its swap model. Boissinot et al. Section II (HAL inria-00349925v3) mention that a swap needs an extra copy 'unless an instruction can perform a swap', which is the setting of this result.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 9).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — A rotation of registers (for example a calling-convention shuffle that permutes argument registers cyclically) is the parallel move `cycleMoves ls`, and the toy move or swap counts become instruction counts if each move is one register copy and each swap one exchange instruction. The card then says k - 1 exchange instructions suffice for a k-cycle, with no temporary. The transfer assumes whole, non-overlapping locations (no sub-registers), one instruction per move or swap, and no register classes; it is not a statement about any compiler's implementation.

#### 10. `cycle-with-swaps-lower-bound`

- **Kind and tier:** theorem; T0. Classical: a k-cycle is not a product of fewer than k - 1 transpositions; mechanized by a union-find potential.
- **Plain claim:** Let ls be an isolated duplicate-free cycle of length k (the parallel move consists of exactly the cycle's moves cycleMoves ls). (a) Every list of swaps (over any locations) that turns a given injective store σ exactly into the cycle's target has at least ls.length - 1 swaps. (b) Over a value type with two distinct values, every list of swaps that turns every store exactly into the cycle's target has at least ls.length - 1 swaps. (ls.length - 1 is k - 1 for k ≥ 1 and 0 for k = 0.)
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.cycle_length_sub_one_le_of_injective_of_runSwaps`, `Toy.ParMove.cycle_length_sub_one_le_of_two_values_of_runSwaps`.

```lean
-- lean/ToyParMove/Swaps.lean:226-228
theorem cycle_length_sub_one_le_of_injective_of_runSwaps {ls : List Loc} {σ : Loc → V}
    {ss : List (Loc × Loc)} (hn : ls.Nodup) (hσ : Function.Injective σ)
    (hreal : runSwaps ss σ = pmove (cycleMoves ls) σ) : ls.length - 1 ≤ ss.length

-- lean/ToyParMove/Swaps.lean:272-275
theorem cycle_length_sub_one_le_of_two_values_of_runSwaps {ls : List Loc}
    {ss : List (Loc × Loc)} (a b : V) (hab : a ≠ b) (hn : ls.Nodup)
    (hreal : ∀ σ : Loc → V, runSwaps ss σ = pmove (cycleMoves ls) σ) :
    ls.length - 1 ≤ ss.length
```

- **Reading with key definitions unfolded (prose):**

```text
(a) ls.Nodup → Function.Injective σ → runSwaps ss σ = pmove (cycleMoves ls) σ → ls.length - 1 ≤ ss.length;  (b) (a b : V) → a ≠ b → ls.Nodup → (∀ σ : Loc → V, runSwaps ss σ = pmove (cycleMoves ls) σ) → ls.length - 1 ≤ ss.length
```

- **Hypothesis ledger:**
  - `hn : ls.Nodup`: with a repeated location the target can be a single transposition. Tightness: **tight (counterexamples `Toy.ParMove.swap_lower_bound_needs_nodup`, `Toy.ParMove.swap_lower_bound_uniform_needs_nodup`)**.
  - `hσ : Function.Injective σ (statement a)` [applies to `cycle_length_sub_one_le_of_injective_of_runSwaps`]: with equal values no swap is needed. Tightness: **tight (counterexample `Toy.ParMove.swap_lower_bound_needs_injective`)**.
  - `hreal (statement a: the swaps realize the cycle exactly from σ)` [applies to `cycle_length_sub_one_le_of_injective_of_runSwaps`]: premise. Tightness: **tight (counterexample `Toy.ParMove.swap_lower_bound_needs_realization`)**.
  - `hab : a ≠ b (statement b)` [applies to `cycle_length_sub_one_le_of_two_values_of_runSwaps`]: over a one-element value type the empty list works on every store. Tightness: **tight (counterexample `Toy.ParMove.swap_lower_bound_uniform_needs_two_values`)**.
  - `hreal (statement b: the swaps realize the cycle exactly on every store)` [applies to `cycle_length_sub_one_le_of_two_values_of_runSwaps`]: premise. Tightness: **tight (counterexample `Toy.ParMove.swap_lower_bound_uniform_needs_realization`)**.
- **Depth:** substantive
- **Non-vacuity witness:** [0,1,2] realized by its 2 swaps (the bound is attained), from σ = id on Nat and from every Bool store. (`Toy.ParMove.nonvacuity_swap_lower_bound`, `Toy.ParMove.nonvacuity_swap_lower_bound_uniform`)
- **Prior art:**
  - Standard fact about permutations: a k-cycle is a product of k - 1 transpositions and of no fewer. No single reference is relied on; the package proves both directions for its swap model. Boissinot et al. Section II (HAL inria-00349925v3) mention that a swap needs an extra copy 'unless an instruction can perform a swap', which is the setting of this result.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 10).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — A rotation of registers (for example a calling-convention shuffle that permutes argument registers cyclically) is the parallel move `cycleMoves ls`, and the toy move or swap counts become instruction counts if each move is one register copy and each swap one exchange instruction. The card then says fewer than k - 1 exchange instructions cannot realize an isolated k-cycle when register values can be arbitrary. The transfer assumes whole, non-overlapping locations (no sub-registers), one instruction per move or swap, and no register classes; it is not a statement about any compiler's implementation.

#### 11. `xor-swap-correct-iff-distinct-or-zero`

- **Kind and tier:** characterization; T0. The xor-swap (Warren Section 2-20) and its aliasing failure are folklore; restated and proved for BitVec stores.
- **Plain claim:** Over w-bit words, the sequence a ^= b; b ^= a; a ^= b exchanges the contents of locations a and b when a ≠ b, and when a = b it sets that location to zero and leaves all others unchanged; hence it equals the true swap exactly when a ≠ b or the aliased (common) operand holds zero.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.xorSwap_eq_swapStore_iff`, `Toy.ParMove.xorSwap_eq_swapStore_of_ne`, `Toy.ParMove.xorSwap_self`.

```lean
-- lean/ToyParMove/XorSwap.lean:61-62
theorem xorSwap_eq_swapStore_iff (σ : Loc → BitVec w) (a b : Loc) :
    xorSwap σ a b = swapStore σ a b ↔ (a ≠ b ∨ σ a = 0#w)

-- lean/ToyParMove/XorSwap.lean:32-33
theorem xorSwap_eq_swapStore_of_ne {a b : Loc} (hab : a ≠ b) (σ : Loc → BitVec w) :
    xorSwap σ a b = swapStore σ a b

-- lean/ToyParMove/XorSwap.lean:53
theorem xorSwap_self (σ : Loc → BitVec w) (a : Loc) : xorSwap σ a a = upd σ a 0#w
```

- **Reading with key definitions unfolded (prose):**

```text
∀ σ a b, xorSwap σ a b = swapStore σ a b ↔ (a ≠ b ∨ σ a = 0#w);  a ≠ b → ∀ σ, xorSwap σ a b = swapStore σ a b;  ∀ σ a, xorSwap σ a a = upd σ a 0#w
```

- **Hypothesis ledger:**
  - `hab : a ≠ b (for xorSwap_eq_swapStore_of_ne)` [applies to `xorSwap_eq_swapStore_of_ne`]: aliased operands are zeroed instead of left alone. Tightness: **tight (counterexample `Toy.ParMove.xorSwap_eq_swapStore_needs_ne`)**.
- **Depth:** shallow
- **Non-vacuity witness:** 8-bit values 0x5A at location 0 and 0xC3 at location 1. (`Toy.ParMove.nonvacuity_xorSwap`)
- **Prior art:**
  - Warren. Hacker's Delight, 2nd edition (2012), Section 2-20 'Exchanging Registers' (publisher's online excerpt at InformIT): 'A very old trick is exchanging the contents of two registers without using a third' (the three exclusive-or sequence). The section does not discuss aliased operands; it also covers exchanging two fields of the same register with masks.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 11).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — `xorSwap` models the three exclusive-or exchange (Warren, Hacker's Delight, Section 2-20) on whole registers of one fixed width. The aliasing failure transfers to any implementation in which both operands name the same full register (for example after register allocation assigns both values of a parallel swap to one register). Overlapping register names and 32-bit xor instructions that zero-extend into 64-bit registers are outside the model and can break the exchange in ways the card does not cover.

#### 12. `xor-swap-sequences-sound-without-self-swaps`

- **Kind and tier:** theorem; T0. Direct consequence of the xor-swap characterization.
- **Plain claim:** A list of swaps none of which is a self-swap behaves the same, on every store of w-bit words, whether each swap is a true exchange or the xor-swap idiom; in particular the xor-swap implementation of the cycle swaps cycleSwaps ls realizes a duplicate-free cycle ls exactly.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runXorSwaps_eq_runSwaps_of_no_self`, `Toy.ParMove.runXorSwaps_cycleSwaps`.

```lean
-- lean/ToyParMove/XorSwap.lean:85-87
theorem runXorSwaps_eq_runSwaps_of_no_self :
    ∀ {ss : List (Loc × Loc)}, (∀ p ∈ ss, p.1 ≠ p.2) → ∀ σ : Loc → BitVec w,
      runXorSwaps ss σ = runSwaps ss σ

-- lean/ToyParMove/XorSwap.lean:107-108
theorem runXorSwaps_cycleSwaps {ls : List Loc} (hn : ls.Nodup) (σ : Loc → BitVec w) :
    runXorSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ
```

- **Reading with key definitions unfolded (prose):**

```text
(∀ p ∈ ss, p.1 ≠ p.2) → ∀ σ, runXorSwaps ss σ = runSwaps ss σ;  ls.Nodup → ∀ σ, runXorSwaps (cycleSwaps ls) σ = pmove (cycleMoves ls) σ
```

- **Hypothesis ledger:**
  - `no self-swap in ss` [applies to `runXorSwaps_eq_runSwaps_of_no_self`]: a self-swap is zeroed by the idiom. Tightness: **tight (counterexample `Toy.ParMove.runXorSwaps_needs_no_self`)**.
  - `hn : ls.Nodup (corollary)` [applies to `runXorSwaps_cycleSwaps`]: a repeated cycle location can yield a self-swap (when l₀ recurs, as in [0, 1, 0]). Tightness: **tight (counterexample `Toy.ParMove.runXorSwaps_cycleSwaps_needs_nodup`)**.
- **Depth:** shallow
- **Non-vacuity witness:** The swap list [(0,1),(0,2)] (no self-swap), and the duplicate-free cycle [0,1,2]. (`Toy.ParMove.nonvacuity_runXorSwaps`)
- **Prior art:**
  - Warren. Hacker's Delight, 2nd edition (2012), Section 2-20 'Exchanging Registers' (publisher's online excerpt at InformIT): 'A very old trick is exchanging the contents of two registers without using a third' (the three exclusive-or sequence). The section does not discuss aliased operands; it also covers exchanging two fields of the same register with masks.
- **Design question:** Register allocators and code generators turn a parallel move (phi-resolution copies, calling-convention shuffles) into a sequence of moves, breaking cycles with a scratch register, swaps, or xor-swaps. Which sequentializations are exactly correct, and which side conditions (destination distinctness, scratch freshness, non-aliasing of swap operands) are necessary?
- **Non-claims:** listed under **Boundaries** (result 12).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — As for the xor characterization: a compiler emitting exchange sequences as xor triples on whole registers of one width must exclude self-exchanges; overlapping register names and zero-extending 32-bit xor instructions are outside the model.

#### 13. `preserve-upper-lane-write-is-very-well-behaved-lens`

- **Kind and tier:** theorem; T1. Folklore (a bit-field update is a lens), made precise for BitVec lanes; general lens hierarchies are mechanized elsewhere (Isabelle AFP Optics) but not for bit lanes.
- **Plain claim:** For a lane (off, wid) that fits in an n-bit register (off + wid ≤ n), reading the lane (getLane) and writing it while preserving all other bits (putLane) form a very well-behaved lens: GetPut, PutGet and PutPut hold. GetPut and PutPut hold even without the fit condition; only PutGet (and hence very-well-behavedness) uses it.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.putLane_veryWellBehaved_of_fits`, `Toy.ParMove.putLane_getPut`, `Toy.ParMove.putLane_putGet_of_fits`, `Toy.ParMove.putLane_putPut`.

```lean
-- lean/ToyParMove/Lanes.lean:156-157
theorem putLane_veryWellBehaved_of_fits {L : Lane} (hfit : L.Fits n) :
    VeryWellBehaved (getLane (n := n) L) (putLane L)

-- lean/ToyParMove/Lanes.lean:127
theorem putLane_getPut (L : Lane) : GetPut (getLane (n := n) L) (putLane L)

-- lean/ToyParMove/Lanes.lean:147
theorem putLane_putGet_of_fits {L : Lane} (hfit : L.Fits n) : PutGet (getLane (n := n) L) (putLane L)

-- lean/ToyParMove/Lanes.lean:139
theorem putLane_putPut (L : Lane) : PutPut (getLane (n := n) L) (putLane L)
```

- **Reading with key definitions unfolded (prose):**

```text
L.off + L.wid ≤ n → VeryWellBehaved (getLane L) (putLane L);  GetPut (getLane L) (putLane L);  L.off + L.wid ≤ n → PutGet (getLane L) (putLane L);  PutPut (getLane L) (putLane L)
```

- **Hypothesis ledger:**
  - `hfit : L.Fits n (for putLane_putGet_of_fits and putLane_veryWellBehaved_of_fits)` [applies to `putLane_putGet_of_fits`, `putLane_veryWellBehaved_of_fits`]: bits of the value beyond the register are lost. Tightness: **tight (counterexample `Toy.ParMove.putLane_putGet_needs_fits`)**.
- **Depth:** shallow
- **Non-vacuity witness:** The lane (8, 8) (x86 ah) in a 64-bit register. (`Toy.ParMove.nonvacuity_putLane_veryWellBehaved`)
- **Prior art:**
  - Foster, Greenwald, Moore, Pierce, Schmitt. "Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem." ACM TOPLAS 29(3), article 17, 2007, DOI 10.1145/1232420.1232424 (bibliographic record from dblp; content from the authors' final version). Section 3 'Semantic Foundations' defines the laws GetPut, PutGet and the optional PutPut, and calls a well-behaved lens that also satisfies PutPut 'very well behaved'. The package defines these laws itself for total functions.
  - Foster, Pardillo-Laursen, Zeyda. "Optics." Archive of Formal Proofs, May 25, 2017 (isa-afp.org/entries/Optics.html). Its abstract describes an Isabelle/HOL mechanisation of an algebraic hierarchy of lenses, including well-behaved and very well-behaved lenses, with a library of algebraic laws. General lens theory; it is not instantiated to bit lanes of machine words here.
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other?
- **Non-claims:** listed under **Boundaries** (result 13).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, an `al`, `ah` or `ax` write with the matching read is a very well-behaved lens on the 64-bit register. Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 14. `disjoint-lane-writes-commute-and-frame`

- **Kind and tier:** theorem; T1. Folklore, made precise.
- **Plain claim:** Writes to two lanes with disjoint bit ranges (one of them empty, or one ending before the other begins) commute, and writing one of them does not change what the other reads; neither statement needs the lanes to fit in the register.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.putLane_comm_of_disjoint`, `Toy.ParMove.getLane_putLane_of_disjoint`.

```lean
-- lean/ToyParMove/Lanes.lean:161-163
theorem putLane_comm_of_disjoint {L₁ L₂ : Lane} (hd : L₁.Disjoint L₂) (v₁ : BitVec L₁.wid)
    (v₂ : BitVec L₂.wid) (w : BitVec n) :
    putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)

-- lean/ToyParMove/Lanes.lean:175-176
theorem getLane_putLane_of_disjoint {L₁ L₂ : Lane} (hd : L₁.Disjoint L₂) (v : BitVec L₁.wid)
    (w : BitVec n) : getLane L₂ (putLane L₁ v w) = getLane L₂ w
```

- **Reading with key definitions unfolded (prose):**

```text
L₁.Disjoint L₂ → ∀ v₁ v₂ w, putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w);  L₁.Disjoint L₂ → ∀ v w, getLane L₂ (putLane L₁ v w) = getLane L₂ w.   Here L₁.Disjoint L₂ := L₁.wid = 0 ∨ L₂.wid = 0 ∨ L₁.off + L₁.wid ≤ L₂.off ∨ L₂.off + L₂.wid ≤ L₁.off, which is equivalent to disjointness of the bit sets [off, off + wid) (Lane.disjoint_iff_bits).
```

- **Hypothesis ledger:**
  - `hd : L₁.Disjoint L₂`: overlapping lanes share bits. Tightness: **tight (counterexamples `Toy.ParMove.putLane_overlapping_not_comm`, `Toy.ParMove.getLane_putLane_needs_disjoint`)**.
- **Depth:** shallow
- **Non-vacuity witness:** Lanes (0,8) and (8,8) (al and ah). (`Toy.ParMove.nonvacuity_putLane_comm`)
- **Prior art:**
  - Foster, Pardillo-Laursen, Zeyda. "Optics." Archive of Formal Proofs, May 25, 2017 (isa-afp.org/entries/Optics.html). Its abstract describes an Isabelle/HOL mechanisation of an algebraic hierarchy of lenses, including well-behaved and very well-behaved lenses, with a library of algebraic laws. General lens theory; it is not instantiated to bit lanes of machine words here.
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other?
- **Non-claims:** listed under **Boundaries** (result 14).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, writes to `al` and `ah` commute, and neither changes what the other lane reads; a 32-bit write is not covered (it zero-extends). Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 15. `lane-writes-commute-iff-disjoint`

- **Kind and tier:** characterization; T1. Folklore, made precise with the edge cases (empty lanes, lanes beyond the register) exposed.
- **Plain claim:** (a) For any two lanes and any register width n, all pairs of preserve-upper writes to the two lanes commute if and only if the lanes share no bit position below n. (b) If at least one of the two lanes fits in the n-bit register, all pairs of writes commute if and only if the lanes are Disjoint (disjoint bit ranges).
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.putLane_comm_iff_disjointIn`, `Toy.ParMove.putLane_comm_iff_disjoint_of_fits`.

```lean
-- lean/ToyParMove/Lanes.lean:189-191
theorem putLane_comm_iff_disjointIn (L₁ L₂ : Lane) :
    (∀ (v₁ : BitVec L₁.wid) (v₂ : BitVec L₂.wid) (w : BitVec n),
      putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)) ↔ L₁.DisjointIn n L₂

-- lean/ToyParMove/Lanes.lean:210-212
theorem putLane_comm_iff_disjoint_of_fits {L₁ L₂ : Lane} (hfit : L₁.Fits n ∨ L₂.Fits n) :
    (∀ (v₁ : BitVec L₁.wid) (v₂ : BitVec L₂.wid) (w : BitVec n),
      putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)) ↔ L₁.Disjoint L₂
```

- **Reading with key definitions unfolded (prose):**

```text
(a) (∀ v₁ v₂ (w : BitVec n), putLane L₁ v₁ (putLane L₂ v₂ w) = putLane L₂ v₂ (putLane L₁ v₁ w)) ↔ L₁.DisjointIn n L₂;  (b) (L₁.Fits n ∨ L₂.Fits n) → ((∀ v₁ v₂ w, ...) ↔ L₁.Disjoint L₂).   Here L₁.DisjointIn n L₂ := ∀ i < n, ¬ (L₁.off ≤ i < L₁.off + L₁.wid ∧ L₂.off ≤ i < L₂.off + L₂.wid).
```

- **Hypothesis ledger:**
  - `hfit : L₁.Fits n ∨ L₂.Fits n (statement b)` [applies to `putLane_comm_iff_disjoint_of_fits`]: lanes that overlap only beyond the register commute although their bit ranges intersect. Tightness: **tight (counterexample `Toy.ParMove.putLane_comm_iff_needs_fits`)**.
- **Depth:** shallow
- **Non-vacuity witness:** In 64 bits: al (0,8) and ah (8,8) (fit, disjoint, commute) and al (0,8) and ax (0,16) (fit, not disjoint, do not commute). (`Toy.ParMove.nonvacuity_putLane_comm_iff`, `Toy.ParMove.nonvacuity_putLane_comm_iff_disjointIn`)
- **Prior art:**
  - Foster, Pardillo-Laursen, Zeyda. "Optics." Archive of Formal Proofs, May 25, 2017 (isa-afp.org/entries/Optics.html). Its abstract describes an Isabelle/HOL mechanisation of an algebraic hierarchy of lenses, including well-behaved and very well-behaved lenses, with a library of algebraic laws. General lens theory; it is not instantiated to bit lanes of machine words here.
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other?
- **Non-claims:** listed under **Boundaries** (result 15).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, two 8-bit or 16-bit writes into one register commute for all values exactly when their bit ranges are disjoint (for example `al`/`ah` commute, `al`/`ax` do not). Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 16. `zero-extend-write-not-a-narrow-lens`

- **Kind and tier:** impossibility; T1. Folklore consequence of zero-extension, made precise for every getter.
- **Plain claim:** If wid < n, no getter whatsoever from n-bit words to wid-bit values makes the zero-extending write (which replaces the whole word by the zero-extended value) satisfy GetPut; in particular it is not a lens on the full word with a wid-bit view.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.writeZext_not_getPut_of_lt`.

```lean
-- lean/ToyParMove/Lanes.lean:273-274
theorem writeZext_not_getPut_of_lt {wid : Nat} (h : wid < n) :
    ¬ ∃ g : BitVec n → BitVec wid, GetPut g (writeZext n (wid := wid))
```

- **Reading with key definitions unfolded:**

```lean
wid < n → ¬ ∃ g : BitVec n → BitVec wid, GetPut g (writeZext n)
```

- **Hypothesis ledger:**
  - `h : wid < n`: at full width the low-lane getter works. Tightness: **tight (counterexample `Toy.ParMove.writeZext_not_getPut_needs_lt`)**.
- **Depth:** shallow
- **Non-vacuity witness:** wid = 32, n = 64 (x86-64 32-bit writes, AArch64 W writes). (`Toy.ParMove.nonvacuity_writeZext`)
- **Positive controls** (nearby settings where the conclusion fails, each proved): `Toy.ParMove.writeZext_getPut_full`. See also the escape hatches under **Boundaries**.
- **Prior art:**
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
  - Arm, 'Learn the architecture - A64 Instruction Set Architecture Guide' (document 102374, version 1.4), page 'Registers in AArch64 - general-purpose registers': 'When a W register is written, as seen in the example above, the top 32 bits of the 64-bit register are zeroed.' Role: documentation (the normative Arm Architecture Reference Manual is not cited). Modeling bridge only.
  - Foster, Greenwald, Moore, Pierce, Schmitt. "Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem." ACM TOPLAS 29(3), article 17, 2007, DOI 10.1145/1232420.1232424 (bibliographic record from dblp; content from the authors' final version). Section 3 'Semantic Foundations' defines the laws GetPut, PutGet and the optional PutPut, and calls a well-behaved lens that also satisfies PutPut 'very well behaved'. The package defines these laws itself for total functions.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other?
- **Non-claims:** listed under **Boundaries** (result 16).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, a 32-bit write (x86-64 `eax`, AArch64 `W`) is not a lens with a 32-bit view of the 64-bit register: writing back the low 32 bits just read clears a nonzero upper half, so no getter makes GetPut hold. Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 17. `zero-extend-write-getput-iff-upper-bits-zero`

- **Kind and tier:** characterization; T1. Folklore, made precise.
- **Plain claim:** Writing back the low wid bits of an n-bit word w with a zero-extending write leaves w unchanged if and only if every bit of w at a position ≥ wid is zero.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.writeZext_getPut_iff`.

```lean
-- lean/ToyParMove/Lanes.lean:254-255
theorem writeZext_getPut_iff {wid : Nat} (w : BitVec n) :
    writeZext n (getLane ⟨0, wid⟩ w) w = w ↔ ∀ i, wid ≤ i → w.getLsbD i = false
```

- **Reading with key definitions unfolded:**

```lean
∀ w : BitVec n, writeZext n (getLane ⟨0, wid⟩ w) w = w ↔ ∀ i, wid ≤ i → w.getLsbD i = false
```

- **Hypothesis ledger:** none (unconditional characterization, universally quantified over `n`, `wid` and `w`; no side-condition hypotheses).
- **Depth:** shallow
- **Non-vacuity witness:** 0x00000000DEADBEEF (holds) and 0x1122334455667788 (fails) with wid = 32, n = 64. (`Toy.ParMove.nonvacuity_writeZext_getPut_iff`)
- **Prior art:**
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
  - Arm, 'Learn the architecture - A64 Instruction Set Architecture Guide' (document 102374, version 1.4), page 'Registers in AArch64 - general-purpose registers': 'When a W register is written, as seen in the example above, the top 32 bits of the 64-bit register are zeroed.' Role: documentation (the normative Arm Architecture Reference Manual is not cited). Modeling bridge only.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other?
- **Non-claims:** listed under **Boundaries** (result 17).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, writing back the low 32 bits of a 64-bit register with a 32-bit write leaves it unchanged exactly when its upper 32 bits are zero. Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 18. `zero-extend-write-is-full-word-replacement`

- **Kind and tier:** theorem; T0. Reference point: unfolds what a zero-extending write is in lane terms; companion to zero-extend-write-not-a-narrow-lens.
- **Plain claim:** A zero-extending write writeZext n v of a wid-bit value equals the full-width lane write (0, n) of v.setWidth n (the zero-extended value when wid ≤ n, the truncated value when wid > n), and the full-width lane is a very well-behaved lens; with the low-lane getter (0, wid), the zero-extending write satisfies PutGet when wid ≤ n and PutPut always.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.writeZext_eq_putLane_full`, `Toy.ParMove.putLane_full_veryWellBehaved`, `Toy.ParMove.writeZext_putGet_of_le`, `Toy.ParMove.writeZext_putPut`.

```lean
-- lean/ToyParMove/Lanes.lean:223-224
theorem writeZext_eq_putLane_full {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    writeZext n v w = putLane ⟨0, n⟩ (v.setWidth n) w

-- lean/ToyParMove/Lanes.lean:232-233
theorem putLane_full_veryWellBehaved :
    VeryWellBehaved (getLane (n := n) ⟨0, n⟩) (putLane ⟨0, n⟩)

-- lean/ToyParMove/Lanes.lean:237-238
theorem writeZext_putGet_of_le {wid : Nat} (h : wid ≤ n) :
    PutGet (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid))

-- lean/ToyParMove/Lanes.lean:249-250
theorem writeZext_putPut {wid : Nat} :
    PutPut (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid))
```

- **Reading with key definitions unfolded (prose):**

```text
∀ v w, writeZext n v w = putLane ⟨0, n⟩ (v.setWidth n) w;  VeryWellBehaved (getLane ⟨0, n⟩) (putLane ⟨0, n⟩);  wid ≤ n → PutGet (getLane ⟨0, wid⟩) (writeZext n);  PutPut (getLane ⟨0, wid⟩) (writeZext n)
```

- **Hypothesis ledger:**
  - `h : wid ≤ n (for writeZext_putGet_of_le)` [applies to `writeZext_putGet_of_le`]: a value wider than the register can lose bits. Tightness: **tight (counterexample `Toy.ParMove.writeZext_putGet_needs_fit`)**.
- **Depth:** shallow
- **Non-vacuity witness:** wid = 32 ≤ n = 64. (`Toy.ParMove.nonvacuity_writeZext`)
- **Prior art:**
  - Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
  - Arm, 'Learn the architecture - A64 Instruction Set Architecture Guide' (document 102374, version 1.4), page 'Registers in AArch64 - general-purpose registers': 'When a W register is written, as seen in the example above, the top 32 bits of the 64-bit register are zeroed.' Role: documentation (the normative Arm Architecture Reference Manual is not cited). Modeling bridge only.
- **Design question:** Partial writes to sub-registers (x86-64 al/ah/ax/eax/rax, AArch64 w/x) either zero-extend into the full register or preserve the other bits. Which algebraic laws describe these writes, and when do two lane writes commute or frame each other? (Reference point.)
- **Non-claims:** listed under **Boundaries** (result 18).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Under the modeling bridges stated above (**Findings → Modeling bridges**; Intel SDM Vol. 1, Section 3.4.1.1, paraphrased; Arm document 102374 v1.4, quoted): 8-bit and 16-bit general-purpose register writes on x86-64 behave like `putLane` on lanes `(0,8)` (`al`), `(8,8)` (`ah`) and `(0,16)` (`ax`) of a 64-bit word, and 32-bit writes on x86-64 and `W`-register writes on AArch64 behave like `writeZext 64` with `wid = 32`. Under this correspondence, a 32-bit write is a full 64-bit replacement by the zero-extended value, a very well-behaved lens whose view is the whole register. Operand encodability, flags, timing and partial-register stalls are not modeled, so this says nothing about which such instructions exist or how fast they are.

#### 19. `distinct-lane-destinations-not-enough`

- **Kind and tier:** counterexample; T0. Concrete instance of a known requirement (Rideau-Serpette-Leroy Section 8 and CompCert's overlap extension assume pairwise-disjoint destinations).
- **Plain claim:** With registers indexed by Nat, 16-bit words, and the register file regs16 (register 0 holds 0x1234, register 1 holds 0xABCD, all others 0), the parallel lane move M = [lm 0 0 1 0 8, lm 0 0 2 0 16] (write register 1's low byte into register 0's low byte, and register 2's low 16 bits into register 0's low 16 bits) has distinct (register, lane) destinations, violates LaneWF, and its two orders give different values in register 0. This one instance shows that distinct (register, lane) destinations (DistinctDstLanes) do not imply LaneWF and do not make the parallel lane move independent of the order of the list; it does not show which condition suffices (see the non-claims).
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.lanePMove_distinct_dst_lanes_not_enough`.

```lean
-- lean/ToyParMove/LaneMoves.lean:237-240
theorem lanePMove_distinct_dst_lanes_not_enough :
    DistinctDstLanes [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧ ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 0 ≠
      lanePMove [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 0
```

- **Reading with key definitions unfolded (prose):**

```text
DistinctDstLanes [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧ ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧ lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 0 ≠ lanePMove [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 0.   Here lm dreg doff sreg soff wid copies wid bits from bit soff of register sreg to bit doff of register dreg, and regs16 r := if r = 0 then 0x1234#16 else if r = 1 then 0xABCD#16 else 0#16.
```

- **Hypothesis ledger:** none (a concrete instance; no hypotheses).
- **Depth:** definitional
- **Non-vacuity witness:** The statement is itself a concrete instance.
- **Prior art:**
  - CompCert lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861, section 'Extension to partially overlapping registers' (also Rideau-Serpette-Leroy Section 8): parmove2_correctness_with_overlap (lines 1588-1596) assumes, for a source list sl and a destination list dl: equal lengths; every source and every destination disjoint from every temporary (disjoint_temps); pairwise-disjoint destinations (pairwise_disjoint dl); no partial overlap between any source and any destination; and no partial overlap among temporaries (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2). Here no_overlap r1 r2 means that r1 and r2 are equal or disjoint. A write sets its target and leaves the other registers that are not disjoint from the target undefined (weak_update). Different model from this package's exact bit-lane writes.
- **Design question:** When the destinations of a parallel move are lanes of registers, what must replace 'distinct destinations' for the parallel move to be well defined and for a sequential emission order to realize it?
- **Non-claims:** listed under **Boundaries** (result 19).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lane moves model a parallel copy between sub-register lanes in which every write keeps the other bits (the x86-64 8-bit and 16-bit case under the modeling bridges stated above in **Findings → Modeling bridges**); they do not model 32-bit moves, which zero-extend. Under this correspondence, distinct (register, lane) names do not make a sub-register parallel copy well defined: `al` and `ax` destinations overlap. Which lanes are real operands is not modeled.

#### 20. `lane-parallel-move-order-independent-for-disjoint-lanes`

- **Kind and tier:** theorem; T1. Lane analogue of order independence for distinct destinations; folklore made precise.
- **Plain claim:** If the destination lanes of lane moves into the same register are pairwise disjoint (LaneWF M) and M' is a reordering of M, then the parallel lane-move semantics (all sources read from the old register file, then all destination lanes written) of M and M' agree on every register file.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.lanePMove_perm_invariant_of_laneWF`.

```lean
-- lean/ToyParMove/LaneMoves.lean:121-122
theorem lanePMove_perm_invariant_of_laneWF {M M' : List (LaneMove R)} (hwf : LaneWF M)
    (hp : M.Perm M') (ρ : R → BitVec n) : lanePMove M ρ = lanePMove M' ρ
```

- **Reading with key definitions unfolded (prose):**

```text
LaneWF M → M.Perm M' → ∀ ρ, lanePMove M ρ = lanePMove M' ρ.   Here LaneWF M := M.Pairwise (fun m₁ m₂ => m₁.dreg = m₂.dreg → m₁.dst.Disjoint m₂.dst).
```

- **Hypothesis ledger:**
  - `hwf : LaneWF M`: overlapping destination lanes can make the result order dependent. Tightness: **tight (counterexample `Toy.ParMove.lanePMove_perm_needs_laneWF`)**.
  - `hp : M.Perm M'`: the other list must consist of the same lane moves. Tightness: **tight (counterexample `Toy.ParMove.lanePMove_perm_needs_perm`)**.
- **Depth:** shallow
- **Non-vacuity witness:** The in-register byte swap [r0.(0,8) ← r0.(8,8), r0.(8,8) ← r0.(0,8)] and its reordering. (`Toy.ParMove.nonvacuity_lanePMove_perm`)
- **Prior art:**
  - CompCert lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861, section 'Extension to partially overlapping registers' (also Rideau-Serpette-Leroy Section 8): parmove2_correctness_with_overlap (lines 1588-1596) assumes, for a source list sl and a destination list dl: equal lengths; every source and every destination disjoint from every temporary (disjoint_temps); pairwise-disjoint destinations (pairwise_disjoint dl); no partial overlap between any source and any destination; and no partial overlap among temporaries (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2). Here no_overlap r1 r2 means that r1 and r2 are equal or disjoint. A write sets its target and leaves the other registers that are not disjoint from the target undefined (weak_update). Different model from this package's exact bit-lane writes.
- **Design question:** When the destinations of a parallel move are lanes of registers, what must replace 'distinct destinations' for the parallel move to be well defined and for a sequential emission order to realize it?
- **Non-claims:** listed under **Boundaries** (result 20).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lane moves model a parallel copy between sub-register lanes in which every write keeps the other bits (the x86-64 8-bit and 16-bit case under the modeling bridges stated above in **Findings → Modeling bridges**); they do not model 32-bit moves, which zero-extend. Under this correspondence, a sub-register parallel copy whose destination lanes are pairwise bit-disjoint within each register is order independent. Which lanes are real operands is not modeled.

#### 21. `lane-parallel-move-sound-for-disjoint-lanes-topological-order`

- **Kind and tier:** theorem; T1. Lane analogue of the topological-order theorem; Rideau-Serpette-Leroy Section 8 (and CompCert's overlap extension) prove a related statement in a different model.
- **Plain claim:** If a parallel lane move M has pairwise disjoint destination lanes per register (LaneWF M) and ms is a reordering of M in which no move writes bits that a later move reads (LaneTopological ms), then executing ms sequentially yields exactly the parallel lane move M, on every register file.
- **Lean statement** (verbatim; proofs omitted): `Toy.ParMove.runLanes_eq_lanePMove_of_laneWF_of_topological`.

```lean
-- lean/ToyParMove/LaneMoves.lean:159-161
theorem runLanes_eq_lanePMove_of_laneWF_of_topological {M ms : List (LaneMove R)}
    (hwf : LaneWF M) (hp : ms.Perm M) (htop : LaneTopological ms) (ρ : R → BitVec n) :
    runLanes ms ρ = lanePMove M ρ
```

- **Reading with key definitions unfolded (prose):**

```text
LaneWF M → ms.Perm M → LaneTopological ms → ∀ ρ, runLanes ms ρ = lanePMove M ρ.   Here LaneTopological ms := ms.Pairwise (fun e l => e.dreg = l.sreg → e.dst.Disjoint l.src).
```

- **Hypothesis ledger:**
  - `hwf : LaneWF M`: with overlapping destination lanes the emitted order can decide which bits win. Tightness: **tight (counterexample `Toy.ParMove.runLanes_needs_laneWF`)**.
  - `hp : ms.Perm M`: the emitted list must consist of the moves of M. Tightness: **tight (counterexample `Toy.ParMove.runLanes_needs_perm`)**.
  - `htop : LaneTopological ms`: a move that overwrites bits a later move reads can change what is copied. Tightness: **tight (counterexample `Toy.ParMove.runLanes_needs_topological`)**.
- **Depth:** shallow
- **Non-vacuity witness:** Inside register 0: shift bytes down ([0,8) ← [8,16), [8,16) ← [16,24)) emitted reader-first, which exercises lane disjointness within one register; also, across registers, r2.(0,8) ← r1.(0,8) emitted before r1.(0,8) ← r0.(0,8). (`Toy.ParMove.nonvacuity_runLanes_same_register`, `Toy.ParMove.nonvacuity_runLanes`)
- **Prior art:**
  - CompCert lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861, section 'Extension to partially overlapping registers' (also Rideau-Serpette-Leroy Section 8): parmove2_correctness_with_overlap (lines 1588-1596) assumes, for a source list sl and a destination list dl: equal lengths; every source and every destination disjoint from every temporary (disjoint_temps); pairwise-disjoint destinations (pairwise_disjoint dl); no partial overlap between any source and any destination; and no partial overlap among temporaries (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2). Here no_overlap r1 r2 means that r1 and r2 are equal or disjoint. A write sets its target and leaves the other registers that are not disjoint from the target undefined (weak_update). Different model from this package's exact bit-lane writes.
  - Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
- **Design question:** When the destinations of a parallel move are lanes of registers, what must replace 'distinct destinations' for the parallel move to be well defined and for a sequential emission order to realize it?
- **Non-claims:** listed under **Boundaries** (result 21).

Basis: execution (Lean kernel check) — the theorems above, and every name in the ledger and witness lines, are kernel-checked under `leanprover/lean4:v4.34.1`; axioms and hashes are listed under **Evidence**.

Basis: derived (modeling bridge) — Lane moves model a parallel copy between sub-register lanes in which every write keeps the other bits (the x86-64 8-bit and 16-bit case under the modeling bridges stated above in **Findings → Modeling bridges**); they do not model 32-bit moves, which zero-extend. Under this correspondence, such a parallel copy can be emitted as sequential preserve-upper lane copies in any lane-topological order. Which lanes are real operands, and how to break cyclic lane copies, is not modeled.

### Supporting theorems cited in the text

Every uncarded theorem of the library that is cited in the definitions, the card text or the
non-claims, quoted verbatim from the source (proofs omitted), in file order. They are
kernel-checked like everything else in the library but are not card results and carry no recorded
statement hash; their axioms are listed under **Evidence** (from `audit/axioms.json`) and are
printed by `lean/RevalidationAudit.lean`. Each entry is labelled as either a universally
quantified theorem or a concrete instance; a concrete instance establishes only that one case, so
wherever the text cites one it is an example or a counterexample to a universal claim, never
evidence for one. The definition examples are quoted under **Definitions**.

```lean
-- lean/ToyParMove/Basic.lean:119
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem functional_of_wellFormed {M : List (Loc × Loc)} (h : WellFormed M) : Functional M

-- lean/ToyParMove/Basic.lean:163-164
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_comp {W : Type} (f : V → W) : ∀ (ms : List (Loc × Loc)) (τ : Loc → V),
    runSeq ms (f ∘ τ) = f ∘ runSeq ms τ

-- lean/ToyParMove/Basic.lean:169-170
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem pmove_comp {W : Type} (f : V → W) (M : List (Loc × Loc)) (τ : Loc → V) :
    pmove M (f ∘ τ) = f ∘ pmove M τ

-- lean/ToyParMove/Basic.lean:187-188
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_eq_pmove_of_id {ms M : List (Loc × Loc)}
    (h : runSeq ms (id : Loc → Loc) = pmove M id) (σ : Loc → V) : runSeq ms σ = pmove M σ

-- lean/ToyParMove/Basic.lean:203-205
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem runSeq_eq_pmove_at_id_of_forall {ms M : List (Loc × Loc)} {l : Loc} (a b : V)
    (hab : a ≠ b) (h : ∀ σ : Loc → V, runSeq ms σ l = pmove M σ l) :
    runSeq ms (id : Loc → Loc) l = pmove M id l

-- lean/ToyParMove/Readings.lean:38-39
-- lean/ToyParMove/Readings.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem functional_duplicate_not_wellFormed :
    Functional [((0 : Nat), (1 : Nat)), (0, 1)] ∧ ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 1)]

-- lean/ToyParMove/Readings.lean:188-189
-- lean/ToyParMove/Readings.lean — universally quantified theorem
theorem pmove_eq_pmoveLast_of_wellFormed {M : List (Loc × Loc)} (hM : WellFormed M)
    (σ : Loc → V) : pmove M σ = pmoveLast M σ

-- lean/ToyParMove/Readings.lean:196-198
-- lean/ToyParMove/Readings.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem pmove_readings_agree_on_equal_source_values :
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l) =
      pmoveLast [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l)

-- lean/ToyParMove/Sequentialize.lean:311-312
-- lean/ToyParMove/Sequentialize.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_emits_duplicates_example :
    sequentialize (9 : Nat) [(0, 1), (0, 1), (1, 0)] = [(9, 0), (0, 1), (0, 1), (1, 9)]

-- lean/ToyParMove/Necessity.lean:51-56
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_loses_tmp_destination :
    Functional [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∈ dsts [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    runSeq (sequentialize 0 [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] (id : Nat → Nat) 0 = 3

-- lean/ToyParMove/Necessity.lean:62-66
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_clobbers_tmp :
    (0 : Nat) ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    runSeq (sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((1 : Nat), (2 : Nat)), (2, 1)] (id : Nat → Nat) 0 = 0

-- lean/ToyParMove/Necessity.lean:72-78
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_works_with_tmp_self_move :
    Functional [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∧
    ¬ ((0 : Nat) ∉ dsts [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∨
       (0 : Nat) ∉ srcs [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) ∧
    ∀ (σ : Nat → Nat) (l : Nat), l ≠ 0 →
      runSeq (sequentialize 0 [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) σ l =
        pmove [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] σ l

-- lean/ToyParMove/Necessity.lean:321-324
-- lean/ToyParMove/Necessity.lean — single concrete move list (all value types and stores); it proves nothing beyond this list
theorem topological_rejects_benign_self_move :
    ¬ Topological [((1 : Nat), (1 : Nat)), (2, 1)] ∧
    ∀ (V : Type) (σ : Nat → V),
      runSeq [((1 : Nat), (1 : Nat)), (2, 1)] σ = pmove [((1 : Nat), (1 : Nat)), (2, 1)] σ

-- lean/ToyParMove/Necessity.lean:338-340
-- lean/ToyParMove/Necessity.lean — universally quantified theorem
theorem not_topological_of_dsts_read {ms C : List (Loc × Loc)} (hC : C ≠ [])
    (hsub : ∀ m ∈ C, m ∈ ms) (hread : ∀ m ∈ C, ∃ m' ∈ C, m' ≠ m ∧ m'.2 = m.1) :
    ¬ Topological ms

-- lean/ToyParMove/Necessity.lean:405-406
-- lean/ToyParMove/Necessity.lean — universally quantified theorem
theorem runSeq_eq_pmoveLast_of_topological :
    ∀ {ms : List (Loc × Loc)}, Topological ms → ∀ σ : Loc → V, runSeq ms σ = pmoveLast ms σ

-- lean/ToyParMove/Cycles.lean:379-380
-- lean/ToyParMove/Cycles.lean — universally quantified theorem
theorem not_topological_of_perm_cycleMoves {ls : List Loc} {ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length) (hp : ms.Perm (cycleMoves ls)) : ¬ Topological ms

-- lean/ToyParMove/Cycles.lean:423
-- lean/ToyParMove/Cycles.lean — universally quantified over all stores Nat → Bool
theorem no_injective_store_nat_bool : ∀ σ : Nat → Bool, ¬ Function.Injective σ

-- lean/ToyParMove/CycleTightness.lean:411-415
-- lean/ToyParMove/CycleTightness.lean — finite check of four concrete instances (k = 2, 3, 4, 5); not a general theorem
theorem sequentialize_cycle_length_examples :
    (sequentialize (9 : Nat) (cycleMoves [0, 1])).length = 3 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2])).length = 4 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3])).length = 5 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3, 4])).length = 6

-- lean/ToyParMove/Swaps.lean:54-55
-- lean/ToyParMove/Swaps.lean — universally quantified theorem
theorem runSwaps_comp (f : V → W) : ∀ (ss : List (Loc × Loc)) (τ : Loc → V),
    runSwaps ss (f ∘ τ) = f ∘ runSwaps ss τ

-- lean/ToyParMove/Swaps.lean:312-313
-- lean/ToyParMove/Swaps.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem length_cycleSwaps_nil :
    (cycleSwaps ([] : List Nat)).length = 0 ∧ ([] : List Nat).length - 1 = 0

-- lean/ToyParMove/XorSwap.lean:118-121
-- lean/ToyParMove/XorSwap.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem xorSwap_unsafe_for_aliased_parallel_swap :
    pmove [((0 : Nat), (0 : Nat)), (0, 0)] (fun _ : Nat => (1#8 : BitVec 8)) 0 = 1#8 ∧
    swapStore (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 1#8 ∧
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 0#8

-- lean/ToyParMove/XorSwap.lean:161-162
-- lean/ToyParMove/XorSwap.lean — universally quantified over stores Nat → BitVec 0 and locations a, b : Nat
theorem xorSwap_eq_swapStore_width_zero (σ : Nat → BitVec 0) (a b : Nat) :
    xorSwap σ a b = swapStore σ a b

-- lean/ToyParMove/Lanes.lean:67-69
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem Lane.disjoint_iff_bits (L₁ L₂ : Lane) :
    L₁.Disjoint L₂ ↔
      ∀ i, ¬ (L₁.off ≤ i ∧ i < L₁.off + L₁.wid ∧ L₂.off ≤ i ∧ i < L₂.off + L₂.wid)

-- lean/ToyParMove/Lanes.lean:110-112
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem getLsbD_putLane (L : Lane) (v : BitVec L.wid) (w : BitVec n) {i : Nat} (hi : i < n) :
    (putLane L v w).getLsbD i =
      if L.off ≤ i ∧ i < L.off + L.wid then v.getLsbD (i - L.off) else w.getLsbD i

-- lean/ToyParMove/Lanes.lean:289-290
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_getPut_of_ge {wid : Nat} (h : n ≤ wid) :
    GetPut (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid))

-- lean/ToyParMove/Lanes.lean:296-297
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_upper_zero {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    ∀ i, wid ≤ i → (writeZext n v w).getLsbD i = false

-- lean/ToyParMove/Lanes.lean:355
-- lean/ToyParMove/Lanes.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8

-- lean/ToyParMove/LaneMoves.lean:138-140
-- lean/ToyParMove/LaneMoves.lean — universally quantified theorem
theorem runLanes_eq_lanePMove_of_topological :
    ∀ {ms : List (LaneMove R)}, LaneTopological ms → ∀ ρ : R → BitVec n,
      runLanes ms ρ = lanePMove ms ρ

-- lean/ToyParMove/LaneMoves.lean:168-170
-- lean/ToyParMove/LaneMoves.lean — universally quantified theorem
theorem laneWF_implies_distinctDstLanes_of_pos_wid {R : Type} [DecidableEq R]
    {M : List (LaneMove R)} (hwf : LaneWF M) (hpos : ∀ m ∈ M, 0 < m.wid) :
    DistinctDstLanes M

-- lean/ToyParMove/LaneMoves.lean:269-270
-- lean/ToyParMove/LaneMoves.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem laneWF_not_implies_distinctDstLanes_width_zero :
    LaneWF [lm 0 4 1 0 0, lm 0 4 2 0 0] ∧ ¬ DistinctDstLanes [lm 0 4 1 0 0, lm 0 4 2 0 0]

-- lean/ToyParMove/LaneMoves.lean:330-333
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (all reorderings, all 16-bit register files); it proves nothing beyond this list
theorem lanePMove_perm_invariant_duplicate_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 8] ∧
    ∀ (M' : List (LaneMove Nat)), M'.Perm [lm 0 0 1 0 8, lm 0 0 1 0 8] →
      ∀ ρ : Nat → BitVec 16, lanePMove M' ρ = lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 8] ρ

-- lean/ToyParMove/LaneMoves.lean:339-342
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (both orders, all 16-bit register files); it proves nothing beyond this list
theorem lanePMove_same_source_overlap_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 16] ∧
    ∀ ρ : Nat → BitVec 16,
      lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 16] ρ = lanePMove [lm 0 0 1 0 16, lm 0 0 1 0 8] ρ

-- lean/ToyParMove/LaneMoves.lean:360-363
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (both orders, all 8-bit register files); it proves nothing beyond this list
theorem lanePMove_beyond_register_overlap_not_laneWF :
    ¬ LaneWF [lm 0 6 1 0 4, lm 0 8 1 0 4] ∧
    ∀ ρ : Nat → BitVec 8,
      lanePMove [lm 0 6 1 0 4, lm 0 8 1 0 4] ρ = lanePMove [lm 0 8 1 0 4, lm 0 6 1 0 4] ρ

-- lean/ToyParMove/LaneMoves.lean:376-379
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (all 16-bit register files); it proves nothing beyond this list
theorem laneTopological_rejects_benign_self_copy :
    ¬ LaneTopological [lm 0 0 0 0 8, lm 1 0 0 0 8] ∧
    ∀ ρ : Nat → BitVec 16,
      runLanes [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ = lanePMove [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ

-- lean/ToyParMove/Boundaries.lean:28-31
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem not_topological_of_contains_cycleMoves {ls : List Loc} {M ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length)
    (hsub : ∀ m ∈ cycleMoves ls, m ∈ M) (hp : ms.Perm M) :
    ¬ Topological ms

-- lean/ToyParMove/Boundaries.lean:141-146
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem cycle_length_sub_one_le_of_injOn_of_runSwaps
    {ls : List Loc} {σ : Loc → V} {ss : List (Loc × Loc)}
    (hn : ls.Nodup)
    (hinj : ∀ x ∈ ls, ∀ y ∈ ls, σ x = σ y → x = y)
    (hreal : runSwaps ss σ = pmove (cycleMoves ls) σ) :
    ls.length - 1 ≤ ss.length

-- lean/ToyParMove/Boundaries.lean:262-267
-- lean/ToyParMove/Boundaries.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem nonvacuity_cycle_length_sub_one_le_of_injOn_of_runSwaps :
    let σ : Nat → Nat := fun l => if l ≤ 2 then l else 0
    ([0, 1, 2] : List Nat).Nodup ∧
      (∀ x ∈ ([0, 1, 2] : List Nat), ∀ y ∈ ([0, 1, 2] : List Nat), σ x = σ y → x = y) ∧
      ¬ Function.Injective σ ∧
      runSwaps (cycleSwaps [0, 1, 2]) σ = pmove (cycleMoves [0, 1, 2]) σ

-- lean/ToyParMove/Boundaries.lean:280-281
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem putLane_putGet_iff_wid_zero_or_fits (L : Lane) :
    PutGet (getLane (n := n) L) (putLane L) ↔ (L.wid = 0 ∨ L.Fits n)

-- lean/ToyParMove/Boundaries.lean:303-304
-- lean/ToyParMove/Boundaries.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem putLane_putGet_width_zero_beyond_register :
    ¬ (⟨9, 0⟩ : Lane).Fits 8 ∧ PutGet (getLane (n := 8) ⟨9, 0⟩) (putLane ⟨9, 0⟩)
```

Basis: execution (Lean kernel check).

### Verbatim statements of counterexamples, witnesses and controls

Every Lean name used by a card as a counterexample, non-vacuity witness or positive control,
quoted verbatim from the source (proofs omitted), in card order.

#### `Toy.ParMove.functional_of_pmove_perm_invariant_needs_two_values` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:226-232
theorem functional_of_pmove_perm_invariant_needs_two_values :
    (∀ a b : Unit, a = b) ∧
    (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Unit,
      pmove M' σ = pmove [(0, 1), (0, 2)] σ) ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    ¬ ((∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Unit,
        pmove M' σ = pmove [(0, 1), (0, 2)] σ) ↔ Functional [((0 : Nat), (1 : Nat)), (0, 2)])
```

#### `Toy.ParMove.functional_of_pmove_perm_invariant_needs_perm_invariance` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:252-256
theorem functional_of_pmove_perm_invariant_needs_perm_invariance :
    (true ≠ false) ∧
    ¬ (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Bool,
        pmove M' σ = pmove [(0, 1), (0, 2)] σ) ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)]
```

#### `Toy.ParMove.pmove_perm_invariant_needs_functional` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:205-208
theorem pmove_perm_invariant_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    List.Perm [((0 : Nat), (1 : Nat)), (0, 2)] [(0, 2), (0, 1)] ∧
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠ pmove [(0, 2), (0, 1)] id
```

#### `Toy.ParMove.pmove_perm_invariant_needs_perm` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:240-243
theorem pmove_perm_invariant_needs_perm :
    Functional ([] : List (Nat × Nat)) ∧
    ¬ List.Perm ([] : List (Nat × Nat)) [(0, 1)] ∧
    pmove ([] : List (Nat × Nat)) (id : Nat → Nat) ≠ pmove [(0, 1)] id
```

#### `Toy.ParMove.pmove_eq_pmoveLast_needs_functional` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:214-217
theorem pmove_eq_pmoveLast_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠
      pmoveLast [((0 : Nat), (1 : Nat)), (0, 2)] id
```

#### `Toy.ParMove.nonvacuity_pmove_perm_invariant_all` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:276-281
theorem nonvacuity_pmove_perm_invariant_all :
    (true ≠ false) ∧
    Functional [((0 : Nat), (1 : Nat)), (1, 0)] ∧
    List.Perm [((0 : Nat), (1 : Nat)), (1, 0)] [(1, 0), (0, 1)] ∧
    (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (1, 0)] → ∀ σ : Nat → Bool,
      pmove M' σ = pmove [(0, 1), (1, 0)] σ)
```

#### `Toy.ParMove.functionalAt_equal_values_example` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:80-82
theorem functionalAt_equal_values_example :
    FunctionalAt (fun l : Nat => if l = 2 then 1 else l) [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)]
```

#### `Toy.ParMove.not_functionalAt_id_example` (`lean/ToyParMove/Readings.lean`; result 2)

```lean
-- lean/ToyParMove/Readings.lean:90-91
theorem not_functionalAt_id_example :
    ¬ FunctionalAt (id : Nat → Nat) [((0 : Nat), (1 : Nat)), (0, 2)]
```

#### `Toy.ParMove.sequentialize_needs_functional` (`lean/ToyParMove/Necessity.lean`; result 3)

```lean
-- lean/ToyParMove/Necessity.lean:24-31
theorem sequentialize_needs_functional :
    ¬ Functional [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] ∧
    ((2 : Nat) ∉ dsts [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] ∨
      (2 : Nat) ∉ srcs [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)]) ∧
    ¬ (∀ l, l ≠ 2 → runSeq (sequentialize 2 [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)])
        (id : Nat → Nat) l = pmove [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] id l) ∧
    ¬ (∀ l, l ≠ 2 → runSeq (sequentialize 2 [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)])
        (id : Nat → Nat) l = pmoveLast [((0 : Nat), (0 : Nat)), (0, 1), (0, 0)] id l)
```

#### `Toy.ParMove.sequentialize_needs_tmp_not_dst_or_not_src` (`lean/ToyParMove/Necessity.lean`; result 3)

```lean
-- lean/ToyParMove/Necessity.lean:39-44
theorem sequentialize_needs_tmp_not_dst_or_not_src :
    Functional [((0 : Nat), (1 : Nat)), (1, 0)] ∧
    ¬ ((0 : Nat) ∉ dsts [((0 : Nat), (1 : Nat)), (1, 0)] ∨
        (0 : Nat) ∉ srcs [((0 : Nat), (1 : Nat)), (1, 0)]) ∧
    ¬ (∀ l, l ≠ 0 → runSeq (sequentialize 0 [((0 : Nat), (1 : Nat)), (1, 0)])
        (id : Nat → Nat) l = pmove [((0 : Nat), (1 : Nat)), (1, 0)] id l)
```

#### `Toy.ParMove.nonvacuity_sequentialize_tmp_is_source` (`lean/ToyParMove/Necessity.lean`; result 3)

```lean
-- lean/ToyParMove/Necessity.lean:91-96
theorem nonvacuity_sequentialize_tmp_is_source :
    Functional [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∧
    ((0 : Nat) ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∨
      (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)]) ∧
    (0 : Nat) ∈ srcs [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] ∧
    sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1), (3, 0)] = [(3, 0), (0, 1), (1, 2), (2, 0)]
```

#### `Toy.ParMove.nonvacuity_sequentialize_tmp_is_destination` (`lean/ToyParMove/Necessity.lean`; result 3)

```lean
-- lean/ToyParMove/Necessity.lean:101-104
theorem nonvacuity_sequentialize_tmp_is_destination :
    Functional [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    ((0 : Nat) ∉ dsts [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∨
      (0 : Nat) ∉ srcs [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)])
```

#### `Toy.ParMove.runSeq_append_needs_first_realization` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:216-223
theorem runSeq_append_needs_first_realization :
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove ([] : List (Nat × Nat)) τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (0 : Nat))], x ∉ dsts ([] : List (Nat × Nat))) ∧
    (∀ x ∈ srcs ([] : List (Nat × Nat)), x ∉ dsts [((1 : Nat), (0 : Nat))]) ∧
    (9 : Nat) ∉ srcs ([] : List (Nat × Nat)) ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([] ++ []) τ l =
        pmove ([((1 : Nat), (0 : Nat))] ++ []) τ l)
```

#### `Toy.ParMove.runSeq_append_needs_second_realization` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:229-236
theorem runSeq_append_needs_second_realization :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove ([] : List (Nat × Nat)) τ l) ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ x ∈ dsts ([] : List (Nat × Nat)), x ∉ dsts [((1 : Nat), (0 : Nat))]) ∧
    (∀ x ∈ srcs [((1 : Nat), (0 : Nat))], x ∉ dsts ([] : List (Nat × Nat))) ∧
    (9 : Nat) ∉ srcs [((1 : Nat), (0 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([] ++ []) τ l =
        pmove (([] : List (Nat × Nat)) ++ [(1, 0)]) τ l)
```

#### `Toy.ParMove.runSeq_append_needs_disjoint_dsts` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:199-206
theorem runSeq_append_needs_disjoint_dsts :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(0, 1)] τ l = pmove [((0 : Nat), (1 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(0, 2)] τ l = pmove [((0 : Nat), (2 : Nat))] τ l) ∧
    (0 : Nat) ∈ dsts [((0 : Nat), (1 : Nat))] ∧ (0 : Nat) ∈ dsts [((0 : Nat), (2 : Nat))] ∧
    (∀ x ∈ srcs [((0 : Nat), (2 : Nat))], x ∉ dsts [((0 : Nat), (1 : Nat))]) ∧
    (9 : Nat) ∉ srcs [((0 : Nat), (2 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([(0, 1)] ++ [(0, 2)]) τ l =
        pmove ([((0 : Nat), (1 : Nat))] ++ [(0, 2)]) τ l)
```

#### `Toy.ParMove.runSeq_append_needs_sources_not_overwritten` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:183-190
theorem runSeq_append_needs_sources_not_overwritten :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(1, 0)] τ l = pmove [((1 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq [(2, 1)] τ l = pmove [((2 : Nat), (1 : Nat))] τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (0 : Nat))], x ∉ dsts [((2 : Nat), (1 : Nat))]) ∧
    (1 : Nat) ∈ srcs [((2 : Nat), (1 : Nat))] ∧ (1 : Nat) ∈ dsts [((1 : Nat), (0 : Nat))] ∧
    (9 : Nat) ∉ srcs [((2 : Nat), (1 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 9 → runSeq ([(1, 0)] ++ [(2, 1)]) τ l =
        pmove ([((1 : Nat), (0 : Nat))] ++ [(2, 1)]) τ l)
```

#### `Toy.ParMove.runSeq_append_needs_tmp_not_src` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:162-170
theorem runSeq_append_needs_tmp_not_src :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 →
      runSeq [(0, 1), (1, 2), (2, 0)] τ l = pmove [((1 : Nat), (2 : Nat)), (2, 1)] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq [(3, 0)] τ l = pmove [((3 : Nat), (0 : Nat))] τ l) ∧
    (∀ x ∈ dsts [((1 : Nat), (2 : Nat)), (2, 1)], x ∉ dsts [((3 : Nat), (0 : Nat))]) ∧
    (∀ x ∈ srcs [((3 : Nat), (0 : Nat))], x ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)]) ∧
    (0 : Nat) ∈ srcs [((3 : Nat), (0 : Nat))] ∧
    ¬ (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq ([(0, 1), (1, 2), (2, 0)] ++ [(3, 0)]) τ l =
        pmove ([((1 : Nat), (2 : Nat)), (2, 1)] ++ [(3, 0)]) τ l)
```

#### `Toy.ParMove.nonvacuity_runSeq_append_realizes_off_tmp` (`lean/ToyParMove/Necessity.lean`; result 4)

```lean
-- lean/ToyParMove/Necessity.lean:242-248
theorem nonvacuity_runSeq_append_realizes_off_tmp :
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 → runSeq [(3, 0)] τ l = pmove [((3 : Nat), (0 : Nat))] τ l) ∧
    (∀ τ : Nat → Nat, ∀ l, l ≠ 0 →
      runSeq [(0, 1), (1, 2), (2, 0)] τ l = pmove [((1 : Nat), (2 : Nat)), (2, 1)] τ l) ∧
    (∀ x ∈ dsts [((3 : Nat), (0 : Nat))], x ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)]) ∧
    (∀ x ∈ srcs [((1 : Nat), (2 : Nat)), (2, 1)], x ∉ dsts [((3 : Nat), (0 : Nat))]) ∧
    (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1)]
```

#### `Toy.ParMove.runSeq_eq_pmove_needs_functional` (`lean/ToyParMove/Necessity.lean`; result 5)

```lean
-- lean/ToyParMove/Necessity.lean:308-311
theorem runSeq_eq_pmove_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧ Topological [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    runSeq [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠
      pmove [((0 : Nat), (1 : Nat)), (0, 2)] id
```

#### `Toy.ParMove.runSeq_eq_pmove_needs_topological` (`lean/ToyParMove/Necessity.lean`; result 5)

```lean
-- lean/ToyParMove/Necessity.lean:300-303
theorem runSeq_eq_pmove_needs_topological :
    Functional [((1 : Nat), (0 : Nat)), (2, 1)] ∧ ¬ Topological [((1 : Nat), (0 : Nat)), (2, 1)] ∧
    runSeq [((1 : Nat), (0 : Nat)), (2, 1)] (id : Nat → Nat) ≠
      pmove [((1 : Nat), (0 : Nat)), (2, 1)] id
```

#### `Toy.ParMove.nonvacuity_runSeq_eq_pmove_of_topological` (`lean/ToyParMove/Necessity.lean`; result 5)

```lean
-- lean/ToyParMove/Necessity.lean:315-316
theorem nonvacuity_runSeq_eq_pmove_of_topological :
    Functional [((2 : Nat), (1 : Nat)), (1, 0)] ∧ Topological [((2 : Nat), (1 : Nat)), (1, 0)]
```

#### `Toy.ParMove.runSeq_cycleSeqScratch_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 6)

```lean
-- lean/ToyParMove/CycleTightness.lean:37-40
theorem runSeq_cycleSeqScratch_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧
    ¬ (∀ l, l ≠ 5 → runSeq (cycleSeqScratch 5 [0, 1, 0]) (id : Nat → Nat) l =
        pmove (cycleMoves [0, 1, 0]) id l)
```

#### `Toy.ParMove.runSeq_cycleSeqScratch_needs_tmp_fresh` (`lean/ToyParMove/CycleTightness.lean`; result 6)

```lean
-- lean/ToyParMove/CycleTightness.lean:44-47
theorem runSeq_cycleSeqScratch_needs_tmp_fresh :
    ([0, 1] : List Nat).Nodup ∧ (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    ¬ (∀ l, l ≠ 0 → runSeq (cycleSeqScratch 0 [0, 1]) (id : Nat → Nat) l =
        pmove (cycleMoves [0, 1]) id l)
```

#### `Toy.ParMove.nonvacuity_runSeq_cycleSeqScratch` (`lean/ToyParMove/CycleTightness.lean`; result 6)

```lean
-- lean/ToyParMove/CycleTightness.lean:52-54
theorem nonvacuity_runSeq_cycleSeqScratch :
    ((0 : Nat) :: [1, 2]).Nodup ∧ (3 : Nat) ∉ ((0 : Nat) :: [1, 2]) ∧
    (cycleSeqScratch (3 : Nat) [0, 1, 2]).length = 4
```

#### `Toy.ParMove.cycle_lower_bound_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:59-64
theorem cycle_lower_bound_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧ Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 5 → runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1, 0]) id l) ∧
    ¬ (([0, 1, 0] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length)
```

#### `Toy.ParMove.cycle_lower_bound_uniform_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:313-318
theorem cycle_lower_bound_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq [((1 : Nat), (0 : Nat))] σ l =
      pmove (cycleMoves [0, 1, 0]) σ l) ∧
    ¬ (([0, 1, 0] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length)
```

#### `Toy.ParMove.cycle_lower_bound_needs_two` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:68-73
theorem cycle_lower_bound_needs_two :
    ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧ (5 : Nat) ∉ ([0] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) l =
      pmove (cycleMoves [0]) id l) ∧
    ¬ (([0] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.cycle_lower_bound_uniform_needs_two` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:324-329
theorem cycle_lower_bound_uniform_needs_two :
    (true ≠ false) ∧ ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧
    (5 : Nat) ∉ ([0] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0]) σ l) ∧
    ¬ (([0] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.cycle_lower_bound_needs_tmp_fresh` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:79-84
theorem cycle_lower_bound_needs_tmp_fresh :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 0 → runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length)
```

#### `Toy.ParMove.cycle_lower_bound_uniform_needs_tmp_fresh` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:336-341
theorem cycle_lower_bound_uniform_needs_tmp_fresh :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 0 → runSeq [((1 : Nat), (0 : Nat))] σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length)
```

#### `Toy.ParMove.cycle_lower_bound_needs_injective` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:90-95
theorem cycle_lower_bound_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) l =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat)) l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.cycle_lower_bound_needs_global_injectivity` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:231-239
theorem cycle_lower_bound_needs_global_injectivity :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ Function.Injective (fun l : Nat => if l = 3 then 0 else l) ∧
    (∀ x y, x ∈ ([0, 1, 2] : List Nat) → y ∈ ([0, 1, 2] : List Nat) →
      (fun l : Nat => if l = 3 then 0 else l) x = (fun l : Nat => if l = 3 then 0 else l) y →
      x = y) ∧
    (∀ l, l ≠ 2 → runSeq [((0 : Nat), (1 : Nat)), (1, 3)] (fun l : Nat => if l = 3 then 0 else l) l =
      pmove (cycleMoves [0, 1]) (fun l : Nat => if l = 3 then 0 else l) l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((0 : Nat), (1 : Nat)), (1, 3)].length)
```

#### `Toy.ParMove.cycle_lower_bound_needs_realization` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:99-104
theorem cycle_lower_bound_needs_realization :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    ¬ (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.cycle_lower_bound_uniform_needs_two_values` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:303-308
theorem cycle_lower_bound_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Unit, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.cycle_lower_bound_uniform_needs_realization` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:348-353
theorem cycle_lower_bound_uniform_needs_realization :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.nonvacuity_cycle_lower_bound` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:111-116
theorem nonvacuity_cycle_lower_bound :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    (cycleSeqScratch (2 : Nat) [0, 1]).length = ([0, 1] : List Nat).length + 1
```

#### `Toy.ParMove.nonvacuity_cycle_lower_bound_uniform` (`lean/ToyParMove/CycleTightness.lean`; result 7)

```lean
-- lean/ToyParMove/CycleTightness.lean:359-364
theorem nonvacuity_cycle_lower_bound_uniform :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    (cycleSeqScratch (2 : Nat) [0, 1]).length = ([0, 1] : List Nat).length + 1
```

#### `Toy.ParMove.cycle_impossibility_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:122-125
theorem cycle_impossibility_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    Function.Injective (id : Nat → Nat) ∧
    runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1, 0]) id
```

#### `Toy.ParMove.cycle_impossibility_uniform_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:285-287
theorem cycle_impossibility_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Bool, runSeq ms σ = pmove (cycleMoves [0, 1, 0]) σ
```

#### `Toy.ParMove.cycle_impossibility_needs_two` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:128-130
theorem cycle_impossibility_needs_two :
    ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧ Function.Injective (id : Nat → Nat) ∧
    runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) = pmove (cycleMoves [0]) id
```

#### `Toy.ParMove.cycle_impossibility_uniform_needs_two` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:291-293
theorem cycle_impossibility_uniform_needs_two :
    (true ≠ false) ∧ ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Bool, runSeq ms σ = pmove (cycleMoves [0]) σ
```

#### `Toy.ParMove.cycle_impossibility_needs_injective` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:136-140
theorem cycle_impossibility_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat))
```

#### `Toy.ParMove.swap_impossibility_needs_injective` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:172-175
theorem swap_impossibility_needs_injective :
    (0 : Nat) ≠ 1 ∧ ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove [((0 : Nat), (1 : Nat)), (1, 0)] (fun _ : Nat => (0 : Nat))
```

#### `Toy.ParMove.cycle_impossibility_needs_global_injectivity` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:254-261
theorem cycle_impossibility_needs_global_injectivity :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ¬ Function.Injective (fun l : Nat => if l = 3 then 2 else l) ∧
    (∀ x ∈ ([0, 1] : List Nat), ∀ y,
      (fun l : Nat => if l = 3 then 2 else l) x = (fun l : Nat => if l = 3 then 2 else l) y →
      x = y) ∧
    runSeq [((2 : Nat), (0 : Nat)), (0, 1), (1, 2), (2, 3)] (fun l : Nat => if l = 3 then 2 else l) =
      pmove (cycleMoves [0, 1]) (fun l : Nat => if l = 3 then 2 else l)
```

#### `Toy.ParMove.swap_impossibility_needs_distinct` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:164-166
theorem swap_impossibility_needs_distinct :
    ¬ ((0 : Nat) ≠ 0) ∧ Function.Injective (id : Nat → Nat) ∧
    runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) = pmove [((0 : Nat), (0 : Nat)), (0, 0)] id
```

#### `Toy.ParMove.cycle_impossibility_uniform_needs_two_values` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:279-281
theorem cycle_impossibility_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Unit, runSeq ms σ = pmove (cycleMoves [0, 1]) σ
```

#### `Toy.ParMove.nonvacuity_cycle_impossibility` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:159-161
theorem nonvacuity_cycle_impossibility :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    Function.Injective (id : Nat → Nat)
```

#### `Toy.ParMove.nonvacuity_swap_impossibility` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:179-180
theorem nonvacuity_swap_impossibility :
    (0 : Nat) ≠ 1 ∧ Function.Injective (id : Nat → Nat)
```

#### `Toy.ParMove.nonvacuity_cycle_impossibility_uniform` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:297-298
theorem nonvacuity_cycle_impossibility_uniform :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length
```

#### `Toy.ParMove.cycle_impossibility_positive_control` (`lean/ToyParMove/CycleTightness.lean`; result 8)

```lean
-- lean/ToyParMove/CycleTightness.lean:148-153
theorem cycle_impossibility_positive_control :
    (∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    runSwaps [((0 : Nat), (1 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1]) id ∧
    runSeq [((3 : Nat), (1 : Nat)), (1, 2), (2, 3)] (id : Nat → Nat) =
      pmove [((3 : Nat), (1 : Nat)), (2, 1), (1, 2)] id
```

#### `Toy.ParMove.cycle_with_outgoing_copy_realized_without_scratch` (`lean/ToyParMove/Necessity.lean`; result 8)

```lean
-- lean/ToyParMove/Necessity.lean:368-371
theorem cycle_with_outgoing_copy_realized_without_scratch :
    (∀ ms : List (Nat × Nat), ms.Perm [(3, 1), (2, 1), (1, 2)] → ¬ Topological ms) ∧
    ∀ (V : Type) (σ : Nat → V),
      runSeq [((3 : Nat), (1 : Nat)), (1, 2), (2, 3)] σ = pmove [((3 : Nat), (1 : Nat)), (2, 1), (1, 2)] σ
```

#### `Toy.ParMove.runSwaps_cycleSwaps_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 9)

```lean
-- lean/ToyParMove/CycleTightness.lean:184-186
theorem runSwaps_cycleSwaps_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧
    runSwaps (cycleSwaps [0, 1, 0]) (id : Nat → Nat) ≠ pmove (cycleMoves [0, 1, 0]) id
```

#### `Toy.ParMove.nonvacuity_runSwaps_cycleSwaps` (`lean/ToyParMove/CycleTightness.lean`; result 9)

```lean
-- lean/ToyParMove/CycleTightness.lean:189-190
theorem nonvacuity_runSwaps_cycleSwaps :
    ([0, 1, 2] : List Nat).Nodup ∧ (cycleSwaps ([0, 1, 2] : List Nat)).length = 2
```

#### `Toy.ParMove.swap_lower_bound_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:193-196
theorem swap_lower_bound_needs_nodup :
    ¬ ([0, 1, 0, 1] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps [((0 : Nat), (1 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1, 0, 1]) id ∧
    ¬ (([0, 1, 0, 1] : List Nat).length - 1 ≤ [((0 : Nat), (1 : Nat))].length)
```

#### `Toy.ParMove.swap_lower_bound_uniform_needs_nodup` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:376-379
theorem swap_lower_bound_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0, 1] : List Nat).Nodup ∧
    (∀ σ : Nat → Bool, runSwaps [((0 : Nat), (1 : Nat))] σ = pmove (cycleMoves [0, 1, 0, 1]) σ) ∧
    ¬ (([0, 1, 0, 1] : List Nat).length - 1 ≤ [((0 : Nat), (1 : Nat))].length)
```

#### `Toy.ParMove.swap_lower_bound_needs_injective` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:204-208
theorem swap_lower_bound_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSwaps ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat)) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.swap_lower_bound_needs_realization` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:212-215
theorem swap_lower_bound_needs_realization :
    ([0, 1] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps ([] : List (Nat × Nat)) (id : Nat → Nat) ≠ pmove (cycleMoves [0, 1]) id ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.swap_lower_bound_uniform_needs_two_values` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:369-372
theorem swap_lower_bound_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧
    (∀ σ : Nat → Unit, runSwaps ([] : List (Nat × Nat)) σ = pmove (cycleMoves [0, 1]) σ) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.swap_lower_bound_uniform_needs_realization` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:384-387
theorem swap_lower_bound_uniform_needs_realization :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧
    ¬ (∀ σ : Nat → Bool, runSwaps ([] : List (Nat × Nat)) σ = pmove (cycleMoves [0, 1]) σ) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length)
```

#### `Toy.ParMove.nonvacuity_swap_lower_bound` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:220-223
theorem nonvacuity_swap_lower_bound :
    ([0, 1, 2] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps (cycleSwaps [0, 1, 2]) (id : Nat → Nat) = pmove (cycleMoves [0, 1, 2]) id ∧
    (cycleSwaps ([0, 1, 2] : List Nat)).length = ([0, 1, 2] : List Nat).length - 1
```

#### `Toy.ParMove.nonvacuity_swap_lower_bound_uniform` (`lean/ToyParMove/CycleTightness.lean`; result 10)

```lean
-- lean/ToyParMove/CycleTightness.lean:393-396
theorem nonvacuity_swap_lower_bound_uniform :
    (true ≠ false) ∧ ([0, 1, 2] : List Nat).Nodup ∧
    (∀ σ : Nat → Bool, runSwaps (cycleSwaps [0, 1, 2]) σ = pmove (cycleMoves [0, 1, 2]) σ) ∧
    (cycleSwaps ([0, 1, 2] : List Nat)).length = ([0, 1, 2] : List Nat).length - 1
```

#### `Toy.ParMove.xorSwap_eq_swapStore_needs_ne` (`lean/ToyParMove/XorSwap.lean`; result 11)

```lean
-- lean/ToyParMove/XorSwap.lean:126-128
theorem xorSwap_eq_swapStore_needs_ne :
    ¬ ((0 : Nat) ≠ 0) ∧
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 ≠ swapStore (fun _ : Nat => (1#8 : BitVec 8)) 0 0
```

#### `Toy.ParMove.nonvacuity_xorSwap` (`lean/ToyParMove/XorSwap.lean`; result 11)

```lean
-- lean/ToyParMove/XorSwap.lean:149-152
theorem nonvacuity_xorSwap :
    (0 : Nat) ≠ 1 ∧
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 0 = 0xC3#8 ∧
    xorSwap (fun l : Nat => if l = 0 then 0x5A#8 else 0xC3#8) 0 1 1 = 0x5A#8
```

#### `Toy.ParMove.runXorSwaps_needs_no_self` (`lean/ToyParMove/XorSwap.lean`; result 12)

```lean
-- lean/ToyParMove/XorSwap.lean:132-135
theorem runXorSwaps_needs_no_self :
    ¬ (∀ p ∈ [((0 : Nat), (0 : Nat))], p.1 ≠ p.2) ∧
    runXorSwaps [((0 : Nat), (0 : Nat))] (fun _ : Nat => (1#8 : BitVec 8)) ≠
      runSwaps [(0, 0)] (fun _ : Nat => (1#8 : BitVec 8))
```

#### `Toy.ParMove.runXorSwaps_cycleSwaps_needs_nodup` (`lean/ToyParMove/XorSwap.lean`; result 12)

```lean
-- lean/ToyParMove/XorSwap.lean:140-145
theorem runXorSwaps_cycleSwaps_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧
    runXorSwaps (cycleSwaps [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) ≠
      pmove (cycleMoves [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) ∧
    runXorSwaps (cycleSwaps [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) 0 = 0#8 ∧
    pmove (cycleMoves [0, 1, 0]) (fun l : Nat => if l = 0 then 1#8 else 2#8) 0 = 1#8
```

#### `Toy.ParMove.nonvacuity_runXorSwaps` (`lean/ToyParMove/XorSwap.lean`; result 12)

```lean
-- lean/ToyParMove/XorSwap.lean:156-157
theorem nonvacuity_runXorSwaps :
    (∀ p ∈ [((0 : Nat), (1 : Nat)), (0, 2)], p.1 ≠ p.2) ∧ ([0, 1, 2] : List Nat).Nodup
```

#### `Toy.ParMove.putLane_putGet_needs_fits` (`lean/ToyParMove/Lanes.lean`; result 13)

```lean
-- lean/ToyParMove/Lanes.lean:365-369
theorem putLane_putGet_needs_fits :
    ¬ (Lane.Fits ⟨4, 8⟩ 8) ∧
    ¬ PutGet (getLane (n := 8) ⟨4, 8⟩) (putLane ⟨4, 8⟩) ∧
    ¬ VeryWellBehaved (getLane (n := 8) ⟨4, 8⟩) (putLane ⟨4, 8⟩) ∧
    getLane (n := 8) ⟨4, 8⟩ (putLane ⟨4, 8⟩ (0xFF#8) (0#8)) ≠ (0xFF#8)
```

#### `Toy.ParMove.nonvacuity_putLane_veryWellBehaved` (`lean/ToyParMove/Lanes.lean`; result 13)

```lean
-- lean/ToyParMove/Lanes.lean:417
theorem nonvacuity_putLane_veryWellBehaved : laneHigh8.Fits 64
```

#### `Toy.ParMove.putLane_overlapping_not_comm` (`lean/ToyParMove/Lanes.lean`; result 14)

```lean
-- lean/ToyParMove/Lanes.lean:375-378
theorem putLane_overlapping_not_comm :
    ¬ laneLow8.Disjoint laneLow16 ∧
    putLane laneLow8 (0xFF#8) (putLane laneLow16 (0x0000#16) (0#16)) ≠
      putLane laneLow16 (0x0000#16) (putLane laneLow8 (0xFF#8) (0#16))
```

#### `Toy.ParMove.getLane_putLane_needs_disjoint` (`lean/ToyParMove/Lanes.lean`; result 14)

```lean
-- lean/ToyParMove/Lanes.lean:381-383
theorem getLane_putLane_needs_disjoint :
    ¬ laneLow8.Disjoint laneLow16 ∧
    getLane laneLow16 (putLane laneLow8 (0xFF#8) (0#16)) ≠ getLane laneLow16 (0#16)
```

#### `Toy.ParMove.nonvacuity_putLane_comm` (`lean/ToyParMove/Lanes.lean`; result 14)

```lean
-- lean/ToyParMove/Lanes.lean:420
theorem nonvacuity_putLane_comm : laneLow8.Disjoint laneHigh8
```

#### `Toy.ParMove.putLane_comm_iff_needs_fits` (`lean/ToyParMove/Lanes.lean`; result 15)

```lean
-- lean/ToyParMove/Lanes.lean:388-395
theorem putLane_comm_iff_needs_fits :
    ¬ (Lane.Fits ⟨6, 4⟩ 8 ∨ Lane.Fits ⟨8, 4⟩ 8) ∧
    (∀ (v₁ : BitVec 4) (v₂ : BitVec 4) (w : BitVec 8),
      putLane ⟨6, 4⟩ v₁ (putLane ⟨8, 4⟩ v₂ w) = putLane ⟨8, 4⟩ v₂ (putLane ⟨6, 4⟩ v₁ w)) ∧
    ¬ Lane.Disjoint ⟨6, 4⟩ ⟨8, 4⟩ ∧
    ¬ ((∀ (v₁ : BitVec 4) (v₂ : BitVec 4) (w : BitVec 8),
      putLane ⟨6, 4⟩ v₁ (putLane ⟨8, 4⟩ v₂ w) = putLane ⟨8, 4⟩ v₂ (putLane ⟨6, 4⟩ v₁ w)) ↔
      Lane.Disjoint ⟨6, 4⟩ ⟨8, 4⟩)
```

#### `Toy.ParMove.nonvacuity_putLane_comm_iff` (`lean/ToyParMove/Lanes.lean`; result 15)

```lean
-- lean/ToyParMove/Lanes.lean:424-426
theorem nonvacuity_putLane_comm_iff :
    (laneLow8.Fits 64 ∨ laneHigh8.Fits 64) ∧ laneLow8.Disjoint laneHigh8 ∧
    (laneLow8.Fits 64 ∨ laneLow16.Fits 64) ∧ ¬ laneLow8.Disjoint laneLow16
```

#### `Toy.ParMove.nonvacuity_putLane_comm_iff_disjointIn` (`lean/ToyParMove/Lanes.lean`; result 15)

```lean
-- lean/ToyParMove/Lanes.lean:430-431
theorem nonvacuity_putLane_comm_iff_disjointIn :
    laneLow8.DisjointIn 64 laneHigh8 ∧ ¬ laneLow8.DisjointIn 64 laneLow16
```

#### `Toy.ParMove.writeZext_not_getPut_needs_lt` (`lean/ToyParMove/Lanes.lean`; result 16)

```lean
-- lean/ToyParMove/Lanes.lean:411-412
theorem writeZext_not_getPut_needs_lt :
    ¬ ((8 : Nat) < 8) ∧ ∃ g : BitVec 8 → BitVec 8, GetPut g (writeZext 8 (wid := 8))
```

#### `Toy.ParMove.nonvacuity_writeZext` (`lean/ToyParMove/Lanes.lean`; result 16)

```lean
-- lean/ToyParMove/Lanes.lean:434
theorem nonvacuity_writeZext : (32 : Nat) < 64 ∧ (32 : Nat) ≤ 64
```

#### `Toy.ParMove.writeZext_getPut_full` (`lean/ToyParMove/Lanes.lean`; result 16)

```lean
-- lean/ToyParMove/Lanes.lean:283
theorem writeZext_getPut_full : GetPut (getLane (n := n) ⟨0, n⟩) (writeZext n (wid := n))
```

#### `Toy.ParMove.nonvacuity_writeZext_getPut_iff` (`lean/ToyParMove/Lanes.lean`; result 17)

```lean
-- lean/ToyParMove/Lanes.lean:438-442
theorem nonvacuity_writeZext_getPut_iff :
    writeZext 64 (getLane ⟨0, 32⟩ (0x00000000DEADBEEF#64)) (0x00000000DEADBEEF#64) =
      0x00000000DEADBEEF#64 ∧
    writeZext 64 (getLane ⟨0, 32⟩ (0x1122334455667788#64)) (0x1122334455667788#64) ≠
      0x1122334455667788#64
```

#### `Toy.ParMove.writeZext_putGet_needs_fit` (`lean/ToyParMove/Lanes.lean`; result 18)

```lean
-- lean/ToyParMove/Lanes.lean:403-405
theorem writeZext_putGet_needs_fit :
    ¬ (16 ≤ 8) ∧ ¬ PutGet (getLane (n := 8) ⟨0, 16⟩) (writeZext 8 (wid := 16)) ∧
    getLane (n := 8) ⟨0, 16⟩ (writeZext 8 (0xFFFF#16) (0#8)) ≠ (0xFFFF#16)
```

#### `Toy.ParMove.lanePMove_perm_needs_laneWF` (`lean/ToyParMove/LaneMoves.lean`; result 20)

```lean
-- lean/ToyParMove/LaneMoves.lean:283-286
theorem lanePMove_perm_needs_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    List.Perm [lm 0 0 1 0 8, lm 0 0 2 0 16] [lm 0 0 2 0 16, lm 0 0 1 0 8] ∧
    lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16 ≠ lanePMove [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16
```

#### `Toy.ParMove.lanePMove_perm_needs_perm` (`lean/ToyParMove/LaneMoves.lean`; result 20)

```lean
-- lean/ToyParMove/LaneMoves.lean:275-278
theorem lanePMove_perm_needs_perm :
    LaneWF [lm 0 0 1 0 8] ∧
    ¬ List.Perm [lm 0 0 1 0 8] ([] : List (LaneMove Nat)) ∧
    lanePMove [lm 0 0 1 0 8] regs16 ≠ lanePMove ([] : List (LaneMove Nat)) regs16
```

#### `Toy.ParMove.nonvacuity_lanePMove_perm` (`lean/ToyParMove/LaneMoves.lean`; result 20)

```lean
-- lean/ToyParMove/LaneMoves.lean:290-292
theorem nonvacuity_lanePMove_perm :
    LaneWF [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 0 8] [lm 0 8 0 0 8, lm 0 0 0 8 8]
```

#### `Toy.ParMove.runLanes_needs_laneWF` (`lean/ToyParMove/LaneMoves.lean`; result 21)

```lean
-- lean/ToyParMove/LaneMoves.lean:243-247
theorem runLanes_needs_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    List.Perm [lm 0 0 2 0 16, lm 0 0 1 0 8] [lm 0 0 1 0 8, lm 0 0 2 0 16] ∧
    LaneTopological [lm 0 0 2 0 16, lm 0 0 1 0 8] ∧
    runLanes [lm 0 0 2 0 16, lm 0 0 1 0 8] regs16 ≠ lanePMove [lm 0 0 1 0 8, lm 0 0 2 0 16] regs16
```

#### `Toy.ParMove.runLanes_needs_perm` (`lean/ToyParMove/LaneMoves.lean`; result 21)

```lean
-- lean/ToyParMove/LaneMoves.lean:259-262
theorem runLanes_needs_perm :
    LaneWF [lm 0 0 1 0 8] ∧ ¬ List.Perm ([] : List (LaneMove Nat)) [lm 0 0 1 0 8] ∧
    LaneTopological ([] : List (LaneMove Nat)) ∧
    runLanes ([] : List (LaneMove Nat)) regs16 ≠ lanePMove [lm 0 0 1 0 8] regs16
```

#### `Toy.ParMove.runLanes_needs_topological` (`lean/ToyParMove/LaneMoves.lean`; result 21)

```lean
-- lean/ToyParMove/LaneMoves.lean:251-255
theorem runLanes_needs_topological :
    LaneWF [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 0 8] [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    ¬ LaneTopological [lm 0 0 0 8 8, lm 0 8 0 0 8] ∧
    runLanes [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16 ≠ lanePMove [lm 0 0 0 8 8, lm 0 8 0 0 8] regs16
```

#### `Toy.ParMove.nonvacuity_runLanes_same_register` (`lean/ToyParMove/LaneMoves.lean`; result 21)

```lean
-- lean/ToyParMove/LaneMoves.lean:299-303
theorem nonvacuity_runLanes_same_register :
    LaneWF [lm 0 8 0 16 8, lm 0 0 0 8 8] ∧
    List.Perm [lm 0 0 0 8 8, lm 0 8 0 16 8] [lm 0 8 0 16 8, lm 0 0 0 8 8] ∧
    LaneTopological [lm 0 0 0 8 8, lm 0 8 0 16 8] ∧
    ¬ LaneTopological [lm 0 8 0 16 8, lm 0 0 0 8 8]
```

#### `Toy.ParMove.nonvacuity_runLanes` (`lean/ToyParMove/LaneMoves.lean`; result 21)

```lean
-- lean/ToyParMove/LaneMoves.lean:308-311
theorem nonvacuity_runLanes :
    LaneWF [lm 1 0 0 0 8, lm 2 0 1 0 8] ∧
    List.Perm [lm 2 0 1 0 8, lm 1 0 0 0 8] [lm 1 0 0 0 8, lm 2 0 1 0 8] ∧
    LaneTopological [lm 2 0 1 0 8, lm 1 0 0 0 8]
```

## Boundaries

### Non-claims (read first)

What each result does not show, verbatim from its card. Several cards share the closing toy-model non-claim; it is repeated so that each list is complete on its own.

#### 1. `pmove-readings-disagree-on-repeated-destination`

- Does not say that repeated destinations are always harmful: a list whose repeated destinations come only from exact duplicates, such as [(0,1),(0,1)], is functional and therefore order-independent on every store (pmove-order-independent-iff-functional, direction b).
- The disagreement needs a store that gives sources 1 and 2 different values: at every store σ with σ 1 = σ 2 the list is FunctionalAt σ, so the two readings agree by pmove-order-independent-iff-functional (c) applied to the reordering M.reverse (pmoveLast M σ is pmove M.reverse σ by definition); pmove_readings_agree_on_equal_source_values checks one such store directly. FunctionalAt is the store-level condition (an informal analogue of Boissinot et al.'s V(b) = V(c)).
- Does not say which reading a real compiler or ISA uses; real parallel moves are normally required to have distinct destinations.
- Only two order-based readings are compared; a nondeterministic or 'undefined' reading is not modeled.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Readings.lean:196-198
-- lean/ToyParMove/Readings.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem pmove_readings_agree_on_equal_source_values :
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l) =
      pmoveLast [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l)
```

#### 2. `pmove-order-independent-iff-functional`

- Functional is strictly weaker than WellFormed (distinct destinations): every well-formed list is functional (functional_of_wellFormed), and the exact duplicate [(0,1),(0,1)] is functional but not well-formed (functional_duplicate_not_wellFormed, a single concrete instance). The uncarded corollary pmove_eq_pmoveLast_of_wellFormed is the WellFormed special case of (b').
- Functional is a condition on source locations, required for order independence on all stores; for one given store the right condition is FunctionalAt (equal source values), which allows two different source locations holding the same value. FunctionalAt is the closest analogue here of the condition Boissinot et al. state for SSA variables (V(b) = V(c)); SSA value equality is a static property of a program rather than of one store, so the correspondence is informal.
- Says nothing about sequential implementations; it is a statement about the parallel semantics only.
- Order independence is about reordering the list, not about which locations are written.
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Basic.lean:119
-- lean/ToyParMove/Basic.lean — universally quantified theorem
theorem functional_of_wellFormed {M : List (Loc × Loc)} (h : WellFormed M) : Functional M

-- lean/ToyParMove/Readings.lean:38-39
-- lean/ToyParMove/Readings.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem functional_duplicate_not_wellFormed :
    Functional [((0 : Nat), (1 : Nat)), (0, 1)] ∧ ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 1)]

-- lean/ToyParMove/Readings.lean:188-189
-- lean/ToyParMove/Readings.lean — universally quantified theorem
theorem pmove_eq_pmoveLast_of_wellFormed {M : List (Loc × Loc)} (hM : WellFormed M)
    (σ : Loc → V) : pmove M σ = pmoveLast M σ
```

#### 3. `sequentialize-sound-off-scratch`

- The conclusion excludes tmp, and no theorem about the final value of tmp is proved, on cyclic or on acyclic inputs (in particular, whether tmp is left unchanged on acyclic inputs is not proved). Breaking a cycle of length at least 2 can overwrite even a fresh tmp: for M = [(1,2),(2,1)], tmp = 0 (neither a source nor a destination of M) and the identity store on Nat, the emitted sequence leaves the old value of 1 at location 0, whereas pmove M keeps the old value of 0 there (sequentialize_clobbers_tmp, a single concrete instance). Self-moves (1-cycles) never cause a write to tmp, because sequentialize drops them before its loop (by definition).
- Liveness is not modeled: a register that is syntactically fresh for M (neither a source nor a destination) can still be unsafe as tmp if it holds a value needed after the parallel move, because each cycle break writes tmp (by the definition of seqLoop it emits the move (tmp, m.1)); sequentialize_clobbers_tmp shows the value of a fresh tmp being changed on one input.
- The two cases allowed by htmp differ in practice. If tmp is a source but not a destination, the theorem gives the parallel result at every location other than tmp, including the destinations of the moves that read tmp; nothing is proved about the value left in tmp, which can be overwritten when a cycle is broken. If tmp is a destination but not a source, the parallel move's own assignment to tmp can be lost: for [(0,3),(1,2),(2,1)] with tmp = 0 and the identity store, the emitted sequence leaves the old value of 1 at 0 instead of the old value of 3 (sequentialize_loses_tmp_destination, a single concrete instance).
- htmp is tight but not necessary: for M = [(0,0),(1,2),(2,1)] with tmp = 0, where tmp is both a destination and a source only through the self-move (0,0), htmp fails and the conclusion still holds for every store Nat → Nat (sequentialize_works_with_tmp_self_move, a single concrete instance). Unproved commentary: the same appears to hold for every functional M in which tmp occurs only in self-moves (tmp, tmp), because sequentialize drops self-moves before its loop and the remaining list satisfies htmp; no theorem in this package states this.
- Full scratch freshness (tmp neither a source nor a destination, as in CompCert's move_no_temp) is sufficient but not necessary for this algorithm; it IS necessary for strategies that may break a cycle while a pending move still reads tmp (see sequential-composition-of-move-blocks, counterexample runSeq_append_needs_tmp_not_src).
- The algorithm drops self-moves (by definition) but does not deduplicate: on the functional input [(0,1),(0,1),(1,0)] with tmp = 9 it emits [(9,0),(0,1),(0,1),(1,9)], which contains the move (0,1) twice (sequentialize_emits_duplicates_example, a single concrete instance).
- One untyped scratch location: unlike CompCert's Parmov.v and Rideau-Serpette-Leroy (a temporary chosen per register, T(r), preserving register classes such as integer versus floating-point), register classes are not modeled.
- The result is about this specific ready-first algorithm, not about the Rideau-Serpette-Leroy algorithm, Boissinot et al.'s Algorithm 1, or any production implementation.
- Not a move-count optimality result, and no move count for general inputs is proved. When no move is ready, the algorithm breaks a cycle through tmp (by the definition of seqLoop), even when a cycle value already has a copy elsewhere, and such a copy can make scratch unnecessary: [(3,1),(2,1),(1,2)] is realized exactly, from every store, by 3 plain moves with no scratch (cycle_with_outgoing_copy_realized_without_scratch). How the move count of sequentialize compares with Boissinot et al.'s Algorithm 1 is not examined. Only the isolated-cycle case is shown to match the lower bound, by a finite check of the cycles of length k = 2..5 on locations 0..k-1 with tmp = 9 (sequentialize_cycle_length_examples).
- No claim about time complexity (the toy algorithm is quadratic).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Sequentialize.lean:311-312
-- lean/ToyParMove/Sequentialize.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_emits_duplicates_example :
    sequentialize (9 : Nat) [(0, 1), (0, 1), (1, 0)] = [(9, 0), (0, 1), (0, 1), (1, 9)]

-- lean/ToyParMove/Necessity.lean:51-56
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_loses_tmp_destination :
    Functional [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∈ dsts [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] ∧
    runSeq (sequentialize 0 [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((0 : Nat), (3 : Nat)), (1, 2), (2, 1)] (id : Nat → Nat) 0 = 3

-- lean/ToyParMove/Necessity.lean:62-66
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_clobbers_tmp :
    (0 : Nat) ∉ dsts [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    (0 : Nat) ∉ srcs [((1 : Nat), (2 : Nat)), (2, 1)] ∧
    runSeq (sequentialize 0 [((1 : Nat), (2 : Nat)), (2, 1)]) (id : Nat → Nat) 0 = 1 ∧
    pmove [((1 : Nat), (2 : Nat)), (2, 1)] (id : Nat → Nat) 0 = 0

-- lean/ToyParMove/Necessity.lean:72-78
-- lean/ToyParMove/Necessity.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem sequentialize_works_with_tmp_self_move :
    Functional [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∧
    ¬ ((0 : Nat) ∉ dsts [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] ∨
       (0 : Nat) ∉ srcs [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) ∧
    ∀ (σ : Nat → Nat) (l : Nat), l ≠ 0 →
      runSeq (sequentialize 0 [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)]) σ l =
        pmove [((0 : Nat), (0 : Nat)), (1, 2), (2, 1)] σ l

-- lean/ToyParMove/CycleTightness.lean:411-415
-- lean/ToyParMove/CycleTightness.lean — finite check of four concrete instances (k = 2, 3, 4, 5); not a general theorem
theorem sequentialize_cycle_length_examples :
    (sequentialize (9 : Nat) (cycleMoves [0, 1])).length = 3 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2])).length = 4 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3])).length = 5 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3, 4])).length = 6
```

#### 4. `sequential-composition-of-move-blocks`

- Both blocks share the single scratch location tmp; composing blocks that clobber two different scratch locations is not covered.
- Does not say every correct sequentialization decomposes into such blocks.
- The counterexample for htmp shows a cycle-first emission order is wrong when tmp is read; it does not show that the Rideau-Serpette-Leroy algorithm or any other published algorithm emits that order.
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

#### 5. `topological-order-realizes-parallel-move`

- Only sufficiency is proved; the converse (every exact plain-move realization of a list in its own order is topological) is not claimed. Topological also rejects harmless orders, e.g. a self-move before a reader of its location ([(1,1),(2,1)] is not topological but runs correctly on every store: topological_rejects_benign_self_move).
- Functional is needed only because the adopted reading is first-entry: for the last-entry reading, a topological list realizes pmoveLast without any functionality hypothesis (runSeq_eq_pmoveLast_of_topological).
- A move list containing a cycle has no topological reordering: if every move of a duplicate-free cycle of length at least 2 occurs in M, then no reordering of M is topological, whatever other moves M contains (not_topological_of_contains_cycleMoves). This follows from the general criterion not_topological_of_dsts_read (a list is not topological if a nonempty collection of its moves has every destination read by another move of the collection); not_topological_of_perm_cycleMoves covers only reorderings of the cycle itself. This does not mean that every cyclic parallel move needs a scratch location or swaps: an isolated cycle does (cycle-without-scratch-impossible), but a cycle with an outgoing copy such as [(3,1),(2,1),(1,2)] is realized exactly, from every store, by the plain moves [(3,1),(1,2),(2,3)], which read the saved value from the already-written destination 3 and are not a reordering of the list (cycle_with_outgoing_copy_realized_without_scratch).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Necessity.lean:321-324
-- lean/ToyParMove/Necessity.lean — single concrete move list (all value types and stores); it proves nothing beyond this list
theorem topological_rejects_benign_self_move :
    ¬ Topological [((1 : Nat), (1 : Nat)), (2, 1)] ∧
    ∀ (V : Type) (σ : Nat → V),
      runSeq [((1 : Nat), (1 : Nat)), (2, 1)] σ = pmove [((1 : Nat), (1 : Nat)), (2, 1)] σ

-- lean/ToyParMove/Necessity.lean:338-340
-- lean/ToyParMove/Necessity.lean — universally quantified theorem
theorem not_topological_of_dsts_read {ms C : List (Loc × Loc)} (hC : C ≠ [])
    (hsub : ∀ m ∈ C, m ∈ ms) (hread : ∀ m ∈ C, ∃ m' ∈ C, m' ≠ m ∧ m'.2 = m.1) :
    ¬ Topological ms

-- lean/ToyParMove/Necessity.lean:405-406
-- lean/ToyParMove/Necessity.lean — universally quantified theorem
theorem runSeq_eq_pmoveLast_of_topological :
    ∀ {ms : List (Loc × Loc)}, Topological ms → ∀ σ : Loc → V, runSeq ms σ = pmoveLast ms σ

-- lean/ToyParMove/Cycles.lean:379-380
-- lean/ToyParMove/Cycles.lean — universally quantified theorem
theorem not_topological_of_perm_cycleMoves {ls : List Loc} {ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length) (hp : ms.Perm (cycleMoves ls)) : ¬ Topological ms

-- lean/ToyParMove/Boundaries.lean:28-31
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem not_topological_of_contains_cycleMoves {ls : List Loc} {M ms : List (Loc × Loc)}
    (hn : ls.Nodup) (hk : 2 ≤ ls.length)
    (hsub : ∀ m ∈ cycleMoves ls, m ∈ M) (hp : ms.Perm M) :
    ¬ Topological ms
```

#### 6. `cycle-with-scratch-upper-bound`

- The theorem says nothing about location tmp. Unproved commentary, read off the definition of cycleSeqScratch (no theorem states it): under the theorem's hypotheses the first move copies l(k-1) into tmp and no later move writes tmp, so tmp ends holding the old value of l(k-1). Hence tmp keeps its own old value exactly when tmp and l(k-1) initially hold equal values (for example on a constant store), and changes whenever they initially hold different values.
- Stated for nonempty cycles (the list l₀ :: rest); for k = 1 the list cycleSeqScratch has 2 moves although the self-move needs none, and for the empty list cycleSeqScratch tmp [] is empty (length 0, not 1).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

#### 7. `cycle-with-scratch-lower-bound`

- Covers one isolated cycle only (cycleMoves ls fixes every location outside ls). No bound for general parallel moves is proved. In particular the count 'moved locations + number of cycles' is not a lower bound for general parallel moves: [(3,1),(2,1),(1,2)], a 2-cycle with an outgoing copy, has 3 moves and one 2-cycle but is realized exactly by 3 plain moves with no scratch (cycle_with_outgoing_copy_realized_without_scratch); Boissinot et al. count one extra copy only per 'circuit with no tree edge'.
- Function.Injective σ is injectivity on the whole location type, so an injective store exists only when the location type is no larger than the value type (a cardinality fact, not proved here); for example no store Nat → Bool is injective (no_injective_store_nat_bool, proved for every σ : Nat → Bool), and by the same cardinality argument (not proved here) no store Nat → BitVec w is injective. In such settings the injective-store statement is vacuous; use the uniform (all-stores) statement of this card, which needs only two distinct values.
- Statement (a) is per store: with coinciding values fewer moves can suffice, and injectivity on the cycle locations and tmp alone does not give the bound (cycle_lower_bound_needs_global_injectivity).
- Moves may use any locations, but only tmp may end with a wrong value; with more clobberable locations the statement does not apply.
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Cycles.lean:423
-- lean/ToyParMove/Cycles.lean — universally quantified over all stores Nat → Bool
theorem no_injective_store_nat_bool : ∀ σ : Nat → Bool, ¬ Function.Injective σ
```

#### 8. `cycle-without-scratch-impossible`

- Escape hatches: allowing one location outside the cycle to be clobbered makes the cycle realizable with k + 1 moves (cycle-with-scratch-upper-bound); a swap primitive realizes it exactly with k - 1 swaps (cycle-with-swaps-upper-bound); cycle_impossibility_positive_control checks both for the 2-cycle [0, 1] at the identity store.
- Escape hatch for non-isolated cycles: cycleMoves ls is an isolated cycle that fixes every location outside ls. If the parallel move also copies a cycle location to a destination outside the cycle, plain moves can suffice with no scratch location and no swap: [(3,1),(2,1),(1,2)] is realized exactly, from every store, by 3 := 1; 1 := 2; 2 := 3 (cycle_with_outgoing_copy_realized_without_scratch; the example of Rideau-Serpette-Leroy Section 9).
- Function.Injective σ is injectivity on the whole location type, so an injective store exists only when the location type is no larger than the value type (a cardinality fact, not proved here); for example no store Nat → Bool is injective (no_injective_store_nat_bool, proved for every σ : Nat → Bool), and by the same cardinality argument (not proved here) no store Nat → BitVec w is injective. In such settings the injective-store statement is vacuous; use the uniform (all-stores) statement of this card, which needs only two distinct values.
- Statement (a) is per store: for a constant store the empty sequence works, and injectivity on the cycle locations alone does not suffice (cycle_impossibility_needs_global_injectivity). Conversely, when no store is injective (for example a 3-cycle of Bool flags), it does not follow that some fixed plain-move sequence works for all stores: statement (b) excludes that whenever the value type has two distinct values.
- Plain moves only; instructions that combine values (xor, add/sub) are not covered (the xor-swap realizes a swap without scratch).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Cycles.lean:423
-- lean/ToyParMove/Cycles.lean — universally quantified over all stores Nat → Bool
theorem no_injective_store_nat_bool : ∀ σ : Nat → Bool, ¬ Function.Injective σ
```

#### 9. `cycle-with-swaps-upper-bound`

- Says nothing about how a swap is implemented; an xor-swap implementation needs distinct operands or a zero value in the aliased location (see xor-swap-correct-iff-distinct-or-zero).
- At k = 0, ls.length - 1 is 0 by truncated subtraction (length_cycleSwaps_nil).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Swaps.lean:312-313
-- lean/ToyParMove/Swaps.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem length_cycleSwaps_nil :
    (cycleSwaps ([] : List Nat)).length = 0 ∧ ([] : List Nat).length - 1 = 0
```

#### 10. `cycle-with-swaps-lower-bound`

- Swap-only sequences; mixing swaps with plain moves or a scratch location is not covered.
- One cycle only.
- Function.Injective σ is injectivity on the whole location type, so an injective store exists only when the location type is no larger than the value type (a cardinality fact, not proved here); for example no store Nat → Bool is injective (no_injective_store_nat_bool, proved for every σ : Nat → Bool), and by the same cardinality argument (not proved here) no store Nat → BitVec w is injective. In such settings the injective-store statement is vacuous; use the uniform (all-stores) statement of this card, which needs only two distinct values.
- Swaps only permute locations: runSwaps ss σ = σ ∘ runSwaps ss id (runSwaps_comp), so a swap sequence never creates a value and cannot keep a backup copy of a cycle value in a location outside the cycle. Consequently statement (a) needs injectivity of σ only on the cycle locations ls (cycle_length_sub_one_le_of_injOn_of_runSwaps, with a store that is injective on the cycle but not globally in nonvacuity_cycle_length_sub_one_le_of_injOn_of_runSwaps); (a) states global Function.Injective σ for uniformity with the plain-move bounds, where injectivity on the cycle is not enough (cycle_lower_bound_needs_global_injectivity).
- At k = 0 the bound ls.length - 1 is 0 by truncated subtraction (length_cycleSwaps_nil).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Cycles.lean:423
-- lean/ToyParMove/Cycles.lean — universally quantified over all stores Nat → Bool
theorem no_injective_store_nat_bool : ∀ σ : Nat → Bool, ¬ Function.Injective σ

-- lean/ToyParMove/Swaps.lean:54-55
-- lean/ToyParMove/Swaps.lean — universally quantified theorem
theorem runSwaps_comp (f : V → W) : ∀ (ss : List (Loc × Loc)) (τ : Loc → V),
    runSwaps ss (f ∘ τ) = f ∘ runSwaps ss τ

-- lean/ToyParMove/Swaps.lean:312-313
-- lean/ToyParMove/Swaps.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem length_cycleSwaps_nil :
    (cycleSwaps ([] : List Nat)).length = 0 ∧ ([] : List Nat).length - 1 = 0

-- lean/ToyParMove/Boundaries.lean:141-146
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem cycle_length_sub_one_le_of_injOn_of_runSwaps
    {ls : List Loc} {σ : Loc → V} {ss : List (Loc × Loc)}
    (hn : ls.Nodup)
    (hinj : ∀ x ∈ ls, ∀ y ∈ ls, σ x = σ y → x = y)
    (hreal : runSwaps ss σ = pmove (cycleMoves ls) σ) :
    ls.length - 1 ≤ ss.length

-- lean/ToyParMove/Boundaries.lean:262-267
-- lean/ToyParMove/Boundaries.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem nonvacuity_cycle_length_sub_one_le_of_injOn_of_runSwaps :
    let σ : Nat → Nat := fun l => if l ≤ 2 then l else 0
    ([0, 1, 2] : List Nat).Nodup ∧
      (∀ x ∈ ([0, 1, 2] : List Nat), ∀ y ∈ ([0, 1, 2] : List Nat), σ x = σ y → x = y) ∧
      ¬ Function.Injective σ ∧
      runSwaps (cycleSwaps [0, 1, 2]) σ = pmove (cycleMoves [0, 1, 2]) σ
```

#### 11. `xor-swap-correct-iff-distinct-or-zero`

- Illustration of the aliasing hazard (a single concrete instance with 8-bit words): if both operands of a parallel swap [(a,b),(b,a)] are allocated to the same register 0 holding 1, the parallel move and the true swap leave 1 there but the xor-swap idiom leaves 0 (xorSwap_unsafe_for_aliased_parallel_swap). By the characterization of this card the failure does not occur when the aliased location holds zero, and at width w = 0 it cannot occur (xorSwap_eq_swapStore_width_zero, stated for locations Nat).
- Locations are independent keys of a store Loc → BitVec w: partial overlap between distinct register names (for example x86 al and ax, which share bits 0..7) is not modeled, and neither are xor instructions that zero-extend their 32-bit result into a 64-bit register; both can break the swap on real hardware.
- Only BitVec words with bitwise xor are modeled; add/sub variants and flag side effects are not.
- No claim about performance or about whether real instruction sets provide an exchange instruction.
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/XorSwap.lean:118-121
-- lean/ToyParMove/XorSwap.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem xorSwap_unsafe_for_aliased_parallel_swap :
    pmove [((0 : Nat), (0 : Nat)), (0, 0)] (fun _ : Nat => (1#8 : BitVec 8)) 0 = 1#8 ∧
    swapStore (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 1#8 ∧
    xorSwap (fun _ : Nat => (1#8 : BitVec 8)) 0 0 0 = 0#8

-- lean/ToyParMove/XorSwap.lean:161-162
-- lean/ToyParMove/XorSwap.lean — universally quantified over stores Nat → BitVec 0 and locations a, b : Nat
theorem xorSwap_eq_swapStore_width_zero (σ : Nat → BitVec 0) (a b : Nat) :
    xorSwap σ a b = swapStore σ a b
```

#### 12. `xor-swap-sequences-sound-without-self-swaps`

- Says nothing about swap lists produced by other algorithms; each must be checked for self-swaps.
- At width w = 0 every word is 0#0, so self-swaps are harmless there; the counterexamples use w = 8.
- Partial sub-register aliasing and 32-bit zero-extending xor instructions are not modeled (see xor-swap-correct-iff-distinct-or-zero).
- Toy model: locations are an arbitrary type with decidable equality and a store is a total function; there are no register classes, no memory operands, no stack slots with different sizes, and no cost model. Nothing is claimed about any production compiler.

#### 13. `preserve-upper-lane-write-is-very-well-behaved-lens`

- The lens laws (GetPut, PutGet, PutPut) are defined locally for total functions; general lens frame laws and product decompositions are outside the scope of this package.
- hfit is sufficient and tight but not exactly necessary: PutGet holds if and only if L.wid = 0 ∨ L.Fits n (putLane_putGet_iff_wid_zero_or_fits), because for an empty lane the view type BitVec 0 has a single element; for example the empty lane (9, 0) lies beyond an 8-bit register and still satisfies PutGet (putLane_putGet_width_zero_beyond_register). Together with the unconditional GetPut and PutPut, VeryWellBehaved therefore also holds for empty lanes.
- Modeling bridge (derived, not a theorem): x86-64 8-bit and 16-bit register writes behave like putLane on lanes (0,8), (8,8), (0,16); 32-bit writes do not, they zero-extend (writeZext 64).
- Which (register, lane) pairs exist as instruction operands on a real ISA, and which combinations one instruction can encode, is not modeled: every lane of every register is allowed here.
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Boundaries.lean:280-281
-- lean/ToyParMove/Boundaries.lean — universally quantified theorem
theorem putLane_putGet_iff_wid_zero_or_fits (L : Lane) :
    PutGet (getLane (n := n) L) (putLane L) ↔ (L.wid = 0 ∨ L.Fits n)

-- lean/ToyParMove/Boundaries.lean:303-304
-- lean/ToyParMove/Boundaries.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem putLane_putGet_width_zero_beyond_register :
    ¬ (⟨9, 0⟩ : Lane).Fits 8 ∧ PutGet (getLane (n := 8) ⟨9, 0⟩) (putLane ⟨9, 0⟩)
```

#### 14. `disjoint-lane-writes-commute-and-frame`

- Disjoint counts bit positions beyond the register; for lanes sticking out of the register it is stronger than needed (lane-writes-commute-iff-disjoint gives the exact in-register condition).
- Concrete instance of the failure for overlapping lanes: in a 16-bit register, writing 0xFF to (0,8) and 0x0000 to (0,16) in the two orders gives different words (putLane_overlapping_not_comm).
- The converse of framing is not stated separately; for commutation see lane-writes-commute-iff-disjoint.
- Applies only to preserve-upper writes. On x86-64 and AArch64 a 32-bit general-purpose register write zero-extends into the 64-bit register (writeZext 64 with wid = 32; see the modeling bridges stated under Findings, Modeling bridges), so the commutation and framing statements of this card do not cover it: writeZext sets every bit at a position ≥ wid to zero (writeZext_upper_zero).
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:296-297
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_upper_zero {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    ∀ i, wid ≤ i → (writeZext n v w).getLsbD i = false
```

#### 15. `lane-writes-commute-iff-disjoint`

- Commutation for all values; specific value pairs may commute even for overlapping lanes (e.g. writing the same bits).
- Empty lanes (wid = 0) are Disjoint from every lane and commute with every write; no positive-width condition is needed.
- Applies only to preserve-upper writes. On x86-64 and AArch64 a 32-bit general-purpose register write zero-extends into the 64-bit register (writeZext 64 with wid = 32; see the modeling bridges stated under Findings, Modeling bridges), so the commutation and framing statements of this card do not cover it: writeZext sets every bit at a position ≥ wid to zero (writeZext_upper_zero).
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:296-297
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_upper_zero {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    ∀ i, wid ≤ i → (writeZext n v w).getLsbD i = false
```

#### 16. `zero-extend-write-not-a-narrow-lens`

- Escape hatch (whole-word view): the zero-extending write is the full-width lane write of the zero-extended value, a very well-behaved lens with the whole word as its view (zero-extend-write-is-full-word-replacement).
- Escape hatch (words with zero upper bits): GetPut fails only on words with a nonzero bit at a position ≥ wid (zero-extend-write-getput-iff-upper-bits-zero). On words whose bits at positions ≥ wid are all zero (for example values produced by earlier zero-extending writes), the low-lane getter and writeZext satisfy GetPut, PutGet (for wid ≤ n, writeZext_putGet_of_le) and PutPut, and writeZext keeps words in that set (writeZext_upper_zero).
- PutGet and PutPut do hold for the zero-extending write with the low-lane getter on all words (writeZext_putGet_of_le, writeZext_putPut); only GetPut fails.
- writeZext n v is defined as BitVec.setWidth n v, which zero-extends when wid ≤ n and truncates to the low n bits when wid > n (the semantics of the core BitVec.setWidth; for example writeZext 8 0x1234#16 0#8 = 0x34#8, writeZext_truncates_example); the name describes the case wid ≤ n, which is the case of the modeling bridges.
- That x86-64 32-bit and AArch64 W-register writes behave like writeZext 64 with wid = 32 is a modeling bridge (derived), not a theorem.
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:296-297
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_upper_zero {wid : Nat} (v : BitVec wid) (w : BitVec n) :
    ∀ i, wid ≤ i → (writeZext n v w).getLsbD i = false

-- lean/ToyParMove/Lanes.lean:355
-- lean/ToyParMove/Lanes.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8
```

#### 17. `zero-extend-write-getput-iff-upper-bits-zero`

- A pointwise statement about one word; it is not a lens law.
- When wid ≥ n the right-hand side holds for every w (bits at positions ≥ n read as false), so the equality holds unconditionally (writeZext_getPut_of_ge).
- writeZext n v is defined as BitVec.setWidth n v, which zero-extends when wid ≤ n and truncates to the low n bits when wid > n (the semantics of the core BitVec.setWidth; for example writeZext 8 0x1234#16 0#8 = 0x34#8, writeZext_truncates_example); the name describes the case wid ≤ n, which is the case of the modeling bridges.
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:289-290
-- lean/ToyParMove/Lanes.lean — universally quantified theorem
theorem writeZext_getPut_of_ge {wid : Nat} (h : n ≤ wid) :
    GetPut (getLane (n := n) ⟨0, wid⟩) (writeZext n (wid := wid))

-- lean/ToyParMove/Lanes.lean:355
-- lean/ToyParMove/Lanes.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8
```

#### 18. `zero-extend-write-is-full-word-replacement`

- The full-word lens has the whole n-bit word as its view; it is not a lens with a wid-bit view (zero-extend-write-not-a-narrow-lens).
- Only writeZext_putPut holds by definitional unfolding; the other three statements need bitwise reasoning (writeZext_eq_putLane_full, writeZext_putGet_of_le) or instantiate preserve-upper-lane-write-is-very-well-behaved-lens.
- writeZext n v is defined as BitVec.setWidth n v, which zero-extends when wid ≤ n and truncates to the low n bits when wid > n (the semantics of the core BitVec.setWidth; for example writeZext 8 0x1234#16 0#8 = 0x34#8, writeZext_truncates_example); the name describes the case wid ≤ n, which is the case of the modeling bridges.
- Toy model: a register is an n-bit word (BitVec n) and a lane is a contiguous bit range (off, wid); no flags, no partial-register stalls or timing, no vector registers, no memory. ISA statements are modeling bridges only (derived), not theorems about hardware.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/Lanes.lean:355
-- lean/ToyParMove/Lanes.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem writeZext_truncates_example : writeZext 8 (0x1234#16) (0#8) = 0x34#8
```

#### 19. `distinct-lane-destinations-not-enough`

- Specific values only. That LaneWF suffices for order independence is the separate result lane-parallel-move-order-independent-for-disjoint-lanes; this card does not prove it.
- For positive-width moves LaneWF implies DistinctDstLanes (laneWF_implies_distinctDstLanes_of_pos_wid, an uncarded universally quantified theorem). At width 0 the implication fails: the list [lm 0 4 1 0 0, lm 0 4 2 0 0] of two empty moves into the same lane (4, 0) of register 0 is LaneWF, because empty lanes are Disjoint by definition, but not DistinctDstLanes (laneWF_not_implies_distinctDstLanes_width_zero, a single concrete instance).
- lanePMove applies the destination-lane writes in list order, so on overlapping bits the later entry wins; this is the opposite tie-break from the whole-register pmove, where the first entry wins.
- Toy model of lane moves: each move copies wid bits between lanes with a preserve-upper write; registers are n-bit words indexed by an arbitrary type with decidable equality. No zero-extending lane moves, no scratch location, no algorithm producing the emission order is given.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/LaneMoves.lean:168-170
-- lean/ToyParMove/LaneMoves.lean — universally quantified theorem
theorem laneWF_implies_distinctDstLanes_of_pos_wid {R : Type} [DecidableEq R]
    {M : List (LaneMove R)} (hwf : LaneWF M) (hpos : ∀ m ∈ M, 0 < m.wid) :
    DistinctDstLanes M

-- lean/ToyParMove/LaneMoves.lean:269-270
-- lean/ToyParMove/LaneMoves.lean — single concrete instance: fixed inputs; it proves nothing beyond this instance
theorem laneWF_not_implies_distinctDstLanes_width_zero :
    LaneWF [lm 0 4 1 0 0, lm 0 4 2 0 0] ∧ ¬ DistinctDstLanes [lm 0 4 1 0 0, lm 0 4 2 0 0]
```

#### 20. `lane-parallel-move-order-independent-for-disjoint-lanes`

- LaneWF is sufficient (this card) but not necessary, even when order independence is required for every register file. Three single instances, each violating LaneWF yet order-independent on every register file of the stated word size: the exact duplicate [lm 0 0 1 0 8, lm 0 0 1 0 8] of a nonempty lane move, 16-bit words, every reordering (lanePMove_perm_invariant_duplicate_not_laneWF); [lm 0 0 1 0 8, lm 0 0 1 0 16], overlapping moves that copy aligned bits from the same source register, 16-bit words, both orders (lanePMove_same_source_overlap_not_laneWF); and [lm 0 6 1 0 4, lm 0 8 1 0 4], 8-bit words, whose destination lanes overlap only at bit positions 8 and 9, beyond the register, both orders (lanePMove_beyond_register_overlap_not_laneWF). No necessary and sufficient condition for order independence of lane moves is proved.
- lanePMove applies the destination-lane writes in list order, so on overlapping bits the later entry wins; this is the opposite tie-break from the whole-register pmove, where the first entry wins.
- Not a model of 32-bit general-purpose register moves on x86-64 or AArch64: those zero-extend into the 64-bit register (writeZext 64), whereas every lane move here preserves the other bits (putLane).
- Which (register, lane) pairs exist as instruction operands on a real ISA, and which combinations one instruction can encode, is not modeled: every lane of every register is allowed here.
- Toy model of lane moves: each move copies wid bits between lanes with a preserve-upper write; registers are n-bit words indexed by an arbitrary type with decidable equality. No zero-extending lane moves, no scratch location, no algorithm producing the emission order is given.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/LaneMoves.lean:330-333
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (all reorderings, all 16-bit register files); it proves nothing beyond this list
theorem lanePMove_perm_invariant_duplicate_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 8] ∧
    ∀ (M' : List (LaneMove Nat)), M'.Perm [lm 0 0 1 0 8, lm 0 0 1 0 8] →
      ∀ ρ : Nat → BitVec 16, lanePMove M' ρ = lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 8] ρ

-- lean/ToyParMove/LaneMoves.lean:339-342
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (both orders, all 16-bit register files); it proves nothing beyond this list
theorem lanePMove_same_source_overlap_not_laneWF :
    ¬ LaneWF [lm 0 0 1 0 8, lm 0 0 1 0 16] ∧
    ∀ ρ : Nat → BitVec 16,
      lanePMove [lm 0 0 1 0 8, lm 0 0 1 0 16] ρ = lanePMove [lm 0 0 1 0 16, lm 0 0 1 0 8] ρ

-- lean/ToyParMove/LaneMoves.lean:360-363
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (both orders, all 8-bit register files); it proves nothing beyond this list
theorem lanePMove_beyond_register_overlap_not_laneWF :
    ¬ LaneWF [lm 0 6 1 0 4, lm 0 8 1 0 4] ∧
    ∀ ρ : Nat → BitVec 8,
      lanePMove [lm 0 6 1 0 4, lm 0 8 1 0 4] ρ = lanePMove [lm 0 8 1 0 4, lm 0 6 1 0 4] ρ
```

#### 21. `lane-parallel-move-sound-for-disjoint-lanes-topological-order`

- When the emitted list is M itself (no reordering), LaneWF is unnecessary: LaneTopological M alone gives runLanes M ρ = lanePMove M ρ (runLanes_eq_lanePMove_of_topological), because both sides apply the writes in the same order. LaneWF is needed because the theorem allows any reordering.
- LaneTopological also rejects some harmless orders: [lm 0 0 0 0 8, lm 1 0 0 0 8] (a self-copy of the low byte of register 0, then a move that reads it) is not lane-topological, yet runLanes and lanePMove agree on it for every 16-bit register file (laneTopological_rejects_benign_self_copy, a single concrete instance).
- Cyclic lane moves are not covered: no theorem states that a cyclic lane move has no lane-topological order (for the in-register byte swap [lm 0 0 0 8 8, lm 0 8 0 0 8], the given order is not lane-topological: runLanes_needs_topological), and breaking such cycles with a scratch lane is not covered.
- No sequentialization algorithm for lane moves is given or verified.
- Unlike the overlap extension of Rideau-Serpette-Leroy and CompCert, writes here are exact preserve-upper writes, so no 'no partial overlap between sources and destinations' hypothesis appears; this is a property of the toy model, not a claim about hardware.
- lanePMove applies the destination-lane writes in list order, so on overlapping bits the later entry wins; this is the opposite tie-break from the whole-register pmove, where the first entry wins.
- Not a model of 32-bit general-purpose register moves on x86-64 or AArch64: those zero-extend into the 64-bit register (writeZext 64), whereas every lane move here preserves the other bits (putLane).
- Which (register, lane) pairs exist as instruction operands on a real ISA, and which combinations one instruction can encode, is not modeled: every lane of every register is allowed here.
- Toy model of lane moves: each move copies wid bits between lanes with a preserve-upper write; registers are n-bit words indexed by an arbitrary type with decidable equality. No zero-extending lane moves, no scratch location, no algorithm producing the emission order is given.

Uncarded theorems cited in these non-claims, verbatim (proofs omitted):

```lean
-- lean/ToyParMove/LaneMoves.lean:138-140
-- lean/ToyParMove/LaneMoves.lean — universally quantified theorem
theorem runLanes_eq_lanePMove_of_topological :
    ∀ {ms : List (LaneMove R)}, LaneTopological ms → ∀ ρ : R → BitVec n,
      runLanes ms ρ = lanePMove ms ρ

-- lean/ToyParMove/LaneMoves.lean:376-379
-- lean/ToyParMove/LaneMoves.lean — single concrete move list (all 16-bit register files); it proves nothing beyond this list
theorem laneTopological_rejects_benign_self_copy :
    ¬ LaneTopological [lm 0 0 0 0 8, lm 1 0 0 0 8] ∧
    ∀ ρ : Nat → BitVec 16,
      runLanes [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ = lanePMove [lm 0 0 0 0 8, lm 1 0 0 0 8] ρ
```

### Escape hatches

Hypotheses whose removal or weakening defeats an impossibility or lower-bound result; each named theorem is proved.

- **cycle-without-scratch-impossible** — (1) allow one location outside the cycle to be clobbered: the cycle is then realized with k + 1 plain moves (result 6, `cycleSeqScratch`; the positive control `cycle_impossibility_positive_control` checks the 2-cycle `[0, 1]` in its first conjunct); (2) allow swaps: k - 1 swaps realize it exactly (result 9; second conjunct of the control, again for `[0, 1]`); (3) drop isolation: for example the 2-cycle with an outgoing copy `[(3,1),(2,1),(1,2)]` is realized by the plain moves `[(3,1),(1,2),(2,3)]` (`cycle_with_outgoing_copy_realized_without_scratch`, third conjunct of the control); (4) drop global injectivity of the store in statements (a), (a'): two equal values elsewhere can let one location be borrowed and restored (`cycle_impossibility_needs_global_injectivity`, a single concrete instance); (5) allow instructions that combine values: the xor-swap realizes a swap without scratch (`xorSwap_eq_swapStore_of_ne`).
- **zero-extend-write-not-a-narrow-lens** — (1) take the whole word as the view: the zero-extending write is the full-width preserve-upper write of the zero-extended value, a very well-behaved lens (`writeZext_eq_putLane_full`, `putLane_full_veryWellBehaved`; positive control `writeZext_getPut_full`); (2) restrict to words whose bits at positions ≥ wid are zero: GetPut then holds (`writeZext_getPut_iff`), and writeZext stays in that set (`writeZext_upper_zero`); (3) `wid = n`: the hypothesis `wid < n` fails, and GetPut holds with the full-width getter `getLane ⟨0, n⟩` for every `n` (`writeZext_getPut_full`; the counterexample `writeZext_not_getPut_needs_lt` is the instance `n = 8`).
- **cycle-with-scratch-lower-bound** and **cycle-with-swaps-lower-bound** — with more clobberable locations, a non-isolated cycle, or a store that is not globally injective (for plain moves), the bounds no longer apply; see the non-claims of these cards and `cycle_lower_bound_needs_global_injectivity`.

### Tightness status

Every hypothesis of every card theorem is labelled `tight` and has a named, proved counterexample in which all other hypotheses of that theorem hold and the conclusion fails. No hypothesis is labelled `harmless` or `unknown`. Where a hypothesis is tight but stronger than needed in a corner case, the card's non-claims say so (result 3: an input in which `tmp` occurs only in a self-move `(tmp, tmp)`; results 5 and 21: harmless self-copies are rejected by `Topological` and `LaneTopological`; result 10: injectivity on the cycle locations suffices; result 13: empty lanes; result 14: lanes beyond the register; result 20: `LaneWF` is not necessary; result 21: `LaneWF` is unnecessary when the emitted list is `M` itself).

### Disproved or dropped statements

None. Every result stated for this package is proved, and no statement was found false.

### Not examined, unknown, unsupported

- **unknown** — a move-count formula (lower bound) for general parallel moves, e.g. one extra copy per cycle with no outgoing copy; only the isolated-cycle case is proved, and the naive count 'moved locations + number of cycles' is known not to be a lower bound in general: the 2-cycle with an outgoing copy `[(3,1),(2,1),(1,2)]` is realized exactly by 3 plain moves (`cycle_with_outgoing_copy_realized_without_scratch`).
- **not examined** — whether `sequentialize tmp M` leaves `tmp` unchanged on acyclic `M`; the algorithm's time complexity; correctness of the Rideau–Serpette–Leroy stack-based algorithm or Boissinot et al.'s Algorithm 1 in this model; sequentialization of cyclic lane moves.
- **not examined** — register classes, several scratch locations, memory operands, and instructions that combine values other than xor (add/sub exchanges, flags).
- **not examined** — the Intel manual's section body (only its table-of-contents entry was confirmed); the normative Arm Architecture Reference Manual (only the Arm guide 102374 v1.4 was read); instruction encodability on either architecture.
- **unsupported by the model** — overlapping whole-register names in the store `Loc → V` (for example `al` and `ax` as two locations); zero-extending lane moves.

## Evidence

### Kernel-check record

- Toolchain: `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API, `repos/leanprover/lean4/git/ref/tags/v4.34.1`, object type `commit`). No Mathlib, no Lake dependency (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyParMove`, and no `[[require]]`).
- `lake build` of `lean/` succeeds with no errors, no warnings and no `sorry`. The sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe`, or `debug.skipKernelTC`. Concrete instances are evaluated with `decide` (kernel reduction) or `rfl`, never by native evaluation.
- Axioms: all 486 declarations of the `ToyParMove` library (computed with Lean's `collectAxioms`) depend only on a subset of `Classical.choice`, `Quot.sound`, `propext`. The per-declaration record is `audit/axioms.json`.
- Statement and closure hashes: `audit/statements.json` records, for every Lean name a card references (results, counterexamples, non-vacuity witnesses, positive controls), the SHA-256 of the statement (`toString (repr ci.type)`, the Lean `repr` of the elaborated type) and of its definition closure (the sorted, newline-joined entries `name : repr(type)`, plus ` := repr(value)` for non-theorems, of every `ToyParMove` constant reachable from the statement through types, definition bodies and inductive constructors; theorem bodies excluded). Both are reproduced below.

| Name | Used by (result: role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.ParMove.pmove_readings_disagree_on_repeated_destination` | 1 result | (none) | `53378f26763385c8677adf45cf78ea08d34ba545e869e8ef46d8696cc7155960` | `cf16e04fd30227d3212cd23cd48e5fc9c8b36eb2677281b45f15a22c4de801a3` (6) |
| `Toy.ParMove.pmove_perm_invariant_iff_functional_of_two_values` | 2 result | Classical.choice, Quot.sound, propext | `65ea40f26a31283591c3d34d1c2ab88e18f4e1a577d6a2dee0935159670ce365` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.pmove_perm_invariant_of_functional` | 2 result | Quot.sound, propext | `370e7c9a0d61a72d60e89b7d328a501a577fad0fb9863c7c469fc5a51c3e507d` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.functional_of_pmove_perm_invariant_of_two_values` | 2 result | Classical.choice, Quot.sound, propext | `8fa2c17c00a9c96d2dfdac7b7874e0356e1ac3e3e402029087481ca02f7f9174` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.pmove_perm_invariant_at_iff_functionalAt` | 2 result | Classical.choice, Quot.sound, propext | `3517c478029fb639d935ac8b9b8f1b6fb68a19a6ade720047b4e47a2b31d023d` | `7f90bf87c8664898a45732184fe373cd3e0e204ad58c9e1d70a480aa0b123eb5` (6) |
| `Toy.ParMove.pmove_eq_pmoveLast_of_functional` | 2 result | Quot.sound, propext | `a77b3cb6d1c882d2e9740e5af5e5b9632d04134032da97dd5211540ea2fde872` | `b03ed65e6c32f09e8867b997ca7e89c4696584091026115fb132f24af001c493` (7) |
| `Toy.ParMove.functional_of_pmove_perm_invariant_needs_two_values` | 2 counterexample | Quot.sound, propext | `64116439f5929a48c77fb6243bed07365cdd1eecad7f45885d928af4f188bcce` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.functional_of_pmove_perm_invariant_needs_perm_invariance` | 2 counterexample | Quot.sound, propext | `d85e5f833470c35d71661f5121e281de61bc11eabc9e9810aa31fface7d63fa7` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.pmove_perm_invariant_needs_functional` | 2 counterexample | Quot.sound, propext | `26cdc4a27479564073d9a59dfb345492d14cad2428a149877b018eb24fa60678` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.pmove_perm_invariant_needs_perm` | 2 counterexample | propext | `81b1bf4cc21711c90589056e109f8b1397460e27a4aeeb3f8f17140a61ef50f2` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.pmove_eq_pmoveLast_needs_functional` | 2 counterexample | Quot.sound, propext | `cc3369e7f4be31beb2e0f9f79383a17f88d35f3f295e98605bc219919e451b74` | `b03ed65e6c32f09e8867b997ca7e89c4696584091026115fb132f24af001c493` (7) |
| `Toy.ParMove.nonvacuity_pmove_perm_invariant_all` | 2 witness | Quot.sound, propext | `9a9a790ca2c8d89b55d540d9df7b5c7da9b404ccffff889dca91cb4ae04d17c1` | `47ddf09cebbf9bc9486511dfe4bb49141ec8e22862770bcf6c1e5a652eeda79a` (6) |
| `Toy.ParMove.functionalAt_equal_values_example` | 2 witness | Quot.sound, propext | `74492b4164d2ea9ad49f18410774734ec58d38e4d827ddd9fb4ba013d98e6a2a` | `27873d37b520e1bb5482ebcc90b70c5b7da2fdc83e556b53dbb2a3ba233e2264` (2) |
| `Toy.ParMove.not_functionalAt_id_example` | 2 witness | propext | `84de8e965827426f0a84f90def5c058c7025e60a8226b31922ced11b28e74d39` | `bdf6836a0fa025956e2043fc1d67a4bdb69b8a5f08808234da47f147bcca871a` (1) |
| `Toy.ParMove.sequentialize_agrees_off_tmp` | 3 result | Classical.choice, Quot.sound, propext | `ad5e7a586e65c94a1600c227de69ea11c85890be52cbef03c9dec18bc24aa26a` | `061690280f480194b50054c4ea35d299a72e9078594ae5aea40e516f6c3e9ccd` (19) |
| `Toy.ParMove.sequentialize_needs_functional` | 3 counterexample | Classical.choice, Quot.sound, propext | `6e8838d3305e2880463cb35834667259fbfb2144b1c44dc009150b2fc6edf1b1` | `5c2e4fb8ce3f6c0d955597e3010687906403676624a5eb634282d947cd422775` (20) |
| `Toy.ParMove.sequentialize_needs_tmp_not_dst_or_not_src` | 3 counterexample | Classical.choice, Quot.sound, propext | `b892c9507b9d731466799c6cf556b750f2bc2b6e6b68115d5c49893287b4de56` | `061690280f480194b50054c4ea35d299a72e9078594ae5aea40e516f6c3e9ccd` (19) |
| `Toy.ParMove.nonvacuity_sequentialize_tmp_is_source` | 3 witness | Classical.choice, Quot.sound, propext | `3290bc10cbcbf07c962c5a127e708f1c93f35218a28514e09df91bc2fc0e1f6f` | `da00f0924c1d92d7944b2848b5483a76a58a6fb6c4fdcfdb806eab9b37cf6806` (11) |
| `Toy.ParMove.nonvacuity_sequentialize_tmp_is_destination` | 3 witness | Quot.sound, propext | `7626a9e72f11caaa989a24f7d6a246e8e7411ad929f0ec4c270a45372916bba1` | `2ebc7a341821943aad76373d6fba7608c71c6d910962961811255a194509c628` (3) |
| `Toy.ParMove.runSeq_append_realizes_off_tmp` | 4 result | Quot.sound, propext | `4c9bf7d0812137962422e9c67ae5553fc4d13ef7ef2f71198117c5cdf381c29e` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_append_needs_first_realization` | 4 counterexample | Quot.sound, propext | `f8607c4d13293970d4555320ed428cdf74a537463e7b36c505c549aef9794a82` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_append_needs_second_realization` | 4 counterexample | Quot.sound, propext | `a568eee6070d954583fa0d96fde6118e5c5feb287023ed8c6799e626b0fd844b` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_append_needs_disjoint_dsts` | 4 counterexample | Quot.sound, propext | `614371e5eb2c4abf4d969a264e21ae425f9be223ae0f516e005c10f987dc4b51` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_append_needs_sources_not_overwritten` | 4 counterexample | Quot.sound, propext | `f8222af5158d9d410406dc3e9eb978145891e8ed7683d03fd87a7c4c7ffb77f9` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_append_needs_tmp_not_src` | 4 counterexample | Classical.choice, Quot.sound, propext | `2dde9fbbb9f1cb4ee7076c88f08bd7de322c659c677047afd2d5efdbe30c475c` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.nonvacuity_runSeq_append_realizes_off_tmp` | 4 witness | Classical.choice, Quot.sound, propext | `71bec9a94d968a3c0e4915939679a5c5614a3bf01669cc994fc0274ec798d362` | `c8616ba8794d4b5a72a4314050d07941bbea3f8a19e5a640e56c7ef85dda003b` (10) |
| `Toy.ParMove.runSeq_eq_pmove_of_topological` | 5 result | Quot.sound, propext | `b54d181ee45311c28a4fb84507fe7ec1730c428ec75d4fdda5521c0c40ec411a` | `619acb39bce55d5ba481db89f24b90660128d971311ff0a7840e3587fbb3c53f` (10) |
| `Toy.ParMove.runSeq_eq_pmove_needs_functional` | 5 counterexample | Quot.sound, propext | `9adbebba95eeb59bad134c33775d48b1a756b442df37e8996f45cd6a4af361cc` | `619acb39bce55d5ba481db89f24b90660128d971311ff0a7840e3587fbb3c53f` (10) |
| `Toy.ParMove.runSeq_eq_pmove_needs_topological` | 5 counterexample | Quot.sound, propext | `2148b50b63fda798b0a1d18260d2f97a1849726f872f2e9b472ed4ec6480e5ba` | `619acb39bce55d5ba481db89f24b90660128d971311ff0a7840e3587fbb3c53f` (10) |
| `Toy.ParMove.nonvacuity_runSeq_eq_pmove_of_topological` | 5 witness | Quot.sound, propext | `e68d72d550fb4a9df2922cedded791c592ac7846b6319e94a7ce21972a45e1bd` | `96e23e3c50f3ee376c8faeced90a00444f44f5588b29615f3d480d9504d9f3b6` (2) |
| `Toy.ParMove.runSeq_cycleSeqScratch` | 6 result | Quot.sound, propext | `36372cdd9904c273a5ae9c0143b60c19bcef44283fb41a9896c6697bc4a08646` | `84745ddf5ba77fa806bf0c9d8db4e82917433251c5a8c5f574d33dc8568c1034` (14) |
| `Toy.ParMove.length_cycleSeqScratch` | 6 result | propext | `fd8324d49af40b82ce3800029975ba4ba810466ff54a57ec73ced07237c80f6a` | `1d18aa9d9a83021d748e443a902fe1da011ece56ad3b2e37a438d134d07cf47e` (5) |
| `Toy.ParMove.runSeq_cycleSeqScratch_needs_nodup` | 6 counterexample | Quot.sound, propext | `bb86fdeab677389cb4098c6aedd67b62fe73dec59d5e646005663aa1a777b5b6` | `84745ddf5ba77fa806bf0c9d8db4e82917433251c5a8c5f574d33dc8568c1034` (14) |
| `Toy.ParMove.runSeq_cycleSeqScratch_needs_tmp_fresh` | 6 counterexample | Quot.sound, propext | `8167c652fd8647cc2c40ba8146370eddeec729d7bf460d601771f0f8df19e021` | `84745ddf5ba77fa806bf0c9d8db4e82917433251c5a8c5f574d33dc8568c1034` (14) |
| `Toy.ParMove.nonvacuity_runSeq_cycleSeqScratch` | 6 witness | Quot.sound, propext | `b33a31dbfc83aca2969f14339fa5d77707230b4d6b14e5120fb33858d4782902` | `1d18aa9d9a83021d748e443a902fe1da011ece56ad3b2e37a438d134d07cf47e` (5) |
| `Toy.ParMove.cycle_length_add_one_le_of_injective_of_realizes_off_tmp` | 7 result | Classical.choice, Quot.sound, propext | `33b466657694aa6c8d8c571e9cf4c94cfa1273b6447668c48636559fad941236` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_length_add_one_le_of_two_values_of_realizes_off_tmp` | 7 result | Classical.choice, Quot.sound, propext | `e8c8d46e2c951889956e03ea8a077158d50dd04d96b5e369756777ed2c48b5a7` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_nodup` | 7 counterexample | Quot.sound, propext | `f5037f9056f1668b881e2afe0473a023809a5e6e300edc40d9c5df8599a56d19` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_uniform_needs_nodup` | 7 counterexample | Quot.sound, propext | `3042baa5381be97fafc4305596450e321942092089773fe69021b19fb9600b8c` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_two` | 7 counterexample | Quot.sound, propext | `095982ce1d7cce4761a22f4c116dc2e8955462b0c1a18de5a52d2d7b8124ab19` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_uniform_needs_two` | 7 counterexample | Quot.sound, propext | `630e76a8cb53ee9549144d9753fa7859e32be3e566c05e8f1a2d7062b052e16b` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_tmp_fresh` | 7 counterexample | Quot.sound, propext | `6f59249339116abfa1054a1647908c8fe8be0c4ef58991160a01cfca3616f8e0` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_uniform_needs_tmp_fresh` | 7 counterexample | Quot.sound, propext | `20352380d3b8be83b21e9ebf84b1e637ebccc539ae56b37f6ca450be94ba9359` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_injective` | 7 counterexample | Quot.sound, propext | `8ee4fbdb67dd778b6b276c723af1fcdd35d3bdfb78b1ea642b8d7067521eabde` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_global_injectivity` | 7 counterexample | Quot.sound, propext | `9711194a6dfc4a6d06740b22a360cea33b7d1986da573901f39f85077418241d` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_needs_realization` | 7 counterexample | Quot.sound, propext | `fa49d2aa9c9caee087843d35978a12281e13a710fb5f9ae846ba5bbeb9565963` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_uniform_needs_two_values` | 7 counterexample | Quot.sound, propext | `c653c77213d67eeade953210031263e8b1da361537867d61793698f2e2323b2e` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_lower_bound_uniform_needs_realization` | 7 counterexample | Quot.sound, propext | `62a3e6992b327bdba0b771d1fa73c04234341c6f7272c0a2347ba95db8e62551` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.nonvacuity_cycle_lower_bound` | 7 witness | Quot.sound, propext | `d9236ab85839934c179f94d0599d785e4dbd3f780c3d96828c9d06e10a858a5b` | `84745ddf5ba77fa806bf0c9d8db4e82917433251c5a8c5f574d33dc8568c1034` (14) |
| `Toy.ParMove.nonvacuity_cycle_lower_bound_uniform` | 7 witness | Quot.sound, propext | `3bde5f7d5cb1bcbac6b9e5c3da093960ba518c7c332f5c4c4a6685bad67679ae` | `84745ddf5ba77fa806bf0c9d8db4e82917433251c5a8c5f574d33dc8568c1034` (14) |
| `Toy.ParMove.runSeq_ne_pmove_cycle_of_injective` | 8 result | Classical.choice, Quot.sound, propext | `de9db9cfd88393e68dd48361cb47d996f31ed37c0c12f86773b3bf4af5abe97e` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.runSeq_ne_pmove_swap_of_injective` | 8 result | Classical.choice, Quot.sound, propext | `c36843eb09c492218da1c42cecdf83a4160843359862f65a5652fa3f607ac001` | `1444a8a6c1cc7f046e6cb5ddb9a000c54307616e3b49ef0381b8ab8b74a0a7e8` (8) |
| `Toy.ParMove.runSeq_ne_pmove_cycle_of_two_values` | 8 result | Classical.choice, Quot.sound, propext | `638c0c4bafb67c6ae595030d23d510e4280c2a495bd96655a775aab5b1fce541` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_impossibility_needs_nodup` | 8 counterexample | Quot.sound, propext | `87113a4c8058fec6b2aa88f56ac7b2fa685b70267292ace7d72519cc01739e5d` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_impossibility_uniform_needs_nodup` | 8 counterexample | Quot.sound, propext | `a124fdaec5304b632bb7ea3ddaf1a859b211fe76cd4875ee45c90f60e8048c2f` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_impossibility_needs_two` | 8 counterexample | Quot.sound, propext | `27af55f4aab5b14cc7421442d677689e3fbbb08b8fe4e14024fa2fa921f53912` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_impossibility_uniform_needs_two` | 8 counterexample | Quot.sound, propext | `786377a5b169290f59feb7d52239b686060f54d09fd842c06454c09fbe5ee8a1` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.cycle_impossibility_needs_injective` | 8 counterexample | Quot.sound | `d32549de8518155cf9c8a28612ea4253c39c4f4c2e30f01fd40580543a188405` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.swap_impossibility_needs_injective` | 8 counterexample | Quot.sound | `4e9c8f4140ab4569080e84331be0467d49f294d7a8797176a49c58f93fbb3110` | `1444a8a6c1cc7f046e6cb5ddb9a000c54307616e3b49ef0381b8ab8b74a0a7e8` (8) |
| `Toy.ParMove.cycle_impossibility_needs_global_injectivity` | 8 counterexample | Quot.sound, propext | `c91ad8dc90450d09123cc7e36065e87234473097e4378dced50a6fa44e47ca0e` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.swap_impossibility_needs_distinct` | 8 counterexample | Quot.sound, propext | `57cf8e80d0af11c32c34f7b7db9c510ea25b832cde4b65d87c0e6cf912c64dd3` | `1444a8a6c1cc7f046e6cb5ddb9a000c54307616e3b49ef0381b8ab8b74a0a7e8` (8) |
| `Toy.ParMove.cycle_impossibility_uniform_needs_two_values` | 8 counterexample | Quot.sound | `36bd4c7871d1ef3a94534b8adf91b27c52dd27171b297bb5b7336ff1f1d1d6ea` | `4415cf87e5bb0ef5cd097fc1ea261790292e1714e8dd2e91eb6ca136bc29881a` (13) |
| `Toy.ParMove.nonvacuity_cycle_impossibility` | 8 witness | (none) | `1b9cbf7aef82329b23c4c0c76f6d88e9dc2b146e0710534252e8d6d806f8ca67` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ParMove.nonvacuity_swap_impossibility` | 8 witness | (none) | `2a5b6fd6add3b40b7334c9726c7fc9654e518a4ce124091fc9c7fe376ed61fa7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ParMove.nonvacuity_cycle_impossibility_uniform` | 8 witness | (none) | `2f232d9e03cbc2f23510c19e62fb5f45936c229a1838031f8e8fddecee03d6aa` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ParMove.cycle_impossibility_positive_control` | 8 control | Quot.sound, propext | `fa57f024db183afe2fb7b463623d303dec471de18f0e684329a7b12ed32198fe` | `ea204fa979d3ad87a117bed4fb68248e8bc129b41186a03e0fa722baf4361b7e` (16) |
| `Toy.ParMove.cycle_with_outgoing_copy_realized_without_scratch` | 8 control | Quot.sound, propext | `d52298fab70013b1533e7791c3afd2f9719c3e8c0708b0bd565d57820ebedc48` | `b9403f40685833e6c1881ec3b04ac481e49c734bfe4e4393e6d86fa4a9045b07` (9) |
| `Toy.ParMove.runSwaps_cycleSwaps` | 9 result | Quot.sound, propext | `6b945aec34c0040fdef0b6f1677a7c641b3e0a1acc0f3f70396e47165199e206` | `d7191cf97efeaef2bf15f43114522fe075b960b539ff2c74d6da5cf919910237` (14) |
| `Toy.ParMove.length_cycleSwaps` | 9 result | propext | `94fe7b308d77458bdb6d818110d6476a8680ffe20ca73b504330cac9b1239ab8` | `d2e074c63ddc556c4083de4c2d9153a52e748847c5c219d867c9b30bb346fc6b` (2) |
| `Toy.ParMove.runSwaps_cycleSwaps_needs_nodup` | 9 counterexample | (none) | `7192581d243adbb5ce46ae0c4aa068d7a3a478e2503524c7a60d1ac302179c89` | `d7191cf97efeaef2bf15f43114522fe075b960b539ff2c74d6da5cf919910237` (14) |
| `Toy.ParMove.nonvacuity_runSwaps_cycleSwaps` | 9 witness | (none) | `1438ff2e36a4e7933a05d65cfc4b25b71363625669402410201b450f2eb4e854` | `d2e074c63ddc556c4083de4c2d9153a52e748847c5c219d867c9b30bb346fc6b` (2) |
| `Toy.ParMove.cycle_length_sub_one_le_of_injective_of_runSwaps` | 10 result | Classical.choice, Quot.sound, propext | `a4cfc5d4307ef0ffb2b7cdce7a9f7636db41b88a9b4ff48a7af1660d0800be6a` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.cycle_length_sub_one_le_of_two_values_of_runSwaps` | 10 result | Classical.choice, Quot.sound, propext | `f863896e01dfc27fb99c0f07f3f35218dd9b9c76a5adcdc019de96fc3878926c` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_needs_nodup` | 10 counterexample | Quot.sound, propext | `d9ebb733fdb701bbdbfcd6da672e2f29ea8fb307a11748c43a432f4d805c3181` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_uniform_needs_nodup` | 10 counterexample | Quot.sound, propext | `983631d6cc7a3b84c2cf04481ef891502eeba301169b0e0255dfefc20cf6466c` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_needs_injective` | 10 counterexample | Quot.sound | `b9e224c00b12e05411389e995a7bee06d1c3f042e680ad3b7f897bdb09ba7ac1` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_needs_realization` | 10 counterexample | (none) | `f0059b4ed611cc463c28eb824b0b24e5148af86f775450db17a90f6ad1cf9457` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_uniform_needs_two_values` | 10 counterexample | Quot.sound | `ae63feaf62c9b8b13da9980159f5d2eb36efae3746a39e5bda70edd08c5a33e0` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.swap_lower_bound_uniform_needs_realization` | 10 counterexample | (none) | `962df3bc48e4d9a1ba9d752594ddc8efd7d1a8d3eab4a27f6f68596722a76b3d` | `3b11abf0cbde14e50616e1254bafe146f2a565bac258b76cc8b53a072ee7cb03` (12) |
| `Toy.ParMove.nonvacuity_swap_lower_bound` | 10 witness | Quot.sound, propext | `3680740d4202756577235dace383575c1fe5152f6a2fdc4621cdf5cd43882582` | `d7191cf97efeaef2bf15f43114522fe075b960b539ff2c74d6da5cf919910237` (14) |
| `Toy.ParMove.nonvacuity_swap_lower_bound_uniform` | 10 witness | Quot.sound, propext | `e8fbd818354e883094c59104a8b7c8a6f1fcbb24d39ae7ef8f990041d11d4d7b` | `d7191cf97efeaef2bf15f43114522fe075b960b539ff2c74d6da5cf919910237` (14) |
| `Toy.ParMove.xorSwap_eq_swapStore_iff` | 11 result | Quot.sound, propext | `8f723f4843060bd735a5a36e7ed09e39e64e2046f94a49b1d6ef58b6a698ada4` | `30bb2b65b3ca23168ffc1e3316801b0f346020801a26593fe3c94fa89fb0dbb1` (4) |
| `Toy.ParMove.xorSwap_eq_swapStore_of_ne` | 11 result | Quot.sound, propext | `c401dbe425112e99ed9cd0d638a26038840b628ebee3eada609c46f631eb0817` | `30bb2b65b3ca23168ffc1e3316801b0f346020801a26593fe3c94fa89fb0dbb1` (4) |
| `Toy.ParMove.xorSwap_self` | 11 result | Quot.sound, propext | `27bc92605cfbc075ebff34d63f9ca52e362221ace44ca5bd7eeb40adb4317439` | `f1ade704bdba5535d70789f6172c40b417ceb74f5b62a717171b705fb9718585` (3) |
| `Toy.ParMove.xorSwap_eq_swapStore_needs_ne` | 11 counterexample | Quot.sound, propext | `fc9198adddebf1379019811dc8a34dd5645a11421689152b0a2e862ecf943b4a` | `30bb2b65b3ca23168ffc1e3316801b0f346020801a26593fe3c94fa89fb0dbb1` (4) |
| `Toy.ParMove.nonvacuity_xorSwap` | 11 witness | Quot.sound, propext | `4f4643fde3e302efb4c5bc0a20e1845286abc5de2be67eb2ef7e042554f65fe8` | `f1ade704bdba5535d70789f6172c40b417ceb74f5b62a717171b705fb9718585` (3) |
| `Toy.ParMove.runXorSwaps_eq_runSwaps_of_no_self` | 12 result | Quot.sound, propext | `e532f6d403bbf14e041bd25a4e8269ae5a990e2251839bad99dedd7d5bbdc14b` | `a1a2f96cd8a10f46dd93fdebdd2a861affa2593f7402760e3c9aa78cc61b844f` (6) |
| `Toy.ParMove.runXorSwaps_cycleSwaps` | 12 result | Quot.sound, propext | `6d767b8b32f9f8eeb2ccc718de158f9af67793c7e08f546baf7df9bcf3a8f9a3` | `875081495f1f810a3c92fb51b175937220f88cb44dff41b4fd8ab74fe610d013` (16) |
| `Toy.ParMove.runXorSwaps_needs_no_self` | 12 counterexample | Quot.sound, propext | `df0348611ab5e2d0f5c284e4a3ed79e5a7c21962857551b99fa0bcf6b63f21ef` | `a1a2f96cd8a10f46dd93fdebdd2a861affa2593f7402760e3c9aa78cc61b844f` (6) |
| `Toy.ParMove.runXorSwaps_cycleSwaps_needs_nodup` | 12 counterexample | Quot.sound, propext | `20a0b7400d4f936fffce762cf148e77176a22f40f8619505d83f5780457c595e` | `875081495f1f810a3c92fb51b175937220f88cb44dff41b4fd8ab74fe610d013` (16) |
| `Toy.ParMove.nonvacuity_runXorSwaps` | 12 witness | (none) | `23113a3801d498dba6d05bcc9a70bb1f8fa6ab7c53e320d32f906330de23d70d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ParMove.putLane_veryWellBehaved_of_fits` | 13 result | Classical.choice, Quot.sound, propext | `3ce8d546ef2d91f2bcd60c57dbac379c7184f69119480e0287bfe20050615e93` | `ee9bb8578d68ecbeabcaadb9a1b4222319e1b4a12afdeb10ce40ce43419615b1` (12) |
| `Toy.ParMove.putLane_getPut` | 13 result | Classical.choice, Quot.sound, propext | `ab2de8081f8ebe81bc45075ffa656f1ba49cc3d7c8d74136b64eb62eeed3ab50` | `08916693bb65ddc2a32fdd0076cb32a85edc472a24ac0ccbd3805e53e161b946` (8) |
| `Toy.ParMove.putLane_putGet_of_fits` | 13 result | Classical.choice, Quot.sound, propext | `980a9165afe9ebc0bffe057fb351e9d599f0b3f135064789125e08f321705e25` | `e04eaca279ec8e382772c87068bdcac9527594e1e4f37d249533245b341600e1` (9) |
| `Toy.ParMove.putLane_putPut` | 13 result | Classical.choice, Quot.sound, propext | `ccaf6448b0d40c780b23676dcad40c96a581a661df4032def61c5799d43bba1b` | `88422d1fabf61fa9ec40666030c70031674518021656c2cee5d9c932490e4aaa` (8) |
| `Toy.ParMove.putLane_putGet_needs_fits` | 13 counterexample | Quot.sound, propext | `2fc75f364ba359a0c9bb5fc98bf7ea82a6303fd60bb2f42a5034dacc6e93943e` | `ee9bb8578d68ecbeabcaadb9a1b4222319e1b4a12afdeb10ce40ce43419615b1` (12) |
| `Toy.ParMove.nonvacuity_putLane_veryWellBehaved` | 13 witness | (none) | `151a8691eda51932b9ac4b49ab24f7132b54ee1a7b68185184ceddf38f443565` | `aea9907637cfcc3e318b32b41fb0c836b12cbcd51f2a6cb4ba53bca7928b95f4` (6) |
| `Toy.ParMove.putLane_comm_of_disjoint` | 14 result | Classical.choice, Quot.sound, propext | `8aa14771dd0d0d63d711bee5c2bf89e97500be7a8b2b69e592bf69bc0fba2a1e` | `ef66f4fd3b4462524f8282290c36b0c20fb9625341869069fd3e2094d7d509e4` (7) |
| `Toy.ParMove.getLane_putLane_of_disjoint` | 14 result | Classical.choice, Quot.sound, propext | `8fb3ad3c3173baf05674a4021d703fe497cd9de2afd05b4957d6f17c8dfc7f96` | `299d658961ce911a72a5d71d1b02363e8c49ff5d315ad03f60858d8c7da8a711` (8) |
| `Toy.ParMove.putLane_overlapping_not_comm` | 14 counterexample | Quot.sound, propext | `421c7eb32c2750889c91d7a6bdf3360c5793b95039f0982f2f028e47fe5e468d` | `254ffc6dd3d819af80e8928275ae0cbb1a6a83c3366c1ab9850eb415d75ad099` (9) |
| `Toy.ParMove.getLane_putLane_needs_disjoint` | 14 counterexample | Quot.sound, propext | `081f20cec13ff8b6539fcde8e6aa08ee86ed4eeb292ad46fec12674de329ce56` | `d78b2cb61783165942c5ed372fe56700788f10b3005dc2620894d51b3a543eac` (10) |
| `Toy.ParMove.nonvacuity_putLane_comm` | 14 witness | (none) | `18847c9ef019ccf94e8b28841893b9699a163636f578d1bb717dd024e5948670` | `e2df019da30db3f13d363e706a51c44cc2434ccce829b621b398ac3bc7ce945b` (7) |
| `Toy.ParMove.putLane_comm_iff_disjointIn` | 15 result | Classical.choice, Quot.sound, propext | `0a54e909d78d12b9d2285adc0793114bfa0340277ac90f81c62a55fe1f4e4d0e` | `aa3d99012146988f298e8c85d1a05c1aaaa843b637903b89e475d334fe3c5b57` (7) |
| `Toy.ParMove.putLane_comm_iff_disjoint_of_fits` | 15 result | Classical.choice, Quot.sound, propext | `e6651c93f8a28125c415112320bac3102e9ef9071d3828aac2d3db5c11d06df3` | `639de20fd1593457b2ed5de08dd2ae7a3e4d65eec7f0f1d84d2faab58ce93d50` (8) |
| `Toy.ParMove.putLane_comm_iff_needs_fits` | 15 counterexample | Classical.choice, Quot.sound, propext | `1177dd5070c34b34263f0bf86c3a4b525a3743d7b55fd04b94ebbceaae631f32` | `639de20fd1593457b2ed5de08dd2ae7a3e4d65eec7f0f1d84d2faab58ce93d50` (8) |
| `Toy.ParMove.nonvacuity_putLane_comm_iff` | 15 witness | (none) | `cbdbb005ca73ba8cfb50e69d3709854deed12f100557a24414f88e70c1efa6f8` | `9c1c6716f91c50fddce65d2bd7dc556633aafbb679674081a574b4f121675fa6` (9) |
| `Toy.ParMove.nonvacuity_putLane_comm_iff_disjointIn` | 15 witness | (none) | `9ff788ff55144b32b42f024ba17dca1a848f38e76980c87aefabce9416e17a59` | `c2e95f4044cb94262c021e2eca3f1b92db50ec71a9f94d181aca9adae85b96fe` (8) |
| `Toy.ParMove.writeZext_not_getPut_of_lt` | 16 result | Classical.choice, Quot.sound, propext | `563287fe606d9565d5e8251c88ac4024aaa968e50c75be2507903e8e751f917d` | `14e1704d63ff3744643aa653f192babdda2e8c8d2cbdd8138568ee15afa6f5be` (2) |
| `Toy.ParMove.writeZext_not_getPut_needs_lt` | 16 counterexample | Quot.sound, propext | `f713f80b0cb03e0818511fbc46494f413b8ffb3682dd2ee2844dc2ee60e250eb` | `14e1704d63ff3744643aa653f192babdda2e8c8d2cbdd8138568ee15afa6f5be` (2) |
| `Toy.ParMove.nonvacuity_writeZext` | 16 witness; 18 witness | (none) | `b66960aa606bedcb4fe8d5bdaf1733eafbe17bd50392116c0dddb23bfdf2f37a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ParMove.writeZext_getPut_full` | 16 control | Quot.sound, propext | `2268cf269af3c89a38de39b0518ff70e3c5375d4d438bc60de26feaa4cb3303b` | `036c1d4e639361ddce52eeee8083a372a7cf1d7cdf11c032b28f06f9f9785772` (7) |
| `Toy.ParMove.writeZext_getPut_iff` | 17 result | Quot.sound, propext | `d0b5ca2f4cf3f7508dfde68cd1b292db7db229fa12b443fb9029aeecd19efc86` | `45b23884d80f610c92d73168a74bac36384655bbd168c666ce473e70c5642a6c` (6) |
| `Toy.ParMove.nonvacuity_writeZext_getPut_iff` | 17 witness | (none) | `22c4d01cb4c1f67f794208bfdd53fda6a161bd3380479d089389720c39c39930` | `45b23884d80f610c92d73168a74bac36384655bbd168c666ce473e70c5642a6c` (6) |
| `Toy.ParMove.writeZext_eq_putLane_full` | 18 result | Classical.choice, Quot.sound, propext | `aa28442d2043331ece55409b96e33d859726c0b37fce6a28834d44c65aed6311` | `cb7ff0e2c1631a062d1b9019a7cf399bd1405a0584b7b47e57f7d26c4cc357d5` (7) |
| `Toy.ParMove.putLane_full_veryWellBehaved` | 18 result | Classical.choice, Quot.sound, propext | `1cf51181af1fbb49bb586a8f85395b54aca4daacf6ca609a5f389d65304de928` | `97e4ce5bb0923a7659ee0c9f5966941a848bb5456a89b0530cb17dea657923b0` (11) |
| `Toy.ParMove.writeZext_putGet_of_le` | 18 result | Quot.sound, propext | `8c8e4dca3455d7618070b32b6353a0e4daccc3b8d80b5cbb082795b5bd680f20` | `86d91b2733225655593229a0e7f82069d8e0808bf4069f1b0df1b6a29a1b72eb` (7) |
| `Toy.ParMove.writeZext_putPut` | 18 result | (none) | `2809b4812abfd90b7cdd0c8ad94804c32afcdc9dc20163753fd6bbf64fe0a242` | `fbf17af5f187793bc95fa3410100213cd84518357f4796afae621e58c9dcc165` (7) |
| `Toy.ParMove.writeZext_putGet_needs_fit` | 18 counterexample | (none) | `3a773492e5c87685b0a54156bf4c4090c742d78ff8bae0fc637c91392162307c` | `86d91b2733225655593229a0e7f82069d8e0808bf4069f1b0df1b6a29a1b72eb` (7) |
| `Toy.ParMove.lanePMove_distinct_dst_lanes_not_enough` | 19 result | Quot.sound, propext | `ded3ebb2405da532009164c7024a263695b6e5286e7b78033f740044b65b858d` | `c72a1f8a2e6767111e2cb311a8373dafc2b9f6468d0883d5ae58b36488004b07` (24) |
| `Toy.ParMove.lanePMove_perm_invariant_of_laneWF` | 20 result | Classical.choice, Quot.sound, propext | `2c6d38098efdc79185b0fb41fc37823bec98570a38b15d59f5877217ac19c930` | `609cdef042d1facefbf79011a5595c0aca113641ab0fd4c29a4cccec91e5d4f5` (21) |
| `Toy.ParMove.lanePMove_perm_needs_laneWF` | 20 counterexample | Quot.sound, propext | `6c61312201378aeee78c3fe174c442aec0a9347ad57f305dba7e59842ab0626f` | `e10fbdedda16655b0b53e7e3f7ea277266dc73706d0e8f2a2764e5094ee289f8` (23) |
| `Toy.ParMove.lanePMove_perm_needs_perm` | 20 counterexample | Quot.sound, propext | `4d5eaa1900073e6b4c281af7fef0f85466003d5b77cab1fed4201081e1b3cf2e` | `e10fbdedda16655b0b53e7e3f7ea277266dc73706d0e8f2a2764e5094ee289f8` (23) |
| `Toy.ParMove.nonvacuity_lanePMove_perm` | 20 witness | (none) | `f8f11e0e6f32fae0d41687c918fc8fbe9263f526ba03400bc29b79658aef0253` | `4250be32587631494c87f2c7ae74c81ebc64e7dbdcd8eb5a2d4424d5ddb6f5df` (13) |
| `Toy.ParMove.runLanes_eq_lanePMove_of_laneWF_of_topological` | 21 result | Classical.choice, Quot.sound, propext | `198594db10f170f07427c947e5169fbc099d5d925b3cc0917c494a0e4590600e` | `b5fc826857125ce7b4465945e861cd4d5542dded69b1530ada3e87a5e2e91091` (24) |
| `Toy.ParMove.runLanes_needs_laneWF` | 21 counterexample | Quot.sound, propext | `6724f3d3d1bbe6bc94b163846994f53de37aa1168223155870f475df04592ef9` | `c3fedac104aee2759ec98321bd05b6b03fb74e056f7c33f8561884c8b84c2e80` (26) |
| `Toy.ParMove.runLanes_needs_perm` | 21 counterexample | Quot.sound, propext | `c54eb34b4a91d34a4ba82969ad6bc400e0286b2077e2a9f8709faa69b1f8a360` | `c3fedac104aee2759ec98321bd05b6b03fb74e056f7c33f8561884c8b84c2e80` (26) |
| `Toy.ParMove.runLanes_needs_topological` | 21 counterexample | Quot.sound, propext | `40c196fe2769c82983b3df0fe7c23222baef66eb50495d57b775512ffb4811cb` | `c3fedac104aee2759ec98321bd05b6b03fb74e056f7c33f8561884c8b84c2e80` (26) |
| `Toy.ParMove.nonvacuity_runLanes_same_register` | 21 witness | (none) | `7f18c13324f5389725adf311749ef660f1fc1f38efd24cfbaab99b4fdeaf6bc2` | `d1af8e6732f4470a461ad44c870efcf1b9050fdd8851306fa78f43045ef5b6c6` (17) |
| `Toy.ParMove.nonvacuity_runLanes` | 21 witness | (none) | `fe0c9ce881af4d207a17fad7cbb11dc251766a3553f2248edd84003ab347a94b` | `d1af8e6732f4470a461ad44c870efcf1b9050fdd8851306fa78f43045ef5b6c6` (17) |

129 names are hashed.

Supporting theorems (no recorded hash; quoted under **Findings → Supporting theorems cited in the text**):

- `Toy.ParMove.functional_of_wellFormed`: axioms Quot.sound, propext.
- `Toy.ParMove.runSeq_comp`: axioms Quot.sound.
- `Toy.ParMove.pmove_comp`: axioms Quot.sound.
- `Toy.ParMove.runSeq_eq_pmove_of_id`: axioms Quot.sound.
- `Toy.ParMove.runSeq_eq_pmove_at_id_of_forall`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.functional_duplicate_not_wellFormed`: axioms propext.
- `Toy.ParMove.pmove_eq_pmoveLast_of_wellFormed`: axioms Quot.sound, propext.
- `Toy.ParMove.pmove_readings_agree_on_equal_source_values`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.sequentialize_emits_duplicates_example`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.sequentialize_loses_tmp_destination`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.sequentialize_clobbers_tmp`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.sequentialize_works_with_tmp_self_move`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.topological_rejects_benign_self_move`: axioms Quot.sound, propext.
- `Toy.ParMove.not_topological_of_dsts_read`: axioms propext.
- `Toy.ParMove.runSeq_eq_pmoveLast_of_topological`: axioms Quot.sound, propext.
- `Toy.ParMove.not_topological_of_perm_cycleMoves`: axioms Quot.sound, propext.
- `Toy.ParMove.no_injective_store_nat_bool`: axioms propext.
- `Toy.ParMove.sequentialize_cycle_length_examples`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.runSwaps_comp`: axioms Quot.sound.
- `Toy.ParMove.length_cycleSwaps_nil`: axioms (none).
- `Toy.ParMove.xorSwap_unsafe_for_aliased_parallel_swap`: axioms Quot.sound, propext.
- `Toy.ParMove.xorSwap_eq_swapStore_width_zero`: axioms Quot.sound, propext.
- `Toy.ParMove.Lane.disjoint_iff_bits`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.getLsbD_putLane`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.writeZext_getPut_of_ge`: axioms Quot.sound, propext.
- `Toy.ParMove.writeZext_upper_zero`: axioms Quot.sound, propext.
- `Toy.ParMove.writeZext_truncates_example`: axioms (none).
- `Toy.ParMove.runLanes_eq_lanePMove_of_topological`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.laneWF_implies_distinctDstLanes_of_pos_wid`: axioms Quot.sound, propext.
- `Toy.ParMove.laneWF_not_implies_distinctDstLanes_width_zero`: axioms (none).
- `Toy.ParMove.lanePMove_perm_invariant_duplicate_not_laneWF`: axioms Quot.sound, propext.
- `Toy.ParMove.lanePMove_same_source_overlap_not_laneWF`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.lanePMove_beyond_register_overlap_not_laneWF`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.laneTopological_rejects_benign_self_copy`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.not_topological_of_contains_cycleMoves`: axioms Quot.sound, propext.
- `Toy.ParMove.cycle_length_sub_one_le_of_injOn_of_runSwaps`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.nonvacuity_cycle_length_sub_one_le_of_injOn_of_runSwaps`: axioms Quot.sound, propext.
- `Toy.ParMove.putLane_putGet_iff_wid_zero_or_fits`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.putLane_putGet_width_zero_beyond_register`: axioms Classical.choice, Quot.sound, propext.

Definition examples and lemmas quoted under **Findings → Definitions** (no recorded hash; examples that are also card witnesses are in the table above):

- `Toy.ParMove.pmove_swap_example`: axioms (none).
- `Toy.ParMove.pmove_rejects_sequential_reading`: axioms (none).
- `Toy.ParMove.wellFormed_swap_example`: axioms (none).
- `Toy.ParMove.not_wellFormed_repeated_destination`: axioms (none).
- `Toy.ParMove.not_functional_two_sources`: axioms Quot.sound, propext.
- `Toy.ParMove.runSeq_swap_via_scratch_example`: axioms (none).
- `Toy.ParMove.runSeq_naive_swap_fails`: axioms (none).
- `Toy.ParMove.isReady_example`: axioms propext.
- `Toy.ParMove.not_isReady_example`: axioms propext.
- `Toy.ParMove.sequentialize_swap_example`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.sequentialize_chain_example`: axioms Classical.choice, Quot.sound, propext.
- `Toy.ParMove.topological_example`: axioms (none).
- `Toy.ParMove.not_topological_example`: axioms (none).
- `Toy.ParMove.cycleMoves_example`: axioms (none).
- `Toy.ParMove.cycleMoves_repeated_not_cycle`: axioms (none).
- `Toy.ParMove.cycleSeqScratch_example`: axioms (none).
- `Toy.ParMove.swapStore_example`: axioms (none).
- `Toy.ParMove.cycleSwaps_example`: axioms (none).
- `Toy.ParMove.runSwaps_order_matters`: axioms (none).
- `Toy.ParMove.xorSwap_examples`: axioms Quot.sound, propext.
- `Toy.ParMove.xorSwap_alias_example`: axioms Quot.sound, propext.
- `Toy.ParMove.veryWellBehaved_fst`: axioms (none).
- `Toy.ParMove.not_putGet_constant_put`: axioms (none).
- `Toy.ParMove.not_veryWellBehaved_constant_put`: axioms (none).
- `Toy.ParMove.putLane_low8_example`: axioms Quot.sound, propext.
- `Toy.ParMove.putLane_high8_example`: axioms Quot.sound, propext.
- `Toy.ParMove.putLane_low32_not_zext`: axioms Quot.sound, propext.
- `Toy.ParMove.writeZext_example`: axioms (none).
- `Toy.ParMove.writeZext_not_preserve_upper`: axioms (none).
- `Toy.ParMove.getLane_examples`: axioms propext.
- `Toy.ParMove.disjoint_examples`: axioms (none).
- `Toy.ParMove.disjointIn_examples`: axioms (none).
- `Toy.ParMove.fits_examples`: axioms (none).
- `Toy.ParMove.lanePMove_byte_swap_example`: axioms Quot.sound, propext.
- `Toy.ParMove.runLanes_byte_swap_naive`: axioms Quot.sound, propext.
- `Toy.ParMove.laneWF_examples`: axioms (none).
- `Toy.ParMove.distinctDstLanes_examples`: axioms (none).
- `Toy.ParMove.laneTopological_examples`: axioms (none).

### Primary sources

Exact records as cited on the cards (prior art of the results and targets of the modeling bridges). Moves are written source first in CompCert, Rideau–Serpette–Leroy and Boissinot et al., and destination first in CakeML and in this package.

- Rideau, Serpette, Leroy. "Tilting at Windmills with Coq: Formal Verification of a Compilation Algorithm for Parallel Moves." Journal of Automated Reasoning 40(4):307-326, 2008, DOI 10.1007/s10817-007-9096-8 (bibliographic record from dblp; content from the authors' preprint at xavierleroy.org/publi/parallel-move.pdf). Moves are written (s ↦ d), source first. Section 2 requires pairwise-distinct destinations ('windmills': 'If a register appeared twice as a destination, its final value after the parallel move would not be uniquely defined'). Section 3 serializes a simple n-cycle with one temporary in n + 1 moves and credits C. May with the general algorithm (remove moves with no successor, then break the remaining disjoint cycles with one temporary); the Coq development verifies a different, stack-based algorithm. Section 9 notes that these algorithms are not optimal in move count: (r3, r2, r1) := (r1, r1, r2) is realizable in 3 moves, r3 := r1; r1 := r2; r2 := r3, using the destination r3 to break the cycle.
- CompCert, file lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861 (github.com/AbsInt/CompCert; file contents at that commit). exec_par gives the parallel semantics; parmove_correctness assumes is_mill (no destination appears twice) and move_no_temp (no temporary occurs as a source or a destination). Moves there are written (source, destination), the reverse of this package's (destination, source).
- Boissinot, Darte, Rastello, Dupont de Dinechin, Guillon. "Revisiting Out-of-SSA Translation for Correctness, Code Quality and Efficiency." CGO 2009, pp. 114-125, DOI 10.1109/CGO.2009.19 (bibliographic record from dblp). Text quoted from the research-report version, HAL inria-00349925v3 (titled '... Code Quality, and Efficiency'), Section III-C 'Sequentialization of parallel copies'. Copies are written a ↦ b (source, destination), the reverse of this package's (destination, source). Section III-C credits C. May (1989) with a similar algorithm and gives Algorithm 1, a ready-list/to-do-list algorithm with 'one extra fresh variable', which generates 'the same number of copies as expressed by the parallel copy, except possibly one additional copy for each circuit with no tree edge'. It also states that each variable has a unique incoming copy: 'a parallel copy (b ↦ a, c ↦ a) is possible but only if V(b) = V(c) in which case one of the copies can be removed', where V(x) is the SSA value of x (Section III-A). That condition is semantic (two possibly different source variables known to hold the same value; the closest notion here is FunctionalAt, a condition at one store), not the syntactic condition Functional (identical source locations).
- CakeML, file compiler/backend/reg_alloc/parmoveScript.sml at commit 4777c4b7c0aa4661994e29f97b9501c3f0b7d602 (github.com/CakeML/cakeml): a HOL4 formalisation of the Rideau-Serpette-Leroy algorithm, with moves written (destination, source) as in this package. Theorem parsem_perm: 'windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2' (order independence for distinct destinations, the WellFormed special case of Functional here); parmove_correct states correctness of the compiled move sequence for windmills.
- May. "The Parallel Assignment Problem Redefined." IEEE Transactions on Software Engineering 15(6):821-824, 1989, DOI 10.1109/32.24735 (bibliographic record from dblp). Cited through the descriptions in Rideau-Serpette-Leroy Section 3 and Boissinot et al. Section III-C, which credit it with the strategy that sequentialize follows: emit moves whose destination is no longer read, then break each remaining cycle with one temporary.
- Briggs, Cooper, Harvey, Simpson. "Practical Improvements to the Construction and Destruction of Static Single Assignment Form." Software: Practice and Experience 28(8):859-881, 1998 (bibliographic record from dblp). Cited, as described in Boissinot et al. Section II, for identifying the 'lost copy problem' and the 'swap problem' that parallel copies cause in out-of-SSA translation.
- Sethi. "A Note on Implementing Parallel Assignment Instructions." Information Processing Letters 2(4):91-95, 1973, DOI 10.1016/0020-0190(73)90024-0; Welch. "Parallel Assignment Revisited." Software: Practice and Experience 13(12):1175-1180, 1983, DOI 10.1002/spe.4380131208 (bibliographic records from dblp). Background, cited through Rideau-Serpette-Leroy Section 1: Sethi shows that compiling general parallel assignments with a constant number of temporaries is NP-hard; Welch outlines the trivial scheme with n temporaries.
- Sreedhar, Ju, Gillies, Santhanam. "Translating Out of Static Single Assignment Form." SAS 1999, LNCS 1694, pp. 194-210, DOI 10.1007/3-540-48294-6_13 (bibliographic record from dblp). Background only: out-of-SSA translation by copy insertion; its content is not relied on.
- Standard fact about permutations: a k-cycle is a product of k - 1 transpositions and of no fewer. No single reference is relied on; the package proves both directions for its swap model. Boissinot et al. Section II (HAL inria-00349925v3) mention that a swap needs an extra copy 'unless an instruction can perform a swap', which is the setting of this result.
- Warren. Hacker's Delight, 2nd edition (Addison-Wesley, 2012, ISBN 978-0-321-84268-8), Section 2-20 'Exchanging Registers' (publisher's online excerpt at InformIT): 'A very old trick is exchanging the contents of two registers without using a third' (the three exclusive-or sequence). The section does not discuss aliased operands; it also covers exchanging two fields of the same register with masks.
- Foster, Greenwald, Moore, Pierce, Schmitt. "Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem." ACM TOPLAS 29(3), article 17, 2007, DOI 10.1145/1232420.1232424 (bibliographic record from dblp; content from the authors' final version). Section 3 'Semantic Foundations' defines the laws GetPut, PutGet and the optional PutPut, and calls a well-behaved lens that also satisfies PutPut 'very well behaved'. The package defines these laws itself for total functions.
- Foster, Pardillo-Laursen, Zeyda. "Optics." Archive of Formal Proofs, May 25, 2017 (isa-afp.org/entries/Optics.html). Its abstract describes an Isabelle/HOL mechanisation of an algebraic hierarchy of lenses, including well-behaved and very well-behaved lenses, with a library of algebraic laws. General lens theory; it is not instantiated to bit lanes of machine words here.
- Intel 64 and IA-32 Architectures Software Developer's Manual, Volume 1: Basic Architecture, Order Number 253665-060US (September 2016), Section 3.4.1.1 'General-Purpose Registers in 64-Bit Mode', p. 3-12. Evidence scope: only the section number, title and page were confirmed at the primary source (the table of contents of that PDF); the section body was not retrieved, so no sentence of it is quoted. The behaviour relied on is paraphrased: in 64-bit mode a 32-bit-operand write zero-extends its result into the 64-bit register, and 8-bit and 16-bit writes leave the other bits of the register unchanged. Role: normative source, paraphrased. Modeling bridge only.
- Arm, 'Learn the architecture - A64 Instruction Set Architecture Guide' (document 102374, version 1.4), page 'Registers in AArch64 - general-purpose registers': 'When a W register is written, as seen in the example above, the top 32 bits of the 64-bit register are zeroed.' Role: documentation (the normative Arm Architecture Reference Manual is not cited). Modeling bridge only.
- CompCert lib/Parmov.v at commit 4710ec093ddea8e6eb86ad519df61c59b654e861, section 'Extension to partially overlapping registers' (also Rideau-Serpette-Leroy Section 8): parmove2_correctness_with_overlap (lines 1588-1596) assumes, for a source list sl and a destination list dl: equal lengths; every source and every destination disjoint from every temporary (disjoint_temps); pairwise-disjoint destinations (pairwise_disjoint dl); no partial overlap between any source and any destination; and no partial overlap among temporaries (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2). Here no_overlap r1 r2 means that r1 and r2 are equal or disjoint. A write sets its target and leaves the other registers that are not disjoint from the target undefined (weak_update). Different model from this package's exact bit-lane writes. The statement at that commit
(`lib/Parmov.v` lines 1588-1599) and the two definitions its hypotheses use (lines 1377-1378 and
1417-1418), verbatim:

```coq
Definition no_overlap (r1 r2: reg) : Prop :=
  r1 = r2 \/ disjoint r1 r2.

Definition disjoint_temps (r: reg) : Prop :=
  forall t, is_temp t -> disjoint r t.

Theorem parmove2_correctness_with_overlap:
  forall sl dl,
  List.length sl = List.length dl ->
  (forall r, In r sl -> disjoint_temps r) ->
  (forall r, In r dl -> disjoint_temps r) ->
  pairwise_disjoint dl ->
  (forall s d, In s sl -> In d dl -> no_overlap s d) ->
  (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2) ->
  forall e,
  let e' := weak_exec_seq (parmove2 sl dl) e in
  List.map e' dl = List.map e sl /\
  forall r, disjoint_list r dl -> disjoint_temps r -> e' r = e r.
```

Re-checked on 2026-11-20: the bibliographic records of the DOIs 10.1007/s10817-007-9096-8 (Journal of Automated Reasoning 40(4):307-326), 10.1109/CGO.2009.19 (CGO 2009, pp. 114-125), 10.1145/1232420.1232424 (ACM TOPLAS 29(3), article 17) and 10.1109/32.24735 (IEEE TSE 15(6):821-824) via Crossref; the commits `4710ec093ddea8e6eb86ad519df61c59b654e861` of `AbsInt/CompCert` and `4777c4b7c0aa4661994e29f97b9501c3f0b7d602` of `CakeML/cakeml` via the GitHub API; in `lib/Parmov.v` at that commit, `exec_par`, `is_mill`, `move_no_temp`, `parmove_correctness`, the section 'Extension to partially overlapping registers', `weak_update` and `parmove2_correctness_with_overlap`; in `parmoveScript.sml` at that commit, `parsem_perm` ('windmill l1 ∧ PERM l1 l2 ⇒ parsem l1 = parsem l2') and `parmove_correct`; the quoted sentence of the Arm guide 102374 v1.4 page; and the entry page and abstract of the Archive of Formal Proofs entry 'Optics' (May 25, 2017). The quoted passages of the Rideau–Serpette–Leroy preprint, the Boissinot et al. research report (HAL inria-00349925v3), the Foster et al. final version and the Hacker's Delight excerpt were read in the cited versions and not re-retrieved on that date. The Intel manual is cited by order number, section number, title and page only (its table of contents); its section body was not retrieved and no sentence of it is quoted. Sources cited 'through' another source (May 1989, Briggs et al. 1998, Sethi 1973, Welch 1983) are cited for what the citing source says about them; their own text is not relied on.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; the Lean project has no dependencies.

**Primary check (one command).** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`,
rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom` declaration,
and then elaborates an inline audit program that (1) computes, with Lean's `collectAxioms`, the
axioms of every declaration of the `ToyParMove` library and fails if any uses an axiom other than
`propext`, `Classical.choice`, `Quot.sound`; and (2) for every Lean name referenced by
`results.json` (fields `lean`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis
`counterexample`s) and every name recorded in `audit/statements.json`, recomputes two SHA-256
hashes and compares them with `audit/statements.json`:

- the **statement hash**: SHA-256 of `toString (repr ci.type)`, the Lean `repr` of the
  declaration's elaborated type;
- the **closure hash**: SHA-256 of the newline-joined, sorted list of entries `name : repr(type)`
  (plus ` := repr(value)` for non-theorems) for every constant of the `ToyParMove` library
  reachable from the statement's type through types, definition bodies and inductive constructors
  (theorem bodies excluded). A change to any definition a statement depends on therefore changes
  its closure hash.

It prints `REVALIDATED` and exits with status 0 iff every check passes. Expected output ends with
`ok   axioms (486 declarations)`, `ok   statement hashes (129 hashed names; 0 referenced
names exist but carry no recorded hash)` and `REVALIDATED`.

**Manual equivalent.**

```sh
cd lean
lake build                              # builds library ToyParMove; must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every name cited in REPORT.md
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`). It
imports `ToyParMove` and issues `#print axioms` for every declaration of the library (theorem,
definition or structure) cited anywhere in `REPORT.md` or `results.json`, including the
definition examples, the structures `Lane` and `LaneMove`, and the supporting theorems that carry
no recorded hash; elaboration fails if any name is missing, and each
printed line must list only (a subset of) `propext`, `Classical.choice`, `Quot.sound`. The recorded
per-declaration axioms are in `audit/axioms.json`. To recompute one statement hash by hand, run the
audit program embedded in `support/revalidate.py` (the string `AUDIT`) with the name of interest
and hash the printed `type_repr` and `closure` fields as described above.

**Cheaper discriminating checks.** If only the Lean toolchain changes, re-running the primary check
is sufficient: a changed elaboration of any statement or definition shows up as a hash mismatch
even when the build succeeds. If a definition in `lean/ToyParMove/` is edited, every card whose
closure includes it is stale; the closure hashes identify which. A passing revalidation establishes
only the kernel-checked statements; it does not re-check any modeling-bridge claim or citation,
which must be re-read against the sources listed under **Evidence** (for the architecture claims:
the Intel manual's Section 3.4.1.1 and the Arm guide 102374 page, or the normative Arm
Architecture Reference Manual).
