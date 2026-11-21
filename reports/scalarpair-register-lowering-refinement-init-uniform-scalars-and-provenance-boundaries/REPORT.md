# Scalar and scalar-pair register lowering: refinement, initialization uniformity and provenance boundaries

## Summary

This package mechanizes, in Lean 4 with no dependencies (no Mathlib), a toy model of
representation lowering. A byte-level value, a list of MiniRust-style abstract bytes (`uninit`,
plain `bits b`, or a pointer fragment `ptrFrag b prov i`), is replaced by one scalar register,
by two scalar registers at fixed offsets (a scalar pair), or kept as a memory blob, and is then
raised back to bytes. The 21 results characterize when this round trip refines the byte-level
value (uniform initialization, ranges, provenance coherence, bytes outside the scalars'
extents), relate register-level reinterpretation to a transmute through memory (exact agreement
versus one-sided refinement), and mark boundaries for unions (whole-value validity, niches,
partial writes, `noundef`).

Model–system relation: none proved. These are statements about a toy model of representation
lowering; they neither establish nor refute the corresponding claims about rustc's `BackendRepr`
lowering, its LLVM backend, Miri, or MiniRust. Every connection to those systems is a separate
`derived (modeling bridge)` claim under **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

"Refines" below means: for every value `x` in the set considered, `BytesLe x (raise …)`, i.e.
the raised bytes are at least as defined as the original, byte by byte (MiniRust's definedness
order). The results, one sentence each:

- **R1.** For every set `V` of byte-level values, each of length exactly `n`, and one scalar `s`
  of any width, the round trip `raise ∘ lower` through `Scalar s` refines the identity on every
  value of `V` iff (a) every byte below `n` outside the scalar's extent is `uninit`, (b) an
  `initialized` scalar's bytes are all initialized or all uninitialized, (d) initialized,
  non-empty bytes of an `initialized` scalar lie in its range, and (c) bytes of an `initialized`
  scalar that are not all uninitialized are provenance coherent, each in every value of `V`.
- **R2.** The same four conditions, for both scalars, characterize the round trip through a
  `ScalarPair a b bOff` (`a` at offset `0`, `b` at offset `bOff`) with disjoint extents
  (`a.size ≤ bOff`), for every set `V` of values each of length exactly `n`.
- **R3.** If `y` is at least as defined as `x` byte by byte (`BytesLe x y`), every typed integer
  and pointer read of `y`, at every offset and width, is at least as defined as that of `x`.
- **R4 / R4b.** For a `union` scalar of any width and every set `V` of values each of length
  exactly `n`, the round trip refines iff every byte below `n` outside the scalar's extent is
  `uninit` in every value of `V`; if the scalar's width is at least `n`, it always refines.
- **R5.** For every primitive `p` of width at least `1` and every range `rng`, the value
  `ptrFrag 0 0 1 :: replicate (p.size - 1) uninit` (truncated subtraction; a value of length
  exactly `p.size`) round-trips through `Scalar (union p)` and does not round-trip through
  `Scalar (initialized p rng)`.
- **R6.** For every size `n` and every set `V`, coarsening to `memory` refines.
- **R7.** For scalars `s`, `t` of equal width `w` with `1 ≤ w ≤ n`, the register-level
  reinterpretation and the byte-level transmute through memory give equal raised bytes on the
  `s`-lowered form of every value of length exactly `n` iff `t` is `union`, or both are
  `initialized` and `s`'s range is included in `t`'s on data of length exactly `w`.
- **R7b.** For every `n` and all scalars `s`, `t` (of any widths, equal or not, including widths
  greater than `n`; with any disciplines and ranges), the register-level reinterpretation is at
  least as defined (`BytesLe`) as the memory transmute on the `s`-lowered form of every value of
  length exactly `n`: discipline compatibility governs exact agreement (R7), not this one-sided
  order.
- **R8.** For pairs at the same `b` offset, with equal component widths, disjoint extents,
  `bOff + b.size ≤ n` and compatible disciplines for both components, componentwise
  reinterpretation and the memory transmute give equal raised bytes, both starting from the
  `(a, b)`-lowered form of every value of length exactly `n`.
- **R9.** Concatenating a padded `ScalarPair` (1-byte scalars at offsets `0` and `2`) into one
  2-byte `union` register disagrees with the memory transmute on the pair-lowered form of the
  3-byte value `[bits 1, uninit, bits 2]`; without padding (`b` at offset exactly `a.size`), into a
  `union` scalar of width exactly `a.size + b.size` with `a.size + b.size ≤ n`, the two paths give
  equal raised bytes, both starting from the `(a, b)`-lowered form of every value of length
  exactly `n`.
- **R10.** A cast that attaches provenance `7` to the 1-byte integer `5` gives `ptrFrag 5 7 0`,
  while the memory transmute and the register reinterpretation to a 1-byte pointer scalar both
  give `bits 5`.
- **R11.** Under trivial whole-value union validity, for every toy union `u`, every field
  descriptor `f` (not necessarily a field of `u`) and every byte list `x`, the union move is
  defined iff `x` has the union's size, and reading `f` is UB iff `f`'s validity predicate
  rejects `f`'s (truncated) bytes.
- **R12.** In `{ a: NonZeroU8, b: u8 }`, after writing `b = 0` over `a = 5`, reading `b` and the
  union move (trivial whole-value validity) are defined, while a move that inherited `a`'s niche
  is UB.
- **R13 / R13b.** For every whole-value validity policy, union and gate that fires on the union,
  the `Unreachable` rewrite of a move-then-return program refines it on every value of the
  union's size iff the policy rejects every such value; consequently, under trivial whole-value
  validity, every gate that fires on all field-wise uninhabited unions fails to refine on
  `neverUnion`.
- **R14 / R14b.** Partial writes are framed: for every byte list, offset and source, written
  positions inside the value take the source bytes, every other position keeps its old byte, and
  source bytes past the end of the value are dropped; byte `j` of a `k`-byte read after the write,
  at a position inside both the read (`j < k`) and the value (`o' + j < x.length`), is the
  written byte if that position was written and the old byte otherwise.
- **R15.** For a `union` register of width at least `n` and a value of length exactly `n`, the
  lane-wise blend of a partial write into the register, raised, equals the memory write.
- **R16.** For every constant fill byte, there is a two-byte value `x` such that the two-byte
  integer read after writing `bits 1` at offset `0` is defined, and the same read after the
  whole-register write of width exactly `2` with that fill in the untouched lane is not at least
  as defined (`¬ OutLe`) as it. `OutLe` is a partial order, so "not at least as defined" is not
  "less defined" (see R16's non-claims).
- **R17.** For every primitive `p` of width at least `1`, the all-`uninit` value of length exactly
  `p.size`, lowered to a `union` register, is passed without UB without `noundef` and is UB with
  `noundef`.

Read the non-claims before relying on a result: the non-claims shared by all results and those
of each result are listed first under **Boundaries**, followed by the escape hatches of the
impossibility results (R5, R13b, R16, R17) and the stronger conclusions that are not
established.

## Applicability

**What the results are about.** Every result is a theorem about the Lean definitions in
`lean/ToyReprLower/` (namespace `Toy.ReprLower`), quoted verbatim under **Findings →
Definitions**. The definitions form a toy model of representation lowering: a byte-level value
(a list of abstract bytes `AByte`) is replaced by one scalar register, two scalar registers at
offsets `0` and `bOff`, or kept as a memory blob (the constructors `scalar`, `pair` and `memory`
of `BRepr`), and raised back to bytes. A scalar is `initialized p range` (a primitive with a
range predicate) or `union p`. The criterion for a correct lowering is MiniRust's definedness
order on byte lists (`BytesLe`); typed integer and pointer reads are monotone in it (R3).

Model–system relation: none proved. These are statements about the toy model; they neither
establish nor refute the corresponding claims about rustc's `BackendRepr` lowering, its LLVM
backend, Miri, or MiniRust. The modeling-bridge paragraphs (labelled `derived (modeling bridge)`)
argue the connection to documented design separately.

**What the definitions are meant to capture (derived (modeling bridge)).** `Scalar` is meant to
capture rustc's `rustc_abi::Scalar::{Initialized, Union}`; `BRepr`'s `pair a b bOff` is meant to
capture `BackendRepr::ScalarPair`, with `a` at offset zero and `b` at `b_offset` in memory order;
`AByte` and `AByte.leb` follow MiniRust's `AbstractByte` and its `le_defined` order; pointer
lowering (`ptrLower`) follows MiniRust's `decode_ptr`; the toy argument-passing step `passArg`
with the `noundef` flag set follows the `noundef` sentence of the LLVM Language Reference, and the
`poison`-on-out-of-range lowering of `initialized` scalars follows its `range` sentence. The
quoted documentation and the reasoning are under **Findings → Modeling bridge to documented
designs**; none of these correspondences is kernel-checked.

**Modelling choices that carry weight**, stated once:

1. An `initialized` scalar whose bytes are partially or wholly uninitialized, or out of range,
   lowers to `poison`; `poison` raises to `uninit` bytes (the toy byte domain, MiniRust's, has no
   poison byte). In particular an all-`uninit` value round-trips through an `initialized` scalar
   (R1's condition (b) is all-or-nothing), although its register is `poison`
   (`initialized_allUninit_roundTrips_but_noundef_ub`).
2. An integer scalar drops provenance. A pointer scalar lowers its (initialized) bytes as
   MiniRust's `decode_ptr` does (`ptrLower`): one pointer's fragments in order give a pointer
   with that provenance; any other initialized bytes give a provenance-free pointer that keeps
   the address bytes.
3. A `union` register holds abstract bytes exactly, provenance fragments and `uninit` bytes
   included (`provenanceStripping_register_not_refines` shows what changes without this).
4. Ranges are arbitrary Boolean predicates on the data bytes, more general than wrapping
   intervals; some tightness witnesses use the length-dependent range `len2Range`.
5. Byte data is an unbounded `Nat`; no result uses byte arithmetic, so 8-bit wrapping does not
   arise.
6. `seg` truncates at the end of a byte list and `place` truncates at `n`; no lowering result
   assumes that a scalar's extent lies inside the value.

**Known gaps between the toy and real systems.** No calling conventions, vectors, floats or
alignment are modelled, and no evaluation order of the two scalars of a pair. The register-level
reinterpretation `regCast` makes no initialization, range or provenance assertion, and
downstream uses of a register that assume `noundef` or a range are not modelled. Whole-value
union validity is a parameter (`UnionValidity`); the toy union preserves every byte, whereas
MiniRust encodes a union value from its chunks and resets every other byte to `Uninit`, and
real unions may have padding. Whether a real backend's integer registers can carry provenance is
not examined (R4, R4b and R15 depend on union registers holding fragments). rustc's single
`Scalar::Initialized` layouts have no trailing padding (the scalar's size equals the layout
size), so condition (a) of R1 concerns the toy's general representations and arises in practice
for scalar pairs and padded values. LLVM's `range` attribute applies to integer and
integer-vector types; the toy also attaches ranges to pointer scalars, as rustc's
`Scalar::Initialized` does with `valid_range`. No context language is modelled: the refinement
criterion is the byte order, not contextual equivalence.

**Degenerate edges.** Widths are arbitrary natural numbers, including `0`; sizes `n = 0` and
empty sets `V` are allowed. `seg x off w` is `(x.drop off).take w`, truncated at the end of `x`;
`place` truncates at `n`. `p.size - 1` in R5 is truncated (natural-number) subtraction, which
does not truncate under R5's guard `1 ≤ p.size`. Per-card degenerate edges are listed on the
cards.

**Lean version and dependencies.** Every theorem was elaborated and kernel-checked with the Lean
4 toolchain `leanprover/lean4` `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`),
using core Lean with no Mathlib and no other dependencies. Behaviour under other Lean versions was
not examined.

**Subjects and how they relate.** The Lean toolchain is the checker of every theorem. The
following pinned revisions are the documented designs that the toy definitions are meant to
capture; they are quoted, with line ranges, in modeling-bridge prose and were not executed or
measured: `rust-lang/rust` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (`rustc_abi` scalar and
backend-representation documentation, the const-eval interpreter's `Immediate`),
`minirust/minirust` at `063d784186d3252bee242217f218223205c0b568` (abstract bytes, pointer
decoding, unions, definedness order), `llvm/llvm-project` at
`a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6` (`llvm/docs/LangRef.md`, the `noundef` and `range`
attributes) and `rust-lang/reference` at `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c` (union
validity). Other revisions of these projects were not examined. CompCert at
`2685140bf72c959446981fb99b5e44a8975021bc` and the papers listed in `REPORT.json` are prior art
that the cards cite; the report does not re-verify their results.

Results already covered by other packages of this corpus are cited, not repeated: the
abstract-byte laws (`byte-representation-galois-laws-and-transmute-composition`,
`byte-level-separation-logic-typed-points-to-and-transmute-view-changes`), integer-to-pointer
casts and exposure (`pointer-provenance-models-and-integer-pointer-cast-optimizations`), validity
inclusion and union validity (`transmutation-soundness-bit-validity-and-reference-variance`,
`zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`), poison and undef
(`undefined-values-poison-undef-freeze-and-refinement`), and niches and valid ranges
(`enum-niche-layout-guarantees-and-validity-invariants`). No result of this package depends on
them.

## Findings

**Evidence roles.** Each result below is a set of Lean theorems checked by the Lean kernel under
the toolchain named in **Applicability**; this is recorded as
`Basis: execution (Lean kernel check)`. Any statement connecting a result or a definition to
rustc, Miri, MiniRust, LLVM or the Rust Reference is a separate claim recorded as
`Basis: derived (modeling bridge)`, with its reasoning (collected under "Modeling bridge to
documented designs" at the end of this section); it is not kernel-checked and holds only to the
extent that the toy definitions capture the documented designs (see the gaps listed under
**Applicability**). "Proved" in this report never means "true of rustc, LLVM, Miri or
MiniRust".

**How to read a card.** *Tier* is `T0` (a known result restated for the toy) or `T1` (folklore
made precise); no result is claimed novel. Every Lean statement is quoted verbatim from the
source, labelled with its `file:line` range. "Refines" means `BytesLe x (raise …)` for every `x`
in `V`: the raised bytes are at least as defined as the original, byte by byte (MiniRust's
order; UB is the top of the refinement order). `typedReads_mono_of_bytesLe` (R3) connects this
order to typed reads. The *hypothesis ledger* lists every hypothesis with its purpose and
tightness; a tightness witness (`tight`) is a proved theorem in which a concrete instance
satisfies every other hypothesis of the named result (or of the named direction) and the
conclusion fails, and the witness-class column says which kind of instance it is. *Depth* is
`definitional`, `shallow` or `substantive`. The *non-vacuity witness* is a proved instance
satisfying all hypotheses. For impossibility results, *positive controls* are proved nearby
settings where the conclusion fails. Each card's non-claims (and, for impossibility results, its
escape hatches) are listed under **Boundaries**. Each card states its model–system relation; for
every card it is: none proved.

### Definitions

#### Abstract bytes and the definedness order

`AByte` has the shape of MiniRust's `AbstractByte`: `uninit`, `bits b` (= `Init(b, None)`) and
`ptrFrag b prov i` (= `Init(b, Some(ProvenanceFrag { provenance: prov, position: i }))`).

```lean
-- lean/ToyReprLower/Basic.lean:27-31
inductive AByte where
  | uninit
  | bits (b : Nat)
  | ptrFrag (b : Nat) (prov : Nat) (i : Nat)
  deriving DecidableEq, Repr
```

`AByte.leb` is MiniRust's `le_defined` on abstract bytes (`uninit` is below everything; adding
provenance makes a byte more defined; a fragment is below itself and nothing else):

```lean
-- lean/ToyReprLower/Basic.lean:38-43
def leb : AByte → AByte → Bool
  | uninit, _ => true
  | bits b, bits c => b == c
  | bits b, ptrFrag c _ _ => b == c
  | ptrFrag b p i, ptrFrag c q j => b == c && p == q && i == j
  | _, _ => false
```

```lean
-- lean/ToyReprLower/Basic.lean:46-48
def isInit : AByte → Bool
  | uninit => false
  | _ => true
```

```lean
-- lean/ToyReprLower/Basic.lean:51-53
def isFrag : AByte → Bool
  | ptrFrag .. => true
  | _ => false
```

```lean
-- lean/ToyReprLower/Basic.lean:56-58
def isBits : AByte → Bool
  | bits _ => true
  | _ => false
```

`AByte.data` gives `0` for `uninit`; every use of it that can affect a result (lowering, typed
reads, condition (d), field validity) is guarded by a check that the bytes are initialized.

```lean
-- lean/ToyReprLower/Basic.lean:63-66
def data : AByte → Nat
  | uninit => 0
  | bits b => b
  | ptrFrag b _ _ => b
```

```lean
-- lean/ToyReprLower/Basic.lean:71-74
def bytesLeb : List AByte → List AByte → Bool
  | [], [] => true
  | a :: as, b :: bs => a.leb b && bytesLeb as bs
  | _, _ => false
```

```lean
-- lean/ToyReprLower/Basic.lean:79
def BytesLe (x y : List AByte) : Prop := bytesLeb x y = true
```

Examples (proved, `lean/ToyReprLower/Examples.lean`): positive — `(bits 1).leb (ptrFrag 1 7 0) =
true`, `BytesLe [uninit, bits 1] [bits 0, ptrFrag 1 7 0]`; negative — `(ptrFrag 1 7 0).leb (bits
1) = false`, `¬ BytesLe [ptrFrag 1 7 0] [bits 1]`, `¬ BytesLe [bits 1] [bits 1, bits 2]` (the lengths differ).

#### Segments and byte-list predicates

`seg x off w` is `(x.drop off).take w`: it is **truncated** at the end of `x` (a segment that
runs past the end is shorter than `w`; `w = 0` gives `[]`).

```lean
-- lean/ToyReprLower/Basic.lean:87
def seg (x : List AByte) (off w : Nat) : List AByte := (x.drop off).take w
```

```lean
-- lean/ToyReprLower/Basic.lean:90
def allInit (bs : List AByte) : Bool := bs.all AByte.isInit
```

```lean
-- lean/ToyReprLower/Basic.lean:93
def allUninit (bs : List AByte) : Bool := bs.all (· == .uninit)
```

```lean
-- lean/ToyReprLower/Basic.lean:96
def allBits (bs : List AByte) : Bool := bs.all AByte.isBits
```

```lean
-- lean/ToyReprLower/Basic.lean:99
def datas (bs : List AByte) : List Nat := bs.map AByte.data
```

```lean
-- lean/ToyReprLower/Basic.lean:103-106
def fragsFrom (p : Nat) : Nat → List AByte → Bool
  | _, [] => true
  | k, .ptrFrag _ q i :: bs => q == p && i == k && fragsFrom p (k + 1) bs
  | _, _ :: _ => false
```

```lean
-- lean/ToyReprLower/Basic.lean:109-111
def fragProv : List AByte → Option Nat
  | .ptrFrag _ p _ :: _ => some p
  | _ => none
```

`ptrProv` is MiniRust's `decode_ptr` provenance rule: the common provenance if every byte is a
fragment of it at the matching position from `0`, else none.

```lean
-- lean/ToyReprLower/Basic.lean:115-118
def ptrProv (bs : List AByte) : Option Nat :=
  match fragProv bs with
  | some p => if fragsFrom p 0 bs then some p else none
  | none => none
```

Degenerate edge: `allInit [] = allUninit [] = allBits [] = true`, and `ptrProv [] = none`.

#### Primitives, scalars, representations

```lean
-- lean/ToyReprLower/Basic.lean:124-127
inductive Prim where
  | int (w : Nat)
  | ptr (w : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyReprLower/Basic.lean:130-132
def Prim.size : Prim → Nat
  | .int w => w
  | .ptr w => w
```

```lean
-- lean/ToyReprLower/Basic.lean:141-143
inductive Scalar where
  | initialized (p : Prim) (range : List Nat → Bool)
  | union (p : Prim)
```

```lean
-- lean/ToyReprLower/Basic.lean:146-148
def Scalar.prim : Scalar → Prim
  | .initialized p _ => p
  | .union p => p
```

```lean
-- lean/ToyReprLower/Basic.lean:151
def Scalar.size (s : Scalar) : Nat := s.prim.size
```

Widths are arbitrary, including `0`. `range` is the toy's stand-in for `rustc_abi::WrappingRange`.

```lean
-- lean/ToyReprLower/Basic.lean:159-162
inductive BRepr where
  | scalar (s : Scalar)
  | pair (a b : Scalar) (bOff : Nat)
  | memory
```

```lean
-- lean/ToyReprLower/Basic.lean:165-168
def BRepr.comps : BRepr → List (Nat × Scalar)
  | .scalar s => [(0, s)]
  | .pair a b o => [(0, a), (o, b)]
  | .memory => []
```

```lean
-- lean/ToyReprLower/Basic.lean:171-174
def BRepr.inExtent : BRepr → Nat → Bool
  | .scalar s, i => decide (i < s.size)
  | .pair a b o, i => decide (i < a.size) || (decide (o ≤ i) && decide (i < o + b.size))
  | .memory, _ => true
```

#### Register values, lowering and raising

```lean
-- lean/ToyReprLower/Basic.lean:185-190
inductive RVal where
  | poison
  | int (ds : List Nat)
  | ptr (prov : Option Nat) (ds : List Nat)
  | raw (bs : List AByte)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyReprLower/Basic.lean:197
def ptrLower (bs : List AByte) : RVal := .ptr (ptrProv bs) (datas bs)
```

```lean
-- lean/ToyReprLower/Basic.lean:206-213
def lowerScalar : Scalar → List AByte → RVal
  | .union _, bs => .raw bs
  | .initialized p rng, bs =>
    if allInit bs && rng (datas bs) then
      match p with
      | .int _ => .int (datas bs)
      | .ptr _ => ptrLower bs
    else .poison
```

```lean
-- lean/ToyReprLower/Basic.lean:216-218
def fragsList (p : Nat) : Nat → List Nat → List AByte
  | _, [] => []
  | k, d :: ds => .ptrFrag d p k :: fragsList p (k + 1) ds
```

```lean
-- lean/ToyReprLower/Basic.lean:223-228
def raiseScalar (s : Scalar) : RVal → List AByte
  | .poison => List.replicate s.size .uninit
  | .int ds => ds.map .bits
  | .ptr none ds => ds.map .bits
  | .ptr (some p) ds => fragsList p 0 ds
  | .raw bs => bs
```

```lean
-- lean/ToyReprLower/Basic.lean:231-235
inductive Lowered where
  | one (v : RVal)
  | two (va vb : RVal)
  | mem (bs : List AByte)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyReprLower/Basic.lean:239-242
def lower : BRepr → List AByte → Lowered
  | .scalar s, x => .one (lowerScalar s (seg x 0 s.size))
  | .pair a b o, x => .two (lowerScalar a (seg x 0 a.size)) (lowerScalar b (seg x o b.size))
  | .memory, x => .mem x
```

```lean
-- lean/ToyReprLower/Basic.lean:246-248
def chunkAt : List (Nat × List AByte) → Nat → AByte
  | [], _ => .uninit
  | (o, c) :: cs, i => if o ≤ i ∧ i < o + c.length then c.getD (i - o) .uninit else chunkAt cs i
```

```lean
-- lean/ToyReprLower/Basic.lean:251-252
def place (n : Nat) (cs : List (Nat × List AByte)) : List AByte :=
  (List.range n).map (chunkAt cs)
```

```lean
-- lean/ToyReprLower/Basic.lean:257-261
def raise (n : Nat) : BRepr → Lowered → List AByte
  | .scalar s, .one v => place n [(0, raiseScalar s v)]
  | .pair a b o, .two va vb => place n [(0, raiseScalar a va), (o, raiseScalar b vb)]
  | .memory, .mem bs => bs
  | _, _ => List.replicate n .uninit
```

Examples (proved, `lean/ToyReprLower/Examples.lean`): positive — `ptrLower [ptrFrag 1 7 0,
ptrFrag 2 7 1] = .ptr (some 7) [1, 2]`; `lowerScalar (.union (.int 2)) [bits 1, uninit] = .raw
[bits 1, uninit]`; plain bytes, mixed provenance, shifted positions, or a mix of plain bytes and
fragments give a provenance-free pointer (`ptrLower [ptrFrag 1 7 0, ptrFrag 2 8 1] = .ptr none
[1, 2]`); negative — `lowerScalar (.initialized (.int 2) fullRange) [bits 1, uninit] = .poison`,
`lowerScalar (.initialized (.int 1) nonZeroRange) [bits 0] = .poison`; an integer scalar built
from fragments is provenance-free (`.int [1, 2]`); a lowered value of the wrong shape raises to
all-`uninit` bytes.

#### Refinement and the four conditions

```lean
-- lean/ToyReprLower/Basic.lean:269-270
def RoundTripRefines (n : Nat) (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → BytesLe x (raise n r (lower r x))
```

```lean
-- lean/ToyReprLower/Basic.lean:274-275
def OutsideExtentsUninit (n : Nat) (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → ∀ i, i < n → r.inExtent i = false → x.getD i .uninit = .uninit
```

```lean
-- lean/ToyReprLower/Basic.lean:279-281
def initUniformAt : Scalar → List AByte → Bool
  | .initialized _ _, bs => allInit bs || allUninit bs
  | .union _, _ => true
```

```lean
-- lean/ToyReprLower/Basic.lean:285-286
def InitUniform (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => initUniformAt c.2 (seg x c.1 c.2.size)) = true
```

Condition (d) consults the range on fully initialized, non-empty bytes; partially initialized
bytes are left to condition (b), and the data of `uninit` bytes is never consulted:

```lean
-- lean/ToyReprLower/Basic.lean:292-294
def rangeInclAt : Scalar → List AByte → Bool
  | .initialized _ rng, bs => allUninit bs || !allInit bs || rng (datas bs)
  | .union _, _ => true
```

```lean
-- lean/ToyReprLower/Basic.lean:298-299
def RangeIncl (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => rangeInclAt c.2 (seg x c.1 c.2.size)) = true
```

```lean
-- lean/ToyReprLower/Basic.lean:304-306
def coherentFor : Prim → List AByte → Bool
  | .int _, bs => !bs.any AByte.isFrag
  | .ptr _, bs => !bs.any AByte.isFrag || (ptrProv bs).isSome
```

```lean
-- lean/ToyReprLower/Basic.lean:309-311
def provCoherentAt : Scalar → List AByte → Bool
  | .initialized p _, bs => allUninit bs || coherentFor p bs
  | .union _, _ => true
```

```lean
-- lean/ToyReprLower/Basic.lean:315-316
def ProvCoherent (r : BRepr) (V : List AByte → Prop) : Prop :=
  ∀ x, V x → r.comps.all (fun c => provCoherentAt c.2 (seg x c.1 c.2.size)) = true
```

Examples (proved): each of `RoundTripRefines`, `OutsideExtentsUninit`, `InitUniform`,
`RangeIncl`, `ProvCoherent` has a positive and a negative instance; `rangeInclAt (.initialized
(.int 2) nonZeroRange) [bits 0, uninit] = true` (range not consulted on partially initialized
bytes) and `rangeInclAt (.initialized (.int 2) nonZeroRange) [bits 0, bits 0] = false`;
`coherentFor (.ptr 2) [bits 1, bits 2] = true`, `coherentFor (.ptr 2) [ptrFrag 1 7 0, ptrFrag 2
8 1] = false`.

#### Typed reads (uses)

```lean
-- lean/ToyReprLower/Basic.lean:321-324
inductive Val where
  | int (ds : List Nat)
  | ptr (prov : Option Nat) (ds : List Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyReprLower/Basic.lean:329-333
def Val.leb : Val → Val → Bool
  | .int a, .int b => a == b
  | .ptr none a, .ptr _ b => a == b
  | .ptr (some p) a, .ptr (some q) b => a == b && p == q
  | _, _ => false
```

```lean
-- lean/ToyReprLower/Basic.lean:337-340
def OutLe : Option Val → Option Val → Prop
  | none, _ => True
  | some v, some w => v.leb w = true
  | some _, none => False
```

```lean
-- lean/ToyReprLower/Basic.lean:349-352
def readInt (off w : Nat) (x : List AByte) : Option Val :=
  if (seg x off w).length = w ∧ allInit (seg x off w) = true then
    some (.int (datas (seg x off w)))
  else none
```

```lean
-- lean/ToyReprLower/Basic.lean:356-359
def readPtr (off w : Nat) (x : List AByte) : Option Val :=
  if (seg x off w).length = w ∧ allInit (seg x off w) = true then
    some (.ptr (ptrProv (seg x off w)) (datas (seg x off w)))
  else none
```

Degenerate edge: at width `0` both reads return an empty value at every offset, past the end
included (`readInt_readPtr_width_zero`).

#### Register-level reinterpretation

`regCastScalar` is a bitcast that keeps register contents and asserts nothing. In particular a
`raw` union register cast into an `initialized` target keeps its bytes, `uninit` bytes and
provenance fragments included (a register value that lowering at the target never produces).

```lean
-- lean/ToyReprLower/Reinterpret.lean:22-32
def regCastScalar (s t : Scalar) (v : RVal) : RVal :=
  match t with
  | .union _ => .raw (raiseScalar s v)
  | .initialized q _ =>
    match v, q with
    | .poison, _ => .poison
    | .int ds, .int _ => .int ds
    | .int ds, .ptr _ => .ptr none ds
    | .ptr _ ds, .int _ => .int ds
    | .ptr pr ds, .ptr _ => .ptr pr ds
    | .raw bs, _ => .raw bs
```

`regCast` models componentwise casts between equal shapes and the concatenating cast of a pair
into a `union` scalar; every other combination passes the lowered value through unchanged (and a
lowered value of the wrong shape raises to `n` uninitialized bytes).

```lean
-- lean/ToyReprLower/Reinterpret.lean:42-46
def regCast : BRepr → BRepr → Lowered → Lowered
  | .scalar s, .scalar t, .one v => .one (regCastScalar s t v)
  | .pair a b _, .pair a' b' _, .two va vb => .two (regCastScalar a a' va) (regCastScalar b b' vb)
  | .pair a b _, .scalar (.union _), .two va vb => .one (.raw (raiseScalar a va ++ raiseScalar b vb))
  | _, _, l => l
```

`CastAgrees` is exact agreement of raised bytes; both paths start from the `σ`-lowered value
`lower σ x`, not from the raw bytes `x`:

```lean
-- lean/ToyReprLower/Reinterpret.lean:52-54
def CastAgrees (n : Nat) (σ τ : BRepr) : Prop :=
  ∀ x : List AByte, x.length = n →
    raise n τ (regCast σ τ (lower σ x)) = raise n τ (lower τ (raise n σ (lower σ x)))
```

`CastRefines` is the one-sided version (register path at least as defined as memory path):

```lean
-- lean/ToyReprLower/Reinterpret.lean:59-61
def CastRefines (n : Nat) (σ τ : BRepr) : Prop :=
  ∀ x : List AByte, x.length = n →
    BytesLe (raise n τ (lower τ (raise n σ (lower σ x)))) (raise n τ (regCast σ τ (lower σ x)))
```

```lean
-- lean/ToyReprLower/Reinterpret.lean:66-71
def DisciplineCompat (s t : Scalar) : Prop :=
  match s, t with
  | _, .union _ => True
  | .initialized p r1, .initialized _ r2 =>
      ∀ ds : List Nat, ds.length = p.size → r1 ds = true → r2 ds = true
  | .union _, .initialized _ _ => False
```

```lean
-- lean/ToyReprLower/Reinterpret.lean:75-79
def DisciplineCompatAnyLen (s t : Scalar) : Prop :=
  match s, t with
  | _, .union _ => True
  | .initialized _ r1, .initialized _ r2 => ∀ ds : List Nat, r1 ds = true → r2 ds = true
  | .union _, .initialized _ _ => False
```

Examples (proved): pointer-to-integer drops provenance, integer-to-pointer has none,
pointer-to-union keeps fragments, union-to-initialized keeps raw bytes; `DisciplineCompat`
positive (`nonZeroRange` into `fullRange`; union into union) and negative (`fullRange` into
`nonZeroRange`; union into initialized); `¬ DisciplineCompatAnyLen (.initialized (.int 2)
fullRange) (.initialized (.int 2) len2Range)` although `DisciplineCompat` holds for that pair.

#### Toy unions

```lean
-- lean/ToyReprLower/Union.lean:18-21
structure UField where
  off : Nat
  size : Nat
  valid : List AByte → Bool
```

```lean
-- lean/ToyReprLower/Union.lean:24-26
structure UnionTy where
  size : Nat
  fields : List UField
```

Whole-value union validity is a parameter; Rust has not decided it for unions without a
zero-sized field (see the Rust Reference quote under "Prior art and modeling bridge").

```lean
-- lean/ToyReprLower/Union.lean:30
abbrev UnionValidity := UnionTy → List AByte → Bool
```

```lean
-- lean/ToyReprLower/Union.lean:34
def trivialUnionValidity : UnionValidity := fun _ _ => true
```

```lean
-- lean/ToyReprLower/Union.lean:37
def emptyUnionValidity : UnionValidity := fun _ _ => false
```

```lean
-- lean/ToyReprLower/Union.lean:41-42
def unionMove (wv : UnionValidity) (u : UnionTy) (x : List AByte) : Option (List AByte) :=
  if x.length = u.size ∧ wv u x = true then some x else none
```

```lean
-- lean/ToyReprLower/Union.lean:46-47
def readField (f : UField) (x : List AByte) : Option (List AByte) :=
  if f.valid (seg x f.off f.size) = true then some (seg x f.off f.size) else none
```

`writeBytes` keeps the length of `x`; source bytes that would land past the end are dropped:

```lean
-- lean/ToyReprLower/Union.lean:52-54
def writeBytes (x : List AByte) (o : Nat) (src : List AByte) : List AByte :=
  (List.range x.length).map fun i =>
    if o ≤ i ∧ i < o + src.length then src.getD (i - o) .uninit else x.getD i .uninit
```

```lean
-- lean/ToyReprLower/Union.lean:58-59
def nicheInheritingMove (f : UField) (x : List AByte) : Option (List AByte) :=
  if f.valid (seg x f.off f.size) = true then some x else none
```

```lean
-- lean/ToyReprLower/Union.lean:62
def FieldwiseUninhabited (u : UnionTy) : Prop := ∀ f ∈ u.fields, ∀ bs, f.valid bs = false
```

```lean
-- lean/ToyReprLower/Union.lean:66-67
def moveThenRet (wv : UnionValidity) (u : UnionTy) (x : List AByte) : Option Val :=
  (unionMove wv u x).map fun _ => .int []
```

```lean
-- lean/ToyReprLower/Union.lean:71-72
def gatedUnreachable (judgedUninhabited : Bool) (prog : Option Val) : Option Val :=
  if judgedUninhabited then none else prog
```

A partial write into a `union` register is a lane-wise blend under a write mask, defined without
reference to `writeBytes` (R15 proves the two equal):

```lean
-- lean/ToyReprLower/Union.lean:76-77
def writeMask (w o len : Nat) : List Bool :=
  (List.range w).map fun i => decide (o ≤ i ∧ i < o + len)
```

```lean
-- lean/ToyReprLower/Union.lean:81-82
def shiftIn (w o : Nat) (src : List AByte) : List AByte :=
  (List.range w).map fun i => src.getD (i - o) .uninit
```

```lean
-- lean/ToyReprLower/Union.lean:86-87
def laneSelect (mask : List Bool) (old new : List AByte) : List AByte :=
  List.zipWith (fun m (p : AByte × AByte) => if m then p.2 else p.1) mask (List.zip old new)
```

```lean
-- lean/ToyReprLower/Union.lean:92-95
def mergeWrite (v : RVal) (o : Nat) (src : List AByte) : RVal :=
  match v with
  | .raw bs => .raw (laneSelect (writeMask bs.length o src.length) bs (shiftIn bs.length o src))
  | v => v
```

```lean
-- lean/ToyReprLower/Union.lean:99-100
def wholeWrite (w : Nat) (fill : AByte) (o : Nat) (src : List AByte) : RVal :=
  .raw (writeBytes (List.replicate w fill) o src)
```

```lean
-- lean/ToyReprLower/Union.lean:104-107
def hasUndef : RVal → Bool
  | .poison => true
  | .raw bs => bs.any (· == .uninit)
  | _ => false
```

```lean
-- lean/ToyReprLower/Union.lean:111-112
def passArg (noundef : Bool) (v : RVal) : Option RVal :=
  if noundef && hasUndef v then none else some v
```

Examples (proved): `unionMove trivialUnionValidity nzOrU8 [uninit] = some [uninit]`, `unionMove
trivialUnionValidity nzOrU8 [] = none`, `unionMove emptyUnionValidity nzOrU8 [uninit] = none`;
`readField` positive and negative; `writeBytes` in range and past the end; `nicheInheritingMove`
positive and negative; `¬ FieldwiseUninhabited nzOrU8`; `writeMask 3 1 1 = [false, true, false]`;
`mergeWrite`, `wholeWrite`, `hasUndef`, `passArg`.

### R1 — Lowering to one scalar refines iff (a), (b), (d) and (c) hold

- **Kind:** characterization. **Tier:** T1 (folklore made precise: rustc's const-eval
  interpreter requires `Scalar::Initialized` components for its immediates, and MiniRust's
  pointer decoding keeps a provenance just when the bytes are one pointer's fragments at matching
  positions; CompCert mechanizes a related byte model, but no mechanized iff of this form was
  found). **Depth:** substantive.
- **Plain claim:** Let `V` be any set of byte-level values, each of length exactly `n`, and let
  the representation be one scalar `s` of any width (the scalar's extent may run past the
  value; `seg` and `place` are truncated). Then the round trip `raise n ∘ lower` through
  `Scalar s` refines the identity on every value of `V` iff, in every value of `V`, with
  `bs` the (truncated) segment of the scalar's extent: (a) every byte below `n` outside the
  scalar's extent is `uninit`; and if `s` is `initialized p rng`: (b) `bs` is all initialized or
  all uninitialized, (d) if `bs` is all initialized and non-empty, its data lie in `rng`, and
  (c) unless `bs` is all uninitialized, `bs` is provenance coherent for `p` (integer: no pointer
  fragment; pointer: no pointer fragment, or one pointer's fragments with one provenance in order
  from position `0`).
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Lowering.lean:137-141
theorem scalar_roundTrip_refines_iff (n : Nat) (s : Scalar) (V : List AByte → Prop)
    (hlen : ∀ x, V x → x.length = n) :
    RoundTripRefines n (.scalar s) V ↔
      OutsideExtentsUninit n (.scalar s) V ∧ InitUniform (.scalar s) V ∧
        RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V
```

Unfolded (prose): `(∀ x ∈ V, x ⊑ raise n (scalar s) (lower (scalar s) x))` iff, for every
`x ∈ V` with `bs := seg x 0 s.size`: `∀ i < n, ¬ i < s.size → x[i] = uninit`, and if
`s = initialized p rng` then `allUninit bs ∨ (allInit bs ∧ rng (datas bs) ∧ coherentFor p bs)`.

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hlen : ∀ x, V x → x.length = n` | values have the type's size, so lengths match after raising | tight for the `←` direction: `cex_scalar_hlen` (a 1-byte `union` scalar with `V = {[]}`); the `→` direction holds without it (`scalar_conditions_of_roundTrip_refines`) | `cex_scalar_hlen` |
| (a) `OutsideExtentsUninit`, premise of `←` | bytes outside the extent are dropped by lowering | tight: a 1-byte integer scalar in a 2-byte value | `cex_scalar_padding_carries_bytes` |
| (b) `InitUniform`, premise of `←` | a partially initialized `initialized` scalar lowers to poison | tight: a 2-byte integer scalar with one `uninit` byte | `cex_scalar_partial_init` |
| (d) `RangeIncl`, premise of `←` | out-of-range data lower to poison | tight: a 1-byte scalar with `nonZeroRange` holding `0` | `cex_scalar_out_of_range` |
| (c) `ProvCoherent`, premise of `←` | an integer scalar drops provenance; a pointer scalar drops mixed provenance | tight: pointer fragments under a 2-byte integer scalar; also fragments of two provenances under a 2-byte pointer scalar | `cex_scalar_frags_under_int`, `cex_scalar_mixed_provenance_ptr` |

No in-bounds hypothesis `s.size ≤ n` is needed: the theorem above holds
for every width (proof by truncation of `seg` and `place`, `scalar_bytesLe_roundTrip_iff`).
The witnesses for (a), (b) and (d) (`cex_scalar_padding_carries_bytes`, `cex_scalar_partial_init`,
`cex_scalar_out_of_range`) each exhibit a typed integer read that is defined before lowering and
UB after; the integer-scalar witness for (c) (`cex_scalar_frags_under_int`) exhibits a typed
pointer read that has provenance before lowering and gives a provenance-free pointer after; the
pointer-scalar witness for (c) (`cex_scalar_mixed_provenance_ptr`) exhibits no typed read and
shows instead that lowering and raising strip the provenance of its two fragments, giving
`[bits 1, bits 2]`.

- **Degenerate edges:** `n = 0` (then `V ⊆ {[]}` and (a) is vacuous); `s.size = 0` (then `bs = []`
  and (b), (d), (c) hold, so the round trip refines iff every byte is `uninit`); `V` empty (both
  sides hold).
- **Non-vacuity:** `nonvacuous_scalar_roundTrip` (a 2-byte pointer scalar holding one pointer's
  fragments, in a 3-byte value whose padding byte is `uninit`; (a) is exercised).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R1).
- **Prior art:** rustc interpreter and `Scalar` documentation; MiniRust `decode_ptr` and
  definedness order (quoted under "Modeling bridge to documented designs"); CompCert's byte-level memory
  values with pointer fragments (`Memdata.v`).
- **Design question:** When may a lowering pass keep a value of a given type in one register
  instead of memory without changing byte-level behaviour?

### R2 — Lowering to a scalar pair refines iff (a), (b), (d) and (c) hold for both scalars

- **Kind:** characterization. **Tier:** T1 (folklore made precise: R1's four conditions, for two
  scalars at fixed, disjoint offsets in memory order, as in rustc's `ScalarPair` layouts).
  **Depth:** substantive.
- **Plain claim:** Let the representation be a pair `a`, `b` with `a` at offset `0` and `b` at
  offset `bOff`, with disjoint extents (`a.size ≤ bOff`; `b`'s extent may run past the value),
  and let `V` be any set of byte-level values, each of length exactly `n`. Then the round trip
  through `ScalarPair a b bOff` refines the identity on every value of `V` iff, in every value of
  `V`, (a) every byte below `n` outside both extents is `uninit`, and (b), (d), (c) hold for each
  `initialized` component on its own (truncated) extent.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Lowering.lean:223-227
theorem pair_roundTrip_refines_iff (n : Nat) (a b : Scalar) (bOff : Nat) (V : List AByte → Prop)
    (hlen : ∀ x, V x → x.length = n) (hab : a.size ≤ bOff) :
    RoundTripRefines n (.pair a b bOff) V ↔
      OutsideExtentsUninit n (.pair a b bOff) V ∧ InitUniform (.pair a b bOff) V ∧
        RangeIncl (.pair a b bOff) V ∧ ProvCoherent (.pair a b bOff) V
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hlen` | lengths match after raising | tight for `←`: two 1-byte `union` scalars with `V = {[]}`; the `→` direction holds without it (`pair_conditions_of_roundTrip_refines`) | `cex_pair_hlen` |
| `hab : a.size ≤ bOff` | extents disjoint, so each byte is raised from its own scalar | tight for `→`: overlapping 2-byte pointer and integer scalars in a 3-byte value; the round trip refines although (c) fails; the `←` direction holds without it (`pair_roundTrip_refines_of_conditions`) | `cex_pair_overlap` |
| (a) premise of `←` | padding between the scalars is dropped | tight: two 1-byte integer scalars at offsets `0` and `2`, padding byte holding data | `cex_pair_padding_carries_bytes` |
| (b) premise of `←` | partial initialization of a component | tight: a 2-byte integer component with one `uninit` byte | `cex_pair_partial_init` |
| (d) premise of `←` | range of a component | tight: a 1-byte `nonZeroRange` component holding `0` | `cex_pair_out_of_range` |
| (c) premise of `←` | a pointer split across the `a`/`b` boundary | tight: two 2-byte pointer scalars in a 4-byte value; each lowers to a provenance-free pointer | `cex_pair_ptr_split_across_boundary` |

No in-bounds hypothesis `bOff + b.size ≤ n` is needed
(`pair_bytesLe_roundTrip_iff` holds without it).

- **Degenerate edges:** `n = 0`; a component of width `0`; `b`'s extent entirely past the value
  (`n ≤ bOff`: its segment is empty and (b), (d), (c) hold for it).
- **Non-vacuity:** `nonvacuous_pair_roundTrip` (a pointer with provenance at offset `0` and an
  integer at offset `3` of a 5-byte value with one `uninit` padding byte).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R2).
- **Prior art:** as R1.
- **Design question:** Which components of a value may be lowered to two scalar registers without
  changing its bytes; in particular whether pointer fragments may straddle the two scalars. By
  R2's condition (c) (derived from `pair_roundTrip_refines_iff`; not proved here as a separate
  theorem), a non-`union` component whose segment holds a pointer fragment must be a pointer
  scalar whose segment consists of fragments of one provenance at positions `0`, `1`, … in
  order. So a pointer whose fragments lie in both segments needs `b` to be `union` (its
  fragments in `b`'s segment do not start at position `0`), and needs `a` to be `union` as well
  when it starts at an interior offset of `a`; when it starts at offset `0`, `a` may instead be a
  pointer scalar whose range admits the data.

### R3 — Typed reads are monotone in the byte order

- **Kind:** theorem. **Tier:** T0 (instance of MiniRust's decode-monotonicity law for integer and
  pointer types; CompCert proves the analogous `decode_val_inject`). **Depth:** shallow.
- **Plain claim:** If `y` is at least as defined as `x` (`BytesLe x y`), then for every offset
  and every width, the typed integer read and the typed pointer read of `y` are at least as
  defined as those of `x` (UB is the least defined outcome).
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Uses.lean:83-84
theorem typedReads_mono_of_bytesLe {x y : List AByte} (h : BytesLe x y) (off w : Nat) :
    OutLe (readInt off w x) (readInt off w y) ∧ OutLe (readPtr off w x) (readPtr off w y)
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `h : BytesLe x y` | the premise | tight: an initialized 1-byte value replaced by `uninit` | `cex_typedReads_without_bytesLe` |

- **Degenerate edge:** width `0` (both reads return an empty value at every offset, past the end
  included: `readInt_readPtr_width_zero`).
- **Non-vacuity:** `nonvacuous_typedReads_mono`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R3).
- **Prior art:** MiniRust monotonicity law (`spec/lang/representation.md`); CompCert
  `decode_val_inject`.
- **Design question:** Licenses using the byte order as the refinement criterion in R1, R2, R4.

### R4 — For a `union` scalar, the round trip refines iff condition (a) holds

- **Kind:** characterization. **Tier:** T1 (folklore made precise: rustc documents that `union`
  scalars "never have niches and even allow undef"; here the `union` special case of R1).
  **Depth:** shallow (corollary of R1).
- **Plain claim:** For a `union` scalar of any width and any set `V` of byte-level values, each of
  length exactly `n` (partially initialized and fragment-carrying values included), the round
  trip through `Scalar (union p)` refines the identity on every value of `V` iff every byte below
  `n` outside the scalar's extent is `uninit` in every value of `V`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Lowering.lean:314-316
theorem union_scalar_roundTrip_refines_iff_outsideExtentsUninit (n : Nat) (p : Prim)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n) :
    RoundTripRefines n (.scalar (.union p)) V ↔ OutsideExtentsUninit n (.scalar (.union p)) V
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hlen` | lengths match | tight for `←`: a 1-byte `union` scalar with `V = {[]}` | `cex_scalar_hlen` |

No in-bounds hypothesis `p.size ≤ n` is needed.

- **Non-vacuity:** `nonvacuous_union_roundTrip` (a 3-byte `union` scalar in a 4-byte value holding
  a fragment, an `uninit` byte, a plain byte and `uninit` padding).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R4).
- **Prior art:** rustc `Scalar::Union` documentation ("unions never have niches and even allow
  undef"); CompCert's `Many32`/`Many64` chunks, which move fragments opaquely; an LLVM byte type
  that would let registers carry such bytes is an open, unmerged proposal and is not relied on.
- **Design question:** Which components may be lowered to registers without any validity
  knowledge about the values?

### R4b — A `union` scalar covering the whole value always refines

- **Kind:** theorem. **Tier:** T0 (corollary of R4). **Depth:** shallow.
- **Plain claim:** For a `union` scalar of width at least `n` and any set `V` of byte-level
  values, each of length exactly `n` (partially initialized and fragment-carrying values
  included), the round trip through `Scalar (union p)` refines the identity on every value of
  `V`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Lowering.lean:325-327
theorem union_scalar_roundTrip_refines_of_covers_value (n : Nat) (p : Prim)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n) (hcov : n ≤ p.size) :
    RoundTripRefines n (.scalar (.union p)) V
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hlen` | lengths match | tight: a 1-byte `union` scalar covering a 1-byte value, `V = {[]}` | `cex_union_covers_value_hlen` |
| `hcov : n ≤ p.size` | no byte of the value lies outside the extent | tight: a 1-byte `union` scalar in a 2-byte value whose second byte holds data | `cex_union_size_lt` |

- **Non-vacuity:** `nonvacuous_union_covers_value`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R4b).
- **Prior art:** as R4.
- **Design question:** Which components may be lowered to registers without any validity
  knowledge about the values, in the common case of a union whose scalar covers the value?

### R5 — For every primitive and range, some union value does not round-trip as `initialized`

- **Kind:** impossibility. **Tier:** T1 (rustc's interpreter documents that a `Scalar`-layout
  union such as `MaybeUninit<u64>` cannot be held as an initialized immediate). **Depth:**
  shallow (via R1).
- **Plain claim:** For every primitive `p` of width at least `1` and every range `rng`, the value
  `ptrFrag 0 0 1 :: replicate (p.size - 1) uninit` (truncated subtraction; a stray pointer
  fragment followed by uninitialized bytes, of length exactly `p.size`) round-trips through
  `Scalar (union p)` and does not round-trip through `Scalar (initialized p rng)`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Witnesses.lean:224-229
theorem initialized_lowering_not_refines_some_union_value (p : Prim) (rng : List Nat → Bool)
    (hp : 1 ≤ p.size) :
    RoundTripRefines p.size (.scalar (.union p))
        (· = .ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit) ∧
      ¬ RoundTripRefines p.size (.scalar (.initialized p rng))
        (· = .ptrFrag 0 0 1 :: List.replicate (p.size - 1) .uninit)
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hp : 1 ≤ p.size` | a lane exists | tight: width `0` (`p = int 0`): the named value has the wrong length, and every set of width-`0` values round-trips through every `initialized` width-`0` scalar | `cex_initialized_lowering_width_zero` |

- **Positive control:** `initialized_lowering_refines_plain_in_range_value` (a plain in-range byte
  round-trips through an `initialized` scalar with `nonZeroRange`).
- **Non-vacuity:** `nonvacuous_initialized_lowering_union_value` (`p = int 1`, full range).
- **Escape hatches:** listed under **Boundaries → Escape hatches of the impossibility results** (R5).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R5).
- **Prior art:** rustc interpreter comment on `MaybeUninit<u64>` (quoted under "Modeling bridge to
  documented designs"; `derived (modeling bridge)`).
- **Design question:** Whether a union component of width at least `1` may be lowered with an
  initialization or range assertion (by R5, not for every value; by R1, for a set of values each
  of length exactly `n`, iff the values satisfy (a)–(d)).

### R6 — Coarsening to `memory` is always a refinement (positive control)

- **Kind:** theorem. **Tier:** T0 (re-derivation: keeping a value in memory is the identity on its
  bytes). **Depth:** definitional.
- **Plain claim:** For every size `n` and every set `V` of byte-level values, the round trip
  through `memory` refines the identity on every value of `V` (it is the identity).
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Lowering.lean:336-337
theorem memory_roundTrip_refines (n : Nat) (V : List AByte → Prop) :
    RoundTripRefines n .memory V
```

- **Hypotheses:** none (`n` is not used). **Non-vacuity:** `nonvacuous_memory_roundTrip`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R6).
- **Design question:** Safe fallback for a lowering pass that cannot establish R1's conditions.

### R7 — Scalar-to-scalar reinterpretation agrees exactly with the memory transmute iff disciplines are compatible

- **Kind:** characterization. **Tier:** T1 (folklore made precise: the informal expectation that
  a register bitcast between equal-width scalars matches a transmute through memory when the
  target admits every value the source can hold; `derived (modeling bridge)`: LLVM's `noundef`
  and `range` attributes, quoted under "Modeling bridge to documented designs", are where that
  admissibility matters; not mechanized in this form). **Depth:** substantive.
- **Plain claim:** For scalars `s`, `t` of equal width `w` with `1 ≤ w ≤ n`, the register-level
  reinterpretation `regCast` from `Scalar s` to `Scalar t` and the byte-level transmute through
  memory (raise at `s`, lower at `t`) give equal raised bytes, both starting from the `s`-lowered
  form `lower (scalar s) x` of every byte-level value `x` of length exactly `n`, iff `t` is a
  `union` scalar, or both are `initialized` and `s`'s range is included in `t`'s on data vectors
  of length exactly `w`. Integer-to-pointer and pointer-to-integer reinterpretations are included.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Reinterpret.lean:314-316
theorem regCast_scalar_agrees_iff_disciplineCompat (n : Nat) (s t : Scalar)
    (hw : s.size = t.size) (hpos : 1 ≤ s.size) (hn : s.size ≤ n) :
    CastAgrees n (.scalar s) (.scalar t) ↔ DisciplineCompat s t
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hw : s.size = t.size` | componentwise bitcast of equal widths | tight for `←`: a 1-byte integer reinterpreted as a 2-byte one with compatible disciplines disagrees | `cex_regCast_scalar_width_mismatch` |
| `hpos : 1 ≤ s.size` | at width `0` nothing distinguishes the paths | tight for `→`: width-`0` `union` to `initialized` agrees; the `←` direction holds without it (`regCast_scalar_agrees_of_disciplineCompat`) | `cex_regCast_scalar_width_zero` |
| `hn : s.size ≤ n` | the extent lies in the value | tight for `→`: length-independent ranges at `n = 0` (`fullRange` into `nonZeroRange`); tight for `←`: the length-dependent `len2Range` at `n = 1` | `cex_regCast_scalar_hn_length_indep`, `cex_regCast_scalar_wider_than_value` |

- **Non-vacuity:** `nonvacuous_regCast_scalar` (pointer to integer); also
  `regCast_int_to_ptr_agrees`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R7).
- **Prior art:** LLVM `noundef`/`range` attribute semantics (pinned LangRef quotes under "Modeling
  bridge to documented designs"; `derived (modeling bridge)`); the formal LLVM semantics of
  `undef`/`poison` by Lee et al. and Alive2.
- **Design question:** When may a transmute between scalar-represented types be compiled as a
  register bitcast without changing the bytes that reach memory?

### R7b — Scalar-to-scalar reinterpretation refines the memory transmute (one-sided), for all widths and disciplines

- **Kind:** theorem. **Tier:** T0 (reference point for R7). **Depth:** shallow.
- **Plain claim:** For every `n` and all scalars `s`, `t` (of any widths, equal or not, including
  widths greater than `n`; with any initialization disciplines and ranges), the register-level
  reinterpretation from `Scalar s` to `Scalar t` is at least as defined (`BytesLe`) as the
  byte-level transmute through memory, both starting from the `s`-lowered form of every
  byte-level value of length exactly `n` (`CastRefines`).
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Reinterpret.lean:630-631
theorem regCast_scalar_refines_transmute (n : Nat) (s t : Scalar) :
    CastRefines n (.scalar s) (.scalar t)
```

- **Hypotheses:** none. The statement quantifies over every `n`, `s` and `t`; neither equal
  widths (`s.size = t.size`) nor `s.size ≤ n` is assumed.
- **Proof idea (prose):** `regCastScalar` keeps the register payload without truncating or padding
  it to `t.size`. On the memory side, the first `t.size` bytes of the raised value (truncated at
  `n`) either fail an `initialized` target's initialization or range check, and then raise to
  `uninit` bytes, or are, position by position, the source register's raised bytes (or `uninit`
  past their end), which the register side keeps at least as defined.
- **Non-vacuity:** not applicable (no hypotheses). Instances:
  `regCast_union_to_initialized_refines_not_agrees` (a 1-byte `union` to `initialized`
  reinterpretation: `CastRefines` holds, `CastAgrees` fails) and
  `castRefines_unequal_widths_and_wider_than_value` (1- and 2-byte `initialized` integers: both
  unequal-width reinterpretations refine on 2-byte values while the 2-byte-to-1-byte one does not
  agree; a 2-byte scalar on 1-byte values refines without agreeing).

```lean
-- lean/ToyReprLower/Witnesses.lean:877-884
theorem castRefines_unequal_widths_and_wider_than_value :
    let s1 : Scalar := .initialized (.int 1) fullRange
    let s2 : Scalar := .initialized (.int 2) fullRange
    let s2len : Scalar := .initialized (.int 2) len2Range
    (s1.size ≠ s2.size ∧ CastRefines 2 (.scalar s1) (.scalar s2) ∧
      CastRefines 2 (.scalar s2) (.scalar s1) ∧ ¬ CastAgrees 2 (.scalar s2) (.scalar s1)) ∧
    (¬ s2.size ≤ 1 ∧ CastRefines 1 (.scalar s2) (.scalar s2len) ∧
      ¬ CastAgrees 1 (.scalar s2) (.scalar s2len))
```

- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R7b).
- **Prior art:** LLVM `noundef`/`range` attribute semantics (pinned LangRef quotes under "Modeling
  bridge to documented designs"; `derived (modeling bridge)`); the formal LLVM semantics of
  `undef`/`poison` by Lee et al. and Alive2.
- **Design question:** Which property does discipline compatibility actually protect in this
  model (answer: exact agreement, R7), so that it is not misread as a refinement condition.

### R8 — Pair-to-pair reinterpretation agrees exactly when offsets coincide and disciplines are compatible

- **Kind:** theorem. **Tier:** T1 (folklore made precise: a componentwise register bitcast
  between equal-width scalar registers, for scalar pairs at a shared `b` offset; not mechanized in
  this form). **Depth:** shallow.
- **Plain claim:** For pairs `(a, b)` and `(a', b')` at the same `b` offset `bOff`, with
  `a.size = a'.size`, `b.size = b'.size`, disjoint extents (`a.size ≤ bOff`), `b`'s extent inside
  the value (`bOff + b.size ≤ n`), and `DisciplineCompat a a'` and `DisciplineCompat b b'`, the
  componentwise register-level reinterpretation and the byte-level transmute through memory give
  equal raised bytes, both starting from the `(a, b)`-lowered form of every byte-level value of
  length exactly `n`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Reinterpret.lean:367-370
theorem regCast_pair_agrees_of_offsetEq_disciplineCompat (n : Nat) (a b a' b' : Scalar)
    (bOff : Nat) (hwa : a.size = a'.size) (hwb : b.size = b'.size) (hab : a.size ≤ bOff)
    (hbn : bOff + b.size ≤ n) (hca : DisciplineCompat a a') (hcb : DisciplineCompat b b') :
    CastAgrees n (.pair a b bOff) (.pair a' b' bOff)
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| shared offset `bOff` | extents coincide | tight: offsets `1` versus `2` for 1-byte integer components, all other hypotheses holding for each offset | `cex_regCast_pair_offset_mismatch` |
| `hwa` | widths of `a` | tight: a 1-byte `a` reinterpreted as a 2-byte `a'` | `cex_regCast_pair_width_mismatch` |
| `hwb` | widths of `b` | tight: a 1-byte `b` reinterpreted as a 2-byte `b'` | `cex_regCast_pair_width_mismatch_b` |
| `hab` | disjoint extents | tight: overlapping 2-byte integer and pointer scalars | `cex_regCast_pair_overlap` |
| `hbn` | `b` in the value | tight for a length-dependent range (`len2Range`); for length-independent range inclusion it can be dropped (`regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen`) | `cex_regCast_pair_out_of_bounds` |
| `hca` | discipline of `a` | tight: a 1-byte `union` component reinterpreted as `initialized` | `cex_regCast_pair_discipline` |
| `hcb` | discipline of `b` | tight: a 1-byte `union` `b` component reinterpreted as a 1-byte `initialized` integer, at `bOff = 1` in a 2-byte value, all other hypotheses holding | `cex_regCast_pair_discipline_b` |

- **Non-vacuity:** `nonvacuous_regCast_pair` (pointer and integer to integer and `union`).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R8).
- **Prior art:** as R7.
- **Design question:** When may a transmute between pair-represented types be compiled as a
  componentwise register bitcast without changing the bytes that reach memory?

### R9 — A pair-to-`union`-scalar reinterpretation across padding disagrees; without padding it agrees

- **Kind:** counterexample (with a general positive control). **Tier:** T0 (re-derivation:
  concatenating registers ignores padding between the fields). **Depth:** definitional
  (counterexample); shallow (positive control).
- **Plain claim:** For a 3-byte value represented as two 1-byte integers at offsets `0` and `2`
  (byte `1` is padding), holding `[bits 1, uninit, bits 2]`, concatenating the two registers into
  one 2-byte `union` register at offset `0` gives the bytes `[bits 1, bits 2, uninit]`, while the
  memory transmute gives `[bits 1, uninit, uninit]` (the 2-byte `union` scalar reads the padding
  byte, not `b`); the two paths disagree.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Witnesses.lean:496-504
theorem regCast_pair_to_union_scalar_across_padding_disagrees :
    let a : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .union (.int 2)
    let x : List AByte := [.bits 1, .uninit, .bits 2]
    raise 3 (.scalar t) (regCast (.pair a a 2) (.scalar t) (lower (.pair a a 2) x)) =
        [.bits 1, .bits 2, .uninit] ∧
      raise 3 (.scalar t) (lower (.scalar t) (raise 3 (.pair a a 2) (lower (.pair a a 2) x))) =
        [.bits 1, .uninit, .uninit] ∧
      ¬ CastAgrees 3 (.pair a a 2) (.scalar t)
```

- **Positive control:** `regCast_pair_to_union_scalar_agrees_of_no_padding` — for a pair with `b`
  at offset exactly `a.size` (no padding between the scalars) and a `union` scalar of width
  exactly `a.size + b.size` with `a.size + b.size ≤ n`, the concatenating reinterpretation and
  the memory transmute give equal raised bytes, both starting from the `(a, b)`-lowered form of
  every value of length exactly `n`; instance
  `regCast_pair_to_union_scalar_agrees_no_padding_instance`.

```lean
-- lean/ToyReprLower/Reinterpret.lean:977-979
theorem regCast_pair_to_union_scalar_agrees_of_no_padding (n : Nat) (a b : Scalar) (q : Prim)
    (hq : q.size = a.size + b.size) (hn : a.size + b.size ≤ n) :
    CastAgrees n (.pair a b a.size) (.scalar (.union q))
```

- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R9).
- **Design question:** Whether a register-level reinterpretation between shapes may ignore the
  padding layout of the source (by R9, not in general).

### R10 — Attaching provenance is not the reinterpretation

- **Kind:** counterexample. **Tier:** T0 (re-derivation: a provenance-attaching cast is a
  different operation from a bitcast). **Depth:** definitional.
- **Plain claim:** For the 1-byte integer `5`, the memory transmute to a 1-byte pointer scalar and
  `regCast` both give `bits 5` (no provenance), while a cast attaching provenance `7`
  (`attachProvCast 7`) gives `ptrFrag 5 7 0`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Witnesses.lean:529-537
theorem provenanceAttachingCast_differs_from_transmute :
    let s : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .initialized (.ptr 1) fullRange
    raise 1 (.scalar t) (lower (.scalar t) (raise 1 (.scalar s) (lower (.scalar s) [.bits 5]))) =
        [.bits 5] ∧
      raise 1 (.scalar t) (regCast (.scalar s) (.scalar t) (lower (.scalar s) [.bits 5])) =
        [.bits 5] ∧
      raise 1 (.scalar t) (.one (attachProvCast 7 (lowerScalar s [.bits 5]))) =
        [.ptrFrag 5 7 0]
```

- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R10).
- **Design question:** Whether a register-level integer-to-pointer reinterpretation may be
  implemented as a provenance-picking cast if it is to match the transmute byte for byte (by R10,
  not in general).

### R11 — Under trivial whole-value validity, a union move is defined iff the size matches; a field read is UB iff its bytes are invalid

- **Kind:** theorem. **Tier:** T0 (re-derivation: union move and field-read validity under
  trivial whole-value validity, restated in the toy). **Depth:** definitional.
- **Plain claim:** For every toy union `u`, field descriptor `f` and byte list `x`: the union move
  under trivial whole-value validity, `unionMove trivialUnionValidity u x`, returns `some x` iff
  `x.length = u.size`; and reading field `f` is UB (`none`) iff `f`'s validity predicate rejects
  `f`'s (truncated) bytes.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Union.lean:120-123
theorem unionMove_trivial_defined_iff_size_and_readField_ub_iff_invalid (u : UnionTy)
    (f : UField) (x : List AByte) :
    (unionMove trivialUnionValidity u x = some x ↔ x.length = u.size) ∧
      (readField f x = none ↔ f.valid (seg x f.off f.size) = false)
```

- **Hypotheses:** none. **Non-vacuity:** `nonvacuous_unionMove_readField`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R11).
- **Design question:** Separating whole-value validity of a union from validity of a projection.

### R12 — A niche-inheriting union move would be UB after a valid field write

- **Kind:** counterexample. **Tier:** T0 (re-derivation: a union does not inherit one field's
  niche when another field admits the niche value). **Depth:** definitional.
- **Plain claim:** In `nzOrU8 = { a: NonZeroU8, b: u8 }`, starting from the bytes of `a = 5` and
  writing `b = 0` (valid for `b`): reading `b` gives `[bits 0]`, the union move under trivial
  whole-value validity is defined, and a move that inherited `a`'s niche
  (`nicheInheritingMove nonZeroU8Field`) is UB.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Union.lean:264-267
theorem nicheInheriting_union_move_ub_after_valid_field_write :
    readField u8Field (writeBytes [.bits 5] 0 [.bits 0]) = some [.bits 0] ∧
    unionMove trivialUnionValidity nzOrU8 (writeBytes [.bits 5] 0 [.bits 0]) = some [.bits 0] ∧
    nicheInheritingMove nonZeroU8Field (writeBytes [.bits 5] 0 [.bits 0]) = none
```

- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R12).
- **Design question:** Whether a union layout may inherit one field's niche when another field
  admits the niche value (by R12, not without making a move after a valid write UB).

### R13 — An `Unreachable` rewrite of a union move refines iff whole-value validity admits no value

- **Kind:** characterization. **Tier:** T0 (re-derivation: rewriting code to `Unreachable` refines
  it exactly when the code is UB on every input, specialized to union moves). **Depth:**
  definitional.
- **Plain claim:** For every whole-value validity policy `wv`, toy union `u`, and gate `gate`
  that fires on `u` (`gate u = true`): replacing the move-then-return program by UB
  (`gatedUnreachable`) is at least as defined as the program, on every byte list of `u`'s size,
  iff `wv` rejects every byte list of `u`'s size.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Union.lean:284-288
theorem unreachableRewrite_refines_iff_no_wholeValue_valid (wv : UnionValidity) (u : UnionTy)
    (gate : UnionTy → Bool) (hgate : gate u = true) :
    (∀ x : List AByte, x.length = u.size →
      OutLe (moveThenRet wv u x) (gatedUnreachable (gate u) (moveThenRet wv u x))) ↔
    ∀ x : List AByte, x.length = u.size → wv u x = false
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hgate : gate u = true` | the rewrite fires | tight: the never-firing gate on `neverUnion` under trivial validity (the program refines itself; validity admits a value) | `cex_unreachableRewrite_gate_false` |

- **Non-vacuity:** `nonvacuous_unreachableRewrite_iff` (the always-firing gate on `neverUnion`:
  both sides true under `emptyUnionValidity`, both false under `trivialUnionValidity`).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R13).
- **Design question:** What an uninhabitedness-gated `Unreachable` rewrite of a union move
  requires: that no value of the union be valid.

### R13b — Under trivial whole-value validity, a field-wise uninhabitedness gate is not a refinement

- **Kind:** impossibility. **Tier:** T0 (re-derivation: R13 under trivial whole-value validity).
  **Depth:** definitional.
- **Plain claim:** For every gate that fires on every `FieldwiseUninhabited` union: the one-byte
  union `neverUnion`, whose single field is uninhabited and which has no zero-sized field, is
  `FieldwiseUninhabited`; under trivial whole-value validity the program that moves its value
  `[uninit]` and returns is defined; and the gated `Unreachable` rewrite of that program is not at
  least as defined.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Union.lean:305-311
theorem fieldwiseUninhabited_gate_not_refinement_of_trivialValidity (gate : UnionTy → Bool)
    (hgate : ∀ u, FieldwiseUninhabited u → gate u = true) :
    FieldwiseUninhabited neverUnion ∧
    moveThenRet trivialUnionValidity neverUnion [.uninit] = some (.int []) ∧
    ¬ OutLe (moveThenRet trivialUnionValidity neverUnion [.uninit])
        (gatedUnreachable (gate neverUnion)
          (moveThenRet trivialUnionValidity neverUnion [.uninit]))
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hgate : ∀ u, FieldwiseUninhabited u → gate u = true` | the gate judges field-wise uninhabited unions uninhabited | tight: the never-firing gate | `cex_fieldwiseGate_never_fires` |

- **Positive control:** `gate_refines_of_emptyValidity` (under `emptyUnionValidity`, every gate
  that fires on `neverUnion` refines on every byte list of its size).
- **Non-vacuity:** `nonvacuous_fieldwiseGate` (the always-firing gate satisfies `hgate`).
- **Escape hatches:** listed under **Boundaries → Escape hatches of the impossibility results** (R13b).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R13b).
- **Design question:** Whether field-wise uninhabitedness may justify treating a union as
  uninhabited (it may not, unless whole-value validity rules out every value).

### R14 — Framing of partial writes

- **Kind:** theorem. **Tier:** T0 (re-derivation: the framing law of byte-wise writes, restated
  for the toy `writeBytes`). **Depth:** definitional.
- **Plain claim:** For every byte list `x`, offset `o` and source `src`: `writeBytes x o src` has
  the length of `x`; every position `i < x.length` with `o ≤ i < o + src.length` holds `src`'s
  byte `i - o`; every other position holds `x`'s old byte (source bytes past the end of `x` are
  dropped).
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Union.lean:133-138
theorem writeBytes_frame (x src : List AByte) (o : Nat) :
    (writeBytes x o src).length = x.length ∧
    (∀ i, i < x.length → o ≤ i → i < o + src.length →
      (writeBytes x o src).getD i .uninit = src.getD (i - o) .uninit) ∧
    (∀ i, ¬ (o ≤ i ∧ i < o + src.length) →
      (writeBytes x o src).getD i .uninit = x.getD i .uninit)
```

- **Hypotheses:** none. **Non-vacuity:** `nonvacuous_writeBytes_frame` (a write inside the value
  and one running past its end).
- **Degenerate edges:** `src = []` (no change); `o ≥ x.length` (no change); `x = []`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R14).
- **Prior art:** the byte-level memory model of CompCert (Leroy and Blazy 2008), whose stores
  satisfy analogous framing laws (the CompCert lemmas themselves were not re-checked here).
- **Design question:** The memory-level semantics of a partial write against which R15 and R16
  compare register-level writes.

### R14b — A wider read after a partial write sees the written bytes plus the old bytes

- **Kind:** theorem. **Tier:** T0 (re-derivation: corollary of R14 for a read wider than the
  write). **Depth:** definitional (corollary of R14).
- **Plain claim:** For `j < k` and a position `o' + j` inside `x` (`o' + j < x.length`), byte `j`
  of the `k`-byte (truncated) read at `o'` after writing `src` at `o` is `src`'s byte
  `o' + j - o` when `o ≤ o' + j < o + src.length`, and otherwise `x`'s old (possibly `uninit`)
  byte.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Union.lean:149-153
theorem readWider_after_partial_write (x src : List AByte) (o o' k j : Nat) (hj : j < k)
    (hin : o' + j < x.length) :
    (seg (writeBytes x o src) o' k).getD j .uninit =
      if o ≤ o' + j ∧ o' + j < o + src.length then src.getD (o' + j - o) .uninit
      else x.getD (o' + j) .uninit
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hj : j < k` | the byte is inside the read | tight: a 1-byte read of a 2-byte value, byte `1` | `cex_readWider_hj` |
| `hin : o' + j < x.length` | the byte is inside the value | tight: the empty value | `cex_readWider_hin` |

- **Non-vacuity:** `nonvacuous_readWider` (both branches, with `hj` and `hin` holding).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R14b).
- **Design question:** The memory-level semantics of a partial write followed by a wider read,
  against which R15 and R16 compare register-level writes.

### R15 — The lane-wise blend of a partial write into a `union` register equals the memory write

- **Kind:** theorem. **Tier:** T0 (re-derivation: a lane-masked blend implements a partial write
  into a register that holds the whole value). **Depth:** shallow.
- **Plain claim:** For a `union` scalar of width at least `n` and a value `x` of length exactly
  `n`, lowering `x` to the register, blending `src` in at offset `o` lane by lane under the write
  mask (`mergeWrite`, defined by `laneSelect`, `writeMask`, `shiftIn` without reference to
  `writeBytes`), and raising gives exactly `writeBytes x o src`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Union.lean:178-181
theorem unionRegister_mergeWrite_eq_memoryWrite (p : Prim) (n : Nat) (hn : n ≤ p.size)
    (x src : List AByte) (o : Nat) (hx : x.length = n) :
    raise n (.scalar (.union p)) (.one (mergeWrite (lowerScalar (.union p) (seg x 0 p.size)) o src))
      = writeBytes x o src
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hn : n ≤ p.size` | the register covers the value | tight: a 1-byte register in a 2-byte value | `cex_mergeWrite_size_lt` |
| `hx : x.length = n` | the value has the type's size | tight: the empty value with a 1-byte register | `cex_mergeWrite_hx` |

- **Non-vacuity:** `nonvacuous_mergeWrite`.
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R15).
- **Design question:** How a partial write to a union kept in a register can be lowered (R15
  gives one lowering that equals the memory write).

### R16 — No constant fill makes a whole-register write refine a partial write

- **Kind:** impossibility. **Tier:** T0 (re-derivation: a constant fill overwrites the lanes a
  partial write leaves untouched). **Depth:** shallow.
- **Plain claim:** For every fill byte `fill`, there is a two-byte value `x` such that writing
  `bits 1` at offset `0` and reading both bytes as an integer is defined, and the same read after
  a whole-register write of width `2` that puts `fill` in the untouched lane is not at least as
  defined (`¬ OutLe`). (The first read is defined because `OutLe none _` always holds, so
  `¬ OutLe` forces it to be `some _`.)
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.

```lean
-- lean/ToyReprLower/Union.lean:196-199
theorem wholeRegisterWrite_no_constant_fill_refines_partial_write :
    ∀ fill : AByte, ∃ x : List AByte, x.length = 2 ∧
      ¬ OutLe (readInt 0 2 (writeBytes x 0 [.bits 1]))
          (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])))
```

- **Hypotheses:** none. **Non-vacuity:** not applicable (no hypotheses); the instance
  `wholeRegisterWrite_uninit_and_zero_fills_instance` shows the reads for `uninit` fill (UB) and
  `bits 0` fill (`[1, 0]` instead of `[1, 9]`).
- **Positive controls:** `wholeWrite_uninit_eq_writeBytes_of_untouched_uninit` (if every byte of
  `x` outside the write window is already `uninit`, the whole-register write with `uninit` fill
  equals the partial write; instance `wholeWrite_untouched_uninit_instance`) and
  `wholeWrite_eq_writeBytes_of_full_width` (a write at offset `0` covering every lane equals the
  partial write for any fill; instance `wholeWrite_full_width_instance`).
- **Escape hatches:** listed under **Boundaries → Escape hatches of the impossibility results** (R16).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R16).

Theorems cited by R16's non-claims (the non-claims are listed under **Boundaries**):

```lean
-- lean/ToyReprLower/Union.lean:366-371
theorem wholeWrite_init_fill_never_strictly_less_defined (fill : AByte) (hf : fill.isInit = true)
    (x : List AByte) :
    ¬ (OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])))
          (readInt 0 2 (writeBytes x 0 [.bits 1])) ∧
        readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 fill 0 [.bits 1])) ≠
          readInt 0 2 (writeBytes x 0 [.bits 1]))
```

```lean
-- lean/ToyReprLower/Union.lean:397-401
theorem wholeWrite_bits0_incomparable_with_partial :
    ¬ OutLe (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]))
        (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1]))) ∧
    ¬ OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1])))
        (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]))
```

```lean
-- lean/ToyReprLower/Union.lean:406-410
theorem wholeWrite_uninit_fill_strictly_less_defined_instance :
    OutLe (readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])))
        (readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1])) ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])) ≠
        readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1])
```

- **Design question:** Whether a partial write into a union kept in a register may be lowered as
  an overwrite of the whole register with a constant fill (by R16 it may not, outside the escape
  hatches).

### R17 — `noundef` on a `union` scalar argument introduces UB

- **Kind:** impossibility. **Tier:** T0 (the toy restatement of LLVM's documented `noundef`
  semantics; the correspondence is `derived (modeling bridge)`). **Depth:** definitional.
- **Plain claim:** For every primitive `p` of width at least `1`, the all-`uninit` byte list of
  width exactly `p.size`, lowered to a `union` scalar register, is passed without UB when the
  argument has no `noundef` attribute and is UB with `noundef`.
- **Model–system relation:** none proved.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis (connection to real systems):** derived (modeling bridge). The card's references to
  rustc, MiniRust, LLVM, the Rust Reference or CompCert (tier justification, prior art,
  non-claims, design question) cite documented behaviour or prior art quoted under "Modeling
  bridge to documented designs"; they are not kernel-checked.

```lean
-- lean/ToyReprLower/Union.lean:324-327
theorem noundef_on_union_scalar_introduces_ub (p : Prim) (hp : 1 ≤ p.size) :
    passArg false (lowerScalar (.union p) (List.replicate p.size .uninit)) =
        some (lowerScalar (.union p) (List.replicate p.size .uninit)) ∧
      passArg true (lowerScalar (.union p) (List.replicate p.size .uninit)) = none
```

| hypothesis | purpose | tightness | witness (class) |
| :--- | :--- | :--- | :--- |
| `hp : 1 ≤ p.size` | a lane exists | tight: width `0` (the value is empty and passes `noundef`) | `cex_noundef_width_zero` |

- **Positive control:** `noundef_passes_initialized_nonpoison` (a non-`poison` value lowered to an
  `initialized` register never trips `noundef`; instance `nonvacuous_noundef_initialized`).
- **Non-vacuity:** `nonvacuous_noundef_union`.
- **Escape hatches:** listed under **Boundaries → Escape hatches of the impossibility results** (R17).
- **Non-claims:** listed under **Boundaries → Non-claims of each result** (R17).
- **Prior art:** LLVM `noundef` attribute (pinned LangRef quote under "Modeling bridge to
  documented designs"; `derived (modeling bridge)`); formal treatments of `undef`/`poison` by
  Lee et al. and Alive2.
- **Design question:** Whether a backend may attach `noundef` to an argument whose type is lowered
  as a `union` scalar (it may not, unless every value is fully initialized).

### Auxiliary definitions and lemmas cited by name

Every package-local declaration mentioned by name above and not quoted there is quoted here.

```lean
-- lean/ToyReprLower/Examples.lean:10
def fullRange : List Nat → Bool := fun _ => true
```

```lean
-- lean/ToyReprLower/Examples.lean:13
def nonZeroRange : List Nat → Bool := fun ds => ds.any (· != 0)
```

```lean
-- lean/ToyReprLower/Examples.lean:17
def len2Range : List Nat → Bool := fun ds => ds.length == 2
```

```lean
-- lean/ToyReprLower/Lowering.lean:103-107
theorem scalar_bytesLe_roundTrip_iff (n : Nat) (s : Scalar) (x : List AByte) (hx : x.length = n) :
    BytesLe x (raise n (.scalar s) (lower (.scalar s) x)) ↔
      (∀ i, i < n → (BRepr.scalar s).inExtent i = false → x.getD i .uninit = .uninit) ∧
      (initUniformAt s (seg x 0 s.size) && rangeInclAt s (seg x 0 s.size) &&
        provCoherentAt s (seg x 0 s.size)) = true
```

```lean
-- lean/ToyReprLower/Lowering.lean:161-164
theorem scalar_conditions_of_roundTrip_refines (n : Nat) (s : Scalar) (V : List AByte → Prop)
    (h : RoundTripRefines n (.scalar s) V) :
    OutsideExtentsUninit n (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V
```

```lean
-- lean/ToyReprLower/Lowering.lean:172-179
theorem pair_bytesLe_roundTrip_iff (n : Nat) (a b : Scalar) (o : Nat) (x : List AByte)
    (hx : x.length = n) (hab : a.size ≤ o) :
    BytesLe x (raise n (.pair a b o) (lower (.pair a b o) x)) ↔
      (∀ i, i < n → (BRepr.pair a b o).inExtent i = false → x.getD i .uninit = .uninit) ∧
      (initUniformAt a (seg x 0 a.size) && rangeInclAt a (seg x 0 a.size) &&
        provCoherentAt a (seg x 0 a.size)) = true ∧
      (initUniformAt b (seg x o b.size) && rangeInclAt b (seg x o b.size) &&
        provCoherentAt b (seg x o b.size)) = true
```

```lean
-- lean/ToyReprLower/Lowering.lean:251-255
theorem pair_roundTrip_refines_of_conditions (n : Nat) (a b : Scalar) (bOff : Nat)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n)
    (ha : OutsideExtentsUninit n (.pair a b bOff) V) (hb : InitUniform (.pair a b bOff) V)
    (hd : RangeIncl (.pair a b bOff) V) (hc : ProvCoherent (.pair a b bOff) V) :
    RoundTripRefines n (.pair a b bOff) V
```

```lean
-- lean/ToyReprLower/Lowering.lean:300-303
theorem pair_conditions_of_roundTrip_refines (n : Nat) (a b : Scalar) (bOff : Nat)
    (V : List AByte → Prop) (hab : a.size ≤ bOff) (h : RoundTripRefines n (.pair a b bOff) V) :
    OutsideExtentsUninit n (.pair a b bOff) V ∧ InitUniform (.pair a b bOff) V ∧
      RangeIncl (.pair a b bOff) V ∧ ProvCoherent (.pair a b bOff) V
```

```lean
-- lean/ToyReprLower/Reinterpret.lean:386-388
theorem regCast_scalar_agrees_of_disciplineCompat (n : Nat) (s t : Scalar)
    (hw : s.size = t.size) (hn : s.size ≤ n) (hc : DisciplineCompat s t) :
    CastAgrees n (.scalar s) (.scalar t)
```

```lean
-- lean/ToyReprLower/Reinterpret.lean:413-414
theorem raise_lower_bytesLe_self (t : Scalar) (bs : List AByte) (h : bs.length = t.size) :
    BytesLe (raiseScalar t (lowerScalar t bs)) bs
```

```lean
-- lean/ToyReprLower/Reinterpret.lean:863-866
theorem regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen (n : Nat) (a b a' b' : Scalar)
    (bOff : Nat) (hwa : a.size = a'.size) (hwb : b.size = b'.size) (hab : a.size ≤ bOff)
    (hca : DisciplineCompatAnyLen a a') (hcb : DisciplineCompatAnyLen b b') :
    CastAgrees n (.pair a b bOff) (.pair a' b' bOff)
```

```lean
-- lean/ToyReprLower/Union.lean:224-226
theorem wholeWrite_uninit_eq_writeBytes_of_untouched_uninit (x src : List AByte) (o : Nat)
    (h : ∀ i, i < x.length → ¬ (o ≤ i ∧ i < o + src.length) → x.getD i .uninit = .uninit) :
    raiseScalar (.union (.int x.length)) (wholeWrite x.length .uninit o src) = writeBytes x o src
```

```lean
-- lean/ToyReprLower/Union.lean:240-242
theorem wholeWrite_eq_writeBytes_of_full_width (x src : List AByte) (fill : AByte)
    (hsrc : x.length ≤ src.length) :
    raiseScalar (.union (.int x.length)) (wholeWrite x.length fill 0 src) = writeBytes x 0 src
```

```lean
-- lean/ToyReprLower/Union.lean:251-252
def nonZeroU8Field : UField :=
  ⟨0, 1, fun bs => match bs with | [b] => b.isInit && b.data != 0 | _ => false⟩
```

```lean
-- lean/ToyReprLower/Union.lean:258
def nzOrU8 : UnionTy := ⟨1, [nonZeroU8Field, u8Field]⟩
```

```lean
-- lean/ToyReprLower/Union.lean:277
def neverUnion : UnionTy := ⟨1, [⟨0, 1, fun _ => false⟩]⟩
```

```lean
-- lean/ToyReprLower/Union.lean:334-335
theorem passArg_noundef_union_eq_none_iff (p : Prim) (x : List AByte) :
    passArg true (lowerScalar (.union p) x) = none ↔ allInit x = false
```

```lean
-- lean/ToyReprLower/Union.lean:349-351
theorem noundef_passes_initialized_nonpoison (q : Prim) (r : List Nat → Bool) (bs : List AByte)
    (h : lowerScalar (.initialized q r) bs ≠ .poison) :
    passArg true (lowerScalar (.initialized q r) bs) = some (lowerScalar (.initialized q r) bs)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:19-26
theorem cex_scalar_padding_carries_bytes :
    let s : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .bits 9])
    (∀ x, V x → x.length = 2) ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ OutsideExtentsUninit 2 (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readInt 1 1 [.bits 7, .bits 9] = some (.int [9]) ∧
      readInt 1 1 (raise 2 (.scalar s) (lower (.scalar s) [.bits 7, .bits 9])) = none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:35-42
theorem cex_scalar_partial_init :
    let s : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .uninit])
    (∀ x, V x → x.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ InitUniform (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readInt 0 1 [.bits 7, .uninit] = some (.int [7]) ∧
      readInt 0 1 (raise 2 (.scalar s) (lower (.scalar s) [.bits 7, .uninit])) = none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:50-57
theorem cex_scalar_out_of_range :
    let s : Scalar := .initialized (.int 1) nonZeroRange
    let V : List AByte → Prop := (· = [.bits 0])
    (∀ x, V x → x.length = 1) ∧ OutsideExtentsUninit 1 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ RangeIncl (.scalar s) V ∧ ¬ RoundTripRefines 1 (.scalar s) V ∧
      readInt 0 1 [.bits 0] = some (.int [0]) ∧
      readInt 0 1 (raise 1 (.scalar s) (lower (.scalar s) [.bits 0])) = none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:66-75
theorem cex_scalar_frags_under_int :
    let s : Scalar := .initialized (.int 2) fullRange
    let x : List AByte := [.ptrFrag 1 7 0, .ptrFrag 2 7 1]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ RangeIncl (.scalar s) V ∧
      ¬ ProvCoherent (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      readPtr 0 2 x = some (.ptr (some 7) [1, 2]) ∧
      readPtr 0 2 (raise 2 (.scalar s) (lower (.scalar s) x)) = some (.ptr none [1, 2]) ∧
      ¬ OutLe (readPtr 0 2 x) (readPtr 0 2 (raise 2 (.scalar s) (lower (.scalar s) x)))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:83-90
theorem cex_scalar_mixed_provenance_ptr :
    let s : Scalar := .initialized (.ptr 2) fullRange
    let x : List AByte := [.ptrFrag 1 7 0, .ptrFrag 2 8 1]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 2) ∧ OutsideExtentsUninit 2 (.scalar s) V ∧
      InitUniform (.scalar s) V ∧ RangeIncl (.scalar s) V ∧
      ¬ ProvCoherent (.scalar s) V ∧ ¬ RoundTripRefines 2 (.scalar s) V ∧
      raise 2 (.scalar s) (lower (.scalar s) x) = [.bits 1, .bits 2]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:99-105
theorem cex_scalar_hlen :
    let s : Scalar := .union (.int 1)
    let V : List AByte → Prop := (· = [])
    ¬ (∀ x, V x → x.length = 1) ∧
      OutsideExtentsUninit 1 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      ¬ RoundTripRefines 1 (.scalar s) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:116-126
theorem cex_pair_ptr_split_across_boundary :
    let a : Scalar := .initialized (.ptr 2) fullRange
    let x : List AByte := [.bits 0, .ptrFrag 1 7 0, .ptrFrag 2 7 1, .bits 3]
    let V : List AByte → Prop := (· = x)
    (∀ y, V y → y.length = 4) ∧ a.size ≤ 2 ∧
      OutsideExtentsUninit 4 (.pair a a 2) V ∧ InitUniform (.pair a a 2) V ∧
      RangeIncl (.pair a a 2) V ∧ ¬ ProvCoherent (.pair a a 2) V ∧
      ¬ RoundTripRefines 4 (.pair a a 2) V ∧
      readPtr 1 2 x = some (.ptr (some 7) [1, 2]) ∧
      readPtr 1 2 (raise 4 (.pair a a 2) (lower (.pair a a 2) x)) = some (.ptr none [1, 2]) ∧
      ¬ OutLe (readPtr 1 2 x) (readPtr 1 2 (raise 4 (.pair a a 2) (lower (.pair a a 2) x)))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:134-139
theorem cex_pair_padding_carries_bytes :
    let a : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 1, .bits 9, .bits 2])
    (∀ y, V y → y.length = 3) ∧ a.size ≤ 2 ∧
      InitUniform (.pair a a 2) V ∧ RangeIncl (.pair a a 2) V ∧ ProvCoherent (.pair a a 2) V ∧
      ¬ OutsideExtentsUninit 3 (.pair a a 2) V ∧ ¬ RoundTripRefines 3 (.pair a a 2) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:147-154
theorem cex_pair_partial_init :
    let a : Scalar := .initialized (.int 2) fullRange
    let b : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 7, .uninit, .bits 1])
    (∀ y, V y → y.length = 3) ∧ a.size ≤ 2 ∧
      OutsideExtentsUninit 3 (.pair a b 2) V ∧ RangeIncl (.pair a b 2) V ∧
      ProvCoherent (.pair a b 2) V ∧
      ¬ InitUniform (.pair a b 2) V ∧ ¬ RoundTripRefines 3 (.pair a b 2) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:161-168
theorem cex_pair_out_of_range :
    let a : Scalar := .initialized (.int 1) nonZeroRange
    let b : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.bits 0, .bits 1])
    (∀ y, V y → y.length = 2) ∧ a.size ≤ 1 ∧
      OutsideExtentsUninit 2 (.pair a b 1) V ∧ InitUniform (.pair a b 1) V ∧
      ProvCoherent (.pair a b 1) V ∧
      ¬ RangeIncl (.pair a b 1) V ∧ ¬ RoundTripRefines 2 (.pair a b 1) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:175-180
theorem cex_pair_hlen :
    let a : Scalar := .union (.int 1)
    let V : List AByte → Prop := (· = [])
    ¬ (∀ x, V x → x.length = 2) ∧ a.size ≤ 1 ∧ OutsideExtentsUninit 2 (.pair a a 1) V ∧
      InitUniform (.pair a a 1) V ∧ RangeIncl (.pair a a 1) V ∧ ProvCoherent (.pair a a 1) V ∧
      ¬ RoundTripRefines 2 (.pair a a 1) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:189-194
theorem cex_pair_overlap :
    let a : Scalar := .initialized (.ptr 2) fullRange
    let b : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop := (· = [.ptrFrag 0 7 0, .ptrFrag 1 7 1, .bits 7])
    (∀ y, V y → y.length = 3) ∧ ¬ a.size ≤ 1 ∧
      RoundTripRefines 3 (.pair a b 1) V ∧ ¬ ProvCoherent (.pair a b 1) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:204-206
theorem cex_union_size_lt :
    (∀ x, (· = [AByte.bits 7, .bits 9]) x → x.length = 2) ∧ ¬ 2 ≤ (Prim.int 1).size ∧
      ¬ RoundTripRefines 2 (.scalar (.union (.int 1))) (· = [.bits 7, .bits 9])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:213-215
theorem cex_union_covers_value_hlen :
    1 ≤ (Prim.int 1).size ∧ ¬ (∀ x, (· = ([] : List AByte)) x → x.length = 1) ∧
      ¬ RoundTripRefines 1 (.scalar (.union (.int 1))) (· = [])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:253-258
theorem nonvacuous_initialized_lowering_union_value :
    1 ≤ (Prim.int 1).size ∧
      RoundTripRefines (Prim.int 1).size (.scalar (.union (.int 1)))
        (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 1).size - 1) .uninit) ∧
      ¬ RoundTripRefines (Prim.int 1).size (.scalar (.initialized (.int 1) fullRange))
        (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 1).size - 1) .uninit)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:263-264
theorem initialized_lowering_refines_plain_in_range_value :
    RoundTripRefines 1 (.scalar (.initialized (.int 1) nonZeroRange)) (· = [.bits 5])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:271-277
theorem cex_initialized_lowering_width_zero (rng : List Nat → Bool) :
    ¬ (RoundTripRefines (Prim.int 0).size (.scalar (.union (.int 0)))
          (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 0).size - 1) .uninit) ∧
        ¬ RoundTripRefines (Prim.int 0).size (.scalar (.initialized (.int 0) rng))
          (· = .ptrFrag 0 0 1 :: List.replicate ((Prim.int 0).size - 1) .uninit)) ∧
      ∀ V : List AByte → Prop, (∀ x, V x → x.length = 0) →
        RoundTripRefines 0 (.scalar (.initialized (.int 0) rng)) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:290-291
theorem provenanceStripping_register_not_refines :
    ¬ BytesLe [.ptrFrag 1 7 0] (stripProv [.ptrFrag 1 7 0])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:298-304
theorem cex_regCast_scalar_width_mismatch :
    (Scalar.initialized (.int 1) fullRange).size ≠ (Scalar.initialized (.int 2) fullRange).size ∧
      1 ≤ (Scalar.initialized (.int 1) fullRange).size ∧
      (Scalar.initialized (.int 1) fullRange).size ≤ 2 ∧
      DisciplineCompat (.initialized (.int 1) fullRange) (.initialized (.int 2) fullRange) ∧
      ¬ CastAgrees 2 (.scalar (.initialized (.int 1) fullRange))
        (.scalar (.initialized (.int 2) fullRange))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:312-316
theorem cex_regCast_scalar_width_zero :
    (Scalar.union (.int 0)).size = (Scalar.initialized (.int 0) fullRange).size ∧
      ¬ 1 ≤ (Scalar.union (.int 0)).size ∧ (Scalar.union (.int 0)).size ≤ 1 ∧
      CastAgrees 1 (.scalar (.union (.int 0))) (.scalar (.initialized (.int 0) fullRange)) ∧
      ¬ DisciplineCompat (.union (.int 0)) (.initialized (.int 0) fullRange)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:325-329
theorem cex_regCast_scalar_hn_length_indep :
    let s : Scalar := .initialized (.int 1) fullRange
    let t : Scalar := .initialized (.int 1) nonZeroRange
    s.size = t.size ∧ 1 ≤ s.size ∧ ¬ s.size ≤ 0 ∧
      CastAgrees 0 (.scalar s) (.scalar t) ∧ ¬ DisciplineCompat s t
```

```lean
-- lean/ToyReprLower/Witnesses.lean:339-345
theorem cex_regCast_scalar_wider_than_value :
    (Scalar.initialized (.int 2) fullRange).size = (Scalar.initialized (.int 2) len2Range).size ∧
      1 ≤ (Scalar.initialized (.int 2) fullRange).size ∧
      ¬ (Scalar.initialized (.int 2) fullRange).size ≤ 1 ∧
      DisciplineCompat (.initialized (.int 2) fullRange) (.initialized (.int 2) len2Range) ∧
      ¬ CastAgrees 1 (.scalar (.initialized (.int 2) fullRange))
        (.scalar (.initialized (.int 2) len2Range))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:370-376
theorem regCastStrip_width1_union_to_initialized_agrees :
    let s : Scalar := .union (.int 1)
    let t : Scalar := .initialized (.int 1) fullRange
    (∀ x : List AByte, x.length = 1 →
      raise 1 (.scalar t) (.one (regCastScalarStrip s t (lowerScalar s (seg x 0 s.size)))) =
        raise 1 (.scalar t) (lower (.scalar t) (raise 1 (.scalar s) (lower (.scalar s) x)))) ∧
    ¬ DisciplineCompat s t
```

```lean
-- lean/ToyReprLower/Witnesses.lean:383-387
theorem regCast_union_to_initialized_refines_not_agrees :
    let s : Scalar := .union (.int 1)
    let t : Scalar := .initialized (.int 1) fullRange
    s.size = t.size ∧ s.size ≤ 1 ∧ ¬ DisciplineCompat s t ∧
      CastRefines 1 (.scalar s) (.scalar t) ∧ ¬ CastAgrees 1 (.scalar s) (.scalar t)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:397-400
theorem cex_regCast_pair_offset_mismatch :
    let a : Scalar := .initialized (.int 1) fullRange
    a.size = a.size ∧ a.size ≤ 1 ∧ a.size ≤ 2 ∧ 1 + a.size ≤ 3 ∧ 2 + a.size ≤ 3 ∧
      DisciplineCompat a a ∧ ¬ CastAgrees 3 (.pair a a 1) (.pair a a 2)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:412-415
theorem regCast_pair_agrees_despite_offset_mismatch_of_empty_range :
    let a : Scalar := .initialized (.int 1) fullRange
    let e : Scalar := .initialized (.int 1) emptyRange
    CastAgrees 3 (.pair a e 1) (.pair a a 2)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:422-426
theorem cex_regCast_pair_discipline :
    let u : Scalar := .union (.int 1)
    let i : Scalar := .initialized (.int 1) fullRange
    u.size = i.size ∧ i.size = i.size ∧ u.size ≤ 1 ∧ 1 + i.size ≤ 2 ∧ DisciplineCompat i i ∧
      ¬ DisciplineCompat u i ∧ ¬ CastAgrees 2 (.pair u i 1) (.pair i i 1)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:433-437
theorem cex_regCast_pair_discipline_b :
    let u : Scalar := .union (.int 1)
    let i : Scalar := .initialized (.int 1) fullRange
    i.size = i.size ∧ u.size = i.size ∧ i.size ≤ 1 ∧ 1 + u.size ≤ 2 ∧ DisciplineCompat i i ∧
      ¬ DisciplineCompat u i ∧ ¬ CastAgrees 2 (.pair i u 1) (.pair i i 1)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:445-449
theorem cex_regCast_pair_overlap :
    let a : Scalar := .initialized (.int 2) fullRange
    let b : Scalar := .initialized (.ptr 2) fullRange
    a.size = a.size ∧ b.size = b.size ∧ DisciplineCompat a a ∧ DisciplineCompat b b ∧
      ¬ a.size ≤ 1 ∧ 1 + b.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a b 1) (.pair a b 1)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:457-462
theorem cex_regCast_pair_out_of_bounds :
    let a : Scalar := .initialized (.int 1) fullRange
    let b : Scalar := .initialized (.int 2) fullRange
    let b' : Scalar := .initialized (.int 2) len2Range
    a.size = a.size ∧ b.size = b'.size ∧ DisciplineCompat a a ∧ DisciplineCompat b b' ∧
      a.size ≤ 1 ∧ ¬ 1 + b.size ≤ 2 ∧ ¬ CastAgrees 2 (.pair a b 1) (.pair a b' 1)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:470-474
theorem cex_regCast_pair_width_mismatch :
    let a : Scalar := .initialized (.int 1) fullRange
    let a' : Scalar := .initialized (.int 2) fullRange
    a.size ≠ a'.size ∧ a.size = a.size ∧ DisciplineCompat a a' ∧ DisciplineCompat a a ∧
      a.size ≤ 2 ∧ 2 + a.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a a 2) (.pair a' a 2)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:481-485
theorem cex_regCast_pair_width_mismatch_b :
    let a : Scalar := .initialized (.int 1) fullRange
    let b' : Scalar := .initialized (.int 2) fullRange
    a.size = a.size ∧ a.size ≠ b'.size ∧ DisciplineCompat a a ∧ DisciplineCompat a b' ∧
      a.size ≤ 1 ∧ 1 + a.size ≤ 3 ∧ ¬ CastAgrees 3 (.pair a a 1) (.pair a b' 1)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:512-515
theorem regCast_pair_to_union_scalar_agrees_no_padding_instance :
    let a : Scalar := .initialized (.int 1) fullRange
    (Prim.int 2).size = a.size + a.size ∧ a.size + a.size ≤ 2 ∧
      CastAgrees 2 (.pair a a a.size) (.scalar (.union (.int 2)))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:522-524
def attachProvCast (p : Nat) : RVal → RVal
  | .int ds => .ptr (some p) ds
  | v => v
```

```lean
-- lean/ToyReprLower/Witnesses.lean:542
theorem bytesLe_bits_ptrFrag_attach : BytesLe [.bits 5] [.ptrFrag 5 7 0]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:549-553
theorem nonvacuous_unionMove_readField :
    [AByte.bits 0].length = nzOrU8.size ∧
      unionMove trivialUnionValidity nzOrU8 [.bits 0] = some [.bits 0] ∧
      readField nonZeroU8Field [.bits 0] = none ∧
      nonZeroU8Field.valid (seg [.bits 0] nonZeroU8Field.off nonZeroU8Field.size) = false
```

```lean
-- lean/ToyReprLower/Witnesses.lean:559-563
theorem nonvacuous_unreachableRewrite_iff :
    (fun _ => true : UnionTy → Bool) neverUnion = true ∧
      (∀ x : List AByte, x.length = neverUnion.size → emptyUnionValidity neverUnion x = false) ∧
      ¬ (∀ x : List AByte, x.length = neverUnion.size →
        trivialUnionValidity neverUnion x = false)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:571-578
theorem cex_unreachableRewrite_gate_false :
    (fun _ => false : UnionTy → Bool) neverUnion ≠ true ∧
      (∀ x : List AByte, x.length = neverUnion.size →
        OutLe (moveThenRet trivialUnionValidity neverUnion x)
          (gatedUnreachable ((fun _ => false : UnionTy → Bool) neverUnion)
            (moveThenRet trivialUnionValidity neverUnion x))) ∧
      ¬ (∀ x : List AByte, x.length = neverUnion.size →
        trivialUnionValidity neverUnion x = false)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:588-589
theorem nonvacuous_fieldwiseGate :
    ∀ u, FieldwiseUninhabited u → (fun _ => true : UnionTy → Bool) u = true
```

```lean
-- lean/ToyReprLower/Witnesses.lean:595-599
theorem cex_fieldwiseGate_never_fires :
    ¬ (∀ u, FieldwiseUninhabited u → (fun _ => false : UnionTy → Bool) u = true) ∧
      OutLe (moveThenRet trivialUnionValidity neverUnion [.uninit])
        (gatedUnreachable ((fun _ => false : UnionTy → Bool) neverUnion)
          (moveThenRet trivialUnionValidity neverUnion [.uninit]))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:611-614
theorem gate_refines_of_emptyValidity (gate : UnionTy → Bool) (hgate : gate neverUnion = true) :
    ∀ x : List AByte, x.length = neverUnion.size →
      OutLe (moveThenRet emptyUnionValidity neverUnion x)
        (gatedUnreachable (gate neverUnion) (moveThenRet emptyUnionValidity neverUnion x))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:620-623
theorem cex_noundef_width_zero :
    ¬ 1 ≤ (Prim.int 0).size ∧
      passArg true (lowerScalar (.union (.int 0)) (List.replicate (Prim.int 0).size .uninit)) ≠
        none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:629-635
theorem initialized_allUninit_roundTrips_but_noundef_ub :
    let s : Scalar := .initialized (.int 1) fullRange
    let V : List AByte → Prop := (· = [.uninit])
    (∀ x, V x → x.length = 1) ∧ RoundTripRefines 1 (.scalar s) V ∧
      OutsideExtentsUninit 1 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V ∧
      lowerScalar s [.uninit] = .poison ∧ passArg true (lowerScalar s [.uninit]) = none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:642-643
theorem cex_typedReads_without_bytesLe :
    ¬ BytesLe [.bits 1] [.uninit] ∧ ¬ OutLe (readInt 0 1 [.bits 1]) (readInt 0 1 [.uninit])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:649-652
theorem typedReads_agree_without_bytesLe :
    (∀ off w : Nat, readInt off w [.ptrFrag 1 7 1] = readInt off w [.bits 1] ∧
      readPtr off w [.ptrFrag 1 7 1] = readPtr off w [.bits 1]) ∧
      ¬ BytesLe [.ptrFrag 1 7 1] [.bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:663-664
theorem readInt_readPtr_width_zero (off : Nat) (x : List AByte) :
    readInt off 0 x = some (.int []) ∧ readPtr off 0 x = some (.ptr none [])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:672-677
theorem nonvacuous_scalar_roundTrip :
    let s : Scalar := .initialized (.ptr 2) fullRange
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1, .uninit])
    (∀ x, V x → x.length = 3) ∧ RoundTripRefines 3 (.scalar s) V ∧
      OutsideExtentsUninit 3 (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:683-690
theorem nonvacuous_pair_roundTrip :
    let a : Scalar := .initialized (.ptr 2) nonZeroRange
    let b : Scalar := .initialized (.int 2) fullRange
    let V : List AByte → Prop :=
      (· = [.ptrFrag 1 7 0, .ptrFrag 2 7 1, .uninit, .bits 3, .bits 0])
    (∀ x, V x → x.length = 5) ∧ a.size ≤ 3 ∧
      RoundTripRefines 5 (.pair a b 3) V ∧ OutsideExtentsUninit 5 (.pair a b 3) V ∧
      InitUniform (.pair a b 3) V ∧ RangeIncl (.pair a b 3) V ∧ ProvCoherent (.pair a b 3) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:696-700
theorem nonvacuous_union_roundTrip :
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .uninit, .bits 4, .uninit])
    (∀ x, V x → x.length = 4) ∧
      RoundTripRefines 4 (.scalar (.union (.int 3))) V ∧
      OutsideExtentsUninit 4 (.scalar (.union (.int 3))) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:705-708
theorem nonvacuous_union_covers_value :
    let V : List AByte → Prop := (· = [.ptrFrag 1 7 0, .uninit, .bits 4])
    (∀ x, V x → x.length = 3) ∧ 3 ≤ (Prim.int 3).size ∧
      RoundTripRefines 3 (.scalar (.union (.int 3))) V
```

```lean
-- lean/ToyReprLower/Witnesses.lean:712
theorem nonvacuous_typedReads_mono : BytesLe [.uninit, .bits 1] [.bits 0, .ptrFrag 1 7 0]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:717-721
theorem nonvacuous_regCast_scalar :
    let s : Scalar := .initialized (.ptr 2) nonZeroRange
    let t : Scalar := .initialized (.int 2) fullRange
    s.size = t.size ∧ 1 ≤ s.size ∧ s.size ≤ 2 ∧ DisciplineCompat s t ∧
      CastAgrees 2 (.scalar s) (.scalar t)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:729-731
theorem regCast_int_to_ptr_agrees :
    CastAgrees 2 (.scalar (.initialized (.int 2) fullRange))
      (.scalar (.initialized (.ptr 2) fullRange))
```

```lean
-- lean/ToyReprLower/Witnesses.lean:737-744
theorem nonvacuous_regCast_pair :
    let a : Scalar := .initialized (.ptr 2) nonZeroRange
    let b : Scalar := .initialized (.int 2) fullRange
    let a' : Scalar := .initialized (.int 2) fullRange
    let b' : Scalar := .union (.int 2)
    a.size = a'.size ∧ b.size = b'.size ∧ a.size ≤ 2 ∧ 2 + b.size ≤ 4 ∧
      DisciplineCompat a a' ∧ DisciplineCompat b b' ∧
      CastAgrees 4 (.pair a b 2) (.pair a' b' 2)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:770-772
theorem nonvacuous_writeBytes_frame :
    writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1] = [.bits 7, .bits 1, .bits 9] ∧
      writeBytes [.bits 7] 0 [.bits 1, .bits 2] = [.bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:778-782
theorem nonvacuous_readWider :
    (1 : Nat) < 3 ∧ 0 + 1 < [AByte.bits 7, .uninit, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1]) 0 3).getD 1 .uninit = .bits 1 ∧
      (2 : Nat) < 3 ∧ 0 + 2 < [AByte.bits 7, .uninit, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .uninit, .bits 9] 1 [.bits 1]) 0 3).getD 2 .uninit = .bits 9
```

```lean
-- lean/ToyReprLower/Witnesses.lean:786-790
theorem cex_readWider_hj :
    ¬ (1 : Nat) < 1 ∧ (0 : Nat) + 1 < [AByte.bits 7, .bits 9].length ∧
      (seg (writeBytes [.bits 7, .bits 9] 0 [.bits 1]) 0 1).getD 1 .uninit ≠
        (if 0 ≤ 0 + 1 ∧ 0 + 1 < 0 + [AByte.bits 1].length then [AByte.bits 1].getD (0 + 1 - 0) .uninit
          else [AByte.bits 7, .bits 9].getD (0 + 1) .uninit)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:794-798
theorem cex_readWider_hin :
    (0 : Nat) < 1 ∧ ¬ (0 : Nat) + 0 < ([] : List AByte).length ∧
      (seg (writeBytes [] 0 [AByte.bits 1]) 0 1).getD 0 .uninit ≠
        (if 0 ≤ 0 + 0 ∧ 0 + 0 < 0 + [AByte.bits 1].length then [AByte.bits 1].getD (0 + 0 - 0) .uninit
          else ([] : List AByte).getD (0 + 0) .uninit)
```

```lean
-- lean/ToyReprLower/Witnesses.lean:803-807
theorem nonvacuous_mergeWrite :
    2 ≤ (Prim.int 2).size ∧ [AByte.bits 7, .uninit].length = 2 ∧
      raise 2 (.scalar (.union (.int 2)))
          (.one (mergeWrite (lowerScalar (.union (.int 2)) (seg [.bits 7, .uninit] 0 2)) 1 [.bits 1]))
        = [.bits 7, .bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:812-816
theorem cex_mergeWrite_size_lt :
    ¬ 2 ≤ (Prim.int 1).size ∧ [AByte.bits 7, .bits 9].length = 2 ∧
      raise 2 (.scalar (.union (.int 1)))
          (.one (mergeWrite (lowerScalar (.union (.int 1)) (seg [.bits 7, .bits 9] 0 1)) 0 [.bits 1]))
        ≠ writeBytes [.bits 7, .bits 9] 0 [.bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:820-824
theorem cex_mergeWrite_hx :
    1 ≤ (Prim.int 1).size ∧ ([] : List AByte).length ≠ 1 ∧
      raise 1 (.scalar (.union (.int 1)))
          (.one (mergeWrite (lowerScalar (.union (.int 1)) (seg [] 0 1)) 0 [.bits 1]))
        ≠ writeBytes [] 0 [.bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:828-829
theorem nonvacuous_memory_roundTrip :
    RoundTripRefines 2 .memory (· = [.ptrFrag 1 7 0, .uninit])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:836-840
theorem wholeRegisterWrite_uninit_and_zero_fills_instance :
    readInt 0 2 (writeBytes [.bits 7, .bits 9] 0 [.bits 1]) = some (.int [1, 9]) ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1])) = none ∧
    readInt 0 2 (raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1])) =
      some (.int [1, 0])
```

```lean
-- lean/ToyReprLower/Witnesses.lean:845-847
theorem wholeWrite_untouched_uninit_instance :
    raiseScalar (.union (.int 2)) (wholeWrite 2 .uninit 0 [.bits 1]) =
      writeBytes [.bits 7, .uninit] 0 [.bits 1]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:852-854
theorem wholeWrite_full_width_instance :
    raiseScalar (.union (.int 2)) (wholeWrite 2 (.bits 0) 0 [.bits 1, .bits 2]) =
      writeBytes [.bits 7, .bits 9] 0 [.bits 1, .bits 2]
```

```lean
-- lean/ToyReprLower/Witnesses.lean:858-863
theorem nonvacuous_noundef_union :
    1 ≤ (Prim.int 1).size ∧
      passArg false (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) =
        some (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) ∧
      passArg true (lowerScalar (.union (.int 1)) (List.replicate (Prim.int 1).size .uninit)) =
        none
```

```lean
-- lean/ToyReprLower/Witnesses.lean:867-870
theorem nonvacuous_noundef_initialized :
    lowerScalar (.initialized (.int 1) fullRange) [.bits 1] ≠ .poison ∧
      passArg true (lowerScalar (.initialized (.int 1) fullRange) [.bits 1]) =
        some (lowerScalar (.initialized (.int 1) fullRange) [.bits 1])
```

```lean
-- lean/ToyReprLower/Union.lean:255-255
def u8Field : UField := ⟨0, 1, fun bs => match bs with | [b] => b.isInit | _ => false⟩
```

```lean
-- lean/ToyReprLower/Witnesses.lean:285-286
def stripProv (bs : List AByte) : List AByte :=
  bs.map fun b => match b with | .ptrFrag d _ _ => .bits d | b => b
```

```lean
-- lean/ToyReprLower/Witnesses.lean:353-364
def regCastScalarStrip (s t : Scalar) (v : RVal) : RVal :=
  match t with
  | .union _ => .raw (raiseScalar s v)
  | .initialized q _ =>
    match v, q with
    | .poison, _ => .poison
    | .int ds, .int _ => .int ds
    | .int ds, .ptr _ => .ptr none ds
    | .ptr _ ds, .int _ => .int ds
    | .ptr pr ds, .ptr _ => .ptr pr ds
    | .raw bs, .int _ => .raw (stripProv bs)
    | .raw bs, .ptr _ => .raw bs
```

```lean
-- lean/ToyReprLower/Witnesses.lean:407-407
def emptyRange : List Nat → Bool := fun _ => false
```

### Modeling bridge to documented designs

Every paragraph in this subsection is `Basis: derived (modeling bridge)`: it quotes documented
behaviour of a real system at a pinned revision and states which toy definition is meant to
capture it. None of it is kernel-checked, and none of it describes a defect in the quoted
software.

rustc quotes are from `rust-lang/rust` at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`;
MiniRust quotes from `minirust/minirust` at commit `063d784186d3252bee242217f218223205c0b568`;
LLVM quotes from `llvm/llvm-project` at commit `a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6`
(`llvm/docs/LangRef.md`); Rust Reference quotes from `rust-lang/reference` at commit
`bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`. Retrieved 2026-11-21.

#### rustc (`derived (modeling bridge)`, documentation)

`compiler/rustc_abi/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1515-1535` (`Scalar`):

```rust
/// Information about one scalar component of a Rust type.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "nightly", derive(StableHash))]
pub enum Scalar {
    Initialized {
        value: Primitive,

        // FIXME(eddyb) always use the shortest range, e.g., by finding
        // the largest space between two consecutive valid values and
        // taking everything else as the (shortest) valid range.
        valid_range: WrappingRange,
    },
    Union {
        /// Even for unions, we need to use the correct registers for the kind of
        /// values inside the union, so we keep the `Primitive` type around. We
        /// also use it to compute the size of the scalar.
        /// However, unions never have niches and even allow undef,
        /// so there is no `valid_range`.
        value: Primitive,
    },
}
```

`compiler/rustc_abi/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1779-1788` (`BackendRepr` docs; not a calling-convention promise):

```rust
/// The way we represent values to the backend
///
/// Previously this was conflated with the "ABI" a type is given, as in the platform-specific ABI.
/// In reality, this implies little about that, but is mostly used to describe the syntactic form
/// emitted for the backend, as most backends handle SSA values and blobs of memory differently.
/// The psABI may need consideration in doing so, but this enum does not constitute a promise for
/// how the value will be lowered to the calling convention, in itself.
///
/// Generally, a codegen backend will prefer to handle smaller values as a scalar or short vector,
/// and larger values will usually prefer to be represented as memory.
```

`compiler/rustc_abi/src/lib.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1793-1805` (`ScalarPair`):

```rust
    /// The data contained in this type can be entirely represented by two scalars.
    /// The two scalars are listed in *memory* order, so `a` is at offset zero
    /// and `b` is at non-zero offset `b_offset`.
    /// These need not be `FieldIdx(0)` and `FieldIdx(1)`.
    ///
    /// As of June 2026 the `b_offset` is always the size of the `a`
    /// scalar rounded up to the platform alignment of the `b` scalar.
    /// That may soon change, however; see MCP#1007.
    ScalarPair {
        a: Scalar,
        b: Scalar,
        b_offset: Size,
    },
```

`compiler/rustc_middle/src/mir/syntax.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:328-335` (`Assign` overlap note; it cites rust-lang/rust#68364, an open discussion, and is not relied on):

```rust
    /// **Needs clarification**: We currently require that the LHS place not overlap with any place
    /// read as part of computation of the RHS for some rvalues. This requirement is under
    /// discussion in [#68364]. Specifically, overlap is permitted only for assignments of a type
    /// with `BackendRepr::Scalar | BackendRepr::ScalarPair` where all the scalar fields are
    /// [`Scalar::Initialized`][rustc_abi::Scalar::Initialized]. As a part of this discussion, it is
    /// also unclear in what order the components are evaluated.
    ///
    /// [#68364]: https://github.com/rust-lang/rust/issues/68364
```

`compiler/rustc_const_eval/src/interpret/operand.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:26-42` (the interpreter's `Immediate`):

```rust
/// An `Immediate` represents a single immediate self-contained Rust value.
///
/// For optimization of a few very common cases, there is also a representation for a pair of
/// primitive values (`ScalarPair`). It allows Miri to avoid making allocations for checked binary
/// operations and wide pointers. This idea was taken from rustc's codegen.
/// In particular, thanks to `ScalarPair`, arithmetic operations and casts can be entirely
/// defined on `Immediate`, and do not have to work with a `Place`.
#[derive(Copy, Clone, Debug)]
pub enum Immediate<Prov: Provenance = CtfeProvenance> {
    /// A single scalar value (must have *initialized* `Scalar` ABI).
    Scalar(Scalar<Prov>),
    /// A pair of two scalar value (must have `ScalarPair` ABI where both fields are
    /// `Scalar::Initialized`).
    ScalarPair(Scalar<Prov>, Scalar<Prov>),
    /// A value of fully uninitialized memory. Can have arbitrary size and layout, but must be sized.
    Uninit,
}
```

`compiler/rustc_const_eval/src/interpret/operand.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:597-602`:

```rust
        // It may seem like all types with `Scalar` or `ScalarPair` ABI are fair game at this point.
        // However, `MaybeUninit<u64>` is considered a `Scalar` as far as its layout is concerned --
        // and yet cannot be represented by an interpreter `Scalar`, since we have to handle the
        // case where some of the bytes are initialized and others are not. So, we need an extra
        // check that walks over the type of `mplace` to make sure it is truly correct to treat this
        // like a `Scalar` (or `ScalarPair`).
```

Basis: derived (modeling bridge). `Scalar` mirrors `Scalar::{Initialized, Union}` ("unions never have niches and even allow undef"); `BRepr.pair a b bOff` mirrors `ScalarPair` with `a` at offset zero and `b` at `b_offset` in memory order. The interpreter quote documents that a `Scalar`-layout union (`MaybeUninit<u64>`) cannot be held as an initialized immediate because some bytes may be initialized and others not; this is the partial-initialization case that R1's condition (b) and R4/R5 isolate. The `Assign` note restricts overlapping assignments to `Scalar`/`ScalarPair` types whose scalars are all `Scalar::Initialized`; R1 shows, in the toy, which further value facts (uniform initialization, range, provenance coherence) a register round trip needs. These paragraphs neither establish nor refute claims about rustc; they state which documented design each toy definition is meant to capture.

#### MiniRust (`derived (modeling bridge)`; documentation quoted)

`spec/lang/representation.md@063d784186d3252bee242217f218223205c0b568:100-103` (pointer
decoding with mixed provenance):

```markdown
Pointers are significantly more complex to represent than just the integer address.
For one, they need to encode the provenance.
When decoding, we have to deal with the possibility of the pointer bytes not all having the same provenance;
this is defined to yield a pointer without provenance.
```

`spec/lang/representation.md@063d784186d3252bee242217f218223205c0b568:117-131` (provenance on
decoding):

```rust
    // Get the provenance. Must be the same for all bytes, else we use `None`.
    // As start value we use the first byte's provenance (to avoid having to add a "top" element).
    let provenance = bytes.fold_with_idx(
        bytes[0].provenance_frag().map(|frag| frag.provenance),
        |acc, idx, byte| {
            // Crucially, if `acc` is ever `None`, it remains `None`.
            if let Some(frag) = byte.provenance_frag() &&
                frag.position == idx && Some(frag.provenance) == acc
            {
                acc
            } else {
                None
            }
        }
    );
```

`spec/lang/representation.md@063d784186d3252bee242217f218223205c0b568:313-319` (unions; lines
322-342 of the same file encode a union value from its chunks and reset every other byte to
`Uninit`, which the toy union does not model):

```markdown
### Unions

A union simply stores the bytes directly, no high-level interpretation of data happens.

- TODO: Some real unions actually do not preserve all bytes, they [can have padding](https://github.com/rust-lang/unsafe-code-guidelines/issues/156).
  So we have to model that there can be "gaps" between the parts of the byte list that are preserved perfectly.
- TODO: Should we require *some* kind of validity? See [this discussion](https://github.com/rust-lang/unsafe-code-guidelines/issues/73).
```

`spec/lang/representation.md@063d784186d3252bee242217f218223205c0b568:652-669` (definedness order
on abstract bytes):

```rust
impl<Provenance> DefinedRelation for AbstractByte<Provenance> {
    fn le_defined(self, other: Self) -> bool {
        use AbstractByte::*;
        match (self, other) {
            // `Uninit <= _`: initializing something makes it "more defined".
            (Uninit, _) =>
                true,
            // Among initialized bytes, adding provenance makes it "more defined".
            (Init(data1, None), Init(data2, _)) =>
                data1 == data2,
            // If both bytes have provenance, everything must be equal.
            (Init(data1, Some(provenance1)), Init(data2, Some(provenance2))) =>
                data1 == data2 && provenance1 == provenance2,
            // Nothing else is related.
            _ => false,
        }
    }
}
```

`spec/lang/representation.md@063d784186d3252bee242217f218223205c0b568:754-756` (monotonicity
laws; lines 759-763 state that `encode(decode(bytes)) <= bytes`, the shape of
`raise_lower_bytesLe_self`):

```markdown
First of all, `encode` and `decode` must both be "monotone":
- If `val1 <= val2` (and if both values are well-formed for `ty`), then `ty.encode(val1) <= ty.encode(val2)`.
- If `bytes1 <= bytes2`, then `ty.decode(bytes1) <= ty.decode(bytes2)`.
```

Basis: derived (modeling bridge). `AByte`, `AByte.leb`, `ptrProv` and `ptrLower` follow these
definitions (`ptrLower` keeps the address bytes and the `decode_ptr` provenance). MiniRust has no
backend scalar representation; the lowering in this package is not part of MiniRust.

#### LLVM IR (`derived (modeling bridge)`; documentation quoted)

`llvm/docs/LangRef.md@a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6:1736-1740` (`noundef`):

```markdown
`noundef`
:   This attribute applies to parameters and return values. If the value
    representation contains any undefined or poison bits, the behavior is
    undefined. Note that this does not refer to padding introduced by the
    type's storage representation.
```

`llvm/docs/LangRef.md@a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6:1954-1967` (`range`):

```markdown
`range(<ty> <a>, <b>)`
:   This attribute expresses the possible range of the parameter or return value.
    If the value is not in the specified range, it is converted to poison.
    The arguments passed to `range` have the following properties:

    -  The type must match the scalar type of the parameter or return value.
    -  The pair `a,b` represents the range `[a,b)`.
    -  Both `a` and `b` are constants.
    -  The range is allowed to wrap.
    -  The empty range is represented using `0,0`.
    -  Otherwise, `a` and `b` are not allowed to be equal.

    This attribute may only be applied to parameters or return values with integer
    or vector of integer types.
```

Basis: derived (modeling bridge). The toy's `passArg true` (UB on an argument with an undefined lane)
follows the `noundef` sentence; its `poison`-on-out-of-range lowering of `initialized` scalars
follows the `range` sentence. The `range` attribute applies to integer and integer-vector types;
the toy also attaches ranges to pointer scalars (as rustc's `Scalar::Initialized` does with
`valid_range`), which is a toy generalization. `noundef` excludes storage padding, which the toy
does not model.

#### Rust Reference (`derived (modeling bridge)`; normative text quoted)

`src/behavior-considered-undefined.md@bcd62f35e8bf480ec5b0fa569b6d12ea5924030c:145-146`:

```markdown
r[undefined.validity.union]
* For a `union`, the exact validity requirements are not decided yet. Obviously, all values that can be created entirely in safe code are valid. If the union has a [zero-sized] field, then every possible value is valid. Further details are [still being debated](https://github.com/rust-lang/unsafe-code-guidelines/issues/438).
```

Basis: derived (modeling bridge). `trivialUnionValidity` is the policy the Reference guarantees for
unions with a zero-sized field; for unions without one (such as `neverUnion`) the Reference
leaves validity undecided, so R13b is stated under trivial validity and R13 quantifies over
policies.

### Prior-art literature

- X. Leroy and S. Blazy, "Formal verification of a C-like memory model and its uses for verifying
  program transformations", Journal of Automated Reasoning 41(1), 2008, DOI
  10.1007/s10817-008-9099-0; CompCert `common/Memdata.v` at `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`
  (`Inductive memval` with `Undef | Byte | Fragment`, L209-212; `decode_val_inject`, L908;
  `memval_lessdef`, L985): a mechanized byte model with pointer fragments and a monotone typed
  decoding (R3), and `Many32`/`Many64` chunks moving fragments opaquely (R4).
- J. Lee et al., "Taming Undefined Behavior in LLVM", PLDI 2017, DOI 10.1145/3062341.3062343;
  N. P. Lopes et al., "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, DOI
  10.1145/3453483.3454030: formal refinement semantics for `undef`/`poison` and LLVM IR
  transformations (R7, R7b, R17).
- J. Kang et al., "A Formal C Memory Model Supporting Integer-Pointer Casts", PLDI 2015, DOI
  10.1145/2737924.2738005; F. Besson, S. Blazy and P. Wilke, "CompCertS", Journal of Automated
  Reasoning 2019, DOI 10.1007/s10817-018-9496-y: mechanized byte-level models with fragments and
  integer-pointer casts (R10).

None of these characterizes register lowering of `Scalar`/`ScalarPair` representations with
initialization uniformity and provenance coherence; the results here restate the byte-model facts
for that question.

## Boundaries

Non-claims first: those shared by all results, then those of each result. Escape hatches of the
impossibility results, attractive stronger conclusions that are not established, tightness
status, cases not examined, and disproved or dropped statements follow.

### Non-claims shared by all results

- **Model–system relation: none proved.** These are statements about the toy model; they neither
  establish nor refute the corresponding claims about rustc, LLVM, Miri or MiniRust.
- **Refinement criterion.** Refinement is MiniRust's byte order `BytesLe`, justified for typed
  integer and pointer reads by R3; agreement of all typed reads does not imply `BytesLe`
  (`typedReads_agree_without_bytesLe`). No context language is modelled.
- **R1 and `noundef`.** R1's condition (b) admits all-`uninit` values of an `initialized` scalar,
  whose register is `poison`; R1 does not license a `noundef` attribute on that register
  (`initialized_allUninit_roundTrips_but_noundef_ub`, R17).
- **R7/R8 measure exact agreement.** Discipline compatibility characterizes exact agreement of
  raised bytes from the lowered value; in the one-sided order every scalar-to-scalar
  reinterpretation, for all widths and every `n`, refines the memory transmute (R7b). Downstream
  `noundef`/range-assuming uses of an `initialized` register are not modelled. At width `1` the
  `union` to `initialized` separation rests on `regCastScalar` keeping fragments
  (`regCastStrip_width1_union_to_initialized_agrees`).
- **Pointer lowering.** Pointer scalars lower as MiniRust's `decode_ptr` (mixed or misplaced
  provenance gives a provenance-free pointer). Calling conventions, vectors, floats and alignment
  are not modelled.
- **Unions.** Whole-value union validity is a parameter; R11, R12 and R13b fix it to
  `trivialUnionValidity`, R13 quantifies over it. Real unions may have padding; the toy union
  preserves every byte. Whether real backend integer registers can carry provenance is not
  examined (R4, R4b, R15 depend on union registers holding fragments).

### Non-claims of each result

- **R1 — Lowering to one scalar refines iff (a), (b), (d) and (c) hold.** (1) Not a statement about typed copies at the value's type (which reset padding to `uninit`); it concerns replacing a byte-level move by registers. (2) "Uniformly initialized" is all-or-nothing, not "fully initialized": an all-`uninit` value round-trips through an `initialized` scalar because `poison` raises to `uninit`; this does not license a `noundef` attribute on that register: `initialized_allUninit_roundTrips_but_noundef_ub` exhibits such a value satisfying all four conditions whose register is `poison` and trips `noundef`. It also does not model rustc's interpreter, which reports an error on reading uninitialized bytes as a scalar, nor LLVM's distinction between poison and undef in memory. (3) The byte order is MiniRust's; the converse "agreement of every typed read implies `BytesLe`" is false (`typedReads_agree_without_bytesLe`: `ptrFrag 1 7 1` and `bits 1` agree on every typed integer and pointer read at every offset and width). (4) Nothing about calling conventions, vectors, floats or alignment. (5) Ranges are arbitrary predicates; nothing is claimed about wrapping intervals specifically. (6) Real `Scalar::Initialized` layouts in rustc have no trailing padding (the scalar's size equals the layout size); condition (a) concerns the toy's general representations and arises in practice for `ScalarPair` and padded values.
- **R2 — Lowering to a scalar pair refines iff (a), (b), (d) and (c) hold for both scalars.** R1's non-claims apply to each component (not typed copies; "uniformly initialized" is all-or-nothing and does not license `noundef`, `initialized_allUninit_roundTrips_but_noundef_ub`; the converse of R3 is false, `typedReads_agree_without_bytesLe`; no calling conventions, vectors, floats or alignment; ranges are arbitrary predicates). In addition, rustc documents `b_offset` as non-zero and currently equal to `a`'s size rounded up to `b`'s alignment, but R2 assumes neither (it assumes disjointness). No evaluation order of the two scalars is modelled. In the toy, a split pointer lowers to two provenance-free pointers (MiniRust `decode_ptr`), so `cex_pair_ptr_split_across_boundary` exhibits a loss of provenance, not UB.
- **R3 — Typed reads are monotone in the byte order.** Covers `readInt` and `readPtr` and no other use; dereferences, provenance-dependent accesses and exposure are not modelled. The converse fails (`typedReads_agree_without_bytesLe`).
- **R4 — For a `union` scalar, the round trip refines iff condition (a) holds.** Depends on the modelling assumption that a union register holds every abstract byte, fragments included; `provenanceStripping_register_not_refines` shows a provenance-stripping register would not refine a fragment byte. Whether a real backend's integer register can carry provenance is not examined.
- **R4b — A `union` scalar covering the whole value always refines.** Depends on the modelling assumption that a union register holds every abstract byte, fragments included (`provenanceStripping_register_not_refines`); whether a real backend's integer register can carry provenance is not examined.
- **R5 — For every primitive and range, some union value does not round-trip as `initialized`.** Does not say which real types are lowered as `union` components. Reading with R1 (derived, not a separate theorem): for every set `V` of values, each of length exactly `n`, attaching a range (lowering a component as `initialized p rng`) refines on `V` iff R1's (a), (b), (d) and (c) hold on `V`; R5 itself is stated for primitives of width at least `1` (`hp : 1 ≤ p.size`).
- **R6 — Coarsening to `memory` is always a refinement (positive control).** Says nothing about performance or about memory-level optimizations; a pass that falls back to `memory` needs none of R1's conditions.
- **R7 — Scalar-to-scalar reinterpretation agrees exactly with the memory transmute iff disciplines are compatible.** (1) `CastAgrees` is exact equality of raised bytes, starting from the lowered value, not one-sided refinement: in the one-sided order every scalar-to-scalar reinterpretation, for all widths and every `n`, refines the memory transmute whatever the disciplines (R7b), and `regCast_union_to_initialized_refines_not_agrees` is a `union` to `initialized` instance that refines without agreeing. R7 thus characterizes when the register path leaks bytes the memory path would not produce (`raw` bytes or out-of-range data in an `initialized` register), not when it is unsafe. (2) Downstream uses of an `initialized` target register that assume `noundef` or a range (which make such leaked values UB or poison in a real backend) are not modelled. (3) At width `1`, the `→` direction for a `union` source rests on `regCastScalar` keeping provenance fragments of a `raw` register in an `initialized` integer target: `regCastStrip_width1_union_to_initialized_agrees` shows that a variant stripping provenance on that cast agrees with the memory transmute on every 1-byte value although the disciplines are incompatible; at widths `2` and more, partial initialization also separates the paths (not proved here as a separate theorem). (4) "Same initialization discipline" is not required: `initialized` to `union` agrees. (5) The integer/pointer distinction is not an obstruction in this toy: both paths drop provenance pointer-to-integer and give a provenance-free pointer integer-to-pointer. (6) Exposure and provenance-picking casts are not modelled (see R10).
- **R7b — Scalar-to-scalar reinterpretation refines the memory transmute (one-sided), for all widths and disciplines.** (1) This does not say that such a bitcast is a sound compilation of a transmute in a real backend: the toy's `regCast` makes no initialization, range or provenance assertion, and downstream `noundef`- or range-assuming uses of an `initialized` register are not modelled. (2) `regCastScalar` does not truncate or pad the payload to `t.size` (see its definition), so for unequal widths the register value need not have `t`'s width; `CastRefines` compares raised bytes and does not say that such a register value is well formed for `t`. (3) Pair shapes and shape-changing reinterpretations are not covered.
- **R8 — Pair-to-pair reinterpretation agrees exactly when offsets coincide and disciplines are compatible.** (1) The converse is not claimed and fails in general: `regCast_pair_agrees_despite_offset_mismatch_of_empty_range` shows agreement despite different offsets when a source component has an empty range. (2) The non-claims (1)–(6) of R7 apply componentwise: `CastAgrees` is exact equality from the lowered value, one-sided refinement is a different property, downstream `noundef`/range uses are not modelled, the width-`1` `union` separation rests on `regCastScalar` keeping fragments, and integer/pointer casts are not obstructions in the toy. (3) Tightness of `hbn` uses the length-dependent `len2Range`; with range inclusion on data of every length (`DisciplineCompatAnyLen`), `hbn` is not needed. (4) Shape-changing reinterpretations are not covered by R8; R9 treats one of them (a pair concatenated into a `union` scalar).
- **R9 — A pair-to-`union`-scalar reinterpretation across padding disagrees; without padding it agrees.** (1) The target is a `union` scalar so that the disagreement isolates the padding gap; a pair reinterpreted into an `initialized` scalar is not modelled by `regCast` (the lowered value passes unchanged). (2) This counterexample neither establishes nor refutes a padding-preserving assembly of the two registers into a 3-byte `union` scalar (not proved here). (3) rustc's single `Scalar` layouts have no trailing padding; the 2-byte scalar in a 3-byte value is a toy shape.
- **R10 — Attaching provenance is not the reinterpretation.** (1) In the toy's definedness order the provenance-attaching result is above the transmute's (`bytesLe_bits_ptrFrag_attach`: `BytesLe [bits 5] [ptrFrag 5 7 0]`), so this exhibits byte-level inequality, not a failure of `BytesLe` refinement. (2) No exposed-provenance semantics, alias analysis or strict-provenance restriction is modelled; integer-to-pointer casts and exposure are the subject of `pointer-provenance-models-and-integer-pointer-cast-optimizations`.
- **R11 — Under trivial whole-value validity, a union move is defined iff the size matches; a field read is UB iff its bytes are invalid.** (1) `f` need not be a field of `u`: the read fact holds for every field descriptor. (2) Whole-value validity is fixed to `trivialUnionValidity`; Rust has not decided union validity for unions without a zero-sized field. (3) Real unions may have padding (MiniRust's open question; MiniRust's union encoding resets bytes outside the union's chunks to `Uninit`), whereas the toy union preserves all bytes.
- **R12 — A niche-inheriting union move would be UB after a valid field write.** This refutes inheriting one field's niche (`NonZeroU8`) when another field (`u8`) validly admits the niche value `0`; it neither establishes nor refutes whether a union whose fields all share a niche (for example `{ a: NonZeroU8, b: NonZeroU8 }`) could carry that niche. Niche-filled enums containing unions are not examined.
- **R13 — An `Unreachable` rewrite of a union move refines iff whole-value validity admits no value.** Inhabitedness-gated rewrites of real compilers are not modelled; the program `moveThenRet` takes the union value as input and models no value-producing operation.
- **R13b — Under trivial whole-value validity, a field-wise uninhabitedness gate is not a refinement.** This result is proved under trivial whole-value union validity. The Rust Reference states that union validity is not decided yet, except that values creatable in safe code are valid and that every value is valid if the union has a zero-sized field; `neverUnion` has no zero-sized field. The result neither establishes nor refutes inhabitedness of such unions in Rust.
- **R14 — Framing of partial writes.** `writeBytes_frame` is a statement about the toy `writeBytes` operation; it neither establishes nor refutes framing claims about real memory models with aliasing, provenance-dependent stores or concurrency.
- **R14b — A wider read after a partial write sees the written bytes plus the old bytes.** `readWider_after_partial_write` is a statement about the toy `writeBytes` and `seg` operations; it neither establishes nor refutes framing claims about real memory models with aliasing, provenance-dependent stores or concurrency. Reads and writes running past the end of `x` are truncated.
- **R15 — The lane-wise blend of a partial write into a `union` register equals the memory write.** (1) `mergeWrite` leaves register values other than `raw` unchanged; partial writes into `initialized` registers are not modelled. (2) This shows that the blend is a correct register-level partial write; it does not show that every correct register-level partial write must be a blend (not proved here). (3) Depends on the modelling assumption that a union register holds every abstract byte.
- **R16 — No constant fill makes a whole-register write refine a partial write.** (1) Covers whole-register writes with a constant fill on a two-byte register; other widths are not examined. (2) `¬ OutLe` means "not at least as defined", not "less defined": `OutLe` is a partial order. For every initialized fill byte (`bits b` or a fragment) and every byte list `x`, the whole-register read is not strictly less defined than the partial-write read (`wholeWrite_init_fill_never_strictly_less_defined`); with fill `bits 0` and `x = [bits 7, bits 9]` the two reads are incomparable (`wholeWrite_bits0_incomparable_with_partial`). With fill `uninit` the whole-register read is UB, and for `x = [bits 7, bits 9]` it is strictly less defined than the partial-write read (`wholeWrite_uninit_fill_strictly_less_defined_instance`).
- **R17 — `noundef` on a `union` scalar argument introduces UB.** (1) The positive control requires `lowerScalar (.initialized q r) bs ≠ .poison`; it does not apply to all-`uninit`, partially initialized or out-of-range values lowered to an `initialized` scalar, which lower to `poison` and trip `noundef` (`initialized_allUninit_roundTrips_but_noundef_ub`): R1's conditions do not license `noundef`. (2) Calling conventions are not modelled; `passArg` is a toy argument-passing step.

### Escape hatches of the impossibility results

Each item names a setting, outside the hypotheses or the quantified range of the result, in which the impossibility does not apply. Items citing a theorem are proved; the others are labelled.

- **R5 — For every primitive and range, some union value does not round-trip as `initialized`.** Width `0` (`cex_initialized_lowering_width_zero`); restricting `V` to values that satisfy R1's (b), (d), (c) for `initialized p rng` (then R1, `scalar_roundTrip_refines_iff`, gives refinement; positive control `initialized_lowering_refines_plain_in_range_value`).
- **R13b — Under trivial whole-value validity, a field-wise uninhabitedness gate is not a refinement.** A whole-value validity policy that rejects every value of `neverUnion` (R13; positive control `gate_refines_of_emptyValidity`); a gate that does not fire on `neverUnion` (`cex_fieldwiseGate_never_fires`).
- **R16 — No constant fill makes a whole-register write refine a partial write.** Untouched bytes known to be `uninit` (`wholeWrite_uninit_eq_writeBytes_of_untouched_uninit`); full-width writes (`wholeWrite_eq_writeBytes_of_full_width`); fills that depend on the old value, i.e. a lane-wise merge (R15, `unionRegister_mergeWrite_eq_memoryWrite`), rather than a constant.
- **R17 — `noundef` on a `union` scalar argument introduces UB.** (1) Width `0` (`cex_noundef_width_zero`); (2) restricting the union's values to all-initialized byte lists, for example after initializing every byte: `passArg_noundef_union_eq_none_iff` shows that a value lowered to a `union` register trips `noundef` iff it is not all initialized; (3) `derived (modeling bridge)`, not modelled in the toy: LLVM's `noundef` does not refer to padding introduced by a type's storage representation.

### Attractive stronger conclusions that are not established

- **A register bitcast is a sound compilation of a transmute in a real backend.** Not
  established: R7b's one-sided refinement holds for every pair of scalars in the toy because
  `regCast` asserts nothing; downstream `noundef`- or range-assuming uses of an `initialized`
  register are not modelled (R7b non-claim (1)).
- **Discipline compatibility is a refinement (safety) condition.** Not established and false in
  the toy: R7 and R8 characterize exact agreement; in the one-sided order every scalar-to-scalar
  reinterpretation refines the transmute (`regCast_scalar_refines_transmute`), and
  `regCast_union_to_initialized_refines_not_agrees` refines without agreeing.
- **R8's converse.** False in general: `regCast_pair_agrees_despite_offset_mismatch_of_empty_range`
  agrees despite different offsets.
- **R1's conditions license `noundef` on the register.** False in the toy:
  `initialized_allUninit_roundTrips_but_noundef_ub` exhibits a value satisfying all four
  conditions whose register is `poison` and trips `noundef`.
- **Agreement of every typed read implies `BytesLe`.** False:
  `typedReads_agree_without_bytesLe`.
- **R16 is a strict-decrease claim.** It is not: for every initialized fill the whole-register
  read is never strictly less defined than the partial-write read
  (`wholeWrite_init_fill_never_strictly_less_defined`), and with fill `bits 0` the two reads are
  incomparable (`wholeWrite_bits0_incomparable_with_partial`).
- **Every correct register-level partial write must be a blend.** Not established: R15 shows that
  the blend is one correct lowering (not proved here that it is the only one).
- **A union whose fields all share a niche cannot carry it.** Not established: R12 neither
  establishes nor refutes this (not proved here either way).
- **Field-wise uninhabited unions are inhabited in Rust.** Not established: R13b is stated under
  trivial whole-value validity, and the Rust Reference leaves union validity undecided for unions
  without a zero-sized field.
- **A padding-preserving assembly of two registers into one wider `union` scalar disagrees with
  the transmute.** Not established: R9's counterexample concatenates without padding into a
  2-byte register (not proved here for other assemblies).

### Hypotheses with `unknown` tightness

None. No hypothesis of any card is left with unknown tightness; R6, R7b, R11, R14 and R16 have no
hypotheses (R7b quantifies over every `n`, `s` and `t`).

### Not examined

Shape-changing reinterpretations other than R9's concatenation into a `union` scalar;
whole-register writes on registers of widths other than two bytes (R16); niches shared by every
field of a union (R12); partial writes into `initialized` registers (R15); evaluation order of
the two scalars of a pair; calling conventions, vectors, floats and alignment.

### Disproved or dropped statements

None. All 21 results were proved as stated; no statement was found false and none was left
unproved.

## Evidence

**Kernel-check record.** Toolchain `leanprover/lean4:v4.34.1` (`leanprover/lean4`, tag
`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, resolved from the tag on
2026-11-21); Lake project `lean/` with one library `ToyReprLower` and no dependencies (core Lean
only, no Mathlib). Observed 2026-11-21: `lake build` succeeds with no `sorry` warnings; no Lean
source contains `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations,
`implemented_by`, `@[extern]` or `unsafe`; all 641 non-internal declarations of the library
depend only on axioms among `propext`, `Classical.choice`, `Quot.sound` (per declaration in
`audit/axioms.json`). Every result is `Basis: execution (Lean kernel check)`. No measurement of
any real system was made.

**Statement and closure hashes.** For each Lean name in the fields `lean`, `lean_names`,
`nonvacuity_witness_lean`, `positive_control_lean` and hypothesis `counterexample` of
`results.json`, `audit/statements.json` records the SHA-256 of the statement and of its
definition closure (computed as described under **Revalidation**). The table lists them with the
axioms of each declaration (`(none)` for a declaration that uses no axiom). Roles are `R`
(result), `CE` (tightness counterexample), `NV` (non-vacuity witness), `PC` (positive control),
and `S` (definition or supporting declaration cited by the card).

| Lean name | Used by (result: role) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.ReprLower.scalar_roundTrip_refines_iff` | R1:R, R5:S | Classical.choice, Quot.sound, propext | `9b548f8300b8ae13b46bb271b9690d03e8c08eb464697db06a86f7ddc6e50a7c` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.cex_scalar_hlen` | R1:CE, R4:CE | propext | `ce1d7336444156ae7d951b31387fec9feef0219696bb4bebbb7c53b121268f7d` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.cex_scalar_padding_carries_bytes` | R1:CE | propext | `27f9204a774972b265d145cf38e46e435a8e9c371bc2e01ebb52bc644ca30c30` | `264b008d6bf334264bbd514c51142d3acd55948d3ec1ba04593ba8f5f3608c6a` (124) |
| `Toy.ReprLower.cex_scalar_partial_init` | R1:CE | propext | `c8671d8f1350e4f7bb4018110ccc14f5e20b78af23161bf4ca32b9469a884a3b` | `264b008d6bf334264bbd514c51142d3acd55948d3ec1ba04593ba8f5f3608c6a` (124) |
| `Toy.ReprLower.cex_scalar_out_of_range` | R1:CE | propext | `12510752bd6b096271e8ffb7e2a6b704142f7cc8871c0d7b59411ef4884d6d4a` | `0f474b7e16bed5d84b47f1062d768bf3b56517932d46d14516b1fdb806774a7d` (124) |
| `Toy.ReprLower.cex_scalar_frags_under_int` | R1:CE | propext | `d60de3a5b2ec1fd270b3d4af31b0d89ae2a3acc7205571e1cb6dab0251bf5220` | `b20dbc33dd3e1de98d4fce336bf7d3e84693d0a9b47167f3ca83b8212bbee357` (134) |
| `Toy.ReprLower.cex_scalar_mixed_provenance_ptr` | R1:CE | propext | `31a6924c4cbd3bd6566fb4f92023f929dd2905570269ae424abf0e31039f860c` | `b63cd43a1d887088d475e752a23888f93c8c753036ca2dfe70402eed429bd21a` (120) |
| `Toy.ReprLower.nonvacuous_scalar_roundTrip` | R1:NV | propext | `5a37a566008195c16c92a5c4b339a76403a4a2330d09d79b994d2b6640636c76` | `b63cd43a1d887088d475e752a23888f93c8c753036ca2dfe70402eed429bd21a` (120) |
| `Toy.ReprLower.pair_roundTrip_refines_iff` | R2:R | Classical.choice, Quot.sound, propext | `5b4ad842e4614eff1c93ba84878e93c4b075efd118d2f13f7899614edd095934` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.cex_pair_hlen` | R2:CE | propext | `6e2e5009c2fb519cb3b43c68e8ea20a3b30e528eb07b36b31fb06d81e5df2b3b` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.cex_pair_overlap` | R2:CE | propext | `dc6d740e32563560595d7b724cba2545c334d1c35ea1d331f75dd2e3a647fa77` | `c3df6930f1fa9d117cfccbee7687c8ceaac18fb56a18e50ed0e41f8c0414e211` (113) |
| `Toy.ReprLower.cex_pair_padding_carries_bytes` | R2:CE | propext | `703083525ea39ce0ef6bd0215b1e9a0772b8f1f607fa11b35c55ec4f39cbc953` | `b63cd43a1d887088d475e752a23888f93c8c753036ca2dfe70402eed429bd21a` (120) |
| `Toy.ReprLower.cex_pair_partial_init` | R2:CE | propext | `8c457c590d1de9c2627dadd34bfaa4b0f6227a6b90a0ef8efdc3499a178ac48e` | `b63cd43a1d887088d475e752a23888f93c8c753036ca2dfe70402eed429bd21a` (120) |
| `Toy.ReprLower.cex_pair_out_of_range` | R2:CE | propext | `537bc60d581c49ca9a1dfc092142ef7c8839869dda14275a70575cf6dca30f50` | `2ce38754ef7e6664da27e0cc86a4aaeecefbaa386fa713a5df6b40dfa14d2973` (121) |
| `Toy.ReprLower.cex_pair_ptr_split_across_boundary` | R2:CE | propext | `fa654308cc95650a132e8fdb8166bb4c742cab126dbae09084d173f5c5f6e01c` | `b20dbc33dd3e1de98d4fce336bf7d3e84693d0a9b47167f3ca83b8212bbee357` (134) |
| `Toy.ReprLower.nonvacuous_pair_roundTrip` | R2:NV | propext | `c31dcc07604e4025f37a3735c2c4d5ac85110652e7fbbba045da0a35dd788031` | `2ce38754ef7e6664da27e0cc86a4aaeecefbaa386fa713a5df6b40dfa14d2973` (121) |
| `Toy.ReprLower.typedReads_mono_of_bytesLe` | R3:R | Classical.choice, Quot.sound, propext | `1387cd81bd5e07f5b4bae9e324b15686678c537b114cf64d8ebe80466f7d874f` | `cd0b0fa33c5e9812ca403588993a2072ed53aa5b4a5b9a4caeb67f846d605300` (47) |
| `Toy.ReprLower.cex_typedReads_without_bytesLe` | R3:CE | propext | `0608f19bea98c2492d3436098cb40d12044dc5b287816df6740d54d53e1e68a8` | `a3db2c4e733b515c91e9fd2c9ecadeea97eaf9e6ac708feea96ee29b6e74764a` (39) |
| `Toy.ReprLower.nonvacuous_typedReads_mono` | R3:NV | propext | `570358416d1ae4031ca421096420f0a0c33ba58e442cf13c404df02c95b8e686` | `030f66ea2c4903a46a042b4c17ef96f34cd7590794a5e96777128ddf833e1a61` (17) |
| `Toy.ReprLower.union_scalar_roundTrip_refines_iff_outsideExtentsUninit` | R4:R | Classical.choice, Quot.sound, propext | `c41f015143eac9ae413affd6c61e9fc635aca0a6c25d5f91e0b840d1ec28f7af` | `d7399dba5cb96ba664007deb338f851774393b13a917dd933e4a629ce69f2096` (90) |
| `Toy.ReprLower.nonvacuous_union_roundTrip` | R4:NV | propext | `730779519a813aa6b8633b7b6de52cba10a69b7f7cad60e7006318df11a236ff` | `d7399dba5cb96ba664007deb338f851774393b13a917dd933e4a629ce69f2096` (90) |
| `Toy.ReprLower.union_scalar_roundTrip_refines_of_covers_value` | R4b:R | Classical.choice, Quot.sound, propext | `df830416e6081051129c20601d8e1d1e4a60f6447a2bfe1509f345f0bc65f3fa` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.cex_union_covers_value_hlen` | R4b:CE | propext | `39e5b8e33b00b9c7a34e927554ef48ebedf3a8cddaf64ff48effb97531bc3376` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.cex_union_size_lt` | R4b:CE | propext | `a6973cc26b7630fec91ed903b3634c0c431b253b6d5aad34f3dbc5fef082e4c3` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.nonvacuous_union_covers_value` | R4b:NV | propext | `d1d600b1e2121873354d49d677aacda3f57a1173c9f68ace79e82ec26db87084` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.initialized_lowering_not_refines_some_union_value` | R5:R | Classical.choice, Quot.sound, propext | `aeeffba086c0b8eb851473f621b108258b54e6f21542650fca4b715c6c233dcd` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.cex_initialized_lowering_width_zero` | R5:CE | Classical.choice, Quot.sound, propext | `0ad5851319cc6eeecb5da44a451912bb14abbef514b13044517d584219762e7b` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.nonvacuous_initialized_lowering_union_value` | R5:NV | Classical.choice, Quot.sound, propext | `872ae2c334176002f024d567023c1880b6d753a055f2b72a9513f8e1e20213cb` | `c7936a4b35c9c525647cbaad251b1e6d8f263f35b683d9067d95d8073f38840d` (88) |
| `Toy.ReprLower.initialized_lowering_refines_plain_in_range_value` | R5:PC | propext | `b750a757449c056c9c18d9c9de118b457db0ea338cbac4cac7176ebd61f0fcfe` | `f4770a316883d4c84c87b1f2549c3fec9da21f5ebb4daf168afdd70ab34e25db` (88) |
| `Toy.ReprLower.memory_roundTrip_refines` | R6:R | Classical.choice, Quot.sound, propext | `1a6f6c20d557db265bd643a7fe116e7e02a626b700f42a61bea2052a62c46af5` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.nonvacuous_memory_roundTrip` | R6:NV | Classical.choice, Quot.sound, propext | `ef2dee9220cdeadc5e9b872bb524ed1c63b694e7d726e1d80b27e77f754dd18e` | `009ceecbf28b623062e07776e92d4f78ebc1058869f8e845239d8def5aa4956f` (87) |
| `Toy.ReprLower.regCast_scalar_agrees_iff_disciplineCompat` | R7:R | Classical.choice, Quot.sound, propext | `fe1415dfe3df11f463b617ba3098caf9af19b97ca30b13d45aa91d4af4e4aacb` | `751e94b757ae41d03eb25989377a42af31ebe3930dabd419502a9a2d49b0ee2c` (94) |
| `Toy.ReprLower.cex_regCast_scalar_width_mismatch` | R7:CE | propext | `552181b2f9517a167c7e7c4fe5449f8413ccfc1e47dd98e8035955209340838b` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_scalar_width_zero` | R7:CE | propext | `eac6553ea7624e1b68611d31db075785f1b112e49475348ea715361130fac2c3` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_scalar_hn_length_indep` | R7:CE | propext | `f0fcec2cec3749e07e6c4baafbdb81d1f0157c1ffe9931f202e5b993502607d8` | `78e05f7433c757ae63e7284c1bf98db5301ef59dda8d053190244ad654df37e7` (96) |
| `Toy.ReprLower.cex_regCast_scalar_wider_than_value` | R7:CE | Classical.choice, Quot.sound, propext | `6d5a2e6f1d17ef9cd7c0256b71c30f774a436b1196567fc2a317da5e0aeb6ec0` | `d78bc3470cb29a266ed633e2bdf0e872c7d5e27660103c0314046ec6ea664a6c` (96) |
| `Toy.ReprLower.nonvacuous_regCast_scalar` | R7:NV | Classical.choice, Quot.sound, propext | `5f0178e23bcc2c33a33044bcbfbf0ca9eb843677ccb326afe6a08653bd8b27ab` | `78e05f7433c757ae63e7284c1bf98db5301ef59dda8d053190244ad654df37e7` (96) |
| `Toy.ReprLower.regCast_scalar_refines_transmute` | R7b:R | Classical.choice, Quot.sound, propext | `4df96fe7089e0b35bf0e6e9a2df9ede2ff36cd5afac4f316976ce3816381f092` | `1899f8539a6860a1cfb984ebe88cf7c56fe8eeaf77a56163a637b6d78689b219` (100) |
| `Toy.ReprLower.regCast_union_to_initialized_refines_not_agrees` | R7b:NV, R7:S | Classical.choice, Quot.sound, propext | `c6a521f632668bf59fa1501fbc55b8f0d1f4ce9e4b7ab70d132ce53914f0dcbf` | `ad980dc77399025c10073fdbd9d379c8f5a98520dc8203a85d70bd7b2cb4dc0b` (104) |
| `Toy.ReprLower.castRefines_unequal_widths_and_wider_than_value` | R7b:NV | Classical.choice, Quot.sound, propext | `3bdc058852f94e3fe809370bc16a18da42f5f86b7b805aea63bae2a1cbeb3929` | `bea551c44e31f084ad6ab0df726a31354f07e84b0f78b98d7e8eb4e23cdab877` (103) |
| `Toy.ReprLower.regCast_pair_agrees_of_offsetEq_disciplineCompat` | R8:R | Classical.choice, Quot.sound, propext | `7132554d65c24a065285153bbfcd29420fdc29667187386f934bd0426419e690` | `751e94b757ae41d03eb25989377a42af31ebe3930dabd419502a9a2d49b0ee2c` (94) |
| `Toy.ReprLower.cex_regCast_pair_offset_mismatch` | R8:CE | propext | `bf77c5d7bb56ab115d4ffee45cfaf458632444de9e8f17d4f7aa4c5e883685cd` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_pair_width_mismatch` | R8:CE | propext | `432bd61578a92d8a6206c7f81d1acc7bf85f4e92a1001bcdf0ad4b8b6a933d74` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_pair_width_mismatch_b` | R8:CE | propext | `002071222bc2dc3e5f318b667491669c32da216aa6f14c9b95194ba3b551b7c2` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_pair_overlap` | R8:CE | propext | `9b502dc43cfbc76ab1d30c804924363ea8de2c892f7a419bfdca9b660c60fa42` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_pair_out_of_bounds` | R8:CE | Classical.choice, Quot.sound, propext | `85b6e083ea1d4c6738f05602eb8cc7e41f2e36821f18090d1efbf05bfbc579d4` | `d78bc3470cb29a266ed633e2bdf0e872c7d5e27660103c0314046ec6ea664a6c` (96) |
| `Toy.ReprLower.cex_regCast_pair_discipline` | R8:CE | propext | `48fdec5cdfcb74330b3d9bd1144697f792ea7fdce8621a0cd0968b26f5bae9e5` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.cex_regCast_pair_discipline_b` | R8:CE | propext | `3f574ede4c214374b38048c2fdbbe8e163e1eaf9869b5ebe7643b894b766350b` | `2e0c13d0b0f80d6ae81795c03008eaac6b9d15f82fc285e367420d527a0a4d69` (95) |
| `Toy.ReprLower.nonvacuous_regCast_pair` | R8:NV | Classical.choice, Quot.sound, propext | `9d6b533d743ac11e2bd5ab9f4b48d9e427dba8d7c276b8a0755f119579ca0e9f` | `78e05f7433c757ae63e7284c1bf98db5301ef59dda8d053190244ad654df37e7` (96) |
| `Toy.ReprLower.regCast_pair_to_union_scalar_across_padding_disagrees` | R9:R | propext | `997708f2c163a367d280c205f779e0c0eb740fb9acbbd3fd77964e367469b40f` | `7d3f8140ad17397f5854b9435d3140197bc1be1588cc303cec04609d643a6342` (93) |
| `Toy.ReprLower.regCast_pair_to_union_scalar_agrees_of_no_padding` | R9:PC | Quot.sound, propext | `cb39332a14accddaaabb8b01a1fb9a92ce936f77aa0cf060e5bbdc1456a1445b` | `7eeee0034885e077a03acd77b54d5ccba0fb07877b1b03b5dc504385cc3f9178` (92) |
| `Toy.ReprLower.regCast_pair_to_union_scalar_agrees_no_padding_instance` | R9:PC | Quot.sound, propext | `49e298529c140e0444c40f9de5c39af4abc86e4c772274e0a4f49d6b75afdae0` | `7d3f8140ad17397f5854b9435d3140197bc1be1588cc303cec04609d643a6342` (93) |
| `Toy.ReprLower.provenanceAttachingCast_differs_from_transmute` | R10:R | propext | `02c8bcaad343c66c35da0fb04adf2c71467e5b97865ab6a3c893b01cea7986e5` | `8c051bb4cfba98750e840b2917ffec4f0a193eaab6c49b695b133176e118d818` (96) |
| `Toy.ReprLower.unionMove_trivial_defined_iff_size_and_readField_ub_iff_invalid` | R11:R | propext | `76d33a795aa99af88ed0b936d812d5734e0c3c8ffe4271d36502a65a82b9c30e` | `e6f10d57c62f5515e2792c08f78e79cd7152c52bed5f646ae19c34a9e9971d0b` (17) |
| `Toy.ReprLower.nonvacuous_unionMove_readField` | R11:NV | propext | `68261ba689ee30e83a4d53f672b246bd7569e347fe173c010ab78a9a2a3b896d` | `90b3d6fd711d2164f3379b22dd52cb64b52c71234a7060d81923a95f8821c7a1` (31) |
| `Toy.ReprLower.nicheInheriting_union_move_ub_after_valid_field_write` | R12:R | propext | `cf7bbc49d4d1b2a772af31f581ba095e26032c06158e4ab8f676920c1cbf9d9c` | `26cc91a5fcf22ea1cf518fcd5fe690336a15ccf23ba92c7f84db2981166c98ac` (33) |
| `Toy.ReprLower.unreachableRewrite_refines_iff_no_wholeValue_valid` | R13:R | Quot.sound, propext | `35347997341375c8c0d3d71cf110c74630b2b499d1759f01751e9241ac76d7fe` | `d9ae34625e2472b8c5d41035f8a8fa8afda7c5f39ca8f24a2c1179341fc7b61c` (26) |
| `Toy.ReprLower.cex_unreachableRewrite_gate_false` | R13:CE | Classical.choice, Quot.sound, propext | `ac53f88c1dd488faacc51141eeb365c3be3e8ad68fbd32164cea6c2aea90491a` | `206553dfda689199d3e9b2ba396aa778599d9b3b53a2889717c24c89aae58b0d` (28) |
| `Toy.ReprLower.nonvacuous_unreachableRewrite_iff` | R13:NV | (none) | `c963c09c001d66478f8154d74a4c7a5d24d080405b6f0317c50fc454760585b6` | `0d5d479acaf48b33c451427ea8afdf0bd020d965228c0051b6ed985bc2408117` (13) |
| `Toy.ReprLower.fieldwiseUninhabited_gate_not_refinement_of_trivialValidity` | R13b:R | propext | `455df43d3afbe20620604a2d0e7ad2c2bd603312a0a26e51e22076815b6e08a0` | `5f07eb867e74d16107c5654846c388d82b964692e102b67234e9bf477218252c` (31) |
| `Toy.ReprLower.cex_fieldwiseGate_never_fires` | R13b:CE | propext | `dddb92595dad5d6521f18d76cb8aa098f24f4b3cd5d4b95c3a3c4b6c603f6dcd` | `5f07eb867e74d16107c5654846c388d82b964692e102b67234e9bf477218252c` (31) |
| `Toy.ReprLower.nonvacuous_fieldwiseGate` | R13b:NV | (none) | `d2322c147fabbb7a6bb1ee47de50a6279ad71155fa858c90089efe1988ba972e` | `e5613734791f6cd998b4fba48bbff201f4696fbfcf7ddc4e151ea6cb264a6eb2` (11) |
| `Toy.ReprLower.gate_refines_of_emptyValidity` | R13b:PC | Quot.sound, propext | `fed58a3e3c90a09c523b7797de9b9e43d1778486f85f5f502cec063a91dbec39` | `94c132b6cbc16076d4b26d07cd1c2643651901eb0642f6b9637b84a6abb75a77` (28) |
| `Toy.ReprLower.writeBytes_frame` | R14:R | Quot.sound, propext | `9ce33ed5123505ff5eb5f3811b5878bf68dd0a36b16295f7ddec34778115b4a3` | `4a38dd75cc76c6e2d1e4e87f34df80a2f81e2638fbaee483807c41696cbaae37` (5) |
| `Toy.ReprLower.nonvacuous_writeBytes_frame` | R14:NV | propext | `faf2bc259c0e6d84ea870a71b82e59c4a60cf73b412248149f34c87ccb2adc76` | `4a38dd75cc76c6e2d1e4e87f34df80a2f81e2638fbaee483807c41696cbaae37` (5) |
| `Toy.ReprLower.readWider_after_partial_write` | R14b:R | Quot.sound, propext | `83b0dbf083b3aee05d9a2200a6d0b1aa0d30ebe3cef095109582ea9812f44e26` | `44dbb2c935b011aeedf78737188891c648659fe1676c12b4137aeef9aebab824` (6) |
| `Toy.ReprLower.cex_readWider_hj` | R14b:CE | propext | `30fb246703f6884616148b5cbc419bcec69c0ae65e729ecb58d7200955664ecd` | `44dbb2c935b011aeedf78737188891c648659fe1676c12b4137aeef9aebab824` (6) |
| `Toy.ReprLower.cex_readWider_hin` | R14b:CE | propext | `168fef8de78946a08c0d438f00d45b87d3f05500d0d07229be390ef95e5290fe` | `44dbb2c935b011aeedf78737188891c648659fe1676c12b4137aeef9aebab824` (6) |
| `Toy.ReprLower.nonvacuous_readWider` | R14b:NV | propext | `95b6e18de0a2595bcaef39dcb08419c17723c12a4ae4fd5d32ec1de4bddb9c0d` | `44dbb2c935b011aeedf78737188891c648659fe1676c12b4137aeef9aebab824` (6) |
| `Toy.ReprLower.unionRegister_mergeWrite_eq_memoryWrite` | R15:R, R16:S | Quot.sound, propext | `c51189668012c88ac7c84adeb0a6caf1a789bfd8a574f284aa5c51ff84803fb6` | `c2bf3f45d165b018c6cfa84f19f4e1a9829bf2a74444c423043d605a658cc843` (84) |
| `Toy.ReprLower.cex_mergeWrite_size_lt` | R15:CE | propext | `a128353d73b8eeffe553c75afd16e4b3fc6552512670a7c5b060cf4fd11a398f` | `c2bf3f45d165b018c6cfa84f19f4e1a9829bf2a74444c423043d605a658cc843` (84) |
| `Toy.ReprLower.cex_mergeWrite_hx` | R15:CE | propext | `c5c3b7c3784d4e0e50f531c968ccabaac82db9dc1f1a5fcb2aa52615b88e91b0` | `c2bf3f45d165b018c6cfa84f19f4e1a9829bf2a74444c423043d605a658cc843` (84) |
| `Toy.ReprLower.nonvacuous_mergeWrite` | R15:NV | propext | `86761565fa5129c94d2a299f078cb95e9498d7319f007f133a5e26530c067273` | `6a2f0f238f92f6592b9900a21166b5eb5df3d09752222dc23f2fa87548354b66` (83) |
| `Toy.ReprLower.wholeRegisterWrite_no_constant_fill_refines_partial_write` | R16:R | Classical.choice, Quot.sound, propext | `c3469de2774aa4991528bdf3a5b86530ee68d0b3e05b4db6f7d2720250364a79` | `15eadb40b09fa71754351c42d9cee7ae9c2c0a181eea812dc88886f0a78ee53d` (58) |
| `Toy.ReprLower.wholeRegisterWrite_uninit_and_zero_fills_instance` | R16:NV | propext | `b4532c38fff6206414bb53173eee1e2a59b441035abc571233b192676e065f60` | `599206f197a07e50d0b13441213d8351edec6b16b8c5214a10baf62775dacd0a` (48) |
| `Toy.ReprLower.wholeWrite_uninit_eq_writeBytes_of_untouched_uninit` | R16:PC | Quot.sound, propext | `6061422bab8405ad8eef0500e084ad9ea1333e3f6e091fdf6304932aecec9ad5` | `f5a24ff079f98ae787fd65360cabaa989f89537ac98ee071ff7c485d22a7de10` (33) |
| `Toy.ReprLower.wholeWrite_untouched_uninit_instance` | R16:PC | propext | `41d94c1d5ba7234d095dc8ab33fc0c2728dbc1b76b82ea87def7096883641e5b` | `f5a24ff079f98ae787fd65360cabaa989f89537ac98ee071ff7c485d22a7de10` (33) |
| `Toy.ReprLower.wholeWrite_eq_writeBytes_of_full_width` | R16:PC | Quot.sound, propext | `e032721df544801c341624dc2d6e832bbdc461ba05451077df752fa5827de915` | `f5a24ff079f98ae787fd65360cabaa989f89537ac98ee071ff7c485d22a7de10` (33) |
| `Toy.ReprLower.wholeWrite_full_width_instance` | R16:PC | propext | `642df03e6931747cac4951ec6f3c1d74a0bdd42ca5ba05da03e71e74f50d9884` | `f5a24ff079f98ae787fd65360cabaa989f89537ac98ee071ff7c485d22a7de10` (33) |
| `Toy.ReprLower.noundef_on_union_scalar_introduces_ub` | R17:R | Quot.sound, propext | `c63df1736546f67a9c98c89977f2093d4a3e145282100b8ba34d4f933db1bbb0` | `213c0b9447763608171e1df57ddeb5109b12b32cd65e01813736cd15740d7f46` (65) |
| `Toy.ReprLower.cex_noundef_width_zero` | R17:CE | propext | `9983763fcde8a9406354649c932175341a3e4733108bc535691f146cf03d26e9` | `213c0b9447763608171e1df57ddeb5109b12b32cd65e01813736cd15740d7f46` (65) |
| `Toy.ReprLower.nonvacuous_noundef_union` | R17:NV | propext | `626a0e9d98eb2619c34fe0e886ec7451749d603e8d7029ec408067477be1a55f` | `213c0b9447763608171e1df57ddeb5109b12b32cd65e01813736cd15740d7f46` (65) |
| `Toy.ReprLower.noundef_passes_initialized_nonpoison` | R17:PC | propext | `de039468dd77a37eec0d9e6500fe1055e8bd2586e8b42d469b3ad93c61c9b9eb` | `66c9446fd0455ffb6dc8b823e51599d6efc62f1acef8754da94da723ececf774` (64) |
| `Toy.ReprLower.nonvacuous_noundef_initialized` | R17:PC | propext | `a02d0683916d67ecff370f2df40bb23e012144e2bfab14c38e254b7b283acd2e` | `2af4d35f2bdf813537b011cf0fff0507383994b477119d117b45e2407e458331` (65) |
| `Toy.ReprLower.AByte` | R1:S, R2:S, R3:S, R4:S, R4b:S, R6:S, R9:S, R11:S, R13:S, R14:S, R14b:S, R15:S, R16:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.AByte.data` | R1:S | (none) | `afc95b381cfbb399db9b5b904d2b1c37bcdf05e02b862d4e2a313e48b20a3962` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.AByte.isBits` | R1:S | propext | `0cd36d40c68fc7081aea9982bab5e0ba3585bc7f29156ae2facdcf879344c1d3` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.AByte.isFrag` | R1:S | propext | `0cd36d40c68fc7081aea9982bab5e0ba3585bc7f29156ae2facdcf879344c1d3` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.AByte.isInit` | R1:S | propext | `0cd36d40c68fc7081aea9982bab5e0ba3585bc7f29156ae2facdcf879344c1d3` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.AByte.leb` | R1:S | propext | `ad66c4a08f3dd0ab9ed7271baaa9107e2fec686e53cad95dc39d0093df8f2cd5` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.BRepr` | R1:S, R2:S, R4:S, R4b:S, R5:S, R6:S, R7:S, R7b:S, R8:S, R9:S, R10:S, R15:S, R17:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.BRepr.comps` | R1:S | (none) | `2ab1c7d781ac8ace7905cb980471dfb00b77cde65a985fe8cd351a7eec36c5d2` | `65bf8dbc0bc999645a490ca3f4488287e505a7d063d8a3cf1ca333ec2f01a25d` (10) |
| `Toy.ReprLower.BRepr.inExtent` | R1:S | (none) | `2ef4498070ca764b6bdd305bfd8df8e1fd2659dbc7ac51a598abb356cb88df29` | `65bf8dbc0bc999645a490ca3f4488287e505a7d063d8a3cf1ca333ec2f01a25d` (10) |
| `Toy.ReprLower.BytesLe` | R1:S, R3:S, R7b:S, R10:S | propext | `b6115d55b4ed7620c946bd280b5b9a279069c9d5ff11effe81426ada2300e35b` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.InitUniform` | R1:S, R2:S | propext | `0a9d3a162204192364108734451b0346cd517602ff16a6839624c03f093ab347` | `51320f5898750bb01c3d180de5f459240cf75d6e12a6a1d8a3215478a583c5ad` (14) |
| `Toy.ReprLower.Lowered` | R1:S, R7:S, R7b:S, R9:S, R10:S, R15:S, R17:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.OutsideExtentsUninit` | R1:S, R2:S, R4:S | propext | `bbde97562af16fe0069b1bdb3c12f98b001776c39e955455d85da145ea25cc72` | `51320f5898750bb01c3d180de5f459240cf75d6e12a6a1d8a3215478a583c5ad` (14) |
| `Toy.ReprLower.ProvCoherent` | R1:S, R2:S | propext | `0a9d3a162204192364108734451b0346cd517602ff16a6839624c03f093ab347` | `51320f5898750bb01c3d180de5f459240cf75d6e12a6a1d8a3215478a583c5ad` (14) |
| `Toy.ReprLower.RVal` | R1:S, R7:S, R7b:S, R8:S, R9:S, R10:S, R15:S, R16:S, R17:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.RangeIncl` | R1:S, R2:S | propext | `0a9d3a162204192364108734451b0346cd517602ff16a6839624c03f093ab347` | `51320f5898750bb01c3d180de5f459240cf75d6e12a6a1d8a3215478a583c5ad` (14) |
| `Toy.ReprLower.RoundTripRefines` | R1:S, R2:S, R4:S, R4b:S, R5:S, R6:S | propext | `bbde97562af16fe0069b1bdb3c12f98b001776c39e955455d85da145ea25cc72` | `51320f5898750bb01c3d180de5f459240cf75d6e12a6a1d8a3215478a583c5ad` (14) |
| `Toy.ReprLower.Scalar` | R1:S, R2:S, R4:S, R4b:S, R5:S, R7:S, R7b:S, R8:S, R9:S, R10:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.Scalar.prim` | R1:S | (none) | `67350c2865ae9cdd4afeeaab92b3b01b856dd85efcf170fff71510e5e08740a2` | `3528f0c2486e998522df6098dfa5936ab29012d8be0ae9eb07f6bf8ff27edfc7` (6) |
| `Toy.ReprLower.Val.leb` | R1:S | propext | `5c4c4ef8f7e1f2d59cceb223b3a2a45fdfa249ee0a9e92a16415e386f79cc970` | `dd51e6ef75cfd9fae46ab60ca4f41f4f885a5abd82ac0598d62d4e53ffafa394` (3) |
| `Toy.ReprLower.allBits` | R1:S | propext | `ada306db897e6a8e0865e1fa3e93ceb822402fb8e756bb0e7deba3702bdf65d7` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.allInit` | R1:S | propext | `ada306db897e6a8e0865e1fa3e93ceb822402fb8e756bb0e7deba3702bdf65d7` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.allUninit` | R1:S | (none) | `ada306db897e6a8e0865e1fa3e93ceb822402fb8e756bb0e7deba3702bdf65d7` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.bytesLeb` | R1:S, R3:S, R7b:S, R10:S | propext | `08403d51d7ab39ce2e87a7219b4d3bd3bd25d787d20471409bd49dd2b26768c8` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.chunkAt` | R1:S | propext | `eeb79e4a8a7c9117b725f8c6fe40fe8788873494bcafaee2ea6f18cbeddbaa9b` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.coherentFor` | R1:S | propext | `2ccf7755cbb2709d1dcc1bc71112cfebb9a6876b778de9a99322c0cc246d1fb1` | `a0fe95eb32a55b54deb3b747c7f43bd5a3b8651d7cf983dc0084a5853ade0ed4` (7) |
| `Toy.ReprLower.datas` | R1:S | (none) | `78c7662604ed04bbc9da2b83e294db6271cd8b40c398264fc71247973c3167f1` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.fragProv` | R1:S, R3:S, R10:S, R15:S, R17:S | propext | `be1109ea36ef704b95602840d284ad3b4a5edbae0cc2c0c3e35ca627d5986f74` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.fragsFrom` | R1:S, R3:S, R10:S, R15:S, R17:S | propext | `8ff7438a45d90b93109814ff806fc968630a6a9f6c86e2f88f71e800f3031f5e` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.initUniformAt` | R1:S, R2:S | propext | `821ab4d7447e1398a3a603838c99f49b3f68550bd1076b1f089e43cf296c61e5` | `9f318c898250cc075e97e117835de25b68555c0ab335f7882979035a4739d9fe` (10) |
| `Toy.ReprLower.initialized_allUninit_roundTrips_but_noundef_ub` | R1:S, R2:S, R17:S | propext | `781b1ecc309aaf5a26d7ebe1dcbb3d70dc35b0fe1b9ec49a3aeb11feb754973f` | `475cf3ba510006745535d8578590a70d2c61edc01e4640ae9f7ff93f280a6329` (125) |
| `Toy.ReprLower.lower` | R1:S, R7:S, R9:S, R10:S, R17:S | propext | `29d875fcdd7194bb4470c43a54f973c1c57d15f344209ecd22fd275887c28642` | `565e2223eafac45e522b05bfe6967b82d0016638390f38544e69f01854773ec4` (23) |
| `Toy.ReprLower.nonZeroRange` | R1:S, R2:S, R5:S, R7:S | (none) | `c86502be0862017e6db1957514bf84e0a190be84d043a17fe2a28b1ce21a9d34` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.place` | R1:S | propext | `32cce1e18ea8fa6d3364de2dfd50cdbfbb8b56e7773b03c244a8df092bfa332b` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.provCoherentAt` | R1:S, R2:S | propext | `821ab4d7447e1398a3a603838c99f49b3f68550bd1076b1f089e43cf296c61e5` | `9f318c898250cc075e97e117835de25b68555c0ab335f7882979035a4739d9fe` (10) |
| `Toy.ReprLower.ptrProv` | R1:S, R3:S, R10:S, R15:S, R17:S | propext | `fdd6f6eb7334b5abb1d10ebfc3a3c17c40d25bfdcd737151c364672a0cccd9ce` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.raise` | R1:S, R7:S, R7b:S, R9:S, R10:S, R15:S | propext | `358f8179aefca3268f3e7141d4ed53815a4230a537ad8febff96ae380a21bfcc` | `565e2223eafac45e522b05bfe6967b82d0016638390f38544e69f01854773ec4` (23) |
| `Toy.ReprLower.raise_lower_bytesLe_self` | R1:S | Classical.choice, Quot.sound, propext | `f60e4ffbb7ef435ddcc46138ae1a860da8e87eb45b24c2f33dd339b4e86dd2e3` | `99320e1e50fcc4bde46b4154b5bbeafd9a3ddc88783cf440a52ece22fea78111` (61) |
| `Toy.ReprLower.rangeInclAt` | R1:S, R2:S | propext | `821ab4d7447e1398a3a603838c99f49b3f68550bd1076b1f089e43cf296c61e5` | `9f318c898250cc075e97e117835de25b68555c0ab335f7882979035a4739d9fe` (10) |
| `Toy.ReprLower.scalar_bytesLe_roundTrip_iff` | R1:S | Classical.choice, Quot.sound, propext | `73f2a53b2e5a5ea39917f05438c1a8a0da7052f28d99803c50c7ccb88363cf13` | `1e1c25ad3aabbeffe74719413a3dc591e60e1449a49336880d1979988333300b` (112) |
| `Toy.ReprLower.scalar_conditions_of_roundTrip_refines` | R1:S | Classical.choice, Quot.sound, propext | `7e2b33213a18089ae77003199fb8057ef5fd08493431557931016495bed3a3ef` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.seg` | R1:S, R11:S, R14b:S, R15:S | (none) | `0366295a20c5b7fc0f63125e8c9c6a759a05f106ee3c68175497b8b5fa172795` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.typedReads_agree_without_bytesLe` | R1:S, R2:S, R3:S | Classical.choice, Quot.sound, propext | `c94f767efc30ca9361871e7693f4980c705cff379f35fbdd15b2aa6cbd59d40e` | `81c5a61b27e8da5f107e8b0912a62b19c3d13ebfadd1259b3e46b9cedf21c839` (37) |
| `Toy.ReprLower.pair_bytesLe_roundTrip_iff` | R2:S | Classical.choice, Quot.sound, propext | `608eda053b11bfda2a7a401f1df475b3e4aa9823ce951aa760e41ea4f1e4ba58` | `1e1c25ad3aabbeffe74719413a3dc591e60e1449a49336880d1979988333300b` (112) |
| `Toy.ReprLower.pair_conditions_of_roundTrip_refines` | R2:S | Classical.choice, Quot.sound, propext | `191301b257df2109b6d5155ab66cef3fa88e38459e9c8563f1583539d8f931e8` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.pair_roundTrip_refines_of_conditions` | R2:S | Classical.choice, Quot.sound, propext | `bc14c937f3168de777cd2dbf76be8cadcdd7e246f414648646f5c1dadd7be781` | `0cdd7323e73bfeaa22cab9094f900714184bb9e40a14725782ddbb88169ff5d2` (119) |
| `Toy.ReprLower.OutLe` | R3:S, R13:S, R13b:S, R16:S | propext | `0a75ee4cd79d36c745a20bc52e746c219d83ebd0bb2da91eda91db6e565b0e38` | `dd51e6ef75cfd9fae46ab60ca4f41f4f885a5abd82ac0598d62d4e53ffafa394` (3) |
| `Toy.ReprLower.Val` | R3:S, R13:S, R13b:S, R16:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.readInt` | R3:S, R16:S | propext | `ab29bd84bcde25f10a6bc4cdf9ffec840ef7db5580e13dea3e1954b5bc6e36ca` | `99df0a01262f9fe26f5ca60e55103050eeb7bca355c8851c4821b58926d73110` (7) |
| `Toy.ReprLower.readInt_readPtr_width_zero` | R3:S | propext | `26c0e6e3e47b715802f4211fe125c74609da063a541c2458fb733689ba5d905f` | `625e006df83b7dbc526d217f914ecdd6ce0fcb42494c98d975ed23b5090d5b94` (29) |
| `Toy.ReprLower.readPtr` | R3:S | propext | `ab29bd84bcde25f10a6bc4cdf9ffec840ef7db5580e13dea3e1954b5bc6e36ca` | `99df0a01262f9fe26f5ca60e55103050eeb7bca355c8851c4821b58926d73110` (7) |
| `Toy.ReprLower.Prim` | R4:S, R4b:S, R5:S, R9:S, R15:S, R17:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.provenanceStripping_register_not_refines` | R4:S, R4b:S | propext | `f2d71f6b51c7d2f05500fd29ebd2e1c59e47a9fd8de4d6b63ac0a3f87d36c428` | `4ac081e45c7fcc733c0964d252851cefc4c109361c383358295ed6dfc35e7f53` (20) |
| `Toy.ReprLower.stripProv` | R4:S, R4b:S, R7:S | propext | `590b60b1346bd41167922e61c268f885f7bae13640ad89e70b44b972ad586a20` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.CastAgrees` | R7:S, R7b:S, R8:S, R9:S | propext | `131403eb9eb7ada2c26e03d7a8a4d52fb32eec2cec438eb3fd4d19a24a0d9ada` | `65bf8dbc0bc999645a490ca3f4488287e505a7d063d8a3cf1ca333ec2f01a25d` (10) |
| `Toy.ReprLower.DisciplineCompat` | R7:S, R8:S | (none) | `de6ff02037f61857a9ff51caac45c33c77ec9e60803822380f65de874d88c494` | `3528f0c2486e998522df6098dfa5936ab29012d8be0ae9eb07f6bf8ff27edfc7` (6) |
| `Toy.ReprLower.fullRange` | R7:S, R7b:S, R9:S, R10:S | (none) | `c86502be0862017e6db1957514bf84e0a190be84d043a17fe2a28b1ce21a9d34` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.len2Range` | R7:S, R7b:S, R8:S | (none) | `c86502be0862017e6db1957514bf84e0a190be84d043a17fe2a28b1ce21a9d34` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.regCast` | R7:S, R7b:S, R9:S, R10:S | propext | `a82f9fd8875ed1961d8396351977010d7160a2bce6508838178aae6b01effbba` | `565e2223eafac45e522b05bfe6967b82d0016638390f38544e69f01854773ec4` (23) |
| `Toy.ReprLower.regCastScalar` | R7:S, R7b:S, R8:S | (none) | `fb4dced07614add60e4452f1dd5cc14aa8553b37fc6ad679bac432e26896abb7` | `8a80b88988a22a9a2594d55204f0fbce7405b6be057e84b3675aba1519a48dd3` (15) |
| `Toy.ReprLower.regCastScalarStrip` | R7:S | propext | `fb4dced07614add60e4452f1dd5cc14aa8553b37fc6ad679bac432e26896abb7` | `8a80b88988a22a9a2594d55204f0fbce7405b6be057e84b3675aba1519a48dd3` (15) |
| `Toy.ReprLower.regCastStrip_width1_union_to_initialized_agrees` | R7:S | propext | `2c12b70137f4fb43b5a5bb633870d3dcf051f4af46dc3ee1baa970a86331ae5e` | `e16aa95863676a1763a619736aff6f9df48dd33f13eca8f1d54555deecf017da` (87) |
| `Toy.ReprLower.regCast_int_to_ptr_agrees` | R7:S | Classical.choice, Quot.sound, propext | `6fa2d9e2b42782e13c2eb9cd75d759e3960ae6829759c36dbbdb21d99ef34a47` | `7d3f8140ad17397f5854b9435d3140197bc1be1588cc303cec04609d643a6342` (93) |
| `Toy.ReprLower.regCast_scalar_agrees_of_disciplineCompat` | R7:S | Classical.choice, Quot.sound, propext | `020c34919e08ce21165d0738adace8efc6faf8c3dec8124a7bd215ec9401b6ab` | `751e94b757ae41d03eb25989377a42af31ebe3930dabd419502a9a2d49b0ee2c` (94) |
| `Toy.ReprLower.CastRefines` | R7b:S | propext | `131403eb9eb7ada2c26e03d7a8a4d52fb32eec2cec438eb3fd4d19a24a0d9ada` | `65bf8dbc0bc999645a490ca3f4488287e505a7d063d8a3cf1ca333ec2f01a25d` (10) |
| `Toy.ReprLower.DisciplineCompatAnyLen` | R8:S | (none) | `de6ff02037f61857a9ff51caac45c33c77ec9e60803822380f65de874d88c494` | `3528f0c2486e998522df6098dfa5936ab29012d8be0ae9eb07f6bf8ff27edfc7` (6) |
| `Toy.ReprLower.emptyRange` | R8:S | (none) | `c86502be0862017e6db1957514bf84e0a190be84d043a17fe2a28b1ce21a9d34` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.regCast_pair_agrees_despite_offset_mismatch_of_empty_range` | R8:S | propext | `9f19d04198143c5c1f63c54ccb2baa731c7ab2a966bb56cd9f8c3c2a37e33266` | `75eca93dea7f0da7055fea3e296498f525dee8bcbcd6ef6bfd44c746f982f073` (94) |
| `Toy.ReprLower.regCast_pair_agrees_of_offsetEq_disciplineCompatAnyLen` | R8:S | Classical.choice, Quot.sound, propext | `a264ef0dd4d667f16a636f7fef478af6d6f0d660b4f7bfa9ec07c0253d406e17` | `f2eb7167e01d380c3a83dde8bb1c0d57048fb12ffb6a870457c521b0d784b5d8` (94) |
| `Toy.ReprLower.attachProvCast` | R10:S | propext | `2e567c1a96cc4000a2a23c359f3d2e17c49752060c030b60dfa240602549c79a` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.bytesLe_bits_ptrFrag_attach` | R10:S | propext | `f7c5f003795934e3973befd7633da8b644bb928f2f150fe50dded018d4a33344` | `030f66ea2c4903a46a042b4c17ef96f34cd7590794a5e96777128ddf833e1a61` (17) |
| `Toy.ReprLower.lowerScalar` | R10:S, R15:S, R17:S | propext | `debf7e5ed587d49b0bdbb4291764e75d207a83f5381e3250cc8d9f3956ea0302` | `8a80b88988a22a9a2594d55204f0fbce7405b6be057e84b3675aba1519a48dd3` (15) |
| `Toy.ReprLower.ptrLower` | R10:S, R15:S, R17:S | propext | `1900955b19ec73eb87f33bb3c978bbfbf4b44c4b1d19aa6090ad54a711de315a` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.Prim.size` | R11:S, R13:S, R13b:S | (none) | `21b59cefa7610711a4f6f04430cbb153ab134e0311a0ca20f9e0255c5184426c` | `314c13ee185c0e1b6542f07df97b61fae9cea33baec2597c3579d460dcba8f6b` (3) |
| `Toy.ReprLower.Scalar.size` | R11:S, R13:S, R13b:S | (none) | `bef5d77a57ba262b5cd243dece80fa0c76dc4ff5f0d77c1fad285e840b80ef07` | `3528f0c2486e998522df6098dfa5936ab29012d8be0ae9eb07f6bf8ff27edfc7` (6) |
| `Toy.ReprLower.UField` | R11:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.UnionTy` | R11:S, R13:S, R13b:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.readField` | R11:S, R12:S | (none) | `319538cd1e1c2ea22a6f2c4acd5a473b4cad9f8283ccfbecb7080d46d6c1ebf8` | `2b52df22114b85cd50ec1b69c86348ced4fa0005c5982ee3f4759fe98027a489` (6) |
| `Toy.ReprLower.trivialUnionValidity` | R11:S, R12:S, R13:S, R13b:S | (none) | `2bdb72006ab24d463429a2bd0896f3be2ea8b7be0a56dfa111463de77ff66a58` | `6d161ef6a702caf3978d208dd0d2d7d9134b1b93047782eeb6cbcc3cc9d46626` (9) |
| `Toy.ReprLower.unionMove` | R11:S, R12:S | (none) | `b3c97fe5c3d460bf1f630c07f611b71273b749e2df7c8fe5cae913d64988ea34` | `6d161ef6a702caf3978d208dd0d2d7d9134b1b93047782eeb6cbcc3cc9d46626` (9) |
| `Toy.ReprLower.nicheInheritingMove` | R12:S | (none) | `319538cd1e1c2ea22a6f2c4acd5a473b4cad9f8283ccfbecb7080d46d6c1ebf8` | `2b52df22114b85cd50ec1b69c86348ced4fa0005c5982ee3f4759fe98027a489` (6) |
| `Toy.ReprLower.nonZeroU8Field` | R12:S | propext | `3fb235046047bcfab88ba2755ac84ce20511d4d22801959c8ccf62d44aa4501a` | `2b52df22114b85cd50ec1b69c86348ced4fa0005c5982ee3f4759fe98027a489` (6) |
| `Toy.ReprLower.nzOrU8` | R12:S | propext | `a74bfd5ffecb913ceeab05e475c063189682a13632a159ae41f11345f2483b8e` | `34a1e052504c1e60157f8bbc7223da3d9e7a7bfcd68f4c8104fefae2b8e3d9e2` (8) |
| `Toy.ReprLower.u8Field` | R12:S | propext | `3fb235046047bcfab88ba2755ac84ce20511d4d22801959c8ccf62d44aa4501a` | `2b52df22114b85cd50ec1b69c86348ced4fa0005c5982ee3f4759fe98027a489` (6) |
| `Toy.ReprLower.writeBytes` | R12:S, R14:S, R14b:S, R15:S, R16:S | propext | `27c4561ec552c64c9a6a4eb995cb20362eec902e429c15ff70e46809c19174cd` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.UnionValidity` | R13:S | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.emptyUnionValidity` | R13:S, R13b:S | (none) | `2bdb72006ab24d463429a2bd0896f3be2ea8b7be0a56dfa111463de77ff66a58` | `6d161ef6a702caf3978d208dd0d2d7d9134b1b93047782eeb6cbcc3cc9d46626` (9) |
| `Toy.ReprLower.gatedUnreachable` | R13:S, R13b:S | (none) | `be09048fc25e979cc047bdfd463faba2b7d3ba7c18e709748110ba4c44a5208b` | `dd51e6ef75cfd9fae46ab60ca4f41f4f885a5abd82ac0598d62d4e53ffafa394` (3) |
| `Toy.ReprLower.moveThenRet` | R13:S, R13b:S | (none) | `1d46abdd87db9058d37bfca647d40a4f9d5fe7824325c4139b3621f498b6609c` | `2734e2bac12934be5aa9a4008df0aa0b800c1f940557e917c14a960f35b9f6c1` (12) |
| `Toy.ReprLower.neverUnion` | R13:S, R13b:S | (none) | `a74bfd5ffecb913ceeab05e475c063189682a13632a159ae41f11345f2483b8e` | `34a1e052504c1e60157f8bbc7223da3d9e7a7bfcd68f4c8104fefae2b8e3d9e2` (8) |
| `Toy.ReprLower.FieldwiseUninhabited` | R13b:S | (none) | `6491dda59120ec28fe2eb026af04999d23a771d2ad763abce5ac6c86943803c6` | `34a1e052504c1e60157f8bbc7223da3d9e7a7bfcd68f4c8104fefae2b8e3d9e2` (8) |
| `Toy.ReprLower.laneSelect` | R15:S | (none) | `0cc80d817c44fb0ad371c0b4def414f06d4ea9c5d47aaf7c9cdaf475283b851b` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.mergeWrite` | R15:S | propext | `36b3e291f18703c577b753ca39677dabaa06fecd14447a837911bfd11d4065a8` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.shiftIn` | R15:S | propext | `4c61da4f17393791be0a9d026b80151e572d93f463e75aaf1f24ca02b7e8dc71` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.writeMask` | R15:S | (none) | `e1c625df3222750f173e3cbf0b16bb3f8d92e7144080efa8ac9ef06dcea63350` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.ReprLower.fragsList` | R16:S | (none) | `8256cdc0f4441522150d8ad794078555d001f94c5548c6ab1956e46eec706b7d` | `3e93d41b10d9376120e3972e0f478dfbcbbe45e6c74ce744af1e467fa56467f1` (4) |
| `Toy.ReprLower.raiseScalar` | R16:S | (none) | `cf0083e11d26c8ab6b4e4990d736cd357722d6495fc3d29127a7e002687b584c` | `8a80b88988a22a9a2594d55204f0fbce7405b6be057e84b3675aba1519a48dd3` (15) |
| `Toy.ReprLower.wholeWrite` | R16:S | propext | `fd85a389120b845efe209021a8858692daa624b3d63f4b03490f381e5b1b395c` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.wholeWrite_bits0_incomparable_with_partial` | R16:S | propext | `bb52b86d1e51168640921bb9df3b25a6a9d30b1d7a64e6d58e3bd66f162ae765` | `15eadb40b09fa71754351c42d9cee7ae9c2c0a181eea812dc88886f0a78ee53d` (58) |
| `Toy.ReprLower.wholeWrite_init_fill_never_strictly_less_defined` | R16:S | Quot.sound, propext | `9ae84686df7515a646cc8dc9215ff40d0c7c7b657a4e2af04fbc412c357297e3` | `15eadb40b09fa71754351c42d9cee7ae9c2c0a181eea812dc88886f0a78ee53d` (58) |
| `Toy.ReprLower.wholeWrite_uninit_fill_strictly_less_defined_instance` | R16:S | propext | `a7e07b71ea3a66f1d7d790ac1ff72a82b6b6a954d71cbf6f4c0c34e67dea85cc` | `15eadb40b09fa71754351c42d9cee7ae9c2c0a181eea812dc88886f0a78ee53d` (58) |
| `Toy.ReprLower.hasUndef` | R17:S | propext | `43144e876fcaca10311edf040760182502a232a7f37f871625bee85c1b83699c` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.passArg` | R17:S | propext | `e7d88062db737bd589a0538a55da1db71d84b2859e4baa806f3f614a95ae63de` | `8202474c2ec2b17bc172e6b83948b25a5b260d19bdbe535795492bed45666413` (9) |
| `Toy.ReprLower.passArg_noundef_union_eq_none_iff` | R17:S | Classical.choice, Quot.sound, propext | `20d63406149beb44ccae612abbc1e031648633287ac6d435c1ad32cc6c90352f` | `66c9446fd0455ffb6dc8b823e51599d6efc62f1acef8754da94da723ececf774` (64) |

### Primary sources

Each pinned file below was fetched at the recorded commit on 2026-11-21, and every quoted line
range under **Findings → Modeling bridge to documented designs** was compared with that file at
that commit and found verbatim. Each recorded commit was checked to be contained in the
repository's default branch on that date.

- **rustc**, `rust-lang/rust` at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`:
  `compiler/rustc_abi/src/lib.rs` lines 1515-1535 (`Scalar`), 1779-1788 (`BackendRepr`
  documentation) and 1793-1805 (`ScalarPair`); `compiler/rustc_middle/src/mir/syntax.rs` lines
  328-335 (`Assign` overlap note); `compiler/rustc_const_eval/src/interpret/operand.rs` lines
  26-42 (`Immediate`) and 597-602 (`MaybeUninit<u64>` comment). Role: documentation and source,
  cited in `derived (modeling bridge)` prose.
- **MiniRust**, `minirust/minirust` at commit `063d784186d3252bee242217f218223205c0b568`:
  `spec/lang/representation.md` lines 100-103 and 117-131 (pointer decoding and provenance),
  313-319 (unions; lines 322-342 encode a union from its chunks), 652-669 (`le_defined` on
  abstract bytes), 754-756 (monotonicity laws; lines 759-763 state the round-trip law). Role:
  documentation, cited in `derived (modeling bridge)` prose.
- **LLVM Language Reference**, `llvm/llvm-project` at commit
  `a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6`: `llvm/docs/LangRef.md` lines 1736-1740
  (`noundef`) and 1954-1967 (`range`). Role: documentation, cited in `derived (modeling bridge)`
  prose; no LLVM behaviour was executed.
- **The Rust Reference**, `rust-lang/reference` at commit
  `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`: `src/behavior-considered-undefined.md` lines
  145-146 (`r[undefined.validity.union]`). Role: normative text, cited in
  `derived (modeling bridge)` prose.
- **CompCert**, `AbsInt/CompCert` at commit `2685140bf72c959446981fb99b5e44a8975021bc`:
  `common/Memdata.v` lines 209-212 (`Inductive memval` with `Undef`, `Byte`, `Fragment`), line
  908 (`Theorem decode_val_inject`), line 985 (`Definition memval_lessdef`), and the `Many32` /
  `Many64` memory chunks. Role: prior art.
- **X. Leroy and S. Blazy.** "Formal verification of a C-like memory model and its uses for
  verifying program transformations." Journal of Automated Reasoning 41(1):1–31, 2008. DOI
  10.1007/s10817-008-9099-0.
- **J. Lee, Y. Kim, Y. Song, C.-K. Hur, S. Das, D. Majnemer, J. Regehr, N. P. Lopes.** "Taming
  Undefined Behavior in LLVM." PLDI 2017, pp. 633–647. DOI 10.1145/3062341.3062343.
- **N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr.** "Alive2: Bounded Translation Validation
  for LLVM." PLDI 2021, pp. 65–79. DOI 10.1145/3453483.3454030.
- **J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis.** "A Formal C Memory
  Model Supporting Integer-Pointer Casts." PLDI 2015, pp. 326–335. DOI 10.1145/2737924.2738005.
- **F. Besson, S. Blazy, P. Wilke.** "CompCertS: A Memory-Aware Verified C Compiler Using a
  Pointer as Integer Semantics." Journal of Automated Reasoning 63(2):369–392, 2019. DOI
  10.1007/s10817-018-9496-y.

For the papers, the bibliographic data (title, authors, venue, DOI) were checked on 2026-11-21;
the section-level content attributed to them on the cards is a summary of their subject matter
and was not re-checked against the full texts on that date.

**Novelty search.** A web search on 2026-11-21 for mechanized results on scalar-pair register
lowering with initialization and provenance found no mechanized characterization of this form;
the closest material is the rustc interpreter source, the MiniRust specification and the CompCert
memory model cited above. An LLVM "byte type" that would let registers carry uninitialized and
provenance-carrying bytes is an open, unmerged proposal and is not relied on. Tiers are T0 and T1;
no T3 claim is made.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; the Lean project has no dependencies.

**Primary check (one command).** From the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`,
rejects any Lean source containing `sorry`, `admit`, `native_decide` or an `axiom`
declaration, and then elaborates an inline audit program that (1) computes, with Lean's
`collectAxioms`, the axioms of every declaration of the `ToyReprLower` library and fails if any
uses an axiom other than `propext`, `Classical.choice`, `Quot.sound`; and (2) for every Lean
name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`,
`positive_control_lean`, and hypothesis `counterexample`s) recomputes two SHA-256 hashes and
compares them with `audit/statements.json`:

- the **statement hash**: SHA-256 of `toString (repr ci.type)`, the Lean `repr` of the
  declaration's elaborated type;
- the **closure hash**: SHA-256 of the newline-joined, sorted list of entries
  `name : repr(type)` (plus ` := repr(value)` for non-theorems) for every constant of the
  `ToyReprLower` library reachable from the statement's type through types, definition bodies
  and inductive constructors (theorem bodies excluded). A change to any definition a statement
  depends on therefore changes its closure hash.

It prints `REVALIDATED` and exits with status 0 iff every check passes. Expected output ends
with `ok   axioms (641 declarations)`, `ok   statement hashes (188 hashed names; 0
referenced names exist but carry no recorded hash)` and `REVALIDATED`.

**Manual equivalent.**

```sh
cd lean
lake build                              # builds library ToyReprLower; must succeed with no `sorry` warnings
lake env lean RevalidationAudit.lean    # prints `#print axioms` for every name cited in REPORT.md
```

`lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`).
It imports `ToyReprLower` and issues `#print axioms` for every package-local Lean name cited in
`REPORT.md` or `results.json` (207 names); elaboration fails if any name is missing, and
each printed line must list only (a subset of) `propext`, `Classical.choice`, `Quot.sound`. The
recorded per-declaration axioms are in `audit/axioms.json`.

**Cheaper discriminating checks.** If only the Lean toolchain changes, re-running the primary
check is sufficient: a changed elaboration of any statement or definition shows up as a hash
mismatch even when the build succeeds. If a definition in `lean/ToyReprLower/` is edited, every
card whose closure includes it is stale; the closure hashes identify which. A passing
revalidation establishes the kernel-checked statements and nothing more; it does not re-check any
modeling-bridge claim or citation, which must be re-read against the pinned sources listed under
**Evidence** (for example by re-fetching each quoted file at its recorded commit and comparing
the quoted line ranges).
