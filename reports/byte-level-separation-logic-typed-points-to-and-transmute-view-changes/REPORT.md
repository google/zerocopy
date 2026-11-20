# Byte-level separation logic: typed points-to, struct padding, transmute view changes, and the frame rule — formalized results in Lean 4

## Summary

This package mechanizes, in Lean 4 without Mathlib, a small separation logic over a heap of
*abstract bytes* (each byte `uninit` or `init d`) with a two-point permission algebra (`full`,
and an idempotent read-only `ro` that may be shared). On top of byte points-to it compares two
typed points-to assertions built from a byte representation `r = (encode, decode)`: the
**encode-based** `ptsEnc` (the cells hold exactly `r.encode v`) and the **decode-based** `ptsDec`
(the cells hold some bytes `x` with `r.decode x = some v`). It characterizes when they coincide,
when struct ownership splits into field ownership plus padding, when a transmute is a pure
*view change* (an entailment between typed points-to at the same address), how read-only typed
views coexist, and which byte-level and typed commands satisfy the frame rule. Everything is a
toy model; see **Applicability** for what it is meant to capture and the known gaps. The
representation vocabulary (abstract bytes, the three laws `DecodeMono`, `DecodeEncode`,
`EncodeLeast`, `IntoBytes`, `FromBytes`, `transmute`) and the separation-structure vocabulary
(commands, triples, `SafetyMono`, `FrameProp`, `FrameRuleSound`) are copied unchanged from two
published packages of this corpus, `byte-representation-galois-laws-and-transmute-composition`
and `frame-rule-locality-and-precise-assertions` (details under **Applicability**).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (result ids are used throughout; Lean names are under **Findings**):

* **R1a** (characterization) — For every n-byte representation (no law assumed), the encode-based typed points-to entails the decode-based one at every permission, address, value and heap exactly when the representation satisfies `DecodeEncode`.
* **R1b** (characterization) — For every representation (no law assumed), the decode-based typed points-to equals the byte-definedness upward closure of the encode-based one (the same cells and permissions, with zero or more `uninit` bytes initialized) at every permission, address, value and heap if and only if `DecodeMono`, `DecodeEncode` and `EncodeLeast` all hold.
* **R1c** (characterization) — Under the three laws and a nonempty byte payload type, the decode-based and encode-based typed points-to coincide everywhere exactly when the representation is `IntoBytes` (no encoding contains `uninit`).
* **R1d** (counterexample) — For the lawful padded representation `u8PadRep` (a `u8` followed by one padding byte), a block whose padding byte is initialized satisfies the decode-based but not the encode-based typed points-to; with `uninit` padding both hold.
* **R2a** (characterization) — For a two-field layout whose fields do not overlap (`NonOverlap`) and any field representations (no laws), the decode-based struct points-to at permission `p` splits exactly into the decode-based points-to of the two fields and the padding cells with arbitrary contents, all three at `p`.
* **R2b** (characterization) — Under the same `NonOverlap` hypothesis (no laws), the encode-based struct points-to at `p` splits exactly into the encode-based points-to of the two fields and the padding cells all holding `uninit`, all three at `p`.
* **R2c** (counterexample) — For a model of `#[repr(C)] struct S { a: u8, b: u16 }` whose padding byte is initialized, the two mixed pairings fail: encode-based fields plus arbitrary padding do not join to the encode-based struct, and the decode-based struct does not split into decode-based fields plus `uninit` padding.
* **R3a** (characterization) — For equal-size representations (no laws), the encode-based points-to of `v` at `A` entails the decode-based points-to of `b` at `B` at every permission, address and heap exactly when `transmute rA rB v = some b`.
* **R3b** (characterization) — If `A` satisfies `DecodeEncode` and `EncodeLeast` and `B` satisfies `DecodeMono`, the decode-based points-to of `v` at `A` entails that of `b` at `B` everywhere exactly when `transmute rA rB v = some b`.
* **R3c** (theorem) — If `A` is `IntoBytes` and satisfies `EncodeLeast`, every successful `transmute rA rB v = some b` yields an entailment from the decode-based points-to of `v` at `A` to that of `b` at `B`, with nothing assumed about `B` (the entailment is vacuous if `A`'s decoder accepts nothing, since `DecodeEncode` of `A` is not assumed).
* **R3f** (theorem) — If moreover `B` is `FromBytes`, then for every `v` such a `b` exists (the result of the transmute) and the entailment holds (again vacuous for a source decoder that accepts nothing).
* **R3d** (counterexample) — Viewing a `bool` (`boolRep`) as a `u8` is a view change for every value, but the reverse is not: the block `[init 2]` holds the `u8` 2 and no `bool`.
* **R3e** (counterexample) — Viewing a two-byte integer (`pairRep`) as a `u8` followed by padding (`u8PadRep`) is a view change for every value, but the reverse is not: `[init 5, uninit]` holds the padded value 5 and no two-byte integer.
* **R4a** (characterization) — Two read-only decode-based typed points-to of equal size at the same address hold separately in a heap exactly when it is one read-only block of bytes that decode to both values, so they are jointly satisfiable iff such bytes exist; two read-only encode-based typed points-to are jointly satisfiable iff the two encodings are equal.
* **R4b** (impossibility) — For equal nonzero sizes, if at least one of the two permissions is `full`, no heap satisfies the separating conjunction of two decode-based typed points-to at the same address.
* **R5a** (characterization) — In every separation structure (no algebraic law assumed), the frame rule is sound for a command iff the command is safety-monotone and has the frame property.
* **R5b** (theorem) — On the byte heap with read-only sharing, the byte store and byte copy, and the typed store, typed copy and typed load at every representation (no laws), are safety-monotone and have the frame property; and if `h` and a frame are disjoint (`hd`) and the cells read are allocated in `h` with bytes `x` (`hr`), the read returns `x` with the frame on either side.
* **R5c** (theorem) — The loose typed copy, which reads unallocated source cells as `uninit` instead of faulting, is safety-monotone and has the frame property whenever the representation satisfies `DecodeMono`.
* **R5d** (counterexample) — The loose byte copy (an unallocated source cell read as `uninit`) is safety-monotone but violates the frame property, and the frame rule fails for it.
* **R5e** (counterexample) — A byte store permitted through a read-only cell is safety-monotone but violates the frame property, and the frame rule fails for it.
* **R5f** (counterexample) — For every byte payload type, the byte heap with read-only sharing is a partial commutative monoid with unit that is not right-cancellative.

What these results do **not** show is listed first under **Boundaries** (per result); the
non-claims rule out tempting stronger readings (temporary `&mut` reborrowing, alignment, interior
mutability, provenance, more general layouts, allocation, concurrency, and zerocopy's exact trait
semantics) and must be read together with the claims.

## Applicability

### Model fidelity

This is a **toy model** (namespace `Toy.ByteSL`), not a model of any production verifier's
definitions. It is meant to capture the byte-level ownership reasoning a verifier for low-level
Rust (or C) needs when padding, uninitialized memory and reinterpretation of memory at another
type are visible:

* **Bytes.** `AByte D` is MiniRust's notion of an abstract byte without provenance in the
  examples: `uninit` or `init d`. The definedness order has `uninit ⊑ x` and
  `init a ⊑ init b ↔ a = b`. The payload type `D` is a parameter of every general theorem; the
  concrete examples use `Byte := UInt8`.
* **Representations.** A representation `r : Rep (Bytes D n) V` is a pair
  `encode : V → Bytes D n`, `decode : Bytes D n → Option V`, read as MiniRust's representation
  relation: a typed store of `v` writes `r.encode v`; a typed load succeeds with `v` when
  `r.decode` of the bytes is `some v`. The laws `DecodeMono`, `DecodeEncode`, `EncodeLeast` are
  MiniRust's "generic properties" of the representation relation, kept as separate hypotheses.
  `IntoBytes` (no encoding contains `uninit`) and `FromBytes` (every fully initialized byte vector
  decodes) are semantic predicates named after zerocopy's traits; they are not those traits.
* **Heap and permissions.** A byte heap maps natural-number addresses to cells
  `⟨perm, byte⟩` with finite support. `perm` is `full` (exclusive: needed to write, like an owner
  or a `&mut`) or `ro` (read-only and freely duplicable, like a shared reference to memory
  without interior mutability). Two heaps are disjoint when every address allocated in both holds
  the same read-only cell in both; union is pointwise and left-biased. So two read-only views may
  share cells; a full cell is never shared.
* **Typed points-to.** `ptsEnc p r a v` (the heap is exactly the `n` cells at `a` with permission
  `p` holding `r.encode v`) models "memory holds what a typed store of `v` wrote", padding
  included; `ptsDec p r a v` (the heap is exactly those cells holding some `x` with
  `r.decode x = some v`) models "a typed load at `a` yields `v`".
* **Structs.** `Layout2` is a two-field layout (field 1 at offset 0, field 2 at offset `off₂`,
  both within `size`), the shape `#[repr(C)]` gives a two-field struct; `structRep` decodes each
  field from its own byte range and never reads padding, and encodes padding as `uninit`, as
  MiniRust's struct representation does.
* **Commands.** Commands are relations from a heap to an outcome (`fault` or a new heap), faulting
  when they touch memory without the required permission (reads need any permission, writes need
  `full`). There is no variable store: a typed load's value is observable only by writing it back
  (`tcopy`) or not at all (`tload`).

**Known gaps** (each also recorded per result under **Boundaries**): no alignment; no interior
mutability; no provenance in the examples (the payload `D` is generic, but nothing here uses
provenance-carrying bytes); only two-point permissions (no fractions, no recombination of read
permissions into a full one, no temporary borrows or lifetimes); only two-field structs with the
first field at offset 0 (no nesting, enums or unions; one union-like layout appears only as a
counterexample); transmutes only between representations of equal size at the same address; no
allocation or deallocation; no concurrency; decoders depend on the bytes only (MiniRust's
machine-state-dependent `check_value` is not modeled).

### Relation to the published packages of this corpus

This package depends on no other package at build time; it copies code instead.

* `lean/Toy/ByteSL/ReprBasic.lean` and `lean/Toy/ByteSL/ReprExamples.lean` are the support files
  `lean/ToyRepr/Basic.lean` and `lean/ToyRepr/Examples.lean` of the published package
  `byte-representation-galois-laws-and-transmute-composition` (google/zerocopy branch `reference`,
  commit `c659d187a4f73e59451f321e013b722eb14b8439`), with the namespace renamed from `Toy.Repr` to
  `Toy.ByteSL` and the import adjusted; their code (comments excluded) is otherwise identical to
  the published files, which was checked by comparing the comment-stripped sources. Their doc
  comments refer to that package's own modules and result labels (e.g. its R5b), not to this
  package's. `transmuteTotal_of_intoBytes_of_fromBytes` in `Transmute.lean` is that package's
  R2a (from its support file `lean/ToyRepr/Transmute.lean`), copied with its proof. `Bytes.slice`
  in `lean/Toy/ByteSL/Struct.lean` is copied from the support file `lean/ToyRepr/Product.lean` of
  the same package at the same commit (code unchanged; namespace `Toy.Repr` renamed to
  `Toy.ByteSL`).
* `lean/Toy/ByteSL/SepBasic.lean` consists of a subset of the declarations of the support file
  `lean/Toy/Sep/Basic.lean` of the published package `frame-rule-locality-and-precise-assertions`
  (google/zerocopy branch `reference`, commit `8ff18039787575ce7f24066acdc7600918ad8185`), in the
  same order, their code unchanged and the namespace renamed from `Toy.Sep` to `Toy.ByteSL`
  (checked the same way). The finite-heap carrier in `lean/Toy/ByteSL/Heap.lean` (`Heap`,
  `Heap.ext`, `Heap.emp`, `Heap.set`, `Heap.join` and the simp lemmas `emp_val`, `set_val`,
  `join_val`) is copied from the support file `lean/Toy/Sep/Heap.lean` of that package at the same
  commit, with the namespace renamed and the type variable renamed from `V` to `C`; that file's
  singleton heap `pt`, its address-disjointness `Disj` and its `SepStruct` instance are not copied
  (this package defines its own permission-aware disjointness). R5a here is the same statement as
  that package's R2b (`Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp`), proved again here;
  R5b–R5f instantiate the abstract notions on this package's byte heap, which that package does
  not contain (its heap model has arbitrary cell values, address-disjoint union and no
  permissions).
* SHA-256 digests of the upstream source files at the recorded commits (paths relative to the
  package directories `reports/byte-representation-galois-laws-and-transmute-composition/` and
  `reports/frame-rule-locality-and-precise-assertions/` on the `reference` branch):
  * commit `c659d187a4f73e59451f321e013b722eb14b8439`: `lean/ToyRepr/Basic.lean`
    `f02729ec1d463c84fa9e9db576b90bc85b71222bbe9e036cd9b2ec4bc25096a5`;
    `lean/ToyRepr/Examples.lean`
    `cf454c65d34a1b47f6ec4dae4653c88180fb2e9bfb4f0d901aa558a9d504c89b`;
    `lean/ToyRepr/Transmute.lean`
    `716b605f8c9816236b9af326e7b65e3d4e9adf9921962f1bc11e87d2fb0e737b`;
    `lean/ToyRepr/Product.lean`
    `752a5444ecdf05a961bf4b8b6feb6e2d79271e32a78ef320212e7c6592e45134`.
  * commit `8ff18039787575ce7f24066acdc7600918ad8185`: `lean/Toy/Sep/Basic.lean`
    `65fee97ab447171c2e534b616f6c509b5b5abbdb7a5de504e7a743104e5b6308`;
    `lean/Toy/Sep/Heap.lean`
    `8c261816143b6cf7142ccdf9d6576ccf934040867e38ebd871d38790bc89b413`.

  The local copies differ from these files (namespace, imports, comments, omitted declarations),
  so their digests differ; the digests identify the upstream inputs only.

### Toolchain and dependencies

Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), pinned in
`lean/lean-toolchain`. The Lake project (`lean/lakefile.toml`, package `toy-bytesl`) has one
library target `Toy` and no dependencies: no Mathlib, no `Std` import, core Lean only.

### How the subjects relate

The Lean toolchain is the checker of every theorem. The MiniRust specification (at the recorded
commit) is the semantic reference the definitions imitate (abstract bytes, the representation
relation and its generic properties, padding behavior). The zerocopy crate (0.8.63) is cited only
for the bounds of its `transmute_ref!` and `transmute_mut!` macros, which the non-claims compare
against. The Verified Software Toolchain source (at the recorded commit) and the papers are prior
art: they are compared with, not formalized. Two unmerged pull requests to the Aeneas verifier
are credited as related context in the prior-art entries only and are not subjects.

### Exact observation versus broader applicability

What is established is exactly the kernel-checked Lean statements quoted under **Findings**,
about the definitions quoted there. Every statement about real systems (Rust types, zerocopy's
macros, VST, CN) is a separate claim labeled `Basis: derived (modeling bridge)` with its
reasoning; none of them is kernel-checked, and each depends on the real system's types having
representations that satisfy the stated hypotheses, which this package does not verify.

## Findings

### Key definitions

Each definition is shown first unfolded informally, then quoted from the Lean source (code only, doc comments omitted). Notation: `⊑` is the definedness order; `disj` and `union` are the operations of the separation structure; on byte heaps `union` is left-biased.

#### Copied byte-representation vocabulary

Copied (namespace renamed, code unchanged) from the published package
`byte-representation-galois-laws-and-transmute-composition` (modules `ReprBasic.lean`,
`ReprExamples.lean`).

```
inductive AByte (D) | uninit | init (d : D)
x ⊑ y   on AByte:  uninit ⊑ y;  init a ⊑ init b ↔ a = b;  init a ⋢ uninit
Bytes D n := Vector (AByte D) n          x ⊑ y  :↔  ∀ i < n, x[i] ⊑ y[i]
Option order (flat): none ⊑ o;  some v ⊑ some w ↔ v = w;  some v ⋢ none
structure Rep (α V) where encode : V → α ; decode : α → Option V

r.DecodeMono   :↔ ∀ x y, x ⊑ y → r.decode x ⊑ r.decode y
r.DecodeEncode :↔ ∀ v, r.decode (r.encode v) = some v
r.EncodeLeast  :↔ ∀ x v, r.decode x = some v → r.encode v ⊑ x
r.IntoBytes    :↔ ∀ v, ∀ i < n, (r.encode v)[i].isInit = true
r.FromBytes    :↔ ∀ x, (∀ i < n, x[i].isInit = true) → ∃ v, r.decode x = some v
transmute ra rb a := rb.decode (ra.encode a)
TransmuteTotal ra rb :↔ ∀ a, ∃ b, transmute ra rb a = some b
```

Concrete representations (payload `Byte := UInt8`): `u8Rep` (1 byte, `[init b] ↦ b`),
`boolRep` (1 byte, only `0`, `1` decode — a niche), `boolNZRep` (every nonzero byte decodes to
`true`, `true` encoded as `1`; violates `EncodeLeast`), `padUnitRep` (1 byte of pure padding),
`exactUnitRep` (`Unit` encoded `[uninit]`, only `[uninit]` decodes; violates `DecodeMono`),
`u8PadRep` (2 bytes: `u8` then one padding byte, encoded `[init b, uninit]`, decoder ignores
byte 1), `pairRep` (2-byte integer, both bytes must be initialized), `noneRep enc` (decoder always
`none`). New here: `emptyPadRep` (payload type `Empty`), `zeroUnitRep` (size 0), `nonMonoBoolRep`
(1 byte, `[uninit] ↦ false`, every `[init d] ↦ true`; `FromBytes`, not `DecodeMono`).

The one-byte representations are built with `byteRep`; the encoder `boolEnc` of `boolRep` (and
`boolNZRep`) also appears in R3d:

```lean
def byteRep (enc : V → D) (dec : D → Option V) : Rep (Bytes D 1) V where
  encode v := #v[.init (enc v)]
  decode x := match x[0] with
    | .init b => dec b
    | .uninit => none

def boolEnc (b : Bool) : Byte := if b then 1 else 0

def boolDec (x : Byte) : Option Bool :=
  if x = 0 then some false else if x = 1 then some true else none

def boolRep : Rep (Bytes Byte 1) Bool := byteRep boolEnc boolDec
```

#### Separation structures and commands

Following the relational presentation of local actions (Yang–O'Hearn 2002; Calcagno–O'Hearn–Yang
2007).

```
class SepStruct S where disj : S → S → Prop ; union : S → S → S
sep P Q h      :↔ ∃ h₁ h₂, disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂
Outcome S      := fault | ok (s : S)          Cmd S := S → Outcome S → Prop
Safe c h       :↔ ¬ c h fault
Triple P c Q   :↔ ∀ h, P h → Safe c h ∧ ∀ h', c h (ok h') → Q h'
SafetyMono c   :↔ ∀ h h', disj h h' → Safe c h → Safe c (union h h')
FrameProp c    :↔ ∀ h h' h'', disj h h' → Safe c h → c (union h h') (ok h'') →
                    ∃ h₀, c h (ok h₀) ∧ disj h₀ h' ∧ h'' = union h₀ h'
Local c        :↔ SafetyMono c ∧ FrameProp c
FrameRuleSound c :↔ ∀ P Q R, Triple P c Q → Triple (sep P R) c (sep Q R)
laws: DisjSymm, UnionComm, UnionAssoc, UnitLaw e, RightCancel; IsSepAlgebra S e (no cancellativity)
```

#### The byte heap

```
inductive Perm | full | ro          -- two-point permission algebra (COY 2007's {RW, R}); no order used
structure Cell D where perm : Perm ; byte : AByte D
structure Heap C where val : Nat → Option C ; finite : ∃ n, ∀ k ≥ n, val k = none
BHeap D := Heap (Cell D)
disj h₁ h₂     :↔ ∀ k c₁ c₂, h₁.val k = some c₁ → h₂.val k = some c₂ → c₁.perm = ro ∧ c₁ = c₂
union h₁ h₂    := fun k => (h₁.val k).or (h₂.val k)                       -- left-biased
blockOn p a x keep : BHeap D   -- cells a+i (i < n, keep i) holding ⟨p, x[i]⟩, nothing else
block p a x := blockOn p a x (fun _ => true)
ptsB p a x h   :↔ h = block p a x                                         -- byte points-to
HeapByteLe h h' :↔ ∀ k, (h.val k = none ↔ h'.val k = none) ∧
                   ∀ c c', h.val k = some c → h'.val k = some c' → c.perm = c'.perm ∧ c.byte ⊑ c'.byte
byteUpClose P h :↔ ∃ h₀, P h₀ ∧ HeapByteLe h₀ h
```

`HeapByteLe` is the byte-definedness order with a **fixed domain**; `byteUpClose` initializes zero
or more `uninit` bytes and never adds or removes cells. It is not the heap-extension order
(sub-heap) under which intuitionistic separation-logic assertions are upward closed (`P * True`).

#### Typed points-to

```
ptsEnc p r a v h :↔ h = block p a (r.encode v)                            -- encode-based
ptsDec p r a v h :↔ ∃ x, h = block p a x ∧ r.decode x = some v            -- decode-based
```

#### Structs (two fields, `repr(C)` placement)

```
structure Layout2 where size₁ size₂ off₂ size : Nat ; fits₁ : size₁ ≤ size ; fits : off₂ + size₂ ≤ size
L.NonOverlap   :↔ L.size₁ ≤ L.off₂                                          -- separate hypothesis
L.isPad i      := i < size ∧ size₁ ≤ i ∧ ¬ (off₂ ≤ i < off₂ + size₂)
structEncode L r₁ r₂ (v₁, v₂) [i] = (r₁.encode v₁)[i]          if i < size₁
                                  = (r₂.encode v₂)[i - off₂]    if off₂ ≤ i < off₂ + size₂
                                  = uninit                      otherwise
structDecode L r₁ r₂ x = (v₁, v₂) if r₁.decode x[0, size₁) = some v₁ and r₂.decode x[off₂, off₂+size₂) = some v₂
                       = none otherwise                         -- padding never read
padAny p L a h    :↔ ∃ y : Bytes D L.size, h = blockOn p a y L.isPad
padUninit p L a h :↔ h = blockOn p a (uninit …) L.isPad
layoutS := ⟨1, 2, 2, 4⟩   -- #[repr(C)] struct S { a: u8, b: u16 }: a at 0, padding at 1, b at 2..3
structS := structRep layoutS u8Rep pairRep
layoutU := ⟨1, 1, 0, 1⟩   -- union-like: both one-byte fields at offset 0 (violates NonOverlap)
```

#### Commands

```
readBytes h a n  = some (bytes of cells a..a+n-1)  if all allocated (any permission), else none
readLoose h a n  = bytes of cells a..a+n-1, an unallocated cell read as uninit
OwnsFull h a n   :↔ ∀ i < n, ∃ b, h.val (a+i) = some ⟨full, b⟩
writeBytes h a x = h with cells a..a+n-1 set to ⟨full, x[i]⟩

bstore a b      : fault unless OwnsFull h a 1;           else ok (writeBytes h a [b])
bcopy src dst   : fault unless readBytes h src 1 = some x ∧ OwnsFull h dst 1; else ok (writeBytes h dst x)
tstore r a v    : fault unless OwnsFull h a n;           else ok (writeBytes h a (r.encode v))
tcopy r src dst : fault unless readBytes h src n = some x ∧ r.decode x = some v ∧ OwnsFull h dst n;
                  else ok (writeBytes h dst (r.encode v))
tload r a       : fault unless readBytes h a n = some x ∧ r.decode x = some v; else ok h   -- no result value
bcopyLoose src dst   : fault unless OwnsFull h dst 1; else ok (writeBytes h dst (readLoose h src 1))
tcopyLoose r src dst : fault unless r.decode (readLoose h src n) = some v ∧ OwnsFull h dst n;
                       else ok (writeBytes h dst (r.encode v))
bstoreShared a b     : fault if h.val a = none; else ok (h.set a ⟨(cell a).perm, b⟩)
```

#### Quoted Lean source

Representations (copied from the published representation package):

```lean
inductive AByte (D : Type) where
  | uninit : AByte D
  | init (d : D) : AByte D
  deriving DecidableEq

def le : AByte D → AByte D → Prop
  | uninit, _ => True
  | init a, init b => a = b
  | init _, uninit => False

abbrev Bytes (D : Type) (n : Nat) := Vector (AByte D) n

instance {D : Type} {n : Nat} : Definedness (Bytes D n) :=
  ⟨fun x y => ∀ (i : Nat) (h : i < n), x[i] ⊑ y[i]⟩

def OptLe {V : Type} : Option V → Option V → Prop
  | none, _ => True
  | some v, some w => v = w
  | some _, none => False

structure Rep (α V : Type) where
  encode : V → α
  decode : α → Option V

def DecodeMono [Definedness α] (r : Rep α V) : Prop :=
  ∀ x y : α, x ⊑ y → r.decode x ⊑ r.decode y

def DecodeEncode (r : Rep α V) : Prop :=
  ∀ v : V, r.decode (r.encode v) = some v

def EncodeLeast [Definedness α] (r : Rep α V) : Prop :=
  ∀ (x : α) (v : V), r.decode x = some v → r.encode v ⊑ x

def IntoBytes {D : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ v : V, (r.encode v).IsInit

def FromBytes {D : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ x : Bytes D n, x.IsInit → ∃ v, r.decode x = some v

def transmute {α A B : Type} (ra : Rep α A) (rb : Rep α B) (a : A) : Option B :=
  rb.decode (ra.encode a)

def TransmuteTotal {α A B : Type} (ra : Rep α A) (rb : Rep α B) : Prop :=
  ∀ a : A, ∃ b : B, transmute ra rb a = some b
```

Separation structures, commands, triples, locality:

```lean
class SepStruct (S : Type u) where
  disj : S → S → Prop
  union : S → S → S

inductive Outcome (S : Type u) where
  | fault : Outcome S
  | ok : S → Outcome S

abbrev Cmd (S : Type u) := S → Outcome S → Prop

abbrev Assn (S : Type u) := S → Prop

def sep [SepStruct S] (P Q : Assn S) : Assn S :=
  fun h => ∃ h₁ h₂, disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

def Safe (c : Cmd S) (h : S) : Prop := ¬ c h .fault

def Triple (P : Assn S) (c : Cmd S) (Q : Assn S) : Prop :=
  ∀ h, P h → Safe c h ∧ ∀ h', c h (.ok h') → Q h'

def SafetyMono [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' : S, disj h h' → Safe c h → Safe c (union h h')

def FrameProp [SepStruct S] (c : Cmd S) : Prop :=
  ∀ h h' h'' : S, disj h h' → Safe c h → c (union h h') (.ok h'') →
    ∃ h₀, c h (.ok h₀) ∧ disj h₀ h' ∧ h'' = union h₀ h'

def Local [SepStruct S] (c : Cmd S) : Prop :=
  SafetyMono c ∧ FrameProp c

def FrameRuleSound [SepStruct S] (c : Cmd S) : Prop :=
  ∀ P Q R : Assn S, Triple P c Q → Triple (sep P R) c (sep Q R)

def DisjSymm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → disj b a

def UnionComm (S : Type u) [SepStruct S] : Prop :=
  ∀ a b : S, disj a b → union a b = union b a

def UnionAssoc (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a b → disj (union a b) c →
    disj b c ∧ disj a (union b c) ∧ union (union a b) c = union a (union b c)

def UnitLaw [SepStruct S] (e : S) : Prop :=
  ∀ a : S, disj e a ∧ union e a = a

def RightCancel (S : Type u) [SepStruct S] : Prop :=
  ∀ a b c : S, disj a c → disj b c → union a c = union b c → a = b

structure IsSepAlgebra (S : Type u) [SepStruct S] (e : S) : Prop where
  disjSymm : DisjSymm S
  comm : UnionComm S
  assoc : UnionAssoc S
  unit : UnitLaw e
```

The byte heap with read-only sharing:

```lean
structure Heap (C : Type) where
  val : Nat → Option C
  finite : ∃ n, ∀ k, n ≤ k → val k = none

def join (h₁ h₂ : Heap C) : Heap C :=
  ⟨fun k => (h₁.val k).or (h₂.val k), by
    obtain ⟨n₁, hn₁⟩ := h₁.finite
    obtain ⟨n₂, hn₂⟩ := h₂.finite
    refine ⟨max n₁ n₂, fun k hk => ?_⟩
    have e1 := hn₁ k (by omega)
    have e2 := hn₂ k (by omega)
    simp [e1, e2]⟩

inductive Perm where
  | full : Perm
  | ro : Perm
  deriving DecidableEq

structure Cell (D : Type) where
  perm : Perm
  byte : AByte D
  deriving DecidableEq

abbrev BHeap (D : Type) := Heap (Cell D)

def BHeap.Disj {D : Type} (h₁ h₂ : BHeap D) : Prop :=
  ∀ k c₁ c₂, h₁.val k = some c₁ → h₂.val k = some c₂ → c₁.perm = .ro ∧ c₁ = c₂

instance (D : Type) : SepStruct (BHeap D) where
  disj := BHeap.Disj
  union := Heap.join

def Heap.blockOn {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) :
    BHeap D where
  val k :=
    if hk : a ≤ k ∧ k < a + n then
      (if keep (k - a) then some ⟨p, x[k - a]'(by omega)⟩ else none)
    else none
  finite := ⟨a + n, fun k hk => by simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]⟩

def Heap.block {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) : BHeap D :=
  Heap.blockOn p a x (fun _ => true)

def ptsB {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) : Assn (BHeap D) :=
  fun h => h = Heap.block p a x

def HeapByteLe {D : Type} (h h' : BHeap D) : Prop :=
  ∀ k, (h.val k = none ↔ h'.val k = none) ∧
    ∀ c c', h.val k = some c → h'.val k = some c' → c.perm = c'.perm ∧ c.byte ⊑ c'.byte

def byteUpClose {D : Type} (P : Assn (BHeap D)) : Assn (BHeap D) :=
  fun h => ∃ h₀, P h₀ ∧ HeapByteLe h₀ h
```

Typed points-to:

```lean
def ptsEnc {D V : Type} {n : Nat} (p : Perm) (r : Rep (Bytes D n) V) (a : Nat) (v : V) :
    Assn (BHeap D) :=
  ptsB p a (r.encode v)

def ptsDec {D V : Type} {n : Nat} (p : Perm) (r : Rep (Bytes D n) V) (a : Nat) (v : V) :
    Assn (BHeap D) :=
  fun h => ∃ x : Bytes D n, ptsB p a x h ∧ r.decode x = some v
```

Two-field structs:

```lean
structure Layout2 where
  size₁ : Nat
  size₂ : Nat
  off₂ : Nat
  size : Nat
  fits₁ : size₁ ≤ size
  fits : off₂ + size₂ ≤ size

def NonOverlap (L : Layout2) : Prop := L.size₁ ≤ L.off₂

def isPad (L : Layout2) (i : Nat) : Bool :=
  decide (i < L.size ∧ L.size₁ ≤ i ∧ ¬ (L.off₂ ≤ i ∧ i < L.off₂ + L.size₂))

def Bytes.slice {D : Type} {n : Nat} (x : Bytes D n) (o m : Nat) (h : o + m ≤ n) : Bytes D m :=
  Vector.ofFn fun t => x[o + t.val]

def structEncode (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (v : V₁ × V₂) : Bytes D L.size :=
  Vector.ofFn fun i =>
    if h₁ : i.val < L.size₁ then (r₁.encode v.1)[i.val]
    else if h₂ : L.off₂ ≤ i.val ∧ i.val < L.off₂ + L.size₂ then
      (r₂.encode v.2)[i.val - L.off₂]'(by omega)
    else .uninit

def structDecode (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂)
    (x : Bytes D L.size) : Option (V₁ × V₂) :=
  match r₁.decode (x.slice 0 L.size₁ L.fits₁_zero), r₂.decode (x.slice L.off₂ L.size₂ L.fits) with
  | some v₁, some v₂ => some (v₁, v₂)
  | _, _ => none

def structRep (L : Layout2) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂) :
    Rep (Bytes D L.size) (V₁ × V₂) :=
  ⟨structEncode L r₁ r₂, structDecode L r₁ r₂⟩

def padAny {D : Type} (p : Perm) (L : Layout2) (a : Nat) : Assn (BHeap D) :=
  fun h => ∃ y : Bytes D L.size, h = Heap.blockOn p a y L.isPad

def padUninit {D : Type} (p : Perm) (L : Layout2) (a : Nat) : Assn (BHeap D) :=
  fun h => h = Heap.blockOn p a (Bytes.uninit L.size) L.isPad
```

Commands:

```lean
def readBytes (h : BHeap D) (a n : Nat) : Option (Bytes D n) :=
  if hall : ∀ i, i < n → (h.val (a + i)).isSome = true then
    some (Vector.ofFn fun i => ((h.val (a + i.val)).get (hall i.val i.isLt)).byte)
  else none

def readLoose (h : BHeap D) (a n : Nat) : Bytes D n :=
  Vector.ofFn fun i => match h.val (a + i.val) with
    | some c => c.byte
    | none => .uninit

def OwnsFull (h : BHeap D) (a n : Nat) : Prop :=
  ∀ i, i < n → ∃ b, h.val (a + i) = some ⟨.full, b⟩

def writeBytes {n : Nat} (h : BHeap D) (a : Nat) (x : Bytes D n) : BHeap D :=
  ⟨fun k => if hk : a ≤ k ∧ k < a + n then some ⟨.full, x[k - a]'(by omega)⟩ else h.val k, by
    obtain ⟨m, hm⟩ := h.finite
    refine ⟨max m (a + n), fun k hk => ?_⟩
    simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]
    exact hm k (by omega)⟩

def bstore (a : Nat) (b : AByte D) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h a 1 ∧ o = .fault) ∨ (OwnsFull h a 1 ∧ o = .ok (writeBytes h a #v[b]))

def bcopy (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((readBytes h src 1 = none ∨ ¬ OwnsFull h dst 1) ∧ o = .fault) ∨
  (∃ x, readBytes h src 1 = some x ∧ OwnsFull h dst 1 ∧ o = .ok (writeBytes h dst x))

def tstore (r : Rep (Bytes D n) V) (a : Nat) (v : V) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h a n ∧ o = .fault) ∨ (OwnsFull h a n ∧ o = .ok (writeBytes h a (r.encode v)))

def tcopy (r : Rep (Bytes D n) V) (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((¬ (∃ x v, readBytes h src n = some x ∧ r.decode x = some v) ∨ ¬ OwnsFull h dst n) ∧
      o = .fault) ∨
  (∃ x v, readBytes h src n = some x ∧ r.decode x = some v ∧ OwnsFull h dst n ∧
      o = .ok (writeBytes h dst (r.encode v)))

def tload (r : Rep (Bytes D n) V) (a : Nat) : Cmd (BHeap D) := fun h o =>
  (¬ (∃ x v, readBytes h a n = some x ∧ r.decode x = some v) ∧ o = .fault) ∨
  ((∃ x v, readBytes h a n = some x ∧ r.decode x = some v) ∧ o = .ok h)

def bcopyLoose (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h dst 1 ∧ o = .fault) ∨
  (OwnsFull h dst 1 ∧ o = .ok (writeBytes h dst (readLoose h src 1)))

def tcopyLoose (r : Rep (Bytes D n) V) (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((¬ (∃ v, r.decode (readLoose h src n) = some v) ∨ ¬ OwnsFull h dst n) ∧ o = .fault) ∨
  (∃ v, r.decode (readLoose h src n) = some v ∧ OwnsFull h dst n ∧
      o = .ok (writeBytes h dst (r.encode v)))

def bstoreShared (a : Nat) (b : AByte D) : Cmd (BHeap D) := fun h o =>
  (h.val a = none ∧ o = .fault) ∨ (∃ c, h.val a = some c ∧ o = .ok (h.set a (some ⟨c.perm, b⟩)))
```

### R1a: `R1a-encode-based-entails-decode-based-iff-decodeEncode`

* **Kind / tier:** characterization, **T0**. The direction 'DecodeEncode gives encode-based => decode-based' is the typed-points-to form of the round-trip law (Tuch-Klein-Norrish 2007 state from-bytes (to-bytes v) = Some v); the converse is immediate. A re-derivation in this vocabulary, kept as a definitional reference point.
* **Plain claim:** For every representation r of n-byte values (no law assumed), the encode-based typed points-to (the n bytes at a are exactly r.encode v) entails the decode-based one (the n bytes at a are some x with r.decode x = some v), at every permission, address, value and heap, exactly when r satisfies DecodeEncode.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
  (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D), ptsEnc p r a v h → ptsDec p r a v h) ↔ r.DecodeEncode
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsEnc_entails_ptsDec_iff_decodeEncode (r : Rep (Bytes D n) V)` :
`(∀ p a v h, h = block p a (r.encode v) → ∃ x, h = block p a x ∧ r.decode x = some v) ↔ ∀ v, r.decode (r.encode v) = some v`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `definitional`.
* **Non-vacuity witness:** u8PadRep (modeling a u8 followed by one padding byte) satisfies DecodeEncode, and the block holding its encoding [init 5, uninit] satisfies the encode-based points-to of 5. (Lean: `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode_nonvacuous`).
* **Prior art:**
  * Tuch, H., Klein, G. & Norrish, M., 'Types, Bytes, and Separation Logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234 (author PDF https://trustworthy.systems/publications/nicta_full_text/134.pdf): a byte-level heap heap-mem; typed reads h-val h p = from-bytes (heap-list h (size-of TYPE('a)) (ptr-val p)) and the law from-bytes (to-bytes v) = Some v; a heap type description kept as an additional state component; separation logic embedded on top, with singleton assertion p |->g v = (lambda s. lift-typ-heap g s p = Some v and dom s = {ptr-val p ..+ size-of TYPE('a)}), where lift-typ-heap is defined only at pointers satisfying the guard and heap type description (s, g |=s p); i.e. a decode-based typed points-to with an exact byte footprint, guarded by alignment and type-description conditions that this package does not model.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * Krebbers, R., 'A Formal C Memory Model for Separation Logic', Journal of Automated Reasoning 57(4), pp. 319-387, 2016, doi:10.1007/s10817-016-9369-1: a Coq-formalized memory model for (non-concurrent) C11 with a permission model designed for separation logic, covering typed and byte-level (untyped) views of memory (cited as related byte-level-with-permissions work, no specific statement relied on).
  * AeneasVerif/aeneas pull request #1551, 'Separation logic over the byte heap' (open and unmerged as observed on 2026-11-20; head commit 1d8f9aa0121faca8ff113c1b9b742b333e3e1519; commits authored by Cezar Andrici; base branch cezar/sl-extraction). Unmerged prototype, described here only as its public source states: backends/lean/Aeneas/SepLogic/Bytes.lean ('The byte contents of the heap as fragments (from fournet/wip-memory-model)') defines pointsTo (the cells hold some admissible encoding of the value, at a sharing depth) and readable (the cells hold some bytes that decode to the value) and proves pointsTo_readable from the representation's encode_decode law; SepLogic/PCM.lean defines a class PartialCommMonoid and the order Subheap ('is a part of': h' is h extended with a compatible part), on which, its header comment says, the separation-logic assertions are upward closed (upward closure under heap extension, not the byte-definedness closure byteUpClose of this package). Not relied on for any formal claim here.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — If a real type's representation (in MiniRust's sense) satisfies `DecodeEncode`, as MiniRust's generic properties state for its representation relation, then memory holding exactly the bytes a typed store wrote can be loaded back at that type with the stored value. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R1b: `R1b-decode-based-equals-byte-upward-closure-iff-three-laws`

* **Kind / tier:** characterization, **T1**. The byte-level fact behind it (the three laws hold iff decode x = some v <-> encode v <= x) is MiniRust's 'Galois connection' remark and R1a of the published representation package; lifting it to heap assertions as a byte-definedness upward closure is folklore made precise here.
* **Plain claim:** For every representation r of n-byte values (no law assumed): the decode-based typed points-to of r equals the byte-definedness upward closure of the encode-based one at every permission p, address a, value v and heap h (h satisfies the decode-based points-to of v at a iff h is obtained from the block holding r.encode v at a by initializing zero or more of its uninit bytes, keeping the same cells and permissions), if and only if r satisfies all three laws DecodeMono, DecodeEncode and EncodeLeast.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast {D V : Type} {n : Nat}
  (r : Rep (Bytes D n) V) :
  (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D), ptsDec p r a v h ↔ byteUpClose (ptsEnc p r a v) h) ↔
    r.DecodeMono ∧ r.DecodeEncode ∧ r.EncodeLeast
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast (r : Rep (Bytes D n) V)` :
`(∀ p a v h, (∃ x, h = block p a x ∧ r.decode x = some v) ↔ ∃ h₀, h₀ = block p a (r.encode v) ∧ HeapByteLe h₀ h) ↔ (r.DecodeMono ∧ r.DecodeEncode ∧ r.EncodeLeast)`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** u8PadRep satisfies all three laws (both sides of R1b hold); the block [init 5, init 7] (padding initialized) is in the byte-definedness upward closure of the encode-based points-to of 5, satisfies the decode-based one, and is not the encoding itself. (Lean: `Toy.ByteSL.ptsDec_eq_byteUpClose_nonvacuous`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * Tuch, H., Klein, G. & Norrish, M., 'Types, Bytes, and Separation Logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234 (author PDF https://trustworthy.systems/publications/nicta_full_text/134.pdf): a byte-level heap heap-mem; typed reads h-val h p = from-bytes (heap-list h (size-of TYPE('a)) (ptr-val p)) and the law from-bytes (to-bytes v) = Some v; a heap type description kept as an additional state component; separation logic embedded on top, with singleton assertion p |->g v = (lambda s. lift-typ-heap g s p = Some v and dom s = {ptr-val p ..+ size-of TYPE('a)}), where lift-typ-heap is defined only at pointers satisfying the guard and heap type description (s, g |=s p); i.e. a decode-based typed points-to with an exact byte footprint, guarded by alignment and type-description conditions that this package does not model.
  * Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817: the standard reference for separation logic and its vocabulary, including the distinction between exact assertions and assertions closed under heap extension (intuitionistic assertions); cited for the contrast with this package's byte-definedness closure.
  * AeneasVerif/aeneas pull request #1551, 'Separation logic over the byte heap' (open and unmerged as observed on 2026-11-20; head commit 1d8f9aa0121faca8ff113c1b9b742b333e3e1519; commits authored by Cezar Andrici; base branch cezar/sl-extraction). Unmerged prototype, described here only as its public source states: backends/lean/Aeneas/SepLogic/Bytes.lean ('The byte contents of the heap as fragments (from fournet/wip-memory-model)') defines pointsTo (the cells hold some admissible encoding of the value, at a sharing depth) and readable (the cells hold some bytes that decode to the value) and proves pointsTo_readable from the representation's encode_decode law; SepLogic/PCM.lean defines a class PartialCommMonoid and the order Subheap ('is a part of': h' is h extended with a compatible part), on which, its header comment says, the separation-logic assertions are upward closed (upward closure under heap extension, not the byte-definedness closure byteUpClose of this package). Not relied on for any formal claim here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — MiniRust states all three laws (as monotonicity, `decode(encode(v)) == Some(v)` and the adjoint inequality) for its representation relation; for such representations the decode-based typed points-to is exactly the encode-based one with some `uninit` bytes initialized, i.e. a typed load sees through initialized padding. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R1c: `R1c-two-typed-points-to-coincide-iff-intoBytes`

* **Kind / tier:** characterization, **T1**. Informally known (padding is what separates 'the bytes a store writes' from 'the bytes a load accepts'); stated and tightness-checked here.
* **Plain claim:** If a representation r satisfies DecodeMono, DecodeEncode and EncodeLeast and the byte payload type is nonempty, then the decode-based and encode-based typed points-to of r coincide (at every permission, address, value and heap) exactly when r is IntoBytes, i.e. no encoding of r contains an uninit byte.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty {D V : Type} {n : Nat}
  (r : Rep (Bytes D n) V) (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (hD : Nonempty D) :
  (∀ (p : Perm) (a : Nat) (v : V) (h : BHeap D), ptsDec p r a v h ↔ ptsEnc p r a v h) ↔ r.IntoBytes
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty (r) (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (hD : Nonempty D)` :
`(∀ p a v h, (∃ x, h = block p a x ∧ r.decode x = some v) ↔ h = block p a (r.encode v)) ↔ ∀ v, ∀ i < n, (r.encode v)[i].isInit = true`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hM : r.DecodeMono` | Lets an encoding with an uninit byte be made more defined while still decoding (left-to-right). | tight: counterexample `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hM` |
| `hDE : r.DecodeEncode` | The encode-based points-to entails the decode-based one. | tight: counterexample `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hDE` |
| `hEL : r.EncodeLeast` | Every byte vector decoding to v lies above the (fully initialized, hence maximal) encoding (right-to-left). | tight: counterexample `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hEL` |
| `hD : Nonempty D` | Supplies an initialized byte to put where an encoding has uninit. | tight: counterexample `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hD` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** All hypotheses hold for u8Rep (IntoBytes; the two coincide) and for u8PadRep (not IntoBytes; they differ, see R1d). (Lean: `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_nonvacuous`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — For Rust types with padding (whose MiniRust encoding contains `Uninit`), the two typed points-to differ; for padding-free lawful types (for example integers, whose encodings are fully initialized) they coincide, so the choice between them matters only for types with `uninit` bytes in some encoding. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R1d: `R1d-initialized-padding-separates-the-two-definitions`

* **Kind / tier:** counterexample, **T0**. The standard padding example; its byte-level content (u8PadRep satisfies the three laws, is not IntoBytes, and decodes [init 5, init 7] to 5) is already mechanized in the published representation package. Restated here as heap assertions.
* **Plain claim:** For u8PadRep (modeling a u8 followed by one padding byte, encoded with uninit padding), which satisfies DecodeMono, DecodeEncode and EncodeLeast, the block [init 5, init 7] (padding byte initialized) satisfies the decode-based but not the encode-based typed points-to of 5; with the padding byte uninit both hold.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding :
  u8PadRep.DecodeMono ∧
    u8PadRep.DecodeEncode ∧
      u8PadRep.EncodeLeast ∧
        ptsDec Perm.full u8PadRep 0 5 (Heap.block Perm.full 0 #v[AByte.init 5, AByte.init 7]) ∧
          ¬ptsEnc Perm.full u8PadRep 0 5 (Heap.block Perm.full 0 #v[AByte.init 5, AByte.init 7])
Toy.ByteSL.u8PadRep_uninit_padding_ptsDec_and_ptsEnc :
  ptsDec Perm.full u8PadRep 0 5 (Heap.block Perm.full 0 #v[AByte.init 5, AByte.uninit]) ∧
    ptsEnc Perm.full u8PadRep 0 5 (Heap.block Perm.full 0 #v[AByte.init 5, AByte.uninit])
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding` :
`u8PadRep.DecodeMono ∧ u8PadRep.DecodeEncode ∧ u8PadRep.EncodeLeast ∧ ptsDec full u8PadRep 0 5 (block full 0 [init 5, init 7]) ∧ ¬ ptsEnc full u8PadRep 0 5 (block full 0 [init 5, init 7])`;
with `u8PadRep_uninit_padding_ptsDec_and_ptsEnc`: both hold at `block full 0 [init 5, uninit]`.

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `definitional`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding`, `Toy.ByteSL.u8PadRep_uninit_padding_ptsDec_and_ptsEnc`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — `u8PadRep` models a two-byte Rust struct consisting of a `u8` followed by one padding byte (MiniRust: padding is encoded `Uninit` and ignored by decode); writing to the padding byte (for example through a byte-level copy of initialized data) leaves memory that a typed load still reads as the struct value but that is no longer the bytes a typed store writes. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R2a: `R2a-decode-based-struct-split-with-padding-any`

* **Kind / tier:** characterization, **T0**. VST mechanizes this split (floyd/field_at.v, Lemma field_at_Tstruct: a struct's field_at equals the separating conjunction of its members' field_at, each wrapped in a spacer owning the following padding as memory_block with arbitrary contents), and CN splits struct ownership into members and padding bytes. Restated here for abstract, lawless field representations; that parameterization is not claimed as new.
* **Plain claim:** For every two-field layout L (field 1 at offset 0, field 2 at offset off2, both within the struct) whose fields do not overlap (L.NonOverlap: size1 <= off2), all field representations r1, r2 (no laws assumed), permission p, base a, values v1, v2 and heap h: h satisfies the decode-based points-to of (v1, v2) at the struct representation structRep L r1 r2 (which decodes each field from its own byte range and never reads padding) with permission p iff h splits into the decode-based points-to of v1 at a, the decode-based points-to of v2 at a + off2, and ownership of the padding cells with arbitrary contents, all three with the same permission p.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap {D V₁ V₂ : Type} (L : Layout2) (hL : L.NonOverlap)
  (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂) (p : Perm) (a : Nat) (v₁ : V₁) (v₂ : V₂)
  (h : BHeap D) :
  ptsDec p (structRep L r₁ r₂) a (v₁, v₂) h ↔
    sep (ptsDec p r₁ a v₁) (sep (ptsDec p r₂ (a + L.off₂) v₂) (padAny p L a)) h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap (L : Layout2) (hL : L.NonOverlap) (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂) p a v₁ v₂ h` :
`ptsDec p (structRep L r₁ r₂) a (v₁, v₂) h ↔ sep (ptsDec p r₁ a v₁) (sep (ptsDec p r₂ (a + L.off₂) v₂) (padAny p L a)) h`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hL : L.NonOverlap` | The two field footprints are disjoint, so at permission full they can be separated (right-hand side) whenever the struct block exists (left-hand side). | tight: counterexample `Toy.ByteSL.ptsDec_struct_split_tight_hL` |
| `Layout2 fields fits1 : size1 <= size, fits : off2 + size2 <= size` | In-bounds invariants of a layout, needed for structRep to be well typed (the field slices must exist); every layout of a real struct satisfies them. They are fields of the structure Layout2, not hypotheses of the theorem. | harmless |

* **Depth:** `shallow`.
* **Non-vacuity witness:** layoutS (#[repr(C)] struct S { a: u8, b: u16 }: a at 0, one padding byte at 1, b at 2..3) is non-overlapping; for structS = structRep layoutS u8Rep pairRep, the block [init 1, init 9, init 2, init 3] (padding initialized to 9) satisfies both sides for (1, (2, 3)). (Lean: `Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_nonvacuous`).
* **Prior art:**
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
  * Published references for VST: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552; Cao, Q., Beringer, L., Gruetter, S., Dodds, J. & Appel, A. W., 'VST-Floyd: A Separation Logic Tool to Verify Correctness of C Programs', Journal of Automated Reasoning 61, pp. 367-422, 2018, doi:10.1007/s10817-018-9457-5. Cited for the program logic whose source files are described under the VST entry; no specific statement of these publications is relied on.
  * Pulte, C., Makwana, D. C., Sewell, T., Memarian, K., Sewell, P. & Krishnaswami, N., 'CN: Verifying Systems C Code with Separation-Logic Refinement Types', PACMPL 7(POPL), Article 1, 2023, doi:10.1145/3571194. Section 2.6: Owned<tau>(p)(v) asserts ownership of the memory pointed to by p with value v, 'equivalent to a separation logic points-to resource p |->tau v, indexed by a C-type tau to capture its memory layout'. Section 2.8: resource inference splits a struct resource into resources for the members 'and of padding bytes, where appropriate', and recombining them 'for a padded struct ... would also consume ownership of padding bytes'.
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Gaeher, L., Sammler, M., Jung, R., Krebbers, R. & Dreyer, D., 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', PACMPL 8(PLDI), Article 192, 2024, doi:10.1145/3656422. Section 4 (Radium): values are lists of memory bytes, each a normal byte (0-255), a location fragment, or poison (e.g. for uninitialized memory); the heap maps locations to memory bytes; loads and stores are parameterized by a layout. Section 4.1 and Fig. 7: struct layouts list explicit unnamed fields for padding, and verification is parametric in a layout algorithm. Section 4.2: unlike lambda-Rust, Radium represents padding, and reading padding bytes as an integer is undefined behavior. Section 5.1 and Fig. 8: value types include uninit st (uninitialized memory of syntactic type st) and maybe_init T.
  * Sammler, M., Lepigre, R., Krebbers, R., Memarian, K., Dreyer, D. & Garg, D., 'RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types', PLDI 2021, pp. 158-174, doi:10.1145/3453483.3454036: the system whose Caesium operational semantics RefinedRust's Radium is based on (as stated in the RefinedRust paper, Sections 1 and 4).
  * Krebbers, R., 'A Formal C Memory Model for Separation Logic', Journal of Automated Reasoning 57(4), pp. 319-387, 2016, doi:10.1007/s10817-016-9369-1: a Coq-formalized memory model for (non-concurrent) C11 with a permission model designed for separation logic, covering typed and byte-level (untyped) views of memory (cited as related byte-level-with-permissions work, no specific statement relied on).
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — For a two-field `#[repr(C)]` struct whose fields do not overlap, decode-based ownership of the struct is equivalent to decode-based ownership of each field plus ownership of the padding bytes with arbitrary contents, which is how VST's `data_at` treats padding (as `memory_block` spacers at the same share). The field offsets are inputs here; that `#[repr(C)]` places the fields as `Layout2` describes is assumed, not derived from a layout algorithm. This is not kernel-checked; it depends on the real types' byte representations matching the model's byte-representation, layout, and permission definitions, which is not verified here.

### R2b: `R2b-encode-based-struct-split-with-padding-uninit`

* **Kind / tier:** characterization, **T1**. Immediate from the struct encoder writing uninit padding (MiniRust); stated here as the encode-based companion of R2a.
* **Plain claim:** For every two-field layout L (field 1 at offset 0, field 2 at offset off2, both within the struct) whose fields do not overlap (L.NonOverlap: size1 <= off2), all field representations r1, r2 (no laws assumed), permission p, base a, values v1, v2 and heap h: h satisfies the encode-based points-to of (v1, v2) at the struct representation structRep L r1 r2 (which encodes each field at its offset and writes uninit padding) with permission p iff h splits into the encode-based points-to of v1 at a, the encode-based points-to of v2 at a + off2, and ownership of the padding cells all holding uninit, all three with the same permission p.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap {D V₁ V₂ : Type} (L : Layout2) (hL : L.NonOverlap)
  (r₁ : Rep (Bytes D L.size₁) V₁) (r₂ : Rep (Bytes D L.size₂) V₂) (p : Perm) (a : Nat) (v₁ : V₁) (v₂ : V₂)
  (h : BHeap D) :
  ptsEnc p (structRep L r₁ r₂) a (v₁, v₂) h ↔
    sep (ptsEnc p r₁ a v₁) (sep (ptsEnc p r₂ (a + L.off₂) v₂) (padUninit p L a)) h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap (L) (hL : L.NonOverlap) (r₁ r₂ p a v₁ v₂ h)` :
`ptsEnc p (structRep L r₁ r₂) a (v₁, v₂) h ↔ sep (ptsEnc p r₁ a v₁) (sep (ptsEnc p r₂ (a + L.off₂) v₂) (padUninit p L a)) h`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hL : L.NonOverlap` | The two field footprints are disjoint, so at permission full they can be separated whenever the struct block exists. | tight: counterexample `Toy.ByteSL.ptsEnc_struct_split_tight_hL` |
| `Layout2 fields fits1 : size1 <= size, fits : off2 + size2 <= size` | In-bounds invariants of a layout, needed for structRep to be well typed; fields of the structure Layout2, not hypotheses of the theorem. | harmless |

* **Depth:** `shallow`.
* **Non-vacuity witness:** layoutS is non-overlapping, and for structS the block [init 1, uninit, init 2, init 3] (its encoding of (1, (2, 3))) satisfies both sides. (Lean: `Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_nonvacuous`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * Pulte, C., Makwana, D. C., Sewell, T., Memarian, K., Sewell, P. & Krishnaswami, N., 'CN: Verifying Systems C Code with Separation-Logic Refinement Types', PACMPL 7(POPL), Article 1, 2023, doi:10.1145/3571194. Section 2.6: Owned<tau>(p)(v) asserts ownership of the memory pointed to by p with value v, 'equivalent to a separation logic points-to resource p |->tau v, indexed by a C-type tau to capture its memory layout'. Section 2.8: resource inference splits a struct resource into resources for the members 'and of padding bytes, where appropriate', and recombining them 'for a padded struct ... would also consume ownership of padding bytes'.
  * Banerjee, R., Memarian, K., Makwana, D., Pulte, C., Krishnaswami, N. & Sewell, P., 'Fulminate: Testing CN Separation-Logic Specifications in C', PACMPL 9(POPL), Article 43, 2025, doi:10.1145/3704879: CN's built-in resources Owned (points-to indexed by C types) and Block (points-to for uninitialised memory); Section 2.3: runtime ownership checking keeps ghost state giving, for each byte of memory, the C stack depth of the function that owns it (per-byte ownership).
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — For the same structs, the bytes a typed store of the struct writes are exactly the bytes typed stores of the fields write plus `uninit` padding, matching MiniRust's statement that struct encode makes padding `Uninit`. This is not kernel-checked; it depends on the real types' byte representations matching the model's byte-representation, layout, and permission definitions, which is not verified here.

### R2c: `R2c-mixed-struct-padding-pairings-fail`

* **Kind / tier:** counterexample, **T1**. Small but instructive instances of the padding problem at the level of heap assertions.
* **Plain claim:** For structS = structRep layoutS u8Rep pairRep (modeling #[repr(C)] struct S { a: u8, b: u16 } with one interior padding byte) and the heap heapS9 holding a = 1, b = (2, 3) with the padding byte initialized to 9: (join) heapS9 satisfies the encode-based field points-to of both fields separated from padding ownership with arbitrary contents, but not the encode-based struct points-to; (split) heapS9 satisfies the decode-based struct points-to of (1, (2, 3)) but does not split into decode-based field points-to separated from uninit padding. Hence the join law fails for 'encode-based fields + arbitrary padding' and the split law fails for 'decode-based fields + uninit padding'.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsEnc_struct_join_padAny_fails :
  sep (ptsEnc Perm.full u8Rep 0 1)
      (sep (ptsEnc Perm.full pairRep (0 + layoutS.off₂) (2, 3)) (padAny Perm.full layoutS 0)) heapS9 ∧
    ¬ptsEnc Perm.full structS 0 (1, 2, 3) heapS9 ∧
      ¬∀ (p : Perm) (a : Nat) (v₁ : Byte) (v₂ : Byte × Byte) (h : BHeap Byte),
          sep (ptsEnc p u8Rep a v₁) (sep (ptsEnc p pairRep (a + layoutS.off₂) v₂) (padAny p layoutS a)) h →
            ptsEnc p structS a (v₁, v₂) h
Toy.ByteSL.ptsDec_struct_split_padUninit_fails :
  ptsDec Perm.full structS 0 (1, 2, 3) heapS9 ∧
    ¬sep (ptsDec Perm.full u8Rep 0 1)
          (sep (ptsDec Perm.full pairRep (0 + layoutS.off₂) (2, 3)) (padUninit Perm.full layoutS 0)) heapS9 ∧
      ¬∀ (p : Perm) (a : Nat) (v₁ : Byte) (v₂ : Byte × Byte) (h : BHeap Byte),
          ptsDec p structS a (v₁, v₂) h →
            sep (ptsDec p u8Rep a v₁) (sep (ptsDec p pairRep (a + layoutS.off₂) v₂) (padUninit p layoutS a)) h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): (two counterexamples, `heapS9 := block full 0 [init 1, init 9, init 2, init 3]`)
`ptsEnc_struct_join_padAny_fails` :
`sep (ptsEnc full u8Rep 0 1) (sep (ptsEnc full pairRep (0 + 2) (2,3)) (padAny full layoutS 0)) heapS9 ∧ ¬ ptsEnc full structS 0 (1,(2,3)) heapS9 ∧ ¬ (∀ p a v₁ v₂ h, sep (ptsEnc p u8Rep a v₁) (sep (ptsEnc p pairRep (a + 2) v₂) (padAny p layoutS a)) h → ptsEnc p structS a (v₁, v₂) h)`;
`ptsDec_struct_split_padUninit_fails` :
`ptsDec full structS 0 (1,(2,3)) heapS9 ∧ ¬ sep (ptsDec full u8Rep 0 1) (sep (ptsDec full pairRep (0 + 2) (2,3)) (padUninit full layoutS 0)) heapS9 ∧ ¬ (∀ p a v₁ v₂ h, ptsDec p structS a (v₁, v₂) h → sep (ptsDec p u8Rep a v₁) (sep (ptsDec p pairRep (a + 2) v₂) (padUninit p layoutS a)) h)`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `definitional`.
* **Non-vacuity witness:** The counterexamples themselves. (Lean: `Toy.ByteSL.ptsEnc_struct_join_padAny_fails`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsEnc_struct_join_padAny_fails`, `Toy.ByteSL.ptsDec_struct_split_padUninit_fails`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — For `#[repr(C)] struct S { a: u8, b: u16 }` on a target where `u16` has alignment 2 (so one padding byte sits at offset 1, as `layoutS` places it), a verifier that splits a struct into fields plus padding must pair decode-based fields with arbitrary padding (R2a) or encode-based fields with `uninit` padding (R2b); the other two pairings are unsound once padding has been written. The layout of `S` is an input to the model, not derived from Rust's layout rules.

### R3a: `R3a-encode-based-source-view-change-iff-transmute`

* **Kind / tier:** characterization, **T0**. MiniRust defines transmute as encode at the source type and decode at the target; this restates it as an entailment of typed points-to.
* **Plain claim:** For representations rA, rB of the same size (no laws assumed), values v and b: the encode-based points-to of v at A entails the decode-based points-to of b at B, at every permission, address and heap, exactly when transmute rA rB v = some b.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A)
  (rB : Rep (Bytes D n) B) (v : A) (b : B) :
  (∀ (p : Perm) (a : Nat) (h : BHeap D), ptsEnc p rA a v h → ptsDec p rB a b h) ↔ transmute rA rB v = some b
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsEnc_entails_ptsDec_iff_transmute_eq_some (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) v b` :
`(∀ p a h, h = block p a (rA.encode v) → ∃ x, h = block p a x ∧ rB.decode x = some b) ↔ rB.decode (rA.encode v) = some b`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `definitional`.
* **Non-vacuity witness:** transmute u8Rep boolRep 1 = some true, and the block [init 1] satisfies the encode-based points-to of 1 at u8Rep. (Lean: `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some_nonvacuous`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
  * zerocopy crate, version 0.8.63, documentation at https://docs.rs/zerocopy/0.8.63/zerocopy/: macro transmute_mut! behaves like a function from &'src mut Src to &'dst mut Dst with bounds Src: FromBytes + IntoBytes, Dst: FromBytes + IntoBytes, align_of::<Src>() >= align_of::<Dst>() and size compatibility; macro transmute_ref! behaves like a function from &'src Src to &'dst Dst with bounds Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, and the same alignment and size conditions. Cited only for these bounds.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — Reinterpreting memory that holds exactly the bytes a typed store of `v : A` wrote as a `B` succeeds with `b` exactly when MiniRust's `transmute` (encode at `A`, decode at `B`) returns `b`; MiniRust's additional `check_value` step is not modeled. This is not kernel-checked; it depends on the real types' byte representations matching the model's byte-representation, layout, and permission definitions, which is not verified here.

### R3b: `R3b-decode-based-source-view-change-iff-transmute-under-laws`

* **Kind / tier:** characterization, **T1**. The byte-level ingredient (validity-set inclusion under the laws) is R5b of the published representation package; stating it pointwise as an entailment of decode-based points-to, with the value b exposed, is new in form but folklore in content.
* **Plain claim:** For representations rA, rB of the same size, if A satisfies DecodeEncode and EncodeLeast and B satisfies DecodeMono, then for all values v, b: the decode-based points-to of v at A entails the decode-based points-to of b at B, at every permission, address and heap, exactly when transmute rA rB v = some b.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono {D A B : Type} {n : Nat}
  (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (hDE_A : rA.DecodeEncode) (hEL_A : rA.EncodeLeast)
  (hM_B : rB.DecodeMono) (v : A) (b : B) :
  (∀ (p : Perm) (a : Nat) (h : BHeap D), ptsDec p rA a v h → ptsDec p rB a b h) ↔ transmute rA rB v = some b
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono (rA rB) (hDE_A : rA.DecodeEncode) (hEL_A : rA.EncodeLeast) (hM_B : rB.DecodeMono) v b` :
`(∀ p a h, ptsDec p rA a v h → ptsDec p rB a b h) ↔ rB.decode (rA.encode v) = some b`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hDE_A : rA.DecodeEncode` | The block holding the A-encoding of v satisfies the decode-based points-to of v (left-to-right). | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hDE_A` |
| `hEL_A : rA.EncodeLeast` | Every byte vector decoding to v at A lies above the A-encoding of v (right-to-left). | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hEL_A` |
| `hM_B : rB.DecodeMono` | Bytes above the A-encoding still decode at B to b (right-to-left). | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hM_B` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** A = pairRep (two-byte integer), B = u8PadRep (padded u8): all laws hold and transmute (5, 7) = some 5. (Lean: `Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_nonvacuous`).
* **Prior art:**
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
  * zerocopy crate, version 0.8.63, documentation at https://docs.rs/zerocopy/0.8.63/zerocopy/: macro transmute_mut! behaves like a function from &'src mut Src to &'dst mut Dst with bounds Src: FromBytes + IntoBytes, Dst: FromBytes + IntoBytes, align_of::<Src>() >= align_of::<Dst>() and size compatibility; macro transmute_ref! behaves like a function from &'src Src to &'dst Dst with bounds Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, and the same alignment and size conditions. Cited only for these bounds.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — For source types whose representations satisfy `DecodeEncode` and `EncodeLeast` and target types with monotone decoders (all three MiniRust properties), a consuming by-reference reinterpretation of a typed view is valid for exactly the values on which the by-value transmute succeeds. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R3c: `R3c-view-change-from-intoBytes-encodeLeast-source-to-any-target`

* **Kind / tier:** theorem, **T1**. The observation that, for an IntoBytes source satisfying EncodeLeast, the decode-based points-to pins the bytes to the encoding, so the view change needs no law on the target, is folklore made precise here; the byte-level facts are those of the published representation package.
* **Plain claim:** For representations rA, rB of the same size: if A is IntoBytes (no encoding contains uninit) and satisfies EncodeLeast, then for every v and every b with transmute rA rB v = some b, the decode-based points-to of v at A entails the decode-based points-to of b at B at every permission, address and heap. Nothing is assumed about B: none of DecodeMono, DecodeEncode, EncodeLeast or FromBytes.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast {D A B : Type} {n : Nat}
  (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) (v : A) (b : B)
  (ht : transmute rA rB v = some b) (p : Perm) (a : Nat) (h : BHeap D) : ptsDec p rA a v h → ptsDec p rB a b h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast (rA rB) (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) v b (ht : rB.decode (rA.encode v) = some b)` :
`∀ p a h, ptsDec p rA a v h → ptsDec p rB a b h`

The entailment is vacuous for a source whose decoder accepts nothing, which the hypotheses allow
because `DecodeEncode` of the source is not assumed
(`Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep`); the non-vacuity witness uses
the lawful source `u8Rep`.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hIB_A : rA.IntoBytes` | With EncodeLeast, the only byte vector decoding to v at A is the encoding of v (an initialized vector is maximal), so the heap holds exactly the bytes transmute decodes. | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hIB_A` |
| `hEL_A : rA.EncodeLeast` | Byte vectors decoding to v at A lie above (hence, being initialized, equal) the encoding of v. | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hEL_A` |
| `ht : transmute rA rB v = some b` | Fixes the target value to the transmute result. | tight: counterexample `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_ht` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** A = u8Rep (IntoBytes, EncodeLeast); transmute succeeds both into nonMonoBoolRep (FromBytes, not DecodeMono) and into boolRep (not FromBytes) at 1, and the decode-based points-to of 1 at u8Rep is inhabited. (Lean: `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_nonvacuous`).
* **Prior art:**
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
  * zerocopy crate, version 0.8.63, documentation at https://docs.rs/zerocopy/0.8.63/zerocopy/: macro transmute_mut! behaves like a function from &'src mut Src to &'dst mut Dst with bounds Src: FromBytes + IntoBytes, Dst: FromBytes + IntoBytes, align_of::<Src>() >= align_of::<Dst>() and size compatibility; macro transmute_ref! behaves like a function from &'src Src to &'dst Dst with bounds Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, and the same alignment and size conditions. Cited only for these bounds.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — zerocopy 0.8.63's `transmute_ref!` requires `Src: IntoBytes + Immutable` and `Dst: FromBytes + Immutable`, and its `transmute_mut!` requires both types to be `FromBytes + IntoBytes`; both also require alignment and size conditions. In this model, the semantic `IntoBytes` of the source together with `EncodeLeast` already makes every successful transmute a consuming view change, with no condition on the target; this does not justify the macros' reborrowing semantics (see the non-claims), and alignment and `Immutable` are outside the model. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R3f: `R3f-total-view-change-from-intoBytes-encodeLeast-to-fromBytes`

* **Kind / tier:** theorem, **T1**. Combines the published package's totality condition (IntoBytes source, FromBytes target, its R2a, copied here with proof) with R3c; zerocopy-style conditions are folklore, the observation that no law is needed on the target is made precise here.
* **Plain claim:** For representations rA, rB of the same size: if A is IntoBytes and satisfies EncodeLeast and B is FromBytes (every fully initialized byte vector decodes), then for every v there is a b, namely the result of transmute rA rB v, such that the decode-based points-to of v at A entails the decode-based points-to of b at B at every permission, address and heap. None of DecodeMono, DecodeEncode, EncodeLeast is assumed for B.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A)
  (rB : Rep (Bytes D n) B) (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) (hFB_B : rB.FromBytes) (v : A) :
  ∃ b, transmute rA rB v = some b ∧ ∀ (p : Perm) (a : Nat) (h : BHeap D), ptsDec p rA a v h → ptsDec p rB a b h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes (rA rB) (hIB_A : rA.IntoBytes) (hEL_A : rA.EncodeLeast) (hFB_B : rB.FromBytes)` :
`∀ v, ∃ b, rB.decode (rA.encode v) = some b ∧ ∀ p a h, ptsDec p rA a v h → ptsDec p rB a b h`

Like R3c, R3f does not assume `DecodeEncode` of the source: for the source `noneRep u8Rep.encode`
(the `u8` encoder with a decoder that accepts nothing) and the target `u8Rep`, all hypotheses hold
and `transmute` is total, yet the source decode-based points-to holds for no heap, so the
entailment is vacuous (`Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep`). The
non-vacuity witness uses the lawful source `u8Rep`.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hIB_A : rA.IntoBytes` | Every A-encoding is fully initialized, so FromBytes B makes transmute succeed; with EncodeLeast it pins the heap to the encoding (as in R3c). | tight: counterexample `Toy.ByteSL.exists_ptsDec_viewChange_tight_hIB_A` |
| `hEL_A : rA.EncodeLeast` | Byte vectors decoding to v at A equal the encoding of v (as in R3c). | tight: counterexample `Toy.ByteSL.exists_ptsDec_viewChange_tight_hEL_A` |
| `hFB_B : rB.FromBytes` | Every fully initialized byte vector decodes at B, so a target value exists. | tight: counterexample `Toy.ByteSL.exists_ptsDec_viewChange_tight_hFB_B` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** A = pairRep (IntoBytes, EncodeLeast), B = u8PadRep (FromBytes): transmute (5, 7) = some 5 and the source points-to is inhabited; also u8Rep -> nonMonoBoolRep satisfies all hypotheses with a target violating DecodeMono. (Lean: `Toy.ByteSL.exists_ptsDec_viewChange_nonvacuous`).
* **Prior art:**
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
  * zerocopy crate, version 0.8.63, documentation at https://docs.rs/zerocopy/0.8.63/zerocopy/: macro transmute_mut! behaves like a function from &'src mut Src to &'dst mut Dst with bounds Src: FromBytes + IntoBytes, Dst: FromBytes + IntoBytes, align_of::<Src>() >= align_of::<Dst>() and size compatibility; macro transmute_ref! behaves like a function from &'src Src to &'dst Dst with bounds Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, and the same alignment and size conditions. Cited only for these bounds.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — With a `FromBytes` target as well (the semantic counterpart of zerocopy's `Dst: FromBytes` bound), the view change exists for every source value, which is the consuming-cast reading of `transmute_ref!`'s trait bounds without its alignment and `Immutable` conditions. This is not kernel-checked; it depends on the real types' byte representations satisfying the stated laws, which is not verified here.

### R3d: `R3d-niche-view-change-is-one-directional`

* **Kind / tier:** counterexample, **T0**. The standard niche example; its byte-level content (boolRep is not FromBytes; the byte 2 does not decode) is mechanized in the published representation package. Restated as entailments.
* **Plain claim:** Viewing boolRep (a bool-like type: only the bytes 0 and 1 decode) as u8Rep is a view change for every value (the boolRep value v becomes the byte boolEnc v), but viewing u8Rep as boolRep is not: the block [init 2] satisfies the decode-based points-to of 2 at u8Rep and of no value at boolRep.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.niche_viewChange_one_directional :
  (∀ (v : Bool) (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p boolRep a v h → ptsDec p u8Rep a (boolEnc v) h) ∧
    ptsDec Perm.full u8Rep 0 2 (Heap.block Perm.full 0 #v[AByte.init 2]) ∧
      (∀ (b : Bool), ¬ptsDec Perm.full boolRep 0 b (Heap.block Perm.full 0 #v[AByte.init 2])) ∧
        ¬∀ (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p u8Rep a 2 h → ∃ b, ptsDec p boolRep a b h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `niche_viewChange_one_directional` :
`(∀ v p a h, ptsDec p boolRep a v h → ptsDec p u8Rep a (boolEnc v) h) ∧ ptsDec full u8Rep 0 2 (block full 0 [init 2]) ∧ (∀ b, ¬ ptsDec full boolRep 0 b (block full 0 [init 2])) ∧ ¬ (∀ p a h, ptsDec p u8Rep a 2 h → ∃ b, ptsDec p boolRep a b h)`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.niche_viewChange_one_directional`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.niche_viewChange_one_directional`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — Rust's `bool` has a niche (only bytes 0 and 1 are valid): a `bool` view of memory may be weakened to a `u8` view, but a `u8` view may not be strengthened to a `bool` view in general, because the bytes may hold 2. The model's `boolRep` encodes this validity rule; Rust's actual `bool` validity is taken from the language rules, not verified here.

### R3e: `R3e-padding-view-change-is-one-directional`

* **Kind / tier:** counterexample, **T0**. The standard 'padding read as data' example; its byte-level content (u8PadRep is not IntoBytes; pairRep rejects an uninit byte) is mechanized in the published representation package. Restated as entailments.
* **Plain claim:** Viewing pairRep (a two-byte integer (x, y), both bytes initialized) as u8PadRep (a u8 followed by a padding byte) is a view change for every value (the padded struct holds x), but the reverse is not: the block [init 5, uninit] satisfies the decode-based points-to of 5 at u8PadRep and of no value at pairRep.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.padding_viewChange_one_directional :
  (∀ (x y : Byte) (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p pairRep a (x, y) h → ptsDec p u8PadRep a x h) ∧
    ptsDec Perm.full u8PadRep 0 5 (Heap.block Perm.full 0 #v[AByte.init 5, AByte.uninit]) ∧
      (∀ (w : Byte × Byte), ¬ptsDec Perm.full pairRep 0 w (Heap.block Perm.full 0 #v[AByte.init 5, AByte.uninit])) ∧
        ¬∀ (p : Perm) (a : Nat) (h : BHeap Byte), ptsDec p u8PadRep a 5 h → ∃ w, ptsDec p pairRep a w h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `padding_viewChange_one_directional` :
`(∀ x y p a h, ptsDec p pairRep a (x, y) h → ptsDec p u8PadRep a x h) ∧ ptsDec full u8PadRep 0 5 (block full 0 [init 5, uninit]) ∧ (∀ w, ¬ ptsDec full pairRep 0 w (block full 0 [init 5, uninit])) ∧ ¬ (∀ p a h, ptsDec p u8PadRep a 5 h → ∃ w, ptsDec p pairRep a w h)`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.padding_viewChange_one_directional`).
* **Prior art:**
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * Gaeher, L., Sammler, M., Jung, R., Krebbers, R. & Dreyer, D., 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', PACMPL 8(PLDI), Article 192, 2024, doi:10.1145/3656422. Section 4 (Radium): values are lists of memory bytes, each a normal byte (0-255), a location fragment, or poison (e.g. for uninitialized memory); the heap maps locations to memory bytes; loads and stores are parameterized by a layout. Section 4.1 and Fig. 7: struct layouts list explicit unnamed fields for padding, and verification is parametric in a layout algorithm. Section 4.2: unlike lambda-Rust, Radium represents padding, and reading padding bytes as an integer is undefined behavior. Section 5.1 and Fig. 8: value types include uninit st (uninitialized memory of syntactic type st) and maybe_init T.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.padding_viewChange_one_directional`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — A two-byte integer may be viewed as a `u8` followed by a padding byte, but not conversely: memory produced by a typed store of the padded struct has an `uninit` second byte, which no integer accepts. The modeled types stand for such Rust types only insofar as their representations match `pairRep` and `u8PadRep`.

### R4a: `R4a-read-only-views-coexist-iff-common-bytes`

* **Kind / tier:** characterization, **T1**. Read-only (fractional or idempotent) sharing is standard (Boyland 2003; Bornat et al. 2005; COY 2007's {R, RW}); the characterization for two typed views over the same bytes is folklore made precise.
* **Plain claim:** For representations rA, rB of the same size, address a and values v, w: (1) a heap h satisfies the separating conjunction of the read-only decode-based points-to of v at A and of w at B, both at a, iff h is the read-only block at a of some byte vector x with rA.decode x = some v and rB.decode x = some w; (2) hence that conjunction is satisfiable iff such an x exists; (3) the separating conjunction of the read-only encode-based points-to of v at A and of w at B is satisfiable iff the two encodings are the same byte vector (a separate statement, not a consequence of (1)).
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.sep_ro_ptsDec_iff_block_decodes {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B)
  (a : Nat) (v : A) (w : B) (h : BHeap D) :
  sep (ptsDec Perm.ro rA a v) (ptsDec Perm.ro rB a w) h ↔
    ∃ x, h = Heap.block Perm.ro a x ∧ rA.decode x = some v ∧ rB.decode x = some w
Toy.ByteSL.sep_ro_ptsDec_satisfiable_iff_common_bytes {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A)
  (rB : Rep (Bytes D n) B) (a : Nat) (v : A) (w : B) :
  (∃ h, sep (ptsDec Perm.ro rA a v) (ptsDec Perm.ro rB a w) h) ↔ ∃ x, rA.decode x = some v ∧ rB.decode x = some w
Toy.ByteSL.sep_ro_ptsEnc_satisfiable_iff_encode_eq {D A B : Type} {n : Nat} (rA : Rep (Bytes D n) A)
  (rB : Rep (Bytes D n) B) (a : Nat) (v : A) (w : B) :
  (∃ h, sep (ptsEnc Perm.ro rA a v) (ptsEnc Perm.ro rB a w) h) ↔ rA.encode v = rB.encode w
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `sep_ro_ptsDec_iff_block_decodes (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) a v w h` :
`sep (ptsDec ro rA a v) (ptsDec ro rB a w) h ↔ ∃ x, h = block ro a x ∧ rA.decode x = some v ∧ rB.decode x = some w`;
`sep_ro_ptsDec_satisfiable_iff_common_bytes` : `(∃ h, sep (ptsDec ro rA a v) (ptsDec ro rB a w) h) ↔ ∃ x, rA.decode x = some v ∧ rB.decode x = some w`;
`sep_ro_ptsEnc_satisfiable_iff_encode_eq` : `(∃ h, sep (ptsEnc ro rA a v) (ptsEnc ro rB a w) h) ↔ rA.encode v = rB.encode w`.

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The byte 1 viewed read-only as the u8Rep value 1 and as the boolRep value true; and no read-only boolRep view coexists with the u8Rep view of 2. (Lean: `Toy.ByteSL.sep_ro_ptsDec_nonvacuous`).
* **Prior art:**
  * Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', PACMPL 2(POPL), Article 66, 2018, doi:10.1145/3158154. Section 3.2: following Lee et al. 2017, freshly allocated memory holds a poison value; the only safe operations on it are loads and stores. Section 3.3: the type of 'arbitrary sequences of n base values' represents uninitialized memory. Sections 4.1-4.2: a type is interpreted by a predicate [[tau]].own(t, vs) on lists of values with |vs| = [[tau]].size, and [[tau1 x tau2]].own splits vs = vs1 ++ vs2 (memory locations hold values, not bytes; products have no padding). Section 4.3: shared references are interpreted by a separate, type-specific sharing predicate [[tau]].shr(kappa, t, l); Section 6 uses it for Cell and Mutex (interior mutability).
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
  * Boyland, J., 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, doi:10.1007/3-540-44898-5_4: introduces fractional permissions (writing needs the whole permission, reading any fraction; fractions recombine). Cited as the origin of fractional permissions; the two-point full / read-only algebra here is a non-fractional, non-recombinable variant.
  * Bornat, R., Calcagno, C., O'Hearn, P. W. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327: brings fractional (and counting) permissions into separation logic; cited by COY 2007 as the source of heaps with permissions.
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf): Section 3 recalls Safety Monotonicity and the Frame Property for relations and states that 'a relation R satisfies Safety Monotonicity and the Frame Property iff the frame rule is sound for it'. Definition 1 takes a separation algebra to be a cancellative partial commutative monoid; its Example 2 (heaps with permissions, HPerm, over a permission algebra required to be cancellative) mentions the permission algebra {R, RW} with R o R = R and RW o p undefined, remarking that it does not allow converting a total (RW) permission into several read permissions or back. That two-point algebra is the permission algebra of this package; the heap algebra it induces with the empty heap as unit is not cancellative (R5f), so this instance lies outside Definition 1.
  * Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, doi:10.1007/978-3-642-10672-9_13 (author PDF https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf): revisits the separation-algebra axioms; its disjointness axiom (a + a = b implies a = b: no nonempty share joins with itself) is motivated by the remark that without disjointness 'the obvious definition of a formula to describe binary trees in fact describes directed acyclic graphs'. The idempotent read-only cells of this package violate that axiom.
  * Vindum, S. F. & Birkedal, L., 'Contextual Refinement of the Michael-Scott Queue (Proof Pearl)', CPP 2021, pp. 76-90, doi:10.1145/3437992.3439930: introduces discardable fractions for Iris points-to assertions, where a fraction can be irrevocably discarded to obtain persistent, freely duplicable read-only ownership; Iris itself is described in Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L. & Dreyer, D., 'Iris from the ground up', Journal of Functional Programming 28, e20, 2018, doi:10.1017/S0956796818000151. The read-only permission of this package behaves like a discarded fraction without the fractional part.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.sep_ro_ptsDec_iff_block_decodes`, `Toy.ByteSL.sep_ro_ptsDec_satisfiable_iff_common_bytes`, `Toy.ByteSL.sep_ro_ptsEnc_satisfiable_iff_encode_eq`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — Two shared (read-only) typed views of the same bytes, for example `&A` and `&B` produced by a read-only reinterpretation of memory without interior mutability, can coexist exactly when some byte pattern is valid for both values; for encode-based views, exactly when the two encodings are identical. Interior mutability (`UnsafeCell`) is outside the model. This is not kernel-checked; it depends on the real types' byte representations matching the model's byte-representation, layout, and permission definitions, which is not verified here.

### R4b: `R4b-full-permission-view-excludes-any-second-view`

* **Kind / tier:** impossibility, **T0**. Exclusivity of full (write) permission is textbook separation logic and mechanized (e.g. VST's data_at_conflict_glb); restated here for two typed views of possibly different types.
* **Plain claim:** For representations rA, rB of the same nonzero size, if at least one of the two permissions is full, no heap satisfies the separating conjunction of the decode-based typed points-to of v at A and of w at B at the same address.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.not_sep_ptsDec_of_full_of_pos_size {D A B : Type} {n : Nat} (hn : 0 < n) (rA : Rep (Bytes D n) A)
  (rB : Rep (Bytes D n) B) (p q : Perm) (hpq : p = Perm.full ∨ q = Perm.full) (a : Nat) (v : A) (w : B) (h : BHeap D) :
  ¬sep (ptsDec p rA a v) (ptsDec q rB a w) h
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `not_sep_ptsDec_of_full_of_pos_size (hn : 0 < n) (rA rB) (p q : Perm) (hpq : p = full ∨ q = full) a v w h` :
`¬ sep (ptsDec p rA a v) (ptsDec q rB a w) h`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hn : 0 < n` | Views of size 0 own no cell and always coexist. | tight: counterexample `Toy.ByteSL.not_sep_ptsDec_tight_hn` |
| `hpq : p = full or q = full` | With read-only permission on both sides the views can coexist. | tight: counterexample `Toy.ByteSL.not_sep_ptsDec_tight_hpq` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** u8Rep and boolRep at size 1 with p = full and q = ro: all hypotheses hold and each view alone is satisfiable. (Lean: `Toy.ByteSL.not_sep_ptsDec_nonvacuous`).
* **Positive control:** `Toy.ByteSL.not_sep_ptsDec_positive_control` — the read-only `u8Rep` view of `1` and the read-only `boolRep` view of `true` at address 0 are jointly satisfiable, so the conclusion fails once neither permission is `full`.
* **Prior art:**
  * Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', PACMPL 2(POPL), Article 66, 2018, doi:10.1145/3158154. Section 3.2: following Lee et al. 2017, freshly allocated memory holds a poison value; the only safe operations on it are loads and stores. Section 3.3: the type of 'arbitrary sequences of n base values' represents uninitialized memory. Sections 4.1-4.2: a type is interpreted by a predicate [[tau]].own(t, vs) on lists of values with |vs| = [[tau]].size, and [[tau1 x tau2]].own splits vs = vs1 ++ vs2 (memory locations hold values, not bytes; products have no padding). Section 4.3: shared references are interpreted by a separate, type-specific sharing predicate [[tau]].shr(kappa, t, l); Section 6 uses it for Cell and Mutex (interior mutability).
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
  * Boyland, J., 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, doi:10.1007/3-540-44898-5_4: introduces fractional permissions (writing needs the whole permission, reading any fraction; fractions recombine). Cited as the origin of fractional permissions; the two-point full / read-only algebra here is a non-fractional, non-recombinable variant.
  * Bornat, R., Calcagno, C., O'Hearn, P. W. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327: brings fractional (and counting) permissions into separation logic; cited by COY 2007 as the source of heaps with permissions.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.not_sep_ptsDec_of_full_of_pos_size`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — An exclusive (full-permission) typed view of nonempty memory, such as one modeling a `&mut` or an owner, excludes any simultaneous second typed view of the same bytes in the separating conjunction, whatever the types; this is the model's form of the aliasing-XOR-mutability discipline, without lifetimes or temporary loans. This is not kernel-checked; it depends on the real types' byte representations matching the model's byte-representation, layout, and permission definitions, which is not verified here.

### R5a: `R5a-frame-rule-iff-locality-in-every-separation-structure`

* **Kind / tier:** characterization, **T0**. Stated by Calcagno-O'Hearn-Yang 2007 (Section 3: a relation satisfies Safety Monotonicity and the Frame Property iff the frame rule is sound for it), building on Yang-O'Hearn 2002 (Lemmas 1-2, Theorem 1, and the abstract partial-commutative-monoid setting of Section 4.1). A re-derivation for the relational commands of this package, with no algebraic law.
* **Plain claim:** In every separation structure (a carrier with a disjointness relation and a union operation, no algebraic law assumed; in particular on the byte heap with read-only sharing, which is not cancellative), for every command c: the frame rule is sound for c (for all assertions P, Q, R, {P} c {Q} implies {P * R} c {Q * R}) iff c is safety-monotone and has the frame property.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.frameRuleSound_iff_safetyMono_and_frameProp.{u_1} {S : Type u_1} [SepStruct S] (c : Cmd S) :
  FrameRuleSound c ↔ SafetyMono c ∧ FrameProp c
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `frameRuleSound_iff_safetyMono_and_frameProp {S} [SepStruct S] (c : Cmd S)` :
`FrameRuleSound c ↔ SafetyMono c ∧ FrameProp c`

The definitions involved (`SepStruct`, `Cmd`, `Triple`, `SafetyMono`, `FrameProp`, `Local`,
`FrameRuleSound`) are copied unchanged from the published package
`frame-rule-locality-and-precise-assertions`, and this statement is that package's R2b; it is
restated here so that the byte-heap results R5b–R5f can be read against it within one package.

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** On the byte heap, {0 |-> uninit} [0] := init 1 {0 |-> init 1} holds for the byte store, so the frame rule has non-trivial premises. (Lean: `Toy.ByteSL.byteHeap_frameRule_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf): Section 3 recalls Safety Monotonicity and the Frame Property for relations and states that 'a relation R satisfies Safety Monotonicity and the Frame Property iff the frame rule is sound for it'. Definition 1 takes a separation algebra to be a cancellative partial commutative monoid; its Example 2 (heaps with permissions, HPerm, over a permission algebra required to be cancellative) mentions the permission algebra {R, RW} with R o R = R and RW o p undefined, remarking that it does not allow converting a total (RW) permission into several read permissions or back. That two-point algebra is the permission algebra of this package; the heap algebra it induces with the empty heap as unit is not cancellative (R5f), so this instance lies outside Definition 1.
  * Klein, G., Kolanski, R. & Boyton, A., 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22, with the Archive of Formal Proofs entry 'Separation Algebra' (May 2012): an Isabelle/HOL type-class library of separation algebras based on COY 2007 in which cancellativity is a separate subclass (cancellative_sep_algebra, assumption sep_add_cancelD: x + z = y + z with x ## z and y ## z implies x = y), the right-cancellation law RightCancel of this package.
  * Published package 'frame-rule-locality-and-precise-assertions' of this corpus (google/zerocopy branch reference, commit 8ff18039787575ce7f24066acdc7600918ad8185). Its definitions of separation structures, commands, outcomes, assertions, separating conjunction, fault-avoiding triples, SafetyMono, FrameProp, Local and FrameRuleSound (support file lean/Toy/Sep/Basic.lean, namespace Toy.Sep) are the source of this package's lean/Toy/ByteSL/SepBasic.lean, which consists of a subset of that file's declarations, their code copied unchanged and the namespace renamed to Toy.ByteSL. Its R2b (Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp: in any separation structure, no laws, FrameRuleSound c <-> SafetyMono c and FrameProp c) is the same statement as R5a here; its R5 shows lookup, mutation, allocation and deallocation local in a finite-heap model with arbitrary cell values, address-disjoint union and no permissions; its R3a-R3d exhibit non-local heap commands (an allocation test, fixed-address allocation that faults, least-free-address allocation, predictable allocation).
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.frameRuleSound_iff_safetyMono_and_frameProp`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — No claim about real systems: the statement is about an abstract separation structure. It is the reason locality (R5b, R5c) and its failure (R5d, R5e) decide whether the frame rule may be used for a command.

### R5b: `R5b-byte-and-typed-commands-are-local`

* **Kind / tier:** theorem, **T0**. Locality of loads and stores is standard (Yang-O'Hearn 2002) and mechanized in byte-level program logics (e.g. VST); here restated for typed loads and stores over abstract, lawless representations on a heap with read-only sharing.
* **Plain claim:** For every byte payload type and every representation r (no laws assumed), each of the following commands is safety-monotone and has the frame property on the byte heap with read-only sharing: the byte store bstore a b and the typed store tstore r a v (fault unless every written cell is held with full permission; then write the byte, resp. r.encode v); the byte copy bcopy src dst (fault unless the source cell is allocated with any permission and the destination cell is held with full permission; copies one abstract byte, uninit included); the typed copy tcopy r src dst (fault unless the n source cells are allocated with any permission and decode, and the n destination cells are held with full permission; then write r.encode of the decoded value); and the typed load tload r a (fault unless the n cells are allocated with any permission and decode; it leaves the heap unchanged and returns nothing). Moreover (readBytes_frame_stable) the bytes such a read sees, hence the value it decodes, are the same in every disjoint extension of the heap, with the frame on either side.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.byte_commands_local {D : Type} :
  (∀ (a : Nat) (b : AByte D), Local (bstore a b)) ∧ ∀ (src dst : Nat), Local (bcopy src dst)
Toy.ByteSL.typed_commands_local {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
  (∀ (a : Nat) (v : V), Local (tstore r a v)) ∧
    (∀ (src dst : Nat), Local (tcopy r src dst)) ∧ ∀ (a : Nat), Local (tload r a)
Toy.ByteSL.readBytes_frame_stable {D : Type} {h h' : BHeap D} (hd : disj h h') {a n : Nat} {x : Bytes D n}
  (hr : readBytes h a n = some x) : readBytes (union h h') a n = some x ∧ readBytes (union h' h) a n = some x
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `byte_commands_local {D}` : `(∀ a b, Local (bstore a b)) ∧ (∀ src dst, Local (bcopy src dst))`;
`typed_commands_local (r : Rep (Bytes D n) V)` : `(∀ a v, Local (tstore r a v)) ∧ (∀ src dst, Local (tcopy r src dst)) ∧ (∀ a, Local (tload r a))`;
`readBytes_frame_stable (hd : disj h h') (hr : readBytes h a n = some x)` : `readBytes (union h h') a n = some x ∧ readBytes (union h' h) a n = some x`.

**The three bundled theorems.** R5b consists of `byte_commands_local` and `typed_commands_local`,
which have no hypotheses (each command's parameters are bound inside its own conjunct, so the
byte commands mention no representation and the `tcopy` and `tload` conjuncts, which take no value
argument, are not vacuous even for an empty value type), and `readBytes_frame_stable`, which
states what "the value a typed load decodes does not depend on the frame" means in this model. Its
two premises are both tight:

* `hd : disj h h'` — the frame `h'` is disjoint from `h`. Because `union` is left-biased on
  overlapping cells, the left-framed conjunct `readBytes (union h h') a n = some x` follows from
  `hr` alone; `hd` is needed for the right-framed conjunct `readBytes (union h' h) a n = some x`
  (proved by rewriting with commutativity of `union` on disjoint heaps). Counterexample
  `Toy.ByteSL.readBytes_frame_stable_tight_hd`: `h` holds the full cell `0 ↦ init 1` and `h'` the
  full cell `0 ↦ init 2`; `hr` holds for `x = [init 1]`, `hd` fails, the left-framed read still
  returns `[init 1]`, and the right-framed one does not.
* `hr : readBytes h a n = some x` — the cells are allocated in `h` (any permission) and hold `x`.
  Counterexample `Toy.ByteSL.readBytes_frame_stable_tight_hr`: the empty heap with the empty frame.

Disjointness allows the frame to overlap `h` on read-only cells holding equal bytes, so the frame
may share the very cells being read: `Toy.ByteSL.readBytes_frame_stable_shared_ro_nonvacuous` reads
the read-only cell `0` of `union hDst hRO1`, where `hDst := block full 1 [uninit]` and
`hRO1 := block ro 0 [init 1]`, with the overlapping frame `hRO1` on either side and
runs `tcopy` and `tload` at `u8Rep` in the framed heap. The locality non-vacuity witness
`byte_and_typed_commands_nonvacuous` uses address-disjoint, full-permission heaps.

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hd : disj h h' (premise of readBytes_frame_stable only; the two locality theorems have no hypotheses)` | The frame must be disjoint from the heap. Because union is left-biased on overlapping cells, the left-framed conjunct readBytes (union h h') a n = some x holds even without it; the hypothesis is needed for the right-framed conjunct readBytes (union h' h) a n = some x. Disjointness allows overlap on read-only cells holding equal bytes, so the frame may share the cells being read at permission ro. | tight: counterexample `Toy.ByteSL.readBytes_frame_stable_tight_hd` |
| `hr : readBytes h a n = some x (premise of readBytes_frame_stable only)` | The cells read must be allocated in h (with any permission) and hold the bytes x. | tight: counterexample `Toy.ByteSL.readBytes_frame_stable_tight_hr` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** Each command has a normal outcome from a concrete heap (e.g. the typed copy at u8Rep from cell 0 to cell 1). For readBytes_frame_stable: the heap union hDst hRO1, where hDst := block full 1 [uninit] (cell 1 fully owned, holding an uninit byte) and hRO1 := block ro 0 [init 1] (cell 0 read-only, holding the byte 1), and the frame hRO1 overlap on the read-only cell 0 and are disjoint; the read of cell 0 returns [init 1] with the frame on either side, and tcopy and tload at u8Rep from address 0 run in the framed heap. (Lean: `Toy.ByteSL.byte_and_typed_commands_nonvacuous`, `Toy.ByteSL.readBytes_frame_stable_shared_ro_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
  * Tuch, H., Klein, G. & Norrish, M., 'Types, Bytes, and Separation Logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234 (author PDF https://trustworthy.systems/publications/nicta_full_text/134.pdf): a byte-level heap heap-mem; typed reads h-val h p = from-bytes (heap-list h (size-of TYPE('a)) (ptr-val p)) and the law from-bytes (to-bytes v) = Some v; a heap type description kept as an additional state component; separation logic embedded on top, with singleton assertion p |->g v = (lambda s. lift-typ-heap g s p = Some v and dom s = {ptr-val p ..+ size-of TYPE('a)}), where lift-typ-heap is defined only at pointers satisfying the guard and heap type description (s, g |=s p); i.e. a decode-based typed points-to with an exact byte footprint, guarded by alignment and type-description conditions that this package does not model.
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
  * Banerjee, R., Memarian, K., Makwana, D., Pulte, C., Krishnaswami, N. & Sewell, P., 'Fulminate: Testing CN Separation-Logic Specifications in C', PACMPL 9(POPL), Article 43, 2025, doi:10.1145/3704879: CN's built-in resources Owned (points-to indexed by C types) and Block (points-to for uninitialised memory); Section 2.3: runtime ownership checking keeps ghost state giving, for each byte of memory, the C stack depth of the function that owns it (per-byte ownership).
  * Published package 'frame-rule-locality-and-precise-assertions' of this corpus (google/zerocopy branch reference, commit 8ff18039787575ce7f24066acdc7600918ad8185). Its definitions of separation structures, commands, outcomes, assertions, separating conjunction, fault-avoiding triples, SafetyMono, FrameProp, Local and FrameRuleSound (support file lean/Toy/Sep/Basic.lean, namespace Toy.Sep) are the source of this package's lean/Toy/ByteSL/SepBasic.lean, which consists of a subset of that file's declarations, their code copied unchanged and the namespace renamed to Toy.ByteSL. Its R2b (Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp: in any separation structure, no laws, FrameRuleSound c <-> SafetyMono c and FrameProp c) is the same statement as R5a here; its R5 shows lookup, mutation, allocation and deallocation local in a finite-heap model with arbitrary cell values, address-disjoint union and no permissions; its R3a-R3d exhibit non-local heap commands (an allocation test, fixed-address allocation that faults, least-free-address allocation, predictable allocation).
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.byte_commands_local`, `Toy.ByteSL.typed_commands_local`, `Toy.ByteSL.readBytes_frame_stable`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — The byte and typed commands model raw-memory operations of unsafe Rust (a byte write, a byte copy, `ptr::write`-like typed stores, `ptr::read`-like typed loads, and copies through a typed temporary), each faulting where real Rust would have undefined behavior for lack of permission. In the model, verifying them with only their own footprint and then framing is sound, on a heap where read-only cells may be shared. That real Rust's operational semantics matches these fault conditions is assumed, not verified.

### R5c: `R5c-loose-typed-copy-is-local-under-decodeMono`

* **Kind / tier:** theorem, **T1**. Combines two standard ingredients (decode is monotone: MiniRust's generic properties and the published representation package's DecodeMono; locality: Yang-O'Hearn 2002). Folklore made precise; no novelty is claimed and no novelty search was run.
* **Plain claim:** For every representation r satisfying DecodeMono and all addresses src, dst, the loose typed copy tcopyLoose r src dst is safety-monotone and has the frame property. This command, instead of faulting, reads each unallocated source cell as uninit; it faults if the n bytes so read do not decode or the destination is not held with full permission, and otherwise writes the encoding of the decoded value at dst. In a disjoint extension the unowned source cells may be present with any bytes, which are at least as defined as uninit, so a monotone decoder still succeeds with the same value: the unowned bytes matter only if decoding already succeeds with uninit in their place, and then they do not change the result.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.tcopyLoose_local_of_decodeMono {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) (hM : r.DecodeMono)
  (src dst : Nat) : Local (tcopyLoose r src dst)
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `tcopyLoose_local_of_decodeMono (r) (hM : r.DecodeMono) src dst` : `Local (tcopyLoose r src dst)`

**Hypothesis ledger:**

| Hypothesis | Why needed | Tightness |
| :--- | :--- | :--- |
| `hM : r.DecodeMono` | Bytes supplied by a frame are more defined than uninit, so a monotone decoder gives the same result and does not start failing. | tight: counterexample `Toy.ByteSL.tcopyLoose_not_local_exactUnitRep` |

* **Depth:** `shallow`.
* **Non-vacuity witness:** u8PadRep is DecodeMono and the loose typed copy runs from a heap owning the source data byte but not the source padding byte. (Lean: `Toy.ByteSL.tcopyLoose_local_nonvacuous`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
  * MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
  * Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean) and restates no result of it as proved here except its R2a, copied with its proof.
  * AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.tcopyLoose_local_of_decodeMono`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — A typed copy that reads padding bytes it does not own as `uninit` is still frame-safe in the model when the decoder ignores (or is monotone in) those bytes; this is a fact about this permissive semantics. In an operational semantics where reading memory owned exclusively by someone else is undefined behavior or a data race, the footprint does not license such reads (`tcopyLoose_reads_frame_owned_full_cell`).

### R5d: `R5d-loose-byte-copy-is-not-local`

* **Kind / tier:** counterexample, **T0**. An instance of Yang-O'Hearn's observation (2002, Section 4.1) that letting a program observe whether a cell is active breaks locality.
* **Plain claim:** The byte copy that reads an unallocated source cell as uninit (bcopyLoose 0 1) is safety-monotone but violates the frame property, and the frame rule fails for it: the triple {1 |-> uninit} bcopyLoose 0 1 {cell 1 holds uninit} holds, but its framing with {0 |-> init 5} does not.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.bcopyLoose_safetyMono_and_not_frameProp :
  SafetyMono (bcopyLoose 0 1) ∧
    ¬FrameProp (bcopyLoose 0 1) ∧
      (Triple (ptsB Perm.full 1 #v[AByte.uninit]) (bcopyLoose 0 1) fun h =>
          h.val 1 = some { perm := Perm.full, byte := AByte.uninit }) ∧
        ¬Triple (sep (ptsB Perm.full 1 #v[AByte.uninit]) (ptsB Perm.full 0 #v[AByte.init 5])) (bcopyLoose 0 1)
              (sep (fun h => h.val 1 = some { perm := Perm.full, byte := AByte.uninit })
                (ptsB Perm.full 0 #v[AByte.init 5])) ∧
          ¬FrameRuleSound (bcopyLoose 0 1)
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `bcopyLoose_safetyMono_and_not_frameProp` (payload `Byte`) :
`SafetyMono (bcopyLoose 0 1) ∧ ¬ FrameProp (bcopyLoose 0 1) ∧ Triple (ptsB full 1 [uninit]) (bcopyLoose 0 1) (fun h => h.val 1 = some ⟨full, uninit⟩) ∧ ¬ Triple (sep (ptsB full 1 [uninit]) (ptsB full 0 [init 5])) (bcopyLoose 0 1) (sep (fun h => h.val 1 = some ⟨full, uninit⟩) (ptsB full 0 [init 5])) ∧ ¬ FrameRuleSound (bcopyLoose 0 1)`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.bcopyLoose_safetyMono_and_not_frameProp`).
* **Prior art:**
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
  * Published package 'frame-rule-locality-and-precise-assertions' of this corpus (google/zerocopy branch reference, commit 8ff18039787575ce7f24066acdc7600918ad8185). Its definitions of separation structures, commands, outcomes, assertions, separating conjunction, fault-avoiding triples, SafetyMono, FrameProp, Local and FrameRuleSound (support file lean/Toy/Sep/Basic.lean, namespace Toy.Sep) are the source of this package's lean/Toy/ByteSL/SepBasic.lean, which consists of a subset of that file's declarations, their code copied unchanged and the namespace renamed to Toy.ByteSL. Its R2b (Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp: in any separation structure, no laws, FrameRuleSound c <-> SafetyMono c and FrameProp c) is the same statement as R5a here; its R5 shows lookup, mutation, allocation and deallocation local in a finite-heap model with arbitrary cell values, address-disjoint union and no permissions; its R3a-R3d exhibit non-local heap commands (an allocation test, fixed-address allocation that faults, least-free-address allocation, predictable allocation).
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.bcopyLoose_safetyMono_and_not_frameProp`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — An operation that treats unowned memory as uninitialized instead of faulting (for example a copy that tolerates out-of-footprint reads) breaks framing, so a program logic cannot verify it with a local footprint; this is the byte-level instance of Yang and O'Hearn's observation that observing whether a cell is allocated defeats locality. The command is a model construct, not a specific Rust operation.

### R5e: `R5e-store-through-read-only-cell-is-not-local`

* **Kind / tier:** counterexample, **T0**. The standard reason read-only (shared) permissions must not allow writes (Bornat et al. 2005), made concrete.
* **Plain claim:** A byte store permitted with read-only permission (bstoreShared 0 (init 2)) is safety-monotone but violates the frame property: the read-only cell hRO1 = {0 |->ro 1} is disjoint from itself, yet every run of the store from hRO1 ends in {0 |->ro 2}, which is not disjoint from the frame hRO1. The frame rule fails for it: {0 |->ro 1} bstoreShared 0 (init 2) {0 |->ro 2} holds, but its framing with {0 |->ro 1} does not.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.bstoreShared_safetyMono_and_not_frameProp :
  SafetyMono (bstoreShared 0 (AByte.init 2)) ∧
    ¬FrameProp (bstoreShared 0 (AByte.init 2)) ∧
      disj hRO1 hRO1 ∧
        (∀ (h₀ : BHeap Byte), bstoreShared 0 (AByte.init 2) hRO1 (Outcome.ok h₀) → ¬disj h₀ hRO1) ∧
          Triple (ptsB Perm.ro 0 #v[AByte.init 1]) (bstoreShared 0 (AByte.init 2)) (ptsB Perm.ro 0 #v[AByte.init 2]) ∧
            ¬Triple (sep (ptsB Perm.ro 0 #v[AByte.init 1]) (ptsB Perm.ro 0 #v[AByte.init 1]))
                  (bstoreShared 0 (AByte.init 2))
                  (sep (ptsB Perm.ro 0 #v[AByte.init 2]) (ptsB Perm.ro 0 #v[AByte.init 1])) ∧
              ¬FrameRuleSound (bstoreShared 0 (AByte.init 2))
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `bstoreShared_safetyMono_and_not_frameProp` (with `hRO1 := block ro 0 [init 1]`) :
`SafetyMono (bstoreShared 0 (init 2)) ∧ ¬ FrameProp (bstoreShared 0 (init 2)) ∧ disj hRO1 hRO1 ∧ (∀ h₀, bstoreShared 0 (init 2) hRO1 (ok h₀) → ¬ disj h₀ hRO1) ∧ Triple (ptsB ro 0 [init 1]) (bstoreShared 0 (init 2)) (ptsB ro 0 [init 2]) ∧ ¬ Triple (sep (ptsB ro 0 [init 1]) (ptsB ro 0 [init 1])) (bstoreShared 0 (init 2)) (sep (ptsB ro 0 [init 2]) (ptsB ro 0 [init 1])) ∧ ¬ FrameRuleSound (bstoreShared 0 (init 2))`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.bstoreShared_safetyMono_and_not_frameProp`).
* **Prior art:**
  * Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', PACMPL 2(POPL), Article 66, 2018, doi:10.1145/3158154. Section 3.2: following Lee et al. 2017, freshly allocated memory holds a poison value; the only safe operations on it are loads and stores. Section 3.3: the type of 'arbitrary sequences of n base values' represents uninitialized memory. Sections 4.1-4.2: a type is interpreted by a predicate [[tau]].own(t, vs) on lists of values with |vs| = [[tau]].size, and [[tau1 x tau2]].own splits vs = vs1 ++ vs2 (memory locations hold values, not bytes; products have no padding). Section 4.3: shared references are interpreted by a separate, type-specific sharing predicate [[tau]].shr(kappa, t, l); Section 6 uses it for Cell and Mutex (interior mutability).
  * Bornat, R., Calcagno, C., O'Hearn, P. W. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327: brings fractional (and counting) permissions into separation logic; cited by COY 2007 as the source of heaps with permissions.
  * Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
  * Published package 'frame-rule-locality-and-precise-assertions' of this corpus (google/zerocopy branch reference, commit 8ff18039787575ce7f24066acdc7600918ad8185). Its definitions of separation structures, commands, outcomes, assertions, separating conjunction, fault-avoiding triples, SafetyMono, FrameProp, Local and FrameRuleSound (support file lean/Toy/Sep/Basic.lean, namespace Toy.Sep) are the source of this package's lean/Toy/ByteSL/SepBasic.lean, which consists of a subset of that file's declarations, their code copied unchanged and the namespace renamed to Toy.ByteSL. Its R2b (Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp: in any separation structure, no laws, FrameRuleSound c <-> SafetyMono c and FrameProp c) is the same statement as R5a here; its R5 shows lookup, mutation, allocation and deallocation local in a finite-heap model with arbitrary cell values, address-disjoint union and no permissions; its R3a-R3d exhibit non-local heap commands (an allocation test, fixed-address allocation that faults, least-free-address allocation, predictable allocation).
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.bstoreShared_safetyMono_and_not_frameProp`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — Writing through a shared (read-only) view, as interior mutability would allow, breaks framing in a logic whose shared views are freely duplicable; a logic that admits such writes needs a different sharing model (for example RustBelt's type-specific sharing predicates). Interior mutability itself is not modeled.

### R5f: `R5f-byte-heap-with-read-only-sharing-is-not-cancellative`

* **Kind / tier:** counterexample, **T0**. The permission algebra is COY 2007's {R, RW} (Definition 1, Example 2); that idempotent sharing makes the induced heap algebra non-cancellative is immediate (h * h = h * emp) and is why later treatments keep cancellativity separate (Klein-Kolanski-Boyton's Isabelle library has a separate cancellative subclass). Restated here.
* **Plain claim:** For every byte payload type D, the byte heap with read-only sharing is a partial commutative monoid with unit (symmetric disjointness, commutativity, partial associativity, the empty heap as unit) but is not right-cancellative: the read-only cell 0 |-> uninit is disjoint from itself and from the empty heap, and combined with itself gives the same heap as the empty heap combined with it, although it is not the empty heap.
* **Design question:** A verifier for low-level Rust wants byte-level ownership (padding, uninitialized memory, reinterpretation) together with typed reasoning: which typed points-to to build from byte points-to, when struct ownership splits into field ownership with padding, when a transmute is a pure view change, and how read-only views interact with these.

**Lean statement(s)** (pretty-printed by Lean with namespaces `Toy.ByteSL` and `SepStruct` open):

```lean
Toy.ByteSL.byteHeap_isSepAlgebra_and_not_rightCancel (D : Type) :
  IsSepAlgebra (BHeap D) Heap.emp ∧
    ¬RightCancel (BHeap D) ∧
      disj (roUninitCell D) (roUninitCell D) ∧
        disj Heap.emp (roUninitCell D) ∧
          union (roUninitCell D) (roUninitCell D) = union Heap.emp (roUninitCell D) ∧ roUninitCell D ≠ Heap.emp
```

**Unfolded** (key definitions expanded by hand; the Lean statement above is authoritative): `byteHeap_isSepAlgebra_and_not_rightCancel (D : Type)` (with `roUninitCell D := block ro 0 [uninit]`) :
`IsSepAlgebra (BHeap D) emp ∧ ¬ RightCancel (BHeap D) ∧ disj (roUninitCell D) (roUninitCell D) ∧ disj emp (roUninitCell D) ∧ union (roUninitCell D) (roUninitCell D) = union emp (roUninitCell D) ∧ roUninitCell D ≠ emp`

**Hypothesis ledger:**

No hypotheses beyond the typed binders of the statement (no representation law and no algebraic law is assumed).

* **Depth:** `shallow`.
* **Non-vacuity witness:** The counterexample itself. (Lean: `Toy.ByteSL.byteHeap_isSepAlgebra_and_not_rightCancel`).
* **Prior art:**
  * Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf): Section 3 recalls Safety Monotonicity and the Frame Property for relations and states that 'a relation R satisfies Safety Monotonicity and the Frame Property iff the frame rule is sound for it'. Definition 1 takes a separation algebra to be a cancellative partial commutative monoid; its Example 2 (heaps with permissions, HPerm, over a permission algebra required to be cancellative) mentions the permission algebra {R, RW} with R o R = R and RW o p undefined, remarking that it does not allow converting a total (RW) permission into several read permissions or back. That two-point algebra is the permission algebra of this package; the heap algebra it induces with the empty heap as unit is not cancellative (R5f), so this instance lies outside Definition 1.
  * Bornat, R., Calcagno, C., O'Hearn, P. W. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327: brings fractional (and counting) permissions into separation logic; cited by COY 2007 as the source of heaps with permissions.
  * Klein, G., Kolanski, R. & Boyton, A., 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22, with the Archive of Formal Proofs entry 'Separation Algebra' (May 2012): an Isabelle/HOL type-class library of separation algebras based on COY 2007 in which cancellativity is a separate subclass (cancellative_sep_algebra, assumption sep_add_cancelD: x + z = y + z with x ## z and y ## z implies x = y), the right-cancellation law RightCancel of this package.
  * Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', Electronic Notes in Theoretical Computer Science 276 (MFPS XXVII), pp. 171-190, 2011, doi:10.1016/j.entcs.2011.09.021: studies the interplay of precision and the conjunction rule in separation logic, the kind of result that does not transfer to non-cancellative models without further argument (cited for its topic only).
  * Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, doi:10.1007/978-3-642-10672-9_13 (author PDF https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf): revisits the separation-algebra axioms; its disjointness axiom (a + a = b implies a = b: no nonempty share joins with itself) is motivated by the remark that without disjointness 'the obvious definition of a formula to describe binary trees in fact describes directed acyclic graphs'. The idempotent read-only cells of this package violate that axiom.
  * Vindum, S. F. & Birkedal, L., 'Contextual Refinement of the Michael-Scott Queue (Proof Pearl)', CPP 2021, pp. 76-90, doi:10.1145/3437992.3439930: introduces discardable fractions for Iris points-to assertions, where a fraction can be irrevocably discarded to obtain persistent, freely duplicable read-only ownership; Iris itself is described in Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L. & Dreyer, D., 'Iris from the ground up', Journal of Functional Programming 28, e20, 2018, doi:10.1017/S0956796818000151. The read-only permission of this package behaves like a discarded fraction without the fractional part.
  * Boyland, J., 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, doi:10.1007/3-540-44898-5_4: introduces fractional permissions (writing needs the whole permission, reading any fraction; fractions recombine). Cited as the origin of fractional permissions; the two-point full / read-only algebra here is a non-fractional, non-recombinable variant.
* **Basis: execution (Lean kernel check)** — `Toy.ByteSL.byteHeap_isSepAlgebra_and_not_rightCancel`; axioms and hashes under **Evidence**.
* **Basis: derived (modeling bridge)** — The read-only-sharing heap is outside the cancellative separation algebras of Calcagno, O'Hearn and Yang 2007 (Definition 1), so results that assume cancellativity (for example about precision and the conjunction rule) do not transfer to it without a new argument; R5a does not need cancellativity.

### What the results say about the design question

* **Which typed points-to?** The decode-based form equals the byte-definedness upward closure of
  the encode-based form exactly when the representation satisfies the three laws (R1b); under the
  laws the two coincide iff the type has no `uninit` bytes in its encodings (R1c); initialized
  padding separates them (R1d). The encode-based form is what a typed store writes; the
  decode-based form is what a typed load needs, is closed under initializing padding, and is the
  form for which view changes have clean conditions (R3b, R3c, R3f). Recommended: decode-based as
  the primary typed points-to, encode-based as the stronger postcondition of typed stores (R1a: it
  entails the decode-based form under `DecodeEncode`). This recommendation is argued from these
  results, not proved as an impossibility for the alternative.
* **Struct split/join with padding.** For non-overlapping layouts both pairings are exact and
  need no representation law: decode-based fields + padding holding anything (R2a), encode-based
  fields + `uninit` padding (R2b), each with one permission for all three pieces. Non-overlap is
  necessary (both laws fail for a union-like layout at full permission). The mixed pairings fail
  (R2c). Recommended: the decode-based pairing (as VST's `data_at` with spacers), since it survives
  initialized padding.
* **Transmute as a view change.** From the encode-based source: exactly when the transmute
  returns `some b` (R3a). From the decode-based source: the same, under `DecodeEncode` and
  `EncodeLeast` of the source and `DecodeMono` of the target (R3b). With an `IntoBytes`,
  `EncodeLeast` source, every successful transmute is a view change with no assumption on the
  target (R3c); if the target is also `FromBytes`, a view change exists for every value (R3f).
  View changes are one-directional: the niche (R3d) and padding (R3e) examples. These are
  consuming view changes at one permission; temporary `&mut` reborrowing, alignment and interior
  mutability are outside the model.
* **Shared views.** Two read-only typed views coexist iff some byte vector decodes under both
  (R4a); full permission on either side excludes them (R4b). Writes through read-only cells break
  the frame property (R5e); the read-only-sharing heap is not cancellative (R5f) and its
  separating conjunction does not imply address disjointness at permission `ro`.
* **Frame rule.** The frame rule is equivalent to locality in every separation structure (R5a);
  byte and typed commands are local for every representation, and reads see the same bytes in
  every disjoint extension (R5b); a typed copy that reads bytes it does not own (as `uninit`) is
  local whenever the decoder is monotone (R5c) — a fact about this permissive semantics, not a
  license to drop padding from typed-load footprints in Rust — can fail to be local for a
  non-monotone decoder (its tightness witness), and the byte-level analogue is not local (R5d).

These recommendations are derived from the results above (`Basis: derived`), not proved as impossibilities for the alternatives.

## Boundaries

### Non-claims (per result)

Read these before relying on any result. They are known not to follow from the statements, or were not examined.

**R1a** (`R1a-encode-based-entails-decode-based-iff-decodeEncode`):

1. Says nothing about the converse entailment (decode-based => encode-based); see R1b and R1c.
2. R1a is the special case rA = rB = r, b = v (quantified over all v) of R3a; it is kept as a separate card only as the single-type reference point.
3. The left-hand side quantifies over all permissions, addresses, values and heaps; failure of DecodeEncode at one value v only shows the entailment fails at that v (Toy.ByteSL.ptsEnc_entails_ptsDec_fails_noneRep), not at every v.
4. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R1b** (`R1b-decode-based-equals-byte-upward-closure-iff-three-laws`):

1. byteUpClose is upward closure in the byte-definedness order with a fixed domain: it keeps addresses and permissions and only turns uninit bytes into initialized ones (it does not change initialized bytes, add or remove cells, or change permissions). It is not the upward closure under heap extension (P * True) of intuitionistic separation logic (Reynolds 2002), which is the sense of 'upward closed' in the cited Aeneas prototype's PCM.lean; no result here is about that closure.
2. Not a statement about any program step: it does not claim that real memory ever spontaneously becomes more defined; it characterizes which heaps the decode-based assertion admits.
3. Each law is independently needed: Toy.ByteSL.ptsDec_eq_byteUpClose_fails_exactUnitRep, Toy.ByteSL.ptsDec_eq_byteUpClose_fails_noneRep and Toy.ByteSL.ptsDec_eq_byteUpClose_fails_boolNZRep each satisfy the other two laws and violate the coincidence. Finer directional facts (for a fixed r, the inclusion of the decode-based points-to in the closure follows from EncodeLeast alone, and the reverse inclusion from DecodeMono and DecodeEncode) are not stated as separate theorems.
4. With a non-flat value order (e.g. pointers with and without provenance) DecodeMono is a different law; not examined.
5. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R1c** (`R1c-two-typed-points-to-coincide-iff-intoBytes`):

1. IntoBytes here is the semantic predicate of the published representation package (no encoding contains uninit), not zerocopy's IntoBytes trait; for provenance-carrying bytes the two differ (see that package).
2. For types that are not IntoBytes the result says only that the two assertions differ somewhere; R1b says exactly how (byte-definedness upward closure) and R1d gives a concrete heap.
3. Does not say which of the two definitions a verifier should adopt; the recommendation in the summary of this package rests on R1b, R2 and R3 together, not on R1c alone.
4. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R1d** (`R1d-initialized-padding-separates-the-two-definitions`):

1. Does not show that the encode-based points-to is unsound or useless: it remains exactly the postcondition of a typed store, which writes uninit padding. It shows only that once the padding byte is initialized (by whatever means) the two assertions disagree; how real Rust operations initialize padding bytes is not modeled.
2. R1b gives the general relationship (the block here is in the byte-definedness upward closure of the encoding) and R1c the exact condition (IntoBytes) under which no such heap exists.
3. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R2a** (`R2a-decode-based-struct-split-with-padding-any`):

1. Only two-field layouts with field 1 at offset 0 and both fields within the struct are covered; offsets are given, not computed by a layout algorithm, and alignment is not modeled. More fields, nested structs, enums, unions (overlapping fields, excluded by NonOverlap) and layouts with leading padding are not examined.
2. The struct representation is structRep, which decodes each field from its own range and never reads padding (MiniRust's struct representation); a representation whose decoder reads padding is not covered.
3. The struct assertion and the three pieces all carry the same permission p; splitting into pieces with different permissions (e.g. one field read-only, the other full) is not stated.
4. With permission ro the separating conjunction allows overlapping read-only pieces; the equivalence still holds because the three footprints are disjoint, but nothing is claimed about splitting a struct into overlapping read-only views.
5. Does not say that padding ownership may be dropped: the right-hand side owns the padding cells, and a struct points-to cannot be reassembled without them.
6. NonOverlap is tight only through permission full (Toy.ByteSL.ptsDec_struct_split_tight_hL uses full); whether the equivalence holds for overlapping layouts at permission ro is not stated.
7. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R2b** (`R2b-encode-based-struct-split-with-padding-uninit`):

1. Only two-field layouts with field 1 at offset 0 and both fields within the struct are covered; offsets are given, not computed by a layout algorithm, and alignment is not modeled. More fields, nested structs, enums, unions (overlapping fields, excluded by NonOverlap) and layouts with leading padding are not examined.
2. The struct representation is structRep, whose encoder writes uninit padding; a struct encoder that writes initialized padding (e.g. zero padding, as u8PadInitRep in the published representation package) is not covered, and for it the padding piece would not be padUninit.
3. The struct assertion and the three pieces all carry the same permission p; splitting into pieces with different permissions (e.g. one field read-only, the other full) is not stated.
4. With permission ro the separating conjunction allows overlapping read-only pieces; the equivalence still holds because the three footprints are disjoint, but nothing is claimed about splitting a struct into overlapping read-only views.
5. Does not say that padding ownership may be dropped: the right-hand side owns the padding cells, and a struct points-to cannot be reassembled without them.
6. Both pairings (decode-based with arbitrary padding, R2a; encode-based with uninit padding, R2b) are exact laws in this model; R2c shows only that the mixed pairings fail. The preference for the decode-based pairing rests on robustness (R1b, R1d, R3) and is argued in prose, not proved as an impossibility.
7. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R2c** (`R2c-mixed-struct-padding-pairings-fail`):

1. The other directions of the mixed pairings (split for encode-based fields with arbitrary padding, join for decode-based fields with uninit padding) are not stated here.
2. Shown for one layout, one pair of field representations and one heap; it is a refutation of the general laws, not a classification of when mixed pairings work.
3. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3a** (`R3a-encode-based-source-view-change-iff-transmute`):

1. The target is decode-based; an entailment into the encode-based points-to of B additionally requires the two encodings to be the same bytes, which is not stated here.
2. Totality (a b for every v) is a separate question; see R3f.
3. R1a is the special case rA = rB, b = v of this card.
4. At permission full the entailment is a consuming, one-way view change: afterwards only the B view is asserted. It does not justify temporarily reborrowing &mut A as &mut B, which must leave a valid A behind after arbitrary writes through the B view and so needs conditions in both directions (zerocopy 0.8.63's transmute_mut! requires both types to be FromBytes and IntoBytes); the reverse view change fails in general (R3d, R3e).
5. In-place reinterpretation in Rust additionally requires the address to be aligned for B (zerocopy's transmute_ref! and transmute_mut! require align_of::<Src>() >= align_of::<Dst>()) and, for shared references &A to &B, the absence of interior mutability (zerocopy's Immutable bound on both types). Neither alignment nor interior mutability is modeled; by-value transmute (which copies the bytes) is a different operation.
6. Only representations of equal size at the same address are covered; transmutes between different sizes, reference casts beyond the two points above, and pointer-integer casts with provenance are not examined.
7. MiniRust's transmute also runs check_value on the result; machine-state-dependent validity is not modeled.
8. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3b** (`R3b-decode-based-source-view-change-iff-transmute-under-laws`):

1. The witness b is the transmute result; nothing is claimed about the transmute being injective, invertible, or value-preserving in any semantic sense.
2. Statement is per value v. Under R3b's laws its all-values form is immediate (not separately stated): TransmuteTotal rA rB holds iff for every v there is a b with the decode-based points-to of v at A entailing that of b at B. R3c and R3f are different results: one-way sufficient conditions (IntoBytes and EncodeLeast of A, plus FromBytes of B for R3f) that assume nothing about B's laws, whereas R3b is an exact condition that assumes DecodeMono of B and also covers padded or niche-carrying sources and targets.
3. At permission full the entailment is a consuming, one-way view change: afterwards only the B view is asserted. It does not justify temporarily reborrowing &mut A as &mut B, which must leave a valid A behind after arbitrary writes through the B view and so needs conditions in both directions (zerocopy 0.8.63's transmute_mut! requires both types to be FromBytes and IntoBytes); the reverse view change fails in general (R3d, R3e).
4. In-place reinterpretation in Rust additionally requires the address to be aligned for B (zerocopy's transmute_ref! and transmute_mut! require align_of::<Src>() >= align_of::<Dst>()) and, for shared references &A to &B, the absence of interior mutability (zerocopy's Immutable bound on both types). Neither alignment nor interior mutability is modeled; by-value transmute (which copies the bytes) is a different operation.
5. Only representations of equal size at the same address are covered; transmutes between different sizes, reference casts beyond the two points above, and pointer-integer casts with provenance are not examined.
6. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3c** (`R3c-view-change-from-intoBytes-encodeLeast-source-to-any-target`):

1. IntoBytes and EncodeLeast of A are sufficient, not necessary: R3b gives the exact per-value condition under other laws, and padded or niche-carrying sources can still have view changes.
2. DecodeEncode of A is not assumed, so for a source whose decoder accepts nothing (e.g. noneRep with the u8 encoder) all hypotheses hold and the entailment is vacuous (Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep); the non-vacuity witness uses a lawful source.
3. Existence of b for every v is R3f (it needs FromBytes of B or another totality argument).
4. At permission full the entailment is a consuming, one-way view change: afterwards only the B view is asserted. It does not justify temporarily reborrowing &mut A as &mut B, which must leave a valid A behind after arbitrary writes through the B view and so needs conditions in both directions (zerocopy 0.8.63's transmute_mut! requires both types to be FromBytes and IntoBytes); the reverse view change fails in general (R3d, R3e).
5. In-place reinterpretation in Rust additionally requires the address to be aligned for B (zerocopy's transmute_ref! and transmute_mut! require align_of::<Src>() >= align_of::<Dst>()) and, for shared references &A to &B, the absence of interior mutability (zerocopy's Immutable bound on both types). Neither alignment nor interior mutability is modeled; by-value transmute (which copies the bytes) is a different operation.
6. IntoBytes and FromBytes are the semantic predicates of the published representation package, not zerocopy's traits (see that package for the divergences, e.g. provenance).
7. Only representations of equal size at the same address are covered; transmutes between different sizes, reference casts beyond the two points above, and pointer-integer casts with provenance are not examined.
8. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3f** (`R3f-total-view-change-from-intoBytes-encodeLeast-to-fromBytes`):

1. IntoBytes and FromBytes are sufficient, not necessary: R3b gives the exact per-value condition under the other laws (and its all-values form under those laws), and padded or niche-carrying types can still have total transmutes and view changes.
2. DecodeEncode of A is not assumed, so for a source whose decoder accepts nothing (e.g. noneRep with the u8 encoder, with target u8Rep, which is FromBytes) all hypotheses hold, transmute is total, and the entailment is vacuous for every v because the source decode-based points-to holds for no heap (Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep); the non-vacuity witness uses a lawful source.
3. The reverse direction (B back to A) is a separate question; it needs the conditions with roles swapped, and R3d, R3e show it fails for the niche and padding examples.
4. At permission full the entailment is a consuming, one-way view change: afterwards only the B view is asserted. It does not justify temporarily reborrowing &mut A as &mut B, which must leave a valid A behind after arbitrary writes through the B view and so needs conditions in both directions (zerocopy 0.8.63's transmute_mut! requires both types to be FromBytes and IntoBytes); the reverse view change fails in general (R3d, R3e).
5. In-place reinterpretation in Rust additionally requires the address to be aligned for B (zerocopy's transmute_ref! and transmute_mut! require align_of::<Src>() >= align_of::<Dst>()) and, for shared references &A to &B, the absence of interior mutability (zerocopy's Immutable bound on both types). Neither alignment nor interior mutability is modeled; by-value transmute (which copies the bytes) is a different operation.
6. IntoBytes and FromBytes are the semantic predicates of the published representation package, not zerocopy's traits (see that package for the divergences, e.g. provenance).
7. Only representations of equal size at the same address are covered; transmutes between different sizes, reference casts beyond the two points above, and pointer-integer casts with provenance are not examined.
8. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3d** (`R3d-niche-view-change-is-one-directional`):

1. boolRep uses only the bytes 0 and 1; Rust's bool has the same validity, but other niche-carrying types (references, NonZero integers, enums) are not examined.
2. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R3e** (`R3e-padding-view-change-is-one-directional`):

1. When the padding byte happens to be initialized (e.g. [init 5, init 9]) the reverse reinterpretation does decode, to a value that depends on the padding byte; the counterexample shows only that the entailment fails for the heap with uninit padding, because the decode-based struct assertion does not constrain the padding byte.
2. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R4a** (`R4a-read-only-views-coexist-iff-common-bytes`):

1. Interior mutability is not modeled: a read-only cell here can never be written (R5e shows a write through it breaks the frame property). In Rust, &T for a type containing UnsafeCell permits mutation through shared references (RustBelt models this with a type-specific sharing predicate), so coexisting shared typed views of such bytes need not be stable; nothing here applies to them.
2. Only two views of the same size at the same address are covered; overlapping views of different sizes or offsets are not examined.
3. Says nothing about how read-only views are obtained from full ownership (no 'share' or freeze step is modeled) or whether full ownership can be recovered (it cannot in this permission algebra).
4. Idempotent read-only sharing violates the disjointness axiom of Dockins, Hobor and Appel (2009): a separating conjunction of read-only assertions does not imply that their footprints are disjoint (two read-only views of the same cells separate, R4a). Inductive predicates built with * at permission ro (lists, trees) therefore admit sharing and cycles (DAGs instead of trees); nothing here supports reading ro-separation as address disjointness.
5. Permissions are the two-point permission algebra full | read-only (read-only cells combine idempotently with equal cells, full cells with nothing); there are no fractions, so nothing here addresses splitting full ownership into read-only pieces or recombining them.
6. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R4b** (`R4b-full-permission-view-excludes-any-second-view`):

1. An impossibility for the separating conjunction only: an ordinary conjunction of a full view with another typed view of the same bytes is satisfiable whenever the bytes decode under both.
2. Escape hatches: drop either hypothesis (size 0, or read-only on both sides) and the views coexist.
3. Says nothing about time: holding full permission now does not rule out later lending the bytes out as two shared views (e.g. via fractional permissions or a lifetime logic) and recovering full permission when the loan ends; no such protocol is modeled.
4. Only equal-size views at the same address are stated; views of different sizes or at overlapping offsets are not covered by the statement.
5. Interior mutability is not modeled: a read-only cell here can never be written (R5e shows a write through it breaks the frame property). In Rust, &T for a type containing UnsafeCell permits mutation through shared references (RustBelt models this with a type-specific sharing predicate), so coexisting shared typed views of such bytes need not be stable; nothing here applies to them.
6. Permissions are the two-point permission algebra full | read-only (read-only cells combine idempotently with equal cells, full cells with nothing); there are no fractions, so nothing here addresses splitting full ownership into read-only pieces or recombining them.
7. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5a** (`R5a-frame-rule-iff-locality-in-every-separation-structure`):

1. Uses no property of the separation structure: it holds for every SepStruct, including lawless ones. So it says nothing about which compositional rules survive non-cancellative read-only sharing; rules that depend on cancellativity or precision (the conjunction rule, reasoning with precise assertions) are not examined.
2. Single commands only: no sequencing, choice or loops, so locality of compound commands is not examined.
3. No variable store: the Hoare-logic side condition of the frame rule (the command modifies no variable free in the frame) is absent only for that reason; nothing here addresses frame rules with stores.
4. Partial correctness with fault avoidance only; nothing about termination.
5. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5b** (`R5b-byte-and-typed-commands-are-local`):

1. Reads require ownership (any permission) of every byte read, padding included; a typed copy whose footprint omits bytes it reads is the loose variant of R5c, which needs DecodeMono.
2. Writes require full permission; a write through a read-only cell is not local (R5e).
3. Commands have no variable store: a loaded value is observable only by writing its encoding into the heap (tcopy) or not at all (tload); tcopy observes the decoded value v only through r.encode v, which need not determine v because no DecodeEncode is assumed.
4. No allocation or deallocation commands; no concurrency.
5. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5c** (`R5c-loose-typed-copy-is-local-under-decodeMono`):

1. Not a license for a verifier to omit padding (or any other bytes a load reads) from a typed load's footprint in general. The result holds for an operational semantics in which reading memory one does not own neither faults nor has any other effect. In Rust and MiniRust a typed load requires the whole range to be dereferenceable, and in a concurrent or aliasing-aware semantics reading bytes that another party holds exclusively is undefined behavior or a data race; Toy.ByteSL.tcopyLoose_reads_frame_owned_full_cell shows the loose copy reading a byte that the frame holds with full permission. Omitting padding from a footprint is safe only where the operation does not read it at all (e.g. field-by-field copies).
2. Locality is not preservation of typed points-to: which assertion holds at the destination afterwards is not stated.
3. No variable store: the loaded value is observable only through r.encode v written at the destination, which need not determine v (DecodeEncode is not assumed).
4. The byte-level analogue is not local (R5d): copying the raw bytes exposes what a monotone decoder hides.
5. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5d** (`R5d-loose-byte-copy-is-not-local`):

1. Shows failure for one command at one pair of addresses; does not classify all non-local commands.
2. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5e** (`R5e-store-through-read-only-cell-is-not-local`):

1. Interior mutability is not modeled: a read-only cell here can never be written (R5e shows a write through it breaks the frame property). In Rust, &T for a type containing UnsafeCell permits mutation through shared references (RustBelt models this with a type-specific sharing predicate), so coexisting shared typed views of such bytes need not be stable; nothing here applies to them.
2. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

**R5f** (`R5f-byte-heap-with-read-only-sharing-is-not-cancellative`):

1. Does not affect R5a, which needs no algebraic law; results that depend on cancellativity (for example relating precision to the conjunction rule) do not transfer to this heap without further argument.
2. Idempotent read-only sharing violates the disjointness axiom of Dockins, Hobor and Appel (2009): a separating conjunction of read-only assertions does not imply that their footprints are disjoint (two read-only views of the same cells separate, R4a). Inductive predicates built with * at permission ro (lists, trees) therefore admit sharing and cycles (DAGs instead of trees); nothing here supports reading ro-separation as address disjointness.
3. Permissions are the two-point permission algebra full | read-only (read-only cells combine idempotently with equal cells, full cells with nothing); there are no fractions, so nothing here addresses splitting full ownership into read-only pieces or recombining them.
4. Toy model: one flat byte heap with natural-number addresses, no allocation, no alignment, no provenance in the examples, no lifetimes or borrows, no concurrency; a representation's decoder depends on the bytes only.

### Escape hatches of the impossibility result

R4b (`not_sep_ptsDec_of_full_of_pos_size`) is the only impossibility result. Each of its
hypotheses is an escape hatch, with a proved counterexample in which the other hypothesis holds and
the conclusion fails:

* drop `hn : 0 < n` — two zero-size views of `()` at the size-0 representation `zeroUnitRep`, both
  at permission `full`, are jointly satisfiable (`Toy.ByteSL.not_sep_ptsDec_tight_hn`);
* drop `hpq : p = full ∨ q = full` — at permission `ro` on both sides, the `u8Rep` view of `1` and
  the `boolRep` view of `true` at address 0 are jointly satisfiable, since the byte `1` decodes under
  both (`Toy.ByteSL.not_sep_ptsDec_tight_hpq`).

Further ways around it that the statement does not exclude: views at different addresses or with
different sizes (not covered by the statement), the ordinary conjunction instead of the separating
conjunction, and protocols over time (lending full permission out as read-only views and getting
it back), none of which is modeled. Positive control: `Toy.ByteSL.not_sep_ptsDec_positive_control`
(the read-only `u8Rep` view of `1` and the read-only `boolRep` view of `true` at address 0 are
jointly satisfiable).

### Hypotheses with `unknown` tightness

None. Every hypothesis in `results.json` is labeled `tight` (with a proved counterexample) or
`harmless` (the in-bounds fields `fits₁`, `fits` of the structure `Layout2`, which are part of the
data of a layout rather than hypotheses of R2a and R2b, and which every layout of a real struct
satisfies).

### Disproved or dropped statements

None. Every statement of this package was proved as stated; no statement was found false, and none
was dropped or weakened.

### Not examined

* Alignment, interior mutability (`UnsafeCell`), provenance-carrying bytes, pointer-integer casts.
* Fractional or counting permissions, recombining read-only permissions into a full one, temporary
  borrows, lifetimes, and reborrowing `&mut A` as `&mut B`.
* Structs with more than two fields, nested structs, enums, unions, layouts computed by a layout
  algorithm, and leading padding.
* Transmutes between types of different sizes and reinterpretation at overlapping but unequal
  addresses.
* Allocation and deallocation commands, a variable store, and concurrency.
* Whether any real Rust type's representation satisfies the laws used as hypotheses.

## Evidence

### Kernel-check records

Toolchain `leanprover/lean4:v4.34.1`; checked on 2026-11-20. `Axioms` is the output of `collectAxioms` (`#print axioms`); `statement` is the SHA-256 of `repr` of the declaration's type; `closure` is the SHA-256 of its definition closure as described under **Revalidation**. The same data is in `audit/statements.json` and `audit/axioms.json`; across all 692 declarations of the library, no axiom outside `propext`, `Classical.choice`, `Quot.sound` occurs.

| Theorem | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode` | R1a result | Classical.choice, Quot.sound, propext | `3315af0b814b600fcdfffce14f769062ee33c98de72bc80d6d34843332895331` | `ccfb494cb7735c6beeffa35d50f325832d45dd6b333c9eec0c262aa58047ee35` (25) |
| `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_decodeEncode_nonvacuous` | R1a non-vacuity | Quot.sound, propext | `b95742750772564d2930dae531e1d4fbc4d9fe7f1986219a54f231ec5c7753fe` | `e8790e5fc1087e72e31085a6142d3a6494d5fe72278c9a05b0839d20c3a0c441` (32) |
| `Toy.ByteSL.ptsDec_eq_byteUpClose_ptsEnc_iff_decodeMono_decodeEncode_encodeLeast` | R1b result | Classical.choice, Quot.sound, propext | `8548901ce993f48018585ae43082723a552dc68b970a4ec095aaec2b8183e3f1` | `4764a9b128030d32411b0030607452f4139e87fa2d9838873aacb14548ba01c7` (44) |
| `Toy.ByteSL.ptsDec_eq_byteUpClose_nonvacuous` | R1b non-vacuity | Classical.choice, Quot.sound, propext | `a3ae9374bc011ccac43d52f71294591f1668574a2faee45f4d248f6e31c1d830` | `c20ae8e937448e52196cc2bf56bdf0149d061f381557150b8e4eac1344debff0` (50) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_of_decodeMono_decodeEncode_encodeLeast_nonempty` | R1c result | Classical.choice, Quot.sound, propext | `1c7900723aa8cac154d86629f5b419fdade21753c9cf2e78de306cfe5924979d` | `a4b0ed23ca669c83ef9e5d795ba21216e9798e201ac1c4340f90ed7b306d6738` (43) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_nonvacuous` | R1c non-vacuity | Quot.sound, propext | `ce06d61ae40b16ae6da4e4fa003cebf06fd13729497bb522b06aabc3a7d3faea` | `e21a80e0d06569dcb35bc7baf9ae3c804c3b4e6e1046da4b3c274a5d37599245` (37) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hM` | R1c counterexample for `hM` | Quot.sound, propext | `d7af7cc91e67f388a8fc73e6a580c8d78113eeb5e10fb1e4455663ebf29533c7` | `fff58119d1d5b5c2a75782898a4a2301b957b8ee5b6e92a0d579bfd054c913de` (44) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hDE` | R1c counterexample for `hDE` | Quot.sound, propext | `c22d0457b821f23d04c51b7b84738aa65943a941ff6e4e0e818d8caec20a1e40` | `42c1042f4016b1c43965e76753d835e0d498a9d7fd202bc95c1aadd393844201` (49) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hEL` | R1c counterexample for `hEL` | Classical.choice, Quot.sound, propext | `5afdeebd7e6ecefe9d9c03b376be4004571254c518643ab1c936dbfa6d4bf3fd` | `8b2333ec5854603a97fc9dab3c80a804ca28d1c1930f91eed16b988db8c58027` (49) |
| `Toy.ByteSL.ptsDec_iff_ptsEnc_iff_intoBytes_tight_hD` | R1c counterexample for `hD` | Quot.sound, propext | `b76cdbaf32abfae31927a0028d061af06dc414deaab5728945a62c7917eeaca2` | `98d48c7126ff57623f3e97d5398607604f80c0b7a152bde3057e8a2c1d85cee5` (45) |
| `Toy.ByteSL.u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding` | R1d result; R1d non-vacuity | Classical.choice, Quot.sound, propext | `a854a63497cf5bf702eb4491fbd21bfa979136857e247e20b157a8f515c626ec` | `10bd34453202f4e8e472b18b8cad019dac83f03f827a486d2394bac92a0bc694` (45) |
| `Toy.ByteSL.u8PadRep_uninit_padding_ptsDec_and_ptsEnc` | R1d result | Quot.sound, propext | `a436882c64b3957d06f924fd5f72da040d2db5646af30a249f1501764f2a0dae` | `e359dfb033b771ff68e4b778bcbe8aa70fbbf7cf17ecd0a2cc82576cf2b35e47` (32) |
| `Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_of_nonOverlap` | R2a result | Classical.choice, Quot.sound, propext | `188849b7a0b950641ed1d5661d3d7e409b315508586050f67c95032126bb3f7e` | `e012740426728a4b75e47f1121529fdc4adbf14e234cb8bd1d05b0dc80f5a510` (53) |
| `Toy.ByteSL.ptsDec_struct_iff_sep_fields_padAny_nonvacuous` | R2a non-vacuity | Quot.sound, propext | `7a788348a84e40cc0f5d2017eaf1cce7d79d051c4bb632c2169c88a9a8d96325` | `71dc7e480696de68d7be52d513592e399208715c6f85f7e1466b549b279c0d48` (74) |
| `Toy.ByteSL.ptsDec_struct_split_tight_hL` | R2a counterexample for `hL` | Classical.choice, Quot.sound, propext | `ce85976a72f28e2c121c3d4ce62cb6448b08fbe32f54b469e48ed1d806fd44df` | `b1f5674bca6939d8e97afcd2bc0c654cc08b593c3c5a28ed20a39f20491ebd77` (64) |
| `Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_of_nonOverlap` | R2b result | Classical.choice, Quot.sound, propext | `f69aae08a069b8d176a276eeb1e6ca25ed814d5aee48fa998145c45ec0c67443` | `bf8059bee4f4c192b46aefee9b216fb7c83c730ff07d6d0027e437db9136baa3` (54) |
| `Toy.ByteSL.ptsEnc_struct_iff_sep_fields_padUninit_nonvacuous` | R2b non-vacuity | Quot.sound, propext | `88d98cab25af8dcb0322d85ab1ed92c1ceec5b8979fb033d99c542039065eb51` | `a0e4a41cf900bec64fb166a43b6b232f5037563a3458ac2a167e702cbc379a13` (75) |
| `Toy.ByteSL.ptsEnc_struct_split_tight_hL` | R2b counterexample for `hL` | Classical.choice, Quot.sound, propext | `59afb26c33ff55a1b26e341f580df0973de3a6c511520645bbcd7ffc6efa0ec9` | `80df2c8a4df466445990e33e41ebe2f3606af82d7276ec2d1c75b3455a7c1932` (65) |
| `Toy.ByteSL.ptsEnc_struct_join_padAny_fails` | R2c result; R2c non-vacuity | Classical.choice, Quot.sound, propext | `b749467238a9442f474f281834c5b086fd7499e372fe5c21ab8a178196847800` | `5b9a9b588e890002e4e507af518897a709a107c4e3d96ee2e8e20b53ef8d3577` (73) |
| `Toy.ByteSL.ptsDec_struct_split_padUninit_fails` | R2c result | Quot.sound, propext | `d55f3cfa6c1d07be9b9584dae8a2e075fb5ea790ef5969097eb08a3a461433fa` | `f6ae2c35bee0be97ed2e1b9598bf52f361755f3dd02918adb47d17eb9b20ceb6` (74) |
| `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some` | R3a result | Classical.choice, Quot.sound, propext | `41b6f6cf66f4b7b5b35cc9b69b35257be40d17bf39b539d0bf1a35c2649057e4` | `e06efbff9e99c493a7e597234294d0863318196005398a22b6a9ec7c7caa6c82` (25) |
| `Toy.ByteSL.ptsEnc_entails_ptsDec_iff_transmute_eq_some_nonvacuous` | R3a non-vacuity | Quot.sound, propext | `21230689efde350a9977f01560abea57ea42827382112c628038a47eb3da866e` | `17a486028cb4caca6a0d99bb869ee728e2fb00e399edca17c8a125867c1c630d` (35) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_of_decodeEncode_encodeLeast_decodeMono` | R3b result | Classical.choice, Quot.sound, propext | `1359da5b6daeaf3d00d3c763472066babaee2644b3f7bb5c0529a52f49f5ec53` | `cc0902f85e4c6b4d5b8c2af84862f6af18c6ec1285f58167bdbe41968e3c75bb` (39) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_iff_transmute_eq_some_nonvacuous` | R3b non-vacuity | Quot.sound, propext | `32699c16310ac5875ddacd37f78b22986d4852094d241b0cc1d4bb795ee266e3` | `38b356b4fa25a16b0c5a402dffc4486128399514ac141302dd43495bbbb692ad` (36) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hDE_A` | R3b counterexample for `hDE_A` | Quot.sound, propext | `9374470c32b9779872ea1ce5aefc06eac34c15c20b87a1c5a0964e2676fbb4ba` | `1fc13493a113f478606c1042bd97756074c5b402c71a6733a788ee83e6c2642b` (45) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hEL_A` | R3b counterexample for `hEL_A` | Classical.choice, Quot.sound, propext | `b4b2276b544ed6bc0e5480614497257e4fd11c91759a70f86ae4089a632ad16b` | `2e1eb0d748e7451492819f1f27577720c36c0c14a20d2927079b3c678ec08f8b` (47) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_tight_hM_B` | R3b counterexample for `hM_B` | Classical.choice, Quot.sound, propext | `cc0ba29a21a62e1b519167f2acadd31e6e80103500ee4e5121c530299cfcc8c0` | `78a64ff7be41ea9654809316573cbb0f1ebf3e9d13affb582b339095db6f29d5` (41) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_of_intoBytes_encodeLeast` | R3c result | Quot.sound, propext | `3be70e48deba18a86e5a1d1b1ba45f6ec6cc8380e0405fb98f6feaa9251ff278` | `69f9a72ce7d687f9abeac3fbdf3a38bee8ae80d4dd44c7662b6868d4ea791b34` (38) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_eq_some_nonvacuous` | R3c non-vacuity | Quot.sound, propext | `e4202be65dd616c57d91acbd4b33c0de062a16cc970bd59927d5a1fd3ec9176a` | `59c6428a533af1fe42a86ab127024decfacea2bd1d77f29ab59af3aa22184e8e` (56) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hIB_A` | R3c counterexample for `hIB_A` | Classical.choice, Quot.sound, propext | `637b57c5afc32898d3dc3fcc5ca0285a01ef202d06f03ec1d36c4e151428c921` | `e1d7ac18589d4bb90359712f576b0d2471b56b0f5f5e601794be2e6226d5fca7` (46) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_hEL_A` | R3c counterexample for `hEL_A` | Classical.choice, Quot.sound, propext | `8ad98e050a08bdb11b54317de93abdd3ec3a86eb5d803c6f5e6de1c1fe817e6a` | `4ab7857d6a27303e7b2144bdc78ae0c501e201106513400128aa3c33fe26e89b` (46) |
| `Toy.ByteSL.ptsDec_entails_ptsDec_of_transmute_tight_ht` | R3c counterexample for `ht` | Classical.choice, Quot.sound, propext | `e5520bedbaa3befa1b46a87c654dd17d11b2dfbb3c920809b2a624d4811d211e` | `69260cd3ad7c09940d6add00ed7e2d550534e799cb0222dff09bc4b4f2bcbd52` (44) |
| `Toy.ByteSL.exists_ptsDec_viewChange_of_intoBytes_encodeLeast_fromBytes` | R3f result | Quot.sound, propext | `3cf175292b719d5ee87e6378222080781de20f5ee7b13442c35cc73c44da7596` | `9c4040092bd45a36655719b31c095b5ac70db9620cb55d4e41bea28d803b7546` (39) |
| `Toy.ByteSL.exists_ptsDec_viewChange_nonvacuous` | R3f non-vacuity | Quot.sound, propext | `8d0fefcabc937863437301b4812579a2eb9f84f864501b2b66bd72ef4cd506a1` | `5dc740cae75cbf12e42b8d201c3bad66357bee73684fcd96d0ae38ac7007aa5b` (64) |
| `Toy.ByteSL.exists_ptsDec_viewChange_tight_hIB_A` | R3f counterexample for `hIB_A` | Quot.sound, propext | `e0944876f05f9a1333ec022d1b90d2fa1987e1a3a3dd96e04270c138bb7466ac` | `5e4f9e149bf34d2900acf6797ebb7f83a6099e2c7d434170a88a2513ff986988` (51) |
| `Toy.ByteSL.exists_ptsDec_viewChange_tight_hEL_A` | R3f counterexample for `hEL_A` | Classical.choice, Quot.sound, propext | `a518b4ca83a8cecae7fc976e843ccbf1d550f2a89d471b4306aad8608f0e0fba` | `e001fdabcf20ce45c18b65d4f04b356ea8cb17f568d0096b5b3516a6fb6aca5a` (47) |
| `Toy.ByteSL.exists_ptsDec_viewChange_tight_hFB_B` | R3f counterexample for `hFB_B` | Quot.sound, propext | `02114534a5b58468098e2e52f0deb017eae3ca0feff26f117b5fbab780bdd923` | `cb6b4eaa87072afc501a2f4a7c7135196efd12bd365c1a19b8880a4edf48f2cc` (48) |
| `Toy.ByteSL.niche_viewChange_one_directional` | R3d result; R3d non-vacuity | Classical.choice, Quot.sound, propext | `1e3b7c6d65300069c4c591cbe2435bd90b5f8f69988110c08ee87cace142fd21` | `dceee1df9fdf9fa1bb1edd519b442a0811f583833eac0c09f73ed1aef14a6405` (33) |
| `Toy.ByteSL.padding_viewChange_one_directional` | R3e result; R3e non-vacuity | Classical.choice, Quot.sound, propext | `387daf548c285e02b0ce7dcb7e6f6c0e4473a140bfd9ffa0dd67ae6c929fbb01` | `dc85e982a2d1021d927587c8f279c89f54fda8536b68727202546e03e4fd0276` (36) |
| `Toy.ByteSL.sep_ro_ptsDec_iff_block_decodes` | R4a result | Classical.choice, Quot.sound, propext | `808d686649655d8481d3d81f114874d45782f3916c6ed1693f7b8e224ee9b6f9` | `4ba92f89ac0729c2eeaa69fc29c140e5a05a7607ba3242713511c3dc013aac8f` (33) |
| `Toy.ByteSL.sep_ro_ptsDec_satisfiable_iff_common_bytes` | R4a result | Classical.choice, Quot.sound, propext | `af6095b324ab4b99c67cc354167dd6e7d8bdc294075d7b95ac9111e9e34508b0` | `4ba92f89ac0729c2eeaa69fc29c140e5a05a7607ba3242713511c3dc013aac8f` (33) |
| `Toy.ByteSL.sep_ro_ptsEnc_satisfiable_iff_encode_eq` | R4a result | Classical.choice, Quot.sound, propext | `0c7e888085c03a10c55c4942d5b39025c463cde92331fbf900cee62458dc9d22` | `eb628c171ff49f28d79636fe902bdfc658bfd1c0470ecebacc98a50465093058` (33) |
| `Toy.ByteSL.sep_ro_ptsDec_nonvacuous` | R4a non-vacuity | Classical.choice, Quot.sound, propext | `e71a36e2796c53f472c3d1eeeb170d7ee2d0a78320a34854acb2503a674e2d81` | `8073306a07a9f3c0f7db20a9f6e8209277ee76b4b6fced4fdd46a0e6081d023c` (44) |
| `Toy.ByteSL.not_sep_ptsDec_of_full_of_pos_size` | R4b result | Classical.choice, Quot.sound, propext | `3a882e27eb93343fb1a4499be19db15e1a4935bbbd4da1277c5c2a9c0d58969b` | `4ba92f89ac0729c2eeaa69fc29c140e5a05a7607ba3242713511c3dc013aac8f` (33) |
| `Toy.ByteSL.not_sep_ptsDec_nonvacuous` | R4b non-vacuity | Quot.sound, propext | `5d04dfa9ba942928ce217335bc175abbb29669698db91bcd11a97c520e7975b9` | `dceee1df9fdf9fa1bb1edd519b442a0811f583833eac0c09f73ed1aef14a6405` (33) |
| `Toy.ByteSL.not_sep_ptsDec_positive_control` | R4b positive control | Classical.choice, Quot.sound, propext | `bad74604503906d643ed3253bb6d8310ef4fc6668fcf97c0af35faa92e9e3806` | `8073306a07a9f3c0f7db20a9f6e8209277ee76b4b6fced4fdd46a0e6081d023c` (44) |
| `Toy.ByteSL.not_sep_ptsDec_tight_hn` | R4b counterexample for `hn` | Quot.sound, propext | `58568502f3b115479a875913711740a09e06fbef00a4044aeaeb86885c052a62` | `b4ddcdf121f94be8ab6d9b5115cbcca0bb2c0aa7a6bc0ff4b9b13d1de564fd2d` (36) |
| `Toy.ByteSL.not_sep_ptsDec_tight_hpq` | R4b counterexample for `hpq` | Classical.choice, Quot.sound, propext | `aeda649eee5afeafd614ba257043e0913125902abff9b8b75074c8b3ee14669b` | `8073306a07a9f3c0f7db20a9f6e8209277ee76b4b6fced4fdd46a0e6081d023c` (44) |
| `Toy.ByteSL.frameRuleSound_iff_safetyMono_and_frameProp` | R5a result | none | `e35700a65dd7f967d3b2dec6619706fcb9c59419b26dfda8f01e3dd71ffad06e` | `55e4ddf5151192cd246f323f3cb72bf4cc2218ab952dee9d8c9f0237e2e0a55b` (15) |
| `Toy.ByteSL.byteHeap_frameRule_nonvacuous` | R5a non-vacuity | Quot.sound, propext | `2e3c9ae848cfcf7d1c42c6b403bba04b89b78633ed99b51075d32a519c68c602` | `62891522610465f7715f2b637d49ab95eb67855da6948c76766e997466bbca12` (32) |
| `Toy.ByteSL.byte_commands_local` | R5b result | Classical.choice, Quot.sound, propext | `27c8946e2574b0f55a52cac771064ad1b16afe4851a3fb2738d02d762ef59f88` | `052b01858ecba5dc5d9c064d3a29db6d8a1c740b5b03d8d6a2a9d43543c2c715` (40) |
| `Toy.ByteSL.typed_commands_local` | R5b result | Classical.choice, Quot.sound, propext | `dcb21d2b19a6a5a473d2684cbd8f191c01b5b67a08e560a2917e7aba6b731f2e` | `d870124ee21742a2b2ae68664327d3221b88c3649a42556f3a4f74e020d869b8` (44) |
| `Toy.ByteSL.readBytes_frame_stable` | R5b result | Classical.choice, Quot.sound, propext | `147b030ce68f7ab502ffd7c6ea4f2f0dd67f5beb03e0ecf09ff6d1cffddb0578` | `d01e99ca365c0b17a747e71338846ef76f831fa2eb45c4fa93fbf81145b415b4` (25) |
| `Toy.ByteSL.byte_and_typed_commands_nonvacuous` | R5b non-vacuity | Quot.sound, propext | `63b0d9ca06c1322a2afe0fa28769b5b0474d424b4b16e9b6bb0e3506ef006abc` | `153e3ac6129f03894a70562f4b399f09d40def59c0e3e499afaab7bd4fbdc91a` (58) |
| `Toy.ByteSL.readBytes_frame_stable_shared_ro_nonvacuous` | R5b non-vacuity | Classical.choice, Quot.sound, propext | `29923570713abee8729c2614cb569357434f3076dcb4333e317fac568e220f4d` | `f20302ca7bdfd23a639288c630ee4a9883736cf588ebf79c6775cf9ca260679e` (55) |
| `Toy.ByteSL.readBytes_frame_stable_tight_hd` | R5b counterexample for `hd` | Quot.sound, propext | `7182940722822ad7441b783194be3581ea4cc9bc13dfc51100dafd495c4e0125` | `bb32e3772be8c3d266432eddc28ccacaadb25d9f63dfb8680fb52c81b2f546eb` (30) |
| `Toy.ByteSL.readBytes_frame_stable_tight_hr` | R5b counterexample for `hr` | Quot.sound, propext | `a06a40f6dca46924ffd2fa1f9e0fb6cd84637f05f03678e466b004234f3cd61d` | `68a2b99e431d07d0f20eb4bdfe4988ef57424fd8848cf691d6d1001fd8822a9c` (28) |
| `Toy.ByteSL.tcopyLoose_local_of_decodeMono` | R5c result | Classical.choice, Quot.sound, propext | `d8af8c29b7329480cf88715b654ab1798e4f6f92df44468874c7464ebdb92df0` | `31859f0cbed180f725e2389005cf34490308266a6bf74891794958f7274c886b` (55) |
| `Toy.ByteSL.tcopyLoose_local_nonvacuous` | R5c non-vacuity | Quot.sound, propext | `036b7654907eed57f63c5e72c06f3643da38712b069c0aa998742da487b1709f` | `d1427931279f0eb3bf667151c85be1cb639465668c8afc6a16ab79a22e888fe7` (60) |
| `Toy.ByteSL.tcopyLoose_not_local_exactUnitRep` | R5c counterexample for `hM` | Quot.sound, propext | `39431489f1d24db57bfdce4e1da3085a9e0f859c63836ccef2cd1bcd7e62839d` | `b411cb5b5f9d9d5a39153141cb9e22998204f647de278121cbf5fe9361507b02` (60) |
| `Toy.ByteSL.bcopyLoose_safetyMono_and_not_frameProp` | R5d result; R5d non-vacuity | Classical.choice, Quot.sound, propext | `c9ceab59fe4843fd6f5b807cce9c6f5cf8fc1447425ce1eb0f0c3ff1ed47c4ad` | `23aa0c0431a7c7656924d5c09e5e6120758fe75253ef981e71104e3433424420` (47) |
| `Toy.ByteSL.bstoreShared_safetyMono_and_not_frameProp` | R5e result; R5e non-vacuity | Quot.sound, propext | `2c85573935055f74ed8ec2f8fabd85fb2446b06d35617fba832d2e9486f49e09` | `88473d7bb72642154a23bb113840760952f71717e9562b52f3b30f32afe3c8df` (44) |
| `Toy.ByteSL.byteHeap_isSepAlgebra_and_not_rightCancel` | R5f result; R5f non-vacuity | Classical.choice, Quot.sound, propext | `621ef9d6ab08a4b851b79dd5ce7b6ee1ef525ce15c93bc610657dc3feca84d0f` | `2276be1e763f42737315cbb195b402e48fcd10cdbcde58dfcbfc97633e31ffd8` (37) |

Other theorems named in this report (not card fields of `results.json`, so no recorded hash; all are in `lean/RevalidationAudit.lean` and `audit/axioms.json`): `Toy.ByteSL.viewChange_hyps_hold_and_source_ptsDec_empty_noneRep` (axioms: Quot.sound, propext); `Toy.ByteSL.tcopyLoose_reads_frame_owned_full_cell` (axioms: Quot.sound, propext); `Toy.ByteSL.transmuteTotal_of_intoBytes_of_fromBytes` (axioms: propext); `Toy.ByteSL.ptsEnc_entails_ptsDec_fails_noneRep` (axioms: Quot.sound, propext); `Toy.ByteSL.ptsDec_eq_byteUpClose_fails_exactUnitRep`, `Toy.ByteSL.ptsDec_eq_byteUpClose_fails_noneRep`, `Toy.ByteSL.ptsDec_eq_byteUpClose_fails_boolNZRep` (axioms: Classical.choice, Quot.sound, propext); `Toy.ByteSL.Layout2.fits₁_zero`, named only inside the quoted definition of `structDecode` (axioms: Quot.sound, propext).

### Primary sources

Pinned repository revisions and pull-request states were observed on 2026-11-20. Each entry states what is relied on; entries cited for context say so.

* **[LEAN]** Lean 4 toolchain, leanprover/lean4 tag v4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52 (tag resolved through the GitHub API on 2026-11-20).
* **[REPR]** Published package 'byte-representation-galois-laws-and-transmute-composition' of this corpus (google/zerocopy branch reference, commit c659d187a4f73e59451f321e013b722eb14b8439): abstract bytes, the definedness order, the laws DecodeMono, DecodeEncode, EncodeLeast (its R1a: together they are equivalent to the lower-adjoint form encode v <= x <-> decode x = some v), IntoBytes/FromBytes and totality of transmute (its R2a: IntoBytes A and FromBytes B make transmute A -> B total; its R5b: under DecodeEncode A, EncodeLeast A and DecodeMono B, totality is inclusion of validity sets), and the concrete representations u8Rep, boolRep, boolNZRep, padUnitRep, exactUnitRep, u8PadRep, pairRep, noneRep with their byte-level law lemmas. This package copies its definitions and examples (support files lean/ToyRepr/Basic.lean and lean/ToyRepr/Examples.lean; code identical after renaming the namespace, checked on 2026-11-20 against the files at that commit) and Bytes.slice (support file lean/ToyRepr/Product.lean, code unchanged), and restates no result of it as proved here except its R2a (support file lean/ToyRepr/Transmute.lean), copied with its proof. SHA-256 digests of these four upstream files are listed under Applicability.
* **[FRAME]** Published package 'frame-rule-locality-and-precise-assertions' of this corpus (google/zerocopy branch reference, commit 8ff18039787575ce7f24066acdc7600918ad8185, the only commit touching reports/frame-rule-locality-and-precise-assertions/ on that branch as observed on 2026-11-20): support file lean/Toy/Sep/Basic.lean (namespace Toy.Sep) defines SepStruct, Outcome, Cmd, Assn, sep, Safe, Triple, SafetyMono, FrameProp, Local, FrameRuleSound and the algebraic laws; this package's SepBasic.lean is a subset of those declarations with unchanged code (checked on 2026-11-20). Support file lean/Toy/Sep/Heap.lean defines the finite-heap carrier Heap with Heap.ext, Heap.emp, Heap.set and Heap.join; this package's Heap.lean copies these (with their simp lemmas emp_val, set_val, join_val), renaming the type variable from V to C and omitting pt, Disj and the SepStruct instance (checked on 2026-11-20). SHA-256 digests of both upstream files are listed under Applicability. Its R2b, Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp, is R5a here; its R5 proves lookup, mutation, allocation and deallocation local in a finite-heap model with arbitrary cell values, address-disjoint union and no permissions; its R3a-R3d give non-local heap commands (an allocation test, fixed-address allocation that faults, least-free-address allocation, predictable allocation).
* **[MINIRUST]** MiniRust specification, file spec/lang/representation.md at minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: struct decode 'ignores the bytes which are before, between, or after the fields (usually called padding)' and encode 'always and deterministically makes those bytes Uninit'; section 'Generic properties': encode and decode are monotone, decode(encode(val)) == Some(val), and decode(bytes) == Some(val) implies encode(val) <= bytes ('an adjoint relationship, or a Galois connection'); the self-assignment discussion (a typed copy decodes and re-encodes, resetting padding to Uninit); section 'Transmutation': Machine::transmute encodes at type1, decodes at type2 (undefined behavior if decoding fails) and then checks the decoded value with check_value, a machine-state-dependent well-formedness check that is not modeled here.
* **[TUCH]** Tuch, H., Klein, G. & Norrish, M., 'Types, Bytes, and Separation Logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234 (author PDF https://trustworthy.systems/publications/nicta_full_text/134.pdf): a byte-level heap heap-mem; typed reads h-val h p = from-bytes (heap-list h (size-of TYPE('a)) (ptr-val p)) and the law from-bytes (to-bytes v) = Some v; a heap type description kept as an additional state component; separation logic embedded on top, with singleton assertion p |->g v = (lambda s. lift-typ-heap g s p = Some v and dom s = {ptr-val p ..+ size-of TYPE('a)}), where lift-typ-heap is defined only at pointers satisfying the guard and heap type description (s, g |=s p); i.e. a decode-based typed points-to with an exact byte footprint, guarded by alignment and type-description conditions that this package does not model.
* **[RUSTBELT]** Jung, R., Jourdan, J.-H., Krebbers, R. & Dreyer, D., 'RustBelt: Securing the Foundations of the Rust Programming Language', PACMPL 2(POPL), Article 66, 2018, doi:10.1145/3158154. Section 3.2: following Lee et al. 2017, freshly allocated memory holds a poison value; the only safe operations on it are loads and stores. Section 3.3: the type of 'arbitrary sequences of n base values' represents uninitialized memory. Sections 4.1-4.2: a type is interpreted by a predicate [[tau]].own(t, vs) on lists of values with |vs| = [[tau]].size, and [[tau1 x tau2]].own splits vs = vs1 ++ vs2 (memory locations hold values, not bytes; products have no padding). Section 4.3: shared references are interpreted by a separate, type-specific sharing predicate [[tau]].shr(kappa, t, l); Section 6 uses it for Cell and Mutex (interior mutability).
* **[REFINEDRUST]** Gaeher, L., Sammler, M., Jung, R., Krebbers, R. & Dreyer, D., 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', PACMPL 8(PLDI), Article 192, 2024, doi:10.1145/3656422. Section 4 (Radium): values are lists of memory bytes, each a normal byte (0-255), a location fragment, or poison (e.g. for uninitialized memory); the heap maps locations to memory bytes; loads and stores are parameterized by a layout. Section 4.1 and Fig. 7: struct layouts list explicit unnamed fields for padding, and verification is parametric in a layout algorithm. Section 4.2: unlike lambda-Rust, Radium represents padding, and reading padding bytes as an integer is undefined behavior. Section 5.1 and Fig. 8: value types include uninit st (uninitialized memory of syntactic type st) and maybe_init T.
* **[REFINEDC]** Sammler, M., Lepigre, R., Krebbers, R., Memarian, K., Dreyer, D. & Garg, D., 'RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types', PLDI 2021, pp. 158-174, doi:10.1145/3453483.3454036: the system whose Caesium operational semantics RefinedRust's Radium is based on (as stated in the RefinedRust paper, Sections 1 and 4).
* **[VST]** Verified Software Toolchain, PrincetonUniversity/VST commit d50ac1969f9f6586621895eb043ccf08a165f731: veric/mapsto_memory_block.v, Definition mapsto (sh : Share.t) (t : type) (v1 v2 : val): with a readable share, either a value v2 with tc_val t v2 is stored at v1, or v2 = Vundef and some value is stored there (mapsto_ sh t v1 := mapsto sh t v1 Vundef); Definition memory_block sh n v: ownership of n bytes with arbitrary contents. floyd/mapsto_memory_block.v: spacer sh be ed := memory_block sh (ed - be) at offset be, and withspacer sh be ed P p := P p * spacer sh be ed p. floyd/field_at.v: nested_sfieldlist_at wraps each struct field's field_at in withspacer, and Lemma field_at_Tstruct (line 518) equates field_at of a struct with nested_sfieldlist_at of its members, so a struct's data_at owns its padding as memory_block (arbitrary contents) at the same share; Lemma data_at_conflict_glb (line 2196): two data_at at the same address whose shares have a non-identity greatest lower bound entail False (for sizeof t > 0). VST's shares form a cancellative share algebra, not the idempotent read-only permission used here.
* **[VSTPUB]** Published references for VST: Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552; Cao, Q., Beringer, L., Gruetter, S., Dodds, J. & Appel, A. W., 'VST-Floyd: A Separation Logic Tool to Verify Correctness of C Programs', Journal of Automated Reasoning 61, pp. 367-422, 2018, doi:10.1007/s10817-018-9457-5. Cited for the program logic whose source files are described under the VST entry; no specific statement of these publications is relied on.
* **[CN]** Pulte, C., Makwana, D. C., Sewell, T., Memarian, K., Sewell, P. & Krishnaswami, N., 'CN: Verifying Systems C Code with Separation-Logic Refinement Types', PACMPL 7(POPL), Article 1, 2023, doi:10.1145/3571194. Section 2.6: Owned<tau>(p)(v) asserts ownership of the memory pointed to by p with value v, 'equivalent to a separation logic points-to resource p |->tau v, indexed by a C-type tau to capture its memory layout'. Section 2.8: resource inference splits a struct resource into resources for the members 'and of padding bytes, where appropriate', and recombining them 'for a padded struct ... would also consume ownership of padding bytes'.
* **[FULMINATE]** Banerjee, R., Memarian, K., Makwana, D., Pulte, C., Krishnaswami, N. & Sewell, P., 'Fulminate: Testing CN Separation-Logic Specifications in C', PACMPL 9(POPL), Article 43, 2025, doi:10.1145/3704879: CN's built-in resources Owned (points-to indexed by C types) and Block (points-to for uninitialised memory); Section 2.3: runtime ownership checking keeps ghost state giving, for each byte of memory, the C stack depth of the function that owns it (per-byte ownership).
* **[KREBBERS]** Krebbers, R., 'A Formal C Memory Model for Separation Logic', Journal of Automated Reasoning 57(4), pp. 319-387, 2016, doi:10.1007/s10817-016-9369-1: a Coq-formalized memory model for (non-concurrent) C11 with a permission model designed for separation logic, covering typed and byte-level (untyped) views of memory (cited as related byte-level-with-permissions work, no specific statement relied on).
* **[AENEAS1551]** AeneasVerif/aeneas pull request #1551, 'Separation logic over the byte heap' (open and unmerged as observed on 2026-11-20; head commit 1d8f9aa0121faca8ff113c1b9b742b333e3e1519; commits authored by Cezar Andrici; base branch cezar/sl-extraction). Unmerged prototype, described here only as its public source states: backends/lean/Aeneas/SepLogic/Bytes.lean ('The byte contents of the heap as fragments (from fournet/wip-memory-model)') defines pointsTo (the cells hold some admissible encoding of the value, at a sharing depth) and readable (the cells hold some bytes that decode to the value) and proves pointsTo_readable from the representation's encode_decode law; SepLogic/PCM.lean defines a class PartialCommMonoid and the order Subheap ('is a part of': h' is h extended with a compatible part), on which, its header comment says, the separation-logic assertions are upward closed (upward closure under heap extension, not the byte-definedness closure byteUpClose of this package). Not relied on for any formal claim here.
* **[AENEAS1497]** AeneasVerif/aeneas pull request #1497, 'Fournet/wip memory model' (open and unmerged as observed on 2026-11-20; head branch fournet/wip-memory-model at commit d17ca83fc07d712d1785f650840cb2073c259e69; commit authors as recorded: 'fournet', Cezar Andrici, Son Ho). Unmerged prototype, described here only as its public source states: its README describes an experimental concrete-address heap model for unsafe Rust with bytes uninit | data U8 | pointer and cells shared Nat Byte | borrowed (two shared cells are compatible when both depths are positive and the bytes are equal); Heap/Repr.lean's Repr has a relational encoder with encode_decode and a decode_mono law ('Decoding does not depend on uninitialized bytes'); Heap/Resources.lean defines pointsTo (an admissible encoding, 'including any permitted uninitialized padding') and readable (decode-based); Heap/TRANSMUTE.md records a more permissive proposal (CompatibleAt / Transmutes) and adopts the stricter exact-result fragment ExactAt(S, T, x, expected) := S.size = T.size and, for all bytes, S.decode(bytes) = Some(x) => T.decode(bytes) = Some(expected), i.e. a decode-based entailment between byte vectors, the shape of R3b/R3c here. Not relied on for any formal claim here.
* **[ZEROCOPY]** zerocopy crate, version 0.8.63, documentation at https://docs.rs/zerocopy/0.8.63/zerocopy/: macro transmute_mut! behaves like a function from &'src mut Src to &'dst mut Dst with bounds Src: FromBytes + IntoBytes, Dst: FromBytes + IntoBytes, align_of::<Src>() >= align_of::<Dst>() and size compatibility; macro transmute_ref! behaves like a function from &'src Src to &'dst Dst with bounds Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, and the same alignment and size conditions. Cited only for these bounds. Crate identity: crates.io checksum (SHA-256 of the .crate file) e5fe1f8f1b06191a00962174c61aa5005e0bb391a6d80d07e24d115c01a92ed8; repository google/zerocopy, tag v0.8.63, commit c55af491426ef53f35fb8c6e83f220fa07712e66 (both observed on 2026-11-20).
* **[REYNOLDS]** Reynolds, J. C., 'Separation Logic: A Logic for Shared Mutable Data Structures', LICS 2002, pp. 55-74, doi:10.1109/LICS.2002.1029817: the standard reference for separation logic and its vocabulary, including the distinction between exact assertions and assertions closed under heap extension (intuitionistic assertions); cited for the contrast with this package's byte-definedness closure.
* **[YO]** Yang, H. & O'Hearn, P. W., 'A Semantic Basis for Local Reasoning', FoSSaCS 2002, LNCS 2303, pp. 402-416, doi:10.1007/3-540-45931-6_28 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf). Section 4: Lemma 1 (Safety and Termination Monotonicity), Lemma 2 (Frame Property), Theorem 1 (soundness of the Frame Rule, with the side condition that the command modifies no variable free in the frame). Section 4.1: an operation that traps memory faults would let a program branch on whether a cell is active, contradicting Safety Monotonicity; and an abstract setting is sketched in which an arbitrary partial commutative monoid replaces heaps, with a local action defined as a relation satisfying Safety and Termination Monotonicity and the Frame Property, for which 'the Frame Rule is sound for every local action' (no cancellativity is required).
* **[COY]** Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (author PDF http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-short.pdf): Section 3 recalls Safety Monotonicity and the Frame Property for relations and states that 'a relation R satisfies Safety Monotonicity and the Frame Property iff the frame rule is sound for it'. Definition 1 takes a separation algebra to be a cancellative partial commutative monoid; its Example 2 (heaps with permissions, HPerm, over a permission algebra required to be cancellative) mentions the permission algebra {R, RW} with R o R = R and RW o p undefined, remarking that it does not allow converting a total (RW) permission into several read permissions or back. That two-point algebra is the permission algebra of this package; the heap algebra it induces with the empty heap as unit is not cancellative (R5f), so this instance lies outside Definition 1.
* **[BORNAT]** Bornat, R., Calcagno, C., O'Hearn, P. W. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327: brings fractional (and counting) permissions into separation logic; cited by COY 2007 as the source of heaps with permissions.
* **[BOYLAND]** Boyland, J., 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, doi:10.1007/3-540-44898-5_4: introduces fractional permissions (writing needs the whole permission, reading any fraction; fractions recombine). Cited as the origin of fractional permissions; the two-point full / read-only algebra here is a non-fractional, non-recombinable variant.
* **[DHA]** Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, doi:10.1007/978-3-642-10672-9_13 (author PDF https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf): revisits the separation-algebra axioms; its disjointness axiom (a + a = b implies a = b: no nonempty share joins with itself) is motivated by the remark that without disjointness 'the obvious definition of a formula to describe binary trees in fact describes directed acyclic graphs'. The idempotent read-only cells of this package violate that axiom.
* **[KKB]** Klein, G., Kolanski, R. & Boyton, A., 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22, with the Archive of Formal Proofs entry 'Separation Algebra' (May 2012): an Isabelle/HOL type-class library of separation algebras based on COY 2007 in which cancellativity is a separate subclass (cancellative_sep_algebra, assumption sep_add_cancelD: x + z = y + z with x ## z and y ## z implies x = y), the right-cancellation law RightCancel of this package.
* **[GBC]** Gotsman, A., Berdine, J. & Cook, B., 'Precision and the Conjunction Rule in Concurrent Separation Logic', Electronic Notes in Theoretical Computer Science 276 (MFPS XXVII), pp. 171-190, 2011, doi:10.1016/j.entcs.2011.09.021: studies the interplay of precision and the conjunction rule in separation logic, the kind of result that does not transfer to non-cancellative models without further argument (cited for its topic only).
* **[DFRAC]** Vindum, S. F. & Birkedal, L., 'Contextual Refinement of the Michael-Scott Queue (Proof Pearl)', CPP 2021, pp. 76-90, doi:10.1145/3437992.3439930: introduces discardable fractions for Iris points-to assertions, where a fraction can be irrevocably discarded to obtain persistent, freely duplicable read-only ownership; Iris itself is described in Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L. & Dreyer, D., 'Iris from the ground up', Journal of Functional Programming 28, e20, 2018, doi:10.1017/S0956796818000151. The read-only permission of this package behaves like a discarded fraction without the fractional part.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and
`python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified),
runs `lake build`, rejects `sorry`/`admit`/`native_decide`/`axiom` in the Lean sources, generates
and runs a small Lean program that computes `collectAxioms` for every library declaration (failing
on any axiom other than `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every
Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of
the `repr` of its type and of its definition closure (the sorted, newline-joined
`name : repr(type)` lines, with ` := repr(value)` for non-theorems, of every package-local constant
reachable from the type; theorem bodies excluded), comparing them with `audit/statements.json`. It
prints `REVALIDATED` on success.

A manual axiom audit without Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean   # '#print axioms' for every theorem named in this report
```

`lean/RevalidationAudit.lean` is outside the library target. Each printed entry (long entries wrap
across lines) must read `'<name>' depends on axioms: [...]` with a subset of `propext`, `Classical.choice`, `Quot.sound`
(or `'<name>' does not depend on any axioms`); this manual check covers axioms only. A passing
`revalidate.py` run re-establishes the kernel checks and the statement identities only; the
modeling-bridge claims are re-checked by re-reading the cited sources at the recorded revisions,
and the claim that the copied modules match the two published packages is re-checked by comparing
`lean/Toy/ByteSL/ReprBasic.lean`, `ReprExamples.lean` and `SepBasic.lean`, together with the
copied fragments (`transmuteTotal_of_intoBytes_of_fromBytes` in `Transmute.lean`, `Bytes.slice` in
`Struct.lean`, and the `Heap` carrier in `Heap.lean`), with the files named under
**Applicability** at the recorded commits (comments removed, namespace renamed; the SHA-256 digests
recorded there identify those upstream files).
