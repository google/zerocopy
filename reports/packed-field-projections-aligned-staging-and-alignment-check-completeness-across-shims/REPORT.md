# Packed-field projections: aligned staging and alignment-check completeness across shims (Lean 4 toy model)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

These are statements about a toy model, formalized in Lean 4, of under-aligned fields of packed
aggregates, reference-taking compiler operations (drops, frees of owning pointers, clones), aligned
staging of those operations, synthesized shims, and dynamic alignment-check instrumentation; they
neither establish nor refute the corresponding claims about Rust, rustc, Miri or any other
implementation. Model–system relation: none proved. Connections to real systems are separate
`derived (modeling bridge)` remarks (Findings, *Modeling bridges*) that cite documented behaviour.

Conventions that every bullet below inherits. Alignment is divisibility on unbounded naturals: an
address `a` is aligned for `n` iff `n ∣ a`; with alignment 0 exactly one address (0) is aligned,
and with alignment 1 every address is aligned. No wrapping and no truncating operation (truncated
subtraction, floor division, modulo) is used. "The run" is the unique, fuel-bounded run produced by
the deterministic generator `run`. `positions P` is a static list: the compiler-operation positions
of the source body and of every shim in `reachableShims P`, which over-approximates the shims a run
enters; a hypothesis that ranges over `positions P` must hold at every listed position, executed by
a run or not.

One sentence per result (its plain claim):

* **`in-place`** (counterexample, T1): For the program `progInPlace` (one local
  `x : packed { u8, R4 }` at address 0, whose source body is the single compiler drop of `x` and
  contains no raw-pointer operation, i.e. `SafeSrc progInPlace`), with no staging and no checks
  (`cfgNone`), the ideal-semantics run destroys the field `x.1`, while the reference-semantics run
  creates a misaligned `&mut` at op 0 of the drop glue of `R4` (address 1, alignment 4): a UB event.
* **`staging`** (theorem, T1): For every toy program `P` whose locals are at aligned addresses
  (`FrameAligned`) and whose source body has no raw-pointer operation (`SafeSrc`), and every
  configuration `cfg` (with any instrumentation policy) such that every compiler-operation position
  of the source body and of the shims the program may enter (`positions`) whose place is
  misalignable is staged (`CritCovers`), every staged value is sized (H1, `StagedSized`), no staged
  drop reaches an address-observing destructor through inline sub-values (H2, `StagedAddrBlind`),
  and every staging temporary is aligned for the staged type (H3, `TempsAligned`), each of these
  four conditions being required at every position in `positions`, executed by a run or not: the
  staged program's reference-semantics run (the run produced by `run`) has no UB event, and its
  observable trace (staging copies removed) equals the ideal-semantics trace of the unstaged
  program.
* **`criterion-exact`** (characterization, T0): For all naturals `A`, `n`, `o` (including 0), some
  multiple `a` of `A` has `a + o` not divisible by `n` iff `n` does not divide `gcd A o`. So, for a
  fixed layout, a place at total offset `o` (summed along the whole path) from a base aligned to `A`
  may be disaligned for alignment `n` exactly when `n ∤ gcd A o`.
* **`criterion-type-sound`** (theorem, T1): If every alignment and every `packed(n)` parameter of
  the environment is a power of two (`PowTwoAligns`), the layout respects packing
  (`RespectsPacking`), and the path from `t0` resolves to a place of type `u` at offset `o`, then a
  place whose type alignment divides its type-based guaranteed alignment `typeGA` (computed along
  the whole path from the base type's alignment) cannot be misaligned from any base address aligned
  for the base type.
* **`criterion-type-covers`** (theorem, T1): For every toy program whose environment has
  power-of-two alignments and `packed(n)` parameters and whose layout respects packing, the
  type-based criterion `critType` (with any temporaries and policy) stages every compiler-operation
  position of the program (`positions`) whose place is misalignable.
* **`criterion-type-exact-over-layouts`** (characterization, T1): If every alignment and every
  `packed(n)` parameter of the environment is a power of two (`PowTwoAligns`), the path from `t0`
  follows the types to a place of type `u` (`typeAt`), and the path takes no projection step
  `(t, j)` twice (`NoRepeatStep`), then some layout that respects packing makes the place
  misalignable (from a base aligned for the base type) iff `u`'s alignment does not divide the
  type-based guaranteed alignment `typeGA` computed over the whole projection path.
* **`criterion-leaf-misses`** (counterexample, T1): (i) For the compiler drop of the nested place
  `x.1.0` (the `R4` field of a non-packed `S` stored in `Q = packed { u8, S }`), the leaf-only
  criterion `critLeaf` (stage iff the immediate parent is `packed(n)` and the field's alignment does
  not divide `n`) does not stage, the place is misalignable, and the unstaged drop is UB; the
  type-based criterion stages it and the run has no UB. (ii) In the two-type environment `envUnder`,
  where the struct `S = { R4 }` declares alignment 1, below its field's alignment 4 (the toy permits
  this), with power-of-two alignments and the zero layout (which respects packing), for a local
  `s : S` at the aligned address 1, the compiler drop of the one-step place `s.0` is not staged by
  `critLeaf` and is UB; `critType` stages it and the run has no UB.
* **`criterion-type-overstages-fixed-layout`** (counterexample, T1): In the four-type environment
  `envOuter` (with power-of-two alignments) and the packing-respecting layout `LOuter`, the
  type-based criterion stages the place `Outer.1.2` although that place (total offset 4 from a base
  aligned to 2, type alignment 2) can never be misaligned, while the offset-aware criterion
  `critExact` does not stage it.
* **`overstaging-aligned`** (counterexample, T1): (i) For the local `y : R4obs` at the aligned
  address 8 (`progAlignedObs`, whose destructor prints its address), staging its drop with `critAll`
  into a temporary at address 16 gives a reference run with no UB event whose observable trace
  prints 16, while the ideal run of the unstaged program prints 8. (ii) Positive control: for the
  local `y : R4` at the aligned address 8 (`progAligned`), the same over-staging gives a run with no
  UB event whose observable trace equals the ideal trace, with exactly one staging copy where the
  ideal run has none.
* **`box-free`** (counterexample, T1): In the toy, where freeing a box is a shim that creates `&mut`
  to the box field at its op 0 and `moveOut` is a no-op marker, consider `progBox` over `envB` (the
  drop of a local `z : packed { u8, Box<R4> }`, then a marker for a deref-move out of the owning
  pointer stored at offset 1 of a local `x : packed { u8, Box<R4> }`, then the free of that pointer
  through the field `x.1`, then the drop of the local `y : R4`). The configuration `cfgDropsOnly`
  (type-based staging restricted to drops, temporaries at address 16) stages every misalignable drop
  position of `progBox`; such a position exists (the drop of `z.1` inside the drop glue of
  `packed { u8, Box<R4> }`); and a misalignable free position exists that `cfgDropsOnly` does not
  stage (the free of `x.1`; `positions_progBox` lists exactly four positions of `progBox`). The
  reference run under `cfgDropsOnly` copies `z.1` to the temporary, drops it there (the pointee's
  destructor, then the free of `z.1`), and then creates a misaligned `&mut` to the box field `x.1`
  at op 0 of the box-free shim: a UB event. Staging the box field itself into an aligned temporary
  before freeing (`cfgType envB`) gives a run without UB whose observable trace equals the ideal
  trace of the unstaged program (`cfgNone`). Removing the `moveOut` marker changes neither run.
* **`completeness`** (characterization, T1): Fix an environment, a layout, a staging criterion,
  temporaries and an instrumentation policy `I : BodyId → Nat → Bool`, chosen before the program.
  Over the class of all programs over that environment and layout — which contains programs whose
  unsafe client code passes arbitrary raw addresses to any shim, programs with user-written
  reference creations at any source position, and programs whose locals sit at any address — every
  run produced by `run` in the reference semantics has no UB event iff `I` checks op 0 of every
  existing shim (drop glue and clone of every type, box free of every box type) of every in-range
  type whose alignment is not 1, and, if some in-range type's alignment is not 1, every source
  position.
* **`precision`** (theorem, T0): For every toy program and configuration, the instrumented
  reference-semantics run produced by `run` equals the uninstrumented run with each UB event at a
  checked position relabelled as a trap; so a check traps only at a checked position where the
  uninstrumented run has a UB event (a misaligned reference creation), never at an aligned reference
  creation.
* **`escape`** (counterexample, T1): Consider `progEscape` over `envA` (locals
  `w, x : packed { u8, R4 }` at addresses 0 and 8; the compiler drop of `w`, then an unsafe client
  call that passes the raw address 9 — the address of `x.1`, as `&raw mut x.1` would produce; the
  toy passes the literal address — to the drop glue of `R4`). Take checks at every source position
  and no check at op 0 of the drop glue of `R4` (`instrSrc`), and type-based staging
  (`critType envA`, temporaries at address 16), which stages every misalignable compiler-operation
  position of `progEscape`; such a position exists (the drop of `w.1` inside the drop glue of
  `packed { u8, R4 }`; `positions_progEscape` lists exactly two positions of `progEscape`). The
  reference run copies `w.1` to the temporary and runs its destructor there, and then the client
  call makes the drop glue of `R4` create a misaligned `&mut` at its op 0: a UB event with no trap.
  With checks everywhere (`instrAll`) the same run ends with a trap at that operation instead.
* **`sufficiency`** (theorem, T1): For every toy program whose locals are at aligned addresses
  (`FrameAligned`), if (a) every compiler-operation position of the program (`positions`: the source
  body and the shims the program may enter, executed by a run or not) whose place is misalignable is
  staged (`CritCovers`) into a temporary aligned for the staged type (`TempsAligned`), (b) every raw
  address that unsafe client code passes to an existing shim is aligned for the shim's type
  (`ClientPtrsAligned`), and (c) every user-written reference creation in the source body is checked
  (`SrcRefsInstrumented`), then the reference-semantics run produced by `run` has no UB event,
  whatever checks the shims have (the policy may check no shim). The run may still end with `trap`,
  `stuck` or `outOfFuel`.
* **`sufficiency-shim`** (theorem, T1): For every toy program whose locals are at aligned addresses
  (`FrameAligned`), if every compiler-operation position of the program (`positions`: the source
  body and the shims the program may enter, executed by a run or not) whose place is misalignable is
  staged (`CritCovers`) into a temporary aligned for the staged type (`TempsAligned`), and every raw
  address that client code passes to an existing shim is aligned for the shim's type
  (`ClientPtrsAligned`), then the reference-semantics run produced by `run` has no UB event inside a
  shim. The run may still have a UB event in the source body and may end with `trap`, `stuck` or
  `outOfFuel`.
* **`no-stuck`** (theorem, T1): For every toy program and configuration, if every staged position of
  the program (of its source body and of the shims it may enter, `positions`, executed by a run or
  not) has a sized type (H1, `StagedSized`), then the run produced by `run`, in either semantics,
  has no `stuck` event.

Non-claims for every card are listed under **Boundaries** (non-claims first), together with the
non-claims shared by all results; read them before relying on a result. Every hypothesis of every
general theorem is `tight`, with a proved counterexample in which all the other hypotheses hold and
the conclusion fails; the witness class of each counterexample is stated in the card's hypothesis
ledger.

## Applicability

### Model fidelity

A toy model, not a mirror of any compiler's data structures. It captures:
under-aligned fields of packed aggregates; reference creation as the alignment-relevant event;
compiler-generated operations that take references to places (drops, freeing an owning pointer
after a deref-move, clones) and *aligned staging* of those operations; synthesized shims (drop
glue and clone for every type, box free for owning-pointer types) callable both by compiler
operations and, with raw pointers, by unsafe client code; and dynamic alignment-check
instrumentation given as a set of (body, operation) pairs. Not modelled: sizes, field overlap and
the layout arithmetic (offsets come from a given layout function), byte memory and value contents,
loads and stores through raw pointers (`readUnaligned` and `moveOut` are no-ops), ownership and
moved-from state, loops and control flow (source bodies are straight-line), borrows, aliasing,
unwinding, drop elaboration (the program says which drops happen), `packed` combined with `align`
on the same type, and any rule that rejects programs statically.

### Degenerate edges

Alignment is divisibility on `Nat`: an address `a` is aligned for `n` iff
`n ∣ a`. With `n = 0` only address `0` is aligned (`misalignable_align_zero`); with `n = 1` every
address is aligned (`refStep_align_one`). Offsets and addresses are unbounded naturals (no
wrapping, no truncating operation is used). `packed(0)` is representable: its fields have
effective alignment `0`, so a packing-respecting layout puts them at offset `0`. Results that need
it assume `PowTwoAligns` (every alignment and every `packed(n)` parameter is a power of two),
which excludes alignment `0` and `packed(0)`. Out-of-range type ids denote a sized scalar of
alignment 1. A field index with no field has effective alignment `0` (`effAlign_out_of_range`),
and a path that leaves the types resolves to `none`. A local without a `frame` entry is placed at
address `0`. The fuel bound `Prog.fuel` is `env.length + 1`; in an environment whose shim nesting
exceeds it, runs end with `outOfFuel`.

### Toolchain and project

The Lean project is `lean/` (one `[[lean_lib]]`, library `ToyPacked`, namespace `Toy.Packed`),
built with Lean `leanprover/lean4:v4.34.1` and core Lean only: no Mathlib and no other dependency
(`lakefile.toml` declares no `[[require]]`). General results are in `ToyPacked/Results.lean` (and
`misalignable_iff_not_dvd_gcd` in `ToyPacked/Hyps.lean`), the lemmas used in their proofs in
`ToyPacked/Lemmas.lean`, and the concrete counterexamples, non-vacuity witnesses and positive
controls in `ToyPacked/Counterexamples.lean` and `ToyPacked/Examples.lean` (proved by `decide` on
concrete instances unless noted). Every result is fully proved; `#print axioms` reports at most
`propext`, `Classical.choice` and `Quot.sound` for every declaration of the library (Evidence).
`lean/RevalidationAudit.lean` is outside the library target and only prints axioms (Revalidation).

### Subjects and how they relate

The subjects in `REPORT.json` are the Lean toolchain release that kernel-checks every theorem, and
the upstream documents whose documented behaviour the toy is modelled on or contrasted with: the
`rust-lang/rust` tree at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (module documentation of
the packed-drop staging pass, `core::ptr::drop_in_place` and `core::pin` documentation, error-index
entries E0793 and E0588, the Miri README and the `-Zub-checks` unstable-book page), the Rust
Reference at `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, RFCs 1240 and
2582 at `rust-lang/rfcs` commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, MiniRust at
`minirust/minirust` commit `063d784186d3252bee242217f218223205c0b568`, and the cited papers. The
relation between the toy and these documents is a design correspondence stated in prose as
`derived (modeling bridge)`; no theorem relates the toy to any of them (model–system relation: none
proved). Beyond the cited files and line ranges no upstream source was examined, and no rustc, Miri
or Clang binary was run.
The Clang UndefinedBehaviorSanitizer page is a live documentation page without an immutable
revision; it is cited in prose with its observation date and is not a subject. Upstream issues and
pull requests are cited in prose as context and are not subjects.

## Findings

Every statement block below is a verbatim quote of the Lean source with its `file:line` range;
proofs are elided as `:= …`. Renderings labelled "Unfolded (prose)" are prose, not Lean terms.
Basis of every card's statement: execution (Lean kernel check). Connections between the toy
and real systems are stated under *Modeling bridges* (basis: derived (modeling bridge));
remarks elsewhere that mention Rust cite documented behaviour and are not findings.

### Definitions (verbatim)

#### Types, layouts, places (`ToyPacked/Basic.lean`)

```lean
-- lean/ToyPacked/Basic.lean:28-33
inductive Kind where
  | scalar
  | res (observesAddr : Bool)
  | box (pointee : Nat)
  | agg (pack : Option Nat) (fields : List Nat)
  deriving DecidableEq, Repr
-- lean/ToyPacked/Basic.lean:37-41
structure TyInfo where
  align : Nat
  sized : Bool
  kind : Kind
  deriving DecidableEq, Repr
```

* `Kind.res obs`: a value whose user destructor takes `&mut self`; `obs = true` means the
  destructor prints its own address (the one way the toy lets behaviour depend on addresses).
  `Kind.box p`: an owning pointer to a heap value of type `p`. `Kind.agg (some n) fs` is
  `packed(n)`; `Kind.agg none fs` is a non-packed struct. `TyInfo.sized = false` marks a type that
  cannot be moved to a temporary of statically known size (an unsized tail).

```lean
-- lean/ToyPacked/Basic.lean:47
abbrev Env := List TyInfo
-- lean/ToyPacked/Basic.lean:50
def Env.ty (env : Env) (t : Nat) : TyInfo := env.getD t default
-- lean/ToyPacked/Basic.lean:53
def Env.align (env : Env) (t : Nat) : Nat := (env.ty t).align
-- lean/ToyPacked/Basic.lean:56-59
def Env.fields (env : Env) (t : Nat) : List Nat :=
  match (env.ty t).kind with
  | .agg _ fs => fs
  | _ => []
-- lean/ToyPacked/Basic.lean:62
def Env.field? (env : Env) (t j : Nat) : Option Nat := (env.fields t)[j]?
-- lean/ToyPacked/Basic.lean:172-175
def Env.isBox (env : Env) (t : Nat) : Bool :=
  match (env.ty t).kind with
  | .box _ => true
  | _ => false
-- lean/ToyPacked/Basic.lean:65
abbrev Layout := Nat → Nat → Nat
-- lean/ToyPacked/Basic.lean:70-75
def resolve (env : Env) (L : Layout) : Nat → List Nat → Option (Nat × Nat)
  | t, [] => some (t, 0)
  | t, j :: rest =>
    match env.field? t j with
    | some f => (resolve env L f rest).map fun r => (r.1, L t j + r.2)
    | none => none
-- lean/ToyPacked/Basic.lean:78-83
def typeAt (env : Env) : Nat → List Nat → Option Nat
  | t, [] => some t
  | t, j :: rest =>
    match env.field? t j with
    | some f => typeAt env f rest
    | none => none
```

* `resolve env L t path` = the type of the projected place and its total offset, the sum of the
  layout offsets along the whole path. Positive `resolve_pos`; negative `resolve_neg` (a path that
  does not follow the types). `typeAt`: the same without offsets (`typeAt_pos`, `typeAt_neg`).

```lean
-- lean/ToyPacked/Basic.lean:88-92
def effAlign (env : Env) (t j : Nat) : Nat :=
  match (env.ty t).kind, env.field? t j with
  | .agg (some n) _, some f => min n (env.align f)
  | .agg none _, some f => env.align f
  | _, _ => 0
-- lean/ToyPacked/Basic.lean:97-102
def typeGA (env : Env) : Nat → List Nat → Nat → Nat
  | _, [], g => g
  | t, j :: rest, g =>
    match env.field? t j with
    | some f => typeGA env f rest (min g (effAlign env t j))
    | none => g
-- lean/ToyPacked/Basic.lean:107
def Misalignable (A n o : Nat) : Prop := ∃ a, A ∣ a ∧ ¬ n ∣ a + o
```

* `effAlign`: the alignment used to position field `j` (the smaller of `n` and the field type's
  alignment in a `packed(n)` parent; `0` if there is no field `j`). Positive `effAlign_pos`
  (`packed(2)` caps an `align(8)` field at 2); negative `effAlign_neg` (a non-packed parent does
  not cap); `effAlign_out_of_range`.
* `typeGA env t path g`: the *type-based guaranteed alignment* of a place, computed along the
  whole projection path from the base alignment `g`; each step takes the minimum with the field's
  effective alignment, so a packed ancestor anywhere on the path caps it. It ignores concrete
  offsets, field order and sibling sizes. Positive `typeGA_pos`; negative `typeGA_neg`.
* `Misalignable A n o`: some base address that is a multiple of `A` puts offset `o` at an address
  that is not a multiple of `n`, i.e. the place *may be disaligned*. Positive `misalignable_pos`;
  negative `misalignable_neg`.

```lean
-- lean/ToyPacked/Basic.lean:110
def IsPow2 (n : Nat) : Prop := ∃ k, k < n ∧ 2 ^ k = n
-- lean/ToyPacked/Basic.lean:115-117
def PowTwoAligns (env : Env) : Prop :=
  ∀ t, t < env.length → IsPow2 (env.align t) ∧
    ∀ n fs, (env.ty t).kind = .agg (some n) fs → IsPow2 n
-- lean/ToyPacked/Basic.lean:138-139
def RespectsPacking (env : Env) (L : Layout) : Prop :=
  ∀ t, t < env.length → ∀ j, j < (env.fields t).length → effAlign env t j ∣ L t j
-- lean/ToyPacked/Basic.lean:146-151
def pathSteps (env : Env) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | t, j :: rest =>
    match env.field? t j with
    | some f => (t, j) :: pathSteps env f rest
    | none => []
-- lean/ToyPacked/Basic.lean:156
def NoRepeatStep (env : Env) (t0 : Nat) (path : List Nat) : Prop := (pathSteps env t0 path).Nodup
-- lean/ToyPacked/Basic.lean:165-166
def FieldIdsDecreasing (env : Env) : Prop :=
  ∀ t, t < env.length → ∀ f, f ∈ env.fields t → f < t
```

* `IsPow2`: positive `isPow2_pos`; negatives `isPow2_neg_zero`, `isPow2_neg_three`.
* `PowTwoAligns`: every in-range type alignment *and* every `packed(n)` parameter is a power of
  two. Positive `powTwoAligns_pos`; negative `powTwoAligns_neg` (`envW`, alignment 3).
* `RespectsPacking env L`: every field offset is a multiple of the field's effective alignment.
  Positive `respectsPacking_pos`; negative `respectsPacking_neg`.
* `pathSteps env t path`: the projection steps `(aggregate type id, field index)` along a path
  (`pathSteps_pos`, `pathSteps_stop`). `NoRepeatStep env t path`: no step occurs twice. Positive
  `noRepeatStep_pos`, `noRepeatStep_cyc_short` (a one-step path in a self-containing aggregate);
  negative `noRepeatStep_neg` (`C = packed { C }`, path `[0, 0]`).
* `FieldIdsDecreasing`: every field type id of an in-range aggregate is smaller than the
  aggregate's id — a sufficient condition for acyclic aggregate containment that also requires the
  types to be listed in topological order; it rejects acyclic environments listed in another order
  (`fieldIdsDecreasing_rejects_envRev`) and says nothing about `box` pointees. Positive
  `fieldIdsDecreasing_pos`; negative `fieldIdsDecreasing_neg`. It implies `NoRepeatStep` for every
  path (`noRepeatStep_of_fieldIdsDecreasing`).

#### Programs, shims and the two semantics (`ToyPacked/Semantics.lean`)

```lean
-- lean/ToyPacked/Semantics.lean:26-29
structure Place where
  root : Nat
  path : List Nat
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:32-36
inductive ShimKind where
  | dropGlue
  | boxFree
  | clone
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:39-42
inductive BodyId where
  | src
  | shim (k : ShimKind) (t : Nat)
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:51-57
inductive Op where
  | comp (k : ShimKind) (p : Place)
  | moveOut (p : Place)
  | readUnaligned (t a : Nat)
  | rawRef (t a : Nat)
  | rawCall (k : ShimKind) (t a : Nat)
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:60-65
structure Prog where
  env : Env
  layout : Layout
  locals : List Nat
  frame : List Nat
  src : List Op
-- lean/ToyPacked/Semantics.lean:68-71
inductive Origin where
  | loc (x : Nat)
  | raw (i : Nat)
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:75-78
structure VName where
  origin : Origin
  path : List Nat
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:81
def VName.child (n : VName) (j : Nat) : VName := ⟨n.origin, n.path ++ [j]⟩
-- lean/ToyPacked/Semantics.lean:85-95
inductive Ev where
  | dtor (n : VName)
  | addrObs (n : VName) (a : Nat)
  | free (n : VName)
  | cloned (n : VName)
  | copy (n : VName)
  | stuck (b : BodyId) (i : Nat)
  | ub (b : BodyId) (i : Nat)
  | trap (b : BodyId) (i : Nat)
  | outOfFuel
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:98-100
def Ev.isUB : Ev → Bool
  | .ub _ _ => true
  | _ => false
-- lean/ToyPacked/Semantics.lean:103-105
def Ev.isShimUB : Ev → Bool
  | .ub (.shim _ _) _ => true
  | _ => false
-- lean/ToyPacked/Semantics.lean:292-294
def Ev.isStuck : Ev → Bool
  | .stuck _ _ => true
  | _ => false
```

* `Op.comp k p`: a compiler-generated reference-taking operation on place `p` (`dropGlue`: drop
  `p`; `boxFree`: free the box at `p`; `clone`: clone `p`). `Op.moveOut p`: a marker for a
  deref-move out of the box at `p`; it is a no-op (the toy tracks neither ownership nor contents).
  `Op.readUnaligned`: a no-op read through a raw pointer. `Op.rawRef t a`: a user-written `&*ptr`.
  `Op.rawCall k t a`: unsafe client code calls shim `k` of type `t` with the raw address `a`.
* Values carry address-independent names (`VName`), so destructor events of a staged and an
  unstaged run are comparable. `Ev.copy` is the (unobservable) cost of a staging move; `stuck`,
  `ub`, `trap` and `outOfFuel` end a run.

```lean
-- lean/ToyPacked/Semantics.lean:108-111
def obs (evs : List Ev) : List Ev :=
  evs.filter fun e => match e with
    | .copy _ => false
    | _ => true
-- lean/ToyPacked/Semantics.lean:114-117
def copies (evs : List Ev) : Nat :=
  (evs.filter fun e => match e with
    | .copy _ => true
    | _ => false).length
-- lean/ToyPacked/Semantics.lean:121
abbrev Crit := ShimKind → Nat → Nat → List Nat → Bool
-- lean/ToyPacked/Semantics.lean:125-128
structure Cfg where
  crit : Crit
  tmp : BodyId → Nat → Nat
  instr : BodyId → Nat → Bool
-- lean/ToyPacked/Semantics.lean:131-134
inductive Mode where
  | ideal
  | ref
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:137-140
structure Out where
  evs : List Ev
  ok : Bool
  deriving DecidableEq, Repr
-- lean/ToyPacked/Semantics.lean:143-147
def Out.andThen (o : Out) (f : Unit → Out) : Out :=
  if o.ok then
    let o' := f ()
    { evs := o.evs ++ o'.evs, ok := o'.ok }
  else o
-- lean/ToyPacked/Semantics.lean:152-159
def needsDrop (env : Env) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, t =>
    match (env.ty t).kind with
    | .scalar => false
    | .res _ => true
    | .box _ => true
    | .agg _ fs => fs.any fun f => needsDrop env fuel f
-- lean/ToyPacked/Semantics.lean:165-172
def AddrBlind (env : Env) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, t =>
    match (env.ty t).kind with
    | .scalar => true
    | .res obs => !obs
    | .box _ => true
    | .agg _ fs => fs.all fun f => AddrBlind env fuel f
-- lean/ToyPacked/Semantics.lean:175
def heapAddr (env : Env) (p : Nat) : Nat := env.align p
-- lean/ToyPacked/Semantics.lean:179-184
def refStep (m : Mode) (cfg : Cfg) (b : BodyId) (i n a : Nat) : Out :=
  match m with
  | .ideal => ⟨[], true⟩
  | .ref =>
    if n ∣ a then ⟨[], true⟩
    else if cfg.instr b i then ⟨[.trap b i], false⟩ else ⟨[.ub b i], false⟩
```

* `refStep`: the one alignment-relevant event. In the ideal semantics it always succeeds. In the
  reference semantics, an aligned reference creation produces no event; a misaligned one produces
  `trap` if the policy checks that (body, op) pair and `ub` otherwise (`refStep_pos`,
  `refStep_neg`, `refStep_trap`, `refStep_ideal`).
* `AddrBlind env fuel t`: no destructor reachable through *inline* sub-values of `t` (those that
  move with `t`) observes its address; a box is address-blind whatever its pointee
  (`addrBlind_pos`, `addrBlind_neg`, `addrBlind_box_pos`).
* `needsDrop`: does `t` have drop glue (`needsDrop_pos`, `needsDrop_neg`). Beyond the fuel bound
  the answer is `false`, so it is monotone in the fuel.

```lean
-- lean/ToyPacked/Semantics.lean:188-190
def shimExists (env : Env) : ShimKind → Nat → Bool
  | .boxFree, t => env.isBox t
  | _, _ => true
-- lean/ToyPacked/Semantics.lean:194-196
def callsShim (env : Env) (fuel : Nat) : ShimKind → Nat → Bool
  | .dropGlue, u => needsDrop env fuel u
  | k, u => shimExists env k u
-- lean/ToyPacked/Semantics.lean:205-212
def compStep (call : Nat → Nat → VName → Out) (env : Env) (fuel : Nat) (cfg : Cfg)
    (k : ShimKind) (b : BodyId) (i A t0 : Nat) (path : List Nat) (u a : Nat) (n : VName) : Out :=
  if callsShim env fuel k u then
    if cfg.crit k A t0 path then
      if (env.ty u).sized then (Out.mk [.copy n] true).andThen fun _ => call u (cfg.tmp b i) n
      else ⟨[.stuck b i], false⟩
    else call u a n
  else ⟨[], true⟩
-- lean/ToyPacked/Semantics.lean:215-216
def seqFields (fs : List Nat) (step : Nat → Nat → Out) : Out :=
  fs.zipIdx.foldl (fun acc p => acc.andThen fun _ => step p.1 p.2) ⟨[], true⟩
-- lean/ToyPacked/Semantics.lean:222-245
def runShim (m : Mode) (cfg : Cfg) (env : Env) (L : Layout) :
    Nat → ShimKind → Nat → Nat → VName → Out
  | 0, _, _, _, _ => ⟨[.outOfFuel], false⟩
  | fuel + 1, k, t, a, n =>
    if shimExists env k t then
    (refStep m cfg (.shim k t) 0 (env.align t) a).andThen fun _ =>
    match k, (env.ty t).kind with
    | .dropGlue, .scalar => ⟨[], true⟩
    | .dropGlue, .res obs => ⟨(if obs then [.addrObs n a] else []) ++ [.dtor n], true⟩
    | .dropGlue, .box p =>
      (if needsDrop env fuel p then
        runShim m cfg env L fuel .dropGlue p (heapAddr env p) (n.child 0)
      else ⟨[], true⟩).andThen fun _ => ⟨[.free n], true⟩
    | .dropGlue, .agg _ fs =>
      seqFields fs fun f j =>
        compStep (fun u a' n' => runShim m cfg env L fuel .dropGlue u a' n') env fuel cfg
          .dropGlue (.shim .dropGlue t) (j + 1) (env.align t) t [j] f (a + L t j) (n.child j)
    | .boxFree, _ => ⟨[.free n], true⟩
    | .clone, .agg _ fs =>
      seqFields fs fun f j =>
        compStep (fun u a' n' => runShim m cfg env L fuel .clone u a' n') env fuel cfg
          .clone (.shim .clone t) (j + 1) (env.align t) t [j] f (a + L t j) (n.child j)
    | .clone, _ => ⟨[.cloned n], true⟩
    else ⟨[], true⟩
-- lean/ToyPacked/Semantics.lean:248
def Prog.fuel (P : Prog) : Nat := P.env.length + 1
-- lean/ToyPacked/Semantics.lean:253-259
def Prog.place (P : Prog) (p : Place) : Option (Nat × Nat × Nat × Nat) :=
  if p.root < P.locals.length then
    let t0 := P.locals.getD p.root 0
    match resolve P.env P.layout t0 p.path with
    | some (u, o) => some (P.env.align t0, t0, u, P.frame.getD p.root 0 + o)
    | none => none
  else none
-- lean/ToyPacked/Semantics.lean:264-274
def srcStep (m : Mode) (cfg : Cfg) (P : Prog) (i : Nat) : Op → Out
  | .comp k p =>
    match P.place p with
    | some (A, t0, u, a) =>
      compStep (fun u' a' n' => runShim m cfg P.env P.layout P.fuel k u' a' n') P.env P.fuel cfg
        k .src i A t0 p.path u a ⟨.loc p.root, p.path⟩
    | none => ⟨[], true⟩
  | .moveOut _ => ⟨[], true⟩
  | .readUnaligned _ _ => ⟨[], true⟩
  | .rawRef t a => refStep m cfg .src i (P.env.align t) a
  | .rawCall k t a => runShim m cfg P.env P.layout P.fuel k t a ⟨.raw i, []⟩
-- lean/ToyPacked/Semantics.lean:277-278
def run (m : Mode) (cfg : Cfg) (P : Prog) : Out :=
  P.src.zipIdx.foldl (fun acc p => acc.andThen fun _ => srcStep m cfg P p.2 p.1) ⟨[], true⟩
```

* `shimExists`: drop glue and clone shims exist for every type id, box-free shims for box types
  (`shimExists_pos`, `shimExists_neg`); a raw call of a nonexistent shim is a no-op
  (`rawCall_missing_shim_noop`).
* `callsShim`: a drop of a type without drop glue and a free of a non-box type call no shim
  (`callsShim_pos`, `callsShim_neg`).
* `compStep`: a compiler operation that calls a shim either runs the shim on the place's address,
  or, if the criterion stages it, moves (copies) the value to the temporary `cfg.tmp b i` and runs
  the shim there, with no write-back; staging an unsized value records `stuck` (a compile-time
  rejection in the toy, not UB).
* `runShim`: op `0` of an existing shim creates the reference `&mut *self` (`&*self` for clone)
  from the incoming address; op `j + 1` of an aggregate's drop glue (clone shim) is the
  compiler-generated drop (clone) of field `j`, at `a + L t j`; a box's pointee is dropped at its
  heap address `heapAddr env p` whatever the box's address.
* `srcStep`: runs source op `i`; the policy is consulted at `rawRef` sites (`cfg.instr .src i`),
  and a `rawCall` site has no check of its own. `run` is the deterministic run of a program: one
  run per program and configuration.

```lean
-- lean/ToyPacked/Semantics.lean:282
def NoUB (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isUB = false
-- lean/ToyPacked/Semantics.lean:287
def NoShimUB (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isShimUB = false
-- lean/ToyPacked/Semantics.lean:297
def NoStuck (o : Out) : Prop := ∀ e, e ∈ o.evs → e.isStuck = false
```

* `NoUB r`: no `Ev.ub` in `r.evs`. It holds, among others, for runs with no misaligned reference
  creation and for runs that end with `trap`, `stuck` or `outOfFuel` before any UB event
  (`noUB_pos`, `noUB_neg`). `NoShimUB`: no UB event inside a shim (`noShimUB_pos`,
  `noShimUB_neg`). `NoStuck`: no `stuck` event (`noStuck_pos`, `noStuck_neg`).

#### Staging criteria, positions and hypotheses (`ToyPacked/Hyps.lean`)

```lean
-- lean/ToyPacked/Hyps.lean:28
def critNone : Crit := fun _ _ _ _ => false
-- lean/ToyPacked/Hyps.lean:31
def critAll : Crit := fun _ _ _ _ => true
-- lean/ToyPacked/Hyps.lean:35-38
def critExact (env : Env) (L : Layout) : Crit := fun _ A t0 path =>
  match resolve env L t0 path with
  | some (u, o) => !decide (env.align u ∣ Nat.gcd A o)
  | none => false
-- lean/ToyPacked/Hyps.lean:42-45
def critType (env : Env) : Crit := fun _ A t0 path =>
  match typeAt env t0 path with
  | some u => !decide (env.align u ∣ typeGA env t0 path A)
  | none => false
-- lean/ToyPacked/Hyps.lean:50-56
def critLeaf (env : Env) : Crit := fun _ _ t0 path =>
  match path.getLast?, typeAt env t0 path.dropLast with
  | some j, some par =>
    match (env.ty par).kind, env.field? par j with
    | .agg (some n) _, some f => !decide (env.align f ∣ n)
    | _, _ => false
  | _, _ => false
-- lean/ToyPacked/Hyps.lean:60
def dropsOnly (c : Crit) : Crit := fun k A t0 path => decide (k = .dropGlue) && c k A t0 path
-- lean/ToyPacked/Hyps.lean:63
def Cfg.unstaged (cfg : Cfg) : Cfg := { cfg with crit := critNone }
```

* `critExact env L`: stage iff the place's type alignment does not divide `gcd A o`, with `o` the
  total offset along the whole path (needs the concrete layout). Positive `critExact_pos`;
  negative `critExact_neg`.
* `critType env`: stage iff the place's type alignment does not divide `typeGA` (it uses the
  types, not the layout). Positive `critType_pos`; negative `critType_neg`; `critType_eq_critExact_packed2_align8`
  (both stage the `u64` of `packed(2) { u8, align(8) { u64 } }`, a combination the toy permits).
* `critLeaf env`: stage iff the immediate parent of the place is `packed(n)`, the place is its
  field `f`, and `env.align f` does not divide `n`; it ignores the base alignment and every
  ancestor other than the immediate parent. Positive `critLeaf_pos`; negative `critLeaf_neg`.
* `dropsOnly c`: `c` restricted to drops (`dropsOnly_pos`, `dropsOnly_neg`).

```lean
-- lean/ToyPacked/Hyps.lean:67-76
structure Pos where
  b : BodyId
  i : Nat
  k : ShimKind
  A : Nat
  t0 : Nat
  path : List Nat
  u : Nat
  o : Nat
  deriving DecidableEq, Repr
-- lean/ToyPacked/Hyps.lean:80-93
def srcPositions (P : Prog) : List Pos :=
  P.src.zipIdx.filterMap fun q =>
    match q.1 with
    | .comp k p =>
      if p.root < P.locals.length then
        match resolve P.env P.layout (P.locals.getD p.root 0) p.path with
        | some (u, o) =>
          if callsShim P.env P.fuel k u then
            some ⟨.src, q.2, k, P.env.align (P.locals.getD p.root 0),
              P.locals.getD p.root 0, p.path, u, o⟩
          else none
        | none => none
      else none
    | _ => none
-- lean/ToyPacked/Hyps.lean:98-106
def reach (env : Env) : Nat → ShimKind → Nat → List (ShimKind × Nat)
  | 0, _, _ => []
  | fuel + 1, k, t => (k, t) ::
    match k, (env.ty t).kind with
    | .dropGlue, .box p => if needsDrop env fuel p then reach env fuel .dropGlue p else []
    | .dropGlue, .agg _ fs =>
      fs.flatMap fun f => if needsDrop env fuel f then reach env fuel .dropGlue f else []
    | .clone, .agg _ fs => fs.flatMap fun f => reach env fuel .clone f
    | _, _ => []
-- lean/ToyPacked/Hyps.lean:111-117
def Op.shimRoot (P : Prog) : Op → Option (ShimKind × Nat)
  | .comp k p =>
    match P.place p with
    | some (_, _, u, _) => if callsShim P.env P.fuel k u then some (k, u) else none
    | none => none
  | .rawCall k t _ => if shimExists P.env k t then some (k, t) else none
  | _ => none
-- lean/ToyPacked/Hyps.lean:120-121
def reachableShims (P : Prog) : List (ShimKind × Nat) :=
  (P.src.filterMap (Op.shimRoot P)).flatMap fun r => reach P.env P.fuel r.1 r.2
-- lean/ToyPacked/Hyps.lean:127-134
def bodyPositions (env : Env) (L : Layout) (fuel : Nat) (k : ShimKind) (t : Nat) : List Pos :=
  match k with
  | .boxFree => []
  | _ =>
    (env.fields t).zipIdx.filterMap fun q =>
      if callsShim env fuel k q.1 then
        some ⟨.shim k t, q.2 + 1, k, env.align t, t, [q.2], q.1, L t q.2⟩
      else none
-- lean/ToyPacked/Hyps.lean:137-138
def shimPositions (P : Prog) : List Pos :=
  (reachableShims P).flatMap fun r => bodyPositions P.env P.layout P.fuel r.1 r.2
-- lean/ToyPacked/Hyps.lean:142
def positions (P : Prog) : List Pos := srcPositions P ++ shimPositions P
-- lean/ToyPacked/Hyps.lean:145
def Pos.staged (cfg : Cfg) (q : Pos) : Bool := cfg.crit q.k q.A q.t0 q.path
```

* `positions P`: the compiler-operation positions of the source body and of the shims a run of
  `P` may enter. `reach` follows, from each shim a source operation calls directly
  (`Op.shimRoot`: a compiler operation that calls a shim, or a raw call of an existing shim; a raw
  call of a shim that does not exist enters no shim), the drop glue of box pointees with drop
  glue, field drops of fields with drop glue, and field clones (`reach_pos`). It over-approximates
  the shims a run enters (it ignores early termination), and it contains no shim of a type the
  program never reaches: a program whose body is a single drop of `x` has no clone positions
  (`positions_progInPlace`), and an empty body has none (`positions_empty`). In a shim body the
  base alignment is the shim type's alignment.

```lean
-- lean/ToyPacked/Hyps.lean:149-150
def CritCovers (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → Misalignable q.A (P.env.align q.u) q.o → q.staged cfg = true
-- lean/ToyPacked/Hyps.lean:156-157
def StagedSized (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → (P.env.ty q.u).sized = true
-- lean/ToyPacked/Hyps.lean:164-165
def StagedAddrBlind (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → q.k = .dropGlue → AddrBlind P.env P.fuel q.u = true
-- lean/ToyPacked/Hyps.lean:171-172
def TempsAligned (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → P.env.align q.u ∣ cfg.tmp q.b q.i
-- lean/ToyPacked/Hyps.lean:178-179
def FrameAligned (P : Prog) : Prop :=
  ∀ x, x < P.locals.length → P.env.align (P.locals.getD x 0) ∣ P.frame.getD x 0
```

* `CritCovers P cfg`: every position whose place is misalignable is staged. Positive
  `critCovers_pos`; negative `critCovers_neg`.
* (H1) `StagedSized`, (H2) `StagedAddrBlind`, (H3) `TempsAligned`: about staged positions.
  Positives `stagedSized_pos`, `stagedAddrBlind_pos`, `tempsAligned_pos`; negatives
  `stagedSized_neg`, `stagedAddrBlind_neg`, `tempsAligned_neg`.
* `FrameAligned P`: every local's base address is aligned for its type (`frameAligned_pos`,
  `frameAligned_neg`).

```lean
-- lean/ToyPacked/Hyps.lean:184-189
def Op.isSafe : Op → Bool
  | .comp _ _ => true
  | .moveOut _ => true
  | .readUnaligned _ _ => true
  | .rawRef _ _ => false
  | .rawCall _ _ _ => false
-- lean/ToyPacked/Hyps.lean:192
def SafeSrc (P : Prog) : Prop := ∀ op, op ∈ P.src → op.isSafe = true
-- lean/ToyPacked/Hyps.lean:198-200
def Op.ptrAligned (env : Env) : Op → Bool
  | .rawCall k t a => !shimExists env k t || decide (env.align t ∣ a)
  | _ => true
-- lean/ToyPacked/Hyps.lean:204
def ClientPtrsAligned (P : Prog) : Prop := ∀ op, op ∈ P.src → op.ptrAligned P.env = true
-- lean/ToyPacked/Hyps.lean:210-212
def Op.isRawRef : Op → Bool
  | .rawRef _ _ => true
  | _ => false
-- lean/ToyPacked/Hyps.lean:215-216
def SrcRefsInstrumented (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ P.src.zipIdx → q.1.isRawRef = true → cfg.instr .src q.2 = true
-- lean/ToyPacked/Hyps.lean:226-229
def AlignRelevantCovered (env : Env) (I : BodyId → Nat → Bool) : Prop :=
  (∀ k t, t < env.length → env.align t ≠ 1 → shimExists env k t = true →
    I (.shim k t) 0 = true) ∧
  ((∃ t, t < env.length ∧ env.align t ≠ 1) → ∀ i, I .src i = true)
-- lean/ToyPacked/Hyps.lean:232-234
def toTrap (I : BodyId → Nat → Bool) : Ev → Ev
  | .ub b i => if I b i then .trap b i else .ub b i
  | e => e
```

* `SafeSrc`: no `rawRef`, no `rawCall` (`safeSrc_pos`, `safeSrc_neg`). `ClientPtrsAligned`: every
  raw call of an existing shim passes an address aligned for the shim's type
  (`clientPtrsAligned_pos`, `clientPtrsAligned_neg`); a raw call of a shim that does not exist is
  a no-op (`rawCall_missing_shim_noop`) and is admitted whatever its address
  (`rawCall_missing_shim_admitted`). `SrcRefsInstrumented`: every `rawRef` position is checked
  (`srcRefsInstrumented_pos`, `srcRefsInstrumented_neg`).
* `AlignRelevantCovered env I`: op `0` of every existing shim of every in-range type whose
  alignment is not 1 is checked, and, if such a type exists, every source position is checked.
  Positives `alignRelevantCovered_pos`, `alignRelevantCovered_trivial_align_one`,
  `alignRelevantCovered_existing_shims` (no checks in the nonexistent box-free shims of non-box
  types); negative `alignRelevantCovered_neg`.

#### Concrete instances (`ToyPacked/Instances.lean`)

```lean
-- lean/ToyPacked/Instances.lean:10
def tU8 : TyInfo := ⟨1, true, .scalar⟩
-- lean/ToyPacked/Instances.lean:12
def tR4 : TyInfo := ⟨4, true, .res false⟩
-- lean/ToyPacked/Instances.lean:14
def tR4obs : TyInfo := ⟨4, true, .res true⟩
-- lean/ToyPacked/Instances.lean:16
def tR2 : TyInfo := ⟨2, true, .res false⟩
-- lean/ToyPacked/Instances.lean:19
def envA : Env := [tU8, tR4, ⟨1, true, .agg (some 1) [0, 1]⟩]
-- lean/ToyPacked/Instances.lean:21
def LA : Layout := fun t j => if t = 2 ∧ j = 1 then 1 else 0
-- lean/ToyPacked/Instances.lean:24
def envObs : Env := [tU8, tR4obs, ⟨1, true, .agg (some 1) [0, 1]⟩]
-- lean/ToyPacked/Instances.lean:27
def envU : Env := [tU8, ⟨4, false, .res false⟩, ⟨1, false, .agg (some 1) [0, 1]⟩]
-- lean/ToyPacked/Instances.lean:30
def envB : Env := [tU8, tR4, ⟨8, true, .box 1⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]
-- lean/ToyPacked/Instances.lean:32
def LB : Layout := fun t j => if t = 3 ∧ j = 1 then 1 else 0
-- lean/ToyPacked/Instances.lean:35
def envQ : Env := [tU8, tR4, ⟨4, true, .agg none [1]⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]
-- lean/ToyPacked/Instances.lean:37
def LQ : Layout := fun t j => if t = 3 ∧ j = 1 then 1 else 0
-- lean/ToyPacked/Instances.lean:40
def envOuter : Env := [tU8, tR2, ⟨1, true, .agg (some 1) [0, 0, 1]⟩, ⟨2, true, .agg none [1, 2]⟩]
-- lean/ToyPacked/Instances.lean:42-43
def LOuter : Layout := fun t j =>
  if t = 2 ∧ j = 1 then 1 else if t = 2 ∧ j = 2 then 2 else if t = 3 ∧ j = 1 then 2 else 0
-- lean/ToyPacked/Instances.lean:46-47
def envP2 : Env := [tU8, ⟨8, true, .scalar⟩, ⟨8, true, .agg none [1]⟩,
  ⟨2, true, .agg (some 2) [0, 2]⟩]
-- lean/ToyPacked/Instances.lean:49
def LP2 : Layout := fun t j => if t = 3 ∧ j = 1 then 2 else 0
-- lean/ToyPacked/Instances.lean:53
def envW : Env := [⟨2, true, .scalar⟩, ⟨3, true, .agg none [0]⟩]
-- lean/ToyPacked/Instances.lean:55
def LW : Layout := fun t j => if t = 1 ∧ j = 0 then 2 else 0
-- lean/ToyPacked/Instances.lean:58
def envRP : Env := [tR4, ⟨4, true, .agg none [0]⟩]
-- lean/ToyPacked/Instances.lean:60
def LRP : Layout := fun t j => if t = 1 ∧ j = 0 then 1 else 0
-- lean/ToyPacked/Instances.lean:63
def envCyc : Env := [⟨2, true, .agg (some 1) [0]⟩]
-- lean/ToyPacked/Instances.lean:67
def envRev : Env := [⟨1, true, .agg (some 1) [1]⟩, tR4]
-- lean/ToyPacked/Instances.lean:70
def envBoxObs : Env := [tU8, tR4obs, ⟨8, true, .box 1⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]
-- lean/ToyPacked/Instances.lean:74
def envUnder : Env := [tR4, ⟨1, true, .agg none [0]⟩]
```

```lean
-- lean/ToyPacked/Instances.lean:78
def progInPlace : Prog := ⟨envA, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:81
def progObs : Prog := ⟨envObs, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:84
def progU : Prog := ⟨envU, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:87
def progMisFrame : Prog := ⟨[tR4], fun _ _ => 0, [0], [2], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:90
def progAligned : Prog := ⟨envA, LA, [1], [8], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:94
def progAlignedObs : Prog := ⟨envObs, LA, [1], [8], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:97
def progBoxObs : Prog := ⟨envBoxObs, LB, [3], [0], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:101
def progUnder : Prog := ⟨envUnder, fun _ _ => 0, [1], [1], [.comp .dropGlue ⟨0, [0]⟩]⟩
-- lean/ToyPacked/Instances.lean:105
def progEmptyU : Prog := ⟨envU, LA, [2], [0], []⟩
-- lean/ToyPacked/Instances.lean:113-114
def progBox : Prog := ⟨envB, LB, [3, 1, 3], [0, 8, 24],
  [.comp .dropGlue ⟨2, []⟩, .moveOut ⟨0, [1]⟩, .comp .boxFree ⟨0, [1]⟩, .comp .dropGlue ⟨1, []⟩]⟩
-- lean/ToyPacked/Instances.lean:117-118
def progBoxNoMove : Prog := ⟨envB, LB, [3, 1, 3], [0, 8, 24],
  [.comp .dropGlue ⟨2, []⟩, .comp .boxFree ⟨0, [1]⟩, .comp .dropGlue ⟨1, []⟩]⟩
-- lean/ToyPacked/Instances.lean:121
def progNested : Prog := ⟨envQ, LQ, [3], [0], [.comp .dropGlue ⟨0, [1, 0]⟩]⟩
-- lean/ToyPacked/Instances.lean:124
def progWholeQ : Prog := ⟨envQ, LQ, [3], [0], [.comp .dropGlue ⟨0, []⟩]⟩
-- lean/ToyPacked/Instances.lean:128
def progClient : Prog := ⟨envA, LA, [2], [0], [.rawCall .dropGlue 1 1]⟩
-- lean/ToyPacked/Instances.lean:136-137
def progEscape : Prog := ⟨envA, LA, [2, 2], [0, 8],
  [.comp .dropGlue ⟨0, []⟩, .rawCall .dropGlue 1 9]⟩
-- lean/ToyPacked/Instances.lean:142
def progUserRef : Prog := ⟨envA, LA, [2, 2], [0, 8], [.comp .dropGlue ⟨0, []⟩, .rawRef 1 9]⟩
-- lean/ToyPacked/Instances.lean:146-147
def progMixed : Prog := ⟨envA, LA, [2], [0],
  [.comp .dropGlue ⟨0, []⟩, .rawCall .dropGlue 1 4, .rawRef 1 1]⟩
-- lean/ToyPacked/Instances.lean:150
def instrNone : BodyId → Nat → Bool := fun _ _ => false
-- lean/ToyPacked/Instances.lean:152
def instrAll : BodyId → Nat → Bool := fun _ _ => true
-- lean/ToyPacked/Instances.lean:154
def instrSrc : BodyId → Nat → Bool := fun b _ => decide (b = .src)
-- lean/ToyPacked/Instances.lean:157
def cfgNone : Cfg := ⟨critNone, fun _ _ => 16, instrNone⟩
-- lean/ToyPacked/Instances.lean:159
def cfgType (env : Env) : Cfg := ⟨critType env, fun _ _ => 16, instrNone⟩
```

* `progBox` (over `envB`): locals `x : packed { u8, Box<R4> }` at address 0, `y : R4` at address
  8 and `z : packed { u8, Box<R4> }` at address 24; the body drops `z` (whose drop glue drops the
  box field `z.1` at offset 1, a misalignable drop), marks a deref-move out of the box field of
  `x` (`moveOut`, a no-op), frees the box through the field `x.1`, and drops `y`. `progBoxNoMove`
  omits the marker. Its positions are listed by `positions_progBox`.
* `progEscape` (over `envA`): locals `w, x : packed { u8, R4 }` at addresses 0 and 8; the body
  drops `w` (whose drop glue drops the field `w.1 : R4` at offset 1, a misalignable drop), then
  unsafe client code passes the raw address 9 (the address of `x.1`) to the drop glue of `R4`.
  `progUserRef` has the same locals and first operation, followed by a user-written `&*ptr` for
  `R4` at address 9. The positions of both are listed by `positions_progEscape`. `progClient` is
  the single client call with address 1 and no compiler operation; it is used by
  `completeness_witness`, `safeSrc_neg` and `clientPtrsAligned_neg`.

### Cards

Statement blocks are verbatim; "Unfolded (prose)" renderings are prose, not Lean terms. Every
tightness counterexample is stated in canonical form: all the other hypotheses hold and the
conclusion fails. Witness classes are given per row.
In every hypothesis ledger, `tight` means: the named counterexample theorem exhibits an
instance, in the stated witness class, satisfying all the other hypotheses of the theorem the
hypothesis belongs to, in which the conclusion fails. It does not mean that the hypothesis is
necessary outside that class.

#### `in-place` — dropping a packed field in place is UB although the source has no `&` (counterexample)

**Lean:** `inPlaceDrop_packedField_ub_though_source_has_no_ref`. **Kind:** counterexample.
**Tier:** T1 (folklore made precise: the motivating example of the documented packed-drop staging
design; see Prior art). **Depth:** shallow (one concrete run, by `decide`).

**Plain claim.** For the program `progInPlace` (one local `x : packed { u8, R4 }` at address 0,
whose source body is the single compiler drop of `x` and contains no raw-pointer operation, i.e.
`SafeSrc progInPlace`), with no staging and no checks (`cfgNone`), the ideal-semantics run destroys
the field `x.1`, while the reference-semantics run creates a misaligned `&mut` at op 0 of the drop
glue of `R4` (address 1, alignment 4): a UB event.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:18-21
theorem inPlaceDrop_packedField_ub_though_source_has_no_ref :
    SafeSrc progInPlace ∧
    (run .ideal cfgNone progInPlace).evs = [.dtor ⟨.loc 0, [1]⟩] ∧
    (run .ref cfgNone progInPlace).evs = [.ub (.shim .dropGlue 1) 0] := …
```

**Hypothesis ledger.** None (a concrete instance).

**Non-vacuity witness:** the theorem itself is the instance.

**Non-claims:** listed under Boundaries (*Non-claims*, card `in-place`); read them before relying on this card.

**Prior art.** rustc `add_moves_for_packed_drops.rs` module documentation (documented design);
`core::ptr::drop_in_place` documentation; RFC 1240 (the original analysis that a destructor is
passed a reference); Reference "Behavior considered undefined" (see Evidence, *Primary sources*).

**Design question.** Can a compiler-generated operation create a misaligned reference that no
source-level reference reveals? Answer in the toy: yes — for `progInPlace`, with no staging and no
checks, the compiler drop of `x` creates a misaligned `&mut` at op 0 of the drop glue of `R4`.

#### `staging` — aligned staging is sound and preserves observable traces (theorem)

**Lean:** `staged_noUB_and_obs_eq_ideal_of_frameAligned_safeSrc_covers_sized_addrBlind_alignedTemps`.
**Kind:** theorem. **Tier:** T1 (aligned staging is documented compiler practice; its soundness and
trace preservation in a toy model are made precise here). **Depth:** substantive (induction over
shim nesting, relating addresses in two runs; `runShim_staging`).

**Plain claim.** For every toy program `P` whose locals are at aligned addresses (`FrameAligned`)
and whose source body has no raw-pointer operation (`SafeSrc`), and every configuration `cfg` (with
any instrumentation policy) such that every compiler-operation position of the source body and of
the shims the program may enter (`positions`) whose place is misalignable is staged (`CritCovers`),
every staged value is sized (H1, `StagedSized`), no staged drop reaches an address-observing
destructor through inline sub-values (H2, `StagedAddrBlind`), and every staging temporary is aligned
for the staged type (H3, `TempsAligned`), each of these four conditions being required at every
position in `positions`, executed by a run or not: the staged program's reference-semantics run (the
run produced by `run`) has no UB event, and its observable trace (staging copies removed) equals the
ideal-semantics trace of the unstaged program.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:25-29
theorem staged_noUB_and_obs_eq_ideal_of_frameAligned_safeSrc_covers_sized_addrBlind_alignedTemps
    (P : Prog) (cfg : Cfg)
    (hframe : FrameAligned P) (hsafe : SafeSrc P) (hcov : CritCovers P cfg)
    (h1 : StagedSized P cfg) (h2 : StagedAddrBlind P cfg) (h3 : TempsAligned P cfg) :
    NoUB (run .ref cfg P) ∧ obs (run .ref cfg P).evs = obs (run .ideal cfg.unstaged P).evs := …
```

Unfolded (prose): `NoUB r` is "no `Ev.ub` in `r.evs`"; `obs` removes `Ev.copy` events;
`cfg.unstaged` replaces the criterion by `critNone`. Since the toy semantics is deterministic and
every run is finite (fuel-bounded), equality of observable traces is the trace-preservation
statement for this model.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hframe : FrameAligned P` | an unstaged place's address is its local's base address plus its offset | tight: `staging_fails_without_frameAligned` (a one-type environment `[tR4]`; one local of alignment 4 at address 2) |
| `hsafe : SafeSrc P` | raw client calls and user references are not compiler operations and are not staged | tight: `staging_fails_without_safeSrc` (three-type environment `envA`; `progEscape`: a staged misalignable drop, then one client call with a misaligned address) |
| `hcov : CritCovers P cfg` | every may-be-disaligned compiler operation is staged | tight: `staging_fails_without_critCovers` (`envA`; no staging, one packed field) |
| `h1 : StagedSized P cfg` | an unsized value cannot be moved to a temporary | tight: `staging_fails_without_stagedSized` (three-type environment `envU` with an unsized packed tail; the staged run is `stuck`) |
| `h2 : StagedAddrBlind P cfg` | a staged destructor runs at the temporary's address | tight: `staging_fails_without_stagedAddrBlind` (three-type environment `envObs`; an address-printing destructor prints 16 instead of 1) |
| `h3 : TempsAligned P cfg` | the reference created at the temporary is aligned for the staged type | tight: `staging_fails_without_tempsAligned` (`envA`; temporary at address 2 for alignment 4) |

Vacuity of the remaining hypotheses in these counterexamples: in `staging_fails_without_safeSrc`
a misalignable position is staged (the fourth conjunct of
`srcInstrumented_rawDropInPlace_misaligned_escapes`, about the same `progEscape` and
`cfgType envA`), and in the `stagedSized`, `stagedAddrBlind` and `tempsAligned` counterexamples
the negated hypothesis itself fails at a staged position; so `CritCovers` and the other H1–H3 hold
there at a staged position. In `staging_fails_without_critCovers` (no staging) H1–H3 hold
vacuously (no position is staged), and in `staging_fails_without_frameAligned` `CritCovers` and
H1–H3 hold vacuously (its single position is not misalignable and none is staged); both facts are
`critCovers_and_frameAligned_counterexamples_stage_nothing`. A local placed at a misaligned
address is not visible to a criterion that reads declared alignments.

H1 and H2 are used for the trace conjunct. The `NoUB` conjunct alone follows without them from
`noUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned_srcRefsInstrumented` and
`clientPtrsAligned_and_srcRefsInstrumented_of_safeSrc` (both proved; the derivation is a direct
application).

**Non-vacuity:** `staging_hyps_hold_progInPlace` (all six hold for `progInPlace` with
`cfgType envA`, and some position is staged); the conclusion on that instance is
`staging_conclusion_progInPlace`. Further instances: `staging_box_of_addrObs_pointee` (a packed
`Box<R4obs>` field is staged and the pointee prints its heap address 4 in both runs),
`staging_hyps_hold_dropsOnly_progInPlace` (drops-only staging of a drop-only program), and
`staging_hyps_hold_progEmptyU` (an unused local of a type with an unsized tail imposes nothing).

**Non-claims:** listed under Boundaries (*Non-claims*, card `staging`); read them before relying on this card.

**Prior art.** rustc `add_moves_for_packed_drops.rs` module documentation (the rewrite
`drop_temp = foo.data; drop(drop_temp)` between storage markers); `core::ptr::drop_in_place`
documentation ("For packed structs, this move is done automatically by the compiler."); `core::pin`
documentation (fields of a `#[repr(packed)]` type are moved to be dropped, so pinning is unusable
with it — the real-system counterpart of H2); Reference `destructors.md` (drop glue).

**Design question.** When is "move to an aligned temporary, then run the reference-taking
operation" a sound and behaviour-preserving lowering? Answer in the toy: for a program whose
locals are aligned and whose source body has no raw-pointer operation, when every misalignable
compiler-operation position (`positions`: the source body and the shims the program may enter) is
staged, every staged value is sized, no staged drop reaches an address-observing destructor through
inline sub-values, and every temporary is aligned for the staged type, each of these four
conditions holding at every position in `positions`, executed by a run or not, the staged
reference run (produced by `run`) has no UB event and the ideal observable trace of the unstaged
program.

#### `criterion-exact` — exact misalignability for a fixed layout (characterization)

**Lean:** `misalignable_iff_not_dvd_gcd`. **Kind:** characterization. **Tier:** T0 (elementary
arithmetic re-derived). **Depth:** shallow.

**Plain claim.** For all naturals `A`, `n`, `o` (including 0), some multiple `a` of `A` has `a + o`
not divisible by `n` iff `n` does not divide `gcd A o`. So, for a fixed layout, a place at total
offset `o` (summed along the whole path) from a base aligned to `A` may be disaligned for alignment
`n` exactly when `n ∤ gcd A o`.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Hyps.lean:12-13
theorem misalignable_iff_not_dvd_gcd (A n o : Nat) :
    Misalignable A n o ↔ ¬ n ∣ Nat.gcd A o := …
```

**Hypothesis ledger.** None.

**Non-vacuity:** `misalignable_pos`, `misalignable_neg`, `misalignable_align_zero`.

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-exact`); read them before relying on this card.

**Prior art.** Miri's `-Zmiri-symbolic-alignment-check` documentation (it checks the requested
alignment of the allocation and the offset into it, the quantity `Misalignable` quantifies over).

**Design question.** What is the exact staging condition when the layout is known? Answer in the
toy: for all naturals `A`, `n`, `o`, the place may be disaligned iff `n ∤ gcd A o`.

#### `criterion-type-sound` — the type-based criterion is sound (theorem)

**Lean:** `not_misalignable_of_powTwo_respectsPacking_dvd_typeGA`. **Kind:** theorem. **Tier:** T1.
**Depth:** shallow (induction over the path using divisibility of minima of powers of two;
`typeGA_props`, `resolve_dvd`).

**Plain claim.** If every alignment and every `packed(n)` parameter of the environment is a power of
two (`PowTwoAligns`), the layout respects packing (`RespectsPacking`), and the path from `t0`
resolves to a place of type `u` at offset `o`, then a place whose type alignment divides its
type-based guaranteed alignment `typeGA` (computed along the whole path from the base type's
alignment) cannot be misaligned from any base address aligned for the base type.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:69-73
theorem not_misalignable_of_powTwo_respectsPacking_dvd_typeGA (env : Env) (L : Layout)
    (hpow : PowTwoAligns env) (hpack : RespectsPacking env L)
    (t0 : Nat) (path : List Nat) (u o : Nat) (hres : resolve env L t0 path = some (u, o))
    (hdvd : env.align u ∣ typeGA env t0 path (env.align t0)) :
    ¬ Misalignable (env.align t0) (env.align u) o := …
```

Unfolded (prose): for powers of two, `n ∣ m` iff `n ≤ m` (standard; not proved here).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hpow : PowTwoAligns env` | a minimum of alignments divides each of them | tight: `typeGA_sound_fails_without_powTwo` (a two-type environment `envW`: base alignment 3, field alignment 2 at offset 2) |
| `hpack : RespectsPacking env L` | offsets are multiples of effective field alignments | tight: `typeGA_sound_fails_without_respectsPacking` (two-type environment `envRP`: an alignment-4 field at offset 1 of a non-packed struct) |
| `hres : resolve env L t0 path = some (u, o)` | ties `u` and `o` to the path; `typeGA` falls back to the base alignment on a path that leaves the types | tight: `typeGA_sound_fails_without_resolve` (three-type environment `envA`; the path `[0]` from `R4`) |
| `hdvd : env.align u ∣ typeGA env t0 path (env.align t0)` | the criterion's "no staging" verdict | tight: `typeGA_sound_fails_without_dvd` (`envA`; field 1 of `packed { u8, R4 }` at offset 1) |

**Non-vacuity:** `typeGA_sound_hyps_hold` (field 0 of `S = { R4 }` in `envQ`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-type-sound`); read them before relying on this card.

**Prior art.** Reference "The alignment modifiers" (`r[layout.repr.alignment.packed-fields]`;
`r[layout.repr.alignment.constraint-alignment]`: alignments are powers of two); MiniRust
`capped_tail_align` (`tail_align.min(packed_align)`, the same capping rule in an executable
specification).

**Design question.** Is a type-only "may be disaligned" check safe to use for staging decisions?
Answer in the toy: yes, when every alignment and `packed(n)` parameter is a power of two and the
layout respects packing: for a path that resolves to `u` at offset `o`, if `align u` divides
`typeGA` then the place cannot be misaligned.

#### `criterion-type-covers` — staging with `critType` meets `CritCovers` (theorem)

**Lean:** `critCovers_critType_of_powTwo_respectsPacking`. **Kind:** theorem. **Tier:** T1.
**Depth:** shallow (a glue corollary of `criterion-type-sound` via `pos_resolve`; it discharges
the `CritCovers` premise of `staging` and `sufficiency`).

**Plain claim.** For every toy program whose environment has power-of-two alignments and `packed(n)`
parameters and whose layout respects packing, the type-based criterion `critType` (with any
temporaries and policy) stages every compiler-operation position of the program (`positions`) whose
place is misalignable.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:86-88
theorem critCovers_critType_of_powTwo_respectsPacking (P : Prog) (tmp : BodyId → Nat → Nat)
    (I : BodyId → Nat → Bool) (hpow : PowTwoAligns P.env) (hpack : RespectsPacking P.env P.layout) :
    CritCovers P ⟨critType P.env, tmp, I⟩ := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hpow : PowTwoAligns P.env` | as in `criterion-type-sound` | tight: `critCovers_critType_fails_without_powTwo` (two-type environment `envW`; a clone of a field of an alignment-3 struct) |
| `hpack : RespectsPacking P.env P.layout` | as in `criterion-type-sound` | tight: `critCovers_critType_fails_without_respectsPacking` (two-type environment `envRP`; an alignment-4 field at offset 1) |

**Non-vacuity:** `critCovers_critType_hyps_hold` (`progNested`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-type-covers`); read them before relying on this card.

**Prior art.** As `criterion-type-sound`.

**Design question.** Can the coverage premise of `staging` and `sufficiency` be discharged by a
type-only check? Answer in the toy: yes, for environments with power-of-two alignments and
`packed(n)` parameters and layouts that respect packing.

#### `criterion-type-exact-over-layouts` — the type-based criterion is exact among packing-respecting layouts (characterization)

**Lean:** `exists_respectsPacking_layout_misalignable_iff_not_dvd_typeGA_of_noRepeatStep_powTwo`.
**Kind:** characterization. **Tier:** T1. **Depth:** substantive (the "if" direction builds a
layout per path: `typeGA_cases`, `resolve_indicator`).

**Plain claim.** If every alignment and every `packed(n)` parameter of the environment is a power of
two (`PowTwoAligns`), the path from `t0` follows the types to a place of type `u` (`typeAt`), and
the path takes no projection step `(t, j)` twice (`NoRepeatStep`), then some layout that respects
packing makes the place misalignable (from a base aligned for the base type) iff `u`'s alignment
does not divide the type-based guaranteed alignment `typeGA` computed over the whole projection
path.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:105-111
theorem exists_respectsPacking_layout_misalignable_iff_not_dvd_typeGA_of_noRepeatStep_powTwo
    (env : Env) (hpow : PowTwoAligns env)
    (t0 : Nat) (path : List Nat) (u : Nat) (hty : typeAt env t0 path = some u)
    (hsteps : NoRepeatStep env t0 path) :
    (∃ L : Layout, RespectsPacking env L ∧ ∃ o, resolve env L t0 path = some (u, o) ∧
        Misalignable (env.align t0) (env.align u) o) ↔
      ¬ env.align u ∣ typeGA env t0 path (env.align t0) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hpow : PowTwoAligns env` | soundness direction; `typeGA` divides the base alignment | tight: `typeGA_exact_fails_without_powTwo` (two-type environment `envW`, alignments 3 and 2) |
| `hty : typeAt env t0 path = some u` | the path follows the types to `u`; `typeGA` falls back to the base alignment otherwise | tight: `typeGA_exact_fails_without_typeAt` (three-type environment `envA`; the path `[99]`) |
| `hsteps : NoRepeatStep env t0 path` | each step's offset can be chosen independently | tight: `typeGA_exact_fails_without_noRepeatStep` (one-type cyclic environment `envCyc`, `C = packed { C }` of alignment 2, path `[0, 0]`: the offset `2 * L 0 0` is never misaligned for 2, yet `typeGA = 1`) |

`NoRepeatStep` holds for every path when field type ids decrease
(`noRepeatStep_of_fieldIdsDecreasing`), and for a particular path even in an environment whose
aggregates contain themselves (`noRepeatStep_cyc_short`).

**Non-vacuity:** `typeGA_exact_hyps_hold` (`x.1.0` of `Q`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-type-exact-over-layouts`); read them before relying on this card.

**Prior art.** Reference "The alignment modifiers"; MiniRust `capped_tail_align`.

**Design question.** Which places need staging, for a criterion that sees the type environment
and the path but not concrete offsets? Answer in the toy: when every alignment and `packed(n)`
parameter is a power of two, for a path that follows the types to `u` and repeats no projection
step, some packing-respecting layout makes the place misalignable iff `align u` does not divide
`typeGA`.

#### `criterion-leaf-misses` — a leaf-only criterion misses nested fields and fields of under-aligned parents (counterexample)

**Lean:** `leafOnlyCrit_misses_nested_field`, `leafOnlyCrit_misses_one_step_underaligned_parent`.
**Kind:** counterexample. **Tier:** T1. **Depth:** shallow (concrete runs, by `decide`).

**Plain claim.** (i) For the compiler drop of the nested place `x.1.0` (the `R4` field of a
non-packed `S` stored in `Q = packed { u8, S }`), the leaf-only criterion `critLeaf` (stage iff the
immediate parent is `packed(n)` and the field's alignment does not divide `n`) does not stage, the
place is misalignable, and the unstaged drop is UB; the type-based criterion stages it and the run
has no UB. (ii) In the two-type environment `envUnder`, where the struct `S = { R4 }` declares
alignment 1, below its field's alignment 4 (the toy permits this), with power-of-two alignments and
the zero layout (which respects packing), for a local `s : S` at the aligned address 1, the compiler
drop of the one-step place `s.0` is not staged by `critLeaf` and is UB; `critType` stages it and the
run has no UB.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:254-259
theorem leafOnlyCrit_misses_nested_field :
    critLeaf envQ .dropGlue 1 3 [1, 0] = false ∧ Misalignable 1 (envQ.align 1) 1 ∧
    (run .ref ⟨critLeaf envQ, fun _ _ => 16, instrNone⟩ progNested).evs =
      [.ub (.shim .dropGlue 1) 0] ∧
    critType envQ .dropGlue 1 3 [1, 0] = true ∧
    NoUB (run .ref (cfgType envQ) progNested) := …
-- lean/ToyPacked/Counterexamples.lean:267-273
theorem leafOnlyCrit_misses_one_step_underaligned_parent :
    PowTwoAligns envUnder ∧ RespectsPacking envUnder (fun _ _ => 0) ∧ FrameAligned progUnder ∧
    critLeaf envUnder .dropGlue 1 1 [0] = false ∧
    (run .ref ⟨critLeaf envUnder, fun _ _ => 16, instrNone⟩ progUnder).evs =
      [.ub (.shim .dropGlue 0) 0] ∧
    critType envUnder .dropGlue 1 1 [0] = true ∧
    NoUB (run .ref (cfgType envUnder) progUnder) := …
```

**Hypothesis ledger.** None (concrete).

**Non-vacuity:** the two theorems are concrete instances (no hypotheses).

**Positive control:** the `critType` conjuncts of both theorems, and
`leafOnlyCrit_stages_field_in_whole_drop` (`critLeaf` itself stages the field `S` in the
whole-value drop of `x`, and that run has no UB).

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-leaf-misses`); read them before relying on this card.

**Prior art.** None specific.

**Design question.** Does a criterion that looks at the immediate parent alone stage every
misalignable place? Answer in the toy: no — `critLeaf` fails to stage a misalignable place in each
of the two instances above (a nested field of a non-packed struct inside a packed field, and a
field of a parent whose declared alignment is below the field's).

#### `criterion-type-overstages-fixed-layout` — the type-based criterion is not exact for a fixed layout (counterexample)

**Lean:** `typeCrit_overstages_fixed_layout`. **Kind:** counterexample. **Tier:** T1. **Depth:**
shallow (by `decide`).

**Plain claim.** In the four-type environment `envOuter` (with power-of-two alignments) and the
packing-respecting layout `LOuter`, the type-based criterion stages the place `Outer.1.2` although
that place (total offset 4 from a base aligned to 2, type alignment 2) can never be misaligned,
while the offset-aware criterion `critExact` does not stage it.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:288-292
theorem typeCrit_overstages_fixed_layout :
    PowTwoAligns envOuter ∧ RespectsPacking envOuter LOuter ∧
    critType envOuter .dropGlue 2 3 [1, 2] = true ∧
    critExact envOuter LOuter .dropGlue 2 3 [1, 2] = false ∧
    resolve envOuter LOuter 3 [1, 2] = some (1, 4) ∧ ¬ Misalignable 2 (envOuter.align 1) 4 := …
```

**Hypothesis ledger.** None (concrete).

**Non-vacuity:** the theorem is a concrete instance (no hypotheses).

**Positive control:** `critExact` on the same place (fourth conjunct).

**Non-claims:** listed under Boundaries (*Non-claims*, card `criterion-type-overstages-fixed-layout`); read them before relying on this card.

**Prior art.** `core::pin` documentation: the compiler "might even" move fields of a
`#[repr(packed)]` type "that happen to be sufficiently aligned".

**Design question.** Is the type-based criterion exact for a known layout? Answer in the toy: no —
in `envOuter` with `LOuter` it stages a place that can never be misaligned.

#### `overstaging-aligned` — over-staging an aligned place: one copy when address-blind, a changed trace when address-observing (counterexample)

**Lean:** `overstaging_aligned_addrObs_changes_trace`; positive control
`overstaging_aligned_place_sound_costs_copy`. **Kind:** counterexample. **Tier:** T1. **Depth:**
shallow (by `decide`).

**Plain claim.** (i) For the local `y : R4obs` at the aligned address 8 (`progAlignedObs`, whose
destructor prints its address), staging its drop with `critAll` into a temporary at address 16 gives
a reference run with no UB event whose observable trace prints 16, while the ideal run of the
unstaged program prints 8. (ii) Positive control: for the local `y : R4` at the aligned address 8
(`progAligned`), the same over-staging gives a run with no UB event whose observable trace equals
the ideal trace, with exactly one staging copy where the ideal run has none.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:300-304
theorem overstaging_aligned_addrObs_changes_trace :
    NoUB (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAlignedObs) ∧
    obs (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAlignedObs).evs =
      [.addrObs ⟨.loc 0, []⟩ 16, .dtor ⟨.loc 0, []⟩] ∧
    obs (run .ideal cfgNone progAlignedObs).evs = [.addrObs ⟨.loc 0, []⟩ 8, .dtor ⟨.loc 0, []⟩] := …
-- lean/ToyPacked/Counterexamples.lean:310-315
theorem overstaging_aligned_place_sound_costs_copy :
    NoUB (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned) ∧
    obs (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned).evs =
      obs (run .ideal cfgNone progAligned).evs ∧
    copies (run .ref ⟨critAll, fun _ _ => 16, instrNone⟩ progAligned).evs = 1 ∧
    copies (run .ideal cfgNone progAligned).evs = 0 := …
```

**Hypothesis ledger.** None (concrete).

**Non-vacuity:** the two theorems are concrete instances (no hypotheses).

**Positive control:** `overstaging_aligned_place_sound_costs_copy`.

**Non-claims:** listed under Boundaries (*Non-claims*, card `overstaging-aligned`); read them before relying on this card.

**Prior art.** `core::pin` documentation (fields of a `#[repr(packed)]` type may be moved to be
dropped even when sufficiently aligned, so pinning is unusable with it).

**Design question.** What does over-staging an aligned place cost? Answer in the toy: in
`progAligned`, one staging copy and no observable change; in `progAlignedObs`, whose destructor
observes its address, a changed observable trace.

#### `box-free` — staging the moved-out value but not the free of the box field leaves UB (counterexample)

**Lean:** `boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok`, `progBox_moveOut_irrelevant`.
**Kind:** counterexample. **Tier:** T1. **Depth:** shallow (by `decide`).

**Plain claim.** In the toy, where freeing a box is a shim that creates `&mut` to the box field at
its op 0 and `moveOut` is a no-op marker, consider `progBox` over `envB` (the drop of a local
`z : packed { u8, Box<R4> }`, then a marker for a deref-move out of the owning pointer stored at
offset 1 of a local `x : packed { u8, Box<R4> }`, then the free of that pointer through the field
`x.1`, then the drop of the local `y : R4`). The configuration `cfgDropsOnly` (type-based staging
restricted to drops, temporaries at address 16) stages every misalignable drop position of
`progBox`; such a position exists (the drop of `z.1` inside the drop glue of
`packed { u8, Box<R4> }`); and a misalignable free position exists that `cfgDropsOnly` does not
stage (the free of `x.1`; `positions_progBox` lists exactly four positions of `progBox`). The
reference run under `cfgDropsOnly` copies `z.1` to the temporary, drops it there (the pointee's
destructor, then the free of `z.1`), and then creates a misaligned `&mut` to the box field `x.1` at
op 0 of the box-free shim: a UB event. Staging the box field itself into an aligned temporary before
freeing (`cfgType envB`) gives a run without UB whose observable trace equals the ideal trace of the
unstaged program (`cfgNone`). Removing the `moveOut` marker changes neither run.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:331-342
theorem boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok :
    (∀ q, q ∈ positions progBox → q.k = .dropGlue →
      Misalignable q.A (envB.align q.u) q.o → q.staged cfgDropsOnly = true) ∧
    (∃ q, q ∈ positions progBox ∧ q.k = .dropGlue ∧
      Misalignable q.A (envB.align q.u) q.o ∧ q.staged cfgDropsOnly = true) ∧
    (∃ q, q ∈ positions progBox ∧ q.k = .boxFree ∧
      Misalignable q.A (envB.align q.u) q.o ∧ q.staged cfgDropsOnly = false) ∧
    (run .ref cfgDropsOnly progBox).evs =
      [.copy ⟨.loc 2, [1]⟩, .dtor ⟨.loc 2, [1, 0]⟩, .free ⟨.loc 2, [1]⟩,
        .ub (.shim .boxFree 2) 0] ∧
    NoUB (run .ref (cfgType envB) progBox) ∧
    obs (run .ref (cfgType envB) progBox).evs = obs (run .ideal cfgNone progBox).evs := …
-- lean/ToyPacked/Counterexamples.lean:347-349
theorem progBox_moveOut_irrelevant :
    (run .ref cfgDropsOnly progBox).evs = (run .ref cfgDropsOnly progBoxNoMove).evs ∧
    (run .ref (cfgType envB) progBox).evs = (run .ref (cfgType envB) progBoxNoMove).evs := …
```

**Hypothesis ledger.** None (concrete).

**Non-vacuity:** the theorems are concrete instances (no hypotheses). The second conjunct of
`boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok` exhibits a misalignable drop position of
`progBox` that `cfgDropsOnly` stages, so its first conjunct does not hold vacuously.

**Positive control:** the last two conjuncts of the first theorem (`cfgType envB`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `box-free`); read them before relying on this card.

**Prior art.** https://github.com/rust-lang/rust/issues/164561 (context; an open issue, not
relied on as normative); Reference `r[undefined.validity.reference-box]`.

**Design question.** Is staging the moved-out value enough when moving out of an owning pointer
stored in a packed field? Answer in the toy: in `progBox`, with frees modelled as reference-taking
shims, staging every misalignable drop (at least one such drop is staged) and no free leaves a UB event in
the box-free shim, while also staging the box field does not; other lowerings of the free are not
examined.

#### `completeness` — instrumentation completeness including synthesized shims (characterization)

**Lean:** `noUB_forall_progs_iff_alignRelevantCovered`. **Kind:** characterization. **Tier:** T1
(a recorded search found no mechanized statement of this form; the result is close to the
definitions, so no novelty is claimed). **Depth:** shallow (the "if" direction is an invariant
over shim nesting, `runShim_noUB_of_covered`; the "only if" direction is constructive: one client
call or one user reference per uncovered operation).

**Plain claim.** Fix an environment, a layout, a staging criterion, temporaries and an
instrumentation policy `I : BodyId → Nat → Bool`, chosen before the program. Over the class of all
programs over that environment and layout — which contains programs whose unsafe client code passes
arbitrary raw addresses to any shim, programs with user-written reference creations at any source
position, and programs whose locals sit at any address — every run produced by `run` in the
reference semantics has no UB event iff `I` checks op 0 of every existing shim (drop glue and clone
of every type, box free of every box type) of every in-range type whose alignment is not 1, and, if
some in-range type's alignment is not 1, every source position.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:150-153
theorem noUB_forall_progs_iff_alignRelevantCovered (env : Env) (L : Layout) (crit : Crit)
    (tmp : BodyId → Nat → Nat) (I : BodyId → Nat → Bool) :
    (∀ P : Prog, P.env = env → P.layout = L → NoUB (run .ref ⟨crit, tmp, I⟩ P)) ↔
      AlignRelevantCovered env I := …
```

**Hypothesis ledger.** None (all parameters are universally quantified).

**Non-vacuity:** `completeness_witness` (checks everywhere cover `envA`; on `progClient` the run
traps), `alignRelevantCovered_existing_shims` (no checks in nonexistent shims), and
`alignRelevantCovered_neg` / `srcInstrumented_rawDropInPlace_misaligned_escapes` for a policy
failing both sides.

**Non-claims:** listed under Boundaries (*Non-claims*, card `completeness`); read them before relying on this card.

**Prior art.** Miri documentation (it detects "Not sufficiently aligned memory accesses and
references"; `-Zmiri-symbolic-alignment-check`; `-Zmiri-disable-alignment-check`); rustc
`-Zub-checks` documentation (runtime UB checks "generated on a best-effort basis"; cited for its
documented behaviour, with no claim about which bodies are checked); Clang UndefinedBehaviorSanitizer
`-fsanitize=alignment` ("Use of a misaligned pointer or creation of a misaligned reference") with
`-fsanitize-trap`; Song et al., "SoK: Sanitizing for Security" (systematizes sanitizer coverage).
No mechanized completeness statement covering synthesized shims was found.

**Design question.** When does dynamic alignment-check instrumentation, given as a fixed set of
(body, op) pairs, prevent every UB event over all programs over an environment and layout? Answer
in the toy: iff it checks op 0 of every existing shim of every in-range type whose alignment is not
1 and, if such a type exists, every source position.

#### `precision` — checks trap at UB sites and nowhere else (theorem)

**Lean:** `run_eq_uninstrumented_map_toTrap`. **Kind:** theorem. **Tier:** T0 (the definitional
property of a check that traps iff the address is misaligned, lifted to runs; no novelty).
**Depth:** shallow (induction over the run; `runShim_precision`).

**Plain claim.** For every toy program and configuration, the instrumented reference-semantics run
produced by `run` equals the uninstrumented run with each UB event at a checked position relabelled
as a trap; so a check traps only at a checked position where the uninstrumented run has a UB event
(a misaligned reference creation), never at an aligned reference creation.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:222-224
theorem run_eq_uninstrumented_map_toTrap (P : Prog) (cfg : Cfg) :
    (run .ref cfg P).evs = (run .ref { cfg with instr := fun _ _ => false } P).evs.map
      (toTrap cfg.instr) := …
```

**Hypothesis ledger.** None.

**Non-vacuity:** `completeness_witness` (`progClient`: `[trap …]` vs `[ub …]`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `precision`); read them before relying on this card.

**Prior art.** Miri `-Zmiri-symbolic-alignment-check` documentation (documents false positives of a
stricter check); Clang UBSan `-fsanitize-trap=alignment`.

**Design question.** Can an alignment check of this kind reject a run that the uninstrumented
semantics accepts? Answer in the toy: no — the instrumented run differs from the uninstrumented run
exactly by relabelling UB events at checked positions as traps.

#### `escape` — UB escapes through an uninstrumented shim (counterexample)

**Lean:** `srcInstrumented_rawDropInPlace_misaligned_escapes`. **Kind:** counterexample.
**Tier:** T1. **Depth:** shallow (one concrete run, by `decide`).

**Plain claim.** Consider `progEscape` over `envA` (locals `w, x : packed { u8, R4 }` at addresses 0
and 8; the compiler drop of `w`, then an unsafe client call that passes the raw address 9 — the
address of `x.1`, as `&raw mut x.1` would produce; the toy passes the literal address — to the drop
glue of `R4`). Take checks at every source position and no check at op 0 of the drop glue of `R4`
(`instrSrc`), and type-based staging (`critType envA`, temporaries at address 16), which stages
every misalignable compiler-operation position of `progEscape`; such a position exists (the drop of
`w.1` inside the drop glue of `packed { u8, R4 }`; `positions_progEscape` lists exactly two
positions of `progEscape`). The reference run copies `w.1` to the temporary and runs its destructor
there, and then the client call makes the drop glue of `R4` create a misaligned `&mut` at its op 0:
a UB event with no trap. With checks everywhere (`instrAll`) the same run ends with a trap at that
operation instead.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Counterexamples.lean:378-386
theorem srcInstrumented_rawDropInPlace_misaligned_escapes :
    (∀ i, instrSrc .src i = true) ∧ instrSrc (.shim .dropGlue 1) 0 = false ∧
    CritCovers progEscape (cfgType envA) ∧
    (∃ q, q ∈ positions progEscape ∧ Misalignable q.A (envA.align q.u) q.o ∧
      q.staged (cfgType envA) = true) ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrSrc⟩ progEscape).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .ub (.shim .dropGlue 1) 0] ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrAll⟩ progEscape).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .trap (.shim .dropGlue 1) 0] := …
```

**Hypothesis ledger.** None (concrete).

**Non-vacuity:** the theorem is a concrete instance (no hypotheses). Its fourth conjunct exhibits a
misalignable compiler-operation position of `progEscape` that `critType envA` stages, so its third
conjunct (`CritCovers`) does not hold vacuously.

**Positive control:** the last conjunct (`instrAll`: the same program traps), and
`completeness_witness` (checks everywhere trap on `progClient`).

**Non-claims:** listed under Boundaries (*Non-claims*, card `escape`); read them before relying on this card.

**Prior art.** RFC 2582 (`&raw` exists so that a raw pointer to a packed field can be created
without an intermediate unaligned reference); Reference `r[undefined.misaligned.raw]`;
`core::ptr::drop_in_place` safety section ("`to_drop` must be properly aligned").

**Design question.** Are checks at source positions enough? Answer in the toy: no — in
`progEscape`, with checks at every source position, none in the drop glue of `R4`, and covering
type-based staging (which stages a misalignable drop), the run has a UB event in the shim;
`sufficiency` gives conditions under which the run has no UB event whatever the shims check.

#### `sufficiency` — no UB without shim checks, under staging, aligned client pointers and source checks (theorem)

**Lean:** `noUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned_srcRefsInstrumented`.
**Kind:** theorem. **Tier:** T1. **Depth:** shallow (a source-level case split on top of the
shim invariant `runShim_noUB_of_aligned` shared with `sufficiency-shim`).

**Plain claim.** For every toy program whose locals are at aligned addresses (`FrameAligned`), if
(a) every compiler-operation position of the program (`positions`: the source body and the shims the
program may enter, executed by a run or not) whose place is misalignable is staged (`CritCovers`)
into a temporary aligned for the staged type (`TempsAligned`), (b) every raw address that unsafe
client code passes to an existing shim is aligned for the shim's type (`ClientPtrsAligned`), and (c)
every user-written reference creation in the source body is checked (`SrcRefsInstrumented`), then
the reference-semantics run produced by `run` has no UB event, whatever checks the shims have (the
policy may check no shim). The run may still end with `trap`, `stuck` or `outOfFuel`.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:252-255
theorem noUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned_srcRefsInstrumented
    (P : Prog) (cfg : Cfg) (hframe : FrameAligned P) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (hb : ClientPtrsAligned P) (hc : SrcRefsInstrumented P cfg) :
    NoUB (run .ref cfg P) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hframe : FrameAligned P` | an unstaged place's address is its local's base address plus its offset | tight: `sufficiency_fails_without_frameAligned` (one-type environment `[tR4]`; one local at address 2) |
| `ha : CritCovers P cfg` (a) | compiler operations hand shims aligned addresses | tight: `sufficiency_fails_without_critCovers` (four-type environment `envB`; the `box-free` program `progBox`: a staged misalignable drop, then an unstaged free) |
| `ht : TempsAligned P cfg` (a) | staged operations hand shims aligned addresses | tight: `sufficiency_fails_without_tempsAligned` (three-type environment `envA`; temporary at address 2) |
| `hb : ClientPtrsAligned P` (b) | client calls hand shims aligned addresses | tight: `sufficiency_fails_without_clientPtrsAligned` (`envA`; the `escape` program `progEscape`: a staged misalignable drop, then a client call with a misaligned address) |
| `hc : SrcRefsInstrumented P cfg` (c) | user references are caught in the source body | tight: `sufficiency_fails_without_srcRefsInstrumented` (`envA`; `progUserRef`: a staged misalignable drop, then one unchecked `&*ptr` at address 9) |

Vacuity of the remaining hypotheses in these counterexamples: in the `critCovers`,
`clientPtrsAligned` and `srcRefsInstrumented` counterexamples a misalignable position is staged
(the second conjunct of `boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok`, the fourth conjunct
of `srcInstrumented_rawDropInPlace_misaligned_escapes` — `cfgSrc` has the criterion
`critType envA` — and `progUserRef_stages_misalignable_position`), and in the `tempsAligned`
counterexample the negated hypothesis fails at a staged position; so `CritCovers` and
`TempsAligned` hold there at a staged position. In `sufficiency_fails_without_frameAligned`
`CritCovers` and `TempsAligned` hold vacuously (its single position is not misalignable and none
is staged: `critCovers_and_frameAligned_counterexamples_stage_nothing`).

**Non-vacuity:** `sufficiency_hyps_hold_progMixed` (all three operations execute: a staged field
drop, an aligned client call, and a user reference that traps).

**Non-claims:** listed under Boundaries (*Non-claims*, card `sufficiency`); read them before relying on this card.

**Prior art.** As `staging` (staging) and `completeness` (checking).

**Design question.** When can shim checks be omitted? Answer in the toy: for a program whose locals
are aligned, when every misalignable compiler-operation position (`positions`: the source body and
the shims the program may enter, executed by a run or not) is staged into a temporary aligned for
the staged type, every raw address passed to an existing shim is aligned for the shim's type, and
every user reference creation in the source body is checked, the reference-semantics run produced
by `run` has no UB event whatever the shims check.

#### `sufficiency-shim` — no UB inside shims under (a) and (b) (theorem)

**Lean:** `noShimUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned`. **Kind:** theorem.
**Tier:** T1. **Depth:** substantive (induction over shim nesting: `runShim_noUB_of_aligned`).

**Plain claim.** For every toy program whose locals are at aligned addresses (`FrameAligned`), if
every compiler-operation position of the program (`positions`: the source body and the shims the
program may enter, executed by a run or not) whose place is misalignable is staged (`CritCovers`)
into a temporary aligned for the staged type (`TempsAligned`), and every raw address that client
code passes to an existing shim is aligned for the shim's type (`ClientPtrsAligned`), then the
reference-semantics run produced by `run` has no UB event inside a shim. The run may still have a UB
event in the source body and may end with `trap`, `stuck` or `outOfFuel`.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:273-276
theorem noShimUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned
    (P : Prog) (cfg : Cfg) (hframe : FrameAligned P) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) (hb : ClientPtrsAligned P) :
    NoShimUB (run .ref cfg P) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `hframe : FrameAligned P` | as in `sufficiency` | tight: `sufficiency_fails_without_frameAligned` (one-type environment `[tR4]`; its last conjunct refutes `NoShimUB`) |
| `ha : CritCovers P cfg` | as in `sufficiency` | tight: `sufficiency_fails_without_critCovers` (four-type environment `envB`; `progBox`) |
| `ht : TempsAligned P cfg` | as in `sufficiency` | tight: `sufficiency_fails_without_tempsAligned` (three-type environment `envA`) |
| `hb : ClientPtrsAligned P` | as in `sufficiency` | tight: `sufficiency_fails_without_clientPtrsAligned` (`envA`; `progEscape`) |

Each of these theorems states the other three hypotheses (and `SrcRefsInstrumented`) and refutes
`NoShimUB` in its last conjunct. Vacuity of the remaining hypotheses is as recorded for
`sufficiency`.

**Non-vacuity:** `sufficiency_hyps_hold_progMixed`.

**Non-claims:** listed under Boundaries (*Non-claims*, card `sufficiency-shim`); read them before relying on this card.

**Prior art.** As `sufficiency`.

**Design question.** Which premises protect shims specifically? Answer in the toy: for a program
whose locals are aligned, when every misalignable compiler-operation position (`positions`: the
source body and the shims the program may enter, executed by a run or not) is staged into a
temporary aligned for the staged type and every raw address passed to an existing shim is aligned
for the shim's type, the reference-semantics run produced by `run` has no UB event inside a shim.

#### `no-stuck` — sized staged values never get stuck (theorem)

**Lean:** `noStuck_of_stagedSized`. **Kind:** theorem. **Tier:** T1. **Depth:** shallow (an
instance of the generic shim invariant that the other shim results also instantiate, relating
run-time operations to `positions` through `Reached`: `runShim_noStuck`; no alignment
arithmetic).

**Plain claim.** For every toy program and configuration, if every staged position of the program
(of its source body and of the shims it may enter, `positions`, executed by a run or not) has a
sized type (H1, `StagedSized`), then the run produced by `run`, in either semantics, has no `stuck`
event.

Basis: execution (Lean kernel check).

```lean
-- lean/ToyPacked/Results.lean:298-299
theorem noStuck_of_stagedSized (m : Mode) (P : Prog) (cfg : Cfg) (h1 : StagedSized P cfg) :
    NoStuck (run m cfg P) := …
```

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
| :-- | :-- | :-- |
| `h1 : StagedSized P cfg` | `compStep` emits `stuck` when it stages a value of an unsized type | tight: `noStuck_fails_without_stagedSized` (three-type environment `envU`; the unsized packed tail is staged) |

**Non-vacuity:** `noStuck_hyps_hold_progInPlace` (a position is staged and every staged position is
sized).

**Non-claims:** listed under Boundaries (*Non-claims*, card `no-stuck`); read them before relying on this card.

**Prior art.** None specific.

**Design question.** Under which condition does staging never get stuck? Answer in the toy: when
every staged position of the program (`positions`: its source body and the shims it may enter,
executed by a run or not) has a sized type, the run produced by `run`, in either semantics, has no
`stuck` event.

### Modeling bridges

Basis: derived (modeling bridge). Each bullet relates the toy to documented behaviour of a real
system by reading the cited text; no bullet is a theorem, and no correspondence is proved
(model–system relation: none proved). Pinned sources and line ranges are listed under Evidence,
*Primary sources*.

* **Packed fields and references.** The Rust Reference states that `&`/`&mut` on a place requires
  the alignment of the field type and that a reference must be aligned
  (`r[undefined.misaligned.reference]`, `src/behavior-considered-undefined.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:93-94`;
  `r[undefined.validity.reference-box]`, same file `:151-152`), that references to unaligned
  fields of packed types are a compiler error (`r[undefined.misaligned.packed]`, same file
  `:96-97`), and that `&raw const`/`&raw mut` on a place based on a misaligned pointer is allowed
  (`r[undefined.misaligned.raw]`, same file `:90-91`). E0793's error-index entry documents the
  compile-time error for references to insufficiently aligned packed fields. The toy's `refStep`
  (UB iff misaligned) and the legality of client raw pointers mirror these documented rules;
  `Misalignable` and `typeGA` correspond to "may be insufficiently aligned" with the packed-field
  positioning rule of `r[layout.repr.alignment.packed-fields]`. Reasoning: direct reading of the
  cited text; the correspondence is not proved.
* **Aligned staging.** The module documentation of rustc's `add_moves_for_packed_drops.rs`
  describes a pass that "moves values being dropped that are within a packed struct to a separate
  local before dropping them, to ensure that they are dropped from an aligned address"
  (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:9-11`),
  because drop glue is called "with a reference to `data`, which must be aligned" (same file
  `:25-25`). `core::ptr::drop_in_place` documents that "Unaligned values cannot be dropped in place
  … For packed structs, this move is done automatically by the compiler."
  (`library/core/src/ptr/mod.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:761-763`), and `core::pin`
  documents that, as a consequence of such moves, pinning cannot be used with a `#[repr(packed)]`
  type (`library/core/src/pin.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:630-633`). The toy's
  `compStep` staging and its hypothesis H2 are modelled on this documented design; this is a
  design correspondence, and it neither establishes nor refutes anything about the pass's
  coverage.
* **Owning-pointer moves.** https://github.com/rust-lang/rust/issues/164561 (open) documents one
  Miri report of a misaligned `&mut Box` when moving out of a `Box` field of a packed struct
  (quoted in the `box-free` non-claims). The toy's `box-free` counterexample is analogous in shape;
  it says nothing further about rustc.
* **Dynamic checking.** Miri's documentation lists "Not sufficiently aligned memory accesses and
  references" among the UB it detects (`src/tools/miri/README.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:15-15`);
  rustc's `-Zub-checks` documentation describes runtime UB checks generated "on a best-effort
  basis" (`src/doc/unstable-book/src/compiler-flags/ub-checks.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:10-10`);
  Clang's UBSan documents `-fsanitize=alignment` (live page, observed 2026-11-21). The toy's
  instrumentation policies are a different mechanism (checks inserted at chosen operations); no
  correspondence with any of these tools is claimed, and nothing here says which bodies or shims
  any of them checks.

### Lemmas used in the proofs and cited by name

```lean
-- lean/ToyPacked/Lemmas.lean:12
def AllEv (p : Ev → Prop) (o : Out) : Prop := ∀ e, e ∈ o.evs → p e
-- lean/ToyPacked/Lemmas.lean:601-602
def PrRel (I : BodyId → Nat → Bool) (o1 o2 : Out) : Prop :=
  o1.evs = o2.evs.map (toTrap I) ∧ o1.ok = o2.ok
-- lean/ToyPacked/Lemmas.lean:308-309
def Reached (P : Prog) (fuel : Nat) (k : ShimKind) (t : Nat) : Prop :=
  fuel ≤ P.fuel ∧ ∀ x, x ∈ reach P.env fuel k t → x ∈ reachableShims P
-- lean/ToyPacked/Lemmas.lean:463
def StRel (o1 o2 : Out) : Prop := NoUB o1 ∧ obs o1.evs = obs o2.evs ∧ o1.ok = o2.ok
-- lean/ToyPacked/Lemmas.lean:507-512
theorem runShim_staging (P : Prog) (cfg : Cfg) (hcov : CritCovers P cfg) (h1 : StagedSized P cfg)
    (h2 : StagedAddrBlind P cfg) (h3 : TempsAligned P cfg) :
    ∀ fuel k t a1 a2 n, Reached P fuel k t → P.env.align t ∣ a1 →
      (a1 = a2 ∨ (k = .dropGlue → AddrBlind P.env fuel t = true)) →
      StRel (runShim .ref cfg P.env P.layout fuel k t a1 n)
        (runShim .ideal cfg.unstaged P.env P.layout fuel k t a2 n)
-- lean/ToyPacked/Lemmas.lean:348-351
theorem runShim_noUB_of_aligned (P : Prog) (cfg : Cfg) (ha : CritCovers P cfg)
    (ht : TempsAligned P cfg) :
    ∀ fuel k t a n, Reached P fuel k t → P.env.align t ∣ a →
      AllEv (fun e => e.isUB = false) (runShim .ref cfg P.env P.layout fuel k t a n) := …
-- lean/ToyPacked/Lemmas.lean:414-417
theorem runShim_noUB_of_covered (cfg : Cfg) (env : Env) (L : Layout)
    (hcov : ∀ k t, t < env.length → env.align t ≠ 1 → shimExists env k t = true →
      cfg.instr (.shim k t) 0 = true) :
    ∀ fuel k t a n, AllEv (fun e => e.isUB = false) (runShim .ref cfg env L fuel k t a n) := …
-- lean/ToyPacked/Lemmas.lean:435-437
theorem runShim_noStuck (m : Mode) (P : Prog) (cfg : Cfg) (h1 : StagedSized P cfg) :
    ∀ fuel k t a n, Reached P fuel k t →
      AllEv (fun e => e.isStuck = false) (runShim m cfg P.env P.layout fuel k t a n) := …
-- lean/ToyPacked/Lemmas.lean:655-657
theorem runShim_precision (cfg : Cfg) (env : Env) (L : Layout) :
    ∀ fuel k t a n, PrRel cfg.instr (runShim .ref cfg env L fuel k t a n)
      (runShim .ref { cfg with instr := fun _ _ => false } env L fuel k t a n)
-- lean/ToyPacked/Lemmas.lean:765-768
theorem typeGA_props (env : Env) (hpow : PowTwoAligns env) :
    ∀ (path : List Nat) (t g : Nat), IsPow2 g →
      IsPow2 (typeGA env t path g) ∧ typeGA env t path g ∣ g ∧
      ∀ s, s ∈ pathSteps env t path → typeGA env t path g ∣ effAlign env s.1 s.2
-- lean/ToyPacked/Lemmas.lean:785-788
theorem typeGA_cases (env : Env) :
    ∀ (path : List Nat) (t g : Nat),
      typeGA env t path g = g ∨
      ∃ s, s ∈ pathSteps env t path ∧ typeGA env t path g = effAlign env s.1 s.2
-- lean/ToyPacked/Lemmas.lean:835-837
theorem resolve_dvd (env : Env) (L : Layout) (d : Nat) :
    ∀ (path : List Nat) (t u o : Nat), resolve env L t path = some (u, o) →
      (∀ s, s ∈ pathSteps env t path → d ∣ L s.1 s.2) → d ∣ o
-- lean/ToyPacked/Lemmas.lean:859-862
theorem resolve_indicator (env : Env) (x : Nat × Nat) (c : Nat) :
    ∀ (path : List Nat) (t u : Nat), (pathSteps env t path).Nodup → typeAt env t path = some u →
      resolve env (fun t' j' => if (t', j') = x then c else 0) t path =
        some (u, if x ∈ pathSteps env t path then c else 0)
-- lean/ToyPacked/Lemmas.lean:884-885
theorem pos_resolve (P : Prog) (q : Pos) (hq : q ∈ positions P) :
    q.A = P.env.align q.t0 ∧ resolve P.env P.layout q.t0 q.path = some (q.u, q.o) := …
-- lean/ToyPacked/Lemmas.lean:932-933
theorem clientPtrsAligned_and_srcRefsInstrumented_of_safeSrc (P : Prog) (cfg : Cfg)
    (hs : SafeSrc P) : ClientPtrsAligned P ∧ SrcRefsInstrumented P cfg := …
-- lean/ToyPacked/Lemmas.lean:956-957
theorem noRepeatStep_of_fieldIdsDecreasing (env : Env) (h : FieldIdsDecreasing env) :
    ∀ (t0 : Nat) (path : List Nat), NoRepeatStep env t0 path
```

### Auxiliary declarations cited by name

#### `ToyPacked/Examples.lean`

```lean
-- lean/ToyPacked/Examples.lean:12
theorem resolve_pos : resolve envQ LQ 3 [1, 0] = some (1, 1) := …
-- lean/ToyPacked/Examples.lean:14
theorem resolve_neg : resolve envQ LQ 3 [2] = none := …
-- lean/ToyPacked/Examples.lean:16
theorem typeAt_pos : typeAt envQ 3 [1, 0] = some 1 := …
-- lean/ToyPacked/Examples.lean:18
theorem typeAt_neg : typeAt envQ 1 [0] = none := …
-- lean/ToyPacked/Examples.lean:23
theorem effAlign_pos : effAlign envP2 3 1 = 2 := …
-- lean/ToyPacked/Examples.lean:25
theorem effAlign_neg : effAlign envQ 2 0 = 4 := …
-- lean/ToyPacked/Examples.lean:27
theorem effAlign_out_of_range : effAlign envQ 2 5 = 0 := …
-- lean/ToyPacked/Examples.lean:29
theorem typeGA_pos : typeGA envQ 3 [1, 0] (envQ.align 3) = 1 := …
-- lean/ToyPacked/Examples.lean:31
theorem typeGA_neg : typeGA envQ 2 [0] (envQ.align 2) = 4 := …
-- lean/ToyPacked/Examples.lean:37
theorem misalignable_pos : Misalignable 1 4 1 := …
-- lean/ToyPacked/Examples.lean:39
theorem misalignable_neg : ¬ Misalignable 4 4 8 := …
-- lean/ToyPacked/Examples.lean:41
theorem misalignable_align_zero : Misalignable 1 0 1 := …
-- lean/ToyPacked/Examples.lean:42
theorem isPow2_pos : IsPow2 8 := …
-- lean/ToyPacked/Examples.lean:43
theorem isPow2_neg_zero : ¬ IsPow2 0 := …
-- lean/ToyPacked/Examples.lean:44
theorem isPow2_neg_three : ¬ IsPow2 3 := …
-- lean/ToyPacked/Examples.lean:45
theorem powTwoAligns_pos : PowTwoAligns envP2 := …
-- lean/ToyPacked/Examples.lean:46
theorem powTwoAligns_neg : ¬ PowTwoAligns envW := …
-- lean/ToyPacked/Examples.lean:47
theorem respectsPacking_pos : RespectsPacking envQ LQ := …
-- lean/ToyPacked/Examples.lean:48
theorem respectsPacking_neg : ¬ RespectsPacking envRP LRP := …
-- lean/ToyPacked/Examples.lean:50
theorem pathSteps_pos : pathSteps envQ 3 [1, 0] = [(3, 1), (2, 0)] := …
-- lean/ToyPacked/Examples.lean:52
theorem pathSteps_stop : pathSteps envQ 3 [2, 0] = [] := …
-- lean/ToyPacked/Examples.lean:53
theorem noRepeatStep_pos : NoRepeatStep envQ 3 [1, 0] := …
-- lean/ToyPacked/Examples.lean:55
theorem noRepeatStep_cyc_short : NoRepeatStep envCyc 0 [0] := …
-- lean/ToyPacked/Examples.lean:57
theorem noRepeatStep_neg : ¬ NoRepeatStep envCyc 0 [0, 0] := …
-- lean/ToyPacked/Examples.lean:58
theorem fieldIdsDecreasing_pos : FieldIdsDecreasing envQ := …
-- lean/ToyPacked/Examples.lean:59
theorem fieldIdsDecreasing_neg : ¬ FieldIdsDecreasing envCyc := …
-- lean/ToyPacked/Examples.lean:62-63
theorem fieldIdsDecreasing_rejects_envRev :
    ¬ FieldIdsDecreasing envRev ∧ NoRepeatStep envRev 0 [0] := …
-- lean/ToyPacked/Examples.lean:68
theorem needsDrop_pos : needsDrop envA 4 2 = true := …
-- lean/ToyPacked/Examples.lean:70
theorem needsDrop_neg : needsDrop [tU8, ⟨1, true, .agg none [0, 0]⟩] 3 1 = false := …
-- lean/ToyPacked/Examples.lean:71
theorem addrBlind_pos : AddrBlind envA 4 2 = true := …
-- lean/ToyPacked/Examples.lean:72
theorem addrBlind_neg : AddrBlind envObs 4 2 = false := …
-- lean/ToyPacked/Examples.lean:75
theorem addrBlind_box_pos : AddrBlind envBoxObs 5 2 = true := …
-- lean/ToyPacked/Examples.lean:79
theorem shimExists_pos : shimExists envB .boxFree 2 = true := …
-- lean/ToyPacked/Examples.lean:81
theorem shimExists_neg : shimExists envA .boxFree 1 = false := …
-- lean/ToyPacked/Examples.lean:82
theorem callsShim_pos : callsShim envA 4 .dropGlue 2 = true := …
-- lean/ToyPacked/Examples.lean:84
theorem callsShim_neg : callsShim envA 4 .dropGlue 0 = false := …
-- lean/ToyPacked/Examples.lean:87
theorem reach_pos : reach envA 4 .dropGlue 2 = [(.dropGlue, 2), (.dropGlue, 1)] := …
-- lean/ToyPacked/Examples.lean:90-92
theorem positions_progInPlace :
    positions progInPlace =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] := …
-- lean/ToyPacked/Examples.lean:95
theorem positions_empty : positions progEmptyU = [] := …
-- lean/ToyPacked/Examples.lean:99-102
theorem positions_progBox :
    positions progBox =
      [⟨.src, 0, .dropGlue, 1, 3, [], 3, 0⟩, ⟨.src, 2, .boxFree, 1, 3, [1], 2, 1⟩,
        ⟨.src, 3, .dropGlue, 4, 1, [], 1, 0⟩, ⟨.shim .dropGlue 3, 2, .dropGlue, 1, 3, [1], 2, 1⟩] := …
-- lean/ToyPacked/Examples.lean:107-111
theorem positions_progEscape :
    positions progEscape =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] ∧
    positions progUserRef =
      [⟨.src, 0, .dropGlue, 1, 2, [], 2, 0⟩, ⟨.shim .dropGlue 2, 2, .dropGlue, 1, 2, [1], 1, 1⟩] := …
-- lean/ToyPacked/Examples.lean:117
theorem refStep_pos : refStep .ref cfgNone .src 0 4 8 = ⟨[], true⟩ := …
-- lean/ToyPacked/Examples.lean:119
theorem refStep_neg : refStep .ref cfgNone .src 0 4 1 = ⟨[.ub .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:121-122
theorem refStep_trap :
    refStep .ref ⟨critNone, fun _ _ => 0, instrAll⟩ .src 0 4 1 = ⟨[.trap .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:125
theorem refStep_ideal : refStep .ideal cfgNone .src 0 4 1 = ⟨[], true⟩ := …
-- lean/ToyPacked/Examples.lean:132
theorem noUB_pos : NoUB ⟨[.dtor ⟨.loc 0, []⟩, .trap .src 1], false⟩ := …
-- lean/ToyPacked/Examples.lean:133
theorem noUB_neg : ¬ NoUB ⟨[.ub .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:134
theorem noShimUB_pos : NoShimUB ⟨[.ub .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:135
theorem noShimUB_neg : ¬ NoShimUB ⟨[.ub (.shim .dropGlue 1) 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:136
theorem noStuck_pos : NoStuck ⟨[.ub .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:137
theorem noStuck_neg : ¬ NoStuck ⟨[.stuck .src 0], false⟩ := …
-- lean/ToyPacked/Examples.lean:139-140
theorem rawCall_missing_shim_noop :
    (run .ref cfgNone ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩).evs = [] := …
-- lean/ToyPacked/Examples.lean:143-145
theorem rawCall_missing_shim_admitted :
    ClientPtrsAligned ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩ ∧
    reachableShims ⟨envA, LA, [], [], [.rawCall .boxFree 1 1]⟩ = [] := …
-- lean/ToyPacked/Examples.lean:149
theorem critExact_pos : critExact envQ LQ .dropGlue 1 3 [1, 0] = true := …
-- lean/ToyPacked/Examples.lean:150
theorem critExact_neg : critExact envOuter LOuter .dropGlue 2 3 [1, 2] = false := …
-- lean/ToyPacked/Examples.lean:151
theorem critType_pos : critType envQ .dropGlue 1 3 [1, 0] = true := …
-- lean/ToyPacked/Examples.lean:152
theorem critType_neg : critType envQ .dropGlue 4 2 [0] = false := …
-- lean/ToyPacked/Examples.lean:153
theorem critLeaf_pos : critLeaf envA .dropGlue 1 2 [1] = true := …
-- lean/ToyPacked/Examples.lean:154
theorem critLeaf_neg : critLeaf envQ .dropGlue 1 3 [1, 0] = false := …
-- lean/ToyPacked/Examples.lean:157-159
theorem critType_eq_critExact_packed2_align8 :
    PowTwoAligns envP2 ∧ RespectsPacking envP2 LP2 ∧
    critType envP2 .dropGlue 2 3 [1, 0] = true ∧ critExact envP2 LP2 .dropGlue 2 3 [1, 0] = true := …
-- lean/ToyPacked/Examples.lean:161
theorem dropsOnly_pos : dropsOnly (critType envB) .dropGlue 1 3 [1] = true := …
-- lean/ToyPacked/Examples.lean:162
theorem dropsOnly_neg : dropsOnly (critType envB) .boxFree 1 3 [1] = false := …
-- lean/ToyPacked/Examples.lean:166
theorem critCovers_pos : CritCovers progInPlace (cfgType envA) := …
-- lean/ToyPacked/Examples.lean:167
theorem critCovers_neg : ¬ CritCovers progInPlace cfgNone := …
-- lean/ToyPacked/Examples.lean:168
theorem stagedSized_pos : StagedSized progInPlace (cfgType envA) := …
-- lean/ToyPacked/Examples.lean:169
theorem stagedSized_neg : ¬ StagedSized progU (cfgType envU) := …
-- lean/ToyPacked/Examples.lean:170
theorem stagedAddrBlind_pos : StagedAddrBlind progInPlace (cfgType envA) := …
-- lean/ToyPacked/Examples.lean:171
theorem stagedAddrBlind_neg : ¬ StagedAddrBlind progObs (cfgType envObs) := …
-- lean/ToyPacked/Examples.lean:172
theorem tempsAligned_pos : TempsAligned progInPlace (cfgType envA) := …
-- lean/ToyPacked/Examples.lean:173-174
theorem tempsAligned_neg :
    ¬ TempsAligned progInPlace ⟨critType envA, fun _ _ => 2, instrNone⟩ := …
-- lean/ToyPacked/Examples.lean:175
theorem frameAligned_pos : FrameAligned progInPlace := …
-- lean/ToyPacked/Examples.lean:176
theorem frameAligned_neg : ¬ FrameAligned progMisFrame := …
-- lean/ToyPacked/Examples.lean:177
theorem safeSrc_pos : SafeSrc progInPlace := …
-- lean/ToyPacked/Examples.lean:178
theorem safeSrc_neg : ¬ SafeSrc progClient := …
-- lean/ToyPacked/Examples.lean:179
theorem clientPtrsAligned_pos : ClientPtrsAligned progMixed := …
-- lean/ToyPacked/Examples.lean:180
theorem clientPtrsAligned_neg : ¬ ClientPtrsAligned progClient := …
-- lean/ToyPacked/Examples.lean:181-182
theorem srcRefsInstrumented_pos :
    SrcRefsInstrumented progMixed ⟨critType envA, fun _ _ => 16, instrSrc⟩ := …
-- lean/ToyPacked/Examples.lean:183
theorem srcRefsInstrumented_neg : ¬ SrcRefsInstrumented progUserRef (cfgType envA) := …
-- lean/ToyPacked/Examples.lean:184
theorem alignRelevantCovered_pos : AlignRelevantCovered envA instrAll := …
-- lean/ToyPacked/Examples.lean:186
theorem alignRelevantCovered_neg : ¬ AlignRelevantCovered envA instrSrc := …
-- lean/ToyPacked/Examples.lean:192
theorem alignRelevantCovered_trivial_align_one : AlignRelevantCovered [tU8] instrNone := …
-- lean/ToyPacked/Examples.lean:201-204
theorem alignRelevantCovered_existing_shims :
    AlignRelevantCovered envA (fun b _ => match b with
      | .shim .boxFree _ => false
      | _ => true) := …
```

#### `ToyPacked/Counterexamples.lean`

```lean
-- lean/ToyPacked/Counterexamples.lean:28-32
theorem staging_hyps_hold_progInPlace :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ CritCovers progInPlace (cfgType envA) ∧
    StagedSized progInPlace (cfgType envA) ∧ StagedAddrBlind progInPlace (cfgType envA) ∧
    TempsAligned progInPlace (cfgType envA) ∧
    (∃ q, q ∈ positions progInPlace ∧ q.staged (cfgType envA) = true) := …
-- lean/ToyPacked/Counterexamples.lean:36-39
theorem staging_conclusion_progInPlace :
    NoUB (run .ref (cfgType envA) progInPlace) ∧
    obs (run .ref (cfgType envA) progInPlace).evs =
      obs (run .ideal (cfgType envA).unstaged progInPlace).evs := …
-- lean/ToyPacked/Counterexamples.lean:43-48
theorem staging_fails_without_stagedSized :
    FrameAligned progU ∧ SafeSrc progU ∧ CritCovers progU (cfgType envU) ∧
    StagedAddrBlind progU (cfgType envU) ∧ TempsAligned progU (cfgType envU) ∧
    ¬ StagedSized progU (cfgType envU) ∧
    ¬ (NoUB (run .ref (cfgType envU) progU) ∧
      obs (run .ref (cfgType envU) progU).evs = obs (run .ideal (cfgType envU).unstaged progU).evs) := …
-- lean/ToyPacked/Counterexamples.lean:53-59
theorem staging_fails_without_stagedAddrBlind :
    FrameAligned progObs ∧ SafeSrc progObs ∧ CritCovers progObs (cfgType envObs) ∧
    StagedSized progObs (cfgType envObs) ∧ TempsAligned progObs (cfgType envObs) ∧
    ¬ StagedAddrBlind progObs (cfgType envObs) ∧
    ¬ (NoUB (run .ref (cfgType envObs) progObs) ∧
      obs (run .ref (cfgType envObs) progObs).evs =
        obs (run .ideal (cfgType envObs).unstaged progObs).evs) := …
-- lean/ToyPacked/Counterexamples.lean:63
def cfgTmp2 : Cfg := ⟨critType envA, fun _ _ => 2, instrNone⟩
-- lean/ToyPacked/Counterexamples.lean:66-71
theorem staging_fails_without_tempsAligned :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ CritCovers progInPlace cfgTmp2 ∧
    StagedSized progInPlace cfgTmp2 ∧ StagedAddrBlind progInPlace cfgTmp2 ∧
    ¬ TempsAligned progInPlace cfgTmp2 ∧
    ¬ (NoUB (run .ref cfgTmp2 progInPlace) ∧
      obs (run .ref cfgTmp2 progInPlace).evs = obs (run .ideal cfgTmp2.unstaged progInPlace).evs) := …
-- lean/ToyPacked/Counterexamples.lean:75-80
theorem staging_fails_without_critCovers :
    FrameAligned progInPlace ∧ SafeSrc progInPlace ∧ StagedSized progInPlace cfgNone ∧
    StagedAddrBlind progInPlace cfgNone ∧ TempsAligned progInPlace cfgNone ∧
    ¬ CritCovers progInPlace cfgNone ∧
    ¬ (NoUB (run .ref cfgNone progInPlace) ∧
      obs (run .ref cfgNone progInPlace).evs = obs (run .ideal cfgNone.unstaged progInPlace).evs) := …
-- lean/ToyPacked/Counterexamples.lean:84-90
theorem staging_fails_without_frameAligned :
    SafeSrc progMisFrame ∧ CritCovers progMisFrame (cfgType [tR4]) ∧
    StagedSized progMisFrame (cfgType [tR4]) ∧ StagedAddrBlind progMisFrame (cfgType [tR4]) ∧
    TempsAligned progMisFrame (cfgType [tR4]) ∧ ¬ FrameAligned progMisFrame ∧
    ¬ (NoUB (run .ref (cfgType [tR4]) progMisFrame) ∧
      obs (run .ref (cfgType [tR4]) progMisFrame).evs =
        obs (run .ideal (cfgType [tR4]).unstaged progMisFrame).evs) := …
-- lean/ToyPacked/Counterexamples.lean:95-99
theorem staging_hyps_hold_dropsOnly_progInPlace :
    CritCovers progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    StagedSized progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    StagedAddrBlind progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ ∧
    TempsAligned progInPlace ⟨dropsOnly (critType envA), fun _ _ => 16, instrNone⟩ := …
-- lean/ToyPacked/Counterexamples.lean:104-107
theorem staging_hyps_hold_progEmptyU :
    FrameAligned progEmptyU ∧ SafeSrc progEmptyU ∧ CritCovers progEmptyU (cfgType envU) ∧
    StagedSized progEmptyU (cfgType envU) ∧ StagedAddrBlind progEmptyU (cfgType envU) ∧
    TempsAligned progEmptyU (cfgType envU) := …
-- lean/ToyPacked/Counterexamples.lean:113-121
theorem staging_box_of_addrObs_pointee :
    FrameAligned progBoxObs ∧ SafeSrc progBoxObs ∧ CritCovers progBoxObs (cfgType envBoxObs) ∧
    StagedSized progBoxObs (cfgType envBoxObs) ∧ StagedAddrBlind progBoxObs (cfgType envBoxObs) ∧
    TempsAligned progBoxObs (cfgType envBoxObs) ∧
    NoUB (run .ref (cfgType envBoxObs) progBoxObs) ∧
    obs (run .ref (cfgType envBoxObs) progBoxObs).evs =
      [.addrObs ⟨.loc 0, [1, 0]⟩ 4, .dtor ⟨.loc 0, [1, 0]⟩, .free ⟨.loc 0, [1]⟩] ∧
    obs (run .ideal (cfgType envBoxObs).unstaged progBoxObs).evs =
      [.addrObs ⟨.loc 0, [1, 0]⟩ 4, .dtor ⟨.loc 0, [1, 0]⟩, .free ⟨.loc 0, [1]⟩] := …
-- lean/ToyPacked/Counterexamples.lean:127-133
theorem staging_fails_without_safeSrc :
    FrameAligned progEscape ∧ CritCovers progEscape (cfgType envA) ∧
    StagedSized progEscape (cfgType envA) ∧ StagedAddrBlind progEscape (cfgType envA) ∧
    TempsAligned progEscape (cfgType envA) ∧ ¬ SafeSrc progEscape ∧
    ¬ (NoUB (run .ref (cfgType envA) progEscape) ∧
      obs (run .ref (cfgType envA) progEscape).evs =
        obs (run .ideal (cfgType envA).unstaged progEscape).evs) := …
-- lean/ToyPacked/Counterexamples.lean:140-142
theorem typeGA_sound_hyps_hold :
    PowTwoAligns envQ ∧ RespectsPacking envQ LQ ∧ resolve envQ LQ 2 [0] = some (1, 0) ∧
    envQ.align 1 ∣ typeGA envQ 2 [0] (envQ.align 2) := …
-- lean/ToyPacked/Counterexamples.lean:147-150
theorem typeGA_sound_fails_without_powTwo :
    RespectsPacking envW LW ∧ resolve envW LW 1 [0] = some (0, 2) ∧
    envW.align 0 ∣ typeGA envW 1 [0] (envW.align 1) ∧ ¬ PowTwoAligns envW ∧
    Misalignable (envW.align 1) (envW.align 0) 2 := …
-- lean/ToyPacked/Counterexamples.lean:155-157
theorem typeGA_sound_fails_without_dvd :
    PowTwoAligns envA ∧ RespectsPacking envA LA ∧ resolve envA LA 2 [1] = some (1, 1) ∧
    ¬ envA.align 1 ∣ typeGA envA 2 [1] (envA.align 2) ∧ Misalignable (envA.align 2) (envA.align 1) 1 := …
-- lean/ToyPacked/Counterexamples.lean:163-165
theorem typeGA_sound_fails_without_resolve :
    PowTwoAligns envA ∧ RespectsPacking envA LA ∧ resolve envA LA 1 [0] ≠ some (1, 1) ∧
    envA.align 1 ∣ typeGA envA 1 [0] (envA.align 1) ∧ Misalignable (envA.align 1) (envA.align 1) 1 := …
-- lean/ToyPacked/Counterexamples.lean:169-172
theorem typeGA_sound_fails_without_respectsPacking :
    PowTwoAligns envRP ∧ resolve envRP LRP 1 [0] = some (0, 1) ∧
    envRP.align 0 ∣ typeGA envRP 1 [0] (envRP.align 1) ∧ ¬ RespectsPacking envRP LRP ∧
    Misalignable (envRP.align 1) (envRP.align 0) 1 := …
-- lean/ToyPacked/Counterexamples.lean:178-179
theorem typeGA_exact_hyps_hold :
    PowTwoAligns envQ ∧ typeAt envQ 3 [1, 0] = some 1 ∧ NoRepeatStep envQ 3 [1, 0] := …
-- lean/ToyPacked/Counterexamples.lean:184-186
theorem critCovers_critType_hyps_hold :
    PowTwoAligns progNested.env ∧ RespectsPacking progNested.env progNested.layout ∧
    CritCovers progNested ⟨critType progNested.env, fun _ _ => 16, instrNone⟩ := …
-- lean/ToyPacked/Counterexamples.lean:190
def progW : Prog := ⟨envW, LW, [1], [3], [.comp .clone ⟨0, [0]⟩]⟩
-- lean/ToyPacked/Counterexamples.lean:193
def progRP : Prog := ⟨envRP, LRP, [1], [0], [.comp .dropGlue ⟨0, [0]⟩]⟩
-- lean/ToyPacked/Counterexamples.lean:196-198
theorem critCovers_critType_fails_without_powTwo :
    RespectsPacking progW.env progW.layout ∧ ¬ PowTwoAligns progW.env ∧
    ¬ CritCovers progW ⟨critType progW.env, fun _ _ => 16, instrNone⟩ := …
-- lean/ToyPacked/Counterexamples.lean:202-204
theorem critCovers_critType_fails_without_respectsPacking :
    PowTwoAligns progRP.env ∧ ¬ RespectsPacking progRP.env progRP.layout ∧
    ¬ CritCovers progRP ⟨critType progRP.env, fun _ _ => 16, instrNone⟩ := …
-- lean/ToyPacked/Counterexamples.lean:210-214
theorem typeGA_exact_fails_without_noRepeatStep :
    PowTwoAligns envCyc ∧ typeAt envCyc 0 [0, 0] = some 0 ∧ ¬ NoRepeatStep envCyc 0 [0, 0] ∧
    ¬ envCyc.align 0 ∣ typeGA envCyc 0 [0, 0] (envCyc.align 0) ∧
    ¬ (∃ L : Layout, RespectsPacking envCyc L ∧ ∃ o, resolve envCyc L 0 [0, 0] = some (0, o) ∧
        Misalignable (envCyc.align 0) (envCyc.align 0) o) := …
-- lean/ToyPacked/Counterexamples.lean:227-231
theorem typeGA_exact_fails_without_powTwo :
    NoRepeatStep envW 1 [0] ∧ typeAt envW 1 [0] = some 0 ∧ ¬ PowTwoAligns envW ∧
    (∃ L : Layout, RespectsPacking envW L ∧ ∃ o, resolve envW L 1 [0] = some (0, o) ∧
        Misalignable (envW.align 1) (envW.align 0) o) ∧
    envW.align 0 ∣ typeGA envW 1 [0] (envW.align 1) := …
-- lean/ToyPacked/Counterexamples.lean:237-241
theorem typeGA_exact_fails_without_typeAt :
    PowTwoAligns envA ∧ NoRepeatStep envA 2 [99] ∧ typeAt envA 2 [99] ≠ some 1 ∧
    ¬ ((∃ L : Layout, RespectsPacking envA L ∧ ∃ o, resolve envA L 2 [99] = some (1, o) ∧
        Misalignable (envA.align 2) (envA.align 1) o) ↔
      ¬ envA.align 1 ∣ typeGA envA 2 [99] (envA.align 2)) := …
-- lean/ToyPacked/Counterexamples.lean:278-280
theorem leafOnlyCrit_stages_field_in_whole_drop :
    critLeaf envQ .dropGlue 1 3 [1] = true ∧
    NoUB (run .ref ⟨critLeaf envQ, fun _ _ => 16, instrNone⟩ progWholeQ) := …
-- lean/ToyPacked/Counterexamples.lean:321
def cfgDropsOnly : Cfg := ⟨dropsOnly (critType envB), fun _ _ => 16, instrNone⟩
-- lean/ToyPacked/Counterexamples.lean:356-357
theorem refStep_align_one (m : Mode) (cfg : Cfg) (b : BodyId) (i a : Nat) :
    refStep m cfg b i 1 a = ⟨[], true⟩ := …
-- lean/ToyPacked/Counterexamples.lean:362-367
theorem completeness_witness :
    AlignRelevantCovered envA instrAll ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrAll⟩ progClient).evs =
      [.trap (.shim .dropGlue 1) 0] ∧
    (run .ref ⟨critType envA, fun _ _ => 16, instrNone⟩ progClient).evs =
      [.ub (.shim .dropGlue 1) 0] := …
-- lean/ToyPacked/Counterexamples.lean:392
def cfgSrc : Cfg := ⟨critType envA, fun _ _ => 16, instrSrc⟩
-- lean/ToyPacked/Counterexamples.lean:396-400
theorem sufficiency_hyps_hold_progMixed :
    FrameAligned progMixed ∧ CritCovers progMixed cfgSrc ∧ TempsAligned progMixed cfgSrc ∧
    ClientPtrsAligned progMixed ∧ SrcRefsInstrumented progMixed cfgSrc ∧
    (run .ref cfgSrc progMixed).evs =
      [.copy ⟨.loc 0, [1]⟩, .dtor ⟨.loc 0, [1]⟩, .dtor ⟨.raw 1, []⟩, .trap .src 2] := …
-- lean/ToyPacked/Counterexamples.lean:406-409
theorem sufficiency_fails_without_critCovers :
    FrameAligned progBox ∧ TempsAligned progBox cfgDropsOnly ∧ ClientPtrsAligned progBox ∧
    SrcRefsInstrumented progBox cfgDropsOnly ∧ ¬ CritCovers progBox cfgDropsOnly ∧
    ¬ NoUB (run .ref cfgDropsOnly progBox) ∧ ¬ NoShimUB (run .ref cfgDropsOnly progBox) := …
-- lean/ToyPacked/Counterexamples.lean:413-416
theorem sufficiency_fails_without_tempsAligned :
    FrameAligned progInPlace ∧ CritCovers progInPlace cfgTmp2 ∧ ClientPtrsAligned progInPlace ∧
    SrcRefsInstrumented progInPlace cfgTmp2 ∧ ¬ TempsAligned progInPlace cfgTmp2 ∧
    ¬ NoUB (run .ref cfgTmp2 progInPlace) ∧ ¬ NoShimUB (run .ref cfgTmp2 progInPlace) := …
-- lean/ToyPacked/Counterexamples.lean:420-425
theorem sufficiency_fails_without_frameAligned :
    CritCovers progMisFrame (cfgType [tR4]) ∧ TempsAligned progMisFrame (cfgType [tR4]) ∧
    ClientPtrsAligned progMisFrame ∧ SrcRefsInstrumented progMisFrame (cfgType [tR4]) ∧
    ¬ FrameAligned progMisFrame ∧
    ¬ NoUB (run .ref (cfgType [tR4]) progMisFrame) ∧
    ¬ NoShimUB (run .ref (cfgType [tR4]) progMisFrame) := …
-- lean/ToyPacked/Counterexamples.lean:430-433
theorem sufficiency_fails_without_clientPtrsAligned :
    FrameAligned progEscape ∧ CritCovers progEscape cfgSrc ∧ TempsAligned progEscape cfgSrc ∧
    SrcRefsInstrumented progEscape cfgSrc ∧ ¬ ClientPtrsAligned progEscape ∧
    ¬ NoUB (run .ref cfgSrc progEscape) ∧ ¬ NoShimUB (run .ref cfgSrc progEscape) := …
-- lean/ToyPacked/Counterexamples.lean:440-442
theorem progUserRef_stages_misalignable_position :
    ∃ q, q ∈ positions progUserRef ∧ Misalignable q.A (envA.align q.u) q.o ∧
      q.staged (cfgType envA) = true := …
-- lean/ToyPacked/Counterexamples.lean:447-452
theorem sufficiency_fails_without_srcRefsInstrumented :
    FrameAligned progUserRef ∧ CritCovers progUserRef (cfgType envA) ∧
    TempsAligned progUserRef (cfgType envA) ∧ ClientPtrsAligned progUserRef ∧
    ¬ SrcRefsInstrumented progUserRef (cfgType envA) ∧
    ¬ NoUB (run .ref (cfgType envA) progUserRef) ∧
    NoShimUB (run .ref (cfgType envA) progUserRef) := …
-- lean/ToyPacked/Counterexamples.lean:459-462
theorem critCovers_and_frameAligned_counterexamples_stage_nothing :
    (∀ q, q ∈ positions progInPlace → q.staged cfgNone = false) ∧
    (∀ q, q ∈ positions progMisFrame →
      ¬ Misalignable q.A (progMisFrame.env.align q.u) q.o ∧ q.staged (cfgType [tR4]) = false) := …
-- lean/ToyPacked/Counterexamples.lean:469-472
theorem noStuck_hyps_hold_progInPlace :
    StagedSized progInPlace (cfgType envA) ∧
    (∃ q, q ∈ positions progInPlace ∧ q.staged (cfgType envA) = true) ∧
    NoStuck (run .ref (cfgType envA) progInPlace) := …
-- lean/ToyPacked/Counterexamples.lean:476-477
theorem noStuck_fails_without_stagedSized :
    ¬ StagedSized progU (cfgType envU) ∧ ¬ NoStuck (run .ref (cfgType envU) progU) := …
-- lean/ToyPacked/Counterexamples.lean:482-485
theorem sufficiency_hyps_hold_progU_stuck :
    FrameAligned progU ∧ CritCovers progU (cfgType envU) ∧ TempsAligned progU (cfgType envU) ∧
    ClientPtrsAligned progU ∧ SrcRefsInstrumented progU (cfgType envU) ∧
    (run .ref (cfgType envU) progU).evs = [.stuck (.shim .dropGlue 2) 2] := …
```

## Boundaries

### Non-claims

Non-claims come first: the shared list applies to every card, and each card's list says what
that card does not show. Read both before relying on a card.

#### Shared by all results

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc, Miri or any other implementation. Model–system relation: none proved
  (no embedding, abstraction or simulation between the toy and any real semantics is stated).
* Nothing here says which bodies or shims of any real compiler receive alignment checks or
  packed-drop staging, or how any real compiler lowers drops, frees or clones.
* The toy has no byte memory, sizes, field overlap, loads or stores through raw pointers,
  ownership tracking, loops, borrows, aliasing, unwinding, drop elaboration or static rejection;
  results that would depend on them are not covered.
* Runs are those produced by the deterministic generator `run` (one run per program and
  configuration); the toy has no scheduler or nondeterminism, and every result that speaks of "the
  run" means the run produced by `run`.
* The positions over which `CritCovers` and H1–H3 range (`positions`) are computed statically from
  the source body; they over-approximate the operations a run executes.

#### `in-place` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* It shows that the unstaged in-place drop is UB in the toy's reference semantics; it neither
  establishes nor refutes that any compiler emits such a program (the toy has no elaboration or
  static rejection).
* The reference is created inside the drop-glue shim (op 0), not in the source body; checks at
  source positions do not see it (cf. `escape`).
* "No `&` in the source" is `SafeSrc progInPlace` (no `rawRef`, no `rawCall`); compiler drops are
  not counted as source references.
* One drop is exhibited. That frees of a box field and clones also create references is a modelling
  choice of `runShim` (see `box-free` for a free); it is not derived here.

#### `staging` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* `CritCovers` and H1–H3 range over `positions P`: the source body and the shims in
  `reachableShims P`. That list over-approximates the shims a run enters (it ignores early
  termination), so a hypothesis can fail on a position no run executes; it contains no shim of a
  type the program never reaches.
* No write-back to the original place is modelled. Staging without write-back preserves behaviour in
  the toy because a staged drop or free consumes the value and a staged clone reads it without
  writing; staging an operation that mutates a live place is outside the model.
* Clone shims take a raw pointer and never observe addresses, and H2 constrains staged drops alone;
  an address-observing or interior-mutable `Clone` cannot be expressed. In Rust, `Clone::clone`
  takes `&self`; this card neither establishes nor refutes anything about staging such clones.
* Aliasing raw pointers into the packed field during a staged operation, and unwinding or panics
  during staging or destruction, are not modelled.
* A box's pointee is dropped at its heap address whatever the box's address, so staging a `Box<T>`
  field moves the pointer, not the pointee; H2 does not constrain pointees behind a box
  (`addrBlind_box_pos`, `staging_box_of_addrObs_pointee`).
* The theorem does not assume acyclicity: it also covers runs that end with `outOfFuel`, and
  equality of observable traces does not imply that the runs complete.
* `CritCovers` is a hypothesis; that `critType` meets it is `criterion-type-covers`.
* `SafeSrc` is a sufficient syntactic restriction; programs with raw-pointer operations are covered
  by `sufficiency` for the `NoUB` part, and trace preservation for them is not stated.
* Traces compare value names, not memory contents: the toy has no byte memory, so "the staged copy
  equals the original value" holds by construction, not by proof.

#### `criterion-exact` (characterization)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* It is about addresses, not about what a compiler can know: a compiler deciding per type, before
  layout, cannot use `o` (see `criterion-type-exact-over-layouts`).
* A path-wise gcd (`gcd` of `A` with each step's offset separately) is a different quantity: offsets
  1 and 1 from base alignment 4 give path-wise gcd 1 but `gcd 4 2 = 2` (arithmetic; not stated as a
  theorem; not proved here).

#### `criterion-type-sound` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* Sound, not exact for a fixed layout: `typeCrit_overstages_fixed_layout`
  (`criterion-type-overstages-fixed-layout`).
* The toy permits `packed(n)` types containing over-aligned types, which Rust rejects (E0588);
  soundness covers them (`critType_eq_critExact_packed2_align8` is one instance), and nothing is
  claimed about how rustc treats them.
* `PowTwoAligns` excludes alignment 0 and `packed(0)`; with them `typeGA` can be 0, and the theorem
  is not stated for that case.

#### `criterion-type-covers` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* It does not say `critType` stages exactly the misalignable positions (it over-stages:
  `typeCrit_overstages_fixed_layout`).

#### `criterion-type-exact-over-layouts` (characterization)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* Exactness is over *all* packing-respecting layouts; for one fixed layout the criterion over-stages
  (`typeCrit_overstages_fixed_layout`), and the exact fixed-layout criterion is `criterion-exact`.
* Layouts here are arbitrary offset functions subject to `RespectsPacking`. No size, overlap or
  field-order constraint is imposed (for example `repr(C)` puts field 0 at offset 0, and sibling
  sizes constrain offsets), so the witnessing layout may not be one any real `repr` produces.
  Whether exactness survives such constraints is not addressed (not proved either way).
* `typeGA` sees the type environment and the path, not field order or sibling sizes.

#### `criterion-leaf-misses` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* Two instances. For the whole-value drop of `x` in `envQ` (through the drop glue of `Q` and then of
  `S`, one projection per shim), `critLeaf` stages `S` itself and the run has no UB
  (`leafOnlyCrit_stages_field_in_whole_drop`).
* Whether `critLeaf` covers every one-step shim position when every struct's declared alignment is
  at least its fields' effective alignments is not addressed (not proved here).

#### `criterion-type-overstages-fixed-layout` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* One instance. Exactness of `critType` over all packing-respecting layouts is
  `criterion-type-exact-over-layouts`; what over-staging costs is `overstaging-aligned`.

#### `overstaging-aligned` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* Two instances; they state no general copy-count law. The general statement for a covering
  criterion that over-stages is `staging`, whose H1–H3 still apply: (i) is an instance where H2
  fails at an aligned place.

#### `box-free` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* A toy instance. It does not describe how any compiler lowers `*p.1` for a packed `p`.
* The UB arises because the free is modelled as a reference-taking shim. A lowering that frees the
  box without creating `&mut Box` (for example, reading the pointer with an unaligned read and
  deallocating through the raw pointer) is outside the toy's `boxFree` shim; this card neither
  establishes nor refutes that such a lowering avoids the UB.
* The toy does not track ownership: the program states which operations happen. After the deref-move
  marker, the program frees the box of `x` (without dropping its pointee) and then drops `y`; `z`
  is a separate local whose whole value is dropped.
* Context (documented upstream, cited as such): https://github.com/rust-lang/rust/issues/164561
  (open) reports that for `#[repr(C, packed)] pub struct P(u8, Box<String>);` and
  `fn f(p: P) -> String { *p.1 }`, Miri reports "Undefined Behavior: constructing invalid value of
  type &mut std::boxed::Box<std::string::String>: encountered an unaligned reference (required 8
  byte alignment but found 2)". The toy result neither establishes nor refutes anything about that
  report.

#### `completeness` (characterization)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* `NoUB` holds for runs with no misaligned reference creation and for runs ending with `trap`,
  `stuck` or `outOfFuel` before any UB event; it does not say that a run traps. That the
  instrumented run emits `trap` exactly where the uninstrumented run emits a UB event at a checked
  position is `precision`; combining the two, under a covering policy every UB event of the
  uninstrumented run becomes a trap.
* The policy is fixed before the program and every program shares the body name `.src`, so the "only
  if" direction forces checks at every source position (including positions holding `readUnaligned`
  or `moveOut`) and in every existing shim kind of every type with alignment not 1 (including clone
  shims of types that need not be cloneable in Rust), because a client may call any existing shim
  and a `rawRef` may sit at any position. `FrameAligned` is not assumed. For a restricted class (no
  unsafe clients, or some shims never called) coverage of fewer operations can suffice
  (`sufficiency`).
* Escape hatch — redundant checks: in richer shims with several reference creations, omitting a
  check whose misalignment always implies an earlier checked one can preserve completeness; the
  toy's shims have one reference creation (op 0), and every existing shim is directly callable, so
  this does not arise here (not proved for richer shims).
* Escape hatch — caller-side checks: `srcStep` consults no check at `rawCall` sites, so checking a
  raw address at the call site before entering a shim is outside the policy space; this card neither
  establishes nor refutes the completeness of caller-side checking.
* In the toy, reference creation (at `rawRef` and op 0 of existing shims) is the alignment-relevant
  operation; misaligned loads and stores through raw pointers and misaligned `Box<T>` values
  (Reference `r[undefined.pointer-access]`, `r[undefined.validity.reference-box]`) are not modelled.
* Operations requiring alignment 1 need not be checked (`refStep_align_one`,
  `alignRelevantCovered_trivial_align_one`); alignment 0 does need checking (address 1 is misaligned
  for it).
* Not about any real compiler's check-insertion pass; the toy does not say which real bodies or
  shims receive checks.

#### `precision` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* Precision holds by construction of `refStep` (a check traps iff the address is misaligned); the
  theorem lifts it to whole runs. Checks with false positives (for example a check that uses a
  stricter notion of alignment, as Miri's symbolic alignment check documents for manual integer
  arithmetic) are outside the model.

#### `escape` (counterexample)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* It refutes, in the toy, the claim "checks at source positions catch every alignment violation" for
  policies that check source positions and not shims. It says nothing about which bodies any real
  compiler or tool instruments.
* The client's own raw-pointer creation is not UB (the Reference allows `&raw mut` on such a place);
  the violation is the shim's reference creation.
* The toy does not track ownership: the program states which operations happen, and in `progEscape`
  the compiler does not drop `x`.
* Escape hatch — caller-side checks: `srcStep` has no check at `rawCall` sites, so the
  counterexample does not refute checking the raw address at the call site.
* Misaligned loads and stores through raw pointers are not modelled.

#### `sufficiency` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* `NoUB` excludes `Ev.ub` events and nothing else: a run may end with `stuck` (an unsized staged
  value: `sufficiency_hyps_hold_progU_stuck`), `trap` (a misaligned checked user reference) or
  `outOfFuel`. Under H1 no run is `stuck` (`no-stuck`).
* H2 (address-blind) is not needed: addresses printed by destructors do not affect UB.
* Premise (c) is not needed for the shim part of the conclusion (`sufficiency-shim`).
* Premise (b) is a precondition on client code; nothing checks it. It constrains raw calls of
  existing shims; a raw call of a shim that does not exist is a no-op and is admitted whatever its
  address (`rawCall_missing_shim_admitted`).
* Not about any real compiler; the toy does not say which real bodies receive checks.

#### `sufficiency-shim` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* UB in the source body (an unchecked user reference) is not excluded:
  `sufficiency_fails_without_srcRefsInstrumented` has `NoShimUB` but not `NoUB`. `stuck`, `trap` and
  `outOfFuel` are not excluded.

#### `no-stuck` (theorem)

* These are statements about the toy model; they neither establish nor refute the corresponding
  claims about Rust, rustc or Miri. Model–system relation: none proved.
* `NoStuck` excludes `Ev.stuck` events and nothing else: a run satisfying it may still have a `ub`,
  `trap` or `outOfFuel` event (`noStuck_pos` is `NoStuck ⟨[.ub .src 0], false⟩`). To exclude UB
  events, combine it with `sufficiency` or `staging`.
* `StagedSized` ranges over the static `positions P` (the source body and the shims in
  `reachableShims P`), which over-approximate the operations a run executes, so the hypothesis can
  fail on a position no run executes.
* `stuck` stands for a compile-time rejection of staging an unsized value; this card neither
  establishes nor refutes anything about how Rust treats unsized fields of packed structs.

### Escape hatches

Which assumptions of the counterexample cards, if changed, defeat them, as far as the package shows:

* `escape`: checking op 0 of the drop glue of `R4` removes the UB event (the `instrAll` conjunct
  of `srcInstrumented_rawDropInPlace_misaligned_escapes` ends with a trap instead). A check at the
  `rawCall` site in the source body is not in the policy space (`srcStep` consults no check at
  `rawCall`), so the card neither establishes nor refutes that caller-side checking suffices.
* `box-free`: staging the box field itself (`cfgType envB`) removes the UB event (the last two
  conjuncts of `boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok`). The UB depends on the free
  being a reference-taking shim; a lowering that frees through a raw pointer is outside the toy's
  `boxFree` shim (neither established nor refuted).
* `in-place`: the staging non-vacuity instance shows that type-based staging of the same program
  (`cfgType envA`) has no UB event (`staging_conclusion_progInPlace`).
* `criterion-leaf-misses`: instance (ii) uses a struct whose declared alignment is below its
  field's alignment; whether `critLeaf` covers every one-step shim position when declared
  alignments are at least the fields' effective alignments is not addressed (not proved here).
* `criterion-type-overstages-fixed-layout`: the offset-aware criterion `critExact` does not stage
  the same place (fourth conjunct of `typeCrit_overstages_fixed_layout`).
* `completeness`, "only if" direction: it relies on the policy being fixed before the program, on
  every program sharing the body name `.src`, on every existing shim being directly callable by
  client code, and on each shim having a single reference creation (op 0). Redundant checks in
  richer shims and caller-side checks at `rawCall` sites are outside the model (not proved here).

### Hypotheses whose tightness is `unknown`

None. Every hypothesis in every hypothesis ledger is `tight`: the named counterexample theorem
states that all the other hypotheses of the same theorem hold and that the conclusion fails, in the
witness class recorded in the ledger row. `tight` does not mean that the hypothesis is necessary
outside that class.

### Open questions (not addressed)

* Whether `critLeaf` covers every one-step shim position under struct-alignment well-formedness
  (not proved here).
* Whether `critType` remains exact over layouts once realistic layout constraints (field order,
  sibling sizes, `repr(C)` placement of field 0) are imposed (not proved either way).
* Caller-side checks at `rawCall` sites, write-back after staging, unwinding during staging or
  destruction, and address-observing or interior-mutable clones are not modelled.

### Disproved or dropped statements

None. Every statement in this package is proved as stated; none was weakened, dropped, or found
false.

## Evidence

Basis of every theorem below: execution (Lean kernel check). Axioms are computed with Lean's
`collectAxioms`; the statement hash is the SHA-256 of the Lean `repr` of the declaration's type,
and the closure hash is the SHA-256 of the sorted `name : type := value` texts of every
package-local constant reachable from that type (theorem bodies excluded), as recorded in
`audit/statements.json` (per-declaration axioms for the whole library: `audit/axioms.json`).

### Toolchain

Lean `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`
(`leanprover/lean4`, fetched from the GitHub API on 2026-11-21); core Lean only, no Mathlib.
The library has 862 audited declarations; every one depends only on a subset of
`propext`, `Classical.choice` and `Quot.sound`.

### Kernel-check record: main results

| Card | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- | :--- |
| `in-place` | `Toy.Packed.inPlaceDrop_packedField_ub_though_source_has_no_ref` | `propext` | `76399ffe4fa5fe2c7754967491d4a4e1786bf077c86441881ff7a57d342661d9` | `dd77a756994cdf0ba4d1995ef9f0f1ae90b3de5fcb02413bb11ceb4625e00034` |
| `staging` | `Toy.Packed.staged_noUB_and_obs_eq_ideal_of_frameAligned_safeSrc_covers_sized_addrBlind_alignedTemps` | `Classical.choice`, `Quot.sound`, `propext` | `2572af738abd4e0a3f395985f808fb77b44e53ce0752a8e7b6c8938328f5d89c` | `c7440440a6e0beefd16c47811032f1013cea8c8d33fcbf6c2e9b108719e8e6e4` |
| `criterion-exact` | `Toy.Packed.misalignable_iff_not_dvd_gcd` | `Quot.sound`, `propext` | `337e889d573378f7e57cdb670c1bd22d7ff76b97968cb5030967d7d6f76b2233` | `a350455d376f2e17f4da8571305d2494f1683a7932979d7ba7e2a81e24bac1d0` |
| `criterion-type-sound` | `Toy.Packed.not_misalignable_of_powTwo_respectsPacking_dvd_typeGA` | `Classical.choice`, `Quot.sound`, `propext` | `404dfb3348704c999346b4317959c9cfdf9a33236fae9bb9afe2cce88f3f5b11` | `fa509ddc41687e712efd6927f9dc5cec68adb9f6c6aa1fffcf9279047015d48c` |
| `criterion-type-covers` | `Toy.Packed.critCovers_critType_of_powTwo_respectsPacking` | `Classical.choice`, `Quot.sound`, `propext` | `b6b674148763b9327a43340c01de7260fff36cf7d9204fa4ea0ed0b18ca1ba06` | `65ab045f6915c2870264dc1ed02741bdc257f908887c16c40115b7b6a6c22e47` |
| `criterion-type-exact-over-layouts` | `Toy.Packed.exists_respectsPacking_layout_misalignable_iff_not_dvd_typeGA_of_noRepeatStep_powTwo` | `Classical.choice`, `Quot.sound`, `propext` | `e5bdeb93864116a15492b8b0cd9bcdba87e883823b947e1a82d8e06af8d6f873` | `d67d8cf4addad734a3ef13fb65644e5a06557963b47c8660d1120294c6281c3e` |
| `criterion-leaf-misses` | `Toy.Packed.leafOnlyCrit_misses_nested_field` | `Quot.sound`, `propext` | `6024fe891e1aa365f335330f164998dc09f029505efbee23332d8de840c58292` | `02101e2e8d8df9fecba3cb2a018a438e9b6c1226dd38a54f8791f5dc902fef87` |
| `criterion-leaf-misses` | `Toy.Packed.leafOnlyCrit_misses_one_step_underaligned_parent` | `Quot.sound`, `propext` | `d645c718730dc0232d2b3ec0b0d56c2797ef1f836cc932b38f7789c470659e68` | `1903be1394b45d1917facc89585c0314725136316c508db4651daee1da476981` |
| `criterion-type-overstages-fixed-layout` | `Toy.Packed.typeCrit_overstages_fixed_layout` | `Quot.sound`, `propext` | `ceafd028373caf8729cdca0a1a3c413af881802e2480b68c34f1f8fc071700c8` | `1f249dc9fa5d9ef05b6b161d6517a3a51569958c40363535ffedba53412968a9` |
| `overstaging-aligned` | `Toy.Packed.overstaging_aligned_addrObs_changes_trace` | `propext` | `a4ddbc07073d3244a8968d2f0f4a74a8f29fd1a470b14d5c1e680569789a6465` | `b66f41b276101a418795227d728cc77ca0ee357928a92ac21def41d48664db54` |
| `box-free` | `Toy.Packed.boxMoveOut_dropsOnlyStaging_ub_boxFieldStaging_ok` | `Quot.sound`, `propext` | `fb2cb51f90652400076bdc62d3d8b8a0ea2f79fcfec459a3c0bcfcb9e4f01059` | `67616a52617d4759b2301d9c0048dd2768d0427a60f7d943157dcfb2ae5abbbc` |
| `box-free` | `Toy.Packed.progBox_moveOut_irrelevant` | `propext` | `aa56d0a7a82ae25fe0d862e7581af6d5551c8ce1d370bdf6e8e13afb4895e4d0` | `487656f95d8003aa10f19db8116faf1d737d845bbe6ff0c1598ee7c2a954fae8` |
| `completeness` | `Toy.Packed.noUB_forall_progs_iff_alignRelevantCovered` | `Quot.sound`, `propext` | `cd9b926fbbe3530183bd05a235d9da384f0e55f2f74023ad9beaa5f0d730d19f` | `0c1ab91566610014ac1b7f8a1dbb1e50e7ea1a27df6674321dedfa566dd30091` |
| `precision` | `Toy.Packed.run_eq_uninstrumented_map_toTrap` | `Quot.sound`, `propext` | `57be9a546304419b6149fc9b842bc1d9c55815d7472bb718d3510782e69fdf60` | `9c37d87f0d38cd17874ff3899b1fe229d510316f4e9180f12ca26b722d4bdf12` |
| `escape` | `Toy.Packed.srcInstrumented_rawDropInPlace_misaligned_escapes` | `Quot.sound`, `propext` | `bc00758e9af0ce4769ea3847576d17e17d8e51b01e24bf5c3419f8f15cb813ab` | `122241527b799a74c7a706e5aec74efcc3f1c98d51fb524ca79a452d473866e0` |
| `sufficiency` | `Toy.Packed.noUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned_srcRefsInstrumented` | `Classical.choice`, `Quot.sound`, `propext` | `4c06e677fefe595d66c30429f0704952849dbe57e4f7f43b6d1980dae0f3d081` | `8bb6d4ff2bb71e499203a3c65c5755b45e192307192aa9839437c7029a1893af` |
| `sufficiency-shim` | `Toy.Packed.noShimUB_of_frameAligned_covers_alignedTemps_clientPtrsAligned` | `Classical.choice`, `Quot.sound`, `propext` | `657377a52869c0754a9b293745e28f7878f69a67f0014ba428364b4ffe36e045` | `53876f58e07df09b8278121b1e176f05b0201cada08e2e1810e23d1025194d64` |
| `no-stuck` | `Toy.Packed.noStuck_of_stagedSized` | `Quot.sound`, `propext` | `bf6aa953513b505fa97fadd5fc583e495ef248d455288fb59c7910765700095f` | `2e02aaad46625a539af06189ce7d49ef1140692f7ef5aa3641b918eee1d03324` |

### Kernel-check record: witnesses, counterexamples, positive controls and cited declarations

All 271 further names referenced by `results.json` (non-vacuity witnesses, positive
controls, tightness counterexamples, and every definition and auxiliary declaration cited by
name).

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Packed.AddrBlind` | `propext` | `4ef94a0752f84d7fe1f3ce4ae4c75235bca9a8e145a4d5abef0941a061b75dbe` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.AlignRelevantCovered` | `propext` | `70f4dab516d8a2a65312438445e7596d175d9652626f291989a04a1a3fe92837` | `a1353f4a6c2a0fffcaceb938f910deef7208a7f837d69e1ca681ad4038435bea` |
| `Toy.Packed.AllEv` | (none) | `7db020444d3ccaeae0b18ffe194ebc80d92626f4d02d7f998da607135a59a6f4` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.BodyId` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Cfg` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Cfg.unstaged` | (none) | `ee76baab42b5c06ac5c60063ec0a1763667fe9dcc0da0c4f08145c92976dd9ac` | `754c8210fe35fbbcaafb6606354f1174201928df3d6c2d049cc09f3128590603` |
| `Toy.Packed.ClientPtrsAligned` | `propext` | `1bc9ac6d95f76a7e894669b687ba2b57195e06f080584046dc65d4233ca68236` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.Crit` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.CritCovers` | `propext` | `336bae64b67d024a662dc4bdc5a526990a5bb267134e289defb172018eb8db1b` | `7b867a5ad11c2ebe8a5693227f88d93b8408899e55db845b9ea1b54a2ac4c132` |
| `Toy.Packed.Env` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Env.align` | `propext` | `6492cc6b185039d4e8d629b03f89a8e092629221b5c7a7c319dc81a29f1797a0` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.Env.field?` | `propext` | `55573211ed59258667e0a4209b647dc800a2bdfc44e2ac8f9e802a6562b59b43` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.Env.fields` | `propext` | `8d0ebce69f5de270d77d4b791fc648282f9ca6eabe402648056fcba5ff1bd79d` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.Env.isBox` | `propext` | `723f69be70c327d62da3ef4b3165b1332c9542551e0164b8dca4cf448533b0e0` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.Env.ty` | `propext` | `de414ef6e0b73f37c1010e57545670f7c41d60baf8d35733a6be908df4a6a152` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.Ev` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Ev.isShimUB` | `propext` | `063f6f8fedcd79a5fd52c1c05fe65e4b5602ee84b505c32a0ce2f06b91995705` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.Ev.isStuck` | `propext` | `063f6f8fedcd79a5fd52c1c05fe65e4b5602ee84b505c32a0ce2f06b91995705` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.Ev.isUB` | `propext` | `063f6f8fedcd79a5fd52c1c05fe65e4b5602ee84b505c32a0ce2f06b91995705` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.FieldIdsDecreasing` | `propext` | `c21f3a4361ce8bee33954f5afc6348c0f8fa10ad8fc9f0b0a7e06579122e8606` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.FrameAligned` | `propext` | `1bc9ac6d95f76a7e894669b687ba2b57195e06f080584046dc65d4233ca68236` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.IsPow2` | (none) | `30ae8e47239fc41a197c9b27201d14f120873072f733cbd240e2182e6746abb8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Kind` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.LA` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LB` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LOuter` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LP2` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LQ` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LRP` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.LW` | (none) | `f6cde5889254f3f2381490aaac09439cfaa4e73ccb4a6abb95395ca8354fe5b2` | `6d57d6390cd8024ddc0bc80363fec0e4f053a7cc89af90813bdd57bf0ced4861` |
| `Toy.Packed.Layout` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Misalignable` | (none) | `c7584579304c393569bef6ae8232654a8c10bd598b157435f0dfe88d7cec8b8a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Mode` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.NoRepeatStep` | `propext` | `5be52c1ae25a100f58a8bef93e2a263246d2113f26113e67b0a54ea5843f9071` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.NoShimUB` | `propext` | `fa4da98b6297de1b765b23f79e230a3c3f768636625e6d17f996a07e181706f2` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.NoStuck` | `propext` | `fa4da98b6297de1b765b23f79e230a3c3f768636625e6d17f996a07e181706f2` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.NoUB` | `propext` | `fa4da98b6297de1b765b23f79e230a3c3f768636625e6d17f996a07e181706f2` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.Op` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Op.isRawRef` | `propext` | `53aa2239229aeb7fe8e3a26ae202d97934ca48a36eb80b9a5fcd966c5c6a96c7` | `612d2c88c23abb51531cca465f4c54063be76c032afed485a773647d156a0afe` |
| `Toy.Packed.Op.isSafe` | (none) | `53aa2239229aeb7fe8e3a26ae202d97934ca48a36eb80b9a5fcd966c5c6a96c7` | `612d2c88c23abb51531cca465f4c54063be76c032afed485a773647d156a0afe` |
| `Toy.Packed.Op.ptrAligned` | `propext` | `66571293428b8bbe0dda4f3f276a491005297e854eb2787307f67bf2d448cc2c` | `93a07eeb34523d124fd4c6cbd940a58b3f60a5afb1d4fa77f6e116b6a803b8f3` |
| `Toy.Packed.Op.shimRoot` | `propext` | `02641ce2b6ef2e304c067558a922c19308d7bc42495c550ddcd7ed599fce4c97` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.Origin` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Out` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Out.andThen` | (none) | `9c3d189d6f0595f5bca58effe5b024d6c001776478f3e3298613142305b71a71` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.Place` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Pos` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Pos.staged` | (none) | `61e1e7894e60e70a968581d3fd8c018bff7a684a6823a6d89e65eb5ed18623f4` | `98673a9465e750223a4cdb7d8b9c7650443111430110d674d7258b5833a57484` |
| `Toy.Packed.PowTwoAligns` | `propext` | `c21f3a4361ce8bee33954f5afc6348c0f8fa10ad8fc9f0b0a7e06579122e8606` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.PrRel` | `propext` | `843cfb67d9bb47f5b6748c628e290fc6d290aea0cb52338f6656f6a6f22d4781` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.Prog` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.Prog.fuel` | (none) | `91d656f980e4cc687ad3150e5db1794aeb396658bcadea5a6dc8e1fc84791d66` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.Prog.place` | `propext` | `f4fb43bb7dd21dbdac6f7cfc3bdd1f6e83a0347e56b234a05d71a0db043d2fcd` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.Reached` | `propext` | `a6bc4cf96fbfe4c3af36175339061d38e82e8761e8fdb7cc8071d54d2edf785f` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.RespectsPacking` | `propext` | `830a171a1de1e8f2056a390099717134ede6aaa7fe220d4f9a8e0bc74eb4a9a5` | `8dd3ab17ea896bf8a5c3849258c49e97ba461cd72effab014708ad591799521c` |
| `Toy.Packed.SafeSrc` | (none) | `1bc9ac6d95f76a7e894669b687ba2b57195e06f080584046dc65d4233ca68236` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.ShimKind` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.SrcRefsInstrumented` | `propext` | `336bae64b67d024a662dc4bdc5a526990a5bb267134e289defb172018eb8db1b` | `7b867a5ad11c2ebe8a5693227f88d93b8408899e55db845b9ea1b54a2ac4c132` |
| `Toy.Packed.StRel` | `propext` | `8ce1a3e88fe58feceba7830b162fb655f0cfeba0a0fa696d9021453dbb9c6ee9` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.StagedAddrBlind` | `propext` | `336bae64b67d024a662dc4bdc5a526990a5bb267134e289defb172018eb8db1b` | `7b867a5ad11c2ebe8a5693227f88d93b8408899e55db845b9ea1b54a2ac4c132` |
| `Toy.Packed.StagedSized` | `propext` | `336bae64b67d024a662dc4bdc5a526990a5bb267134e289defb172018eb8db1b` | `7b867a5ad11c2ebe8a5693227f88d93b8408899e55db845b9ea1b54a2ac4c132` |
| `Toy.Packed.TempsAligned` | `propext` | `336bae64b67d024a662dc4bdc5a526990a5bb267134e289defb172018eb8db1b` | `7b867a5ad11c2ebe8a5693227f88d93b8408899e55db845b9ea1b54a2ac4c132` |
| `Toy.Packed.TyInfo` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.VName` | (none) | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Packed.VName.child` | (none) | `2f8a1de1a110882a280c3523146144c32631225089f67f86eb3a6e22e987fbaf` | `56ee27d6745eb73093e979a43baac01d915482ec339d528daa2f9b569daf3dc0` |
| `Toy.Packed.addrBlind_box_pos` | `propext` | `50f2e473556579aa6f447ee7920065eb8f2e95e98a86dc161879a79937cafd89` | `186b7fb9ba035d7ca9275846ae1b45fa5ab7c7fc6090fb71040a51685e32a318` |
| `Toy.Packed.addrBlind_neg` | `propext` | `cd63ad7655d626453a51635c592a8745a68c213f1d7a31bf85fa338f82e3f53e` | `4dc5f06c534914979fb9a48638ea7bd8330743af748691b269d5c30ff103d804` |
| `Toy.Packed.addrBlind_pos` | `propext` | `d17da099dd64f05d655c09b7003f60850420458cc7f4fde97acec5e95899aa16` | `0d33584f0c7654d5ebd965dfb25d40ab1fff3a781c5ee1b6edecdb8782ccb110` |
| `Toy.Packed.alignRelevantCovered_existing_shims` | `Quot.sound`, `propext` | `571ac29f56ac2fa82a3afb641d97ed9697f298c1a6f1cd9838d35c77e779c12d` | `0b50e75f3cdd54bb16bd40753ca3e62723b2cfe96389de4f3d9e41b24cc44fbf` |
| `Toy.Packed.alignRelevantCovered_neg` | `propext` | `e4d4a02a0eb85a6bcade7c590ffa4994a5c5b33de06111fedc4b48321fa8ba5f` | `0c26c32bd0e6a77cc1dc54ac865496a6b278360382eb82a701064de3892dfe49` |
| `Toy.Packed.alignRelevantCovered_pos` | `propext` | `d54511c5d2a4c5e5718ddfa841fb3d6cb8dca9ff74424d922e2f8d57ab2339f7` | `fbc598063978143f2f275891cfccbfa7176eb45e5ecdce8f1de2636f2ade7188` |
| `Toy.Packed.alignRelevantCovered_trivial_align_one` | `propext` | `c83cbb4f33c336cfc6eb23e98c97b9ece53cfd011ade4037bf5f72080ee213fe` | `9a498cd9befbf9b00ba3ace99d45918a254d26f5fd4f593afbb2d88afa07070a` |
| `Toy.Packed.bodyPositions` | `propext` | `8fa7727e97de2cbeedb32665c5653b6ff66411f242c0f20690227a007879208c` | `fa55bf869a3b24fae06f2c4074f6ffec499a1adf72fe6245fa4089fa107004ea` |
| `Toy.Packed.callsShim` | `propext` | `a4ee84bfe706a2767672ed2ebb310583903ac628ecdac2971eeb65876b0666a9` | `d5c11cbb0a0ba49558120e15804f4d4ed566f210936ecd76ea42a94fc13fe60f` |
| `Toy.Packed.callsShim_neg` | `propext` | `44be0f4421b5091e9f39ec7f3944c9d7050cce334a9df0eeca94b329e78db010` | `7f82addfc7f1827f38d79964d646957523f5a96a41d904988a4da04f1e6a80a1` |
| `Toy.Packed.callsShim_pos` | `propext` | `6c548a688d7e874fe6531a20cf4c0d6b107b788ba1be51b3cd90498e4f6d29cb` | `7f82addfc7f1827f38d79964d646957523f5a96a41d904988a4da04f1e6a80a1` |
| `Toy.Packed.cfgDropsOnly` | `propext` | `3c3862af84fff0c69c6415ae1fbef6bdf857cc2c759eaae091c2d0b6442670a5` | `754c8210fe35fbbcaafb6606354f1174201928df3d6c2d049cc09f3128590603` |
| `Toy.Packed.cfgNone` | (none) | `3c3862af84fff0c69c6415ae1fbef6bdf857cc2c759eaae091c2d0b6442670a5` | `754c8210fe35fbbcaafb6606354f1174201928df3d6c2d049cc09f3128590603` |
| `Toy.Packed.cfgSrc` | `propext` | `3c3862af84fff0c69c6415ae1fbef6bdf857cc2c759eaae091c2d0b6442670a5` | `754c8210fe35fbbcaafb6606354f1174201928df3d6c2d049cc09f3128590603` |
| `Toy.Packed.cfgTmp2` | `propext` | `3c3862af84fff0c69c6415ae1fbef6bdf857cc2c759eaae091c2d0b6442670a5` | `754c8210fe35fbbcaafb6606354f1174201928df3d6c2d049cc09f3128590603` |
| `Toy.Packed.cfgType` | `propext` | `100b206c2437f81f1302108637f7e8fe27be5b9a884b06501b6352a55fde0fcb` | `495459914ae19952df7f6d7818b987c2585f8007252b06afdadcd127388c4028` |
| `Toy.Packed.clientPtrsAligned_and_srcRefsInstrumented_of_safeSrc` | `propext` | `0b76c1a99e4a05d7d966eaa730b07031e5c5371663656bb5ebfa068142d146f3` | `d0d6e38469a699f3aed52c6780ee64b35435e441d5342c5edb0fdc3e2640508d` |
| `Toy.Packed.clientPtrsAligned_neg` | `propext` | `467fbfdedb48079b8e8062c7b2abc3eb17ac6c1abd034f6391731365bc335dab` | `47d50c62bd2c1e78086d7731377627b75f77c8c0f020ad7f9db86b5ae6ced50e` |
| `Toy.Packed.clientPtrsAligned_pos` | `propext` | `7a251bdafe22faaa63be43136ed4e9c5d1bac541a2f209abfcbea97df5efdf13` | `29bf496c0779fbf331cacf8cfb3362f1fed5e118481f718ff57da5543ef347e9` |
| `Toy.Packed.compStep` | `propext` | `ebf1432b6a03430387a160c853871dbb148e564db899564cc9b35d8a28de1e0e` | `1f1850de9d796005f1902780aee966f9543c79b9881d8d6391b2d8958eb368d5` |
| `Toy.Packed.completeness_witness` | `propext` | `247f014b307bb50d454bea3694ea068ce7c748eba58ae8d4e8c45c091eb2db27` | `694bb83edb8bd968fd11a1dd2406c72cd0b363b9acefec0eae761bc9f32283f4` |
| `Toy.Packed.copies` | `propext` | `278e8c24d5e9ec3bfea05bb5385dd283f9d8ac9b560a316887ab977f6823f216` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.critAll` | (none) | `b6315df70da8066a3aba3c51ca003214d78c502250b2559822123f562fb9fdc2` | `04dacd3558668ffa60a7601d663c1bd5d7691e2cea2a9a67e22ce05ae5c09002` |
| `Toy.Packed.critCovers_and_frameAligned_counterexamples_stage_nothing` | `Quot.sound`, `propext` | `4fc6d94a047cd526268928393456b2e3c3e1ca7a1d252bf0522665865e175881` | `f492e7f86dc8be54feeb18a105e001d62136473ff396ef17056030b9594a3c7e` |
| `Toy.Packed.critCovers_critType_fails_without_powTwo` | `Quot.sound`, `propext` | `197695075ede2f785afb816c5bdeefec3af158fe9b9137a0854ec4728ee3d1ed` | `1554f5d712e7e73aadb787363eb89dc931c6269c3529047e1d7afb61f4d78d70` |
| `Toy.Packed.critCovers_critType_fails_without_respectsPacking` | `Quot.sound`, `propext` | `0d13cc2fa24e851380c47c87382ea2bbcd0683f7972663274f84024814fcc31d` | `040ca79f82a5b757d00321e9a3449946f59583e2e58e831035397f48d502866d` |
| `Toy.Packed.critCovers_critType_hyps_hold` | `Quot.sound`, `propext` | `07f859efc82c3eb95c902bce3a3077fb59a199e10b3f606a03442f81240479d8` | `a5deb8228f378342fc31d1b2142f25b2f3c2e40b5c36cf6d8eb6672e1ccac6b8` |
| `Toy.Packed.critCovers_neg` | `Quot.sound`, `propext` | `53d2c69768555cddb7c09c6ab4a482ff3324049ebd70f14f26a424a15e6344af` | `70cfdb1ab93a90865c6bf9f108aea3467ceb2afd1723df0cd95e383e7bc120c0` |
| `Toy.Packed.critCovers_pos` | `Quot.sound`, `propext` | `d499d6587b60166daaf06561a67151cafbd8d59461ae470b57aa9482b7da48d0` | `9a1d6ec1912abf6823bc851e6840ead92e7feaea5c06d7ceb88c7318b38f5888` |
| `Toy.Packed.critExact` | `propext` | `183bfba10d595fb8bd22d0ac77bc9ba24c14ff5c99304c26838ac833cb84aeb9` | `71751a857405825d9961c701790d8e458a0355adfaada9671add481ba3ed5c08` |
| `Toy.Packed.critExact_neg` | `propext` | `9156f142d171f1dfe59ab829494d96db383eedf81c5ab94f7242efb48d9a5b4b` | `27f4a412860b4af69a31f4865c47890f05ba3e857993b8df9f71449897de086f` |
| `Toy.Packed.critExact_pos` | `propext` | `46a314535e4c2c95235f0ccd9444249984b8cb0fbaa2e65f759c1b0eab45ca54` | `246de90953e9d0eb3463d69f123403131190b7683cc89c32eac69439ea5f9564` |
| `Toy.Packed.critLeaf` | `propext` | `68e5a5aafccf680b9845023b03b0d0b7ea330b34b7b2085bb9342c910b344e73` | `e91b057a2f6440912adae7402dc029462ee7fda5e0d46dc11488ddd8070da5d6` |
| `Toy.Packed.critLeaf_neg` | `propext` | `bf7ea07b2c4008db98c566a2a78d034362424d610fae0fb488e7c16f070176c0` | `847bbce19fd9731fe416f32f12393f1dcb38eeb854150d2946bb2162223894d7` |
| `Toy.Packed.critLeaf_pos` | `propext` | `d9a299dd4fdb4d54667c5901f625bd30a8725a4792b352699a8661f079c60b8b` | `af24e1ff83e799da6a8db9d195352406a26778327b1949d4a9424f3ec1012082` |
| `Toy.Packed.critNone` | (none) | `b6315df70da8066a3aba3c51ca003214d78c502250b2559822123f562fb9fdc2` | `04dacd3558668ffa60a7601d663c1bd5d7691e2cea2a9a67e22ce05ae5c09002` |
| `Toy.Packed.critType` | `propext` | `68e5a5aafccf680b9845023b03b0d0b7ea330b34b7b2085bb9342c910b344e73` | `e91b057a2f6440912adae7402dc029462ee7fda5e0d46dc11488ddd8070da5d6` |
| `Toy.Packed.critType_eq_critExact_packed2_align8` | `Quot.sound`, `propext` | `e01751c17594a1c3eb1d1debbf949da8880608ec82b150d83a43eba96f3a1bd9` | `f8caabd7d31afd134d7a6be7fa127025a3151504a98bf060b860cbc1fb45a3a9` |
| `Toy.Packed.critType_neg` | `propext` | `6d7cdbf640078ee474a409cfeeeeccb84d8865c4f2f8dfcd3a812b17bfaa9cd1` | `4a32eca128967c3f0cde2feebcf3a9014cb0cc7b50cb530c230f7db679b9bec7` |
| `Toy.Packed.critType_pos` | `propext` | `b4b03bb618b3d478736033082019ebf37ac3369ec778319cb22378fd974fd479` | `4a32eca128967c3f0cde2feebcf3a9014cb0cc7b50cb530c230f7db679b9bec7` |
| `Toy.Packed.dropsOnly` | (none) | `eae3df630ca081089121bf09a0cd4279bbe85453c79ea74d8cd0636a20b8f543` | `04dacd3558668ffa60a7601d663c1bd5d7691e2cea2a9a67e22ce05ae5c09002` |
| `Toy.Packed.dropsOnly_neg` | `propext` | `fa566f8e651fb2645e4dfbdb959613de59c36ed42b81c82a2ec7c51cd12137db` | `0e507f0381be0872129e684a1489fa63eeb9fe52f53c748dadf684cc0e26a222` |
| `Toy.Packed.dropsOnly_pos` | `propext` | `2276f220101349679c3828f72067686503e165c2e074ed3f49371d26ad09fa81` | `0e507f0381be0872129e684a1489fa63eeb9fe52f53c748dadf684cc0e26a222` |
| `Toy.Packed.effAlign` | `propext` | `128d8110ba7d226c44d818c46229203f9e98740be7af52a9ae5d5cd87d04dd98` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.effAlign_neg` | `propext` | `5bf910319e43d106b9a1f3caa3ef290369c3d4de902b362a83a66c08cac853cc` | `3ef75781e2912adf5ab22a0500223aff212f661641e9070da1f6d66ebd8dee01` |
| `Toy.Packed.effAlign_out_of_range` | `propext` | `6c49fe0e2b24a59bf48f0324962647c3e6867e594bb8ea9db47aa542b6319c12` | `3ef75781e2912adf5ab22a0500223aff212f661641e9070da1f6d66ebd8dee01` |
| `Toy.Packed.effAlign_pos` | `propext` | `514b935033f50c3deef1615276bdd45d1a7ba406dbd61779862d42bf8957f2a5` | `a64a34492d8db9ff4935742c958c33054bf5d4f76fbfd46bacdffd8994ef0e35` |
| `Toy.Packed.envA` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envB` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envBoxObs` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envCyc` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envObs` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envOuter` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envP2` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envQ` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envRP` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envRev` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envU` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envUnder` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.envW` | (none) | `4fd0d4222d1f3486a780b752d9c9b0a774628d00104a954ea2b855d85d120b25` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.fieldIdsDecreasing_neg` | `propext` | `6b6ea223f0ff4d5848adf39ffb15f3d9674decc35d3139f11fa4e8252859abce` | `f723debb0353141961d057bce3565781c4b09640ccae773e5a9ba01b910cc0d1` |
| `Toy.Packed.fieldIdsDecreasing_pos` | `propext` | `cd3783be41e9cb407d1c9e5dd6d8d1cca1ed1d3597ad7790bbd026bc3f2bfdb7` | `49bac09bfde2e46a30684929ceda61444c73a2623d072cf3bf7a73859a394ec4` |
| `Toy.Packed.fieldIdsDecreasing_rejects_envRev` | `propext` | `5f215994d208d4af2b88b289ab242f4df0623aa74ba30079fcccde5987159d62` | `084bc128e54f263182fb5455aa17939ee5e026a7cd091199977c6e9795ca8bf8` |
| `Toy.Packed.frameAligned_neg` | `propext` | `91a3da86e15e8762c60010c7581d51772050b86170fbc957e0e73b92f9919e70` | `afb85cd2162a4badb296cf17619be817f8f9d70ec0dd20d5aac53619ec96242f` |
| `Toy.Packed.frameAligned_pos` | `propext` | `932b2a666a3a5be556d2e80b31fb3bc7a1036b65b3737864e8e92a2557bfea70` | `486d6bc222d5a2421fc4a398754d56055a7d25e0e0b34d25444aea24c9811cc8` |
| `Toy.Packed.heapAddr` | `propext` | `67c2204ed2509329da46d22b7d492e754a0e0e2b2627893ab3c2b5195d31b4c7` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.instrAll` | (none) | `24789093a461da4796ae745e1f4e591a76d11c61dba726bf27a6b2104973a689` | `8d085664253f5f471bde7cea9c5baa3ef8a11148432862c200cb9656bf917d43` |
| `Toy.Packed.instrNone` | (none) | `24789093a461da4796ae745e1f4e591a76d11c61dba726bf27a6b2104973a689` | `8d085664253f5f471bde7cea9c5baa3ef8a11148432862c200cb9656bf917d43` |
| `Toy.Packed.instrSrc` | (none) | `24789093a461da4796ae745e1f4e591a76d11c61dba726bf27a6b2104973a689` | `8d085664253f5f471bde7cea9c5baa3ef8a11148432862c200cb9656bf917d43` |
| `Toy.Packed.isPow2_neg_three` | `Quot.sound`, `propext` | `4cd5fd51025f50b94cb3a384b5430dbd1f2655dc3e26f564825266329b039579` | `a6e4f9e445fab83982b4738223d05008c1b695afed51b17c2c2e29fe5e76abf7` |
| `Toy.Packed.isPow2_neg_zero` | `Quot.sound`, `propext` | `774d407341e5cbe2431e30b35ad57e5833e619b1ba501a4fe398e0c33e5c6968` | `a6e4f9e445fab83982b4738223d05008c1b695afed51b17c2c2e29fe5e76abf7` |
| `Toy.Packed.isPow2_pos` | `Quot.sound`, `propext` | `d81c2ae6c50bd2cba9c20a31ef998ca04e68113c949df46ba3b27ed3506533f2` | `a6e4f9e445fab83982b4738223d05008c1b695afed51b17c2c2e29fe5e76abf7` |
| `Toy.Packed.leafOnlyCrit_stages_field_in_whole_drop` | `propext` | `5975178489297be1557aeb0ba5213763f1d12e4506d7a3e6640befed3def04ee` | `59337f583c9a3e5bba6eff4e83bcbf9e860f24b15d7aacf98ad83f1c9d015cf7` |
| `Toy.Packed.misalignable_align_zero` | `Quot.sound`, `propext` | `6686baafb2c39f208270bd94de229b4bdc12f9126630265d92d1928f5292d81a` | `a350455d376f2e17f4da8571305d2494f1683a7932979d7ba7e2a81e24bac1d0` |
| `Toy.Packed.misalignable_neg` | `Quot.sound`, `propext` | `ca3ffd179238ab286a4e87357e34b2337fd2dd58841dad3feb76ef2277cd0385` | `a350455d376f2e17f4da8571305d2494f1683a7932979d7ba7e2a81e24bac1d0` |
| `Toy.Packed.misalignable_pos` | `propext` | `676aefb608a5a46f5e28d7b748fc7d6afacf502332b1429f0181e1b5a96bbc17` | `a350455d376f2e17f4da8571305d2494f1683a7932979d7ba7e2a81e24bac1d0` |
| `Toy.Packed.needsDrop` | `propext` | `4ef94a0752f84d7fe1f3ce4ae4c75235bca9a8e145a4d5abef0941a061b75dbe` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.needsDrop_neg` | `propext` | `e53b9c7f927c2450324bb11aed5d965e90c2b77d0f3aa88483042e415b01c4bd` | `84e95f3fdc92662c664beeb42024c461ce7a87a857d30debec817d16072702ae` |
| `Toy.Packed.needsDrop_pos` | `propext` | `9ab598cb4d9eede6499dfc3cff6a77c0eecb1af93397182a070192485f6bcec5` | `05dc1884052e9907e9762f19eb82ad806c473031a04e775d2fbfaa1b9d960e82` |
| `Toy.Packed.noRepeatStep_cyc_short` | `propext` | `30baefd36f5fc92ba8aca02c4cfb2747012fa41616f7032bbff872447005e9e6` | `58daf6558a8ab60248ee18cd511253f6d123a946030213d7359eb9d387431f18` |
| `Toy.Packed.noRepeatStep_neg` | `propext` | `9c1952bff0089e520d81e1b07368367e719f36a756042831206e09d28719b59a` | `58daf6558a8ab60248ee18cd511253f6d123a946030213d7359eb9d387431f18` |
| `Toy.Packed.noRepeatStep_of_fieldIdsDecreasing` | `Quot.sound`, `propext` | `c922f52adcf6a0a5b4d7d73b8db6ad9bfb5b15fbf7fc5ab53647bbbe67b03bb4` | `dc3ab54360641e305ee12faee3d8f2656a5143f115a739a3108df9b933369c5d` |
| `Toy.Packed.noRepeatStep_pos` | `propext` | `f88825bdb7685ffcaaa730c80d1f3b3498d4d5abfa2be9873b913f5420de568f` | `f2425952914d172cfdbdae8d88cc75e0c5ad8b92861bd528d4cdad440c1dc229` |
| `Toy.Packed.noShimUB_neg` | `propext` | `76ea3cdee2bf8ba2805467688a42e1470276224611d6a05a87c5d1ba2856c18a` | `9db96eb2d973822bd5612e2cb77190ac4a3f73c658512c540e59f8abce30c1ac` |
| `Toy.Packed.noShimUB_pos` | `propext` | `fe9db1296326b91e6ec91675c56b09ff8cbda5821751b732f5eec0a945e3eed0` | `9db96eb2d973822bd5612e2cb77190ac4a3f73c658512c540e59f8abce30c1ac` |
| `Toy.Packed.noStuck_fails_without_stagedSized` | `propext` | `e8617e4859b9c278868d73f5ff3bb35069b99e851a539e2f7115eff00d258b29` | `8add5c63db11ee61b91d400d0df2619acdde73511e23f25f83f0ee8122284cb6` |
| `Toy.Packed.noStuck_hyps_hold_progInPlace` | `propext` | `cfe391638cd29f069a7f09a71ea797a8e9669b0ae018a1c5d0578a0943a41997` | `fec2635a9ef19d4a723de260f6ac4ca2952321aa2874ef668521e63cf155505f` |
| `Toy.Packed.noStuck_neg` | `propext` | `ec953b717ecbfe97b8d73a28762d2cc902dc16e3e344cd343ca7af8eaf7f3fb1` | `4893d055183473e6d88ec84cbc946f0ba77ff5423919928c21e1c0c75136d56d` |
| `Toy.Packed.noStuck_pos` | `propext` | `15488bf81eb6714017655c6d8a1a2fbdf51a9724a05d7e008c981657ebcbf213` | `4893d055183473e6d88ec84cbc946f0ba77ff5423919928c21e1c0c75136d56d` |
| `Toy.Packed.noUB_neg` | `propext` | `9f1490a78a7db30de373eb2f33c5148ca42deb1dfa1ebf5b4a5ae8c2bf438a62` | `6564c298bccc94dd865a3ec5a04c564d66eb9881e292b53c8be7c31f598f3a44` |
| `Toy.Packed.noUB_pos` | `propext` | `5cd2d87cffe2ff41c7ad8613f95aa1e1a4fc7e799fb135eb9866d055fd31e183` | `6564c298bccc94dd865a3ec5a04c564d66eb9881e292b53c8be7c31f598f3a44` |
| `Toy.Packed.obs` | `propext` | `8fe206b476e12a9622d591e9d34ebaf7ce982637240e1492f85de799ff064c80` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.overstaging_aligned_place_sound_costs_copy` | `propext` | `a1c8337a4e5c3acdaa29853da9bf0ee1ad21b17d23a95421e1fd2ec5a551b210` | `2454a884e5445990810355bf73d3de8c5f29c136765b8bc57f8925d776e729f7` |
| `Toy.Packed.pathSteps` | `propext` | `dc92ff3345c4e26e3c068b570d7c0c42e57e4d9c71f4e3f4b97156ce877954fc` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.pathSteps_pos` | `propext` | `32e217f02a878793c9985dd1b0b0109cd84229c0a262b7e186feb03baa68b363` | `c3a93f520e13ca39b8fdf72c81c15a232d66177705667006307e240398c707c5` |
| `Toy.Packed.pathSteps_stop` | `propext` | `9e5e5e6885983c4b3e70e97f103338e15bac6ed1e80f02231dea3fdc4859b406` | `c3a93f520e13ca39b8fdf72c81c15a232d66177705667006307e240398c707c5` |
| `Toy.Packed.pos_resolve` | `Quot.sound`, `propext` | `c26d5569d0742701355282b6c6951fc62c6e5dc7a4d287efffaf35603ded5b8b` | `a86f6437a950cda8bb1df89ccc6d81f9c9fa7991929d939185650819f96cb42c` |
| `Toy.Packed.positions` | `propext` | `2d991a71e1bf99d46a5f2873197c6acc0f839e2267bee61f7eaf4db411ade04d` | `fd5f993cc423b8cc46add0fc28f6a6bfd10e4b472c6ce642e45ba1db3c3539da` |
| `Toy.Packed.positions_empty` | `propext` | `b9ce5fbdd0668937c84b1594b40a44100b97596f744ec8c4c8072a103d9764fa` | `8f1e27b9d1b7ec475bc4a0e27d9214c1e2a15bc1557f9c0f9744df77e12d9667` |
| `Toy.Packed.positions_progBox` | `propext` | `135ea7a6f69bab7e3d7cc35cfd0cbb586ebe505aba253f09a004c837d9775e1c` | `772ce2d1557be3a6b9988f59e9cd2dd80b9786344c29956ab4cf2d2adb4a0189` |
| `Toy.Packed.positions_progEscape` | `propext` | `d417019ce8c239982b59a31bddd3021506f8dfdcd47911981ca71bc771a7a702` | `55e7f2db43a7fc1015136686737013804a3231481aec8695c440e9cf58eb6f4d` |
| `Toy.Packed.positions_progInPlace` | `propext` | `0610b19bce243354a1b2a8e124fc0c7b4ce4d40e5ddfd03a6c516f620977fd0b` | `fa9d29b544934c86a4512d69cda8af28ffd54a0f19e243afb06d819da5d9829a` |
| `Toy.Packed.powTwoAligns_neg` | `Quot.sound`, `propext` | `0d19ac04a03838df6d2402932311f1d17503bec994f8993f7a418c14c4e15aff` | `b46d02206a7a5c1aee76b08f56bc222ba9b5e7d853e1bd72fee28fdfb97f8327` |
| `Toy.Packed.powTwoAligns_pos` | `Quot.sound`, `propext` | `b7aed13b80d1bf6814637416f2210d0dfddb5649061b10495baa94294bbb86c0` | `e5af8f47fbacbd69b1c515e8cfe9e86f23b2ddb6958165e6a576fcc790253ab2` |
| `Toy.Packed.progAligned` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progAlignedObs` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progBox` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progBoxNoMove` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progBoxObs` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progClient` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progEmptyU` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progEscape` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progInPlace` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progMisFrame` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progMixed` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progNested` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progObs` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progRP` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progU` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progUnder` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progUserRef` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progUserRef_stages_misalignable_position` | `Quot.sound`, `propext` | `8b7b07e41c4cf50f063bfd8cf7bf4b94489526fac5421697f7f079bd6c9518a0` | `bf418bf3c35c7ded7d9813e0056efbd69c11638a6b7d48339fa9715a338a52f6` |
| `Toy.Packed.progW` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.progWholeQ` | (none) | `f69eeaa5fd4b9f317294c63f408052324f229ea5136b98360b525c24d4fac7c4` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.rawCall_missing_shim_admitted` | `propext` | `ecd7efc79330e48fd2966918344e010debccdf78c0ce0ff78375146b056a0edb` | `b2decfe7f8b07dbda330479ddbe60a728213dc99d6158d5033578ef66278a435` |
| `Toy.Packed.rawCall_missing_shim_noop` | `propext` | `c38d5e0d1fa29e1a2481f800fd3cd31670e6fa2c89b897b0dcd28c4873ebc0cb` | `f62adadffe33be71ac7f25be2623fe84571ee2be309168b88a56b275dfc1f7ca` |
| `Toy.Packed.reach` | `propext` | `a146d2c9bdadcff66d22692afec954a195b88809dcb129dc5606120a0c6a616b` | `d5c11cbb0a0ba49558120e15804f4d4ed566f210936ecd76ea42a94fc13fe60f` |
| `Toy.Packed.reach_pos` | `propext` | `a7f9bb32b1e7194d5560163163e34698bdf7e1974a7517cd157c5b51faac82a3` | `b6a4e377ffecf06c145187953fd7905f8e6394f01288290d5a50385b875a7c17` |
| `Toy.Packed.reachableShims` | `propext` | `61230936bcc211b4b27e6fa6572fe4683942c626524b6f59642a1a4d2b1ef17a` | `8f5122b7da7cf3b892fcfc37fe3fc6d4f77fb03ab6291cbbc27703bee1689798` |
| `Toy.Packed.refStep` | `propext` | `ca589e767a42c7694553e82e2f3b15516b5c1277221b44891fbf11da3ea26657` | `46beb9a8c8a56ff4cb80f3ab964b97c254afca854e94e20aff55867c1b54502c` |
| `Toy.Packed.refStep_align_one` | `propext` | `4724899527b5a9df2adf540a989d86678c13ca4c8278526dfaeb32b0e641ba14` | `2d289651c69c7a6d840a8e8b252e9a84f1b5b25d83649cb88fdbbfea641d89fa` |
| `Toy.Packed.refStep_ideal` | `propext` | `850e04cd26a827c2aca4544b8e1989760ae8f3886e60091f4d1135b94f449a91` | `a6f7a957d9b0daffa1b2e07d9689a41a9ec7b7661f37fb645b458ef4ca89ea91` |
| `Toy.Packed.refStep_neg` | `propext` | `0113c8b6ded7b2e32810053c5f7e079e15c261357bfd1c83fe92d724b9834176` | `a6f7a957d9b0daffa1b2e07d9689a41a9ec7b7661f37fb645b458ef4ca89ea91` |
| `Toy.Packed.refStep_pos` | `propext` | `a77df58209c221161a0491f80e4d0249b48e2810f3d20a755c10d91e6f00abe7` | `a6f7a957d9b0daffa1b2e07d9689a41a9ec7b7661f37fb645b458ef4ca89ea91` |
| `Toy.Packed.refStep_trap` | `propext` | `a0c714361aa5655c128edaeb8aa60bf92b037ddd1d682c4d56b556f02aa1801d` | `7cd36284b2f16391ae8016aff2ce984cd9c89afae52258d0ed4cfc32e85b3507` |
| `Toy.Packed.resolve` | `propext` | `0577249867efba4f5cc5082d4981f78700af4a36f6c644c790ce0f3df68ab18d` | `8dd3ab17ea896bf8a5c3849258c49e97ba461cd72effab014708ad591799521c` |
| `Toy.Packed.resolve_dvd` | `propext` | `c28ff8fc1eda420077a38afdbde15a3e98076b204f9ea719ea0e69b1c38a22ae` | `f63b38b4c69cca6fbc4721461343ae0b83518c0c41864febc103081c45f37f61` |
| `Toy.Packed.resolve_indicator` | `Quot.sound`, `propext` | `4976b8ec8aa4b78e231316b4d7de67fca4d0b502d7d0cf89790eb58432bedfde` | `a959c16793aeaff5a4b09a98b7a122a6f8600865e1d432259a489229643d15e8` |
| `Toy.Packed.resolve_neg` | `propext` | `a7851821d310064362a900dcaf65e4e5aaa7ec67081d22fb28cd3e327b1cb62a` | `10b97c25b43ebdce81f15e01f48ba99145d4c195e18b151388a96f52f73e8b1f` |
| `Toy.Packed.resolve_pos` | `propext` | `620962d6847b3efcf22d8fd7ad3a7b9cbf3cb98dc36602f5eec69e3c1ab10a07` | `10b97c25b43ebdce81f15e01f48ba99145d4c195e18b151388a96f52f73e8b1f` |
| `Toy.Packed.respectsPacking_neg` | `propext` | `87a0a83264997a162285a6e05fb8a5272c095b9372a14fd23f6dd2777f1f2254` | `53610cd4874960be47239d0bb3fb9074cfa3be996529ca3baee0c9976ec0fc29` |
| `Toy.Packed.respectsPacking_pos` | `propext` | `79a852258de8adc97cbcad45c008bee379df47b66908e862dd8015ee0615b072` | `9f419997bd5fa1ac77cb91de64568b8f32e107d8092cbf4edceba487db9769e1` |
| `Toy.Packed.run` | `propext` | `6d112316c1a1116527ad6a06c3d75e20b0528c3d0f178aa446bfbcce7b9f4a93` | `7c01319de3e6c6980b273667a1775994f34263d97ddf6efbc5175faf819237c4` |
| `Toy.Packed.runShim` | `propext` | `3717b79caf90e79ae5eddc8783386268d17b18e33097472884ebdafc3dc7c975` | `3b56b53ab7f5b4977d99c6b72f6a3bbd81c5b6a47e190799ae847020dfc13a04` |
| `Toy.Packed.runShim_noStuck` | `Quot.sound`, `propext` | `bad4669798066753f0bceb2260e5b9463612bf1e3d48a6623e8717e7cd8fc7d5` | `2368bdebc0dacf97f9493b9a0f9182526d3c9ab6154253effb7fa1d8defcac12` |
| `Toy.Packed.runShim_noUB_of_aligned` | `Classical.choice`, `Quot.sound`, `propext` | `cd73cb1303ce9031cb138b8ebd589511ff9e38e46cdc197195192f31efd87e24` | `3ac9ab79106e9eb00f9ea3280f327c60319afae8b3a4ea73f4664ad11829d8ef` |
| `Toy.Packed.runShim_noUB_of_covered` | `propext` | `268df9560d60f4b7affc00613817db5cd1fd302b5178b5bff290639254af83c4` | `744cc2af7d135a8e93f1a01c40d7d0c596aa152d30363449ff9d22b6323b16df` |
| `Toy.Packed.runShim_precision` | `Quot.sound`, `propext` | `da61335d79fc868382e8a5beb8d548a543ad1d2ea2e545b05bd2b382594a140d` | `d3901ae7af0ee11bd604af37f346518087003946171eafed60eecbcabdb854eb` |
| `Toy.Packed.runShim_staging` | `Classical.choice`, `Quot.sound`, `propext` | `a9422f6c0202be987a66c678d3a65092f44fc377af5d06a7ce816eb35df7cc18` | `7d7ca6d3ec63bdf32d84f41ba09cb3bd66ab23bea2b696f72cd20f4f7b2d49c5` |
| `Toy.Packed.safeSrc_neg` | (none) | `aeceb97d3643eac94fc1355a2845259e0196ea46c996cf778a5b76cce30b051c` | `c95b3736170c75826833dbc20d5ae0d354a23fe7de30c614acd4585969725b33` |
| `Toy.Packed.safeSrc_pos` | (none) | `02ee1cccb471f3ced2c1e599cbe6ffc1e2d01c511a6a9ae97b54c0f43b4b9dd3` | `6a17f87110cf13785392387234affc0d3d22f3dc235dd5343e457b7d5c465f26` |
| `Toy.Packed.seqFields` | (none) | `3613bdc872f9f97ec35ed2a7e0a3c4154842789bb0c0d8f45e3e8310e956e3ed` | `250d6405f3b3ebf16df353322f716294e2dbfb34a2e40b4b3fb73515e710ea06` |
| `Toy.Packed.shimExists` | `propext` | `cd0aa667f07643b018ddf7ce0e85078f3eace35f11246fa6694a66461885e73c` | `d5c11cbb0a0ba49558120e15804f4d4ed566f210936ecd76ea42a94fc13fe60f` |
| `Toy.Packed.shimExists_neg` | `propext` | `9786e9980ad17f2ecb2099de0dd29f3e09c7abafa054c8dba96329232d07ea74` | `20c1723675dc36ea7b8a0ec1b28879d7d191f6afa1308a86298bbdc2da932903` |
| `Toy.Packed.shimExists_pos` | `propext` | `e4a21ecf48754f0d28c5d819d3e821fafedad73fcb2f7aa739beeac0db50e085` | `02545cce4c6e6a4749ab955c1875c5ef9eb7895cccf7ee4fa7a15d2f389bf5f1` |
| `Toy.Packed.shimPositions` | `propext` | `2d991a71e1bf99d46a5f2873197c6acc0f839e2267bee61f7eaf4db411ade04d` | `fd5f993cc423b8cc46add0fc28f6a6bfd10e4b472c6ce642e45ba1db3c3539da` |
| `Toy.Packed.srcPositions` | `propext` | `2d991a71e1bf99d46a5f2873197c6acc0f839e2267bee61f7eaf4db411ade04d` | `fd5f993cc423b8cc46add0fc28f6a6bfd10e4b472c6ce642e45ba1db3c3539da` |
| `Toy.Packed.srcRefsInstrumented_neg` | `propext` | `0aefed787a1108d6ff58cf9755ef928480683a4bcb260782122a1de84b1166a9` | `9d19bde82a11fbb09b747012c0e544b509eb39402343553676ae4786df6d30f3` |
| `Toy.Packed.srcRefsInstrumented_pos` | `propext` | `bbaa04295e5e377d637a48cb2ddb687efff45116632862bc3ebcccc69d63072c` | `31062baea19c744236089c9f352fb57d62c0fa5414d80c0d587b5b8b8945ffea` |
| `Toy.Packed.srcStep` | `propext` | `b566ccc11031d3064cff65d2e19e399657f8480b3370bca56439f5272f72dbb5` | `7c01319de3e6c6980b273667a1775994f34263d97ddf6efbc5175faf819237c4` |
| `Toy.Packed.stagedAddrBlind_neg` | `propext` | `a54c3a331725ac6e8f0893a770594c4271395c4a82a3fabf8ae6a0388bfb3f08` | `3451def4656f01671326c20ad0ab5feeac7c9cc8cc7caafaa10e05d037c874fc` |
| `Toy.Packed.stagedAddrBlind_pos` | `propext` | `870e9a3a5b023e73e96d1c545133551ef151d661d58f0f4eb38b4c0f3eaf28c0` | `8545ff6403ef41c43b2debc0c8cb27a8d91c00ec6c5bb306e61e364c5a9fd9aa` |
| `Toy.Packed.stagedSized_neg` | `propext` | `2ccc7f22c4025e839151e16f7027a27a843c72253d19e42ec44c3e8c2e2c1068` | `74dbc08fac665c926236fc109ca5705067de68f3ba956d3bea37fede8b81d3d5` |
| `Toy.Packed.stagedSized_pos` | `propext` | `c3741d5362a18ea6e18edb9ad4f5db721796640d1586f126303907e71f908461` | `26e1b132e175cc0f133ab99643f0a274fbf16e6412c5ca8c06965e386d49997a` |
| `Toy.Packed.staging_box_of_addrObs_pointee` | `Quot.sound`, `propext` | `550f36795e2060b58fdb921fc35f41afec20bdefcfa06277c964b7bc2156ae7c` | `e997d5a2a9f6d2a9bbbcc91ecf8da773bc9651961c43b92a1a7fa1e756d52a90` |
| `Toy.Packed.staging_conclusion_progInPlace` | `propext` | `5f789df2c0b931d10cd81ecb18eef8726544effc296749a065ac8bf99b0c8e97` | `178760f2a29c4ae80a77f90385c541fee956cff111796ebcb04be454f5db55b5` |
| `Toy.Packed.staging_fails_without_critCovers` | `Quot.sound`, `propext` | `91cd230e15ccb3fef234508df2975461a71a698cd557617a0a2846ccc1267ab7` | `b7b5584a8bc206e2aa3712b4e8e9b879750881f86b89cae1fdbefa43db87fb18` |
| `Toy.Packed.staging_fails_without_frameAligned` | `Quot.sound`, `propext` | `be4ec915925fed098331ff0ea2c73ee91da6fb9de1493628fe5ea6970baec5c9` | `29c65ec1d185029a0f66c07d4a6cfd0c57e39767cacfdac7128c44749f3a27b2` |
| `Toy.Packed.staging_fails_without_safeSrc` | `Quot.sound`, `propext` | `8417dd419c4e245c00b9ccfbf67c41b21205099c0e24831648998ff426dbfebf` | `a6f51f18958d7bedfc638b0a53d08b71248671306f3efb41e7994487cdbf8a83` |
| `Toy.Packed.staging_fails_without_stagedAddrBlind` | `Quot.sound`, `propext` | `131a6230d44e98916244a38950df130dc583e64feb8bb523488c125e7b4d9cd9` | `344e81b7084bc9bbdf8b6ab2782b2298f168b18289ac09f44ed9dc697c5703d4` |
| `Toy.Packed.staging_fails_without_stagedSized` | `Quot.sound`, `propext` | `b6ddeb0db9ce404122c15e7257a6f9e43345aa36a258e934f0acec343ba039cc` | `3b9e60fbe7338faaa782cf2edf9fc5cc4418e223ca0dce9549de5ca83921ff1a` |
| `Toy.Packed.staging_fails_without_tempsAligned` | `Quot.sound`, `propext` | `0ad14bd2083e0f57f199c1fa2fe2177d7074fd3af562ef7b461061533871cf75` | `1215144af5eb857ae2587a0b770371ac69d7665f0d3c79dbab65de664a538a39` |
| `Toy.Packed.staging_hyps_hold_dropsOnly_progInPlace` | `Quot.sound`, `propext` | `b70373307964aaa07897ea2bb8326f8865255ce67ab45c7215bbca9c96453b10` | `5f23732ba47757f192e6591d1cc6b4644b613751977ca34151d51eb10b39d58f` |
| `Toy.Packed.staging_hyps_hold_progEmptyU` | `Quot.sound`, `propext` | `7b9c5b599cab5d1042afb421dcc897e545e557db2da3828fdc654fce9b4f998b` | `b7b0fc11ac8b8564c89b15a51ee1b405dec1a44d28ff52015277070b18a64e26` |
| `Toy.Packed.staging_hyps_hold_progInPlace` | `Quot.sound`, `propext` | `ac7efd8482f8135de87ffb748880535f4df5dafd61d67ea3f115fd47a33970c8` | `7edb109c12035814486e0763cbf7edec2a0fb22b64b12d70200ff7c9478b6098` |
| `Toy.Packed.sufficiency_fails_without_clientPtrsAligned` | `Quot.sound`, `propext` | `339ab27620cdab9125220419661aefdc962553848830b26bc754bc20fe79fc54` | `fd3cfcfd575d4fdd22dc866f377222018cd1a50e35e0edbbcf90b0eaed1948ac` |
| `Toy.Packed.sufficiency_fails_without_critCovers` | `Quot.sound`, `propext` | `1c65b0c3340af985f4dd6f69268175ec54d90a9505471e48491c057998925087` | `b5257096a893de6c9699cabb79b8d8ccdc68a4e9533b43c396451bb37ec494db` |
| `Toy.Packed.sufficiency_fails_without_frameAligned` | `Quot.sound`, `propext` | `d9018db04bf7a31261925700aa289a87e4fa60c73e56342a2d4013548f6601b5` | `e69565743947dafda238ffd9d405f0177c782a3d3289d5f19f2387ae941dc114` |
| `Toy.Packed.sufficiency_fails_without_srcRefsInstrumented` | `Quot.sound`, `propext` | `24b46f45a34eefa7d44c68fb5e86c535285cb6c8091ab0589ceb7b73793ede30` | `4097c8639d392f73a1531f8edb80bc4b7b7aa76f6ef09a4c980425bbef09b47a` |
| `Toy.Packed.sufficiency_fails_without_tempsAligned` | `Quot.sound`, `propext` | `216e528f7eb1d2a060a90b9b113204032a3666bc0542569f15d98ba3ad5e5bb5` | `5f54439ca83f02030b7ed4621a5537fa8134d338b0efea3571a14aa4721fcf5b` |
| `Toy.Packed.sufficiency_hyps_hold_progMixed` | `Quot.sound`, `propext` | `60adaa1d8ac08bb1e6cc1ac7f5f780e53f9b50a625169b927051044fc5e91264` | `8da46a9a251fe809f62f258be3ab8fd032393e1fdb52505314411eef54a978f0` |
| `Toy.Packed.sufficiency_hyps_hold_progU_stuck` | `Quot.sound`, `propext` | `8eb082ee1c397f40067f847436b89c6812e5c75f9dc8dc97d0fe7b59d40b365c` | `a36f586b61a73a95a4180bc8e3a12e9df569a2c5dd1069694ab2e5d64db56dca` |
| `Toy.Packed.tR2` | (none) | `24d6dfa950604f81d642377ccdb8c95cedd25368b45ca54e49aee7377df170ff` | `ae77f9e8fab862c01cf1454962dcd5eb201c19e76d953d6efe32d60a17785b73` |
| `Toy.Packed.tR4` | (none) | `24d6dfa950604f81d642377ccdb8c95cedd25368b45ca54e49aee7377df170ff` | `ae77f9e8fab862c01cf1454962dcd5eb201c19e76d953d6efe32d60a17785b73` |
| `Toy.Packed.tR4obs` | (none) | `24d6dfa950604f81d642377ccdb8c95cedd25368b45ca54e49aee7377df170ff` | `ae77f9e8fab862c01cf1454962dcd5eb201c19e76d953d6efe32d60a17785b73` |
| `Toy.Packed.tU8` | (none) | `24d6dfa950604f81d642377ccdb8c95cedd25368b45ca54e49aee7377df170ff` | `ae77f9e8fab862c01cf1454962dcd5eb201c19e76d953d6efe32d60a17785b73` |
| `Toy.Packed.tempsAligned_neg` | `propext` | `863d5e57f1ca5236e5f956d44e2c5d96cb61a3eb2674a4cb30f4eb60c59af31c` | `be6e58ec8f28b9626549fd58e1467a83c86e6a398c9d595175f32706bb33ac2b` |
| `Toy.Packed.tempsAligned_pos` | `propext` | `15e5fbed6d7173daa52e68e5d62ca7e068e31511a10d1806f11bbc87a9e32823` | `16c1c7cfef9ecbeaf58aa6bd42352ddc381ef77cd097e3b103f06174199185ea` |
| `Toy.Packed.toTrap` | `propext` | `090ac0cf5c13483789068406edcf0aa7b64695c4cebce5ac2a5e65f76f911de8` | `cd21208c0f39ae7447d974c446c960c34fd4f143cb0267ea5ec386c8af9bb460` |
| `Toy.Packed.typeAt` | `propext` | `f53fc95d662061fd1c3b828e3c586cc737817674d52f436cee0b39cc98334fb3` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.typeAt_neg` | `propext` | `e4f0109cf514bbb825822104e6ceae718390bcd67f8bdc3d5861f903265ffbf3` | `6d68a9216ee9e07fadf2cb84f970cf1f95719bc8eec517de63ab0e4b57fa336b` |
| `Toy.Packed.typeAt_pos` | `propext` | `63fc2ec97e8ca8aff17b0ada2df28cb9a088323caf035d89e4e9902ba4a3105d` | `6d68a9216ee9e07fadf2cb84f970cf1f95719bc8eec517de63ab0e4b57fa336b` |
| `Toy.Packed.typeGA` | `propext` | `d15668800fd93e253b24f1b626c29cf982d1778d6620baddcefb04cd5fcd8846` | `714eb6c0ac58130bcd05575fb7815118e96e4c35114c0f786e8db1fb9144b9ce` |
| `Toy.Packed.typeGA_cases` | `Quot.sound`, `propext` | `e8fc12bcc3314e26009cb33971fa2ca0d73259b863ad6b276134809c4ef4a6f7` | `e61cfb434c26157c3e2a92554281516f44c51b401a0b26730a9017c1905d47ac` |
| `Toy.Packed.typeGA_exact_fails_without_noRepeatStep` | `Quot.sound`, `propext` | `6411100df6b2ce857870b89cd1f86ce8f1b02df8cb7653403490eb70dbad260c` | `be14bdf0475bdf818fe4a54d85781681c72b8695c4735929c45c0fc36e389e8a` |
| `Toy.Packed.typeGA_exact_fails_without_powTwo` | `Quot.sound`, `propext` | `d25fa76c72e9c07814bbf1c67950c4a3c1add9795c641ca371ff7672bc4d1f86` | `6a4c012ee722ffa77cf7f7f286de480858221cef70456ca17b801053faee9110` |
| `Toy.Packed.typeGA_exact_fails_without_typeAt` | `Quot.sound`, `propext` | `e48b27644d23d1b7d9fc8980e841bb8195e9d3d83bd90dafb55f40df4b9e67ce` | `b8be0092521b9bc082baa8b3b95e08d76da814823bf5a2067fdd319bf26881ba` |
| `Toy.Packed.typeGA_exact_hyps_hold` | `Quot.sound`, `propext` | `37b196ed23ae2420acdda781625f8d8fdc7b716467f623f15ce9052f6905caea` | `ea6db0e61da414c9fb273806faca6ea464ea9777463050d29c3e8fc8300986d0` |
| `Toy.Packed.typeGA_neg` | `propext` | `3ffabc5979190049bca2213ea34686928ebdf1583ee9f0a956a62898438db4ae` | `7aac5481e8a019d609a670fbe2cf6f611d6a1eebf8a026a662ae9b03834180c8` |
| `Toy.Packed.typeGA_pos` | `propext` | `6f3cc8df0d3b971b47a4d7d38181ea48d5782bf2567f77d9c5ca7e57f26f10a1` | `7aac5481e8a019d609a670fbe2cf6f611d6a1eebf8a026a662ae9b03834180c8` |
| `Toy.Packed.typeGA_props` | `Classical.choice`, `Quot.sound`, `propext` | `32561ea2034a34a083c0f01af04c0d6061191f89190a551c9cd844b44d4bc3a3` | `6daf52e3e228ea1a2eee303918256c58eaceef81fcc396bb78f1a64cc108338d` |
| `Toy.Packed.typeGA_sound_fails_without_dvd` | `Quot.sound`, `propext` | `8011e5e51647fb71cdf289250e6f3b71cd6c451fba2c907e445a6d1a3713dfde` | `6d18e44a8065c0969515675fb972c58dd74eed813163fd284acb9779eecf2276` |
| `Toy.Packed.typeGA_sound_fails_without_powTwo` | `Quot.sound`, `propext` | `d4f84430a7728ca167794eda1bd7c06f740fc00b5b20ca88b75dd8e3a871db12` | `892bd2692c95b745b0e7519bfb678cee2612fe539a8f0c000f4ab930b289e79f` |
| `Toy.Packed.typeGA_sound_fails_without_resolve` | `Quot.sound`, `propext` | `133507281ad7cfbf77ee17527142d976d299b0cb77adc3efe6c757e2eaebe43f` | `6d18e44a8065c0969515675fb972c58dd74eed813163fd284acb9779eecf2276` |
| `Toy.Packed.typeGA_sound_fails_without_respectsPacking` | `Quot.sound`, `propext` | `2b7a315cd8ea968829eaedc153326aa1843c9e118c8132f1bb3911b75758adc9` | `fef4a254093bd07986baf8f0c8a0465cecb216b4373ebe3f3a20ac89a9342182` |
| `Toy.Packed.typeGA_sound_hyps_hold` | `Quot.sound`, `propext` | `65544371a7cc1ab8f618a78ca2c28d1924ff25252fca629cfa9dc3bd9a63f0d0` | `2afb13da3568432aa9d2db2074dfcf35c054dce064f1fd996a5c090c1c929bc7` |

### Primary sources

Every external quote below was checked against the file at the pinned revision on 2026-11-21;
`path@commit:A-B` gives the full line range of the quoted text. These documents are evidence of
documented behaviour (evidence role: documentation, or normative for the Rust Reference); they are
used in `derived (modeling bridge)` remarks and prior-art notes, never as a finding about an
implementation.

* The Rust Reference, `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:
  * `src/type-layout.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:638-639`
    (`r[layout.repr.alignment.constraint-alignment]`: "The alignment value must be a power of two
    from 1 up to 2<sup>29</sup>.");
  * `src/type-layout.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:647-648`
    (`r[layout.repr.alignment.packed-fields]`: "The alignments of each field, for the purpose of
    positioning fields, is the smaller of the specified alignment and the alignment of the field's
    type.");
  * `src/type-layout.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:653-654`
    (`r[layout.repr.alignment.constraint-exclusive]`, `align` and `packed` exclusive; cited, not
    quoted);
  * `src/behavior-considered-undefined.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:18-19`
    (`r[undefined.pointer-access]`), `:78-97` (`r[undefined.misaligned]` through
    `r[undefined.misaligned.packed]`), including `:90-91` (`r[undefined.misaligned.raw]`),
    `:93-94` (`r[undefined.misaligned.reference]`) and `:96-97` (`r[undefined.misaligned.packed]`),
    and `:151-152` (`r[undefined.validity.reference-box]`);
  * `src/destructors.md@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:8-11` (`r[destructors.operation]`:
    "The destructor of a type `T` consists of: … 1. If `T: Drop`, calling
    [`<T as core::ops::Drop>::drop`](core::ops::Drop::drop) 2. Recursively running the destructor
    of all of its fields.").
* `rust-lang/rust` commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (2026-08-05):
  * `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:9-11`
    ("This pass moves values being dropped that are within a packed struct to a separate local
    before dropping them, to ensure that they are dropped from an aligned address.") and `:25-25`
    ("We want to call `drop_glue::<Vec<u8>>` with a reference to `data`, which must be aligned.");
    the module documentation `:9-38` (including the illustrated rewrite
    `drop_temp = foo.data; drop(drop_temp)` between storage markers, `:30-34`) is cited as
    documented design, with no claim about the implementation;
  * `library/core/src/ptr/mod.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:761-763` ("Unaligned
    values cannot be dropped in place, they must be copied to an aligned location first using
    [`ptr::read_unaligned`]. For packed structs, this move is done automatically by the
    compiler.") and `:776-776` ("`to_drop` must be properly aligned, even if `T` has size 0.");
  * `library/core/src/pin.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:630-633` ("Moreover, if your
    type is [`#[repr(packed)]`][packed], the compiler will automatically move fields around to be
    able to drop them. It might even do that for fields that happen to be sufficiently aligned. As
    a consequence, you cannot use pinning with a [`#[repr(packed)]`][packed] type.") and `:802-807`
    (pinned destruction: "the struct *must not* be [`#[repr(packed)]`][packed]", on `:807`);
  * `compiler/rustc_error_codes/src/error_codes/E0793.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:28-29`
    ("Creating a reference to an insufficiently aligned packed field is [undefined behavior] and
    therefore disallowed.");
  * `compiler/rustc_error_codes/src/error_codes/E0588.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:14-16`
    ("Just like you cannot have both `align` and `packed` representation hints on the same type, a
    `packed` type cannot contain another type with the `align` representation hint.");
  * `src/tools/miri/README.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:15-15` ("Not sufficiently
    aligned memory accesses and references"), `:399-408` (`-Zmiri-symbolic-alignment-check`: "the
    symbolic alignment check only takes into account the requested alignment of the relevant
    allocation, and the offset into that allocation", with "some false positives when the code
    does manual integer arithmetic to ensure alignment"), `:442-444`
    (`-Zmiri-disable-alignment-check`);
  * `src/doc/unstable-book/src/compiler-flags/ub-checks.md@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:10-10`
    ("All checks are generated on a best-effort basis; even if we have a check implemented for some
    cause of Undefined Behavior, it may be possible for the check to not fire.").
* `rust-lang/rfcs` commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:
  * `text/1240-repr-packed-unsafe-ref.md@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:8-10` ("Taking a
    reference into a struct marked `repr(packed)` should become `unsafe`, because it can lead to
    undefined behaviour. `repr(packed)` structs need to be banned from storing `Drop` types for
    this reason.") and `:154-160` (the destructor of `T` "is passed a reference to that `T`",
    `:155-156`);
  * `text/2582-raw-reference-mir-operator.md@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07:23-24`
    ("`&packed.field as *const _` creates an intermediate unaligned reference, triggering undefined
    behavior because it is not aligned.").
* MiniRust, `minirust/minirust` commit `063d784186d3252bee242217f218223205c0b568`:
  `spec/lang/types.md@063d784186d3252bee242217f218223205c0b568:201-207` (`capped_tail_align`:
  `tail_align.min(packed_align)` when packed).
* Clang UndefinedBehaviorSanitizer documentation,
  https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html (live page without an immutable
  revision, observed 2026-11-21): "-fsanitize=alignment: Use of a misaligned pointer or creation
  of a misaligned reference", and `-fsanitize-trap=`.
* D. Song, J. Lettner, P. Rajasekaran, Y. Na, S. Volckaert, P. Larsen, M. Franz, "SoK: Sanitizing
  for Security", IEEE Symposium on Security and Privacy 2019, doi:10.1109/SP.2019.00010.
* Related mechanizations without packed-drop staging or shim-check completeness: R. Jung,
  J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: Securing the Foundations of the Rust
  Programming Language", POPL 2018, doi:10.1145/3158154; L. Gäher, M. Sammler, R. Jung,
  R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust
  Programs", PLDI 2024, doi:10.1145/3656422.
* Context (cited in prose, not subjects, not normative): the `unaligned_references` lint became a
  hard error through https://github.com/rust-lang/rust/pull/102513 ("make unaligned_reference a
  hard error", merged 2023-02-01), tracked in https://github.com/rust-lang/rust/issues/82523
  (closed 2023-02-01); E0793 links to the tracking issue.
  https://github.com/rust-lang/rust/issues/164561 ("moving a `Box` out of a packed struct creates
  a misaligned `&mut Box` to drop it", open, created 2026-10-19) is context for `box-free`; an
  open issue, not relied on as normative.

### Observation dates

All external sources above, the upstream issue and pull-request states, and the Lean toolchain tag
were checked on 2026-11-21; the Lean build and audit were run on the same date.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the toolchain
download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs
`lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or
declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of
the library `ToyPacked` and checks that only `propext`, `Classical.choice` and `Quot.sound` occur;
and (4) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`,
`nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` entries) and
every name recorded in `audit/statements.json`, recomputes the SHA-256 of the statement (the Lean
`repr` of the declaration's type) and of its definition closure (the sorted
`name : type := value` texts of every package-local constant reachable from the statement, theorem
bodies excluded) and compares both with `audit/statements.json`. This is exactly what is hashed;
proofs are not hashed, but step (1) re-checks every proof in the kernel. Exit status 0, with the
final line `REVALIDATED`, means all four checks passed.

Manual alternative (build, then print the axioms of the main result of every card):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs
`#print axioms` on the `lean` theorem(s) of every card. Each line of its output must list only
`propext`, `Classical.choice` and `Quot.sound`, or report that the declaration depends on no axioms.

To check one statement hash by hand, print the statement and closure texts with a short Lean
program modelled on the audit program embedded in `support/revalidate.py` (the `AUDIT` string), and
hash them with Python's `hashlib.sha256` over the UTF-8 text (the closure entries sorted and joined
with newlines); compare with the corresponding entry of `audit/statements.json`.

What revalidation does not cover: the modeling bridges and prior-art notes are prose; re-checking
them means re-reading the pinned files at the line ranges given under Evidence.
