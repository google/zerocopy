# Pointer capability modalities in a toy model: lattice, LLVM-style attribute lowering at call entry and at the return point, niche lifting, and SROA monotonicity (Lean 4)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

This package is a Lean 4 toy model (core Lean, no Mathlib) of the guarantees a Rust-like compiler attaches to a pointer for the duration of a call, and of how those guarantees lower to LLVM-style parameter attributes. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM.

Model conventions that every statement below carries:

- Every modality `Mod` is a call-entry modality: a set of seven atoms describing a pointer that exists at call entry, promised at call entry (`aligned`, `nonnull`, `derefEntry`) or over the call's execution (`derefWhole`, `frozen`, `unique`, `bounded`). Bounded provenance is the explicit atom `bounded` (its trace meaning is `ArgInRange`: every access during the call through an argument-derived pointer stays inside the pointee bytes); `den s m` (written `⟦m⟧`) imposes exactly the atoms of `m`, so it imposes `bounded` exactly when `m` contains it, and every trace is in `⟦Mod.bot⟧` (`den_bot`).
- Argument attributes are evaluated at call entry (`dereferenceable`) or over the call (`noalias`, `nofree`, `readonly`); return-value attributes are evaluated at the return point (`attrSat s .ret`), for a pointer carrying a call-entry modality when it is returned. No statement models a returned value's own validity invariant at the return point.
- Pointee sizes are positive by construction (`Shape.size_pos`); cards whose proofs use it say so (positive-size shapes), and zero-sized pointees are not representable. Address `0` is in no allocation. Addresses are unbounded natural numbers (no wrapping, no `isize::MAX` bound). Allocations created during the call are not represented.

One sentence per result (hypotheses first; the full claims are in Findings):

- `R1-lattice`: Call-entry modalities ordered by inclusion form a bounded lattice with meet `Mod.inf`, join `Mod.sup`, least element `Mod.bot` and greatest element `Mod.top`; and for every pointee shape `s`, implication closure `cl s` is extensive, monotone and idempotent with `s`-closed values, and the `s`-closed call-entry modalities contain `Mod.top` and `cl s Mod.bot` and are closed under `Mod.inf` and `Mod.sup`.
- `R1-antitone`: For every shape `s`, call-entry modalities `m₁ m₂` and trace `t`: if `m₁ ≤ m₂` and `t ∈ ⟦m₂⟧`, then `t ∈ ⟦m₁⟧`; and `t ∈ ⟦Mod.sup m₁ m₂⟧` iff `t ∈ ⟦m₁⟧` and `t ∈ ⟦m₂⟧` (a labelled reference point).
- `R1-closure`: For every shape `s`, call-entry modality `m` and trace `t`: `t ∈ ⟦cl s m⟧` iff `t ∈ ⟦m⟧` (in the toy, address `0` is in no allocation, which makes either deref atom imply `nonnull`).
- `R1-embedding`: For every positive-size shape `s` and call-entry modalities `m₁ m₂`: every trace of `⟦m₁⟧` is in `⟦m₂⟧` iff `m₂ ≤ cl s m₁`; and if `m₁` is closed for `s`, then `⟦m₁⟧ ⊆ ⟦m₂⟧` iff `m₂ ≤ m₁`.
- `R1-transformers-best`: For every positive-size shape `s`, pointer kind `k` and call-entry modality `m'`: every trace permitted by the transcribed rule `kindRule s k` satisfies `m'` iff `m' ≤ cl s (kindBase k)`; for all call-entry modalities `m m'`, every trace permitted by `relaxRule s m` satisfies `m'` iff `m' ≤ cl s (tRelax m)`; and for call-entry modalities `m₁ m₂` with `⟦m₁⟧ = ⟦m₂⟧`, each of `tRelax`, `tCell`, `tPin`, `tBox` gives call-entry modalities with equal semantics. The safe pointer kinds carry the atom `bounded`; raw pointers (`Mod.bot`) and `tRelax` do not.
- `R1-dropped-atoms`: For every positive-size shape `s`, named traces permitted by the transcribed rules violate each atom that a transformer removes from the call-entry modality it is applied to: inside a relaxing wrapper a former `refFull` pointer may dangle, have its pointee written, and be used just outside the pointee (failing `bounded`), and a former `mutFull` pointer may be read through an unrelated pointer; the pointees of `tCell refFull`, `tPin mutFull`, `tBox mutFull` and `tBox (tPin mutFull)` may be freed during the call, the pointee of `tCell refFull` may be written, and the pointees of `tPin mutFull` and `tBox (tPin mutFull)` may be read through an unrelated pointer.
- `R2-comp-iff`: For every relaxing transformer `T : Mod → Mod` and flag `deep`, the bottom-up computation `comp T deep` is sound against the top-down reference semantics `req` at every pointer leaf of every toy type (leaves of every positive-size shape and every call-entry modality) iff `T` is sound (`TransformerSound T`, equivalently `∀ m, T m ≤ tRelax m`) and `deep = true`; restricted to types built from the four documented pointer constructors, the deep computation with the unsound transformer `tRelaxExceptFrozenOnly` is sound against `req` at every pointer leaf of every such type.
- `R2-shallow-cex`: For every positive-size shape `s`, in `MaybeDangling<(Wrapper(&mut T), u8)>` the shallow computation with any relaxing transformer gives the nested `&mut T` leaf the full call-entry modality `mutFull`, while the reference requirement is `tRelax mutFull`; a dangling trace and a foreign-read trace satisfy the requirement and violate `derefEntry`, respectively `unique`.
- `R2-documented-exact`: For every toy type `τ` and path `p`, `comp tRelax true τ p = req τ p`.
- `R3-lower-sound`: For every shape `s`, position `pos` (argument or return), call-entry modality `m` and trace `t` with `t ∈ ⟦m⟧`, `t` satisfies every attribute of `lower s pos m` at `pos`: at argument position `dereferenceable` is evaluated at call entry and `noalias`, `nofree`, `readonly` over the call (in the closure `cl s m`, `lower` takes argument `noalias` from the atom `bounded` together with `frozen` or `unique`, and argument `readonly` from `bounded` together with `frozen`); at return position the attributes are evaluated at the return point for that pointer when it is returned, and `lower s .ret m` is not a lowering of a returned value's validity invariant.
- `R3-lower-best`: For every positive-size shape `s`, position `pos`, call-entry modality `m` and attribute set `A`: every trace of `⟦m⟧` satisfies `A` at `pos` (argument attributes at call entry and over the call; return-value attributes at the return point) iff `A ≤ lower s pos m`; and an attribute set that is sound for `⟦m⟧` at `pos` and contains every attribute set sound for `⟦m⟧` at `pos` equals `lower s pos m`. At return position this is the largest set of return-point attributes that the call-entry modality `m` justifies for a returned pointer carrying it, not a best lowering of a returned value's validity invariant.
- `R3-galois`: For every relation `P` between attributes and traces, `alphaOf P` and `gammaOf P` form a Galois connection (reverse inclusion on attribute sets); for every positive-size shape `s` and position `pos`, `alphaSet s pos` and `gammaDual s pos` therefore form a Galois connection, and `lower s pos m = (alphaSet s pos (denP s m)).val` for every call-entry modality `m`; and for every shape `s` and position `pos`, `lower s pos` has no left adjoint, over all call-entry modalities or over `s`-closed ones, and `lower s .arg` has no right adjoint over all call-entry modalities.
- `R3-stronger-unsound`: For every positive-size shape `s`, each listed attribute is outside the argument lowering `lower s .arg m` (attributes at call entry and over the call) of the listed call-entry modality `m`, and a named trace of `⟦m⟧` violates `lower s .arg m` with that attribute added: `nofree`, `readonly` and `noalias` for `kindBase (.shared false)`; `noalias` and `nofree` for `kindBase (.mutRef false)`; `nofree` for `kindBase (.box true)`; `dereferenceable` for `tRelax refFull`; `noalias` and `readonly` for `refFullNoBounded` and `noalias` for `mutFullNoBounded` (`refFull` and `mutFull` without the atom `bounded`, whose meaning is `ArgInRange`).
- `R3-position`: For every positive-size shape `s`: the argument lowering of the call-entry modality `refFull` contains `noalias`, and the trace `tReadAfter s`, which is in `⟦m⟧` for every call-entry modality `m`, satisfies argument `noalias` (over the call) and violates return `noalias` (after the return point); and the argument lowering of the call-entry modality `tCell refFull` contains `dereferenceable` (at call entry), and the trace `tFreed s` (pointee freed during the call) is in `⟦tCell refFull⟧`, satisfies `dereferenceable` at call entry and violates the toy's `dereferenceable` at the return point. Neither witness concerns a returned value's validity invariant or the attributes rustc attaches to return values.
- `R4-niche-sound`: For every positive-size shape `s`, payload call-entry modality `m` and trace `t` with `denOpt s 0 m t` (either `t.addr = 0` and no argument-tagged read, write or free happens during the call, or `t ∈ ⟦m⟧`), `t` satisfies at argument position (call entry and over the call) every attribute of `liftOpt s m`, which is `lower s .arg m` without `nonnull` and `dereferenceable`; and for every attribute set `A`, every trace of `denOpt s 0 m` satisfies `A` at argument position iff `A ≤ liftOpt s m`.
- `R4-niche-iff`: For every shape `s`, payload call-entry modality `m` and value `v`, under the hypothesis `IsNiche s m v` (no trace of `⟦m⟧` has address `v`): every trace of `denOpt s v m` satisfies `liftOpt s m` at argument position (call entry and over the call) iff `v = 0`.
- `R4-niche-cex`: For the two-byte, two-aligned shape `s2` and payload call-entry modality `refFull`, `1` is a niche of `refFull`, and with `None` encoded at `1` (a counterfactual encoding) the `None` trace `tAt 1` violates the argument attributes `dereferenceable_or_null` and `align` of `liftOpt s2 refFull` (evaluated at call entry); and for every shape `s` and payload call-entry modality `m`, the null `None` trace `tNull` is a trace of `denOpt s 0 m` and violates argument `nonnull` and `dereferenceable` (at call entry).
- `R5-sroa-iff`: For every toy type `τ` (its pointer leaves have positive-size shapes) and list of field paths `qs`: replacing a local of type `τ` by one local per field path in `qs`, each with the field's declared type (`scalarize τ qs`; paths that are not fields are skipped), is a refinement for every assertion pattern and every assignment of call traces to asserted leaves (`Refines`) iff for every `q ∈ qs` with declared field type `σ` and every pointer leaf `p'` of `σ` whose call-entry modality computed inside `σ` is `m`, `m ≤ posTrans τ q m`.
- `R5-sroa-headline`: For every shape `s`, scalarizing `ManuallyDrop<(&mut T, u8)>` into its fields `&mut T` and `u8` with their declared types turns the program `progDangling s`, whose wrapped reference legally dangles, from defined into undefined: the reference's position call-entry modality is `tRelax mutFull`, while its declared call-entry modality `mutFull` has an argument lowering containing `dereferenceable` and `noalias`, which the lowering of `tRelax mutFull` lacks.
- `R6-repairs`: For toy types whose pointer leaves have positive-size shapes, the policies `repairExclude`, `repairRetype` and `repairStopAtRelaxer` are each sound (every scalarization they return is a refinement for every assertion pattern and every assignment of call traces) and `naivePolicy` is not; all three are exact (whenever one of them scalarizes a type `τ` with path list `qs` (`pol τ qs = some locals` for that policy), one new local per requested field path of `τ`, in order, and every pointer leaf of a new local has exactly the call-entry modality of the same leaf in `τ`), and `repairRetype` returns a scalarization for every type and path list; whenever `repairExclude` scalarizes, `repairStopAtRelaxer` returns the same locals, and whenever `repairStopAtRelaxer` scalarizes, `repairRetype` returns the same locals, both inclusions strict; and `repairStopAtRelaxer` refuses `ManuallyDrop<u8>` with paths `[[.inner]]` although that scalarization is a refinement.

Non-claims for every result are listed first under Boundaries, one subsection per card; attractive stronger readings that are not established are listed there as well.

## Applicability

### Model fidelity

This is a toy model, not a mirror of production definitions. All declarations live in the Lean namespace `Toy.Modality`. The definitions are meant to capture:

- the guarantees a Rust-like compiler attaches to a pointer argument for the duration of a call, as seven capability atoms of a call-entry modality (`Mod`): alignment, non-null, dereferenceability at call entry (`derefEntry`), dereferenceability at call entry together with "no containing allocation freed during the call" (`derefWhole`), no write to the pointee during the call (`frozen`), no access to the pointee through an unrelated pointer during the call (`unique`), and bounded provenance (`bounded`, meaning `ArgInRange`: every access during the call through an argument-derived pointer stays inside the pointee bytes);
- the trace semantics of these atoms over single-call traces (`Trace`: pointer address, allocations live at call entry, tagged events during and after the call);
- how relaxing wrappers (`MaybeDangling`, `ManuallyDrop`) and pointee predicates (`UnsafeCell` / non-`Freeze`, non-`Unpin`, `Box`) weaken a modality (`tRelax`, `tCell`, `tPin`, `tBox`), transcribed from documentation as trace rules (`kindRule`, `relaxRule`);
- a bottom-up computation of pointer-leaf modalities over a small by-value type language (`Ty`: scalars, pointer leaves `Ty.ptr s m` with erased pointee type, pairs, relaxing wrappers) against a top-down reference requirement (`req`);
- the lowering `lower s pos m` of a call-entry modality to seven LLVM-style attributes (`align`, `nonnull`, `dereferenceable`, `dereferenceable_or_null`, `noalias`, `nofree`, `readonly`) at argument position and at return position, with attribute meanings `attrSat` that are the toy's readings of LLVM LangRef;
- lifting through an Option-like niche (`denOpt`, `liftOpt`), and scalar replacement of aggregates (`scalarize`) judged by refinement over a toy program model (`Prog`: an assertion pattern plus an assignment of call traces; no operational semantics), with three repair policies.

Program points. Every `Mod` is a call-entry modality of a pointer that exists at call entry. `lower s .arg m` collects argument attributes (`dereferenceable` evaluated at call entry; `noalias`, `nofree`, `readonly` over the call). `lower s .ret m` collects the return-value attributes, evaluated at the return point by `attrSat s .ret`, to which a pointer carrying the call-entry modality `m` is entitled when it is returned (for example an argument returned unchanged). It is not a lowering of the validity invariant that a returned value has at the return point; the toy does not represent that invariant (the Rust Reference states it; see Prior art of `R3-lower-sound`).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Real systems appear in separate `Basis: derived (modeling bridge)` lines and in prior-art entries that cite their documentation, source and public issues.

Known gaps (see also the per-card non-claims under Boundaries):

- Pointee sizes are positive by construction (`Shape.size_pos`); zero-sized pointees are not representable. The section "Kernel dependency audit for `Shape.size_pos`" records which proofs use the field.
- Address `0` is in no allocation; non-zero LLVM address spaces and the `null_pointer_is_valid` function attribute are not modelled.
- Addresses, sizes and lengths are unbounded natural numbers: `t.addr + s.size` never wraps, and address-space size and `isize::MAX` bounds are not modelled (so the toy has no upper-bound niches).
- Allocations created during the call are not represented, so a freshly allocated return value is not expressible; no atom constrains events after the return.
- Attribute meanings treat every violation as undefined behaviour (LLVM's `align` and `nonnull` yield poison unless combined with `noundef`); `nofree` and `readonly` are read as never satisfied at return position (a modelling choice; LangRef line 1588 states that `nofree` is not a valid attribute for return values).
- The type language has no enums or unions, and pointers behind a pointer indirection are not modelled (nesting is by value).
- The toy `box` kind stands for a box with the global allocator; custom allocators, the `box_noalias` option, unoptimized builds and uninhabited pointees are not modelled.
- SROA is judged over assertion patterns and trace assignments, not over an operational semantics; lifetime transitions, retag points and partially initialized fields are not modelled.

### Toolchain and project

- Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only (no Mathlib, no `[[require]]`).
- Lake project `lean/` with one library target `Toy` (`lean/lakefile.toml`); modules `Toy.Modality.{Imported, Basic, Lattice, Transformers, Types, Lowering, Niche, SROA, Examples}`.
- `lean/RevalidationAudit.lean` (outside the library target) prints the axioms of every main result; `support/size_pos_audit.lean` is the kernel dependency audit script for `Shape.size_pos`; `support/revalidate.py` rebuilds the project and rechecks axioms and hashes.
- Paths in statement fences are relative to the package root. Every theorem of the package is fully proved; `#print axioms` reports at most `propext`, `Classical.choice`, `Quot.sound`.

### Subjects and how they relate

The Lean toolchain checks the statements. The other subjects are real systems and documents that the definitions are meant to capture or that the cards cite as prior art; the report interprets the toy through them in `derived (modeling bridge)` lines and proves nothing about them:

- rust-lang/rust at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`: rustc's ABI attribute computation (`compiler/rustc_ty_utils/src/abi.rs`), layout recursion through `MaybeDangling` and null niches (`compiler/rustc_middle/src/ty/layout.rs`), MIR scalar replacement of aggregates (`compiler/rustc_mir_transform/src/sroa.rs`), and `library/core/src/mem/{maybe_dangling.rs, manually_drop.rs}`.
- rust-lang/rust at `cd2a75d9d58d7bd7b59cde543684fc83c3e785d2` (the merge commit of rust-lang/rust pull 164568): the SROA exclusion of `MaybeDangling`-like types that `repairStopAtRelaxer` is compared with.
- llvm/llvm-project at `5b10d2d74929eae78912771222c9855af97496f4` (release llvmorg-23.1.6), `llvm/docs/LangRef.md`: parameter-attribute documentation read by `attrSat`.
- rust-lang/rfcs at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: RFC 3336 (`MaybeDangling`), RFC 3467 (`UnsafePinned`), RFC 1860 (`ManuallyDrop`).
- rust-lang/reference at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/behavior-considered-undefined.md`: the validity invariant of references and boxes, which the toy does not represent.
- Papers cited as prior art (identified by DOI under Evidence).

## Findings

Findings are organised as follows: the definitions every statement depends on, quoted verbatim with their source locations; one card per result (tier, verbatim Lean statements, plain claim, evidence basis, hypothesis ledger, depth, non-vacuity witness, positive control where the result is a counterexample, prior art and design question; the card's non-claims are under Boundaries); the kernel dependency audit for `Shape.size_pos`; and every auxiliary declaration a card mentions by name, quoted verbatim. "Tight" in a hypothesis ledger means that a fully proved Lean counterexample, in the class recorded next to it, satisfies all the other hypotheses and violates the conclusion.

### Definitions (verbatim)

#### Pointee shapes

```lean
-- lean/Toy/Modality/Basic.lean:27-30
structure Shape where
  size : Nat
  alignLog : Nat
  size_pos : 0 < size
```
```lean
-- lean/Toy/Modality/Basic.lean:33
def Shape.align (s : Shape) : Nat := 2 ^ s.alignLog
```

A pointee has `size` bytes, positive by construction (`size_pos`), and alignment `2 ^ alignLog` (never 0). Examples: `ex_shape`.

#### Atoms and modalities

```lean
-- lean/Toy/Modality/Basic.lean:50-58
inductive Atom
  | aligned
  | nonnull
  | derefEntry
  | derefWhole
  | frozen
  | unique
  | bounded
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:64-72
structure Mod where
  aligned : Bool
  nonnull : Bool
  derefEntry : Bool
  derefWhole : Bool
  frozen : Bool
  unique : Bool
  bounded : Bool
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:75-82
def Mod.has (m : Mod) : Atom → Bool
  | .aligned => m.aligned
  | .nonnull => m.nonnull
  | .derefEntry => m.derefEntry
  | .derefWhole => m.derefWhole
  | .frozen => m.frozen
  | .unique => m.unique
  | .bounded => m.bounded
```

```lean
-- lean/Toy/Modality/Basic.lean:86
instance : LE Mod := ⟨fun m₁ m₂ => ∀ a, m₁.has a = true → m₂.has a = true⟩
```

```lean
-- lean/Toy/Modality/Basic.lean:112-115
def Mod.inf (m₁ m₂ : Mod) : Mod :=
  ⟨m₁.aligned && m₂.aligned, m₁.nonnull && m₂.nonnull, m₁.derefEntry && m₂.derefEntry,
   m₁.derefWhole && m₂.derefWhole, m₁.frozen && m₂.frozen, m₁.unique && m₂.unique,
   m₁.bounded && m₂.bounded⟩
```
```lean
-- lean/Toy/Modality/Basic.lean:118-121
def Mod.sup (m₁ m₂ : Mod) : Mod :=
  ⟨m₁.aligned || m₂.aligned, m₁.nonnull || m₂.nonnull, m₁.derefEntry || m₂.derefEntry,
   m₁.derefWhole || m₂.derefWhole, m₁.frozen || m₂.frozen, m₁.unique || m₂.unique,
   m₁.bounded || m₂.bounded⟩
```
```lean
-- lean/Toy/Modality/Basic.lean:125
def Mod.bot : Mod := ⟨false, false, false, false, false, false, false⟩
```
```lean
-- lean/Toy/Modality/Basic.lean:128
def Mod.top : Mod := ⟨true, true, true, true, true, true, true⟩
```

A modality is a set of atoms; `≤` is inclusion (more atoms = stronger promise). Examples: `ex_mod_le`, `ex_mod_inf_sup`.

#### Traces

```lean
-- lean/Toy/Modality/Basic.lean:152-155
inductive Tag
  | arg
  | other
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:159-163
inductive Event
  | read (tg : Tag) (loc : Nat)
  | write (tg : Tag) (loc : Nat)
  | free (tg : Tag) (id : Nat)
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:166-170
structure Alloc where
  id : Nat
  base : Nat
  len : Nat
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:177-182
structure Trace where
  addr : Nat
  live : List Alloc
  during : List Event
  after : List Event
  deriving Repr
```
```lean
-- lean/Toy/Modality/Basic.lean:186-187
def Alloc.contains (al : Alloc) (x : Nat) : Prop :=
  0 < al.base ∧ al.base ≤ x ∧ x < al.base + al.len
```
```lean
-- lean/Toy/Modality/Basic.lean:191-192
def Alloc.covers (al : Alloc) (a n : Nat) : Prop :=
  0 < al.base ∧ al.base ≤ a ∧ a + n ≤ al.base + al.len
```
```lean
-- lean/Toy/Modality/Basic.lean:195
def InRange (s : Shape) (a x : Nat) : Prop := a ≤ x ∧ x < a + s.size
```
```lean
-- lean/Toy/Modality/Basic.lean:198-199
def AccessedBy (es : List Event) (tg : Tag) (x : Nat) : Prop :=
  Event.read tg x ∈ es ∨ Event.write tg x ∈ es
```
```lean
-- lean/Toy/Modality/Basic.lean:202
def Written (es : List Event) (x : Nat) : Prop := ∃ tg, Event.write tg x ∈ es
```
```lean
-- lean/Toy/Modality/Basic.lean:207-208
def ArgInRange (s : Shape) (t : Trace) : Prop :=
  ∀ x, AccessedBy t.during .arg x → InRange s t.addr x
```
```lean
-- lean/Toy/Modality/Basic.lean:211-212
def Dereferenceable (s : Shape) (t : Trace) : Prop :=
  ∃ al ∈ t.live, al.covers t.addr s.size
```
```lean
-- lean/Toy/Modality/Basic.lean:216-217
def NotFreedDuring (t : Trace) : Prop :=
  ∀ al ∈ t.live, al.contains t.addr → ∀ tg, Event.free tg al.id ∉ t.during
```

A trace records the pointer address, the allocations live at call entry, and the tagged events during and after the call. Allocations created during the call are not represented. Address `0` is in no allocation. Examples: `ex_argInRange` (accesses after the return are not constrained), `ex_dereferenceable`, `ex_notFreedDuring`.

#### Trace semantics of atoms and modalities

```lean
-- lean/Toy/Modality/Basic.lean:220-227
def atomSat (s : Shape) : Atom → Trace → Prop
  | .aligned, t => t.addr % s.align = 0
  | .nonnull, t => t.addr ≠ 0
  | .derefEntry, t => Dereferenceable s t
  | .derefWhole, t => Dereferenceable s t ∧ NotFreedDuring t
  | .frozen, t => ∀ x, InRange s t.addr x → ¬ Written t.during x
  | .unique, t => ∀ x, InRange s t.addr x → ¬ AccessedBy t.during .other x
  | .bounded, t => ArgInRange s t
```
```lean
-- lean/Toy/Modality/Basic.lean:231-232
def den (s : Shape) (m : Mod) (t : Trace) : Prop :=
  ∀ a, m.has a = true → atomSat s a t
```

`bounded` means that every access during the call through an argument-derived pointer stays inside the pointee bytes; it is an atom like the others, so `⟦m⟧` imposes it exactly when `m` contains it. Examples: `ex_atomSat`, `ex_den`.

#### Implication closure

```lean
-- lean/Toy/Modality/Basic.lean:240-244
def cl (s : Shape) (m : Mod) : Mod :=
  { m with
    aligned := m.aligned || s.alignLog == 0
    nonnull := m.nonnull || m.derefEntry || m.derefWhole
    derefEntry := m.derefEntry || m.derefWhole }
```
```lean
-- lean/Toy/Modality/Basic.lean:247
def Closed (s : Shape) (m : Mod) : Prop := cl s m = m
```

Examples: `ex_closed`, `ex_cl`.

#### Transformers, pointer kinds and transcribed rules

```lean
-- lean/Toy/Modality/Transformers.lean:36-39
def clDeref (m : Mod) : Mod :=
  { m with
    nonnull := m.nonnull || m.derefEntry || m.derefWhole
    derefEntry := m.derefEntry || m.derefWhole }
```
```lean
-- lean/Toy/Modality/Transformers.lean:43-44
def tRelax (m : Mod) : Mod :=
  { Mod.bot with aligned := m.aligned, nonnull := (clDeref m).nonnull }
```
```lean
-- lean/Toy/Modality/Transformers.lean:48
def tCell (m : Mod) : Mod := { clDeref m with frozen := false, derefWhole := false, unique := false }
```
```lean
-- lean/Toy/Modality/Transformers.lean:52
def tPin (m : Mod) : Mod := { clDeref m with unique := false, derefWhole := false }
```
```lean
-- lean/Toy/Modality/Transformers.lean:56
def tBox (m : Mod) : Mod := { clDeref m with derefWhole := false }
```
```lean
-- lean/Toy/Modality/Transformers.lean:60
def refFull : Mod := ⟨true, true, true, true, true, false, true⟩
```
```lean
-- lean/Toy/Modality/Transformers.lean:64
def mutFull : Mod := ⟨true, true, true, true, false, true, true⟩
```
```lean
-- lean/Toy/Modality/Transformers.lean:69-74
inductive PtrKind
  | shared (freeze : Bool)
  | mutRef (unpin : Bool)
  | box (unpin : Bool)
  | raw
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Transformers.lean:77-84
def kindBase : PtrKind → Mod
  | .shared true => refFull
  | .shared false => tCell refFull
  | .mutRef true => mutFull
  | .mutRef false => tPin mutFull
  | .box true => tBox mutFull
  | .box false => tBox (tPin mutFull)
  | .raw => Mod.bot
```
```lean
-- lean/Toy/Modality/Transformers.lean:103-116
def kindRule (s : Shape) : PtrKind → Trace → Prop
  | .shared true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ NotFreedDuring t ∧ atomSat s .frozen t ∧ ArgInRange s t
  | .shared false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .mutRef true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ NotFreedDuring t ∧ atomSat s .unique t ∧ ArgInRange s t
  | .mutRef false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .box true, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ atomSat s .unique t ∧ ArgInRange s t
  | .box false, t => atomSat s .aligned t ∧ atomSat s .nonnull t ∧
      Dereferenceable s t ∧ ArgInRange s t
  | .raw, _ => True
```
```lean
-- lean/Toy/Modality/Transformers.lean:122-124
def relaxRule (s : Shape) (m : Mod) (t : Trace) : Prop :=
  ((cl s m).aligned = true → atomSat s .aligned t) ∧
    ((cl s m).nonnull = true → atomSat s .nonnull t)
```

Each transformer first applies the shape-independent closure `clDeref`, so dropping `derefWhole` keeps `derefEntry` and `nonnull`. `kindRule` and `relaxRule` transcribe the documented rules as trace predicates. Examples: `ex_transformers`, `ex_clDeref`, `ex_kindBase`, `ex_kindRule`, `ex_relaxRule`.

#### Toy types and the bottom-up computation

```lean
-- lean/Toy/Modality/Types.lean:27-33
inductive Wrap
  | maybeDangling
  | manuallyDrop
  | transparent
  | unsafeCell
  | unsafePinned
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Types.lean:36-39
def Wrap.relaxes : Wrap → Bool
  | .maybeDangling => true
  | .manuallyDrop => true
  | _ => false
```
```lean
-- lean/Toy/Modality/Types.lean:46-50
inductive Ty
  | scalar
  | ptr (s : Shape) (m : Mod)
  | pair (a b : Ty)
  | wrap (w : Wrap) (τ : Ty)
```
```lean
-- lean/Toy/Modality/Types.lean:54-58
inductive Step
  | fst
  | snd
  | inner
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Types.lean:61
abbrev Path := List Step
```
```lean
-- lean/Toy/Modality/Types.lean:64-66
def Ty.isPtr : Ty → Bool
  | .ptr _ _ => true
  | _ => false
```
```lean
-- lean/Toy/Modality/Types.lean:70-75
def Ty.freeze : Ty → Bool
  | .scalar => true
  | .ptr _ _ => true
  | .pair a b => a.freeze && b.freeze
  | .wrap .unsafeCell _ => false
  | .wrap _ τ => τ.freeze
```
```lean
-- lean/Toy/Modality/Types.lean:79-84
def Ty.unpin : Ty → Bool
  | .scalar => true
  | .ptr _ _ => true
  | .pair a b => a.unpin && b.unpin
  | .wrap .unsafePinned _ => false
  | .wrap _ τ => τ.unpin
```
```lean
-- lean/Toy/Modality/Types.lean:87
def refTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.shared T.freeze))
```
```lean
-- lean/Toy/Modality/Types.lean:90
def mutRefTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.mutRef T.unpin))
```
```lean
-- lean/Toy/Modality/Types.lean:93
def boxTy (s : Shape) (T : Ty) : Ty := .ptr s (kindBase (.box T.unpin))
```
```lean
-- lean/Toy/Modality/Types.lean:96
def rawTy (s : Shape) : Ty := .ptr s (kindBase .raw)
```
```lean
-- lean/Toy/Modality/Types.lean:101-106
def leafAt : Ty → Path → Option (Shape × Mod)
  | .ptr s m, [] => some (s, m)
  | .pair a _, .fst :: p => leafAt a p
  | .pair _ b, .snd :: p => leafAt b p
  | .wrap _ τ, .inner :: p => leafAt τ p
  | _, _ => none
```
```lean
-- lean/Toy/Modality/Types.lean:109-113
def relaxedOn : Ty → Path → Bool
  | .pair a _, .fst :: p => relaxedOn a p
  | .pair _ b, .snd :: p => relaxedOn b p
  | .wrap w τ, .inner :: p => w.relaxes || relaxedOn τ p
  | _, _ => false
```
```lean
-- lean/Toy/Modality/Types.lean:119-126
def comp (T : Mod → Mod) (deep : Bool) : Ty → Path → Option (Shape × Mod)
  | .ptr s m, [] => some (s, m)
  | .pair a _, .fst :: p => comp T deep a p
  | .pair _ b, .snd :: p => comp T deep b p
  | .wrap w τ, .inner :: p =>
      (comp T deep τ p).map fun sm =>
        (sm.1, if w.relaxes && (deep || τ.isPtr) then T sm.2 else sm.2)
  | _, _ => none
```
```lean
-- lean/Toy/Modality/Types.lean:130-135
def reqAux : Bool → Ty → Path → Option (Shape × Mod)
  | r, .ptr s m, [] => some (s, if r then tRelax m else m)
  | r, .pair a _, .fst :: p => reqAux r a p
  | r, .pair _ b, .snd :: p => reqAux r b p
  | r, .wrap w τ, .inner :: p => reqAux (r || w.relaxes) τ p
  | _, _, _ => none
```
```lean
-- lean/Toy/Modality/Types.lean:138
def req (τ : Ty) (p : Path) : Option (Shape × Mod) := reqAux false τ p
```
```lean
-- lean/Toy/Modality/Types.lean:142-143
def TransformerSound (T : Mod → Mod) : Prop :=
  ∀ (s : Shape) (m : Mod) (t : Trace), den s (tRelax m) t → den s (T m) t
```
```lean
-- lean/Toy/Modality/Types.lean:147-149
def CompSound (T : Mod → Mod) (deep : Bool) : Prop :=
  ∀ (τ : Ty) (p : Path) (s : Shape) (m m₀ : Mod),
    comp T deep τ p = some (s, m) → req τ p = some (s, m₀) → ∀ t, den s m₀ t → den s m t
```
```lean
-- lean/Toy/Modality/Types.lean:385-392
inductive DocTy : Ty → Prop
  | scalar : DocTy .scalar
  | ref (s : Shape) {T : Ty} : DocTy T → DocTy (refTy s T)
  | mutRef (s : Shape) {T : Ty} : DocTy T → DocTy (mutRefTy s T)
  | box (s : Shape) {T : Ty} : DocTy T → DocTy (boxTy s T)
  | raw (s : Shape) : DocTy (rawTy s)
  | pair {a b : Ty} : DocTy a → DocTy b → DocTy (.pair a b)
  | wrap (w : Wrap) {τ : Ty} : DocTy τ → DocTy (.wrap w τ)
```

`Ty.ptr s m` erases the pointee type; nesting is by value. Examples: `ex_wrap_relaxes`, `ex_freeze_unpin`, `ex_pointer_constructors`, `ex_leafAt_relaxedOn`, `ex_comp_req`, `ex_transformerSound`, `ex_compSound`, `ex_docTy`.

#### Attributes and the lowering

```lean
-- lean/Toy/Modality/Lowering.lean:40-48
inductive Attr
  | align
  | nonnull
  | dereferenceable
  | dereferenceableOrNull
  | noalias
  | nofree
  | readonly
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Lowering.lean:51-59
structure AttrSet where
  align : Bool
  nonnull : Bool
  dereferenceable : Bool
  dereferenceableOrNull : Bool
  noalias : Bool
  nofree : Bool
  readonly : Bool
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Lowering.lean:62-69
def AttrSet.has (A : AttrSet) : Attr → Bool
  | .align => A.align
  | .nonnull => A.nonnull
  | .dereferenceable => A.dereferenceable
  | .dereferenceableOrNull => A.dereferenceableOrNull
  | .noalias => A.noalias
  | .nofree => A.nofree
  | .readonly => A.readonly
```

```lean
-- lean/Toy/Modality/Lowering.lean:72
instance : LE AttrSet := ⟨fun A B => ∀ a, A.has a = true → B.has a = true⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:96-99
inductive Pos
  | arg
  | ret
  deriving DecidableEq, Repr
```
```lean
-- lean/Toy/Modality/Lowering.lean:109-110
def DereferenceableAtReturn (s : Shape) (t : Trace) : Prop :=
  Dereferenceable s t ∧ NotFreedDuring t
```
```lean
-- lean/Toy/Modality/Lowering.lean:133-146
def attrSat (s : Shape) : Pos → Attr → Trace → Prop
  | _, .align, t => t.addr % s.align = 0
  | _, .nonnull, t => t.addr ≠ 0
  | .arg, .dereferenceable, t => Dereferenceable s t
  | .ret, .dereferenceable, t => DereferenceableAtReturn s t
  | .arg, .dereferenceableOrNull, t => t.addr = 0 ∨ Dereferenceable s t
  | .ret, .dereferenceableOrNull, t => t.addr = 0 ∨ DereferenceableAtReturn s t
  | .arg, .noalias, t =>
      ∀ x, AccessedBy t.during .arg x → Written t.during x → ¬ AccessedBy t.during .other x
  | .arg, .nofree, t => ∀ al ∈ t.live, al.contains t.addr → Event.free .arg al.id ∉ t.during
  | .arg, .readonly, t => ∀ x, Event.write .arg x ∉ t.during
  | .ret, .noalias, t => ∀ x, InRange s t.addr x → ¬ AccessedBy t.after .other x
  | .ret, .nofree, _ => False
  | .ret, .readonly, _ => False
```
```lean
-- lean/Toy/Modality/Lowering.lean:149-150
def gammaSet (s : Shape) (pos : Pos) (A : AttrSet) (t : Trace) : Prop :=
  ∀ a, A.has a = true → attrSat s pos a t
```
```lean
-- lean/Toy/Modality/Lowering.lean:153-155
def Pos.isArg : Pos → Bool
  | .arg => true
  | .ret => false
```
```lean
-- lean/Toy/Modality/Lowering.lean:168-173
def lower (s : Shape) (pos : Pos) (m : Mod) : AttrSet :=
  let c := cl s m
  let d := if pos.isArg then c.derefEntry else c.derefWhole
  ⟨c.aligned, c.nonnull, d, d,
   pos.isArg && c.bounded && (c.frozen || c.unique), pos.isArg && c.derefWhole,
   pos.isArg && c.bounded && c.frozen⟩
```

`dereferenceable` is evaluated at call entry for arguments and at the return point for return values; `nofree` and `readonly` are never satisfied at return position. Examples: `ex_attrSat`, `ex_gammaSet`, `ex_lower`.

Program points. Every modality is a call-entry modality: a set of promises about a pointer that exists at call entry, made at call entry (`aligned`, `nonnull`, `derefEntry`) or about the call's execution (`derefWhole`, `frozen`, `unique`, `bounded`). `lower s .arg m` collects the argument attributes that every trace of `⟦m⟧` satisfies (`dereferenceable` at call entry; `noalias`, `nofree`, `readonly` over the call). `lower s .ret m` collects the return-value attributes, evaluated at the return point by `attrSat s .ret`, that every trace of `⟦m⟧` satisfies: the attributes to which a pointer carrying the call-entry modality `m` is entitled when it is returned (for example an argument returned unchanged). The toy has no modality for the validity invariant of a returned value at the return point, and `lower s .ret` is not a lowering of it. `DereferenceableAtReturn` is definitionally the atom `derefWhole` (`dereferenceableAtReturn_iff_atomSat_derefWhole`), and `lower s .ret m` contains `dereferenceable` exactly when `cl s m` contains `derefWhole` (`lower_dereferenceable_eq`).

#### Galois connection

```lean
-- lean/Toy/Modality/Imported.lean:26
def Pred (σ : Type) : Type := σ → Prop
```
```lean
-- lean/Toy/Modality/Imported.lean:29
instance instLEPred (σ : Type) : LE (Pred σ) := ⟨fun x y => ∀ s, x s → y s⟩
```
```lean
-- lean/Toy/Modality/Imported.lean:33-34
def GaloisConnection {σ A : Type} [LE A] (α : Pred σ → A) (γ : A → Pred σ) : Prop :=
  ∀ x a, α x ≤ a ↔ x ≤ γ a
```
```lean
-- lean/Toy/Modality/Lowering.lean:386-387
structure AttrDual where
  val : AttrSet
```

```lean
-- lean/Toy/Modality/Lowering.lean:389
instance : LE AttrDual := ⟨fun A B => B.val ≤ A.val⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:399-406
noncomputable def alphaOf (P : Attr → Trace → Prop) (X : Imported.Pred Trace) : AttrDual :=
  ⟨⟨decide (∀ t, X t → P .align t),
    decide (∀ t, X t → P .nonnull t),
    decide (∀ t, X t → P .dereferenceable t),
    decide (∀ t, X t → P .dereferenceableOrNull t),
    decide (∀ t, X t → P .noalias t),
    decide (∀ t, X t → P .nofree t),
    decide (∀ t, X t → P .readonly t)⟩⟩
```
```lean
-- lean/Toy/Modality/Lowering.lean:410-411
def gammaOf (P : Attr → Trace → Prop) (A : AttrDual) : Imported.Pred Trace :=
  fun t => ∀ a, A.val.has a = true → P a t
```
```lean
-- lean/Toy/Modality/Lowering.lean:414-415
noncomputable def alphaSet (s : Shape) (pos : Pos) (X : Imported.Pred Trace) : AttrDual :=
  alphaOf (attrSat s pos) X
```
```lean
-- lean/Toy/Modality/Lowering.lean:419-420
def gammaDual (s : Shape) (pos : Pos) (A : AttrDual) : Imported.Pred Trace :=
  gammaOf (attrSat s pos) A
```
```lean
-- lean/Toy/Modality/Lowering.lean:423
def denP (s : Shape) (m : Mod) : Imported.Pred Trace := fun t => den s m t
```

`Imported.Pred`, `Imported.instLEPred` and `Imported.GaloisConnection` are copied verbatim (up to the namespace) from the published package `galois-connections-best-abstract-transformers-and-fixpoint-transfer` (google/zerocopy branch `reference`, commit a0dca4883c555805181f8149eafd7e65ab238991; `lean/Toy/AbsInt/Basic.lean` lines 21 and 25, git blob ae1c1a94c6c73ef95c162cdc585fbfd044eecf90; `lean/Toy/AbsInt/Galois.lean` lines 27-28, git blob 7828c554deffea6e4da6073f8eaa36a11844adfe). Examples: `ex_galois_defs`.

#### Niche lifting

```lean
-- lean/Toy/Modality/Niche.lean:21-23
def NoArgEvents (t : Trace) : Prop :=
  ∀ x, Event.read .arg x ∉ t.during ∧ Event.write .arg x ∉ t.during ∧
    Event.free .arg x ∉ t.during
```
```lean
-- lean/Toy/Modality/Niche.lean:27-28
def IsNiche (s : Shape) (m : Mod) (v : Nat) : Prop :=
  ∀ t, den s m t → t.addr ≠ v
```
```lean
-- lean/Toy/Modality/Niche.lean:34-35
def denOpt (s : Shape) (v : Nat) (m : Mod) (t : Trace) : Prop :=
  (t.addr = v ∧ NoArgEvents t) ∨ den s m t
```
```lean
-- lean/Toy/Modality/Niche.lean:39-40
def liftOpt (s : Shape) (m : Mod) : AttrSet :=
  { lower s .arg m with nonnull := false, dereferenceable := false }
```
```lean
-- lean/Toy/Modality/Niche.lean:43
def tAt (v : Nat) : Trace := ⟨v, [], [], []⟩
```

Examples: `ex_noArgEvents`, `ex_isNiche`, `ex_denOpt`, `ex_liftOpt`.

#### SROA

```lean
-- lean/Toy/Modality/SROA.lean:23
def modAt (τ : Ty) (p : Path) : Option (Shape × Mod) := comp tRelax true τ p
```
```lean
-- lean/Toy/Modality/SROA.lean:26-31
def fieldTy : Ty → Path → Option Ty
  | τ, [] => some τ
  | .pair a _, .fst :: q => fieldTy a q
  | .pair _ b, .snd :: q => fieldTy b q
  | .wrap _ τ, .inner :: q => fieldTy τ q
  | _, _ => none
```
```lean
-- lean/Toy/Modality/SROA.lean:35
def wrapTrans (w : Wrap) (m : Mod) : Mod := if w.relaxes then tRelax m else m
```
```lean
-- lean/Toy/Modality/SROA.lean:39-44
def posTrans : Ty → Path → Mod → Mod
  | _, [] => id
  | .pair a _, .fst :: q => posTrans a q
  | .pair _ b, .snd :: q => posTrans b q
  | .wrap w τ, .inner :: q => fun m => wrapTrans w (posTrans τ q m)
  | _, _ => id
```
```lean
-- lean/Toy/Modality/SROA.lean:50-52
structure Prog where
  asserts : Path → Bool
  exec : Path → Trace
```
```lean
-- lean/Toy/Modality/SROA.lean:56-57
def SrcSafe (τ : Ty) (P : Prog) : Prop :=
  ∀ p s m, modAt τ p = some (s, m) → P.asserts p = true → den s m (P.exec p)
```
```lean
-- lean/Toy/Modality/SROA.lean:61-63
def TgtSafe (locals : List (Path × Ty)) (P : Prog) : Prop :=
  ∀ q σ, (q, σ) ∈ locals → ∀ p' s m, modAt σ p' = some (s, m) →
    P.asserts (q ++ p') = true → den s m (P.exec (q ++ p'))
```
```lean
-- lean/Toy/Modality/SROA.lean:67-68
def Refines (τ : Ty) (locals : List (Path × Ty)) : Prop :=
  ∀ P, SrcSafe τ P → TgtSafe locals P
```
```lean
-- lean/Toy/Modality/SROA.lean:72-73
def scalarize (τ : Ty) (qs : List Path) : List (Path × Ty) :=
  qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, σ)
```

Examples: `ex_fieldTy_posTrans`, `ex_refines`, `ex_safe`.

#### Repairs

```lean
-- lean/Toy/Modality/SROA.lean:278-282
def containsRelaxer : Ty → Bool
  | .scalar => false
  | .ptr _ _ => false
  | .pair a b => containsRelaxer a || containsRelaxer b
  | .wrap w τ => w.relaxes || containsRelaxer τ
```
```lean
-- lean/Toy/Modality/SROA.lean:288-292
def relaxAll : Ty → Ty
  | .scalar => .scalar
  | .ptr s m => .ptr s (tRelax m)
  | .pair a b => .pair (relaxAll a) (relaxAll b)
  | .wrap w τ => .wrap w (relaxAll τ)
```
```lean
-- lean/Toy/Modality/SROA.lean:296
def retype (τ : Ty) (q : Path) (σ : Ty) : Ty := if relaxedOn τ q then relaxAll σ else σ
```
```lean
-- lean/Toy/Modality/SROA.lean:300
abbrev Policy := Ty → List Path → Option (List (Path × Ty))
```
```lean
-- lean/Toy/Modality/SROA.lean:304
def repairExclude : Policy := fun τ qs => if containsRelaxer τ then none else some (scalarize τ qs)
```
```lean
-- lean/Toy/Modality/SROA.lean:308-309
def repairRetype : Policy := fun τ qs =>
  some (qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, retype τ q σ))
```
```lean
-- lean/Toy/Modality/SROA.lean:314-315
def repairStopAtRelaxer : Policy := fun τ qs =>
  if qs.all (fun q => (fieldTy τ q).isNone || !relaxedOn τ q) then some (scalarize τ qs) else none
```
```lean
-- lean/Toy/Modality/SROA.lean:318
def naivePolicy : Policy := fun τ qs => some (scalarize τ qs)
```
```lean
-- lean/Toy/Modality/SROA.lean:321-322
def PolicySound (pol : Policy) : Prop :=
  ∀ τ qs locals, pol τ qs = some locals → Refines τ locals
```
```lean
-- lean/Toy/Modality/SROA.lean:327-330
def PolicyExact (pol : Policy) : Prop :=
  ∀ τ qs locals, pol τ qs = some locals →
    locals.map Prod.fst = qs.filter (fun q => (fieldTy τ q).isSome) ∧
    ∀ q σ, (q, σ) ∈ locals → ∀ p', modAt σ p' = modAt τ (q ++ p')
```

Examples: `ex_repair_helpers`, `ex_policy`.

#### Witness traces

```lean
-- lean/Toy/Modality/Lattice.lean:40
def wAlloc (s : Shape) (base : Nat) : Alloc := ⟨0, base, s.size⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:44
def tStar (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:47
def tMis (s : Shape) : Trace := ⟨1, [wAlloc s 1], [], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:50
def tNull : Trace := ⟨0, [], [], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:53
def tDangling (s : Shape) : Trace := ⟨s.align, [], [], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:56
def tFreed (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [.free .arg 0], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:59
def tArgWrite (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [.write .arg s.align], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:62-63
def tForeignRead (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.read .other s.align], []⟩
```
```lean
-- lean/Toy/Modality/Lattice.lean:67-69
def tOutOfRange (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.write .arg (s.align + s.size), .read .other (s.align + s.size)],
    []⟩
```
```lean
-- lean/Toy/Modality/Lowering.lean:193-194
def tConflict (s : Shape) : Trace :=
  ⟨s.align, [wAlloc s s.align], [.write .arg s.align, .read .other s.align], []⟩
```
```lean
-- lean/Toy/Modality/Lowering.lean:198
def tReadAfter (s : Shape) : Trace := ⟨s.align, [wAlloc s s.align], [], [.read .other s.align]⟩
```
```lean
-- lean/Toy/Modality/SROA.lean:144-145
def tDangleAliased (s : Shape) : Trace :=
  ⟨s.align, [], [.write .other s.align, .read .arg (s.align + s.size)], []⟩
```

### Cards

#### `R1-lattice` — `mod_bounded_lattice`

Kind: theorem. Tier: T0 (Powerset lattices and closure operators are textbook; restated for the seven atoms and the shape-dependent closure.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lattice.lean:250-258
theorem mod_bounded_lattice :
    (∀ m : Mod, m ≤ m) ∧
    (∀ m₁ m₂ m₃ : Mod, m₁ ≤ m₂ → m₂ ≤ m₃ → m₁ ≤ m₃) ∧
    (∀ m₁ m₂ : Mod, m₁ ≤ m₂ → m₂ ≤ m₁ → m₁ = m₂) ∧
    (∀ m₁ m₂ : Mod, Mod.inf m₁ m₂ ≤ m₁ ∧ Mod.inf m₁ m₂ ≤ m₂) ∧
    (∀ m m₁ m₂ : Mod, m ≤ m₁ → m ≤ m₂ → m ≤ Mod.inf m₁ m₂) ∧
    (∀ m₁ m₂ : Mod, m₁ ≤ Mod.sup m₁ m₂ ∧ m₂ ≤ Mod.sup m₁ m₂) ∧
    (∀ m m₁ m₂ : Mod, m₁ ≤ m → m₂ ≤ m → Mod.sup m₁ m₂ ≤ m) ∧
    (∀ m : Mod, Mod.bot ≤ m ∧ m ≤ Mod.top) := by …
```
```lean
-- lean/Toy/Modality/Lattice.lean:284-291
theorem cl_closure_operator_and_closed_sublattice (s : Shape) :
    (∀ m, m ≤ cl s m) ∧
    (∀ m₁ m₂, m₁ ≤ m₂ → cl s m₁ ≤ cl s m₂) ∧
    (∀ m, cl s (cl s m) = cl s m) ∧
    (∀ m, Closed s (cl s m)) ∧
    (∀ m₁ m₂, Closed s m₁ → Closed s m₂ → Closed s (Mod.inf m₁ m₂)) ∧
    (∀ m₁ m₂, Closed s m₁ → Closed s m₂ → Closed s (Mod.sup m₁ m₂)) ∧
    Closed s Mod.top ∧ Closed s (cl s Mod.bot) := by …
```

Plain claim: Modalities (sets of the seven capability atoms, `Mod`) ordered by inclusion form a bounded lattice with meet `Mod.inf`, join `Mod.sup`, least element `Mod.bot` and greatest element `Mod.top`; and (`cl_closure_operator_and_closed_sublattice`) for every pointee shape `s`, implication closure `cl s` is extensive, monotone and idempotent with closed values, and the `s`-closed modalities contain `Mod.top` and `cl s Mod.bot` and are closed under `Mod.inf` and `Mod.sup` (a sublattice).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): none needed; the card concerns the toy's order structure and closure operator and makes no claim about rustc or LLVM.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `ex_closed` (e.g. `refFull` is closed for `s1`) and `ex_mod_inf_sup` (the meet of `refFull` and `mutFull` is computed). (Lean: `ex_closed`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-lattice`”.

Prior art:

- Order theory and abstract interpretation: Davey, Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press 2002, doi:10.1017/CBO9780511809088 (powerset lattices, closure operators, Galois connections); Cousot, Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, doi:10.1145/512950.512973.
- Reference-capability lattices in type systems (different setting, not re-modelled): Gordon, Parkinson, Parsons, Bromfield, Duffy, "Uniqueness and Reference Immutability for Safe Parallelism", OOPSLA 2012, doi:10.1145/2384616.2384619.

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R1-antitone` — `den_antitone`

Kind: theorem. Tier: T0 (Immediate from the definition of the semantics; kept as a labelled reference point.) Depth: definitional. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lattice.lean:341-342
theorem den_antitone (s : Shape) {m₁ m₂ : Mod} (h : m₁ ≤ m₂) (t : Trace)
    (ht : den s m₂ t) : den s m₁ t := …
```
```lean
-- lean/Toy/Modality/Lattice.lean:346-347
theorem den_sup_iff (s : Shape) (m₁ m₂ : Mod) (t : Trace) :
    den s (Mod.sup m₁ m₂) t ↔ den s m₁ t ∧ den s m₂ t := by …
```

Plain claim: For every shape `s`, modalities `m₁ m₂` and trace `t`: if `m₁ ≤ m₂` and `t ∈ ⟦m₂⟧` (`den s m₂ t`), then `t ∈ ⟦m₁⟧`; and (`den_sup_iff`) `t ∈ ⟦Mod.sup m₁ m₂⟧` iff `t ∈ ⟦m₁⟧` and `t ∈ ⟦m₂⟧`. `den s m t` is the conjunction of the trace meanings `atomSat s a t` of the atoms `a` of `m`, with no further condition (`den_bot`: every trace is in `⟦Mod.bot⟧`).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): none needed; the card concerns the toy's semantics `den` and makes no claim about rustc or LLVM.

Hypothesis ledger:

- `h (den_antitone) : m₁ ≤ m₂` — the weaker modality's atoms are among the stronger's; tight: counterexample `cex_den_antitone_le`, in the class the one-byte shape s1, m₁ = Mod.top, m₂ = Mod.bot, t = tNull.
- `ht (den_antitone) : den s m₂ t` — the trace is permitted by the stronger modality; tight: counterexample `cex_den_antitone_ht`, in the class the one-byte shape s1, m₁ = refFull, m₂ = Mod.top, t = tNull.

Non-vacuity witness: `nv_den_antitone`: `refFull ≤ Mod.top` and `tStar s1 ∈ ⟦Mod.top⟧`. (Lean: `nv_den_antitone`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-antitone`”.

Prior art:

- Immediate from the definitions; no source relied on.

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R1-closure` — `den_cl_iff`

Kind: theorem. Tier: T1 (The implications are folklore (dereferenceable implies non-null in address space 0); stated as a semantic invariance of the closure.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lattice.lean:361
theorem den_cl_iff (s : Shape) (m : Mod) (t : Trace) : den s (cl s m) t ↔ den s m t := by …
```

Plain claim: For every shape `s`, modality `m` and trace `t`: `t ∈ ⟦cl s m⟧` iff `t ∈ ⟦m⟧`. The atoms added by closure hold on every trace of `⟦m⟧`: `derefEntry` from `derefWhole`; `nonnull` from either deref atom, because address `0` is never inside an allocation (`Alloc.covers` requires `0 < al.base ∧ al.base ≤ a`); and `aligned` when the alignment is `1`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the closure rules mirror two documented LLVM facts, read as the toy's design rather than proved about LLVM: `dereferenceable` implies `nonnull` in `addrspace(0)` unless `null_pointer_is_valid` is set (LangRef lines 1627-1631), which the toy reproduces by excluding address `0` from every allocation, and alignment 1 is trivially satisfied. No model–system relation is proved, and these statements neither establish nor refute the corresponding claims about LLVM.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `nv_den_cl`: at the non-closed modality `{derefWhole}` for `s1`, `tStar s1` is in both sides and `tNull` in neither. (Lean: `nv_den_cl`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-closure`”.

Prior art:

- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R1-embedding` — `den_subset_iff_le_cl`

Kind: characterization. Tier: T1 (Order embedding of a finite capability set into trace sets via independent witnesses; folklore made precise.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lattice.lean:389-390
theorem den_subset_iff_le_cl (s : Shape) (m₁ m₂ : Mod) :
    (∀ t, den s m₁ t → den s m₂ t) ↔ m₂ ≤ cl s m₁ := by …
```
```lean
-- lean/Toy/Modality/Lattice.lean:402-403
theorem den_subset_iff_le_of_closed (s : Shape) {m₁ : Mod} (h : Closed s m₁) (m₂ : Mod) :
    (∀ t, den s m₁ t → den s m₂ t) ↔ m₂ ≤ m₁ := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`) and modalities `m₁ m₂`: every trace of `⟦m₁⟧` is in `⟦m₂⟧` iff `m₂ ≤ cl s m₁`; and (`den_subset_iff_le_of_closed`) if `m₁` is closed for `s`, then `⟦m₁⟧ ⊆ ⟦m₂⟧` iff `m₂ ≤ m₁`. For each atom outside `cl s m₁` an explicit witness trace satisfies `m₁` and violates the atom (`tMis`, `tNull`, `tDangling`, `tFreed`, `tArgWrite`, `tForeignRead`, `tOutOfRange`).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): none beyond the reading of the atoms described under Applicability; the card makes no claim about rustc or LLVM.

Hypothesis ledger:

- `h : Closed s m₁ (den_subset_iff_le_of_closed)` — lets the closure be dropped from the right-hand side; tight: counterexample `cex_den_subset_closed`, in the class the one-byte shape s1, m₁ = {derefEntry}, m₂ = {nonnull}.

Non-vacuity witness: `nv_den_subset`: `refFull` is closed for `s1` and both sides hold for `m₂ = tRelax refFull`. (Lean: `nv_den_subset`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-embedding`”.

Prior art:

- Order theory and abstract interpretation: Davey, Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press 2002, doi:10.1017/CBO9780511809088 (powerset lattices, closure operators, Galois connections); Cousot, Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, doi:10.1145/512950.512973.

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R1-transformers-best` — `kindBase_best`

Kind: characterization. Tier: T1 (The documented per-constructor rules, transcribed as trace predicates, with the transformers shown to be their best abstraction; folklore made precise.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Transformers.lean:189-190
theorem kindBase_best (s : Shape) (k : PtrKind) (m' : Mod) :
    (∀ t, kindRule s k t → den s m' t) ↔ m' ≤ cl s (kindBase k) := by …
```
```lean
-- lean/Toy/Modality/Transformers.lean:198-199
theorem tRelax_best (s : Shape) (m m' : Mod) :
    (∀ t, relaxRule s m t → den s m' t) ↔ m' ≤ cl s (tRelax m) := by …
```
```lean
-- lean/Toy/Modality/Transformers.lean:169-174
theorem transformers_respect_den (s : Shape) (m₁ m₂ : Mod)
    (h : ∀ t, den s m₁ t ↔ den s m₂ t) :
    (∀ t, den s (tRelax m₁) t ↔ den s (tRelax m₂) t) ∧
    (∀ t, den s (tCell m₁) t ↔ den s (tCell m₂) t) ∧
    (∀ t, den s (tPin m₁) t ↔ den s (tPin m₂) t) ∧
    (∀ t, den s (tBox m₁) t ↔ den s (tBox m₂) t) := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), pointer kind `k` and modality `m'`: every trace permitted by `kindRule s k` satisfies `m'` iff `m' ≤ cl s (kindBase k)`; (`tRelax_best`) for all modalities `m m'`, every trace permitted by `relaxRule s m` satisfies `m'` iff `m' ≤ cl s (tRelax m)`; and (`transformers_respect_den`) for modalities `m₁ m₂` with `⟦m₁⟧ = ⟦m₂⟧`, each of `tRelax`, `tCell`, `tPin`, `tBox` gives modalities with equal semantics. Each transformer first adds the atoms implied by `derefWhole ⇒ derefEntry ⇒ nonnull` (`clDeref`), then drops its atoms (`tRelax` keeps `aligned` and `nonnull`; `tCell` drops `frozen`, `derefWhole`, `unique`; `tPin` drops `unique`, `derefWhole`; `tBox` drops `derefWhole`).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `kindRule` and `relaxRule` transcribe, as trace predicates, the weakenings documented for `MaybeDangling` (RFC 3336 lines 94-102 and 139-148; `library/core/src/mem/maybe_dangling.rs` lines 6-10) and the attribute conditions in rustc's ABI computation (`compiler/rustc_ty_utils/src/abi.rs` lines 339-416 at 26bfbf28: `noalias` from `frozen` for shared and from `unpin` for mutable references, `nofree` for frozen shared and `unpin` mutable references, `readonly` for frozen shared references). The transcription is checked by reading these sources against the definitions quoted in this report; it is not a proved relation, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger:

- `h : ∀ t, den s m₁ t ↔ den s m₂ t (transformers_respect_den)` — the two inputs are semantically equal; tight: counterexample `cex_transformers_respect_h`, in the class the one-byte shape s1, m₁ = Mod.bot, m₂ = refFull.

Non-vacuity witness: `nv_transformers_best`: every rule permits `tStar s1` and implies the computed modality; `nv_transformers_respect`: `{derefWhole}` and its closure for `s2` are distinct with equal semantics. (Lean: `nv_transformers_best`, `nv_transformers_respect`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-transformers-best`”.

Prior art:

- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).
- rustc `compiler/rustc_middle/src/ty/layout.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 1092-1104 (`MaybeDangling` arm: recurse into field 0, then `safe: None` with line 1095 "// Mark the pointer as raw", `size: Size::ZERO`, and line 1100 "// Preserve the alignment assertion! That is required even inside `MaybeDangling`.") and lines 1132-1141 (null-niche recursion: recurse into the untagged variant only if `niche_start == 0`, relying on `dereferenceable` being added only with a non-null proof and on null being aligned for all alignments) (source).
- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).
- rustc `library/core/src/mem/maybe_dangling.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 6-10 (a reference wrapped in `MaybeDangling`, including in a (nested) field, does not have to follow pointer aliasing rules or be dereferenceable) and `library/core/src/mem/manually_drop.rs` lines 156-160 (`ManuallyDrop` wraps `MaybeDangling<T>`) (documentation, source).
- RFC 3467 (`UnsafePinned`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3467-unsafe-pinned.md` line 245 (`impl<T> !Unpin for UnsafePinned<T>`) and lines 364-366 (`noalias` on mutable references is tied to `UnsafeUnpin` types).
- Published package `pin-structural-projection-address-stability-and-drop-guarantee` (google/zerocopy branch `reference`, commit 383075883be4fb20e686252c4c5f8c15ad161414), card `unpin-sound-iff-pinned-fields-unpin`: the `Unpin` side of mutable references to non-`Unpin` pointees.
- Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness` (google/zerocopy branch `reference`, commit 6249da8fcc95a6f49780588838ac00f4686187bd), card `R7a-immutable-not-byte-determined`: interior mutability (the toy `Ty.freeze`) is not determined by bytes.

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R1-dropped-atoms` — `transformer_dropped_atoms_can_fail`

Kind: counterexample. Tier: T1 (Explicit witnesses for the documented weakenings.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Transformers.lean:218-230
theorem transformer_dropped_atoms_can_fail (s : Shape) :
    (relaxRule s refFull (tDangling s) ∧ ¬ atomSat s .derefEntry (tDangling s) ∧
      ¬ atomSat s .derefWhole (tDangling s)) ∧
    (relaxRule s refFull (tArgWrite s) ∧ ¬ atomSat s .frozen (tArgWrite s)) ∧
    (relaxRule s refFull (tOutOfRange s) ∧ ¬ atomSat s .bounded (tOutOfRange s)) ∧
    (relaxRule s mutFull (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.shared false) (tArgWrite s) ∧ ¬ atomSat s .frozen (tArgWrite s)) ∧
    (kindRule s (.shared false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.mutRef false) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.mutRef false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.box true) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) ∧
    (kindRule s (.box false) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s)) ∧
    (kindRule s (.box false) (tFreed s) ∧ ¬ atomSat s .derefWhole (tFreed s)) := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), explicit traces permitted by the transcribed rules violate each atom that a transformer removes from the modality it is applied to: inside a relaxing wrapper a former `refFull` pointer may dangle (`tDangling s`, failing `derefEntry` and `derefWhole`), its pointee may be written (`tArgWrite s`, failing `frozen`), and it may be used just outside the pointee (`tOutOfRange s`, failing `bounded`); a former `mutFull` pointer may be read through an unrelated pointer (`tForeignRead s`, failing `unique`); for `tCell refFull` (shared reference to a non-`Freeze` pointee) the pointee may be written (failing `frozen`) and freed (`tFreed s`, failing `derefWhole`); for `tPin mutFull` (mutable reference to a non-`Unpin` pointee) it may be read through an unrelated pointer (failing `unique`) and freed (failing `derefWhole`); for `tBox mutFull` it may be freed (failing `derefWhole`); and for `tBox (tPin mutFull)` it may be read through an unrelated pointer (failing `unique`) and freed (failing `derefWhole`).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): each witness trace illustrates a weakening that the cited documentation states in prose (RFC 3336 lines 94-102: references inside `MaybeDangling` need not be dereferenceable or follow aliasing guarantees; `compiler/rustc_ty_utils/src/abi.rs` lines 366-410 at 26bfbf28: no `noalias` or `nofree` for shared references to non-`Freeze` pointees, no `nofree` for boxes). Which of the toy traces a real program can produce is not examined, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: Each conjunct exhibits its trace. (Lean: `transformer_dropped_atoms_can_fail`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R1-dropped-atoms`”.

Prior art:

- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).
- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R2-comp-iff` — `compSound_iff_transformerSound_and_deep`

Kind: characterization. Tier: T2 (The documented deep-relaxation rule as a necessary and sufficient condition over all relaxing transformers.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Types.lean:320-321
theorem compSound_iff_transformerSound_and_deep (T : Mod → Mod) (deep : Bool) :
    CompSound T deep ↔ TransformerSound T ∧ deep = true := by …
```
```lean
-- lean/Toy/Modality/Types.lean:434-437
theorem compSound_on_docTy_not_imply_transformerSound :
    (∀ τ, DocTy τ → ∀ p s m m₀, comp tRelaxExceptFrozenOnly true τ p = some (s, m) →
      req τ p = some (s, m₀) → ∀ t, den s m₀ t → den s m t) ∧
    ¬ TransformerSound tRelaxExceptFrozenOnly := by …
```

Plain claim: For every relaxing transformer `T : Mod → Mod` and flag `deep`, the bottom-up computation `comp T deep` is sound against the top-down reference semantics `req` at every pointer leaf of every type — pointer leaves `Ty.ptr s m` of every positive-size shape (every `Shape` has `size_pos : 0 < size`) and every modality included — iff `T` is sound (`TransformerSound T`, equivalently `∀ m, T m ≤ tRelax m` by `transformerSound_iff_le_tRelax`) and `deep = true`. Restricted to types built from the four documented pointer constructors (`DocTy`), the "only if" for `T` fails (`compSound_on_docTy_not_imply_transformerSound`: with `tRelaxExceptFrozenOnly` the deep computation is sound on every `DocTy` type and the transformer is not sound).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `comp T true` is read as the layout recursion in which rustc marks a pointer below `MaybeDangling` as raw (`compiler/rustc_middle/src/ty/layout.rs` lines 1092-1104 at 26bfbf28) and RFC 3336's rule that the relaxation reaches values in (nested) fields (lines 139-148). The reading is argued from these sources, not proved, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger:

- `TransformerSound T (right-hand side, ← direction)` — the relaxing transformer must not keep atoms `tRelax` drops; tight: counterexample `cex_comp_transformer`, in the class the identity transformer with deep = true.
- `deep = true (right-hand side, ← direction)` — relaxation must reach nested pointer leaves; tight: counterexample `cex_comp_deep`, in the class the documented transformer tRelax with deep = false.

Non-vacuity witness: `nv_compSound`: both sides hold for `tRelax` with `deep = true`. (Lean: `nv_compSound`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R2-comp-iff`”.

Prior art:

- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).
- rustc `library/core/src/mem/maybe_dangling.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 6-10 (a reference wrapped in `MaybeDangling`, including in a (nested) field, does not have to follow pointer aliasing rules or be dereferenceable) and `library/core/src/mem/manually_drop.rs` lines 156-160 (`ManuallyDrop` wraps `MaybeDangling<T>`) (documentation, source).
- RFC 1860 (`ManuallyDrop`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/1860-manually-drop.md` lines 54-60 (the `ManuallyDrop<T>` wrapper struct).
- rustc `compiler/rustc_middle/src/ty/layout.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 1092-1104 (`MaybeDangling` arm: recurse into field 0, then `safe: None` with line 1095 "// Mark the pointer as raw", `size: Size::ZERO`, and line 1100 "// Preserve the alignment assertion! That is required even inside `MaybeDangling`.") and lines 1132-1141 (null-niche recursion: recurse into the untagged variant only if `niche_start == 0`, relying on `dereferenceable` being added only with a non-null proof and on null being aligned for all alignments) (source).

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R2-shallow-cex` — `shallow_relaxer_leaves_nested_promises`

Kind: counterexample. Tier: T1 (A concrete instance of the documented nested-field rule.) Depth: definitional. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Types.lean:304-309
theorem shallow_relaxer_leaves_nested_promises (s : Shape) :
    (∀ T : Mod → Mod, comp T false (tyNestedMD s) pathNestedMD = some (s, mutFull)) ∧
    req (tyNestedMD s) pathNestedMD = some (s, tRelax mutFull) ∧
    mutFull.derefEntry = true ∧ mutFull.unique = true ∧
    den s (tRelax mutFull) (tDangling s) ∧ ¬ atomSat s .derefEntry (tDangling s) ∧
    den s (tRelax mutFull) (tForeignRead s) ∧ ¬ atomSat s .unique (tForeignRead s) := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), in `tyNestedMD s` (`MaybeDangling<(Wrapper(&mut T), u8)>`), the shallow computation with any relaxing transformer `T` gives the nested `&mut T` leaf (path `pathNestedMD`) the full modality `mutFull` (with `derefEntry` and `unique`), while the reference requirement is `tRelax mutFull`; the dangling trace `tDangling s` and the foreign-read trace `tForeignRead s` satisfy the requirement and violate `derefEntry`, respectively `unique`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the type `tyNestedMD s` renders `MaybeDangling<(Wrapper(&mut T), u8)>`, a by-value nesting to which RFC 3336 lines 139-148 apply the relaxation; the toy computation is not rustc's, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: The theorem exhibits both traces. (Lean: `shallow_relaxer_leaves_nested_promises`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R2-shallow-cex`”.

Prior art:

- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).
- rustc `library/core/src/mem/maybe_dangling.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 6-10 (a reference wrapped in `MaybeDangling`, including in a (nested) field, does not have to follow pointer aliasing rules or be dereferenceable) and `library/core/src/mem/manually_drop.rs` lines 156-160 (`ManuallyDrop` wraps `MaybeDangling<T>`) (documentation, source).

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R2-documented-exact` — `comp_tRelax_deep_eq_req`

Kind: theorem. Tier: T1 (The documented computation coincides with the reference semantics; folklore made precise.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Types.lean:377
theorem comp_tRelax_deep_eq_req (τ : Ty) (p : Path) : comp tRelax true τ p = req τ p := by …
```

Plain claim: For every type `τ` and path `p`, `comp tRelax true τ p = req τ p`: the documented deep computation equals the reference requirement at every path.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `comp tRelax true` is the toy rendering of the documented deep relaxation (RFC 3336 lines 94-102 and 139-148); these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `ex_comp_req`: both sides are `some (s1, tRelax mutFull)` at the nested leaf of `tyNestedMD s1`. (Lean: `ex_comp_req`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R2-documented-exact`”.

Prior art:

- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).

Design question: Is there a compositional lattice of pointer-guarantee modalities with sound per-constructor transformers?

#### `R3-lower-sound` — `lower_sound`

Kind: theorem. Tier: T1 (Each attribute condition is documented engineering; stated as one soundness theorem for call-entry modalities at both positions.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lowering.lean:318-319
theorem lower_sound (s : Shape) (pos : Pos) (m : Mod) (t : Trace) (ht : den s m t) :
    gammaSet s pos (lower s pos m) t := by …
```

Plain claim: For every shape `s`, position `pos` (argument or return), modality `m` and trace `t` with `t ∈ ⟦m⟧`, `t` satisfies every attribute of `lower s pos m` at `pos` (`⟦m⟧ ⊆ γ(α m)`). The modality `m` is a call-entry modality (promises about a pointer that exists at call entry, at entry and over the call); at `pos = .arg` the attributes are argument attributes (`dereferenceable` evaluated at call entry; `noalias`, `nofree` and `readonly` over the call), and at `pos = .ret` they are return-value attributes evaluated at the return point by `attrSat s .ret` on the same trace, that is, for that pointer when it is returned; `lower s .ret m` is not a lowering of a returned value's own validity invariant at the return point. From the closure `cl s m`, `lower` emits `align` from `aligned` and `nonnull` from `nonnull`; `dereferenceable` and `dereferenceable_or_null` from `derefEntry` at argument position and from `derefWhole` (covered at call entry and not freed during the call) at return position; and at argument position `noalias` from `bounded` together with `frozen` or `unique`, `nofree` from `derefWhole`, and `readonly` from `bounded` together with `frozen`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the attribute meanings `attrSat` are the toy's readings of LLVM LangRef (documentation; lines listed under Prior art), and `lower s .arg` is compared in prose with the argument attribute conditions in `compiler/rustc_ty_utils/src/abi.rs` lines 339-416 at 26bfbf28, without any claim that rustc computes `lower`. At return position the toy describes the attributes to which a returned pointer is entitled by its call-entry modality; it models neither rustc's return-value attributes nor a returned value's validity invariant. These statements neither establish nor refute the corresponding claims about rustc or LLVM.

Hypothesis ledger:

- `ht : den s m t` — the trace is one the modality permits; tight: counterexample `cex_lower_sound_ht`, in the class the one-byte shape s1, m = refFull, the trace tFreed s1.

Non-vacuity witness: `nv_lower`: `tStar s1 ∈ ⟦refFull⟧`. (Lean: `nv_lower`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R3-lower-sound`”.

Prior art:

- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).
- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).
- The Rust Reference at rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, `src/behavior-considered-undefined.md`: producing an invalid value is undefined behaviour, and line 59 reads `"Producing" a value happens any time a value is assigned to or read from a place, passed to a function/primitive operation or returned from a function/primitive operation.`; line 152 requires a reference or `Box<T>` to be aligned and non-null and not dangling, and line 104 calls a reference dangling if not all of the bytes it points to are part of the same live allocation (documentation). This is the validity invariant of a returned reference or box at the return point, which the toy does not represent.
- Formal treatments of LLVM IR semantics and attributes (not re-modelled): Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes, "Taming Undefined Behavior in LLVM", PLDI 2017, doi:10.1145/3062341.3062343 (poison versus immediate undefined behaviour, relevant to `align`/`nonnull` without `noundef`); Lopes, Lee, Hur, Liu, Regehr, "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, doi:10.1145/3453483.3454030.

Design question: Is the lowering of modalities to IR parameter attributes a sound and best abstraction?

#### `R3-lower-best` — `lower_best_iff`

Kind: characterization. Tier: T2 (Known attribute conditions restated as a best-abstraction characterization over all attribute sets.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lowering.lean:357-358
theorem lower_best_iff (s : Shape) (pos : Pos) (m : Mod) (A : AttrSet) :
    (∀ t, den s m t → gammaSet s pos A t) ↔ A ≤ lower s pos m := by …
```
```lean
-- lean/Toy/Modality/Lowering.lean:371-374
theorem lower_unique (s : Shape) (pos : Pos) (m : Mod) (A : AttrSet)
    (hs : ∀ t, den s m t → gammaSet s pos A t)
    (hb : ∀ B : AttrSet, (∀ t, den s m t → gammaSet s pos B t) → B ≤ A) :
    A = lower s pos m := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), position `pos`, modality `m` and attribute set `A`: every trace of `⟦m⟧` satisfies `A` at `pos` iff `A ≤ lower s pos m`; and (`lower_unique`) an attribute set `A` that is sound for `⟦m⟧` at `pos` and contains every attribute set sound for `⟦m⟧` at `pos` equals `lower s pos m`. The modality `m` is a call-entry modality, so at `pos = .ret` `lower s .ret m` is the largest set of return-value attributes, evaluated at the return point by `attrSat s .ret`, that the call-entry modality `m` justifies for a pointer carrying it when it is returned; it is not the best lowering of a returned value's validity invariant at the return point, which the toy does not represent.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): as for `R3-lower-sound`: 'best' is relative to the toy's seven attributes and their LangRef-style readings, and at return position it concerns the attributes justified by a call-entry modality, not rustc's return-value attributes or a returned value's validity invariant. These statements neither establish nor refute the corresponding claims about rustc or LLVM.

Hypothesis ledger:

- `hs (lower_unique) : ∀ t, den s m t → gammaSet s pos A t` — excludes over-large sets; tight: counterexample `cex_lower_unique_sound`, in the class the one-byte shape s1, m = tCell refFull, A = all seven attributes.
- `hb (lower_unique) : ∀ B, (∀ t, den s m t → gammaSet s pos B t) → B ≤ A` — excludes under-large sets; tight: counterexample `cex_lower_unique_best`, in the class the one-byte shape s1, m = refFull, A = the empty set.

Non-vacuity witness: `nv_lower`: `A = lower s1 .arg refFull` satisfies both hypotheses of `lower_unique`. (Lean: `nv_lower`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R3-lower-best`”.

Prior art:

- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).
- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).
- The Rust Reference at rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, `src/behavior-considered-undefined.md`: producing an invalid value is undefined behaviour, and line 59 reads `"Producing" a value happens any time a value is assigned to or read from a place, passed to a function/primitive operation or returned from a function/primitive operation.`; line 152 requires a reference or `Box<T>` to be aligned and non-null and not dangling, and line 104 calls a reference dangling if not all of the bytes it points to are part of the same live allocation (documentation). This is the validity invariant of a returned reference or box at the return point, which the toy does not represent.
- Published package `galois-connections-best-abstract-transformers-and-fixpoint-transfer` (google/zerocopy branch `reference`, commit a0dca4883c555805181f8149eafd7e65ab238991), cards `R1-gc-iff` (characterization of the Galois-connection notion, stated for a reflexive and transitive abstract order), `R2-best-sound` and `R2-best-least` (best abstract transformers): cited, not re-proved; its `GaloisConnection` and `Pred` definitions are copied into the module `Toy.Modality.Imported`.
- Published package `aliasing-models-and-reference-based-optimizations` (google/zerocopy branch `reference`, commit 62e8715787fde13fecdffe87b22f5700a96af019), cards `R1a-read-elim-mut-unpassed` and `R2a-read-elim-shared-ro`: toy justifications of reference-based optimizations; used as justification for `noalias`, not re-modelled.
- Semantic justifications of `noalias` for references (not re-modelled): Jung, Jourdan, Krebbers, Dreyer, "RustBelt", POPL 2018, doi:10.1145/3158154; Jung, Dang, Kang, Dreyer, "Stacked Borrows", POPL 2020, doi:10.1145/3371109; Villani, Hostert, Dreyer, Jung, "Tree Borrows", PLDI 2025, doi:10.1145/3735592.
- Formal treatments of LLVM IR semantics and attributes (not re-modelled): Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes, "Taming Undefined Behavior in LLVM", PLDI 2017, doi:10.1145/3062341.3062343 (poison versus immediate undefined behaviour, relevant to `align`/`nonnull` without `noundef`); Lopes, Lee, Hur, Liu, Regehr, "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, doi:10.1145/3453483.3454030.
- Novelty search (web search for mechanized lowerings of Rust pointer guarantees to LLVM parameter attributes, best-abstraction lowerings, and SROA preconditions for relaxing wrappers) found no mechanized statement of this form; tier kept below T3.

Design question: Is the lowering of modalities to IR parameter attributes a sound and best abstraction?

#### `R3-galois` — `alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den`

Kind: theorem. Tier: T0 (The first conjunct is the polarity Galois connection that every relation induces (textbook); the second is a corollary of `lower_best_iff`.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lowering.lean:457-459
theorem alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den (s : Shape) (pos : Pos) :
    Imported.GaloisConnection (alphaSet s pos) (gammaDual s pos) ∧
    ∀ m, lower s pos m = (alphaSet s pos (denP s m)).val := by …
```
```lean
-- lean/Toy/Modality/Lowering.lean:439-440
theorem polarity_galois (P : Attr → Trace → Prop) :
    Imported.GaloisConnection (alphaOf P) (gammaOf P) := by …
```
```lean
-- lean/Toy/Modality/Lowering.lean:495-499
theorem lower_no_left_adjoint_and_arg_no_right_adjoint (s : Shape) (pos : Pos) :
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), A ≤ lower s pos m ↔ u A ≤ m) ∧
    (¬ ∃ u : AttrSet → {m : Mod // Closed s m}, ∀ (m : {m : Mod // Closed s m}) (A : AttrSet),
      A ≤ lower s pos m.1 ↔ (u A).1 ≤ m.1) ∧
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), lower s .arg m ≤ A ↔ m ≤ u A) := by …
```

Plain claim: For every relation `P` between attributes and traces, `alphaOf P` and `gammaOf P` form a Galois connection in the imported sense with the reverse-inclusion order on attribute sets (`polarity_galois`); for every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`) and position `pos`, the instance `alphaSet s pos`, `gammaDual s pos` (with `P = attrSat s pos`) is therefore a Galois connection, and for every modality `m`, `lower s pos m = (alphaSet s pos (denP s m)).val`. By contrast (`lower_no_left_adjoint_and_arg_no_right_adjoint`), for every shape `s` and position `pos` there is no function `u : AttrSet → Mod` with `A ≤ lower s pos m ↔ u A ≤ m` for all `m` and `A` (no left adjoint), neither over all modalities nor over `s`-closed ones, and there is no function `u : AttrSet → Mod` with `lower s .arg m ≤ A ↔ m ≤ u A` for all `m` and `A` (no right adjoint of the argument lowering over all modalities).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): none beyond the toy's LangRef-style attribute readings; the Galois connection and the adjoint statements are order-theoretic facts about the toy and make no claim about rustc or LLVM.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `ex_galois_defs`: instances of `AttrDual`, `gammaDual`, `denP` and `alphaSet s1 .arg (denP s1 refFull) = lower s1 .arg refFull`. (Lean: `ex_galois_defs`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R3-galois`”.

Prior art:

- Polarity Galois connections induced by a relation between objects and attributes: Ganter, Wille, Formal Concept Analysis: Mathematical Foundations, Springer 1999, doi:10.1007/978-3-642-59830-2; Davey, Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press 2002, doi:10.1017/CBO9780511809088.
- Order theory and abstract interpretation: Davey, Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press 2002, doi:10.1017/CBO9780511809088 (powerset lattices, closure operators, Galois connections); Cousot, Cousot, "Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints", POPL 1977, doi:10.1145/512950.512973.
- Published package `galois-connections-best-abstract-transformers-and-fixpoint-transfer` (google/zerocopy branch `reference`, commit a0dca4883c555805181f8149eafd7e65ab238991), cards `R1-gc-iff` (characterization of the Galois-connection notion, stated for a reflexive and transitive abstract order), `R2-best-sound` and `R2-best-least` (best abstract transformers): cited, not re-proved; its `GaloisConnection` and `Pred` definitions are copied into the module `Toy.Modality.Imported`.

Design question: Is the lowering of modalities to IR parameter attributes a sound and best abstraction?

#### `R3-stronger-unsound` — `stronger_arg_lowerings_counterexamples`

Kind: counterexample. Tier: T1 (Concrete witnesses for documented exclusions.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lowering.lean:672-705
theorem stronger_arg_lowerings_counterexamples (s : Shape) :
    ((lower s .arg (kindBase (.shared false))).nofree = false ∧
      den s (kindBase (.shared false)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (kindBase (.shared false))).readonly = false ∧
      den s (kindBase (.shared false)) (tArgWrite s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .readonly)
        (tArgWrite s)) ∧
    ((lower s .arg (kindBase (.shared false))).noalias = false ∧
      den s (kindBase (.shared false)) (tConflict s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.shared false))).insert .noalias)
        (tConflict s)) ∧
    ((lower s .arg (kindBase (.mutRef false))).noalias = false ∧
      den s (kindBase (.mutRef false)) (tConflict s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.mutRef false))).insert .noalias)
        (tConflict s)) ∧
    ((lower s .arg (kindBase (.mutRef false))).nofree = false ∧
      den s (kindBase (.mutRef false)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.mutRef false))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (kindBase (.box true))).nofree = false ∧
      den s (kindBase (.box true)) (tFreed s) ∧
      ¬ gammaSet s .arg ((lower s .arg (kindBase (.box true))).insert .nofree) (tFreed s)) ∧
    ((lower s .arg (tRelax refFull)).dereferenceable = false ∧
      den s (tRelax refFull) (tDangling s) ∧
      ¬ gammaSet s .arg ((lower s .arg (tRelax refFull)).insert .dereferenceable)
        (tDangling s)) ∧
    ((lower s .arg refFullNoBounded).noalias = false ∧
      (lower s .arg refFullNoBounded).readonly = false ∧
      den s refFullNoBounded (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg refFullNoBounded).insert .noalias) (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg refFullNoBounded).insert .readonly) (tOutOfRange s)) ∧
    ((lower s .arg mutFullNoBounded).noalias = false ∧
      den s mutFullNoBounded (tOutOfRange s) ∧
      ¬ gammaSet s .arg ((lower s .arg mutFullNoBounded).insert .noalias) (tOutOfRange s)) := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), each listed attribute is outside `lower s .arg m` for the listed `m`, and a trace of `⟦m⟧` violates `lower s .arg m` with that attribute added: for a shared reference to a non-`Freeze` pointee (`kindBase (.shared false)`), `nofree` (`tFreed s`), `readonly` (`tArgWrite s`) and `noalias` (`tConflict s`); for a mutable reference to a non-`Unpin` pointee (`kindBase (.mutRef false)`), `noalias` (`tConflict s`) and `nofree` (`tFreed s`); for a box of an `Unpin` pointee (`kindBase (.box true)`), `nofree` (`tFreed s`); `dereferenceable` inside a relaxing wrapper (`tRelax refFull`, `tDangling s`); `noalias` and `readonly` for `refFullNoBounded` and `noalias` for `mutFullNoBounded` (`refFull` and `mutFull` without `bounded`; `tOutOfRange s`, an access through the argument just outside the pointee).

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): each conjunct corresponds to an attribute that the cited rustc code does not attach in the corresponding case (`compiler/rustc_ty_utils/src/abi.rs` lines 366-415 at 26bfbf28) or that RFC 3336 lines 94-102 withdraws inside `MaybeDangling`; the correspondence is argued from these sources, and these statements neither establish nor refute the corresponding claims about rustc or LLVM.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: Each conjunct exhibits its trace. (Lean: `stronger_arg_lowerings_counterexamples`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R3-stronger-unsound`”.

Prior art:

- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).
- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).

Design question: Is the lowering of modalities to IR parameter attributes a sound and best abstraction?

#### `R3-position` — `refFull_arg_lowering_not_sound_at_return`

Kind: counterexample. Tier: T1 (Concrete witnesses that a call-entry modality entails different attributes at call entry and at the return point: argument versus return `noalias`, and call-entry dereferenceability versus dereferenceability at the return point after a free during the call. Neither witness concerns a returned value's validity invariant at the return point or the attributes rustc attaches to return values.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Lowering.lean:740-745
theorem refFull_arg_lowering_not_sound_at_return (s : Shape) :
    (lower s .arg refFull).noalias = true ∧ (lower s .arg refFull).nofree = true ∧
    (lower s .arg refFull).readonly = true ∧
    (∀ m, den s m (tReadAfter s)) ∧ attrSat s .arg .noalias (tReadAfter s) ∧
    ¬ attrSat s .ret .noalias (tReadAfter s) ∧
    ¬ gammaSet s .ret (lower s .arg refFull) (tReadAfter s) := by …
```
```lean
-- lean/Toy/Modality/Lowering.lean:763-767
theorem entry_deref_of_tCell_refFull_not_sound_at_return (s : Shape) :
    (lower s .arg (tCell refFull)).dereferenceable = true ∧
    den s (tCell refFull) (tFreed s) ∧ attrSat s .arg .dereferenceable (tFreed s) ∧
    ¬ attrSat s .ret .dereferenceable (tFreed s) ∧
    ¬ gammaSet s .ret (lower s .arg (tCell refFull)) (tFreed s) := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`): (`refFull_arg_lowering_not_sound_at_return`) the argument lowering of the call-entry modality `refFull` contains `noalias`, `nofree` and `readonly`; the trace `tReadAfter s` (an unrelated read of the pointee after the return) is in `⟦m⟧` for every modality `m`, satisfies argument `noalias` (over the call) and violates return `noalias` (after the return), so `lower s .arg refFull` is not sound at return position; and (`entry_deref_of_tCell_refFull_not_sound_at_return`) the argument lowering of the call-entry modality `tCell refFull` contains `dereferenceable` (evaluated at call entry), and the trace `tFreed s` (the pointee allocation is freed through the pointer during the call) is in `⟦tCell refFull⟧`, satisfies `dereferenceable` at argument position (call entry) and violates the toy's return-position `dereferenceable` (`DereferenceableAtReturn`, evaluated at the return point), so `lower s .arg (tCell refFull)` is not sound at return position: a pointer that carries the call-entry modality `tCell refFull` and is returned is not entitled to return-position `dereferenceable` by that modality.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): LangRef states that `dereferenceable` implies dereferenceability at the point of the attribute, which is function entry for arguments and the point of the call for return values, and that the underlying object may be freed after that point (lines 1636-1640) and gives return `noalias` an allocation-like meaning (lines 1528-1534); the toy's return-position readings follow these descriptions. The witnesses concern pointers carrying call-entry modalities, not the attributes rustc attaches to return values or a returned value's validity invariant, and these statements neither establish nor refute the corresponding claims about rustc or LLVM.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: Each theorem exhibits its trace. (Lean: `refFull_arg_lowering_not_sound_at_return`).

Positive control: `tRelax_arg_lowering_eq_ret_lowering`.

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R3-position`”.

Prior art:

- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).
- rustc `compiler/rustc_ty_utils/src/abi.rs` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 339-416 (in `arg_attrs_for_rust_scalar`, lines 321-420, whose parameter `is_return`, line 327, is `arg_idx.is_none()` at the call site, lines 589 and 602, hence true for the return value): `nonnull` from the validity range (lines 339-342); `pointee_align` (when the pointee alignment exceeds 1) and `pointee_size` are recorded at lines 346-352 for every pointer with pointee information, at argument and at return position alike (no `is_return` condition; line 352: `attrs.pointee_size = pointee.size;`); `noalias` is computed at lines 366-370 as `frozen` for shared references, `unpin` for mutable references, and `unpin && global && noalias_for_box` for boxes (line 369; `noalias_for_box` is the unstable `box_noalias` option, line 358), and is not emitted in return position (lines 371-375); `nofree` for frozen shared and `unpin` mutable references, never at return position or for boxes (lines 392-410); `readonly` for frozen shared references outside return position (lines 412-415); the comments link rust-lang/rust pull 98017 and unsafe-code-guidelines issues 326, 381 and 385. This package does not examine which LLVM attributes rustc's LLVM backend emits from these recorded fields, at argument or at return position. In `compiler/rustc_middle/src/ty/layout.rs` at the same commit, `frozen` and `unpin` are false unless optimizing (line 1051: `let optimize = tcx.sess.opts.optimize != OptLevel::No;`), `unpin` also requires `is_unsafe_unpin` (lines 1065-1067 for mutable references, 1082-1084 for boxes), and the box flag `global` is `this.ty.is_box_global(tcx)` (line 1085) (source).
- The Rust Reference at rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, `src/behavior-considered-undefined.md`: producing an invalid value is undefined behaviour, and line 59 reads `"Producing" a value happens any time a value is assigned to or read from a place, passed to a function/primitive operation or returned from a function/primitive operation.`; line 152 requires a reference or `Box<T>` to be aligned and non-null and not dangling, and line 104 calls a reference dangling if not all of the bytes it points to are part of the same live allocation (documentation). This is the validity invariant of a returned reference or box at the return point, which the toy does not represent.

Design question: Is the lowering of modalities to IR parameter attributes a sound and best abstraction?

#### `R4-niche-sound` — `liftOpt_sound_of_noneVal_zero`

Kind: characterization. Tier: T1 (The documented null-niche recursion, stated as soundness and optimality of the lifted lowering.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Niche.lean:94-95
theorem liftOpt_sound_of_noneVal_zero (s : Shape) (m : Mod) (t : Trace)
    (ht : denOpt s 0 m t) : gammaSet s .arg (liftOpt s m) t := by …
```
```lean
-- lean/Toy/Modality/Niche.lean:122-123
theorem liftOpt_best_iff (s : Shape) (m : Mod) (A : AttrSet) :
    (∀ t, denOpt s 0 m t → gammaSet s .arg A t) ↔ A ≤ liftOpt s m := by …
```

Plain claim: For every positive-size shape `s` (every `Shape` has `size_pos : 0 < size`), payload modality `m` and trace `t` with `denOpt s 0 m t` (either `t.addr = 0` and no argument-tagged read, write or free happens during the call (`NoArgEvents`), or `t ∈ ⟦m⟧`), `t` satisfies every attribute of `liftOpt s m` at argument position; `liftOpt s m` is `lower s .arg m` without `nonnull` and `dereferenceable`, so each of `align`, `dereferenceable_or_null`, `noalias`, `nofree`, `readonly` is lifted exactly when `lower s .arg m` has it. And (`liftOpt_best_iff`) for every attribute set `A`, every trace of `denOpt s 0 m` satisfies `A` at argument position iff `A ≤ liftOpt s m`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `liftOpt` with `None` at address `0` is read as rustc's null-niche recursion (`compiler/rustc_middle/src/ty/layout.rs` lines 1132-1141 at 26bfbf28: recurse into the untagged variant when `niche_start == 0`); the reading is argued from the source, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger:

- `ht (liftOpt_sound_of_noneVal_zero) : denOpt s 0 m t` — the trace is a trace of the option whose None is the null value; tight: counterexample `cex_liftOpt_noneVal`, in the class the two-byte shape s2, m = refFull, the None trace tAt 1 of the niche-1 encoding.

Non-vacuity witness: `nv_niche`: the null `None` trace `tNull` is a trace of `denOpt s1 0 refFull`. (Lean: `nv_niche`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R4-niche-sound`”.

Prior art:

- rustc `compiler/rustc_middle/src/ty/layout.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 1092-1104 (`MaybeDangling` arm: recurse into field 0, then `safe: None` with line 1095 "// Mark the pointer as raw", `size: Size::ZERO`, and line 1100 "// Preserve the alignment assertion! That is required even inside `MaybeDangling`.") and lines 1132-1141 (null-niche recursion: recurse into the untagged variant only if `niche_start == 0`, relying on `dereferenceable` being added only with a non-null proof and on null being aligned for all alignments) (source).
- LLVM LangRef at release llvmorg-23.1.6 (llvm/llvm-project commit 5b10d2d74929eae78912771222c9855af97496f4), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534 (return-value semantics, "acts like a system memory allocation function", lines 1528-1534), `nofree` lines 1574-1588 (line 1588: "This is not a valid attribute for return values."), `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640 (lines 1627-1631: implies `nonnull` in `addrspace(0)` except with `null_pointer_is_valid`; lines 1636-1640: dereferenceability "at the point of the attribute (i.e. on function entry for arguments or at the point of the call for return values)"), `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (phrased for a pointer argument: "the function does not write through this pointer argument") (documentation).
- Published package `enum-niche-layout-guarantees-and-validity-invariants` (google/zerocopy branch `reference`, commit f9bee82a6d3f8bb6698b4c9e716138018db94d4d), cards `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical` (for any layout of an option type with `None` mapped to the zero pattern (`hnone`) and both round-trip laws (`hde`, `hcan`), a pattern decodes to `None` iff it is the zero pattern) and `opt_opt_nonZero_no_decEnc_layout_in_payload_size` (for every `n`, the two-level option over the `n`-byte `NonZero` payload, modelling `Option<Option<NonZeroUN>>`, has no decode-after-encode layout in `n` bytes): source of the niche encodings; cited, not re-proved.

Design question: When may a pointer's attributes be lifted through an Option-like enum's niche?

#### `R4-niche-iff` — `liftOpt_sound_iff_noneVal_eq_zero_of_isNiche`

Kind: characterization. Tier: T2 (The documented null-niche condition stated as necessary and sufficient for genuine niches.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Niche.lean:143-145
theorem liftOpt_sound_iff_noneVal_eq_zero_of_isNiche (s : Shape) (m : Mod) (v : Nat)
    (hv : IsNiche s m v) :
    (∀ t, denOpt s v m t → gammaSet s .arg (liftOpt s m) t) ↔ v = 0 := by …
```

Plain claim: For every shape `s`, payload modality `m` and value `v` that is a niche of `m` (`IsNiche s m v`: no trace of `⟦m⟧` has address `v`): every trace of `denOpt s v m` satisfies `liftOpt s m` at argument position iff `v = 0`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the cited rustc code lifts attributes through a niche that starts at zero (`compiler/rustc_middle/src/ty/layout.rs` lines 1132-1141 at 26bfbf28); non-zero niche encodings of pointers are counterfactual for that code and serve to show why lifting needs the null niche. These statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger:

- `hv : IsNiche s m v` — the None encoding is not a valid payload address; tight: counterexample `cex_liftOpt_iff_isNiche`, in the class the one-byte shape s1, m = Mod.bot, v = 1.

Non-vacuity witness: `nv_niche_zero`: `0` is a niche of `refFull` at the one-byte shape `s1` (the case `v = 0`, in which both sides of the equivalence hold); `nv_niche`: `1` is a niche of `refFull` at the two-byte shape `s2` (the case `v = 1`, in which both sides fail). (Lean: `nv_niche_zero`, `nv_niche`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R4-niche-iff`”.

Prior art:

- rustc `compiler/rustc_middle/src/ty/layout.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 1092-1104 (`MaybeDangling` arm: recurse into field 0, then `safe: None` with line 1095 "// Mark the pointer as raw", `size: Size::ZERO`, and line 1100 "// Preserve the alignment assertion! That is required even inside `MaybeDangling`.") and lines 1132-1141 (null-niche recursion: recurse into the untagged variant only if `niche_start == 0`, relying on `dereferenceable` being added only with a non-null proof and on null being aligned for all alignments) (source).
- Published package `enum-niche-layout-guarantees-and-validity-invariants` (google/zerocopy branch `reference`, commit f9bee82a6d3f8bb6698b4c9e716138018db94d4d), cards `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical` (for any layout of an option type with `None` mapped to the zero pattern (`hnone`) and both round-trip laws (`hde`, `hcan`), a pattern decodes to `None` iff it is the zero pattern) and `opt_opt_nonZero_no_decEnc_layout_in_payload_size` (for every `n`, the two-level option over the `n`-byte `NonZero` payload, modelling `Option<Option<NonZeroUN>>`, has no decode-after-encode layout in `n` bytes): source of the niche encodings; cited, not re-proved.

Design question: When may a pointer's attributes be lifted through an Option-like enum's niche?

#### `R4-niche-cex` — `liftOpt_unsound_at_niche_one`

Kind: counterexample. Tier: T1 (Concrete witnesses.) Depth: definitional. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/Niche.lean:181-185
theorem liftOpt_unsound_at_niche_one :
    IsNiche s2 refFull 1 ∧
    (liftOpt s2 refFull).dereferenceableOrNull = true ∧ (liftOpt s2 refFull).align = true ∧
    denOpt s2 1 refFull (tAt 1) ∧
    ¬ attrSat s2 .arg .dereferenceableOrNull (tAt 1) ∧ ¬ attrSat s2 .arg .align (tAt 1) := by …
```
```lean
-- lean/Toy/Modality/Niche.lean:199-201
theorem lift_nonnull_dereferenceable_unsound_at_null (s : Shape) (m : Mod) :
    denOpt s 0 m tNull ∧ ¬ attrSat s .arg .nonnull tNull ∧
    ¬ attrSat s .arg .dereferenceable tNull := by …
```

Plain claim: For the two-byte, two-aligned shape `s2` and payload modality `refFull`, `1` is a niche of `refFull`, and with `None` encoded at `1` (a counterfactual encoding), `liftOpt s2 refFull` contains `dereferenceable_or_null` and `align` and the `None` trace `tAt 1` violates both; and (`lift_nonnull_dereferenceable_unsound_at_null`) for every shape `s` and payload modality `m`, the null `None` trace `tNull` is a trace of `denOpt s 0 m` and violates `nonnull` and `dereferenceable`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the niche-1 encoding is a toy counterfactual, not a description of rustc's layout of `Option<Option<&u16>>`; these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: Each theorem exhibits its trace. (Lean: `liftOpt_unsound_at_niche_one`).

Positive control: `liftOpt_sound_of_noneVal_zero`.

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R4-niche-cex`”.

Prior art:

- rustc `compiler/rustc_middle/src/ty/layout.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 1092-1104 (`MaybeDangling` arm: recurse into field 0, then `safe: None` with line 1095 "// Mark the pointer as raw", `size: Size::ZERO`, and line 1100 "// Preserve the alignment assertion! That is required even inside `MaybeDangling`.") and lines 1132-1141 (null-niche recursion: recurse into the untagged variant only if `niche_start == 0`, relying on `dereferenceable` being added only with a non-null proof and on null being aligned for all alignments) (source).
- Published package `enum-niche-layout-guarantees-and-validity-invariants` (google/zerocopy branch `reference`, commit f9bee82a6d3f8bb6698b4c9e716138018db94d4d), cards `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical` (for any layout of an option type with `None` mapped to the zero pattern (`hnone`) and both round-trip laws (`hde`, `hcan`), a pattern decodes to `None` iff it is the zero pattern) and `opt_opt_nonZero_no_decEnc_layout_in_payload_size` (for every `n`, the two-level option over the `n`-byte `NonZero` payload, modelling `Option<Option<NonZeroUN>>`, has no decode-after-encode layout in `n` bytes): source of the niche encodings; cited, not re-proved.

Design question: When may a pointer's attributes be lifted through an Option-like enum's niche?

#### `R5-sroa-iff` — `scalarize_refines_iff_declared_le_posMod`

Kind: characterization. Tier: T2 (The SROA precondition for relaxing wrappers stated as necessary and sufficient over all programs of the toy program model.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/SROA.lean:197-200
theorem scalarize_refines_iff_declared_le_posMod (τ : Ty) (qs : List Path) :
    Refines τ (scalarize τ qs) ↔
    ∀ q ∈ qs, ∀ σ, fieldTy τ q = some σ → ∀ p' s m, modAt σ p' = some (s, m) →
      m ≤ posTrans τ q m := by …
```

Plain claim: For every type `τ` (whose pointer leaves `Ty.ptr s m` have positive-size shapes: every `Shape` has `size_pos : 0 < size`) and list of field paths `qs`: replacing a local of type `τ` by one local per field path in `qs`, each with the field's declared type (`scalarize τ qs`; paths that are not fields are skipped), is a refinement for all programs (`Refines`: every assertion pattern `P.asserts` and every assignment `P.exec` of call traces to asserted leaves) iff for every `q ∈ qs` with declared field type `σ` and every pointer leaf `p'` of `σ` whose modality computed inside `σ` is `m` (`modAt σ p' = some (s, m)`), `m ≤ posTrans τ q m`.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `scalarize` is read as MIR scalar replacement of aggregates into field-typed locals (`compiler/rustc_mir_transform/src/sroa.rs` at 26bfbf28, lines 67-84); the toy has no operational semantics (a program is an assertion pattern plus an assignment of traces), so the reading is an analogy argued from the source, and these statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `nv_sroa`: for `(&mut T, u8)` both sides hold. (Lean: `nv_sroa`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R5-sroa-iff`”.

Prior art:

- rustc `compiler/rustc_mir_transform/src/sroa.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 67-84 (excluded types: unions, enums, SIMD, `DynMetadata`) and at cd2a75d9d58d7bd7b59cde543684fc83c3e785d2 (the merge commit of rust-lang/rust pull 164568) lines 62-85 (additionally excludes locals whose type satisfies `ty.is_like_maybe_dangling()`, lines 66-69; line 66 reads "// Types like MaybeDangling relax validity requirements of inner references.") (source).
- https://github.com/rust-lang/rust/issues/164176 (closed; labels `I-miscompile`, `A-mir-opt`): "ScalarReplacementOfAggregates doesn't handle ManuallyDrop/MaybeDangling"; reports a program using `ManuallyDrop<&mut u8>` that runs under Miri without UB with the MIR inlining pass enabled and is reported as UB when the ScalarReplacementOfAggregates pass is enabled as well. Fixed by https://github.com/rust-lang/rust/pull/164568 (merged 2026-10-20, merge commit cd2a75d9d58d7bd7b59cde543684fc83c3e785d2): "Exclude MaybeDangling like types from SROA"; "References inside a MaybeDangling doesn't have to satisfy any memory-depended validity properties. SROA cannot rewrite operations in terms of an inner type, which might require it."
- RFC 3336 (`MaybeDangling`, merged), rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07 `text/3336-maybe-dangling.md` lines 94-102 (references and boxes in `P` need not be dereferenceable or follow aliasing guarantees; they still have to be non-null and aligned, and `MaybeDangling<&!>` is still invalid; `ManuallyDrop<T>` wraps `T` in a `MaybeDangling`), lines 139-148 (aliasing and liveness rules apply when values are passed in a (nested) field of a compound type, "but not behind pointer indirections and also not for values inside a `MaybeDangling<_>`"), lines 172-173 (below `MaybeDangling` no memory-related attributes; `aligned` still emitted). The `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 is open (documentation).
- rustc `library/core/src/mem/maybe_dangling.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 6-10 (a reference wrapped in `MaybeDangling`, including in a (nested) field, does not have to follow pointer aliasing rules or be dereferenceable) and `library/core/src/mem/manually_drop.rs` lines 156-160 (`ManuallyDrop` wraps `MaybeDangling<T>`) (documentation, source).
- Novelty search (web search for mechanized lowerings of Rust pointer guarantees to LLVM parameter attributes, best-abstraction lowerings, and SROA preconditions for relaxing wrappers) found no mechanized statement of this form; tier kept below T3.
- Refinement checking of LLVM IR transformations (not re-modelled; cited as prior art for refinement-based correctness of optimizations): Lopes, Lee, Hur, Liu, Regehr, "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, doi:10.1145/3453483.3454030.

Design question: Exactly when may SROA scalarize an aggregate into field-typed locals without re-attaching promises a wrapper relaxed?

#### `R5-sroa-headline` — `sroa_hoist_out_of_manuallyDrop_counterexample`

Kind: counterexample. Tier: T1 (A toy rendering of a documented miscompilation pattern.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/SROA.lean:247-257
theorem sroa_hoist_out_of_manuallyDrop_counterexample (s : Shape) :
    scalarize (tyMDPair s) qsMDPair =
      [([.inner, .fst], mutRefTy s .scalar), ([.inner, .snd], .scalar)] ∧
    modAt (tyMDPair s) [.inner, .fst] = some (s, tRelax mutFull) ∧
    modAt (mutRefTy s .scalar) [] = some (s, mutFull) ∧
    SrcSafe (tyMDPair s) (progDangling s) ∧
    ¬ TgtSafe (scalarize (tyMDPair s) qsMDPair) (progDangling s) ∧
    ¬ Refines (tyMDPair s) (scalarize (tyMDPair s) qsMDPair) ∧
    (lower s .arg mutFull).dereferenceable = true ∧ (lower s .arg mutFull).noalias = true ∧
    (lower s .arg (tRelax mutFull)).dereferenceable = false ∧
    (lower s .arg (tRelax mutFull)).noalias = false := by …
```

Plain claim: For every shape `s`, scalarizing `ManuallyDrop<(&mut T, u8)>` (`tyMDPair s`) into its fields `&mut T` and `u8` (`qsMDPair`) with their declared types turns the program `progDangling s`, whose wrapped reference legally dangles, from defined into undefined: the position modality of the reference is `tRelax mutFull` while its declared modality is `mutFull`, whose argument lowering contains `dereferenceable` and `noalias` that the position modality's lowering lacks.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): the toy program has the shape described in https://github.com/rust-lang/rust/issues/164176 (scalar replacement of a `ManuallyDrop<&mut u8>`), but the toy uses a dangling trace where the reported reproducer invalidates the wrapped reference by a write through another pointer; these statements neither establish nor refute any claim about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: The theorem exhibits the program. (Lean: `sroa_hoist_out_of_manuallyDrop_counterexample`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R5-sroa-headline`”.

Prior art:

- https://github.com/rust-lang/rust/issues/164176 (closed; labels `I-miscompile`, `A-mir-opt`): "ScalarReplacementOfAggregates doesn't handle ManuallyDrop/MaybeDangling"; reports a program using `ManuallyDrop<&mut u8>` that runs under Miri without UB with the MIR inlining pass enabled and is reported as UB when the ScalarReplacementOfAggregates pass is enabled as well. Fixed by https://github.com/rust-lang/rust/pull/164568 (merged 2026-10-20, merge commit cd2a75d9d58d7bd7b59cde543684fc83c3e785d2): "Exclude MaybeDangling like types from SROA"; "References inside a MaybeDangling doesn't have to satisfy any memory-depended validity properties. SROA cannot rewrite operations in terms of an inner type, which might require it."
- rustc `compiler/rustc_mir_transform/src/sroa.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 67-84 (excluded types: unions, enums, SIMD, `DynMetadata`) and at cd2a75d9d58d7bd7b59cde543684fc83c3e785d2 (the merge commit of rust-lang/rust pull 164568) lines 62-85 (additionally excludes locals whose type satisfies `ty.is_like_maybe_dangling()`, lines 66-69; line 66 reads "// Types like MaybeDangling relax validity requirements of inner references.") (source).

Design question: Exactly when may SROA scalarize an aggregate into field-typed locals without re-attaching promises a wrapper relaxed?

#### `R6-repairs` — `repairs_sound`

Kind: theorem. Tier: T1 (The stop-at-relaxer policy mirrors the merged rustc change; the exclusion and retyping policies are toy alternatives, compared by proved acceptance inclusions.) Depth: shallow. Evidence role: execution (Lean kernel check).

Statement (verbatim):

```lean
-- lean/Toy/Modality/SROA.lean:452-454
theorem repairs_sound :
    PolicySound repairExclude ∧ PolicySound repairRetype ∧ PolicySound repairStopAtRelaxer ∧
    ¬ PolicySound naivePolicy := by …
```
```lean
-- lean/Toy/Modality/SROA.lean:489-491
theorem repairs_exact_and_retype_total :
    PolicyExact repairExclude ∧ PolicyExact repairRetype ∧ PolicyExact repairStopAtRelaxer ∧
    ∀ τ qs, (repairRetype τ qs).isSome = true := by …
```
```lean
-- lean/Toy/Modality/SROA.lean:549-557
theorem repair_policies_acceptance_hierarchy :
    (∀ τ qs locals, repairExclude τ qs = some locals → repairStopAtRelaxer τ qs = some locals) ∧
    (∀ τ qs locals, repairStopAtRelaxer τ qs = some locals → repairRetype τ qs = some locals) ∧
    repairExclude (tyPairMD s1) [[.fst], [.snd]] = none ∧
    (repairStopAtRelaxer (tyPairMD s1) [[.fst], [.snd]]).isSome = true ∧
    repairStopAtRelaxer (tyMDPair s1) qsMDPair = none ∧
    (repairRetype (tyMDPair s1) qsMDPair).isSome = true ∧
    repairStopAtRelaxer tyMDScalar [[.inner]] = none ∧
    Refines tyMDScalar (scalarize tyMDScalar [[.inner]]) := by …
```

Plain claim: For types whose pointer leaves have positive-size shapes (every `Shape` has `size_pos : 0 < size`), the exclusion policy `repairExclude`, the retyping policy `repairRetype` and the stop-at-relaxer policy `repairStopAtRelaxer` are each sound (`PolicySound`: every scalarization they return is a refinement for all programs), and `naivePolicy` is not; (`repairs_exact_and_retype_total`) all three are exact (`PolicyExact`: whenever the policy scalarizes a type `τ` with path list `qs` (`pol τ qs = some locals`), one new local per requested field path of `τ`, in order, and every pointer leaf of a new local has exactly the modality the same leaf has in `τ`), and `repairRetype` returns a scalarization for every type and path list; (`repair_policies_acceptance_hierarchy`) whenever `repairExclude` scalarizes, `repairStopAtRelaxer` returns the same locals, and whenever `repairStopAtRelaxer` scalarizes, `repairRetype` returns the same locals, both inclusions strict (`tyPairMD s1`; `tyMDPair s1` with `qsMDPair`), and `repairStopAtRelaxer` refuses `tyMDScalar` (`ManuallyDrop<u8>`) with paths `[[.inner]]` although that scalarization is a refinement.

Basis: execution (Lean kernel check) for every Lean statement quoted in this card.

Basis: derived (modeling bridge): `repairStopAtRelaxer` is read as the exclusion added by the merge commit cd2a75d9d58d7bd7b59cde543684fc83c3e785d2 of rust-lang/rust pull 164568 (`compiler/rustc_mir_transform/src/sroa.rs` lines 62-85 there: locals whose type satisfies `ty.is_like_maybe_dangling()` are excluded); `repairExclude` and `repairRetype` correspond to no cited rustc code. These statements neither establish nor refute the corresponding claims about rustc.

Hypothesis ledger: none (the statement has no hypotheses).

Non-vacuity witness: `nv_repairs`: all three policies scalarize `(&mut T, u8)`, and `repairRetype` scalarizes the headline type. (Lean: `nv_repairs`).

Non-claims: listed under Boundaries, in the subsection “Non-claims: `R6-repairs`”.

Prior art:

- rustc `compiler/rustc_mir_transform/src/sroa.rs` at 26bfbf28f5f79dff333ce5a232f131b496ec9cfe lines 67-84 (excluded types: unions, enums, SIMD, `DynMetadata`) and at cd2a75d9d58d7bd7b59cde543684fc83c3e785d2 (the merge commit of rust-lang/rust pull 164568) lines 62-85 (additionally excludes locals whose type satisfies `ty.is_like_maybe_dangling()`, lines 66-69; line 66 reads "// Types like MaybeDangling relax validity requirements of inner references.") (source).
- https://github.com/rust-lang/rust/issues/164176 (closed; labels `I-miscompile`, `A-mir-opt`): "ScalarReplacementOfAggregates doesn't handle ManuallyDrop/MaybeDangling"; reports a program using `ManuallyDrop<&mut u8>` that runs under Miri without UB with the MIR inlining pass enabled and is reported as UB when the ScalarReplacementOfAggregates pass is enabled as well. Fixed by https://github.com/rust-lang/rust/pull/164568 (merged 2026-10-20, merge commit cd2a75d9d58d7bd7b59cde543684fc83c3e785d2): "Exclude MaybeDangling like types from SROA"; "References inside a MaybeDangling doesn't have to satisfy any memory-depended validity properties. SROA cannot rewrite operations in terms of an inner type, which might require it."

Design question: Exactly when may SROA scalarize an aggregate into field-typed locals without re-attaching promises a wrapper relaxed?

### Kernel dependency audit for `Shape.size_pos`

Whether the proof of each main theorem depends, transitively through package constants, on the field `Shape.size_pos` (positive pointee size). Produced by the script `support/size_pos_audit.lean` (`lake env lean ../support/size_pos_audit.lean` from `lean/`).

| Theorem | uses `Shape.size_pos` |
| :--- | :--- |
| `mod_bounded_lattice` | no |
| `cl_closure_operator_and_closed_sublattice` | no |
| `den_antitone` | no |
| `den_sup_iff` | no |
| `den_cl_iff` | no |
| `den_subset_iff_le_cl` | yes |
| `den_subset_iff_le_of_closed` | yes |
| `kindBase_best` | yes |
| `tRelax_best` | yes |
| `transformers_respect_den` | yes |
| `transformer_dropped_atoms_can_fail` | yes |
| `compSound_iff_transformerSound_and_deep` | yes |
| `compSound_on_docTy_not_imply_transformerSound` | yes |
| `shallow_relaxer_leaves_nested_promises` | yes |
| `comp_tRelax_deep_eq_req` | no |
| `lower_sound` | no |
| `lower_best_iff` | yes |
| `lower_unique` | yes |
| `alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den` | yes |
| `polarity_galois` | no |
| `lower_no_left_adjoint_and_arg_no_right_adjoint` | no |
| `stronger_arg_lowerings_counterexamples` | yes |
| `refFull_arg_lowering_not_sound_at_return` | yes |
| `entry_deref_of_tCell_refFull_not_sound_at_return` | yes |
| `tRelax_arg_lowering_eq_ret_lowering` | no |
| `liftOpt_sound_of_noneVal_zero` | no |
| `liftOpt_best_iff` | yes |
| `liftOpt_sound_iff_noneVal_eq_zero_of_isNiche` | no |
| `liftOpt_unsound_at_niche_one` | no |
| `lift_nonnull_dereferenceable_unsound_at_null` | no |
| `scalarize_refines_iff_declared_le_posMod` | yes |
| `sroa_hoist_out_of_manuallyDrop_counterexample` | no |
| `repairs_sound` | yes |
| `repairs_exact_and_retype_total` | no |
| `repair_policies_acceptance_hierarchy` | yes |

### Auxiliary definitions and lemmas cited by name (verbatim)

```lean
-- lean/Toy/Modality/Basic.lean:278
theorem den_bot (s : Shape) (t : Trace) : den s Mod.bot t := …
```

```lean
-- lean/Toy/Modality/Examples.lean:18
theorem ex_shape : s1.size = 1 ∧ s1.align = 1 ∧ s2.align = 2 ∧ ¬ ∃ s : Shape, s.size = 0 := …
```

```lean
-- lean/Toy/Modality/Examples.lean:22
theorem ex_mod_le : refFull ≤ Mod.top ∧ ¬ Mod.top ≤ refFull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:27-29
theorem ex_mod_inf_sup :
    Mod.inf refFull mutFull = ⟨true, true, true, true, false, false, true⟩ ∧
    Mod.sup refFull mutFull = Mod.top ∧ Mod.inf refFull mutFull ≠ refFull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:52-54
theorem ex_argInRange :
    ArgInRange s1 (tArgWrite s1) ∧ ¬ ArgInRange s1 ⟨1, [], [.write .arg 5], []⟩ ∧
    ArgInRange s1 ⟨1, [], [], [.write .arg 5]⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:61-63
theorem ex_dereferenceable :
    Dereferenceable s1 (tStar s1) ∧ ¬ Dereferenceable s1 (tDangling s1) ∧
    ¬ Dereferenceable s1 ⟨0, [⟨0, 0, 4⟩], [], []⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:69
theorem ex_notFreedDuring : NotFreedDuring (tStar s1) ∧ ¬ NotFreedDuring (tFreed s1) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:74-79
theorem ex_atomSat :
    (∀ a, atomSat s2 a (tStar s2)) ∧
    ¬ atomSat s2 .aligned (tMis s2) ∧ ¬ atomSat s2 .nonnull tNull ∧
    ¬ atomSat s2 .derefEntry (tDangling s2) ∧ ¬ atomSat s2 .derefWhole (tFreed s2) ∧
    ¬ atomSat s2 .frozen (tArgWrite s2) ∧ ¬ atomSat s2 .unique (tForeignRead s2) ∧
    ¬ atomSat s2 .bounded (tOutOfRange s2) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:87-89
theorem ex_den :
    den s1 Mod.top (tStar s1) ∧ den s1 Mod.bot (tOutOfRange s1) ∧
    ¬ den s1 refFull (tFreed s1) ∧ ¬ den s1 refFull (tOutOfRange s1) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:34-36
theorem ex_closed :
    Closed s1 refFull ∧ ¬ Closed s1 ⟨false, false, true, false, false, false, false⟩ ∧
    Closed s2 Mod.bot ∧ ¬ Closed s1 Mod.bot := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:40-44
theorem ex_cl :
    cl s2 ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, true, false, false, false⟩ ∧
    cl s2 ⟨false, false, false, true, false, false, false⟩ ≠
      ⟨false, false, false, true, false, false, false⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:98-108
theorem ex_transformers :
    tRelax refFull = ⟨true, true, false, false, false, false, false⟩ ∧
    tCell refFull = ⟨true, true, true, false, false, false, true⟩ ∧
    tPin mutFull = ⟨true, true, true, false, false, false, true⟩ ∧
    tBox mutFull = ⟨true, true, true, false, false, true, true⟩ ∧
    tRelax ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, false, false, false, false, false⟩ ∧
    tBox ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, false, false, false, false⟩ ∧
    tRelax refFull ≠ refFull ∧ tCell refFull ≠ refFull ∧ tPin mutFull ≠ mutFull ∧
    tBox mutFull ≠ mutFull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:112-116
theorem ex_clDeref :
    clDeref ⟨false, false, false, true, false, false, false⟩ =
      ⟨false, true, true, true, false, false, false⟩ ∧
    clDeref ⟨true, false, false, false, false, false, false⟩ =
      ⟨true, false, false, false, false, false, false⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:120-125
theorem ex_kindBase :
    kindBase (.shared true) = refFull ∧ kindBase (.mutRef true) = mutFull ∧
    kindBase (.box true) = ⟨true, true, true, false, false, true, true⟩ ∧
    kindBase .raw = Mod.bot ∧
    kindBase (.shared false) ≠ kindBase (.shared true) ∧
    kindBase (.box false) ≠ kindBase (.box true) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:140-143
theorem ex_kindRule :
    kindRule s1 (.shared true) (tStar s1) ∧ ¬ kindRule s1 (.shared true) (tArgWrite s1) ∧
    ¬ kindRule s1 (.shared true) (tOutOfRange s1) ∧
    kindRule s1 (.shared false) (tArgWrite s1) ∧ kindRule s1 .raw (tOutOfRange s1) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:152
theorem ex_relaxRule : relaxRule s1 refFull (tDangling s1) ∧ ¬ relaxRule s1 refFull tNull := …
```

```lean
-- lean/Toy/Modality/Examples.lean:159-161
theorem ex_wrap_relaxes :
    Wrap.maybeDangling.relaxes = true ∧ Wrap.manuallyDrop.relaxes = true ∧
    Wrap.unsafeCell.relaxes = false := …
```

```lean
-- lean/Toy/Modality/Examples.lean:166-170
theorem ex_freeze_unpin :
    (Ty.pair .scalar .scalar).freeze = true ∧ (Ty.pair .scalar .scalar).unpin = true ∧
    (Ty.wrap .unsafeCell .scalar).freeze = false ∧
    (Ty.wrap .unsafePinned .scalar).unpin = false ∧
    (Ty.wrap .unsafeCell .scalar).unpin = true := …
```

```lean
-- lean/Toy/Modality/Examples.lean:176-182
theorem ex_pointer_constructors :
    refTy s1 (.wrap .unsafeCell .scalar) = .ptr s1 (tCell refFull) ∧
    mutRefTy s1 (.wrap .unsafePinned .scalar) = .ptr s1 (tPin mutFull) ∧
    boxTy s1 (.wrap .unsafePinned .scalar) = .ptr s1 (tBox (tPin mutFull)) ∧
    boxTy s1 .scalar = .ptr s1 (tBox mutFull) ∧
    rawTy s1 = .ptr s1 Mod.bot ∧
    modAt (.wrap .unsafeCell (refTy s1 .scalar)) [.inner] = some (s1, refFull) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:188-192
theorem ex_leafAt_relaxedOn :
    leafAt (tyNestedMD s1) pathNestedMD = some (s1, mutFull) ∧
    relaxedOn (tyNestedMD s1) pathNestedMD = true ∧
    leafAt (tyNestedMD s1) [.inner] = none ∧
    relaxedOn (.pair (refTy s1 .scalar) .scalar) [.fst] = false := …
```

```lean
-- lean/Toy/Modality/Examples.lean:196-203
theorem ex_comp_req :
    comp tRelax true (.wrap .maybeDangling (refTy s1 .scalar)) [.inner] =
      some (s1, tRelax refFull) ∧
    comp tRelax false (.wrap .maybeDangling (refTy s1 .scalar)) [.inner] =
      some (s1, tRelax refFull) ∧
    comp tRelax true (tyNestedMD s1) pathNestedMD ≠
      comp tRelax false (tyNestedMD s1) pathNestedMD ∧
    req (tyNestedMD s1) pathNestedMD = some (s1, tRelax mutFull) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:211
theorem ex_transformerSound : TransformerSound tRelax ∧ ¬ TransformerSound id := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:231
theorem ex_compSound : CompSound tRelax true ∧ ¬ CompSound tRelax false := …
```

```lean
-- lean/Toy/Modality/Examples.lean:247-248
theorem ex_docTy :
    DocTy (refTy s1 .scalar) ∧ DocTy (tyNestedMD s1) ∧ ¬ DocTy (.ptr s1 modFrozenOnly) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:264-271
theorem ex_attrSat :
    (∀ a, attrSat s1 .arg a (tStar s1)) ∧ attrSat s1 .ret .noalias (tStar s1) ∧
    ¬ attrSat s1 .arg .nonnull tNull ∧ ¬ attrSat s1 .arg .dereferenceable (tDangling s1) ∧
    ¬ attrSat s1 .arg .dereferenceableOrNull (tDangling s1) ∧
    ¬ attrSat s1 .arg .noalias (tConflict s1) ∧ ¬ attrSat s1 .arg .nofree (tFreed s1) ∧
    ¬ attrSat s1 .arg .readonly (tArgWrite s1) ∧ ¬ attrSat s2 .arg .align (tMis s2) ∧
    attrSat s1 .arg .dereferenceable (tFreed s1) ∧ ¬ attrSat s1 .ret .dereferenceable (tFreed s1) ∧
    ¬ attrSat s1 .ret .nofree (tStar s1) ∧ ¬ attrSat s1 .ret .readonly (tStar s1) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:285-287
theorem ex_gammaSet :
    gammaSet s1 .arg (lower s1 .arg refFull) (tStar s1) ∧
    ¬ gammaSet s1 .arg (lower s1 .arg refFull) (tFreed s1) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:298-308
theorem ex_lower :
    lower s2 .arg refFull = ⟨true, true, true, true, true, true, true⟩ ∧
    lower s2 .arg (tCell refFull) = ⟨true, true, true, true, false, false, false⟩ ∧
    lower s2 .arg mutFull = ⟨true, true, true, true, true, true, false⟩ ∧
    lower s2 .arg (tBox mutFull) = ⟨true, true, true, true, true, false, false⟩ ∧
    lower s2 .arg (tRelax refFull) = ⟨true, true, false, false, false, false, false⟩ ∧
    lower s2 .arg Mod.bot = ⟨false, false, false, false, false, false, false⟩ ∧
    lower s2 .arg refFullNoBounded = ⟨true, true, true, true, false, true, false⟩ ∧
    lower s2 .ret refFull = ⟨true, true, true, true, false, false, false⟩ ∧
    lower s2 .ret (tCell refFull) = ⟨true, true, false, false, false, false, false⟩ ∧
    lower s1 .arg Mod.bot ≠ lower s2 .arg Mod.bot := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:316-322
theorem ex_galois_defs :
    (⟨lower s1 .arg refFull⟩ : AttrDual) ≤ ⟨lower s1 .arg Mod.bot⟩ ∧
    ¬ (⟨lower s1 .arg Mod.bot⟩ : AttrDual) ≤ ⟨lower s1 .arg refFull⟩ ∧
    gammaDual s1 .arg ⟨lower s1 .arg refFull⟩ (tStar s1) ∧
    ¬ gammaDual s1 .arg ⟨lower s1 .arg refFull⟩ (tFreed s1) ∧
    denP s1 refFull (tStar s1) ∧ ¬ denP s1 refFull (tFreed s1) ∧
    (alphaSet s1 .arg (denP s1 refFull)).val = lower s1 .arg refFull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:333
theorem ex_noArgEvents : NoArgEvents tNull ∧ ¬ NoArgEvents (tArgWrite s1) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:340-342
theorem ex_isNiche :
    IsNiche s2 refFull 1 ∧ IsNiche s2 (tRelax refFull) 1 ∧ ¬ IsNiche s1 Mod.bot 1 ∧
    ¬ IsNiche s2 (tRelax refFull) 2 := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:353-355
theorem ex_denOpt :
    denOpt s1 0 refFull tNull ∧ denOpt s1 0 refFull (tStar s1) ∧
    ¬ denOpt s1 0 refFull ⟨0, [], [.read .arg 0], []⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:365-368
theorem ex_liftOpt :
    liftOpt s2 refFull = ⟨true, false, false, true, true, true, true⟩ ∧
    liftOpt s2 refFull ≠ lower s2 .arg refFull ∧
    liftOpt s2 Mod.bot = ⟨false, false, false, false, false, false, false⟩ := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:375-379
theorem ex_fieldTy_posTrans :
    fieldTy (tyMDPair s1) [.inner, .fst] = some (mutRefTy s1 .scalar) ∧
    posTrans (tyMDPair s1) [.inner, .fst] mutFull = tRelax mutFull ∧
    fieldTy (tyMDPair s1) [.fst] = none ∧
    posTrans (.pair (mutRefTy s1 .scalar) .scalar) [.fst] mutFull = mutFull := …
```

```lean
-- lean/Toy/Modality/Examples.lean:387-389
theorem ex_refines :
    Refines (tyPlainPair s1) (scalarize (tyPlainPair s1) [[.fst], [.snd]]) ∧
    ¬ Refines (tyMDPair s1) (scalarize (tyMDPair s1) qsMDPair) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:396-400
theorem ex_safe :
    SrcSafe (tyMDPair s1) ⟨fun _ => false, fun _ => tNull⟩ ∧
    TgtSafe (scalarize (tyMDPair s1) qsMDPair) ⟨fun _ => false, fun _ => tNull⟩ ∧
    SrcSafe (tyMDPair s1) (progDangling s1) ∧
    ¬ TgtSafe (scalarize (tyMDPair s1) qsMDPair) (progDangling s1) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:406-410
theorem ex_repair_helpers :
    containsRelaxer (tyMDPair s1) = true ∧ containsRelaxer (tyPlainPair s1) = false ∧
    relaxAll (mutRefTy s1 .scalar) = .ptr s1 (tRelax mutFull) ∧
    retype (tyMDPair s1) [.inner, .fst] (mutRefTy s1 .scalar) = .ptr s1 (tRelax mutFull) ∧
    retype (tyPlainPair s1) [.fst] (mutRefTy s1 .scalar) = mutRefTy s1 .scalar := …
```

```lean
-- lean/Toy/Modality/Examples.lean:416-418
theorem ex_policy :
    PolicySound repairRetype ∧ PolicyExact repairRetype ∧ ¬ PolicySound naivePolicy ∧
    PolicySound (fun _ _ => some []) ∧ ¬ PolicyExact (fun _ _ => some []) := …
```

```lean
-- lean/Toy/Modality/Types.lean:258
def s1 : Shape := ⟨1, 0, by decide⟩
```

```lean
-- lean/Toy/Modality/Examples.lean:511-512
theorem cex_den_antitone_le :
    ¬ Mod.top ≤ Mod.bot ∧ den s1 Mod.bot tNull ∧ ¬ den s1 Mod.top tNull := …
```

```lean
-- lean/Toy/Modality/Examples.lean:518-519
theorem cex_den_antitone_ht :
    refFull ≤ Mod.top ∧ ¬ den s1 Mod.top tNull ∧ ¬ den s1 refFull tNull := …
```

```lean
-- lean/Toy/Modality/Examples.lean:425
theorem nv_den_antitone : refFull ≤ Mod.top ∧ den s1 Mod.top (tStar s1) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:434-437
theorem nv_den_cl :
    ¬ Closed s1 modDerefWholeOnly ∧
    den s1 modDerefWholeOnly (tStar s1) ∧ den s1 (cl s1 modDerefWholeOnly) (tStar s1) ∧
    ¬ den s1 modDerefWholeOnly tNull ∧ ¬ den s1 (cl s1 modDerefWholeOnly) tNull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:524-529
theorem cex_den_subset_closed :
    ¬ Closed s1 ⟨false, false, true, false, false, false, false⟩ ∧
    ¬ ((∀ t, den s1 ⟨false, false, true, false, false, false, false⟩ t →
          den s1 ⟨false, true, false, false, false, false, false⟩ t) ↔
        (⟨false, true, false, false, false, false, false⟩ : Mod) ≤
          ⟨false, false, true, false, false, false, false⟩) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:443-445
theorem nv_den_subset :
    Closed s1 refFull ∧ (∀ t, den s1 refFull t → den s1 (tRelax refFull) t) ∧
    tRelax refFull ≤ refFull := …
```

```lean
-- lean/Toy/Modality/Examples.lean:538-540
theorem cex_transformers_respect_h :
    ¬ (∀ t, den s1 Mod.bot t ↔ den s1 refFull t) ∧
    ¬ (∀ t, den s1 (tRelax Mod.bot) t ↔ den s1 (tRelax refFull) t) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:450-453
theorem nv_transformers_best :
    (∀ k, ∀ t, kindRule s1 k t → den s1 (kindBase k) t) ∧
    (∀ m, ∀ t, relaxRule s1 m t → den s1 (tRelax m) t) ∧
    (∀ k, kindRule s1 k (tStar s1)) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:460-462
theorem nv_transformers_respect :
    modDerefWholeOnly ≠ cl s2 modDerefWholeOnly ∧
    (∀ t, den s2 modDerefWholeOnly t ↔ den s2 (cl s2 modDerefWholeOnly) t) := …
```

```lean
-- lean/Toy/Modality/Types.lean:261
def s2 : Shape := ⟨2, 1, by decide⟩
```

```lean
-- lean/Toy/Modality/Transformers.lean:128-129
theorem kindRule_iff_den (s : Shape) (k : PtrKind) (t : Trace) :
    kindRule s k t ↔ den s (kindBase k) t := by …
```

```lean
-- lean/Toy/Modality/Transformers.lean:140-141
theorem relaxRule_iff_den (s : Shape) (m : Mod) (t : Trace) :
    relaxRule s m t ↔ den s (tRelax m) t := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:131-134
theorem kindBase_three_kinds_coincide :
    kindBase (.shared false) = ⟨true, true, true, false, false, false, true⟩ ∧
    kindBase (.mutRef false) = kindBase (.shared false) ∧
    kindBase (.box false) = kindBase (.shared false) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:284-285
theorem transformerSound_iff_le_tRelax (T : Mod → Mod) :
    TransformerSound T ↔ ∀ m, T m ≤ tRelax m := by …
```

```lean
-- lean/Toy/Modality/Types.lean:427
def tRelaxExceptFrozenOnly (m : Mod) : Mod := if m == modFrozenOnly then Mod.top else tRelax m
```

```lean
-- lean/Toy/Modality/Examples.lean:582-583
theorem cex_comp_transformer :
    ¬ TransformerSound id ∧ ¬ CompSound id true := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:590
theorem cex_comp_deep : TransformerSound tRelax ∧ ¬ CompSound tRelax false := …
```

```lean
-- lean/Toy/Modality/Examples.lean:467
theorem nv_compSound : CompSound tRelax true ∧ TransformerSound tRelax ∧ true = true := …
```

```lean
-- lean/Toy/Modality/Examples.lean:238-240
theorem compSound_const_bot :
    TransformerSound (fun _ => Mod.bot) ∧ CompSound (fun _ => Mod.bot) true ∧
    (fun _ => Mod.bot) refFull ≠ tRelax refFull := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:218-219
theorem transformerSound_tRelax_comp_cl_s2 :
    (∀ m, tRelax (cl s2 m) = tRelax m) ∧ TransformerSound (fun m => tRelax (cl s2 m)) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:269
def pathNestedMD : Path := [.inner, .fst, .inner]
```

```lean
-- lean/Toy/Modality/Types.lean:279
theorem tRelax_tRelax (m : Mod) : tRelax (tRelax m) = tRelax m := …
```

```lean
-- lean/Toy/Modality/Examples.lean:549-550
theorem cex_lower_sound_ht :
    ¬ den s1 refFull (tFreed s1) ∧ ¬ gammaSet s1 .arg (lower s1 .arg refFull) (tFreed s1) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:473-476
theorem nv_lower :
    den s1 refFull (tStar s1) ∧
    (∀ t, den s1 refFull t → gammaSet s1 .arg (lower s1 .arg refFull) t) ∧
    (∀ B : AttrSet, (∀ t, den s1 refFull t → gammaSet s1 .arg B t) → B ≤ lower s1 .arg refFull) := …
```

```lean
-- lean/Toy/Modality/Examples.lean:556-561
theorem cex_lower_unique_sound :
    ¬ (∀ t, den s1 (tCell refFull) t →
        gammaSet s1 .arg ⟨true, true, true, true, true, true, true⟩ t) ∧
    (∀ B : AttrSet, (∀ t, den s1 (tCell refFull) t → gammaSet s1 .arg B t) →
      B ≤ ⟨true, true, true, true, true, true, true⟩) ∧
    (⟨true, true, true, true, true, true, true⟩ : AttrSet) ≠ lower s1 .arg (tCell refFull) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:568-573
theorem cex_lower_unique_best :
    (∀ t, den s1 refFull t →
      gammaSet s1 .arg ⟨false, false, false, false, false, false, false⟩ t) ∧
    ¬ (∀ B : AttrSet, (∀ t, den s1 refFull t → gammaSet s1 .arg B t) →
      B ≤ ⟨false, false, false, false, false, false, false⟩) ∧
    (⟨false, false, false, false, false, false, false⟩ : AttrSet) ≠ lower s1 .arg refFull := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:392-393
theorem attrDual_le_refl_trans :
    (∀ A : AttrDual, A ≤ A) ∧ (∀ A B C : AttrDual, A ≤ B → B ≤ C → A ≤ C) := …
```

```lean
-- lean/Toy/Modality/Lowering.lean:655
def refFullNoBounded : Mod := ⟨true, true, true, true, true, false, false⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:658
def mutFullNoBounded : Mod := ⟨true, true, true, true, false, true, false⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:777-778
theorem tRelax_arg_lowering_eq_ret_lowering (s : Shape) (m : Mod) :
    lower s .arg (tRelax m) = lower s .ret (tRelax m) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:604-606
theorem cex_liftOpt_noneVal :
    ¬ denOpt s2 0 refFull (tAt 1) ∧ denOpt s2 1 refFull (tAt 1) ∧
    ¬ gammaSet s2 .arg (liftOpt s2 refFull) (tAt 1) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:481
theorem nv_niche : denOpt s1 0 refFull tNull ∧ IsNiche s2 refFull 1 := …
```

```lean
-- lean/Toy/Modality/Niche.lean:50-51
theorem arg_nofree_of_addr_zero (s : Shape) (t : Trace) (h0 : t.addr = 0) :
    attrSat s .arg .nofree t := by …
```

```lean
-- lean/Toy/Modality/Basic.lean:290
theorem zero_mod_align (s : Shape) : 0 % s.align = 0 := …
```

```lean
-- lean/Toy/Modality/Examples.lean:595-597
theorem cex_liftOpt_iff_isNiche :
    ¬ IsNiche s1 Mod.bot 1 ∧
    ¬ ((∀ t, denOpt s1 1 Mod.bot t → gammaSet s1 .arg (liftOpt s1 Mod.bot) t) ↔ (1 : Nat) = 0) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:491-494
theorem nv_sroa :
    Refines (tyPlainPair s1) (scalarize (tyPlainPair s1) [[.fst], [.snd]]) ∧
    (∀ q ∈ ([[.fst], [.snd]] : List Path), ∀ σ, fieldTy (tyPlainPair s1) q = some σ →
      ∀ p' s m, modAt σ p' = some (s, m) → m ≤ posTrans (tyPlainPair s1) q m) := …
```

```lean
-- lean/Toy/Modality/SROA.lean:81-82
theorem modAt_append (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ) :
    modAt τ (q ++ p') = (modAt σ p').map (fun x => (x.1, posTrans τ q x.2)) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:232
def qsMDPair : List Path := [[.inner, .fst], [.inner, .snd]]
```

```lean
-- lean/Toy/Modality/SROA.lean:538
def tyMDScalar : Ty := .wrap .manuallyDrop .scalar
```

```lean
-- lean/Toy/Modality/Examples.lean:500-504
theorem nv_repairs :
    (repairExclude (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairStopAtRelaxer (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairRetype (tyPlainPair s1) [[.fst], [.snd]]).isSome = true ∧
    (repairRetype (tyMDPair s1) qsMDPair).isSome = true := …
```

```lean
-- lean/Toy/Modality/SROA.lean:523-525
theorem policySound_degenerate :
    PolicySound (fun _ _ => none) ∧ PolicySound (fun _ _ => some []) ∧
    ¬ PolicyExact (fun _ _ => some []) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:409
theorem policySound_of_exact (pol : Policy) (h : PolicyExact pol) : PolicySound pol := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:376-377
theorem modAt_retype (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ) :
    modAt (retype τ q σ) p' = modAt τ (q ++ p') := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:348-349
theorem modAt_relaxAll (σ : Ty) (p : Path) :
    modAt (relaxAll σ) p = (modAt σ p).map (fun x => (x.1, tRelax x.2)) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:569-571
def retRightAdjoint (A : AttrSet) : Mod :=
  ⟨A.align, A.nonnull, A.nonnull, A.nonnull && A.dereferenceable && A.dereferenceableOrNull,
   true, true, true⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:177-178
theorem dereferenceableAtReturn_iff_atomSat_derefWhole (s : Shape) (t : Trace) :
    DereferenceableAtReturn s t ↔ atomSat s .derefWhole t := …
```

```lean
-- lean/Toy/Modality/Lowering.lean:184-186
theorem lower_dereferenceable_eq (s : Shape) (m : Mod) :
    (lower s .arg m).dereferenceable = (cl s m).derefEntry ∧
    (lower s .ret m).dereferenceable = (cl s m).derefWhole := …
```

```lean
-- lean/Toy/Modality/Lowering.lean:791-799
theorem kindBase_ret_lowering_dereferenceable_by_kind (s : Shape) :
    (∀ k ∈ [PtrKind.shared false, PtrKind.mutRef false, PtrKind.box true, PtrKind.box false],
      (lower s .arg (kindBase k)).dereferenceable = true ∧
      (lower s .arg (kindBase k)).dereferenceableOrNull = true ∧
      (lower s .ret (kindBase k)).dereferenceable = false ∧
      (lower s .ret (kindBase k)).dereferenceableOrNull = false) ∧
    (∀ k ∈ [PtrKind.shared true, PtrKind.mutRef true],
      (lower s .ret (kindBase k)).dereferenceable = true ∧
      (lower s .ret (kindBase k)).dereferenceableOrNull = true) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:547-549
theorem lower_arg_no_right_adjoint_on_closed (s : Shape) :
    ¬ ∃ u : AttrSet → {m : Mod // Closed s m},
      ∀ (m : {m : Mod // Closed s m}) (A : AttrSet), lower s .arg m.1 ≤ A ↔ m.1 ≤ (u A).1 := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:576-578
theorem lower_ret_right_adjoint_of_alignLog_ne_zero (s : Shape) (hs : s.alignLog ≠ 0) :
    (∀ A, Closed s (retRightAdjoint A)) ∧
    (∀ (m : Mod) (A : AttrSet), lower s .ret m ≤ A ↔ m ≤ retRightAdjoint A) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:631-634
theorem lower_ret_no_right_adjoint_of_alignLog_eq_zero (s : Shape) (hs : s.alignLog = 0) :
    (¬ ∃ u : AttrSet → Mod, ∀ (m : Mod) (A : AttrSet), lower s .ret m ≤ A ↔ m ≤ u A) ∧
    (¬ ∃ u : AttrSet → {m : Mod // Closed s m},
      ∀ (m : {m : Mod // Closed s m}) (A : AttrSet), lower s .ret m.1 ≤ A ↔ m.1 ≤ (u A).1) := by …
```

```lean
-- lean/Toy/Modality/Niche.lean:61-63
theorem aligned_and_misaligned_of_nonzero_niche (s : Shape) (m : Mod) (v : Nat)
    (hv : IsNiche s m v) (hv0 : v ≠ 0) :
    m.aligned = true ∧ s.alignLog ≠ 0 ∧ ¬ (v % s.align = 0) := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:487
theorem nv_niche_zero : IsNiche s1 refFull 0 ∧ IsNiche s2 refFull 0 := …
```

```lean
-- lean/Toy/Modality/SROA.lean:420-424
theorem policyExact_refusing_and_scalar_reshaping :
    PolicyExact (fun _ _ => none) ∧
    PolicyExact (fun τ qs =>
      some (qs.filterMap fun q => (fieldTy τ q).map fun σ =>
        (q, match σ with | .scalar => .pair .scalar .scalar | _ => retype τ q σ))) := by …
```

```lean
-- lean/Toy/Modality/Lattice.lean:410-411
theorem cl_eq_of_den_iff (s : Shape) {m₁ m₂ : Mod} (h : ∀ t, den s m₁ t ↔ den s m₂ t) :
    cl s m₁ = cl s m₂ := by …
```

#### Further declarations recorded in `results.json` (verbatim)

Helper lemmas and definitions that `results.json` lists in `lean_names` (so that their statement and closure hashes are recorded) and that the Evidence tables name; quoted here so that every package declaration this report names is quoted with its source location.

```lean
-- lean/Toy/Modality/Lowering.lean:87
theorem AttrSet.ext_has {A B : AttrSet} (h : ∀ a, A.has a = B.has a) : A = B := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:75-82
def AttrSet.insert (A : AttrSet) : Attr → AttrSet
  | .align => { A with align := true }
  | .nonnull => { A with nonnull := true }
  | .dereferenceable => { A with dereferenceable := true }
  | .dereferenceableOrNull => { A with dereferenceableOrNull := true }
  | .noalias => { A with noalias := true }
  | .nofree => { A with nofree := true }
  | .readonly => { A with readonly := true }
```

```lean
-- lean/Toy/Modality/Types.lean:394-395
theorem DocTy.leaf_kindBase {τ : Ty} (h : DocTy τ) :
    ∀ p s m, leafAt τ p = some (s, m) → ∃ k, m = kindBase k := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:426-427
theorem alphaOf_has (P : Attr → Trace → Prop) (X : Imported.Pred Trace) (a : Attr) :
    (alphaOf P X).val.has a = decide (∀ t, X t → P a t) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:431-432
theorem alphaSet_has (s : Shape) (pos : Pos) (X : Imported.Pred Trace) (a : Attr) :
    (alphaSet s pos X).val.has a = decide (∀ t, X t → attrSat s pos a t) := …
```

```lean
-- lean/Toy/Modality/Lowering.lean:477
def attrsNoalias : AttrSet := ⟨false, false, false, false, true, false, false⟩
```

```lean
-- lean/Toy/Modality/Transformers.lean:156-158
theorem cl_transformer_cl (s : Shape) (m : Mod) :
    cl s (tRelax (cl s m)) = cl s (tRelax m) ∧ cl s (tCell (cl s m)) = cl s (tCell m) ∧
    cl s (tPin (cl s m)) = cl s (tPin m) ∧ cl s (tBox (cl s m)) = cl s (tBox m) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:210-214
theorem comp_deep_inv (T : Mod → Mod) (hT : TransformerSound T) (τ : Ty) (p : Path)
    (s : Shape) (c b : Mod) (hc : comp T true τ p = some (s, c))
    (hb : leafAt τ p = some (s, b)) :
    (relaxedOn τ p = false → c = b) ∧
    (relaxedOn τ p = true → ∀ t, den s (tRelax b) t → den s c t) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:180-181
theorem comp_eq_some_leaf (T : Mod → Mod) (deep : Bool) (τ : Ty) (p : Path) (s : Shape)
    (c : Mod) (h : comp T deep τ p = some (s, c)) : ∃ b, leafAt τ p = some (s, b) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:344-346
theorem comp_tRelax_deep_eq_leaf (τ : Ty) (p : Path) :
    comp tRelax true τ p = (leafAt τ p).map
      (fun x => (x.1, if relaxedOn τ p then tRelax x.2 else x.2)) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:200
theorem den_tReadAfter (s : Shape) (m : Mod) : den s m (tReadAfter s) := by …
```

```lean
-- lean/Toy/Modality/Types.lean:271
theorem den_tRelax_tDangling (s : Shape) (m : Mod) : den s (tRelax m) (tDangling s) := …
```

```lean
-- lean/Toy/Modality/Types.lean:275
theorem den_tRelax_tForeignRead (s : Shape) (m : Mod) : den s (tRelax m) (tForeignRead s) := …
```

```lean
-- lean/Toy/Modality/Transformers.lean:300-301
theorem den_transformer_of_den (s : Shape) (m : Mod) (t : Trace) (h : den s m t) :
    den s (tRelax m) t ∧ den s (tCell m) t ∧ den s (tPin m) t ∧ den s (tBox m) t := by …
```

```lean
-- lean/Toy/Modality/Lattice.lean:218-219
theorem exists_den_not_atomSat_of_not_has_cl (s : Shape) (m : Mod) (a : Atom)
    (h : (cl s m).has a = false) : ∃ t, den s m t ∧ ¬ atomSat s a t := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:254-255
theorem exists_den_not_attrSat_of_not_has_lower (s : Shape) (pos : Pos) (m : Mod) (a : Attr)
    (h : (lower s pos m).has a = false) : ∃ t, den s m t ∧ ¬ attrSat s pos a t := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:389-391
theorem filterMap_fieldTy_map_fst (τ : Ty) (qs : List Path) (f : Path → Ty → Ty) :
    (qs.filterMap fun q => (fieldTy τ q).map fun σ => (q, f q σ)).map Prod.fst =
      qs.filter (fun q => (fieldTy τ q).isSome) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:166-168
theorem le_tRelax_iff (m : Mod) :
    m ≤ tRelax m ↔ ¬ (m.derefEntry = true ∨ m.derefWhole = true ∨ m.frozen = true ∨
      m.unique = true ∨ m.bounded = true) := by …
```

```lean
-- lean/Toy/Modality/Niche.lean:210-212
theorem liftOpt_sound_at_non_niche_one :
    ¬ IsNiche s1 Mod.bot 1 ∧
    (∀ t, denOpt s1 1 Mod.bot t → gammaSet s1 .arg (liftOpt s1 Mod.bot) t) ∧ (1 : Nat) ≠ 0 := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:180-181
theorem mem_scalarize (τ : Ty) (qs : List Path) (q : Path) (σ : Ty) :
    (q, σ) ∈ scalarize τ qs ↔ q ∈ qs ∧ fieldTy τ q = some σ := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:384-385
theorem modAt_eq_of_not_relaxedOn (τ : Ty) (q p' : Path) (σ : Ty) (h : fieldTy τ q = some σ)
    (hr : relaxedOn τ q = false) : modAt σ p' = modAt τ (q ++ p') := by …
```

```lean
-- lean/Toy/Modality/Examples.lean:429
def modDerefWholeOnly : Mod := ⟨false, false, false, true, false, false, false⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:480
def modFrozenBounded : Mod := ⟨false, false, false, false, true, false, true⟩
```

```lean
-- lean/Toy/Modality/Types.lean:423
def modFrozenOnly : Mod := ⟨false, false, false, false, true, false, false⟩
```

```lean
-- lean/Toy/Modality/Lowering.lean:483
def modUniqueBounded : Mod := ⟨false, false, false, false, false, true, true⟩
```

```lean
-- lean/Toy/Modality/Basic.lean:285-286
theorem ne_zero_of_dereferenceable {s : Shape} {t : Trace} (h : Dereferenceable s t) :
    t.addr ≠ 0 := by …
```

```lean
-- lean/Toy/Modality/Niche.lean:45
theorem noArgEvents_tAt (v : Nat) : NoArgEvents (tAt v) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:224
theorem not_noalias_tConflict (s : Shape) : ¬ attrSat s .arg .noalias (tConflict s) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:229
theorem not_noalias_tOutOfRange (s : Shape) : ¬ attrSat s .arg .noalias (tOutOfRange s) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:237
theorem not_nofree_tFreed (s : Shape) : ¬ attrSat s .arg .nofree (tFreed s) := by …
```

```lean
-- lean/Toy/Modality/Lowering.lean:234
theorem not_readonly_tOutOfRange (s : Shape) : ¬ attrSat s .arg .readonly (tOutOfRange s) := …
```

```lean
-- lean/Toy/Modality/Lowering.lean:205
theorem not_ret_noalias_tReadAfter (s : Shape) : ¬ attrSat s .ret .noalias (tReadAfter s) := …
```

```lean
-- lean/Toy/Modality/SROA.lean:116-117
theorem posTrans_eq (τ : Ty) (q : Path) (m : Mod) :
    posTrans τ q m = if relaxedOn τ q then tRelax m else m := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:236-237
def progDangling (s : Shape) : Prog :=
  ⟨fun r => decide (r = [.inner, .fst]), fun _ => tDangling s⟩
```

```lean
-- lean/Toy/Modality/SROA.lean:401-402
theorem refines_scalarize_of_not_relaxedOn (τ : Ty) (qs : List Path)
    (h : ∀ q ∈ qs, relaxedOn τ q = false) : Refines τ (scalarize τ qs) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:332-333
theorem relaxedOn_eq_false_of_containsRelaxer (τ : Ty) (q : Path)
    (h : containsRelaxer τ = false) : relaxedOn τ q = false := by …
```

```lean
-- lean/Toy/Modality/Types.lean:153-155
theorem reqAux_eq (r : Bool) (τ : Ty) (p : Path) :
    reqAux r τ p = (leafAt τ p).map
      (fun x => (x.1, if r || relaxedOn τ p then tRelax x.2 else x.2)) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:397-398
theorem scalarize_map_fst (τ : Ty) (qs : List Path) :
    (scalarize τ qs).map Prod.fst = qs.filter (fun q => (fieldTy τ q).isSome) := …
```

```lean
-- lean/Toy/Modality/SROA.lean:441-443
theorem stopAtRelaxer_not_relaxedOn {τ : Ty} {qs : List Path}
    (hall : qs.all (fun q => (fieldTy τ q).isNone || !relaxedOn τ q) = true)
    {q : Path} (hq : q ∈ qs) {σ : Ty} (hσ : fieldTy τ q = some σ) : relaxedOn τ q = false := by …
```

```lean
-- lean/Toy/Modality/Transformers.lean:279-283
theorem transformers_deflationary_closed (s : Shape) :
    (∀ m, tRelax m ≤ cl s m ∧ tCell m ≤ cl s m ∧ tPin m ≤ cl s m ∧ tBox m ≤ cl s m) ∧
    (∀ m, Closed s m → Closed s (tRelax m) ∧ Closed s (tCell m) ∧ Closed s (tPin m) ∧
      Closed s (tBox m)) ∧
    (∀ m, tRelax (tRelax m) = tRelax m) := by …
```

```lean
-- lean/Toy/Modality/SROA.lean:229
def tyMDPair (s : Shape) : Ty := .wrap .manuallyDrop (.pair (mutRefTy s .scalar) .scalar)
```

```lean
-- lean/Toy/Modality/Types.lean:265-266
def tyNestedMD (s : Shape) : Ty :=
  .wrap .maybeDangling (.pair (.wrap .transparent (mutRefTy s .scalar)) .scalar)
```

```lean
-- lean/Toy/Modality/SROA.lean:535
def tyPairMD (s : Shape) : Ty := .pair (.wrap .manuallyDrop (mutRefTy s .scalar)) .scalar
```

```lean
-- lean/Toy/Modality/Examples.lean:382
def tyPlainPair (s : Shape) : Ty := .pair (mutRefTy s .scalar) .scalar
```

## Boundaries

### Non-claims

Each card's non-claims are listed below, verbatim from the `non_claims` field of its entry in `results.json`. Two non-claims apply to every card:

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM.
- Every `Mod` is a call-entry modality. No statement of the package represents the validity invariant of a value at the return point, and no statement says which attributes rustc attaches, or LLVM accepts, at return position.

#### Non-claims: `R1-lattice`

- `Mod` has 128 elements (seven Booleans); no cardinality theorem is stated.
- Says nothing about traces; the semantic content is in `den_antitone`, `den_cl_iff` and `den_subset_iff_le_cl`.
- When `s.alignLog = 0` (alignment 1), `Mod.bot` is not `s`-closed (`ex_closed`: `¬ Closed s1 Mod.bot`), so the `s`-closed modalities form a sublattice whose least element is `cl s Mod.bot`, not a sublattice containing `Mod.bot`.
- Closure of the `s`-closed modalities under `Mod.sup` uses that every rule of `cl s` has a single premise; for closure rules with several premises, closed sets need not be closed under unions (not proved here).
- The closure rules are the toy's (`derefWhole` ⇒ `derefEntry` ⇒ `nonnull`; `aligned` at alignment 1); `frozen`, `unique` and `bounded` take part in no rule; other implications a real memory model may have are not modelled.
- Kernel dependency audit for `Shape.size_pos`: the proofs of `mod_bounded_lattice` and `cl_closure_operator_and_closed_sublattice` do not use it.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R1-antitone`

- A labelled reference point: both statements are one-step consequences of the definition of `den` and are subsumed by `den_subset_iff_le_cl`; they inform no design question on their own.
- No well-formedness condition is built into `den`; in particular bounded provenance is the atom `bounded`, imposed exactly when the modality contains it.
- The proofs of `den_antitone` and `den_sup_iff` do not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R1-closure`

- The proof does not use `Shape.size_pos` (kernel dependency audit). The implication `derefEntry ⇒ nonnull` holds also for zero-length coverage, because `Alloc.covers` already excludes address `0`.
- Address `0` is never inside an allocation (`Alloc.contains` and `Alloc.covers` require a positive base); this is what makes `derefEntry` imply `nonnull`. Non-zero LLVM address spaces and the `null_pointer_is_valid` function attribute, under which `dereferenceable` does not imply `nonnull` (LangRef lines 1627-1631), are not modelled.
- Addresses, sizes and lengths are unbounded natural numbers: `t.addr + s.size` never wraps, and address-space size and `isize::MAX` bounds are not modelled.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R1-embedding`

- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- Deallocation is not a write: `frozen` constrains writes and not frees, so `frozen` and `derefWhole` are independent atoms; models in which a free counts as a write are not examined.
- The witness traces are single-call traces of this toy; nothing is claimed about which of them a real program can produce.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R1-transformers-best`

- `kindRule` and `relaxRule` transcribe the documented rules in terms of the atom meanings (`kindRule_iff_den`, `relaxRule_iff_den`), so both soundness and optimality of `kindBase` and `tRelax` follow from `den_subset_iff_le_cl`; they are not validated against an independent operational semantics. `kindBase_best` and `tRelax_best` follow by unfolding these transcriptions (definitional), while `transformers_respect_den` uses `cl_eq_of_den_iff` and `den_subset_iff_le_cl` (shallow); the card's depth is therefore `shallow`.
- Three pointer kinds get the same base modality `{aligned, nonnull, derefEntry, bounded}` (`kindBase_three_kinds_coincide`): shared references to non-`Freeze` pointees, mutable references to non-`Unpin` pointees and boxes of non-`Unpin` pointees. The transformers `tCell`, `tPin`, `tBox` are applied in `kindBase` to `refFull` and `mutFull`.
- `bounded` (bounded provenance, `ArgInRange`) is an explicit atom: `den s m` imposes it exactly when `m` contains it. The safe pointer kinds of `kindRule` carry it and `Mod.bot` (raw pointers) and `tRelax` do not; this assignment is a modelling choice of the toy, and which Rust aliasing model guarantees bounded provenance for references is not examined.
- `Mod.bot` and `kindRule s .raw` impose no condition: a raw pointer may be used outside its pointee bytes.
- The toy `box` kind stands for a box with the global allocator; custom allocators (rustc's `global = false`), the `box_noalias` option, unoptimized builds (rustc computes `frozen` and `unpin` as false under `OptLevel::No`), and uninhabited pointees (`MaybeDangling<&!>`, still invalid per RFC 3336) are not modelled.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R1-dropped-atoms`

- A witness corollary of `kindBase_best` and `tRelax_best`, which already give a failing trace for every atom outside the closure; this theorem names the traces.
- Atoms that a modality never had are not "dropped": `refFull` has no `unique` (shared references permit concurrent reads), so `tCell` removing `unique` from it changes nothing.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R2-comp-iff`

- `Ty.ptr s m` is a leaf whose pointee type is erased: `comp` and `req` model by-value nesting (pairs and wrappers) and say nothing about pointers reached behind a pointer indirection (for example the inner reference of `MaybeDangling<&&mut T>`).
- `deep` compares two propagation modes, the wrapper's immediate pointer content (`deep = false`) and every by-value pointer leaf below it (`deep = true`); depth-bounded or wrapper-selective strategies are not examined.
- Soundness is not precision: `fun _ => Mod.bot` is a sound transformer and its deep computation is sound (`compSound_const_bot`).
- `TransformerSound` is a semantic condition: the relaxer `fun m => tRelax (cl s2 m)`, which closes for `s2` before relaxing, equals `tRelax` and is sound (`transformerSound_tRelax_comp_cl_s2`).
- Once `TransformerSound T` is reduced to `∀ m, T m ≤ tRelax m`, the ← direction is a structural induction over types; the depth label is `shallow`.
- No enums or unions are part of the type language.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R2-shallow-cex`

- The witness used by the `deep = true` direction of `compSound_iff_transformerSound_and_deep`, stated separately to name the type and traces.
- The nesting is by value (a field of a pair inside the wrapper); pointers behind a pointer indirection are not modelled.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R2-documented-exact`

- Relies on `tRelax` being idempotent (`tRelax_tRelax`): `comp tRelax true` applies `tRelax` once per enclosing relaxing wrapper, while `req`, whose definition fixes the weakening to `tRelax`, applies it once when at least one relaxing wrapper encloses the leaf. `req` is not parameterized by a transformer; for a non-idempotent transformer `T`, `comp T true` would differ from a requirement that applies `T` once at nested relaxing wrappers (not proved here).
- Nesting is by value; pointers behind a pointer indirection are not modelled.
- The proof does not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R3-lower-sound`

- The attribute meanings are the toy's LangRef-style readings in which every violation is undefined behaviour (LLVM's `align` and `nonnull` yield poison unless combined with `noundef`).
- `frozen` and `unique` constrain the pointee bytes, while argument `noalias` and `readonly` constrain every address accessed through the argument; `lower` requires `bounded` for them, and without `bounded` they are unsound (`stronger_arg_lowerings_counterexamples`, `tOutOfRange s`).
- `dereferenceable` is evaluated at the point of the attribute: call entry for an argument (`Dereferenceable`) and the return point for a return value (`DereferenceableAtReturn`: covered at call entry and no containing allocation freed during the call, which is definitionally the atom `derefWhole` by `dereferenceableAtReturn_iff_atomSat_derefWhole`; hence `lower s .ret m` contains `dereferenceable` exactly when `cl s m` contains `derefWhole`, `lower_dereferenceable_eq`). Allocations created during the call are not represented, so a freshly allocated return value is not expressible.
- Program points: every `Mod` is a call-entry modality of a pointer that exists at call entry (promises at call entry and over the call; see `Atom`). `lower s .ret m` is the set of return-value attributes, evaluated at the return point by `attrSat s .ret`, to which a pointer carrying the call-entry modality `m` is entitled when it is returned (for example an argument returned unchanged). It is not a lowering of the validity invariant that a returned value has at the return point, which the toy does not represent (the Rust Reference requires a reference or `Box<T>` to be non-dangling whenever it is produced, including when it is returned; see Prior art). In particular, the absence of `dereferenceable` from `lower s .ret (kindBase k)` for `k` among `.shared false`, `.mutRef false`, `.box true`, `.box false` (`kindBase_ret_lowering_dereferenceable_by_kind`) records that call-entry dereferenceability of such a pointer does not survive a free during the call (`entry_deref_of_tCell_refFull_not_sound_at_return`); it does not say that a value returned at type `&UnsafeCell<T>`, `&mut T` with `T: !Unpin`, or `Box<T>` may fail to be dereferenceable at the return point.
- The toy's `lower s .ret` is not a model of the attributes rustc attaches to return values. At rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe, `arg_attrs_for_rust_scalar` records `pointee_size` for return values as for arguments (`compiler/rustc_ty_utils/src/abi.rs` lines 346-352, no `is_return` condition); this package does not examine which LLVM attributes rustc's LLVM backend emits from that field, at return position or elsewhere. These statements neither establish nor refute the corresponding claims about which attributes rustc attaches to return values.
- LangRef states that `nofree` is not a valid attribute for return values (line 1588) and phrases `readonly` for a pointer argument; the toy reads both as never satisfied at return position (a modelling choice, not a LangRef rule for `readonly`). Return `noalias` is the toy reading "no pointee byte is accessed through an unrelated pointer after the return" of LangRef's allocation-like return semantics; no atom constrains events after the return.
- Address `0` is never inside an allocation (`Alloc.contains` and `Alloc.covers` require a positive base); this is what makes `derefEntry` imply `nonnull`. Non-zero LLVM address spaces and the `null_pointer_is_valid` function attribute, under which `dereferenceable` does not imply `nonnull` (LangRef lines 1627-1631), are not modelled.
- The proof does not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R3-lower-best`

- 'Best' is relative to the seven modelled attributes and their toy meanings.
- `align` is included whenever the closure contains `aligned`, including alignment 1 where it is trivially true (LangRef lines 1497-1505: `align 1` has no effect on non-byval, non-preallocated arguments); `dereferenceable` and `dereferenceable_or_null` are both included when the deref condition holds although the first implies the second. Which attributes rustc emits, and under which conditions (for example `align` values, `dereferenceable(n)` versus `dereferenceable_or_null(n)`, `noundef`, `captures(...)`, `writable`), is neither modelled nor examined here.
- At return position the best lowering never contains `noalias` (no atom constrains events after the return), `nofree` or `readonly` (never satisfied there), and contains `dereferenceable` exactly when the closure of the call-entry modality contains `derefWhole` (`lower_dereferenceable_eq`); for the base modalities of the six safe pointer kinds, `lower s .ret (kindBase k)` lacks `dereferenceable` for `k` = `.shared false`, `.mutRef false`, `.box true`, `.box false` and contains it for `.shared true`, `.mutRef true` (`kindBase_ret_lowering_dereferenceable_by_kind`).
- Program points: every `Mod` is a call-entry modality of a pointer that exists at call entry (promises at call entry and over the call; see `Atom`). `lower s .ret m` is the set of return-value attributes, evaluated at the return point by `attrSat s .ret`, to which a pointer carrying the call-entry modality `m` is entitled when it is returned (for example an argument returned unchanged). It is not a lowering of the validity invariant that a returned value has at the return point, which the toy does not represent (the Rust Reference requires a reference or `Box<T>` to be non-dangling whenever it is produced, including when it is returned; see Prior art). In particular, the absence of `dereferenceable` from `lower s .ret (kindBase k)` for `k` among `.shared false`, `.mutRef false`, `.box true`, `.box false` (`kindBase_ret_lowering_dereferenceable_by_kind`) records that call-entry dereferenceability of such a pointer does not survive a free during the call (`entry_deref_of_tCell_refFull_not_sound_at_return`); it does not say that a value returned at type `&UnsafeCell<T>`, `&mut T` with `T: !Unpin`, or `Box<T>` may fail to be dereferenceable at the return point.
- The toy's `lower s .ret` is not a model of the attributes rustc attaches to return values. At rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe, `arg_attrs_for_rust_scalar` records `pointee_size` for return values as for arguments (`compiler/rustc_ty_utils/src/abi.rs` lines 346-352, no `is_return` condition); this package does not examine which LLVM attributes rustc's LLVM backend emits from that field, at return position or elsewhere. These statements neither establish nor refute the corresponding claims about which attributes rustc attaches to return values.
- `frozen` and `unique` constrain the pointee bytes, while argument `noalias` and `readonly` constrain every address accessed through the argument; `lower` requires `bounded` for them, and without `bounded` they are unsound (`stronger_arg_lowerings_counterexamples`, `tOutOfRange s`).
- Address `0` is never inside an allocation (`Alloc.contains` and `Alloc.covers` require a positive base); this is what makes `derefEntry` imply `nonnull`. Non-zero LLVM address spaces and the `null_pointer_is_valid` function attribute, under which `dereferenceable` does not imply `nonnull` (LangRef lines 1627-1631), are not modelled.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R3-galois`

- The Galois connection is between predicates on traces and attribute sets; it holds for every relation (`polarity_galois`) and carries no content specific to modalities. Between modalities and attribute sets, `lower s pos` has no left adjoint (no `u` with `A ≤ lower s pos m ↔ u A ≤ m`), over all modalities and over `s`-closed modalities, and `lower s .arg` has no right adjoint (no `u` with `lower s .arg m ≤ A ↔ m ≤ u A`) over all modalities (`lower_no_left_adjoint_and_arg_no_right_adjoint`) and over `s`-closed modalities (`lower_arg_no_right_adjoint_on_closed`). `lower s .ret` has the right adjoint `retRightAdjoint`, with `s`-closed values, when `s.alignLog ≠ 0` (`lower_ret_right_adjoint_of_alignLog_ne_zero`), and no right adjoint, over all or over `s`-closed modalities, when `s.alignLog = 0` (`lower_ret_no_right_adjoint_of_alignLog_eq_zero`). These three lemmas are auxiliary; they are not part of the card's main statement.
- The cited package's characterization of Galois connections (card `R1-gc-iff`) is stated for a reflexive and transitive abstract order; the reverse-inclusion order on `AttrDual` is reflexive and transitive (`attrDual_le_refl_trans`). Monotonicity, extensivity and reductivity are not re-proved here.
- Kernel dependency audit for `Shape.size_pos` (shapes have positive size by construction): the proof of `alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den` uses it, so zero-sized pointees are outside their scope and these statements neither establish nor refute the corresponding claims for them; the proofs of `polarity_galois`, `lower_no_left_adjoint_and_arg_no_right_adjoint` do not use it.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R3-stronger-unsound`

- Each conjunct is one instance; the general statement that every attribute outside `lower s pos m` fails on some trace of `⟦m⟧` is `lower_best_iff`.
- The `bounded` conjuncts concern the hypothetical modalities `refFullNoBounded` and `mutFullNoBounded`, which no pointer kind of `kindBase` has.
- Return position is covered by `refFull_arg_lowering_not_sound_at_return` and `entry_deref_of_tCell_refFull_not_sound_at_return`.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R3-position`

- The counterexamples concern the call-entry modalities `refFull` and `tCell refFull`; for relaxed pointers the argument and return lowerings coincide (`tRelax_arg_lowering_eq_ret_lowering`), so their argument lowering is sound at return position.
- No atom constrains events after the return, so `tReadAfter s` is in `⟦m⟧` for every `m` and no modality justifies return `noalias` in this toy; the reasons rustc gives for never emitting return-position `noalias` (abi.rs lines 371-372, linking unsafe-code-guidelines issue 385) are not modelled.
- `nofree` and `readonly` are never satisfied at return position (see `attrSat`), so the argument lowering of `refFull` also fails there on every trace; the counterexample does not rely on this.
- Program points: every `Mod` is a call-entry modality of a pointer that exists at call entry (promises at call entry and over the call; see `Atom`). `lower s .ret m` is the set of return-value attributes, evaluated at the return point by `attrSat s .ret`, to which a pointer carrying the call-entry modality `m` is entitled when it is returned (for example an argument returned unchanged). It is not a lowering of the validity invariant that a returned value has at the return point, which the toy does not represent (the Rust Reference requires a reference or `Box<T>` to be non-dangling whenever it is produced, including when it is returned; see Prior art). In particular, the absence of `dereferenceable` from `lower s .ret (kindBase k)` for `k` among `.shared false`, `.mutRef false`, `.box true`, `.box false` (`kindBase_ret_lowering_dereferenceable_by_kind`) records that call-entry dereferenceability of such a pointer does not survive a free during the call (`entry_deref_of_tCell_refFull_not_sound_at_return`); it does not say that a value returned at type `&UnsafeCell<T>`, `&mut T` with `T: !Unpin`, or `Box<T>` may fail to be dereferenceable at the return point.
- The toy's `lower s .ret` is not a model of the attributes rustc attaches to return values. At rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe, `arg_attrs_for_rust_scalar` records `pointee_size` for return values as for arguments (`compiler/rustc_ty_utils/src/abi.rs` lines 346-352, no `is_return` condition); this package does not examine which LLVM attributes rustc's LLVM backend emits from that field, at return position or elsewhere. These statements neither establish nor refute the corresponding claims about which attributes rustc attaches to return values.
- Kernel dependency audit for `Shape.size_pos` (shapes have positive size by construction): the proofs of `refFull_arg_lowering_not_sound_at_return`, `entry_deref_of_tCell_refFull_not_sound_at_return` use it, so zero-sized pointees are outside their scope and these statements neither establish nor refute the corresponding claims for them; the proof of `tRelax_arg_lowering_eq_ret_lowering` does not use it.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R4-niche-sound`

- On the `None` branch, `noalias` and `readonly` use `NoArgEvents`; `nofree` holds on every trace with address `0` (`arg_nofree_of_addr_zero`), so the free clause of `NoArgEvents` is not used.
- `NoArgEvents` constrains argument-tagged events during the call; `Trace` records no pointer provenance beyond the tags.
- Holds also when `0` is not a niche of `m` (for example `m = Mod.bot`, where address `0` is a valid payload value).
- Null is aligned for every alignment (`zero_mod_align`; alignment is `2 ^ alignLog`, never `0`).
- Address `0` is never inside an allocation (`Alloc.contains` and `Alloc.covers` require a positive base); this is what makes `derefEntry` imply `nonnull`. Non-zero LLVM address spaces and the `null_pointer_is_valid` function attribute, under which `dereferenceable` does not imply `nonnull` (LangRef lines 1627-1631), are not modelled.
- Kernel dependency audit for `Shape.size_pos` (shapes have positive size by construction): the proof of `liftOpt_best_iff` uses it, so zero-sized pointees are outside their scope and these statements neither establish nor refute the corresponding claims for them; the proof of `liftOpt_sound_of_noneVal_zero` does not use it.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R4-niche-iff`

- For a non-zero niche the failing attribute is `align` (a non-zero niche of `m` violates `aligned`, which is then in `liftOpt s m`); this includes payloads without `derefEntry`, such as `tRelax refFull` at `s2`, where `1` is a niche (`ex_isNiche`).
- Addresses are unbounded natural numbers, so the toy has no upper-bound niches (such as addresses above `isize::MAX`): every non-zero niche `v` of `m` comes from misalignment (`aligned_and_misaligned_of_nonzero_niche`: `m.aligned = true`, `s.alignLog ≠ 0` and `v % s.align ≠ 0`).
- Statements are at argument position (`gammaSet s .arg`); return position is not examined for `liftOpt`.
- Non-zero niche encodings of pointers are counterfactual for the cited rustc code (the null-niche recursion requires `niche_start == 0`); they serve to show why lifting needs the null niche.
- The proof does not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R4-niche-cex`

- In the cited rustc code the attribute-lifting recursion requires the niche to start at zero (`niche_start == 0`), and the cited package shows that a two-level option over its `NonZero` payload has no decode-after-encode layout in the payload size; the niche-1 encoding is a toy counterfactual, not a description of rustc's `Option<Option<&u16>>`.
- The proofs of `liftOpt_unsound_at_niche_one` and `lift_nonnull_dereferenceable_unsound_at_null` do not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R5-sroa-iff`

- `m` is the field-local modality computed inside `σ` (it already accounts for relaxing wrappers inside `σ`), not the bare leaf modality `leafAt σ p'`.
- A program is an assertion pattern plus an assignment of traces (`Prog`), with no operational semantics; temporal lifetime transitions (a pointer valid when stored and invalidated later), movement or duplication of retag points, and partially initialized or dead fields are not modelled. With this program model the proof is direct: the forward direction builds a one-program witness from the trace `tDangleAliased` and uses `modAt_append`, `posTrans_eq`, `le_tRelax_iff` and `mem_scalarize` together with two lemmas about that trace, and the reverse direction uses `modAt_append`, `mem_scalarize` and `den_antitone`; the depth label is `shallow`.
- The condition is checked per field and per pointer leaf; no enums or unions are part of the type language.
- Shapes have positive size by construction (`Shape.size_pos`, a field of `Shape`), and the proof uses it (kernel dependency audit); zero-sized pointees are not representable, and these statements neither establish nor refute the corresponding claims for them.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R5-sroa-headline`

- rust-lang/rust#164176 independently reports a rustc SROA miscompilation involving `ManuallyDrop<&mut u8>`, whose reproducer invalidates the wrapped reference by a write through another pointer; this toy counterexample uses a dangling trace instead, and neither establishes nor refutes any claim about rustc.
- The proof does not use `Shape.size_pos` (kernel dependency audit).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

#### Non-claims: `R6-repairs`

- `PolicySound` alone admits degenerate policies: always refusing and always returning no locals are sound, and the latter is not exact (`policySound_degenerate`); exactness is the separate predicate `PolicyExact`, which implies soundness (`policySound_of_exact`). `PolicyExact` holds vacuously for the always-refusing policy, and it constrains the modalities of pointer leaves (`modAt`), not the scalar structure of the new locals: a policy that retypes scalar fields as pairs of scalars and otherwise behaves like `repairRetype` is exact (`policyExact_refusing_and_scalar_reshaping`).
- `repairRetype` gives each new local under a relaxing wrapper the type `relaxAll σ`, whose pointer leaves have modality `tRelax m` (alignment and non-null promises kept; `modAt_retype`, `modAt_relaxAll`). If `m` keeps neither promise, so that `tRelax m = Mod.bot` (for example a raw pointer, `m = Mod.bot`), the new leaf has the raw-pointer modality `kindBase .raw`, which is `Mod.bot` by the definition of `kindBase`. If `tRelax m ≠ Mod.bot` (for example the base modality of a shared reference, a mutable reference or a box, which keeps alignment and non-null), then `tRelax m` is not the modality of any of the four documented pointer constructors (not proved here). How a compiler would express such a type is not examined.
- `repairStopAtRelaxer` is more conservative than the exact condition of `scalarize_refines_iff_declared_le_posMod`: it refuses `tyMDScalar` with paths `[[.inner]]` although that scalarization refines (`repair_policies_acceptance_hierarchy`).
- The correspondence between `repairStopAtRelaxer` and the merged rustc change (which excludes locals whose type satisfies `is_like_maybe_dangling()`) is a derived modelling bridge; the exclusion and retyping policies correspond to no cited rustc code.
- Kernel dependency audit for `Shape.size_pos` (shapes have positive size by construction): the proofs of `repairs_sound`, `repair_policies_acceptance_hierarchy` use it, so zero-sized pointees are outside their scope and these statements neither establish nor refute the corresponding claims for them; the proof of `repairs_exact_and_retype_total` does not use it.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc or LLVM. Model–system relation: none proved.

### Attractive stronger conclusions that are not established

- That rustc emits, or that it withholds, LLVM `dereferenceable(n)` or `dereferenceable_or_null(n)` on return values of any type. The package cites where rustc records `pointee_size` for return values and does not examine which LLVM attributes its backend emits from that field.
- That a value returned at type `&UnsafeCell<T>`, `&mut T` with `T: !Unpin`, or `Box<T>` may fail to be dereferenceable at the return point. The absence of `dereferenceable` from `lower s .ret (kindBase k)` for those kinds (`kindBase_ret_lowering_dereferenceable_by_kind`) is a statement about what the call-entry modality justifies, not about the returned value's validity invariant.
- That `lower` is what rustc computes, or that the toy attribute meanings `attrSat` are LLVM's semantics. Both are compared in `derived (modeling bridge)` prose.
- That rustc's scalar replacement of aggregates is correct at either cited revision, or that other MIR passes handle `MaybeDangling` correctly. `R5-sroa-iff` characterizes refinement in the toy program model, and `R6-repairs` compares toy policies.
- Any of the results for zero-sized pointees, non-zero address spaces, `null_pointer_is_valid`, wrapping address arithmetic, enums, unions, or pointers behind a pointer indirection.

### Escape hatches

Which hypotheses or settings, when dropped or changed, defeat the negative results (each item names a proved theorem quoted in this report):

- `R3-position`: for relaxed call-entry modalities the argument and return lowerings coincide (`tRelax_arg_lowering_eq_ret_lowering`), so the argument lowering of `tRelax m` is sound at return position.
- `R3-stronger-unsound`: the `noalias` and `readonly` conjuncts concern `refFullNoBounded` and `mutFullNoBounded`, which lack the atom `bounded`; with `bounded` present, `lower s .arg refFull` contains `noalias` and `readonly` (`refFull_arg_lowering_not_sound_at_return`), `lower s .arg mutFull` contains `noalias` (`sroa_hoist_out_of_manuallyDrop_counterexample`), and both lowerings are sound (`lower_sound`).
- `R3-galois`: the absence of a right adjoint is stated for `lower s .arg`; at return position, `lower s .ret` has the right adjoint `retRightAdjoint` when `s.alignLog ≠ 0` (`lower_ret_right_adjoint_of_alignLog_ne_zero`) and none when `s.alignLog = 0` (`lower_ret_no_right_adjoint_of_alignLog_eq_zero`).
- `R4-niche-cex` and `R4-niche-iff`: with `None` encoded at address `0`, lifting is sound (`liftOpt_sound_of_noneVal_zero`); without the hypothesis `IsNiche s m v` the equivalence fails (`cex_liftOpt_iff_isNiche`, at `m = Mod.bot` and `v = 1`).
- `R2-comp-iff`: restricted to types built from the four documented pointer constructors, soundness of the deep computation does not force `TransformerSound T` (`compSound_on_docTy_not_imply_transformerSound`).
- `R2-shallow-cex`: with `deep = true`, the documented computation equals the reference requirement at every path (`comp_tRelax_deep_eq_req`).
- `R5-sroa-headline`: retyping the new locals so that their pointer leaves carry the relaxed call-entry modality removes the counterexample: `repairRetype` returns a scalarization of `tyMDPair s1` with `qsMDPair` (`nv_repairs`), and every scalarization it returns is a refinement (`repairs_sound`).
- `R1-embedding`: without `Closed s m₁` the closure cannot be dropped (`cex_den_subset_closed`).

### Hypotheses whose tightness is `unknown`

None. Every hypothesis in every ledger is `tight`, with a fully proved counterexample theorem named in the ledger.

### Dropped or disproved statements

None. All 20 results are fully proved with the statements quoted in their cards; none is dropped or disproved.

### Not examined

- LLVM's implementation of the attributes (the toy reads LangRef), and the LLVM IR that rustc emits.
- MIR passes other than scalar replacement of aggregates.
- Executions with more than one call, concurrency, and events before call entry.
- Novelty: a web search for mechanized lowerings of Rust pointer guarantees to LLVM parameter attributes, best-abstraction lowerings and SROA preconditions for relaxing wrappers found no mechanized statement of this form; no result is claimed novel (no `T3` tier).

## Evidence

Basis for every theorem below: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; `lake build` of `lean/` succeeds, and no Lean source of the package contains `sorry`, `admit`, `native_decide` or an `axiom`/`opaque` declaration. The axiom audit (`Lean.collectAxioms`, recorded in `audit/axioms.json`) covers all 902 non-internal declarations of the library `Toy` (including generated equation lemmas); 0 of them depend on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. The statement hash is the SHA-256 of the Lean `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded). Both are recorded for all 281 names referenced by `results.json` in `audit/statements.json` and are recomputed by `support/revalidate.py`. The kernel check and the hash records were produced on 2026-11-21; the external sources below were read at the pinned revisions on the same date.

Where the results are proved: the main statements are in `Lattice` (`R1-lattice` to `R1-embedding`), `Transformers` (`R1-transformers-best`, `R1-dropped-atoms`), `Types` (`R2-*`), `Lowering` (`R3-*`), `Niche` (`R4-*`) and `SROA` (`R5-*`, `R6-repairs`), each quoted with its file and line range in its card; the definitions are in `Basic` and the same modules; `Imported` holds the two definitions copied from the cited Galois-connection package; `Examples` holds the positive and negative examples of the definitions, the `nv_*` non-vacuity witnesses and the `cex_*` tightness counterexamples (a counterexample card is its own non-vacuity witness). The proofs are direct: case analysis over the seven atoms and attributes, explicit witness traces, and structural induction over the toy type language.

### Main results (card `lean` fields)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Modality.mod_bounded_lattice` | `propext` | `14944556871cf3b6325eefc29f01a6046d81d2332a2abadb0cb4415f72130408` | `2e8e905fb1e4029bd1cbb414b8b34f3457ff91440af60fc9f4104b461a4c1f3f` |
| `Toy.Modality.cl_closure_operator_and_closed_sublattice` | `Quot.sound`, `propext` | `e66ea3985a340219f96702541e05ed2cc31cace25a6cefae5a57bbb523922eaf` | `375495aaa48b808ac61ca73aba03814a8e9176b89103ec407b95b82a8b923339` |
| `Toy.Modality.den_antitone` | none | `6d0f86df7b4800d7b317b6314c8bf714c1ed7163be66edc8baecf0bf9ebb479d` | `fe6be7e2a9d82112d8134698d5d83d26b4f9d20bc13174119f2fab30e388d1a6` |
| `Toy.Modality.den_sup_iff` | `propext` | `71c4b71444797d4fa8d41fecd506d7e4917086a3c4734c6cd9cf74541129cf7f` | `b707da10df4d6655619c00835e618a39515c4e367f99e011bf41fcbb205e0101` |
| `Toy.Modality.den_cl_iff` | `Quot.sound`, `propext` | `37f3d504612bcbef00612ce37eb34300b4d59eb40288a354581b6d60a5d4eba8` | `fdcd17b62c53d5e6f0dc858ca0d6874e67631a32a8f3d28303217f6501acf0b0` |
| `Toy.Modality.den_subset_iff_le_cl` | `Quot.sound`, `propext` | `cc3a8b385d221769bfcbd5e501fe19bc6438607db24f632bb6a95b8c34afe37c` | `d250d99c732c4ede39b4d8ffe24cfd8a127cff29382f38484e48c4a146542577` |
| `Toy.Modality.den_subset_iff_le_of_closed` | `Quot.sound`, `propext` | `428ef7a2045c9c7e18df6ade45a56e38b877ed925d0ae870b351c6f3fb6c503f` | `1a9e640036a13e3eb7278b7496be26fe411145e90e8bb9851571343387491be8` |
| `Toy.Modality.kindBase_best` | `Quot.sound`, `propext` | `53f2fb9582d8a98fbd4d24ad08a95c9b178fef12c229004a64b0ac25cdc4d78a` | `4bf8ec0d4ce96d75f92c550852a7c4f0893bc0a358c671d87c81ba938e53cef0` |
| `Toy.Modality.tRelax_best` | `Quot.sound`, `propext` | `f3023227ddec7ff544239e576df74cc74c433a40211cddfc90830fe89bdbeb74` | `ffe8aa3e2d1e18069975a6e6631ac18af37cc196afff3fb2103981d90d2fe786` |
| `Toy.Modality.transformers_respect_den` | `Quot.sound`, `propext` | `d0970367e7448e44a8fd07651efeaf228a9ca15e12fc1728f85dc9888fcd8454` | `854fe174d60d3ba7157f4d9ba3f00d54cd0f1ab1ed3995c722cf9b0ec5ae4814` |
| `Toy.Modality.transformer_dropped_atoms_can_fail` | `Quot.sound`, `propext` | `7a6e545f8541f180f6cf9f4f9595e9b701bdb60a3f357bcd8fb76f0d4a52a590` | `f214f4b72ba9218d23de05863a192c480c2147bba23206d85b49dc8ab112cb1c` |
| `Toy.Modality.compSound_iff_transformerSound_and_deep` | `Quot.sound`, `propext` | `e44dd70719182e156d187ef5821826326de696d28039154fa66a176457061b7a` | `42dec4e109a5700a2207aac93b3e20cfd97ce2bfd8bb439547d5c6b35e5cf3c6` |
| `Toy.Modality.compSound_on_docTy_not_imply_transformerSound` | `Quot.sound`, `propext` | `a52b86d60dd6b2f1df49a05d86814f9c0221ed3289108ecc3c7ede0a0f1bea61` | `802aba2e7f41c6626ebd6ce57bee5363349989610ad3106a203a49fcf37cac6d` |
| `Toy.Modality.shallow_relaxer_leaves_nested_promises` | `Quot.sound`, `propext` | `a1d9c87ad6acac342ed2c469f95b1c28b040b376ff07577f94cbbf7008a3c8d8` | `8e1872d0f31576077ac333384b1a3f162a83febdbc11e1d8f0ab40643ffb5ef4` |
| `Toy.Modality.comp_tRelax_deep_eq_req` | `Quot.sound`, `propext` | `1298dc60806fb48905eebf77c357c58d8d80b5c454e6dfdc6b1e74536487f323` | `bdbe64e493d0b20dbecffe076bae33f9b46269a08883fa3099a24d02ec626cba` |
| `Toy.Modality.lower_sound` | `Quot.sound`, `propext` | `3dca7b1786ddee27463d6a8062cf09d6a6feddd4848a0f1ffbcf6a5787908200` | `c74106409ad6e1377ff338a6396699c18d06662496dad1bab696a1847603d384` |
| `Toy.Modality.lower_best_iff` | `Quot.sound`, `propext` | `02729a73c4349455d224418aca35740ee71f26a2eeb0fb39f1939936675424b7` | `05225a0387187edcd05c8f71c80c654dc6f3cbd90b2bf870af0937225270b2a4` |
| `Toy.Modality.lower_unique` | `Quot.sound`, `propext` | `f26e213f37d5a3474edb16e55ee7aa7cd75e3ca662e1402ede9908323fd66a7b` | `05225a0387187edcd05c8f71c80c654dc6f3cbd90b2bf870af0937225270b2a4` |
| `Toy.Modality.alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den` | `Classical.choice`, `Quot.sound`, `propext` | `9c473328916210054875fa002d4eb2dd8b4e9726ac75ee0d10613db25df35021` | `81715769c27449059fef4c83b67e7a5db2648eb00703b394e359d60c168a2ffd` |
| `Toy.Modality.polarity_galois` | `Classical.choice`, `Quot.sound`, `propext` | `57d1648da4e68417333277e3b09e94fd9e424f4cd425f17e8b03fb2105e0b239` | `72bc82e2bbfb51f2fd82d7b0badcf928d1a2e10bb7fdaaf24f22bdb1aba3efc1` |
| `Toy.Modality.lower_no_left_adjoint_and_arg_no_right_adjoint` | `Quot.sound`, `propext` | `006c44ec28fb2bed2a283488be48681cde73633da930a130c52b29731c59d9c7` | `eacaa42485c79dac3321f8c43c9bfa3cd758932fa352be27c48a8f2b11275e7b` |
| `Toy.Modality.stronger_arg_lowerings_counterexamples` | `Quot.sound`, `propext` | `fce8d95220267cbe44469b455f2872046a8f9aeb4abdb6926525e2eba8678f3a` | `d766942d3b240ca90dcc2c42da5fa0693125c7e136edd436b87a4e50b2a391e5` |
| `Toy.Modality.refFull_arg_lowering_not_sound_at_return` | `Quot.sound`, `propext` | `f7cea0f8ea17274c96084fe954fc369b34bc0fc4b6c5ddd8754055532d4a8acc` | `a3c41583f787682d0323be84d105445c407fede89da62396a7d3b5575529397b` |
| `Toy.Modality.entry_deref_of_tCell_refFull_not_sound_at_return` | `Quot.sound`, `propext` | `e97d0cf71726393c4a5171b7c75ed7e94b116fc79fe4a96717f0226a49f242e1` | `6493c29ca54e58ef514ff017c2a8498ad30aaacf5890761ed580bdc0237cac5f` |
| `Toy.Modality.liftOpt_sound_of_noneVal_zero` | `Quot.sound`, `propext` | `d9c67098b8748f355bc23b562e30fc73cfa20a18ca8daf22a20aa2042460fb65` | `c8acb03efb6eece9cee5a7d18e1ccf22abfef81748c76ee9fbcc6b1adfd645c0` |
| `Toy.Modality.liftOpt_best_iff` | `Quot.sound`, `propext` | `2e268901c874d7969a15b60f07e0097cbd1abfa9f374b1b72b6e2cbfda841566` | `346e4b70dc603dd18d8b8928f65a93e3a0cd12edbc2963acf25837fe7a474409` |
| `Toy.Modality.liftOpt_sound_iff_noneVal_eq_zero_of_isNiche` | `Classical.choice`, `Quot.sound`, `propext` | `f3659a57923153824b822e9c69a926248748405600a33d861394861b0ede630c` | `5a10d3fa4e8865b5d8f25514d5d4802436cdbbc3f3721e01a3edb1f3c4e211e1` |
| `Toy.Modality.liftOpt_unsound_at_niche_one` | `propext` | `7d3b538f72c7d4622a417bed866a6bf86424d6fee344e99bf8ef794960751b55` | `48a279b929687dc59857580638cff9c4e564908aa1e2a043ec432447a5332c25` |
| `Toy.Modality.lift_nonnull_dereferenceable_unsound_at_null` | `propext` | `cb526ce88738b926e573f71789a8dc0a6f7f7d680fa0e1f05fbfb432992601b8` | `eb954c3b427e886dfd397ffe5d1f403ad48ac03659904de08f862fd879247304` |
| `Toy.Modality.scalarize_refines_iff_declared_le_posMod` | `Classical.choice`, `Quot.sound`, `propext` | `8928740ac92ea5c70a010feea71c7289394856a1d94f90d3d62953919597c70d` | `60579f4c868c10b795c852d5c3e3a2d04a10fd06cbdbf5af98868b034b65942b` |
| `Toy.Modality.sroa_hoist_out_of_manuallyDrop_counterexample` | `Quot.sound`, `propext` | `44cac4f0cfadc77ee36d7e23a0d938878c5172bbab1ef54f48e8eda438bb90a8` | `26e01ed8b19d5c6e5a3fb9543fbf5ad0f0f1d49f8f7673308f1c88b1bf21e18a` |
| `Toy.Modality.repairs_sound` | `Classical.choice`, `Quot.sound`, `propext` | `09d60e816635eb8d527ff743617f2efb7d427713404c8e4ff4da1e0742c15ef7` | `b9d1583bc1eaa5830e30244ed050908ec8b545e9b8106f81176c39c87bac7878` |
| `Toy.Modality.repairs_exact_and_retype_total` | `Quot.sound`, `propext` | `4dd12b7b2d0c32a669e6d6e7d6fc2664e43d490a0f4ad270c0d4a9f5e3d2025d` | `e9fe1bcfc74a1b78bffb67da240fd93f61243ba21655281c8daab1402caa654c` |
| `Toy.Modality.repair_policies_acceptance_hierarchy` | `Classical.choice`, `Quot.sound`, `propext` | `2ac9ae25a6143ceddaa0b29b64bc29dac52401cc417586fb1a9973eb07ee1c98` | `241deacc3e6e69b5dd41b5b4ebe608042548e31e0f090041b5614ff3decedc00` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Modality.ex_closed` | none | `cae6d77797cd0866fcf958c61cb29a8479d6a7e288a9fcc61dd942c8e113515d` | `01d31afdad3d56071abb8a5e470d5270b2ccf43f08c2a6103fc4f1c401c7cc6a` |
| `Toy.Modality.nv_den_antitone` | `Quot.sound`, `propext` | `e933787802619e39e846d25b5a85226e2ed09cbd98a5922ea919e287239835fb` | `b88d101a4ce1e9030a5f4b6e3d8faee81d2a089cb36925741b6e516f41b504f3` |
| `Toy.Modality.cex_den_antitone_le` | `propext` | `fb94d8d4c47cd5c8f30e6c33c601498c65de87774305fe952ef6533306e5bc82` | `9f568be1e2cbb6a9226c715d9c2d7da9c8f99e5190c0ad070f230a5f2894fae0` |
| `Toy.Modality.cex_den_antitone_ht` | none | `b7cd881975ea30dfd37e78171c4d0e584fd22cfad3ecdc8a54edd47d911cf16c` | `b39744bb94ddf8add3121eaf4e64961a35a7e7378f1567dab04e37510d76856b` |
| `Toy.Modality.nv_den_cl` | `Quot.sound`, `propext` | `b1286730a200a015c593a36ec8cb808e8459a3ca6a8f8d1a0d4cf05cb8cfecfc` | `12cde00c584c42f21aa31a5d9dd045ead22bb623c23a3d312b686681362c8ee2` |
| `Toy.Modality.nv_den_subset` | `Quot.sound`, `propext` | `b9e0324142f5f9075c7ba6a09b8acbc22cb7889a5a84258f46bf65d1456187a8` | `4607357cc77a1c3123cb79c558af7f63779e29378bde46e9faf428288e75ea97` |
| `Toy.Modality.cex_den_subset_closed` | `Quot.sound`, `propext` | `3c973c7e740404557207ac2776029ff88487e768cd344823c782bdb2cb5586f7` | `b1973b83ac0d94b6d08ef2779d4cc68b1060742a26c6f3cf6404e8e0c7f53db5` |
| `Toy.Modality.nv_transformers_best` | `Quot.sound`, `propext` | `b69490fdbd3cda62dcfeafe756fb7c9a686ffeeeebe6f0f765c412fed3d94381` | `88002e527640dca9f2e507bef20c19411a59d113408893c475feeb44a8ba7a5e` |
| `Toy.Modality.nv_transformers_respect` | `Quot.sound`, `propext` | `de652502e4e230cd958cf989beb7d81a9c0fe06943d12b450adcf0958fe1d875` | `796c5219979c9ddc266336390383b3d34e386cdbb0b86b5b4eade733d33ffbff` |
| `Toy.Modality.cex_transformers_respect_h` | `propext` | `4d768b244a1208f79073375fd72c23120fff3d0d6cb04352e51279028ec5fd30` | `11e1d207c5dbd93e01bf796d5a2ed9e13f292652237e7f1f249c561975bdbc1a` |
| `Toy.Modality.nv_compSound` | `Quot.sound`, `propext` | `0fdfef4f145b08f0a91f7e34648a78b2f7c902271473eaddc36c6780811a7b7f` | `42dec4e109a5700a2207aac93b3e20cfd97ce2bfd8bb439547d5c6b35e5cf3c6` |
| `Toy.Modality.cex_comp_transformer` | `Quot.sound`, `propext` | `62cd36a98ee2dd2f2bb85437f744075bd72a8d63ef25dd7027b664a01b51acae` | `42dec4e109a5700a2207aac93b3e20cfd97ce2bfd8bb439547d5c6b35e5cf3c6` |
| `Toy.Modality.cex_comp_deep` | `Quot.sound`, `propext` | `df0197ff4daa899a81930caf4cbaf90c67f7321c7359031e07151a7b64b13811` | `42dec4e109a5700a2207aac93b3e20cfd97ce2bfd8bb439547d5c6b35e5cf3c6` |
| `Toy.Modality.ex_comp_req` | `propext` | `66cc76ef717f0f7fdd0e285ab24059dcb49d5d2701291332f102e678f70a1555` | `064b6564b158794028385f2dc7a076d1a1f6842e22c2f446b63328b43eefcdc5` |
| `Toy.Modality.nv_lower` | `Quot.sound`, `propext` | `a74f04e7a59d0747f21302cb65b1a8a68e3d80e64bcb8873e377763c6ddbd27b` | `b320f12c7bc24d52ba63046d00ca8d670b55e3149940f0e66e6ba2796b5c4f11` |
| `Toy.Modality.cex_lower_sound_ht` | `Quot.sound`, `propext` | `52d12370d30713304813f8466233c8b3a279defe0b332243a87bc73c1539f3a5` | `a4437abefdf99c2a52192f2a1b6ab5b3d1a18271a98e2fe0f2f4e98b33802c1d` |
| `Toy.Modality.cex_lower_unique_sound` | `Quot.sound`, `propext` | `1ab10b88adc6a1251a29fb52cc6803edd9026da89729a6ad93af96d175e6fac5` | `049cbfff0a5db2f9186428846f5d95f2f5b709d5bd5b83c8d052fef37fc3bd10` |
| `Toy.Modality.cex_lower_unique_best` | `Quot.sound`, `propext` | `a79417554c4686a3ce2921705c37c66805c21e5a757ee6bf3fe1a2b150ae9460` | `2301fc820a3b1d14eac866d3bd75ae8236a303a3f555a2b9e1bbfab09f58c1ed` |
| `Toy.Modality.ex_galois_defs` | `Classical.choice`, `Quot.sound`, `propext` | `62a98e41ab23ddbfae256474ed6484cf01ab984185dd340663bb98993bc18abb` | `0f9cedc8f5491385b0744a633a764356d7368b72adabd1a33d95c0dbb2f497d0` |
| `Toy.Modality.tRelax_arg_lowering_eq_ret_lowering` | `propext` | `e9e0b56aa0a75ac8c3bce3c2652ce7c839850db133257bfce8c9dbb36f4ff48f` | `57683ad34b7ca6f99515e51c7d5b298373389191e9332fb7343abff1fcf5f458` |
| `Toy.Modality.nv_niche` | `propext` | `e996c1af5debf2a21be804d5c55b2401deb45472e84169ac2345044e73e38ad8` | `9955ce41453329b758c8640e5680f16adf1edf648ba51991e5462506ab5d6864` |
| `Toy.Modality.cex_liftOpt_noneVal` | `propext` | `b16e16db1db0b2565275ddaeba1bcdec7817cd788dcf1d749ae796caad936b7f` | `a9e12be1ec700f1ba91de9d1f6a82da8a1870522a60c62e187907554ee4bf692` |
| `Toy.Modality.nv_niche_zero` | none | `73bc379c7aa951eec4f6fa510c41f94c821b74377dc7b2e8f046f21077aa6add` | `35c5e50f60805aa37dad4de75326c19ebc771a4b64b2fe028ee80122c655e621` |
| `Toy.Modality.cex_liftOpt_iff_isNiche` | `Classical.choice`, `Quot.sound`, `propext` | `1b2e6e759f038df33657605cbc2027c4c8e4c0e75c5092f90a01d40c9bedb580` | `dfe21413108999d920cb05fc486c70618643236f14d5e78f79c19fae167bcb42` |
| `Toy.Modality.nv_sroa` | `Classical.choice`, `Quot.sound`, `propext` | `61405d3d3244d1e71eff208c9270ce73355a9d342fed57acf36b7b4b467200ba` | `095d2bd03d59ecb31ad85420b6e8e547bca3e3c6830e20d821e8c6be63e2716c` |
| `Toy.Modality.nv_repairs` | `propext` | `952d70343815e216bb09bb33f7c9953ad4c4baa222a2b02b7daea736998f9af4` | `7a2ab9cdfb9d57c0b42aed012bf8f5ae5afff3a9d9c11972ec684ee591c16f33` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.Modality.AccessedBy` | none | `bc1c2fa6685a763d394e55daadc7cd58f4d05d0c39d0d74672752ba477311977` | `5eb26a43c17707b7c70dec1b8d8325681edc5429788abb46da71d4f698cba1c9` |
| `Toy.Modality.Alloc` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Alloc.contains` | none | `a448949f39b3d154b1d742587a8c91dc61d1409b4e0c4c067d473c682d37ea1b` | `c790e216037d98aa36c6bf70c244383a604cb815db5682f9694f5f57c0b3340e` |
| `Toy.Modality.Alloc.covers` | none | `84268dbf630880f5177d94004d6158cefffb5bbcc90c6512347aaf57e418e2ea` | `c790e216037d98aa36c6bf70c244383a604cb815db5682f9694f5f57c0b3340e` |
| `Toy.Modality.ArgInRange` | none | `0e18935b9165f05f3f73297542541d24ed72dc3cd2953ecf1afcea1f45d9fe43` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.Atom` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Attr` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.AttrDual` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.AttrSet` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.AttrSet.ext_has` | none | `82b4dc3f7de3d5d6ed6f46aab1d384273d2efb4ceea07579619c60897d34656e` | `a912c7beeb930b1814f8075a055a1447c2c3b2bbd694e252345b0b847ed9842b` |
| `Toy.Modality.AttrSet.has` | none | `c1da9a075292f9ada4379650f01f1f4afaa1db5ad9ab8e0e41ee64a7ad6248d3` | `1d2a8bdec11b08cee316dfc210babb021f3a1ef50e6f1853dcf6f4eb47965a22` |
| `Toy.Modality.AttrSet.insert` | none | `9b917d9ddd6edf39c7dee0a2d1f6b00a1498ad6ddf38dc236c7e3de9df798c2c` | `1d2a8bdec11b08cee316dfc210babb021f3a1ef50e6f1853dcf6f4eb47965a22` |
| `Toy.Modality.Closed` | none | `d8f40d8477e85bc311cf520080e6c7f99f0515ee7c880cf5d84a5d032fca0f72` | `f1312f6de90dd4b8caddfc8d20953e27451a510f368880b31dc9691bb2ba7f12` |
| `Toy.Modality.CompSound` | `propext` | `b2f477f18512088f19ed269efe7cdce72e0186253b7c8e2c918aee9fec4b669f` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.Dereferenceable` | none | `0e18935b9165f05f3f73297542541d24ed72dc3cd2953ecf1afcea1f45d9fe43` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.DereferenceableAtReturn` | none | `0e18935b9165f05f3f73297542541d24ed72dc3cd2953ecf1afcea1f45d9fe43` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.DocTy` | `propext` | `788a1a0b8eecb5a208831651f4ef1726ec4effb6a4074181a543a7e9415dca9d` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.DocTy.leaf_kindBase` | `propext` | `78a62bcf25729ad6f8640e6d213fcecbe70530842cd5c5eb2ba3c10efbe3b2dd` | `dfdfa2d6fec0afe072cf4131929422d629d98146e94e1890ceb05fd606a67eb4` |
| `Toy.Modality.Event` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Imported.GaloisConnection` | none | `912f5ca196f16b3d6bd36c5ad4fae13f8b5dec51f0eb14e2aee3e52b90965376` | `ba428d8788be3880d3fc0f89c1e9cebf3f2bde152f76135a59a9c9587eaa1d30` |
| `Toy.Modality.Imported.Pred` | none | `83a3e70864bd8e0535067fe584b304ad2cdbdda672daef9db111eedd89047a8d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Imported.instLEPred` | none | `7ee1bdc3d8630897f2129926b98c5ea48a276bd2934437f6efe1304785f1de69` | `ba428d8788be3880d3fc0f89c1e9cebf3f2bde152f76135a59a9c9587eaa1d30` |
| `Toy.Modality.InRange` | none | `0ce55211684a9a4c3dbe3a5dcf1dcdc82511fb67c0329000038e24210b3ee7dc` | `4d403dc2efd11259a1187dd82ef42f494d8ef89943d45b7b1f5ebd6986be327f` |
| `Toy.Modality.IsNiche` | none | `55a62a33002d7cbc08820c43b5cf8ac6c98e8802b5526ee20cb10f1d8eefbd6b` | `f1312f6de90dd4b8caddfc8d20953e27451a510f368880b31dc9691bb2ba7f12` |
| `Toy.Modality.Mod` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Mod.bot` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.Mod.has` | none | `adac1b3d0e5983f5f4ed5cffa3b3960e2fab81a855f1748549a3f1399cd4c83e` | `63141fbda890e4665916be7f0f2935abb72027c7d6987d498dbf09b58c03ee1d` |
| `Toy.Modality.Mod.inf` | none | `081eedabd8b980bea5a6a3e768f651d2c5cb04217edd37c2a888257d669dfe10` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.Mod.sup` | none | `081eedabd8b980bea5a6a3e768f651d2c5cb04217edd37c2a888257d669dfe10` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.Mod.top` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.NoArgEvents` | none | `4f45b61a51e6081c73759efe4265c0e7577b4c38caa4d4538480a0e30ea53f3b` | `0a1e3671868851b491b886d9c52a5cfa3fa3b2a0be664e814a1f73668720d085` |
| `Toy.Modality.NotFreedDuring` | none | `4f45b61a51e6081c73759efe4265c0e7577b4c38caa4d4538480a0e30ea53f3b` | `0a1e3671868851b491b886d9c52a5cfa3fa3b2a0be664e814a1f73668720d085` |
| `Toy.Modality.Path` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Policy` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.PolicyExact` | `propext` | `32bae5fe2a47e9778a9a84cded15c62208ce237a17b6714ca0b58fb2a5ee7daf` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.PolicySound` | `propext` | `32bae5fe2a47e9778a9a84cded15c62208ce237a17b6714ca0b58fb2a5ee7daf` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.Pos` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Pos.isArg` | none | `82ced563208a43d802a58703fb6864097f3a825afba6ba480a345009ada6ed00` | `02be78314d9217efe00924b7eb5e9ed4d8bbc522470005c9f1d09acd1c2141e6` |
| `Toy.Modality.Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.PtrKind` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Refines` | `propext` | `84d356a2d8d1048aab1135cce5bb89f700e448c7a4fae16300dafef4a66cefdf` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.Shape` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Shape.align` | none | `12e248f8e46b35a9a20613f2a1da863f478e418cf56cd139b46034aac0301445` | `4d403dc2efd11259a1187dd82ef42f494d8ef89943d45b7b1f5ebd6986be327f` |
| `Toy.Modality.SrcSafe` | `propext` | `60fd651cf2f6a55d81cb295c7a21da8ac58c4250be8711cc9a9caa627afebc27` | `d918d4ee213d55409ba7aae0863e04a078205b76cc5b8e9079064f89cc219db8` |
| `Toy.Modality.Step` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Tag` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.TgtSafe` | `propext` | `6ef10b876dd9d3af9acba4d07581bbf1fe1df5ddbdee1abede76dd3000372ca9` | `d918d4ee213d55409ba7aae0863e04a078205b76cc5b8e9079064f89cc219db8` |
| `Toy.Modality.Trace` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.TransformerSound` | none | `e5c531615fcf5e1ce912498ba702f9b6f727706e79cd8e3a6836b6ad57bcd455` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.Ty` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Ty.freeze` | `propext` | `e7eb1508bdebffcd7f44df6538e9ef0120d00a5fd5529cce577ca066601704e9` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.Ty.isPtr` | `propext` | `e7eb1508bdebffcd7f44df6538e9ef0120d00a5fd5529cce577ca066601704e9` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.Ty.unpin` | `propext` | `e7eb1508bdebffcd7f44df6538e9ef0120d00a5fd5529cce577ca066601704e9` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.Wrap` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.Modality.Wrap.relaxes` | `propext` | `794244fa59f1829d27ab0f0b1f0c9bfec3028dd4a5d0c3d4c126cb8d750bd2de` | `52f75b22bd554af0be03b8879f26461cd83aaa88f5118b26b1278382463eedf7` |
| `Toy.Modality.Written` | none | `c935387057539050795cacf1bd9dbdaa0ac69df54b1d7156f82ae7573262a789` | `5eb26a43c17707b7c70dec1b8d8325681edc5429788abb46da71d4f698cba1c9` |
| `Toy.Modality.aligned_and_misaligned_of_nonzero_niche` | `Classical.choice`, `Quot.sound`, `propext` | `ddf8a8ba37c6af82a76ec938a040d5ed64eac8b06c18be8d982ddcd60896b01c` | `6cdb1739143d1e6ed0d2f55b54bed39ac4fef7b09da022f5ad2c14248e685282` |
| `Toy.Modality.alphaOf` | `Classical.choice`, `Quot.sound`, `propext` | `b79ff9a8155de712424465a3db489db0d8683d9bf296458acf654c65ea6742fa` | `a330f833879abed01b2701b0818fccaaeb18b984c777d4ba4995a4af761c2911` |
| `Toy.Modality.alphaOf_has` | `Classical.choice`, `Quot.sound`, `propext` | `da6a8c7740de985082974fbb0fc75bde204edf0236162ffab8172f13cbac03c1` | `91dcf3358ba1741666994236484c9a3f36cebeef50d7e254d7b149d886e5ae92` |
| `Toy.Modality.alphaSet` | `Classical.choice`, `Quot.sound`, `propext` | `20556c920d49d96095be10553bfb86911b946fe261d7600a181670ede822a85c` | `ea769b6d56ecb301edb901ff83b0b1af54062f46f73fc50df9f49ca92aad1a1e` |
| `Toy.Modality.alphaSet_has` | `Classical.choice`, `Quot.sound`, `propext` | `6be09b8dded5785a6824a85f3e82ef60f4e2b0930b3da4f9226ff70fd0c4edf4` | `de97432a12b4e9bb0114ce14fd2ea20de8e0302c4735d0e5bc2ba0c1ac525f06` |
| `Toy.Modality.arg_nofree_of_addr_zero` | `Quot.sound`, `propext` | `948e40e13c2e4672a255bc351943bea9a5c87df0f52f1e725e433b1f58762e7d` | `ed5d7bb2041e1a12cd987f85d042183b8b7fa7eacd6fb3f8e843448d0fbd351c` |
| `Toy.Modality.atomSat` | none | `42678e74c8e7e9e0e9f20d54a886c1e58216e5e8983299923bcbb593e0cccff2` | `cf2ba2a69cdd2de7bd057a0921b7f1f205258bfce3e40231b74306b67db8a08b` |
| `Toy.Modality.attrDual_le_refl_trans` | none | `473483a866cfbc08a6739da15562eafe109e94e65d8b809cd78f51929ea6916d` | `85875a6bb8b4a4a86231bb14b62d2a267481559e730198a3510697c79364e7d1` |
| `Toy.Modality.attrSat` | none | `949d7d9c15cea6992bf1a9aed0ae6663f741954cf3fccd2144a5d020819e3ce2` | `a16299a5ab8e0580fc69732ef26ea42399ff4ff4c8470b1125872dacac75274b` |
| `Toy.Modality.attrsNoalias` | none | `9c0a069a63b4ff54844bbd4812adafe715ebd5f81e83e309f7b24e2229e2ff50` | `8dfb9b73ef03ac5019d885bda27cf1991efd8191e3fa116b8cc3835e2b2368c1` |
| `Toy.Modality.boxTy` | `propext` | `b4e5ce1dae311467f75fbc5a7ddf477f82b76612d52a8941afbf038ae449e8ea` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.cl` | none | `a7adf485622abfa724a08fd422a424b5340b041d529c65654119874f8942a292` | `f1312f6de90dd4b8caddfc8d20953e27451a510f368880b31dc9691bb2ba7f12` |
| `Toy.Modality.clDeref` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.cl_eq_of_den_iff` | `Quot.sound`, `propext` | `cc0d6f32f98f7a206154ce64b4592ba3c0ef58065251e92ca9c1c257b9d90e58` | `fdcd17b62c53d5e6f0dc858ca0d6874e67631a32a8f3d28303217f6501acf0b0` |
| `Toy.Modality.cl_transformer_cl` | `propext` | `5fc37f49529fb691a0b3aa72bcd2e5dbb19fbf11b26c0f7da20ce3412b8c5032` | `e74455830ae2046ffebe601b2828ff0d45dfebf13e2cc127145220e467d29dc0` |
| `Toy.Modality.comp` | `propext` | `c3174568485fb599f5801a3270e841d981f029be55a4b31b6cffeb28920f16e5` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.compSound_const_bot` | `Quot.sound`, `propext` | `358353fd93c2a4a142627de1a6b9166e77905ac09a8ce236acbda101b6bd97f1` | `1ac7d80ade5f40c76af720036bd9204c7cd3d88567c66cb7283454e7367f83d4` |
| `Toy.Modality.comp_deep_inv` | `Quot.sound`, `propext` | `3cf362d97c427e1913b3c8c647b4c65c9b3c5118f3875b594b93286a4b678410` | `a4fbcce963934d9272274caf873ba90f3bc52bd623b63747f39384bdc96b0d46` |
| `Toy.Modality.comp_eq_some_leaf` | `Quot.sound`, `propext` | `f158f2eb5b6fc5dc398cdfc0b0717786072a2f5b6c7b7738eff9a8949022ae1e` | `8c54b64c3e89b0bdd13aa662b027054b03c83a3eda5f310edb0987619a2da8be` |
| `Toy.Modality.comp_tRelax_deep_eq_leaf` | `Quot.sound`, `propext` | `9169e34a71c6ed474732aed1993c5815ebc11520217a48ac4ac2fffe3d3ab20b` | `340e83cc482bac1c885eee374dac08dcf0481574d26739c73099f8fbdafaf3f9` |
| `Toy.Modality.containsRelaxer` | `propext` | `e7eb1508bdebffcd7f44df6538e9ef0120d00a5fd5529cce577ca066601704e9` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.den` | none | `f173c02623f8c47bf69a61cb6f756f4fb1896288d4fe8c630486fd56fa6ceb5d` | `ddcf65278e4a36365265ad997f12cd3eb8b2c92c62caf9e14d65950c29adf45d` |
| `Toy.Modality.denOpt` | none | `d93ce7efd58947a212a59bee232e58c39b11d04d43939ed7f8e2645bc09e77c9` | `ddcf65278e4a36365265ad997f12cd3eb8b2c92c62caf9e14d65950c29adf45d` |
| `Toy.Modality.denP` | none | `d2fde8f8e51ec67d9111b263695bfa6bf850432b2a96aac79b55fd175a996c22` | `c20d8b0545bc0f1476ba5609c742d803eda4fe47507df8684377e9e4de43bb65` |
| `Toy.Modality.den_bot` | `propext` | `c3fa913ebd9b39e83e8aaa964957bdb6b3da2d1ab8a4e9b4403bc9c7a4094cc0` | `96ea02e9cf131b2b53aa45d2b085db37fddb2a280e8ac368a047c2c4e6d45539` |
| `Toy.Modality.den_tReadAfter` | `Quot.sound`, `propext` | `67de2c85a161710e197feedda7c67029c422eec7163f403ff866544dfa62318e` | `50a48c94eee21c0ef207e578c8f922f007a23c8e707d57cdfd3971ef0a7f33ba` |
| `Toy.Modality.den_tRelax_tDangling` | `Quot.sound`, `propext` | `2020bc887d75fee10f283a46da1d97fea65b30a75c3b40e85e9a22b7ad4d89b2` | `8b6098dca36773a4441285e78b35ce2ac8d13cad8e0e500668bbf6b4897b047d` |
| `Toy.Modality.den_tRelax_tForeignRead` | `Quot.sound`, `propext` | `864e16ebf6c69010c70a0f976f5c5e22431aa1593d559ccf83911bc70fa8eefe` | `746dcb721bfe3340d6e0849695a8db653faef783f636421568f417aa682e6d1c` |
| `Toy.Modality.den_transformer_of_den` | `Quot.sound`, `propext` | `14513f0f1ea9f6634352065d65ddb0c3f62130c457f7c7a307600e77b35d9aae` | `854fe174d60d3ba7157f4d9ba3f00d54cd0f1ab1ed3995c722cf9b0ec5ae4814` |
| `Toy.Modality.dereferenceableAtReturn_iff_atomSat_derefWhole` | none | `c0dab82876abfa23cfcfe30e7edb743d44d2995a392169daaec2594db5aa4d6d` | `1cba8cde6116887f934b81f8d854168c6cfdf4651183e7ab5a1326a6e7bad5e7` |
| `Toy.Modality.ex_argInRange` | `Quot.sound`, `propext` | `942075b6a7808ddeef4d3f8b9c65299cd41c9af03eefd2aa507bad11c888c21d` | `e8f636f7890e7999f658812ad335e64e23fc4c564b251bc1ea92583a55342a06` |
| `Toy.Modality.ex_atomSat` | `Quot.sound`, `propext` | `625a3b8e8b1ef64a214e8b2cd23459915a42d64535e193fba6c21a87db4d0c55` | `b65cb464dd26f55b1b6cb4aa84ee52a389da1073c3847f999a4b56728bf1146a` |
| `Toy.Modality.ex_attrSat` | `Quot.sound`, `propext` | `d78afe31c9e2c42ab1f88588956bb45791416d61a59543743a14540e4a4e5b41` | `e89acb01cd1a1541afd8d66449830e83206acd2baca96d2f5e5b353c0eaa6960` |
| `Toy.Modality.ex_cl` | none | `79d8025ec4f96aee116374bcba39da54559b68c89e59c76314d30c210335793c` | `a17f989f5cd6c517eaf45cb4dac4798c5cf696211f66620a002160c522db0f33` |
| `Toy.Modality.ex_clDeref` | none | `40bc82906d7751b92d9f21361c12ab4ad04c22777ce6d35f2fd7085b3edc40c4` | `954955d194763b076aed0aa6c0949d89f0b2e370ee298f74e7bd7c53a2c7504c` |
| `Toy.Modality.ex_compSound` | `Quot.sound`, `propext` | `dd51b57a0f6bc2d079cb4322103b7b21329b70e969a383a5ff98dc65bdd56e5a` | `1eb6e81bd288fa68f60e5e17f375f1c9ada67cb9126a5422c92e2a108c16760c` |
| `Toy.Modality.ex_den` | `Quot.sound`, `propext` | `0f7bd049a0d1adee7d35471300576d93110ed1ae956f8d8bdac3044e80881006` | `9e70f29eef8ecd532e66aca460921b7952c46478219887ddd4f4216381649743` |
| `Toy.Modality.ex_denOpt` | `Quot.sound`, `propext` | `12948612a51e3fcb1ea59467cccfea524c9ecd88741b0f73a9ab12e9ccb93b1d` | `7f95c06126ee7bedac189aa6ab58d76392a62a3cad9cfb0491970fe5fc579a11` |
| `Toy.Modality.ex_dereferenceable` | `Quot.sound`, `propext` | `5c5decfab2f1c99dd7a4e581d21d4532e3e66aa67a9c47c288ce39958ff9dcf5` | `e1588431aabdf241274864b3a5ab74edd17a7d32ba72b35639fd9f0ffee66d73` |
| `Toy.Modality.ex_docTy` | `propext` | `0ffa1594e55c654141f2fbf4e1038fcab12d022a6b313491e5e7b8733add6b18` | `106165e35398251ee2e451e652c8fcbdbc6e69894b825ad4217af2e04668672c` |
| `Toy.Modality.ex_fieldTy_posTrans` | `propext` | `61b220de6b482f79db62e516269c9764fdc5e0916df05dd8bf0682d354bbbb5d` | `f10e539e0b64dcc97c3c92a8aac773e9130d3736a5ef1f635924b4664e1413b7` |
| `Toy.Modality.ex_freeze_unpin` | `propext` | `28b3ff9112a26f1197dafb25486f11a894ead387c82253411116ec4fa24983fe` | `a1c44d84a6e0bae664a428769212145bd015431349c8872e72559d836750766b` |
| `Toy.Modality.ex_gammaSet` | `Quot.sound`, `propext` | `1c69cab9c89b665b4f681e0cdbb4611b98c2e28a4e60cf14e5674efd635c9180` | `6ae4202e0323c8b422ea4d19b9f03d1490fde7d08c70ee85ef5af24b15699d12` |
| `Toy.Modality.ex_isNiche` | `Classical.choice`, `Quot.sound`, `propext` | `da4bbc53e01aae4375f1b577b46aef053fb8338413e353df33f86ddee7e20570` | `0b15c7150fcdacc4ce4a8d60947d344ac526f3791bec930945c13a80b7c5a193` |
| `Toy.Modality.ex_kindBase` | none | `5955be4c9b65f9d0742e8e967bdd10faf195c0317b1d0459e6ed8c87c6cf50db` | `45d27580d334b6e5b867a5c601cbf067f4441b12653bc0ae7e695f0d49cea3be` |
| `Toy.Modality.ex_kindRule` | `Quot.sound`, `propext` | `06ad5ca841898e8c001c4122b7312ec885f7c3219dcc14b4ef3d744a8d86db37` | `70a248f9e44ece7f0614523c37318c97d8781fa498168681c5cb3207099d3ccf` |
| `Toy.Modality.ex_leafAt_relaxedOn` | `propext` | `bffd7b1c04db1a133f28048cfd0e18c25bd4e81e53d38bedf69ab13fa73032ee` | `c990798d52746215f2494c06ae95b1e79a643dae236e9dc177d3275b3ed099fd` |
| `Toy.Modality.ex_liftOpt` | none | `3bd7793856c1275e0470027d5e52c5cb8a4e75dfea3880230a6bcb79eb4ee9c4` | `5657f73301c35851978d34014e79eb99f370f296b8e7dabefa7df47f75a5a58b` |
| `Toy.Modality.ex_lower` | none | `bb6e7349520d3d3b65ba4b7ab05def5bc86dfaa1334b3d0be67777490a86a2bd` | `1148632fa56379aa84b7c36f1de05ff6b767ff27c75643a8d691718bddec49c1` |
| `Toy.Modality.ex_mod_inf_sup` | none | `b78aae2dd96c452acdcc3d0cee233626962b29b04cec1de9f84f150c4d3402a9` | `e440c1cc5a9209179bb68571121171cfdc58126b9dfd2cda3467cb092e43aa04` |
| `Toy.Modality.ex_mod_le` | none | `9672903beb84f43026aafbf6f1aabd0d10bfea6a6ace1291a2f4f253a21cd6d5` | `7bf27aa4d3fabfdd510d08733daabd6aa2fed4f0c9d83a27b530be3a2f689877` |
| `Toy.Modality.ex_noArgEvents` | `propext` | `5b39c892d5a484120c76f5c4d676c3791f7d77f6060c7f9156beb3e90588c2e8` | `c7390f46f5ebfbfe905c5a3b3bb4d70bd1b2145b035137cadcbaaa56115f01e2` |
| `Toy.Modality.ex_notFreedDuring` | `Quot.sound`, `propext` | `e91add7e8af281505c94683349fc71451ba3143019db78aa984af6d1dd072bd5` | `596e412215a31dac40b56f8d470de7f905afb40a5e509c9a9d2db88ae157c416` |
| `Toy.Modality.ex_pointer_constructors` | `propext` | `9c38436d54e41c2ade61c9e892eb4883b8790d91fbca990a6599ab4e0add9372` | `0c97bd879a387be1b58e902c5909187ab161ab0d6a6751daaff4474d379c25f4` |
| `Toy.Modality.ex_policy` | `Classical.choice`, `Quot.sound`, `propext` | `6c35e359aede4b1fdc3af6a2616a82e11dcaa30bd83f5a7501d3cfa8998261d6` | `590bfd884882065e8dd8eb3c550971d856c4c0538e69a3feaa39021f389c6715` |
| `Toy.Modality.ex_refines` | `Classical.choice`, `Quot.sound`, `propext` | `6ef3a32714050c3a38368ab04696c5b95885e2afe2240409a378836eeaf1c5b4` | `0fd105b275f3da8979866207287b0f126ca4933da0b51ff019e0f2ce00cea536` |
| `Toy.Modality.ex_relaxRule` | `Quot.sound`, `propext` | `9c9ae84ff737d6a4290cc5c9dafc87ed64c09410931185a61656fe63a00c072f` | `1e4a94086f26d01ee69bbb3753be85174761fe3662549dc942ea42db7f12435b` |
| `Toy.Modality.ex_repair_helpers` | `propext` | `d9eafac430fdc77f33c510ed63c4a98be19123b0600b788217a7df4182a72ab0` | `c977b34cee148c84febec375adf3d58f302cc4eb77e716f64fa28d8406504619` |
| `Toy.Modality.ex_safe` | `Quot.sound`, `propext` | `352b1fce353d94b2cbbed60ac934a7e51a283432ee467bfd5873276e9ce9d76e` | `b064442e301a6b2f2fc35e0059a7e3ac92805d4d413765d2cc1fef44bc09df12` |
| `Toy.Modality.ex_shape` | `Classical.choice`, `Quot.sound`, `propext` | `25d87e708aa9b06d1420ba2acc0aca37e38fa8fd6a6c10ce248461d12b562829` | `6bc28df8f5820285f2b232204bdb12702e1c0ef90d17803c14d81e79cd3141ff` |
| `Toy.Modality.ex_transformerSound` | `Quot.sound`, `propext` | `137d5fb81509609821c14a18c82c3ded3779123ee967cfb586cbac56a059974a` | `dfe9c5f9ece3f5438db02709e5e9c8465d26f8e26f83b35f2c943c6c87ce311c` |
| `Toy.Modality.ex_transformers` | none | `e04a6de35e50375022bb6ebb9e6bc7d72d6aeeecb0ab7a5039ffb8a171d657e8` | `97de6447a30e0951b322a8ee7802b6926c68fb460572bfb941d73e375e87c3c6` |
| `Toy.Modality.ex_wrap_relaxes` | `propext` | `24d05a9ef7c830a2ee038de333a87110a26f51854bc3e6f2bd6d4e86abe8e2f9` | `5b96ec214fd4a5699703a2206c33f746c9193c96ce8c0a1fc91abc018aed7c44` |
| `Toy.Modality.exists_den_not_atomSat_of_not_has_cl` | `Quot.sound`, `propext` | `d97e3d7430cccce1de212d83106e98dfaadb5043abb51e093504a2d4e1fdb5f4` | `fdcd17b62c53d5e6f0dc858ca0d6874e67631a32a8f3d28303217f6501acf0b0` |
| `Toy.Modality.exists_den_not_attrSat_of_not_has_lower` | `Quot.sound`, `propext` | `eb3c783647be940a79210d9e315aa059e2033722a4bf4acf48ebcf63b40261a1` | `cd1e6693a9176a2229ba8de252f2f341c7580ef24d5ae97ab57d10aa8a1da3f9` |
| `Toy.Modality.fieldTy` | `propext` | `e9d911a5fbac7da03653f060c8da7fccde9a66bfc0b663d80fe4476a1c150794` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.filterMap_fieldTy_map_fst` | `propext` | `c867d3cf963657412f964b68c09c523c8bb7d49bfa2941e77d6eab64cfccb002` | `017430d12806ec6984f735a9763ddc002f3e8a5e205593c0a1a1ee711bc2597e` |
| `Toy.Modality.gammaDual` | none | `9b8d2faf25e79348217605618e2b099e7e4e42c1fe1915cf15c2bfc429fdbe3a` | `ea769b6d56ecb301edb901ff83b0b1af54062f46f73fc50df9f49ca92aad1a1e` |
| `Toy.Modality.gammaOf` | none | `e9ca27466f0e9124305eec09742f4cbefa7ef3755e1da8149d1c204f72a8d994` | `a330f833879abed01b2701b0818fccaaeb18b984c777d4ba4995a4af761c2911` |
| `Toy.Modality.gammaSet` | none | `db611417fce181a04e2b30424a9772911b764e5accb30e2efd2e02578f4f5283` | `65ed12093914ee5ed5e759c0eabd4fc82ed9a0413269b5341113d62a9a654df5` |
| `Toy.Modality.kindBase` | none | `2bc892cff37fe58e1795b613d560db00c560c254e0345bd553b4e5168dd45c45` | `0befcefa1b81cb63ed6edae847a0c46d1c5e4aa461f457a332044a3fad1c95d1` |
| `Toy.Modality.kindBase_ret_lowering_dereferenceable_by_kind` | `propext` | `9e071aef5928c291d975f45d03f130a8f8a49e2a3b9f9a5ce23344cb1ede9a72` | `659a15d80e94a2dab74d1f116dcd21033aad52279d12ff14e5ca440e03da4c27` |
| `Toy.Modality.kindBase_three_kinds_coincide` | none | `ef86567a9aa1ba4c04cdcc7aec09fe1072ef0a9f9f7060184b937aeddd3a3dea` | `45d27580d334b6e5b867a5c601cbf067f4441b12653bc0ae7e695f0d49cea3be` |
| `Toy.Modality.kindRule` | none | `877adff6b0f410adaef658a9e7c468a119896ee1b59cd80611c8223212dddb50` | `b6fdc35ec5648b8665609997e1af8bc84ba1a0d4c2ec1b6eec7ddb4df135c4ee` |
| `Toy.Modality.kindRule_iff_den` | `propext` | `da371eace443d26d28afa7e08b89ae81e972579686d61304c7dd104d330d1a36` | `baf743c4ff7499a3c905878ecf23c5ee14e9d50d6f28985a42b287047120e5e1` |
| `Toy.Modality.le_tRelax_iff` | `propext` | `c31fddb86a1016f89972bc29e68f1bbc8ad3f07022ecea1781e28e05cd372a79` | `d3685ca59edc7b6e932553f7693a51337e3ca6a22aa0932d2a094d41e623bf1a` |
| `Toy.Modality.leafAt` | `propext` | `28dcd35664bc2cdb2f222fb732aad6cef5c25194795396b17b88f982e5bb4227` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.liftOpt` | none | `96881a4f6d7e610e9349894dedd4c7eacb42f84d29e02a166cd589704d355c42` | `f7722a9613382b95659c66a8ac4c6afe4e3bede8d18f608dbab63791de12255b` |
| `Toy.Modality.liftOpt_sound_at_non_niche_one` | `Classical.choice`, `Quot.sound`, `propext` | `c2af42f9cadac1bea2a375a8ec51bc24c842d1c220eddfcacc0e84851cda7fab` | `dfe21413108999d920cb05fc486c70618643236f14d5e78f79c19fae167bcb42` |
| `Toy.Modality.lower` | none | `e4f52e7ad408a0bec06e542b9820f3e8119a11d6f120dc46a7bfcfc677519aba` | `bf23437b83f1c2b65c1ad1cd36f0ffb23789a373d1eed56b4e37ecf2fcab5073` |
| `Toy.Modality.lower_arg_no_right_adjoint_on_closed` | `Quot.sound`, `propext` | `42200e122c64c00ef876d2bcb466d2bcd17a47739f4a191bee82c73ac66f82fc` | `eacaa42485c79dac3321f8c43c9bfa3cd758932fa352be27c48a8f2b11275e7b` |
| `Toy.Modality.lower_dereferenceable_eq` | none | `6b497ad5e0621c61c9f4d054921f956f93169303785c4e70496b20eeb165923e` | `caf37bc09156f54800af43a208c0d805e99cffde6a5af544a00d9c67ebb6248d` |
| `Toy.Modality.lower_ret_no_right_adjoint_of_alignLog_eq_zero` | `Classical.choice`, `Quot.sound`, `propext` | `8c8c3b841aaf645baf259813544339b48ea2cb1057fc6396fd780546f98b1222` | `eacaa42485c79dac3321f8c43c9bfa3cd758932fa352be27c48a8f2b11275e7b` |
| `Toy.Modality.lower_ret_right_adjoint_of_alignLog_ne_zero` | `Quot.sound`, `propext` | `fb15fc1da137a06eca49ed52f643d3a69943ce05605a33a1ffe04552af8a0889` | `650eb954615f9e020ce6c90a6aafa3a57bfee62ad025633547b25ab613882bd4` |
| `Toy.Modality.mem_scalarize` | `Quot.sound`, `propext` | `359f631883567c632f652731306a65edc6130ac8bbebb4aa4d98e8733eae2b2d` | `d4dd19690e17e4ae5c269185dce89957acc7d705924d0359c9965ce11763d905` |
| `Toy.Modality.modAt` | `propext` | `dde4420d6f1d4d2792b9226f50bad8b14ca2ec0d7e4e8fff76ae486c8a54ae3e` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.modAt_append` | `Quot.sound`, `propext` | `83fdacb6a92022a7ca3d93c939643b535fabf8f08e3ae7ce20e71f2a5f9db799` | `1e3092d86a0a176d1152230aa56fa2c87a923306ac69e2162d7852c7f9627efe` |
| `Toy.Modality.modAt_eq_of_not_relaxedOn` | `Quot.sound`, `propext` | `66787e77fb4790ed3bdc0193e9bab1fc1412114d0d31ade785b23320326cdb06` | `eb7d02881557da100a24f0f96010b0370c287d7932e980c17d178569c7f4360b` |
| `Toy.Modality.modAt_relaxAll` | `Quot.sound`, `propext` | `821ad797f12275bc568489821c66a5f450093ec0eaaeefbe13877b77a77aafc2` | `d006438ff3a01722cffc99ced2c72ba763bfc847ee4cce3a5938a3c0063daeb4` |
| `Toy.Modality.modAt_retype` | `Quot.sound`, `propext` | `4559b18b2fc122ec69794a6e57d36ecb1c3521f59a23894eae07565cc0547ac2` | `65796d3ab037fcdf6344552e31ed759c3c6f9d684a8a6262b4d2c2b43c617bb3` |
| `Toy.Modality.modDerefWholeOnly` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.modFrozenBounded` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.modFrozenOnly` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.modUniqueBounded` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.mutFull` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.mutFullNoBounded` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.mutRefTy` | `propext` | `b4e5ce1dae311467f75fbc5a7ddf477f82b76612d52a8941afbf038ae449e8ea` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.naivePolicy` | `propext` | `dd03611924a29ae8eaba3c02b9b966b934d7f5e0df718f6abfd36e8a8292db6e` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.ne_zero_of_dereferenceable` | `Quot.sound`, `propext` | `fc552c4195a0f2eb1d5dd1ce4f56e29c61f7b2e389e68eef6c4d8d64b16db87a` | `7d41293c92eacf7f297b9c60530e6f3295736d1d7e4468960ada44934efdbd3e` |
| `Toy.Modality.noArgEvents_tAt` | `propext` | `35b8ad2e5436fe3d47faefd235a965179b87801cf795ef0c8fa46f0fde66f7ef` | `b470f0a83244fba34946a88723fb5eecd15ed0e1c40082037c58ba883ff35700` |
| `Toy.Modality.not_noalias_tConflict` | `propext` | `6ca0a88ffec076efeb75a5597cc527fc425f8ce3342b1f2d61bb8a1dc52040f9` | `ada44a7c6f778dd755c12f02a903800355d24a491870533e9ccfae1f5643084c` |
| `Toy.Modality.not_noalias_tOutOfRange` | `propext` | `a977800443350f9d295e9cc5abdb44bfe0a93b83aa2d7e2f698b3cc76130880b` | `c69ea4a420b46b256e3f16bfd06b741d69e8fd4e464b1fe0bcddba8bc1719500` |
| `Toy.Modality.not_nofree_tFreed` | `Quot.sound`, `propext` | `62cddaea1bbf3e872cda2e4b040fb3f98fbfe3ff6a7f7c350595f2fdae786f4f` | `3107794e5384b6f30e7e9a81f7976f687d816794c670662c93316c7a3ccbf8be` |
| `Toy.Modality.not_readonly_tOutOfRange` | `propext` | `84d1154cf789910d6dc4911f6d6845b9ad44164a7f3a1dd3581f4461c69a2699` | `c69ea4a420b46b256e3f16bfd06b741d69e8fd4e464b1fe0bcddba8bc1719500` |
| `Toy.Modality.not_ret_noalias_tReadAfter` | `Quot.sound`, `propext` | `410e204bcf613d2afa637ac3230d119644a89391eb07fba3c3d68bf037147f1f` | `423ae76bbaa6d0769a36e71726c941bb971503ddf4d440333f50bd375ee4ae24` |
| `Toy.Modality.pathNestedMD` | none | `e29109f065e5e083b0ec84c213e8b9cebaf62b20679976d5a79d2abb18cde5d8` | `670948e6b0c4f39f7b85036c66065109f1c3685bec721df540cf6c5229f80deb` |
| `Toy.Modality.policyExact_refusing_and_scalar_reshaping` | `Quot.sound`, `propext` | `75d6bf00d9eb9043fba8347913db619b87d5cbe84609ac937a838346027b0fe0` | `5df71d353ebe9e5bf4cec53a0b3bbec498f8c1fc3cb237ca7beb6b504dd3b61d` |
| `Toy.Modality.policySound_degenerate` | `Classical.choice`, `Quot.sound`, `propext` | `0781ab3661624567e9dc8ec22ffc332bee808a0266c4ef3a1c36282e4b0bddba` | `dfc98c976e5c833b77942e321ea661fc6896526822b076ef4d6bbcac355ee8ec` |
| `Toy.Modality.policySound_of_exact` | `propext` | `1daba2730422e5476a8732e6bacbe7cad0c2b5014d295a1fadef4608d49d025f` | `dfc98c976e5c833b77942e321ea661fc6896526822b076ef4d6bbcac355ee8ec` |
| `Toy.Modality.posTrans` | `propext` | `263ff5ffb5931b4dc5cf264bb8446691bfdb3e249f277b7a7a1e266577383f5f` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.posTrans_eq` | `Quot.sound`, `propext` | `3c1769a01b368abadf9ce1dc92c3ee9c878ac73672bc6426db45e914753d6abb` | `f0c8ad8ca3322cfeaa1842123f620d302395ca4000a08c0561cc2189e301d5a0` |
| `Toy.Modality.progDangling` | none | `2260dee8c757258759f5a50088ad7c09aa4d5d82ef8cf0f262e34cbc2b289c87` | `6f6127283d715a199d4e231c3c0f6e05e5ed10ffd51e1ffa22078431a4c024cc` |
| `Toy.Modality.qsMDPair` | none | `d0284f386545d826133606227d9b04dca4938bf8d16b247e5c4f7dc3de4ced74` | `670948e6b0c4f39f7b85036c66065109f1c3685bec721df540cf6c5229f80deb` |
| `Toy.Modality.rawTy` | none | `7c4e1747e9229b9de2c9440a2788ee1db3d6f0c8d66df70d7e6953a807228d8a` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.refFull` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.refFullNoBounded` | none | `d4b503df174a3f74c3779438e7a9b3f414226724732c61d2ff9a2d33ba63d1fb` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.refTy` | `propext` | `b4e5ce1dae311467f75fbc5a7ddf477f82b76612d52a8941afbf038ae449e8ea` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.refines_scalarize_of_not_relaxedOn` | `Classical.choice`, `Quot.sound`, `propext` | `f2b8601d66e2c65dea6dbe333559f74e6ce04ef68b15925690dbf64639c9d7b7` | `256b8e560004354b7d71c21768ce9b1d20342ee9bc76eded91024049984c70d8` |
| `Toy.Modality.relaxAll` | none | `7d00d948a0f1a9c019d745ea9302b084f9becdfe50bb695bc645e31f0b63ecff` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.relaxRule` | none | `f173c02623f8c47bf69a61cb6f756f4fb1896288d4fe8c630486fd56fa6ceb5d` | `ddcf65278e4a36365265ad997f12cd3eb8b2c92c62caf9e14d65950c29adf45d` |
| `Toy.Modality.relaxRule_iff_den` | `Quot.sound`, `propext` | `7c7b79fe5652783d8126925ffa2e4929cf7f1bf56553f18dd9350c4b9bd2cc75` | `cca28bb66a7429c97187cbef8c1b8e2136e128163416e90c34c9b9e397ccfbc1` |
| `Toy.Modality.relaxedOn` | `propext` | `ea18c0c1eedd3db7b75b8bb5dc257463f7bf4f3a37e0ca3b824504ba2052f0a9` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.relaxedOn_eq_false_of_containsRelaxer` | `propext` | `7d91c07ab54528c8b8f480e4977e03d788ad5a06d0072b2c40ac4ffe43f4a3a3` | `ab15ee27164919ac454cdfc5a0dfb27bf6b06aa31d5fab12dcd294d64fbd8a56` |
| `Toy.Modality.repairExclude` | `propext` | `dd03611924a29ae8eaba3c02b9b966b934d7f5e0df718f6abfd36e8a8292db6e` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.repairRetype` | `propext` | `dd03611924a29ae8eaba3c02b9b966b934d7f5e0df718f6abfd36e8a8292db6e` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.repairStopAtRelaxer` | `propext` | `dd03611924a29ae8eaba3c02b9b966b934d7f5e0df718f6abfd36e8a8292db6e` | `d7b845b78517bc98eed1bd98d3cc9e8dbf3123fa964f399643be586f114513a7` |
| `Toy.Modality.req` | `propext` | `dde4420d6f1d4d2792b9226f50bad8b14ca2ec0d7e4e8fff76ae486c8a54ae3e` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.reqAux` | `propext` | `b2499ca99135340917372295826abda7e51e7198d3b7ff699a8a47df43fc07d4` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.reqAux_eq` | `Quot.sound`, `propext` | `81d9ddf8c931b809fb8c15435d587c0664bd50703e1a00dbb1e2b4c0f8a49aee` | `6deb099a08cc12d41a1fc5cb44e18771dcf33cd930ccfc41039850edd3d19a9f` |
| `Toy.Modality.retRightAdjoint` | none | `957e08f7b4738127ccd605aa369cfac7f9bc63225ea34314b6df7a8393bd264e` | `034bf8ea9723d8a96ef8a44d4eb8698432526aa22471c1b5296e3bf33eea2c44` |
| `Toy.Modality.retype` | `propext` | `011498e6b3b35b66f4dc5c7b05c9177fb441efae2f92a2c6e7900c8150a02c79` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.s1` | none | `f9bc269541845aa7f1cb7b236119737ac7794e1282e6a3778ef56ce5f9dd6884` | `4d403dc2efd11259a1187dd82ef42f494d8ef89943d45b7b1f5ebd6986be327f` |
| `Toy.Modality.s2` | none | `f9bc269541845aa7f1cb7b236119737ac7794e1282e6a3778ef56ce5f9dd6884` | `4d403dc2efd11259a1187dd82ef42f494d8ef89943d45b7b1f5ebd6986be327f` |
| `Toy.Modality.scalarize` | `propext` | `82b104e9ee7243580c25cd73fcdcbb6d633ae4ba57545725ce58f4242884fced` | `832700bc27e4691636dbc4c95eed5d00825fd15071efa9c83351916a786d9496` |
| `Toy.Modality.scalarize_map_fst` | `propext` | `2d9033bc8a3c8bbfe83651def33be2305aaac6f9cbf079318e0a510c6c61681b` | `d4dd19690e17e4ae5c269185dce89957acc7d705924d0359c9965ce11763d905` |
| `Toy.Modality.stopAtRelaxer_not_relaxedOn` | `Quot.sound`, `propext` | `f2133d4c705c8fd9fe64863da0dbfc41bfbc876fdb7e0d5cb76dd655a5d4023b` | `6c54f6f831cedbb11f1ecd86346a1357b5508e50c86d9db8d968bbc7d207f7fd` |
| `Toy.Modality.tArgWrite` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tAt` | none | `81f342e02585bbdef4c8b594bf99fd5a59c3b4f3965ed604bfe8c192b585d843` | `0a1e3671868851b491b886d9c52a5cfa3fa3b2a0be664e814a1f73668720d085` |
| `Toy.Modality.tBox` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.tCell` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.tConflict` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tDangleAliased` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tDangling` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tForeignRead` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tFreed` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tMis` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tNull` | none | `9569cb32ddd24799b71e3a87de367948cb92951ff6f839ae2983cc56c0959692` | `0a1e3671868851b491b886d9c52a5cfa3fa3b2a0be664e814a1f73668720d085` |
| `Toy.Modality.tOutOfRange` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tPin` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.tReadAfter` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.tRelax` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.tRelaxExceptFrozenOnly` | none | `8832ee78402e5535100618c1eb9aa3f3d3a6fd1a972ce8acb6efea4d75a1a14e` | `209bb0b07849ecb7dad24f21326f9691444cbca1621a93c2c24c7825b858c733` |
| `Toy.Modality.tRelax_tRelax` | `Quot.sound`, `propext` | `7a4d2786bdd8b45451c79d53533a62fe72edddc7b26faa25392d897e9de5123b` | `55b1b890b7d50a05c8c21168490917b58b913450dec1458d89b8bda9bc88cb4a` |
| `Toy.Modality.tStar` | none | `3245aa3e71f21e036efd501967bda65d1681df32b6b7dcdfc533e152564c7b7c` | `362132f8da506f991d0068f4a7b107a52f1205ed81e123ca3349834acb543784` |
| `Toy.Modality.transformerSound_iff_le_tRelax` | `Quot.sound`, `propext` | `c8b7d6172eda14cf6ebac2f2234bde9f69c0a7b7ad907ffb77cfc5b34d032e97` | `d69144cca1791e2168138dea865b5ec5f54710b768d51afc4773b4dca1868a3e` |
| `Toy.Modality.transformerSound_tRelax_comp_cl_s2` | `propext` | `db504b0385d0b349a84342248cc87859abde53471641da8d5ff31e55c47ddc83` | `ef7c7febc4dfb0e15f235b4ba40407a8481b5bc2718ee9843273ff036d8e2149` |
| `Toy.Modality.transformers_deflationary_closed` | `Quot.sound`, `propext` | `93a7838bfdf597dc23484ad9496e94c86a2b129cba4d236740fc3fc42ad8d9ed` | `a166527df9b5a343c3527cab2e93324696928ca4364f3044ef9831e4ee15fbfc` |
| `Toy.Modality.tyMDPair` | `propext` | `7c4e1747e9229b9de2c9440a2788ee1db3d6f0c8d66df70d7e6953a807228d8a` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.tyMDScalar` | none | `9a5c9db125d8e69508c9ca4b44e1698180d7d55cd409cd433f60ada220050df8` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.tyNestedMD` | `propext` | `7c4e1747e9229b9de2c9440a2788ee1db3d6f0c8d66df70d7e6953a807228d8a` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.tyPairMD` | `propext` | `7c4e1747e9229b9de2c9440a2788ee1db3d6f0c8d66df70d7e6953a807228d8a` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.tyPlainPair` | `propext` | `7c4e1747e9229b9de2c9440a2788ee1db3d6f0c8d66df70d7e6953a807228d8a` | `190532a7b1c9ab29abb37390220cbabed34f2a83cafb98c184f38b4b638bee0f` |
| `Toy.Modality.wAlloc` | none | `dcdcd9e363312321fb9b3443fc60bd535537c91c580287705d2e1a0465633f96` | `b1b5f9e68f60b98a375909efc6b1ea36015bfce85dc0c6f852553424b15291f4` |
| `Toy.Modality.wrapTrans` | `propext` | `e114592c4559c10f19996ccd6cdab3a1e71b1a334903cb21d5c509f994a0ecfd` | `5f9fcc6bf3734f48e3129a26000163a496b4f70eac3ee76ece4b9c8398f5b915` |
| `Toy.Modality.zero_mod_align` | none | `3d6d066e3b47761b469c9cc9576bd07be4734747cc1980a12d2d1a2406bf404d` | `78da1e5d2ff55db0931e2b1355be36eb333a975106bd389b17df08ba4d767bd0` |

### Primary sources

External sources, read at the pinned revisions (evidence roles as in the cards: documentation or source). They support the `derived (modeling bridge)` lines and prior-art entries, not the theorems.

- rust-lang/rust, commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (source):
  - `compiler/rustc_ty_utils/src/abi.rs`: `arg_attrs_for_rust_scalar` lines 321-420 (parameter `is_return` line 327; `nonnull` lines 339-342; `pointee_align` and `pointee_size` recorded at lines 346-352, line 352: `attrs.pointee_size = pointee.size;`; `noalias_for_box` line 358; `noalias` lines 366-370 and its absence at return position lines 371-375; `nofree` lines 392-410; `readonly` lines 412-415); call sites with `is_return = arg_idx.is_none()` lines 589 and 602.
  - `compiler/rustc_middle/src/ty/layout.rs`: line 1051 (`let optimize = tcx.sess.opts.optimize != OptLevel::No;`), lines 1065-1067 and 1082-1084 (`is_unsafe_unpin`), line 1085 (`is_box_global`), lines 1092-1104 (`MaybeDangling` arm), lines 1132-1141 (null-niche recursion).
  - `compiler/rustc_mir_transform/src/sroa.rs` lines 67-84 (types excluded from scalar replacement).
  - `library/core/src/mem/maybe_dangling.rs` lines 6-10; `library/core/src/mem/manually_drop.rs` lines 156-160.
- rust-lang/rust, commit `cd2a75d9d58d7bd7b59cde543684fc83c3e785d2` (merge commit of rust-lang/rust pull 164568, committed 2026-10-20), `compiler/rustc_mir_transform/src/sroa.rs` lines 62-85 (exclusion of `ty.is_like_maybe_dangling()` types, lines 66-69) (source).
- llvm/llvm-project, commit `5b10d2d74929eae78912771222c9855af97496f4` (release llvmorg-23.1.6), `llvm/docs/LangRef.md`: `align` lines 1497-1505, `noalias` lines 1512-1534, `nofree` lines 1574-1588, `nonnull` lines 1609-1618, `dereferenceable(<n>)` lines 1622-1640, `dereferenceable_or_null(<n>)` lines 1644-1655, `noundef` lines 1699-1703, `readonly` lines 1797-1803 (documentation).
- rust-lang/rfcs, commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/3336-maybe-dangling.md` lines 94-102, 139-148 and 172-173; `text/3467-unsafe-pinned.md` line 245 and lines 364-366; `text/1860-manually-drop.md` lines 54-60 (documentation).
- rust-lang/reference, commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `src/behavior-considered-undefined.md` lines 59, 104 and 152 (documentation).
- Public issue tracker items, cited in prose and not relied on as normative: https://github.com/rust-lang/rust/issues/164176 (closed, labels `I-miscompile` and `A-mir-opt`), fixed by https://github.com/rust-lang/rust/pull/164568 (merged); the `MaybeDangling` tracking issue https://github.com/rust-lang/rust/issues/118166 (open).
- Definitions copied into `Toy.Modality.Imported`: published package `galois-connections-best-abstract-transformers-and-fixpoint-transfer` (google/zerocopy branch `reference`, commit `a0dca4883c555805181f8149eafd7e65ab238991`), `lean/Toy/AbsInt/Basic.lean` lines 21 and 25 (git blob `ae1c1a94c6c73ef95c162cdc585fbfd044eecf90`) and `lean/Toy/AbsInt/Galois.lean` lines 27-28 (git blob `7828c554deffea6e4da6073f8eaa36a11844adfe`). Other published packages cited in prior-art entries (not subjects): `aliasing-models-and-reference-based-optimizations` (commit `62e8715787fde13fecdffe87b22f5700a96af019`), `enum-niche-layout-guarantees-and-validity-invariants` (commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), `pin-structural-projection-address-stability-and-drop-guarantee` (commit `383075883be4fb20e686252c4c5f8c15ad161414`), `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness` (commit `6249da8fcc95a6f49780588838ac00f4686187bd`).
- Papers (prior art; not re-modelled): Davey, Priestley, *Introduction to Lattices and Order*, 2nd ed., 2002, doi:10.1017/CBO9780511809088; Cousot, Cousot, POPL 1977, doi:10.1145/512950.512973; Ganter, Wille, *Formal Concept Analysis: Mathematical Foundations*, 1999, doi:10.1007/978-3-642-59830-2; Gordon, Parkinson, Parsons, Bromfield, Duffy, OOPSLA 2012, doi:10.1145/2384616.2384619; Jung, Jourdan, Krebbers, Dreyer, "RustBelt", POPL 2018, doi:10.1145/3158154; Jung, Dang, Kang, Dreyer, "Stacked Borrows", POPL 2020, doi:10.1145/3371109; Villani, Hostert, Dreyer, Jung, "Tree Borrows", PLDI 2025, doi:10.1145/3735592; Lee, Kim, Song, Hur, Das, Majnemer, Regehr, Lopes, "Taming Undefined Behavior in LLVM", PLDI 2017, doi:10.1145/3062341.3062343; Lopes, Lee, Hur, Liu, Regehr, "Alive2: Bounded Translation Validation for LLVM", PLDI 2021, doi:10.1145/3453483.3454030.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the toolchain download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs `lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and checks that only `propext`, `Classical.choice` and `Quot.sound` occur; and (4) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` entries) recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (the sorted `name : type := value` texts of every package-local constant reachable from the statement, theorem bodies excluded) and compares them with `audit/statements.json`. Exit status 0 means all four checks passed. The script's docstring states exactly what is hashed.

Manual alternative (build and print the axioms of the main results):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs `#print axioms` on every main result of the cards. Each line of its output must list no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

Kernel dependency audit for `Shape.size_pos` (reproduces the table in Findings):

```text
cd lean
lake env lean ../support/size_pos_audit.lean
```

What revalidation does not cover: the `derived (modeling bridge)` lines and prior-art entries depend on the external sources at their pinned revisions. To check them against a newer subject, re-read the cited line ranges (for example `compiler/rustc_ty_utils/src/abi.rs` `arg_attrs_for_rust_scalar`, `compiler/rustc_middle/src/ty/layout.rs` around the `MaybeDangling` arm and the null-niche recursion, `compiler/rustc_mir_transform/src/sroa.rs`, and the LangRef parameter-attribute entries) and compare them with the definitions quoted in Findings.
