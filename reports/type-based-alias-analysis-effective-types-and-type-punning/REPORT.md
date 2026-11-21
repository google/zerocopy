# Type-based alias analysis, effective types and type punning in a toy byte-memory model (Lean 4)

## Summary

This package formalizes, in Lean 4 without Mathlib, a toy straight-line language over
byte-addressed memory with two memory semantics: **(E)**, a C-like effective-type semantics
(per-byte effective-type tags, declared objects whose type is fixed, a character-type (`u8`)
exemption, and a `memcpy` that copies tags), and **(U)**, an untyped semantics in which bytes carry
no type. For this toy model, it proves results about when moving a memory access past another one on
the basis of the access types alone (type-based alias analysis, TBAA) is a contextual refinement,
about how `memcpy`, byte accesses and declared objects interact with type punning, and about how
the behaviours of (E) and (U) relate. All 13 results are kernel-checked Lean theorems: no `sorry`, and no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`. Model–system relation: none proved. These are
statements about the toy model; they neither establish nor refute the corresponding claims about C,
C++, LLVM or Rust.

Each bullet below is the plain-language claim of one result card, verbatim; the hypotheses are
stated in the claim.

- **R1-hoist-load-above-incompatible-store-sound-E.** Under the effective-type semantics with the standard discipline (character exemption), if T is not u8, U is not u8, T and U share no leaf scalar type (NoCommonLeaf T U), and the load's destination register differs from the store's source register, then moving a load at type T above an earlier store at type U is a refinement in every context, from every initial state, and for every address pair.
- **R1b-sink-load-below-incompatible-store-unsound-E.** Under the effective-type semantics with the standard discipline (character exemption), although every hypothesis of R1 holds (u32 and f32 are non-character types with no common leaf, and the registers differ), moving a u32 load below a later f32 store to the same allocated bytes is not a refinement: the f32 store legitimately re-types allocated storage after the load, so in the transformed program the load is undefined. The theorem's statement names no context or initial state; the witness inside its proof is the context [] / [out 1] with the initial state freshAt 0 16 [1,1,1,1], whose bytes 0 to 15 are allocated storage with no effective type yet, and sink_load_below_store_witness_runs states its runs: the source terminates normally, printing the four zero bytes it loaded, while the transformed program stops at a type fault before any output.
- **R1c-store-store-swap-unsound-E.** Under the effective-type semantics with the standard discipline (character exemption), although both types are non-character and share no leaf, swapping a u32 store and an f32 store to the same allocated bytes is not a refinement: the later store determines both the value and the effective type. The theorem's statement names no context or initial state; the witness inside its proof is the context [] / [load 2 u8 0, out 2] with the initial state (freshAt 0 16 []).withRegs (regs2 [1,1,1,1] [2,2,2,2]), whose bytes 0 to 15 are allocated storage with no effective type yet. store_store_swap_witness_runs states its runs: the byte load observes the value written by the later store (the source prints [2], the swapped program [1]); with the suffix [load 2 f32 0, out 2] instead, the source prints [2,2,2,2], while the swapped program, whose later store is the u32 store, stops at a type fault before any output.
- **R2-tbaa-hoist-unsound-U.** Under the untyped semantics, for all types T and U (with no condition relating them) and every address p: (1) from the witness state uWit U p, the target [load 1 T p, store U p 0, out 1] has the behaviour 'print T.size zero bytes', which the source [store U p 0, load 1 T p, out 1] lacks; and (2) for all registers s and r, hoisting a T-load from p above a U-store to the same address p is not a refinement. Consequently, for every criterion C on pairs of access types: if, whenever C T U holds, this same-address hoist is a refinement under the untyped semantics for every address p and every pair of distinct registers s ≠ r, then C holds for no pair of types (no_type_criterion_licenses_same_addr_hoist_U); and if, whenever C T U holds, the same-address hoist is a refinement under the untyped semantics for at least one address p and one pair of registers s, r, then C holds for no pair of types (no_type_criterion_licenses_same_addr_hoist_U_at_one_site).
- **R3a-memcpy-then-typed-load-defined-E.** Under the effective-type semantics with the standard discipline, for every state σ, type T, source p, destination q (overlapping ranges allowed) and register s: memcpy q p T.size followed by a T-load from q and out s terminates normally, printing exactly the bytes that were at p, if and only if MemcpyLoadOk σ T p q holds (both ranges allocated, and at each byte offset i the leaf T.leafAt i is compatible with the destination byte's declared leaf if that byte belongs to a declared object, and with the source byte's tag otherwise). Corollary: if a T-load from p would pass the checks (ReadableAt) and the destination range is allocated and its declared bytes accept T (ReceivesAt), the copy-then-load is defined and returns the bytes at p.
- **R3b-byte-copy-defined-forces-byte-tbaa-unsound.** For every compatibility discipline c with memcpy performing its byte accesses under c, and every type T: if byte-wise copying the T-object of objSt T (to the untyped storage at address 8) is defined, then, from the initial state objSt T with suffix [out 1], moving a byte (u8) load of address 0 above a T-store to address 0 is not a refinement. For T ≠ u8 this is the cross-type reading: a discipline cannot both make the byte-access copy defined and make byte loads non-aliasing with T stores; for T = u8 the refuted reordering is a same-type u8/u8 one.
- **R4a-no-type-fault-implies-E-equals-U.** For every configuration cfg, program P and initial state σ: if the effective-type execution of P from σ under cfg does not stop at a type fault (¬ TypeFaults cfg P σ), then its behaviours equal those of the untyped execution of P from erase σ.
- **R4b-untyped-run-refines-effective-type-run.** For every configuration cfg, program P and initial state σ, every behaviour of the untyped execution of P from erase σ is a behaviour of the effective-type execution of P from σ under cfg. Moreover (behE_not_refines_behU_iff), for every cfg, P and σ, the converse inclusion (every behaviour of the effective-type execution is a behaviour of the untyped execution) fails if and only if the effective-type execution stops at a type fault (TypeFaults cfg P σ) and, in addition, the untyped execution from erase σ either terminates normally (UDefined P (erase σ)) or has a strictly longer output trace than the effective-type execution.
- **R4c-agreement-iff-no-type-fault-given-U-defined.** For every configuration cfg, program P and initial state σ, if the untyped execution of P from erase σ terminates normally (UDefined), then the behaviours under (E) and (U) coincide if and only if the (E) execution does not stop at a type fault.
- **R5a-store-store-swap-sound-E-declared.** Under the effective-type semantics with the standard discipline, if T is not u8, U is not u8, and T and U share no leaf, then swapping a T-store to p and a U-store to q is a refinement in every context and from every initial state in which every allocated byte of [p, p + T.size) belongs to a declared object.
- **R5b-sink-load-below-store-sound-E-declared.** Under the effective-type semantics with the standard discipline, if T is not u8, U is not u8, T and U share no leaf, and the load's destination register differs from the store's source register, then moving a T-load from p below a later U-store to q (sink) is a refinement in every context and from every initial state in which every allocated byte of [p, p + T.size) belongs to a declared object.
- **R5c-store-swap-scheme-sound-on-declared-not-on-allocated.** Under the effective-type semantics with the standard discipline, for the address-parametric scheme 'swap a u32 store to p and an f32 store to q': (1) for all p and q, the swap is a refinement in every context from every initial state in which every allocated byte of [p, p + 4) belongs to a declared object; (2) it is not the case that, for all p and q, the swap is a refinement in every context from every initial state in which every allocated byte of [p, p + 4) is allocated storage (it fails at p = q = 0, a site that the theorem's statement does not name; store_swap_scheme_fails_at_zero states that it is not the case that, at p = q = 0, the swap is a refinement in every context from every initial state in which every allocated byte of [0, 4) is allocated storage).
- **R6-disjoint-ranges-hoist-sound-U.** Under the untyped semantics, if the address ranges [p, p + T.size) and [q, q + U.size) are disjoint and the load's destination register differs from the store's source register, then moving a T-load from p above a U-store to q is a refinement in every context and from every initial state. No type hypothesis is involved.

What the results do **not** show is listed first under **Boundaries** (non-claims, per result),
followed by escape hatches and the status of every statement.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a toy model. It keeps the mechanisms that the design questions turn on and omits everything
else:

- **(E) effective types.** Every allocated byte is either *allocated storage* with an optional leaf
  tag (no tag: no effective type yet) or a byte of a *declared object* whose leaf type is fixed.
  A store at a non-character type sets the tags of the allocated-storage bytes it writes; a `u8`
  store keeps them; a load is undefined (a `type` fault) when a byte's tag is incompatible with the
  load's leaf type; a store into a declared object at an incompatible leaf type is undefined;
  `memcpy` copies tags into allocated storage and leaves declared bytes' types unchanged. The
  compatibility discipline is a parameter (`Compat`, `ECfg`); the intended C-like configuration
  is `stdCfg` (the discipline `stdCompat`, with the character exemption, and `memcpy` performing
  checked byte accesses). This is meant to follow the dynamic reading of ISO C11 6.5p6–7 (N1570):
  the effective type of storage with no declared type is set by a non-character store and copied
  by `memcpy`, a declared object keeps its declared type, and a character type may access any
  object. C++ has an analogous rule in N4950 [basic.lval] p11, which makes an access undefined
  unless the glvalue's type is similar to the dynamic type of the object, its signed or unsigned
  variant, or char, unsigned char or std::byte.
- **(U) untyped memory.** Bytes carry no type; a load at `T` succeeds when its bytes are allocated
  and the value is valid for `T`, and reinterprets them. This is meant to capture memory without
  types, as in LLVM IR when no `!tbaa` metadata is used ("In LLVM IR, memory does not have types",
  LangRef at the pinned commit), and Rust, whose Reference states its aliasing undefined behaviour
  in terms of references and `Box` with no type-based rule.
- **Refinement.** Replacing a block `src` by `tgt` is sound (`ReorderSoundFrom`, `ReorderSound`)
  when, for every program prefix and suffix and every initial state satisfying the precondition,
  every behaviour of the transformed program is a behaviour of the original. A behaviour is an
  output trace together with normal termination or undefined behaviour; undefined behaviour after
  trace `t` permits every outcome whose trace extends `t` (it does not retract output already
  emitted). Execution is deterministic.

Known gaps between the toy and the systems it is meant to capture:

- Straight-line programs with constant addresses; no control flow, calls, allocation or
  deallocation, object lifetimes, pointers stored in memory, arrays, or concurrency.
- Five access types: `u8` (the single character type), `u16`, `u32`, `f32` and the padding-free
  struct `pair` = {`u32`, `f32`}. No unions, qualifiers, signed/unsigned variants, or C's
  compatible-type relation. Type disjointness is the per-byte criterion `NoCommonLeaf`, which is
  coarser than C's "neither type is (an aggregate containing) the other" whenever two distinct
  struct types share a scalar member type, and which ignores offsets inside aggregates.
- Every byte list of the right length is a valid value of every type (no uninitialized bytes, no
  pointer provenance, no alignment requirement, no invalid bit patterns).
- A `u8` store into allocated storage keeps the byte's tag (a modeling choice; in the literal text
  of C11 6.5p6 a character-type store modifies the stored value, after which later accesses take
  the type of their own lvalue). Explicit `u8` load/store loops do not transfer effective types,
  while `memcpy` does (`byte_loop_copy_does_not_transfer_effective_type`); C11 6.5p6 also transfers
  the effective type for copies "as an array of character type", which the toy does not model for
  explicit loops.
- The toy's `memcpy` reads all source bytes before writing (the semantics of C's `memmove`), and
  copies between overlapping ranges can be defined (`memcpy_overlap_defined_examples`); C11's
  undefined behaviour for overlapping `memcpy` (N1570 7.24.2.1p2) is not modeled.
- Declared objects have no lifetime end; storage reused for another type (C++ placement new, stack
  slots reused across variable lifetimes) is not declared storage in the toy's sense.
- C++'s implicit object creation by `memcpy` (N4950 [cstring.syn] p3) is not modeled; LLVM's
  `!tbaa` access-pair rule and Rust's reference-based aliasing models (Stacked Borrows, Tree
  Borrows) are not modeled.

**Model–system relation: none proved.** The package states and proves no embedding, abstraction or
simulation between the toy semantics and C, C++, LLVM IR or Rust. Every connection to those
systems below is a separate `derived (modeling bridge)` claim with its reasoning stated. These are
statements about the toy model; they neither establish nor refute the corresponding claims about
C, C++, LLVM or Rust. The theorems relating (E) and (U) (R4a, R4b, R4c) are relations between two
toy semantics, not between the toy and a real system.

**How the subjects listed in `REPORT.json` relate.** They fall into three groups. (a) The Lean 4
toolchain (`leanprover/lean4` `v4.34.1`) is the system in which every statement of this package is
kernel-checked (see **Evidence**). (b) ISO C11 (Committee Draft N1570), the C++ working draft N4950, the LLVM
Language Reference Manual and the Rust Reference are the language and IR specifications whose rules
motivate the toy's two semantics, (E) and (U). Model–system relation: none proved; these are
statements about the toy model, and they neither establish nor refute the corresponding claims about
those specifications. (c) The remaining subjects are prior-art reference points cited in the cards'
tier justifications, prior art and modeling-bridge lines, and are not modeled: WG14 Defect Report
#236 (the committee's reading of the aliasing rule for allocated storage), the Rust Unsafe Code
Guidelines glossary, Stacked Borrows and Tree Borrows (Rust aliasing models), Krebbers's "Aliasing
Restrictions of C11 Formalized in Coq" with the CH2O Coq development, Diwan, McKinley and Moss's
"Type-Based Alias Analysis", Hathhorn, Ellison and Rosu's "Defining the Undefinedness of C",
Memarian et al.'s "Into the Depths of C", Tuch, Klein and Norrish's "Types, Bytes, and Separation
Logic", and Leroy and Blazy's C-like memory model with its CompCert mechanization. No result is
derived from, or formally compared with, any of them. The report thus concerns the toy model: it is
kernel-checked with (a), motivated by (b) and positioned against (c); it is neither a combination of
these subjects nor a formal comparison between them.

### Toolchain and project

- Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core
  Lean and `Std`; no Mathlib and no Lake dependencies.
- Lake project in `lean/` (`lakefile.toml`, package `toy_tbaa`, one library `ToyTbaa`). Modules:
  `ToyTbaa/Basic.lean` (types, programs, execution, behaviours, refinement),
  `ToyTbaa/Semantics.lean` (the two memory semantics, hypothesis predicates, concrete states),
  `ToyTbaa/Examples.lean` (definition examples), `ToyTbaa/Lemmas.lean` (proof infrastructure),
  `ToyTbaa/Results.lean` (results, counterexamples, non-vacuity theorems, positive controls),
  `ToyTbaa/Companions.lean` (companion statements that state, in their types, the witnesses used
  inside the proofs of R1b, R1c and R5c, and a further `valsAt` example; no other declaration
  depends on them).
  Definitions live in the Lean namespace `Toy.Tbaa`, results in `Toy.Tbaa.Results`, definition
  examples in `Toy.Tbaa.Examples`, companion statements in `Toy.Tbaa.Companions`.
- Paths in `-- path.lean:A-B` citations are relative to the package directory.

### Model definitions (verbatim)

Every definition from `lean/ToyTbaa/Basic.lean` and `lean/ToyTbaa/Semantics.lean` that a statement,
card or rendering in this report names is quoted below verbatim, in source order (doc comments
omitted). Definitions from the other modules are quoted under **Findings › Auxiliary declarations
cited by name**.

#### Types, values and instructions (`lean/ToyTbaa/Basic.lean`)

`Ty` is the access-type universe. `Ty.leaves` gives the per-byte leaf layout (a `pair` is four `u32` bytes followed by four `f32` bytes), `Ty.size` its length (every toy type has size at least 1), and `Ty.Valid` accepts every byte list of length `T.size`. Bytes, register names and addresses are natural numbers: no bit width, no wrapping. Instructions: `set r v`, `load r T p` (reads `T.size` bytes at `p, p+1, …`), `store T p r`, `memcpy dst src n` (as if through a temporary buffer) and `out r` (emits register `r`; the observable event). `Instr.isLoad` tests whether an instruction is a load.

```lean
-- lean/ToyTbaa/Basic.lean:18
abbrev Byte := Nat
```

```lean
-- lean/ToyTbaa/Basic.lean:21
abbrev Val := List Byte
```

```lean
-- lean/ToyTbaa/Basic.lean:24
abbrev Reg := Nat
```

```lean
-- lean/ToyTbaa/Basic.lean:29-34
inductive Scalar where
  | u8
  | u32
  | f32
  | u16
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Basic.lean:40-46
inductive Ty where
  | u8
  | u32
  | f32
  | pair
  | u16
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Basic.lean:52-57
def leaves : Ty → List Scalar
  | .u8 => [.u8]
  | .u32 => [.u32, .u32, .u32, .u32]
  | .f32 => [.f32, .f32, .f32, .f32]
  | .pair => [.u32, .u32, .u32, .u32, .f32, .f32, .f32, .f32]
  | .u16 => [.u16, .u16]
```

```lean
-- lean/ToyTbaa/Basic.lean:60
def size (T : Ty) : Nat := T.leaves.length
```

```lean
-- lean/ToyTbaa/Basic.lean:63
def leafAt (T : Ty) (i : Nat) : Scalar := T.leaves.getD i .u8
```

```lean
-- lean/ToyTbaa/Basic.lean:71
def Valid (T : Ty) (v : Val) : Prop := v.length = T.size
```

```lean
-- lean/ToyTbaa/Basic.lean:86-92
inductive Instr where
  | set (r : Reg) (v : Val)
  | load (r : Reg) (T : Ty) (p : Nat)
  | store (T : Ty) (p : Nat) (r : Reg)
  | memcpy (dst src n : Nat)
  | out (r : Reg)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Basic.lean:95-97
def Instr.isLoad : Instr → Bool
  | .load .. => true
  | _ => false
```

#### Execution, behaviours and refinement (`lean/ToyTbaa/Basic.lean`)

`runFrom` executes deterministically and stops at the first fault; `exec` returns `done t` (normal termination with trace `t`) or `ub t` (undefined behaviour after trace `t`). `Allows (done t) o'` holds when `o' = done t`; `Allows (ub t) o'` holds when `t` is a prefix of the trace of `o'`. `Beh`, `Refines`, `ReorderSoundFrom` and `ReorderSound` are the behaviour set, refinement (every target behaviour is a source behaviour) and contextual soundness of a block replacement.

```lean
-- lean/ToyTbaa/Basic.lean:101-104
inductive Fault where
  | base
  | type
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Basic.lean:107-110
inductive Step (S : Type) where
  | next (s : S)
  | emit (v : Val) (s : S)
  | fault (k : Fault)
```

```lean
-- lean/ToyTbaa/Basic.lean:114-116
inductive Final (S : Type) where
  | ok (s : S) (t : List Val)
  | fault (k : Fault) (t : List Val)
```

```lean
-- lean/ToyTbaa/Basic.lean:120-123
inductive Outcome where
  | done (t : List Val)
  | ub (t : List Val)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Basic.lean:127-133
def runFrom {S : Type} (step : Instr → S → Step S) : List Instr → S → List Val → Final S
  | [], s, t => .ok s t
  | i :: P, s, t =>
    match step i s with
    | .next s' => runFrom step P s' t
    | .emit v s' => runFrom step P s' (t ++ [v])
    | .fault k => .fault k t
```

```lean
-- lean/ToyTbaa/Basic.lean:136-138
def Final.outcome {S : Type} : Final S → Outcome
  | .ok _ t => .done t
  | .fault _ t => .ub t
```

```lean
-- lean/ToyTbaa/Basic.lean:141-142
def exec {S : Type} (step : Instr → S → Step S) (P : List Instr) (s : S) : Outcome :=
  (runFrom step P s []).outcome
```

```lean
-- lean/ToyTbaa/Basic.lean:145-147
def Outcome.trace : Outcome → List Val
  | .done t => t
  | .ub t => t
```

```lean
-- lean/ToyTbaa/Basic.lean:157-159
def Allows : Outcome → Outcome → Prop
  | .done t, o' => o' = .done t
  | .ub t, o' => t <+: o'.trace
```

```lean
-- lean/ToyTbaa/Basic.lean:165-166
def Beh {S : Type} (step : Instr → S → Step S) (P : List Instr) (s : S) : Outcome → Prop :=
  Allows (exec step P s)
```

```lean
-- lean/ToyTbaa/Basic.lean:169
def Refines (tgt src : Outcome → Prop) : Prop := ∀ o, tgt o → src o
```

```lean
-- lean/ToyTbaa/Basic.lean:174-176
def ReorderSoundFrom {S : Type} (Pre : S → Prop) (step : Instr → S → Step S)
    (src tgt : List Instr) : Prop :=
  ∀ pre post s, Pre s → Refines (Beh step (pre ++ tgt ++ post) s) (Beh step (pre ++ src ++ post) s)
```

```lean
-- lean/ToyTbaa/Basic.lean:180-181
def ReorderSound {S : Type} (step : Instr → S → Step S) (src tgt : List Instr) : Prop :=
  ReorderSoundFrom (fun _ => True) step src tgt
```

#### Shared helpers (`lean/ToyTbaa/Semantics.lean`)

`readRange m p n` returns the `n` entries at `p, …, p+n-1`, or `none` if one of them is unallocated (for `n = 0` it returns `some []`). `updRange m p n f` applies `f (a - p)` at every address `a` with `p ≤ a < p + n` (the subtraction is truncated natural-number subtraction, applied when `p ≤ a`, so it does not truncate).

```lean
-- lean/ToyTbaa/Semantics.lean:26-27
def updReg (rs : Reg → Val) (r : Reg) (v : Val) : Reg → Val :=
  fun r' => if r' = r then v else rs r'
```

```lean
-- lean/ToyTbaa/Semantics.lean:30-31
def updRange {α : Type} (m : Nat → Option α) (p n : Nat) (f : Nat → α → α) : Nat → Option α :=
  fun a => if p ≤ a ∧ a < p + n then (m a).map (f (a - p)) else m a
```

```lean
-- lean/ToyTbaa/Semantics.lean:34-39
def readRange {α : Type} (m : Nat → Option α) (p : Nat) : Nat → Option (List α)
  | 0 => some []
  | n + 1 =>
    match m p, readRange m (p + 1) n with
    | some c, some cs => some (c :: cs)
    | _, _ => none
```

#### The effective-type semantics (E) (`lean/ToyTbaa/Semantics.lean`)

A load or store checks, in this order, that its bytes are allocated (else a `base` fault), that the value is well-sized (else a `base` fault), and the effective-type condition of the configuration (else a `type` fault). `stdCompat` admits a `u8` access to any byte, any access to a byte with no tag, and an access whose leaf equals the tag; `strictCompat` removes the `u8` exemption from the checks, while the effect of a `u8` store on tags (fixed by `storeCell`: a `u8` store keeps the tag of allocated storage) is the same under every discipline. `TagsOk` and `DeclOk` are `List.all` over `List.zip`, which truncates to the shorter list; every use is guarded by `readRange`, whose result has `T.size` cells. `memcpy` reads all source cells before writing, copies tags into allocated storage (`copyCell`), and, when `memcpyChecksBytes` is set, checks its byte accesses with `CopyBytesOk`. By these definitions, `memcpy dst src 0` reads and writes no cell and is defined at any addresses.

```lean
-- lean/ToyTbaa/Semantics.lean:48-51
inductive Eff where
  | alloc (tag : Option Scalar)
  | decl (s : Scalar)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Semantics.lean:54-56
def Eff.tag : Eff → Option Scalar
  | .alloc t => t
  | .decl s => some s
```

```lean
-- lean/ToyTbaa/Semantics.lean:59-62
structure Cell where
  val : Byte
  eff : Eff
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyTbaa/Semantics.lean:65
abbrev Mem := Nat → Option Cell
```

```lean
-- lean/ToyTbaa/Semantics.lean:68-70
structure St where
  mem : Mem
  regs : Reg → Val
```

```lean
-- lean/ToyTbaa/Semantics.lean:74
abbrev Compat := Option Scalar → Scalar → Bool
```

```lean
-- lean/ToyTbaa/Semantics.lean:78-81
def stdCompat : Compat
  | _, .u8 => true
  | none, _ => true
  | some a, b => decide (a = b)
```

```lean
-- lean/ToyTbaa/Semantics.lean:89-91
def strictCompat : Compat
  | none, _ => true
  | some a, b => decide (a = b)
```

```lean
-- lean/ToyTbaa/Semantics.lean:97-99
structure ECfg where
  compat : Compat
  memcpyChecksBytes : Bool
```

```lean
-- lean/ToyTbaa/Semantics.lean:102
def stdCfg : ECfg := ⟨stdCompat, true⟩
```

```lean
-- lean/ToyTbaa/Semantics.lean:105-106
def TagsOk (c : Compat) (cs : List Cell) (T : Ty) : Bool :=
  (cs.zip T.leaves).all fun x => c x.1.eff.tag x.2
```

```lean
-- lean/ToyTbaa/Semantics.lean:110-114
def DeclOk (c : Compat) (cs : List Cell) (T : Ty) : Bool :=
  (cs.zip T.leaves).all fun x =>
    match x.1.eff with
    | .decl d => c (some d) x.2
    | .alloc _ => true
```

```lean
-- lean/ToyTbaa/Semantics.lean:119-124
def storeCell (T : Ty) (v : Val) (i : Nat) (cell : Cell) : Cell :=
  { val := v.getD i 0
    eff := match cell.eff, T.leafAt i with
      | .alloc t, .u8 => .alloc t
      | .alloc _, s => .alloc (some s)
      | .decl d, _ => .decl d }
```

```lean
-- lean/ToyTbaa/Semantics.lean:128-132
def copyCell (sc cell : Cell) : Cell :=
  { val := sc.val
    eff := match cell.eff with
      | .alloc _ => .alloc sc.eff.tag
      | .decl d => .decl d }
```

```lean
-- lean/ToyTbaa/Semantics.lean:135-138
def copyFrom (cs : List Cell) (i : Nat) (cell : Cell) : Cell :=
  match cs[i]? with
  | some sc => copyCell sc cell
  | none => cell
```

```lean
-- lean/ToyTbaa/Semantics.lean:142-144
def CopyBytesOk (c : Compat) (cs ds : List Cell) : Bool :=
  cs.all (fun x => c x.eff.tag .u8) &&
  ds.all (fun x => match x.eff with | .decl d => c (some d) .u8 | .alloc _ => true)
```

```lean
-- lean/ToyTbaa/Semantics.lean:147-173
def stepE (cfg : ECfg) : Instr → St → Step St
  | .set r v, σ => .next { σ with regs := updReg σ.regs r v }
  | .load r T p, σ =>
    match readRange σ.mem p T.size with
    | none => .fault .base
    | some cs =>
      if T.Valid (cs.map Cell.val) then
        if TagsOk cfg.compat cs T then .next { σ with regs := updReg σ.regs r (cs.map Cell.val) }
        else .fault .type
      else .fault .base
  | .store T p r, σ =>
    match readRange σ.mem p T.size with
    | none => .fault .base
    | some cs =>
      if T.Valid (σ.regs r) then
        if DeclOk cfg.compat cs T then
          .next { σ with mem := updRange σ.mem p T.size (storeCell T (σ.regs r)) }
        else .fault .type
      else .fault .base
  | .memcpy dst src n, σ =>
    match readRange σ.mem src n, readRange σ.mem dst n with
    | some cs, some ds =>
      if !cfg.memcpyChecksBytes || CopyBytesOk cfg.compat cs ds then
        .next { σ with mem := updRange σ.mem dst n (copyFrom cs) }
      else .fault .type
    | _, _ => .fault .base
  | .out r, σ => .emit (σ.regs r) σ
```

#### The untyped semantics (U) (`lean/ToyTbaa/Semantics.lean`)

`stepU` performs the same allocation and validity checks with no effective-type checks; `erase` forgets the effective-type state of every byte and keeps the registers.

```lean
-- lean/ToyTbaa/Semantics.lean:178
abbrev UMem := Nat → Option Byte
```

```lean
-- lean/ToyTbaa/Semantics.lean:181-183
structure USt where
  mem : UMem
  regs : Reg → Val
```

```lean
-- lean/ToyTbaa/Semantics.lean:186-204
def stepU : Instr → USt → Step USt
  | .set r v, u => .next { u with regs := updReg u.regs r v }
  | .load r T p, u =>
    match readRange u.mem p T.size with
    | none => .fault .base
    | some bs => if T.Valid bs then .next { u with regs := updReg u.regs r bs } else .fault .base
  | .store T p r, u =>
    match readRange u.mem p T.size with
    | none => .fault .base
    | some _ =>
      if T.Valid (u.regs r) then
        .next { u with mem := updRange u.mem p T.size (fun i _ => (u.regs r).getD i 0) }
      else .fault .base
  | .memcpy dst src n, u =>
    match readRange u.mem src n, readRange u.mem dst n with
    | some bs, some _ =>
      .next { u with mem := updRange u.mem dst n (fun i b => bs.getD i b) }
    | _, _ => .fault .base
  | .out r, u => .emit (u.regs r) u
```

```lean
-- lean/ToyTbaa/Semantics.lean:207
def erase (σ : St) : USt := ⟨fun a => (σ.mem a).map Cell.val, σ.regs⟩
```

#### Hypothesis predicates (`lean/ToyTbaa/Semantics.lean`)

`NoCommonLeaf T U` says that no leaf scalar type of `T` is a leaf of `U`; on the toy universe it holds for the unordered pairs {u32, f32}, {u16, u32}, {u16, f32}, {u16, pair} and {u8, X} for every X ≠ u8 (`noCommonLeaf_table`). `RangesDisjoint p n q m` is `p + n ≤ q ∨ q + m ≤ p` (for an empty range, `n = 0`, it still requires `p ≤ q` or `q + m ≤ p`). `DeclaredOn σ p n` (resp. `AllocatedOn σ p n`) says that every allocated byte of `[p, p+n)` belongs to a declared object (resp. is allocated storage); unallocated bytes are permitted, and both hold trivially when `n = 0`. `MemcpyLoadOk σ T p q` is the per-byte condition used by R3a; `valsAt` returns the empty list if a byte of the range is unallocated. `TypeFaults cfg P σ` says that the (E) run of `P` from `σ` stops at a `type` fault; it is a verdict of the semantics, not the programming idiom "type punning". `UDefined P u` says that the (U) run terminates normally.

```lean
-- lean/ToyTbaa/Semantics.lean:217
def NoCommonLeaf (T U : Ty) : Prop := ∀ s, s ∈ T.leaves → s ∉ U.leaves
```

```lean
-- lean/ToyTbaa/Semantics.lean:223
def RangesDisjoint (p n q m : Nat) : Prop := p + n ≤ q ∨ q + m ≤ p
```

```lean
-- lean/ToyTbaa/Semantics.lean:229-231
def Eff.isDecl : Eff → Bool
  | .decl _ => true
  | .alloc _ => false
```

```lean
-- lean/ToyTbaa/Semantics.lean:236-237
def DeclaredOn (σ : St) (p n : Nat) : Prop :=
  ∀ i, i < n → (σ.mem (p + i)).all (fun cell => cell.eff.isDecl) = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:245-246
def AllocatedOn (σ : St) (p n : Nat) : Prop :=
  ∀ i, i < n → (σ.mem (p + i)).all (fun cell => !cell.eff.isDecl) = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:258-259
def ReadableAt (c : Compat) (σ : St) (T : Ty) (p : Nat) : Prop :=
  ∃ cs, readRange σ.mem p T.size = some cs ∧ TagsOk c cs T = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:267-268
def ReceivesAt (σ : St) (T : Ty) (q : Nat) : Prop :=
  ∃ ds, readRange σ.mem q T.size = some ds ∧ DeclOk stdCompat ds T = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:276-279
def memcpyLoadCheck (x : (Cell × Cell) × Scalar) : Bool :=
  match x.1.2.eff with
  | .decl d => stdCompat (some d) x.2
  | .alloc _ => stdCompat x.1.1.eff.tag x.2
```

```lean
-- lean/ToyTbaa/Semantics.lean:288-292
def MemcpyLoadOk (σ : St) (T : Ty) (p q : Nat) : Prop :=
  ∃ cs ds,
    readRange σ.mem p T.size = some cs ∧
    readRange σ.mem q T.size = some ds ∧
    ((cs.zip ds).zip T.leaves).all memcpyLoadCheck = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:307-308
def valsAt (σ : St) (p n : Nat) : List Byte :=
  ((readRange σ.mem p n).getD []).map Cell.val
```

```lean
-- lean/ToyTbaa/Semantics.lean:312-318
def typeFaultsB (cfg : ECfg) : List Instr → St → Bool
  | [], _ => false
  | i :: P, σ =>
    match stepE cfg i σ with
    | .fault k => k == .type
    | .next σ' => typeFaultsB cfg P σ'
    | .emit _ σ' => typeFaultsB cfg P σ'
```

```lean
-- lean/ToyTbaa/Semantics.lean:331
def TypeFaults (cfg : ECfg) (P : List Instr) (σ : St) : Prop := typeFaultsB cfg P σ = true
```

```lean
-- lean/ToyTbaa/Semantics.lean:337
def UDefined (P : List Instr) (u : USt) : Prop := ∃ t, exec stepU P u = .done t
```

#### Concrete states (`lean/ToyTbaa/Semantics.lean`)

Concrete initial states used by witnesses and counterexamples. Addresses outside the described ranges are unallocated.

```lean
-- lean/ToyTbaa/Semantics.lean:351-352
def freshAt (p n : Nat) (rv : Val) : St :=
  ⟨fun a => if p ≤ a ∧ a < p + n then some ⟨0, .alloc none⟩ else none, fun _ => rv⟩
```

```lean
-- lean/ToyTbaa/Semantics.lean:356-357
def declSt (s : Scalar) (n : Nat) (rv : Val) : St :=
  ⟨fun a => if a < n then some ⟨0, .decl s⟩ else none, fun _ => rv⟩
```

```lean
-- lean/ToyTbaa/Semantics.lean:361-363
def declPairSt (rv : Val) : St :=
  ⟨fun a => if a < 4 then some ⟨0, .decl .u32⟩ else if a < 8 then some ⟨0, .decl .f32⟩ else none,
   fun _ => rv⟩
```

```lean
-- lean/ToyTbaa/Semantics.lean:366
def St.withRegs (σ : St) (rs : Reg → Val) : St := ⟨σ.mem, rs⟩
```

```lean
-- lean/ToyTbaa/Semantics.lean:369
def regs2 (v0 v1 : Val) : Reg → Val := fun r => if r = 0 then v0 else v1
```

```lean
-- lean/ToyTbaa/Semantics.lean:374-377
def objSt (T : Ty) : St :=
  ⟨fun a => if a < T.size then some ⟨0, .alloc (some (T.leafAt a))⟩
            else if a < 16 then some ⟨0, .alloc none⟩ else none,
   fun _ => List.replicate T.size 1⟩
```

### Definition examples (proved)

Each core definition has proved instances where it holds (or a run is defined) and proved
instances where it fails (or a run is undefined); for the function `valsAt`, the second column
is its fallback (the empty list) on a range that is not entirely allocated. The statements are
quoted under **Findings › Auxiliary declarations cited by name**.

| Definition | Holds / defined (proved) | Fails / undefined (proved) |
| :--- | :--- | :--- |
| `Ty.leaves`, `Ty.size`, `Ty.leafAt` | `pair_layout` | `pair_byte4_not_u32` |
| `Ty.Valid` | `f32_valid_any_pattern` | `u32_invalid_short` |
| `stdCompat` | `stdCompat_admits` | `stdCompat_rejects` |
| `strictCompat` | `strictCompat_admits` | `strictCompat_rejects_byte` |
| `NoCommonLeaf` | `noCommonLeaf_admits` (u32/f32, u8/u32, pair/u16), `noCommonLeaf_non_u8_struct_instances`; the complete table `noCommonLeaf_table` | `noCommonLeaf_rejects` (pair/u32, f32/f32) |
| `RangesDisjoint` | `rangesDisjoint_admits` | `rangesDisjoint_rejects` |
| `DeclaredOn` | `declaredOn_admits` | `declaredOn_rejects` |
| `AllocatedOn` | `allocatedOn_admits` | `allocatedOn_rejects` |
| `ReadableAt` | `readableAt_admits` | `readableAt_rejects` |
| `ReceivesAt` | `receivesAt_admits` | `receivesAt_rejects` |
| `MemcpyLoadOk` | `memcpyLoadOk_admits` (object copy; punning into a declared object) | `memcpyLoadOk_rejects` |
| `valsAt` | `valsAt_example` | `valsAt_unallocated_example` (a range that is not entirely allocated gives the empty list) |
| `stepE` with `stdCfg` | `stepE_same_type_defined`, `stepE_byte_read_defined`, `stepE_allocated_retype_defined`, `stepE_memcpy_copies_type_defined`, `stepE_memcpy_into_declared_defined`, `stepE_pair_member_access` (first conjunct), `stepE_pair_load_from_member_stores_defined` | `stepE_punning_ub`, `stepE_declared_store_mismatch_ub`, `stepE_memcpy_copy_punning_ub`, `stepE_pair_member_access` (second conjunct), `byte_loop_copy_does_not_transfer_effective_type` (first conjunct), `stepE_unallocated_ub` |
| `stepU` | `stepU_punning_defined` | `stepU_unallocated_ub` |
| `erase` | `erase_example` | `erase_example` (second conjunct: an unallocated address) |
| `TypeFaults` | `typeFaults_admits`; `typeFaults_same_type_nonstandard_cfg` (a nonstandard configuration) | `typeFaults_rejects` |
| `UDefined` | `uDefined_admits` | `uDefined_rejects` |
| `Allows`, `Refines` | `refines_admits` | `refines_rejects` |
| `ReorderSound` | `reorderSound_admits` (from `reorderSound_refl`) | `reorderSound_rejects` |

## Findings

Each card gives the tier, the plain-language claim, the Lean statement as a verbatim source quote
(the proof is elided as `:= …` or `:= by …`; it is in the cited file), the hypothesis ledger, the
depth label, the non-vacuity witness, the positive control for impossibility results, the
statements of all supporting theorems the card names, prior art, and the design question. Its
non-claims are under **Boundaries**. Every theorem quoted in this section is kernel-checked
(`Basis: execution (Lean kernel check)`); each card's connection to real systems is a separate
`Basis: derived (modeling bridge)` line.

Block notation: the *hoist* replacement turns `[store U q r, load s T p]` into
`[load s T p, store U q r]` (a load moved above an earlier store); the *sink* replacement turns
`[load s T p, store U q r]` into `[store U q r, load s T p]` (a load moved below a later store);
the *store/store swap* exchanges two adjacent stores. "Tight" in a ledger means that a proved
counterexample theorem exhibits an instance, in the stated witness class, satisfying all the other
hypotheses in which the conclusion fails.

### R1-hoist-load-above-incompatible-store-sound-E

**Kind:** theorem. **Tier:** T1. **Depth:** shallow.

**Plain claim.** Under the effective-type semantics with the standard discipline (character exemption), if T is not u8, U is not u8, T and U share no leaf scalar type (NoCommonLeaf T U), and the load's destination register differs from the store's source register, then moving a load at type T above an earlier store at type U is a refinement in every context, from every initial state, and for every address pair.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:33-36
theorem hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8
    (T U : Ty) (p q : Nat) (s r : Reg)
    (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSound (stepE stdCfg) [.store U q r, .load s T p] [.load s T p, .store U q r] := by …
```

Unfolded rendering of `hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8` after its binders (`ReorderSound`, `ReorderSoundFrom`, `Refines` and `Beh` unfolded; checked to be definitionally equal to the statement):

```lean
∀ (pre post : List Instr) (σ : St), True →
  ∀ o : Outcome,
    Allows (exec (stepE stdCfg) (pre ++ [Instr.load s T p, Instr.store U q r] ++ post) σ) o →
    Allows (exec (stepE stdCfg) (pre ++ [Instr.store U q r, Instr.load s T p] ++ post) σ) o
```

**Tier justification.** Known informally (C11 6.5p6-7; the type-based alias analysis of compilers) and, at the level of single memory operations on statically typed memory trees, mechanized by Krebbers (CPP 2013, Coq lemma mem_non_aliasing). That lemma is symmetric because CH2O objects receive their type at allocation; it is not a statement about reordering program instructions. R1 is a contextual-refinement statement for the load-hoisting transformation in a model where stores re-type allocated storage, in which the symmetric reading fails (R1b, R1c). No mechanized statement of this form was found in the sources examined.

**Hypothesis ledger.**

- `hT : T ≠ Ty.u8`. *Purpose:* A byte load may read bytes of any effective type (the character exemption), so after the store it is defined and sees the new byte. *Tightness:* tight; counterexample `hoist_E_needs_load_ne_u8`; witness class: overlapping addresses p = q = 0 on untyped allocated storage (freshAt 0 16), T = u8, U = u32.
- `hU : U ≠ Ty.u8`. *Purpose:* After a byte store, a later typed load of the same bytes can still be defined and then sees the new byte. In the toy a byte store into allocated storage keeps the byte's tag (a modeling choice: in the literal text of C11 6.5p6 a character-type store modifies the stored value, which ends the period in which a previously stored effective type applies, and later accesses then take the type of their own lvalue). The counterexamples do not depend on that choice: one uses fresh storage with no tag, the other a declared u32 object, whose type no store changes. *Tightness:* tight; counterexamples `hoist_E_needs_store_ne_u8`, `hoist_E_needs_store_ne_u8_on_declared`; witness class: overlapping addresses p = q = 0, T = u32, U = u8: on untyped allocated storage with no tag (hoist_E_needs_store_ne_u8), and on a declared u32 object, where the witness state satisfies DeclaredOn on the load's range and the hoist is not sound even from the states declared on that range (hoist_E_needs_store_ne_u8_on_declared).
- `hTU : NoCommonLeaf T U`. *Purpose:* Types sharing a leaf can alias: a struct load can read a member just stored. 'T ≠ U' is not enough (pair vs u32). *Tightness:* tight; counterexample `hoist_E_needs_noCommonLeaf`; witness class: overlapping addresses p = q = 0 on untyped allocated storage, T = pair, U = u32.
- `hsr : s ≠ r`. *Purpose:* Register data dependence: if the load overwrites the store's source register, the store writes a different value. *Tightness:* tight; counterexample `hoist_E_needs_distinct_registers`; witness class: disjoint addresses p = 8, q = 0 on untyped allocated storage, s = r = 0, T = f32, U = u32.

**Non-vacuity witness.** Scalar instance T = f32, U = u32, p = 8, q = 0, s = 1, r = 0 (hoist_E_nonvacuous) and struct instance T = pair, U = u16, p = 0, q = 8, s = 1, r = 0 (hoist_E_nonvacuous_struct): all hypotheses hold, the source block (with suffix out 1) is defined from a concrete state, and the target gives the same outcome. (Lean: `hoist_E_nonvacuous`, `hoist_E_nonvacuous_struct`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:76-81
theorem hoist_E_nonvacuous :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧ (1 : Reg) ≠ 0 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 8, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.load 1 .f32 8, .store .u32 0 0, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:86-91
theorem hoist_E_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ (1 : Reg) ≠ 0 ∧
    exec (stepE stdCfg) [.store .u16 8 0, .load 1 .pair 0, .out 1] (freshAt 0 16 [1, 1]) =
      .done [[0, 0, 0, 0, 0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.load 1 .pair 0, .store .u16 8 0, .out 1] (freshAt 0 16 [1, 1]) =
      .done [[0, 0, 0, 0, 0, 0, 0, 0]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:96-98
theorem hoist_E_needs_load_ne_u8 :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u8 .u32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0] [.load 1 .u8 0, .store .u32 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:105-107
theorem hoist_E_needs_store_ne_u8 :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:116-121
theorem hoist_E_needs_store_ne_u8_on_declared :
    Ty.u32 ≠ .u8 ∧ NoCommonLeaf .u32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declSt .u32 4 [1]) 0 Ty.u32.size ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u32.size) (stepE stdCfg)
        [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u8 0 0, .load 1 .u32 0] [.load 1 .u32 0, .store .u8 0 0] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:132-134
theorem hoist_E_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ (1 : Reg) ≠ 0 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 1 .pair 0] [.load 1 .pair 0, .store .u32 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:141-143
theorem hoist_E_needs_distinct_registers :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .load 0 .f32 8] [.load 0 .f32 8, .store .u32 0 0] := …
```

**Prior art.**

- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).
- Robbert Krebbers. The C Standard Formalized in Coq. PhD thesis, Radboud University Nijmegen, 2015 (IPA Dissertation Series 2015-22): the CH2O formalization of the C11 standard, including its aliasing restrictions.
- Amer Diwan, Kathryn S. McKinley, J. Eliot B. Moss. Type-Based Alias Analysis. PLDI 1998, pp. 106-117. https://doi.org/10.1145/277650.277670 (introduces type-based alias analysis for a type-safe language, with disambiguation by declared types and by field types; it does not consider C effective types or re-typing of storage).
- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- ISO/IEC 9899:201x Committee Draft N1570, section 6.5 paragraph 6 (text checked at http://port70.net/~nsz/c/c11/n1570.html#6.5p6): a non-character store into an object with no declared type sets its effective type 'for that access and for subsequent accesses that do not modify the stored value'; 'For all other accesses to an object having no declared type, the effective type of the object is simply the type of the lvalue used for the access.'
- Chris Hathhorn, Chucky Ellison, Grigore Rosu. Defining the Undefinedness of C. PLDI 2015, pp. 336-345. https://doi.org/10.1145/2737924.2737979 (Section 3.4, paragraph 'Strict Aliasing': declared types are stored with object representations and, for malloc'd memory, the type of the last object stored is tracked, which matches the toy's allocated-storage rule for typed stores; that paragraph does not discuss memcpy or the transfer of effective types by copying).
- Kayvan Memarian, Justus Matthiesen, James Lingard, Kyndylan Nienhuis, David Chisnall, Robert N. M. Watson, Peter Sewell. Into the Depths of C: Elaborating the De Facto Standards. PLDI 2016, pp. 1-15. https://doi.org/10.1145/2908080.2908081 (the gap between ISO C and de facto C practice, including effective types; the Cerberus semantics).
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types.

**Design question.** May a compiler move a typed load above a typed store on the basis of types alone in an effective-type memory model, and which type relation (not mere inequality of types) does that need?

**Non-claims:** see **Boundaries › Non-claims › R1-hoist-load-above-incompatible-store-sound-E**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — The (E) semantics is meant to follow the dynamic reading of ISO C11 6.5p6–7 (N1570): a store through a non-character lvalue into storage with no declared type gives that storage the stored type, a declared object keeps its declared type, and character-type accesses are exempt from the aliasing list; C++ has an analogous list in N4950 [basic.lval] p11 (the dynamic type, its signed or unsigned variant, and char, unsigned char or std::byte). The hypotheses of this theorem (both access types non-character, no common scalar leaf) play the role of the type-disjointness test that type-based alias analysis applies to C and C++ accesses. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C, C++ or LLVM IR is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R1b-sink-load-below-incompatible-store-unsound-E

**Kind:** counterexample. **Tier:** T1. **Depth:** definitional.

**Plain claim.** Under the effective-type semantics with the standard discipline (character exemption), although every hypothesis of R1 holds (u32 and f32 are non-character types with no common leaf, and the registers differ), moving a u32 load below a later f32 store to the same allocated bytes is not a refinement: the f32 store legitimately re-types allocated storage after the load, so in the transformed program the load is undefined. The theorem's statement names no context or initial state; the witness inside its proof is the context [] / [out 1] with the initial state freshAt 0 16 [1,1,1,1], whose bytes 0 to 15 are allocated storage with no effective type yet, and sink_load_below_store_witness_runs states its runs: the source terminates normally, printing the four zero bytes it loaded, while the transformed program stops at a type fault before any output.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:152-154
theorem sink_load_below_store_not_sound_E :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSound (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u32 0] := …
```

**Tier justification.** DR 236 Example 1 describes this reordering on allocated storage in prose (an int load and a later double store; hoisting the store 'changes the computation'); no mechanized statement was found.

**Hypothesis ledger.**

- None: the statement is closed, or universally quantified over all of its inputs with no hypothesis.

**Non-vacuity witness.** The statement is closed and is itself a concrete instance: it instantiates R1's hypotheses at T = u32, U = f32, p = q = 0, s = 1, r = 0 and proves them. The refuting context [] / [out 1] and initial state freshAt 0 16 [1,1,1,1] are witnesses inside the proof, not part of the statement; sink_load_below_store_witness_runs states their runs. (Lean: `sink_load_below_store_not_sound_E`, `sink_load_below_store_witness_runs`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Companions.lean:29-36
theorem sink_load_below_store_witness_runs :
    exec (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) =
      .ub [] ∧
    TypeFaults stdCfg [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) ∧
    ¬ Allows (exec (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0, .out 1] (freshAt 0 16 ones4))
      (exec (stepE stdCfg) [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4)) := by …
```

**Prior art.**

- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').
- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types.
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).

**Design question.** Which TBAA reorderings stop being justified when stores can re-type allocated storage?

**Non-claims:** see **Boundaries › Non-claims › R1b-sink-load-below-incompatible-store-unsound-E**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — The witness program has the shape of WG14 DR 236 Example 1 (an int load followed by a double store to the same allocated storage). In the toy, the literal dynamic re-typing reading of C11 6.5p6 makes the later store re-type the storage, so the sink is not a refinement; the WG14 committee response to DR 236 instead declares such programs undefined, which is a different reading that the toy does not model. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or LLVM IR is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R1c-store-store-swap-unsound-E

**Kind:** counterexample. **Tier:** T1. **Depth:** definitional.

**Plain claim.** Under the effective-type semantics with the standard discipline (character exemption), although both types are non-character and share no leaf, swapping a u32 store and an f32 store to the same allocated bytes is not a refinement: the later store determines both the value and the effective type. The theorem's statement names no context or initial state; the witness inside its proof is the context [] / [load 2 u8 0, out 2] with the initial state (freshAt 0 16 []).withRegs (regs2 [1,1,1,1] [2,2,2,2]), whose bytes 0 to 15 are allocated storage with no effective type yet. store_store_swap_witness_runs states its runs: the byte load observes the value written by the later store (the source prints [2], the swapped program [1]); with the suffix [load 2 f32 0, out 2] instead, the source prints [2,2,2,2], while the swapped program, whose later store is the u32 store, stops at a type fault before any output.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:160-162
theorem store_store_reorder_not_sound_E :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] := …
```

**Tier justification.** DR 236 Example 1 directly illustrates the load/store case (R1b); this store/store swap is the analogous two-store consequence of the same re-typing rule. No mechanized statement was found.

**Hypothesis ledger.**

- None: the statement is closed, or universally quantified over all of its inputs with no hypothesis.

**Non-vacuity witness.** The statement is closed and is itself a concrete instance: it instantiates the type conditions at u32 and f32 (both stores to address 0, from registers 0 and 1) and proves them. The refuting context [] / [load 2 u8 0, out 2] and initial state (freshAt 0 16 []).withRegs (regs2 [1,1,1,1] [2,2,2,2]) are witnesses inside the proof, not part of the statement; store_store_swap_witness_runs states their runs. (Lean: `store_store_reorder_not_sound_E`, `store_store_swap_witness_runs`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Companions.lean:46-56
theorem store_store_swap_witness_runs :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1, .load 2 .u8 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [[2]] ∧
    exec (stepE stdCfg) [.store .f32 0 1, .store .u32 0 0, .load 2 .u8 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [[1]] ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [twos4] ∧
    exec (stepE stdCfg) [.store .f32 0 1, .store .u32 0 0, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .ub [] ∧
    TypeFaults stdCfg [.store .f32 0 1, .store .u32 0 0, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) := by …
```

**Prior art.**

- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').
- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types.
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).

**Design question.** Which TBAA reorderings stop being justified when stores can re-type allocated storage?

**Non-claims:** see **Boundaries › Non-claims › R1c-store-store-swap-unsound-E**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — This is the two-store analogue of the DR 236 Example 1 shape under the literal dynamic re-typing reading of C11 6.5p6 modeled by (E): the later of two stores to allocated storage determines both the stored value and the effective type. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or LLVM IR is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R2-tbaa-hoist-unsound-U

**Kind:** impossibility. **Tier:** T1. **Depth:** shallow.

**Plain claim.** Under the untyped semantics, for all types T and U (with no condition relating them) and every address p: (1) from the witness state uWit U p, the target [load 1 T p, store U p 0, out 1] has the behaviour 'print T.size zero bytes', which the source [store U p 0, load 1 T p, out 1] lacks; and (2) for all registers s and r, hoisting a T-load from p above a U-store to the same address p is not a refinement. Consequently, for every criterion C on pairs of access types: if, whenever C T U holds, this same-address hoist is a refinement under the untyped semantics for every address p and every pair of distinct registers s ≠ r, then C holds for no pair of types (no_type_criterion_licenses_same_addr_hoist_U); and if, whenever C T U holds, the same-address hoist is a refinement under the untyped semantics for at least one address p and one pair of registers s, r, then C holds for no pair of types (no_type_criterion_licenses_same_addr_hoist_U_at_one_site).

**Lean statements** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:210-213
theorem hoist_load_above_store_same_addr_unsound_U (T U : Ty) (p : Nat) :
    (Beh stepU [.load 1 T p, .store U p 0, .out 1] (uWit U p) (.done [List.replicate T.size 0]) ∧
     ¬ Beh stepU [.store U p 0, .load 1 T p, .out 1] (uWit U p) (.done [List.replicate T.size 0])) ∧
    ∀ s r : Reg, ¬ ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:283-286
theorem no_type_criterion_licenses_same_addr_hoist_U (C : Ty → Ty → Prop)
    (hC : ∀ T U p s r, C T U → s ≠ r →
      ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) :
    ∀ T U, ¬ C T U := …
```

```lean
-- lean/ToyTbaa/Results.lean:295-298
theorem no_type_criterion_licenses_same_addr_hoist_U_at_one_site (C : Ty → Ty → Prop)
    (hC : ∀ T U, C T U → ∃ p s r,
      ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) :
    ∀ T U, ¬ C T U := …
```

**Tier justification.** That untyped memory gives no type-based alias facts is folklore (the Rust Reference states its aliasing undefined behaviour in terms of references and Box; LLVM IR memory has no types); made precise here with an explicit witness and a universally quantified refutation.

**Hypothesis ledger.**

- `hC : ∀ T U p s r, C T U → s ≠ r → ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]` (premise of no_type_criterion_licenses_same_addr_hoist_U). *Purpose:* The corollary is about criteria that license the same-address hoist for distinct registers (s ≠ r is the register condition of R1 and R6). Without s ≠ r a premise of this shape would refute every criterion through register clobbering alone, at an address pair where R6 licenses the hoist for distinct registers (same_register_premise_refutes_disjoint_hoist_U). Without the premise the conclusion fails for the criterion that accepts every pair. *Tightness:* tight; counterexample `no_type_criterion_needs_premise`; witness class: the criterion C := fun _ _ => True (the theorem has no other hypothesis).
- `hC : ∀ T U, C T U → ∃ p s r, ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]` (premise of no_type_criterion_licenses_same_addr_hoist_U_at_one_site). *Purpose:* A weaker premise than the previous one (a single licensed address and register pair per accepted pair of types); without it the conclusion fails for the criterion that accepts every pair. *Tightness:* tight; counterexample `no_type_criterion_at_one_site_needs_premise`; witness class: the criterion C := fun _ _ => True (the theorem has no other hypothesis).

**Non-vacuity witness.** T = f32, U = u32, p = 0 (fully proved instance of part (1), hoist_unsound_U_instance). The premises of both corollaries are satisfied by the empty criterion C := fun _ _ => False (no_type_criterion_premises_satisfiable); by the corollaries, every criterion satisfying them holds for no pair of types. (Lean: `hoist_unsound_U_instance`, `no_type_criterion_premises_satisfiable`.)

**Positive control.** `hoist_U_witness_refines_under_E_or_disjoint`: a nearby setting in which the impossibility's conclusion fails (statement quoted below).

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:354-356
theorem hoist_unsound_U_instance :
    Beh stepU [.load 1 .f32 0, .store .u32 0 0, .out 1] (uWit .u32 0) (.done [[0, 0, 0, 0]]) ∧
    ¬ Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (uWit .u32 0) (.done [[0, 0, 0, 0]]) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:346-350
theorem no_type_criterion_premises_satisfiable :
    (∀ T U p s r, (fun _ _ : Ty => False) T U → s ≠ r →
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    (∀ T U, (fun _ _ : Ty => False) T U → ∃ p s r,
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) := …
```

```lean
-- lean/ToyTbaa/Results.lean:363-367
theorem hoist_U_witness_refines_under_E_or_disjoint :
    Refines (Beh (stepE stdCfg) [.load 1 .f32 0, .store .u32 0 0, .out 1] (freshAt 0 16 ones4))
            (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4)) ∧
    Refines (Beh stepU [.load 1 .f32 8, .store .u32 0 0, .out 1] (uWit .u32 0))
            (Beh stepU [.store .u32 0 0, .load 1 .f32 8, .out 1] (uWit .u32 0)) := …
```

```lean
-- lean/ToyTbaa/Results.lean:307-310
theorem no_type_criterion_needs_premise :
    ¬ (∀ T U p s r, (fun _ _ : Ty => True) T U → s ≠ r →
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    ¬ (∀ T U : Ty, ¬ (fun _ _ : Ty => True) T U) := …
```

```lean
-- lean/ToyTbaa/Results.lean:318-321
theorem no_type_criterion_at_one_site_needs_premise :
    ¬ (∀ T U, (fun _ _ : Ty => True) T U → ∃ p s r,
        ReorderSound stepU [.store U p r, .load s T p] [.load s T p, .store U p r]) ∧
    ¬ (∀ T U : Ty, ¬ (fun _ _ : Ty => True) T U) := …
```

**Prior art.**

- The Rust Reference, 'Behavior considered undefined', rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, file src/behavior-considered-undefined.md (rule undefined.alias states the aliasing rules in terms of &T, &mut T and Box<T>, with no type-based rule; rule undefined.validity.scalar requires integers and floats to be initialized).
- Rust Unsafe Code Guidelines, glossary, rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce, file reference/src/glossary.md (entry 'Abstract Byte': an abstract byte is Uninit or Init(u8, Option<Provenance>), so the per-byte shadow state is initialization and provenance, not a type; entry 'Aliasing', line 90: 'Zero Sized Types _never_ alias each other, because their span length is always 0').
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types.
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. POPL 2020. https://doi.org/10.1145/3371109 (aliasing rules for Rust references over untyped memory, independent of types).
- Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. PLDI 2025. https://doi.org/10.1145/3735592 (a successor aliasing model for Rust references).

**Design question.** Can a language with untyped memory and byte-level reinterpretation (transmute, zerocopy-style casts) use type-based alias analysis at all?

**Non-claims:** see **Boundaries › Non-claims › R2-tbaa-hoist-unsound-U**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — The (U) semantics is meant to capture memory in which bytes carry no type: LLVM IR memory (LangRef at the pinned commit: 'In LLVM IR, memory does not have types'), and Rust, whose Reference states its aliasing undefined behaviour in terms of &T, &mut T and Box<T> with no type-based rule and whose abstract bytes carry initialization and provenance rather than a type (Unsafe Code Guidelines glossary). The theorem shows, for the toy, that no criterion on the pair of access types licenses the same-address hoist. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and LLVM IR or Rust is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R3a-memcpy-then-typed-load-defined-E

**Kind:** characterization. **Tier:** T1. **Depth:** shallow.

**Plain claim.** Under the effective-type semantics with the standard discipline, for every state σ, type T, source p, destination q (overlapping ranges allowed) and register s: memcpy q p T.size followed by a T-load from q and out s terminates normally, printing exactly the bytes that were at p, if and only if MemcpyLoadOk σ T p q holds (both ranges allocated, and at each byte offset i the leaf T.leafAt i is compatible with the destination byte's declared leaf if that byte belongs to a declared object, and with the source byte's tag otherwise). Corollary: if a T-load from p would pass the checks (ReadableAt) and the destination range is allocated and its declared bytes accept T (ReceivesAt), the copy-then-load is defined and returns the bytes at p.

**Lean statements** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:378-380
theorem memcpy_then_typed_load_defined_E_iff (σ : St) (T : Ty) (p q : Nat) (s : Reg) :
    exec (stepE stdCfg) [.memcpy q p T.size, .load s T q, .out s] σ = .done [valsAt σ p T.size] ↔
      MemcpyLoadOk σ T p q := by …
```

```lean
-- lean/ToyTbaa/Results.lean:420-422
theorem memcpy_then_typed_load_defined_E_of_readable_of_receives (σ : St) (T : Ty) (p q : Nat)
    (s : Reg) (hsrc : ReadableAt stdCompat σ T p) (hdst : ReceivesAt σ T q) :
    exec (stepE stdCfg) [.memcpy q p T.size, .load s T q, .out s] σ = .done [valsAt σ p T.size] := by …
```

**Tier justification.** C11 6.5p6 (third sentence) states the effective-type transfer by memcpy into storage with no declared type in prose; the exact per-byte condition for a copy followed by a typed load is made precise here. No mechanized statement was found.

**Hypothesis ledger.**

- `hsrc : ReadableAt stdCompat σ T p` (hypothesis of the corollary). *Purpose:* Allocated destination bytes receive the source's tags, so the source bytes must be readable at T. *Tightness:* tight; counterexample `memcpy_then_load_needs_readable_source`; witness class: an f32 object (objSt f32) copied to untyped allocated storage at 8 and loaded at u32.
- `hdst : ReceivesAt σ T q` (hypothesis of the corollary). *Purpose:* A declared destination keeps its declared type; if that type rejects T the load faults. *Tightness:* tight; counterexample `memcpy_then_load_needs_receiving_destination`; witness class: a u32 object copied into a declared f32 object at 8 and loaded at u32.

**Non-vacuity witness.** Both sides of the characterization are inhabited: copying the u32 object of objSt u32 into untyped storage, and memcpy punning of an f32 object into a declared u32 object, satisfy MemcpyLoadOk and run to completion; copying an f32 object into allocated storage and loading it at u32 violates MemcpyLoadOk and is undefined (memcpy_then_load_nonvacuous). The corollary's hypotheses hold for objSt u32 (memcpy_corollary_nonvacuous). (Lean: `memcpy_then_load_nonvacuous`, `memcpy_corollary_nonvacuous`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:446-453
theorem memcpy_then_load_nonvacuous :
    MemcpyLoadOk (objSt .u32) .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .u32) = .done [[0, 0, 0, 0]] ∧
    MemcpyLoadOk Examples.punIntoDeclSt .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] Examples.punIntoDeclSt =
      .done [[1, 1, 1, 1]] ∧
    ¬ MemcpyLoadOk (objSt .f32) .u32 0 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .f32) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:458-459
theorem memcpy_corollary_nonvacuous :
    ReadableAt stdCompat (objSt .u32) .u32 0 ∧ ReceivesAt (objSt .u32) .u32 8 := by …
```

```lean
-- lean/ToyTbaa/Results.lean:472-475
theorem memcpy_then_load_needs_readable_source :
    ¬ ReadableAt stdCompat (objSt .f32) .u32 0 ∧ ReceivesAt (objSt .f32) .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] (objSt .f32) ≠
      .done [valsAt (objSt .f32) 0 4] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:487-490
theorem memcpy_then_load_needs_receiving_destination :
    ReadableAt stdCompat copyIntoDeclF32 .u32 0 ∧ ¬ ReceivesAt copyIntoDeclF32 .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] copyIntoDeclF32 ≠
      .done [valsAt copyIntoDeclF32 0 4] := by …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- ISO/IEC 9899:201x Committee Draft N1570, section 6.5 paragraph 6 (text checked at http://port70.net/~nsz/c/c11/n1570.html#6.5p6): a non-character store into an object with no declared type sets its effective type 'for that access and for subsequent accesses that do not modify the stored value'; 'For all other accesses to an object having no declared type, the effective type of the object is simply the type of the lvalue used for the access.'
- C++ working draft N4950 (2023-05-10), [cstring.syn] paragraph 3 ('Both functions implicitly create objects ([intro.object]) in the destination region of storage immediately prior to copying the sequence of characters to the destination.') and [intro.object] paragraph 10 (implicit object creation 'if doing so would result in the program having defined behavior'); checked at https://timsong-cpp.github.io/cppwp/n4950/cstring.syn and .../intro.object.
- Chris Hathhorn, Chucky Ellison, Grigore Rosu. Defining the Undefinedness of C. PLDI 2015, pp. 336-345. https://doi.org/10.1145/2737924.2737979 (Section 3.4, paragraph 'Strict Aliasing': declared types are stored with object representations and, for malloc'd memory, the type of the last object stored is tracked, which matches the toy's allocated-storage rule for typed stores; that paragraph does not discuss memcpy or the transfer of effective types by copying).
- Harvey Tuch, Gerwin Klein, Michael Norrish. Types, Bytes, and Separation Logic. POPL 2007, pp. 97-108. https://doi.org/10.1145/1190216.1190234 (Isabelle/HOL: typed heap views lifted from an untyped byte-level C memory).
- Kayvan Memarian, Justus Matthiesen, James Lingard, Kyndylan Nienhuis, David Chisnall, Robert N. M. Watson, Peter Sewell. Into the Depths of C: Elaborating the De Facto Standards. PLDI 2016, pp. 1-15. https://doi.org/10.1145/2908080.2908081 (the gap between ISO C and de facto C practice, including effective types; the Cerberus semantics).
- ISO/IEC 9899:201x Committee Draft N1570, section 7.24.2.1 paragraph 2 (memcpy: 'If copying takes place between objects that overlap, the behavior is undefined.') and section 7.24.2.2 paragraph 2 (memmove: 'Copying takes place as if the n characters from the object pointed to by s2 are first copied into a temporary array of n characters that does not overlap the objects pointed to by s1 and s2, and then the n characters from the temporary array are copied into the object pointed to by s1.'); text checked at http://port70.net/~nsz/c/c11/n1570.html#7.24.2.1.

**Design question.** When is a memcpy of a typed object followed by a typed load of the copy defined under effective types, and how do the tag transfer of memcpy and declared destinations (memcpy punning) enter?

**Non-claims:** see **Boundaries › Non-claims › R3a-memcpy-then-typed-load-defined-E**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — C11 6.5p6 (third sentence) states that copying into an object with no declared type using memcpy or memmove gives the destination the effective type of the source; the toy's memcpy copies per-byte tags into allocated storage and leaves declared bytes' types unchanged, and MemcpyLoadOk is the per-byte condition that results for a copy followed by a typed load. C++ instead specifies implicit object creation by memcpy (N4950 [cstring.syn] p3), which the toy does not model. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or C++ is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R3b-byte-copy-defined-forces-byte-tbaa-unsound

**Kind:** impossibility. **Tier:** T1. **Depth:** definitional.

**Plain claim.** For every compatibility discipline c with memcpy performing its byte accesses under c, and every type T: if byte-wise copying the T-object of objSt T (to the untyped storage at address 8) is defined, then, from the initial state objSt T with suffix [out 1], moving a byte (u8) load of address 0 above a T-store to address 0 is not a refinement. For T ≠ u8 this is the cross-type reading: a discipline cannot both make the byte-access copy defined and make byte loads non-aliasing with T stores; for T = u8 the refuted reordering is a same-type u8/u8 one.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:525-528
theorem byte_copy_defined_forces_byte_hoist_unsound (c : Compat) (T : Ty)
    (hcopy : exec (stepE ⟨c, true⟩) [.memcpy 8 0 T.size] (objSt T) = .done []) :
    ¬ Refines (Beh (stepE ⟨c, true⟩) [.load 1 .u8 0, .store T 0 0, .out 1] (objSt T))
              (Beh (stepE ⟨c, true⟩) [.store T 0 0, .load 1 .u8 0, .out 1] (objSt T)) := by …
```

**Tier justification.** That the character-type exemption exists so that objects can be copied byte-wise, and that it costs alias precision for character accesses, is folklore around C11 6.5p7's last item; made precise here as a witness-level dichotomy over all compatibility disciplines.

**Hypothesis ledger.**

- `hcopy : exec (stepE ⟨c, true⟩) [memcpy 8 0 T.size] (objSt T) = done []`. *Purpose:* The byte-access copy is defined, which forces c to admit u8 reads of every leaf of T, so the source's byte load after the T-store is defined and sees the new byte. *Tightness:* tight; counterexample `strict_copy_ub_and_byte_hoist_refines`; witness class: c = strictCompat, T = u32: the copy is undefined and the hoist is a refinement at the witnesses.
- `memcpyChecksBytes = true` (the configuration ⟨c, true⟩). *Purpose:* The copy is made of u8 accesses checked by c. With a copy primitive that bypasses the checks, the strict discipline has a defined copy and a sound byte hoist at the same witnesses. *Tightness:* tight; counterexample `byte_hoist_refines_with_unchecked_memcpy`; witness class: c = strictCompat, T = u32, memcpy unchecked: the copy is defined and the hoist is a refinement.

**Non-vacuity witness.** With the standard discipline the copies of the u32 and pair objects are defined (byte_copy_defined_nonvacuous). (Lean: `byte_copy_defined_nonvacuous`.)

**Positive control.** `byte_hoist_refines_with_unchecked_memcpy`: a nearby setting in which the impossibility's conclusion fails (statement quoted below).

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:541-543
theorem byte_copy_defined_nonvacuous :
    exec (stepE stdCfg) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .done [] ∧
    exec (stepE stdCfg) [.memcpy 8 0 Ty.pair.size] (objSt .pair) = .done [] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:548-551
theorem byte_hoist_refines_with_unchecked_memcpy :
    exec (stepE ⟨strictCompat, false⟩) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .done [] ∧
    Refines (Beh (stepE ⟨strictCompat, false⟩) [.load 1 .u8 0, .store .u32 0 0, .out 1] (objSt .u32))
            (Beh (stepE ⟨strictCompat, false⟩) [.store .u32 0 0, .load 1 .u8 0, .out 1] (objSt .u32)) := …
```

```lean
-- lean/ToyTbaa/Results.lean:556-559
theorem strict_copy_ub_and_byte_hoist_refines :
    exec (stepE ⟨strictCompat, true⟩) [.memcpy 8 0 Ty.u32.size] (objSt .u32) = .ub [] ∧
    Refines (Beh (stepE ⟨strictCompat, true⟩) [.load 1 .u8 0, .store .u32 0 0, .out 1] (objSt .u32))
            (Beh (stepE ⟨strictCompat, true⟩) [.store .u32 0 0, .load 1 .u8 0, .out 1] (objSt .u32)) := …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).

**Design question.** Is the character-type exemption avoidable, i.e. can byte-wise copying be defined while byte accesses remain disjoint from typed accesses for alias analysis?

**Non-claims:** see **Boundaries › Non-claims › R3b-byte-copy-defined-forces-byte-tbaa-unsound**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — In C11 the last item of the 6.5p7 aliasing list (a character type) and in C++ item (11.3) of N4950 [basic.lval] p11 (char, unsigned char, std::byte) allow byte-wise access to any object, which is what makes byte-wise copying of objects defined. The toy has a single byte type (u8), and the theorem quantifies over every compatibility discipline of the toy. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or C++ is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R4a-no-type-fault-implies-E-equals-U

**Kind:** theorem. **Tier:** T1. **Depth:** shallow.

**Plain claim.** For every configuration cfg, program P and initial state σ: if the effective-type execution of P from σ under cfg does not stop at a type fault (¬ TypeFaults cfg P σ), then its behaviours equal those of the untyped execution of P from erase σ.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:603-605
theorem behE_eq_behU_of_not_typeFaults (cfg : ECfg) (P : List Instr) (σ : St)
    (h : ¬ TypeFaults cfg P σ) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) := …
```

Unfolded rendering of `behE_eq_behU_of_not_typeFaults` after the binders `cfg P σ` (`TypeFaults` and `Beh` unfolded; checked to be definitionally equal to the statement):

```lean
¬ typeFaultsB cfg P σ = true →
  Allows (exec (stepE cfg) P σ) = Allows (exec stepU P (erase σ))
```

**Tier justification.** That effective types add undefined behaviour and remove no untyped behaviour (R4b; so programs without effective-type violations behave the same on untyped memory) is folklore; Tuch, Klein and Norrish relate typed and untyped byte-level views in another formalism. Made precise here as an exact equality of behaviour sets.

**Hypothesis ledger.**

- `h : ¬ TypeFaults cfg P σ`. *Purpose:* A type fault makes the (E) run undefined where the (U) run continues. *Tightness:* tight; counterexample `agreement_needs_no_type_fault`; witness class: the program [store u32 0 0, load 1 f32 0, out 1] from untyped allocated storage, cfg = stdCfg.

**Non-vacuity witness.** A program that reads a u32 object bytewise does not type-fault, and its two behaviour sets coincide. (Lean: `behE_eq_behU_nonvacuous`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:610-613
theorem behE_eq_behU_nonvacuous :
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) =
      Beh stepU [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) := …
```

```lean
-- lean/ToyTbaa/Results.lean:618-621
theorem agreement_needs_no_type_fault :
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ≠
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) := by …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- Harvey Tuch, Gerwin Klein, Michael Norrish. Types, Bytes, and Separation Logic. POPL 2007, pp. 97-108. https://doi.org/10.1145/1190216.1190234 (Isabelle/HOL: typed heap views lifted from an untyped byte-level C memory).
- Kayvan Memarian, Justus Matthiesen, James Lingard, Kyndylan Nienhuis, David Chisnall, Robert N. M. Watson, Peter Sewell. Into the Depths of C: Elaborating the De Facto Standards. PLDI 2016, pp. 1-15. https://doi.org/10.1145/2908080.2908081 (the gap between ISO C and de facto C practice, including effective types; the Cerberus semantics).

**Design question.** Which programs behave the same under effective-type and untyped memory, i.e. what does a type-based memory model forbid beyond an untyped one?

**Non-claims:** see **Boundaries › Non-claims › R4a-no-type-fault-implies-E-equals-U**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Reading (E) as C-like effective-type execution and (U) as execution on untyped memory (for example code compiled without type-based alias assumptions), the theorem is a toy counterpart of the folklore that a program without effective-type violations behaves the same on untyped memory. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C, LLVM IR or machine code is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R4b-untyped-run-refines-effective-type-run

**Kind:** theorem. **Tier:** T1. **Depth:** shallow.

**Plain claim.** For every configuration cfg, program P and initial state σ, every behaviour of the untyped execution of P from erase σ is a behaviour of the effective-type execution of P from σ under cfg. Moreover (behE_not_refines_behU_iff), for every cfg, P and σ, the converse inclusion (every behaviour of the effective-type execution is a behaviour of the untyped execution) fails if and only if the effective-type execution stops at a type fault (TypeFaults cfg P σ) and, in addition, the untyped execution from erase σ either terminates normally (UDefined P (erase σ)) or has a strictly longer output trace than the effective-type execution.

**Lean statements** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:644-645
theorem behU_erase_refines_behE (cfg : ECfg) (P : List Instr) (σ : St) :
    Refines (Beh stepU P (erase σ)) (Beh (stepE cfg) P σ) := …
```

```lean
-- lean/ToyTbaa/Results.lean:722-726
theorem behE_not_refines_behU_iff (cfg : ECfg) (P : List Instr) (σ : St) :
    ¬ Refines (Beh (stepE cfg) P σ) (Beh stepU P (erase σ)) ↔
      TypeFaults cfg P σ ∧
        (UDefined P (erase σ) ∨
         (exec (stepE cfg) P σ).trace.length < (exec stepU P (erase σ)).trace.length) := by …
```

**Tier justification.** Folklore (effective types add undefined behaviour and remove no untyped behaviour); made precise here as a refinement for every configuration, program and state, together with the exact condition under which the converse inclusion fails.

**Hypothesis ledger.**

- None: the statement is closed, or universally quantified over all of its inputs with no hypothesis.

**Non-vacuity witness.** No hypotheses. An instance where the inclusion is strict is behU_refines_behE_strict_instance; both sides of the converse characterization occur: behE_not_refines_behU_of_uDefined_nonvacuous (a type-faulting program with a defined untyped run, where the converse fails, and a byte-reading program, where it holds), behE_not_refines_behU_without_uDefined (the converse fails through the trace-length disjunct) and behE_refines_behU_masked_instance (a type-faulting program for which the converse holds). (Lean: `behU_refines_behE_strict_instance`, `behE_not_refines_behU_of_uDefined_nonvacuous`, `behE_not_refines_behU_without_uDefined`, `behE_refines_behU_masked_instance`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:649-653
theorem behU_refines_behE_strict_instance :
    Refines (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)))
            (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4)) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4))
              (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4))) := …
```

```lean
-- lean/ToyTbaa/Results.lean:790-798
theorem behE_not_refines_behU_of_uDefined_nonvacuous :
    UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4))) ∧
    UDefined [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) ∧
    Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4))) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:809-818
theorem behE_not_refines_behU_without_uDefined :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    ¬ Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
                (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100]
                (erase (freshAt 0 16 ones4))) ∧
    ¬ (∀ (cfg : ECfg) (Q : List Instr) (s : St),
        ¬ Refines (Beh (stepE cfg) Q s) (Beh stepU Q (erase s)) ↔
          (TypeFaults cfg Q s ∧ UDefined Q (erase s))) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:830-834
theorem behE_refines_behU_masked_instance :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Refines (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4))
        (Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4))) := by …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types.
- Harvey Tuch, Gerwin Klein, Michael Norrish. Types, Bytes, and Separation Logic. POPL 2007, pp. 97-108. https://doi.org/10.1145/1190216.1190234 (Isabelle/HOL: typed heap views lifted from an untyped byte-level C memory).

**Design question.** Is running an effective-type program on untyped memory, with no type-based alias metadata, always a refinement?

**Non-claims:** see **Boundaries › Non-claims › R4b-untyped-run-refines-effective-type-run**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Reading (E) as C-like effective-type execution and (U) as execution on untyped memory without type-based alias metadata, the refinement is a toy counterpart of the folklore that running an effective-type program on untyped memory is a correct implementation of it. It does not cover LLVM IR with '!tbaa' metadata, whose access-pair rule is different (see the non-claims). Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C, LLVM IR or machine code is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R4c-agreement-iff-no-type-fault-given-U-defined

**Kind:** characterization. **Tier:** T1. **Depth:** shallow.

**Plain claim.** For every configuration cfg, program P and initial state σ, if the untyped execution of P from erase σ terminates normally (UDefined), then the behaviours under (E) and (U) coincide if and only if the (E) execution does not stop at a type fault.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:659-661
theorem behE_eq_behU_iff_not_typeFaults_of_uDefined (cfg : ECfg) (P : List Instr) (σ : St)
    (hU : UDefined P (erase σ)) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) ↔ ¬ TypeFaults cfg P σ := by …
```

**Tier justification.** Folklore boundary made precise; the definedness side condition is new to this statement and tight.

**Hypothesis ledger.**

- `hU : UDefined P (erase σ)`. *Purpose:* Without it, a type fault can be masked by a later base fault of the untyped run with the same trace. *Tightness:* tight; counterexample `typeFault_masked_by_later_base_fault`; witness class: the program [store u32 0 0, load 1 f32 0, load 2 u8 100] from untyped allocated storage (no out between the type fault and the base fault).

**Non-vacuity witness.** Both sides occur with a defined untyped run: a type-faulting program and a byte-reading program that does not type-fault. (Lean: `behE_eq_behU_iff_nonvacuous`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:676-680
theorem behE_eq_behU_iff_nonvacuous :
    UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) ∧
    UDefined [.store .u32 0 0, .load 1 .u8 0, .out 1] (erase (freshAt 0 16 ones4)) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:686-693
theorem typeFault_masked_by_later_base_fault :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) =
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    ¬ (Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4) =
        Beh stepU [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ↔
       ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .load 2 .u8 100] (freshAt 0 16 ones4)) := by …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).

**Design question.** Which programs behave the same under effective-type and untyped memory?

**Non-claims:** see **Boundaries › Non-claims › R4c-agreement-iff-no-type-fault-given-U-defined**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Same reading as R4a and R4b: (E) as C-like effective-type execution, (U) as untyped execution. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C, LLVM IR or machine code is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R5a-store-store-swap-sound-E-declared

**Kind:** theorem. **Tier:** T1. **Depth:** shallow.

**Plain claim.** Under the effective-type semantics with the standard discipline, if T is not u8, U is not u8, and T and U share no leaf, then swapping a T-store to p and a U-store to q is a refinement in every context and from every initial state in which every allocated byte of [p, p + T.size) belongs to a declared object.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:844-847
theorem store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8 (T U : Ty) (p q : Nat)
    (a b : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) :
    ReorderSoundFrom (fun σ => DeclaredOn σ p T.size) (stepE stdCfg)
      [.store T p a, .store U q b] [.store U q b, .store T p a] := by …
```

Unfolded rendering of `store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8` after its binders (`ReorderSoundFrom`, `DeclaredOn`, `Refines` and `Beh` unfolded; checked to be definitionally equal to the statement):

```lean
∀ (pre post : List Instr) (σ : St),
  (∀ i, i < T.size → (σ.mem (p + i)).all (fun cell => cell.eff.isDecl) = true) →
  ∀ o : Outcome,
    Allows (exec (stepE stdCfg) (pre ++ [Instr.store U q b, Instr.store T p a] ++ post) σ) o →
    Allows (exec (stepE stdCfg) (pre ++ [Instr.store T p a, Instr.store U q b] ++ post) σ) o
```

**Tier justification.** Follows the C11 rule that declared objects keep their declared type (6.5p6, first sentence); not found mechanized as a reordering statement.

**Hypothesis ledger.**

- `Pre : DeclaredOn σ p T.size`. *Purpose:* Declared bytes keep their type, so overlapping stores of types without a common leaf cannot both succeed; on allocated storage the swap changes the final value and type (R1c). *Tightness:* tight; counterexample `store_store_needs_declared_storage`; witness class: overlapping addresses p = q = 0 on untyped allocated storage (where DeclaredOn fails), T = u32, U = f32.
- `hT : T ≠ Ty.u8`. *Purpose:* A byte store into a declared object is allowed and changes the value. *Tightness:* tight; counterexample `store_store_declared_needs_first_ne_u8`; witness class: overlapping addresses p = q = 0 in a declared f32 object, T = u8, U = f32.
- `hU : U ≠ Ty.u8`. *Purpose:* Symmetric to hT. *Tightness:* tight; counterexample `store_store_declared_needs_second_ne_u8`; witness class: overlapping addresses p = q = 0 in a declared f32 object, T = f32, U = u8.
- `hTU : NoCommonLeaf T U`. *Purpose:* A struct store and a member store to the same declared struct both succeed. *Tightness:* tight; counterexample `store_store_declared_needs_noCommonLeaf`; witness class: overlapping addresses p = q = 0 in a declared pair object, T = pair, U = u32.

**Non-vacuity witness.** Scalar instance T = u32 at 0, U = f32 at 4 in a declared pair object, and struct instance T = pair at 0 (declared), U = u16 at 8: the hypotheses hold and the source block is defined. (Lean: `store_store_declared_nonvacuous`, `store_store_declared_nonvacuous_struct`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:895-899
theorem store_store_declared_nonvacuous :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    DeclaredOn ((declPairSt []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((declPairSt []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:908-912
theorem store_store_declared_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧
    DeclaredOn (declPairThenFresh (regs2 (List.replicate 8 1) [2, 2])) 0 8 ∧
    exec (stepE stdCfg) [.store .pair 0 0, .store .u16 8 1, .load 2 .u8 0, .out 2]
      (declPairThenFresh (regs2 (List.replicate 8 1) [2, 2])) = .done [[1]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:917-920
theorem store_store_needs_declared_storage :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧
    ¬ DeclaredOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:925-928
theorem store_store_declared_needs_first_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u8 .f32 ∧ DeclaredOn ((declSt .f32 4 []).withRegs (regs2 [1] twos4)) 0 1 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u8.size) (stepE stdCfg)
        [.store .u8 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u8 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:935-938
theorem store_store_declared_needs_second_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .f32 .u8 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.f32.size) (stepE stdCfg)
        [.store .f32 0 0, .store .u8 0 1] [.store .u8 0 1, .store .f32 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:946-949
theorem store_store_declared_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.pair.size) (stepE stdCfg)
        [.store .pair 0 0, .store .u32 0 1] [.store .u32 0 1, .store .pair 0 0] := …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).

**Design question.** Does declared storage license more TBAA reorderings than allocated storage, and which?

**Non-claims:** see **Boundaries › Non-claims › R5a-store-store-swap-sound-E-declared**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — C11 6.5p6 (first sentence): the effective type of an object for an access to its stored value is the declared type of the object, if any. The toy's declared bytes keep their leaf type, which is the property this theorem uses. Toy declared objects have no lifetime end, unlike C objects with automatic storage duration or C++ objects whose storage is reused. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or C++ is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R5b-sink-load-below-store-sound-E-declared

**Kind:** theorem. **Tier:** T1. **Depth:** shallow.

**Plain claim.** Under the effective-type semantics with the standard discipline, if T is not u8, U is not u8, T and U share no leaf, and the load's destination register differs from the store's source register, then moving a T-load from p below a later U-store to q (sink) is a refinement in every context and from every initial state in which every allocated byte of [p, p + T.size) belongs to a declared object.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1048-1051
theorem sink_load_below_store_sound_E_of_declared_of_noCommonLeaf_of_ne_u8 (T U : Ty) (p q : Nat)
    (s r : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSoundFrom (fun σ => DeclaredOn σ p T.size) (stepE stdCfg)
      [.load s T p, .store U q r] [.store U q r, .load s T p] := by …
```

**Tier justification.** Follows the C11 rule that declared objects keep their declared type (6.5p6, first sentence); not found mechanized as a reordering statement.

**Hypothesis ledger.**

- `Pre : DeclaredOn σ p T.size`. *Purpose:* On allocated storage the later store re-types the bytes, so after the sink the load is undefined (R1b). *Tightness:* tight; counterexample `sink_needs_declared_storage`; witness class: overlapping addresses p = q = 0 on untyped allocated storage (where DeclaredOn fails), T = u32, U = f32.
- `hT : T ≠ Ty.u8`. *Purpose:* A byte load of a declared object is allowed and sees the new value after the sink. *Tightness:* tight; counterexample `sink_declared_needs_load_ne_u8`; witness class: overlapping addresses p = q = 0 in a declared f32 object, T = u8, U = f32.
- `hU : U ≠ Ty.u8`. *Purpose:* A byte store into a declared object is allowed and changes the value. *Tightness:* tight; counterexample `sink_declared_needs_store_ne_u8`; witness class: overlapping addresses p = q = 0 in a declared f32 object, T = f32, U = u8.
- `hTU : NoCommonLeaf T U`. *Purpose:* A struct load can read a member just stored. *Tightness:* tight; counterexample `sink_declared_needs_noCommonLeaf`; witness class: overlapping addresses p = q = 0 in a declared pair object, T = pair, U = u32.
- `hsr : s ≠ r`. *Purpose:* Register data dependence. *Tightness:* tight; counterexample `sink_declared_needs_distinct_registers`; witness class: disjoint addresses p = 4, q = 0 in a declared pair object, s = r = 0, T = f32, U = u32.

**Non-vacuity witness.** Scalar instance T = f32 at 4, U = u32 at 0 in a declared pair object, and struct instance T = pair at 0 (declared), U = u16 at 8: the hypotheses hold and the source block is defined. (Lean: `sink_declared_nonvacuous`, `sink_declared_nonvacuous_struct`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1094-1098
theorem sink_declared_nonvacuous :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declPairSt ones4) 4 4 ∧
    exec (stepE stdCfg) [.load 1 .f32 4, .store .u32 0 0, .out 1] (declPairSt ones4) =
      .done [[0, 0, 0, 0]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1101-1105
theorem sink_declared_nonvacuous_struct :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ (1 : Reg) ≠ 0 ∧
    DeclaredOn (declPairThenFresh (fun _ => [2, 2])) 0 8 ∧
    exec (stepE stdCfg) [.load 1 .pair 0, .store .u16 8 0, .out 1]
      (declPairThenFresh (fun _ => [2, 2])) = .done [[0, 0, 0, 0, 0, 0, 0, 0]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1110-1113
theorem sink_needs_declared_storage :
    Ty.u32 ≠ .u8 ∧ Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u32 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ DeclaredOn (freshAt 0 16 ones4) 0 4 ∧
    ¬ ReorderSound (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u32 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:1118-1121
theorem sink_declared_needs_load_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .u8 .f32 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.u8.size) (stepE stdCfg)
        [.load 1 .u8 0, .store .f32 0 0] [.store .f32 0 0, .load 1 .u8 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:1127-1130
theorem sink_declared_needs_store_ne_u8 :
    Ty.f32 ≠ .u8 ∧ NoCommonLeaf .f32 .u8 ∧ (1 : Reg) ≠ 0 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.f32.size) (stepE stdCfg)
        [.load 1 .f32 0, .store .u8 0 0] [.store .u8 0 0, .load 1 .f32 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:1136-1139
theorem sink_declared_needs_noCommonLeaf :
    Ty.pair ≠ .u32 ∧ Ty.pair ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ (1 : Reg) ≠ 0 ∧ ¬ NoCommonLeaf .pair .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 Ty.pair.size) (stepE stdCfg)
        [.load 1 .pair 0, .store .u32 0 0] [.store .u32 0 0, .load 1 .pair 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:1146-1149
theorem sink_declared_needs_distinct_registers :
    Ty.f32 ≠ .u8 ∧ Ty.u32 ≠ .u8 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 4 Ty.f32.size) (stepE stdCfg)
        [.load 0 .f32 4, .store .u32 0 0] [.store .u32 0 0, .load 0 .f32 4] := …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).

**Design question.** Does declared storage license more TBAA reorderings than allocated storage, and which?

**Non-claims:** see **Boundaries › Non-claims › R5b-sink-load-below-store-sound-E-declared**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Same modeling of declared objects as R5a (C11 6.5p6, first sentence; no lifetime end in the toy). Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or C++ is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R5c-store-swap-scheme-sound-on-declared-not-on-allocated

**Kind:** theorem. **Tier:** T1. **Depth:** definitional.

**Plain claim.** Under the effective-type semantics with the standard discipline, for the address-parametric scheme 'swap a u32 store to p and an f32 store to q': (1) for all p and q, the swap is a refinement in every context from every initial state in which every allocated byte of [p, p + 4) belongs to a declared object; (2) it is not the case that, for all p and q, the swap is a refinement in every context from every initial state in which every allocated byte of [p, p + 4) is allocated storage (it fails at p = q = 0, a site that the theorem's statement does not name; store_swap_scheme_fails_at_zero states that it is not the case that, at p = q = 0, the swap is a refinement in every context from every initial state in which every allocated byte of [0, 4) is allocated storage).

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1248-1252
theorem store_swap_scheme_sound_on_declared_not_on_allocated :
    (∀ p q, ReorderSoundFrom (fun σ => DeclaredOn σ p 4) (stepE stdCfg)
        [.store .u32 p 0, .store .f32 q 1] [.store .f32 q 1, .store .u32 p 0]) ∧
    ¬ (∀ p q, ReorderSoundFrom (fun σ => AllocatedOn σ p 4) (stepE stdCfg)
        [.store .u32 p 0, .store .f32 q 1] [.store .f32 q 1, .store .u32 p 0]) := …
```

**Tier justification.** Combines R5a and R1c into a statement about one reordering scheme; not found mechanized.

**Hypothesis ledger.**

- None: the statement is closed, or universally quantified over all of its inputs with no hypothesis.

**Non-vacuity witness.** At p = 0, q = 4 a declared pair object satisfies the declared precondition and the scheme's source block is defined; at p = q = 0 untyped allocated storage satisfies the allocated precondition (store_swap_scheme_nonvacuous). (Lean: `store_swap_scheme_nonvacuous`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1261-1265
theorem store_swap_scheme_nonvacuous :
    DeclaredOn ((declPairSt []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 1, .load 2 .pair 0, .out 2]
      ((declPairSt []).withRegs (regs2 ones4 twos4)) = .done [ones4 ++ twos4] ∧
    AllocatedOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 := by …
```

```lean
-- lean/ToyTbaa/Companions.lean:62-65
theorem store_swap_scheme_fails_at_zero :
    AllocatedOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    ¬ ReorderSoundFrom (fun σ => AllocatedOn σ 0 4) (stepE stdCfg)
        [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] := …
```

**Prior art.**

- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').

**Design question.** Does declared storage license more TBAA reorderings than allocated storage, and which?

**Non-claims:** see **Boundaries › Non-claims › R5c-store-swap-scheme-sound-on-declared-not-on-allocated**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Same modeling of declared objects and allocated storage as R5a and R1c (C11 6.5p6). Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and C or C++ is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### R6-disjoint-ranges-hoist-sound-U

**Kind:** theorem. **Tier:** T0. **Depth:** shallow.

**Plain claim.** Under the untyped semantics, if the address ranges [p, p + T.size) and [q, q + U.size) are disjoint and the load's destination register differs from the store's source register, then moving a T-load from p above a U-store to q is a refinement in every context and from every initial state. No type hypothesis is involved.

**Lean statement** (verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1340-1342
theorem hoist_load_above_store_sound_U_of_disjoint_ranges (T U : Ty) (p q : Nat) (s r : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) (hsr : s ≠ r) :
    ReorderSound stepU [.store U q r, .load s T p] [.load s T p, .store U q r] := by …
```

Unfolded rendering of `hoist_load_above_store_sound_U_of_disjoint_ranges` after its binders (`ReorderSound`, `ReorderSoundFrom`, `Refines` and `Beh` unfolded; checked to be definitionally equal to the statement):

```lean
∀ (pre post : List Instr) (u : USt), True →
  ∀ o : Outcome,
    Allows (exec stepU (pre ++ [Instr.load s T p, Instr.store U q r] ++ post) u) o →
    Allows (exec stepU (pre ++ [Instr.store U q r, Instr.load s T p] ++ post) u) o
```

**Tier justification.** Commuting accesses to disjoint byte ranges over untyped memory is mechanized in CompCert's memory model (Coq, Theorem load_store_other); restated here as a contextual refinement for the load-hoisting transformation.

**Hypothesis ledger.**

- `hdisj : RangesDisjoint p T.size q U.size`. *Purpose:* Overlapping accesses alias under untyped memory regardless of types (R2). *Tightness:* tight; counterexample `hoist_U_needs_disjoint_ranges`; witness class: overlapping addresses p = q = 0 on untyped memory, T = f32, U = u32, s = 1, r = 0.
- `hsr : s ≠ r`. *Purpose:* Register data dependence. *Tightness:* tight; counterexample `hoist_U_needs_distinct_registers`; witness class: disjoint addresses p = 8, q = 0 on untyped memory, s = r = 0.

**Non-vacuity witness.** T = f32 at 8, U = u32 at 0, s = 1, r = 0 (hoist_U_disjoint_instance). (Lean: `hoist_U_disjoint_instance`.)

**Supporting statements** (counterexamples, witnesses and controls named above; verbatim):

```lean
-- lean/ToyTbaa/Results.lean:1366-1369
theorem hoist_U_disjoint_instance :
    RangesDisjoint 8 Ty.f32.size 0 Ty.u32.size ∧ (1 : Reg) ≠ 0 ∧
    Refines (Beh stepU ([] ++ [.load 1 .f32 8, .store .u32 0 0] ++ [.out 1]) (uWit .u32 0))
            (Beh stepU ([] ++ [.store .u32 0 0, .load 1 .f32 8] ++ [.out 1]) (uWit .u32 0)) := …
```

```lean
-- lean/ToyTbaa/Results.lean:1375-1377
theorem hoist_U_needs_disjoint_ranges :
    ¬ RangesDisjoint 0 Ty.f32.size 0 Ty.u32.size ∧ (1 : Reg) ≠ 0 ∧ NoCommonLeaf .f32 .u32 ∧
    ¬ ReorderSound stepU [.store .u32 0 0, .load 1 .f32 0] [.load 1 .f32 0, .store .u32 0 0] := …
```

```lean
-- lean/ToyTbaa/Results.lean:1383-1385
theorem hoist_U_needs_distinct_registers :
    RangesDisjoint 8 Ty.f32.size 0 Ty.u32.size ∧
    ¬ ReorderSound stepU [.store .u32 0 0, .load 0 .f32 8] [.load 0 .f32 8, .store .u32 0 0] := …
```

**Prior art.**

- Xavier Leroy and Sandrine Blazy. Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations. Journal of Automated Reasoning 41(1):1-31, 2008. https://doi.org/10.1007/s10817-008-9099-0. Mechanized in CompCert: AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc, file common/Memory.v lines 1086-1091, Theorem load_store_other (after a store, a load from another block or from a byte range disjoint from the stored range returns what it returned before), over untyped byte-level memory.
- The Rust Reference, 'Behavior considered undefined', rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, file src/behavior-considered-undefined.md (rule undefined.alias states the aliasing rules in terms of &T, &mut T and Box<T>, with no type-based rule; rule undefined.validity.scalar requires integers and floats to be initialized).
- Rust Unsafe Code Guidelines, glossary, rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce, file reference/src/glossary.md (entry 'Abstract Byte': an abstract byte is Uninit or Init(u8, Option<Provenance>), so the per-byte shadow state is initialization and provenance, not a type; entry 'Aliasing', line 90: 'Zero Sized Types _never_ alias each other, because their span length is always 0').
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. POPL 2020. https://doi.org/10.1145/3371109 (aliasing rules for Rust references over untyped memory, independent of types).
- Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. PLDI 2025. https://doi.org/10.1145/3735592 (a successor aliasing model for Rust references).

**Design question.** What justifies reordering under untyped memory, if not types?

**Non-claims:** see **Boundaries › Non-claims › R6-disjoint-ranges-hoist-sound-U**.

Basis: execution (Lean kernel check) — every statement quoted in this card.

Basis: derived (modeling bridge) — Address-range disjointness is the alias argument available in any byte-addressed memory without types, such as LLVM IR memory or Rust's abstract machine as described in the cited sources. Model–system relation: none proved (no embedding, abstraction or simulation between the toy semantics and LLVM IR or Rust is stated or proved in this package). These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### Auxiliary declarations cited by name

Statements of every other package declaration that this report names (supporting theorems cited in
non-claims, definition examples, and definitions used by them), verbatim. The companion statements in
`lean/ToyTbaa/Companions.lean` are quoted in the cards that cite them (R1b, R1c, R5c) and below.

#### Definition examples and their states (`lean/ToyTbaa/Examples.lean`)

```lean
-- lean/ToyTbaa/Examples.lean:13
def ones4 : Val := [1, 1, 1, 1]
```

```lean
-- lean/ToyTbaa/Examples.lean:18
theorem pair_layout : Ty.pair.size = 8 ∧ Ty.pair.leafAt 0 = .u32 ∧ Ty.u8.size = 1 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:21
theorem pair_byte4_not_u32 : Ty.pair.leafAt 4 ≠ .u32 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:24
theorem f32_valid_any_pattern : Ty.f32.Valid [255, 0, 7, 9] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:27
theorem u32_invalid_short : ¬ Ty.u32.Valid [1, 2] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:33-35
theorem stdCompat_admits :
    stdCompat (some .u32) .u8 = true ∧ stdCompat (some .u32) .u32 = true ∧
    stdCompat none .f32 = true := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:38
theorem stdCompat_rejects : stdCompat (some .u32) .f32 = false := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:41
theorem strictCompat_admits : strictCompat (some .u32) .u32 = true := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:45
theorem strictCompat_rejects_byte : strictCompat (some .u32) .u8 = false := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:51-52
theorem noCommonLeaf_admits :
    NoCommonLeaf .u32 .f32 ∧ NoCommonLeaf .u8 .u32 ∧ NoCommonLeaf .pair .u16 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:55-59
theorem noCommonLeaf_table (T U : Ty) :
    NoCommonLeaf T U ↔
      (T ≠ .u8 ∧ U = .u8) ∨ (T = .u8 ∧ U ≠ .u8) ∨
      (T = .u32 ∧ U = .f32) ∨ (T = .f32 ∧ U = .u32) ∨
      (T = .u16 ∧ U ≠ .u16 ∧ U ≠ .u8) ∨ (T ≠ .u16 ∧ T ≠ .u8 ∧ U = .u16) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:64-65
theorem noCommonLeaf_non_u8_struct_instances :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ NoCommonLeaf .u16 .pair := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:69
theorem noCommonLeaf_rejects : ¬ NoCommonLeaf .pair .u32 ∧ ¬ NoCommonLeaf .f32 .f32 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:72
theorem rangesDisjoint_admits : RangesDisjoint 0 4 4 4 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:75
theorem rangesDisjoint_rejects : ¬ RangesDisjoint 0 4 3 1 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:78
theorem declaredOn_admits : DeclaredOn (declSt .u32 4 ones4) 0 4 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:81
theorem declaredOn_rejects : ¬ DeclaredOn (freshAt 0 16 ones4) 0 4 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:84
theorem allocatedOn_admits : AllocatedOn (freshAt 0 16 ones4) 0 4 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:87
theorem allocatedOn_rejects : ¬ AllocatedOn (declSt .u32 4 ones4) 0 4 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:92-93
theorem readableAt_admits :
    ReadableAt stdCompat (objSt .u32) .u32 0 ∧ ReadableAt stdCompat (objSt .u32) .u8 1 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:96-97
theorem readableAt_rejects :
    ¬ ReadableAt stdCompat (objSt .u32) .f32 0 ∧ ¬ ReadableAt stdCompat (objSt .u32) .u8 16 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:101-102
theorem receivesAt_admits :
    ReceivesAt (objSt .u32) .u32 8 ∧ ReceivesAt (declSt .u32 4 ones4) .u32 0 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:106-107
theorem receivesAt_rejects :
    ¬ ReceivesAt (declSt .f32 4 ones4) .u32 0 ∧ ¬ ReceivesAt (objSt .u32) .u32 16 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:111-114
def punIntoDeclSt : St :=
  ⟨fun a => if a < 4 then some ⟨1, .alloc (some .f32)⟩
            else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .u32⟩ else none,
   fun _ => ones4⟩
```

```lean
-- lean/ToyTbaa/Examples.lean:118-119
theorem memcpyLoadOk_admits :
    MemcpyLoadOk (objSt .u32) .u32 0 8 ∧ MemcpyLoadOk punIntoDeclSt .u32 0 8 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:123-124
theorem memcpyLoadOk_rejects :
    ¬ MemcpyLoadOk (objSt .f32) .u32 0 8 ∧ ¬ MemcpyLoadOk (objSt .u32) .u32 0 14 := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:126
theorem valsAt_example : valsAt (objSt .u32) 0 4 = [0, 0, 0, 0] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:131-133
theorem stepE_same_type_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) =
      .done [ones4] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:136-138
theorem stepE_punning_ub :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) =
      .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:141-143
theorem stepE_byte_read_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) =
      .done [[1]] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:147-149
theorem stepE_allocated_retype_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 0, .load 1 .f32 0, .out 1]
      (freshAt 0 16 ones4) = .done [ones4] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:153-154
theorem stepE_declared_store_mismatch_ub :
    exec (stepE stdCfg) [.store .f32 0 0] (declSt .u32 4 ones4) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:158-160
theorem stepE_memcpy_copies_type_defined :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .f32 8, .out 1]
      (freshAt 0 16 ones4) = .done [ones4] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:164-166
theorem stepE_memcpy_copy_punning_ub :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (freshAt 0 16 ones4) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:170-174
theorem stepE_memcpy_into_declared_defined :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨0, .alloc none⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .u32⟩ else none,
        fun _ => ones4⟩ : St) = .done [ones4] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:178-182
theorem stepE_pair_member_access :
    exec (stepE stdCfg) [.store .pair 0 0, .load 1 .u32 0, .out 1]
        (freshAt 0 16 (List.replicate 8 1)) = .done [ones4] ∧
    exec (stepE stdCfg) [.store .pair 0 0, .load 1 .u32 4, .out 1]
        (freshAt 0 16 (List.replicate 8 1)) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:186-188
theorem stepE_pair_load_from_member_stores_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 0, .load 1 .pair 0, .out 1]
      (freshAt 0 16 ones4) = .done [[1, 1, 1, 1, 1, 1, 1, 1]] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:194-205
theorem byte_loop_copy_does_not_transfer_effective_type :
    exec (stepE stdCfg)
      [.load 2 .u8 0, .store .u8 8 2, .load 2 .u8 1, .store .u8 9 2,
       .load 2 .u8 2, .store .u8 10 2, .load 2 .u8 3, .store .u8 11 2,
       .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨1, .alloc (some .u32)⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .alloc (some .f32)⟩ else none,
        fun _ => []⟩ : St) = .ub [] ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨1, .alloc (some .u32)⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .alloc (some .f32)⟩ else none,
        fun _ => []⟩ : St) = .done [[1, 1, 1, 1]] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:208-209
theorem stepE_unallocated_ub :
    exec (stepE stdCfg) [.load 1 .u8 100, .out 1] (freshAt 0 16 ones4) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:214-216
theorem stepU_punning_defined :
    exec stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) =
      .done [ones4] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:219-220
theorem stepU_unallocated_ub :
    exec stepU [.load 1 .u8 100, .out 1] (erase (freshAt 0 16 ones4)) = .ub [] := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:222-223
theorem erase_example :
    (erase (freshAt 0 16 ones4)).mem 2 = some 0 ∧ (erase (freshAt 0 16 ones4)).mem 16 = none := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:230-232
theorem typeFaults_admits :
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0] (freshAt 0 16 ones4) ∧
    TypeFaults stdCfg [.store .f32 0 0] (declSt .u32 4 ones4) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:237-241
theorem typeFaults_rejects :
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u32 0] (freshAt 0 16 ones4) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 2] (freshAt 0 16 ones4) ∧
    ¬ TypeFaults stdCfg [.memcpy 8 0 4, .load 1 .u32 8] punIntoDeclSt ∧
    ¬ TypeFaults stdCfg [.load 1 .u8 100, .load 1 .f32 0] (objSt .u32) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:245-246
theorem typeFaults_same_type_nonstandard_cfg :
    TypeFaults ⟨fun _ _ => false, true⟩ [.store .u32 0 0, .load 1 .u32 0] (freshAt 0 16 ones4) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:249
theorem uDefined_admits : UDefined [.store .u32 0 0, .load 1 .f32 0] (erase (freshAt 0 16 ones4)) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:252
theorem uDefined_rejects : ¬ UDefined [.load 1 .u8 100] (erase (freshAt 0 16 ones4)) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:257-258
theorem refines_admits :
    Refines (Allows (.done [[5]])) (Allows (.ub [])) ∧ Refines (Allows (.done [[5]])) (Allows (.done [[5]])) := …
```

```lean
-- lean/ToyTbaa/Examples.lean:262-264
theorem refines_rejects :
    ¬ Refines (Allows (.done [[0]])) (Allows (.done [[1]])) ∧
    ¬ Refines (Allows (.done [[2]])) (Allows (.ub [[1]])) := by …
```

```lean
-- lean/ToyTbaa/Examples.lean:270
theorem reorderSound_admits : ReorderSound (stepE stdCfg) [.store .u32 0 0] [.store .u32 0 0] := …
```

```lean
-- lean/ToyTbaa/Examples.lean:275-276
theorem reorderSound_rejects :
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .u32 0 1] [.store .u32 0 1, .store .u32 0 0] := …
```

#### Supporting definitions and theorems (`lean/ToyTbaa/Results.lean`)

```lean
-- lean/ToyTbaa/Results.lean:21
def ones4 : Val := [1, 1, 1, 1]
```

```lean
-- lean/ToyTbaa/Results.lean:24
def twos4 : Val := [2, 2, 2, 2]
```

```lean
-- lean/ToyTbaa/Results.lean:171
def uWit (U : Ty) (p : Nat) : USt := erase (freshAt p 16 (List.replicate U.size 1))
```

```lean
-- lean/ToyTbaa/Results.lean:332-335
theorem same_register_premise_refutes_disjoint_hoist_U (C : Ty → Ty → Prop)
    (hC : ∀ T U s r, C T U →
      ReorderSound stepU [.store U 0 r, .load s T 8] [.load s T 8, .store U 0 r]) :
    ∀ T U, ¬ C T U := by …
```

```lean
-- lean/ToyTbaa/Results.lean:463-466
theorem readable_source_not_necessary :
    ¬ ReadableAt stdCompat Examples.punIntoDeclSt .u32 0 ∧ ReceivesAt Examples.punIntoDeclSt .u32 8 ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1] Examples.punIntoDeclSt =
      .done [valsAt Examples.punIntoDeclSt 0 4] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:480-483
def copyIntoDeclF32 : St :=
  ⟨fun a => if a < 4 then some ⟨0, .alloc (some .u32)⟩
            else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .f32⟩ else none,
   fun _ => ones4⟩
```

```lean
-- lean/ToyTbaa/Results.lean:495-498
def partialOverlapPunSt : St :=
  ⟨fun a => if a < 2 then some ⟨7, .alloc (some .f32)⟩
            else if a < 6 then some ⟨9, .decl .u32⟩ else none,
   fun _ => []⟩
```

```lean
-- lean/ToyTbaa/Results.lean:505-514
theorem memcpy_overlap_defined_examples :
    MemcpyLoadOk partialOverlapPunSt .u32 0 2 ∧
    exec (stepE stdCfg) [.memcpy 2 0 Ty.u32.size, .load 1 .u32 2, .out 1] partialOverlapPunSt =
      .done [[7, 7, 9, 9]] ∧
    exec stepU [.memcpy 2 0 Ty.u32.size, .load 1 .u32 2, .out 1] (erase partialOverlapPunSt) =
      .done [[7, 7, 9, 9]] ∧
    valsAt partialOverlapPunSt 0 4 = [7, 7, 9, 9] ∧
    MemcpyLoadOk (objSt .u16) .u16 0 0 ∧
    exec (stepE stdCfg) [.memcpy 0 0 Ty.u16.size, .load 0 .u16 0, .out 0] (objSt .u16) =
      .done [[0, 0]] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:566-570
theorem strict_typed_load_above_byte_store_not_refines :
    ¬ Refines (Beh (stepE ⟨strictCompat, true⟩) [.load 1 .u32 0, .store .u8 0 0, .out 1]
                ((objSt .u32).withRegs (regs2 [1] ones4)))
              (Beh (stepE ⟨strictCompat, true⟩) [.store .u8 0 0, .load 1 .u32 0, .out 1]
                ((objSt .u32).withRegs (regs2 [1] ones4))) := …
```

```lean
-- lean/ToyTbaa/Results.lean:576-580
theorem byte_copy_u8_case_is_same_type :
    exec (stepE ⟨strictCompat, true⟩) [.memcpy 8 0 Ty.u8.size] (objSt .u8) = .done [] ∧
    (match stepE stdCfg (.store .u8 0 0) (freshAt 0 16 [0]) with
     | .next σ' => decide (σ'.mem 0 = (objSt .u8).mem 0)
     | _ => false) = false := by …
```

```lean
-- lean/ToyTbaa/Results.lean:585-587
def mixedCompat : Compat
  | some .f32, .u8 => false
  | t, s => stdCompat t s
```

```lean
-- lean/ToyTbaa/Results.lean:592-595
theorem byte_dichotomy_not_exclusive_for_pair :
    exec (stepE ⟨mixedCompat, true⟩) [.memcpy 8 0 Ty.pair.size] (objSt .pair) = .ub [] ∧
    ¬ Refines (Beh (stepE ⟨mixedCompat, true⟩) [.load 1 .u8 0, .store .pair 0 0, .out 1] (objSt .pair))
              (Beh (stepE ⟨mixedCompat, true⟩) [.store .pair 0 0, .load 1 .u8 0, .out 1] (objSt .pair)) := …
```

```lean
-- lean/ToyTbaa/Results.lean:632-636
theorem declared_store_mismatch_diverges_without_loads :
    [Instr.store .f32 0 0].all (fun i => !i.isLoad) = true ∧
    TypeFaults stdCfg [.store .f32 0 0] (declSt .u32 4 ones4) ∧
    Beh (stepE stdCfg) [.store .f32 0 0] (declSt .u32 4 ones4) ≠
      Beh stepU [.store .f32 0 0] (erase (declSt .u32 4 ones4)) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:703-707
theorem typeFault_unmasked_despite_later_base_fault :
    ¬ UDefined [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) ∧
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ∧
    Beh (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (freshAt 0 16 ones4) ≠
      Beh stepU [.store .u32 0 0, .load 1 .f32 0, .out 1, .load 2 .u8 100] (erase (freshAt 0 16 ones4)) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:764-766
theorem behE_not_refines_behU_iff_typeFaults_of_uDefined (cfg : ECfg) (P : List Instr) (σ : St)
    (hU : UDefined P (erase σ)) :
    ¬ Refines (Beh (stepE cfg) P σ) (Beh stepU P (erase σ)) ↔ TypeFaults cfg P σ := by …
```

```lean
-- lean/ToyTbaa/Results.lean:774-778
theorem behE_eq_behU_iff (cfg : ECfg) (P : List Instr) (σ : St) :
    Beh (stepE cfg) P σ = Beh stepU P (erase σ) ↔
      ¬ (TypeFaults cfg P σ ∧
        (UDefined P (erase σ) ∨
         (exec (stepE cfg) P σ).trace.length < (exec stepU P (erase σ)).trace.length)) := by …
```

```lean
-- lean/ToyTbaa/Results.lean:902-904
def declPairThenFresh (rs : Reg → Val) : St :=
  ⟨fun a => if a < 4 then some ⟨0, .decl .u32⟩ else if a < 8 then some ⟨0, .decl .f32⟩
            else if a < 16 then some ⟨0, .alloc none⟩ else none, rs⟩
```

```lean
-- lean/ToyTbaa/Results.lean:956-959
theorem store_store_reorder_sound_E_of_second_declared (T U : Ty) (p q : Nat)
    (a b : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) :
    ReorderSoundFrom (fun σ => DeclaredOn σ q U.size) (stepE stdCfg)
      [.store T p a, .store U q b] [.store U q b, .store T p a] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1007-1009
theorem store_store_reorder_sound_E_of_disjoint_ranges (T U : Ty) (p q : Nat) (a b : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) :
    ReorderSound (stepE stdCfg) [.store T p a, .store U q b] [.store U q b, .store T p a] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1156-1159
theorem sink_load_below_store_sound_E_of_store_range_declared (T U : Ty) (p q : Nat)
    (s r : Reg) (hT : T ≠ .u8) (hU : U ≠ .u8) (hTU : NoCommonLeaf T U) (hsr : s ≠ r) :
    ReorderSoundFrom (fun σ => DeclaredOn σ q U.size) (stepE stdCfg)
      [.load s T p, .store U q r] [.store U q r, .load s T p] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1204-1206
theorem sink_load_below_store_sound_E_of_disjoint_ranges (T U : Ty) (p q : Nat) (s r : Reg)
    (hdisj : RangesDisjoint p T.size q U.size) (hsr : s ≠ r) :
    ReorderSound (stepE stdCfg) [.load s T p, .store U q r] [.store U q r, .load s T p] := by …
```

```lean
-- lean/ToyTbaa/Results.lean:1270
def allocHoistSrc : List Instr := [.memcpy 0 0 4, .set 0 ones4, .out 1, .store .f32 0 0]
```

```lean
-- lean/ToyTbaa/Results.lean:1273
def allocHoistTgt : List Instr := [.memcpy 0 0 4, .set 0 ones4, .store .f32 0 0, .out 1]
```

```lean
-- lean/ToyTbaa/Results.lean:1322-1327
theorem declared_and_allocated_preconditions_incomparable :
    AllocatedOn (freshAt 0 16 ones4) 0 4 ∧
    exec (stepE stdCfg) allocHoistSrc (freshAt 0 16 ones4) = .done [ones4] ∧
    ReorderSoundFrom (fun σ => AllocatedOn σ 0 4) (stepE stdCfg) allocHoistSrc allocHoistTgt ∧
    DeclaredOn (declSt .u32 4 ones4) 0 4 ∧
    ¬ ReorderSoundFrom (fun σ => DeclaredOn σ 0 4) (stepE stdCfg) allocHoistSrc allocHoistTgt := …
```

#### Companion example (`lean/ToyTbaa/Companions.lean`)

```lean
-- lean/ToyTbaa/Companions.lean:21-22
theorem valsAt_unallocated_example :
    valsAt (objSt .u32) 16 4 = [] ∧ valsAt (objSt .u32) 14 4 = [] := by …
```

#### Basic facts (`lean/ToyTbaa/Basic.lean`, `lean/ToyTbaa/Semantics.lean`)

```lean
-- lean/ToyTbaa/Basic.lean:214-215
theorem reorderSound_refl {S : Type} (step : Instr → S → Step S) (B : List Instr) :
    ReorderSound step B B := …
```

## Boundaries

### Non-claims

#### R1-hoist-load-above-incompatible-store-sound-E

- The statement covers the hoist direction (a load moved earlier, above a store). Its hypotheses do not license the sink (a load moved later, below a store) or the swap of two stores: R1b and R1c are instances (T = u32, U = f32, the same address, untyped allocated storage) that satisfy the type hypotheses and in which those replacements are not refinements.
- Does not say that T ≠ U suffices: a struct and its member type are distinct but alias (hoist_E_needs_noCommonLeaf). NoCommonLeaf is a per-byte criterion: it is coarser than C's 'neither type is (an aggregate containing) the other' whenever two distinct struct types share a scalar member type (they share a leaf, so the result does not apply to them, although C11, CH2O and LLVM struct-path TBAA can treat them as non-aliasing), and it ignores offsets, so it cannot separate two fields of the same scalar type at different offsets. Per-byte tags carry no object boundaries: a pair load of bytes written by a separate u32 store and f32 store is defined in this model (Toy.Tbaa.Examples.stepE_pair_load_from_member_stores_defined). C's compatible-type relation, unions, qualifiers and signedness variants are not modeled.
- The refinement is from the effective-type semantics to itself. It does not say the transformation is sound for an implementation that gives programs untyped-memory semantics (for example a C compiler run in a no-strict-aliasing mode): under untyped memory the hoist across a same-address store is not a refinement (R2). Running the transformed effective-type program on untyped memory is covered by composing with R4b, which is not stated as a separate theorem.
- Does not cover memcpy-based or byte-based reordering, nor reordering across unknown code. Across a call that may free, reallocate or memcpy-re-type the storage, nothing is claimed (not modeled).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R1b-sink-load-below-incompatible-store-unsound-E

- Does not say that compilers performing this reordering violate ISO C as interpreted by WG14: the committee response to DR 236 declares such programs undefined and states that the translator may rearrange the accesses by the usual aliasing rules. It says that the literal dynamic re-typing reading of C11 6.5p6 modeled here does not justify the reordering.
- Does not apply to semantics with an access-pair rule, such as LLVM IR's '!tbaa' metadata (accesses that alias although their tags say noalias are undefined) or CH2O's typed allocation (Krebbers's lemma is symmetric). In LLVM IR the sink is licensed when the load's and the store's '!tbaa' tags are noalias, that is, when neither tag's (BaseTy, Offset) pair is reachable from the other's via the Parent relation, which is stronger than the tags being different (the tag of an access to a struct member through the struct type and the tag of a plain access at the member's scalar type are different but alias). In CH2O the corresponding condition is that both addresses are frozen, neither type is unsigned char, and neither type is a subobject type of the other; under it, Krebbers's lemma mem_non_aliasing gives that the two addresses are disjoint or that a lookup at either after a store to the other is undefined. Neither system is modeled here, and these conditions are not proved here.
- Escape hatches under this semantics: the sink is a refinement when the load's bytes are declared storage (R5b) or the store's bytes are declared storage (sink_load_below_store_sound_E_of_store_range_declared), in both cases under R1's type and register hypotheses; and, for every pair of types, when the two byte ranges are disjoint and the registers differ (sink_load_below_store_sound_E_of_disjoint_ranges).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R1c-store-store-swap-unsound-E

- Does not say that compilers performing this swap violate ISO C as interpreted by WG14: the committee response to DR 236 declares programs whose differently typed pointers designate the same storage undefined, which would license such rearrangements. It says that the literal dynamic re-typing reading of C11 6.5p6 modeled here does not justify the swap.
- Does not apply to semantics with an access-pair rule, such as LLVM IR's '!tbaa' metadata, or to CH2O's typed allocation. In LLVM IR the swap is licensed when the two stores' '!tbaa' tags are noalias, that is, when neither tag's (BaseTy, Offset) pair is reachable from the other's via the Parent relation, which is stronger than the tags being different (the tag of an access to a struct member through the struct type and the tag of a plain access at the member's scalar type are different but alias). In CH2O the corresponding condition is that both addresses are frozen, neither type is unsigned char, and neither type is a subobject type of the other; under it, Krebbers's lemma mem_non_aliasing gives that the two addresses are disjoint or that a lookup at either after a store to the other is undefined. Neither system is modeled here, and these conditions are not proved here.
- Escape hatches under this semantics: the swap is a refinement when the first store's bytes are declared storage (R5a) or the second store's bytes are declared storage (store_store_reorder_sound_E_of_second_declared), in both cases when neither type is u8 and the types share no leaf; and, for every pair of types, when the two byte ranges are disjoint (store_store_reorder_sound_E_of_disjoint_ranges).
- Does not depend on any load being type-incompatible: the suffix of the witness inside the proof observes the result through a byte load (store_store_swap_witness_runs, first two conjuncts).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R2-tbaa-hoist-unsound-U

- Does not say Rust or LLVM compilers cannot reorder memory accesses: reorderings justified by address disjointness (R6) or by reference-based aliasing rules (Stacked Borrows, Tree Borrows; &T, &mut T and Box<T>) remain available. It is about raw untyped accesses and types alone.
- The refutation is stated for accesses with the same start address p; partially overlapping accesses are not covered by the statement.
- Escape hatches outside the model: zero-sized types (in Rust, accesses of size 0 never alias; the toy's types all have size at least 1), uninitialized or padding bytes, alignment, and pointer provenance are not modeled, and none of them is a type-based alias rule.
- Types with invalid bit patterns are not modeled; for them a typed load can be undefined under (U) too, which is a validity rule, not TBAA.
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R3a-memcpy-then-typed-load-defined-E

- Does not say that memcpy avoids effective-type undefined behaviour in general. Under (E), as in C11 6.5p6, memcpy into allocated storage (no declared type) copies the source's effective type, so loading the copy at an incompatible type is undefined (memcpy_then_load_nonvacuous, last two conjuncts); by the characterization (memcpy_then_typed_load_defined_E_iff) and the definition of MemcpyLoadOk, if the copy-then-load terminates normally printing the bytes that were at p, then at every byte offset where the source byte's tag is incompatible with T's leaf, the destination byte belongs to a declared object whose leaf is compatible with T's leaf (memcpy punning at an incompatible type goes through declared destination bytes); an instance of memcpy punning into a declared object is Toy.Tbaa.Examples.stepE_memcpy_into_declared_defined. In C++ (N4950 [cstring.syn] p3, [intro.object] p10) memcpy implicitly creates objects in the destination, so the corresponding C++ program with malloc'd storage can be defined; C++ is not modeled.
- The corollary's ReadableAt is not necessary: memcpy punning into a declared object is defined although the source is not readable at the destination's type (readable_source_not_necessary).
- Defined typed use of the copy relies on memcpy transferring tags, not on the character exemption alone: a loop of u8 loads and u8 stores through a register leaves an f32-typed destination f32-typed, so a u32 load of it is undefined (Toy.Tbaa.Examples.byte_loop_copy_does_not_transfer_effective_type). C11 6.5p6 also transfers the effective type for copies 'as an array of character type'; the toy does not model that clause for explicit byte loops.
- Says nothing about copies whose length differs from T.size or that start at another offset.
- The toy's memcpy reads every source byte before writing any destination byte, which is the semantics of C's memmove, and its step has no condition on overlap; copies between overlapping ranges can be defined in the toy, and the plain claim's 'overlapping ranges allowed' refers to this primitive (memcpy_overlap_defined_examples: copying [0, 4) to [2, 6) prints the original source bytes, and a self-copy is defined). ISO C11 (N1570 7.24.2.1p2) makes memcpy between overlapping objects undefined behaviour; that undefinedness is not modeled, so for overlapping ranges the statement describes a memmove-like copy, not C's memcpy.
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R3b-byte-copy-defined-forces-byte-tbaa-unsound

- The statement concerns hoisting a u8 load above a T store. It says nothing about the opposite pair (a T load and a u8 store): byte stores keep the tags of allocated storage under every discipline, so even under strictCompat a u32 load cannot be hoisted above a u8 store to the same bytes (strict_typed_load_above_byte_store_not_refines).
- Witness-level statement: one initial state (objSt T) and one context (suffix out 1). The universal form (copy defined from all suitable states implies the hoist is unsound in some context) follows directly from it but is not stated separately.
- The dichotomy is an inclusive 'or': for pair, a discipline that exempts byte reads of u32 bytes but not of f32 bytes makes the copy undefined and the byte hoist unsound (byte_dichotomy_not_exclusive_for_pair).
- For T = u8 the witness state's u8 tag is not produced by u8 stores into fresh storage (byte_copy_u8_case_is_same_type); the T = u8 case is the degenerate same-type case.
- Escape hatch outside the model: a language can separate an arithmetic byte type that is TBAA-disjoint from u32/f32 from a distinct representation-inspection byte type used by copy routines; the toy has a single byte type (not modeled).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R4a-no-type-fault-implies-E-equals-U

- TypeFaults cfg P σ is a verdict of the semantics stepE cfg (the run stops at a type fault), not the programming idiom 'type punning': sanctioned byte reinterpretation (reading any object through u8 under stdCfg, or memcpy into a declared object followed by a load at its declared type) does not type-fault (Toy.Tbaa.Examples.typeFaults_rejects), and for a nonstandard cfg even a same-type access can type-fault (Toy.Tbaa.Examples.typeFaults_same_type_nonstandard_cfg).
- Type faults also arise from stores: a store into a declared object at an incompatible type, in a program without any load, already separates (E) from (U) (declared_store_mismatch_diverges_without_loads).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R4b-untyped-run-refines-effective-type-run

- Does not say that compiling an effective-type program to LLVM IR with '!tbaa' metadata (strict-aliasing mode) is a refinement: LLVM's access-pair rule makes some accesses undefined that (E) defines, for example the allocated-storage re-typing of R1b and R1c. R4b is about running on untyped memory without such a rule (for example -fno-strict-aliasing, or machine code after lowering).
- Type faulting alone does not decide the converse inclusion. If the untyped execution terminates normally (UDefined), the converse inclusion fails if and only if the effective-type execution stops at a type fault (behE_not_refines_behU_iff_typeFaults_of_uDefined). If the untyped execution also faults, a type-faulting program can break the converse inclusion (behE_not_refines_behU_without_uDefined: the untyped run prints before its later base fault) or satisfy it (behE_refines_behU_masked_instance: no out between the type fault and the later base fault). In particular the condition 'the program type-faults and its untyped run is defined' is sufficient but not necessary for the converse inclusion to fail (behE_not_refines_behU_without_uDefined refutes the corresponding biconditional).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R4c-agreement-iff-no-type-fault-given-U-defined

- Without UDefined the stated equivalence can fail, and the exact condition is different: for every cfg, P and σ, the behaviours under (E) and (U) coincide if and only if it is not the case that the program type-faults while the untyped execution terminates normally or has a strictly longer output trace (behE_eq_behU_iff). Instances without UDefined: a type-faulting program whose behaviour sets coincide (no out between the type fault and the later base fault of the untyped run, typeFault_masked_by_later_base_fault) and one whose behaviour sets differ (an out between them, typeFault_unmasked_despite_later_base_fault).
- TypeFaults is the semantics' verdict, not the idiom 'type punning' (see R4a), and it counts stores into declared objects as well as loads (declared_store_mismatch_diverges_without_loads).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R5a-store-store-swap-sound-E-declared

- The precondition declares the first store's range alone; the second store's range need not be declared as well, because any overlapping byte lies in both ranges. Under the same type hypotheses, declaring the second store's range instead also suffices (store_store_reorder_sound_E_of_second_declared). DeclaredOn is not necessary for the swap to be a refinement: for every pair of types and disjoint byte ranges the swap is a refinement from every initial state, including states where DeclaredOn fails (store_store_reorder_sound_E_of_disjoint_ranges). The tightness witness for DeclaredOn is an overlapping address pair (p = q = 0 on allocated storage).
- Declared objects in the toy have no lifetime end. Storage that is reused for a different type (C++ placement new or the end of an object's lifetime; stack slots reused across non-overlapping variable lifetimes, such as { int x; } { float y; } or llvm.lifetime.start/end) is not declared storage in this sense, and nothing is claimed for it.
- NoCommonLeaf is a per-byte criterion: it is coarser than C's 'neither type is (an aggregate containing) the other' whenever two distinct struct types share a scalar member type (they share a leaf, so the result does not apply to them, although C11, CH2O and LLVM struct-path TBAA can treat them as non-aliasing), and it ignores offsets, so it cannot separate two fields of the same scalar type at different offsets. Per-byte tags carry no object boundaries: a pair load of bytes written by a separate u32 store and f32 store is defined in this model (Toy.Tbaa.Examples.stepE_pair_load_from_member_stores_defined). C's compatible-type relation, unions, qualifiers and signedness variants are not modeled.
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R5b-sink-load-below-store-sound-E-declared

- The precondition declares the load's range alone; the store's range need not be declared as well, because any overlapping byte lies in both ranges. Under the same type and register hypotheses, declaring the store's range instead also suffices (sink_load_below_store_sound_E_of_store_range_declared). DeclaredOn is not necessary for the sink to be a refinement: for every pair of types, disjoint byte ranges and distinct registers the sink is a refinement from every initial state, including states where DeclaredOn fails (sink_load_below_store_sound_E_of_disjoint_ranges). The tightness witness for DeclaredOn is an overlapping address pair (p = q = 0 on allocated storage).
- Declared objects in the toy have no lifetime end. Storage that is reused for a different type (C++ placement new or the end of an object's lifetime; stack slots reused across non-overlapping variable lifetimes, such as { int x; } { float y; } or llvm.lifetime.start/end) is not declared storage in this sense, and nothing is claimed for it.
- NoCommonLeaf is a per-byte criterion: it is coarser than C's 'neither type is (an aggregate containing) the other' whenever two distinct struct types share a scalar member type (they share a leaf, so the result does not apply to them, although C11, CH2O and LLVM struct-path TBAA can treat them as non-aliasing), and it ignores offsets, so it cannot separate two fields of the same scalar type at different offsets. Per-byte tags carry no object boundaries: a pair load of bytes written by a separate u32 store and f32 store is defined in this model (Toy.Tbaa.Examples.stepE_pair_load_from_member_stores_defined). C's compatible-type relation, unions, qualifiers and signedness variants are not modeled.
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R5c-store-swap-scheme-sound-on-declared-not-on-allocated

- Does not say that declared storage licenses every reordering that allocated storage licenses. Over arbitrary replacements the two preconditions are incomparable, even for a pure reordering: moving an f32 store above an out (after a guard making [0, 4) accessible) is sound from every state whose bytes [0, 4) are allocated storage, with a defined source run, and not sound from states whose bytes [0, 4) are declared (declared_and_allocated_preconditions_incomparable).
- The statement concerns the store/store scheme for the types u32 and f32; R5a and R5b give the general declared-storage results, and R1, R1b, R1c the allocated-storage ones.
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

#### R6-disjoint-ranges-hoist-sound-U

- Addresses are unbounded natural numbers: RangesDisjoint uses Nat arithmetic with no 32- or 64-bit wraparound, so ranges that wrap around the end of a real address space are not modeled.
- Disjointness is a hypothesis; how a compiler establishes it (provenance, reference rules such as Stacked Borrows or Tree Borrows, or alias analysis) is outside the statement.
- Store/store swaps and sinks under (U) with disjoint ranges are not stated (expected to hold; not proved here).
- Toy model: straight-line programs with constant addresses; five access types (u8, u16, u32, f32, and a padding-free struct pair = {u32, f32}); every byte list of the right length is valid for every type (no uninitialized bytes, pointer provenance or alignment); no unions, qualifiers, signed/unsigned variants, arrays, pointers stored in memory, allocation or deallocation, object lifetimes, control flow, calls, or concurrency. The observable behaviour of a run is its output trace together with whether it terminates normally or with undefined behaviour, and undefined behaviour does not retract output already emitted.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about C, C++, LLVM or Rust.

### Escape hatches

- **R2 (under (U), no criterion on the pair of access types licenses the same-address hoist).**
  The conclusion fails in nearby settings: with disjoint byte ranges and distinct registers the
  hoist is a refinement under (U) for every pair of types (R6,
  `hoist_load_above_store_sound_U_of_disjoint_ranges`); and, as proved instances, the same-address
  `f32`-load/`u32`-store hoist is a refinement under (E) from `freshAt 0 16 ones4`, while under (U)
  the hoist with the load moved to the disjoint address 8 is a refinement from `uWit .u32 0`
  (`hoist_U_witness_refines_under_E_or_disjoint`). Outside the model (not modeled): reference-based
  aliasing rules (Stacked Borrows, Tree Borrows), zero-sized types, uninitialized or padding bytes,
  alignment, pointer provenance and invalid bit patterns; none of these is a type-based rule.
- **R3b (a defined byte-wise copy forces the byte hoist to be unsound).** With a copy primitive that
  bypasses the effective-type checks (`memcpyChecksBytes = false`), the strict discipline has both a
  defined copy and a byte hoist that is a refinement at the witnesses (T = u32, initial state
  `objSt .u32`; `byte_hoist_refines_with_unchecked_memcpy`);
  with byte accesses checked under `strictCompat`, the copy is undefined and the hoist is a
  refinement at the witnesses (`strict_copy_ub_and_byte_hoist_refines`). Outside the model (not
  modeled): a language with two byte types, an arithmetic one that is disjoint from `u32`/`f32` for
  alias analysis and a representation-inspection one used by copy routines.
- **R1b and R1c (re-typing of allocated storage defeats the sink and the store/store swap).** Under
  R1's type and register hypotheses the sink is a refinement when the load's range is declared
  storage (R5b) or when the store's range is declared storage
  (`sink_load_below_store_sound_E_of_store_range_declared`); for every pair of types it is a
  refinement when the two byte ranges are disjoint and the registers differ
  (`sink_load_below_store_sound_E_of_disjoint_ranges`). When neither type is `u8` and the types
  share no leaf, the swap is a refinement when the first store's range is declared storage (R5a) or
  the second store's range is (`store_store_reorder_sound_E_of_second_declared`); for every pair of
  types it is a refinement when the two byte ranges are disjoint
  (`store_store_reorder_sound_E_of_disjoint_ranges`).

### Hypotheses with unknown tightness

None. Every hypothesis of every card is `tight`, with a proved counterexample theorem named in its
ledger entry.

### Disproved or dropped statements

None. Every statement of the package is proved as stated; none was disproved, weakened or
dropped.

### Not examined

- Programs with control flow, calls, loops, dynamic addresses or concurrency; reordering across
  unknown code.
- Partially overlapping accesses with different start addresses under (U) (R2 is stated for
  accesses with the same start address).
- Transformations other than the hoist, the sink and the store/store swap of two adjacent
  accesses (for example eliminating or merging accesses, or moving `memcpy`).
- Under (U) with disjoint byte ranges, the store/store swap and the sink are expected to be
  refinements (not proved here).

## Evidence

### Kernel-check record

- Toolchain: `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std`, no Mathlib.
- `lake build` of a fresh copy of `lean/` (artifact cache disabled) succeeds without warnings.
- Axiom audit (`audit/axioms.json`): every one of the 683 declarations of the library
  depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
  `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe` occurs in the
  sources.
- Statement hashes (`audit/statements.json`): for each declaration below, `statement` is the
  SHA-256 of Lean's `repr` of its type, and `closure` is the SHA-256 of the sorted lines
  `name : repr(type)` (followed by ` := repr(value)` for definitions; theorem bodies excluded) of
  every package-local constant reachable from that type; the number in parentheses is the number
  of closure lines. The axioms column lists the axioms the declaration depends on.

| Declaration | Role | Axioms | statement SHA-256 | closure SHA-256 (lines) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Tbaa.Results.hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8` | R1 result | Classical.choice, Quot.sound, propext | `143a01b68c5ebdd8b9fe1efe7c29368b117473428e31439f8d28795adfc370e3` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.sink_load_below_store_not_sound_E` | R1b result; R1b witness | Quot.sound, propext | `eb2204effa721fa44a472871bd7e02e29c787362656fff39bf978e798c6ea819` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.store_store_reorder_not_sound_E` | R1c result; R1c witness | Quot.sound, propext | `ed301a778ee8f3c94e46dea334ab8f54f06bea4bf69ecb6c3890bac93b80f51b` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.hoist_load_above_store_same_addr_unsound_U` | R2 result | Classical.choice, Quot.sound, propext | `80850dc693b3f7c045d25b309dc92c53205c7d5ecd252af276f72a54f730550d` | `47742f138a1e164b248ada757ee1aa201e14507036d0193b19c8611b793e94b1` (94) |
| `Toy.Tbaa.Results.no_type_criterion_licenses_same_addr_hoist_U` | R2 result | Classical.choice, Quot.sound, propext | `c617c7d89e47a5b1c5443fc4d706dd0020dbf018a4f12ac787036e936d64838f` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.no_type_criterion_licenses_same_addr_hoist_U_at_one_site` | R2 result | Classical.choice, Quot.sound, propext | `449bf1c62969c7d86fe49532805d47e9796db2ffb95be0e64edfab3c027c0703` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.memcpy_then_typed_load_defined_E_iff` | R3a result | Classical.choice, Quot.sound, propext | `3c807abe29d139e61c43fa18efa262727226bfca0d975560b5380d72cea05f14` | `d58c08f777b1366e4fc7445f709ad431831ce27615b91a545444fb76762fd9d8` (109) |
| `Toy.Tbaa.Results.memcpy_then_typed_load_defined_E_of_readable_of_receives` | R3a result | Classical.choice, Quot.sound, propext | `0d8bbcfa2dc2efe3b45b60083cc80ecc0a00f6aa7796c421d1507179a99fcf3e` | `6a45698de766fe49be72b5f31b2c8bca55c79d73d2409cd6fb6b664c554b35c1` (109) |
| `Toy.Tbaa.Results.byte_copy_defined_forces_byte_hoist_unsound` | R3b result | Quot.sound, propext | `4ac7539cfb5bd275e6ac3bff415cbdc568feb99336f1deeb31c5f7b92a91e392` | `9092591792d29dd9239f3a40c61220040f8553e29a67bdd5d7d131032daf8bb6` (109) |
| `Toy.Tbaa.Results.behE_eq_behU_of_not_typeFaults` | R4a result | Quot.sound, propext | `8190644b0ccfb26c04061030cdf4bf4f4c1f0dc5e91cdcad5fabd85a11c0cb82` | `feb7e1ab5cb03f5b9d8bef5d36f097f41cfeb49c5566f35f274ca8475a797440` (128) |
| `Toy.Tbaa.Results.behU_erase_refines_behE` | R4b result | Quot.sound, propext | `67fcd383e833f250d9a5e14ffa68af5a8caaad572b91c0fec5d8046fe6e79c25` | `e17b388e7b581b76b17f70ea93f3e8ff7835075018fb816cb22eaca8467fa93e` (118) |
| `Toy.Tbaa.Results.behE_eq_behU_iff_not_typeFaults_of_uDefined` | R4c result | Quot.sound, propext | `fe25d143fe5e6c9597e4e7087c52193b5ac8f5fc8297f1ff0e7b1af3c7097d00` | `4ae37802a9967a481f8bdfd1d793001c569cee07ae2abd2148ecfdafe0eff555` (129) |
| `Toy.Tbaa.Results.behE_not_refines_behU_iff` | R4b result | Quot.sound, propext | `7611c166fb2363aa01c598f4f6b499fa0e85ad82a5ce995241528bc293f1ef90` | `1c45728baefae005cb9eab34cdee74a13fef3357c79a114cf47bb126ec2048ba` (130) |
| `Toy.Tbaa.Results.store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8` | R5a result | Classical.choice, Quot.sound, propext | `d2b94a905cea46a14eb91b2e9b8ff24e70f2bd0bd88a8357795761fbc06b5949` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_declared_of_noCommonLeaf_of_ne_u8` | R5b result | Classical.choice, Quot.sound, propext | `07ae17fd0f88db66f3d5d99e4f830fde680f1ecf67513f9100d6b229a28559d8` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.store_swap_scheme_sound_on_declared_not_on_allocated` | R5c result | Classical.choice, Quot.sound, propext | `3d4401e7e8b97e7d0ce31d843dcc06984a6882431840fdf7ae53bd341ccce916` | `34726fd2ba571182db5d144ef3e59e43c83a107763f6d6baa5f1bba4be37a246` (118) |
| `Toy.Tbaa.Results.hoist_load_above_store_sound_U_of_disjoint_ranges` | R6 result | Classical.choice, Quot.sound, propext | `5afda65ea43863cecef4c8eb52b20a200a11b4b7ec704e10f19405597daa7822` | `79018ca9cf4b581c493e73b4ce15f90230c39d9bde4e46ef1bc0efbde0478b2a` (81) |
| `Toy.Tbaa.Results.hoist_E_nonvacuous` | R1 witness | propext | `bfbd28f7033005c9deda901d11e38a40058f1333fa4eb9ccaa898909369f8ce9` | `f85abfdac521d3a4cb37a5106cdce818a7328f969b6de3456a1b9f57ef5647c9` (109) |
| `Toy.Tbaa.Results.hoist_E_nonvacuous_struct` | R1 witness | propext | `177da2d81ce1a1adf8a74deb9b1a5371debd7dbdb9ac9b8bdc6966bd252349eb` | `70fcc76bca7b53db5e7dcfb01089aeb270c84924212dd1cac9d439f9e3082fb0` (108) |
| `Toy.Tbaa.Results.hoist_E_needs_load_ne_u8` | R1 counterexample | Quot.sound, propext | `4334b6097ae7e28b607d2d422f15a37ab3a2ee7b3721802e0dd6284e5a0b772e` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.hoist_E_needs_store_ne_u8` | R1 counterexample | Quot.sound, propext | `8f1a2db0e1df5017c51a38dc3226e55289dd3f18a1769baf5d25e8ae04033383` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.hoist_E_needs_store_ne_u8_on_declared` | R1 counterexample | Quot.sound, propext | `3996c1f084d855b2d7c70159c3610f860a4fd3993e5eeafee65f6cfb2fe0f457` | `7b4eedeb1c7a78929451e6e15e97e1e4ac0d1efe08f6d44618c4013363ed9598` (120) |
| `Toy.Tbaa.Results.hoist_E_needs_noCommonLeaf` | R1 counterexample | Quot.sound, propext | `19233ebdc80eabe218ea22da4818bcb08ff0e2a083b1385e033330aef50c39b0` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.hoist_E_needs_distinct_registers` | R1 counterexample | Quot.sound, propext | `8701ed664590e18241efa933079ad3cf6e58989a45b8eeb59f9577a95cf29430` | `1476f59de6aa82abfd3de51ed145ac803f00840db1cb989b8cbd5982bfe0f466` (117) |
| `Toy.Tbaa.Results.no_type_criterion_needs_premise` | R2 counterexample | Classical.choice, Quot.sound, propext | `b3632dac145992c6466a274c0b5ee41a11737975f6566a19e55782a1b548cc90` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.no_type_criterion_at_one_site_needs_premise` | R2 counterexample | Classical.choice, Quot.sound, propext | `2ab384c4939e3f7713a04c9b71bda22df7cc20b2c18e8505136b1d464b5dc046` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.no_type_criterion_premises_satisfiable` | R2 witness | propext | `865000ecfcc7b5def13f8631b6c2e06aba62c5dc1025754c5c26397d44c1697d` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.hoist_unsound_U_instance` | R2 witness | Quot.sound, propext | `d1eaef737a6997d059f8cacf556f99b1cab08b477db65d9d3d1db9e54d7aea6a` | `44a315fcacb1f0b88f8c56680331dc990a84232107477947a3203796c01a4f9c` (91) |
| `Toy.Tbaa.Results.hoist_U_witness_refines_under_E_or_disjoint` | R2 control | Quot.sound, propext | `8c50c845b54524d8a49620cd2c5f9e2d9d3751465eccc28eae9401cd9a8a96c3` | `9dfffa2449e22e7c26ec9cea15f308df08c609f1ea81c1acab2a26dff467cd27` (127) |
| `Toy.Tbaa.Results.memcpy_then_load_nonvacuous` | R3a witness | propext | `7a4c7167f052dac6cebba2f2824d15f4bbc86a16779f3dc015e8f2396f87cbd0` | `1cbebd42bcc6b5b08f73a8ac4492ab012c73cf2081c71949ddcaa255d5cde982` (111) |
| `Toy.Tbaa.Results.memcpy_corollary_nonvacuous` | R3a witness | Quot.sound, propext | `55d12ccdbb597e5e90a7040a320253be2650e5946a6b8cac8d4a475a62d3bf93` | `3dede7c9d9683b0cec97158b6a1a8b56ced3bb5caa95b00a6a8792256bb6db2f` (55) |
| `Toy.Tbaa.Results.memcpy_then_load_needs_readable_source` | R3a counterexample | Quot.sound, propext | `9256bf48925ab71ea04457d65761d5332ca3e596090a692b9e3c79b848ad2cb9` | `a356ed35bec90b2498bde89bd7491ccde8b836367b8b7d81e5b61a716da50ab9` (110) |
| `Toy.Tbaa.Results.memcpy_then_load_needs_receiving_destination` | R3a counterexample | Quot.sound, propext | `4cf84f9196c5fabaab059feefcdea8793f503bc4d80e7a508dbc2dabcdc5524b` | `e34e4731a76e42dbe154e7c7f1d82725fffd2f4a759d0ca52d98b2f3c30ba9c7` (111) |
| `Toy.Tbaa.Results.byte_copy_defined_nonvacuous` | R3b witness | propext | `b8d7e0d69d44cc836ded4d9bd5f0c13e96e28051145319caace55d58281cf51c` | `b6c20ab2d8bcac9006fbd86bab754f20b8cb5d7d7bbd5bae30d2bd04d00cff32` (107) |
| `Toy.Tbaa.Results.byte_hoist_refines_with_unchecked_memcpy` | R3b control; R3b counterexample | Quot.sound, propext | `d03854fa56a848dd0aa59a9896d12e79fd62153ff8a6b9c314b057fc16f5a53d` | `8198b0a867fd9919bc0c3b4e446a8d7a20bcd0caa635fc5ad560ac0c18850848` (114) |
| `Toy.Tbaa.Results.strict_copy_ub_and_byte_hoist_refines` | R3b counterexample | Quot.sound, propext | `398d57b856067231d3b9d630d5db40fc153c554829fde47634a8aa56505285d6` | `8198b0a867fd9919bc0c3b4e446a8d7a20bcd0caa635fc5ad560ac0c18850848` (114) |
| `Toy.Tbaa.Results.behE_eq_behU_nonvacuous` | R4a witness | propext | `80f420e7a8d0cc29203f9a4c25bee7e4deba8968db60d674b5ac846fdd35615a` | `d823a29f8849b834371c2abf4cb992f1f09610a3fb486322847362ed0d41ff19` (136) |
| `Toy.Tbaa.Results.agreement_needs_no_type_fault` | R4a counterexample | Quot.sound, propext | `259d2541ca26ee12a66ec94595ba54c4804bf1dd9094de7e90acb0b399f2dd32` | `d823a29f8849b834371c2abf4cb992f1f09610a3fb486322847362ed0d41ff19` (136) |
| `Toy.Tbaa.Results.behU_refines_behE_strict_instance` | R4b witness | Quot.sound, propext | `2696c50623afc06ae17af76eebcf74da78eefd951f13018ee77795a765bd9b80` | `2061a87454bd27cb1ffbdb46cb4a089fe3592e69e68c1ab49af0b48401ffc514` (126) |
| `Toy.Tbaa.Results.behE_eq_behU_iff_nonvacuous` | R4c witness | Quot.sound, propext | `bf28ae9028afb498b2d1b89cbae5da2bc8310edb2104d652e729854a3ee0f210` | `9df940b714d51de9c7308d59c134d241582dd1252a7b5e6fa1d79e59b0365cf3` (130) |
| `Toy.Tbaa.Results.typeFault_masked_by_later_base_fault` | R4c counterexample | Quot.sound, propext | `38d57d940a9a057eca3f629f1003bb7a3e54352e3c2e7fbd94824b6ee34b8e6d` | `86db4747099db041c5d8e1d42585338b0d65733b31cd1e45ab80096d102380d2` (137) |
| `Toy.Tbaa.Results.behE_not_refines_behU_of_uDefined_nonvacuous` | R4b witness | Quot.sound, propext | `66cace553de0abad9a56e8b2caabd7695f7294215c70c69282e507026d48f5df` | `f1b59f81ab9b07837e9174ab4e24e33436c282ed8397be4a4f2ebe46521ea361` (138) |
| `Toy.Tbaa.Results.behE_not_refines_behU_without_uDefined` | R4b witness | Quot.sound, propext | `6b4efc2cd9591016977d485176947ddd4794632c1bc1b8b7c5e3133383cbc317` | `f1b59f81ab9b07837e9174ab4e24e33436c282ed8397be4a4f2ebe46521ea361` (138) |
| `Toy.Tbaa.Results.behE_refines_behU_masked_instance` | R4b witness | Quot.sound, propext | `e99757e69ea8cb9b9efa127eb6a0b5ac0fdf92e5266cd6a35580272af214ce79` | `f1b59f81ab9b07837e9174ab4e24e33436c282ed8397be4a4f2ebe46521ea361` (138) |
| `Toy.Tbaa.Results.store_store_declared_nonvacuous` | R5a witness | propext | `f6f7e355e05a798adeef19078da9a95fc58b736b014212b5eaae0adc096fae65` | `a5af43f213cbe4edc9c0ea008fb35171976ac8d1e3f4f15e8f7d932452cccbd8` (114) |
| `Toy.Tbaa.Results.store_store_declared_nonvacuous_struct` | R5a witness | propext | `76ae91440c40e3fc0894c8214010b3e749f862cf458c0fd302f28dec146ba4c4` | `39b8a1da85e4a0f8083ad9ff435de965cf467e1116d21a04e96b80ae8ed239b1` (111) |
| `Toy.Tbaa.Results.store_store_needs_declared_storage` | R5a counterexample | Quot.sound, propext | `a52a29f0b3e0277532bb47271778fde8be4f39040f049ae6e054a3bdf2ca84a6` | `654cfc03a8df29bdad88e7ef4429177a36bdc050dadb714f9da04cfb9a052365` (124) |
| `Toy.Tbaa.Results.store_store_declared_needs_first_ne_u8` | R5a counterexample | Quot.sound, propext | `d2aa223f2073aeb2b1baf1a01ec5dbae717ef8f6b3f1816950ee4949a5915a5b` | `10302b5ae12b3f7080dc1ed5d6807a664af1c4b12fa5f44ce03f98c511a623d0` (122) |
| `Toy.Tbaa.Results.store_store_declared_needs_second_ne_u8` | R5a counterexample | Quot.sound, propext | `8ea0bf81cc432b0e486e6885d003f5b6fc6a73af85319de0f6e712dc17782cab` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.store_store_declared_needs_noCommonLeaf` | R5a counterexample | Quot.sound, propext | `7875adb80ce4773616232fc68dc74e2c93bd50e95ea913625fcdca17dd42b7c9` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_declared_nonvacuous` | R5b witness | propext | `8cc122d7773a2adb3a4faaa2bbb2e1bcfaff10d635e0060ecf9c95cc9e74e978` | `5f2bdd78fedef28a548ca6c75652ef1e915436abb274496d75df9ced2dde0a0b` (111) |
| `Toy.Tbaa.Results.sink_declared_nonvacuous_struct` | R5b witness | propext | `59f64e3ea2ddbf0633649da4f777d1db7a62ddc8540c429d67d837285955d798` | `1d619a8cdad44c2f1dd90a32200240e9f6e107026381461f0f9641128f017351` (110) |
| `Toy.Tbaa.Results.sink_needs_declared_storage` | R5b counterexample | Quot.sound, propext | `6e13cf7a337c30d265a1493a912964dc65da56e70443f0ce61943f24d95f2866` | `20b03dea8defe14525fb375dff2a3969be460d50e5a3f8af0f7afc024033c2af` (121) |
| `Toy.Tbaa.Results.sink_declared_needs_load_ne_u8` | R5b counterexample | Quot.sound, propext | `e9db505788c135d7f55a2057350c123f575469fae35f2e4762a1ab1d18d0b863` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_declared_needs_store_ne_u8` | R5b counterexample | Quot.sound, propext | `17b47b42aa461463f3ef8b272b6a3a88e38e53e29e4d28df8329ddde7e0f7159` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_declared_needs_noCommonLeaf` | R5b counterexample | Quot.sound, propext | `e3a91da94c5f30dd4de9d0d3be40a6ec0abc6d2f1f16d9f1289657de2ce03483` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_declared_needs_distinct_registers` | R5b counterexample | Quot.sound, propext | `340cb81467238d1cab91e55f0b5bd3d180ec98c107ccb9e6535b66c9cfac3aad` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.store_swap_scheme_nonvacuous` | R5c witness | propext | `581c67efb4ec8430f4a2e6887e427656a958071c65171bffffc31654924aac76` | `ffed00d12058dbfc161b94ae3067ecb56fe72512fe469d2ca38aabd04f135e7a` (115) |
| `Toy.Tbaa.Results.hoist_U_disjoint_instance` | R6 witness | Quot.sound, propext | `d35fe923cc8fab842557d1d79ec36958b3711b088327c9628d55bd49bc0237d7` | `2db95249b032e502869d1bc966098bcb97fa46e6c265da218f2613a41362b38b` (93) |
| `Toy.Tbaa.Results.hoist_U_needs_disjoint_ranges` | R6 counterexample | Quot.sound, propext | `2de247f12606a93df15eadf37f5ec126781d780b911217175543ea0bdde46538` | `53b8a1638ba43acf40ef40c53e0c691d1991ebd0db8921014f3da2e9162f0660` (82) |
| `Toy.Tbaa.Results.hoist_U_needs_distinct_registers` | R6 counterexample | Quot.sound, propext | `e9284ef071b6cf8e83947556feb50db4bff90115930db7eb21e5c56f712e1e2c` | `79018ca9cf4b581c493e73b4ce15f90230c39d9bde4e46ef1bc0efbde0478b2a` (81) |
| `Toy.Tbaa.Byte` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Val` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Reg` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Scalar` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Ty` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Ty.leaves` | cited | none | `45955ec0c0afc10f5cdc3d3ecb9ab8f8f853951b2c2789f1358b07f8dd685a5f` | `f73e22a30bda9c2f3c0aff4977aaefcee06cbf03586f72eb7193620979732f86` (11) |
| `Toy.Tbaa.Ty.size` | cited | none | `e57c684f70edbb914bb7c4e095df8b35aed3f8cfa84f90c2ada85ecd428eaef7` | `210ec6da3cdb0b1ecf9e4cf8e1110257eeba8af80349eeb66a28875b33cc7caa` (6) |
| `Toy.Tbaa.Ty.leafAt` | cited | propext | `079f0dcb06d70b80c566a2b80a8fdee7f2d748e277e88f02cf3d692b5a09d637` | `f73e22a30bda9c2f3c0aff4977aaefcee06cbf03586f72eb7193620979732f86` (11) |
| `Toy.Tbaa.Ty.Valid` | cited | none | `89087ee04f2cb5106ee7d938f96edc35b8473cf7c0cd9383cfeac7c50c86fc14` | `6e7be5061f8d7197d6b2c907e8d7bbda137d47c7f66410ba9203e33868ac7687` (8) |
| `Toy.Tbaa.Instr` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Instr.isLoad` | cited | propext | `695c892b085391cc2d7e2c75059c4a12cb8a34b15596a0989bb82a3ca552512b` | `5ea6dac47fb86946fb40aeff237a8f73da8cb3baf36e0bfb0cd3c7be5dd3a704` (15) |
| `Toy.Tbaa.Fault` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Step` | cited | none | `a8dc5c150dffbeb8ef8091cecafe85672f8110e0fe10cca4d6a5836328177c85` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Final` | cited | none | `a8dc5c150dffbeb8ef8091cecafe85672f8110e0fe10cca4d6a5836328177c85` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Outcome` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.runFrom` | cited | none | `bc37a7bb0fca7a2ad5b6879900f4e9d7a082c654f785a06f064f3965560b91f2` | `cb3495edd59f4f6b935af2aa15b5a1b55055bed389724caa29e632b4ee3d02c7` (25) |
| `Toy.Tbaa.Final.outcome` | cited | none | `cf79ffafb4f8dfa3fbb49fc9d8418e82635a66d3f149ae9a1e0a9f8ad157032f` | `d50b17196ff855f9391ab80cbd023356092be7a5093298cc751ee584d97818ba` (11) |
| `Toy.Tbaa.exec` | cited | none | `0e4b5619d8e2303c0b3f9d269b32d8c915b99defc3ff816524ce20d7c41958a8` | `bf6a863fe152c950bac112d41e89d23e9ca27c27e631f7d3f6e9c464742bb49c` (25) |
| `Toy.Tbaa.Outcome.trace` | cited | none | `d12fbd1aca631d21f346a0ecef05ce7db9a9fe536482c70a226ecc22c06a4710` | `85b381cfe2a755c4f09e607d64b7d260636e63a44090d66cb9de44c19d7dae54` (5) |
| `Toy.Tbaa.Allows` | cited | none | `fc62dd8e62523fa860a954853a0499b6b57af65c46012d9b5c3b83cfbc0d3150` | `85b381cfe2a755c4f09e607d64b7d260636e63a44090d66cb9de44c19d7dae54` (5) |
| `Toy.Tbaa.Beh` | cited | none | `8c841bd11c8726d94427a2169a8eb694c2b51312a39d5e8dabc220cbd480c5a5` | `bf6a863fe152c950bac112d41e89d23e9ca27c27e631f7d3f6e9c464742bb49c` (25) |
| `Toy.Tbaa.Refines` | cited | none | `1bcd42635ab015a343a68e8e996ad8b5b11b9f29eed0c442c11650b6c75bdbba` | `85b381cfe2a755c4f09e607d64b7d260636e63a44090d66cb9de44c19d7dae54` (5) |
| `Toy.Tbaa.ReorderSoundFrom` | cited | none | `88760f2ea78acc8f462b8f77b1ad48eb31c6df02c169d65033afa215667324f6` | `253f93a31da1fdeb327cc993516c32a3b57a5b90f1ac9a6b4c87ff1fa6f73ccd` (22) |
| `Toy.Tbaa.ReorderSound` | cited | none | `4dbf1b1a92da088d17c76e771ab6a7c7f37e80f6966ccf1414c176b5c6ac2338` | `253f93a31da1fdeb327cc993516c32a3b57a5b90f1ac9a6b4c87ff1fa6f73ccd` (22) |
| `Toy.Tbaa.reorderSound_refl` | cited | none | `e00f4eb6ff9465cd396b81965bb62ffd68ec0dd9cf8fc956e8d8c3125e3900ee` | `acacb24754f4b7d3610bd8f94e5e1ede49f97f365bbca7014a8cc7bf49ae33f7` (49) |
| `Toy.Tbaa.updReg` | cited | none | `253385bd994b35917782a512927b6c7605fb5fef3c75b1001eb5503de7b11185` | `63f9dc30dd2cff3847061dfb415299c83b753b3b0be7fd553b01bc3ddcd64e45` (3) |
| `Toy.Tbaa.updRange` | cited | none | `898b562949863ab768555451e34c8909645154266af940f3429694d65de3947a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.readRange` | cited | propext | `33ebde8f96301f5f72f4f952d7c9b25e91b7f59ccec9866d47453140d7fba7eb` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Eff` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Eff.tag` | cited | none | `9591fc0af437d63852913c4323e33c9a1b9895aaace28ceb99bc4a4653876bfc` | `4bf29ba6486eb52980eef3166cd0ac30b2090d8020cf4cd99b58482405587b13` (8) |
| `Toy.Tbaa.Cell` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Mem` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.St` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Compat` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.stdCompat` | cited | propext | `681340293c3b75890a26ef6a9e5eee04542e05730c8f8da7239ad35320325b72` | `ebbad8b2f3c8d8d3acae8ceda62b9d10540ced632926e8544d3881644f728e12` (6) |
| `Toy.Tbaa.strictCompat` | cited | none | `681340293c3b75890a26ef6a9e5eee04542e05730c8f8da7239ad35320325b72` | `ebbad8b2f3c8d8d3acae8ceda62b9d10540ced632926e8544d3881644f728e12` (6) |
| `Toy.Tbaa.ECfg` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.stdCfg` | cited | propext | `8eb2837268d172c816e4cad81198825bb4a4b092b06fefa833b20345d2e5917a` | `b6b48e6ea76a55f73f9f67a3a15ca64b75dd499dc3532a109b6d95669b99d7af` (8) |
| `Toy.Tbaa.TagsOk` | cited | none | `40d5ce2c7a752dcd469f94243a5a2a6935d3dd0d56158315916f4897d40e59cd` | `33ee1d41cccb64743e5de5410eef6d6033de65dab427f8b19caeb1d55e598f6b` (18) |
| `Toy.Tbaa.DeclOk` | cited | none | `40d5ce2c7a752dcd469f94243a5a2a6935d3dd0d56158315916f4897d40e59cd` | `33ee1d41cccb64743e5de5410eef6d6033de65dab427f8b19caeb1d55e598f6b` (18) |
| `Toy.Tbaa.storeCell` | cited | propext | `bfdca416899e155b38d00506cdadd5194347cea79ca68be1cee5a9c469bbfdf1` | `167a7f8f6509a291a4ce029859fbf0c8d573b9b54ec9b01a93dde21f34e9f102` (18) |
| `Toy.Tbaa.copyCell` | cited | none | `3c91b14f1f3afeb117dc28bd0dbe6c78e51907ff0ef3f64a324d3dfd7de26cda` | `38419805ca76bf9b93e0b49266932800642bd90341ca96ceb2e2488005d2b421` (11) |
| `Toy.Tbaa.copyFrom` | cited | propext | `4810f599ac49d306e8cc5f554b51b569c1e13d58f0d1e32ed576bea6c329a495` | `38419805ca76bf9b93e0b49266932800642bd90341ca96ceb2e2488005d2b421` (11) |
| `Toy.Tbaa.CopyBytesOk` | cited | none | `8841f1625667e74c5c2c4c83d9f170c9bb3b9e8129a83b7b71a257d0d86fd27c` | `ea3b97176093853be5339223e11f44890529c43b7b017f5bb338bde1473d041a` (12) |
| `Toy.Tbaa.stepE` | cited | propext | `89c5a8d4add4f1648a66496608b869cae5d7a345dabf980cf04f72e3df00340a` | `d16e07059f0b836787174ea80e43a819fff12e1e53a8642ab0dee87dd3db04a3` (38) |
| `Toy.Tbaa.UMem` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.USt` | cited | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.stepU` | cited | propext | `eb6591a39a409024b0b775cc161935fb33cdb24aefdb80dc05a65218e7ded5a9` | `cd0acd387fc5549ae4172de34a787ba2d0cfc634a4f7822b12dd6bb4306dbd39` (25) |
| `Toy.Tbaa.erase` | cited | none | `b66701c81c7955f20eea081f79d271db931c45a8af4b1e5b2018a46eae16acef` | `2ec2559299b3932642deb4e62cbf8c21b9c978d1b60b39ccf93c04d359fd65e8` (19) |
| `Toy.Tbaa.NoCommonLeaf` | cited | none | `c21728917ee27785bad85f2b86eda515d50e9da2ebd236dbecaa8cd2b7d51773` | `210ec6da3cdb0b1ecf9e4cf8e1110257eeba8af80349eeb66a28875b33cc7caa` (6) |
| `Toy.Tbaa.RangesDisjoint` | cited | none | `09bc01f36ba224268694ce3a10172ba9542cf54732f2a993ca4a7592a5cb655d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.Tbaa.Eff.isDecl` | cited | none | `ad8aeb0e2ae58c028dabd06fda49794acc8b65a69cb2276c9c9a3b134b20900a` | `4bf29ba6486eb52980eef3166cd0ac30b2090d8020cf4cd99b58482405587b13` (8) |
| `Toy.Tbaa.DeclaredOn` | cited | none | `0263d2455e83fdfef1b8cd8df4a66706e7eabe560c64f99a484663f677388580` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.AllocatedOn` | cited | none | `0263d2455e83fdfef1b8cd8df4a66706e7eabe560c64f99a484663f677388580` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.ReadableAt` | cited | propext | `c768048cec25113d4229b486bbe8281a1a4a422fde1b8b0850b706aefb369b0b` | `44654868b8e3a4ca06a4e7e84486843ce6520f9633cb1f30e1e3299e42fb6284` (23) |
| `Toy.Tbaa.ReceivesAt` | cited | propext | `e286d4278aba7ab6525c8df127eda7d4b65757671b8fc0a0ad3be4e8ac5ae617` | `8eb3a1a24dbba862a2c24bbdab58b174d76515682618d00eb2a12a39b37ba021` (22) |
| `Toy.Tbaa.memcpyLoadCheck` | cited | propext | `01ad144dd0d4e8b0301899075fc15be9dcb7870e75abe1a5295de31ccb53b73a` | `38419805ca76bf9b93e0b49266932800642bd90341ca96ceb2e2488005d2b421` (11) |
| `Toy.Tbaa.MemcpyLoadOk` | cited | propext | `34d07a2ca0a8c798206da31c5831bc8ad072782d3e1da6a39e9c5ec8fcf0323c` | `8eb3a1a24dbba862a2c24bbdab58b174d76515682618d00eb2a12a39b37ba021` (22) |
| `Toy.Tbaa.valsAt` | cited | propext | `3be830e5454744273b4266d7119e083794771bd644ba70e608bab23a7e8fcf46` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.typeFaultsB` | cited | propext | `9ab21e742d11e8898da274a2c32e4a260077c313023dc6cf1759175c1a3a65b1` | `04a585497bef77f831a5d416aac42ca6117fc6959e9d4da968275b5c58211308` (31) |
| `Toy.Tbaa.TypeFaults` | cited | propext | `173639d027e4e290463034475afb30e3f913b543636391c86e50890eeb11a2ad` | `04a585497bef77f831a5d416aac42ca6117fc6959e9d4da968275b5c58211308` (31) |
| `Toy.Tbaa.UDefined` | cited | propext | `c3d020edc5cf64d9386abc6d12f9c6840fe02d86643164e5b036b7db9cd1bdeb` | `eb478f5d27222bd62f9dee8e92555e84feffa5e74fddfbef6195bbfe502ca4d5` (18) |
| `Toy.Tbaa.freshAt` | cited | none | `6e24164572bf4627706d36d587a217789bfea03d8aba47dec7a23fafb3627a86` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.declSt` | cited | none | `143ea06ce4c4a76a2194817587c9395c84f5165134e1204f1442396bc2b61bea` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.declPairSt` | cited | none | `fef9d9fa3ce1dc6d5e196e0176bc15ac860c7e7eb5e7fc2e245a819c60675b9c` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.St.withRegs` | cited | none | `7ee5dc3a755b63763071db3dc9b88c69dfb6bb9d3545dacd79b192b1c9c63059` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.regs2` | cited | none | `4415e0345865fb9de1b25335c77de61dc30489b384e3befff4b5658d278ed9c8` | `63f9dc30dd2cff3847061dfb415299c83b753b3b0be7fd553b01bc3ddcd64e45` (3) |
| `Toy.Tbaa.objSt` | cited | propext | `b735976080c3fc8e4aeef52459748685ddec11cc69b8ad1e2eb21e9fe6be7fcd` | `8eb3a1a24dbba862a2c24bbdab58b174d76515682618d00eb2a12a39b37ba021` (22) |
| `Toy.Tbaa.Examples.ones4` | cited | none | `5bd284638acdedcbb87d064a15424369f8d86d8fc66cb771e0f56727a696a898` | `250538aff357a27395353d31e8c7e55c4c6138a0a07ed2c8a913108f504daee7` (2) |
| `Toy.Tbaa.Examples.pair_layout` | cited | propext | `33ab1fb4df7eb2531a29f59e1ae8cd9db89189efcfde117ba94209112aa7b16f` | `e3c04522ce23a954b9d12cf8e365c31fa53b4017eaa2206bca4dd5f65e249088` (17) |
| `Toy.Tbaa.Examples.pair_byte4_not_u32` | cited | propext | `4b96e2e61135b78fe1d648494308aaf6ff85570b84c95ffae4f09c4f61c73c13` | `b1c2d35cc6e9c8e7bd6efb1876e89168b7258c0b22d8cd7d4573dcbf67867f82` (16) |
| `Toy.Tbaa.Examples.f32_valid_any_pattern` | cited | none | `70f7d87ff3a445d9387160b757685e4b1188f58a53e72e5ccc9b9bc33742d78d` | `0872c817075f6e12c4fb0107976fa6781c465aa673624a8599ca7958e1db83c1` (19) |
| `Toy.Tbaa.Examples.u32_invalid_short` | cited | none | `3b7c7bbdd1853a73171f96770539e2a247641920f4d4eb7f2388ecec2b7f3e00` | `0872c817075f6e12c4fb0107976fa6781c465aa673624a8599ca7958e1db83c1` (19) |
| `Toy.Tbaa.Examples.stdCompat_admits` | cited | propext | `d504cd7cd380ffadc7ad26dbd00789644babfdf4821a6f0a19a6cd1d18eba555` | `eba2071919b7515a7ded6b18e2691e46a52231e4f0cfda9ce8bae4bff5e61063` (15) |
| `Toy.Tbaa.Examples.stdCompat_rejects` | cited | propext | `55fcba61dacfd344bc0b5f048742a3503ac8b44662005af614c9c722ae442d13` | `eba2071919b7515a7ded6b18e2691e46a52231e4f0cfda9ce8bae4bff5e61063` (15) |
| `Toy.Tbaa.Examples.strictCompat_admits` | cited | none | `7820632cc1115ad366cae0f25ba130150c9e853977c2acc183ff7cc77592b948` | `35eb2d0487171e17ee7e88d1a0ece92fdb118ac0759587b37ad9a125cb44cc99` (14) |
| `Toy.Tbaa.Examples.strictCompat_rejects_byte` | cited | none | `2d7fb2bd48201137e6a66ab56289d39671622c54ed5a5fa55f5049a8aa9ca57f` | `35eb2d0487171e17ee7e88d1a0ece92fdb118ac0759587b37ad9a125cb44cc99` (14) |
| `Toy.Tbaa.Examples.noCommonLeaf_admits` | cited | propext | `adcdc9ea0a7d806e60c365fed152d1257a800f1b18fc193a4e229a0c79809d88` | `01827a83424e97634d8810b25f6d42f2b3db7ae220ff3be899194f3b009033bf` (16) |
| `Toy.Tbaa.Examples.noCommonLeaf_table` | cited | propext | `c05af396d38baf3529bc2f81e58914756857e36d29d76c038c01b577eade8d16` | `01827a83424e97634d8810b25f6d42f2b3db7ae220ff3be899194f3b009033bf` (16) |
| `Toy.Tbaa.Examples.noCommonLeaf_non_u8_struct_instances` | cited | propext | `9837cad039e18713cfffdcb1f7a12f4e6fb54cef8bad5086309a88415fa27d26` | `01827a83424e97634d8810b25f6d42f2b3db7ae220ff3be899194f3b009033bf` (16) |
| `Toy.Tbaa.Examples.noCommonLeaf_rejects` | cited | propext | `f3378014933faddb12984b91d20307c4da6af930a1b04cb43ecb9a91f165940d` | `01827a83424e97634d8810b25f6d42f2b3db7ae220ff3be899194f3b009033bf` (16) |
| `Toy.Tbaa.Examples.rangesDisjoint_admits` | cited | none | `e6fbef137381c746c5c11e209633207b16678be575eff54b8de28ecd8c2a2eef` | `3e669c99cd756d9e45574db553e00677d1037b29f6a68ed34a80c4d050325ff6` (1) |
| `Toy.Tbaa.Examples.rangesDisjoint_rejects` | cited | none | `0bb4567e366232ee297b1e8218ffee3b72738a8d4bf27972036ddbbc8cd6d7ac` | `3e669c99cd756d9e45574db553e00677d1037b29f6a68ed34a80c4d050325ff6` (1) |
| `Toy.Tbaa.Examples.declaredOn_admits` | cited | none | `9431a997e267dacae9c94fa327f26a42f5c6e53ec797626a7b80bd7c85acd13d` | `8b0e23af2e9f18abd7ea8ee956dc06f20448a38131e6718654a3ef1ee000d009` (25) |
| `Toy.Tbaa.Examples.declaredOn_rejects` | cited | none | `5083f916eeb51bf91fefa8a8464de92d4ada0b3000006b70f4ac04cbc72062d1` | `07b835f1619183944a7123193f2cb479a3091782748ae6a3259bf4c5d865f3d4` (25) |
| `Toy.Tbaa.Examples.allocatedOn_admits` | cited | none | `2cf152e4fdbdb67525dd93de1ca596ce21b3f757fd07037daa7379a2bd30cbc2` | `fafde7d243cd296adfc52a43fdfe4eada219095e5f1fdf4d2b9dd178652e0daf` (25) |
| `Toy.Tbaa.Examples.allocatedOn_rejects` | cited | none | `70ed2460f6d5e4e155d29a3842d694f427cd1bd49330db905fd1e9ad06d397d2` | `d4ec2d9bc30823306eaaec5f72644c876f6e610c6ff56b3280558f4bf25ec245` (25) |
| `Toy.Tbaa.Examples.readableAt_admits` | cited | Quot.sound, propext | `cab7454802766fb9e8622b44349b7adce70c1c1910c88bfe2450b55e018723be` | `1538c17dd5efa6d87831249ed8f8d41e83806be6e6912453b48a238005d13cdd` (52) |
| `Toy.Tbaa.Examples.readableAt_rejects` | cited | Quot.sound, propext | `50f86ba83148afa1b54e1519e627498d8df177a9504b93fb7ab206b72f1d3f2e` | `1538c17dd5efa6d87831249ed8f8d41e83806be6e6912453b48a238005d13cdd` (52) |
| `Toy.Tbaa.Examples.receivesAt_admits` | cited | Quot.sound, propext | `ff443c087f36b6dccbe74c714cf6de6374814b7ec0e47af5560e43574e080814` | `94080a43b20698a44a191dc18eff856ab7b1a17758eb2de3b5eb7bf0b03fe244` (53) |
| `Toy.Tbaa.Examples.receivesAt_rejects` | cited | Quot.sound, propext | `66e5411f11001f053fcaaad1a5782426aa89a5c78c06c308b5577d02cbe5a8b5` | `94080a43b20698a44a191dc18eff856ab7b1a17758eb2de3b5eb7bf0b03fe244` (53) |
| `Toy.Tbaa.Examples.punIntoDeclSt` | cited | none | `b86ba8748fc1ac0a9d0d9c63a4dc7e3f9175b065ca811400493e5a60abdc7889` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.Examples.memcpyLoadOk_admits` | cited | propext | `9de9996c092711c737dc916f8d607b489d871d552de553b5ac4de5b033a3e094` | `5d59fd5691e95fa3c676f072f51928bc023013cbad25f139319fab494adb0622` (55) |
| `Toy.Tbaa.Examples.memcpyLoadOk_rejects` | cited | propext | `76f2a63575f3f9fba202e13ea0d0c148a89c18639edf46d64430ffce86eb2347` | `bd5db9cc217e494b44fcb9618976f1169a730059264706562d788773e8bab9b3` (53) |
| `Toy.Tbaa.Examples.valsAt_example` | cited | propext | `a4d198cfc2a8807d591b2e01158b2e99751666432cc81a08704fe49e5d6f3cbb` | `97eb15d47c0440ded2a7074d75e9a42738af20df9f8035df4da73d1cfeb2aeed` (37) |
| `Toy.Tbaa.Examples.stepE_same_type_defined` | cited | propext | `196297f247955e5ca8c8e93f5c2a7e6073f574079969fd2584917e6df49a93a8` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_punning_ub` | cited | propext | `e06f0c854e985a95375e2cdfa581ed50034330ff6afd4966ce162e81fdf8b1e4` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_byte_read_defined` | cited | propext | `fea6aeadb67e7af07c626da5b5b07c0df8c53fc05428a074a483fc75b83a632a` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_allocated_retype_defined` | cited | propext | `d32c9d9c0345c8927cd82fa99ac90601db808e5e4b87a20a75a4ebc06cb7e465` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_declared_store_mismatch_ub` | cited | propext | `887134d727d69a3b0e2893b70949e2463aa0db75d6b4008fdeceee60ff7e3e45` | `31a466f53ce988cffb61ce86546078e411c1401dd979bf723241d8a7a09788ca` (108) |
| `Toy.Tbaa.Examples.stepE_memcpy_copies_type_defined` | cited | propext | `3927dda0d878f384022d57de6b35f17123095b462a1134a855d0835673e60d1e` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_memcpy_copy_punning_ub` | cited | propext | `bbe03c77edecb33dbe7693f8ffc95728548bcf0b377670f0fdc6321ec7a90121` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_memcpy_into_declared_defined` | cited | propext | `583eaf77f9a821f08f9ce04cb3427cb98c15775cddef9e7162545d47fb892632` | `e7fa7a8a623a0022e0efe3500bb9465f3197a018d6389db1f9dbd02a77d295a7` (107) |
| `Toy.Tbaa.Examples.stepE_pair_member_access` | cited | propext | `c74d0c6769a1eb1b84df260a1b1c5a58ea7783235e3d9bf1b529e0bd564dda86` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepE_pair_load_from_member_stores_defined` | cited | propext | `849b9a9bab8e84933cd3892fd894a82d2beec41fec68c808bfbc499782e846b4` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.byte_loop_copy_does_not_transfer_effective_type` | cited | propext | `530fce9f7da1f26dbbcf1fbc54ddc8a469c0136b1ae999c82a474152684a9ee4` | `0120a34d51def907a887aafa37fd24ed5fc678a87b63e7cce47aab78c83af004` (106) |
| `Toy.Tbaa.Examples.stepE_unallocated_ub` | cited | propext | `2187d8fd6b95e1c6744441cebb07841de05b5d9bbece0ae1477a04258ad6eee3` | `97f564683e07849469c5a5aa17292b0762004e1e367aa60c44dd39aee897e55e` (108) |
| `Toy.Tbaa.Examples.stepU_punning_defined` | cited | propext | `26c48b46948d5bce357454531db6beb10fa311dc04c2f3838e401ff14be2c551` | `063071f17a7fc22aa1d17075643054c045c34ebe4d3d553bb480bcd6c80a2066` (84) |
| `Toy.Tbaa.Examples.stepU_unallocated_ub` | cited | propext | `13e36e5ec2ecdecf554a5ca12d454238345646bebcdd349793aa981a7c1f5239` | `063071f17a7fc22aa1d17075643054c045c34ebe4d3d553bb480bcd6c80a2066` (84) |
| `Toy.Tbaa.Examples.erase_example` | cited | none | `9f6f5b9e7ecc165a89afd2ffc7a90098de06c3fc5cefa942368addcbdd3b1a64` | `4ecdbcf251a657f74f25e73efacd9857ed0b41d9bca19af4a271a1fe9b463c6b` (26) |
| `Toy.Tbaa.Examples.typeFaults_admits` | cited | propext | `925fc986301fc4b86ab7ce00834451748491caadfa6f0bcb3c403553b7956a57` | `a73a697044d7426626dc1b27df497d1b9a845873d7af538d753f4963a84efe8a` (105) |
| `Toy.Tbaa.Examples.typeFaults_rejects` | cited | propext | `f3dee93a184938be474ba58de626f6cde1afdbf424b9382b90ced29eb7a5ec9f` | `957216c611d1d9cdd4413c8097b8536d78aad557a485eca2530b7e996f0adcca` (106) |
| `Toy.Tbaa.Examples.typeFaults_same_type_nonstandard_cfg` | cited | propext | `20bf0d29f8bf9bbc613e189d77e8d76d7ffefed97fe72f33dfad0d465cbed4c6` | `29ac192ed88b2cdd4138c24d6b7998b8f63be1e2d949be5b590e912190799a25` (98) |
| `Toy.Tbaa.Examples.uDefined_admits` | cited | Quot.sound, propext | `8d43853eea95c1d57bcc7f6f1d3ce61aaa3cd69ad915f285bc3e25275fdfacc7` | `8f3ee9803c62c5f2a26873fa34eee274fe5516b15accce0d1467f023e1cf5d68` (85) |
| `Toy.Tbaa.Examples.uDefined_rejects` | cited | Quot.sound, propext | `37d91fd02fd15725c0a5a44e968ef480ea232cafe74d7c018d4e7126e15c7a91` | `8f3ee9803c62c5f2a26873fa34eee274fe5516b15accce0d1467f023e1cf5d68` (85) |
| `Toy.Tbaa.Examples.refines_admits` | cited | Quot.sound, propext | `b00c2c4fab5c01ee4233a22bdfeece8d22b87f65f128e5b389baa5c7d0658048` | `240fe7d91a7dad95c5b51db36160c23b7f62d450b5e2e150972795be8feda34d` (12) |
| `Toy.Tbaa.Examples.refines_rejects` | cited | Quot.sound, propext | `30fbe472e404b588bf85abc3c0b1653f5385e21494cbddb19a8da58ff5f44ad8` | `240fe7d91a7dad95c5b51db36160c23b7f62d450b5e2e150972795be8feda34d` (12) |
| `Toy.Tbaa.Examples.reorderSound_admits` | cited | propext | `a14784c59f525501ba3f3fc6b1900b5ed8caa0da8de19517b8eb27b5f1130d40` | `5c58dcb6a6ed6de339cdfbb32254de46423a795e909148fc272c379d85b255d8` (116) |
| `Toy.Tbaa.Examples.reorderSound_rejects` | cited | Quot.sound, propext | `cb391a14d1958ddc6825f69c071d83daa3db68fd6f085c000307313878434ef5` | `5c58dcb6a6ed6de339cdfbb32254de46423a795e909148fc272c379d85b255d8` (116) |
| `Toy.Tbaa.Results.ones4` | cited | none | `5bd284638acdedcbb87d064a15424369f8d86d8fc66cb771e0f56727a696a898` | `250538aff357a27395353d31e8c7e55c4c6138a0a07ed2c8a913108f504daee7` (2) |
| `Toy.Tbaa.Results.twos4` | cited | none | `5bd284638acdedcbb87d064a15424369f8d86d8fc66cb771e0f56727a696a898` | `250538aff357a27395353d31e8c7e55c4c6138a0a07ed2c8a913108f504daee7` (2) |
| `Toy.Tbaa.Results.uWit` | cited | none | `12064240cd187f17f29397442bf4b9165f91577329d4b07aec5e8592c4918505` | `6fa01ca6d1c2ad512e7aa2620667a6443aedea5d7b5257828d74a4a4ce41b535` (12) |
| `Toy.Tbaa.Results.same_register_premise_refutes_disjoint_hoist_U` | cited | Quot.sound, propext | `19a476e74ae6aceffbd1c796cd82adad261a0968eded549c7fa421d79e19d462` | `85ac6ec18e660744e1d837ca266f829685919bf54ad4e4caed861eecfe6ebd1e` (80) |
| `Toy.Tbaa.Results.readable_source_not_necessary` | cited | Quot.sound, propext | `94dd0ea857197ede6d97f0b2c22f6f395f2c13314d62a21eaf684dc17f7a4158` | `9047229254c919c1f6add1fbbbed4fd970bdcfba90759ee19bf4822a128bdf62` (111) |
| `Toy.Tbaa.Results.copyIntoDeclF32` | cited | none | `b86ba8748fc1ac0a9d0d9c63a4dc7e3f9175b065ca811400493e5a60abdc7889` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.Results.partialOverlapPunSt` | cited | none | `b86ba8748fc1ac0a9d0d9c63a4dc7e3f9175b065ca811400493e5a60abdc7889` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.Results.memcpy_overlap_defined_examples` | cited | propext | `e9644db1e948a19f18aac620ec0f2e5e1c03df6ee7828e553c90ad7e373ab57b` | `7d67b63667b782e7e98366706581d10d262c8ed3cb20a8bcf05b2115ca3bd5a1` (121) |
| `Toy.Tbaa.Results.strict_typed_load_above_byte_store_not_refines` | cited | Quot.sound, propext | `50100bb266cb9befef5e77ebad108d8d446c3baba9167eb2be05e2fdbe3df5af` | `8da3cc0da57bb804498157eac20e6c1af2e20005a647328e104e39db9fb9f7d3` (117) |
| `Toy.Tbaa.Results.byte_copy_u8_case_is_same_type` | cited | propext | `fe0e52b2dad4eed4c5495876dc48929b1f3c5358c6a8836961d51ad0f947aabb` | `b59cad1145a569c016050bbbaf1d0116a0412c905ecdd181caae6f0fc6b70622` (130) |
| `Toy.Tbaa.Results.mixedCompat` | cited | propext | `681340293c3b75890a26ef6a9e5eee04542e05730c8f8da7239ad35320325b72` | `ebbad8b2f3c8d8d3acae8ceda62b9d10540ced632926e8544d3881644f728e12` (6) |
| `Toy.Tbaa.Results.byte_dichotomy_not_exclusive_for_pair` | cited | Quot.sound, propext | `0ec474dc5b36a1906bc42999f14e783a387e5ad3f102eac6595ff8e0b7b65957` | `d08e6202d79cf5180d3c39d946c79edd58a45b2ea798ec25bb16841a4976e915` (119) |
| `Toy.Tbaa.Results.declared_store_mismatch_diverges_without_loads` | cited | Quot.sound, propext | `c25cfa1751f1ea2986297b34d3a7d1d6fc0bba539817b36f95271c06c52f4235` | `c896cf51d6e54a04c08f99ce040452425ab5cbe3a6c5eb00c6ef73f4d0e25019` (140) |
| `Toy.Tbaa.Results.typeFault_unmasked_despite_later_base_fault` | cited | Quot.sound, propext | `dc4564eeea8ea064daf3c095831870ad58177052422d606cc52141de00374558` | `86db4747099db041c5d8e1d42585338b0d65733b31cd1e45ab80096d102380d2` (137) |
| `Toy.Tbaa.Results.behE_not_refines_behU_iff_typeFaults_of_uDefined` | cited | Quot.sound, propext | `5a12c9a70fd85ba16639dcef81b03c2e920a1a9511f382d701b16b8627fa0a05` | `1c45728baefae005cb9eab34cdee74a13fef3357c79a114cf47bb126ec2048ba` (130) |
| `Toy.Tbaa.Results.behE_eq_behU_iff` | cited | Classical.choice, Quot.sound, propext | `316caa588512284c16a0887983904811f993f866f6d639258ad43b65ede8fed5` | `4ae37802a9967a481f8bdfd1d793001c569cee07ae2abd2148ecfdafe0eff555` (129) |
| `Toy.Tbaa.Results.declPairThenFresh` | cited | none | `7c505aed070635b26cedfee37e5645672aa23fc2d1575e11669745adacf6e3f0` | `efff3eb6756ab50c4463120ea3a5aea1bfb696d283e71ba4091910b220a3ec70` (16) |
| `Toy.Tbaa.Results.store_store_reorder_sound_E_of_second_declared` | cited | Classical.choice, Quot.sound, propext | `4f887399e973c14df3b5233111c68045eb9ced453902b0e103c51d32225e7ff5` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.store_store_reorder_sound_E_of_disjoint_ranges` | cited | Classical.choice, Quot.sound, propext | `eb8e599c06d7f3ee43c7d0eab3e6bc248c9fc7eda263405e4ec895a94ade963c` | `abfcb6d0e43d0320d6ee226bf133c99d5f5bb26894e55e425bce88ec2d7fee39` (117) |
| `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_store_range_declared` | cited | Classical.choice, Quot.sound, propext | `25818bda44833466d353653da74b57930a5cb0b1daf657d5add9bac21c1bd6ba` | `f2fe10033ea6bc4455f90e12e79454771b52689b67401f4436b84cbceab3bfcf` (118) |
| `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_disjoint_ranges` | cited | Classical.choice, Quot.sound, propext | `b6aa2669a12cc7f2eb3be650e2564e24ea286f230df46da957b97e2a24b5da37` | `abfcb6d0e43d0320d6ee226bf133c99d5f5bb26894e55e425bce88ec2d7fee39` (117) |
| `Toy.Tbaa.Results.allocHoistSrc` | cited | none | `f589334b48b5e0cfd9ec5ef5eb326d8fa47afb50075edb60f8e5ed9e151e2eac` | `5ea6dac47fb86946fb40aeff237a8f73da8cb3baf36e0bfb0cd3c7be5dd3a704` (15) |
| `Toy.Tbaa.Results.allocHoistTgt` | cited | none | `f589334b48b5e0cfd9ec5ef5eb326d8fa47afb50075edb60f8e5ed9e151e2eac` | `5ea6dac47fb86946fb40aeff237a8f73da8cb3baf36e0bfb0cd3c7be5dd3a704` (15) |
| `Toy.Tbaa.Results.declared_and_allocated_preconditions_incomparable` | cited | Quot.sound, propext | `74a732526a897a5306536fe45a411f1ade1ff6cc9f0432ccfd3232e4ac9cfcc4` | `fc00471bd9ac7a918710232ceaaa7d54cea444c65685ddddb5b9869d1381da96` (123) |
| `Toy.Tbaa.Companions.sink_load_below_store_witness_runs` | cited | Quot.sound, propext | `b1e20fd8e709a148de3f45d8196add08f307f69bcb053183a76afc216ee836f8` | `6a6ad75726610897c40e55cf5efc5961529f24fd5d650c2ca0df3a9dd01024d4` (125) |
| `Toy.Tbaa.Companions.store_store_swap_witness_runs` | cited | propext | `1994c883d469da05dc0bdcee6b8bbe0043cd2c0b7c58be656a2508e576f71108` | `156d597d13a1fc3d651b9a2e24f559e7137fc888a7516de96b14e674b425fc37` (122) |
| `Toy.Tbaa.Companions.store_swap_scheme_fails_at_zero` | cited | Quot.sound, propext | `c35e73a51f66e488377d48a1c288c4267bdf569dc8e816be54521b8eb79343dd` | `f3b485e28cb5f9c335e747fbf198ee4db075cdfcbd6ae220d29e075b867fdbf3` (122) |
| `Toy.Tbaa.Companions.valsAt_unallocated_example` | cited | propext | `21aa069e459b57c7e2ee7895cb9b4fbce810c80c29fb589580444d26b29ae221` | `97eb15d47c0440ded2a7074d75e9a42738af20df9f8035df4da73d1cfeb2aeed` (37) |

### Primary sources

- Lean 4 toolchain release `v4.34.1`, repository leanprover/lean4, tag commit 5045d0056413266e57c625dcd7c365b10e377c52 (tag reference read from the GitHub API).
- C++ working draft N4950 (2023-05-10), [basic.lval] paragraph 11: 'If a program attempts to access the stored value of an object through a glvalue whose type is not similar to one of the following types the behavior is undefined: (11.1) the dynamic type of the object, (11.2) a type that is the signed or unsigned type corresponding to the dynamic type of the object, or (11.3) a char, unsigned char, or std::byte type.' Official WG21 document: https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2023/n4950.pdf (title page: document number N4950, date 2023-05-10; paragraph 11 of [basic.lval] checked there); also checked in the HTML rendering https://timsong-cpp.github.io/cppwp/n4950/basic.lval.
- Robbert Krebbers. Aliasing Restrictions of C11 Formalized in Coq. CPP 2013, LNCS 8307, pp. 50-65. https://doi.org/10.1007/978-3-319-03545-1_4. Coq development: robbertkrebbers/ch2o, commit 1afb3f615db053b741341e9bfd1d5c65bddea641. File memory/aliasing.v (lines 170-180, Lemma mem_non_aliasing) proves a memory-operation lemma: for addresses a1, a2 of types σ1, σ2 that are both annotated 'frozen' (no union type-punning) and are not unsigned char, either all their offsets are disjoint, or σ1 is a subobject type of σ2, or σ2 of σ1, or a lookup at a2 after a store to (or force of) a1 is undefined and, symmetrically, a lookup at a1 after a store to a2 is undefined. The file contains memory-level lemmas only (ref_disjoint_cases, addr_disjoint_cases, cmap_non_aliasing, mem_non_aliasing), no theorem about reordering program instructions. Objects get their type at allocation (memory/memory.v lines 27-31: mem_alloc sets τ := type_of v), so stores do not re-type allocated storage, which is why that lemma is symmetric whereas the toy's R1 is not (R1b).
- Robbert Krebbers. The C Standard Formalized in Coq. PhD thesis, Radboud University Nijmegen, 2015 (IPA Dissertation Series 2015-22): the CH2O formalization of the C11 standard, including its aliasing restrictions.
- Amer Diwan, Kathryn S. McKinley, J. Eliot B. Moss. Type-Based Alias Analysis. PLDI 1998, pp. 106-117. https://doi.org/10.1145/277650.277670 (introduces type-based alias analysis for a type-safe language, with disambiguation by declared types and by field types; it does not consider C effective types or re-typing of storage).
- ISO/IEC 9899:201x Committee Draft N1570 (April 12, 2011), section 6.5 paragraphs 6-7 and footnotes 87-88 (effective type; the aliasing list, whose last item is 'a character type' and whose fifth item admits an aggregate or union type that includes the effective type among its members). https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf (paragraph text checked in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5p6).
- ISO/IEC 9899:201x Committee Draft N1570, section 6.5 paragraph 6 (text checked at http://port70.net/~nsz/c/c11/n1570.html#6.5p6): a non-character store into an object with no declared type sets its effective type 'for that access and for subsequent accesses that do not modify the stored value'; 'For all other accesses to an object having no declared type, the effective type of the object is simply the type of the lvalue used for the access.'
- Chris Hathhorn, Chucky Ellison, Grigore Rosu. Defining the Undefinedness of C. PLDI 2015, pp. 336-345. https://doi.org/10.1145/2737924.2737979 (Section 3.4, paragraph 'Strict Aliasing': declared types are stored with object representations and, for malloc'd memory, the type of the last object stored is tracked, which matches the toy's allocated-storage rule for typed stores; that paragraph does not discuss memcpy or the transfer of effective types by copying).
- Kayvan Memarian, Justus Matthiesen, James Lingard, Kyndylan Nienhuis, David Chisnall, Robert N. M. Watson, Peter Sewell. Into the Depths of C: Elaborating the De Facto Standards. PLDI 2016, pp. 1-15. https://doi.org/10.1145/2908080.2908081 (the gap between ISO C and de facto C practice, including effective types; the Cerberus semantics).
- LLVM Language Reference Manual, section "'tbaa' Metadata", llvm/llvm-project commit a2f1d1aeb6f5c700ac9a15592b6f81c3ec41e6c6, file llvm/docs/LangRef.md (line 7540: 'In LLVM IR, memory does not have types'; lines 7609-7611: 'If memory accesses alias even though they are noalias according to `!tbaa` metadata, the behavior is undefined.'). This is an access-pair rule over untyped memory, not C's dynamic effective types. Lines 7593-7609 define when two access tags alias, through an `ImmediateParent` relation on `(BaseTy, Offset)` pairs (for a struct type, the member type at that offset): 'A memory access with an access tag `(BaseTy1, AccessTy1, Offset1)` aliases a memory access with an access tag `(BaseTy2, AccessTy2, Offset2)` if either `(BaseTy1, Offset1)` is reachable from `(Base2, Offset2)` via the `Parent` relation or vice versa.'
- WG14 Defect Report #236 (submitted 2000-10-18; record version 1.6, 2006-05-08), 'The interpretation of type based aliasing rule when applied to union objects or allocated objects'. https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_236.htm (Example 1: an int load followed by a double store to the same allocated storage, where hoisting the store above the load 'changes the computation'; Committee Response: 'Both programs invoke undefined behavior, by calling function f with pointers qi and qd that have different types but designate the same region of storage. The translator has every right to rearrange accesses to *qi and *qd by the usual aliasing rules.').
- The Rust Reference, 'Behavior considered undefined', rust-lang/reference commit c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c, file src/behavior-considered-undefined.md (rule undefined.alias states the aliasing rules in terms of &T, &mut T and Box<T>, with no type-based rule; rule undefined.validity.scalar requires integers and floats to be initialized).
- Rust Unsafe Code Guidelines, glossary, rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce, file reference/src/glossary.md (entry 'Abstract Byte': an abstract byte is Uninit or Init(u8, Option<Provenance>), so the per-byte shadow state is initialization and provenance, not a type; entry 'Aliasing', line 90: 'Zero Sized Types _never_ alias each other, because their span length is always 0').
- Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer. Stacked Borrows: An Aliasing Model for Rust. POPL 2020. https://doi.org/10.1145/3371109 (aliasing rules for Rust references over untyped memory, independent of types).
- Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung. Tree Borrows. PLDI 2025. https://doi.org/10.1145/3735592 (a successor aliasing model for Rust references).
- C++ working draft N4950 (2023-05-10), [cstring.syn] paragraph 3 ('Both functions implicitly create objects ([intro.object]) in the destination region of storage immediately prior to copying the sequence of characters to the destination.') and [intro.object] paragraph 10 (implicit object creation 'if doing so would result in the program having defined behavior'); checked at https://timsong-cpp.github.io/cppwp/n4950/cstring.syn and .../intro.object.
- Harvey Tuch, Gerwin Klein, Michael Norrish. Types, Bytes, and Separation Logic. POPL 2007, pp. 97-108. https://doi.org/10.1145/1190216.1190234 (Isabelle/HOL: typed heap views lifted from an untyped byte-level C memory).
- ISO/IEC 9899:201x Committee Draft N1570, section 7.24.2.1 paragraph 2 (memcpy: 'If copying takes place between objects that overlap, the behavior is undefined.') and section 7.24.2.2 paragraph 2 (memmove: 'Copying takes place as if the n characters from the object pointed to by s2 are first copied into a temporary array of n characters that does not overlap the objects pointed to by s1 and s2, and then the n characters from the temporary array are copied into the object pointed to by s1.'); text checked at http://port70.net/~nsz/c/c11/n1570.html#7.24.2.1.
- Xavier Leroy and Sandrine Blazy. Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations. Journal of Automated Reasoning 41(1):1-31, 2008. https://doi.org/10.1007/s10817-008-9099-0. Mechanized in CompCert: AbsInt/CompCert commit 2685140bf72c959446981fb99b5e44a8975021bc, file common/Memory.v lines 1086-1091, Theorem load_store_other (after a store, a load from another block or from a byte range disjoint from the stored range returns what it returned before), over untyped byte-level memory.

### Observation dates

All execution evidence (build, axiom audit, statement hashes) was produced on 2026-11-21. On the
same date the following source records were re-checked at their pinned locations: the Lean tag
commit (GitHub API), N4950 [basic.lval] p11 (in the official WG21 PDF and in the HTML rendering), LLVM
LangRef lines 7540 and 7593–7611 at the pinned
commit, the Rust Reference rule identifiers `undefined.alias` and `undefined.validity.scalar` at the
pinned commit, the Unsafe Code Guidelines glossary line 90 at the pinned commit, the location of
`mem_non_aliasing` in CH2O's `memory/aliasing.v` (lines 170-180) at the pinned commit, and the DR 236 committee
response. The remaining records (N1570 paragraph texts, N4950 [cstring.syn] and [intro.object],
bibliographic data and DOIs) were checked between 2026-11-20 and 2026-11-21.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and
`python3`. The primary check, run from the package directory, is:

```bash
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, runs `lake build`, rejects `sorry`, `admit`,
`native_decide` and `axiom` in the sources, checks that every declaration of the library depends
on no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (Lean's `collectAxioms`), and
recomputes the statement and closure hashes of every name recorded in `audit/statements.json` or
referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`,
`positive_control_lean` and hypothesis `counterexample`s), as described under
**Evidence**. It prints `REVALIDATED` and exits with status 0 when every check passes.

The same audit by hand, with the package-included audit program `lean/RevalidationAudit.lean`
(outside the library target; it prints the axioms of every library declaration and the type and
closure text of every recorded name as one JSON line):

```bash
cd lean
lake build
lake env lean RevalidationAudit.lean > /tmp/tbaa_audit.out
cd ..
python3 - <<'EOF'
import hashlib, json, re
audit = json.loads(re.search(r"REVALIDATE_JSON (\{.*\})", open("/tmp/tbaa_audit.out").read()).group(1))
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = [d["name"] for d in audit["decls"] if set(d["axioms"]) - allowed]
rec = json.load(open("audit/statements.json"))["statements"]
mism = []
for s in audit["stmts"]:
    got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
           "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
           "closure_size": len(s["closure"])}
    if s.get("missing") or rec.get(s["name"]) != got:
        mism.append(s["name"])
print("axioms ok" if not bad else f"axiom violations: {bad}")
print(f"{len(audit['stmts'])} names; hash mismatches: {mism}")
EOF
```

To re-check one result narrowly, print its axioms (here R1):

```bash
cd lean
printf 'import ToyTbaa\n#print axioms Toy.Tbaa.Results.hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8\n' > /tmp/tbaa_axioms.lean
lake env lean /tmp/tbaa_axioms.lean
```

A passing run establishes that the quoted statements are proved under the pinned toolchain from
the standard axioms and that their statements and definition closures are unchanged; it says
nothing about C, C++, LLVM or Rust.
