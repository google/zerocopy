# Layout automata for transmutability: universal vs. existential product checks, size extension, and reference `Freeze` obligations (Lean 4 toy model)

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

This package is a Lean 4 toy model (core Lean, no Mathlib) of layout automata for transmutability checking. A fixed-size type's bit validity is represented as a finite automaton over 257 symbols (the byte values 0-255 and `uninit`), and a check explores the product of a source and a destination automaton either universally (`forallCheck`, no validity promise) or existentially (`existsCheck`, the programmer promises that the particular value is valid at the destination). The cards LD1-* (universal check), LD2-* (existential check) and LD3-* (size extension) state which language relations the two explorations decide and under which hypotheses; the cards LD4-* state the reference-cast obligation matrix in a toy reference model that combines bit validity with the `frozen` and `unique` assertions of shared and mutable references and a whole-region `Freeze` flag. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker, the unstable `core::mem::TransmuteFrom` trait, or zerocopy.

Model conventions that every statement below carries:

- A layout automaton `Layout` has exactly one start state and exactly one accept state, and labelled edges carrying single symbols. It is a partial automaton (a state may lack an edge for a symbol), runs never step out of the accept state (`Path`), it is neither deterministic, acyclic nor fixed-size by construction, and a position with an `uninit` edge need not accept the 256 initialised byte values.
- `fit n s` is the destination-size view of a source word: the first `n` symbols of `s`, followed by `uninit` symbols up to length `n` when `s` is shorter (truncated subtraction `n - s.length`; at `n = 0`, `fit 0 s = []`).
- `B.FixedSize n` says that every word accepted by `B` has length exactly `n`; it holds at every `n` for an automaton with empty language, and at `n = 0` exactly for the languages `{[]}` (a zero-sized type) and empty (an uninhabited type).
- `B.Deterministic` allows at most one target per source state and label at every state of `B`, reachable or not, including the accept state. `A.ReachableLive` says that every state reachable from the start of `A`, the start state included, can still reach the accept state, so it includes inhabitation (`A` accepts at least one word) and excludes reachable dead branches.
- `B.ReachableLiveAcyclic` says that no non-empty run of `B` returns to a state that is reachable from the start and from which the accept state is reachable; cycles through unreachable or dead states are allowed, and the accepted words may have different lengths. For every `n`, `B.FixedSize n` implies it (`reachableLiveAcyclic_of_fixedSize`), and `B.Acyclic` (no non-empty cycle at any state, reachable or not, live or dead) implies it (`reachableLiveAcyclic_of_acyclic`); it is strictly weaker than each of the two (`reachableLiveAcyclic_strictly_weaker_than_both`), and `FixedSize` and `Acyclic` are incomparable (`fixedSize_acyclic_incomparable`).
- Both checks are pure recursive functions run with the step budget `fuelFor B`, one more than the length of the edge list of `B` with duplicate and unreachable edges counted; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`). No memo table is modelled.
- In the reference model, a referent type `RefTy` is a validity predicate plus one `Freeze` Boolean for the whole region; `freeze = false` lets a shared view overwrite the whole region with any byte string valid at its type (uniform `Cell`-like interior mutability). `Sound ms md S D` requires every run of permitted operations, from every `S`-valid initial contents, to satisfy the toy's three assertions (valid reads, no write while `frozen` is in force, no source access while a mutable destination is live). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, destructors, and Rust's aliasing and provenance models are not modelled.

Corrections to commonly stated forms (each witnessed by fully proved counterexamples; details at the start of Findings):

- The universal check does not decide `L(A) ⊆ L(B)` from determinism of the destination alone: the exact form (LD1-iff) assumes equal fixed sizes (exactly `n` for both automata), a deterministic destination `B` (at every state, reachable or not) and a source without reachable dead states whose start state reaches the accept state; each of the four hypotheses is tight, with fully proved counterexamples in the classes recorded in the LD1-iff ledger.
- The existential check decides `L(A) ∩ L(B) ≠ ∅` (LD2-iff) under equal fixed sizes (exactly `n` for both) and the same source liveness hypothesis, which includes inhabitation; determinism of either automaton is not assumed.
- The reference obligation matrix that requires `Freeze` on shared sources and destinations is sound (LD4-matrix-sound) and is exact when the destination is `Freeze` whenever the destination reference is shared and the source is satisfiable (LD4-matrix-iff). Without the `Freeze` assumption on the destination it is not exact in the toy: the casts `& cellByteRef → & cellByteRef` and `&mut cellByteRef → & cellByteRef` (the `&Cell<u8> → &Cell<u8>` and `&mut Cell<u8> → &Cell<u8>` shapes, `cellByteRef` being the toy's reading of `Cell<u8>`: one initialised byte, not `Freeze`) are sound (`sound_shared_shared_cell_cell`, `sound_mut_shared_cell_cell`) although neither referent is `Freeze`. Dropping the source-side `Freeze` obligation from the `&` → `&` cell admits there an unsound cast, `& cellByteRef → & byteRef` (LD4-cell).

One entry per result (hypotheses first; the full cards are in Findings):

- `LD1-sound` — `forallCheck_sound_fit_of_fixedSize`: For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not) and every destination layout automaton `B` all of whose accepted words have length exactly `nB` (`B.FixedSize nB`): if `forallCheck A B = true`, then for every word `s` accepted by `A`, `B` accepts `fit nB s` (the first `nB` symbols of `s`, followed by `uninit` symbols up to length `nB` when `s` is shorter; truncated subtraction `nB - s.length`).
- `LD1-complete` — `forallCheck_complete_fit_of_fixedSize_det_live`: For every destination layout automaton `B` that is deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and all of whose accepted words have length exactly `nB` (`B.FixedSize nB`), and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if for every word `s` accepted by `A`, `B` accepts `fit nB s`, then `forallCheck A B = true`.
- `LD1-complete-acyc` — `forallCheck_complete_fit_of_reachableLiveAcyclic_det_live`: For every destination layout automaton `B` that is deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and without non-empty cycles through its reachable live part (`B.ReachableLiveAcyclic`: no non-empty run returns to a state that is reachable from the start state of `B` and from which the accept state of `B` is reachable; cycles through unreachable states or through dead states are allowed, and the accepted words may have different lengths), every destination size `nB`, and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if for every word `s` accepted by `A`, `B` accepts `fit nB s`, then `forallCheck A B = true`.
- `LD1-iff` — `forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live`: For layout automata `A` and `B` all of whose accepted words have length exactly `n` (the same `n` for both: `A.FixedSize n`, `B.FixedSize n`), with `B` deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and every reachable state of `A`, the start state included, live (`A.ReachableLive`): `forallCheck A B = true` if and only if every word accepted by `A` is accepted by `B` (`Subset A B`).
- `LD1-nd` — `forallCheck_complete_needs_deterministic`: For the layout automata `ndSrcL` (deterministic, fixed size exactly 2) and `ndDstL` (not deterministic: byte 0 from the start leads to two different states), `ndDstL` has fixed size exactly 2, every reachable state of `ndSrcL` is live, and `ndDstL` accepts `fit 2 s` for every word `s` accepted by `ndSrcL`, yet `forallCheck ndSrcL ndDstL = false`.
- `LD2-sound` — `existsCheck_sound_fit_of_fixedSize_live`: For every destination layout automaton `B` (deterministic or not) all of whose accepted words have length exactly `nB` (`B.FixedSize nB`), and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if `existsCheck A B = true`, then there is a word `s` accepted by `A` such that `B` accepts `fit nB s` (`FitMeets A B nB`).
- `LD2-sound-exists` — `existsCheck_sound_exists_fitMeets_of_live`: For every destination layout automaton `B` (deterministic or not, of fixed size or not, cyclic or not) and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if `existsCheck A B = true`, then there is a size `nB` and a word `s` accepted by `A` such that `B` accepts `fit nB s` (`∃ nB, FitMeets A B nB`).
- `LD2-noloss` — `existsCheck_eq_false_imp_no_promise_of_fixedSize`: For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not) and every destination layout automaton `B` (deterministic or not) all of whose accepted words have length exactly `nB` (`B.FixedSize nB`): if `existsCheck A B = false`, then no word `s` accepted by `A` has `fit nB s` accepted by `B`; so rejecting a pair never rejects one for which some valid source value satisfies the validity promise at size `nB`.
- `LD2-noloss-acyc` — `existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic`: For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not), every destination layout automaton `B` (deterministic or not) without non-empty cycles through its reachable live part (`B.ReachableLiveAcyclic`: no non-empty run returns to a state that is reachable from the start state of `B` and from which the accept state of `B` is reachable; cycles through unreachable states or through dead states are allowed, and the accepted words may have different lengths), and every size `nB`: if `existsCheck A B = false`, then no word `s` accepted by `A` has `fit nB s` accepted by `B`.
- `LD2-iff` — `existsCheck_eq_true_iff_meets_of_eq_fixedSize_live`: For layout automata `A` and `B` all of whose accepted words have length exactly `n` (the same `n` for both), with every reachable state of `A`, the start state included, live (`A.ReachableLive`; `B` may be nondeterministic): `existsCheck A B = true` if and only if there is a word accepted by both (`Meets A B`).
- `LD3-ext` — `forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live`: For a source layout automaton `A` all of whose accepted words have length exactly `nA` and a destination layout automaton `B` all of whose accepted words have length exactly `nB`, with `nA ≤ nB`, `B` deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and every reachable state of `A`, the start state included, live (`A.ReachableLive`): `forallCheck A B = true` if and only if, for every word `s` accepted by `A`, `B` accepts `s` followed by exactly `nB - nA` `uninit` symbols.
- `LD3-u16` — `extension_u8_to_u16_rejected_u8_to_u8Pad_accepted`: For the toy layouts `u8L` (one initialised byte, size exactly 1), `u16L` (two initialised bytes, size exactly 2) and `u8PadL` (an initialised byte followed by a position that admits all 257 symbols, size exactly 2): `forallCheck u8L u16L = false` and `u16L` rejects `fit 2 [0] = [0, uninit]`, while `forallCheck u8L u8PadL = true` and `u8PadL` accepts `[b, uninit]` for every byte value `b`.
- `LD4-ss` — `sharedShared_sound_iff`: In the toy reference model (`Sound`), for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a shared reference to `S` to a shared reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid, `S` and `D` have the same `Freeze` flag, and, when `D` is not `Freeze`, every `D`-valid byte string is `S`-valid.
- `LD4-ms` — `mutShared_sound_iff`: In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a mutable reference to `S` to a shared reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid and, when `D` is not `Freeze`, every `D`-valid byte string is `S`-valid; `S`'s `Freeze` flag does not occur in the condition.
- `LD4-mm` — `mutMut_sound_iff`: In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a mutable reference to `S` to a mutable reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid and every `D`-valid byte string is `S`-valid; neither `Freeze` flag occurs.
- `LD4-sm` — `sharedMut_not_sound`: In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D` (any validities, any `Freeze` flags), an unchecked cast from a shared reference to `S` to a mutable reference to `D` is not sound.
- `LD4-matrix-sound` — `sound_of_matrixOK`: In the toy reference model, for every mode pair `ms`, `md` and all referent types `S` and `D` (no satisfiability hypothesis, no `Freeze` hypothesis): if the obligation matrix `MatrixOK` holds — `& → &`: `S ⊆ D`, `D` `Freeze` and `S` `Freeze`; `&mut → &`: `S ⊆ D` and `D` `Freeze`; `&mut → &mut`: `S ⊆ D` and `D ⊆ S`; `& → &mut`: never — then the cast is sound.
- `LD4-matrix-iff` — `matrixOK_iff_sound_of_sharedDst_freeze`: In the toy reference model, for every mode pair, for every source referent type `S` with at least one valid byte string (`Satisfiable S`), and every destination referent type `D` that is `Freeze` whenever the destination reference is shared: `MatrixOK` holds if and only if the cast is sound.
- `LD4-cell` — `cellByte_to_byte_admitted_without_srcFreeze`: For the toy referents `cellByteRef` (validity of one initialised byte, not `Freeze`; modelling `Cell<u8>`) and `byteRef` (the same validity, `Freeze`; modelling `u8`): the obligation matrix with the source-side `Freeze` obligation removed (`MatrixOKNoSrcFreeze`) holds for `& cellByteRef → & byteRef`, the two validities are included in each other, and the cast is not sound; from contents `[0]`, writing `[1]` through the source view is permitted (`Permitted`), the `frozen` assertion is in force (`FrozenDuring`), and that one-operation run violates an assertion (`RunOK` fails); the full `MatrixOK` rejects this cast and accepts `& byteRef → & byteRef`, which is sound.
- `LD4-refcheck` — `refCheck_sound_of_eq_fixedSize`: For referent layout automata `S` and `D` all of whose accepted words have length exactly `n` (the same `n` for both; deterministic or not, with or without dead branches), every mode pair `ms`, `md` and all caller-supplied `Freeze` flags `fzS`, `fzD`: if `refCheck ms md S fzS D fzD = true`, then the cast is sound in the toy reference model for the referent types `RefTy.ofLayout S fzS` and `RefTy.ofLayout D fzD`.

Non-claims for every result are listed first under Boundaries, one subsection per card; attractive stronger readings that are not established, escape hatches, and what was not examined follow there.

## Applicability

### Model fidelity

This is a toy model, not a mirror of production definitions. All declarations live in the Lean namespace `Toy.LayoutDfa` (library `ToyLayoutDfa`). The definitions are meant to capture:

- the layout automata of a transmutability checker: one start state, one accept state, and edges over the 256 byte values and an `uninit` value (`Sym`, `Layout`), with the language `Lang` standing for the valid byte strings of a fixed-size type;
- the two exploration modes of the product of a source and a destination automaton, with the truncation rule (success once the destination reaches its accept state), the extension rule (follow an `uninit` edge of the destination once the source reaches its accept state) and a step budget (`forallAux`, `forallCheck`, `existsAux`, `existsCheck`, `fuelFor`);
- the language relations those explorations are compared with: inclusion (`Subset`), non-empty intersection (`Meets`) and their destination-size views (`fit`, `FitSubset`, `FitMeets`);
- reference casts in a toy reference model: referent types with a whole-region `Freeze` flag (`RefTy`), the operations each view may perform while the cast reference is live (`Permitted`), the assertions those operations must satisfy (`OpOK`, `RunOK`, with the `frozen` assertion `FrozenDuring` and a `unique` clause), soundness `Sound`, the obligation matrix `MatrixOK`, and the matrix with inclusions decided by `forallCheck` (`refCheck`).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker, the unstable `core::mem::TransmuteFrom` trait, zerocopy, or Rust reference casts. Real systems appear in separate `Basis: derived (modeling bridge)` lines of the cards and in the section "Modeling bridge (derived; not kernel-checked)" under Findings, which cite their documentation and source at pinned revisions.

Known gaps (see also the per-card non-claims under Boundaries):

- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled.
- `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values (the fixtures `uL`, `b0uL` and `boolUL` use such positions; `mu8L` and `u8PadL` do not).
- The checks have no rule for uninhabited sources; the hypothesis `A.ReachableLive` excludes them instead.
- No memo table is modelled; that caching the checks' results per state pair is transparent is not proved here. The step budget `fuelFor B` depends on the edge list of `B`, so two edge lists with the same language can receive different answers (`checks_depend_on_edge_list_representation`).
- The `Freeze` flag covers the whole referent region. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled; `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- A non-`Freeze` shared view may write any byte string valid at its type to the whole region; `!Freeze` wrappers whose APIs restrict the written values are not modelled.
- `&mut S → &D` is modelled as a reborrow whose source is inactive while the destination is live; pointer provenance, aliasing-tag retagging, two-phase borrows and longer reborrow chains are not modelled.
- Degenerate sizes: at size `0`, `fit 0 s = []` discards the whole source word; an automaton with empty language has `FixedSize n` for every `n`. The cards state how each result behaves at these edges.
- The Rust type named in a fixture's doc comment (for example `u8L` for `u8`, `cellByteRef` for `Cell<u8>`) is an intended reading; the correspondence is not proved.

### Toolchain and project

- Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean, with no Mathlib and no `[[require]]` dependencies.
- Lake project `lean/` with one library target `ToyLayoutDfa` (`lean/lakefile.toml`); modules `ToyLayoutDfa.{Basic, Fixtures, Tools, Lemmas, Refs, RefTools, Results, Examples, Counterexamples, Counterexamples2, RefExamples, RefCounterexamples}`. The main theorems are in `lean/ToyLayoutDfa/Results.lean`; counterexample cards are in the counterexample modules.
- `lean/RevalidationAudit.lean` (outside the library target) prints the axioms of every theorem referenced by `results.json`; `support/revalidate.py` rebuilds the project and rechecks banned tokens, axioms and hashes.
- Paths in statement fences are relative to the package root. Every theorem of the package is fully proved; `#print axioms` reports at most `propext`, `Classical.choice`, `Quot.sound`. Renderings labelled "Unfolded (prose)" are explanations, not checked Lean terms.

### Subjects and how they relate

The Lean toolchain checks the statements. The other subjects are real systems and documents that the definitions are meant to capture or that the cards cite as prior art; the report interprets the toy through them in `derived (modeling bridge)` lines and proves nothing about them:

- rust-lang/rust at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`: rustc's transmutability checker (`compiler/rustc_transmute/src/layout/{mod.rs, dfa.rs}`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`) and the core library's `TransmuteFrom`/`Assume` documentation (`library/core/src/mem/transmutability.rs`), `Freeze` (`library/core/src/marker.rs`) and `Cell` (`library/core/src/cell.rs`).
- leanprover-community/mathlib4 at `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean`: a mechanized DFA library cited as prior art (not imported).
- Papers cited as prior art, identified by DOI under Evidence.

## Findings

Findings are organised as follows: corrections to commonly stated forms; the definitions every statement depends on, quoted verbatim with their source locations; one card per result (verbatim Lean statement, plain claim, kind, tier, depth, evidence basis, hypothesis ledger, non-vacuity witness, positive control where the card is an impossibility or counterexample, prior art and design question; the card's non-claims are under Boundaries); every auxiliary declaration a card mentions by name, quoted verbatim; and the modeling bridge to real systems. "Tight" in a hypothesis ledger means that a fully proved Lean counterexample, in the witness class recorded next to it, satisfies all the other hypotheses and violates the conclusion.

### Corrections to commonly stated forms

Each correction is witnessed by a fully proved counterexample named in brackets.

1. "For a deterministic destination, the universal check succeeds iff `L(A) ⊆ L(B)`" is false as stated for the layout check: its truncation and extension rules accept size-mismatched pairs [`forallCheck_iff_subset_needs_fixedSize_src`, `forallCheck_iff_subset_needs_fixedSize_dst`], and there is a source with a reachable dead branch (`deadL`) for which it rejects an included pair [`forallCheck_iff_subset_needs_reachableLive`]. The exact form (LD1-iff) adds equal fixed sizes and source liveness; soundness, stated for the destination-size view `fit nB`, holds under a fixed destination size alone (LD1-sound), and there is a destination whose words have two different lengths (`varDstL`) for which it fails [`forallCheck_sound_needs_fixedSize_dst_variable`].

2. "The existential check succeeds iff `L(A) ∩ L(B) ≠ ∅`" likewise needs equal fixed sizes and source liveness for the forward direction [`existsCheck_iff_meets_needs_fixedSize_src`, `existsCheck_iff_meets_needs_fixedSize_dst`, `existsCheck_iff_meets_needs_reachableLive`]; source liveness includes inhabitation, which the edge-free uninhabited source `neverL` violates without having any dead branch [`existsCheck_iff_meets_needs_reachableLive_uninhabited`]. The backward direction, stated for the destination-size view (no satisfiable promise is rejected), holds under a fixed destination size alone (LD2-noloss) or under the absence of cycles through the reachable live part of the destination alone (LD2-noloss-acyc); neither direction assumes determinism.

3. "Completeness of the universal check needs a fixed destination size" is false: the absence of non-empty cycles through the reachable live part of the destination (`ReachableLiveAcyclic`) suffices (LD1-complete-acyc), and there is a deterministic destination without a fixed size (`varDstL`) that it covers [`forallCheck_complete_acyc_nonvacuous`]. A fixed size and global acyclicity (`Acyclic`) each imply `ReachableLiveAcyclic`, and neither implies the other [`fixedSize_acyclic_incomparable`].

4. "A shared-to-shared reference cast is sound iff `L(S) ⊆ L(D)`, `D: Freeze` and `S: Freeze`" is false in the toy: the cast `& cellByteRef → & cellByteRef` (the `&Cell<u8> → &Cell<u8>` shape: neither side `Freeze`, equal validities) is sound [`sound_shared_shared_cell_cell`]. The stated form holds when `D: Freeze` is assumed (LD4-ss, LD4-matrix-iff).

5. "A mutable-to-shared reference cast is sound iff `L(S) ⊆ L(D)` and `D: Freeze`" is false in the toy: the cast `&mut cellByteRef → & cellByteRef` (the `&mut Cell<u8> → &Cell<u8>` shape) is sound [`sound_mut_shared_cell_cell`]. The stated form holds when `D: Freeze` is assumed, and `S: Freeze` is never needed in this cell (LD4-ms).

### Definitions (verbatim)

#### Automata and checks (`lean/ToyLayoutDfa/Basic.lean`)

```lean
-- lean/ToyLayoutDfa/Basic.lean:40-43
inductive Sym where
  | byte (b : Fin 256)
  | uninit
  deriving DecidableEq, Repr
```
The 257-symbol abstract-byte alphabet: 256 initialised byte values and `uninit`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:49-53
structure Layout where
  start : Nat
  accept : Nat
  edges : List (Nat × Sym × Nat)
  deriving Repr
```
A layout automaton: start state, one accept state, labelled edges. Not deterministic, acyclic or fixed-size by construction; a partial automaton (a state may lack an edge for a symbol), with no initialisation monotonicity (a position may accept `Sym.uninit` without the 256 byte values).

```lean
-- lean/ToyLayoutDfa/Basic.lean:58-59
def out (A : Layout) (q : Nat) : List (Sym × Nat) :=
  A.edges.filterMap (fun e => if e.1 = q then some (e.2.1, e.2.2) else none)
```
The edges leaving a state, in list order.

```lean
-- lean/ToyLayoutDfa/Basic.lean:63-66
inductive Path (A : Layout) : Nat → List Sym → Nat → Prop
  | nil (q : Nat) : Path A q [] q
  | cons {q : Nat} {a : Sym} {q' : Nat} {w : List Sym} {r : Nat} :
      q ≠ A.accept → (q, a, q') ∈ A.edges → Path A q' w r → Path A q (a :: w) r
```
Runs that never step out of the accept state (the accept state is terminal, as in the documented rustc semantics that out-edges of the accept state are ignored). Examples: `ex_lang_accept_terminal`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:69-70
def Accepts (A : Layout) (q : Nat) (w : List Sym) : Prop :=
  A.Path q w A.accept
```
Some run on the word ends in the accept state. Examples: `ex_lang_bool`, `ex_lang_u8`, `ex_lang_unit`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:74-75
def Lang (A : Layout) (w : List Sym) : Prop :=
  A.Accepts A.start w
```
The language: words accepted from the start state; meant to capture the valid byte strings of the type. Examples: `ex_lang_bool`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:80-81
def Deterministic (A : Layout) : Prop :=
  ∀ e₁ ∈ A.edges, ∀ e₂ ∈ A.edges, e₁.1 = e₂.1 → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2
```
At most one target per source state and label, at every state, reachable or not, including the accept state. Examples: `ex_deterministic`, `ex_not_deterministic`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:86-87
def FixedSize (A : Layout) (n : Nat) : Prop :=
  ∀ w, A.Lang w → w.length = n
```
Every accepted word has length exactly `n`; holds at every `n` for the empty language, and at `n = 0` exactly for the languages `{[]}` and empty. Examples: `ex_fixedSize`, `ex_not_fixedSize`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:95-96
def ReachableLive (A : Layout) : Prop :=
  ∀ w q, A.Path A.start w q → ∃ v, A.Accepts q v
```
Every state reachable from the start, the start state included, can still reach the accept state; in particular the language is non-empty (`inhabited_of_reachableLive`). Examples: `ex_reachableLive`, `ex_not_reachableLive` (a dead branch), `ex_not_reachableLive_uninhabited` (no word at all).

```lean
-- lean/ToyLayoutDfa/Basic.lean:102-103
def Acyclic (A : Layout) : Prop :=
  ∀ q w, w ≠ [] → ¬ A.Path q w q
```
No non-empty run from any state, reachable or unreachable, live or dead, returns to the state it started from; incomparable with `FixedSize` (`fixedSize_acyclic_incomparable`). Examples: `ex_acyclic`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:111-113
def ReachableLiveAcyclic (A : Layout) : Prop :=
  ∀ (pre : List Sym) (p : Nat) (c v : List Sym), c ≠ [] →
    A.Path A.start pre p → A.Path p c p → A.Accepts p v → False
```
No non-empty run returns to a state that is reachable from the start and from which the accept state is reachable; cycles through unreachable or dead states are allowed. Implied by `FixedSize` (`reachableLiveAcyclic_of_fixedSize`) and by `Acyclic` (`reachableLiveAcyclic_of_acyclic`). Examples: `ex_reachableLiveAcyclic`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:119-121
def ReachableDeterministic (A : Layout) : Prop :=
  ∀ w q, A.Path A.start w q → q ≠ A.accept →
    ∀ e₁ ∈ A.edges, ∀ e₂ ∈ A.edges, e₁.1 = q → e₂.1 = q → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2
```
Determinism at the states reachable from the start other than the accept state; implied by `Deterministic` (`reachableDeterministic_of_deterministic`) and strictly weaker (`ex_reachableDeterministic`). Assumed by the budget lemma `forallAux_complete_fit_of_lt_fuel`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:132-132
def fuelFor (B : Layout) : Nat := B.edges.length + 1
```
The step budget of both checks: one more than the length of the edge list, duplicate and unreachable edges included (`checks_depend_on_edge_list_representation`).

```lean
-- lean/ToyLayoutDfa/Basic.lean:142-150
def forallAux (A B : Layout) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, qa, qb =>
    if qb = B.accept then true
    else if qa = A.accept then
      (B.out qb).any (fun p => p.1 == Sym.uninit && forallAux A B fuel qa p.2)
    else
      (A.out qa).all (fun p =>
        (B.out qb).any (fun r => r.1 == p.1 && forallAux A B fuel p.2 r.2))
```
The universal product exploration (truncation, extension, then for-all/exists over edges). Examples: `ex_forallCheck`, `ex_not_forallCheck`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:154-155
def forallCheck (A B : Layout) : Bool :=
  forallAux A B (fuelFor B) A.start B.start
```
The universal check from the start states; meant to capture a transmutability check without a validity promise. Examples: `ex_forallCheck`, `ex_not_forallCheck`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:160-168
def existsAux (A B : Layout) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, qa, qb =>
    if qb = B.accept then true
    else if qa = A.accept then
      (B.out qb).any (fun p => p.1 == Sym.uninit && existsAux A B fuel qa p.2)
    else
      (A.out qa).any (fun p =>
        (B.out qb).any (fun r => r.1 == p.1 && existsAux A B fuel p.2 r.2))
```
The existential product exploration (exists/exists over edges). Examples: `ex_existsCheck`, `ex_not_existsCheck`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:172-173
def existsCheck (A B : Layout) : Bool :=
  existsAux A B (fuelFor B) A.start B.start
```
The existential check; meant to capture a transmutability check under a programmer validity promise. Examples: `ex_existsCheck`, `ex_not_existsCheck`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:180-181
def fit (n : Nat) (s : List Sym) : List Sym :=
  s.take n ++ List.replicate (n - s.length) Sym.uninit
```
The destination-size view: truncate to `n`, or pad with `uninit` to length `n` (truncated subtraction `n - s.length`; `fit 0 s = []`). Examples: `ex_fit`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:184-185
def Subset (A B : Layout) : Prop :=
  ∀ s, A.Lang s → B.Lang s
```
Language inclusion. Examples: `ex_subset`, `ex_not_subset`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:188-189
def Meets (A B : Layout) : Prop :=
  ∃ s, A.Lang s ∧ B.Lang s
```
Non-empty intersection. Examples: `ex_meets`, `ex_not_meets`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:194-195
def FitSubset (A B : Layout) (n : Nat) : Prop :=
  ∀ s, A.Lang s → B.Lang (fit n s)
```
Every valid source string, viewed at destination size, is destination-valid. Examples: `ex_fitSubset`, `ex_not_fitSubset`.

```lean
-- lean/ToyLayoutDfa/Basic.lean:200-201
def FitMeets (A B : Layout) (n : Nat) : Prop :=
  ∃ s, A.Lang s ∧ B.Lang (fit n s)
```
Some valid source string, viewed at destination size, is destination-valid (the validity promise is satisfiable). Examples: `ex_fitMeets`, `ex_not_fitMeets`.

#### Reference model (`lean/ToyLayoutDfa/Refs.lean`, `lean/ToyLayoutDfa/RefTools.lean`)

```lean
-- lean/ToyLayoutDfa/Refs.lean:53-55
structure RefTy where
  valid : List Sym → Prop
  freeze : Bool
```
A referent type: bit validity plus a `Freeze` flag for the whole region (validity alone does not determine `Freeze`); `freeze = false` means a shared view may overwrite the whole region with any byte string valid at its type.

```lean
-- lean/ToyLayoutDfa/Refs.lean:59-59
def RefTy.ofLayout (A : Layout) (fz : Bool) : RefTy := ⟨A.Lang, fz⟩
```
The referent type of a layout automaton with a given `Freeze` flag.

```lean
-- lean/ToyLayoutDfa/Refs.lean:62-62
def Includes (S D : RefTy) : Prop := ∀ m, S.valid m → D.valid m
```
Validity inclusion of referent types. Examples: `ex_includes`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:65-65
def Satisfiable (S : RefTy) : Prop := ∃ m, S.valid m
```
Some byte string is valid. Examples: `ex_satisfiable`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:68-71
inductive Mode where
  | shared
  | mutable
  deriving DecidableEq, Repr
```
Shared (`&`) or mutable (`&mut`) reference.

```lean
-- lean/ToyLayoutDfa/Refs.lean:75-78
inductive View where
  | src
  | dst
  deriving DecidableEq, Repr
```
The source view or the destination view of the region.

```lean
-- lean/ToyLayoutDfa/Refs.lean:82-84
inductive Op where
  | read (v : View)
  | write (v : View) (bytes : List Sym)
```
A read through a view, or a write of a whole byte string through a view.

```lean
-- lean/ToyLayoutDfa/Refs.lean:87-89
def viewTy (S D : RefTy) : View → RefTy
  | .src => S
  | .dst => D
```
The referent type a view is typed at.

```lean
-- lean/ToyLayoutDfa/Refs.lean:93-97
def Permitted (ms md : Mode) (S D : RefTy) : Op → Prop
  | .read .src => ms = .shared
  | .read .dst => True
  | .write .src b => ms = .shared ∧ S.freeze = false ∧ S.valid b
  | .write .dst b => (md = .mutable ∨ D.freeze = false) ∧ D.valid b
```
The capability of each view while the cast reference is live. Examples: `ex_permitted`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:101-102
def FrozenDuring (ms md : Mode) (S D : RefTy) : Prop :=
  (ms = .shared ∧ S.freeze = true) ∨ (md = .shared ∧ D.freeze = true)
```
Some live view is a shared reference to a `Freeze` referent, so the `frozen` assertion is in force. Examples: `ex_frozenDuring`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:108-110
def OpOK (ms md : Mode) (S D : RefTy) (m : List Sym) : Op → Prop
  | .read v => (viewTy S D v).valid m ∧ ¬ (md = .mutable ∧ v = .src)
  | .write v _ => ¬ FrozenDuring ms md S D ∧ ¬ (md = .mutable ∧ v = .src)
```
The assertions one operation must satisfy: valid reads, no writes under `frozen`, no source access under a live `&mut` destination (`unique`). Examples: `ex_opOK`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:113-115
def Op.next (m : List Sym) : Op → List Sym
  | .read _ => m
  | .write _ b => b
```
The contents after an operation.

```lean
-- lean/ToyLayoutDfa/Refs.lean:119-121
def RunOK (ms md : Mode) (S D : RefTy) : List Sym → List Op → Prop
  | m, [] => S.valid m
  | m, op :: ops => OpOK ms md S D m op ∧ RunOK ms md S D (op.next m) ops
```
A run satisfies every assertion and the source side then reads bytes valid at `S`. Examples: `ex_runOK`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:126-127
def Sound (ms md : Mode) (S D : RefTy) : Prop :=
  ∀ m, S.valid m → ∀ ops : List Op, (∀ op ∈ ops, Permitted ms md S D op) → RunOK ms md S D m ops
```
Every permitted run from every `S`-valid initial contents satisfies every assertion. Examples: `ex_sound`, `ex_not_sound`.

```lean
-- lean/ToyLayoutDfa/RefTools.lean:40-41
def SoundOneStep (ms md : Mode) (S D : RefTy) : Prop :=
  ∀ m, S.valid m → ∀ op, Permitted ms md S D op → OpOK ms md S D m op ∧ S.valid (op.next m)
```
The one-operation form of `Sound`; equivalent to it (`sound_iff_soundOneStep`), because a write replaces the whole region.

```lean
-- lean/ToyLayoutDfa/Refs.lean:135-139
def MatrixOK : Mode → Mode → RefTy → RefTy → Prop
  | .shared, .shared, S, D => Includes S D ∧ D.freeze = true ∧ S.freeze = true
  | .mutable, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .mutable, S, D => Includes S D ∧ Includes D S
  | .shared, .mutable, _, _ => False
```
The reference obligation matrix. Examples: `ex_matrixOK`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:143-147
def MatrixOKNoSrcFreeze : Mode → Mode → RefTy → RefTy → Prop
  | .shared, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .shared, S, D => Includes S D ∧ D.freeze = true
  | .mutable, .mutable, S, D => Includes S D ∧ Includes D S
  | .shared, .mutable, _, _ => False
```
The matrix without the source-side `Freeze` obligation in the `& → &` cell. Examples: `ex_matrixOKNoSrcFreeze`.

```lean
-- lean/ToyLayoutDfa/Refs.lean:153-157
def refCheck : Mode → Mode → Layout → Bool → Layout → Bool → Bool
  | .shared, .shared, S, fzS, D, fzD => forallCheck S D && fzD && fzS
  | .mutable, .shared, S, _, D, fzD => forallCheck S D && fzD
  | .mutable, .mutable, S, _, D, _ => forallCheck S D && forallCheck D S
  | .shared, .mutable, _, _, _, _ => false
```
The matrix with inclusions decided by `forallCheck` and caller-supplied `Freeze` flags (not computed from the layouts). Examples: `ex_refCheck`.

#### Fixtures (`lean/ToyLayoutDfa/Fixtures.lean`, `lean/ToyLayoutDfa/RefTools.lean`, `lean/ToyLayoutDfa/Examples.lean`)

The Rust type named in each fixture's doc comment is an intended reading; the correspondence is not proved.

```lean
-- lean/ToyLayoutDfa/Fixtures.lean:28-28
def unitL : Layout := ⟨0, 0, []⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:31-31
def u8L : Layout := ⟨0, 1, byteEdges 0 1⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:34-34
def boolL : Layout := ⟨0, 1, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:37-37
def u16L : Layout := ⟨0, 2, byteEdges 0 1 ++ byteEdges 1 2⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:41-41
def u8PadL : Layout := ⟨0, 2, byteEdges 0 1 ++ anyEdges 1 2⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:44-44
def mu8L : Layout := ⟨0, 1, anyEdges 0 1⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:49-49
def b0L : Layout := ⟨0, 1, [(0, Sym.byte 0, 1)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:52-52
def b1L : Layout := ⟨0, 1, [(0, Sym.byte 1, 1)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:57-57
def uL : Layout := ⟨0, 1, [(0, Sym.uninit, 1)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:61-61
def b0uL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (1, Sym.uninit, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:65-66
def boolUL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1), (1, Sym.uninit, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:69-70
def bool2L : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1), (1, Sym.byte 0, 2), (1, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:74-74
def deadL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:77-78
def ndSrcL : Layout :=
  ⟨0, 3, [(0, Sym.byte 0, 1), (1, Sym.byte 1, 3), (1, Sym.byte 2, 3)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:83-84
def ndDstL : Layout :=
  ⟨0, 3, [(0, Sym.byte 0, 1), (0, Sym.byte 0, 2), (1, Sym.byte 1, 3), (2, Sym.byte 2, 3)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:87-89
def chainL : Layout :=
  ⟨0, 5, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 2), (2, Sym.byte 0, 3), (3, Sym.byte 0, 4),
    (4, Sym.byte 1, 5)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:94-94
def cycL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1), (1, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:99-99
def neverL : Layout := ⟨0, 1, []⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:104-105
def varDstL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 2), (0, Sym.byte 1, 1), (1, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:108-109
def pairSrcL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 3), (1, Sym.byte 0, 2), (3, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:113-115
def cycDupL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 0, 1), (0, Sym.byte 0, 1), (1, Sym.byte 0, 1),
    (1, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:120-121
def deadCycReachL : Layout :=
  ⟨0, 1, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 2), (2, Sym.byte 1, 2)]⟩
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:174-174
def acceptNDL : Layout := ⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 2), (1, Sym.byte 0, 3)]⟩
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:110-110
abbrev byteRef : RefTy := RefTy.ofLayout u8L true
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:113-113
abbrev cellByteRef : RefTy := RefTy.ofLayout u8L false
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:116-116
abbrev boolRef : RefTy := RefTy.ofLayout boolL true
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:119-119
abbrev cellBoolRef : RefTy := RefTy.ofLayout boolL false
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:122-122
def neverRef : RefTy := ⟨fun _ => False, true⟩
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:15-16
def allSyms : List Sym :=
  (List.finRange 256).map Sym.byte ++ [Sym.uninit]
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:19-20
def byteEdges (q q' : Nat) : List (Nat × Sym × Nat) :=
  (List.finRange 256).map (fun b => (q, Sym.byte b, q'))
```
```lean
-- lean/ToyLayoutDfa/Fixtures.lean:24-25
def anyEdges (q q' : Nat) : List (Nat × Sym × Nat) :=
  allSyms.map (fun s => (q, s, q'))
```

#### Definition examples (`lean/ToyLayoutDfa/Examples.lean`, `lean/ToyLayoutDfa/RefExamples.lean`)

Every example is fully proved.

```lean
-- lean/ToyLayoutDfa/Examples.lean:22-25
theorem ex_lang_accept_terminal :
    (⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1)]⟩ : Layout).Lang [Sym.byte 0] ∧
    ¬ (⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1)]⟩ : Layout).Lang
      [Sym.byte 0, Sym.byte 0] := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:17-18
theorem ex_lang_bool : boolL.Lang [Sym.byte 0] ∧ boolL.Lang [Sym.byte 1] ∧
    ¬ boolL.Lang [Sym.byte 2] ∧ ¬ boolL.Lang [Sym.uninit] ∧ ¬ boolL.Lang [] := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:28-28
theorem ex_lang_u8 : (∀ b : Fin 256, u8L.Lang [Sym.byte b]) ∧ ¬ u8L.Lang [Sym.uninit] := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:31-31
theorem ex_lang_unit : unitL.Lang [] ∧ ¬ unitL.Lang [Sym.byte 0] := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:36-37
theorem ex_deterministic : boolL.Deterministic ∧ ndSrcL.Deterministic ∧ cycL.Deterministic ∧
    deadL.Deterministic ∧ unitL.Deterministic := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:40-40
theorem ex_not_deterministic : ¬ ndDstL.Deterministic := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:45-46
theorem ex_fixedSize : boolL.FixedSize 1 ∧ unitL.FixedSize 0 ∧ deadL.FixedSize 1 ∧
    ndDstL.FixedSize 2 := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:53-53
theorem ex_not_fixedSize : ¬ cycL.FixedSize 2 ∧ ¬ boolL.FixedSize 2 := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:60-61
theorem ex_reachableLive : boolL.ReachableLive ∧ ndDstL.ReachableLive ∧
    unitL.ReachableLive := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:76-76
theorem ex_not_reachableLive : ¬ deadL.ReachableLive := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:91-91
theorem ex_not_reachableLive_uninhabited : ¬ neverL.ReachableLive := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:110-110
theorem ex_acyclic : boolL.Acyclic ∧ varDstL.Acyclic ∧ ¬ cycL.Acyclic := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:162-164
theorem ex_reachableLiveAcyclic :
    varDstL.ReachableLiveAcyclic ∧ deadCycReachL.ReachableLiveAcyclic ∧
      ¬ deadCycReachL.Acyclic ∧ ¬ cycL.ReachableLiveAcyclic := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:200-202
theorem ex_reachableDeterministic :
    boolL.ReachableDeterministic ∧ acceptNDL.ReachableDeterministic ∧
      ¬ acceptNDL.Deterministic ∧ ¬ ndDstL.ReachableDeterministic := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:208-211
theorem ex_fit : fit 2 [Sym.byte 0] = [Sym.byte 0, Sym.uninit] ∧
    fit 1 [Sym.byte 0, Sym.byte 1] = [Sym.byte 0] ∧
    fit 2 [Sym.byte 0, Sym.byte 1] = [Sym.byte 0, Sym.byte 1] ∧
    fit 0 [Sym.byte 0] = [] := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:216-217
theorem ex_forallCheck : forallCheck boolL u8L = true ∧ forallCheck u8L u8L = true ∧
    forallCheck u8L u8PadL = true ∧ forallCheck u16L u8L = true := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:220-221
theorem ex_not_forallCheck : forallCheck u8L boolL = false ∧ forallCheck u8L u16L = false ∧
    forallCheck boolL b0L = false := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:224-224
theorem ex_existsCheck : existsCheck u8L boolL = true ∧ existsCheck boolL b0L = true := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:227-227
theorem ex_not_existsCheck : existsCheck b0L b1L = false ∧ existsCheck u8L u16L = false := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:232-232
theorem ex_subset : Subset b0L boolL := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:236-236
theorem ex_not_subset : ¬ Subset boolL b0L := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:239-239
theorem ex_meets : Meets boolL b0L := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:241-241
theorem ex_not_meets : ¬ Meets b0L b1L := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:246-246
theorem ex_fitSubset : FitSubset b0L b0uL 2 := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:250-250
theorem ex_not_fitSubset : ¬ FitSubset b0L bool2L 2 := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:253-253
theorem ex_fitMeets : FitMeets boolL b0L 1 := …
```
```lean
-- lean/ToyLayoutDfa/Examples.lean:255-255
theorem ex_not_fitMeets : ¬ FitMeets b0L b1L 1 := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:177-177
theorem ex_includes : Includes boolRef byteRef ∧ ¬ Includes byteRef boolRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:180-180
theorem ex_satisfiable : Satisfiable byteRef ∧ ¬ Satisfiable neverRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:183-189
theorem ex_permitted :
    Permitted .mutable .shared byteRef byteRef (.read .dst) ∧
    ¬ Permitted .mutable .shared byteRef byteRef (.read .src) ∧
    Permitted .shared .shared cellByteRef byteRef (.write .src [Sym.byte 5]) ∧
    ¬ Permitted .shared .shared byteRef byteRef (.write .src [Sym.byte 5]) ∧
    Permitted .mutable .mutable byteRef byteRef (.write .dst [Sym.byte 5]) ∧
    ¬ Permitted .mutable .shared byteRef byteRef (.write .dst [Sym.byte 5]) := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:193-196
theorem ex_frozenDuring :
    FrozenDuring .shared .shared cellByteRef byteRef ∧
    ¬ FrozenDuring .mutable .shared byteRef cellByteRef ∧
    ¬ FrozenDuring .mutable .mutable byteRef byteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:199-202
theorem ex_opOK :
    OpOK .shared .shared cellByteRef byteRef [Sym.byte 0] (.read .dst) ∧
    ¬ OpOK .shared .shared cellByteRef byteRef [Sym.byte 0] (.write .src [Sym.byte 1]) ∧
    ¬ OpOK .shared .mutable byteRef byteRef [Sym.byte 0] (.read .src) := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:205-207
theorem ex_runOK :
    RunOK .mutable .mutable byteRef byteRef [Sym.byte 0] [.write .dst [Sym.byte 1], .read .dst] ∧
    ¬ RunOK .mutable .mutable boolRef byteRef [Sym.byte 0] [.write .dst [Sym.byte 2]] := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:211-211
theorem ex_sound : Sound .shared .shared boolRef byteRef ∧ Sound .mutable .mutable byteRef byteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:214-215
theorem ex_not_sound : ¬ Sound .mutable .mutable boolRef byteRef ∧
    ¬ Sound .mutable .shared byteRef boolRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:218-220
theorem ex_matrixOK :
    MatrixOK .shared .shared boolRef byteRef ∧ ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
    ¬ MatrixOK .shared .mutable byteRef byteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:223-225
theorem ex_matrixOKNoSrcFreeze :
    MatrixOKNoSrcFreeze .shared .shared cellByteRef byteRef ∧
    ¬ MatrixOKNoSrcFreeze .shared .shared cellByteRef cellByteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:228-231
theorem ex_refCheck :
    refCheck .shared .shared boolL true u8L true = true ∧
    refCheck .shared .shared u8L false u8L true = false ∧
    refCheck .shared .mutable u8L true u8L true = false := …
```

### Cards

| id | kind | Lean name | tier | depth |
| --- | --- | --- | --- | --- |
| LD1-sound | theorem | `forallCheck_sound_fit_of_fixedSize` | T1 | substantive |
| LD1-complete | theorem | `forallCheck_complete_fit_of_fixedSize_det_live` | T1 | shallow |
| LD1-complete-acyc | theorem | `forallCheck_complete_fit_of_reachableLiveAcyclic_det_live` | T1 | substantive |
| LD1-iff | characterization | `forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live` | T1 | shallow |
| LD1-nd | counterexample | `forallCheck_complete_needs_deterministic` | T0 | definitional |
| LD2-sound | theorem | `existsCheck_sound_fit_of_fixedSize_live` | T1 | shallow |
| LD2-sound-exists | theorem | `existsCheck_sound_exists_fitMeets_of_live` | T1 | substantive |
| LD2-noloss | theorem | `existsCheck_eq_false_imp_no_promise_of_fixedSize` | T1 | shallow |
| LD2-noloss-acyc | theorem | `existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic` | T1 | substantive |
| LD2-iff | characterization | `existsCheck_eq_true_iff_meets_of_eq_fixedSize_live` | T1 | shallow |
| LD3-ext | characterization | `forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live` | T1 | shallow |
| LD3-u16 | counterexample | `extension_u8_to_u16_rejected_u8_to_u8Pad_accepted` | T0 | definitional |
| LD4-ss | characterization | `sharedShared_sound_iff` | T1 | shallow |
| LD4-ms | characterization | `mutShared_sound_iff` | T1 | shallow |
| LD4-mm | characterization | `mutMut_sound_iff` | T0 | shallow |
| LD4-sm | impossibility | `sharedMut_not_sound` | T0 | definitional |
| LD4-matrix-sound | theorem | `sound_of_matrixOK` | T1 | shallow |
| LD4-matrix-iff | characterization | `matrixOK_iff_sound_of_sharedDst_freeze` | T1 | shallow |
| LD4-cell | counterexample | `cellByte_to_byte_admitted_without_srcFreeze` | T0 | definitional |
| LD4-refcheck | theorem | `refCheck_sound_of_eq_fixedSize` | T1 | shallow |

#### `LD1-sound` — `forallCheck_sound_fit_of_fixedSize`

```lean
-- lean/ToyLayoutDfa/Results.lean:23-24
theorem forallCheck_sound_fit_of_fixedSize {A B : Layout} {nB : Nat} (hB : B.FixedSize nB) :
    forallCheck A B = true → FitSubset A B nB := …
```
Unfolded (prose): `FitSubset A B nB` is `∀ s, A.Lang s → B.Lang (s.take nB ++ List.replicate (nB - s.length) Sym.uninit)`.

- **Plain claim:** For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not) and every destination layout automaton `B` all of whose accepted words have length exactly `nB` (`B.FixedSize nB`): if `forallCheck A B = true`, then for every word `s` accepted by `A`, `B` accepts `fit nB s` (the first `nB` symbols of `s`, followed by `uninit` symbols up to length `nB` when `s` is shorter; truncated subtraction `nB - s.length`).
- **Kind:** theorem. **Tier:** T1 — Soundness of a simulation-style product check for inclusion is folklore, and textbook automata constructions are mechanized (prior art below); made precise here for the 257-symbol layout encoding with the layout check's truncation and extension rules and the `fit` view, which no mechanization found in the search covers.
- **Depth:** substantive.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments).
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hB : B.FixedSize nB` | Gives the truncation rule (success as soon as the destination reaches its accept state) the meaning "the first `nB` symbols are valid"; without it, there is a pair (`pairSrcL`, `varDstL`) that the check accepts although no size satisfies the conclusion. | tight: counterexamples `forallCheck_sound_needs_fixedSize_dst_variable`, `forallCheck_sound_needs_fixedSize_dst` (witness class: a 3-state deterministic acyclic destination whose words have lengths 1 and 2 (`varDstL`) against a 4-state fixed-size source (`pairSrcL`): the check accepts and `FitSubset` fails at every `nB`; also the fixed-size-0 destination `unitL` evaluated at `nB = 1`) |

- **Non-vacuity witness:** `b0L` into `boolL` with `nB = 1`: `boolL` has fixed size exactly 1 and the check accepts. (`forallCheck_sound_fit_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD1-sound`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
  - Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:151-153
theorem forallCheck_sound_needs_fixedSize_dst_variable :
    (∀ n, ¬ varDstL.FixedSize n) ∧ forallCheck pairSrcL varDstL = true ∧
      ∀ n, ¬ FitSubset pairSrcL varDstL n := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:109-110
theorem forallCheck_sound_needs_fixedSize_dst :
    ¬ unitL.FixedSize 1 ∧ forallCheck b0L unitL = true ∧ ¬ FitSubset b0L unitL 1 := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:114-115
theorem forallCheck_sound_fit_nonvacuous :
    boolL.FixedSize 1 ∧ forallCheck b0L boolL = true := …
```

#### `LD1-complete` — `forallCheck_complete_fit_of_fixedSize_det_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:49-51
theorem forallCheck_complete_fit_of_fixedSize_det_live {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true := …
```
Unfolded (prose): `A.ReachableLive` is `∀ w q, A.Path A.start w q → ∃ v, A.Accepts q v`; `B.Deterministic` is `∀ e₁ ∈ B.edges, ∀ e₂ ∈ B.edges, e₁.1 = e₂.1 → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2`.

- **Plain claim:** For every destination layout automaton `B` that is deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and all of whose accepted words have length exactly `nB` (`B.FixedSize nB`), and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if for every word `s` accepted by `A`, `B` accepts `fit nB s`, then `forallCheck A B = true`.
- **Kind:** theorem. **Tier:** T1 — Completeness of the per-pair universal check for deterministic destinations is folklore (the product of DFAs); the liveness and size hypotheses that the layout check's truncation, extension and step-budget rules require are made explicit and shown tight here. Proved as the fixed-size corollary of LD1-complete-acyc.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hB : B.FixedSize nB` | Implies `B.ReachableLiveAcyclic` (`reachableLiveAcyclic_of_fixedSize`), which bounds every accepted destination word by the length of the edge list (`length_le_edges_of_reachableLiveAcyclic`), so the step budget `fuelFor B` suffices; this card is the fixed-size corollary of LD1-complete-acyc. `B.Acyclic` is a different sufficient condition (corollary `forallCheck_complete_fit_of_acyclic_det_live`): neither of `B.FixedSize nB` and `B.Acyclic` implies the other (`fixedSize_acyclic_incomparable`). | tight: counterexample `forallCheck_complete_needs_fixedSize_dst` (witness class: a deterministic destination with a self-loop (3 edges, words of unbounded length) and a 6-state chain source; the step budget is exhausted) |
  | `hdet : B.Deterministic` | The check commits to one destination edge per source edge; there is a destination with two targets for one label (`ndDstL`) for which that commitment makes the check reject an included source. | tight: counterexample `forallCheck_complete_needs_deterministic` (witness class: small acyclic automata with at most 4 states over byte values 0-2, fixed size exactly 2) |
  | `hlive : A.ReachableLive` | The check demands a destination edge for every source edge, including edges into dead source branches that contribute no word. | tight: counterexample `forallCheck_complete_needs_reachableLive` (witness class: a 3-state source with one reachable dead state and a 2-state destination) |

- **Non-vacuity witness:** `b0L` into `boolL` with `nB = 1`. (`forallCheck_complete_fit_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD1-complete`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
  - D. L. Dill, A. J. Hu, H. Wong-Toi, Checking for language inclusion using simulation preorders, in Computer Aided Verification (CAV '91), LNCS 575, Springer, 1992, pp. 255-265, DOI 10.1007/3-540-55179-4_25 (bibliographic record checked; text not read): simulation preorders as a sufficient, efficiently checkable condition for language inclusion.
  - Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:198-200
theorem forallCheck_complete_needs_fixedSize_dst :
    cycL.Deterministic ∧ chainL.ReachableLive ∧ FitSubset chainL cycL 5 ∧
      ¬ cycL.FixedSize 5 ∧ forallCheck chainL cycL = false := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:175-178
theorem forallCheck_complete_needs_deterministic :
    ndDstL.FixedSize 2 ∧ ndSrcL.ReachableLive ∧ FitSubset ndSrcL ndDstL 2 ∧
      ¬ ndDstL.Deterministic ∧ forallCheck ndSrcL ndDstL = false ∧
      ndSrcL.Deterministic ∧ ndSrcL.FixedSize 2 := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:190-192
theorem forallCheck_complete_needs_reachableLive :
    b1L.FixedSize 1 ∧ b1L.Deterministic ∧ FitSubset deadL b1L 1 ∧ ¬ deadL.ReachableLive ∧
      forallCheck deadL b1L = false := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:203-204
theorem forallCheck_complete_fit_nonvacuous :
    boolL.FixedSize 1 ∧ boolL.Deterministic ∧ b0L.ReachableLive ∧ FitSubset b0L boolL 1 := …
```

#### `LD1-complete-acyc` — `forallCheck_complete_fit_of_reachableLiveAcyclic_det_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:36-38
theorem forallCheck_complete_fit_of_reachableLiveAcyclic_det_live {A B : Layout} {nB : Nat}
    (hno : B.ReachableLiveAcyclic) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true := …
```
Unfolded (prose): `B.ReachableLiveAcyclic` is `∀ (pre : List Sym) (p : Nat) (c v : List Sym), c ≠ [] → B.Path B.start pre p → B.Path p c p → B.Accepts p v → False`.

- **Plain claim:** For every destination layout automaton `B` that is deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and without non-empty cycles through its reachable live part (`B.ReachableLiveAcyclic`: no non-empty run returns to a state that is reachable from the start state of `B` and from which the accept state of `B` is reachable; cycles through unreachable states or through dead states are allowed, and the accepted words may have different lengths), every destination size `nB`, and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if for every word `s` accepted by `A`, `B` accepts `fit nB s`, then `forallCheck A B = true`.
- **Kind:** theorem. **Tier:** T1 — Shows that the absence of cycles through the reachable live part of the destination suffices for completeness of the layout check with its step budget (folklore for acyclic product exploration, made precise here); it covers destinations without a fixed size and destinations with cycles through unreachable or dead states.
- **Depth:** substantive.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hno : B.ReachableLiveAcyclic` | Bounds every accepted destination word by the length of the edge list (`length_le_edges_of_reachableLiveAcyclic`), so the step budget suffices. | tight: counterexample `forallCheck_complete_needs_reachableLiveAcyclic` (witness class: a deterministic destination with a self-loop at a reachable live state (3 edges) and a 6-state chain source; the step budget is exhausted) |
  | `hdet : B.Deterministic` | As in LD1-complete. | tight: counterexample `forallCheck_complete_acyc_needs_deterministic` (witness class: small acyclic automata with at most 4 states over byte values 0-2) |
  | `hlive : A.ReachableLive` | As in LD1-complete. | tight: counterexample `forallCheck_complete_acyc_needs_reachableLive` (witness class: a 3-state source with one reachable dead state and a 2-state acyclic destination) |

- **Non-vacuity witness:** `b0L` into `varDstL` (deterministic, acyclic, no fixed size) and into `deadCycReachL` (deterministic, fixed size 1, a self-loop at a reachable dead state, so not `Acyclic`), both at `nB = 1`; the first instance lies outside LD1-complete, the second outside the global-acyclicity corollary `forallCheck_complete_fit_of_acyclic_det_live`. (`forallCheck_complete_acyc_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD1-complete-acyc`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
  - Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:213-215
theorem forallCheck_complete_needs_reachableLiveAcyclic :
    cycL.Deterministic ∧ chainL.ReachableLive ∧ FitSubset chainL cycL 5 ∧
      ¬ cycL.ReachableLiveAcyclic ∧ forallCheck chainL cycL = false := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:218-220
theorem forallCheck_complete_acyc_needs_deterministic :
    ndDstL.ReachableLiveAcyclic ∧ ndSrcL.ReachableLive ∧ FitSubset ndSrcL ndDstL 2 ∧
      ¬ ndDstL.Deterministic ∧ forallCheck ndSrcL ndDstL = false := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:224-226
theorem forallCheck_complete_acyc_needs_reachableLive :
    b1L.ReachableLiveAcyclic ∧ b1L.Deterministic ∧ FitSubset deadL b1L 1 ∧
      ¬ deadL.ReachableLive ∧ forallCheck deadL b1L = false := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:233-237
theorem forallCheck_complete_acyc_nonvacuous :
    (varDstL.ReachableLiveAcyclic ∧ varDstL.Deterministic ∧ b0L.ReachableLive ∧
      FitSubset b0L varDstL 1 ∧ (∀ n, ¬ varDstL.FixedSize n)) ∧
    (deadCycReachL.ReachableLiveAcyclic ∧ deadCycReachL.Deterministic ∧ b0L.ReachableLive ∧
      FitSubset b0L deadCycReachL 1 ∧ ¬ deadCycReachL.Acyclic) := …
```

#### `LD1-iff` — `forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:64-67
theorem forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (hdet : B.Deterministic)
    (hlive : A.ReachableLive) :
    forallCheck A B = true ↔ Subset A B := …
```
Unfolded (prose): `Subset A B` is `∀ s, A.Lang s → B.Lang s`.

- **Plain claim:** For layout automata `A` and `B` all of whose accepted words have length exactly `n` (the same `n` for both: `A.FixedSize n`, `B.FixedSize n`), with `B` deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and every reachable state of `A`, the start state included, live (`A.ReachableLive`): `forallCheck A B = true` if and only if every word accepted by `A` is accepted by `B` (`Subset A B`).
- **Kind:** characterization. **Tier:** T1 — Inclusion of DFA languages by product exploration is textbook and mechanized for total DFAs (prior art below); the T1 content is the exact hypothesis set (equal fixed sizes, source liveness, determinism) under which the layout check, with its truncation, extension and step-budget rules, decides inclusion, each hypothesis shown tight.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hA : A.FixedSize n` | Without it, there is a shorter source (`unitL`) that the extension rule accepts because its padded strings, not its own strings, are valid. | tight: counterexamples `forallCheck_iff_subset_needs_fixedSize_src`, `fixedSize_src_counterexamples_hold_for_mu8L` (witness class: source `()` (size 0) and the destination `{[uninit]}` (one `uninit` symbol) (`uL`) with `n = 1`; the same failure with the initialisation-monotone destination `mu8L` (`MaybeUninit<u8>`)) |
  | `hB : B.FixedSize n` | Without it, there is a longer source (`b0L`) that the truncation rule accepts. | tight: counterexample `forallCheck_iff_subset_needs_fixedSize_dst` (witness class: source `{[0]}` and destination `()` with `n = 1`) |
  | `hdet : B.Deterministic` | As in LD1-complete. | tight: counterexample `forallCheck_iff_subset_needs_deterministic` (witness class: small acyclic automata with at most 4 states over byte values 0-2, fixed size exactly 2) |
  | `hlive : A.ReachableLive` | As in LD1-complete. | tight: counterexample `forallCheck_iff_subset_needs_reachableLive` (witness class: a 3-state source with one dead state, `n = 1`) |

- **Non-vacuity witness:** `b0L`/`boolL` (accepted and included) and `boolL`/`b0L` (rejected and not included), all hypotheses holding in both. (`forallCheck_iff_subset_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD1-iff`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
  - M. O. Rabin, D. Scott, Finite automata and their decision problems, IBM Journal of Research and Development 3(2):114-125, 1959, DOI 10.1147/rd.32.0114 (bibliographic record checked; text not read): finite automata, nondeterministic automata, and decision problems for them.
  - Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:296-298
theorem forallCheck_iff_subset_needs_fixedSize_src :
    uL.FixedSize 1 ∧ uL.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (forallCheck unitL uL = true ↔ Subset unitL uL) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:154-159
theorem fixedSize_src_counterexamples_hold_for_mu8L :
    mu8L.FixedSize 1 ∧ mu8L.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
    ¬ (forallCheck unitL mu8L = true ↔ Subset unitL mu8L) ∧
    ¬ (existsCheck unitL mu8L = true ↔ Meets unitL mu8L) ∧
    refCheck .shared .shared unitL true mu8L true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout mu8L true) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:304-306
theorem forallCheck_iff_subset_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ unitL.Deterministic ∧ b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (forallCheck b0L unitL = true ↔ Subset b0L unitL) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:310-312
theorem forallCheck_iff_subset_needs_deterministic :
    ndSrcL.FixedSize 2 ∧ ndDstL.FixedSize 2 ∧ ndSrcL.ReachableLive ∧ ¬ ndDstL.Deterministic ∧
      ¬ (forallCheck ndSrcL ndDstL = true ↔ Subset ndSrcL ndDstL) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:316-318
theorem forallCheck_iff_subset_needs_reachableLive :
    deadL.FixedSize 1 ∧ b1L.FixedSize 1 ∧ b1L.Deterministic ∧ ¬ deadL.ReachableLive ∧
      ¬ (forallCheck deadL b1L = true ↔ Subset deadL b1L) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:324-328
theorem forallCheck_iff_subset_nonvacuous :
    (b0L.FixedSize 1 ∧ boolL.FixedSize 1 ∧ boolL.Deterministic ∧ b0L.ReachableLive ∧
      forallCheck b0L boolL = true ∧ Subset b0L boolL) ∧
    (boolL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ b0L.Deterministic ∧ boolL.ReachableLive ∧
      forallCheck boolL b0L = false ∧ ¬ Subset boolL b0L) := …
```

#### `LD1-nd` — `forallCheck_complete_needs_deterministic`

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:175-178
theorem forallCheck_complete_needs_deterministic :
    ndDstL.FixedSize 2 ∧ ndSrcL.ReachableLive ∧ FitSubset ndSrcL ndDstL 2 ∧
      ¬ ndDstL.Deterministic ∧ forallCheck ndSrcL ndDstL = false ∧
      ndSrcL.Deterministic ∧ ndSrcL.FixedSize 2 := …
```
Unfolded (prose): both automata accept exactly the words `[0, 1]` and `[0, 2]` (`ndSrcL_ndDstL_lang`); after byte 0 the check must pick one destination state, and state 1 has a single outgoing edge, labelled 1, and state 2 a single outgoing edge, labelled 2.

- **Role:** Headline counterexample; the same theorem is the tightness counterexample for `hdet` in LD1-complete.
- **Plain claim:** For the layout automata `ndSrcL` (deterministic, fixed size exactly 2) and `ndDstL` (not deterministic: byte 0 from the start leads to two different states), `ndDstL` has fixed size exactly 2, every reachable state of `ndSrcL` is live, and `ndDstL` accepts `fit 2 s` for every word `s` accepted by `ndSrcL`, yet `forallCheck ndSrcL ndDstL = false`.
- **Kind:** counterexample. **Tier:** T0 — That a per-state simulation check is sufficient but not necessary for inclusion into a nondeterministic automaton is classical (simulation versus trace inclusion); this is a concrete instance in the layout encoding.
- **Depth:** definitional.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `ndDstL` is a nondeterministic encoding. rustc's layout automaton type is named `Dfa`; whether its automata are deterministic in the sense of `Deterministic` is not examined, and no claim about rustc is derived from this counterexample (see Modeling bridge item 1). The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments).
- **Hypothesis ledger:** no hypotheses (a statement about concrete fixtures).
- **Non-vacuity witness:** The theorem is itself a concrete instance. (`forallCheck_complete_needs_deterministic`)
- **Positive control:** `forallCheck_ndSrcL_self`.
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD1-nd`".
- **Prior art:**
  - D. L. Dill, A. J. Hu, H. Wong-Toi, Checking for language inclusion using simulation preorders, in Computer Aided Verification (CAV '91), LNCS 575, Springer, 1992, pp. 255-265, DOI 10.1007/3-540-55179-4_25 (bibliographic record checked; text not read): simulation preorders as a sufficient, efficiently checkable condition for language inclusion.
  - R. J. van Glabbeek, The linear time – branching time spectrum, CONCUR '90, LNCS 458, Springer, 1990, pp. 278-297, DOI 10.1007/BFb0039066 (bibliographic record checked; text not read): a classification of process semantics that separates trace (language) inclusion from simulation.
  - M. De Wulf, L. Doyen, T. A. Henzinger, J.-F. Raskin, Antichains: a new algorithm for checking universality of finite automata, CAV 2006, LNCS 4144, Springer, 2006, pp. 17-30, DOI 10.1007/11817963_5 (bibliographic record checked; text not read): exact universality (and inclusion) checking for nondeterministic automata over sets of states without explicit determinisation.
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:184-184
theorem forallCheck_ndSrcL_self : ndSrcL.Deterministic ∧ forallCheck ndSrcL ndSrcL = true := …
```

#### `LD2-sound` — `existsCheck_sound_fit_of_fixedSize_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:92-94
theorem existsCheck_sound_fit_of_fixedSize_live {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) (hlive : A.ReachableLive) :
    existsCheck A B = true → FitMeets A B nB := …
```
Unfolded (prose): `FitMeets A B nB` is `∃ s, A.Lang s ∧ B.Lang (s.take nB ++ List.replicate (nB - s.length) Sym.uninit)`.

- **Plain claim:** For every destination layout automaton `B` (deterministic or not) all of whose accepted words have length exactly `nB` (`B.FixedSize nB`), and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if `existsCheck A B = true`, then there is a word `s` accepted by `A` such that `B` accepts `fit nB s` (`FitMeets A B nB`).
- **Kind:** theorem. **Tier:** T1 — Soundness of an existential product search for non-empty intersection is textbook; the layout check's truncation and extension rules and the liveness hypothesis (which includes source inhabitation) are made precise. The fixed-destination-size corollary of LD2-sound-exists.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `existsCheck` is read as the exploration mode used when the compiler may assume a validity check by the programmer (some source transition, some destination transition), and `FitMeets A B nB` as the satisfiability, by at least one valid source value, of the caller's validity promise documented for `Assume::VALIDITY`, as stated in the sources cited here. rustc answers yes for an uninhabited source before any exploration, a rule the toy's checks do not have; the hypothesis `A.ReachableLive` excludes uninhabited sources instead. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 116-123: when the source layout is uninhabited the query answers yes before any automaton exploration (source comment: "conclude that the transmutation is acceptable, because instances of the `src` type do not exist", lines 118-119). The toy's checks have no such rule; the `ReachableLive` hypothesis excludes uninhabited sources instead.
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hB : B.FixedSize nB` | Pins the size parameter `nB` to the length of the destination word the check finds; without it the conclusion still holds at some size (LD2-sound-exists), but not necessarily at the given `nB`. | tight: counterexample `existsCheck_sound_needs_fixedSize_dst` (witness class: the fixed-size-0 destination `unitL` evaluated at `nB = 1`, source `b0L`) |
  | `hlive : A.ReachableLive` | Truncation succeeds as soon as the destination reaches its accept state, without inspecting the rest of the source; there is a source with a dead branch (`deadL`), and there is a source with no word at all (`neverL`), for which the check reaches that point along a prefix of no source word. | tight: counterexamples `existsCheck_sound_needs_reachableLive`, `existsCheck_sound_needs_reachableLive_uninhabited` (witness class: a 3-state source with one dead state against destination `{[0]}`; and the uninhabited, edge-free source `neverL` against `unitL` at `nB = 0`) |

- **Non-vacuity witness:** `boolL` against `b0L`, `nB = 1`. (`existsCheck_sound_fit_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD2-sound`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:17-19
theorem existsCheck_sound_needs_fixedSize_dst :
    b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧ existsCheck b0L unitL = true ∧
      ¬ FitMeets b0L unitL 1 := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:28-30
theorem existsCheck_sound_needs_reachableLive :
    b0L.FixedSize 1 ∧ ¬ deadL.ReachableLive ∧ existsCheck deadL b0L = true ∧
      ¬ FitMeets deadL b0L 1 := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:48-50
theorem existsCheck_sound_needs_reachableLive_uninhabited :
    unitL.FixedSize 0 ∧ ¬ neverL.ReachableLive ∧ neverL.edges = [] ∧
      existsCheck neverL unitL = true ∧ ¬ FitMeets neverL unitL 0 := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:36-37
theorem existsCheck_sound_fit_nonvacuous :
    b0L.FixedSize 1 ∧ boolL.ReachableLive ∧ existsCheck boolL b0L = true := …
```

#### `LD2-sound-exists` — `existsCheck_sound_exists_fitMeets_of_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:83-84
theorem existsCheck_sound_exists_fitMeets_of_live {A B : Layout} (hlive : A.ReachableLive) :
    existsCheck A B = true → ∃ nB, FitMeets A B nB := …
```

- **Plain claim:** For every destination layout automaton `B` (deterministic or not, of fixed size or not, cyclic or not) and every source layout automaton `A` every state of which that is reachable from its start (by runs that stop at the accept state), the start state included, can still reach the accept state (`A.ReachableLive`; in particular `A` accepts at least one word): if `existsCheck A B = true`, then there is a size `nB` and a word `s` accepted by `A` such that `B` accepts `fit nB s` (`∃ nB, FitMeets A B nB`).
- **Kind:** theorem. **Tier:** T1 — A folklore property of existential product search, made precise for the layout check; it shows that the destination-size hypothesis of LD2-sound serves to pin the size parameter.
- **Depth:** substantive.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `existsCheck` is read as the exploration mode used when the compiler may assume a validity check by the programmer (some source transition, some destination transition), and `FitMeets A B nB` as the satisfiability, by at least one valid source value, of the caller's validity promise documented for `Assume::VALIDITY`, as stated in the sources cited here. rustc answers yes for an uninhabited source before any exploration, a rule the toy's checks do not have; the hypothesis `A.ReachableLive` excludes uninhabited sources instead. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 116-123: when the source layout is uninhabited the query answers yes before any automaton exploration (source comment: "conclude that the transmutation is acceptable, because instances of the `src` type do not exist", lines 118-119). The toy's checks have no such rule; the `ReachableLive` hypothesis excludes uninhabited sources instead.
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hlive : A.ReachableLive` | As in LD2-sound. | tight: counterexamples `existsCheck_sound_exists_needs_reachableLive`, `existsCheck_sound_exists_needs_reachableLive_uninhabited` (witness class: a 3-state source with one dead state against `{[0]}`, and the uninhabited, edge-free `neverL` against `unitL`; in both, no size `nB` makes the promise satisfiable) |

- **Non-vacuity witness:** `boolL` against `b0L`; and `pairSrcL` against `varDstL`, a destination without a fixed size, where the promise is satisfiable at size 1. (`existsCheck_sound_exists_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD2-sound-exists`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:58-59
theorem existsCheck_sound_exists_needs_reachableLive :
    ¬ deadL.ReachableLive ∧ existsCheck deadL b0L = true ∧ ¬ ∃ n, FitMeets deadL b0L n := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:74-76
theorem existsCheck_sound_exists_needs_reachableLive_uninhabited :
    ¬ neverL.ReachableLive ∧ existsCheck neverL unitL = true ∧
      ¬ ∃ n, FitMeets neverL unitL n := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:84-87
theorem existsCheck_sound_exists_nonvacuous :
    boolL.ReachableLive ∧ existsCheck boolL b0L = true ∧
      pairSrcL.ReachableLive ∧ existsCheck pairSrcL varDstL = true ∧
      (∀ n, ¬ varDstL.FixedSize n) ∧ FitMeets pairSrcL varDstL 1 := …
```

#### `LD2-noloss` — `existsCheck_eq_false_imp_no_promise_of_fixedSize`

```lean
-- lean/ToyLayoutDfa/Results.lean:120-122
theorem existsCheck_eq_false_imp_no_promise_of_fixedSize {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) := …
```

- **Plain claim:** For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not) and every destination layout automaton `B` (deterministic or not) all of whose accepted words have length exactly `nB` (`B.FixedSize nB`): if `existsCheck A B = false`, then no word `s` accepted by `A` has `fit nB s` accepted by `B`; so rejecting a pair never rejects one for which some valid source value satisfies the validity promise at size `nB`.
- **Kind:** theorem. **Tier:** T1 — Completeness of an exhaustive existential product search is folklore; stated here as "rejection loses no satisfiable promise" for the layout check with its step budget. Proved as the fixed-size corollary of LD2-noloss-acyc.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `existsCheck` is read as the exploration mode used when the compiler may assume a validity check by the programmer (some source transition, some destination transition), and `FitMeets A B nB` as the satisfiability, by at least one valid source value, of the caller's validity promise documented for `Assume::VALIDITY`, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hB : B.FixedSize nB` | Implies `B.ReachableLiveAcyclic` (`reachableLiveAcyclic_of_fixedSize`), which bounds every accepted destination word by the length of the edge list, so the step budget suffices; this card is the fixed-size corollary of LD2-noloss-acyc. `B.Acyclic` is a different sufficient condition (corollary `existsCheck_eq_false_imp_no_promise_of_acyclic`): neither of `B.FixedSize nB` and `B.Acyclic` implies the other (`fixedSize_acyclic_incomparable`). | tight: counterexample `existsCheck_noPromise_needs_fixedSize_dst` (witness class: a deterministic destination with a self-loop (3 edges, words of unbounded length) and a 6-state chain source whose word the destination accepts; the step budget is exhausted) |

- **Non-vacuity witness:** `b0L` against `b1L`: the check rejects and `b1L` has fixed size exactly 1. (`existsCheck_noPromise_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD2-noloss`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:96-99
theorem existsCheck_noPromise_needs_fixedSize_dst :
    ¬ cycL.FixedSize 5 ∧ existsCheck chainL cycL = false ∧
      chainL.Lang [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1] ∧
      cycL.Lang (fit 5 [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1]) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:102-103
theorem existsCheck_noPromise_nonvacuous :
    b1L.FixedSize 1 ∧ existsCheck b0L b1L = false := …
```

#### `LD2-noloss-acyc` — `existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic`

```lean
-- lean/ToyLayoutDfa/Results.lean:105-107
theorem existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic {A B : Layout} {nB : Nat}
    (hno : B.ReachableLiveAcyclic) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) := …
```
Unfolded (prose): `B.ReachableLiveAcyclic` is `∀ (pre : List Sym) (p : Nat) (c v : List Sym), c ≠ [] → B.Path B.start pre p → B.Path p c p → B.Accepts p v → False`.

- **Plain claim:** For every source layout automaton `A` (deterministic or not, with or without dead branches, with empty language or not), every destination layout automaton `B` (deterministic or not) without non-empty cycles through its reachable live part (`B.ReachableLiveAcyclic`: no non-empty run returns to a state that is reachable from the start state of `B` and from which the accept state of `B` is reachable; cycles through unreachable states or through dead states are allowed, and the accepted words may have different lengths), and every size `nB`: if `existsCheck A B = false`, then no word `s` accepted by `A` has `fit nB s` accepted by `B`.
- **Kind:** theorem. **Tier:** T1 — Settles, for the existential check, that the absence of cycles through the reachable live part of the destination suffices for the step budget; folklore for acyclic product exploration, made precise here.
- **Depth:** substantive.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `existsCheck` is read as the exploration mode used when the compiler may assume a validity check by the programmer (some source transition, some destination transition), and `FitMeets A B nB` as the satisfiability, by at least one valid source value, of the caller's validity promise documented for `Assume::VALIDITY`, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hno : B.ReachableLiveAcyclic` | Bounds every accepted destination word by the length of the edge list (`length_le_edges_of_reachableLiveAcyclic`), so the step budget suffices. | tight: counterexample `existsCheck_noPromise_needs_reachableLiveAcyclic` (witness class: a deterministic destination with a self-loop (3 edges, words of unbounded length) and a 6-state chain source whose word the destination accepts; the step budget is exhausted) |

- **Non-vacuity witness:** `b0L` against `b1L`; `b1L` against `varDstL` (acyclic, no fixed size); and `b1L` against `deadCycReachL` (fixed size 1, not `Acyclic`); the check rejects in all three. (`existsCheck_noPromise_acyclic_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD2-noloss-acyc`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:110-113
theorem existsCheck_noPromise_needs_reachableLiveAcyclic :
    ¬ cycL.ReachableLiveAcyclic ∧ existsCheck chainL cycL = false ∧
      chainL.Lang [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1] ∧
      cycL.Lang (fit 5 [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1]) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:118-123
theorem existsCheck_noPromise_acyclic_nonvacuous :
    (b1L.ReachableLiveAcyclic ∧ existsCheck b0L b1L = false) ∧
      (varDstL.ReachableLiveAcyclic ∧ (∀ n, ¬ varDstL.FixedSize n) ∧
        existsCheck b1L varDstL = false) ∧
      (deadCycReachL.ReachableLiveAcyclic ∧ ¬ deadCycReachL.Acyclic ∧
        existsCheck b1L deadCycReachL = false) := …
```

#### `LD2-iff` — `existsCheck_eq_true_iff_meets_of_eq_fixedSize_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:133-135
theorem existsCheck_eq_true_iff_meets_of_eq_fixedSize_live {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (hlive : A.ReachableLive) :
    existsCheck A B = true ↔ Meets A B := …
```
Unfolded (prose): `Meets A B` is `∃ s, A.Lang s ∧ B.Lang s`.

- **Plain claim:** For layout automata `A` and `B` all of whose accepted words have length exactly `n` (the same `n` for both), with every reachable state of `A`, the start state included, live (`A.ReachableLive`; `B` may be nondeterministic): `existsCheck A B = true` if and only if there is a word accepted by both (`Meets A B`).
- **Kind:** characterization. **Tier:** T1 — Non-emptiness of a DFA product is textbook and mechanized for total DFAs (prior art); the T1 content is the exact hypothesis set (equal fixed sizes, source liveness including inhabitation; no determinism) under which the layout check decides non-empty intersection, each hypothesis shown tight.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `existsCheck` is read as the exploration mode used when the compiler may assume a validity check by the programmer (some source transition, some destination transition), and `FitMeets A B nB` as the satisfiability, by at least one valid source value, of the caller's validity promise documented for `Assume::VALIDITY`, as stated in the sources cited here. rustc answers yes for an uninhabited source before any exploration, a rule the toy's checks do not have; the hypothesis `A.ReachableLive` excludes uninhabited sources instead. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 116-123: when the source layout is uninhabited the query answers yes before any automaton exploration (source comment: "conclude that the transmutation is acceptable, because instances of the `src` type do not exist", lines 118-119). The toy's checks have no such rule; the `ReachableLive` hypothesis excludes uninhabited sources instead.
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hA : A.FixedSize n` | Without it, there is a shorter source (`unitL`) that the extension rule accepts. | tight: counterexamples `existsCheck_iff_meets_needs_fixedSize_src`, `fixedSize_src_counterexamples_hold_for_mu8L` (witness class: source `()` and the destination `{[uninit]}` (one `uninit` symbol), `n = 1`; the same failure with the initialisation-monotone destination `mu8L`) |
  | `hB : B.FixedSize n` | Without it, there is a longer source (`b0L`) that the truncation rule accepts. | tight: counterexample `existsCheck_iff_meets_needs_fixedSize_dst` (witness class: source `{[0]}` and destination `()`, `n = 1`) |
  | `hlive : A.ReachableLive` | As in LD2-sound. | tight: counterexamples `existsCheck_iff_meets_needs_reachableLive`, `existsCheck_iff_meets_needs_reachableLive_uninhabited` (witness class: a 3-state source with one dead state, `n = 1`; and the uninhabited, edge-free `neverL` against `unitL`, `n = 0`) |

- **Non-vacuity witness:** `boolL`/`b0L` (accepted, meeting) and `b0L`/`b1L` (rejected, disjoint). (`existsCheck_iff_meets_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD2-iff`".
- **Prior art:**
  - J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
  - Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:131-133
theorem existsCheck_iff_meets_needs_fixedSize_src :
    uL.FixedSize 1 ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (existsCheck unitL uL = true ↔ Meets unitL uL) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:154-159
theorem fixedSize_src_counterexamples_hold_for_mu8L :
    mu8L.FixedSize 1 ∧ mu8L.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
    ¬ (forallCheck unitL mu8L = true ↔ Subset unitL mu8L) ∧
    ¬ (existsCheck unitL mu8L = true ↔ Meets unitL mu8L) ∧
    refCheck .shared .shared unitL true mu8L true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout mu8L true) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:140-142
theorem existsCheck_iff_meets_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (existsCheck b0L unitL = true ↔ Meets b0L unitL) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:156-158
theorem existsCheck_iff_meets_needs_reachableLive :
    deadL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ ¬ deadL.ReachableLive ∧
      ¬ (existsCheck deadL b0L = true ↔ Meets deadL b0L) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:150-152
theorem existsCheck_iff_meets_needs_reachableLive_uninhabited :
    neverL.FixedSize 0 ∧ unitL.FixedSize 0 ∧ ¬ neverL.ReachableLive ∧
      ¬ (existsCheck neverL unitL = true ↔ Meets neverL unitL) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:166-170
theorem existsCheck_iff_meets_nonvacuous :
    (boolL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ boolL.ReachableLive ∧
      existsCheck boolL b0L = true ∧ Meets boolL b0L) ∧
    (b0L.FixedSize 1 ∧ b1L.FixedSize 1 ∧ b0L.ReachableLive ∧
      existsCheck b0L b1L = false ∧ ¬ Meets b0L b1L) := …
```

#### `LD3-ext` — `forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live`

```lean
-- lean/ToyLayoutDfa/Results.lean:153-157
theorem forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live {A B : Layout}
    {nA nB : Nat} (hA : A.FixedSize nA) (hB : B.FixedSize nB) (hle : nA ≤ nB)
    (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    forallCheck A B = true ↔
      ∀ s, A.Lang s → B.Lang (s ++ List.replicate (nB - nA) Sym.uninit) := …
```

- **Plain claim:** For a source layout automaton `A` all of whose accepted words have length exactly `nA` and a destination layout automaton `B` all of whose accepted words have length exactly `nB`, with `nA ≤ nB`, `B` deterministic (`B.Deterministic`: from every state, reachable or not, including the accept state, at most one target per label) and every reachable state of `A`, the start state included, live (`A.ReachableLive`): `forallCheck A B = true` if and only if, for every word `s` accepted by `A`, `B` accepts `s` followed by exactly `nB - nA` `uninit` symbols.
- **Kind:** characterization. **Tier:** T1 — Follows the documented union-transmute extension semantics (trailing uninitialised bytes); the exact decision statement for the layout check is made precise here.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The padded form `s ++ List.replicate (nB - nA) Sym.uninit` and `fit` are read as the documented union-transmute extension of the source with trailing uninitialised bytes, and the fixtures named after Rust types (`u8L`, `u16L`, `u8PadL`) as intended readings of those types' layouts, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hA : A.FixedSize nA` | Fixes the padding length `nB - nA` for every source word. | tight: counterexample `extension_iff_needs_fixedSize_src` (witness class: source `{[0]}` claimed at size 0, destination `{[0, uninit]}`, `nB = 2`) |
  | `hB : B.FixedSize nB` | Ties the destination accept state to length `nB`. | tight: counterexample `extension_iff_needs_fixedSize_dst` (witness class: source and destination `{[0]}`, `nB = 2`) |
  | `hle : nA ≤ nB` | For a longer source the check truncates; with truncated subtraction the padded form then asks for inclusion of the full source words. | tight: counterexample `extension_iff_needs_le` (witness class: source `{[0]}` (size exactly 1), destination `()` (size exactly 0)) |
  | `hdet : B.Deterministic` | As in LD1-complete. | tight: counterexample `extension_iff_needs_deterministic` (witness class: small acyclic automata with at most 4 states over byte values 0-2, `nA = nB = 2`) |
  | `hlive : A.ReachableLive` | As in LD1-complete. | tight: counterexample `extension_iff_needs_reachableLive` (witness class: a 3-state source with one dead state, `nA = nB = 1`) |

- **Non-vacuity witness:** `boolL` into `boolUL` (accepted; padded strings valid) and into `bool2L` (rejected; `[0, uninit]` invalid); on initialisation-monotone full-width fixtures, `u8L` into `u8PadL` (accepted) and into `u16L` (rejected). (`extension_iff_nonvacuous`, `extension_iff_nonvacuous_fullWidth`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD3-ext`".
- **Prior art:**
  - No prior art beyond the documentation and source of the real system cited in this card's modeling bridge.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:178-182
theorem extension_iff_needs_fixedSize_src :
    b0uL.FixedSize 2 ∧ 0 ≤ 2 ∧ b0uL.Deterministic ∧ b0L.ReachableLive ∧
      ¬ b0L.FixedSize 0 ∧
      ¬ (forallCheck b0L b0uL = true ↔
        ∀ s, b0L.Lang s → b0uL.Lang (s ++ List.replicate (2 - 0) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:188-192
theorem extension_iff_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ 1 ≤ 2 ∧ b0L.Deterministic ∧ b0L.ReachableLive ∧
      ¬ b0L.FixedSize 2 ∧
      ¬ (forallCheck b0L b0L = true ↔
        ∀ s, b0L.Lang s → b0L.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:199-203
theorem extension_iff_needs_le :
    b0L.FixedSize 1 ∧ unitL.FixedSize 0 ∧ unitL.Deterministic ∧ b0L.ReachableLive ∧
      ¬ (1 ≤ 0) ∧
      ¬ (forallCheck b0L unitL = true ↔
        ∀ s, b0L.Lang s → unitL.Lang (s ++ List.replicate (0 - 1) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:207-211
theorem extension_iff_needs_deterministic :
    ndSrcL.FixedSize 2 ∧ ndDstL.FixedSize 2 ∧ 2 ≤ 2 ∧ ndSrcL.ReachableLive ∧
      ¬ ndDstL.Deterministic ∧
      ¬ (forallCheck ndSrcL ndDstL = true ↔
        ∀ s, ndSrcL.Lang s → ndDstL.Lang (s ++ List.replicate (2 - 2) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:216-220
theorem extension_iff_needs_reachableLive :
    deadL.FixedSize 1 ∧ b1L.FixedSize 1 ∧ 1 ≤ 1 ∧ b1L.Deterministic ∧
      ¬ deadL.ReachableLive ∧
      ¬ (forallCheck deadL b1L = true ↔
        ∀ s, deadL.Lang s → b1L.Lang (s ++ List.replicate (1 - 1) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:228-234
theorem extension_iff_nonvacuous :
    (boolL.FixedSize 1 ∧ boolUL.FixedSize 2 ∧ 1 ≤ 2 ∧ boolUL.Deterministic ∧
      boolL.ReachableLive ∧ forallCheck boolL boolUL = true ∧
      ∀ s, boolL.Lang s → boolUL.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) ∧
    (boolL.FixedSize 1 ∧ bool2L.FixedSize 2 ∧ 1 ≤ 2 ∧ bool2L.Deterministic ∧
      boolL.ReachableLive ∧ forallCheck boolL bool2L = false ∧
      ¬ bool2L.Lang ([Sym.byte 0] ++ List.replicate (2 - 1) Sym.uninit)) := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:298-304
theorem extension_iff_nonvacuous_fullWidth :
    (u8L.FixedSize 1 ∧ u8PadL.FixedSize 2 ∧ 1 ≤ 2 ∧ u8PadL.Deterministic ∧
      u8L.ReachableLive ∧ forallCheck u8L u8PadL = true ∧
      ∀ s, u8L.Lang s → u8PadL.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) ∧
    (u8L.FixedSize 1 ∧ u16L.FixedSize 2 ∧ 1 ≤ 2 ∧ u16L.Deterministic ∧
      u8L.ReachableLive ∧ forallCheck u8L u16L = false ∧
      ¬ u16L.Lang ([Sym.byte 0] ++ List.replicate (2 - 1) Sym.uninit)) := …
```

#### `LD3-u16` — `extension_u8_to_u16_rejected_u8_to_u8Pad_accepted`

```lean
-- lean/ToyLayoutDfa/Counterexamples2.lean:252-256
theorem extension_u8_to_u16_rejected_u8_to_u8Pad_accepted :
    u8L.FixedSize 1 ∧ u16L.FixedSize 2 ∧ u8PadL.FixedSize 2 ∧
      forallCheck u8L u16L = false ∧ ¬ u16L.Lang (fit 2 [Sym.byte 0]) ∧
      forallCheck u8L u8PadL = true ∧
      (∀ b : Fin 256, u8PadL.Lang [Sym.byte b, Sym.uninit]) := …
```

- **Role:** Full-width reference instance of LD3-ext (initialisation-monotone fixtures).
- **Plain claim:** For the toy layouts `u8L` (one initialised byte, size exactly 1), `u16L` (two initialised bytes, size exactly 2) and `u8PadL` (an initialised byte followed by a position that admits all 257 symbols, size exactly 2): `forallCheck u8L u16L = false` and `u16L` rejects `fit 2 [0] = [0, uninit]`, while `forallCheck u8L u8PadL = true` and `u8PadL` accepts `[b, uninit]` for every byte value `b`.
- **Kind:** counterexample. **Tier:** T0 — A reference instance of LD3-ext on full-width fixtures.
- **Depth:** definitional.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): The padded form `s ++ List.replicate (nB - nA) Sym.uninit` and `fit` are read as the documented union-transmute extension of the source with trailing uninitialised bytes, and the fixtures named after Rust types (`u8L`, `u16L`, `u8PadL`) as intended readings of those types' layouts, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments).
- **Hypothesis ledger:** no hypotheses (a statement about concrete fixtures).
- **Non-vacuity witness:** The theorem is itself a concrete instance. (`extension_u8_to_u16_rejected_u8_to_u8Pad_accepted`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD3-u16`".
- **Prior art:**
  - No prior art beyond the documentation and source of the real system cited in this card's modeling bridge.
- **Design question:** Exactly which language relations do the universal and existential product explorations of layout automata decide, and under which determinism, liveness, size and acyclicity hypotheses?

#### `LD4-ss` — `sharedShared_sound_iff`

```lean
-- lean/ToyLayoutDfa/Results.lean:174-176
theorem sharedShared_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .shared .shared S D ↔
      Includes S D ∧ S.freeze = D.freeze ∧ (D.freeze = false → Includes D S) := …
```

- **Plain claim:** In the toy reference model (`Sound`), for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a shared reference to `S` to a shared reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid, `S` and `D` have the same `Freeze` flag, and, when `D` is not `Freeze`, every `D`-valid byte string is `S`-valid.
- **Kind:** characterization. **Tier:** T1 — Combines the bit-validity conditions of shared reference casts (published package `transmutation-soundness-bit-validity-and-reference-variance`, cards R2 and R4) with the `frozen` assertion of shared references to `Freeze` referents; folklore in the Rust community, made precise in the toy.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
  - rust-lang/rust issue 164247 (https://github.com/rust-lang/rust/issues/164247; open on 2026-11-21, labelled I-unsound; title "TransmuteFrom::<_, Assume::NOTHING> can transmute references to types with interior mutability"): a public report whose example transmutes a shared reference to a `Cell` into `&[u8; 4]` and then calls `cell.set(1)` while the byte reference is in use. Prose context; not a subject and not relied on.
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : Satisfiable S` | From an uninhabited source every cast is vacuously sound. | tight: counterexample `sharedShared_sound_iff_needs_satisfiable` (witness class: the uninhabited referent `neverRef` and `cellByteRef`) |

- **Non-vacuity witness:** `& boolRef → & byteRef` (sound), `& cellByteRef → & byteRef` (unsound), `& cellByteRef → & cellByteRef` (sound). (`sharedShared_sound_iff_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-ss`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - Published package `send-sync-auto-traits-thread-safety-typing-and-interior-mutability`: card cell-not-sync (`not_semSync_cell`: two holders of a shared reference to a `Cell` can both write its storage).
  - Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:38-42
theorem sharedShared_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .shared .shared neverRef cellByteRef ↔
      Includes neverRef cellByteRef ∧ neverRef.freeze = cellByteRef.freeze ∧
        (cellByteRef.freeze = false → Includes cellByteRef neverRef)) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:177-180
theorem sharedShared_sound_iff_nonvacuous :
    Satisfiable boolRef ∧ Sound .shared .shared boolRef byteRef ∧
    Satisfiable cellByteRef ∧ ¬ Sound .shared .shared cellByteRef byteRef ∧
    Sound .shared .shared cellByteRef cellByteRef := …
```

#### `LD4-ms` — `mutShared_sound_iff`

```lean
-- lean/ToyLayoutDfa/Results.lean:189-190
theorem mutShared_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .mutable .shared S D ↔ Includes S D ∧ (D.freeze = false → Includes D S) := …
```

- **Plain claim:** In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a mutable reference to `S` to a shared reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid and, when `D` is not `Freeze`, every `D`-valid byte string is `S`-valid; `S`'s `Freeze` flag does not occur in the condition.
- **Kind:** characterization. **Tier:** T1 — As LD4-ss; the reborrowed `&mut` is inactive while the shared reference is live.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. A cast from `&mut S` to `&D` is read as a reborrow whose source is inactive while the shared reference is live. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : Satisfiable S` | As in LD4-ss. | tight: counterexample `mutShared_sound_iff_needs_satisfiable` (witness class: `neverRef` and `cellByteRef`) |

- **Non-vacuity witness:** `&mut boolRef → & byteRef` (sound), `&mut byteRef → & boolRef` (unsound), `&mut cellByteRef → & cellByteRef` (sound). (`mutShared_sound_iff_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-ms`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - Published package `send-sync-auto-traits-thread-safety-typing-and-interior-mutability`: card cell-not-sync (`not_semSync_cell`: two holders of a shared reference to a `Cell` can both write its storage).
  - Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:46-50
theorem mutShared_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .mutable .shared neverRef cellByteRef ↔
      Includes neverRef cellByteRef ∧
        (cellByteRef.freeze = false → Includes cellByteRef neverRef)) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:184-187
theorem mutShared_sound_iff_nonvacuous :
    Satisfiable boolRef ∧ Sound .mutable .shared boolRef byteRef ∧
    Satisfiable byteRef ∧ ¬ Sound .mutable .shared byteRef boolRef ∧
    Sound .mutable .shared cellByteRef cellByteRef := …
```

#### `LD4-mm` — `mutMut_sound_iff`

```lean
-- lean/ToyLayoutDfa/Results.lean:198-199
theorem mutMut_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .mutable .mutable S D ↔ Includes S D ∧ Includes D S := …
```

- **Plain claim:** In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D`: an unchecked cast from a mutable reference to `S` to a mutable reference to `D` is sound if and only if every `S`-valid byte string is `D`-valid and every `D`-valid byte string is `S`-valid; neither `Freeze` flag occurs.
- **Kind:** characterization. **Tier:** T0 — Restates card R3 of the published package `transmutation-soundness-bit-validity-and-reference-variance` in the combined toy model; `Freeze` flags play no role.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): A cast from `&mut S` to `&mut D` is read as a reborrow: the source reference performs no operation while the destination `&mut` is live, the destination may read the region and may write any `D`-valid byte string to it, and when the destination's use ends the source reads the region at type `S`. The `Freeze` flags play no role in this cell. This reading is informal, cites no external source, and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about Rust reference casts.
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : Satisfiable S` | As in LD4-ss. | tight: counterexample `mutMut_sound_iff_needs_satisfiable` (witness class: `neverRef` and `byteRef`) |

- **Non-vacuity witness:** `&mut byteRef → &mut byteRef` (sound), `&mut boolRef → &mut byteRef` (unsound). (`mutMut_sound_iff_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-mm`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:54-56
theorem mutMut_sound_iff_needs_satisfiable :
    ¬ Satisfiable neverRef ∧
    ¬ (Sound .mutable .mutable neverRef byteRef ↔ Includes neverRef byteRef ∧ Includes byteRef neverRef) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:191-193
theorem mutMut_sound_iff_nonvacuous :
    Satisfiable byteRef ∧ Sound .mutable .mutable byteRef byteRef ∧
    Satisfiable boolRef ∧ ¬ Sound .mutable .mutable boolRef byteRef := …
```

#### `LD4-sm` — `sharedMut_not_sound`

```lean
-- lean/ToyLayoutDfa/Results.lean:207-208
theorem sharedMut_not_sound {S D : RefTy} (hS : Satisfiable S) :
    ¬ Sound .shared .mutable S D := …
```

- **Role:** Definitional check of the `unique` assertion built into `OpOK`.
- **Plain claim:** In the toy reference model, for every source referent type `S` with at least one valid byte string (`Satisfiable S`) and every destination referent type `D` (any validities, any `Freeze` flags), an unchecked cast from a shared reference to `S` to a mutable reference to `D` is not sound.
- **Kind:** impossibility. **Tier:** T0 — Folklore (`&T → &mut T` is never allowed); in this toy a one-step unfolding of the `unique` clause of `OpOK`.
- **Depth:** definitional.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): A cast from `&S` to `&mut D` is read as producing a mutable reference while the shared source reference remains usable; in the toy, one read through the source while the destination `&mut` is live violates the `unique` assertion. Apart from the hypothesis `Satisfiable S`, the validities and the `Freeze` flags play no role in this cell. This reading is informal, cites no external source, and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about Rust reference casts.
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : Satisfiable S` | From an uninhabited source every cast is vacuously sound. | tight: counterexample `sharedMut_not_sound_needs_satisfiable` (witness class: `neverRef` and `byteRef`) |

- **Non-vacuity witness:** `& byteRef → &mut byteRef`. (`sharedMut_not_sound_nonvacuous`)
- **Positive control:** `sharedMut_positive_control`.
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-sm`".
- **Prior art:**
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:61-62
theorem sharedMut_not_sound_needs_satisfiable :
    ¬ Satisfiable neverRef ∧ Sound .shared .mutable neverRef byteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:197-198
theorem sharedMut_not_sound_nonvacuous :
    Satisfiable byteRef ∧ ¬ Sound .shared .mutable byteRef byteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:67-68
theorem sharedMut_positive_control :
    Sound .mutable .mutable byteRef byteRef ∧ Sound .shared .shared byteRef byteRef := …
```

#### `LD4-matrix-sound` — `sound_of_matrixOK`

```lean
-- lean/ToyLayoutDfa/Results.lean:222-223
theorem sound_of_matrixOK {ms md : Mode} {S D : RefTy} :
    MatrixOK ms md S D → Sound ms md S D := …
```

- **Plain claim:** In the toy reference model, for every mode pair `ms`, `md` and all referent types `S` and `D` (no satisfiability hypothesis, no `Freeze` hypothesis): if the obligation matrix `MatrixOK` holds — `& → &`: `S ⊆ D`, `D` `Freeze` and `S` `Freeze`; `&mut → &`: `S ⊆ D` and `D` `Freeze`; `&mut → &mut`: `S ⊆ D` and `D ⊆ S`; `& → &mut`: never — then the cast is sound.
- **Kind:** theorem. **Tier:** T1 — The obligation matrix imposed by checkers that require `Freeze` on shared sources and destinations; its soundness in the toy is made precise here.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
- **Hypothesis ledger:** no side hypotheses: the theorem is universally quantified over both modes `ms`, `md` and both referent types `S`, `D`, and its antecedent is `MatrixOK ms md S D`; neither `Satisfiable S` nor `D.freeze = true` is assumed.
- **Non-vacuity witness:** The three accepting cells each hold for a fixture pair. (`sound_of_matrixOK_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-matrix-sound`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - Published package `send-sync-auto-traits-thread-safety-typing-and-interior-mutability`: card cell-not-sync (`not_semSync_cell`: two holders of a shared reference to a `Cell` can both write its storage).
  - Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:201-203
theorem sound_of_matrixOK_nonvacuous :
    MatrixOK .shared .shared boolRef byteRef ∧ MatrixOK .mutable .shared boolRef byteRef ∧
    MatrixOK .mutable .mutable byteRef byteRef := …
```

#### `LD4-matrix-iff` — `matrixOK_iff_sound_of_sharedDst_freeze`

```lean
-- lean/ToyLayoutDfa/Results.lean:236-238
theorem matrixOK_iff_sound_of_sharedDst_freeze {ms md : Mode} {S D : RefTy}
    (hS : Satisfiable S) (hD : md = .shared → D.freeze = true) :
    MatrixOK ms md S D ↔ Sound ms md S D := …
```

- **Plain claim:** In the toy reference model, for every mode pair, for every source referent type `S` with at least one valid byte string (`Satisfiable S`), and every destination referent type `D` that is `Freeze` whenever the destination reference is shared: `MatrixOK` holds if and only if the cast is sound.
- **Kind:** characterization. **Tier:** T1 — Corollary of LD4-ss, LD4-ms, LD4-mm, LD4-sm and LD4-matrix-sound.
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : Satisfiable S` | As in LD4-ss. | tight: counterexample `matrixOK_iff_sound_needs_satisfiable` (witness class: `& neverRef → &mut byteRef`) |
  | `hD : md = .shared → D.freeze = true` | There is a shared, non-`Freeze` destination (`cellByteRef`) with sound casts outside the matrix. | tight: counterexample `matrixOK_iff_sound_needs_sharedDst_freeze` (witness class: `& cellByteRef → & cellByteRef` and `&mut cellByteRef → & cellByteRef`) |

- **Non-vacuity witness:** `& boolRef → & byteRef` (accepted, sound) and `& cellByteRef → & byteRef` (rejected, unsound). (`matrixOK_iff_sound_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-matrix-iff`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - Published package `send-sync-auto-traits-thread-safety-typing-and-interior-mutability`: card cell-not-sync (`not_semSync_cell`: two holders of a shared reference to a `Cell` can both write its storage).
  - Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`).
  - R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
  - R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
  - N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:73-75
theorem matrixOK_iff_sound_needs_satisfiable :
    ¬ Satisfiable neverRef ∧ (Mode.mutable = Mode.shared → byteRef.freeze = true) ∧
    ¬ (MatrixOK .shared .mutable neverRef byteRef ↔ Sound .shared .mutable neverRef byteRef) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:82-87
theorem matrixOK_iff_sound_needs_sharedDst_freeze :
    Satisfiable cellByteRef ∧ ¬ (Mode.shared = Mode.shared → cellByteRef.freeze = true) ∧
    ¬ (MatrixOK .shared .shared cellByteRef cellByteRef ↔
      Sound .shared .shared cellByteRef cellByteRef) ∧
    ¬ (MatrixOK .mutable .shared cellByteRef cellByteRef ↔
      Sound .mutable .shared cellByteRef cellByteRef) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:209-214
theorem matrixOK_iff_sound_nonvacuous :
    (Satisfiable boolRef ∧ (Mode.shared = Mode.shared → byteRef.freeze = true) ∧
      MatrixOK .shared .shared boolRef byteRef ∧ Sound .shared .shared boolRef byteRef) ∧
    (Satisfiable cellByteRef ∧ (Mode.shared = Mode.shared → byteRef.freeze = true) ∧
      ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
      ¬ Sound .shared .shared cellByteRef byteRef) := …
```

#### `LD4-cell` — `cellByte_to_byte_admitted_without_srcFreeze`

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:22-30
theorem cellByte_to_byte_admitted_without_srcFreeze :
    MatrixOKNoSrcFreeze .shared .shared cellByteRef byteRef ∧
    Includes cellByteRef byteRef ∧ Includes byteRef cellByteRef ∧
    ¬ Sound .shared .shared cellByteRef byteRef ∧
    Permitted .shared .shared cellByteRef byteRef (.write .src [Sym.byte 1]) ∧
    FrozenDuring .shared .shared cellByteRef byteRef ∧
    ¬ RunOK .shared .shared cellByteRef byteRef [Sym.byte 0] [.write .src [Sym.byte 1]] ∧
    ¬ MatrixOK .shared .shared cellByteRef byteRef ∧
    MatrixOK .shared .shared byteRef byteRef ∧ Sound .shared .shared byteRef byteRef := …
```

- **Role:** Headline counterexample for dropping the source-side `Freeze` obligation.
- **Plain claim:** For the toy referents `cellByteRef` (validity of one initialised byte, not `Freeze`; modelling `Cell<u8>`) and `byteRef` (the same validity, `Freeze`; modelling `u8`): the obligation matrix with the source-side `Freeze` obligation removed (`MatrixOKNoSrcFreeze`) holds for `& cellByteRef → & byteRef`, the two validities are included in each other, and the cast is not sound; from contents `[0]`, writing `[1]` through the source view is permitted (`Permitted`), the `frozen` assertion is in force (`FrozenDuring`), and that one-operation run violates an assertion (`RunOK` fails); the full `MatrixOK` rejects this cast and accepts `& byteRef → & byteRef`, which is sound.
- **Kind:** counterexample. **Tier:** T0 — A concrete instance of a known hazard of interior mutability, of the shape described by a public report (https://github.com/rust-lang/rust/issues/164247), in the toy.
- **Depth:** definitional.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. The counterexample has the shape of the example in the public report https://github.com/rust-lang/rust/issues/164247 (a shared reference to a `Cell` transmuted to a byte-array reference, then `cell.set(1)` while the byte reference is in use); no claim is made about the implementation behind that report. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
  - rust-lang/rust issue 164247 (https://github.com/rust-lang/rust/issues/164247; open on 2026-11-21, labelled I-unsound; title "TransmuteFrom::<_, Assume::NOTHING> can transmute references to types with interior mutability"): a public report whose example transmutes a shared reference to a `Cell` into `&[u8; 4]` and then calls `cell.set(1)` while the byte reference is in use. Prose context; not a subject and not relied on.
- **Hypothesis ledger:** no hypotheses (a statement about concrete fixtures).
- **Non-vacuity witness:** The theorem is itself a concrete instance. (`cellByte_to_byte_admitted_without_srcFreeze`)
- **Positive control:** `sound_shared_shared_byte_byte`.
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-cell`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
  - Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`).
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefExamples.lean:51-51
theorem sound_shared_shared_byte_byte : Sound .shared .shared byteRef byteRef := …
```

#### `LD4-refcheck` — `refCheck_sound_of_eq_fixedSize`

```lean
-- lean/ToyLayoutDfa/Results.lean:259-262
theorem refCheck_sound_of_eq_fixedSize {ms md : Mode} {S D : Layout} {fzS fzD : Bool} {n : Nat}
    (hS : S.FixedSize n) (hD : D.FixedSize n) :
    refCheck ms md S fzS D fzD = true →
      Sound ms md (RefTy.ofLayout S fzS) (RefTy.ofLayout D fzD) := …
```

- **Plain claim:** For referent layout automata `S` and `D` all of whose accepted words have length exactly `n` (the same `n` for both; deterministic or not, with or without dead branches), every mode pair `ms`, `md` and all caller-supplied `Freeze` flags `fzS`, `fzD`: if `refCheck ms md S fzS D fzD = true`, then the cast is sound in the toy reference model for the referent types `RefTy.ofLayout S fzS` and `RefTy.ofLayout D fzD`.
- **Kind:** theorem. **Tier:** T1 — Composition of LD1-sound with the matrix soundness (LD4-matrix-sound).
- **Depth:** shallow.
- **Basis:** execution (Lean kernel check), for every Lean statement quoted in this card.
- **Basis:** derived (modeling bridge): `RefTy.freeze` is read as `core::marker::Freeze` holding for the whole referent, and the writes of a non-`Freeze` shared view as those that `Cell` permits (any value valid at its type, through a shared reference); `cellByteRef` and `byteRef` are read as `Cell<u8>` and `u8`, as stated in the sources cited here. `refCheck` is read as a reference rule that decides validity inclusion with the universal layout check and takes the `Freeze` flags from the caller. `forallCheck` is read as the exploration mode of rustc's transmutability checker used when the compiler cannot assume a validity check by the programmer (for every source transition, some destination transition), with its truncation rule (success once the destination reaches its accept state) and its extension rule (the destination's `uninit` edge once the source reaches its accept state), as stated in the source comments cited here. The reading is argued from the cited documentation and source and is not proved. Model–system relation: none proved. These statements neither establish nor refute the corresponding claims about the cited systems.
  Sources read for this bridge (pinned revisions):
  - rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
  - `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
  - `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
- **Hypothesis ledger:**

  | hypothesis | why it is there | tightness |
  | --- | --- | --- |
  | `hS : S.FixedSize n` | Equal referent sizes: there is a shorter source referent (`unitL` into `uL`) for which the value-level extension rule makes `refCheck` accept an unsound cast. | tight: counterexamples `refCheck_sound_needs_fixedSize_src`, `fixedSize_src_counterexamples_hold_for_mu8L` (witness class: `& () → & {[uninit]}`, `n = 1`; the same failure with the initialisation-monotone destination `mu8L`) |
  | `hD : D.FixedSize n` | Equal referent sizes: there is a longer source referent (`b0L` into `unitL`) for which the value-level truncation rule makes `refCheck` accept a cast that is unsound for whole-region references. | tight: counterexample `refCheck_sound_needs_fixedSize_dst` (witness class: `& {[0]} → & ()`, `n = 1`) |

- **Non-vacuity witness:** `refCheck` accepts `& boolL → & u8L`, `&mut boolL → & u8L` and `&mut u8L → &mut u8L` (all `Freeze`). (`refCheck_sound_nonvacuous`)
- **Non-claims:** listed first under Boundaries, in the subsection "Non-claims: `LD4-refcheck`".
- **Prior art:**
  - Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results.
  - Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee).
- **Design question:** For reference casts, which `Freeze` obligations make a validity-inclusion check sound, and which make it exact?

Counterexamples, witnesses and controls named above (verbatim):

```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:97-99
theorem refCheck_sound_needs_fixedSize_src :
    uL.FixedSize 1 ∧ ¬ unitL.FixedSize 1 ∧ refCheck .shared .shared unitL true uL true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout uL true) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:154-159
theorem fixedSize_src_counterexamples_hold_for_mu8L :
    mu8L.FixedSize 1 ∧ mu8L.Deterministic ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
    ¬ (forallCheck unitL mu8L = true ↔ Subset unitL mu8L) ∧
    ¬ (existsCheck unitL mu8L = true ↔ Meets unitL mu8L) ∧
    refCheck .shared .shared unitL true mu8L true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout unitL true) (RefTy.ofLayout mu8L true) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:112-114
theorem refCheck_sound_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ ¬ unitL.FixedSize 1 ∧ refCheck .shared .shared b0L true unitL true = true ∧
    ¬ Sound .shared .shared (RefTy.ofLayout b0L true) (RefTy.ofLayout unitL true) := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:220-223
theorem refCheck_sound_nonvacuous :
    boolL.FixedSize 1 ∧ u8L.FixedSize 1 ∧ refCheck .shared .shared boolL true u8L true = true ∧
    refCheck .mutable .shared boolL true u8L true = true ∧
    refCheck .mutable .mutable u8L true u8L true = true := …
```

### Auxiliary lemmas cited by name (verbatim)

Fully proved helpers and fixture facts (none is a result of the package); proofs elided.

```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:249-253
theorem fixedSize_acyclic_incomparable :
    (deadCycReachL.FixedSize 1 ∧ deadCycReachL.Deterministic ∧ deadCycReachL.Lang [Sym.byte 0] ∧
      ¬ deadCycReachL.Acyclic) ∧
    (varDstL.Acyclic ∧ varDstL.Deterministic ∧ varDstL.Lang [Sym.byte 0] ∧
      ∀ n, ¬ varDstL.FixedSize n) := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:62-62
theorem sound_shared_shared_cell_cell : Sound .shared .shared cellByteRef cellByteRef := …
```
```lean
-- lean/ToyLayoutDfa/RefExamples.lean:90-90
theorem sound_mut_shared_cell_cell : Sound .mutable .shared cellByteRef cellByteRef := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:42-42
theorem inhabited_of_reachableLive {A : Layout} (h : A.ReachableLive) : ∃ s, A.Lang s := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:367-368
theorem reachableLiveAcyclic_of_fixedSize {B : Layout} {n : Nat} (hB : B.FixedSize n) :
    B.ReachableLiveAcyclic := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:376-376
theorem reachableLiveAcyclic_of_acyclic {B : Layout} (hB : B.Acyclic) : B.ReachableLiveAcyclic := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:45-46
theorem reachableDeterministic_of_deterministic {A : Layout} (h : A.Deterministic) :
    A.ReachableDeterministic := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:256-258
theorem forallAux_complete_fit_of_lt_fuel {A B : Layout} {nB fuel : Nat}
    (hfuel : nB < fuel) (hdet : B.ReachableDeterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallAux A B fuel A.start B.start = true := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:281-285
theorem checks_depend_on_edge_list_representation :
    cycDupL.start = cycL.start ∧ cycDupL.accept = cycL.accept ∧
      (∀ e, e ∈ cycDupL.edges ↔ e ∈ cycL.edges) ∧ (∀ w, cycDupL.Lang w ↔ cycL.Lang w) ∧
      forallCheck chainL cycL = false ∧ forallCheck chainL cycDupL = true ∧
      existsCheck chainL cycL = false ∧ existsCheck chainL cycDupL = true := …
```
```lean
-- lean/ToyLayoutDfa/RefTools.lean:45-46
theorem sound_iff_soundOneStep {ms md : Mode} {S D : RefTy} :
    Sound ms md S D ↔ SoundOneStep ms md S D := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:358-359
theorem length_le_edges_of_reachableLiveAcyclic {B : Layout} (hno : B.ReachableLiveAcyclic)
    {w : List Sym} (hw : B.Lang w) : w.length ≤ B.edges.length := …
```
```lean
-- lean/ToyLayoutDfa/Results.lean:56-58
theorem forallCheck_complete_fit_of_acyclic_det_live {A B : Layout} {nB : Nat}
    (hacyc : B.Acyclic) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:259-261
theorem reachableLiveAcyclic_strictly_weaker_than_both :
    (deadCycReachL.ReachableLiveAcyclic ∧ ¬ deadCycReachL.Acyclic) ∧
    (varDstL.ReachableLiveAcyclic ∧ ∀ n, ¬ varDstL.FixedSize n) := …
```
```lean
-- lean/ToyLayoutDfa/Results.lean:250-251
theorem subset_of_forallCheck_of_eq_fixedSize {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (h : forallCheck A B = true) : Subset A B := …
```
```lean
-- lean/ToyLayoutDfa/Counterexamples.lean:76-78
theorem ndSrcL_ndDstL_lang (s : List Sym) :
    (ndSrcL.Lang s ↔ s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2]) ∧
    (ndDstL.Lang s ↔ s = [Sym.byte 0, Sym.byte 1] ∨ s = [Sym.byte 0, Sym.byte 2]) := …
```
```lean
-- lean/ToyLayoutDfa/Results.lean:126-128
theorem existsCheck_eq_false_imp_no_promise_of_acyclic {A B : Layout} {nB : Nat}
    (hacyc : B.Acyclic) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) := …
```
```lean
-- lean/ToyLayoutDfa/Lemmas.lean:304-306
theorem existsAux_start_of_lang_fit_of_lt_fuel {A B : Layout} {k fuel : Nat} {s : List Sym}
    (hs : A.Lang s) (hb : B.Lang (fit k s)) (hk : k < fuel) :
    existsAux A B fuel A.start B.start = true := …
```
```lean
-- lean/ToyLayoutDfa/RefCounterexamples.lean:127-130
theorem refCheck_mutMut_needs_eq_fixedSize :
    unitL.FixedSize 0 ∧ uL.FixedSize 1 ∧
    refCheck .mutable .mutable unitL true uL true = true ∧
    ¬ Sound .mutable .mutable (RefTy.ofLayout unitL true) (RefTy.ofLayout uL true) := …
```

### Modeling bridge (derived; not kernel-checked)

Basis for every item: derived (modeling bridge). Model–system relation: none proved.

1. **Layout automata.** rustc's transmutability checker represents layouts as automata with one start and one accept state, byte edges labelled by ranges over 0..=256 where 256 stands for an uninitialised byte, and `Byte::uninit()` covering every value (rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments)). The toy uses single-symbol edges over the same 257 values; a padding position is 257 edges (`anyEdges`). The toy's terminal accept state follows the documented comment that out-edges of the accept state do not affect the semantics. Unlike rustc's uninit range, the toy does not force a position with an `uninit` edge to accept every byte value; the fixtures `uL`, `b0uL` and `boolUL` use such positions, and `mu8L`, `u8PadL` do not.

2. **The two quantifiers.** rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role). Quoted (lines 213-215): "if the compiler may assume that the programmer is doing additional validity checks, (e.g.: that `src != 3u8` when the destination type is `bool`) then there must exist at least one transition out of `src_state` such that the transmute is viable..."; (lines 218-220): "if the compiler cannot assume that the programmer is doing additional validity checks, then for all transitions out of `src_state`, such that the transmute is viable... then there must exist at least one transition out of `dst_state` such that the transmute is viable...". `forallCheck` and `existsCheck` model these two modes for byte edges; reference edges and `Answer::If` conditions are not modelled.

3. **Uninhabited sources.** rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 116-123: when the source layout is uninhabited the query answers yes before any automaton exploration (source comment: "conclude that the transmutation is acceptable, because instances of the `src` type do not exist", lines 118-119). The toy's checks have no such rule; the `ReachableLive` hypothesis excludes uninhabited sources instead.

4. **Validity promise and extension semantics.** `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation). The toy's `FitMeets` is the satisfiability of that promise for some valid source value, and `fit` pads with `uninit` as the documented union-transmute does.

5. **Reference model.** The toy's `frozen` and `unique` assertions follow the modality atoms of the published pointer-modality package; non-`Freeze` shared referents permit writes as `Cell` does; `Freeze` is a flag independent of validity, as `UnsafeCell<u8>` and `u8` show (`core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source)). `Cell::from_mut`, `Cell::as_slice_of_cells` and `Cell::as_array_of_cells` are documented, stable APIs of the `&mut T → &Cell<T>`, `&Cell<[T]> → &[Cell<T>]` and `&Cell<[T; N]> → &[Cell<T>; N]` shapes, matching the toy's sound non-`Freeze` cells (`core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation)). The toy's `Freeze` flag covers the whole region; Rust's `Freeze` is about containment of `UnsafeCell` anywhere in the type, so types with interior mutability in part of their bytes have no faithful encoding in the toy.

6. **Public report.** rust-lang/rust issue 164247 (https://github.com/rust-lang/rust/issues/164247; open on 2026-11-21, labelled I-unsound; title "TransmuteFrom::<_, Assume::NOTHING> can transmute references to types with interior mutability"): a public report whose example transmutes a shared reference to a `Cell` into `&[u8; 4]` and then calls `cell.set(1)` while the byte reference is in use. Prose context; not a subject and not relied on.

## Boundaries

### Non-claims

Non-claims of each card, listed first. Every card also carries the scope statement: these are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker, the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD1-sound`

- Does not say the check is complete; completeness needs further hypotheses (LD1-complete, LD1-complete-acyc), and there is a nondeterministic destination (`ndDstL`, LD1-nd) for which it fails.
- `FixedSize` holds at every size for an automaton with empty language. When the source `A` has empty language, `FitSubset A B nB` holds vacuously; when the destination `B` has empty language (so `B.FixedSize nB` holds for every `nB`), the theorem says that `forallCheck A B = false` for every inhabited source `A`.
- Says nothing positive about destinations whose accepted words have different lengths: there is such a destination (`varDstL`) and a source (`pairSrcL`) that the check accepts although `FitSubset` fails at every size (`forallCheck_sound_needs_fixedSize_dst_variable`).
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD1-complete`

- Does not cover nondeterministic destinations (LD1-nd) or sources with reachable dead branches; a check that tracks sets of destination states is not modelled (its completeness is not proved here).
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem. For such sources the check's answer is not characterized here.
- `B.Deterministic` constrains every state of `B`, reachable or not, including the out-edges of the accept state. The proof uses determinism at states reachable from the start other than the accept state (`forallAux_complete_fit_of_lt_fuel` assumes `ReachableDeterministic` instead), but this card's statement assumes `Deterministic`.
- On destinations with a non-empty cycle through their reachable live part the check's behaviour is characterized by neither this card nor LD1-complete-acyc; the budget lemma `forallAux_complete_fit_of_lt_fuel` covers every destination size below the step budget.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD1-complete-acyc`

- `B.ReachableLiveAcyclic` is implied by `B.FixedSize nB` (`reachableLiveAcyclic_of_fixedSize`) and by `B.Acyclic` (`reachableLiveAcyclic_of_acyclic`), and is strictly weaker than each (`reachableLiveAcyclic_strictly_weaker_than_both`: `deadCycReachL` has a fixed size and a cycle at a reachable dead state; `varDstL` is acyclic without a fixed size). `B.FixedSize nB` and `B.Acyclic` are incomparable (`fixedSize_acyclic_incomparable`). This card therefore implies LD1-complete and the global-acyclicity corollary `forallCheck_complete_fit_of_acyclic_det_live`.
- Whether a still weaker hypothesis on `B` suffices is not examined, beyond the budget lemma `forallAux_complete_fit_of_lt_fuel`, which needs a destination size below the step budget.
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem. For such sources the check's answer is not characterized here.
- `B.Deterministic` constrains every state of `B`, reachable or not, including the out-edges of the accept state. The proof uses determinism at states reachable from the start other than the accept state (`forallAux_complete_fit_of_lt_fuel` assumes `ReachableDeterministic` instead), but this card's statement assumes `Deterministic`.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD1-iff`

- This is the equal-size corollary of LD1-sound and LD1-complete (at equal sizes `fit n s = s`), and the case `nA = nB` of LD3-ext. For unequal sizes the check decides the `fit` relation (LD1-sound, LD1-complete, LD3-ext), which differs from inclusion.
- The soundness direction holds without `hdet` and `hlive` (`subset_of_forallCheck_of_eq_fixedSize`); both are assumed for the completeness direction, where each is tight.
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem.
- `B.Deterministic` constrains every state of `B`, reachable or not, including the out-edges of the accept state. The proof uses determinism at states reachable from the start other than the accept state (`forallAux_complete_fit_of_lt_fuel` assumes `ReachableDeterministic` instead), but this card's statement assumes `Deterministic`.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD1-nd`

- Does not show that every nondeterministic destination defeats the check.
- The failure is of the check, not of inclusion: both automata have the same language (`ndSrcL_ndDstL_lang`).
- Says nothing about rustc, whose layout automaton type is named `Dfa` (whether its automata are deterministic in the sense of `Deterministic` is not examined here); this counterexample concerns a nondeterministic encoding.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD2-sound`

- This is the fixed-destination-size corollary of LD2-sound-exists: `hB` pins the existential size to `nB`.
- `existsCheck A B = true` does not make an `Assume::VALIDITY`-style transmute sound without a guarantee from the caller, and it does not identify which source values are valid at `B`; it establishes that the validity promise is satisfiable by at least one source word.
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem. Without `hlive`, `existsCheck neverL unitL = true` although `neverL` accepts no word (`existsCheck_sound_needs_reachableLive_uninhabited`); rustc answers yes for uninhabited sources before any exploration (see the card's modeling-bridge line), a rule the toy's checks do not have.
- There is a source with a dead branch (`deadL`, against `b0L`) for which the check accepts although no valid source value satisfies the promise (`existsCheck_sound_needs_reachableLive`); by the definition of `FitMeets`, no use of that pair can satisfy the promise.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD2-sound-exists`

- The size `nB` is existentially quantified: it is the length of the destination word the check found; for a destination with words of several lengths it is one of them.
- The universal check has no analogue of this statement without a fixed destination size: there is a pair (`pairSrcL`, `varDstL`) that `forallCheck` accepts while `FitSubset` fails at every size (`forallCheck_sound_needs_fixedSize_dst_variable`).
- `existsCheck A B = true` does not make an `Assume::VALIDITY`-style transmute sound without a guarantee from the caller, and it does not identify which source values are valid at `B`; it establishes that the validity promise is satisfiable by at least one source word.
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem. Without `hlive`, `existsCheck neverL unitL = true` although `neverL` accepts no word (`existsCheck_sound_exists_needs_reachableLive_uninhabited`); rustc answers yes for uninhabited sources before any exploration (see the card's modeling-bridge line), a rule the toy's checks do not have.
- Degenerate zero size: the existential size may be `nB = 0`, where `fit 0 s = []` discards the whole source word; the conclusion then says that `B` accepts `[]`.
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD2-noloss`

- Does not establish the converse: there is a source with a reachable dead branch (`deadL`) and there is a source with empty language (`neverL`) for which `existsCheck A B = true` holds although no source word satisfies the promise (`existsCheck_sound_needs_reachableLive`, `existsCheck_sound_needs_reachableLive_uninhabited`); see LD2-sound.
- On destinations with a non-empty cycle through their reachable live part the check's answer is characterized by neither this card nor LD2-noloss-acyc; the budget lemma `existsAux_start_of_lang_fit_of_lt_fuel` covers every destination size below the step budget.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD2-noloss-acyc`

- Does not establish the converse: there is a source with a reachable dead branch (`deadL`) and there is a source with empty language (`neverL`) for which `existsCheck A B = true` holds although no source word satisfies the promise (`existsCheck_sound_needs_reachableLive`, `existsCheck_sound_needs_reachableLive_uninhabited`); see LD2-sound.
- `B.ReachableLiveAcyclic` is implied by `B.FixedSize nB` (`reachableLiveAcyclic_of_fixedSize`) and by `B.Acyclic` (`reachableLiveAcyclic_of_acyclic`), and is strictly weaker than each (`reachableLiveAcyclic_strictly_weaker_than_both`: `deadCycReachL` has a fixed size and a cycle at a reachable dead state; `varDstL` is acyclic without a fixed size). `B.FixedSize nB` and `B.Acyclic` are incomparable (`fixedSize_acyclic_incomparable`). This card therefore implies LD2-noloss and the global-acyclicity corollary `existsCheck_eq_false_imp_no_promise_of_acyclic`.
- Whether a still weaker hypothesis on `B` suffices is not examined, beyond the budget lemma `existsAux_start_of_lang_fit_of_lt_fuel`, which needs a destination size below the step budget.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD2-iff`

- Determinism of either automaton is not assumed.
- This is the equal-size corollary of LD2-sound and LD2-noloss.
- `existsCheck A B = true` does not make an `Assume::VALIDITY`-style transmute sound without a guarantee from the caller, and it does not identify which source values are valid at `B`; it establishes that the validity promise is satisfiable by at least one source word.
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem. Without `hlive`, `existsCheck neverL unitL = true` although `neverL` accepts no word (`existsCheck_iff_meets_needs_reachableLive_uninhabited`); rustc answers yes for uninhabited sources before any exploration (see the card's modeling-bridge line), a rule the toy's checks do not have.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD3-ext`

- The condition is per source word: the destination must accept each valid source string followed by `uninit` symbols. It is not the condition that every destination state at depth `nA` accepts `uninit` continuations (such a state may be unreachable by source words); the relation between the two is not proved here.
- Says nothing about a source longer than the destination (truncation); see LD1-sound and LD1-complete for the `fit` form covering both cases.
- The semantics of the extra bytes (`uninit`) is the toy's reading of a union-style transmute; other conventions (zero-filled or copied bytes) are not modelled.
- Value-level size extension does not transfer to whole-region reference casts: there is a shorter source referent (`unitL` into `uL`) for which `refCheck` accepts a cast that is unsound in the reference model (`refCheck_sound_needs_fixedSize_src`; LD4-refcheck).
- `A.ReachableLive` requires `A.start` itself to reach `A.accept` (`inhabited_of_reachableLive`), so source automata with empty language, including the edge-free `neverL`, are outside this theorem.
- `B.Deterministic` constrains every state of `B`, reachable or not, including the out-edges of the accept state. The proof uses determinism at states reachable from the start other than the accept state (`forallAux_complete_fit_of_lt_fuel` assumes `ReachableDeterministic` instead), but this card's statement assumes `Deterministic`.
- Degenerate zero size: at size 0, `fit 0 s = []` discards the whole source word, and `FixedSize 0` holds exactly when the language is `{[]}` (a zero-sized type) or empty (an uninhabited type). At `nA = 0` the padded word consists of exactly `nB` `uninit` symbols.
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- Edges carry single symbols of the 257-symbol alphabet; byte-range edges, reference (pointer) edges inside layouts, alignment, and the `Assume` flags other than validity are not modelled. `Layout` is a partial automaton with a single terminal accept state (textbook DFAs have a total transition function and non-terminal accept states), and it does not enforce initialisation monotonicity: a position may accept `Sym.uninit` without accepting the 256 initialised byte values, unlike rustc's uninit byte range, which covers every value.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD3-u16`

- Rejection of `u8L` into `u16L` reflects union-style `uninit` padding (`fit 2 [b] = [b, uninit]`), not integer zero-extension (`u8 as u16`); the existential check rejects this pair as well (`ex_not_existsCheck`).
- The fixtures are toy automata named after Rust types; their correspondence with rustc's layouts of those types is a modelling assumption.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-ss`

- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- `RefTy.freeze` is a single Boolean for the whole referent region: `freeze = false` models uniform `Cell`-like interior mutability, under which a shared view may overwrite the whole region with any byte string valid at its type. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled. For example, `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- Necessity (the `→` direction) and the counterexample runs assume that a non-`Freeze` shared view can write any byte string valid at its type to the whole region (`Cell`-like unrestricted writes, including the empty string for a zero-sized referent). `!Freeze` wrappers whose APIs restrict the written values, or never write during the cast, are not modelled; for them the necessity direction is not established (escape hatch).
- In particular the toy counts `& cellByteRef → & cellByteRef` (the `&Cell<u8> → &Cell<u8>` shape, `cellByteRef` being the toy's reading of `Cell<u8>`) as sound (`sound_shared_shared_cell_cell`); real checkers may reject such casts for reasons outside the toy.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-ms`

- The toy models `&mut S → &D` as a reborrow whose source `&mut` is inactive while the destination `&` is live; pointer provenance and aliasing-tag retagging of a bit-level transmute of `&mut` into `&` are not modelled. Two-phase borrows and reborrow chains longer than one step are not modelled either.
- That `D: Freeze` is not necessary (`&mut cellByteRef → & cellByteRef`, the `&mut Cell<u8> → &Cell<u8>` shape with `cellByteRef` the toy's reading of `Cell<u8>`, is sound in the toy, `sound_mut_shared_cell_cell`) is a statement about the toy.
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- `RefTy.freeze` is a single Boolean for the whole referent region: `freeze = false` models uniform `Cell`-like interior mutability, under which a shared view may overwrite the whole region with any byte string valid at its type. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled. For example, `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- Necessity (the `→` direction) and the counterexample runs assume that a non-`Freeze` shared view can write any byte string valid at its type to the whole region (`Cell`-like unrestricted writes, including the empty string for a zero-sized referent). `!Freeze` wrappers whose APIs restrict the written values, or never write during the cast, are not modelled; for them the necessity direction is not established (escape hatch).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-mm`

- Writes through the cast reference are of arbitrary `D`-valid values; APIs that restrict writes are not modelled.
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructor compatibility (drop glue run on overwrite or at the end of the borrow) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-sm`

- Escape hatches that defeat the impossibility: (1) dropping `Satisfiable S` (an uninhabited source makes `Sound` vacuous: `sharedMut_not_sound_needs_satisfiable`); (2) weakening the `unique` assertion of `OpOK`, which in the toy forbids even a single read through the source view with no write; (3) APIs with dynamic exclusivity (such as `RefCell::borrow_mut` or `Mutex::lock`) that suspend source accesses while the `&mut` is live, which the toy does not model. Whether the impossibility persists under a weaker uniqueness notion is not proved here.
- Says nothing about raw-pointer or `UnsafeCell::get` routes to mutation.
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-matrix-sound`

- The matrix is not exact without further hypotheses: the toy has sound casts it rejects (LD4-matrix-iff, `matrixOK_iff_sound_needs_sharedDst_freeze`).
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- `RefTy.freeze` is a single Boolean for the whole referent region: `freeze = false` models uniform `Cell`-like interior mutability, under which a shared view may overwrite the whole region with any byte string valid at its type. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled. For example, `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- The toy models `&mut S → &D` as a reborrow whose source `&mut` is inactive while the destination `&` is live; pointer provenance and aliasing-tag retagging of a bit-level transmute of `&mut` into `&` are not modelled.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-matrix-iff`

- Exactness is relative to the toy's assertions; it does not say real checkers that impose these obligations are exact.
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- `RefTy.freeze` is a single Boolean for the whole referent region: `freeze = false` models uniform `Cell`-like interior mutability, under which a shared view may overwrite the whole region with any byte string valid at its type. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled. For example, `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- Necessity (the `→` direction) and the counterexample runs assume that a non-`Freeze` shared view can write any byte string valid at its type to the whole region (`Cell`-like unrestricted writes, including the empty string for a zero-sized referent). `!Freeze` wrappers whose APIs restrict the written values, or never write during the cast, are not modelled; for them the necessity direction is not established (escape hatch).
- The toy models `&mut S → &D` as a reborrow whose source `&mut` is inactive while the destination `&` is live; pointer provenance and aliasing-tag retagging of a bit-level transmute of `&mut` into `&` are not modelled.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-cell`

- The violation is of the toy's `frozen` assertion; for bit validity alone the cast is fine (card R4-src of the published package `transmutation-soundness-bit-validity-and-reference-variance`).
- The counterexample run assumes that a non-`Freeze` shared view can write any byte string valid at its type to the whole region (`Cell`-like unrestricted writes); in this run the source view writes `[1]` over the contents `[0]`. `!Freeze` wrappers whose APIs restrict the written values, or never write during the cast, are not modelled; the counterexample does not cover them, and whether such a cast is unsound for them is not examined (escape hatch).
- No claim is made about the implementation behind https://github.com/rust-lang/rust/issues/164247; the issue serves as context: a public report of the same shape.
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

#### Non-claims: `LD4-refcheck`

- Completeness of `refCheck` is not stated as a theorem (not proved here).
- `fzS` and `fzD` are trusted caller-supplied Booleans; `refCheck` does not compute or verify `Freeze` from the layouts `S` and `D`, which cannot distinguish `Cell<u8>` from `u8`.
- `refCheck_sound_needs_fixedSize_dst` (`& {[0]} → & ()` failing) is a consequence of the toy's whole-region reference model, in which both views validate the entire region; it neither establishes nor refutes the soundness of prefix-shrinking shared reference casts (`&T → &U` with a smaller `U`), which are not modelled.
- The equal-size requirement also bites in the `&mut → &mut` cell (`refCheck_mutMut_needs_eq_fixedSize`).
- `Sound` consists of the toy's three assertions (bit validity of reads, the whole-region `frozen` assertion, and `unique`). Referent sizes (both views cover the same region), alignment, lifetimes, library safety invariants, Rust's aliasing and provenance models (Stacked Borrows, Tree Borrows) and destructors (drop glue) are not modelled. `Sound` is equivalent to its one-operation form `SoundOneStep` (`sound_iff_soundOneStep`): runs of several operations add nothing in this model, because a write replaces the whole region.
- `RefTy.freeze` is a single Boolean for the whole referent region: `freeze = false` models uniform `Cell`-like interior mutability, under which a shared view may overwrite the whole region with any byte string valid at its type. Per-byte placement of `UnsafeCell` and synchronisation (`Sync`, atomics, locks) are not modelled. For example, `(u8, Cell<u8>)` and `(Cell<u8>, u8)` of equal validity, or `Cell<u8>` and `AtomicU8`, receive the same encoding, so the toy's verdict on a cast between them carries no information about Rust.
- The toy models `&mut S → &D` as a reborrow whose source `&mut` is inactive while the destination `&` is live; pointer provenance and aliasing-tag retagging of a bit-level transmute of `&mut` into `&` are not modelled.
- Degenerate zero size: at `n = 0` both layouts accept at most `[]` (zero-sized or uninhabited referents).
- `forallCheck` and `existsCheck` are pure recursive functions of a state pair and a step budget; no memo table is modelled, and that caching their results per state pair is transparent is not proved here. The budget `fuelFor B` is one more than the length of the edge list of `B`, counting duplicate and unreachable edges; there are two edge lists for the same cyclic destination (`cycL`, `cycDupL`) on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's transmutability checker (`rustc_transmute`), the unstable `core::mem::TransmuteFrom` trait, or zerocopy. Model–system relation: none proved.

### Attractive stronger conclusions that are not established

- That rustc's transmutability checker decides inclusion or non-empty intersection exactly, or that `TransmuteFrom` accepts or rejects any particular pair of Rust types. The cards characterize the toy checks `forallCheck` and `existsCheck`; the correspondence with rustc is a derived modeling bridge.
- That every nondeterministic destination defeats the universal check. LD1-nd exhibits one destination (`ndDstL`) for which it does; `forallCheck_ndSrcL_self` shows that the check accepts the deterministic `ndSrcL` against itself.
- That the absence of cycles through the reachable live part of the destination is the weakest hypothesis under which the universal check is complete or the existential check loses no satisfiable promise. Each of `B.ReachableLiveAcyclic`, `B.FixedSize nB` and `B.Acyclic` is shown sufficient (LD1-complete-acyc, LD1-complete, `forallCheck_complete_fit_of_acyclic_det_live`; LD2-noloss-acyc, LD2-noloss, `existsCheck_eq_false_imp_no_promise_of_acyclic`), and dropping `B.ReachableLiveAcyclic` without a replacement can fail (`forallCheck_complete_needs_reachableLiveAcyclic`, `existsCheck_noPromise_needs_reachableLiveAcyclic`); whether a weaker condition suffices is not examined beyond the budget lemmas `forallAux_complete_fit_of_lt_fuel` and `existsAux_start_of_lang_fit_of_lt_fuel`, which need a destination size below the step budget.
- That the checks' answers depend on the languages of the automata alone. In the toy they do not: there are two edge lists with the same language for the same cyclic destination on which both checks give different answers (`checks_depend_on_edge_list_representation`).
- That `existsCheck A B = true` makes an `Assume::VALIDITY`-style transmute sound, or identifies which source values are valid at `B`. LD2-sound and LD2-sound-exists establish that the validity promise is satisfiable by at least one source word.
- That a Rust cast of the `&Cell<u8> → &Cell<u8>` or `&mut Cell<u8> → &Cell<u8>` shape is sound, or that a Rust cast of the `&Cell<u8> → &u8` shape has undefined behaviour. The toy's verdicts on `cellByteRef` and `byteRef` are statements about the toy reference model.
- That `refCheck` is complete (not proved here), or that it computes `Freeze`: its `Freeze` flags are caller-supplied Booleans.
- Any result for byte-range edges, reference edges inside layouts, alignment, `Assume` flags other than validity, per-byte `UnsafeCell` placement, synchronisation, provenance or aliasing-tag retagging.

### Escape hatches

Which hypotheses or settings, when dropped or changed, defeat the impossibility and counterexample results (each item names a proved theorem quoted in this report or says that it is not proved here):

- LD4-sm (`sharedMut_not_sound`): dropping `Satisfiable S` defeats the impossibility (`sharedMut_not_sound_needs_satisfiable`: from the uninhabited `neverRef` the cast `& neverRef → &mut byteRef` is vacuously sound). Weakening the `unique` clause of `OpOK`, or APIs with dynamic exclusivity that suspend source accesses while the `&mut` is live, are outside the model; whether the impossibility persists under a weaker uniqueness notion is not proved here. The positive control `sharedMut_positive_control` shows sound casts in the `&mut` → `&mut` and `&` → `&` cells.
- LD1-nd (`forallCheck_complete_needs_deterministic`): with a deterministic destination the universal check is complete under the hypotheses of LD1-complete or LD1-complete-acyc, and it accepts the deterministic `ndSrcL` against itself (`forallCheck_ndSrcL_self`).
- LD4-cell (`cellByte_to_byte_admitted_without_srcFreeze`): with the source-side `Freeze` obligation restored (`MatrixOK`), the cast `& cellByteRef → & byteRef` is rejected, and `& byteRef → & byteRef` is accepted and sound (the same theorem; `sound_shared_shared_byte_byte`).
- LD3-u16 (`extension_u8_to_u16_rejected_u8_to_u8Pad_accepted`): a destination whose second position admits all 257 symbols (`u8PadL`) accepts the extension that `u16L` rejects.
- The necessity directions of LD4-ss, LD4-ms and LD4-matrix-iff, and the counterexample run of LD4-cell, assume that a non-`Freeze` shared view can write any byte string valid at its type to the whole region; for `!Freeze` wrappers whose APIs restrict the written values, or that never write during the cast, neither those necessity directions nor the LD4-cell counterexample is established.

### Hypotheses whose tightness is `unknown`

None. Every hypothesis in every ledger is `tight`, with a fully proved counterexample theorem named in the ledger.

### Dropped or disproved statements

None. All 20 results are fully proved with the statements quoted in their cards; none is dropped or disproved.

### Not examined

- Checks that track sets of destination states (as in antichain-based inclusion checking); their completeness for nondeterministic destinations is not proved here.
- rustc's actual layouts for the Rust types named in fixture doc comments, rustc's memoization of the exploration, its `Answer::If` conditions and its reference edges.
- Prefix-shrinking shared reference casts (`&T → &U` with a smaller `U`); the toy's reference model validates the whole region in both views.
- Novelty: a web search (2026-11-21) for mechanized proofs of DFA-based transmutability checkers in Lean, Coq or Isabelle, and for mechanized automata libraries, found no mechanization of the layout check's exact correctness (with truncation, extension and step budget) or of the reference `Freeze` matrix; mechanized automata libraries were found (prior art in the cards). This is a search record, not a proof of absence; no result is claimed novel (no `T3` tier).

## Evidence

Basis for every theorem below: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`); no Mathlib; `lake build` of `lean/` succeeds, and no Lean source of the package contains `sorry`, `admit`, `native_decide` or an `axiom`/`opaque` declaration. The axiom audit (`Lean.collectAxioms`, recorded in `audit/axioms.json`) covers all 522 non-internal constants of the modules of the library `ToyLayoutDfa` (constructors, recursors and generated auxiliary declarations included); none of them depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. The statement hash is the SHA-256 of the Lean `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted `name : type := value` texts of every package-local constant reachable from the statement (theorem bodies excluded). Both are recorded for all 204 names referenced by `results.json` in `audit/statements.json` and are recomputed by `support/revalidate.py`. The kernel check and the hash records were produced on 2026-11-21; the external sources below were read at the pinned revisions on the same date.

Where the results are proved: the main theorems are in `lean/ToyLayoutDfa/Results.lean`; the counterexample cards LD1-nd, LD3-u16 and LD4-cell are in `Counterexamples.lean`, `Counterexamples2.lean` and `RefCounterexamples.lean`; definitions are in `Basic.lean`, `Fixtures.lean`, `Refs.lean` and `RefTools.lean`; definition examples are in `Examples.lean` and `RefExamples.lean`; proof infrastructure is in `Tools.lean`, `Lemmas.lean` and `RefTools.lean`. Soundness of both checks goes through invariants for an arbitrary step budget ("some size-`k` view `fit k v` is accepted"), which `FixedSize` pins to `k = nB`; completeness goes through the budget lemma `forallAux_complete_fit_of_lt_fuel` and no-loss through an analogous budget lemma for `existsAux` (of the form of `existsAux_start_of_lang_fit_of_lt_fuel`), together with the bound `length_le_edges_of_reachableLiveAcyclic` (an accepting run that repeats a reachable live state yields a cycle); the reference cells go through `sound_iff_soundOneStep`. Concrete counterexamples and witnesses are kernel-checked computations (`decide`, including `decide +kernel` on the 256- and 257-edge fixtures) or short structural proofs.

### Main results (card `lean` fields)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.LayoutDfa.forallCheck_sound_fit_of_fixedSize` | `Quot.sound`, `propext` | `13dcae29f640e230fb3b7a48f4d79b1603b248bd6fbcb2bfdf5b1202b67b1aa7` | `a58b3b02adb5aa092921a0e94dc79ed3765b20e79056553e525e2f26b37ac3ad` |
| `Toy.LayoutDfa.forallCheck_complete_fit_of_fixedSize_det_live` | `Classical.choice`, `Quot.sound`, `propext` | `8cbaeb613225df70e083dab93f5702bff89360568066e0b22810cc7e803feca6` | `283122872ca16341ca293cd32df747364592d9e1c09471ec56482676f9f0f342` |
| `Toy.LayoutDfa.forallCheck_complete_fit_of_reachableLiveAcyclic_det_live` | `Classical.choice`, `Quot.sound`, `propext` | `576d11fffe306b9e9c47f3af42a4eb78349e862e495d11789b19d76ce663de0b` | `6b6ea5f7f771e3e4c3887e63659b5185ca35f2bcf72223a0fb9f20c09c20d591` |
| `Toy.LayoutDfa.forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live` | `Classical.choice`, `Quot.sound`, `propext` | `6ec827477204920cf8a55ed963badee91a1915d686d7842e325fe75467e007b7` | `f78747dcc57c505a7e6053236144ee12f75a68042dfeb4b8fdeaa5c20760a4a5` |
| `Toy.LayoutDfa.forallCheck_complete_needs_deterministic` | `Quot.sound`, `propext` | `c1d018652e13908d6cf0ad2e729f26575cd35a21e91d71e993cc8b9f575b0f47` | `f386acf44a62f6d520d3068ec03c1cbed51ff4bb39febefe9c5d79b484491145` |
| `Toy.LayoutDfa.existsCheck_sound_fit_of_fixedSize_live` | `Quot.sound`, `propext` | `08770b7cd7a5cf84715574fdc5c8948aa92da419c8f56a4a54e7a26e2ad0f001` | `17c13224252ee2bc38c1a3ea5e3713a0e0b79b93d2ad31d223f29ce3c7e57278` |
| `Toy.LayoutDfa.existsCheck_sound_exists_fitMeets_of_live` | `Quot.sound`, `propext` | `5b905b329921bde05808c1c57547ec449be675f15850c95d5c511df82b4a93e6` | `1fc1e2c2fdea754d6c892872fce41dff30290da7c29d7a559f0eb9f80d51180a` |
| `Toy.LayoutDfa.existsCheck_eq_false_imp_no_promise_of_fixedSize` | `Classical.choice`, `Quot.sound`, `propext` | `34913a5300adb543ac5be94838188d0756fd8c40bc6f261c97ed7f70c192d757` | `279a99afb49dd5931c66ca8849736f93dabaf2ff844d20a09a5d2b2ebcf9840a` |
| `Toy.LayoutDfa.existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic` | `Classical.choice`, `Quot.sound`, `propext` | `61c906037821e181b7c8c10eafa73aa5678d4d3320cc3733487f6edd00f91dd5` | `3651b00a070fa04fb847ef09d795fdbbcad6fd59a6554c477cf92f59de8d3540` |
| `Toy.LayoutDfa.existsCheck_eq_true_iff_meets_of_eq_fixedSize_live` | `Classical.choice`, `Quot.sound`, `propext` | `6a32600cd98c03b50e4f7dff86db19b32c72d180f8b489dc58d8213c943bac90` | `0852912e381bfdc30dd6c8f984f26856fd4b248b6abb4e3eaf2bff4af1083287` |
| `Toy.LayoutDfa.forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live` | `Classical.choice`, `Quot.sound`, `propext` | `2f02dbd15d4cb6c1e9979c53af3c667530f46683f73b92152cd8611a6cfcd6ac` | `aafa9a7dbc5662671d14181dcb8c631a93cedcdc42b0e4be9f878247e757f992` |
| `Toy.LayoutDfa.extension_u8_to_u16_rejected_u8_to_u8Pad_accepted` | `Quot.sound`, `propext` | `b9e9cf624c8a1dccaa43faa6181a00bc011176d47bc54cdb06f87b05be06b2c3` | `a76b66c463362986b86da87ef994cd87d7d8e3d3d0769266011795ded8ca135e` |
| `Toy.LayoutDfa.sharedShared_sound_iff` | `Quot.sound`, `propext` | `ad441b08fd5f4591862796070b89200fe936dd5ea2eb87685d71e26a82b6b14f` | `82446588839982eb10168b30bc322266db5edf6ca025af385795fb37d92b1a9e` |
| `Toy.LayoutDfa.mutShared_sound_iff` | `Quot.sound`, `propext` | `7c898ba2d9a53f64bb8c2de39abff8c6d7c9a1a46842152388af10b79a5adf1a` | `82446588839982eb10168b30bc322266db5edf6ca025af385795fb37d92b1a9e` |
| `Toy.LayoutDfa.mutMut_sound_iff` | `Quot.sound`, `propext` | `91283319fa03c015d149263117705dfaf807c45622897698dd234a1fbd806ac6` | `82446588839982eb10168b30bc322266db5edf6ca025af385795fb37d92b1a9e` |
| `Toy.LayoutDfa.sharedMut_not_sound` | `propext` | `b7796817566910097dbb82d8dbed7bde6a4bb59a2e09a1dc49df829633e6e024` | `21f4fd80f6198ebcc01340bdea5327679c40ee2c3878264645a1570b309561c0` |
| `Toy.LayoutDfa.sound_of_matrixOK` | `Quot.sound`, `propext` | `b6cf20edf8f55ad8eee6c5c6b5f20788c2dc977fc9fda778525134c7d7b8f1c0` | `d322920f489abaae06c05a09409065e572484fc1be589436e30725a403781dda` |
| `Toy.LayoutDfa.matrixOK_iff_sound_of_sharedDst_freeze` | `Quot.sound`, `propext` | `5da2bcb1b727b090c5c580142ba38a8b86837d119cd8da15a3e9224c537ae9dc` | `79308764359fc5ae8f9844af4fc4f8602a362f8c806f1bfbc0c8674e3fbe2960` |
| `Toy.LayoutDfa.cellByte_to_byte_admitted_without_srcFreeze` | `Quot.sound`, `propext` | `eba3c967f4bbfe0d279d80188da0a21a6b6a3528fb2cbc0bd5381d411b661d0f` | `9fdf367b9a2ddd5a025b96a3a1c2b54a6582082e63773e1a76dc02ad10786d64` |
| `Toy.LayoutDfa.refCheck_sound_of_eq_fixedSize` | `Quot.sound`, `propext` | `d1ea5f45383070d1c00128e2ba6a228fb59431cace5ab0b85686c5fa049798eb` | `99aff33af5694719fe78b1a40e246345276879b38b348f1088f8add05e07966c` |

### Non-vacuity witnesses, positive controls and tightness counterexamples

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.LayoutDfa.forallCheck_sound_fit_nonvacuous` | `propext` | `2b8286f3bea33bf012f63ad8858e86d14b12503fb1f02a72c4cf80d03ccf832b` | `2075f8e024b6f8f33d25ae3dfcfd9d417a0a2de14006f7fd1a7a6d358b1499dc` |
| `Toy.LayoutDfa.forallCheck_sound_needs_fixedSize_dst_variable` | `Quot.sound`, `propext` | `4b6fcad393a10e994010d4a8cdde6c25d1bb938fc5917d3f79f0a31b5eeb9012` | `2d281214c72465da82d7c3baa3054165cc7bce8f30be84e845460b9845ab0f2a` |
| `Toy.LayoutDfa.forallCheck_sound_needs_fixedSize_dst` | `Quot.sound`, `propext` | `f63c1fe066651607072d39d4503d372096c450dff811fac6c71cebe1ad6a78ce` | `078cf2dcb1a79f09db3e92b2fa89aa244c410f6e4182e7faf571f61d07f66a15` |
| `Toy.LayoutDfa.forallCheck_complete_fit_nonvacuous` | `Quot.sound`, `propext` | `6ebb24ff4831748e12718ea7a2fef3495791ce721dbbebceafb4153c5bd6c17e` | `1d1b39e4f73637b5a04e21b5e47af60aeff8e563b24c06e586e9932bf124f88e` |
| `Toy.LayoutDfa.forallCheck_complete_needs_fixedSize_dst` | `Quot.sound`, `propext` | `eac89ef87f58f3ce565108861d513c3ac4298ff706136f56d6b3fc0c92991919` | `377414342043b60abf71c5134247f69c12ccd2a7d16d6e36d100d9304d31b252` |
| `Toy.LayoutDfa.forallCheck_complete_needs_reachableLive` | `Quot.sound`, `propext` | `e3554d2dc25e329496a6a205216725f051d9031cec4c66223c441641c64b01fb` | `7908145b354101796cf44eda33a72650ab48eaac7d85787cd51c53386823a6fc` |
| `Toy.LayoutDfa.forallCheck_complete_acyc_nonvacuous` | `Quot.sound`, `propext` | `be9544e66251f3f582b66aa045862d3978720445be02574ff69a847ba10322af` | `00f5d6ab1a123fbd44d07731e78b1816f250b4e5e05b99f493f8d48836ebb064` |
| `Toy.LayoutDfa.forallCheck_complete_needs_reachableLiveAcyclic` | `Quot.sound`, `propext` | `313b13f82a99f690e8951949233dea35e33d1b9ec0a2d7a611b2347f23b382b9` | `b54583382b2ad6f2e7a566ed97c84421b8a9d46f74dfb4e9a82f6bbf5a4e22b5` |
| `Toy.LayoutDfa.forallCheck_complete_acyc_needs_deterministic` | `Quot.sound`, `propext` | `7793550200c0c339395597b3c7637cefe19ab84ec84e76e7448322a3518ed9e4` | `82d329be5df9842608d27140ca6e20ddbeb08cc0f786dd66c03b66d58565d362` |
| `Toy.LayoutDfa.forallCheck_complete_acyc_needs_reachableLive` | `Quot.sound`, `propext` | `1dcce2602916ce91b2239315f68249fbb4b77ed0e41ae7e1202a6d96365566bd` | `08931fc78abfa14eb2f9a0cbaa6244b72ddb69ec01d243c7a4a7223e218bc77d` |
| `Toy.LayoutDfa.forallCheck_iff_subset_nonvacuous` | `Quot.sound`, `propext` | `1321a4a9384631d1d09855f64b2a7f9721a4a9594b2fa9c962ee36d41dd5d4cb` | `3b6a3fc9c7672faa5755187ae32c4a33e92438ac9ddd5a528b55fbbf17c92f85` |
| `Toy.LayoutDfa.forallCheck_iff_subset_needs_fixedSize_src` | `Quot.sound`, `propext` | `15e0d456b825ffe4791170573b97eb64e1b8793cc74bed80180ae370a3f6e52f` | `e7987527d24b6e27520fce74b5714e22dad33150f0d5d78109eb207d1e69e0a4` |
| `Toy.LayoutDfa.fixedSize_src_counterexamples_hold_for_mu8L` | `Quot.sound`, `propext` | `6077c19ffc8e6dd5f0abafa903db358d863ba52cbe89108969ae52226313cb65` | `55faa3ddbbedee5a2dbc00dd76ea8163651374da5cdf43a1c208ee68b3dd7215` |
| `Toy.LayoutDfa.forallCheck_iff_subset_needs_fixedSize_dst` | `Quot.sound`, `propext` | `8de4a75e86869f22c5377b26b7f56f43c52509162bc19c66954a2756d94b6660` | `883fe2e7ea0ab1bf99cb4f986e46f13ce6a3598ce38434891ec099a89057d604` |
| `Toy.LayoutDfa.forallCheck_iff_subset_needs_deterministic` | `Quot.sound`, `propext` | `c0a9cbfd6bfa208762bd9288c12a14222346c3e7d4903962ff5c403633f5370f` | `22bcb1d6dbba74c01779ff33d9ff3d6956e08007ff4ecdf2798d18cd1b4ad0a0` |
| `Toy.LayoutDfa.forallCheck_iff_subset_needs_reachableLive` | `Quot.sound`, `propext` | `a4efe05a2b931ce2e8add8c46b4ef77068af1204062cc39bbeb83bb207cbb68c` | `486e156a3899158eabb318de1c280ac542afbc1a0485892760c989ced998dd2f` |
| `Toy.LayoutDfa.forallCheck_ndSrcL_self` | `propext` | `8cc8e7ddcfdfaad70e50b6ae6ee2a4e0b388e5966e59be2c22c5b73a1813a876` | `8f2752b361770632561b73d73e7fad77976804bf8fe7fa46a34c16c7ef283f86` |
| `Toy.LayoutDfa.existsCheck_sound_fit_nonvacuous` | `Quot.sound`, `propext` | `1bc940adafe48e659497a080bb8d8ee328574a5cd86f52b9e937f4e3ccbdd52f` | `15ca6392d37750881ddf3f56e2f9a29dda967d6d649ec99bde6b0e921679295c` |
| `Toy.LayoutDfa.existsCheck_sound_needs_fixedSize_dst` | `Quot.sound`, `propext` | `bd8a9551bacbfcb07b6254f660ee59e864ddf978041eb7043e6cf6ab36a99d68` | `43ee7ee5ff7664ab2859dad2baa73ed46ad4951b98b9e69d598fc8c21b343e43` |
| `Toy.LayoutDfa.existsCheck_sound_needs_reachableLive` | `Quot.sound`, `propext` | `0dcc4c42c795a841616403db1e955d9528dff7da402ddb1e4f935a82266b0eb4` | `3cdf909b41080f186729588e1e2cef13f82930ecfbc9ae04fed32de1f7f0cf60` |
| `Toy.LayoutDfa.existsCheck_sound_needs_reachableLive_uninhabited` | `propext` | `360742688d011740f11376eb44d72b660a26b91b1681db46436f0d464d5e710b` | `d8d21d8d9f51152522175b118177ba4e4088c6d85743ce01ca97c7f46c20f66b` |
| `Toy.LayoutDfa.existsCheck_sound_exists_nonvacuous` | `Quot.sound`, `propext` | `63c0d60bcca9b473efd499d69692208a2f35e41874b0ee8bcf0f522357435350` | `b1405e2b9efed3869635f6110c7ccbcd8c5552a675699d20de37d55eb769afad` |
| `Toy.LayoutDfa.existsCheck_sound_exists_needs_reachableLive` | `Quot.sound`, `propext` | `d4b5d1a66cff66917ed1687bad0f1d8754736edea3f0d59ed7e2b6196d1defa6` | `1108bd809049b59d3fa71f18187ff890b9adc6a1f38f25003ba18a1b6650546c` |
| `Toy.LayoutDfa.existsCheck_sound_exists_needs_reachableLive_uninhabited` | `propext` | `015a3d91ad43c41c4915dcdcbed0b6f548f574353e85a3a56b09f81e20ad3182` | `b7bf27cf28918b992700bb56a9311c6d59a53ca7645f03ba5468da0db8910047` |
| `Toy.LayoutDfa.existsCheck_noPromise_nonvacuous` | `propext` | `6c1659537a34c53f9916892fd4b797c0af8eeab19b7a7cf1bb47e0a25fb952ce` | `813ac5db91a2eb043b6bfe00cf3148adcdef0f720a80abee65cf5ed18bbcb7ef` |
| `Toy.LayoutDfa.existsCheck_noPromise_needs_fixedSize_dst` | `Quot.sound`, `propext` | `9053b71edfe28cb7c64349a6ab92f54add066d7b9236121497d85dae2a639059` | `ccbb1a64acf2e18bd0946c257511f6d58d752ffb2ad80d790de8eea5a74aefe4` |
| `Toy.LayoutDfa.existsCheck_noPromise_acyclic_nonvacuous` | `Quot.sound`, `propext` | `0c39f95c7887a971e052ec029224c81723b520746346f071e2d1ef01fd3cc53c` | `5434cf37880fb5201feb98a42c6712bda8ae6950030983e5d913760ca8cac068` |
| `Toy.LayoutDfa.existsCheck_noPromise_needs_reachableLiveAcyclic` | `Quot.sound`, `propext` | `6af852d46a1c4a0eedffc306b534a685f94830582b81c4dfee3071e05e8beb6e` | `06897026b8c1a0d7286b4f77b661d51a4580a6d83fb37c48900bce13f707e790` |
| `Toy.LayoutDfa.existsCheck_iff_meets_nonvacuous` | `Quot.sound`, `propext` | `4abc22d5915b819d42adb3a5042db0a2b488c6aba068b67dc507a36c7d487527` | `25a1d80283130d73109c4da3f2bc507fe4a6e8c6ce37d3ccb80879611e8da3bf` |
| `Toy.LayoutDfa.existsCheck_iff_meets_needs_fixedSize_src` | `Quot.sound`, `propext` | `45b9f4fa684d17f58b75d88784f7ee59f4708c72cc6cbe793c7c9d2af6adc65b` | `21aac8dfafca151bbc112466ffefef22b4882edad429faca48d84cb555c26717` |
| `Toy.LayoutDfa.existsCheck_iff_meets_needs_fixedSize_dst` | `Quot.sound`, `propext` | `4fa3175be6ad78f28bc068927b7a9fe3767ad15d0b2fc678840210f91412c0ec` | `6bcde8f8b78a0369f7f49e98c783eb4e8e9d60d0cf4432f59430ac68b5747814` |
| `Toy.LayoutDfa.existsCheck_iff_meets_needs_reachableLive` | `Quot.sound`, `propext` | `ba3d83319e8fd0b624e4d89cb6cbb791291bc450b449c0aa017c37d672e1dc1e` | `4e0e5a0848a63d14eadfe46fff07800cb3bc4ae55fec14e2722175f84ff81bcb` |
| `Toy.LayoutDfa.existsCheck_iff_meets_needs_reachableLive_uninhabited` | `propext` | `e48a42f39108a901c10308711501fd3158d15e1cf809f4bf74fff3d91db2b41d` | `d1fc6c2efade94d089376d461ed0e52ad5127996b6334622b1c20007c33bc014` |
| `Toy.LayoutDfa.extension_iff_nonvacuous` | `Quot.sound`, `propext` | `c5d02eb61a308a68bc423e0291b163aa74c555092863ac464a73824d70a2f250` | `20a19ca2f790442e9a7389b5b194e6bf6f9fd8895b42e01d4f2d75284c4c1c4f` |
| `Toy.LayoutDfa.extension_iff_nonvacuous_fullWidth` | `Quot.sound`, `propext` | `78c59cd0c30f1eb4deaf845ab5dd499660bdea48a52a7466537327b9c1569c2d` | `46a905d78d6fb12b917400f68728a422ac090c43ccbfd88da4de4d1094cfce07` |
| `Toy.LayoutDfa.extension_iff_needs_fixedSize_src` | `Quot.sound`, `propext` | `a4ab2b71d3d39438727e63dc0b179050653691332a2718ef2241d1cfaac047b0` | `c6fcad27ba568c03e51f706bfe9097e72c49bd8b8c0a9d41d24462ba4a5fca74` |
| `Toy.LayoutDfa.extension_iff_needs_fixedSize_dst` | `Quot.sound`, `propext` | `bb834d40679f123097a751b609c4e7bdbb16284590c2f38b329634ed309d2536` | `9ca3ad63b50537728f5262d367a8d51d1a62b0a850e7c020a22097aaf9dbe3d4` |
| `Toy.LayoutDfa.extension_iff_needs_le` | `Quot.sound`, `propext` | `9459d7df800ad03294c3e3051296810bc0289df0f98a4ae4ec595c71fd363876` | `a9619c99293d247f0364ba7f59afe620da258d6e045b721325a5302a7757df4f` |
| `Toy.LayoutDfa.extension_iff_needs_deterministic` | `Quot.sound`, `propext` | `5e373f61336c96fbb73df6582a0eff8c029b897bff80ca97d34295437df05313` | `21a04b373904379638e79211d2b595e88a95ec6eb67b5eb1b5dd8aed1370a4ce` |
| `Toy.LayoutDfa.extension_iff_needs_reachableLive` | `Quot.sound`, `propext` | `56849583a7eb7da8036ccd4be1ac7eb5fea5044bc8f24e89168bbc00cc3d0e71` | `bffbb1e782f014b386b9c051514bc538c88c9ba49bb5ffb0c80edf5a36b9b5cd` |
| `Toy.LayoutDfa.sharedShared_sound_iff_nonvacuous` | `Quot.sound`, `propext` | `18b45f91182c3e547c040b47ff73653c8ce453f024ae3464a95942227871bcf1` | `5d59a09a6c7b21c5b9940f08d0195d85c7a67688cbf68fb46de03695acf976df` |
| `Toy.LayoutDfa.sharedShared_sound_iff_needs_satisfiable` | none | `c97196848985c3adb1d6a0615fcd3a2633846f5c3b323e524e75ae37909e9241` | `3f8f6f2458c76f8f1cf74ad0bde3ee70a10e5b32a5d5e40dc64f0644010e6be4` |
| `Toy.LayoutDfa.mutShared_sound_iff_nonvacuous` | `Quot.sound`, `propext` | `df452924354c009b75f20ce928e839857e380a58fb132cf159648ddaa76f046b` | `5d59a09a6c7b21c5b9940f08d0195d85c7a67688cbf68fb46de03695acf976df` |
| `Toy.LayoutDfa.mutShared_sound_iff_needs_satisfiable` | `Quot.sound`, `propext` | `14ac42ebb2586c80651650c77f63e5fae761de98e79e01c946aaecedb58aed37` | `3f8f6f2458c76f8f1cf74ad0bde3ee70a10e5b32a5d5e40dc64f0644010e6be4` |
| `Toy.LayoutDfa.mutMut_sound_iff_nonvacuous` | `Quot.sound`, `propext` | `24d1c7f1cc21ff945aa9645ff452bd87e5bfb2c8488328e568680357859b36da` | `2f3457fcc365cdd492ca50f7c9f5b3962e0a813e1e07d69b7d47417ca81c0f9f` |
| `Toy.LayoutDfa.mutMut_sound_iff_needs_satisfiable` | `Quot.sound`, `propext` | `12821fae803719e896549e8473b2c5e2a6d99b5ee179f007f85d695cf0619abe` | `932394fcf605a789ebd32c6ec5989da3954778b3efc6df1655462372234ed75e` |
| `Toy.LayoutDfa.sharedMut_not_sound_nonvacuous` | `Quot.sound`, `propext` | `82e4734dd994c0ef9afc9451b7e1a87f9b4317d9ded18f45f1d9554143a6e799` | `bc14ff129a2fc605251cd06a36c521d477baa22920d041a888b6a8eb9e4b73a8` |
| `Toy.LayoutDfa.sharedMut_positive_control` | `propext` | `91b0e6f5f8cb07912b5e41ddebfd490bacf14bdb774e73407a87b0a076032fae` | `f6b8d3c3e0980c906547e0c1c99358b344320f03d971770c60989cda5a4e2623` |
| `Toy.LayoutDfa.sharedMut_not_sound_needs_satisfiable` | none | `3a3011832f55a0935097245977a30d426e0269180a362020a0702da7f7b6236c` | `b1525d8784278ee9cbb0a04d9d57a64ed54a0eeb13a75c8f1142acf2919f25cf` |
| `Toy.LayoutDfa.sound_of_matrixOK_nonvacuous` | `Quot.sound`, `propext` | `18c11ad0de9b85b5513894867b8967afc32bf00294a380798c4e8ff9e1bd0c17` | `e2355d0c5d7da24fef8169e9227acc5ac5fc8b7b32a1d46a513e8380e58aa5cd` |
| `Toy.LayoutDfa.matrixOK_iff_sound_nonvacuous` | `Quot.sound`, `propext` | `e7a23b03d2f2c40c899f2ce616cde1823e62cbc21cd793ddb0b4f40e086e998d` | `9f76eea6671c6c5223997ec00b38860d31a8c00f346e59a7bc753ef1ed1319f1` |
| `Toy.LayoutDfa.matrixOK_iff_sound_needs_satisfiable` | none | `f2a1f391c6f3ca1450599e8a59582b6267433e27da3377a1fde2a1986273f39f` | `89492379fa87c084420d8443e868741535a6e52e608c5a7ba9b7c9084ec6b545` |
| `Toy.LayoutDfa.matrixOK_iff_sound_needs_sharedDst_freeze` | `Quot.sound`, `propext` | `f81716a810f8d938a2243cd31b14fc4245e2499d1d38608d54bf356bf1e80185` | `6a8d4b6eb4f9db3c9e869e6eaa378a64486a50e097c10edaef0656f673b601ff` |
| `Toy.LayoutDfa.sound_shared_shared_byte_byte` | none | `d65d7d82e7f25b4b8c873a3800290262f026d3e78a899629d684cdf8affa7c6c` | `f6b8d3c3e0980c906547e0c1c99358b344320f03d971770c60989cda5a4e2623` |
| `Toy.LayoutDfa.refCheck_sound_nonvacuous` | `propext` | `fbdad59d0fca71ed9ff47b934ca0ad4936b677aa3b9631757f6dad44a7303668` | `1d0a82484298a831427866e29dfbbd06c728aa3595ab7888e9522b7cffe053a5` |
| `Toy.LayoutDfa.refCheck_sound_needs_fixedSize_src` | `Quot.sound`, `propext` | `0391ea897b03ec60b34cf6a57d992d9da4fe930e58c67c7b965da1377a97ccf8` | `1232fe3c3ee99bb0dc74df96abe42f8430335b10c6f2ae79208bb49a8f7a83e5` |
| `Toy.LayoutDfa.refCheck_sound_needs_fixedSize_dst` | `Quot.sound`, `propext` | `fee256f2d811488699454b69dc5d7d70616084a7b4000283046d7a970cd40180` | `195912897f374c5c1b01492519f2dc67bb9c94365413b1fbb8a0b87d67ed4e7e` |

### Definitions and auxiliary declarations cited by name (`lean_names`)

| Name | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- |
| `Toy.LayoutDfa.FitMeets` | none | `b516fc54cffffb16d98bfd956bfce6b3a66065a7f40ba5df2ebf8aa7a5195e8d` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.FitSubset` | none | `b516fc54cffffb16d98bfd956bfce6b3a66065a7f40ba5df2ebf8aa7a5195e8d` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.FrozenDuring` | none | `63928db40fa99c4c5fa8c929ed07addc5db6077ad87dff4d44e2185f16c2a57e` | `da08814ee5e156a06f2465aa855c6578c11707be0967e4737c478e426edb1f2b` |
| `Toy.LayoutDfa.Includes` | none | `2efefa82f7f6c1f2423ee9205319495efecb0e9877a842f6d5dae0a089b5107d` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.Layout` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.Layout.Accepts` | none | `8992a8c8e95d43dabb11ccb1a4dc8039f8ac81e07bdf707bdab1a58063e75a1f` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.Acyclic` | none | `4d9f29638b65530ddb86275a5391411739074db63f953e16584dd456b6b1d61e` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.Deterministic` | none | `4d9f29638b65530ddb86275a5391411739074db63f953e16584dd456b6b1d61e` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.FixedSize` | none | `61de30e58049e7d30f7a9d4e64b027a4bac91a0632bc0a2f193234b616bba4b1` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.Lang` | none | `b86b298f544da7150ebac7d2309fd085acbd0fdaaee266eaf5b4434525bf5d2a` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.Path` | none | `787959b0a1ccbd1212c7e4963655b0e7223a76af200b29047365be615bf9839d` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.ReachableDeterministic` | none | `4d9f29638b65530ddb86275a5391411739074db63f953e16584dd456b6b1d61e` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.ReachableLive` | none | `4d9f29638b65530ddb86275a5391411739074db63f953e16584dd456b6b1d61e` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.ReachableLiveAcyclic` | none | `4d9f29638b65530ddb86275a5391411739074db63f953e16584dd456b6b1d61e` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.inhabited_of_reachableLive` | none | `90df64d272a86df93b19c48dcffcdc200eebe8069134081e59c404893790c6bd` | `813de25b7f5cfc6cb9eb24f33a28f0bd6ce03ad11e528c8a86e0120e068d159c` |
| `Toy.LayoutDfa.Layout.out` | none | `b392387fb90dca6010d5b618006a162056f25055f3a0e8b54020ab22c6fbadac` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Layout.reachableDeterministic_of_deterministic` | none | `2d0e5e8b1a799cf88c084601f591d946f5aadc01a583e278989e24daf9d3ce44` | `738fc8be40dcc268e45f8f4fcec42a95d4a2dec56d356b1ec0bf72ae3f971083` |
| `Toy.LayoutDfa.MatrixOK` | none | `97e9148de9df75c4eb7a02c166ad76d435b8cf70fa30148b3685a5f0a3b5004d` | `da08814ee5e156a06f2465aa855c6578c11707be0967e4737c478e426edb1f2b` |
| `Toy.LayoutDfa.MatrixOKNoSrcFreeze` | none | `97e9148de9df75c4eb7a02c166ad76d435b8cf70fa30148b3685a5f0a3b5004d` | `da08814ee5e156a06f2465aa855c6578c11707be0967e4737c478e426edb1f2b` |
| `Toy.LayoutDfa.Meets` | none | `430f7bac12ea6d817f6cdc81b7138bbc6c316bf08a53c4b19efdfff4a10e6345` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Mode` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.Op` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.Op.next` | none | `2b8da31cf2b27297460e58f7409ccc4387047b88d05b15a209441fb269342b3d` | `77212fa501e8f97a116ec3d98c492b68d11b452143d916af700314ba2ec62f9f` |
| `Toy.LayoutDfa.OpOK` | none | `7a516692f3cd04589b08c4816bdca4a177414ccb979874c7d079e84979f40696` | `e2ffa7a50141ed39624656d13ffb5bccf33c746e7fe20d7bf3da5a281b69c71b` |
| `Toy.LayoutDfa.Permitted` | none | `73e6a5f4663991e52d9408a433cd4b13c8b6e14d3851cc510eb2d7bff3ca6784` | `e2ffa7a50141ed39624656d13ffb5bccf33c746e7fe20d7bf3da5a281b69c71b` |
| `Toy.LayoutDfa.RefTy` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.RefTy.ofLayout` | none | `20d5e4c9fab1f484789c86913942f1341d8f83286c5a3ace8e8ed09ca0d62ba3` | `b3ad95bcdf716b58828bfdac68d6f34db1df35f35f6e14bb94f61e41901f82d4` |
| `Toy.LayoutDfa.RunOK` | none | `b6c0a1f147b0397667d159e8b18562a2c7e1ed732962336d5c1b18c53e0a4eac` | `e2ffa7a50141ed39624656d13ffb5bccf33c746e7fe20d7bf3da5a281b69c71b` |
| `Toy.LayoutDfa.Satisfiable` | none | `2c5817d61e36c7f9d292afca8479d9188db7a40148467483fc448628593a6e22` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.Sound` | none | `63928db40fa99c4c5fa8c929ed07addc5db6077ad87dff4d44e2185f16c2a57e` | `da08814ee5e156a06f2465aa855c6578c11707be0967e4737c478e426edb1f2b` |
| `Toy.LayoutDfa.SoundOneStep` | none | `63928db40fa99c4c5fa8c929ed07addc5db6077ad87dff4d44e2185f16c2a57e` | `da08814ee5e156a06f2465aa855c6578c11707be0967e4737c478e426edb1f2b` |
| `Toy.LayoutDfa.Subset` | none | `430f7bac12ea6d817f6cdc81b7138bbc6c316bf08a53c4b19efdfff4a10e6345` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.Sym` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.View` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Toy.LayoutDfa.acceptNDL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.allSyms` | none | `64e5b173cff383403a63e4227efcb1fd82904fcd03691def8196672d693dfbfe` | `ea1b7b2a78860365d9074c0d2931fb7737ed62c6453d7ae1b938f6cd15d550c7` |
| `Toy.LayoutDfa.anyEdges` | none | `e1602562fb87f35961d0ad18dd82986f7f797861c746517b31cb823e48e90c91` | `ea1b7b2a78860365d9074c0d2931fb7737ed62c6453d7ae1b938f6cd15d550c7` |
| `Toy.LayoutDfa.b0L` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.b0uL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.b1L` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.bool2L` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.boolL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.boolRef` | `propext` | `c8497768e30db45609f7c9d71e70d94d4abca3f1b49f2140cf3ffa24c7d5ca7a` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.boolUL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.byteEdges` | none | `e1602562fb87f35961d0ad18dd82986f7f797861c746517b31cb823e48e90c91` | `ea1b7b2a78860365d9074c0d2931fb7737ed62c6453d7ae1b938f6cd15d550c7` |
| `Toy.LayoutDfa.byteRef` | none | `c8497768e30db45609f7c9d71e70d94d4abca3f1b49f2140cf3ffa24c7d5ca7a` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.cellBoolRef` | `propext` | `c8497768e30db45609f7c9d71e70d94d4abca3f1b49f2140cf3ffa24c7d5ca7a` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.cellByteRef` | none | `c8497768e30db45609f7c9d71e70d94d4abca3f1b49f2140cf3ffa24c7d5ca7a` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.chainL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.checks_depend_on_edge_list_representation` | `propext` | `5e08634b3e9cca7a35c9b905e961786eef2687352cd3cd622e1f5cf1a223a628` | `ab9609a2426b12aec85b72c12108c5e718854e942f70f41fce9e645b0473a334` |
| `Toy.LayoutDfa.cycDupL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.cycL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.deadCycReachL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.deadL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.ex_acyclic` | `Quot.sound`, `propext` | `60e49d32462ccd02c2685a22b31e7e9cc39703f2466b1eeffdba7f8c9fc21952` | `d5d48e1b1a3c88734c1b5b43f883e29dad6959db515377cb7d07a58b581d19fb` |
| `Toy.LayoutDfa.ex_deterministic` | `propext` | `e0971e594c2916e4cd8a626ae60056215dc6645da24a426ae7ed9a8d0d20c16d` | `3eafa0507b95a827279fe747da842403b5cbb854a598ce40f751ddad65289a97` |
| `Toy.LayoutDfa.ex_existsCheck` | `propext` | `5eab9386d89b974417c41d34959e38e193bde75efa06e2423baf27a2b3a4994a` | `45945d2d56301b2c84e5d4ccc97be7383247347b679791e863a8680dce0d11a7` |
| `Toy.LayoutDfa.ex_fit` | `propext` | `5170007cfc89108f46e0dfcd13005b21bfbc49b92850f356650926c0427f315f` | `ce78670d42c6995099b8f27d9804132d522acff8ddf7d7a7f845a1a4d76ad04f` |
| `Toy.LayoutDfa.ex_fitMeets` | `Quot.sound`, `propext` | `7a297cbce8c5157b816ce5ccd41fa5d4caaea76f13f1f6d73d33cddba778055a` | `c1f79edce6075ee337bb1d187ff2d637bfd35dca9483336c7b9e0fee8beb8607` |
| `Toy.LayoutDfa.ex_fitSubset` | `Quot.sound`, `propext` | `3da60d8b55e2be55b59576768f5e5de6a0928d334c70caf45fab8612e5c4ea53` | `7a6c22e9ce19c8761b95d3158f1c541c3ca01f13bf257b510fdbdccc719569d9` |
| `Toy.LayoutDfa.ex_fixedSize` | `propext` | `07433cb03eb695885eb859f44ae00bbcaf7009998020fac9ea40ee980eb91112` | `3f8fafa4793b20539020426763797dc5fc6dd81d52d8d8be9c80d36505adf01f` |
| `Toy.LayoutDfa.ex_forallCheck` | `propext` | `686a848eea82a9558c4e066474266f7b23c3e4cb812e99cab0f0de68cef62328` | `eee0ce133241e694ad43582e67012a1b8c85d061ef77166f541e143d2ffed4e7` |
| `Toy.LayoutDfa.ex_frozenDuring` | `propext` | `2f4e0757687f90764ad0089119478efaab7177ce9776fde57d318cc05896cca3` | `df1de81b53113be71d14f4cc979e5cf2cbc996088f86d2f18248b8f42c1c3429` |
| `Toy.LayoutDfa.ex_includes` | `Quot.sound`, `propext` | `3106c1d88895fe9ce9ae9a52bbe291667d144359d8674d7d30de46f6071465b8` | `e7b4c6f8f0f3fd3417f35d28c3622d6b931cbf6fb93ea726204aebdec7d643c0` |
| `Toy.LayoutDfa.ex_lang_accept_terminal` | `Quot.sound`, `propext` | `6b8261b85a4bf9930c6cb26b1acab74df3fc59cc4869e0a0fc062f8f19b200cc` | `39baf6ba792f920614b146bdd53b0579e988cabe7c12a1e22a3d15bacece56cc` |
| `Toy.LayoutDfa.ex_lang_bool` | `Quot.sound`, `propext` | `9202b2f4e995670e08b8690bf934a66c21724d2c86d93e84e0fcb169ea7ac354` | `dc824d6a74588309323373e279bdd22429b4aa804910a3a999918dc762414ae5` |
| `Toy.LayoutDfa.ex_lang_u8` | `Quot.sound`, `propext` | `df3f8495e21888510a6dd752851e3a50158fa8d207f11a3aebe83c11b66e1323` | `35f33264bda37313b2e9f155bc43a498c08bde435d4fa5760b20dc899c9601c8` |
| `Toy.LayoutDfa.ex_lang_unit` | `Quot.sound`, `propext` | `94203f644b723343ddb7504f9945f02d4c91be566a282096236e5cd54664c4eb` | `3c44900a4c799895edc4c5360e3a25108a31a27cb4d44f076ef7642e037b4f35` |
| `Toy.LayoutDfa.ex_matrixOK` | `Quot.sound`, `propext` | `83d913ec7bbe8369bf062391856a225c684b6231103a519131c0c7dc73f63ab2` | `577623ab776fa4512a5c9e33c4b7603cce6732ac9deb119603358b2b1c7b56b4` |
| `Toy.LayoutDfa.ex_matrixOKNoSrcFreeze` | none | `91093cdeee38f8ff7d9e2d7edd5ce095834e4106e7b6ccadba53a4ca89ea425a` | `55dc5d86b0a8a897e57434482f5f4ebda31ae929da935c968e97aaaf647b2267` |
| `Toy.LayoutDfa.ex_meets` | `Quot.sound`, `propext` | `fa43916c5e7e3dc5a02ea3f6a3aa488e4c375d6c9bf15d95bbeed9fd0285e95a` | `87f8cdb20946339eab960427f6b68532e998274aa0f924ee6d41c72690afb9fa` |
| `Toy.LayoutDfa.ex_not_deterministic` | `propext` | `773018204e75f6c86447edfb9489813f75ee98f9ef192f1fa0fa80581af0bc37` | `1bb595d03c9522029c552ce65e3298e7551906067f776948fb40bdd7c7eb2aa9` |
| `Toy.LayoutDfa.ex_not_existsCheck` | `propext` | `2606d4fd7cd19986f96a2677e4d1d772b535eb96dad9e9e7df426ea8693c6eed` | `f987024949cdc15813998f5d3a2b39b9c0df8bc12a4a9f0d28944435e7af08f9` |
| `Toy.LayoutDfa.ex_not_fitMeets` | `Quot.sound`, `propext` | `eaf813dc250b18c31a6502d11daa80a09830fb6b44d4ec8b798c6cecaeffcc97` | `8db3b2090ba0d335ef3869e520c2d901c0706a1e06402f065edd88f06adc776c` |
| `Toy.LayoutDfa.ex_not_fitSubset` | `Quot.sound`, `propext` | `899ccb791bb2ba1f8c572e09a83d609fe5cdb36169e37d51836d4ca13b374415` | `e0bd6387d60c32ac30cfd638f18f4077ed0a547cd2f6f3aa44a0ce0910b3adfb` |
| `Toy.LayoutDfa.ex_not_fixedSize` | `Quot.sound`, `propext` | `5ea239ff69e362d8c8ec75eab11b8fd1ffd5d51bebdcbaa4b600a357673d847d` | `97844c6e98f70d6cd71f16723c48a61dc963a05a420823c071aebd6852ef6168` |
| `Toy.LayoutDfa.ex_not_forallCheck` | `propext` | `8aca4823796bb1863c7e307b17208142d537bec1859b32c5e3ab0b671772faea` | `c35b38910504d1db040e2a02ca79eeea10d3ea211895f8eca828ad563819374d` |
| `Toy.LayoutDfa.ex_not_meets` | `Quot.sound`, `propext` | `de9421a3f916061c1e7397a57759bee314f7c5ba95e3f24ef7994dd619703a66` | `10424b8f4a2538ebf5fc7aafa50f0cb9bd827704a95f8037b494e84f24ca0e7f` |
| `Toy.LayoutDfa.ex_not_reachableLive` | `Quot.sound`, `propext` | `c5d53fecd17976307860f19601aae650f92cf1128bc636e210caaaedbe535353` | `52f38dee1edf1a4a4e431f8a863decd4048223501f40422ccfa22541c0615065` |
| `Toy.LayoutDfa.ex_not_reachableLive_uninhabited` | `propext` | `58533524574ed86ba1ebb38083866edb32cd6d49ef91c271184d36d6ba81c876` | `eae8209fbef9305068b5b9b4cfb846514b9308b4c0f6161ca751e0ed056637e0` |
| `Toy.LayoutDfa.ex_not_sound` | `Quot.sound`, `propext` | `1a499f80f49f7049b8c8f1d1dc7c1b9252824018915efcc6973ae9c4b3de0123` | `3ba63a17a060eb4b33714beb328f4ce82cb71ed5e8a96d6c08eed1b8b447c2fd` |
| `Toy.LayoutDfa.ex_not_subset` | `Quot.sound`, `propext` | `77bfa695bc3c2f61703d69dba8e10f838abbdfc4c2d78683e6c4b57e3dd96257` | `55e9b89cb1491ad978f8841a2cfce298a52d97440f84192ec96e42b4981ff925` |
| `Toy.LayoutDfa.ex_opOK` | `Quot.sound`, `propext` | `d86ff8f7b39f1ba527d04433880275c5fdd39d20a358bdaa82d8f97f53ca5f70` | `8fffc5b5372a533f77a42ab4f90210914a71289b9e3b1a786ff9a793fc6f5a54` |
| `Toy.LayoutDfa.ex_permitted` | `Quot.sound`, `propext` | `7e31a8dc4e4373a4bd6f6257b2d33858dc87d35367a01332e44f7ab4ddcb3962` | `39665647ed1860101710d73498c0cb485a90a085b09a671799cdbc43a5d30e0a` |
| `Toy.LayoutDfa.ex_reachableDeterministic` | `Quot.sound`, `propext` | `eed73eedfe91c588776d0ebed2c160bd7aab14249b030f442c77b086a4179f84` | `12c78d3f074e8519e8683f8d02428a988217413ed79d709d0c982932a058ccbc` |
| `Toy.LayoutDfa.ex_reachableLive` | `Quot.sound`, `propext` | `6606eba9f43347ee126548530c803466b26a40dafc78c4df9a9f41d2136605cb` | `d0817316229da6eb670e011527616f436954d1912e54ff2fc5cfec79fba23389` |
| `Toy.LayoutDfa.ex_reachableLiveAcyclic` | `Quot.sound`, `propext` | `c16d42e624b9ae93579a018f252d18b7bf09689ca41de2f04424a0fe13f72f7b` | `e07083354c85d38a641afef83b24183a0cd9c649aab8ce1295e11ca602afefce` |
| `Toy.LayoutDfa.ex_refCheck` | `propext` | `5f7997df50ca8541f560cf26071c898ae1723d5362e6c84da7833ff24554128d` | `b72496758fb02e7d1c98b2c2c650ef9f39fc22f20242f8674ac1588f7aa0a18f` |
| `Toy.LayoutDfa.ex_runOK` | `Quot.sound`, `propext` | `529c75833a72367d5dbae9d1e1402427facb2db13dcc14d9f6dd6d1553fbf9a1` | `9e02400a306c7c9d135db1b6deead282f4118264b66e51e403646b804455390c` |
| `Toy.LayoutDfa.ex_satisfiable` | `Quot.sound`, `propext` | `b9ac96d4975adf1632fe8784b2b2adf058413c3f51c3d264cd02d1ed96b0ecdb` | `f5cfeef1fca9c741955a08fb06c1df1f1894ecf8c8f4e914010aa82c92a9f21d` |
| `Toy.LayoutDfa.ex_sound` | `Quot.sound`, `propext` | `b7cef1112afc922eb3e3782d3684b40341503ce5779ec5b70e1e75c7c507568f` | `3ba63a17a060eb4b33714beb328f4ce82cb71ed5e8a96d6c08eed1b8b447c2fd` |
| `Toy.LayoutDfa.ex_subset` | `Quot.sound`, `propext` | `91f9fa0b6251fbf888c13e3ebdbe11cdc99bba8ab8074d315f68d598824ebd93` | `55e9b89cb1491ad978f8841a2cfce298a52d97440f84192ec96e42b4981ff925` |
| `Toy.LayoutDfa.existsAux` | none | `77d83c96be3d1d515c1e6a8bd56dee5fbbc6449c5187facdc9c3cc99908be6cc` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.existsAux_start_of_lang_fit_of_lt_fuel` | `Quot.sound`, `propext` | `30f5caebcb34b640bdb466eaca3d4917c2857bba1d111b0a4ef38d073b14f892` | `c5f5c95f1775710dedb657379ec8729600a944c32cbe90c0f56d08be6f830e36` |
| `Toy.LayoutDfa.existsCheck` | none | `f1a4d04ca45404b8e9dac0ee90410fb9353a4f4a579adf9021cfcf4c8bcc0abe` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.existsCheck_eq_false_imp_no_promise_of_acyclic` | `Classical.choice`, `Quot.sound`, `propext` | `b2a92feeff0d68d0e144fbddce041327de6e9e4fd5014eaaedf46d91fb907943` | `821e734c1b61b66c684afdf1a77d3bc8134e785f7926c79735bba558d6ca323b` |
| `Toy.LayoutDfa.fit` | none | `1218c6e67a70b7234b611cded78140738d06206ee6e17a774432ac4b1c66803c` | `ea1b7b2a78860365d9074c0d2931fb7737ed62c6453d7ae1b938f6cd15d550c7` |
| `Toy.LayoutDfa.fixedSize_acyclic_incomparable` | `Quot.sound`, `propext` | `9065c5b0bbf7daec082b09e0a1431f3bc5b0167217b7483822d7e0c1e0be393a` | `c7af0d8ab66ed6dd77f4cef8bb61112fcef1c625216690dd55c1705a6bb7e391` |
| `Toy.LayoutDfa.forallAux` | none | `77d83c96be3d1d515c1e6a8bd56dee5fbbc6449c5187facdc9c3cc99908be6cc` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.forallAux_complete_fit_of_lt_fuel` | `Quot.sound`, `propext` | `251c951ee407add66610b53d24e8a4edcee7b9794238a99f1454fd6c8e9236c2` | `075e84a2e990d26d6fa4aa37cc834b305b0088d6f39d4aa2ce45c93bec71bc69` |
| `Toy.LayoutDfa.forallCheck` | none | `f1a4d04ca45404b8e9dac0ee90410fb9353a4f4a579adf9021cfcf4c8bcc0abe` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.forallCheck_complete_fit_of_acyclic_det_live` | `Classical.choice`, `Quot.sound`, `propext` | `d3281283f5a58b494e54153504114b6aeec971530adbb5ade1738e94cc6a0384` | `345ee179132d4221dd41c98c9bbac826688ab18cb038b08dfd7d364a832ba16b` |
| `Toy.LayoutDfa.fuelFor` | none | `609d480f582895b3f795ee5532abdae7da79fded368bbe4b56606b4760932fca` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.length_le_edges_of_reachableLiveAcyclic` | `Classical.choice`, `Quot.sound`, `propext` | `f8e4e6744b7705ae5bb1b71d0e6a3709f61d0eab8e35a927e3439c213eb742d8` | `e2870006e40be924d7cf2646479251fa47d3d16831df0ef752acd8e10d1f1554` |
| `Toy.LayoutDfa.mu8L` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.ndDstL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.ndSrcL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.ndSrcL_ndDstL_lang` | `Quot.sound`, `propext` | `99b4fa9ae16f10d9e708baaab64cb470cdc164aa4ab489aa32b452c9fa1d9f53` | `36d95a8301b1ac9558c3281b05d90b05c19a20ade2e277a57f1d8ef48a4a433b` |
| `Toy.LayoutDfa.neverL` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.neverRef` | none | `c8497768e30db45609f7c9d71e70d94d4abca3f1b49f2140cf3ffa24c7d5ca7a` | `624de93f2377f5366bd79de29ca99cd0269aceab68e61e705c6d09c76ae7ad7b` |
| `Toy.LayoutDfa.pairSrcL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.reachableLiveAcyclic_of_acyclic` | none | `90ad970d49ca1f9b700765cb426cfeb30a976d3cf96c4a3fdf18b576bcfac067` | `a697b04f5527410e0e2a648d1e04d36dddb53b0bac6d029588dc5ef908245bed` |
| `Toy.LayoutDfa.reachableLiveAcyclic_of_fixedSize` | `Quot.sound`, `propext` | `0e0def0e2958342f0b3035c31f58961d824650842c2bfe0755f9913be800763c` | `81d63fbb5e1912afc38446048a58f434bf1ec81af95bf2ec78d718fc8228c815` |
| `Toy.LayoutDfa.reachableLiveAcyclic_strictly_weaker_than_both` | `Quot.sound`, `propext` | `53d3586499e6a620b4462909de419efab0b10651f4e467603f5221c9070e1ed0` | `4bba3cc00252397edc7bcf298db64c154f775dc58bdbd23f21fbefdfbd9be00b` |
| `Toy.LayoutDfa.refCheck` | none | `ce37101e9a4958aa2dca2578d8ea207cf79d7afea759c65e35489679c5e58fd0` | `9def0d20d75f02d1b598872c2ff9965aa2b5e88f1fefedb4ce8755ade1c78ca0` |
| `Toy.LayoutDfa.refCheck_mutMut_needs_eq_fixedSize` | `Quot.sound`, `propext` | `dee9a34b9c113c704dc9b15a3d3d2910026bbb1fdd5b62ea22b519504b363a31` | `1232fe3c3ee99bb0dc74df96abe42f8430335b10c6f2ae79208bb49a8f7a83e5` |
| `Toy.LayoutDfa.sound_iff_soundOneStep` | `Quot.sound`, `propext` | `4ece4c1c15d3b62dc2bb3e10699bd7a044a460bf15e8d9b4b38a1fc53c0ad7bb` | `94897892330bf502bab77269a81ee3bdc48ad399ef0020db09da4ed99a0e74b5` |
| `Toy.LayoutDfa.sound_mut_shared_cell_cell` | `propext` | `26a4b270c2f81d28d32d0d63edc858cbbba7c95f0b7a0cacf59f49225110630b` | `8d4536939beac5f30ac24e031ee623cfe1e2469ea45b4226edece810e7b439a4` |
| `Toy.LayoutDfa.sound_shared_shared_cell_cell` | `propext` | `f8d88489ce8901c2fb6e1ddcf60dc1e559d11989e8683bd6cbc9ab5183f1279a` | `8d4536939beac5f30ac24e031ee623cfe1e2469ea45b4226edece810e7b439a4` |
| `Toy.LayoutDfa.subset_of_forallCheck_of_eq_fixedSize` | `Quot.sound`, `propext` | `d9b48e9b59e6e125f5ebe2006f552991a0a557fbf2ef1244664d248c9e75f068` | `494e15d50862869af8eb0db06bd0d5fe99cfd5771459e719b76fef490f9f508d` |
| `Toy.LayoutDfa.u16L` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.u8L` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.u8PadL` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.uL` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.unitL` | none | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.varDstL` | `propext` | `1da99cad707a5f026883f541a26323a71f7a2099f127b2f82185a43dbb659761` | `711fd24633bdd19e7eb4534d641b76560cd18ee5fbb254733d0bae5085f13d45` |
| `Toy.LayoutDfa.viewTy` | none | `a958ff683dd8cb3f17399a2f0f634586110cae530dc549da05967bc89d39ff9e` | `f8013e4634b717401a18c8bb34e9b45f6971a5c4eb4ab275e0c91a432f49dc22` |

### Primary sources

External sources, read at the pinned revisions (evidence roles as stated in each entry). They support the `derived (modeling bridge)` lines and prior-art entries, not the theorems.

- rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs`: lines 187-210 (truncation when the destination is at its accept state; extension through the destination's uninit edge when the source is at its accept state), lines 212-222 (the two quantifier comments), lines 377-412 (`enum Quantifier` and `Quantifier::apply`) (source and source comments; documentation role).
- rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` lines 116-123: when the source layout is uninhabited the query answers yes before any automaton exploration (source comment: "conclude that the transmutation is acceptable, because instances of the `src` type do not exist", lines 118-119). The toy's checks have no such rule; the `ReachableLive` hypothesis excludes uninhabited sources instead.
- rustc at commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `compiler/rustc_transmute/src/layout/mod.rs` lines 14-54 (`Byte` is a range over 0..=256 with 256 the uninit value; `Byte::uninit()` covers every value, lines 40-43) and `compiler/rustc_transmute/src/layout/dfa.rs` lines 10-18 (`Dfa` with one `start` and one `accept` state), lines 199-201 (out-edges of the accept state do not affect the semantics), lines 252-255 (`get_uninit_edge_dst`) (source and source comments).
- `core::mem::TransmuteFrom` / `core::mem::Assume` (unstable feature `transmutability`), rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/mem/transmutability.rs` lines 41-44 (union-transmutes extend `Src` with trailing padding to fill trailing uninitialized bytes of `Self`), lines 110-111 (with `ASSUME.validity` the caller must guarantee that `src` is a bit-valid instance of `Self`), line 85 (`#[unstable(feature = "transmutability", issue = "99571")]`) (documentation).
- `core::marker::Freeze`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/marker.rs` lines 890-918: the unstable auto trait `Freeze` (lines 890-891: "Used to determine whether a type contains any `UnsafeCell` internally, but not through an indirection."), with `impl<T: PointeeSized> !Freeze for UnsafeCell<T>` at line 909 (source).
- `core::cell::Cell`, rust-lang/rust commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, `library/core/src/cell.rs` lines 277-279 (`Cell<T>` has the same in-memory representation as `T`), lines 636-655 (`Cell::from_mut`, a `&Cell<T>` from a `&mut T`), lines 719-739 (`Cell::as_slice_of_cells`, a `&[Cell<T>]` from a `&Cell<[T]>`), lines 741-759 (`Cell::as_array_of_cells`, a `&[Cell<T>; N]` from a `&Cell<[T; N]>`, stable since Rust 1.91.0) (documentation).
- RFC 2835 (Project Safe Transmute), rust-lang/rfcs commit `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/2835-project-safe-transmute.md` lines 9-10: a merged RFC forming a project group "with the purpose of designing subsequent RFCs around the topic of safe transmute between types" (context; not relied on).
- J. E. Hopcroft, R. Motwani, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation, 2nd ed., Addison-Wesley, 2001, Chapter 4: closure of regular languages under intersection by the product construction (Section 4.2.1, Theorem 4.8), decision properties (Section 4.3) and testing equivalence of automata (Section 4.4), all for total DFAs with non-terminal accept sets. Section numbers and contents are taken from secondary sources; the primary text was not accessed.
- M. O. Rabin, D. Scott, Finite automata and their decision problems, IBM Journal of Research and Development 3(2):114-125, 1959, DOI 10.1147/rd.32.0114 (bibliographic record checked; text not read): finite automata, nondeterministic automata, and decision problems for them.
- D. L. Dill, A. J. Hu, H. Wong-Toi, Checking for language inclusion using simulation preorders, in Computer Aided Verification (CAV '91), LNCS 575, Springer, 1992, pp. 255-265, DOI 10.1007/3-540-55179-4_25 (bibliographic record checked; text not read): simulation preorders as a sufficient, efficiently checkable condition for language inclusion.
- R. J. van Glabbeek, The linear time – branching time spectrum, CONCUR '90, LNCS 458, Springer, 1990, pp. 278-297, DOI 10.1007/BFb0039066 (bibliographic record checked; text not read): a classification of process semantics that separates trace (language) inclusion from simulation.
- M. De Wulf, L. Doyen, T. A. Henzinger, J.-F. Raskin, Antichains: a new algorithm for checking universality of finite automata, CAV 2006, LNCS 4144, Springer, 2006, pp. 17-30, DOI 10.1007/11817963_5 (bibliographic record checked; text not read): exact universality (and inclusion) checking for nondeterministic automata over sets of states without explicit determinisation.
- Mechanized automata theory, cited as context: C. Doczkal, J.-O. Kaiser, G. Smolka, A constructive theory of regular languages in Coq, CPP 2013, LNCS 8307, Springer, 2013, pp. 82-97, DOI 10.1007/978-3-319-03545-1_6 (DFAs, NFAs, closure properties and decidable equivalence; bibliographic record checked, text not read); Lean 4 Mathlib, leanprover-community/mathlib4 commit `a495318fed6482b3c90df686de5131b46a70fd5b`, `Mathlib/Computability/DFA.lean` lines 57-65 (`structure DFA` with a total transition function `step : σ → α → σ` and a set of accept states) and lines 318-338 (`DFA.inter`, `accepts_inter`) (source). Neither was found to formalize a check with this package's truncation and extension rules or step budget (search record under Evidence, Primary sources; not a proof of absence).
- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, RustBelt: securing the foundations of the Rust programming language, PACMPL 2 (POPL 2018), article 66, DOI 10.1145/3158154 (bibliographic record checked; text not read): machine-checked semantic soundness of a Rust subset including `Cell` and other interior-mutability libraries.
- R. Jung, H.-H. Dang, J. Kang, D. Dreyer, Stacked Borrows: an aliasing model for Rust, PACMPL 4 (POPL 2020), DOI 10.1145/3371109 (bibliographic record checked; text not read): an operational aliasing model for references.
- N. Villani, J. Hostert, D. Dreyer, R. Jung, Tree Borrows, PACMPL 9 (PLDI 2025), DOI 10.1145/3735592 (bibliographic record checked; text not read): a tree-structured aliasing model for Rust with per-location permissions.
- Published package `transmutation-soundness-bit-validity-and-reference-variance`: cards R2 (`sharedSound_iff_includes`), R3 (`mutSound_iff_includes_and_satisfiable_imp_includes_rev`), R4 (`sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev`) and R4-src (`sharedIMSound_noDstWrites_iff_includes`): the bit-validity conditions of reference casts over validity sets, which this package does not re-prove as standalone results (google/zerocopy branch `reference`, commit `4b379cbb55a9c944533423ec4d6f82cfd758728b`; cited, not re-proved).
- Published package `pointer-capability-modality-lattice-ir-attribute-lowering-and-sroa-monotonicity`: the `frozen` atom (no pointee byte written while the pointer is live) and the `unique` atom (no access through another pointer), and card R1-transformers-best (`kindBase_best`; `tCell` drops `frozen` for a shared reference to a non-`Freeze` pointee) (google/zerocopy branch `reference`, commit `4b379cbb55a9c944533423ec4d6f82cfd758728b`; cited, not re-proved).
- Published package `zerocopy-trait-semantics-over-layouts-and-derive-check-soundness`: card R7a-immutable-not-byte-determined (`immutable_not_byte_determined`: `UnsafeCell<u8>` and `u8` have the same byte semantics but differ in `Immutable`) (google/zerocopy branch `reference`, commit `4b379cbb55a9c944533423ec4d6f82cfd758728b`; cited, not re-proved).
- Published package `send-sync-auto-traits-thread-safety-typing-and-interior-mutability`: card cell-not-sync (`not_semSync_cell`: two holders of a shared reference to a `Cell` can both write its storage) (google/zerocopy branch `reference`, commit `4b379cbb55a9c944533423ec4d6f82cfd758728b`; cited, not re-proved).
- Published packages `byte-representation-galois-laws-and-transmute-composition` (card R5b-total-iff-validity-set-inclusion: value transmute total iff validity inclusion, including partially uninitialised byte vectors) and `byte-level-separation-logic-typed-points-to-and-transmute-view-changes` (card R3e-padding-view-change-is-one-directional): abstract bytes with an uninit value (google/zerocopy branch `reference`, commit `4b379cbb55a9c944533423ec4d6f82cfd758728b`; cited, not re-proved).
- rust-lang/rust issue 164247 (https://github.com/rust-lang/rust/issues/164247; open on 2026-11-21, labelled I-unsound; title "TransmuteFrom::<_, Assume::NOTHING> can transmute references to types with interior mutability"): a public report whose example transmutes a shared reference to a `Cell` into `&[u8; 4]` and then calls `cell.set(1)` while the byte reference is in use. Prose context; not a subject and not relied on.
- Novelty search (web search, 2026-11-21, queries on mechanized proofs of DFA-based transmutability checkers in Lean, Coq or Isabelle, and on mechanized automata libraries): no mechanization of the layout check's exact correctness (with truncation, extension and step budget) or of the reference `Freeze` matrix was found; mechanized automata libraries were found (prior art above). This is a search record, not a proof of absence.

## Revalidation

Requirements: `elan` (it installs the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No other tool and no network access beyond the toolchain download are needed.

Primary command, run from the package directory:

```text
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory and never modifies the package. It then (1) runs `lake build`; (2) checks that no Lean source contains `sorry`, `admit` or `native_decide` or declares an `axiom`; (3) computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and checks that no axiom other than `propext`, `Classical.choice` and `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` entries) recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (the sorted `name : type := value` texts of every package-local constant reachable from the statement, theorem bodies excluded) and compares them with `audit/statements.json`. Exit status 0 means all four checks passed. The script's docstring states exactly what is hashed.

Manual alternative (build and print the axioms of every theorem referenced by `results.json`):

```text
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is not part of the library target; it imports the library and runs `#print axioms` on every theorem referenced by `results.json`. Each line of its output must list no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

What revalidation does not cover: the `derived (modeling bridge)` lines and prior-art entries depend on the external sources at their pinned revisions. To check them against a newer subject, re-read the cited line ranges (for example `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` around the truncation, extension and quantifier code, `compiler/rustc_transmute/src/layout/{mod.rs, dfa.rs}`, `library/core/src/mem/transmutability.rs`, `library/core/src/marker.rs` around `Freeze`, and `library/core/src/cell.rs`) and compare them with the definitions quoted in Findings.
