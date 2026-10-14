# What a RustBelt-to-MiniRust spatial linking theorem must preserve

## Summary

RustBelt's lifetime logic and semantic-interface method are reusable proof components, but its λRust soundness theorem does not already establish safety for MiniRust bytes, bounded operations or Tree Borrows. A bridge must reflect every relevant concrete bad execution into a bad execution of the proved model, or prove a concrete invariant that rules that execution out. A map that merely forgets bytes, provenance and alias permissions cannot supply this property.

The inspected 2026 RefinedRust artifact already has byte fragments, bounded integers and explicit adequacy. It is a closer operational starting point than original λRust, but it also requires an operational relation to the selected MiniRust memory model. Our checked fragment proofs establish the direction of safety transfer and exhibit two failed erasures. Safe Rust experiments additionally show why a functional contract for a parser or shared view must retain the ownership and callback conditions needed by its spatial implementation.

## Applicability

The operational subjects are MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, the original LambdaRust `popl18` source archive identified by SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`, and the RefinedRust 2026 source artifact identified by SHA-256 `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`. Archive identity is used because an immutable upstream commit was not recovered from either archive in this investigation. Selected source files were inspected directly without running their native code.

Aeneas `ac9f1bc5262a5e4ff1e24ca78617121382202727` and Gillian-Rust `83d739e83034d71162fb66b569041cf301123df7` provide two comparison interfaces. The report reuses the existing exact-revision corpus for their broader pipelines and directly rechecks Aeneas configuration and Gillian's dual contract emitter. It does not compare every supported Rust feature.

The executed subject is our safe `support/safe_clients.rs`, compiled with rustc 1.99.0, full commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, host `aarch64-apple-darwin`. The mechanized subject is our `support/Bridge.lean`, checked by Lean 4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`. These owned models and client executions are separate from the upstream semantics. No RustBelt, RefinedRust, MiniRust or unsafe Rust program was executed.

## Findings

### 1. Five different things can be reused, with different obligations

The original source separates the underlying Iris logic, lifetime resources, semantic type predicates, semantic typing rules and library implementations. In `theories/typing/type.v:22–47`, a type supplies a size, ownership predicate over lists of λRust values and sharing predicate over a lifetime, thread and location. Sharing is persistent, with explicit sharing and lifetime-monotonicity obligations. `theories/typing/lib/cell.v:12–15` defines a `Cell` sharing predicate using a thread-indexed non-atomic borrow; `cell_get_type` and `cell_replace_type` prove operations against that interpretation. These are actual definitions and proof statements, not interchangeable names for permission to access bytes.

The original `theories/lang/lang.v` defines locations as block/offset pairs, integer literals in `Z`, and heaps of values plus lock state. Its `PlusOp` computes mathematical addition. Its `theories/typing/soundness.v:28–32` assumes semantic typing of the entry value for every required ghost-state instance and concludes that every finitely reachable thread pool is nonracing and each thread is a value or reducible. The source's closed variant is at lines 63–67. The λRust paper's fundamental theorem supplies semantic typing for its syntactic rules; unsafe libraries instead supply proofs of their semantic interfaces.

Consequently:

| Component | Reuse that the evidence supports | Additional MiniRust obligation |
| --- | --- | --- |
| Iris proof framework | Build a logic for another transition system | New state interpretation and adequacy instance |
| Lifetime resources | Reuse logical statements after matching their resource premises | Connect opening/closing to concrete retag/access/protector transitions |
| Semantic type design | Separate ownership from persistent sharing | Define byte validity, initialized ranges, provenance and alias authority |
| λRust typing lemmas | Reuse proofs in their original operational subject | Simulation or reproved rules for MiniRust |
| Library proof scripts | Port the invariant and proof structure | Prove the concrete implementation and every primitive under the new interpretation |

Basis: **source**, original archive files above; **derived**, explicit reuse obligations. The existing [RustBelt interface account](../rustbelt-unsafe-abstraction-model-popl-2018/REPORT.md) gives the paper's client-composition statement; this report adds direct theorem-source inspection and the missing operational arrow.

### 2. Safety transfer needs bad-execution reflection in the concrete-to-proved direction

Let `B_M(C[L])` mean that a linked MiniRust client/library has a finite execution prefix reaching the selected bad outcome. The identity of `M` includes target parameters, memory implementation and the chosen treatment of ordinary and predictive choices. Let `E` map the supported linked program and permitted entry state to a λRust or Radium subject.

One sufficient interface is:

```text
for every admitted client C and initial state satisfying Inv:
  B_M(C[L]) implies B_P(E(C[L]))
and:
  E(C[L]) satisfies the proved model's semantic typing/WP premises.
```

The existing model's adequacy then excludes `B_P`, hence excludes `B_M`. The relation must cover bad source prefixes; a theorem conditioned on source UB-freedom cannot independently establish that same premise. Functional correctness additionally needs an observation/result transport relation. Safety alone does not equate returned values, panics, divergence or permitted effects.

`Bridge.safety_transfer` proves the generic contrapositive implication without axioms. `Bridge.contextual_link` checks the client-quantified composition schema, also without axioms. Its premises remain explicit arguments: it does not implement the missing operational simulation or infer that a current rustc-accepted client satisfies them.

The counterexamples `invalid_bool_erasure` and `invalid_tag_erasure` map a concrete cell to its mathematical value. In the Boolean case the numeric value2 remains visible, but `abstractBad = False` omits its validity rule; in the tag case the map also discards tag liveness. Reflection fails for these distinct reasons. This tiny model isolates the omitted validity judgment and erased resource distinction; it is not an implementation of λRust or Tree Borrows. MiniRust's actual Boolean decode, unchecked-overflow branches and alias-changing reads provide the operational distinctions that a real relation must address. An overflow example must distinguish wrapping, checked and unchecked operators; mathematical semantic integers do not imply that MiniRust machine operations are unbounded.

Basis: **execution**, checked owned Lean theorems; **source**, MiniRust `representation.md`, `operators.md`, memory interface; **derived**, proposed sufficient bridge interface.

### 3. Radium already closes part of the representation gap, and exposes new comparison questions

The newer RefinedRust source is more concrete than the 2024 comparison's omissions might suggest. `radium/loc.v:12–23,49–52` represents mathematical addresses separately from allocation or function-pointer provenance. `radium/val.v:82–101` has ordinary bytes, indexed pointer fragments and poison; a value is a list of these bytes. `val_to_loc_n` accepts an exact pointer-fragment encoding, and its neighboring lemmas establish helper-level round trips. This source therefore cannot be classified as a value-cell heap merely because it uses Iris or mathematical integers.

Its `refinedrust_adequacy` at `rust_typing/typing/adequacy.v:93–111` assumes a `LayoutAlg`, allocated statics, an initial function/thread state, in-range entry addresses and a ghost-state-parametric proof of typed entry functions with provable preconditions. For every supplied finite `nsteps` execution, every reached thread is `not_stuck`. It is a concrete adequacy interface, but its operational subject is `c_lang`, not MiniRust.

Even representation helper equality is not automatic: Radium `val_to_loc_n` requires the exact fragment list, whereas MiniRust `decode_ptr` can decode initialized numeric bytes with missing/mixed fragments into an address with absent provenance. The companion [representation investigation](../minirust-representation-copy-provenance-laws-d821c6e/REPORT.md) examines this difference. An embedding must say whether it restricts such raw pointer representations, relates the absent-provenance cases differently, or changes one model. Source definitions establish this comparison question; they do not establish whole-language disagreement for an actual Rust example.

Basis: **source**, directly inspected artifact members and MiniRust helpers. The existing [Radium report](../refinedrust-radium-proof-boundary-2026-v2/REPORT.md) records the full theorem/TCB and absent generated proof dependencies; those dependencies were not rebuilt here.

### 4. Functional contracts can forget storage only through a restricted observation interface

For a pure parser over a shared byte slice, a useful abstract value relation is the byte sequence plus length. The spatial side must still guarantee initialized readable bytes, lifetime validity and permission for each load. An input/output proof about a mathematical list does not prove these premises. Padding, provenance or ownership may be existentially hidden only when the admitted client observations cannot distinguish their hidden states and each call restores the invariant.

For a mutable slice view, the relation must also track which concrete region implements the current and final sequence, and how ownership returns to the owner when the borrow ends. An interval split alone proves neither retag permissions nor protector restoration. `Bridge.split_cover` proves coverage and `split_disjoint` proves disjointness for natural-number intervals. They do not check machine-address overflow, element layout, pointer authority or callbacks.

For interior mutability, shared access permits safe mutation through appropriate types. Our safe `callback_read` reads a `Cell<u8>`, calls a closure that retains a shared alias and sets the cell, then reads it again. All 65,536 initial/final byte pairs pass the actual expected-result check; 65,280 have different reads. A contract that exposes an immutable snapshot across an unrestricted callback is false for this interface. A valid abstraction must expose a transition relation, constrain callbacks, or use a resource invariant that supports the mutation.

The same binary checks a two-byte little-endian parser for 65,536 pairs and safe split/mutate clients for every `0 ≤ mid ≤ n ≤ 16` (153 cases). These confirm the concrete test fixture's behavior, not a soundness theorem for its standard-library implementation.

Basis: **execution**, `safe-client-results.json`, compiler identity and retained MIR; **execution**, checked interval lemmas; **derived**, abstraction conditions.

### 5. Existing hybrid routes identify interfaces, not a common MiniRust linking theorem

Aeneas's functional translation reasons about generated pure definitions after Charon extraction and its own transformations. The existing [Aeneas resource report](../aeneas-resource-semantics-nightly-2026-06-03/REPORT.md) and [translation obligations](../aeneas-translation-correctness-obligations-nightly-2026-06-03/REPORT.md) give that exact interface. A MiniRust wrapper contract must be transported through those concrete lowerings and primitive models; a proof of a matching mathematical function name is insufficient.

Gillian's `creusillian/src/lib.rs:201–216` directly emits the original pre/post clauses as Creusot attributes and an elaborated specification as Gillian attributes. This is an actual contract-exchange point. It does not itself prove that both interpretations denote the same concrete byte/provenance behaviors. The [existing Gillian investigation](../gillian-rust-hybrid-resource-boundary-83d739e/REPORT.md) retains its resource and prophecy limitations. RefinedRust instead keeps functional refinements and spatial reasoning within one Radium/Iris model, reducing a cross-model handshake while retaining the Rust-to-Radium and MiniRust correspondence boundaries.

An eventual contextual theorem must quantify over the admitted client language, linked callee identities, trait/dictionary assumptions, lifetime substitutions and allowed callbacks. Foreign/unsafe clients require their own preconditions. This is the exact remaining theorem question, not a claim that one route already solves it.

Basis: **source**, Gillian emitter and Aeneas configuration; existing pinned source reports; **derived**, composition interface.

## Boundaries

- **Established here:** direct theorem/representation source inventory, a sufficient client-quantified reflection interface, checked generic logical implications and erasure counterexamples, and performed safe parser/split/interior-mutable callback experiments.
- **Unestablished:** any λRust-to-MiniRust or Radium-to-MiniRust operational relation, MiniRust fundamental theorem, or contextual source-Rust safety/functional abstraction theorem. No real allocation API, `split_at_mut` or `Cell` implementation was ported and proved under MiniRust; these concrete port experiments remain unperformed research, distinct from the broader future fundamental/linking theorem.
- **Not examined:** complete Radium alias semantics, original archive rebuild/assumption closure, Aeneas/Gillian interoperability execution, concurrency/relaxed memory, unwinding, trait objects, arbitrary source clients and unsafe/foreign caller domains.
- **Known limitation of the owned proofs:** their natural-number intervals omit bounded addresses and their erased cell model is deliberately minimal. The proof's success establishes the stated implication/counterexample only.
- **MR19 scope:** the need to account for interacting byte/alias/callback effects is identified, but no semantic handler framework or modular extension theorem is investigated here.

## Evidence

Evidence was acquired or materially rechecked on 2026-10-14. `source-evidence.json` binds exact repositories/archive hashes, paths and inspected symbols. Primary sources are the [MiniRust pin](https://github.com/minirust/minirust/tree/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed), [LambdaRust archive](https://gitlab.mpi-sws.org/iris/lambda-rust/-/archive/popl18/lambda-rust-popl18.tar.gz), [RefinedRust artifact](https://zenodo.org/records/21636474), and the [dual contract emitter](https://github.com/GillianPlatform/gillian-rust/blob/83d739e83034d71162fb66b569041cf301123df7/creusillian/src/lib.rs#L201).

`support/Bridge.lean` and `support/lean.log` retain theorem statements and printed axiom dependencies. The generic transfer/linking endpoints use no axioms; counterexamples use `propext`; interval proofs additionally use `Quot.sound`, and coverage also uses `Classical.choice`. There are no accepted `sorry` declarations. The unused interval-bound warning is harmless and retained.

`support/safe_clients.rs`, `safe_clients.mir`, `rustc-version.txt`, `rustc.log` and `safe-client-results.json` preserve the executed source, compiler-facing IR and output. The MIR is compiler-produced evidence for this fixture, not a MiniRust input or proof certificate.

## Revalidation

Run Lean on `support/Bridge.lean` with the recorded toolchain and inspect both exit status and printed axioms. Compile `support/safe_clients.rs` with the recorded rustc, retaining MIR, then run the safe binary. The cheap discriminators are the invalid-cell reflection witnesses and the callback that changes a shared `Cell`.

For a real bridge, recheck the exact adequacy statements and memory primitives, then instantiate the bad-prefix reflection and result-transport premises for one concrete supported API. Matching successful client outputs cannot revalidate those universal premises.

*Authored by an AI agent acting on joshlf's behalf.*

