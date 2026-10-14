# Iris execution adequacy and the resources a Rust instance must supply

## Summary

Iris connects logical proofs to executions of an explicitly supplied language. At the inspected revision, ordinary weakest-precondition adequacy establishes postconditions for reached results and non-stuckness after finite executions when `NotStuck` is selected. It does not establish termination, fair progress, or correspondence with rustc.

Camera laws, frame-preserving updates, guarded recursion, and proof-mode entailments provide reusable interfaces. A Rust instance still owes an operational interpretation of bytes, allocations, provenance, permissions and library contracts. Those interpretations are premises of the safety argument, rather than consequences of using Iris notation.

## Applicability

The principal source is the public Iris repository mirror `rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`, committed 2026-09-24. Source statements were inspected; the development was not rebuilt and its complete assumption closure was not audited.

The lifetime interface is examined separately in the `popl18` LambdaRust source archive, whose acquired bytes have SHA-256 `b35bf71ccf43367493a18db9af428279a4c56e3a2e7d57fbbc90a2de1cbe3996`. That historical dependency combination is not identified with the 2026 Iris revision. No compatibility between the two developments is claimed.

## Findings

### The language and state interpretation determine the safety subject

`language.v` packages expressions, values, states and observations, with a primitive step producing observations, a successor expression/state and forked expressions. `LanguageMixin` requires round-trip value conversion and that reducible expressions are not already values. This interface does not prescribe Rust memory or UB: the language instance must define which operations have steps and which become stuck. Basis: **source**. [Language interface](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/program_logic/language.v#L5).

`irisGS_gen` additionally supplies a state interpretation indexed by physical state, elapsed step count, remaining observations and fork count; a fork postcondition; and later-credit accounting. `wp_pre` requires reducibility in `NotStuck` mode, accounts for every primitive successor, re-establishes the state interpretation, and recursively proves the main and forked weakest preconditions. The recursive occurrence is guarded, and `wp_pre_contractive` justifies the fixpoint construction. Basis: **source**. [Weakest precondition](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/program_logic/weakestpre.v#L9).

### Adequacy has a precise partial-correctness conclusion

`adequate` quantifies over every configuration reachable by `rtc erased_step`. If the leading thread has returned a value, the pure result/state predicate holds. When stuckness is `NotStuck`, every reachable thread is either a value or reducible. `adequate_tp_safe` consequently gives a next step unless all threads are values. None of these statements requires an execution to finish.

`wp_adequacy_gen` requires logical initialization for every invariant instance and remaining observation list. Its convenient state interpretation ignores elapsed and fork counts, fixes additional laters per step to zero, and fixes a particular monotonicity proof; the source explicitly warns that other instances need the stronger adequacy interface. `wp_adequacy` specializes the credit mode. A Rust safety theorem must identify the actual instance used, rather than treating this helper as parameter-free. Basis: **source**. [Adequacy definitions and premises](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/program_logic/adequacy.v#L181).

### Cameras constrain legal splitting and updates

`CmraMixin` combines step-indexed equivalence, validity, composition and partial core with associativity, commutativity, validity monotonicity, core laws and an extension law. A camera therefore provides more than a disjointness predicate. `cmra_update x y` quantifies over every step index and optional frame: validity of `x` with that frame must imply validity of `y` with the same frame. An update checked against only the currently displayed proof context is weaker than this interface. Basis: **source** + **derived** consequence. [Camera mixin](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/cmra.v#L56), [updates](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/updates.v#L8).

`auth_both_validN` states that an authoritative state and fragment compose validly exactly when the fragment is included at the index and the authoritative state is valid. This supports a physical-state interpretation with client ownership fragments, but says nothing by itself about the contents of a Rust allocation. Basis: **source**. [Authoritative resources](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/auth.v#L199).

For byte-level verification, the resource carrier must retain the distinctions needed by the operational model: allocation instance/liveness; initialized versus uninitialized contents; provenance-bearing representations; and access/alias permissions. An authoritative map and range fragments are candidate ingredients. Their camera laws and connection to concrete loads/stores must be proved. This is a **derived construction obligation**; this report does not present a verified camera for zerocopy memory.

### Guarded recursion imposes real proof obligations

The OFE fixpoint construction assumes an inhabited complete OFE and a contractive function. `fixpoint_unfold` and `fixpoint_unique` are proved under those premises. Contractiveness relates arguments equal at earlier indices to results equal at the current index; an arbitrary recursive Rust invariant is not admitted merely because it can be written as an equation. The inspected BI fixpoint-property lemmas also retain a finite-index assumption. Basis: **source**. [Fixpoint construction](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/algebra/ofe.v#L670), [BI fixpoint laws](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/bi/lib/fixpoint_banach.v#L13).

Later modalities and credits discharge logical delays according to the operational-step accounting supplied by the instance. They are not a termination argument or permission to remove an arbitrary guard. Basis: **derived** from `wp_pre` and its credit accounting.

### Lifetimes and ordinary prophecies expose different logical interfaces

The historical lifetime signature provides fractional live tokens, persistent dead tokens, inclusion and borrow assertions. `lft_tok_dead` excludes holding live and dead evidence together. `bor_create` trades guarded ownership for a borrow and a recovery continuation activated by dead-lifetime evidence. `bor_shorten` consumes an inclusion proof; accessors require masks, lifetime tokens and a closing continuation. The `Parameter` declarations belong to a module signature; `lifetime.v` supplies that signature by including concrete model definitions and proved laws. They are not, by their declaration form alone, evidence of global admitted axioms. Basis: **source**, `theories/lifetime/lifetime_sig.v`, `lifetime.v`, and model files in the identified archive.

Modern ordinary prophecy resources use `proph_map_interp` to connect authoritative future-value lists with remaining observation events. Resolution consumes the first corresponding predicted value and updates the remaining list; agreement ties client prophecy ownership to that interpretation. A new language must expose suitable observation events and preserve this state interpretation. This is a different interface from RustHornBelt's parametric prophecy mechanism, addressed in the companion report. Basis: **source**. [Prophecy map](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/base_logic/lib/proph_map.v#L33).

### Proof automation supplies witnesses for logical judgments

The proof-mode `Frame` class carries the entailment `□?p R ∗ Q ⊢ P`; `FromAssumption` and `IntoPure` similarly carry entailments. Search, matching and tactics construct those witnesses. Accepting a search decision without its entailment would change the trust boundary. Extending automation with a new instance can remain conservative when the instance supplies a checked proof under the existing logic; adding a new primitive logical rule requires its own soundness argument. Basis: **source** + **derived** trust distinction. [Proof-mode classes](https://github.com/rocq-iris/iris/blob/8e4909593a3a84f850d224a344cbd3a380672088/iris/proofmode/classes.v#L386).

## Boundaries

- **Known not to apply:** ordinary WP adequacy does not prove termination, fairness or all Rust UB obligations. It concerns the supplied primitive-step semantics.
- **Not examined:** a complete modern Iris assumption audit or build, serialized spatial certificates, and concrete Rust byte/provenance cameras.
- **Unknown:** a source-to-Radium/MiniRust/rustc relation sufficient to use this generic adequacy theorem as a Rust-level guarantee.
- **Not examined:** full Lithium/Diaframe/Quiver comparison, parametric prophecy proofs, or porting the historical lifetime implementation to this Iris revision.
- **Not examined:** Lean-native Iris compatibility, feature parity and a Rust language instance. Those require a separately pinned feasibility investigation.

## Evidence

Direct source retrieval and archive inspection occurred on 2026-10-14. Evidence is **source** and **derived**, with no fresh proof checking or program execution.

At the full Iris commit above: `program_logic/language.v:5–29`; `weakestpre.v:9–93`; `adequacy.v:181–255`; `algebra/cmra.v:56–89`; `updates.v:8–15`; `auth.v:199–205`; `ofe.v:670–760`; `bi/lib/fixpoint_banach.v`; `base_logic/lib/proph_map.v`; `proofmode/classes.v:386–387`.

Historical source archive: [LambdaRust popl18 archive](https://gitlab.mpi-sws.org/iris/lambda-rust/-/archive/popl18/lambda-rust-popl18.tar.gz), exact acquired SHA-256 above, paths under `lambda-rust-popl18/`. The tag's full Git revision was not independently resolved; the hash binds inspected bytes. `theories/lifetime/model/borrow.v:70` proves `bor_create`; `model/primitive.v:275,308–343,415` supplies consistency, inclusion and shortening laws.

## Revalidation

Diff the exact language, WP and adequacy interfaces together; changes to observations, fork semantics, state interpretation or credit accounting can alter the theorem premises. For a new resource, check its mixin laws and updates against arbitrary compatible frames before proving operational rules. For recursive invariants, inspect contractiveness and index assumptions. Before treating an automated proof as accepted evidence, check the generated term and its assumptions in the exact prover/dependency environment. A theorem about one language instance requires another correspondence argument before it can justify another language.

*Authored by an AI agent acting on joshlf's behalf.*
