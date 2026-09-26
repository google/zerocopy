# Rust auto-trait coinduction and recursive unsafe impls at nightly-2026-05-31

## Summary

At `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, auto traits such as `Send` and `Sync` are coinductive: some recursive proof cycles are accepted rather than treated as ordinary inductive recursion. This is necessary for recursive data structures whose automatically generated auto-trait proof eventually asks for the same auto trait again.

The same machinery also admits a qualitatively different cycle:

```rust
struct NotSend(Rc<()>);

unsafe impl Send for NotSend
where
    NotSend: Send,
{}
```

To prove `NotSend: Send`, the compiler can select the explicit impl and then encounter its own `NotSend: Send` where-bound. At the pinned revision, both solver implementations contain rules under which this self-cycle is accepted. The classic solver accepts a repeated cycle when every participating trait predicate is coinductive. The next solver marks an impl where-bound as a coinductive step when the current goal is a coinductive trait, and a coinductive cycle begins from provisional success.

The result is that an explicit unsafe auto-trait impl can participate in the same coinduction that justifies structural recursion through automatically generated auto-trait impls. A source-level `where Self: Send` guard is therefore not, by itself, evidence that the unsafe impl's semantic safety obligation has been established independently.

Whether this behavior should be classified as a compiler soundness bug or as evidence that the semantic obligation of a recursive `unsafe impl` must be stronger than a simple implication from its where-bounds was unresolved upstream at the pin. rust-lang/rust#149743 tracks exactly that dispute. google/zerocopy#3380 records the same concern for Anneal-era reasoning. This report preserves the compiler behavior and the unresolved interpretation separately.

No fresh compiler execution was performed. The report uses the exact pinned solver source, the Rust Reference's unsafe-impl contract, standard-library trait definitions, checked-in solver tests, implementation history, and upstream issue discussion.

## Applicability

Compiler subject:

- repository: `rust-lang/rust`;
- revision: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`;
- Anneal-era toolchain date: nightly-2026-05-31.

Reference subject:

- repository: `rust-lang/reference`;
- revision: `ad35aca481751a06afeb23820a672b0f3b11a476`.

The report covers the classic trait solver and the next solver as implemented at this revision. It does not depend on which one a particular invocation selects for the simple self-cycle, because both implementations have a source path that treats an auto-trait cycle coinductively.

The concrete motivating pattern uses `Send`, which is an unsafe auto trait at this pin. `Sync` has the same two relevant properties. The compiler also treats `Sized` as coinductive through an internal marker, but users cannot write arbitrary `Sized` impls, so the unsafe-impl concern discussed here centers on user-implementable unsafe auto traits.

## Findings

### Rust makes unsafe impls programmer assertions of extra safety conditions

The pinned Rust Reference says an unsafe trait defines extra safety conditions that implementations must uphold. Writing `unsafe impl` states that the programmer has discharged those proof obligations.

That language establishes the safety boundary but does not define a formal logical rule for recursive where-clauses. In particular, it does not say that compiler derivability of the impl's own trait bound is sufficient to discharge the trait's semantic safety contract.

Basis: **normative** Rust Reference.

### `Send` and `Sync` are unsafe auto traits

The pinned core library declares both `Send` and `Sync` with `pub unsafe auto trait`. The same source explains that `Rc`-style shared reference counting is not thread-safe, and `alloc::rc::Rc` carries explicit negative `Send` and `Sync` impls.

Thus the motivating `NotSend(Rc<()>)` example is not merely syntactically interesting: its field type is explicitly not `Send`, while an explicit impl can assert `Send` for the wrapper.

Basis: **source**.

### Structural auto-trait recursion is intentionally coinductive

The pinned unstable-book documentation explains the normal reason for coinduction. For a recursive type such as a linked list, the automatically generated `Send` proof follows the fields through `Box<List<T>>` and eventually reaches `List<T>: Send` again. Ordinary inductive cycle rejection would fail a legitimate recursive structure.

The rustc-dev-guide likewise describes auto traits, `Sized`, and selected well-formedness goals as coinductive and explains the solver's provisional-result treatment of cycles.

This intended structural case is important because it supplies the motivation for coinduction; it does not by itself justify every user-written recursive impl.

Basis: upstream **documentation**.

### The classic solver accepts an all-coinductive cycle

In the pinned classic solver, recursive evaluation detects a repeated trait obligation and calls `coinductive_match` on the cycle. That function accepts the cycle when each participating trait predicate is coinductive.

For the direct self-loop

`NotSend: Send -> NotSend: Send`

the cycle contains only `Send`. Since `Send` is an auto trait and therefore coinductive, the source rule classifies the cycle as successful rather than as an ordinary inductive recursion failure.

The classic solver does not distinguish whether the edge back to `NotSend: Send` came from an automatically synthesized structural auto-trait impl or from a user-written explicit impl's where-clause.

Basis: **source**.

### The next solver makes an impl where-bound a coinductive step for coinductive traits

The pinned next solver uses more explicit path semantics. `CurrentGoalKind::CoinductiveTrait` is selected when the trait being proved is coinductive. When the solver steps into `GoalSource::ImplWhereBound` under such a goal, it records `PathKind::Coinductive`.

When a cycle is classified coinductive, the search graph's initial provisional result is `Certainty::Yes` with no constraints. Subsequent fixpoint processing can refine that result, but the recursive call itself is not rejected merely for returning to the same auto-trait goal.

For

`unsafe impl Send for NotSend where NotSend: Send`

selecting the impl exposes an impl where-bound while proving the coinductive trait `Send`. That is exactly the source condition the next solver labels a coinductive step.

Basis: **source**.

### The next solver's broader rule was deliberate, but the unsafe-impl consequence remained disputed

PR #136824 changed next-solver cycle semantics so that a cycle is coinductive once it contains at least one coinductive step. Its description says an impl where-clause of a coinductive trait is such a step and motivates the rule using guarded corecursive dictionary construction.

The same description argues that stepping into an auto-trait impl can make a cycle coinductive. At the implementation level, the rule applies to `ImplWhereBound` based on the current coinductive trait goal; it does not encode a separate distinction between an automatically synthesized auto-trait impl and an explicit user-written one.

By December 2025, rust-lang/rust#149743 identified the safety consequence explicitly. The issue uses an `unsafe impl Sync for MyCell where MyCell: Sync`-style example and asks whether the solver behavior is unsound or the usual understanding of the unsafe-impl proof obligation is incomplete. The issue remained open at the compiler pin.

Basis: implementation-history **documentation** + **source**.

### Upstream discussion proposed a stronger notion of productive progress

The discussion in rust-lang/rust#149743 distinguishes two possible kinds of recursive step.

One view is that an automatically synthesized auto-trait impl is productive because it unfolds the structure of the type into obligations on its fields. A manually written impl such as `unsafe impl Send for T where T: Send` does not visibly make that structural progress and therefore should not be allowed to justify itself.

That distinction was a proposal in discussion, not an implemented rule established by this report. The pinned next solver still marks an impl where-bound under a coinductive trait as a coinductive path step.

Basis: upstream **documentation/history** + compiler **source**.

### Non-auto recursive traits do not get the same direct coinductive treatment

The classic solver's `coinductive_match` requires all trait predicates in the accepted cycle to be coinductive. An ordinary user trait therefore does not satisfy the direct self-cycle rule.

The next solver likewise treats an impl where-bound as coinductive only when `current_goal_kind` is `CoinductiveTrait`. Under an ordinary trait goal, the corresponding cycle is not promoted to the same coinductive path kind.

google/zerocopy#3380 records the observed contrast: an analogous recursive non-auto trait obligation overflows rather than establishing the trait. This matches the source distinction, though this report did not rerun that fixture.

Basis: **source** + preserved project-history **documentation**.

### “The compiler proved the bound” and “the unsafe contract is independently justified” are distinct facts

The Rust Reference makes the unsafe impl a programmer assertion of semantic safety conditions. The trait solver decides whether trait predicates are derivable according to Rust's trait-system rules.

For recursive unsafe auto-trait impls, those two layers can interact circularly: the solver may derive the where-bound through the very impl whose semantic safety is at issue.

Therefore, any external verifier or proof discipline that treats an unsafe impl's where-bounds as semantic assumptions must distinguish ordinary assumptions from self-supporting coinductive derivations. This is a derived constraint on sound reasoning, not a choice of Anneal architecture.

Basis: **derived** from the normative unsafe-impl contract and pinned solver behavior.

## Boundaries

- No fresh rustc execution was performed.
- The report establishes the source mechanics that admit the direct recursive auto-trait cycle; it does not claim an exhaustive characterization of every trait-solver cycle.
- rust-lang/rust#149743 was unresolved at the pin. This report does not decide the contested question of whether the compiler behavior itself is unsound or the semantic contract of recursive unsafe impls must be interpreted differently.
- The report does not prove a concrete undefined-behavior execution from the minimal `NotSend` declaration. It establishes that `Rc` is explicitly `!Send` while the recursive explicit impl can participate in a self-supporting `Send` proof.
- Classic-solver and next-solver cycle algorithms differ materially beyond the simple pattern covered here.
- The next solver has additional path kinds for normalization, type relations, coherence, ambiguity, and other goal sources. Those are not exhaustively surveyed.
- Auto-trait behavior involving negative impls, specialization, trait aliases, dyn objects, projections, higher-ranked bounds, and lifetime cycles is outside this report except where cited as context.
- `Sized` is coinductive but not a user-implementable analogue of `Send`/`Sync`; no broader unsafe-impl conclusion is drawn from it.
- No claim is made that adjacent Rust revisions retain these exact cycle rules.
- No Anneal verification-result model or mitigation is selected.

## Evidence

**Normative Rust Reference**

- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `src/unsafe-keyword.md`, blob `7658c1f5c5425d03e2183e89b55260e5e9fd889b`: unsafe traits define extra safety conditions; `unsafe impl` asserts those conditions are discharged.

**Compiler and library source — `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`**

- `library/core/src/marker.rs`, blob `53141aabacc453e3781bbe9593618e26c06ca732`: `Send` and `Sync` declarations; `Sized` coinductive marker and rationale.
- `library/alloc/src/rc.rs`, blob `523c9b8b1585846d448791b40d0b800f7286af0e`: explicit negative `Send` and `Sync` impls for `Rc`.
- `compiler/rustc_middle/src/ty/mod.rs`, blob `6df1ed82d260a5c95dbe9671f2c7ddf8585c36ab`: `trait_is_auto` and `trait_is_coinductive`.
- `compiler/rustc_trait_selection/src/traits/select/mod.rs`, blob `eadc937639f209ceaebef0eaf59cf4b279d507e7`: classic-solver recursive-cycle detection and `coinductive_match`.
- `compiler/rustc_next_trait_solver/src/solve/eval_ctxt/mod.rs`, blob `54d306466cf5b1b5b8f32625606b469dcfa7d5a8`: `CurrentGoalKind::CoinductiveTrait` and `ImplWhereBound -> PathKind::Coinductive`.
- `compiler/rustc_next_trait_solver/src/solve/search_graph.rs`, blob `a46261fcf72716f5571a996da35fa0ffc6e4504f`: provisional success for `PathKind::Coinductive`.
- `src/doc/rustc-dev-guide/src/solve/coinduction.md`, blob `9753f7539c27a08bd443817f9086bd047be957d9`: coinductive-cycle model and future-work discussion.
- `src/doc/unstable-book/src/language-features/auto-traits.md`, blob `014e15d1ada6833d828961f1e5879cf333611a96`: automatic auto-trait impls and cyclic matching.
- `tests/ui/traits/next-solver/cycles/coinduction/only-one-coinductive-step-needed.rs`, blob `e41f7d7f3ceb341d1f48aa4b591435aaccde4273`: preserved fixture documenting the next solver's one-productive-step policy and its difference from the classic solver.

**Implementation and issue history**

- rust-lang/rust PR #136824, merged 2025-02-28: introduced the next solver's “one coinductive step” cycle semantics and documented the guarded-corecursion rationale.
- rust-lang/rust#149743, opened 2025-12-07 and still open at the pin: “Coinductive auto-trait treatment is questionably sound”; records the unresolved unsafe-impl contract dispute.
- google/zerocopy#3380, opened 2026-05-19: records the same self-referential `Send` concern in Anneal development. A follow-up comment from lcnr states that either the unsafe impl or compiler interpretation is wrong and leans slightly toward the coinduction support being wrong.

No evidence above is fresh **execution**.

## Revalidation

For a later compiler pin, use the smallest source discriminator first:

1. inspect `trait_is_coinductive` and the definitions of `Send`/`Sync`;
2. inspect the classic solver's cycle classifier if that solver still exists;
3. inspect the next solver mapping from impl where-bounds to cycle/path kinds and its provisional result for a coinductive cycle;
4. check rust-lang/rust#149743 and any linked language/trait-system decision for a resolved semantic contract.

On a capable execution surface, compile two minimal controls at the exact revision:

```rust
use std::rc::Rc;

struct NotSend(Rc<()>);
unsafe impl Send for NotSend where NotSend: Send {}

trait Foo {}
impl Foo for NotSend where NotSend: Foo {}
```

Require `NotSend: Send` and `NotSend: Foo` separately, under each supported solver mode. Preserve commands, diagnostics, solver flags, and exact revision. Add a structurally recursive auto-trait control such as `struct List(Box<Option<List>>)`.

That experiment distinguishes the direct self-supporting explicit impl from intended structural auto-trait recursion. It does not, by itself, settle the semantic safety contract of recursive unsafe impls.
