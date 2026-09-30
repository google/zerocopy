# Early cutoff: equality is relative to a consumer

## Summary

Early cutoff is sound only when “unchanged” means unchanged for the downstream
observation that is being skipped. There is no useful global equality relation
that simultaneously captures source identity, compiler semantics, generated
model semantics, diagnostics, provenance, object code, and verification
authority.

Three mature incremental mechanisms make the same architectural point at
different scales. Jane Street Incremental lets each node choose the predicate
that decides whether a recomputed value should propagate. rustc's red-green
query engine reruns a dirty query and can stop invalidation when the query's
stable result fingerprint is unchanged; projection queries deliberately create
change-propagation firewalls around large changing values. GHC recompiles a
module when its own source changes, but can stop *downstream* recompilation when
the ABI or the particular imported declarations a client used are unchanged.
The cutoff boundary and the equality relation are paired.

For Anneal, this argues against one “workspace hash” or one normalized-source
identity governing every kind of reuse. Exact bytes are the conservative
criterion for reusing a captured artifact as that exact artifact. A canonical
model fingerprint may be enough to avoid rebuilding proof work that depends
only on that model. An interface fingerprint may shield clients that observe
only that interface. Source/provenance and presentation state must still move
when their observations changed, even if the mathematical model did not.
Verification success has a stronger condition again: a current Rust-level claim
needs current evidence connecting the identified Rust subject to the reused
model and proof, not merely evidence that an old model hash matches.

The practical rule is therefore **recompute until reaching a boundary with a
checkable equality that is a congruence for the downstream use; then cut off
only that downstream path**. When the relevant observation cannot be
characterized or its dependencies cannot be captured, conservative invalidation
is the correct fallback. Maintaining separate semantic and presentation
dependencies is worth the complexity only where the semantic work is expensive,
presentation-only changes occur often enough to matter, and the two dependency
classes can be kept explicit and testable.

## Applicability

This report addresses J039 from `google/zerocopy#3732`: byte equality,
normalized syntax, interface/ABI equality, observational equivalence, and
claim-relative equivalence as reuse criteria. It is a comparative literature and
architecture synthesis, not a benchmark and not an adopted Anneal design.

The directly examined mechanisms are:

- rustc incremental compilation as documented at
  `rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`;
- Jane Street Incremental at
  `janestreet/incremental@98b5750ec3c006641351bfd858a89136a5dbc52c`;
- GHC's current recompilation checker at
  `ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`, with the
  versioned GHC 7.0 user guide used as historical corroboration;
- the published Anneal/Charon/Aeneas provenance probe
  `anneal-3731-charon-relocation-comment-provenance-2026-09-29` at
  `reference@a5ecd5bde3d2b33457b5a13b4b435d79515f4012`; and
- Anneal's design contract at
  `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

These subjects are not claimed to implement the same algorithm. Jane Street
Incremental exposes a general dynamic dependency graph and user-selected
cutoffs. rustc uses compiler-owned queries and stable fingerprints. GHC's
recompilation checker records module/entity usage and interface fingerprints.
The Anneal probe is bounded execution evidence about two translator stages. The
comparison is about where each system places a boundary at which a coarser
notion of sameness is sufficient.

This report assumes that the dependency set for the reused result is already
sound. Equality cannot compensate for an unobserved dependency. Dynamic and
negative dependency discovery is the separate J038 problem.

## Findings

### Early cutoff is a relation between a value and a downstream observation

Suppose a stage recomputes value `x'` after an input change, while a cached
downstream computation was previously built from `x`. The question is not
whether `x` and `x'` are “really equal.” The operational question is whether
every observation made by the downstream computation that we intend to skip
would be unchanged.

For a downstream consumer `C`, a sufficient cutoff relation `~C` has this
property:

```text
x ~C x'  =>  C cannot distinguish x from x' in any way material to the reused result
```

That is deliberately weaker than mathematical equality of the producer's full
value and stronger than “they look similar.” It also exposes why a cutoff can be
safe for one edge and unsafe for another. A compiler client that sees only an
exported type may ignore a private implementation edit. A diagnostic renderer
that must report source locations may not ignore a relocation. A verifier that
accepts a theorem about one model may ignore a presentational change only after
the current source-to-model correspondence has been re-established.

The relation need not even be an equivalence relation in a general incremental
library. A user can choose an approximate cutoff such as “two floats differ by
less than ε”; that predicate may fail transitivity and may intentionally change
observable behavior. The useful term is therefore *cutoff predicate*. “Equality”
is appropriate only when the predicate actually preserves the observation being
reused.

Basis: **derived** from the three mechanisms below, with Jane Street
Incremental providing direct evidence that cutoff is a configurable predicate
rather than a built-in semantic theorem.

### Jane Street Incremental makes the cutoff policy explicit

At `janestreet/incremental@98b5750...`,
`src/incremental_intf.ml` describes stabilization as recomputing a changed node
and adding its parents to the recompute heap only when the node's value
“changes.” The definition of change is configurable. The default is physical
equality; `set_cutoff` can replace it, and the documentation gives a float
threshold as an example.

This design makes two points unusually clear.

First, early cutoff belongs to the produced value, not to the original input.
An input can change, the node can recompute, and propagation can still stop
because the node's new value is equivalent enough under its cutoff predicate.

Second, the library cannot infer whether a custom predicate preserves the
meaning of an arbitrary downstream function. If a downstream computation can
distinguish two values that the cutoff declares equivalent, it may remain stale.
The library's mechanism supplies a place to express a cutoff; the application
owns the semantic justification for that cutoff.

The 2015 first-party introduction to Incremental presented it as dynamic
self-adjusting computation, and later Jane Street examples used projection
nodes so that a large model could change while only projections whose values
changed propagated. That is the same structural idea as an interface or query
firewall: recompute a comparatively cheap projection, then compare the thing
the consumer actually observes.

**Anneal implication, derived:** a configurable “equivalence” hook on arbitrary
opaque artifacts would be too weak as an acceptance primitive. If Anneal uses
cutoffs, the safe relation should normally be fixed by a typed stage boundary
whose downstream observations are known, or the result should be explicitly
advisory/approximate. User-selected approximate cutoffs are appropriate only
for outputs whose contract admits approximation.

Basis: **source/documentation**, `src/incremental_intf.ml`, blob
`eabce575943287f144a8f66cf342fd9db438a33e`, plus the 2015 Jane Street
“Introducing Incremental” account.

### rustc re-evaluates through a dirty boundary and compares the query result

The rustc development guide's red-green algorithm is a concrete answer to the
problem of over-invalidation. If all dependencies of a query are green, the
query stays green without running. If a dependency is red, rustc may rerun the
query; if the rerun produces the same result fingerprint as the previous
session, the query itself becomes green and its dependents need not rerun.

The comparison is not source-byte equality. rustc computes a 128-bit
`Fingerprint` from the query result using stable hashing. Values whose in-memory
identity can differ between sessions, such as `DefId`, are mapped to stable
counterparts before hashing. The guide explicitly records both the cost and the
risk: stable hashing is expensive enough to matter for incremental compilation,
and hash collisions are possible, though treated as negligible with the chosen
128-bit fingerprint and hash quality.

Two refinements are especially relevant to Anneal:

1. A `no_hash` query cannot establish result equality and therefore must be
   treated as changed for downstream invalidation. Avoiding an expensive
   comparison gives up cutoff power.
2. Projection queries can form a “firewall.” A large monolithic query may
   change or be conservatively red, while small projections of that result are
   separately fingerprinted. Only dependents of changed projections rerun.

This is a stronger pattern than globally normalizing the monolithic value. The
system asks what each dependent actually needs and gives that observation its
own node and fingerprint. Granularity is not free: dependency tracking,
fingerprint computation, retained graph state, and debugging all cost time and
memory. rustc's own documentation describes fingerprinting as a significant
incremental cost.

The history also matters. Rust's 2016 alpha announcement described a coarse
dependency graph focused heavily on code-generation reuse and called out false
positives from coarse granularity as expected future work. The current
red-green design is not evidence that the finest possible granularity was
obviously correct from the start; it is an evolved mechanism that pays
additional machinery to stop propagation at more useful semantic boundaries.

**Anneal implication, derived:** if Charon or Aeneas exposes a stable,
well-defined projection that a later stage alone observes, that projection can
be a legitimate cutoff boundary. Inventing an Anneal-side projection over an
opaque upstream output is safe only if Anneal can establish that the skipped
consumer truly observes no discarded distinction.

Basis: first-party **documentation/history** at
`rust-lang/rustc-dev-guide@8ae6c255...`,
`src/queries/incremental-compilation.md` blob
`079a2b2e00a7f2dd088fab5a4d74541a53659ea1` and
`src/queries/incremental-compilation-in-detail.md` blob
`9893edd54b950155da586843baa3319da15dcc4e`; Rust project blog,
“Incremental Compilation,” 2016-09-08.

### GHC distinguishes producer recompilation from downstream invalidation

GHC demonstrates why interface equality should usually stop a *dependent* path,
not excuse recomputing the changed producer.

At `ghc/ghc@234bab081...`, `GHC.Iface.Recomp` first checks the current module's
source hash. If the source hash changed, that module must compile. For imported
modules, however, the old interface records what the client used. The
recompilation checker compares fingerprints of those uses against current
fingerprints.

The current source contains two useful granularity choices:

- for package modules, GHC tracks the module ABI hash. The source comment says
  this is safe but may cause more recompilation;
- for home modules, it can check the export information and individual entity
  fingerprints that the client used.

The ABI hash itself is intended to include what is visible to a client.
`addAbiHashes` describes a declaration's ABI as everything made visible about
that declaration that a client can depend on. Individual declaration hashes are
computed so home-package recompilation checking can be fine-grained. The
interface hash is broader than the ABI hash because it also includes information
that can affect whether the module itself must be recompiled.

Versioned GHC 7.0 documentation already described interface-file and
per-declaration fingerprints used to avoid unnecessary downstream recompilation.
The current implementation is substantially richer, but the durable principle
is the same: source identity answers whether the producer is the same source;
interface equality answers whether a particular class of clients needs to see a
change.

This is also a warning against calling an interface hash “semantic equality.”
It is semantic only relative to the client contract encoded by that interface.
If a client observes implementation details through inlining, plugins,
Template Haskell, orphan instances, generated bytecode, dependent files, or
another channel, those observations must be reflected in the recorded
recompilation information or the cutoff is unsound. The current checker contains
specific machinery for many such cases rather than relying on the exported type
surface alone.

**Anneal implication, derived:** if a proof client consumes a stable obligation
or model interface, equality of that interface can shield proof work from a
producer's private changes. It cannot by itself say that the new Rust source
corresponds to the old model or that source-oriented diagnostics are current.

Basis: GHC **source**,
`ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`,
`compiler/GHC/Iface/Recomp.hs`, blob
`cbd1d392ccd3cee37a0c4dd7dc75ec6117a88dc8`; versioned GHC 7.0 user-guide
recompilation documentation.

### Byte equality is conservative about representation, not complete about meaning

Byte equality has a valuable property: for a captured immutable artifact, equal
bytes establish that the artifact representation is exactly the same. A
content-addressed cache can therefore reuse those bytes without inventing a
normalizer.

That criterion is often intentionally too strong. Two source files that differ
only in inert whitespace or comments can compile to the same semantic
intermediate representation. Two serialized objects can encode the same
logical value with harmless ordering differences. A source path can move while
the translated function body remains the same.

Byte equality is also not sufficient for the result of an *effectful stage* if
the stage depends on information outside those bytes. Equal Rust source does
not establish equal build-script outputs, environment variables, compiler
version, plugins, filesystem lookups, or target configuration. This report does
not attempt to solve that input-closure problem; it simply treats the captured
environment/model identity as part of the value whose reuse must be justified.

The conservative default is therefore:

```text
same captured inputs + same required environment identity + same exact artifact bytes
```

for direct artifact reuse. A coarser relation should be introduced only at a
boundary where the discarded differences are known not to matter.

Basis: **derived**; hidden-input limits are outside J039 and belong to the
dependency-closure analysis in J038.

### Normalized syntax is useful only when the erased syntax is outside the consumer contract

“Normalized syntax” is not one relation. A normalizer may erase comments,
whitespace, source paths, identifier spelling choices, declaration order, span
locations, generated metadata, or other distinctions. Each erased distinction
creates an obligation: no skipped consumer may depend on it.

The published Charon/Aeneas provenance probe gives a concrete Anneal-relevant
example. For one pinned one-function fixture, appending an inert comment after
the function changed Charon's serialized full source contents but left the
generated Aeneas Lean byte-identical. Moving byte-identical Rust source to
another root changed the local source-file path in LLBC and changed only a
source-path documentation line in the generated Lean after the probe's
schema-aware comparison.

Those observations support two different cutoff paths for that fixture:

- a model-content consumer could potentially reuse the generated Lean after the
  inert comment edit;
- a source/provenance consumer could not pretend nothing changed, because the
  LLBC source contents or source path had changed.

The same report explicitly limits the result. A comment that changes line
positions, participates in macro input, becomes a documentation attribute, or
affects a path-sensitive build can matter. Relocating a larger workspace can
also affect path dependencies, build scripts, generated files, or macros. The
probe is evidence for separating dependency classes, not a license to globally
strip comments and paths.

**Anneal implication, derived:** normalization should produce a named semantic
projection, not replace source identity. If a stage keys expensive proof work
by normalized/model content, keep the original source snapshot and mapping as a
parallel dependency of diagnostics and source-model correspondence.

Basis: published **execution** evidence,
`reference@a5ecd5bde3d2b33457b5a13b4b435d79515f4012`,
`reports/anneal-3731-charon-relocation-comment-provenance-2026-09-29/`.

### Interface and ABI equality are deliberate projections, not universal compatibility

Interface equality is more useful than normalized syntax when the abstraction
boundary itself defines what clients may observe. GHC's declaration ABI is a
strong example: its source says the declaration ABI represents what is made
visible and on which a client can depend. The resulting fingerprint is therefore
paired with a client model.

For Anneal, possible interface-shaped boundaries include a set of proof
obligations, a normalized theorem statement, a translator model, a declared
trust manifest, or an exported contract for a verified Rust abstraction.
Whether any one of these is sufficient depends on the consumer:

- an obligation solver may care only about the proposition and imported logical
  environment;
- a proof-repair UI may also care about names and source locations;
- an acceptance layer cares about the identified Rust subject, promises,
  coverage, trust, and source-model justification.

A stable obligation ABI could therefore prevent proof recomputation while a
changed source mapping still regenerates. Conversely, an unchanged textual
theorem statement is not sufficient if the imported environment or trusted
axioms changed.

The cost is schema ownership. Once Anneal treats a projection as a stable
cutoff boundary, it must define what observations belong in that projection,
version it when those observations change, and test that producers do not omit
semantically material information. A coarse interface is easier to reason about
but invalidates more. A fine interface saves more work but expands the
dependency and compatibility surface.

Basis: **derived** from GHC's client-relative ABI fingerprints and Anneal's
current success semantics.

### Full observational equivalence is the ideal boundary and usually the wrong implementation mechanism

Observational equivalence can be stated cleanly: two values are equivalent for a
consumer when every observation the consumer is permitted to make produces the
same relevant result. This definition explains why the previous mechanisms are
sound when their contracts hold.

It is rarely a practical cache key for an opaque compiler or prover. Establishing
equivalence of arbitrary programs, translators, process behavior, or generated
proof environments may require work comparable to rerunning the consumer, or
may depend on effects that the host does not control. The practical systems
studied here therefore use *checkable proxies for the observation boundary*:
query-result fingerprints, interface/entity fingerprints, or application-owned
cutoff predicates.

Anneal should do the same. Prefer a projection whose sufficiency can be argued
from an interface contract or validated independently. If the only available
statement is “these two complete tool executions would have behaved the same,”
running the stage again is often the cheapest trustworthy test.

This does not rule out stronger equivalence certificates. If an upstream tool
can emit a checked canonical model, a proof-producing normalization, or another
certificate that establishes the exact relation a downstream proof consumes,
that certificate can justify a coarser cutoff. The key difference is that the
equivalence is then evidence, not a host-side guess.

Basis: **derived** comparison. No claim is made here that a particular broad
observational-equivalence problem is decidable or undecidable; the engineering
judgment is only that the examined tool boundaries do not provide such a
general certificate.

### Anneal needs claim-relative equality at the acceptance boundary

Anneal's design contract makes the acceptance observation unusually strong.
Verification success must identify the program or behavior to which the result
applies, the promises established, and the trusted code and assumptions on
which those promises depend. A Rust-level claim also needs a justified route
from the Rust program to the proof obligations.

That means “same mathematical model” is not enough to reuse an old successful
result for new source. A source edit can leave the generated model unchanged
while changing the identity of the Rust subject, source mapping, coverage
evidence, or trusted translation circumstances. The Charon/Aeneas comment probe
demonstrates the first half of that possibility directly: source-level identity
changed while generated Lean did not.

A sound reuse decomposition is therefore layered:

```text
source snapshot / build context
        |
        | current translation + correspondence evidence
        v
semantic model / obligations  ---- model equality ----> reusable proof work
        |
        | theorem checking in identified logical environment
        v
proof result / trust facts
        |
        | current source + promise + coverage + trust association
        v
verification acceptance
```

A semantic cutoff can stop the expensive right-hand proof path when the model,
obligations, logical environment, and trust-relevant inputs are equivalent.
It does not stop the source/correspondence path that establishes that the
current Rust subject is represented by that model. A presentation cutoff may be
different again: diagnostics can require new paths or spans even if the model
and proof remain unchanged.

This is *claim-relative equivalence*: two upstream states are interchangeable
only for a specified claim and its evidence obligations. The relation for
“reuse this theorem proof” can be coarser than the relation for “reuse this
diagnostic,” while the relation for “publish success for this Rust subject”
must include enough current identity and correspondence to satisfy the design
contract.

**Conditional recommendation:** make acceptance depend on explicit source,
model/obligation, environment/toolchain, trust, and generation identities.
Permit a semantic stage to reuse an old result when a named equivalence relation
for that stage has been established, but carry the original and current
identities separately. Never let equality of a derived model silently relabel an
old accepted result as a current Rust-level result.

Basis: Anneal **normative project design** at
`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`,
`anneal/DESIGN.md`, blob
`0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`, plus the published provenance
probe. The reuse architecture is **derived** analysis, not adopted policy.

### Separate semantic and presentation dependencies only when the split pays for itself

The Charon/Aeneas probe shows a real case in which semantic output stayed equal
while provenance changed. rustc and GHC show that projection boundaries can
prevent large downstream invalidations. These facts make a separate semantic
and presentation dependency graph plausible, but not automatically worthwhile.

A split earns its complexity when all of the following are true:

1. semantic/proof recomputation is materially more expensive than updating
   source mappings or presentation state;
2. edits that preserve the semantic projection occur often enough to matter;
3. the semantic projection has a stable, testable contract;
4. presentation/provenance state can be refreshed without mutating the reused
   semantic artifact in ways that invalidate its identity;
5. acceptance can combine current provenance with reused semantic evidence
   without confusing the identity of either.

If these conditions do not hold, a single coarse stage invalidation is easier
to audit and may be faster overall. rustc itself records that fingerprinting has
a meaningful cost, and GHC deliberately uses a coarser ABI hash for package
modules even though finer checks can avoid some recompilation. More reuse is not
free.

A useful initial Anneal shape is therefore a small number of explicit
projections: exact source/build identity, semantic model/obligation identity,
proof-environment identity, and presentation/provenance identity. Finer
projections should be added in response to measured recomputation cost and a
clear sufficiency argument, not because an incremental framework can represent
them.

Basis: **derived** comparative judgment.

### Decision matrix

The following matrix states which cutoff each equality can justify *when its
preconditions hold*. It does not say the relation is always cheaply computable.

| Relation | What it establishes | Safe cutoff examples | What it does not establish |
| --- | --- | --- | --- |
| Exact byte equality | Same captured representation | Reuse immutable artifact bytes; avoid reparsing exact artifact | Same ambient environment; semantic equivalence after different bytes; current source correspondence |
| Normalized syntax equality | Same chosen syntax projection | Skip consumers proven insensitive to erased trivia/ordering/locations | Current spans/provenance; safety for macros/plugins/build inputs not represented by the normalization |
| Interface/ABI equality | Same contract-visible projection | Avoid recompiling/reproving clients restricted to that interface | Equality of private implementation, diagnostics, producer source, or unrelated consumers |
| Query/result equality | Same stage result under its stable representation | Stop downstream invalidation for dependents of that query/projection | Correctness if the query omitted dependencies or stable hashing omitted observable state |
| Observational equivalence | Same behavior for a specified observer set | In principle, any consumer inside that set | A practical generic decision procedure or equality for observers outside the set |
| Claim-relative equivalence | Same evidence-relevant state for a named claim | Reuse proof/model work for that claim while refreshing unrelated state | Permission to relabel stale source/provenance or broaden the claim |

The matrix's central distinction is between **producer identity** and
**consumer-visible equality**. GHC recompiles a changed producer and then uses
interface fingerprints to spare clients. rustc reruns a dirty query and then
uses the result fingerprint to spare dependents. Anneal should preserve that
direction: a coarser downstream cutoff should not become an excuse to skip the
upstream work needed to establish that the coarse projection is still valid.

## Boundaries

This report does not establish that any proposed Anneal model, obligation, ABI,
or canonicalization is currently sufficient for reuse. No new Anneal,
Charon, Aeneas, Lean, rustc, GHC, or Incremental execution was performed.

The Jane Street cutoff API permits application-defined predicates, including
approximate ones. This report does not interpret every use of `set_cutoff` as a
correctness-preserving equivalence. The point is precisely that the application
owns that judgment.

rustc's stable fingerprints are hashes, not mathematical equality. The
development guide records a nonzero collision possibility and treats it as
practically negligible. This report does not upgrade that engineering assumption
into a proof.

GHC's ABI and entity fingerprints are compiler-defined client projections. The
report does not claim that source-compatible, ABI-compatible, and
behaviorally-equivalent Haskell modules are the same relation. Current GHC
source contains special cases for plugins, orphan-like information, bytecode,
dependent files/directories, flags, and other observations that prevent such a
simplification.

The Charon/Aeneas provenance result is a bounded fixture. It does not establish
that arbitrary comments, whitespace, relocations, macro changes, generated
files, or build scripts are semantically inert. Its value here is as a
counterexample to the idea that one raw serialized identity must govern both
model reuse and provenance.

The report assumes a sound dependency closure. A correct equality relation over
the *known* inputs cannot notice a file, environment variable, failed lookup,
directory entry, plugin, clock, or other dependency that the stage failed to
model. J038 addresses that orthogonal failure mode.

“Claim-relative equivalence” is this report's synthesis, not terminology or
policy adopted by rustc, GHC, Jane Street, Charon, Aeneas, Lean, or Anneal. It
is intended to make the acceptance obligation explicit: the relation must be
sufficient for the claim whose work is being reused.

## Evidence

### rustc

Repository:
`rust-lang/rustc-dev-guide@8ae6c255bb0675bbcb8bd0c197e8e70505bd7e85`.

- `src/queries/incremental-compilation.md`, blob
  `079a2b2e00a7f2dd088fab5a4d74541a53659ea1`: red/green query semantics,
  rerunning a query with red inputs, and marking it green when the result hash
  is unchanged.
- `src/queries/incremental-compilation-in-detail.md`, blob
  `9893edd54b950155da586843baa3319da15dcc4e`: stable 128-bit fingerprints,
  collision and hashing-cost caveats, `no_hash`, `eval_always`, and projection
  queries as change-propagation firewalls.
- Rust project blog, Michael Woerister, “Incremental Compilation,”
  2016-09-08: alpha architecture, coarse early dependency granularity, and the
  explicit plan to reduce false-positive invalidation.

Evidence role: first-party **documentation/history**. This report did not inspect
the current `rustc` implementation behind every documented query-engine
mechanism.

### Jane Street Incremental

Repository:
`janestreet/incremental@98b5750ec3c006641351bfd858a89136a5dbc52c`.

- `src/incremental_intf.ml`, blob
  `eabce575943287f144a8f66cf342fd9db438a33e`: stabilization algorithm,
  physical-equality default, configurable cutoff predicate, and float-threshold
  example.
- Jane Street blog, Yaron Minsky, “Introducing Incremental,” 2015-07-18:
  first-party historical account of the library and dynamic self-adjusting
  computation.
- Jane Street blog, “Self Adjusting DOM”: first-party example of projecting a
  larger model into incrementals so unchanged projections cut off downstream
  propagation.

Evidence role: **source/documentation/history**.

### GHC

Repository:
`ghc/ghc@234bab081682018da7d04b22eee4b80f70381d07`.

- `compiler/GHC/Iface/Recomp.hs`, blob
  `cbd1d392ccd3cee37a0c4dd7dc75ec6117a88dc8`: source-hash check for the module
  being compiled; `mi_usages`; package-module ABI hash checking; home-module
  export and per-entity usage checking; interface and declaration ABI
  fingerprint construction.
- GHC 7.0 versioned user guide, “Filenames and separate compilation”: historical
  documentation of interface-file and per-declaration fingerprints used to
  stop recompilation when the things a client used are unchanged.

Evidence role: current **source** plus versioned first-party **documentation**.
The historical documentation is used to establish continuity of the broad
strategy, not byte-for-byte continuity of implementation details.

### Anneal and current reference evidence

Anneal design authority:
`google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

- `anneal/DESIGN.md`, blob
  `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: verification-success identity
  requirements and the requirement that Rust-level claims have justified Rust
  semantics.

Published reference evidence at
`reference@a5ecd5bde3d2b33457b5a13b4b435d79515f4012`:

- `reports/anneal-3731-charon-relocation-comment-provenance-2026-09-29/REPORT.md`,
  blob `1c409aed27a7abe0b7e6feddb199167e95767dcc`: bounded execution showing an
  inert appended comment changed LLBC source contents while generated Lean
  remained byte-identical, and relocation changed provenance/path material
  without changing the translated declaration body after the report's narrow
  normalization.
- Its `REPORT.json`, blob
  `05647fc13e52e758e43a37dffd92bdfd0bf91cf6`, pins Charon
  `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, Aeneas
  `ac9f1bc5262a5e4ff1e24ca78617121382202727`, and Rust
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`.

Evidence role: Anneal **design authority** plus published **execution evidence**.
The claim-relative reuse architecture in this report is derived analysis.

## Revalidation

For another rustc, GHC, or Incremental revision, the cheapest literature
revalidation is to diff the exact mechanisms named above: rustc's result
fingerprinting/red-green/projection-query documentation and implementation;
Incremental's cutoff type and stabilization propagation; and GHC's source-hash,
usage, ABI, and entity-fingerprint checks. A change in hash algorithm is less
important than a change in what information enters the compared projection or
which downstream consumers are allowed to rely on it.

For Anneal, revalidate the judgment with a small matrix of source changes against
the then-current Charon/Aeneas/Lean pins:

1. exact no-op rewrite;
2. whitespace or comment edit that does not move semantic spans;
3. source relocation;
4. private implementation edit that preserves an exported proof obligation;
5. edit that changes an obligation;
6. trust/environment change with unchanged source;
7. presentation-only source-map change with an otherwise equal generated model.

For every cell, preserve and compare separately the exact source snapshot,
build/environment manifest, Charon model, Aeneas/Lean generated semantics,
obligation/theorem statement, proof result, trust record, and source/provenance
mapping. The important assertion is not that two artifacts happened to hash
equal. It is that every skipped downstream stage consumed a projection proven
equal under its declared cutoff, while every changed observation continued down
the dependency path that owns it.

A particularly discriminating acceptance test is the inert-change case already
suggested by the published provenance probe: reuse expensive proof work only
after a fresh translation/correspondence step establishes the same semantic
model for the current source, then verify that diagnostics and the final result
refer to the current source identity rather than the prior generation. If that
cannot be expressed cleanly, Anneal should keep the coarser invalidation boundary
instead of adding a semantic/presentation split.