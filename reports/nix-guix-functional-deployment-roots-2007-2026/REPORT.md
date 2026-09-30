# Nix and Guix: immutable closures, mutable roots, and deployment correctness

## Summary

Nix and Guix separate two concerns that ordinary in-place deployment tends to conflate: **constructing an immutable realization** and **deciding which realization is current**. That separation is the transferable result for Anneal.

Nix's store is not accurately described as one universal content-addressed namespace. Current Nix distinguishes derivation identity, input-addressed outputs, fixed or floating content-addressed outputs, dependency reachability, profiles, and garbage-collector roots. A profile or NixOS generation is a mutable naming/lifetime layer that points at immutable store objects. Switching the current generation and later collecting old generations are separate state transitions. Guix deliberately inherited Nix's low-level build/deployment model and built transactional upgrades, rollbacks, per-user profiles, and garbage collection on top of it.

That architecture makes preparation non-destructive, permits old and new realizations to coexist, and makes rollback cheap **while the old realization remains rooted**. It does not make deployment purely functional end to end. The original NixOS paper explicitly limits the functional model to static state and leaves mutable state such as `/var` outside it. Its activation script mutates the running system. Current NixOS likewise builds a new system before `switch`, then inspects the existing system and applies effectful changes such as service and mount transitions. A store identity therefore does not by itself prove that activation was correct or that all runtime inputs were captured.

For Anneal, the useful design is smaller than Nix or Guix. Prepared Lean/Rust/Aeneas/Mathlib universes should be immutable, explicitly identified generations. Publication should be a small validated transition that changes which generation is authoritative. A generation that is no longer current must remain retained while a live proof session or other consumer can still reference it; after the last lease disappears, it may be reclaimed. The identity of the preparation recipe, admitted upstream assets, realized prepared tree, distributable archive, and active generation should remain distinguishable rather than being collapsed into one hash.

Current Anneal evidence makes those distinctions necessary. Anneal already places many upstream assets behind Nix fixed-output boundaries, but those hashes identify particular acquisition results, not the whole executable universe. Existing reference work also shows that the final omnibus archive is not presently established as byte-reproducible, that copied Rust and Lean trees were exercised outside the store only while `/nix/store` remained available, and that installed read-only state is an accidental-write guard rather than continuous integrity validation. Those are not failures of the Nix pattern; they show where Anneal's own publication and runtime boundary begins.

The conditional judgment is therefore: **borrow immutable realizations, explicit roots, generation switching, and lease-aware reclamation; do not import a general functional package manager unless Anneal's workload demonstrates the need for one**. A small generation manager plus explicit artifact identities is sufficient while Anneal has a modest, mostly fixed preparation graph. A Nix-like general derivation/store engine becomes more attractive only if Anneal acquires many independently reusable artifacts, dynamic closure composition, distributed substitution, cross-user cache sharing, or enough rebuild/garbage-collection complexity that bespoke orchestration begins reimplementing those semantics.

## Applicability

This report addresses issue #3732 J046, **Nix and Guix: immutable closures, mutable roots, and deployment correctness**. It is a design-history and architecture report, not a recommendation that Anneal depend on Nix or Guix at runtime.

The Nix historical account uses Dolstra and Hemel's 2007 HotOS XI paper to reconstruct the rationale for functional system deployment and the original boundary between immutable static configuration and mutable runtime state. Claims about current Nix profile, garbage-collection, derivation-output, and NixOS switching behavior use the Nix 2.35.2 reference manual and the current stable NixOS manual observed on 2026-09-30. Where those current documents differ in terminology from the 2007 paper, the current documentation controls the report's account of present behavior.

The Guix account uses Ludovic Courtès's 2013 European Lisp Symposium paper for the project's original package-management architecture: transactional upgrades and rollbacks, per-user profiles, garbage collection, and reuse of Nix's lower-level build/deployment layer. The 2026-01-23 Guix 1.5.0 release announcement establishes that this is a current system and preserves the project's high-level reproducibility/deployment goal. This report does not infer unexamined 2026 Guix implementation details from the 2013 paper.

The Anneal comparison is bound to `google/zerocopy` main revision `cc135f46155b72e4b51188525c2974a3b84acf92` for `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`, and to reference revision `30b9d5749aed6049d949f4f582dd64c70088d07a` for adjacent Nix/toolchain evidence. Those project documents require precise success semantics, justified source/model correspondence, compositional verification, explicit and shrinkable trust, and minimally sufficient mechanisms. The Anneal implications below are **derived design analysis** under those constraints. They are not an adopted architecture and do not override the project's deliberate non-decisions about component boundaries, artifact schemas, or validation strategy.

The phrase **immutable realization** in this report means a prepared filesystem/store object or generation whose content is not mutated in place after admission. It does not imply that the object's store path is necessarily a hash of its contents. Current Nix explicitly supports both input-addressed and content-addressed derivation outputs. Likewise, **closure** means the graph of referenced store objects reachable from a root; it does not mean that all ambient host state, runtime plugins, network state, secrets, or application data have been captured.

## Findings

### Functional deployment separates realization from activation

The 2007 NixOS paper begins from a failure mode of imperative deployment: packages and configuration are updated in place, so the result depends on prior mutable state and old configurations are overwritten. Its replacement model builds static artifacts as immutable store values. A new system configuration is built alongside the old one; a top-level system object contains an activation script that makes that configuration current. Because the old store objects remain intact, the system can roll back to an earlier configuration as long as those objects have not been garbage-collected.

That is a stronger and more useful statement than “Nix is reproducible.” Preparation and activation have different semantics:

- preparation constructs a candidate realization without destroying the current one;
- activation changes which realization controls boot/runtime behavior;
- retention determines which earlier realizations remain available for rollback.

Current NixOS preserves the same separation. `nixos-rebuild switch` builds a configuration, makes it the boot default, and then attempts to realize it in the running system. `nixos-rebuild test` can activate a built configuration without making it the boot default. Rollback selects a previous generation that remains available.

For Anneal, this maps directly to preparing a complete tool/proof universe before publication. Building or validating a candidate generation should not mutate the generation currently serving proof work. Publication should be an explicit state transition after validation, not the last incidental side effect of the build.

Basis: **documentation** (2007 NixOS paper; current NixOS manual) + **derived** Anneal mapping.

### Derivation identity, output identity, closure, and current generation are different objects

The 2007 paper described ordinary Nix store paths in terms of a hash of build inputs. Current Nix has a more precise taxonomy. A derivation is a build-step specification whose own encoded store object is content-addressed. Its outputs may be **input-addressed** or **content-addressed**; content-addressed outputs may in turn be fixed or floating. The current Nix manual therefore explicitly warns against treating all derivation outputs as one form of content-addressed object.

A realized output also has references to other store objects. The transitive set reachable from those references is its closure. That closure is a dependency/liveness relation, not the same thing as the derivation recipe or output address.

Profiles add another layer. Nix 2.35.2 documents a profile as versioned links: a mutable profile link selects one generation link, and that generation points into the store. NixOS system generations use the same basic idea at system scale. The current pointer can move while the underlying store objects remain immutable.

This yields at least five identities that a verification system should avoid collapsing:

1. the **recipe/configuration identity** that describes how to prepare a result;
2. the **admitted upstream-input identity**, such as a fixed-output hash;
3. the **realized prepared-universe identity** or manifest;
4. the **distribution/archive identity**, if the universe is serialized or transformed for transport; and
5. the **active-generation identity** that says which prepared universe is authoritative now.

Anneal's current reference evidence already demonstrates why this matters. Its fixed-output derivations constrain several upstream trees and archives, but the final omnibus archive undergoes later transformations and is not currently established as one canonical byte string. A fixed-output acquisition hash is therefore not automatically the final archive identity or the active installation identity.

Basis: **documentation** (Nix 2.35.2 derivation/profile model) + **reference evidence** + **derived** identity decomposition.

### Rollback depends on retention, not merely immutability

Immutable old outputs make rollback possible only while those outputs remain reachable. Nix 2.35.2 garbage collection deletes store objects that are not reachable from a root. Profiles are roots, and deleting old profile generations may make more store objects collectible. The manual explicitly notes that deleting previous configurations makes rollback to them impossible.

This makes the garbage-collector root set part of the deployment correctness model. A root is not just a storage-management implementation detail: it records which historical realizations the system promises to keep usable.

The closest Anneal analogue is a live session or job that began against generation `G`. Publishing generation `G+1` should not invalidate the old session by reclaiming `G` underneath it. A safe lifecycle is:

1. publish `G+1` as current;
2. keep `G` rooted while any session, transaction, or externally visible result can still depend on it;
3. drop the root only after the last such reference is gone; and
4. reclaim `G` only when it is both non-current and unreferenced.

A bounded recent-history policy can coexist with this rule, but it cannot override live leases. Conversely, keeping every historical generation forever would reproduce the Nix model's documented disk-space cost without a corresponding correctness need.

Basis: **documentation** (Nix 2.35.2 GC roots, garbage collection, profiles) + **derived** lifecycle judgment.

### Immutable static state does not eliminate mutable deployment state

The original NixOS authors explicitly draw the boundary. The functional model applies to static software and configuration, while mutable state such as most of `/var` lies outside it. They call out `/etc/passwd` as a mixed static/mutable case: the activation script can ensure configured accounts exist, but the update depends on prior file contents and is therefore stateful.

Current NixOS still has an effectful activation step. During a switch it inspects the currently running system, including current systemd state and `/etc/fstab`, then computes and performs changes such as service or mount transitions. Building the target system closure does not itself establish that these transitions succeeded or that all application data is compatible with the new generation.

The same limit matters for Anneal. A prepared Lean/toolchain universe may be immutable while the following remain mutable or ambient:

- the source buffer or workspace being verified;
- generated scratch files;
- environment variables and process settings;
- external package/plugin state loaded after preparation;
- network-visible resources;
- host libraries or executables not actually captured by the prepared closure;
- long-lived compiler/prover processes retaining state from an earlier generation; and
- publication metadata that says which generation is current.

The deployment analogy is therefore useful precisely because it tells Anneal what **not** to infer. Immutability of prepared bytes is strong evidence against in-place drift. It is not a proof that the runtime environment, source/model correspondence, semantic inputs, or activation transaction are correct.

Basis: **documentation** (2007 NixOS paper; current NixOS switching description) + **derived** Anneal boundary.

### Guix shows that transactional user-facing deployment can be built on a lower-level immutable store model

Courtès's 2013 Guix paper describes Guix as a functional package manager that builds on Nix's low-level build and deployment layer while adding a Scheme programming interface. Its stated deployment properties include transactional upgrades and rollbacks, unprivileged package management, per-user profiles, and garbage collection. The design deliberately separates the user-facing package/configuration language from the lower-level store/deployment substrate.

That historical division is useful for Anneal because it argues against making one component own every layer. Anneal can have a small substrate responsible for prepared-generation identity, retention, and publication while allowing higher-level policy to decide what should be prepared and when. The higher layer may be expressive or even executable without acquiring direct authority to mutate published state.

Guix also illustrates a cost of expressive configuration. Its package descriptions and build programs are Scheme code. Executable configuration can be convenient and compositional, but its semantic inputs are broader than a small declarative record unless the execution environment is itself tightly controlled. For Anneal, arbitrary preparation hooks or plugin code should therefore be treated as execution whose inputs and effects must be captured, isolated, or explicitly trusted—not as inert configuration merely because it participates in generation construction.

The Guix 1.5.0 release announcement on 2026-01-23 describes the current project in the same broad terms: reproducible computing environments that can be deployed over time and across devices. This confirms continuity of the project's high-level purpose, not byte-for-byte continuity of the 2013 implementation.

Basis: **documentation** (Guix 2013 paper and 2026 release announcement) + **derived** Anneal layering judgment.

### Content addressing is useful evidence, but it is not a universal correctness oracle

A content address answers a narrow question: whether a store object's bytes/tree match an expected content identity under the chosen addressing method. An input-addressed output instead identifies the result through the derivation that produced it. Neither identity by itself proves provenance, semantic suitability, source/model correspondence, or correct activation.

Anneal's current reference corpus already records a concrete version of this distinction. The Nix fixed-output report finds that Anneal uses expected hashes to admit upstream archives and synthesized trees. It also states that those hashes are integrity/reproducibility gates, not publisher-authentication or semantic-correctness proofs. The archive-reproducibility report then finds that the later omnibus tar construction is not currently established as byte-canonical. These two observations are compatible: a pipeline can strongly identify particular inputs without thereby giving every later representation one universal hash identity.

For Anneal, the practical consequence is to use the strongest identity available for each boundary rather than inventing one master digest. A prepared-generation manifest can name:

- source revision or source snapshot identity;
- translator/prover/tool revisions;
- fixed-output or content identities for admitted upstream assets;
- configuration and feature identities;
- the realized prepared-tree identity when available;
- archive/package identity when distributed;
- host/runtime assumptions that remain external; and
- the generation ID that publication made current.

A later proof result can then bind to the prepared generation and its manifest. This is more auditable than treating “same cache hash” or “same archive” as a synonym for “same verification environment.”

Basis: **documentation** + **current Anneal reference evidence** + **derived** identity policy.

### Prepared-universe closure must be defined by the property Anneal wants to claim

Nix's store closure is based on declared and discovered references between store objects. That is enough for Nix's store consistency and deployment machinery, but it does not prove that an arbitrary program has no undeclared semantic dependency on the host. The 2007 paper's model already acknowledges pragmatic exceptions and mutable external state; current Nix derivations also rely on explicit input specifications and purity rules that the derivation creator must honor.

Anneal therefore needs a **claim-relative closure**, not merely a filesystem closure. If the promise is that a verification result corresponds to a particular Rust program under a particular translator/prover/toolchain environment, then every input that can materially change that relation must be either:

- captured and named in the generation identity;
- reconstructed from something captured and named;
- independently validated at use time; or
- exposed as a trusted external assumption in the result's TCB/provenance.

Runtime-loaded plugins, compiler extensions, arbitrary environment variables, native libraries found through host search paths, network content, and source buffers are examples of state that can escape a prepared tree unless Anneal deliberately brings them inside this boundary.

This is where Anneal's design contract is stricter than a package manager's ordinary deployment goal. A package manager can successfully activate a program even if the program later reads mutable application data. Anneal cannot claim that a proof applies to a program/model pair if an unrecorded input can change the model or obligations used for that proof.

Basis: **documentation** (Nix derivation input model) + **Anneal design contract** + **derived** claim-relative closure analysis.

### Current Anneal packaging is already close to the immutable-realization half of the pattern

Existing `reference` reports show three relevant properties of Anneal's current toolchain work.

First, the flake uses fixed-output boundaries for important upstream assets. This gives Anneal explicit identities for several externally acquired inputs before later ordinary derivations transform them.

Second, a relocation probe copied the Nix-built Rust and Lean fixed-output trees outside `/nix/store`, preserved their NAR hashes and path inventories, and successfully exercised selected tools on `aarch64-darwin`. The original store remained mounted, so the experiment does not establish a completely self-contained relocated closure. It does show that immutable prepared trees can be treated as concrete artifacts rather than ephemeral build directories.

Third, Anneal's archive/install evidence deliberately keeps mutable generated work outside the read-only installed toolchain tree. The installed tree's read-only bits are not a security boundary, and existing installations are not continuously revalidated, but the structural split is the right one: stable prepared dependencies on one side, per-workspace mutation on the other.

The missing J046 layer is therefore not “make Anneal use immutable artifacts.” Much of that direction is already present. The missing architectural decision is how those artifacts become **generations with explicit publication and lifetime semantics** rather than merely products of a packaging pipeline.

Basis: **current Anneal reference evidence** + **derived** synthesis.

### A small generation manager is a better default than a general Nix-like engine

Nix and Guix solve problems substantially larger than Anneal's current preparation problem: large software graphs, many users, arbitrary package definitions, distributed substitutes, system deployment, profile history, and garbage collection over a shared global store. Their generality is costly but justified by that domain.

Anneal can capture the most valuable semantics with a much smaller abstraction:

- **PreparedGeneration**: immutable manifest plus prepared artifact roots.
- **CurrentGeneration**: one atomically readable/publishable pointer or version record.
- **Lease/Pin**: a live reference held by a session, job, result under construction, or rollback policy.
- **Publish(candidate)**: validates the complete candidate identity and then atomically moves `CurrentGeneration`.
- **Retire(generation)**: marks a non-current generation eligible for collection after the last lease disappears.
- **Collect()**: deletes only generations that are neither current nor leased/pinned.

The preparation graph behind `PreparedGeneration` can initially be an ordinary DAG or explicit sequence. Anneal does not need a general evaluator, derivation language, or global content-addressed store merely to obtain non-destructive generation construction and safe publication.

This judgment should change if measured requirements accumulate: many independently reusable intermediate artifacts; dynamic dependency/closure discovery; distributed build substitution; cross-project or cross-user cache sharing; sophisticated partial rebuilds; or recurrent bugs in home-grown identity/retention logic. At that point, adopting a mature store/build abstraction may reduce rather than increase complexity.

Basis: **derived** comparison against Nix/Guix scope and Anneal's current design constraints.

### Alternatives preserve different subsets of the result

Several simpler or differently scoped designs are serious alternatives.

**Overwrite-in-place installation** has the least machinery. It also weakens rollback and makes readers vulnerable to partially updated state unless the update is carefully staged and swapped. It is reasonable only if Anneal can tolerate invalidating all consumers and can cheaply rebuild after failure.

**Immutable content-addressed blobs without a derivation model** preserve artifact identity, deduplication, and non-destructive publication while omitting a general build language. This may be the best implementation shape for Anneal if its preparation process stays small. The cost is that build provenance and dependency explanations must live in an explicit manifest rather than being supplied by a derivation graph.

**Lockfiles plus mutable installation directories** capture versions with low conceptual cost but allow post-install drift unless the installation is revalidated. They also make rollback and concurrent readers harder because “the toolchain directory” has one mutable meaning.

**Containers or VM images** can capture more operating-system state than a package-store closure and provide stronger process isolation. They are coarser and more expensive, and runtime secrets, network services, host kernel behavior, or mounted workspaces can still remain outside the image identity. They solve a different boundary than immutable generation publication.

The right choice is therefore not “most hermetic representation wins.” Anneal should pick the smallest mechanism that captures the semantic inputs its verification claims depend on and gives publication/lifetime transitions explicit, checkable meaning.

Basis: **derived** design comparison.

## Boundaries

**No fresh Nix or Guix execution.** This report relies on current official Nix/NixOS documentation, historical primary literature, the Guix release announcement, and already-preserved Anneal execution/reference evidence. It does not contain a new Nix profile switch, garbage-collection probe, Guix transaction, or Anneal packaging build.

**No claim that every Nix output is content-addressed.** Current Nix documents both input-addressed and content-addressed derivation outputs. The derivation encoding itself is content-addressed, but that does not make all outputs content-addressed.

**The 2007 NixOS paper is historical evidence.** Its specific service manager, package counts, path hashing description, and implementation details are not treated as current NixOS behavior where current documentation exists. It is used chiefly for architecture rationale and the original static/mutable-state boundary.

**The 2013 Guix paper is historical evidence.** It establishes the intended layered architecture and original deployment properties. This report does not claim that every implementation mechanism described there remains unchanged in Guix 1.5.0. The 2026 release announcement establishes current project continuity only at a high level.

**No universal hermeticity claim.** A Nix or Guix store closure is not evidence that arbitrary runtime behavior has no host, network, plugin, secret, kernel, or mutable-data dependencies. Whether such state matters depends on the claim being made.

**No conclusion that Anneal's final omnibus archive has a canonical byte identity.** Existing reference evidence says the opposite for the examined revision. A future packaging change could establish one, but it must be separately validated.

**No conclusion that Anneal's copied toolchain trees are independent of `/nix/store` on all hosts.** The recorded `aarch64-darwin` relocation probe kept the original store mounted and did not test the complete Aeneas/Charon/Mathlib workflow.

**No conclusion that read-only installed toolchains are tamper-proof.** Existing reference evidence characterizes the permission scheme as an accidental-write guard, not a security boundary or continuous integrity check.

**No adopted lease protocol.** The proposed current/leased/retired generation lifecycle is derived architecture analysis. The exact ownership mechanism, atomicity primitive, rollback window, on-disk layout, and process/session API remain design choices.

**Disk and cache costs are not measured for Anneal.** The NixOS paper documents the general storage cost of retaining immutable closures, but this report has no Anneal-specific measurement of generation size, churn rate, lease duration, or deduplication opportunity.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-30 unless otherwise noted.

### Nix and NixOS

- Eelco Dolstra and Armijn Hemel, *Purely Functional System Configuration Management*, HotOS XI, 2007: `https://www.usenix.org/legacy/event/hotos07/tech/full_papers/dolstra/dolstra_html/`.
  - Architecture rationale for immutable static configuration and non-destructive realization.
  - Top-level system object with activation script and rollback while old configurations remain uncollected.
  - Explicit statement that mutable state such as most of `/var` lies outside the purely functional model.
  - `/etc/passwd` as a mixed static/mutable example whose activation remains stateful.
  - Storage-cost discussion for retained immutable closures.
- Nix 2.35.2 Reference Manual, **Profiles**: `https://nix.dev/manual/nix/2.35/command-ref/files/profiles.html`.
  - Versioned profile links and current-generation indirection.
- Nix 2.35.2 Reference Manual, **Garbage Collector Roots**: `https://nix.dev/manual/nix/2.35/package-management/garbage-collector-roots`.
  - Roots retain their referenced store paths and dependencies.
- Nix 2.35.2 Reference Manual, **nix-store --gc**: `https://nix.dev/manual/nix/2.35/command-ref/nix-store/gc.html`.
  - Reachability from roots defines live/dead store objects.
- Nix 2.35.2 Reference Manual, **nix-collect-garbage**: `https://nix.dev/manual/nix/2.35/command-ref/nix-collect-garbage.html`.
  - Profiles are GC roots; deleting old generations can make rollback impossible.
- Nix 2.35.2 Reference Manual, **Store Derivation and Deriving Path**: `https://nix.dev/manual/nix/2.35/store/derivation/index.html`.
  - Derivations specify build steps and explicit inputs; encoded derivation store objects are content-addressed.
- Nix 2.35.2 Reference Manual, **Derivation Outputs and Types of Derivations**: `https://nix.dev/manual/nix/2.35/store/derivation/outputs/index.html`.
  - Current distinction between input-addressed and content-addressed outputs and fixed/floating addressing.
- NixOS stable manual observed 2026-09-30: `https://nixos.org/manual/nixos/stable/`.
  - `nixos-rebuild switch`, `test`, rollback, current-system inspection, and effectful service/mount switching.

Evidence roles: **documentation**. The HotOS paper is also primary author evidence for original design intent and historical implementation.

### Guix

- Ludovic Courtès, *Functional Package Management with Guix*, European Lisp Symposium 2013, arXiv:1305.4584v1, submitted 2013-05-20: `https://arxiv.org/abs/1305.4584`.
  - States Guix's transactional upgrades/rollbacks, per-user profiles, garbage collection, and dependence on Nix's lower-level build/deployment layer.
  - Describes Scheme as the package/build programming interface.
- GNU announcement, **guix-1.5.0 released [stable]**, 2026-01-23: `https://lists.gnu.org/archive/html/info-gnu/2026-01/msg00004.html`.
  - Establishes the current stable release and continuing reproducible/deployable-environment goal.

Evidence roles: **documentation**. The 2013 paper is primary author evidence for original design; the 2026 announcement is current release evidence, not a source-level architecture audit.

### Anneal design constraints

At `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`:

- `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`.
- `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`.

These establish the promise-oriented constraints under which the Nix/Guix analogy is interpreted: precise successful-result meaning, faithful Rust/model connection, compositional abstraction, explicit/shrinkable trust, and minimally sufficient mechanisms.

Evidence role: **source**.

### Current Anneal reference evidence

At `google/zerocopy` reference revision `30b9d5749aed6049d949f4f582dd64c70088d07a`:

- `reports/anneal-nix-fixed-output-downloads-main-41f5b37/REPORT.md`, blob `5f5142381dca9d2c38dbcde41c6d0f77d15b1f7a`.
  - Upstream archive/tree acquisition behind fixed-output identities; hashes are integrity/reproducibility gates rather than provenance or semantic-correctness proofs.
- `reports/anneal-nix-toolchain-tree-relocation-aarch64-darwin-2026-09-27/REPORT.md`, blob `262a141a145a2532745aaad71289896b5b3af1b2`.
  - Rust/Lean fixed-output trees copied outside the store and exercised on `aarch64-darwin`, with the original store still available.
- `reports/anneal-omnibus-archive-byte-reproducibility-main-41f5b37/REPORT.md`, blob `3bf9a589b81b0fdba5648b78a0b7a3dba842ecf9`.
  - Final omnibus archive not currently established as byte-reproducible despite pinned/materialized inputs.
- `reports/anneal-archive-read-only-behavior-main-41f5b37/REPORT.md` at the same reference revision.
  - Read-only packaged payload as an accidental-write guard; mutable generated workspace separate; existing installation not continuously revalidated.

Evidence role: **reference evidence** assembled from prior source/execution investigations. This report uses those observations rather than rerunning the experiments.

### Derived analysis

The proposed Anneal generation/lease/publication model, the five-way identity separation, the claim-relative closure requirement, and the recommendation against prematurely adopting a general Nix-like evaluator/store are **derived** from the sources above plus Anneal's design contract. They are not statements made by Nix, Guix, or current Anneal source.

## Revalidation

For a future Anneal design or packaging revision, the cheapest reliable revalidation is to test the boundaries separately rather than rerun the whole literature review.

1. **Identity:** inventory every identifier used for source/configuration, admitted upstream assets, prepared trees/manifests, distributed archives, and the current published generation. If one identifier is being used for multiple distinct roles, reconstruct whether the equivalence is actually justified.
2. **Preparation:** build two generations side by side and verify that preparing the second cannot mutate the first or the current-generation pointer.
3. **Publication:** stage a complete candidate, fail validation intentionally, and confirm the current generation does not change. Then publish a valid candidate and verify the transition by readback.
4. **Reader lifetime:** start a long-lived consumer on generation `G`, publish `G+1`, run collection, and confirm `G` remains usable until that consumer releases its lease. Then release it and confirm `G` becomes collectible under policy.
5. **Closure completeness:** run the prepared universe in an environment where undeclared host dependencies are absent or deliberately perturbed. Record every discovered runtime dependency rather than assuming store/filesystem closure equals semantic closure.
6. **Archive/install distinction:** if Anneal relies on a final archive digest, rebuild independently and compare bytes under the claimed conditions. If it relies on a prepared-tree manifest instead, validate the extracted tree against that manifest on every trust boundary where mutation could occur.
7. **Mutable workspace separation:** confirm generated proof/source state is written only to an explicitly mutable workspace and that changing it cannot mutate the shared prepared generation.

Revisit the architectural judgment—not just the implementation—if Anneal develops many independently reusable intermediate artifacts, dynamic dependencies, distributed substitution, cross-user cache sharing, or retention/rebuild complexity that makes a general derivation/store engine cheaper to reason about than the small generation manager proposed here.