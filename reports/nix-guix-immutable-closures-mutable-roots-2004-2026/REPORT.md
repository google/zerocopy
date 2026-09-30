# Nix and Guix: immutable closures, mutable roots, and deployment correctness

## Summary

Nix and Guix make a strong architectural separation that is directly useful to Anneal: immutable realized objects can be given stable identities and shared freely, while a much smaller mutable layer selects which immutable generation is current and which generations remain live. That separation makes upgrades, rollback, coexistence, and garbage collection tractable. It does **not** make deployment or execution purely immutable. Activation still mutates a running machine, live consumers can outlast the generation that launched them, garbage collection needs roots that reflect those consumers, and reproducibility depends on whether every material input was actually captured by the functional model.

The most important transfer to Anneal is therefore not “use Nix hashes” or “make the prepared Lean directory immutable.” It is to separate four kinds of identity and authority that are easy to conflate:

1. **recipe/provenance identity** — what source, configuration, toolchain, dependency, and preparation inputs were requested;
2. **realized-output identity** — which exact prepared artifacts were produced;
3. **publication identity** — which validated realization a mutable project/session root currently names; and
4. **lifetime roots or leases** — which older realizations must remain available because a rollback point or live consumer still depends on them.

Nix itself shows why the first two must remain distinct. Traditional input-addressed derivation outputs are identified by the way they were produced, while content-addressed outputs are identified by realized content. The current manual explicitly models deriving paths separately from store paths when an output's eventual store identity is not yet known. A single “generation hash” in Anneal would therefore be underspecified unless its role is explicit.

NixOS and Guix also show why an immutable closure is not a complete deployment-correctness argument. NixOS builds a system closure, then `switch-to-configuration` inspects the *current* machine, executes activation code, and stops, reloads, restarts, or starts services. Current NixOS source makes `/run/current-system` a garbage-collection root only after activation code runs. Guix likewise provides transactional generations and garbage-collected store objects, but its operational model includes a mutable current generation and system reconfiguration. The functional package graph gives a strong answer to “which immutable artifacts belong together”; it does not, by itself, answer “which live process is using which generation,” “did arbitrary executable configuration observe undeclared host state,” or “are two environments semantically equivalent for this verifier.”

For Anneal, the defensible conditional design is therefore a **prepared-universe object plus a small mutable publication/lifetime layer**. Preparation should produce a self-describing manifest that records the source/configuration/toolchain inputs Anneal intends to bind, the realized artifacts and dependency closure it actually produced, and the host/runtime assumptions that remain outside that closure. Publication should atomically select only a previously validated realized universe. Live Lean/LSP/translation workers should be pinned to a generation or lease rather than implicitly following “current.” Retired universes should be reclaimable only after both rollback policy and active-consumer leases permit it.

This remains insufficient when configuration or execution can escape the captured world. Lake configuration, plugins, native libraries, environment variables, host tools, network access, dynamically discovered files, or long-lived foreign processes can all make the effective environment larger than the immutable directory Anneal prepared. Those inputs must be prohibited, sandboxed, captured into identity, or admitted explicitly into the trusted assumptions. Nix and Guix are strongest precedents for **making the closure boundary explicit**; they are not evidence that every useful execution environment is automatically closed.

## Applicability

This report addresses #3732 J046: whether the functional-deployment lineage represented by Nix and Guix gives Anneal a useful model for prepared Lean universes, publication, rollback, and lifetime management.

The historical Nix evidence begins with Dolstra, de Jonge, and Visser's 2004 LISA paper, which framed unsafe deployment as a dependency-identification and coexistence problem and introduced cryptographically distinguished component paths. Dolstra's 2006 dissertation generalized this into the “purely functional software deployment model.” Current Nix behavior is pinned to `NixOS/nix@9bc9ab32a57504f068847af4f8013417476cb1ec`; the report uses that revision's profile, garbage-collection, derivation, and store-object documentation rather than assuming the 2004 mechanism is unchanged.

The operational NixOS evidence is pinned separately to `NixOS/nixpkgs@6cb205c37b7c0c39b643163d1b7721b5f9bc0913`. That distinction matters: the Nix store/profile model and a NixOS system switch are related but not identical abstractions. Current NixOS documentation and source explicitly expose an imperative activation phase and reconciliation with current systemd and mount state.

For Guix, the historical anchor is Ludovic Courtès, “Functional Package Management with Guix,” ELS 2013, arXiv:1305.4584. It states that Guix builds on Nix's low-level build/deployment layer while adding Scheme as the package/build programming interface, transactional upgrade/rollback, per-user profiles, and garbage collection. Courtès and Ricardo Wurmus's 2015 Euro-Par workshop paper, DOI `10.1007/978-3-319-27308-2_47`, is used as an author-reported account of reproducible user-controlled environments, not as proof that all host/platform effects are captured. Current Guix operational behavior is taken from the GNU Guix Reference Manual as observed on 2026-09-30. GitHub's `guix-mirror/guix` repository is not used as current source authority: its own current README states that the mirror has been out of service since December 2023 and directs users to the upstream Codeberg repository.

Anneal's normative comparison point is `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, especially `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`. Those documents require verification results to have enough identity and scope for their promises to be meaningful, require trust to remain explicit, and deliberately leave the exact component and verification-subject boundaries unresolved. Current reference evidence is observed at `google/zerocopy` `reference@30b9d5749aed6049d949f4f582dd64c70088d07a`. Existing reference reports already examine Anneal's Nix fixed-output acquisition, toolchain relocation, archive reproducibility, and installed Lean/Lake inventory. J046 is complementary: it asks what the *deployment architecture* implies about identity, activation, roots, and long-lived consumers.

## Findings

### Functional deployment separates immutable realizations from mutable selection

The 2004 Nix paper's motivating problem was not merely reproducible compilation. It emphasized safe dependencies, simultaneous versions, atomic upgrades/downgrades, and safe garbage collection. The core trick was to place component instances at unique paths derived from their inputs so incompatible or independently produced instances do not overwrite one another.

Current Nix profiles preserve the same high-level separation. Store objects live at immutable-looking unique store paths. A user environment is itself a store object containing links to the selected packages. Each profile generation is an external symlink to one such user environment, and the profile's current pointer is another symlink to the selected generation. Updating the current symlink is the small mutable act that selects an otherwise immutable generation. Old generations remain available for rollback.

That architecture matters more than the specific use of symlinks. It allows “prepare” and “publish” to have different failure modes. Building a new store closure can fail without disturbing the current profile. Only after the new realization exists does the mutable selection step make it current. Anneal can use the same separation even if its representation is a manifest plus directories rather than a Nix store.

A useful Anneal analogue is:

- **prepare:** construct and validate a candidate universe without changing the current one;
- **publish:** atomically update a small generation pointer or mapping after validation;
- **consume:** bind each worker/session to the selected generation identity, not to a path whose meaning can change underneath it; and
- **retire:** remove a generation from future selection without destroying it while rollback policy or active consumers still require it.

The key property is not that every byte is immutable forever. It is that mutation of “what is current” is explicit, small, and separable from constructing the thing that may become current.

### Derivation identity and output identity are different questions

A common shorthand says a Nix store path “is the hash of the package.” Current Nix documentation makes the real model more nuanced.

For an **input-addressed derivation output**, the output's store path is a function of the derivation that produced it — the *way it was made* — rather than its realized byte contents. Two byte-identical outputs produced through different input-addressed recipes can therefore have different store identities. Current Nix also supports **content-addressed outputs**, where the realized content participates in determining the output store identity. Its derivation model consequently distinguishes a *deriving path* (“the output of this derivation”) from a concrete store path; for floating content-addressed output, the latter may not be known until the build is realized.

This history is directly relevant to Anneal because a prepared universe has at least two useful identities:

- the **requested preparation**: selected Rust subject, Aeneas/Charon/Lean revisions, Lake/project configuration, dependency-resolution inputs, feature choices, target/platform assumptions, and preparation implementation/version; and
- the **realized universe**: the actual generated sources, compiled artifacts, manifests, native objects, plugins, caches, and other files that the verifier will consume.

Conflating these loses useful information. A recipe identity can explain provenance and cache eligibility even when non-determinism or an undeclared input makes two realizations differ. A realized identity can establish equality of captured artifacts without proving that the recipe was complete or that uncaptured ambient inputs are irrelevant. Anneal should record both when both matter.

This also argues against using successful preparation or import as an all-purpose identity oracle. “This recipe successfully produced a universe” is weaker than “this is the same realized universe,” which is weaker again than “all behavior-relevant environment inputs are equal.”

### A dependency closure is only as complete as the dependency model

Nix garbage collection operates on explicit reachability. Current documentation says store paths reachable directly or indirectly from garbage-collector roots are live; other paths can be collected. The default profile generations are roots, and explicit GC roots can be added. `keep-derivations` and `keep-outputs` alter how build-time and runtime dependencies of roots are retained.

This produces an important conditional guarantee: if a runtime dependency is represented by the store-reference graph and the root set correctly represents intended liveness, garbage collection preserves it. It does not prove that an arbitrary program's every semantically relevant dependency was represented in that graph.

The same distinction appears in Anneal's current Nix-related reference evidence. `anneal-nix-toolchain-tree-relocation-aarch64-darwin-2026-09-27` copied Lean and Rust fixed-output trees outside `/nix/store`, preserved their NAR hashes, and successfully ran smoke programs from the copies. But the report explicitly stops short of claiming store independence because `/nix/store` remained available and an uninspected runtime dependency could still have resolved from it. That negative space is exactly J046's lesson: artifact closure and execution closure are separate claims.

For a prepared Lean universe, likely escape hatches include:

- executable Lake/Lean configuration that reads environment variables, the filesystem, or process state;
- dynamically loaded Lean or native plugins;
- native shared libraries found through host loader rules;
- tools found through `PATH` or absolute host paths;
- network-fetched or externally cached data;
- generated files or package roots discovered after the manifest was formed; and
- long-lived helper processes that preserve state from an earlier generation.

If Anneal wants a prepared-universe identity to support a verification claim, each behavior-relevant escape must be handled deliberately: include it in the manifest/identity, mediate it through a controlled service, sandbox it away, validate its output before use, or retain it as an explicit trusted assumption. Merely placing the visible files in an immutable directory does not close the world.

### Profiles and generations solve rollback selection, not live-consumer lifetime by themselves

Nix's profile model keeps old generations because rollback needs them. Garbage collection becomes effective only after old generations are deleted. This already demonstrates that “not current” does not mean “safe to delete.”

Nix also has a second liveness problem: programs can continue running after the profile or generation that launched them stops being current. Nix has long treated open files/running programs as possible runtime roots, and current Nix includes a roots-daemon mechanism for environments where the main daemon cannot discover runtime roots by scanning `/proc`. This is a separate mechanism from the profile's current-generation pointer.

That distinction maps cleanly to Anneal. A GUI/editor session, Lean language-server process, translation worker, or proof process may have loaded files, modules, native libraries, or in-memory state from generation G. Publishing G+1 must not silently turn that existing process into a G+1 consumer. Nor is it necessarily safe to delete G merely because the global current pointer moved.

Anneal therefore needs an explicit answer to two independent questions:

- **Selection:** Which generation should a newly started operation use?
- **Lifetime:** Which generations must remain available because existing operations still depend on them?

The smallest robust mechanism is a generation-pinned session plus a lease/refcount/root on the corresponding universe. Publishing changes the selection root for new work. Existing work either remains pinned to its old generation until it exits, or performs an explicit migration/restart that obtains a new generation. Reclamation occurs only after policy roots (for example the last N rollback points) and active leases are both gone.

This model also gives stale-result handling a precise basis. Results should carry the generation they actually used. The caller can then decide whether a result from G remains useful after G+1 became current rather than silently treating “latest now” as “the inputs this computation saw.”

### Activation is a state transition, not merely choosing an immutable closure

NixOS exposes the limit of a purely functional description particularly clearly. A system configuration is built as an immutable Nix output, but `nixos-rebuild switch` does more than repoint a profile. Current NixOS documentation says the switch machinery inspects the running system's mount and systemd state, computes actions, stops units, runs the activation script, may restart systemd, reloads or restarts units, starts new units, and reports failures.

Current `activation-script.nix` is explicit about this imperative boundary. Activation snippets update `/etc`, create accounts, mount filesystems, and perform other host mutations; they are required to be idempotent and fast because they run at boot and system switch. After the activation snippets, the script updates `/run/current-system` to the selected store path, and NixOS arranges a GC root for that current-system path.

This is not a defect in NixOS. It is the consequence of applying an immutable desired-state artifact to a mutable running world. But it means the correctness of the realized store closure is not identical to the correctness of activation. A failed, partial, or semantically inadequate activation can leave a live system in a state that cannot be inferred from the immutable path alone.

Anneal should preserve this distinction. If “preparing a Lean universe” includes only constructing immutable artifacts, then preparation can be a mostly functional operation. If making a universe usable requires mutating shared indexes, symlinks, caches, editor state, sockets, daemons, or other ambient resources, those mutations are a separate activation/publication protocol and need their own atomicity, failure, and recovery semantics.

The safest default is to minimize activation: prepare everything under a fresh generation-owned location, validate it there, then publish by a single pointer/mapping update. Anything that cannot be reduced to that pointer update should be treated as an explicit additional state transition rather than being hidden inside “preparation succeeded.”

### Guix confirms the architecture while moving more policy into an executable language

Guix's 2013 design explicitly builds on Nix's low-level functional deployment layer. It retains transactional upgrades/rollback, per-user profiles, and garbage collection while representing packages and build programs with Scheme. This is important because it shows both the strength and the boundary of the model.

The strength is compositional configuration: a general programming language can construct derivations and build programs while the store/deployment layer still gives immutable realizations, generations, and reachability-based reclamation. The current Guix manual likewise describes GC roots under `/var/guix/gcroots`, profile generations, deletion of old generations before reclamation, and whole-system generations produced by `guix system reconfigure` with rollback to older system generations.

The boundary is that an expressive configuration language is not automatically a closed semantic input. Purity is obtained by which effects the deployment system admits into derivations/builds and how those effects are represented, not by the surface language merely being Scheme. The same caution applies to Anneal's Lake/Lean configuration. An executable configuration layer can be perfectly compatible with a reproducible prepared universe if all of its relevant inputs are controlled or captured. If it can observe untracked host state, its source text alone is not a sufficient identity.

Courtès and Wurmus's 2015 HPC account supports this conditional reading. They argue that functional package management materially improves reproducibility and environment sharing, motivated by the problem of software being upgraded, removed, or rebuilt underneath users. That is evidence for generation pinning and explicit environments. It does not establish that a package-manager closure captures the kernel, CPU behavior, every host facility, or every dynamic effect relevant to an arbitrary computation. Anneal should borrow the explicit-environment discipline without inflating it into a stronger semantic-equivalence guarantee than the evidence supports.

### The useful Anneal object is a prepared universe, not a copied Nix profile

A direct emulation of Nix profiles would be over-specific. Anneal does not need to become a package manager, and its verification subject may be narrower or differently structured than a complete user environment. What transfers is the factorization.

A prepared-universe record should be able to answer, at minimum:

**Recipe/provenance.** What exact source/model/tool/configuration inputs caused this universe to be prepared? Which inputs were intentionally excluded, and why are they irrelevant or trusted?

**Realization.** What exact artifact set and dependency closure did preparation produce? Which content hashes, file manifests, package revisions, native-library identities, and generated-source identities are needed to detect substitution or drift?

**Validation.** Which checks establish that the realization is internally usable for its stated purpose? Import/build smoke tests can be evidence here, but their scope must be explicit.

**Publication.** What mutable pointer or mapping makes this universe the default for new work? What generation/fencing token identifies that publication event?

**Consumption.** Which generation did a concrete verifier/editor/worker actually use? Does the result name that generation rather than infer it from whatever is current when the result is read?

**Lifetime.** Which rollback roots and active-session leases keep retired universes live? What policy makes reclamation safe?

This model is intentionally smaller than Nix. Anneal need not reproduce Nix's full derivation language, substituter protocol, build sandbox, content-addressed-store machinery, or general-purpose garbage collector if simpler manifests and generation directories satisfy the same relevant invariants.

### Atomic publication needs a validation fence

Nix profiles make pointer replacement atomic, but pointer atomicity alone is not enough for Anneal. Verification results have stronger success semantics than “the package manager selected these files.” A publication should therefore be fenced by the candidate's validation state.

The ordering should be:

1. construct generation G in a location not visible as current;
2. record its recipe/provenance and realized identities;
3. validate all checks required for G's advertised meaning;
4. record a ready/validated generation token;
5. atomically publish the current pointer from the previously current generation to G; and
6. have new consumers capture G's generation token before using it.

If validation fails, G can remain as diagnostic material or be discarded, but it must not become current. If publication races, the generation token makes the conflict explicit. If a consumer starts before publication and finishes after it, its result remains a result for the generation it captured.

This resembles a Nix profile switch, but the extra validation fence follows from Anneal's principle that missing evidence or failed tools cannot silently acquire the meaning of verification success.

### Garbage-collection reachability should not double as semantic validity

Nix and Guix use graph reachability to answer a storage question: which store objects must be retained? Anneal should avoid using the same mechanism to answer a semantic question.

An active lease can show that generation G must not be deleted. It cannot show that G is valid for a newly edited Rust snapshot, that its Lean environment matches a newly selected Aeneas revision, or that a cached proof result is fresh. Likewise, the fact that G is unreachable and reclaimable says nothing about whether a historical result that names G was correct at the time.

The separation suggests three independent relations:

- **identity/correspondence:** this operation or result refers to generation G;
- **validity/freshness:** G is acceptable for this particular verification subject and dependency snapshot; and
- **liveness/reachability:** G's files must remain available for current or rollback consumers.

Collapsing them into one “current generation” flag recreates exactly the ambiguity that functional deployment helps avoid.

### Serious alternatives are viable, but each must preserve the same distinctions

Anneal could choose a simpler strategy than a persistent multi-generation universe store: serialize all work, destroy the old environment only after every process exits, and rebuild the whole environment for each source generation. This can be correct and may be the best initial implementation if preparation is cheap enough. Its cost is lost reuse and slower interactive transitions, not weaker semantics by necessity.

Anneal could also use OS/process isolation rather than a managed artifact closure: start a fresh sandbox/container/VM with the full environment for each generation. That can give a clearer execution boundary, especially for native plugins or tools whose dependencies are difficult to enumerate. It may be heavier and still needs provenance and result identity; an opaque container image is not automatically a sufficient verification-subject description.

A third alternative is to delegate environment ownership to Lake/Nix/another upstream service and record only its immutable handle. This is attractive if the upstream system can provide a stable, complete closure identity plus lifetime guarantees. It is insufficient if Anneal cannot establish what the handle covers or whether long-lived consumers and ambient inputs respect it.

The deciding question is therefore not “should Anneal copy Nix?” It is which layer can provide the smallest interface that makes recipe identity, realized identity, publication, consumer pinning, and reclamation explicit enough to uphold Anneal's success semantics.

### Conditional judgment for Anneal

J046 supports a qualified architectural recommendation.

**Adopt the functional-deployment separation:** construct immutable or append-only prepared universes; publish through a small mutable generation pointer; keep rollback/current selection separate from artifact construction; and represent active consumer lifetime separately from selection.

**Record both recipe and realization identity where non-determinism or incomplete closure is plausible:** a provenance key can justify intended correspondence and cache lookup; a realized manifest/hash can show what was actually produced. Neither should be silently treated as proof of complete semantic-environment equality.

**Make ambient escapes explicit:** executable configuration, native plugins, host dynamic libraries, environment variables, external caches, network inputs, and persistent helper processes must be captured, controlled, validated, or trusted. A store-like directory boundary does not erase them.

**Fence publication on validation:** a generation can become current only after the checks required for its advertised meaning pass. Current-pointer atomicity is necessary for coherent selection but does not substitute for validation.

**Pin consumers and results to generations:** existing sessions should not drift merely because “current” changed. Reclamation should wait for both rollback policy and active leases.

**Do not inherit Nix mechanisms without need:** Anneal does not require a general-purpose package manager, global `/nix/store`, full derivation evaluator, or Nix's exact hashing scheme to gain these properties. The transferable value is the separation of identities, immutable realization, mutable selection, and explicit reachability.

## Boundaries

**No Nix, NixOS, Guix, Lake, Lean, Aeneas, or Anneal execution was performed for this report.** Mechanism claims come from pinned current Nix/NixOS source and documentation, current Guix documentation, and primary historical papers. Current Anneal execution evidence is reused only where an existing reference report already records it.

**The report does not equate Nix input-addressed paths with content hashes.** Current Nix has multiple output-addressing modes. The distinction between derivation/recipe identity and realized output identity is a finding, not an implementation detail to flatten away.

**Historical motivation is not current implementation specification.** The 2004 Nix paper and 2006 thesis establish the functional-deployment rationale. Current behavior is tied to the 2026 source/manual revision instead of backdating later mechanisms.

**Guix current-source evidence is limited.** The GitHub mirror is explicitly out of service; this run therefore treats the current Guix manual as operational documentation and the 2013/2015 papers as historical/author evidence. It does not claim a line-by-line audit of the current upstream Codeberg source.

**Current Guix manual PDF could not be fetched through the web PDF renderer in this run.** Search indexing exposed relevant current-manual passages, but direct PDF fetch returned HTTP 403 and a screenshot attempt consequently could not render a PDF page. This limits the report to the surfaced manual text rather than a visual inspection of the cited pages.

**Reproducibility is property-relative.** Functional package management can strongly improve reproducible software environments without proving identical runtime behavior across kernels, CPUs, host services, time, network state, or other uncaptured effects. This report makes no byte-for-byte or behavioral-reproducibility claim for Anneal.

**Reachability is not freshness.** A GC root or active lease establishes retention, not that an environment matches the current Rust/model/dependency snapshot.

**Atomic pointer replacement is not atomic live-system transition.** NixOS's current switch machinery explicitly performs imperative activation and service reconciliation. Anneal should not infer that publishing a generation pointer atomically migrates already-running processes.

**The current Anneal architecture deliberately leaves component boundaries undecided.** The prepared-universe/published-generation model here is derived analysis, not adopted Anneal policy.

**No storage/performance threshold is established.** Whether Anneal should keep two generations, dozens, or use content sharing/GC depends on measured preparation cost, artifact size, editor concurrency, and rollback/debugging needs.

## Evidence

### Primary historical sources

- Eelco Dolstra, Merijn de Jonge, and Eelco Visser, “Nix: A Safe and Policy-Free System for Software Deployment,” LISA 2004, pp. 79–92. USENIX: `https://www.usenix.org/conference/lisa-04/nix-safe-and-policy-free-system-software-deployment`. Used for the original dependency/coexistence/safe-upgrade rationale and the unique-component-path architecture.
- Eelco Dolstra, *The Purely Functional Software Deployment Model*, PhD thesis, Utrecht University, 2006. Used for the broader historical functional-deployment framing.
- Ludovic Courtès, “Functional Package Management with Guix,” ELS 2013, arXiv:1305.4584. Used for Guix's explicit inheritance of Nix's low-level deployment layer, Scheme EDSL/two-tier programming, profiles, rollback, and GC.
- Ludovic Courtès and Ricardo Wurmus, “Reproducible and User-Controlled Software Environments in HPC with Guix,” Euro-Par 2015 Workshops, LNCS 9523, pp. 579–591, DOI `10.1007/978-3-319-27308-2_47`. Used as author-reported evidence that functional environments improve reproducibility and sharing for long-lived scientific workloads.

### Current Nix source and documentation

All repository paths below are at `NixOS/nix@9bc9ab32a57504f068847af4f8013417476cb1ec` unless otherwise stated.

- `doc/manual/source/package-management/profiles.md`, blob `53cf5061f834e160e09db7a3bc2226806e662c41`: store objects, user environments, generations, profile current pointer, atomic symlink switch, rollback, and profile-root caveat.
- `doc/manual/source/package-management/garbage-collection.md`, blob `29a3b3101490024d77bd0c6f5373d9fdb907e1a8`: generations retain store objects; deletion of old generations precedes effective reclamation; `keep-derivations`/`keep-outputs` semantics.
- `doc/manual/source/package-management/garbage-collector-roots.md`, blob `925a3316239ff6ddfeca9787b6adbc2e9ef9f8d4`: explicit GC roots and dependency retention.
- `doc/manual/source/store/derivation/outputs/input-address.md`: input-addressed output identity is based on the derivation/how the output was made rather than realized content.
- `doc/manual/source/store/derivation/outputs/content-address.md`: content-addressed output semantics and motivation.
- `doc/manual/source/store/derivation/index.md` and `doc/manual/source/store/resolution.md`: derivations, outputs, deriving paths, store paths, and resolution when a content-addressed output path is not known before realization.
- `src/nix/unix/store-roots-daemon.md` plus current release notes: runtime-root discovery for running processes when normal `/proc` scanning is unavailable.
- Historical Nix release note 0.10: open files/running programs used as roots so uninstalled-but-running programs are not collected. This is historical continuity evidence, not a statement that the current implementation is identical.

### Current NixOS operational source

All repository paths below are at `NixOS/nixpkgs@6cb205c37b7c0c39b643163d1b7721b5f9bc0913`.

- `nixos/doc/manual/development/what-happens-during-a-system-switch.chapter.md`, blob `2aedb08e2a9746675dfbdc5e91b5e2952cec1629`: a switch inspects current mounts/systemd state and executes an ordered stop/activate/reload/restart/start reconciliation sequence.
- `nixos/modules/system/activation/activation-script.nix`, blob `338fc1911c01e698eb90eaacad8c5fd0385005b1`: activation snippets are imperative host mutations, are expected to be idempotent, and the non-dry activation updates `/run/current-system`; NixOS arranges a GC root for the current system.
- NixOS 26.05 manual observed 2026-09-30: `nixos-rebuild switch` builds the new configuration, makes it the boot default, and tries to realize it in the running system; user services are not automatically started/stopped. This is supporting documentation for the source-level distinction between immutable closure and live activation.

### Current Guix documentation

- GNU Guix Reference Manual, development version observed 2026-09-30: default profiles are GC roots under `/var/guix/gcroots`; old profile generations must be deleted before their store objects can be reclaimed; `guix system reconfigure` produces a new system generation and Guix supports rollback to earlier generations. Direct PDF retrieval in this run was blocked with HTTP 403; the cited passages were surfaced by the web index.
- `guix-mirror/guix` current GitHub README, blob `539cc20d0f0de3efc498b810366b4853dc43e6b6`, states that the GitHub mirror has been out of service since December 2023 and points to Codeberg. This is why the report does not treat the mirror's apparent `master` ref as current Guix source authority.

### Anneal authority and adjacent evidence

- `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md`, blob `d5339a95254eae14ac201139d07d9d36d48a19fb`: verification success must fail closed and preserve the intended promise.
- Same revision, `anneal/DESIGN.md`, blob `0e8170979f3a466f2460c0ef7ec6d9a6b92650b8`: successful results require enough identity/scope to make the promise meaningful; missing evidence cannot silently count as success; trust is explicit; exact component/subject boundaries remain non-decisions.
- `google/zerocopy` `reference@30b9d5749aed6049d949f4f582dd64c70088d07a`, `reports/anneal-nix-toolchain-tree-relocation-aarch64-darwin-2026-09-27/REPORT.md`, blob `262a141a145a2532745aaad71289896b5b3af1b2`: copied Nix-produced Lean/Rust trees retained NAR identity and ran smoke programs, but the source report explicitly does not establish independence from the still-mounted Nix store. Used as existing Anneal-specific evidence that artifact-tree identity does not automatically prove runtime dependency closure.

### Evidence roles

- **Author intent/history:** 2004 Nix paper, 2006 thesis, 2013 Guix paper, 2015 Guix/HPC paper.
- **Current mechanism:** pinned 2026 Nix and NixOS source/documentation; current Guix manual text.
- **Existing execution evidence:** current Anneal reference relocation report only; no new subject-system execution in J046.
- **Derived inference:** all recommendations about Anneal's prepared-universe identity, generation pinning, leases, validation fencing, and ambient-input treatment.

## Revalidation

Revalidate J046 if Anneal adopts a concrete preparation/publication design, if the selected Lean/Lake/Aeneas/Charon revisions change materially, or if environment preparation begins executing configuration/plugins in a different trust or sandbox boundary.

For Nix, reread the exact selected Nix revision's derivation-output addressing documentation, profile-generation semantics, GC-root behavior, and runtime-root handling. Do not infer current behavior from the 2004 paper alone. If Anneal relies on content-addressed Nix outputs, verify which relevant outputs are actually content-addressed rather than assuming that property from the store path syntax.

For NixOS-like publication, inspect the actual current-pointer update and every side effect that precedes or follows it. Test failure injection at each boundary: incomplete preparation, validation failure, publication race, process start during publication, crash after pointer replacement, rollback while old consumers exist, and reclamation while a consumer holds an old generation.

For Guix, use the then-current upstream Codeberg source or an authoritative release tarball/manual rather than the broken GitHub mirror. Recheck profile roots, system-generation switching, activation/service semantics, and garbage-collection behavior against that revision.

For Anneal, instrument a prepared-universe prototype to record both requested/provenance inputs and realized artifacts. Then probe likely escape paths: environment variables, host `PATH`, native dynamic libraries, Lake executable configuration, plugins, generated files, external caches, network access, and long-lived worker state. A claim of closed-world preparation should require evidence that each material channel is either captured or blocked.

Finally, test consumer lifetime independently from publication. Start a long-lived Lean/LSP/translation process on G, publish G+1, issue more requests to the old process, and attempt reclamation. The desired semantics should be stated before the experiment: either the process is explicitly pinned to G until restart, or migration to G+1 is an explicit protocol with its own validation. Merely observing that the process still runs is not enough to decide which model Anneal has implemented.