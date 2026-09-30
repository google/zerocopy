# Theseus: ownership, state spill, and global invariants

## Summary

Theseus provides strong evidence for a narrow architectural pattern, not for the stronger claim that Rust ownership can make system-wide identity or freshness problems disappear.

Within one Rust address space, an owned or reference-counted runtime object can make **liveness** compositional: clients hold the object that represents a resource, dependency edges hold the code and data they need alive, and retirement can remove an object from the namespace before its storage is actually destroyed. Theseus uses that pattern for memory resources and loaded code. Its task-to-`LoadedCrate` ownership chain is particularly relevant to long-lived proof environments: a consumer can retain a prepared environment while a newer generation becomes current, and destruction can wait until old readers release their references.

The same history also gives a direct counterexample to a broader ownership argument. The original Theseus design treated types such as `AllocatedFrames` as unique representations of underlying resources. A later correctness study states that Rust's ownership rules guarantee a single owner of a *linear-type instance* but do not establish that two independently created instances denote disjoint underlying resources. A duplicate-frame allocator bug violated the intended global invariant despite the local ownership discipline. The later design therefore adds verified creation/bookkeeping and a specification of when resource identifiers overlap. Local affine ownership preserves a uniqueness fact *after a correct constructor has established it*; it does not establish global uniqueness by itself.

For Anneal, the conditional judgment is therefore:

- use owned/immutable handles to express **in-process liveness and retention**, especially when an old prepared generation may remain usable after publication of a new one;
- establish **artifact identity, admissibility, and current-generation authority** separately, through preparation/publication logic that checks content/build identity and serializes the authority transition; and
- treat cross-process freshness as an external protocol property, not as something a Rust handle proves.

A content-addressed immutable artifact may need little type-level machinery for identity at all. Conversely, if Anneal keeps loaded Lean state or another process-local object alive, an ownership/reference graph can prevent premature reclamation without being asked to decide which generation is current. Theseus's evolution mechanism reinforces that separation: ownership keeps referenced code alive, while isolated loading, dependency validation, relocation rewriting, metadata locking, state transfer, and explicit namespace publication determine whether a replacement is coherent.

Basis: documentation + source + published research + derived comparison.

## Applicability

This report addresses J005 in `google/zerocopy#3732`: what Theseus shows about local affine ownership, spilled/global state, resource identity, code/data lifetime, and safe replacement, and which of those lessons transfer to Anneal artifact handles and loaded proof environments.

The historical subjects are intentionally separated:

- The 2017 PLOS paper is an **early design account**. It describes a state-spill-free ideal and explicitly says much of the implementation was incomplete and subject to change. It is evidence for original rationale and alternatives, not for later implementation behavior.
- The 2020 OSDI paper is the mature project account used here for the implemented architecture, live evolution mechanism, state-spill compromises, and evaluation.
- The 2024-12-31 correctness paper is a later retrospective and design extension. It explicitly narrows a central intralingual claim by distinguishing ownership of a representation from uniqueness of the represented resource. It also presents a verified representation creator and a revised memory-management argument.
- The source tree is pinned to `theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c` (2024-09-22), the latest commit on the repository's `theseus_main` branch observed for this report. It predates the arXiv posting of the later correctness paper. The current source therefore corroborates the OSDI-era loaded-code and crate-swapping mechanisms, but this report does not assume that the paper's `RepCreator` implementation is merged into that source revision.
- The duplicate-frame fix is pinned separately because it is historical evidence about the global uniqueness failure. The public issue and two repair commits occurred in October 2021, after OSDI 2020.

The Anneal conclusions are **derived applicability judgments**, not claims that Theseus and Anneal have the same workload. Theseus manages mutable OS resources, machine addresses, loaded executable sections, and in-band live update. Anneal manages generated artifacts, proof environments, workers, and external tools. The analogy is strongest where both systems need to distinguish (1) identity, (2) permission to start new work, (3) liveness for existing users, and (4) eventual reclamation. It is weak where Theseus relies on a single Rust runtime or machine-local address-space invariants that do not extend across processes or durable storage.

No fresh Theseus execution or benchmark was performed. The central conclusion does not depend on a new performance measurement.

## Findings

### 1. State-spill freedom began as an architectural goal, not an ownership theorem

The 2017 design starts from a broad diagnosis: conventional modularization, encapsulation, privilege boundaries, and hardware-driven decomposition can leave components entangled because one component retains lasting state on behalf of another. Its proposed response is correspondingly broad. It prefers flat first-class modules, client-held opaque state, stateless communication, and runtime replaceability. Rust is presented as an enabling mechanism because affine ownership can move state between components cheaply and safely.

Two qualifications in that early paper matter for later interpretation. First, the authors explicitly prioritize eliminating state spill even over performance and ease of programming; this is a design objective, not an empirical theorem that every form of central state is harmful. Second, the paper says the implementation was still being transformed toward the proposed design and that most of the concepts were unimplemented and subject to change. The early account should therefore be read as the problem statement and original rationale.

By OSDI 2020 the project had kept the goal but weakened the absolutism. The mature design still uses client ownership to avoid server-maintained handle tables. For example, a memory client owns a `MappedPages` object instead of holding a virtual-address handle whose server must look up hidden metadata. Shared resource state can use reference counting. Reclaimable or revocable resources can use absence-aware types and weak references.

But OSDI 2020 also classifies some spill as harmless or unavoidable. Recomputable caches are permitted as soft state. Hardware-required state and context for asynchronous entry points cannot always be exported to a client. Theseus moves such mandatory state into a minimal `state_db` with a well-defined owner and static lifetime; `state_db` must serialize itself for its own replacement, and the cell manager has a similar obligation for cell metadata. This is an important historical change: the durable idea is **make state ownership and lifetime explicit and minimize accidental coupling**, not “all server/global state can be eliminated.”

Basis: PLOS 2017 §§1-3; OSDI 2020 §§5.1-5.2. Evidence roles: published research + derived historical comparison.

### 2. Local ownership can make resource cleanup and liveness compositional

Theseus's most transferable use of ownership is not global identity; it is local lifetime control.

For ordinary resources, clients own typed values that represent what they acquired. Cleanup is tied to `Drop` and unwinding rather than to an unrelated server's table. Sharing uses reference-counted objects where appropriate. This gives the compiler visibility into the lifetime of the *representation object* and turns cleanup into a property of that object's ownership path.

Loaded code uses the same idea at a larger scale. The OSDI task invariant is: all memory transitively reachable from a task's entry function must outlive the task. Encoding every stack or program reference with a lifetime derived from the underlying mapped pages would be impractical. Instead, Theseus establishes a coarse ownership chain: the task owns the loaded cell containing its entry function, and a loaded cell owns the cells it depends on. That ownership graph keeps the mapped text/data reachable from the task alive.

The pinned source tree preserves this mechanism in current names. `book/src/subsystems/task_invariants.md` says a task owns the `LoadedCrate` containing its entry function and that `LoadedCrate` owns dependency crates through per-section metadata. `kernel/crate_metadata` uses strong dependencies from a section to what it needs and weak back-pointers from a dependency to its dependents. The module comments state the intended drop order directly: a dependent may be dropped before its dependency, but not vice versa. `StrongCrateRef` and `WeakCrateRef` are the runtime handles around `LoadedCrate`.

That pattern separates **discoverability/authority** from **physical lifetime**. A crate can be removed from a namespace so new lookups no longer select it, while outstanding dependency references can keep its backing memory alive. OSDI 2020 explicitly credits compile-time ownership semantics for allowing the cell manager to remove old symbols without first traversing the entire dependency graph to prove that no references remain; actual unloading waits until references are gone.

For Anneal, the narrow transfer is strong. A prepared environment handle can own or reference exactly the process-local objects needed by an active verification. Publishing generation G+1 need not invalidate a live handle to G if the contract permits old readers. Generation collection can then remove G from the set of selectable generations first and reclaim G only after its retained handles disappear.

What this does **not** decide is whether G was prepared from the right inputs, whether G is the latest published generation, whether two separately created handles denote the same artifact, or whether a different process has moved current authority to G+2. Those are different facts.

Basis: OSDI 2020 §§4.2-4.3, 6.1; `book/src/subsystems/task_invariants.md`; `kernel/crate_metadata/src/lib.rs`. Evidence roles: published research + source + derived Anneal applicability.

### 3. Live replacement depends on a protocol around ownership

Theseus's cell swapping is useful precisely because it shows what ownership does *not* replace.

The 2020 mechanism is a staged protocol:

1. load candidate cells into an isolated namespace;
2. validate dependencies in both directions;
3. redirect dependencies by rewriting relocations and metadata, update relevant on-stack references, and transfer state when necessary; and
4. replace the old namespace-visible cells/symbols with the new ones.

The current source at `1fbfe567...` preserves the same separation. `crate_swap::swap_crates` loads replacements into a temporary `CrateNamespace`, rewrites dependencies, copies `.data`/`.bss` state or invokes supplied transfer functions, and then removes old namespace entries. It accepts a list of swap requests so multiple related crates can be changed together instead of transiently linking a new component against an old peer. The OTA update path keeps new object files in a separate directory until the live swap succeeds because replacing the files first could let another load observe an inconsistent mixture.

The source also contains a warning that is easy to miss if one remembers only the OSDI architectural story: `swap_crates` does not guarantee semantic correctness after an arbitrary replacement. If a function or data structure changes, the caller remains responsible for ensuring that the needed related crates are included. State-transfer functions are part of the public mechanism for exactly this reason. The OSDI implementation likewise used manual state-transfer functions and reported automatic generation as ongoing work.

The OSDI evaluation further reports that some evolution stages require locking cell metadata to prevent overlapping evolution, and some updates can require a system pause unless components tolerate temporary state unavailability. In other words, “old code remains alive while referenced” solves a reclamation hazard, but **coherent publication is still serialized stateful work**.

For Anneal, this supports a two-layer architecture:

- a **prepared immutable generation** can be freely read and retained once constructed; and
- a narrow **authority transition** determines when that generation is selectable as current and which old generations can begin retirement.

Making every computation globally serial would be unnecessary; pretending publication is just another immutable handle operation would be unsafe. The Theseus analogy favors serializing the small authority-changing step while allowing expensive preparation and old-reader execution to proceed concurrently.

Basis: OSDI 2020 §6.1 and Fig. 2 discussion; `kernel/crate_swap/src/lib.rs`; `applications/upd/src/lib.rs`. Evidence roles: published research + source + derived Anneal applicability.

### 4. The later correctness work identifies the exact limit of affine ownership

The strongest evidence in J005 is a correction from the Theseus project itself.

The later correctness paper distinguishes a **representation instance** from the **resource value it represents**. A Rust linear/affine type can make one value non-copyable and give it a single ownership path. That does not stop a buggy constructor or allocator from creating a second, distinct value whose identifier overlaps the first. Therefore, “there is one owner of each representation” does not imply “there is one representation of each underlying resource.”

The paper presents an Intralingual Representation System (IRS) to repair that gap. Its generic `RepCreator` contains bookkeeping plus a private constructor. `create_unique_representation` checks that a proposed resource identifier does not overlap an existing identifier before creating the linear representation. The `ResourceIdentifier::overlaps` relation is itself part of the specification, so the guarantee depends on defining resource identity/overlap correctly.

The proof sketch deliberately combines mechanisms:

- the type system prevents a representation from being cloned or copied;
- formally verified creation/mutation operations prevent overlapping identifiers; and
- unverified operations are prevented from mutating the identifier in ways that bypass those checks.

This division of labor is more informative than either “Rust solved it” or “everything needs full verification.” Formal checking establishes the global creation invariant; linear types preserve it cheaply across ordinary use.

The memory subsystem is the motivating counterexample. The intended invariant was that Pages/Frames values uniquely represent virtual/physical regions, enabling a bijective mapping argument. The paper says original Theseus relied on manual checks for the uniqueness property because uniqueness is beyond the scope of intralingual design, and reports a frame-allocator bug that created overlapping `Frames` instances. The failure had existed in a rare path for years and materially delayed network-driver development.

Public repository history independently corroborates the failure mode. Issue #451, opened 2021-10-19 while working on NIC mappings, reports two allocations returning the same physical frame. The first repair, `abb5b837...`, removed newly reserved frames from the general free list. Follow-up testing showed that duplicate allocations were still possible, and `5d62e567...` added fixed region classification so a newly reserved range could not overlap a general-purpose region. The issue was then closed. The later paper does not identify #451 by number, so treating the issue as the paper's exact anecdote is a derived match rather than an explicit author statement; the author, workload, symptom, and mechanism align closely.

The current Theseus book still describes advanced memory objects as globally exclusive. The later paper supplies the missing justification that the book's simple wording omits: global exclusivity is only as sound as the constructor/bookkeeping that prevents overlapping representations.

Basis: Ijaz/Boos/Zhong arXiv:2501.00248v1 §§5.2-5.3; Theseus issue #451; commits `abb5b837...` and `5d62e567...`; current `book/src/subsystems/memory.md`. Evidence roles: published research + issue history + source history + derived cross-source identification.

### 5. Identity is a specification and authority problem before it is a lifetime problem

The `RepCreator` result generalizes beyond physical memory: **uniqueness is relative to an identity/overlap relation**. If that relation is wrong, the constructor can be perfectly serialized and still establish the wrong invariant.

This is the central warning for Anneal. A Rust type such as `PreparedEnvironment` can be affine and immutable while two values still refer to semantically incompatible environments that happen to share a path, package name, or nominal version. Conversely, two different filesystem trees may be equivalent for a particular proof if the identity contract intentionally ignores irrelevant bytes. The hard question is not “who owns this handle?” but “what facts make two preparations the same or conflicting for the promise Anneal makes?”

Potential Anneal identity inputs include source revisions, toolchain revisions, dependency lock state, generated-source identity, configuration, target/platform, and any other state that can alter accepted proof behavior. This report does not choose that set. It establishes only that local ownership cannot substitute for defining and checking it.

The same applies to freshness. A handle can prove that its referent has not been reclaimed in the process that owns it. It cannot prove that another process has not published a newer generation. Currentness is an authority relation over generations, not an aliasing property of the handle. Cross-process currentness therefore needs an external observation with a race-safe publication protocol or equivalent native synchronization.

A content-addressed immutable design makes the distinction especially clear. If an artifact is named by a cryptographic digest over all semantically relevant inputs, global identity may be established independently of Rust ownership. The Rust handle then contributes only lifetime and ergonomic access. If the artifact name is mutable or underspecified, making its handle affine does not repair the identity problem.

Basis: arXiv:2501.00248v1 `RepCreator`/`ResourceIdentifier` design + derived application to Anneal's design contract. Evidence role: derived.

### 6. Explicit roots and unavoidable state are not architectural failures

The mature Theseus history argues against treating every central coordinator, index, or metadata store as evidence of bad architecture.

`state_db` and the cell manager exist because some state has no natural client owner or must outlive the component that normally manipulates it. Those roots are made narrow and explicit, and they receive special replacement rules. The live-swap path similarly relies on `CellNamespace` metadata and locking to arbitrate what is visible.

For Anneal, an explicit current-generation pointer, artifact index, preparation registry, or publication coordinator may therefore be the *correct* place for state that cannot be derived from a local consumer handle. The useful question is whether such state is minimal, has clear ownership and replacement semantics, and is the authoritative source for the facts only it can establish. Moving authority into a Rust object held by one worker does not remove the need for shared authority; it only hides it from other processes.

This cuts both ways. A central registry should not absorb facts that immutable artifacts can carry themselves. Theseus's client-owned resources show the benefit of pushing liveness and cleanup to the objects that actually need them. The architecture should centralize the authority transition, not every read or every lifetime.

Basis: OSDI 2020 §5.2 and §6.1 + derived Anneal applicability.

### 7. Retention has a real cost

Reference-counted liveness converts use-after-free into delayed reclamation. It does not make reclamation free.

Theseus explicitly uses strong and weak references for different resource relationships, and the loaded-crate graph can keep old code/data resident while dependents exist. Its swap implementation can also cache removed crates as soft state to speed later swaps. Those choices are reasonable for its workloads but expose the cost that an Anneal design must account for: old readers can retain old generations indefinitely unless the protocol bounds them, cancels them, or applies external retention policy.

The Anneal consequence is not “avoid references.” It is to define generation collection separately from correctness. Correctness may permit an old reader to finish forever; operations may still need quotas, deadlines, weak-index entries, or explicit retirement diagnostics so disk/memory use remains bounded. A weak registry can say “this generation is still around if someone else owns it” without becoming the owner that keeps it alive.

Basis: OSDI 2020 resource-sharing/revocation discussion; current `StrongCrateRef`/`WeakCrateRef`; current swap cache. Evidence roles: source + published research + derived.

### 8. Conditional judgment for Anneal

The Theseus record discriminates among three possible architectural positions.

**Position A: encode generation correctness in ownership.** This is too strong. Ownership can preserve a correct local invariant but cannot define artifact identity, establish non-overlap among independently constructed representations, or establish cross-process freshness. The duplicate-frame history is a concrete counterexample to the general form of the argument.

**Position B: ignore ownership and use only a global coordinator/store.** This throws away a useful local mechanism. Once a prepared environment is accepted, ordinary use should not need repeated global coordination merely to keep its process-local state alive. Reference ownership can make old-reader liveness and reclamation mechanically safe.

**Position C: split global authority from local liveness.** The evidence favors this position, subject to Anneal-specific validation. A narrow preparation/publication layer establishes the semantic identity and authority of a generation. Immutable handles then carry that established identity and retain the process-local/durable objects needed by users. Publication of a successor prevents new selection of the predecessor; outstanding predecessor handles remain valid according to an explicit old-reader policy; collection occurs after liveness and retention conditions permit it.

This is a conditional conclusion, not adopted Anneal policy. Evidence that would change it includes an Anneal design in which every relevant environment is independently content-addressed and stateless so local runtime retention is unnecessary, or evidence that Lean/Charon/Aeneas process state cannot safely coexist across generation transitions and therefore requires a stronger quiescence rule. Those questions belong to Anneal-specific probes and protocol design.

Basis: synthesis of all evidence above.

## Boundaries

**Not examined: exact current implementation of the 2024 `RepCreator` work.** The pinned public Theseus `theseus_main` head observed here is dated 2024-09-22 and does not expose the paper's `RepCreator` names through the current source search used for this report. The arXiv paper was posted 2024-12-31. This report treats its implementation/proof as a published research result, not as a claim about the pinned repository head.

**Not examined: cryptographic identity schemes.** The Anneal discussion of content addressing is an architectural counterexample used to separate identity from ownership. No hash construction, collision policy, or exact cache key is recommended here.

**Not examined: cross-process reference counting.** Theseus's relevant ownership guarantees live inside one Rust system image. This report does not infer that distributed reference counting, leases, or durable refcounts are appropriate for Anneal. Cross-process freshness and collection require their own protocol.

**Unknown: how much of Theseus's live-update protocol generalizes to long-lived Lean servers.** The analogy identifies roles—prepare, validate, publish, retain old readers, collect—but not the exact synchronization needed by Lean's elaborator or Lake environment. An Anneal design must use Lean-specific evidence for that.

**Known not to apply: “ownership proves artifact identity.”** The later correctness work directly rejects the underlying general inference: single ownership of a linear instance does not rule out another independently created instance representing overlapping underlying state.

**Known not to apply: “replacement is safe once old storage stays alive.”** Current `crate_swap` documentation explicitly disclaims semantic correctness for arbitrary code/data changes. State compatibility and coordinated replacement remain caller/protocol obligations.

**Evidence limit: issue #451 linkage.** The public issue strongly matches the later paper's described frame-allocation bug, but the paper does not cite the GitHub issue number in the passages examined. This report uses the issue as independent evidence of the same class of global-uniqueness failure and labels the exact identity match as derived.

**Evidence limit: evaluation scope.** OSDI 2020 demonstrates selected live-evolution scenarios and fault-injection workloads, not a proof that arbitrary cell swaps are correct. The source warning is consistent with that limit.

## Evidence

### Historical design

- Kevin Boos and Lin Zhong, *Theseus: a State Spill-free Operating System*, PLOS 2017, DOI `10.1145/3144555.3144560`, PDF: <https://www.theseus-os.com/kevinaboos/docs/theseus_plos2017.pdf>. Examined 2026-09-30. Relevant material: §§1-3, especially the definition of state spill, rejection of server-held progress state, flat module architecture, and the explicit statement that much of the early design remained unimplemented and subject to change.
- Kevin Boos et al., *Theseus: an Experiment in Operating System Structure and State Management*, OSDI 2020, PDF: <https://www.usenix.org/system/files/osdi20-boos.pdf>. Examined 2026-09-30. Relevant material: §§3-6 and §7.1. In particular: intralingual ownership/resource cleanup; task-to-cell lifetime chain; handle avoidance and client ownership; `state_db` for unavoidable state; staged cell swapping; metadata/dependency rewriting; state transfer; evaluation and locking/atomicity limits.

### Later correctness work

- Ramla Ijaz, Kevin Boos, Lin Zhong, *Combining Type Checking and Formal Verification for Lightweight OS Correctness*, arXiv `2501.00248v1`, 2024-12-31, <https://arxiv.org/abs/2501.00248>. Examined 2026-09-30. Relevant material: introduction and §§5.2-5.3. `RepCreator` combines verified global bookkeeping with a private constructor; `ResourceIdentifier::overlaps` is part of the specification; the proof of representation uniqueness uses the type system, formal verification, and intralingual assertions together. The memory-management section reports the overlapping-`Frames` bug and states that uniqueness is beyond what intralingual design alone establishes.

### Pinned current source

Repository: `theseus-os/Theseus`, revision `1fbfe567075a65ed749b6680db1aeb538819c70c`.

- `book/src/design/design.md`, blob `24fe60e94daba9a2357727bf247474cbb89ea540`: `LoadedCrate` owns mapped regions and metadata; `CrateNamespace` is the symbol/linking namespace.
- `book/src/subsystems/task_invariants.md`, blob `b624063b03f16fcd12b9ea43f9fec40a10922994`, especially lines 45-59 in the observed revision: the task → `LoadedCrate` → dependency-crate ownership chain used to establish code/data lifetime.
- `book/src/subsystems/memory.md`, blob `c0cdf1f9bf24739c64ffe66e20d781db0f9d9960`, especially the advanced-memory-type section: documents the intended system-wide exclusivity property of `AllocatedPages`/`AllocatedFrames`/`MappedPages`.
- `kernel/crate_metadata/src/lib.rs`, blob `683bf27cc4588054f7ce5ecb1c5ab36070d0254c`: strong dependency / weak dependent graph, `StrongCrateRef`, `WeakCrateRef`, `LoadedCrate`, and mapped section ownership.
- `kernel/crate_swap/src/lib.rs`, blob `c9f943e87dd18fe7e951fc548d0cbec5b6ce3634`: staged swap implementation, temporary namespace, relocation/dependency rewriting, state transfer, old-crate cache, and the explicit correctness warning.
- `applications/upd/src/lib.rs`, blob `562f6af8cc31311bcb194686b1e7bebf8105dba2`: keeps replacement files separate until the live swap succeeds to avoid mixed old/new loading.
- `Makefile`, blob `c487c7de59405315202961ee792d08e4fa124625`: `merge_sections` is documented as a load-time/memory optimization that may interfere with crate swapping, an example of evolution metadata carrying implementation cost.

Stable source locators can be formed from the pinned revision, for example:
<https://github.com/theseus-os/Theseus/blob/1fbfe567075a65ed749b6680db1aeb538819c70c/book/src/subsystems/task_invariants.md>
<https://github.com/theseus-os/Theseus/blob/1fbfe567075a65ed749b6680db1aeb538819c70c/kernel/crate_swap/src/lib.rs>

### Global-uniqueness failure and repair

- Theseus issue #451, *Frame allocator will allocate two copies of a frame*, opened 2021-10-19 and closed 2021-10-29: <https://github.com/theseus-os/Theseus/issues/451>. The report shows NIC memory setup receiving the same physical address from distinct allocations and traces the problem to reserved/general frame bookkeeping.
- Commit `abb5b83785224a78b2b22cc00d4e3af3865e60b6`, 2021-10-20: <https://github.com/theseus-os/Theseus/commit/abb5b83785224a78b2b22cc00d4e3af3865e60b6>. First repair removes newly reserved ranges from the general free list.
- A follow-up issue comment demonstrated a remaining duplicate-allocation path.
- Commit `5d62e567227e137db27c0c69728e732c5771c923`, 2021-10-29: <https://github.com/theseus-os/Theseus/commit/5d62e567227e137db27c0c69728e732c5771c923>. Adds fixed general-region tracking and rejects new reserved regions that overlap general-purpose regions, closing #451.

### Related source-hardening history

These commits are not the central J005 evidence, but they show that the project continued to move assumptions behind narrower checked interfaces rather than treating the initial ownership architecture as complete:

- `fbe80b056c75b23e4b51cf0bbd47cf17f05da671` (2021-08-04): moved executable-function reinterpretation into `LoadedSection::as_func()` to improve safety and restrict it to text sections.
- `919d9a2867532db2896299f9cf441f678319b99a` (2022-08-02): marked `LoadedSection::as_func()` unsafe because the requested function signature could not yet be guaranteed.
- `b92483cbb0807f9ed2dea46900ff7448819e0f59` (2023-02-23): made `LoadedSection` non-exhaustive to prevent foreign crates from directly constructing its fields.

These changes support a cautious interpretation of “intralingual”: the project repeatedly tightened creation/access boundaries as previously unchecked premises became visible.

## Revalidation

For a later Theseus revision, revalidate the findings in four narrow passes rather than repeating the full literature survey.

1. **Loaded-code lifetime.** Inspect `book/src/subsystems/task_invariants.md`, `kernel/crate_metadata`, and the current task structure. Check whether a task still retains its entry crate/environment and whether dependency edges still hold strong references in the direction needed to prevent premature unloading. If the ownership graph changes, reassess the old-reader analogy.
2. **Replacement protocol.** Inspect `kernel/crate_swap` and the update client. Check whether replacement still uses isolated preparation, dependency validation/rewriting, state transfer, and an authority-changing namespace step; also check whether the explicit correctness warning remains. A redesign that makes arbitrary replacement formally safe would materially change this report.
3. **Global representation uniqueness.** Locate the implementation corresponding to the 2024 paper's IRS/`RepCreator`, or its successor. Verify how unique identifiers are created, how overlap/equality is specified, and whether bypass constructors or mutations exist. If the implementation has moved to a different verification tool or proof boundary, preserve that distinction.
4. **Anneal transfer.** Recheck the Anneal generation/identity contract itself. If all relevant artifacts become immutable and content-addressed with a complete semantic digest, ownership may become purely a liveness optimization. If a loaded proof environment has hidden mutable state or a generation transition invalidates old readers, the retention conclusion must be narrowed.

The cheapest discriminator for the main judgment is the constructor question: **Can two independently constructed handles pass Rust's local ownership rules while denoting conflicting underlying state?** If yes, a separate global identity/admissibility mechanism remains necessary regardless of how elegant the handle type is.