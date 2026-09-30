# Compatibility-constrained rewrites: zCore, reL4, Theseus, and Anneal

## Summary

A rewrite can preserve an external contract without preserving the old implementation, and it can preserve implementation continuity without freezing the final architecture. zCore, reL4, and Theseus make those dimensions visible because they chose different points in that design space.

zCore reimplemented Zircon-facing behavior in Rust while reorganizing the kernel around Rust kernel-object and hardware-abstraction layers; the same codebase later added Linux-facing behavior and both libOS and bare-metal execution. reL4 instead embedded Rust into an existing seL4 build and replaced C functions incrementally through a temporary C/Rust compatibility layer, while keeping seL4 tests as a behavioral oracle. Theseus chose a clean slate so that Rust ownership and language-level mechanisms could shape the operating-system architecture itself; that freedom came with an explicit compatibility and maturity cost, including missing POSIX support in the 2020 evaluation.

For Anneal, the durable boundary is unusually clear. The current design contract explicitly leaves the annotation language, proof encoding, result schema, command-line interface, TCB-log serialization, tool boundaries, and exact theorem strategy undecided. The current README also labels V1 as historical and non-authoritative. Anneal therefore should not treat V1 command names such as `verify`, `generate`, and `expand`, nor generated Lean names such as `Pre`, `Post`, and `spec`, as architectural compatibility obligations merely because they existed.

Anneal does need to preserve the semantics that its current principles and design contract make durable: verification success must have a precise scope and trust basis; Rust-level claims must be justified against Rust behavior; verification must compose across abstraction boundaries; ordinary use must remain Rust-oriented; and missing evidence or trusted assumptions must remain explicit. A redesign may replace the mechanisms that realize those properties. If real users or tools depend on a V1 surface, the evidence here favors a versioned compatibility adapter around the redesigned core rather than freezing that surface into the core architecture.

## Applicability

This report answers J008 from `google/zerocopy` issue #3732 by comparing three rewrite strategies and applying the comparison to Anneal's current redesign. The comparison separates three questions that are easy to conflate:

1. **Code ancestry:** how much old implementation and build structure remains during or after the rewrite?
2. **Externally promised semantics:** which behaviors must existing clients still observe?
3. **Internal architecture:** which abstractions, module boundaries, and representations may change?

The zCore observations apply to `rcore-os/zCore` at commit `8de51f4ee053bcaaf435897febf648bcb4d45479`, with historical context from repository documentation. zCore is a work in progress; its test harnesses and compatibility goals do not establish complete Zircon or Linux compatibility.

The reL4 source observations apply to `rel4team/rel4_kernel` at commit `da74b45b69c89d9e6f43161006f3b586fda41107`. The 2024 project report at `9dc90edc02e78ae79e647e1d1a4200c7cdf85afe` supplies the authors' account of the incremental migration method. That report is project-authored evidence, not an independent evaluation. The broader reL4 ecosystem has continued to evolve; a 2026 ReL4 Book page describes both a legacy mixed seL4/reL4 “lib mode” and a pure-Rust “bin mode,” but that moving documentation is used only as an evolution signal, not as the basis for claims about the identified 2024 source snapshot.

The Theseus observations combine its current repository snapshot at `1fbfe567075a65ed749b6680db1aeb538819c70c` with the peer-reviewed OSDI 2020 paper. The paper evaluates Theseus as a clean-slate operating system, not as a rewrite of an established compatibility surface. Its value here is comparative: it shows what design freedom can buy when compatibility is intentionally not the primary constraint.

The Anneal conclusions apply to the current redesign at `google/zerocopy` commit `cc135f46155b72e4b51188525c2974a3b84acf92`. The `anneal/v1/` tree at that same revision is historical evidence about the previous user and generated-proof surfaces; `anneal/README.md` explicitly says V1 is not current design authority.

## Findings

### Compatibility has three independent axes

The three projects show that “rewrite compatibility” is not a single property.

| Project | Code ancestry during the work | Externally constrained semantics | Internal architectural freedom |
| --- | --- | --- | --- |
| zCore | New Rust implementation rather than an in-place translation of Zircon | Zircon-facing system behavior was the initial target; the project runs Zircon user programs and official core tests, then also added Linux-facing behavior | High: Rust kernel-object crates, syscall layers, a shared HAL, and libOS/bare-metal modes differ materially from simply reproducing Zircon's source organization |
| reL4 | Deliberately incremental replacement inside the seL4 build/test environment | seL4 compatibility and native seL4 tests constrain behavior during migration | Medium during migration, higher afterward: FFI and C-style shims preserve continuity while Rust modules reorganize code; the project marks at least one C-style compatibility module for later removal |
| Theseus | From-scratch Rust OS | No inherited POSIX or established-kernel compatibility contract in the 2020 design | Very high: cells, single-address-space/single-privilege execution, and intralingual invariants were chosen to exploit Rust rather than mimic an older kernel |

Basis: source + documentation + derived comparison.

A compatibility target therefore does not imply architectural imitation. zCore is the clearest example. Its current workspace separates `zircon-object`, `zircon-syscall`, `linux-object`, `linux-syscall`, `kernel-hal`, a loader, and the kernel. The loader can select Linux, Zircon, and libOS features independently. `linux-object` itself depends on `zircon-object`, while both layers depend on the shared HAL. This structure preserves externally useful Zircon and Linux behaviors while making the reusable object model and hardware boundary first-class Rust architecture.

Basis: source (`rcore-os/zCore`, `Cargo.toml`, `loader/Cargo.toml`, `linux-object/Cargo.toml`, `kernel-hal/src/kernel_handler.rs`).

### zCore preserved a behavioral target, not a source-shaped kernel

zCore's legacy README states its original goal directly: reimplement the Zircon microkernel in safe Rust as a userspace program. The same document describes both Zircon and Linux execution in libOS and bare-metal modes and provides commands for running official Zircon core tests and Linux libc tests. The current English README describes the project as a kernel based on Zircon with a Linux-compatible mode.

The source architecture is broader than a source-to-source port. `zircon-syscall` dispatches Zircon system calls onto Rust kernel-object abstractions. `kernel-hal` defines a kernel-facing hardware abstraction, and the loader selects Linux/Zircon and host/bare-metal combinations through Cargo features. That organization lets one internal object and hardware substrate serve more than the original Zircon-facing environment.

This strategy buys architectural freedom while retaining an external behavioral oracle, but it also makes the compatibility boundary expensive to finish. The project documentation labels the kernel a work in progress, and its Linux test documentation preserves failed-test lists rather than claiming complete compatibility. Public evidence therefore supports “compatibility as a target under active construction,” not “drop-in equivalence already achieved.”

Basis: source + project documentation. The conclusion about architectural freedom is derived from the relationship between the compatibility tests and the independently factored internal crates.

### reL4 used compatibility as migration scaffolding

The reL4 project report says the team embedded portions of Rust into seL4 and replaced C functions step by step specifically to avoid a complete one-shot reconstruction. It describes building the Rust side as a static library, linking it into the seL4 build, using FFI in both directions, and validating the replacement incrementally. The same report says that FFI functions were grouped so the invasive compatibility code could later be removed.

The identified `rel4_kernel` snapshot still shows this scaffolding. `build.py` can build the Rust implementation or switch to a C `baseline`, and it wires both into the seL4 test environment. `src/deps.rs` declares C functions that Rust still calls. Rust exports many `#[no_mangle]`/`extern "C"` entry points for C callers. `src/cspace/mod.rs` labels its C-style compatibility module as temporary and slated for deletion.

At the same time, the project report explicitly rejects a mechanical C-to-unsafe-Rust transliteration as the final design. It describes regrouping procedural C operations into Rust methods and using Rust ownership and lifetime structure where possible. Thus the FFI boundary preserved incremental substitutability, not the final module architecture.

This strategy reduces the size of each migration step and keeps a native test oracle continuously available. Its cost is a period in which two language models, two calling conventions, old symbol shapes, and new Rust abstractions coexist. The report itself notes that missing C symbols had to be supplied as compatibility functions during partial conversion, and the source still contains compatibility wrappers. That machinery is useful when continuity matters, but it is also debt to delete rather than a design to canonize.

Basis: project-authored documentation + source. The judgment about migration debt is derived from the explicitly temporary compatibility module and the mixed-language boundary.

### Theseus spent compatibility budget to buy architectural leverage

The Theseus authors say they chose to write an OS from scratch while investigating whether they could avoid “state spill” between operating-system components. Rust's ownership model then became part of the architecture rather than only an implementation language. Their OSDI paper describes runtime-persistent component boundaries (“cells”), extensive use of language-level mechanisms to enforce OS invariants, and an execution model in which safe-Rust applications, libraries, and core OS components coexist in a single address space and privilege level.

That freedom came with a direct adoption cost. The 2020 paper reports roughly four person-years of effort and about 38,000 lines of from-scratch Rust, while also saying Theseus was much less complete than mature systems and lacked POSIX support and a full standard library. The current repository still describes Theseus as a new OS written from scratch to explore novel structure and intralingual design, and says it is not yet mature.

Theseus therefore does not show that clean-slate work is faster or more successful. It shows a narrower point: when inherited external semantics are not a hard requirement, a team can let the new language reshape the architecture much more aggressively, but it must absorb the resulting ecosystem and maturity gap.

Basis: peer-reviewed paper + current project documentation + derived judgment.

### Method cannot be inferred from speed or eventual success

The three projects do not supply a controlled comparison of engineering time, defect rate, completeness, or long-term maintenance. They differ in scope, team, maturity, compatibility goals, and evaluation method. Public evidence can show what constraints each migration method imposed and what tradeoffs the authors reported. It cannot establish that one method is generally faster, safer, or causally responsible for eventual project success.

This matters for Anneal because an attractive rewrite narrative can otherwise become a false optimization target. reL4's incremental path is evidence that compatibility shims can support stepwise replacement; zCore is evidence that behavioral compatibility can coexist with a substantially different internal architecture; Theseus is evidence that dropping inherited compatibility can unlock deeper redesign. None is evidence that Anneal should copy a project's development tempo or expected outcome.

Basis: derived from the non-comparable evidence base.

### Anneal's current durable boundary is semantic, not textual

Anneal's current `DESIGN.md` makes the preservation question unusually explicit. It says the design contract intentionally stops short of specifying an annotation language, proof encoding, result schema, command-line interface, or division of responsibility among Rust, Charon, Aeneas, Lean, and Anneal. Its list of deliberate non-decisions also leaves open command names, profiles, warnings, exit codes, TCB-log serialization, tool boundaries, and the exact theorem or validation strategy.

The same document does make several properties durable:

- A successful result must identify the program or behavior covered, the promises established, and the trusted code and assumptions on which those promises depend. Missing evidence or tool failure cannot silently acquire the meaning of success.
- A Rust-level theorem must be connected soundly to the Rust behavior it claims, including the obligations required to rule out undefined behavior.
- Verification should compose through abstraction boundaries without reopening private implementation details, while preserving any ownership, provenance, initialization, concurrency, protocol, I/O, or nondeterministic structure that matters to the promise.
- Ordinary use must be Rust-oriented; users should not need Lean 4 merely to use Anneal effectively, and unsatisfied obligations should map back to the Rust program.
- Trust must remain explicit and shrinkable as checked evidence replaces assumptions.

Those are compatibility obligations because the current principles and design contract make them promises. Their present implementation mechanisms are not.

Basis: normative project design contract and principles at `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`.

### V1 exposes useful migration surfaces, but the redesign has not promised their shape

Historical V1 exposed `cargo anneal verify`, `setup`, `expand`, and `generate`. `expand` could print Anneal-generated and Aeneas-generated Lean. The V1 generator produced named `Pre` and `Post` structures and a `spec` theorem, used generated Aeneas files such as `Funs.lean` and `Types.lean`, and maintained source mappings so Lean errors could be projected back into Rust source spans.

These V1 details matter in two different ways.

First, some are mechanisms for current durable goals. Source mappings served the Rust-oriented diagnostic goal. Generated Lean access served specialist workflows. An incremental mode such as `--allow-sorry` served the need to distinguish unfinished proof work from ordinary verified success. A redesign should preserve those user-level capabilities where the current design still requires them, even if it changes the file names, theorem representation, source-map format, or flag names.

Second, the exact textual and command surfaces are not current commitments. `anneal/README.md` calls V1 historical and warns that its documentation may conflict with current principles. Current `anneal/src/main.rs` contains a redesign whose CLI presently exposes only `setup`, while `DESIGN.md` explicitly refuses to freeze the command-line interface and proof encoding. The existence of V1 consumers would create migration work, but it would not retroactively make every generated identifier part of Anneal's architecture.

Basis: current normative design + current source + historical V1 source. The distinction between capability and encoding is derived.

### A compatibility shell is the strongest default for the Anneal redesign

The comparison supports a conditional strategy for Anneal:

1. **Write down the semantic compatibility surface before choosing adapters.** Treat the current principles and design contract as the hard surface: success meaning, trust visibility, Rust-level justification, compositionality, and Rust-oriented ordinary use. Do not expand that surface merely because V1 happened to emit a particular theorem or command.
2. **Keep the redesigned core free to change proof representation and tool boundaries.** zCore demonstrates that external semantics can remain the target while internal architecture changes substantially. Anneal should preserve verified meaning, not V1's generated Lean topology.
3. **Add a versioned compatibility adapter only where actual consumers justify it.** If users or automation invoke V1 commands or ingest generated Lean, preserve that path temporarily through translation, wrappers, or a versioned export format. reL4 shows the value of an explicitly temporary compatibility layer; its source also shows why that layer should have a deletion plan.
4. **Test behavior at the promised boundary.** Differential or regression tests should ask whether the same Rust input receives equivalent verified/failed/incomplete classification, trust accounting, and actionable diagnostics where those are promised. Textual equality of generated Lean should be a test only if Anneal deliberately adopts that text as an API.
5. **Expose low-level proof machinery without freezing its internal representation.** The current design allows specialists access to Lean, Aeneas, resource logics, and generated models. A versioned inspection/export interface can satisfy that need more safely than making internal filenames and theorem names permanently stable.

This “redesigned core plus compatibility shell” approach lies between a flag-day clean slate and a forever-frozen V1 surface. It preserves migration options without allowing temporary artifacts to foreclose the architecture.

Basis: derived from the three-project comparison and Anneal's current design contract.

### Serious alternatives remain conditional on external adoption evidence

**Freeze V1's CLI and generated proof interface.** This minimizes migration for any current consumers, but it conflicts with the explicit current non-decision about CLI and proof encoding. It would be justified only if external adoption is large enough that compatibility cost dominates architecture cost, and even then a stable adapter is less constraining than freezing internal representations.

**Make a flag-day break from V1.** This maximizes design freedom and matches the current README's statement that V1 is historical. It is reasonable if V1 had little external use or if its users can migrate cheaply. Theseus shows the architectural upside of clean-slate freedom, but also warns that compatibility and ecosystem work do not disappear; they are simply paid by users and the new project instead of by a bridge.

**Run old and new proof pipelines side by side while replacing pieces incrementally.** This is the closest Anneal analogue to reL4. It can make semantic deltas observable at every step, but it also increases the trusted surface and operational complexity while both pipelines exist. It is most attractive where source/model correspondence or generated-proof changes are too large to validate safely in one jump.

**Preserve only the source-level Rust annotations while replacing generated proof machinery.** This resembles zCore's external-semantics/internal-architecture split. It may offer the best migration value if annotations have real users but generated Lean has few external consumers. The current design contract does not require today's annotation language, however, so even this should be evidence-driven rather than assumed.

Basis: derived conditional judgment; no survey of Anneal V1 consumers was performed.

## Boundaries

**Not examined:** This report does not survey downstream Anneal V1 users, scripts, editor integrations, or unpublished workflows. Therefore it cannot say which historical V1 surfaces have de facto ecosystem compatibility value. That survey should precede any irreversible removal decision.

**Not examined:** This report does not benchmark zCore, reL4, or Theseus, compare defect rates, or reconstruct person-hours on a common basis. It makes no claim that one rewrite strategy is faster or more successful.

**Known not to apply:** Theseus does not preserve an inherited POSIX or legacy-kernel compatibility target in the 2020 design, so it cannot answer how a clean-slate architecture behaves under a hard compatibility requirement. It is useful only as the unconstrained comparison point.

**Unknown:** zCore's public test infrastructure demonstrates active Zircon/Linux compatibility checking, but this investigation did not establish a complete passing matrix for the identified revision. The project itself remains work in progress.

**Unknown:** The identified `rel4team/rel4_kernel` snapshot is an earlier migration surface, while the broader reL4 ecosystem now documents a pure-Rust binary mode. This report does not prove that every current reL4 implementation detail descends directly from the older snapshot.

**Unsupported stronger conclusion:** The projects do not establish that preserving a compatibility layer causes better quality, nor that clean-slate design causes better architecture. They expose constraints and tradeoffs; they do not identify a universal causal winner.

**Anneal-specific boundary:** The current design contract itself says the CLI, annotation language, proof encoding, result schema, and tool boundaries are undecided. A report about rewrite precedent cannot override that authority by declaring one of those mechanisms stable.

## Evidence

Evidence was acquired or materially revalidated on 2026-09-30 unless otherwise noted.

### Anneal current redesign

- **Normative:** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/PRINCIPLES.md`, especially “Anneal's promise to its users” and “How we make decisions about Anneal.” This establishes the no-fail-open promise, UB-freedom priority, user-oriented proof experience, and decision principles.
- **Normative:** same revision, `anneal/DESIGN.md`, especially “Verification success has a precise meaning,” “Rust-level claims require justified Rust semantics,” “Verification composes through abstraction boundaries,” “The ordinary interface is Rust-oriented,” “Trust is explicit and replaceable by evidence,” and “Deliberate non-decisions.” This is the main authority for what must survive a redesign and what remains open.
- **Documentation:** same revision, `anneal/README.md`. It states that `anneal/` is the current redesign and `anneal/v1/` is historical; V1 documentation is not current design authority.
- **Source:** same revision, `anneal/src/main.rs`, `Cli`/`Commands`. The current redesign currently exposes only `setup`; this is evidence about implementation state, not a durable CLI contract.

### Anneal historical V1

- **Source:** `google/zerocopy@cc135f46155b72e4b51188525c2974a3b84acf92`, `anneal/v1/src/main.rs`, `Commands`, `ExpandArgs`, and `prepare_and_run`. V1 exposed `Verify`, `Setup`, `Expand`, and `Generate` and exposed generated Lean for inspection.
- **Source:** same revision, `anneal/v1/src/generate.rs`, `SourceMapping`, `GeneratedArtifact`, `NamingContext`, and `generate_artifact`. The generator tracked Rust-to-Lean spans and emitted internal names such as `spec` plus generated imports.
- **Documentation:** same revision, `anneal/v1/docs/design/design.md`, sections 7, 9, and 12. It documents V1 `Pre`/`Post`/`spec` generation, Cargo-like CLI behavior, and generated workspace layout. This is historical mechanism documentation, not current authority.

### zCore

- **Source/documentation:** `rcore-os/zCore@8de51f4ee053bcaaf435897febf648bcb4d45479`, `README-arch.md`. It states the original safe-Rust Zircon reimplementation goal, marks the project work in progress, documents Zircon and Linux in libOS and bare-metal modes, and documents official Zircon core-test and Linux libc-test execution.
- **Documentation:** same revision, `docs/README_EN.md`. It describes the current project as based on Zircon with a Linux-compatible mode and preserves compatibility-oriented build commands.
- **Source:** same revision, root `Cargo.toml`, `loader/Cargo.toml`, `linux-object/Cargo.toml`, `kernel-hal/src/kernel_handler.rs`, and `zircon-syscall/src/lib.rs`. Together they show separate Zircon/Linux syscall and object layers over a shared HAL, with feature-selected libOS and bare-metal paths.
- **History:** `rcore-os/zCore@fdcdee0a664d0b9dc6984d2c70043485a7b5f3c9`, commit “add zircon-userboot. support running userboot until syscall.” The diff already describes the project as a safe-Rust Zircon reimplementation and adds userboot loading, illustrating early external-behavior work.

### reL4

- **Source:** `rel4team/rel4_kernel@da74b45b69c89d9e6f43161006f3b586fda41107`, `README.md` and `build.py`. The build can run the Rust kernel or a C baseline inside the seL4 test environment.
- **Source:** same revision, `Cargo.toml`, `src/deps.rs`, `src/object/mod.rs`, `src/cspace/mod.rs`, and `src/kernel/fastpath.rs`. These files show a Rust `staticlib`, C imports, exported compatibility symbols, and an explicitly temporary C-style compatibility module.
- **Documentation/source account:** `oscomp/first-prize-osf2024-StarryOS-yyds@9dc90edc02e78ae79e647e1d1a4200c7cdf85afe`, `doc/2024_OSCOMP_final.md`, subsection “使用 Rust 对 seL4 微内核进行改造.” The authors describe incremental embedding/replacement, bidirectional FFI, deliberate grouping of invasive compatibility code for later removal, object-oriented Rust refactoring, and seL4-native test compatibility.
- **Documentation, moving current source:** ReL4 Book, `https://rel4team.github.io/zh/docs/quick_start/rel4-cli/`, observed 2026-09-30. It distinguishes a legacy “lib mode” linked with seL4 from a developing pure-Rust “bin mode.” Because this page is not pinned to an immutable revision in this report, it is used only as evidence that the project continued to reduce the migration bridge.

### Theseus

- **Peer-reviewed documentation:** Kevin Boos, Namitha Liyanage, Ramla Ijaz, and Lin Zhong, “Theseus: an Experiment in Operating System Structure and State Management,” OSDI 2020, pp. 1–19, `https://www.usenix.org/conference/osdi20/presentation/boos`. The paper says the team chose to write an OS from scratch, explains runtime-persistent cells and intralingual design, and reports roughly four person-years / 38,000 lines of from-scratch Rust along with missing POSIX support and a full standard library.
- **Source/documentation:** `theseus-os/Theseus@1fbfe567075a65ed749b6680db1aeb538819c70c`, `README.md`. The current project still describes Theseus as a new OS written from scratch to explore novel OS structure and intralingual design, and states that it is not yet mature.

A structured evidence index is preserved as `evidence-map.json` in this package. It repeats the immutable coordinates and separates direct source facts from derived Anneal implications.

## Revalidation

For Anneal, revalidate the report by reading three small regions at the new target revision: `anneal/PRINCIPLES.md`, `anneal/DESIGN.md` (especially “Deliberate non-decisions”), and `anneal/README.md`. If the design contract begins promising a CLI, annotation syntax, proof encoding, result schema, or generated-proof interface, this report's conclusion about redesign freedom must be narrowed. Then inspect the current CLI and generated-proof/export code only to determine whether implementation surfaces have become intentionally versioned APIs.

For V1 migration pressure, the cheapest missing check is not another source diff. Survey actual consumers: repository references to `cargo anneal verify|generate|expand`, scripts that parse generated Lean, editor integrations, and external documentation. Classify each dependency as source-level, CLI-level, or generated-proof-level. That evidence determines which compatibility adapters are worth carrying.

For zCore, revalidate the separation between external compatibility and internal architecture by checking the current workspace membership, loader feature graph, HAL boundary, and Zircon/Linux test commands. A change that removes Zircon/Linux compatibility goals or collapses the shared object/HAL structure would weaken its relevance to Anneal.

For reL4, check whether the current kernel still maintains a mixed seL4/reL4 mode, whether compatibility modules remain explicitly temporary, and whether pure-Rust binary mode can run the same seL4 tests. If current reL4 no longer uses the incremental bridge, preserve the historical source revision rather than rewriting this report as though the old snapshot never existed.

For Theseus, the OSDI 2020 paper is fixed historical evidence. Revalidate only if the comparison needs current maturity or compatibility claims; inspect the current README and recent papers rather than projecting 2020 limitations forward.