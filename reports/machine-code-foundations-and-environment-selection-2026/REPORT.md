# Selecting machine-code foundations by the missing semantic interface

## Summary

The remaining assembly alternatives contribute specific interfaces. ACL2 x86isa supplies a byte fetch/decode/execute machine with application and system views. K's examined x86 semantics supplies executable rewrite rules and a documented hardware co-simulation workflow. Bedrock2 supplies compiler and event-loop composition interfaces over a configurable RISC-V machine. HOL4/HolBA and CakeML supply the previously investigated byte lifting and hardware-linking mechanisms. None supplies a Rust ABI/resource theorem merely by supporting the same architecture name.

A particularly useful inspected counterexample is RISC-V's MinimalMMIO instance: the abstract machine interface includes fences, reservations and privileged operations, but this concrete interpretation rejects them. Interface constructors therefore cannot serve as a support inventory. Its actual MMIO read rule also requires both a nonempty response set and the postcondition for every allowed response, preventing vacuous success or single-response validation.

## Applicability

Direct source pins, independently observed2026-10-14: ACL2/x86isa `acl2/acl2@2df7fd8b81f0f36964114b09007c17dc7f8d2d28`; K x86 `kframework/X86-64-semantics@592380aea04820ea11cfa5475b343f0257f2474e`; Bedrock2 `mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13`; RISC-V Coq `mit-plv/riscv-coq@45dc8dfc17c77aabb433355b9d39edc6bfd429ae`. The last two are independently selected source subjects, not an established compatible submodule/build combination. No version continuity or fresh execution of these systems is inferred.

The report addresses the additional mechanism-selection questions of AS23, and inputs to AS18/AS24/AS27/AS28. It reuses the exact HOL4, HolBA and CakeML subject boundaries in the existing corpus. The only new execution is an owned finite MMIO response-contract probe; it is not an upstream machine emulator, theorem replay or real MMIO access.

## Findings

### Byte-level x86 modeling and execution modes in ACL2

Basis: **source** and embedded project **documentation**, with **derived** adapter implications.

The x86isa README identifies instruction fetch, decode and execution as the modeled path. `machine/x86.lisp` constructs dispatch from opcode tables, includes prefix and VEX/EVEX dispatch machinery, and maintains the modeled state. Thus this is a potential independent decoding/instruction-model route, whereas Kraken executes laid-out AST directives. A selected x86isa program theorem still needs its exact bytes, initial state, step bound or invariant, postcondition and underlying books inspected; a repository containing machine-code proofs is not itself that certificate.

The inspected `doc.lisp` distinguishes application and system views. Application-view execution avoids simulating the paging machinery; system-view execution represents the physical/linear address distinction and system structures. The documentation describes proving their abstraction relation as outside that account's scope. This is a documentary boundary, not an exhaustive source search establishing that no relation exists anywhere in the project.

Executable integrations are another boundary. `machine/x86.lisp` describes raw-Lisp TTY replacements that perform host I/O, and includes books with a syscall execution trust tag. The build documentation explains optional host syscall execution through dynamic libraries. A consumer must distinguish logical definitions/theorems from raw execution configuration and trust tags; it should not accept a host syscall trace as a proof about a logical environment. We did not execute or certify these books or audit every trust-tag dependency.

For Anneal, investigate a narrow x86isa-to-selected-Kraken instruction relation, or prove directly against selected byte-level x86isa semantics. Both need a bridge from Rust values/resources and the chosen ABI. Switching theorem provers changes proof transport and kernel assumptions; it does not reconstruct Rust provenance from an address.

### K x86 offers a concrete validation workflow, with a pinned tool dependency

Basis: pinned **documentation/source**; no fresh K execution.

The examined README claims a sequential Haswell user-instruction scope of3155 variants/774 mnemonics and reports instruction/program co-simulation. Those are upstream scope/testing claims, not independently repeated counts or an ISA-wide proof. The documented workflow compares the model and real processor after instructions. This is a transferable disagreement-finding technique for Kraken's selected operations; a finite agreement corpus cannot establish universal ISA correspondence.

The same README explicitly warns that a changed K machine-integer syntax breaks compilation with then-current master and names an older compatible K commit or fork. Therefore a future replay must bind the K compiler/backend and libraries as well as the semantics. We did not try an arbitrary present K installation, and the source warning is not a measured failure of every newer tool version.

`semantics/x86-memory.k` decomposes machine integers into labeled byte expressions and reconstructs values with extraction/concatenation. Its default abstract byte is an undefined eight-bit value. Its memory API separately names allocation, load and store operations. These rules offer a source to inspect when comparing byte interpretation, but their presence is not a Rust permission model or a checked binary-loader relation. A complete candidate must identify the imported common-memory rules, undefined-value interpretation, loader and proof backend. We did not audit their full transitive closure or run a K proof.

### Bedrock2 has a concrete compiler/composition endpoint

Basis: direct **source**, plus project **documentation** for orientation.

At the inspected pin `compiler/Pipeline.v` defines each language using Program, Valid and Call, with leakage, trace, memory, arguments, metrics and postcondition components. `phase_correct` requires preservation of Valid and a relation on calls, including explicit leakage transformations and metric bounds. `compose_phases_correct` composes those obligations. The composed pipeline includes flattening, immediate selection, dead-code elimination, register allocation, spilling and the RISC-V phase. These are actual source interfaces, not the much shorter README theorem summary.

`compiler_correct` requires valid source functions and successful compilation, a high-level execution judgment, enough and correctly sized stack space, initial PC, return-address alignment, argument registers, initial trace/metrics and `machine_ok`. It concludes a `runsTo` machine judgment with the high-level postcondition, related leakage, caller-saved register changes, return PC and renewed machine invariant. This is a substantial model-level call/return/frame interface. Its context also requires a well-formed external specification (`ext_spec_ok`), `compile_ext_call_correct`, and `compile_ext_call_length_ignores_positions`; external-call implementations are not justified by the compiler statement alone. It is conditional on its source semantics, external specification, architecture and machine assumptions; no source-Rust theorem follows.

The source explicitly imports functional and propositional extensionality. We inspected theorem statements and proof bodies, but did not kernel-check them or compute per-theorem assumptions. The README's pipeline reaches instruction encoding and describes an event-loop establish/preserve/use interface and a Kami hardware connection. Those broader endpoints remain attributed documentation here; this report does not claim a fresh byte or processor theorem replay.

For a Rust assembly project, a controlled Bedrock2 source route could replace some arbitrary-assembly import work. Its word/byte source domain, documented restrictions on function pointers/recursion and explicit stack discipline also constrain what can be ported. A generated routine still requires exact final-byte binding and a Rust caller relation; the ability to compile a C-like language does not establish either.

### The RISC-V interpretation makes environment promises explicit

Basis: direct **source** and owned finite **execution**.

`RiscvProgram` names register, memory-width, reservation, CSR, privilege, fence and cycle operations. `RiscvMachine` adds translation and timer/counter interfaces. The inspected default instance's translation returns the supplied address without alignment checks, while another helper checks alignment. Source comments deliberately distinguish these configurations. `raiseExceptionWithInfo` describes its simplified machine-mode/no-interrupt scope. Do not replace those selected instances with a generic full-system RISC-V claim.

`Platform/MinimalMMIO.v` gives a concrete environment relation. A nonmemory load requires an MMIO address, permitted alignment/width, existence of an allowed read result, and continuation correctness for every allowed read result. The inspected MMIO load appends an event with empty memory maps; it does not itself implement a Rust ownership or heap transfer. Ordinary mapped stores invalidate executable-address permissions over the written range; fetches require an executable address. The same interpreter returns False for reservations, CSR/privilege operations and Fence. Constructor availability in Machine.v therefore does not prove support in MinimalMMIO.

The owned response probe enumerates candidate sets over{0,7,42}. It accepts a nonempty set whose every result satisfies the required postcondition, rejects an empty set, rejects an allowed bad response hidden by testing only one good result, and separately checks that omitting an event or memory update fails an owned candidate result predicate. That second predicate is a small distinct interface fixture, not MinimalMMIO's actual event relation or an implemented environment adapter. This reproduces the quantifier distinction only; it does not execute Coq, claim a device follows the relation, or add Rust ownership to that byte/event model.

These are useful patterns for the Kraken device-ready experiment: select an explicit environment relation, preserve every permitted response and effect, and reject unsupported actions. A fully general device or concurrency relation is a different scope.

### Reuse existing lifting and hardware results rather than repeat a name survey

Basis: substantively reviewed **corpus/source** results and **derived** selection criteria.

[HOL proof-producing synthesis and binary lifting](../hol-proof-producing-synthesis-and-binary-lifting/REPORT.md) identifies a concrete HolBA transfer guard: a lifted execution's machine-step correspondence excludes the assertion-failed branch. It also identifies compilation-through-decompilation certificates bound to emitted bytes. These mechanisms directly address import/decoder obligations, provided the generated guards and initial-state domain are separately proved.

[Assembly and ISA proof boundaries](../assembly-isa-proof-boundaries-2013-2026/REPORT.md) distinguishes CompCert's formal assembly endpoint, concrete seL4 binary validation and CakeML/Silver hardware composition. A hardware theorem applies to its identified processor, not every implementation of the same ISA. The new CompCert permission report adds the actual every-byte access gate; the s2n experiment adds a real185-byte artifact match.

| Missing obligation | Mechanism worth evaluating | Required additional bridge |
|---|---|---|
| AST to decoded bytes | x86isa decode path; HOL lifting; s2n literal/object import | Exact byte/entry/layout relation and theorem assumptions |
| Instruction disagreement | K's co-simulation method; new Kraken/native corpus | Corpus coverage is finite; an ISA relation remains separate |
| Full access width/permission | CompCert range predicate; Kraken strict interpretation | Complete effect production and Rust authority relation |
| Controlled source compilation/calls | Bedrock2 or Jasmin pass/call relations | Accepted source semantics, external contracts and Rust ABI |
| Device/event environment | MinimalMMIO nonempty/universal response relation | Real environment refinement and ownership transfer |
| Hardware endpoint | CakeML/Silver or identified Bedrock/Kami connection | Exact compatible configuration and selected processor theorem |

This selects reusable mechanisms without ranking projects by repository size or reported instruction counts. We deliberately did not install every ecosystem or port an identical routine to all of them: the completed comparison records source/theorem boundaries and a specific consumer for each route. Cross-prover proof-cost and full common-program ports remain unperformed experiments.

## Boundaries

No ACL2, K, Coq, HOL4, Bedrock2 compiler or hardware build was run. No fresh theorem closure, complete ISA validation, arbitrary binary proof, Rust ABI adapter, relaxed-memory compatibility or device implementation theorem is claimed. Published project scope and build warnings are attributed evidence, not our executed results.

The inspected K version is historical. The ACL2 source is a development commit, not the released ACL2 version mentioned in its root README. Independently chosen Bedrock2/RISC-V pins are not asserted to be a tested pair. Full dependency and raw-execution trust audits remain prerequisites of adoption.

## Evidence

`source-evidence.json` records exact URLs, full source hashes/Git blob hashes, narrow symbols and selected excerpts from ten primary files. Source text was inspected through pinned GitHub endpoints; no mirror is required by the report. The prior HOL/CakeML reports retain their own exact subjects and proof-replay limits. `support/response_contract.py` and `response-results.json` preserve the owned finite controls.

## Revalidation

Re-read the selected decode, phase/call, machine-instance and MMIO interfaces at the intended pins. Check actual concrete interpretations after adding an instruction constructor. Run the finite response probe, then test the same bad-response/empty-response/omitted-effect controls against any implemented adapter. Before accepting an upstream certificate, replay its actual theorem and dependencies and discharge initial-state, guards, environment and final-byte premises. A successful source inspection or project build cannot replace that check.

*Authored by an AI agent acting on joshlf's behalf.*
