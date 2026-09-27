# Assembly and ISA proof boundaries

## Summary

A verification theorem is only as end-to-end as its last modeled machine boundary and the correspondences that connect that model to the artifact that actually runs.

Three systems expose different stopping points.

**CompCert 3.18** proves semantic preservation down to an abstract syntax tree for target assembly. Its own documentation states that printing that assembly, assembling it, and linking object files into an executable are not formally verified. The compiler theorem is therefore stronger than an ordinary compiler test suite but does not by itself prove that the final linked binary executes according to the source program.

**seL4’s 2013 binary translation validation** deliberately closes more of that gap. It proves refinement between the verified C source and the generated binary for the kernel functions covered by the prior proof, validating compilation and linking for that concrete binary. The paper also states its remaining boundary: assembly routines and volatile accesses used for hardware control were omitted.

**CakeML’s 2019 “Verified Compilation on a Verified Processor”** closes a different gap. The authors connect CakeML’s verified compiler to a verified hardware target, Silver, so the theorem reaches hardware-level execution rather than stopping at an ISA-level software model. That result demonstrates that compiler verification and processor verification do not compose merely because both exist; their semantic interfaces must be made compatible.

The reusable lesson is not that every verifier must prove a processor. It is that “verified to assembly,” “verified binary,” “verified ISA execution,” and “verified hardware execution” are different claims. A reference or proof report should name the final modeled artifact, the semantics used at that layer, every unverified transformation after it, and the assumption that connects the modeled ISA to the actual processor.

Basis: **source** + **documentation** + **publication** + **derived** synthesis. No fresh compiler, linker, binary validator, simulator, FPGA, or proof-assistant execution was performed.

## Applicability

This report examines three proof boundaries.

**CompCert 3.18.** The exact source revision is `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`. `VERSION` identifies version 3.18. `driver/Compiler.v` is the whole compiler and semantic-preservation development. The CompCert 3.18 documentation describes the next stage explicitly: the verified compiler produces an abstract syntax tree for target assembly, then ordinary tooling prints, assembles, and links it. The documentation says this assembling/linking part is not formally verified.

**seL4 binary verification.** Sewell, Myreen, and Klein, “Translation Validation for a Verified OS Kernel,” PLDI 2013, extends the earlier seL4 C verification to the binary level for the covered kernel functions. Its abstract says the method checks compilation, including some optimizations, and linking. It also records two exclusions: assembly routines and volatile accesses used to control hardware.

**CakeML plus Silver.** Lööw, Kumar, Tan, Myreen, Norrish, Abrahamsson, and Fox, “Verified Compilation on a Verified Processor,” PLDI 2019, DOI `10.1145/3314221.3314622`, connects the CakeML verified software stack to a verified proof-of-concept processor. The paper’s target is Silver, not an arbitrary commercial processor.

“ISA proof boundary” here means the point where software correctness is stated against a formal machine-instruction semantics. “Hardware proof boundary” means a further theorem connects that instruction-level semantics to a hardware implementation. A project can use a realistic ISA semantics without verifying that a particular chip implements it correctly.

The report does not treat an ISA manual, an assembler, an object-file format, a linker, a loader, an ABI, and a processor implementation as one interchangeable layer. Each can be a separate correspondence obligation.

## Findings

### “Verified compilation” must name the final semantic artifact

Compiler-correctness statements often end at a formal target language. That target may look like assembly or machine code, but the proof concerns the target language as represented inside the theorem prover.

The next physical artifact can differ:

1. an assembly abstract syntax tree;
2. printed assembly text;
3. an object file;
4. a linked executable image;
5. bytes loaded into memory;
6. an ISA-level execution;
7. a concrete hardware execution.

A theorem that ends at step 1 does not silently prove steps 2–7. A theorem that ends at step 6 still assumes that the processor implements the modeled ISA unless hardware verification or another correspondence argument closes that gap.

Basis: **derived** from the three examined systems.

### CompCert 3.18 stops before ordinary assembler and linker execution

CompCert 3.18 proves its compiler passes inside Rocq/Coq and produces a target assembly program in its formal development.

The project’s current compiler page states the boundary directly. Part 3 prints the target assembly abstract syntax tree as concrete assembly syntax, then invokes the system assembler and linker to produce object files and executables. It says, “This part is not yet formally verified.”

That sentence matters because a successful CompCert proof establishes semantic preservation for the compiler’s formal source-to-target translation. It does not make the external assembler or linker part of the proved transformation merely because the command-line compiler invokes them.

The same page also notes that the formal semantic-preservation guarantee applies only to whole programs compiled as a whole. Thus two boundaries coexist:

- the verified source-to-assembly translation; and
- the unverified assembly/linking path used to obtain an executable.

Basis: **source** — exact CompCert 3.18 `VERSION` and `driver/Compiler.v`; **documentation** — CompCert C compiler page.

### An assembly semantics is not a processor proof

A formal target language can define what an assembly instruction is supposed to do. That definition is a software proof interface.

The processor that runs the instruction is a separate implementation. Its correctness question is whether its RTL, gates, microcode, or other implementation refines the architectural semantics assumed by the software proof.

Therefore a verified compiler to a formal ISA model normally carries a hardware assumption: the actual processor behaves according to that model for the executions covered by the theorem. That assumption can be entirely reasonable and explicit. It becomes a problem only when the reporting language collapses “proved against ISA semantics” into “proved on this physical CPU.”

Basis: **publication** — Verified Compilation on a Verified Processor; **derived** distinction.

### Binary validation can close compiler and linker gaps for one concrete artifact

The seL4 binary-verification work takes a per-artifact route rather than proving a general-purpose compiler and linker correct.

The paper starts from the already verified C implementation and proves refinement between the C semantics and the semantics of the generated binary. Its abstract explicitly says this checks “the validity of compilation, including some optimisations, and linking.”

That approach changes the trust boundary. The proof does not need to trust the particular compiler run merely because GCC generated the code. It validates the resulting binary against the verified source-level program.

The guarantee is artifact-specific. A different compiler version, different flags, changed linker behavior, or changed source produces a different binary that must be validated again.

Basis: **publication** — Sewell, Myreen, and Klein, PLDI 2013.

### Binary-level verification still has hardware-facing exclusions

The same seL4 result records an important limit. It handled the functions covered by the prior C proof but omitted assembly routines and volatile accesses used to control hardware.

Those exclusions show why “binary verified” is not automatically “whole machine verified.” Kernels often contain exactly the operations that cross the software/hardware boundary most directly: privileged instructions, device-register access, interrupt setup, context-switch assembly, and boot code.

A verification report must therefore preserve the excluded instruction classes and hardware interactions, not only the nominal fact that the main C code was validated to binary.

Basis: **publication** — seL4 binary-verification abstract.

### Assembler, linker, loader, and ISA are distinct proof boundaries

The stages after a compiler’s formal target can introduce distinct failure modes.

**Printer/encoder.** A formal instruction must be converted to concrete syntax or bytes. A bug can encode a different instruction.

**Assembler.** Labels, relocations, pseudo-instructions, section layout, and instruction encodings can change the produced object.

**Linker.** Symbol resolution, relocation, section placement, relaxation, and runtime support can alter the executable image.

**Loader/runtime environment.** The operating system or firmware maps segments, initializes process state, resolves dynamic dependencies, and supplies ABI/runtime services.

**ISA semantics.** The proof assumes a meaning for executed instructions, exceptions, memory operations, and architectural state.

**Hardware implementation.** A processor must realize that architectural behavior under the conditions modeled by the theorem.

A system may verify several stages at once, validate a concrete artifact after the fact, or carry some stages as assumptions. The important requirement is to keep them separate in trust accounting.

Basis: **derived**, with concrete examples from CompCert, seL4, and CakeML/Silver.

### Translation validation and verified toolchains close different gaps

A verified assembler or linker proves a transformation generically. Translation validation instead checks whether a particular output is related to its input.

The seL4 work uses the latter strategy at the C-to-binary boundary. This can compensate for an unverified compiler/linker run for a concrete artifact if the validator and its semantic foundations are sound.

CompCert uses a general verified compiler transformation but leaves the assembler/linker stage outside its proof.

Neither architecture dominates mechanically. A validated binary can provide a strong artifact-level guarantee without proving the whole compiler correct. A verified compiler can provide a reusable theorem for every accepted compilation but still leave downstream transformations outside its TCB. The two methods can also be combined.

Basis: **publication/documentation** + **derived** synthesis.

### CakeML/Silver shows that two separately verified layers still need a compatibility theorem

Before the 2019 CakeML/Silver work, verified compilers and verified processors already existed. The paper’s motivation states that these efforts had not been compatible enough to yield one end-to-end theorem about running verified-compiled code on verified hardware.

The contribution was not merely to place two verified projects next to each other. The authors extended the CakeML trustworthy-development methodology so the software compiler semantics and the Silver hardware correctness result met at a common boundary.

That is the reusable pattern: proof composition requires semantic compatibility. A compiler theorem over one machine model and a processor theorem over a differently defined architectural model do not automatically compose.

Basis: **publication** — DOI `10.1145/3314221.3314622`.

### A hardware-level theorem is still scoped to a hardware subject

The 2019 result uses Silver, a verified proof-of-concept processor introduced by the paper.

Its hardware-level theorem therefore does not establish correctness of an arbitrary ARM, x86, RISC-V, or other commercial implementation merely because CakeML can target those ISAs elsewhere. Hardware verification is subject-specific.

This illustrates a general identity rule for proof artifacts: the proof must record which processor model and implementation it covers. “RISC-V” or “x86-64” alone is not a sufficient hardware identity when the theorem is about a concrete implementation.

Basis: **publication** — Verified Compilation on a Verified Processor.

### ISA manuals and formal ISA models can differ

A software proof usually uses a mechanized ISA semantics, not prose directly.

The mechanized model introduces another correspondence question: does it faithfully encode the architectural specification relevant to the target? A verified hardware implementation can be proved against the mechanized model, which helps close that gap for the verified implementation, but the model itself remains part of the formal specification/TBC boundary.

For a production verification stack, the report should identify:

- the exact formal ISA model;
- the modeled architectural version/extensions;
- assumptions about exceptions, memory, privilege, concurrency, and devices;
- any correspondence evidence between the model and normative architecture documentation; and
- any hardware proof that a particular implementation refines the model.

Basis: **derived** from the hardware/software compatibility problem highlighted by the CakeML/Silver work.

### Inline assembly and volatile/device access deserve explicit treatment

The seL4 omission is a useful warning for systems-language verification.

Inline assembly and volatile/device accesses often fall outside ordinary language semantics or compiler-correctness theorems. Treating them as opaque externals can preserve modularity, but then the theorem becomes conditional on their specification. Erasing them or modeling them as ordinary pure functions can lose behavior that matters to correctness.

A source-to-model pipeline should therefore identify whether these operations are:

- rejected;
- given formal semantics;
- modeled by an explicit external relation;
- validated against binary/hardware behavior; or
- trusted as assumptions.

Basis: **publication** — seL4 binary-verification boundary; **derived** classification.

### The final assurance statement should name the unresolved suffix of the toolchain

The shortest durable trust statement is not “verified to machine code.” It is a chain.

For example:

> Source proof → verified compiler → formal assembly semantics → **unverified assembler/linker** → executable → **assumed ISA-conforming CPU**

or:

> Source proof → concrete binary validation → formal ISA execution → **assembly/device routines excluded**

or:

> Source proof → verified compiler → formal machine semantics → verified Silver processor → hardware-level theorem.

This form makes the unresolved suffix visible. It also makes later improvements local: a verified assembler closes one edge; binary validation closes another; a processor proof closes the ISA-to-hardware edge.

Basis: **derived** synthesis.

## Boundaries

- **Known not to apply:** CompCert 3.18’s verified compiler theorem does not include its ordinary assembler and linker stage. The project documentation states this explicitly.
- **Known not to apply:** the seL4 2013 binary-validation result omits assembly routines and volatile hardware-control accesses.
- **Known not to apply:** the CakeML/Silver hardware theorem applies to the verified Silver processor subject described by the paper, not arbitrary processors implementing the same or another ISA.
- **Not examined:** this report does not audit current production assembler/linker implementations, ELF loaders, dynamic linkers, firmware, or operating-system loaders.
- **Not examined:** it does not compare Sail, Isla, K, ASL, HOL4 ISA models, or other mechanized ISA definitions.
- **Not examined:** it does not establish a correspondence between any current commercial processor and the formal machine semantics used by Anneal’s dependencies.
- **Not examined:** it does not audit inline assembly or volatile/device operations in `google/zerocopy`.
- **Unknown:** whether a future Anneal proof boundary will end before, at, or after machine-code generation. The current report is a technique/trust-boundary reference, not a current Anneal architecture commitment.
- “Binary-level” does not imply “hardware-level.” A binary proof can still depend on an ISA semantics and hardware-conformance assumption.
- “Hardware-level” does not imply all peripherals, firmware, analog effects, timing behavior, speculative side channels, or physical faults are modeled.
- No fresh **execution** evidence was produced.

## Evidence

### CompCert 3.18

Repository: `AbsInt/CompCert`  
Revision: `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`  
`VERSION` blob: `5fd2882f6f042e89ce617586ce5041f5762c1766`  
`driver/Compiler.v` blob: `60fc74fec1411216425004f6d63567354e146e9c`

The source identifies the whole compiler and semantic-preservation development. The project’s CompCert C page describes the output boundary and says that printing target assembly, assembling, and linking are not yet formally verified.

Documentation: `https://compcert.org/compcert-C.html`  
Commented development: `https://compcert.org/doc/`

Evidence role: **source** + **documentation**.

### seL4 binary translation validation

Thomas Sewell, Magnus Myreen, and Gerwin Klein. “Translation Validation for a Verified OS Kernel.” PLDI 2013, pp. 471–481.

Publication record: `https://trustworthy.systems/publications/nictaabstracts/Sewell_MK_13.abstract`  
Paper: `https://trustworthy.systems/publications/nicta_full_text/6449.pdf`

The abstract states that the work extends seL4 verification from 9500 lines of C to the binary level, checks compilation including some optimizations and linking, and omits assembly routines and volatile hardware-control accesses.

Evidence role: **publication**.

### Verified compilation on a verified processor

Andreas Lööw, Ramana Kumar, Yong Kiam Tan, Magnus O. Myreen, Michael Norrish, Oskar Abrahamsson, and Anthony Fox. “Verified Compilation on a Verified Processor.” PLDI 2019. DOI `10.1145/3314221.3314622`.

Primary conference page: `https://pldi19.sigplan.org/details/pldi-2019-papers/16/Verified-Compilation-on-a-Verified-Processor`  
Author/project preprint: `https://cakeml.org/pldi19.pdf`

The paper explains that previously verified software and hardware stacks did not automatically yield one end-to-end theorem, then connects CakeML to the verified Silver processor to obtain hardware-level correctness statements.

Evidence role: **publication**.

### CakeML compiler background

Yong Kiam Tan, Magnus Myreen, Ramana Kumar, Anthony Fox, Scott Owens, and Michael Norrish. “The Verified CakeML Compiler Backend.” *Journal of Functional Programming* 29, 2019. DOI `10.1017/S0956796818000229`.

The backend compiles through a sequence of verified intermediate languages to machine code for several architectures. This source is background for the software side of the 2019 verified-processor connection.

Evidence role: **publication/background**.

No proof assistant, compiler, assembler, linker, binary validator, ISA simulator, or processor was executed in this run.

## Revalidation

For a future compiler or verifier, identify the proof endpoint before repeating any broad research.

1. Record the exact last target language or artifact covered by the theorem: assembly AST, encoded bytes, object file, linked executable, loaded image, ISA execution, or hardware implementation.
2. List every transformation after that endpoint.
3. For each transformation, classify the evidence as verified transformation, per-artifact validation, tested/unverified tooling, or explicit assumption.
4. Identify the exact formal ISA semantics and architectural configuration used by the proof.
5. Determine what connects that semantics to the actual processor: a verified hardware refinement, a validated implementation, an architectural-conformance assumption, or nothing recorded.
6. Probe inline assembly, volatile/device accesses, privileged instructions, runtime stubs, and startup/loader code separately; these are common places where the main theorem stops.

For a newer CompCert release, the cheapest check is the current compiler documentation plus the exact whole-compiler source. If assembling/linking becomes formally verified, preserve that as a new version-specific result rather than carrying forward the 3.18 boundary.

For a binary-validation system, rerun the validator on the exact release artifact and preserve the validated binary identity. A source theorem plus an old validation result does not cover a rebuilt executable.

For a hardware-linked theorem, record both the formal ISA model and the exact verified processor implementation. Do not generalize a proof about one verified core to other implementations merely because they share an ISA name.