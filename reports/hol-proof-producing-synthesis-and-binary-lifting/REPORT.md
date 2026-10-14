# HOL proof-producing synthesis and binary lifting

## Summary

Proof production can certify generated syntax or the actual machine bytes, depending on the endpoint. Myreen's compilation through decompilation certifies bytes under a generated machine-state precondition. CakeML synthesis relates a HOL value or monadic transition to a CakeML expression. HolBA lifting relates a binary to BIR, but its lifting predicate explicitly admits assertion failure: a separate proof must rule out that branch before transferring a useful execution property.

## Applicability

This comparison uses the full ESOP 2007 primary paper, the CC 2009 author paper, the JFP 2014 pure CakeML translation paper, the JAR 2020 monadic synthesis paper, and the ENTCS 2007 code-generation paper. The source observations concern independently pinned HOL4, CakeML, and HolBA revisions listed in metadata. They do not establish that current source exactly reproduces any historical paper artifact. The acquired Li/Owens/Slind PDF has 15 pages and SHA-256 `f077d7ef766635bf34c4ea3c46297b0fde5ec88135695034d2c0fd903752bd1c`; its paper subject remains separate from current HOL4 source.

The findings address P004–P007 and adjacent compiler-family mechanisms. They do not certify unsafe Rust, a Rust-to-HOL front end, or any Anneal implementation. Anneal deductions below are proposed proof interfaces.

## Findings

### Per-run synthesis and schemas

**Basis: documentation from primary papers.** Li/Owens/Slind's paper describes recursion-equation-to-assembly compilation using both translation validation and compiler verification. Blech/Poetzsch-Heffter's §2.3, Fig.6, existentially selects `STEPS`, `PCREL`, and `VARMAP`, requires related initial states, and checks each related program-counter pair with `correctstep`. Their §3.2 explains the weak bisimulation argument for equal output traces. Their modeled integers are unbounded; two pseudo instructions are atomic in the presentation. §4 reduces repeated mapping-injectivity proof work through schemas. This is evidence for a particular code-generation phase, rather than a theorem about arbitrary realistic MIPS execution. [ESOP abstract](https://link.springer.com/chapter/10.1007/978-3-540-71316-6_15), [ENTCS paper](https://jblech.net/wp-content/uploads/2013/07/BlechPoetzsch-HeffterCOCV07.pdf).

### The full ESOP paper's mixed certificate pipeline

**Basis: documentation**, Li/Owens/Slind §§2 and 4, PDF pp.2–3 and 6–9. HOL-, ANF and ACF are shallow HOL functions; HSL and CFL have imperative ASTs and operational meanings. Closure/CPS conversion uses proved rewrites. An unverified register allocator proposes placement/spilling, later checked by function equality. ACF-to-HSL validation synthesizes a function using projective Hoare rules and compares it with the original. Those rules retain live unmodified variables. HSL-to-CFL changes the state representation; CFL-to-ARM-like code connects modeled registers/memory. The composed theorem relates generated outputs to the original HOL function.

The input is a total HOL function, not arbitrary Rust. For Anneal, the mechanism supports untrusted placement decisions and reusable semantic rules; it still needs the source failure/progress and memory-authority interface demanded by a Rust claim. This is a **derived** constraint, not an inspected Rust extension or a newly replayed compiler certificate.

### Compilation through byte decompilation

**Basis: documentation from the CC 2009 paper, §2, PDF pp.4–6; source for the current code-generation entry point.** The compiler first emits bytes, then decompiles them into a function `f'` with a machine-code Hoare theorem, and proves `f'=f`. The certificate has the shape `f_pre(input) ⇒ {representation(input) * PC(p) * frame} bytes {representation(f(input)) * PC(end) * frame}`. Its generated precondition includes reachable memory-domain and alignment constraints and machine-exception conditions. Extensions supply previously proved triples. Actual emitted bytes are the decompiler's input, so the assembler is outside this proof's trusted production path. The theorem remains conditional on the processor model and precondition. [Author paper](https://www.cl.cam.ac.uk/~mom22/extensible-compilation.pdf).

At HOL4 pin `166fd15df77be1f2e79dc8592a933b1a65540526`, `examples/machine-code/compiler/codegenLib.sml` imports the decompiler and compilation libraries (line4) and records decompiled results (lines337–345). This corroborates the mechanism's continued source presence; it is not a replay of a historical compiler or a checked certificate for a newly generated binary.

### Pure and stateful representation relations

**Basis: documentation from JFP 2014 §4.3.2–4.4.3, printed pp.16–22.** Pure translation derives `DeclAssum(declarations,env) ∧ precondition ⇒ Eval env code (inv f)`. Recursive cases use the defining induction theorem; unresolved side conditions remain explicit. Datatype invariants connect HOL values to CakeML constructor values. Partially specified functions and equality on closure-containing values require additional restrictions. [Author paper](https://www.cl.cam.ac.uk/~mom22/jfp14.pdf).

At CakeML pin `f73189499bb295f0859dec7ee38c169c48da682c`, `translator/ml_translatorScript.sml:38–59` defines `Eval` by existence of a terminating `eval_rel` result for every initial reference store, allowing an appended fresh-reference suffix. `AppReturns` quantifies over related arguments and initial stores; `Arrow a b f cl` packages that property for every `x`. This is stronger than merely mapping equal input/output values in one test, while still referring to CakeML semantics.

**Basis: documentation from JAR 2020 §3.3–3.5, PDF pp.9–12.** `EvalM` universally quantifies over states satisfying a heap relation, then existentially supplies a clock, resulting states, and a result satisfying a transition relation and frame property. Its `monad` relation separately matches successful returns and raised exceptions. The state relation connects HOL state fields to CakeML references, arrays, and an FFI projection; a flag can prohibit I/O for local-state synthesis. These are substantive state and effect bridges, with user-selected assertions and library lemmas. [Author paper](https://cakeml.org/jar20.pdf).

### Lifting assertions are obligations

**Basis: source.** At HolBA pin `c20c5aeae7c4464c3a5032ee66d9e31324937fe1`, `src/theory/tools/lifter/bir_inst_liftingScript.sml:1831–1880` defines `bir_is_lifted_prog`. It requires a well-formed protected memory interval, instruction bytes in that interval, valid guarded labels, related machine/BIR states, a matching PC, and a live BIR state. Executing to the next address label must end; **only if the result is not `BST_AssertionViolated`** must there be a machine step, unchanged protected interval, and related successor. `bir_is_lifted_prog_MULTI_STEP_EXEC:2049–2074` retains the same assertion-failure guard, preserves code bytes, and allows a running state or jump outside the lifted program.

This is a precise transfer boundary. A lifting certificate does not itself show that lifted assertions hold, that a whole executable remains inside the analyzed region, or that arbitrary machine execution succeeds.

### Derived Anneal interface and maintenance costs

**Basis: derived.** Separate three artifacts: a syntax/byte identity certificate, a representation theorem, and proofs that its preconditions hold for the admitted source executions. A theorem whose concrete-success clause is guarded by an assertion is useful only with an independent assertion discharge; otherwise the model may stop exactly where the concrete program becomes problematic. The same concern applies to generated alignment and domain guards.

The stateful synthesis pattern suggests keeping byte representation and access authority in different assertions. A value invariant can explain encoding; a heap assertion can explain ownership and framing. To accommodate typed loads, alias creation, reallocation, or transfer events, those events must appear in the relation or its supporting semantics. A list-to-array correspondence does not imply this richer authority relation.

Proof generation can use heuristic search and schemas without trusting that search if the final theorem is kernel checked. Maintenance still includes new instruction triples, representation invariants, rules for effects, side-condition automation, and the model of the processor. A fast schema can reduce repeated proof work without broadening the proposition it proves.

## Boundaries

No HOL4, Isabelle, or CakeML build was run. No generated certificate was checked in this investigation. Source files were read at immutable pins; dependent theories, axioms, proof oracles, kernel binary, and complete transitive proof dependencies were not audited. The Li/Owens/Slind theorem was read in the primary paper; its executable artifact, Blech executable artifacts, and current binary release correspondence were not rechecked. No absence-of-admissions conclusion follows from selected source inspection.

The source/pure bridges here concern their own modeled stores and execution classes. They do not establish Rust provenance, concurrent memory semantics, layout authority, or runtime typed-copy semantics. The reported HolBA guard is an inspected definition, not a discovered soundness defect.

## Evidence

- Primary papers: Li/Owens/Slind, ESOP2007, DOI `10.1007/978-3-540-71316-6_15` (full primary 15-page PDF, §§2/4); Blech/Poetzsch-Heffter, ENTCS190(4), DOI `10.1016/j.entcs.2007.09.008`, §§2.3/3.2/4, 17-page author PDF; Myreen/Slind/Gordon, CC2009, DOI `10.1007/978-3-642-00722-4_2`, §2, 15-page author PDF; Myreen/Owens, JFP24(2–3), 2014, §§4.3–4.4, 32-page author PDF; Abrahamsson et al., JAR2020, §§3.3–3.5, 20-page author PDF.
- HOL4 code-generation blob `a753533152d304d8aebcaf27eecbb447096713c4`; CakeML translator-definition blob `10b29a5a165490875bf1c9dbc98f9e96af9661f6`; HolBA lifting-definition blob `e13a9e4d33a6f65d29ed982cfd254109f5f33e4a`. Obtain using the repository/revision/path coordinates above or pinned GitHub raw URLs.
- The ESOP primary PDF was acquired through its [institution-hosted paper copy](https://citeseerx.ist.psu.edu/document?doi=22dc1cedb9a8598565ca3d67139ca9fba0333ec3&repid=rep1&type=pdf) and text-extracted with native PDFKit on 2026-10-14. Other papers were inspected through web text extraction; the Li/Owens/Slind PDF hash is retained above; other PDF byte hashes were not acquired. Publication, author URL, page count, and narrow coordinates are the retained identities.

## Revalidation

Fetch the pinned source paths and compare blob identities. Replay the selected definitions and theorem scripts with their recorded prover dependencies before making a checked-proof claim. For an Anneal pilot, require a concrete pair of programs or bytes, inspect its representation relation and every generated guard, and separately prove guards and failure correspondence. For a new implementation claim, inspect and replay the exact ESOP artifact rather than identifying current HOL4 code with the historical compiler.

*Authored by an AI agent acting on joshlf's behalf.*
