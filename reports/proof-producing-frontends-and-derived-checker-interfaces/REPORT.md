# Proof-producing frontends and derived checker interfaces

## Summary

CairoZero, Œuf, Verdict and derived inductive checkers export different propositions. CairoZero proves a concrete machine-code specification on halting traces. Œuf validates that a reflected AST denotes the original logical function. Verdict preserves an input specification while generating a matching executable function. QuickChick distinguishes proved acceptance, proved rejection and insufficient search fuel. These mechanisms can remove trust in selected generation stages while retaining the meaning of specifications, semantic encodings and executable wrappers as separate obligations.

## Applicability

Source observations apply to starkware-libs/formal-proofs d0dd8279612a248cbc6bf6d286030bf0bb2a37ff, uwplse/oeuf f3e4d236465ba872d1f1b8229548fa0edf8f7a3f, secure-foundations/verdict 9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67 and QuickChick/QuickChick e35dc8e917f0e36b4ab7cbc66b7d0f7131122588. Publication models are distinct subjects. The retained CairoZero implementation is in lean3; the repository also contains newer Lean4 work, which was not substituted for that implementation.

This comparison answers the mechanism questions P018/P019/P024/P026 and informs P113/P117/P120. It does not certify general unsafe Rust or construct a new Anneal executable checker. No Lean, Rocq, Verus or compiler was run.

## Findings

### CairoZero: machine-bound partial correctness

**Basis: primary paper.** The 2025 long paper generates machine-code descriptions, default specifications and Lean3 proofs. Users separately prove that generated specifications imply their intended specifications; modular calls use those callee specifications. Loops and recursion use bounded halting-trace induction rather than a termination proof. The memory model is read-only over a finite field. A separate cryptographic execution certificate supplies successful execution; the logical compiler proof is not itself a STARK receipt. [Versioned paper, §§2/4](https://arxiv.org/pdf/2501.15002v1).

**Basis: source.** lean3/.../semantics/soundness/hoare.lean:158–171 defines ensures by quantifying over every halting trace starting at the specified register state. Such a trace must reach a state satisfying P with an appropriate step/range-check bound. ensures_ret additionally fixes the return program counter and frame pointer from the input frame. ensures_of_ensuresb:173–177 turns the family of bounded judgments into the unbounded judgment.

The generated ec_is_zero_soundness.lean:24–40 supplies a useful concrete certificate endpoint: assumptions locate code_is_zero and its dependencies at exact memory offsets and relate the arguments to stack locations; the conclusion is ensures_ret with rc_ensures and spec_is_zero. The proof then unpacks the instruction words and steps through them. Code-placement, caller representation and range-check conditions are part of the proposition, rather than informal setup.

This is partial correctness. If there is no halting trace, ensures alone does not prove that execution succeeds. A failing assertion cannot be reclassified as a proved successful execution merely because a conditional postcondition theorem exists. For an Anneal safety goal, determine separately whether the selected source failures are exposed, excluded by a caller premise, or hidden outside the successful-trace judgment.

### Cairo's retained README and actual group proof differ

**Basis: documentation plus source.** The retained lean3 README:141–156 still warns of an associativity sorry. The inspected k1 elliptic_curves.lean:189–202 and r1 file:201–214 instead construct add_comm_group using embeddings into imported mathlib elliptic-curve points; both inspected files contain no sorry. This agrees with the 2025 paper's narrow account that the old gap was removed. The README warning is not evidence of an active admission in those files. Imported mathlib dependencies were not replayed or exhaustively audited.

This illustrates an artifact gate: identify the actual statement and proof dependency before promoting either a historical gap or a publication improvement to the current executable route.

### Œuf: bind the original logical function before compilation

**Basis: primary paper.** Œuf validates reflection through computational denotation, allowing an untrusted plugin to perform early transformations. Its ABI relates logical values to machine representations so related functions applied to related arguments produce related results. The accepted Gallina fragment is restricted; unsupported terms fail reflection. Serialization connects the checked AST to the separate compiler process. [CPP 2018 paper, §§2–3/6](https://homes.cs.washington.edu/~djg/papers/oeuf2018.pdf).

**Basis: source.** demos/list_max/list_max.v:70–82 proves equivalence between the ordinary recursive function and its eliminator-based form. list_max_cu_validate:97–98 equates the reflected compilation unit's denotation with that latter function by reflexivity. Line103 serializes that exact unit. The original function, supported representation and reflected AST are distinct values connected by explicit equalities.

src/Oeuf.v:transf_whole_program separately translates the compilation unit and C shim into Cminor, links them and invokes the CompCert backend, propagating each error. The driver at374–378 parses the compilation-unit file and exits on None. The serialized AST round-trip theorem is examined in the companion parsing report; neither reflection validation nor a format round trip proves an arbitrary C shim's behavior.

### Verdict: retained specification and generated implementation

**Basis: primary paper.** Verdict's policy DSL compiles first-order predicates and bounded quantifiers into executable Verus functions, loop invariants and equivalence proofs. Its promised endpoint is equality to the policy specification; that policy and Verus/Rust tooling remain trusted for the corresponding claims. Separate conformance arguments connect selected policies to external requirements. [USENIX 2025 paper, §3/§4.3](https://verified.how/papers/verdict.pdf).

**Basis: source.** verdict-rspec/src/lib.rs:1582–1607 emits the parsed input spec function, structs and enums, then generates executable versions and View implementations. Lines1455–1477 generate the postcondition equating the executable result's view to the spec call. The generator therefore retains a separately visible specification rather than only checking an unconstrained replacement specification.

This is still relative to how the input tokens are parsed and interpreted by Verus. The source macro states a no-name-clash assumption and leaves type/lifetime checks to subsequent processing (1668–1679). Unsupported items return compilation errors. The generated functions carry exec_allows_no_decreases_clause; the inspected generation interface alone is not a general termination certificate. A proof against the retained policy cannot establish that the policy is the intended external standard.

The current README distinguishes cargo verus build from ordinary cargo build without verification, and identifies verdict-bin as an unverified front end. These routes may execute similar Rust code while supplying different checking evidence. The verified-crypto feature and external glue are additional configuration/dependency boundaries; no complete crypto or CLI audit was performed.

### Derived inductive checkers: three outcomes and separate proofs

**Basis: primary paper.** Computing Correctly with Inductive Relations derives fuel-bounded checkers plus soundness/completeness proofs, using producers to instantiate otherwise unknown constructor variables. Insufficient fuel yields None rather than a negative decision. The proofs are about the declared inductive relation, whose independent semantic theorem remains necessary for translation validation. [PLDI 2022 paper, §§3/5/8](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf).

**Basis: source.** QuickChick src/Decidability.v:20 declares decOpt : nat → option bool. src/CheckerProofs.v:19–43 distinguishes:

| Proposition | Required result |
|---|---|
| Positive soundness | Some true implies P |
| Positive completeness | P implies acceptance for some fuel |
| Negative soundness | Some false implies not P |
| Negative completeness | Not P implies rejection for some fuel |
| Size monotonicity | A decided Boolean remains unchanged at larger fuel |

These are different proof interfaces. In particular, positive completeness is not a promise that one selected finite fuel decides every negative case. The generic logical soundness theorem can justify using computation instead of constructing a full constructor derivation, provided its assumptions and actual computation are checked.

tutorials/DerivingProofs.v:290–296 invokes derive_sound and derive_complete for a relation checker. The tutorial also contains active illustrative Admitted declarations at207/210. This investigation does not count the whole tutorial as an admission-free application or infer that every framework theorem depends on those examples. The declared checker proof, supporting typeclass instances and executable extraction must each be identified.

### Independent meaning and maintenance obligations

**Basis: derived.** An Anneal certificate boundary should name three separately reviewable things: the original specification/function, the generated artifact, and the proposition connecting them. A checker of an inductive syntactic relation additionally needs a theorem that this relation implies the required semantics. A machine-code postcondition with a generated weak specification can be mathematically correct while leaving the desired property unproved.

For obligation generation, require a theorem whose conclusion is the independently stated source property when every generated obligation is discharged. Correct proofs of an incomplete set do not establish this implication. The inspected systems offer concrete patterns for some interfaces; this wave did not inspect an artifact proving complete Verus VC generation against an independent Rust semantics.

Maintenance follows the inspected boundary: AST syntax and binding, reflection/denotation, source-fragment changes, code placement and dependency locations, assertion/loop rules, fuel behavior, retained specification meaning, target libraries and executable checking configuration. A future pilot should preserve one original function/specification and inspect the generated proposition before introducing automatic checking across more passes.

## Boundaries

No upstream build, kernel replay, generated executable or benchmark was produced. The retained Cairo Lean3 files and current repository identity are not a claim about all newer Cairo/Sierra/Stwo implementations. The k1/r1 associativity result is selected-source inspection, not a complete axiom audit.

Œuf's dependency bootstrap script follows a moving PrettyParsing repository; this wave identifies the Œuf proof script but does not claim a fully pinned historical dependency build. Verdict's published guarantees do not remove the original policy, Verus verification, Rust compilation or external implementation boundaries. QuickChick's illustrative admissions are scoped to those declarations.

General unsafe Rust, complete VC-generation semantic correctness, all unsupported source constructs, and the actual generated-checker prototype P136 were not established.

## Evidence

- CairoZero arXiv 2501.15002v1, 26-page expanded paper (2025-01-25), §§2/4, PDF pp3/8–9; retained source pin in metadata. hoare.lean path: lean3/src/starkware/cairo/lean/semantics/soundness/hoare.lean, blobd55b2789dd7e284304067f939916b9c3bfb1ef06, ensures:158–171. Generated endpoint: lean3/src/starkware/cairo/common/secp256r1/verification/ec_is_zero_soundness.lean, blobbd32e87a20410a5ff7be011b058a0958120548db, auto_sound_is_zero:24–40.
- Cairo k1/r1 paths: lean3/src/starkware/cairo/common/cairo_secp/elliptic_curves.lean, blobe14a6daacf33c76c3c26475e4cc411a434102d64; corresponding secp256r1/elliptic_curves.lean, blob 5f51895d6e289653d4266c59b6cc2777c0128c8b. lean3/README.md blob 8bf8edcf8e6884b6801bb777bc15fe0eae8f556d.
- Œuf CPP 2018 DOI 10.1145/3167089; current demos/list_max/list_max.v, blob 7c600e5e50b49b584e5cd04d2fbd462802108a35; src/Oeuf.v, blob 8769ab99159b1bd31c7aed887e8426ae09060e5e; src/OeufDriver.ml, blobc246fd446d5d7e12bf151938d4d98d1d3af11211.
- Verdict 17-page USENIX 2025 primary paper, §4.3/PDF p7 and §3/PDF p3. Current verdict-rspec/src/lib.rs, blobe99ca5f032234d65e1f0b40f6334729df3a359a3; README.md blob 55c68346778bd6ca7be66c1aeb8d9c3b7682729c.
- PLDI 2022 DOI 10.1145/3519939.3523707, 15-page primary paper. QuickChick src/CheckerProofs.v, blob 65c2d4f40633c5fed00d8c947ee386cbaa2528fa; src/Decidability.v, blob 7f58551ef921b25c0c104896583a90df50254bf8; tutorials/DerivingProofs.v, blobdd218b5d6c713d217bd2ecf469de84d43438831c.
- Primary papers and pinned public source acquired 2026-10-14; no mirrors or PDF byte hashes stored. Selected file paths, full pins, symbols and narrow coordinates are the reproducible evidence.

## Revalidation

Re-fetch the exact files, compare blobs and check the identified propositions/dependencies with compatible toolchains before claiming proof replay. For reflection, compare the denoted AST to the independently retained function. For the DSL, retain the original parsed spec and audit the generated equality and configuration. For a derived relation checker, check positive/negative/fuel contracts and a separate semantic theorem for the relation. For Cairo, inspect code and dependency placement plus the chosen halting-trace premise.

*Authored by an AI agent acting on joshlf's behalf.*
