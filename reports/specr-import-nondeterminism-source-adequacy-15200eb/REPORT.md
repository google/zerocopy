# Specr import, nondeterminism and Rust-to-core safety boundaries

## Summary

The pinned working Specr tool is a Rust syntax transformer with an executable support library. Its output can be typechecked by rustc, but the inspected tree contains no Specr operational semantics plus proved import theorem, or Rocq/Lean backend. A separate typechecker/compiler project exists in primary documentation; its cited source is inaccessible in this investigation, so the absence of a formal backend across all work is unknown.

Demonic choice, predictive angelic choice, semantic UB, empty behavior, divergence and interpreter failure are different outcomes. The executable library's 50-sample `pick` and unimplemented `predict` cannot decide the corresponding semantic quantifiers. The Rust-to-MiniRust translator makes UB-preservation choices explicitly, yet neither those flags nor an ordinary compiler-refinement theorem establish source-safety reflection.

## Applicability

Source inspection pins Specr `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (0.1.41), MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` and Rust Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. The Reference is a separately pinned comparison, not the documentation version contemporaneous with the earlier MiniRust commit. The accepted 2026 executable-spec goal and two ETH project documents were examined as primary documentation, with URL/document-date identity because their PDF/page bytes were not acquired and hashed here.

The performed experiments are our Python extraction/choice/erasure transcriptions and Lean finite-choice lemmas. They do not run `specr-transpile`, `libspecr`, `minimize`, rustc MIR optimizations or an end-to-end source pipeline. No deliberately invalid Rust is executed. Complete repository tree inventories were inspected: Specr has 77 entries and MiniRust has 401; neither inventory is truncated.

## Findings

### 1. Literate extraction and elaboration are observable semantic boundaries

At this pin `specr-transpile/src/source.rs` gathers Markdown files under each top-level module directory, concatenates the selected code and parses it using `syn`. It uses filesystem enumeration without a sort in the inspected traversal. `filter_specr_lang` recognizes the exact delimiters newline + three backticks + `rust` + newline, and a closing fence followed by newline. `rust,ignore` blocks are intentionally excluded. A formal importer must account for the selected source bytes, module assembly and declaration/arm order, rather than treating all displayed Markdown as code.

Our independently written line collector and a direct control-flow transcription agree on an ordinary documented fence. They discriminate a code fence at byte zero and a closing fence without a final newline: the exact source algorithm respectively skips the former and reaches its unclosed-segment path for the latter. These are boundary inputs, not claims that the pinned MiniRust files have those forms. We model the latter as a classified result and do not trigger the subject's panic.

`main.rs:compile` orders transformations as argmatch, recursive indirection, impl merging, automatic derives, index rewriting and object-bound insertion. Argmatch runs first because it creates match expressions that the recursive-type pass must visit. `argmatch.rs` matches method names, impl structure and nonmatched signature portions, collects submatches in AST order, and produces ordinary match arms.

`typerec/fix.rs` identifies a variant using only its final path segment. It wraps constructions in `GcCow::new` and introduces extracted locals in match arms. The README explicitly documents missing prior name resolution, possible collisions and unsupported reference/ref-mut matching on indirectly stored fields. MiniRust's enum encoder itself avoids a `let ... else` because this pass does not recognize it as a match. A name-resolving formal import must therefore define its own accepted subset or justify agreement; it cannot silently reinterpret these cases with full Rust name resolution.

The support library implements Copy-like collection handles via garbage-collected data. Its documented mutation clones the structure. Preserving mathematical value behavior requires the clone-on-write and mutable-reference rules, not an unproved identification of physical handles with the spec's lists/maps. These implementation/semantic identities were not proved here.

Basis: **source**, Specr `source.rs`, `main.rs`, `argmatch.rs`, `typerec/fix.rs`; **documentation**, pinned transpiler README; **execution**, `support/probe.py` fence discriminators.

### 2. Generated Rust checking does not check Specr semantic preservation

The pinned README describes a newline-separated configuration, but `config.rs:Config::load` actually parses `toml::Table` with required `input`, `output`, `name` and optional attributes/channel/library path. This is a directly observed documentation/source mismatch. Reproduction should follow the actual parser.

The command accepts an optional `--check`; with no option, `check=false`. `main.rs:check` runs `cargo check` in the generated crate and forwards a failed status. That checks generated Rust's syntax/types under its actual dependencies. It does not prove the literate program's effects, recursive calls, copy semantics or import mapping correct.

`libspecr/src/ret.rs` implements a generic monadic return over Option, Result, Nondet and NdResult. `ndresult.rs` explicitly represents its executable combined effect as a wrapper around `Result<T,E>`; `?` returns the inner value and propagates errors, while nondeterministic execution has already selected one sampled value. A formal backend needs an explicit effect interpretation: early return, fallible bind, ordinary choice and predictive choice cannot all be imported as one ordinary Result branch.

Three possible formal routes therefore have different obligations:

| Route | Work that must be justified |
| --- | --- |
| Verified translator | Define the accepted Specr semantics and prove translation/import preservation, including recursion and effects |
| Small trusted elaborator | Pin/audit the parser, resolution and elaboration implementation; kernel checking proves the imported subject conditional on that TCB |
| Proof-producing import | Check source identity, resolved names, coverage and each transformation's semantic certificate against fixed rules |

None is established merely by Rust typechecking. The table is a **derived** comparison of trust boundaries, not a claim that these routes are implemented.

### 3. Existing formal-backend work must be classified by artifact status

The complete pinned Specr tree contains the transpiler/support-library crates and no `.v`, `.lean` or `.agda` files or named formal backend. The MiniRust README describes a theorem-prover translation as future work. These are exact tree/document observations, not a global nonexistence theorem.

Philipp Thiel's *A Type-Checker for Specr* (dated 2025-02-08), §§3–4, describes a separate resolving/typechecking compiler, missing standard-library support, inference, effect handling, early returns and match exhaustiveness. Its appendix identifies `minirust/specr2@49808b490b2ebd4e93be7322760077d949765527`. The public repository commits API and that exact commit page returned 404 here. This report therefore does not attribute inspected code or present-day support to that project.

Jakub Kaššák's 2025-03-24 official project description proposes a Rocq backend, Hindley–Milner inference and additional effect/return/mutation/loop support. This is a planned development, not proof that its backend was completed or verified. The official student-project page links a description but no completed report for that entry. A later or private artifact may exist; it remains **unknown** here.

Basis: **source**, complete pinned trees; **documentation**, [Thiel thesis](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/BachelorTheses/2024-Philipp-Thesis.pdf), [compiler project description](https://ethz.ch/content/dam/ethz/special-interest/infk/inst-pls/plf-dam/documents/StudentProjects/PracticalWork-reports/2025-Jakub-Description.pdf) and [official project index](https://plf.inf.ethz.ch/education/student-projects.html); preserved access result.

### 4. Choice certificates must preserve quantifiers and continuation meaning

The MiniRust README defines ordinary `pick` demonically: correctness is required for every allowed choice. An empty allowed set yields no behavior. It defines `predict` angelically: there must exist a suitable choice; no allowed choice is UB. Its distribution parameter is only an executable sampling hint and does not restrict semantic behaviors.

The executable `libspecr/src/nondet.rs` samples at most 50 candidates for `pick`, then panics if none satisfy the predicate. `predict` is unimplemented. Neither panic is automatically semantic UB. For example, a domain of 4,096 values with one valid candidate has a nonempty semantic choice set, yet 50 legal misses are possible. Our deterministic miss-stream control retains that witness. Under an explicitly assumed uniform independent sampler the miss probability is approximately 0.9878657000; that arithmetic is a property of this constructed distribution, not a measurement of `libspecr` randomness.

| Outcome | Meaning that a validator must retain |
| --- | --- |
| Ordinary choice succeeds on one path | One witnessed execution; no universal safety conclusion |
| Ordinary allowed set empty | No semantic behavior at that choice |
| Predictive allowed set empty | Semantic UB |
| Predictive witness exists | Must also justify its continuation and use at later accesses |
| Divergent path | Not a terminal UB/error result; safety/termination claims differ |
| Sampling budget exhausted or unimplemented primitive | Tool limitation; semantic classification still unresolved |

`Choices.lean` proves empty-set behavior for the chosen predicates, an existential/universal distinction, complete demonic-certificate soundness and angelic witness-certificate soundness. A demonic certificate needs a coverage proof; an angelic certificate needs membership and a proved continuation. The Python probe rejects an omitted bad demonic branch and an unexposed angelic witness.

The 16 Boolean relations are exhaustively classified to show that `∀a.∃p.R(a,p)` and `∃p.∀a.R(a,p)` can differ. This establishes the danger of swapping choice scope. It does not settle MiniRust's full mixed-choice game semantics: sequencing, future-dependent predictions, divergence and exposed provenance require an explicit formal interpretation before selecting one quantifier order for arbitrary programs.

Basis: **source/documentation**, pinned choice definitions; **execution**, owned Python and checked Lean; **derived**, certificate obligations.

### 5. Rust-to-core extraction has safety-relevant stages before execution

`minimize/main.rs:DEFAULT_ARGS` requests `--cfg=miri`, encoded MIR, extra const UB checks, retags, optimization level zero and `-Zmir-preserve-ub`, disables the alignment-check pass and compiler UB checks, then inserts user arguments after defaults. Effective arguments matter: the source does not prevent later user arguments from changing relevant settings. `FnCtxt::new` obtains `instance_mir` and instantiates/normalizes generics while erasing regions.

The inspected lowering maps retags to `Statement::Validate`, with a function-entry flag. Exposed-pointer casts are promoted from assignments to intrinsics; the with-exposed branch has an explicit comment that it is untested because of `predict`. Copy and Move operands both lower to `ValueExpr::Load`. This preserves a typed read but does not, by itself, justify source move/deinitialization behavior; the correspondence must explain the representation of moves and later accesses.

The Drop branch `bb.rs:220–263` extracts a drop function and emits a Call with `unwind_block: None`, while the ordinary Call branch receives its MIR unwind action. This exact omission is a cleanup-edge correspondence question. No executed example here establishes whether a supported input can distinguish it, and no claim is made that every destructor or cleanup is unsupported.

Unsupported statements, coroutine/tail-call/inline-assembly terminators, float casts, closure-to-function coercions and thread-local rvalues have explicit error paths in the inspected source. Their rejection is a translation outcome, not evidence about the Rust program's safety. Constants use a separate translation path; it was located but not fully audited.

Our bad-execution erasure control removes a discarded bad-Boolean load from a tiny source model and obtains a normal-return target. It demonstrates why valid-output refinement on already-safe sources is insufficient for safety reflection. It is deliberately faulty owned lowering, not a measured `minimize` bug. No real paired MIR-to-MiniRust corpus or per-pass proof is produced.

Basis: **source**, `main.rs`, `function.rs`, `bb.rs`, `rvalue.rs`; **execution**, owned erasure control; **derived**, exact correspondence obligations.

### 6. Reference clauses and executable policy need separate identities

The [accepted executable-spec goal](https://goals.rust-lang.org/2026/executable-spec.html) proposes source desugarings, static judgments and MiniRust integration, with authoritative/non-authoritative sections and feature evolution. It treats MiniRust as a candidate source of truth and excludes most standard-library and low-level environment details. This is a development direction, not present authority for every pinned MiniRust rule.

`clause-corpus.json` records five narrow comparisons without running invalid Rust:

| Case | Current pinned Reference | MiniRust pin / classification |
| --- | --- | --- |
| Raw place/address formation without a load | Raw-borrow rules permit places unsuitable for references; load/store and projection obligations are separate | Do not repeat the README's historical broad raw-dereference discrepancy as a verified current disagreement |
| Reference to initialized, invalid Boolean referent | Reference validity includes valid pointee, explicitly debated | MiniRust checks nonnull/alignment/dereferenceability/inhabitedness but explicitly does not inspect pointee data; a policy difference remains |
| Zero-size access or reference | Zero size removes danglingness; reference nonnull/alignment rules remain | BasicMemory zero-size pointer check skips provenance, while load/store alignment occurs first and safe-pointer checks remain |
| Wide-pointer metadata | Valid usize/trait vtable and total-size conditions, with raw-vtable uncertainty | MiniRust has explicit metadata/vtable and dynamic-size checks; no general equivalence claimed |
| Union storage versus Boolean field read | Overall union validity unresolved; field read must be valid at field type | Union chunks can retain Uninit/provenance; decoding a Boolean field still rejects 2/Uninit |

The second case is a documented disagreement/unresolved policy boundary, not an adjudication by interpreter output. MiniRust's typed operations cannot repair an incorrectly chosen method, raw place, metadata type or dropped source computation upstream.

Basis: pinned Reference **normative** clauses and MiniRust **source**; **derived**, classification. The corpus identifies exact anchors and distinguishes unexecuted reasoning from observed tool results.

## Boundaries

- **Established here:** source/transform inventory, a bounded formal-artifact search with explicit access failure, exact executable-choice limits, checked finite quantifier/certificate controls, selected source-safety lowering obligations and a clause-linked comparison corpus.
- **Unestablished:** verified Specr elaboration/import, a complete operational semantics for Specr effects and mixed choices, a formal backend applicable to this MiniRust pin, Rust-to-MIR-to-MiniRust source-safety correspondence or a complete authoritative Rust specification.
- **Not executed:** upstream transpiler/interpreter/minimize, rare-allocation behavior in BasicMemory, actual exposed-provenance execution, paired Rust/MIR/core programs and all intermediate optimization stages.
- **Not examined:** every constant, intrinsic, unsupported branch, source feature/static judgment or target; ownership and aliasing preservation across the whole pipeline.
- **Inaccessible:** the separate Specr2 artifact at the thesis commit. A proposed backend or inaccessible source does not count as checked evidence.
- **MR19:** no modular-effect framework theorem is imported here. Effect handling is an explicit requirement of the missing import theorem.

## Evidence

All evidence was acquired on 2026-10-14. `source-evidence.json` contains pinned files/blob identities and precise symbol spans; `artifact-inventory.json` records tree counts and the narrow formal-file search; `specr2-access.json` preserves the 404.

Primary source entry points are [Specr transpiler](https://github.com/minirust/specr/tree/15200eb5e676e2ee91f43bd79e674f8fc32e5348/specr-transpile), [choice implementation](https://github.com/minirust/specr/blob/15200eb5e676e2ee91f43bd79e674f8fc32e5348/libspecr/src/nondet.rs), [translator](https://github.com/minirust/minirust/tree/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/tooling/minimize/src) and [Reference UB clauses](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/behavior-considered-undefined.md).

`support/probe.py`, `results.json`, `python.log`, `Choices.lean` and `lean.log` preserve the executed inputs/results. Lean exits zero. Empty-choice and existential/universal theorems print `propext` and sometimes `Quot.sound`; certificate soundness lemmas print no axioms. No accepted declaration uses `sorryAx`.

## Revalidation

Rerun the portable Python controls from `support/` and Lean on `support/Choices.lean`. Then diff exact fence extraction, transformation order, variant resolution, effect wrappers and choice implementation. A new backend requires inspecting its actual source, acceptance/unsupported behavior, semantics and theorem; a project description cannot revalidate it.

For source-safety correspondence, retain effective rustc arguments and each selected MIR/core representation, then check the retag, discarded-load, cast and cleanup-edge discriminators. A sampler timeout or unsupported lowering must retain its tool-failure status. Recheck the pinned Reference anchors before carrying any historical discrepancy forward.

*Authored by an AI agent acting on joshlf's behalf.*

