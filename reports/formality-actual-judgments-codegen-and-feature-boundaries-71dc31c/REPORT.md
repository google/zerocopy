# Actual formality judgments, code generation and feature boundaries

## Summary

The pinned a-mir-formality implementation now runs the previously unperformed
judgment/codegen controls. Twenty owned inputs produce the expected distinct
parse, checking, query, code-generation and execution outcomes. Four generated
programs reach `MachineStop` in the repository's vendored MiniRust model. Four
selected upstream normalization/projection tests also pass by direct execution
of already-linked test binaries.

The trusted-body distinction is operational: a reachable trusted helper passes
checking and then fails code generation with `function helper must have
expression body`. An uncalled trusted helper remains accepted but is absent from
the generated reachable program. An uncalled ill-typed function still makes
checking fail. These are different coverage policies with actual consequences.

The selected observer build succeeded. A subsequent Cargo test compilation was
stopped at the assigned disk boundary before any test ran through Cargo. That
stop remains an operational result; the later four direct tests do not turn it
into a completed Cargo suite or full-workspace run.

## Applicability

The subject is `rust-lang/a-mir-formality` at
`71dc31c1b186df1f0a64d8464b8103195902a5a5`. The 423,932-byte public archive has
SHA256 `dacb47547f117edd5ec63ad75dfcf6e78e219c46a7be1cd3f290836a5cb1db8c`.
All 254 original source blobs match the independently fetched, untruncated Git
tree. The only source-tree addition is the owned `examples/owned_e07.rs` observer;
no original source or lock file was edited.

The requested `nightly-2026-04-01` was supplied by the parent in a task-private
toolchain: rustc `48cc71ee88cd0f11217eced958b9930970da998b`, release
1.96.0-nightly, LLVM 22.1.2, and Cargo 1.96.0-nightly `888f67534`. The actual rustc,
Cargo and compiler-driver hashes are retained. The build uses one job, no
incremental compilation and zero debug information. Cargo home, target, temporary
files and compiler cache are task-private. No stable/compiler/dependency upgrade
was substituted. The minimal compiler/Cargo/std components suffice for these
selected targets; this is not the repository's complete requested-component CI.

`Cargo.lock` stays byte-identical. Its 172 registry entries include other
platform/workspace dependencies. Eighty-three exact cached archives were copied
read-only; locked host fetching brought the private cache to 127 archives, all
matching lock checksums. No full mdbook workspace build was attempted.

The executed dynamic subject is this revision's vendored `minirust-rs` with
libspecr=0.1.40, `BasicMemory<x86_64>`, on an Arm macOS host. It is neither current
MiniRust `d821c6e` nor a native x86 execution. Unsafe-call/unsafe-impl negative
inputs are text submitted to the formality DSL; invalid Rust is not compiled or
executed. Python 3.9.6 orchestrates the owned observations.

## Findings

### F1. Generic FnDef calls produce distinct checked instances

Basis: pinned **source**, actual **execution**, inspected derivations/programs.

| Input | Actual result |
|---|---|
| `identity::<i32>(42)` | Checks; generated program has 3 functions; prints 42; `MachineStop` after 21 steps |
| Same generic body at i32 and bool | Checks; 4 functions; prints 42 then true; `MachineStop` after 36 steps |
| i32 instantiation assigned to bool | Parses, then checking rejects |
| Generic call missing its argument | Parses, then checking rejects |

The generated counts comprise main, the required monomorphic identities and the
synthetic start function. Program dumps retain actual types and bodies; the
different outputs distinguish the two instances. The source queue uses resolved
FnDef identifiers and parameters, rather than resolving an arbitrary Rust method
call from its surface spelling. The retained checking derivations expose the
call rule and its argument/type obligations. This runs the existing rule; it
does not prove trait solving, Rust name resolution or monomorphization correct.

### F2. Trusted checking and executable-body coverage differ

Basis: actual **execution** and source-linked rule traces.

The reachable-helper case contains a `trusted fn body` checking leaf with no
body-validation premises. Its caller checks successfully, but `codegen_program`
returns the expression-body error quoted above. The complete error and rule
trace are retained; the rejection is not a crash.

Leaving the same trusted helper uncalled changes code-generation reachability:
main prints 42 and stops after 11 steps, with only main and the synthetic start
in the generated program. Checking still processes the trusted declaration.
Replacing that uncalled helper by an expression body returning bool where i32
is required instead rejects the crate. Thus checking does inspect declared
expression bodies that code generation need not enqueue.

An accepted program can consequently contain assumed trusted leaves even when
its reachable generated program executes. Execution of that reachable program
does not retrospectively establish all declared bodies or the trusted contract.
The separate no-body rule for trait declarations is source-inspected here, not
an additional executed body-implementation test.

### F3. Normalization uses implementations and assumptions, with negative controls

Basis: actual **execution** of `test_prove`, constraints and derivation trees.

Four query inputs separate two paths. A generic `Iterator` implementation for
`Vec<T>` establishes `<Vec<T> as Iterator>::Item = T`; replacing the universally
required output by u32 yields no solution. An explicit associated-type equality
assumption establishes that equality; changing only the required result to bool
again yields no solution. The successful queries each have one returned
constraint result with `known_true=true`; complete proof trees and failed-query
diagnostics are archived.

After listing two complete, already-linked upstream test executables, four exact
test functions also exit0 with empty stderr: `normalize_basic`,
`normalize_into_iterator`, `projection_equality` and
`test_mirror_normalizes_u32_to_u32`. They exercise the upstream expected
substitution/constraint results. No snapshot was updated. Their source Git
identities, executable hashes, dep-info and direct commands are retained.

These are executable derivations of the implementation's judgments. `ProofTree`
is Rust data, not a theorem checked by an independent proof-assistant kernel;
neither successful queries nor those source tests establish a general
normalization or frontend adequacy theorem.

### F4. Feature and owner scope is observable

Basis: actual **execution**, grammar/codegen **source**, explicit census.

A declared `polonius_alpha` gate parses, checks, generates the same 3-function
i32 program and reaches `MachineStop`. This loan-free example does not
distinguish the borrow algorithms. An unknown feature name, cfg attribute,
`macro_rules!`, async function and closure expression each fail parsing. Those
are observed results for the recorded DSL spellings at this revision, not a
global claim about related research or future support.

`feature-and-owner-census.json` records the actual crate-item/body/gate grammar,
the generated-function counts and the rejected feature specimens. Of five
code-generation attempts, four succeed and the reachable trusted case rejects.
Each successful generated program has empty
globals, traits and vtables, matching the inspected constructor.

The observed generated owners are the monomorphic queue and synthetic start of
manually supplied DSL input. No rustc macro expansion, closure shim, generated
async resume/drop body or complete configured-source owner importer is supplied
by this experiment. Parsed ASTs and full checking traces preserve which
declarations were actually checked. Six upstream codegen tests are explicitly
ignored for AliasTy/Derefable support; this is a source census, not six newly
executed failures.

### F5. Safety markers constrain judgments without proving semantic trait laws

Basis: actual **execution** and inspected rule premises.

A safe caller invoking a declared unsafe function parses and is rejected by
checking. An empty unsafe trait with an explicitly unsafe implementation checks;
the otherwise identical unmarked implementation is rejected. These controls
exercise the existing safe-call gate and trait/impl Safety comparison.

The accepted empty implementation supplies no proof of a zerocopy validity,
Send/Sync, length or other semantic invariant. Such library obligations cannot
be inferred from matching safety markers. The earlier open-contract report's
semantic-law controls remain distinct from these actual formality judgments.

### F6. Status and resource boundaries remain explicit

Basis: captured **execution**.

The 20 unique cases comprise 5 parser rejections, 5 checking rejections, 2 failed
queries, 1 post-check codegen rejection and 7 exit-zero outcomes. Four of the
exit-zero outcomes include model execution; the others are successful checking
or queries. Every predicted stage/status and expected machine output agrees.
The first complete run took about 4.99 process-inclusive seconds in total. A
package-only repeat using the same already-built observer reproduces every
semantic output file byte-for-byte for all 20 cases.

The observer build exits0 after 70.00 seconds with a 769,675,341-byte target.
Subsequent selected Cargo test compilation grows the target to 1,110,361,762
bytes. The one-second monitor observes that jump past the 1 GiB limit and
terminates the process group after 2.14 seconds. Cargo exits−15 before producing
test stdout. No broader compile/retry follows. The parent permits retention
under a 1.2 GiB ceiling pending its own cleanup.

Two test executables were already linked. Before direct use, process inspection
confirms no remaining owned compiler process; regular-file, arm64 Mach-O
segment/symbol bounds, exact dep-info and source Git identities are checked.
Dep-info source paths are relative to the recorded Cargo source working
directory. Two `--list` calls and the four exact tests in F3 then succeed. These
observed build associations are not a verified compiler/decoder theorem.

No unexpected native panic/assertion occurred. Preparation diagnostics remain
separate: sandbox archive DNS failure followed by authorized acquisition;
explicit Python `py_compile` denied at its configured nonlocal cache, then
in-memory syntax checking; denied sandbox process inventory followed by the
authorized read-only check; and correction of an inspection assumption that
dep-info source paths would be absolute. No executable ran before the final
identity checks passed. None is relabeled a semantic rejection or hidden.

## Boundaries

This completes the selected E07 execution slice: real pinned judgments/codegen,
trusted-body and generic controls, associated-type queries, safety-marker and
feature/owner observations. The complete Cargo suite, ignored codegen cases,
full workspace, general feature coverage and all borrow-check modes were not
executed. The budget-stopped Cargo command remains stopped.

No Rust-source frontend proof, configured generated-owner completeness,
unsafe-trait semantic contract, compiler-correctness theorem, all-client safety
theorem or current MiniRust/Miri correspondence is established. The compiler,
Rust judgment implementation, macros, vendored core, runtime and owned
input/output transport remain explicit trust premises. P127/P131 and the
stronger source, logic, elaboration and library milestones remain separate.

The scalar runs do not establish physical pointer authority, arbitrary aliasing,
concurrency, unwind fidelity or target independence. Matching selected outputs
and finite operational traces is not universal semantic equivalence.

## Evidence

`support/source.tar.gz`, `source-tree.json` and `source-acquisition.json` bind the
complete original source. `owned_e07.rs`, the 20 fixture inputs and four queries,
`case-plan.json`, `run_cases.py` and `run_phase.py` preserve the owned additions
and actual execution policy. `observed-cases.tar.gz` retains all 114 first-run
case files, including full derivations, rule traces, ASTs, generated programs,
machine outcomes and status records. Compression preserves useful complete
evidence without publishing 29 MB of repetitive plain text.

The phase logs retain locked fetching, successful building and the resource
stop. `direct-tests/` and `direct-test-build-association.json` retain the four
direct tests and prerequisite checks. Tool/driver identities and all 127 cached
archive checksum checks are included; tool binaries and Cargo caches are not.
The source archive includes its original licenses.

Raw originals remain unchanged in private task scratch. Public log copies only
replace declared absolute display-path prefixes. `public-path-projection.json`
binds original/public SHA256 values and identifies each replacement; exact
original prefix strings remain in the excluded private receipt. Input source,
program/proof semantics, statuses and native output bytes are not changed by
that editorial projection.

## Revalidation

With the exact toolchain and a read-only Cargo home containing the recorded
locked archives/index, run:

```sh
python3 -B support/replay_owned.py --toolchain "$APRIL1_TOOLCHAIN" --cargo-home-source "$LOCKED_CARGO_HOME" --workdir "$FRESH_WORKDIR"
```

The helper verifies source/tool/dependency identities, copies inputs into a new
directory, builds only the owned observer with the 1 GiB target guard and runs
the 20 cases. It makes no installation or network request. `--prepare-only`
verifies/copies 254 source blobs and 127 cached dependencies without building;
that preparation path was exercised successfully from this package. A fresh
second build was not performed after the allocation stop. The recorded
package-only repeat reuses the identified observer, as stated in F6.

The helper does not silently rerun the stopped Cargo suite. Repeating upstream
test compilation needs an explicitly sufficient budget. If already-built test
binaries are reused, first bind their identities/source association, list their
tests and run the exact names. A changed outcome, compiler, library, source or
feature spelling needs investigation at its actual parse/check/codegen/runtime
stage; do not weaken an expected result to make a new version appear compatible.

*Authored by an AI agent acting on joshlf's behalf.*
