# Kraken source, AST, layout, and fragment-proof boundaries

## Summary

Kraken `8af78062037bc237b341d20252aafd1797c1bcb7` checks assembly AST semantics under an externally supplied layout. Its X64 file parser first erases dot-directive lines, including data and alignment directives. Fresh parser checks demonstrate that different data bytes can yield identical ASTs, while the layout interface admits zero-size instructions, duplicate labels, and signed-address wrap. Those are correspondence obligations for an importer; successful AST proofs alone do not discharge them.

The pinned baseline supplies eventuality composition and byte-map separation lemmas. The examined fragment/WP proposals were still open on 2026-10-14. Their described bridges must be kept separate from baseline theorems and from executed evidence.

## Applicability

This is an X64 parser/layout investigation plus a source-level account of common and X64 proof composition. The accompanying Lean probe used Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) against a fresh build of the pinned Kraken source, whose requested toolchain is `nightly-2026-09-21`. AArch64 uses the shared layout representation but its parser was not subjected to the same directive specimens. The Python importer experiment accepts one manufactured, relocation-free byte grammar; it is not a general x86 decoder or an object-file proof.

AS02 and AS03 are answered for the demonstrated fidelity and layout boundaries. AS17 is answered for the baseline judgment and the observed proposal states; the proposed embedding/concatenation proofs and mutants were not executed.

## Findings

### Direct parsing and file preprocessing have different subjects

The `parse("...")` elaborator directly applies the X64 parser and constructs an AST at elaboration time. `parseFile("...")` reads a file, calls `stripDirectives`, then parses the retained text. `stripDirectives` retains blank/comment lines, lines not starting with a dot, and dot-prefixed lines containing a colon. It drops every other dot-prefixed line. The keyword list does not restrict stripping: both the recognized-keyword and fallback branches return false. Thus its behavior includes unknown directives as well as `.data`, `.section`, `.byte`, `.p2align`, and CFI lines. [Parser elaborators](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Parser.lean#L26), [stripping implementation](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Parser/Basic.lean#L1167).

The final successful `ParserLayout.log` records:

| Specimen | Observed result |
|---|---|
| Raw `.section .rodata` / label / `.byte 1` / alignment / text / MOV / RET | Direct parser rejects `.section` |
| Same input after stripping | Four directives: two labels plus MOV and RET |
| Change `.byte 1` to `.byte 2`, then strip/parse | Resulting ASTs compare equal |
| Raw `.align 16` | Parser accepts one directive |
| `.align 16` after stripping | Parser accepts zero directives |
| `movq (%rdi), (%rsi)` | Parser rejects two memory operands |
| `syscall` | Parser rejects unsupported instruction |
| `mov $1, (%rax)` | Parser rejects missing width annotation |

The `.byte` test shows loss of source identity, not an accepted executable data block. The raw parser does not suddenly model stripped data. The `.align` test also shows why a parser's supported grammar and the file front end's retained grammar must be inspected separately. CFI removal concerns unwind metadata, not an instruction postcondition.

Kraken's README deliberately allows unencodable ASTs, including memory-to-memory MOV semantics. The observed parser rejects that particular textual form. Therefore the model's AST permissiveness should not be described as proof that every parser accepts it, nor should parser rejection establish that all manually constructed ASTs are encodable. [Model scope](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/README.md#incidental-extensions-to-x64).

Basis: **source** + **execution**.

### Layout is an input, and instruction fetch is over laid-out directives

Common `Layout Directive` contains a start `Int64` and an arbitrary function from list index to `Nat` size. Applying it pairs every directive with its supplied size. `Executable.withAddresses` advances by `Int64.ofNat size`. The representation does not carry a positive-size theorem, encoder/decoder witness, label-uniqueness proof, no-wrap premise, or object-byte identity. The common prefix lemma `directivesAtFromPrefix` only relates two list views of this representation. [Layout interface](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/Layout.lean#L20).

Fresh executions construct two instructions of size zero and observe both in `directivesAtAddress 4096`. A size-one instruction beginning at signed `Int64` maximum places the next directive at signed minimum. Duplicate labels resolve to the first matching laid-out label; an absent label resolves to `-1`. These outcomes are accepted representation behavior, not failed layout validation. [Label resolution and stepping](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L801).

`Instr.interp` emits an execute-access range built from PC and the supplied size. The model does not fetch and decode instruction bytes from `dmem`. Labels consume their supplied size through `Directives.interp`, although their directive semantics merely continue. Consequently a complete byte certificate must relate instruction boundaries and sizes to the actual decoded bytes and constrain label/data/alignment handling. A permission checker over an incorrect external size checks the incorrect range.

`Program.fakeLayout` is a testing layout: its start and most instruction lengths come from hashes; scalar NOP lengths and data lengths have special cases. It is not evidence of actual encoding lengths. [Artificial layout](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/X64/Semantics.lean#L833).

### A narrow byte-binding experiment exposes distinct checks

`binding_probe.py` defines a deliberately small, unverified importer for exactly eight bytes: the chosen MOV-to-RAX signed-immediate form and RET. The specimen is manufactured directly; no assembler, object file, loader, or target CPU participates. Its local certificate binds a SHA256 byte identity, decoded tuple, sizes `[7,1]`, nonwrapping signed layout, and unique boundary labels. The positive specimen passes. Rejected mutants are:

- changed bytes with a stale hash;
- changed immediate with a correspondingly updated hash but unchanged expected AST;
- wrong sizes;
- duplicate or interior labels;
- extra embedded data;
- signed layout overflow.

This execution demonstrates what different certificate fields reject in one explicit protocol. It does not prove the importer faithful to Intel's ISA, prove Kraken's AST-to-bytes relation, or establish a real object-file round trip. An updated hash alone cannot repair a mismatched decoded program. `binding_probe.json` preserves every acceptance/rejection result. The actual pinned s2n-bignum ELF comparison in the companion artifact report provides a separate, real-object specimen.

The expected AST tuple is a supplied test input, not an authenticated theorem identity. Changing both the expected tuple and the bytes creates another specimen; a production certificate consumer would also need an independently bound expected claim.

Issue #5 describes reprinting an AST and comparing assembled bytes as a mitigation; it was observed open on 2026-10-14. That proposal supplies neither a completed generic parser theorem nor a proof that all preprocessing losses are irrelevant. Even a successful round trip needs an explanation of which symbols, relocations, sections, and loader transformations it binds. [Primary issue](https://github.com/AeneasVerif/kraken/issues/5).

Basis: owned **execution**; certificate implications **derived**. The issue is **documentation**, not executed validation.

### Baseline composition and proposed fragment WPs have different status

The pinned common logic provides `eventually_trans`, `eventually_weaken`, and `reg_dec_loop`. These compose eventualities under one chosen transition relation and a supplied invariant. The X64 byte-map separation infrastructure provides local load/store lemmas over explicitly partitioned maps. None of these facts by itself identifies a different host executable's layout or proves a fragment's jumps stay within permitted entry/exit points. [Temporal composition](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/OmniSemantics.lean#L30), [separation-memory lemmas](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/SeparationMem.lean).

The live observations below are descriptions/status snapshots, not proof audits of those heads. `support/pr-observation.json` preserves the complete returned metadata, including each exact head and base.

| PR | Observed state on 2026-10-14 | Head | Described contribution |
|---|---|---|---|
| [140](https://github.com/AeneasVerif/kraken/pull/140) | open, draft, unmerged | `5a23c15f7fba444b5016a4f625229c344455b433` | Relate step1 and straightline; body says final step missing |
| [165](https://github.com/AeneasVerif/kraken/pull/165) | open, non-draft, unmerged | `9f2536e37b40e39245ce3b6d32804695e65e80e3` | Host-relative `Program.wp` and `Program.step1_of_wp` bridge |
| [166](https://github.com/AeneasVerif/kraken/pull/166) | open, draft, unmerged | `4fae14b3e3d78b7c2df5959010b2e9c1a4c32e3e` | `kvcgen64`, instruction specs, scoped WP instance and straightline bridge |
| [161](https://github.com/AeneasVerif/kraken/pull/161) | open, draft, unmerged | `12371fd0e0f99fa692a0fe0f900b1e37293bfe9b` in `sgraf812/kraken` | Separation WP, frame closure, and memory-arithmetic example; broader frame inference described as next work |

A host-relative WP is a useful interface because it can state where the fragment occurs and which exit relation must hold. The proof obligations still depend on the exact Host, occurrence witness, jump and layout assumptions, interpretation, and theorem closure. PR naming or a body excerpt cannot establish those premises. This report did not build those heads or run embedding, concatenation, escaping-jump, or overlap mutants.

## Boundaries

- **Known not to apply:** stripped X64 file input is not a byte-preserving representation of arbitrary assembly files. The data and alignment counterexamples establish this narrowly.
- **Known not to apply:** `Layout`, `fakeLayout`, and execute-access effects are not independent decoding certificates.
- **Not examined:** a proved parser/printer, macro expansion, linker relocation processing, a generic decoder, actual Kraken-to-object witness, and AArch64 parser fidelity specimens.
- **Not examined:** selected theorem closures and concrete embedding/escape/overlap controls for the four PR heads. The baseline composition source review is complete for the named lemmas; the proposed fragment infrastructure remains a genuine research gap here.
- **Unknown:** whether an application-specific assembly subset can prove all discarded directives irrelevant without another importer. The result depends on that subset's data, metadata, and deployment use.

## Evidence

All Kraken source claims identify `8af78062037bc237b341d20252aafd1797c1bcb7`; `source-manifest.json` records exact inspected files and symbols. `ParserLayout.lean` and final `.log` preserve the actual parsing/layout probes. The initial log records an ordinary malformed Lean structure literal and a refused evaluation of its unresolved declaration; it is not successful evidence, and `#eval!` was never used. The corrected final probe exited zero.

`binding_probe.py` and `.json` are self-contained owned execution evidence. PR metadata and issue observations were acquired on 2026-10-14; they apply to that observation and the recorded heads. No PR-specific proof was executed.

Historical command, generated-manifest path and log strings are explicitly path-normalized for publication; `public-path-projection.json` records original and public hashes. Raw process statuses and technical outcomes are unchanged. Historical producer hashes refer to their original observations; the package file manifest binds the published bytes. The retained Rust/Lean program and source-archive bytes are unchanged.

## Revalidation

After building the pinned Kraken source with a named Lean version, set `LEAN_PATH` to its `build/lib/lean` directory and run Lean on `support/ParserLayout.lean`. Compare the dropped-byte and alignment cases, duplicate/missing label results, signed wrap, and zero-size fetch result. Rerun `python3 support/binding_probe.py` to check the local certificate's independent negative controls.

For a new front end, diff `stripDirectives`, direct/file elaborators, and layout/label lookup before repeating broad research. For fragment WPs, fetch the exact selected head, inspect its theorem statements and axiom closure, then execute concatenation/embedding and escaping-jump/overlap controls against that head; observing a PR's changed state is insufficient.

*Authored by an AI agent acting on joshlf's behalf.*
