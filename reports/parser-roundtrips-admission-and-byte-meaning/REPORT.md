# Parser round trips, admission and byte meaning

## Summary

Verified parsing can preserve a formal value across a file boundary, prove format-relative rejection, or enforce a unique complete encoding. These are different propositions. Œuf supplies an AST round trip; Narcissus connects relational formats, stateful encoders and decoders; Verdict's current DER interface states stronger non-malleability and prefix rejection. EverParse separates prefix validation, complete-buffer wrappers, arithmetic checks and external stream/probe contracts. None automatically establishes the intended meaning of an independently unspecified certificate grammar or its graph references.

## Applicability

The source subjects are uwplse/oeuf f3e4d236465ba872d1f1b8229548fa0edf8f7a3f, mit-plv/fiat b7757d28f68c39c3c58192a27f217064b0b35e3b, secure-foundations/verdict 9bc18bc5a287c1608dcb74a6eee7b9ca94a62b67 and project-everest/everparse ad9414befa0241e8b3a9c84f9ee979445bad85d4. Paper definitions are publication-specific; current declarations and selected proof scripts were inspected without replay.

The investigation addresses T041/P117 and supports T047/P121. VerParse and a complete alternate ASN.1 compiler survey were not examined. The preserved finite specimen is original and illustrative, not execution of any upstream verified parser.

## Findings

### Œuf: an inverse on serializer-produced ASTs

**Basis: source.** src/Pretty.v:2258–2278 defines print/pretty and parse for compilation_unit, then proves parse_print_id and parse_pretty_id: parsing either generated string returns Some of the same unit. The theorem therefore binds the reflected program value across this serialization boundary.

src/OeufDriver.ml:374–378 reads a file, calls that parser and rejects None. The proof depends on PrettyParsing tree parsing/printing; scripts/build_pretty_parsing.sh clones and pulls its dependency without a pinned revision. This report identifies the Œuf statement and invocation, not a reproducible complete dependency build or proof that file transport is faithful.

**Basis: derived.** Parse-after-print is enough to preserve values that the trusted workflow serialized. It does not alone state that every accepted string is canonical, that alternate strings are rejected, or that malformed references and duplicates cannot be accepted. Those properties require the actual accepted-language and semantic admission contracts.

### Narcissus: relational formats and state agreement

**Basis: primary paper.** Narcissus specifies a relation among source value, bytes and encoder state. Decoder correctness includes state agreement and rejection relative to that format. Theorem 2.3 makes a correct decoder invert a correct encoder; Theorem 2.4 only guarantees an encoding exists for an accepted source value. Exact reproduction of accepted bytes needs unique encodings. The format may deliberately permit padding alternatives and compressed references. [ICFP 2019 paper, §2.2](https://adam.chlipala.net/papers/NarcissusICFP19/NarcissusICFP19.pdf).

**Basis: source.** src/Narcissus/Common/Specs.v:40–68 defines CorrectDecoder for a view V. From a valid formatted prefix, source predicate, related caches and decoder invariant, it returns a related view, the unchanged supplied extension and related updated caches. Conversely, a successful decode yields a consumed prefix admitted by view_format, a decomposition of the original bytes into that prefix plus remainder, View_Predicate and cache/invariant preservation.

CorrectEncoder:70–79 states both success refinement and that None excludes every format result for that source/cache. CorrectDecoderNone:87–110 derives format-relative rejection under its invariant and cache agreement. This is stronger than a test of a few round trips, but remains relative to the chosen format, view and cache relation.

A lossy view is intentionally different from recovering the full original source record. A decoder cache used for compressed references also has a semantic invariant; syntax alone does not prove that a back-reference denotes the intended object. The mathematical interface allows different encoder/decoder cache representations without pretending they are identical.

### Verdict: complete DER and stronger canonicality properties

**Basis: source.** verdict-parser/src/lib.rs:43–96 gives parse_x509_der an explicit contract. Ok must agree with spec_parse_x509_der; other bytes yielding the same spec value must be identical when their length fits usize::MAX; nonempty suffixes must fail when the combined length fits usize::MAX; Err implies the spec parser rejects. The body uses combinator round-trip theorems to discharge those properties. This selected DER endpoint is more specific than an unrestricted inverse claim.

**Basis: primary paper.** Verdict's parser section combines soundness, completeness, non-malleability and prefix security, rather than treating successful decoding as the only requirement. [USENIX 2025 paper, §4.1/PDF p6](https://verified.how/papers/verdict.pdf).

The current library imports Vest properties/combinators. This wave did not replay those dependencies or audit the entire ASN.1/DER standard interpretation, every extension policy or base64 front end. A theorem about spec_parse_x509_der supplies correctness with respect to that named model; matching a normative format remains a separate interpretation question.

### EverParse: prefix and complete-buffer validation differ

**Basis: primary manual.** The 3d language documentation says ordinary entrypoint wrappers accept a valid prefix within the supplied buffer. --complete_wrappers additionally rejects trailing bytes and is available only for the buffer stream binding. Extern/static streams require separate operations. Integer constraints use machine arithmetic; unsafe overflow conditions fail verification rather than becoming unbounded integer arithmetic. [3d language manual, Structs/Constraints](https://project-everest.github.io/everparse/3d-lang.html).

The API manual describes memory/arithmetic safety, format correctness and double-fetch freedom. It also places input-stream/probe implementations and subsequent use of returned field pointers under caller obligations. These declarations do not make an arbitrary callback or mutable transport implementation verified. [3d API manual, Formal guarantees/Input streams](https://project-everest.github.io/everparse/3d.html).

**Basis: source.** lib/everparse/3d/EverParse3d.Prelude.fsti:270–299 requires representable results for byte arithmetic and nonzero divisors; the postcondition relates machine results to the mathematical operation. The generic source contracts expose the obligation rather than silently permitting wraparound.

Current source contains LowParse definitions as well as newer Pulse-based paths. An old filename is not evidence that every current generated route uses it. No selected specification was compiled in this wave, so the exact generated F*/C artifact and its complete checker/extraction dependencies remain unexamined.

### Cached hashes preserve evidence identity only under the selected mode

**Basis: primary API documentation.** EverParse hash checking skips regeneration and verification. Strong mode compares recorded source and output hashes; weak/inplace modes check the source hash while permitting output changes, which the documentation says void verification guarantees. A verified hashing primitive cannot compensate for a mode that deliberately omits the generated output from comparison. [Hash-checking documentation](https://project-everest.github.io/everparse/3d.html#alternate-mode-hash-checking).

**Basis: source.** src/3d/hashchk/HashCheck.fs:6–36 scans in-place hash comments and rejects absent or disagreeing markers. It does not semantically validate the surrounding C text. This is a concrete identity check with a narrower predicate than source-to-C correctness.

The record of hashes itself must have a justified relationship to previously checked artifacts. A newly supplied attacker-controlled manifest cannot acquire that relationship just by containing internally consistent digests.

### Certificate admission needs syntax and semantic rules

**Basis: derived.** For an Anneal format, decide the following requirements independently of a parser generator:

| Input issue | Required admission rule |
|---|---|
| Truncation/trailing bytes | Chosen complete-input or framed-stream policy |
| Duplicate fields or identifiers | Reject ambiguity or define one explicit meaning and prove consumer agreement |
| Unknown fields/versions | Reject or implement a stated compatibility rule |
| Integer lengths/counts | Checked bounds and representation conversion before allocation/indexing |
| Cross-references | Resolved identity, existence, type and scope; cycle rules where relevant |
| Noncanonical byte encodings | Decide whether semantic equality suffices or unique bytes are required |
| Filesystem/stream changes | Relate consumed bytes and events to the artifacts named by the checker |

A correct grammar recognizer need not validate the certificate's semantic graph. Likewise, a well-formed graph can encode the wrong source/model pair. Serialization, semantic admission and source correspondence should export separate propositions that compose over the same objects.

### Original finite specimen: round trip does not force rejection

The preserved serialization_witness.py exhaustively checks a tiny 256-value domain: a canonical encoder writes a version byte and value byte, and both a prefix decoder and complete decoder invert it. The prefix decoder also accepts extra trailing bytes; only the complete decoder rejects them. This is an original finite counterexample to inferring complete-input rejection from round-trip success.

The specimen additionally records the current Python standard JSON decoder accepting duplicate keys, and a local strict decoder rejecting them. Neither parser is claimed formally verified. The result illustrates why duplicate policy must be explicit; it is not evidence about Œuf, Narcissus, Verdict or EverParse implementation behavior.

### Derived adoption and maintenance gates

Select a representation contract before selecting automation: AST equality, view equality, format membership and unique byte identity serve different consumers. Keep failure outcomes explicit and require the same schema/version throughout transport. A parsed certificate should be bound to the intended subject/configuration before checking its relation.

Maintenance includes format definitions, reserved fields, views/caches, integer widths, generated parser code, dependency pins, cached manifests, external streams/probes and output wrappers. Adoption can start with a single schema and discriminating malformed cases, then replay its proof dependencies and bind the actual executable. No performance or proof-cost comparison is inferred here.

## Boundaries

No upstream parser/generator, F*, Verus, Rocq or extracted executable was run. Selected statements and proof scripts are source observations, not new kernel replay. VerParse, complete current ASN.1 conformance and an actual Anneal certificate grammar/graph checker were not examined.

The original finite specimen proves only its own finite behavior. It does not replace an upstream inversion, safety, malformed-input or I/O theorem. Prefix acceptance, lossy views, optional canonicality and external streams remain deliberate scope choices rather than universal parser defects.

## Evidence

- Œuf full pin in metadata: src/Pretty.v, blobf7b0b57b135771118ba4faff82c0a7e93d702372, compilation_unit.parse_print_id:2267–2273/parse_pretty_id:2275–2281; src/OeufDriver.ml blobc246fd446d5d7e12bf151938d4d98d1d3af11211; dependency script blob 3051bd7d32c65a04ad93c2b7a0c6141ae0406143.
- Narcissus ICFP 2019 DOI 10.1145/3341686, 29-page author PDF, Definitions2.1/2.2 and Theorems2.3/2.4, PDF pp10–11. Current Common/Specs.v blob 49a3488b0bfe1bcc6f2b3d07ac3bd93e6c6741ec, narrow definitions 40–79 and rejection lemma 87–110.
- Verdict current verdict-parser/src/lib.rs blob 5a8584d6cc0564513207cdbde2f4f5188995f2bf; common/vest.rs blob 76216c3455a479363eb449a22117284506523331. Primary paper 17 pages, §4.1.
- EverParse current lib/everparse/3d/EverParse3d.Prelude.fsti blob 27c2231886003b7e253781a178b19106cfff1347; src/3d/hashchk/HashCheck.fs blob 8195de81df3fa443b578f7ec6220ff3b000e98f1. Manual states coverage for releases v2025.05.20 or later; exact observed publication text and current implementation pins are separate.
- Original serialization_witness.py and serialization-results.json preserve invocation/output. Run with Python3.14.8 -B -I. Primary acquisition and finite execution2026-10-14; no upstream mirrors or PDF byte hashes stored.

## Revalidation

Retrieve exact source and check the actual parser/serializer propositions, including dependencies. Inspect whether a new endpoint consumes a prefix or complete input, preserves views/cache relations, rejects duplicate identities and handles every semantic reference. Re-run the finite specimen only as an illustrative boundary check. Before claiming executable assurance, connect the selected parser theorem, extraction/compiler route, stream/filesystem semantics and installed artifact.

*Authored by an AI agent acting on joshlf's behalf.*
