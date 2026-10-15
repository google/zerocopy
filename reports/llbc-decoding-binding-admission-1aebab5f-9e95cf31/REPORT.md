# LLBC decoding, binding, and partial-result admission at two Charon pins

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The inspected Charon OCaml JSON decoder checks a version string and recursively recognizes the serialized constructor/record shapes. It does not thereby establish declaration closure, well-scoped identifiers, valid substitutions, completeness of the extraction, or semantic correctness. Its top-level envelope accepts exactly two specified fields, or those same fields followed by **one arbitrary third association**, which it discards. In normal Rust serialization that third field is `has_errors`, indicating a partial crate. The inspected Aeneas load path cannot recover that discarded envelope flag from the returned crate.

This is an information-loss boundary, not demonstrated unsound acceptance. Per-item errors remain represented; later checks and caller policy can reject inputs. Rust-side checking is best-effort and distinct from decoding. Identifier and binder helpers do not constitute intrinsically well-formed syntax or a verified validator.

## Applicability

This report addresses A11 (admission and completeness) and A12 (syntax, binding, substitution). It directly examines:

- Charon `1aebab5f03a58067e5dc0ede2fec584117f54964`, named by Aeneas's `charon-pin` as its compatible dependency.
- Charon `9e95cf318e3a2964fcf5e03104cde5b718f98ea5`, the separately identified upstream subject.
- Aeneas `21345f80fa212c596f6437378d7d57984fa2ea77`, for its load, preprocessing, supported-type, synthesis, and error-output paths.

The two Charon revisions are not interchangeable merely because both report version `0.1.291`. Exact Git trees show equal blobs for the selected OCaml decoder/generated representations, identifier and substitution modules, Rust export/krate/bodies/vars/substitution/trait-proof files. The Rust `typecheck_and_unify.rs` blobs differ and were inspected separately for the claims below. This is a selected-file comparison, not an assertion that all files or behavior match. `source-reading.json` records exact subjects, blobs, ranges, and unresolved questions.

Acquisition was through read-only GitHub tools on 2026-10-15. No decoder probe, malformed input, build, compiler run, or proof check was executed. The `.llbc` JSON path is central here: Aeneas `Main` calls `crate_of_json_file`; this decoder explicitly rejects a file detected as Postcard. Postcard has a separate deserializer and is not covered by the JSON-envelope findings. [`Aeneas charon-pin`][source-1], [`OfJson.crate_of_json_file`; L55–67][source-2].

## Findings

### 1. The serialization envelope and the decoded crate have different information

Basis: source + documentation. Rust `CrateData` contains `charon_version`, `translated`, and `has_errors`; its documentation says a true error flag means the crate is only a partial description of the input. Construction takes the flag from `TransformCtx.has_errors()`. The Rust deserializer compares the serialized version string to the current program version. [`export.rs` at compatible pin; L14–83][source-3], [same region at upstream pin; L14–83][source-4].

The OCaml top-level pattern is precisely:

```ocaml
`Assoc [("charon_version", charon_version); ("translated", translated)]
`Assoc [("charon_version", charon_version); ("translated", translated); _]
```

It parses the first value as a string, compares it for equality to `CharonVersion.supported_charon_version`, decodes `translated`, and constructs the client `crate`. The third pair's **key and value are both ignored**. The pattern is not a generic dictionary lookup: the first two fields have the shown order; there can be exactly zero or one additional pair; additional fields or reordering do not match these branches. These are source-pattern facts, not empirically tested parser behavior. [`OfJson.crate_of_json`, compatible pin; L21–53][source-2], [upstream pin; L21–53][source-5].

`supported_charon_version` is `"0.1.291"`, generated from Cargo metadata. It is a schema compatibility guard, not a cryptographic statement that the payload came from either exact commit or was emitted by Charon at all. An unchanged version string cannot distinguish these two commits. Strong artifact identity therefore needs the producer pin and extraction/build inputs in addition to the serialized string. [`CharonVersion.ml`; L1–3][source-6].

The wrapper also constructs a reduced client crate from `translated_crate`: it retains options, target information, names, ordered declarations, and declaration maps; it does not expose the envelope flag. The generated decoder parses `runtime_checks` and `files`; those fields do not appear in the wrapper's returned record. Files have deserialization-context uses, so “not returned as a crate field” does not mean their contents are ignored during decoding. The policy effect of not retaining `runtime_checks` was not traced here. [`translated_crate_of_json`; L4021–4123][source-7].

### 2. The admission consequence is conditional and narrower than accepted unsoundness

Basis: source + derived. Aeneas `Main` loads the returned crate, clears short names, checks `options.preset = Some Aeneas`, applies its own prepasses, and translates or borrow-checks. Its final `has_errors` local is computed from Aeneas's own `Errors.error_list`, after work has occurred. The inspected load path has no envelope flag available to require a wholly error-free upstream extraction. [`Main.ml`, loading and preset; L583–602][source-8], [final status; L755–812][source-8].

Derived conditional risk: **if** a downstream use treats successful decoding plus a locally successful translation as evidence that the entire requested Rust target was extracted without omissions, the discarded partial-output indicator cannot justify that inference. This report does not show that any malformed or partial input passes all later checks, generates a hole-free target, or supports a false theorem. It also does not show that a particular build wrapper fails to reject Charon's process status or log errors. Those are independent checks that could enforce a stronger admission policy.

A theorem about a selected definition can remain valid under explicit model assumptions while the requested crate is incomplete. Completeness additionally identifies requested roots/target, present dependencies, opacity, errors, and bodies. Schema recognition does not check that closure.

### 3. Generated decoding recognizes structure, not all well-formedness conditions

Basis: source. `Generated_OfJson.ml` is partly generated from templates and AST generation tooling. Most decoders match exact serialized constructors/field lists, recursively call subdecoders, and accumulate errors using `combine_error_msgs`. For example, `fun_decl_of_json` independently decodes `def_id`, metadata, generics, signature, source, and body, then forms a record; it does not in that function prove the body has the signature's type or that all referenced declarations exist. [`generated decoder provenance`; L1–27][source-7], [`fun_decl_of_json`; L2825–2845][source-7].

| Representation case | Checked by the inspected decoder | Still requires separate evidence |
| --- | --- | --- |
| Scalar identifier | JSON integer and identifier-specific wrapper | Nonnegative/range constraints and reference validity |
| Index vector | List of values; index decoder parameter unused | Each reference is in range and each stored declaration ID agrees with its slot |
| Optional indexed map | List of optional values, converted to map keyed by list positions | Meaning of holes, closure of references to absent entries, key/record-ID coherence |
| Index map | List of key/value pairs | Key uniqueness or semantic consistency of target mappings |
| Binder | Parameter record and payload decoded; serialized `kind` ignored in this decoder | Scope correctness and compatibility of uses under that binder |
| Trait reference | Proof-form constructor plus claimed trait declaration reference decoded | The proof form establishes that claimed trait with the instantiated arguments |

`index_vec_of_json` simply delegates to `list_of_json` for values. `opt_indexed_map_of_json` preserves optional positions and `map_of_indexed_list` drops `None` while retaining the original positional index as key. Thus sparse maps are represented deliberately; decoding is not evidence that every hole is unreachable. `index_map_of_json` returns a pair list, not a uniqueness-checked mathematical function. [`index_vec_of_json`; L965–976][source-7], [optional map decoder; L61–69][source-7], [pair-list map decoder; L3074–3087][source-7], [`map_of_indexed_list`; L288–297][source-9].

Deduplication accepts untagged values, a full `Value [id; value]` stored with table replacement, or an earlier `Deduplicated id` lookup; absent keys return an explicit mismatch error. Tables exist separately for types, trait references, constants, sizes, inhabitedness, and spans. This avoids repeated serialized payloads; it is not an ownership/freshness proof for IDs. The module-level `empty_of_json_ctx` is a mutable-table value reused by `crate_of_json`; multi-call reset/isolation behavior was not tested, and the inspected CLI processes one file. [`dedup_val_of_json`; L25–50][source-7], [`DeserializationCtx`; L23–42][source-10].

### 4. Partial, opaque, target-dispatch, and external bodies remain distinguishable

Basis: source + documentation. The Rust body sum distinguishes structured and unstructured bodies; target dispatch; extern and intrinsic bodies; intentionally opaque bodies; missing bodies; and translation-error bodies. Target dispatch maps target triples to function references. The OCaml decoder preserves these as distinct variants, including error span/message. A normal `.llbc` body is therefore not merely `Some body` versus `None`. [`Body`, upstream pin; L27–81][source-11], [`body_of_json`, compatible pin; L2347–2382][source-7].

Per-item metadata also retains `has_errors`, opacity, source text, locality, origin information, language/diagnostic items, and attributes. This is distinct from the discarded envelope flag. It is incorrect to say all upstream error metadata vanishes. Conversely, preserving it is not equivalent to enforcing rejection wherever it appears. [`item_meta_of_json`; L3163–3209][source-7].

Aeneas's transparent-body dispatcher symbolically executes `StructuredBody`; for `TargetDispatchBody` it directly constructs `SymbolicAst.TargetDispatch`; other variants yield no symbolic body there. Its prepass recovery records an error and replaces the function body with `ErrorBody`. Later body translation can yield an absent pure body, and extraction can emit `sorry`/admission forms. These paths must remain distinguished when assessing a completed target: an intentional external model, a target façade, an extraction failure, and an unavailable body have different justification needs even if some ultimately print as declarations without executable bodies. [`Translate.translate_function_to_symbolics`; L22–51][source-12], [`PrePasses` recovery; L2343–2364][source-13], [`Extract` holes; L703–741][source-14].

### 5. Identifier namespaces prevent mixing kinds, not dangling references

Basis: source + documentation. OCaml `Identifiers.IdGen()` is generative: type, function, field, local, and other identifiers from separate instances are distinct opaque types to the OCaml compiler. Internally the representation is an integer, and `of_int`/`to_int` provide conversion. JSON decoding is exactly `OfJsonBasic.int_of_json`; the inspected branch performs no nonnegativity or context-membership check. `nth` delegates to `List.nth`; `update_nth` can raise out-of-range; fresh-generation increment checks integer overflow. [`Id` rationale; L3–31][source-9], [implementation; L174–274][source-9].

Derived distinction: identifier kinds prevent mixing field/function IDs, but do not prove membership in a crate/body or agreement of positional keys with internal `def_id`. Decodable negative/out-of-range IDs may fail later; final acceptance was not tested.

### 6. Binders use de Bruijn depth plus a variable namespace

Basis: source. `de_bruijn_var` is `Bound (depth, variable_id)` or `Free variable_id`. The outer item binder can use free variables; inner binders add de Bruijn depth. The OCaml depth is an integer decoded as an integer, with no decoder-side binder-stack proof. Generic binders carry generic parameters and a payload. The serialized binder's `kind` field is matched and ignored in `binder_of_json`; this describes an intentional representation projection and does not imply every role-specific invariant is unnecessary. [`Generated_Types`, binding representation; L45–84][source-15], [`binder_of_json`; L315–329][source-7], [`de_bruijn_var_of_json`; L692–715][source-7].

The Rust `BindingStack`/`BinderSlice` maps a bound depth from the innermost end of the stack and maps a free variable to the outer item level. `get_var` combines depth lookup with variable lookup and returns `Option`; this is a runtime validity test, not a type-indexed membership witness. [`vars.rs`, lookup; L475–496][source-16].

OCaml substitution distinguishes substituting free variables, substituting depth-zero bound variables, removing the depth-zero binder while decrementing outer depths, and moving under a binder. On entering a binder, `shift_subst` adjusts both the substitution's domain depth and its outputs; the visitor applies that shifted substitution to parameters and body. Trait substitutions additionally handle clause region arguments. Removing a binder with an unexpected bound variable can explicitly fail through `error_sb_subst`. [`Substitute.ml`, operations; L74–211][source-17].

Rust substitution likewise tracks depth and substitutes the binder being removed, decrementing outer bound variables, leaving free variables alone, and moving replacement values under the current depth. Fallible methods return `GenericsMismatch`; some infallible convenience methods rely on caller preconditions and can panic. Moving out from under binders returns `None` when a removed binder still binds a used variable. These are algorithms for avoiding capture, not a located proof of their composition laws. [`SubstVisitor.process_var`; L74–113][source-18], [movement and fallible substitution; L252–328][source-18].

### 7. Rust's checker is a separate best-effort transformation pass

Basis: source + documentation. At both Charon pins, `Check::PostTranslation` and `PostTransformation` run only when `no_typecheck` is false. They skip items already marked `item_meta.has_errors`, maintain a binder stack, inspect references and generic arguments, and may unify body-region identifiers before rewriting those identifiers through the body. They explicitly accept some mismatches within reused default methods. The current checker additionally contains a monomorphization-related permissive ADT-matching branch absent from the compatible pin. These files have different blobs, so line ranges and findings must not be silently transferred. [Compatible checker pass; L769–844][source-19], [upstream checker pass; L779–853][source-20], [upstream permissive matching; L95–142][source-20].

`match_tys` explicitly says it errs toward acceptance because it cannot reproduce rustc's full type equality. It accepts several difficult forms without deciding equality; `match_regions` returns success and unifies body regions when applicable, rather than proving all region equalities. Binder visits can accept type errors in some default-method/associated-type configurations. Invalid bound region/type/const variables are checked by lookup and reported. These are meaningful consistency checks, but not a verified total decision procedure for LLBC well-formedness. [`current binding checks`; L510–555][source-20].

Trait references pair a proof-form constructor with a claimed trait declaration reference. The checker reconstructs the expected predicate for supported clause, parent-clause, associated-item-clause, and explicit implementation cases, applies generic/region substitutions, and compares it to the claimed predicate. Unhandled forms can return success; builtin trait checks have explicit exceptions for traits whose associated types cannot be resolved. This is more than schema parsing, but less than an independently checked proof object for arbitrary trait reasoning. [`match_trait_ref_against_itself`; L175–236][source-20], [builtin exceptions; L610–658][source-20], [decoded proof forms; L1535–1617][source-7].

### 8. Aeneas checks some properties after information-erasing transformations

Basis: source + derived. Aeneas's early preset check precedes preprocessing. Its body-region erasure replaces region variables/body regions in structured statement bodies while preserving function operands specially; local types are also erased. Later type/signature support checks reject certain implied relationships between higher-ranked and free lifetimes. Pure-variable closure checks are gated by `sanity_checks`; pure expression checking is gated by `type_check_pure_code`, both default false. No single pre-erasure verified admission predicate was established by this reading. [`erase_body_regions`; L44–87][source-13], [`bound/free implied-bound guard`; L978–1082][source-21], [`well-binding gate`; L53–98][source-12], [`pure checking gate`; L1293–1303][source-22].

Derived admission obligations are therefore layered: byte format and version; complete producer outcome; valid map/reference graph; well-scoped binders and generic arities; body/type consistency; supported interpreter subset; target/model selection; error-free generated definitions; and elaborated theorem identity. If a property depends on information erased by a pass, either it must be checked beforehand or its adequacy must be recovered from a proved invariant. This is a requirement for a semantic argument, not a finding that the implementation currently accepts a violating input.

### 9. Representation alternatives clarify which properties need evidence

Basis: derived comparison of the inspected representation, not implementation intent.

| Representation style | What it can make explicit | Remaining obligation/tradeoff |
| --- | --- | --- |
| Intrinsically typed/scoped syntax | Constructors carry typing/scope indices, preventing many malformed internal terms | Decoding must produce witnesses; transformations transport indices; richer dependent invariants can complicate efficient graph operations. |
| Raw syntax paired with well-formedness proofs | Existing simple storage plus a separately stated contextual predicate | Every consumer must retain the witness and every transformation preserve it; reflection/checker correctness still needs proof. |
| Raw syntax with verified validators | Efficient decoding/storage, with a small acceptance theorem tied to validator success | The validator must cover the precise semantic preconditions and completeness policy; a shape decoder alone is insufficient. |
| Inspected OCaml/Rust implementation | Kind-separated IDs, binder-aware helpers, selected dynamic checks, typed annotations, error recovery | These safeguards do not intrinsically attach a verified membership/typing witness to every term. |

Needed proof facts include substitution identity/composition, shift commutation, fresh opening/closing inverses, scope preservation, generic/trait substitution validity, and alpha-renaming invariance. Maps/dedup tables/graphs need lookup/update, uniqueness, holes, traversal-order, and identifier-correspondence specifications. No implementation-to-mathematical-structure refinement theorem was checked. This comparison does not prescribe toolchain changes.

### 10. Concrete collection interfaces already expose useful refinement laws

The [finite-map and directed-graph comparison](finite-map-graph-comparison.md) inspects actual Charon/Aeneas OCaml wrappers and Lean 4.35 HashMap, DHashMap, ExtHashMap, TreeMap and Array laws. It distinguishes lookup/domain preservation, quotient equality, ordered enumeration and SCC-level obligations. [finite-map-laws.json](finite-map-laws.json) preserves the law matrix. Source proof declarations were read without compilation; no refinement of the existing OCaml structures or graph algorithm is claimed.

## Boundaries

- **Unknown:** whether any hand-edited malformed/partial JSON reaches a successful complete target translation; whether a producer-status wrapper already excludes every partial artifact; a complete declaration-closure predicate; all duplicate-map behavior in later consumers; and a complete formal admissible LLBC subset.
- **Not examined:** Postcard's admission behavior; all schema-generation templates; every Rust checker case; every Aeneas lookup/recovery branch; multi-file decoder-context reuse; all target-dispatch/model semantics; and malformed-input tests. Exact selected-blob equality does not establish whole-repository equality.
- **Unsupported in identified paths:** Postcard through `crate_of_json_file`; some higher-ranked/free implied lifetime relationships; unhandled body forms in the transparent symbolic interpreter; and other cases rejected later rather than by a single decoder predicate.
- **Known not to imply:** successful version/schema decoding does not certify provenance or well-formedness; per-kind identifier types do not prove membership; preserved per-item metadata does not restore the discarded envelope flag; a generated file or local theorem does not establish whole-target completeness.

## Evidence

All links are pinned primary source. `source-reading.json` records selected comparison blobs and scope; `admission-matrix.json` separates implemented guards, omitted decoder checks, later checks, and unresolved semantic facts. Source and source-comment documentation support implementation findings; conditional risks and representation tradeoffs are explicitly derived. No claim rests on execution or an uninspected mechanized theorem.

## Revalidation

Compare `OfJson.crate_of_json`, `CharonVersion`, and producer `CrateData`; field order, envelope policy, or version changes can alter admission. Compare generated decoder blobs before extending cross-pin claims. Independently check body/error metadata, map conversion, ID decoding, binder-kind handling, and dedup-table lifetime.

Inspect checker gates/skips, permissive matching, binder/trait checks, and error propagation; follow Aeneas preprocessing to see which information remains. Future probes should vary envelope errors, one missing declaration, slot/ID mismatch, bad binder index, target map, or error body. Preserve exact bytes/status/errors/output. None was run here; tests would not replace an explicit admission predicate and preservation theorem.

[source-1]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/charon-pin
[source-2]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/OfJson.ml
[source-3]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon/src/export.rs
[source-4]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/export.rs
[source-5]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon-ml/src/OfJson.ml
[source-6]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/CharonVersion.ml
[source-7]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/generated/Generated_OfJson.ml
[source-8]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Main.ml
[source-9]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/Identifiers.ml
[source-10]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/DeserializationCtx.ml
[source-11]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/bodies.rs
[source-12]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/Translate.ml
[source-13]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/PrePasses.ml
[source-14]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/extract/Extract.ml
[source-15]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/generated/Generated_Types.ml
[source-16]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/type_level/vars.rs
[source-17]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon-ml/src/Substitute.ml
[source-18]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/ast/type_level/substitute.rs
[source-19]: https://github.com/AeneasVerif/charon/blob/1aebab5f03a58067e5dc0ede2fec584117f54964/charon/src/transform/typecheck_and_unify.rs
[source-20]: https://github.com/AeneasVerif/charon/blob/9e95cf318e3a2964fcf5e03104cde5b718f98ea5/charon/src/transform/typecheck_and_unify.rs
[source-21]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/llbc/TypesAnalysis.ml
[source-22]: https://github.com/AeneasVerif/aeneas/blob/21345f80fa212c596f6437378d7d57984fa2ea77/src/symbolic/SymbolicToPureTypes.ml
