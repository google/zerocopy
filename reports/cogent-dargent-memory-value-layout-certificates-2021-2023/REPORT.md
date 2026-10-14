# Memory-to-value certificates and independent layout meaning: Cogent and Dargent

## Summary

An abstract functional value can support imperative reasoning only through a state relation that retains the authority and observations of the concrete computation. The relation must survive mutation and preserve the caller's frame. Separately, getter/setter algebra can hold for a representation that disagrees with the intended byte layout; layout meaning needs its own checked proposition.

This report examines the published Cogent and Dargent bridges and derives a bounded Anneal path. Its small witness distinguishes algebraic consistency from physical-format agreement. It does not certify Rust memory access or a Cogent/Dargent installation.

## Applicability

The theory comparison concerns Cogent JFP 2021, DOI `10.1017/S095679682100023X`, and Dargent POPL 2023, DOI `10.1145/3571240`. The author PDFs were directly inspected. Current upstream versions, generated artifacts, and machine execution are outside this observation.

The Anneal subject is `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`. Its pure `Rust.Layout`, `Rust.Bytes`, and `Rust.Storage` models are compared with the missing concrete-to-abstract state bridge; the papers do not prove those Rust models faithful.

## Findings

### Cogent's propositions separate the semantic shift from concrete nonfailure

Basis: **documentation** — [Cogent author paper](https://www.trustworthy.systems/publications/papers/OConnor_CRJAKMSK_21.pdf), Theorem 4.3, Definition 5.1, Generated Theorem 5.7.

For a typed expression and related environments, an update evaluation yields a value evaluation, a related result, and a frame relation on writable footprints; output read footprints are contained in input read footprints. The concrete-C predicate separately has this shape:

```text
TypedFootprint(U,μ) ∧ R(μ,σ) ⇒
  NF(P(σ)) ∧ ∀(c,σ') ∈ Out(P(σ)).
    ∃u,μ'. UpdateEval(U,μ,e,u,μ') ∧ R(μ',σ') ∧ ValueRel(u,c).
```

`R` relates each store object to the appropriate valid typed heap. The generated overall theorem composes pure embedding, value semantics, update semantics, and monadic C. Foreign functions need specification/refinement and frame obligations; C-semantics fidelity remains a premise. Cogent's core is total and excludes recursion. Isabelle tactics produce program-specific proofs; the general semantic-shift theorem is reusable.

### Dargent separates data refinement from physical-format agreement

Basis: **documentation** — [Dargent author paper](https://trustworthy.systems/publications/papers/Chen_LOKMJR_23.pdf), §§3.4, 4.1–4.5.

Packed records relate to word arrays through generated field getters. High-level functional embeddings remain unchanged. Getter/setter obligations include:

```text
ValueRel(x,v) ⇒ ValueRel(x,get_a(set_a(arr,v)))
a ≠ b ⇒ get_a(set_b(arr,v)) = get_a(arr).
```

These algebraic laws do not fix layout meaning. A separate getter theorem relates `get_b(arr)` to the generic `uval_from_array(type,layout,arr)` on format-valid arrays. For the analogous setter check, §4.4, PDF p.18 (printed 47:18), explicitly says: “We have not yet done the same for setters”. It separately proves outside-field-bit preservation. This is a missing proof reported in that paper, not evidence of incorrect setters or a finding about today's artifact. Layout typing checks compatibility and record-field nonoverlap. The examined framework assumes a little-endian machine; big-endian fields use byte reversal. AutoCorres imports accessor C; Isabelle tactics prove bridges.

### The memory-to-pure bridge is not an encoder requirement for every model

Basis: **derived** + **documentation** — pinned `SEMANTICS.md`, lines 192–225; `ADMISSION_DESIGN.md`, lines 134–232, 605–635.

Anneal's mathematical decoder may forget information, admit several raw representatives of one mathematical value, or impose a conditional specification domain. That is compatible with a useful state relation. It does not follow that every annotated value requires an encoder or an injective representation theorem.

The execution relation has a different responsibility: it must retain whatever is needed to justify each access and each requested observation. For a byte read, the relevant state can include allocation identity, range, lifetime, initializedness, alignment where required, provenance, and permission/interference conditions. A numeric referent bound supplies only one component. The exact components depend on the chosen Rust semantics and primitive; this list is a design obligation, not a claim that a particular published memory model already supplies them.

For a logical mutation `v → v'`, the concrete-to-pure theorem should express both result correspondence and a frame:

```text
R(concrete_state, logical_owned_value, caller_frame)
  ∧ primitive_entry_guard
  ⇒ normal_update preserves R and caller_frame,
     or the bad primitive branch becomes model failure.
```

If an alias can observe a destructive update while the pure model retains the old value, a result-only theorem does not resolve the discrepancy. Either ownership excludes that observation, the model includes the observer/effect, or the operation remains unsupported. A spatial extension can therefore be local: keep pure borrowed values where a frame theorem justifies them; add explicit memory only for the boundaries whose observations demand it.

### Runtime transfers require an operation theorem

Basis: **derived** from the separation of value relation, state relation, and layout meaning; **documentation** — pinned model README, lines 5–22, and `SEMANTICS.md`, lines 169–190.

The same payload value can survive a transfer while padding initializedness changes. A decoder that observes only payload can relate both states, yet a later byte-view or wider read may require information that relation forgot. The state bridge must either prove preservation of every observed byte/initializedness fact or forget the padding facts at all boundaries and reject later operations that depend on them.

Encoding round trips and positional endian theorems do not establish that an actual Rust load/store has access authority, or that a typed copy transfers all physical bytes. Those need separate concrete operation semantics. Likewise, layout sizes and field offsets can be correct even when a pointer is not allowed to reach them.

The pinned `ADMISSION_DESIGN.md` describes narrow initialized-slice copy and Boolean-production boundaries and excludes general storage/provenance claims. Its later extension requirements must not be mistaken for fresh proof of those extensions. This investigation inspected the docs and did not rerun their admission or proof builds.

### A small representation witness

Basis: **execution** — report-owned `layout_witness.py`; **derived** — interpretation.

The witness uses a 4-bit word holding two independent 2-bit fields. Two accessor families, one expected and one swapping the physical fields, both satisfy exact round trip and the distinct-field frame law for every word and field value. The swapped family fails an independently stated field-offset getter law, first at word `1`.

The same script models one initialized payload byte with one initialized padding byte, then forgets padding initializedness during a chosen abstract transfer. Payload decoding agrees before and after; the padding-read guard fails afterwards. This is a constructed relation counterexample, not a test of Rust's implementation or Dargent's code.

These witnesses justify two independent checks in a future certificate: accessor algebra for refinement, and agreement with independently specified external layout/byte observations. A generator emitting both implementation and its meaning must not satisfy the second check merely by defining the meaning through its own accessor.

### Bounded pilot and acceptance gates

Basis: **derived**, proposed work only.

Start with a padding-free initialized byte array and one explicit guarded byte operation. Bind the operation's Rust item, instantiated type, source/configuration, imported AST, and Lean definition. Supply a relation whose concrete entry premises describe incoming access authority without assuming the operation is safe. Prove normal-result correspondence, frame preservation, and exposure of the invalid producer/access branch; then compose with the existing pure encoding theorem.

Add a field accessor only after an independent type/layout description fixes its meaning. Require a format-valid entry relation that covers all permitted library inputs. Mutation controls should change a field offset, endian setting, type instantiation, and bad-input guard independently; each relevant certificate must fail for the corresponding mismatch.

This pilot can reduce trust in one operation's mathematical interpretation. It would leave source import, all unrelated primitives, parser/serialization, semantics adequacy, and final coverage aggregation outside that new theorem unless separately covered.

## Boundaries

- **Not examined:** Cogent/Dargent release source, generated proof artifacts, or Isabelle checking. The equations are publication-level propositions, not rechecked kernel results.
- **Not established:** arbitrary Rust-to-C certification. A C backend theorem would still need a Rust-to-C relation, ABI/FFI validity, source-UB exposure, and correspondence of the C semantics with the intended execution.
- **Known scope distinction:** the published total-language setting does not supply termination handling for arbitrary recursive or diverging Rust programs.
- **Not established:** general typed copies, padding initializedness preservation, provenance, concurrency, interior mutation, and destructor effects for Anneal.
- **Unknown:** cost and scalability of a mixed Aeneas-plus-spatial proof interface. The proposed minimal bridge has not been implemented.

## Evidence

Observed 2026-10-14. No paper-byte hashes were obtained; DOI, author URL, section/theorem number, and page count identify the directly inspected copies. The Cogent author PDF has line-numbered manuscript formatting; use theorem numbers rather than assuming its page numbers match the publisher edition.

| Source | Identity and coordinates | Role |
| --- | --- | --- |
| Cogent JFP 2021, e25 | DOI `10.1017/S095679682100023X`; [publisher identity](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/cogent-uniqueness-types-and-certifying-compilation/47AC86F02534818B95A56FA1A283A0A6); [author PDF](https://www.trustworthy.systems/publications/papers/OConnor_CRJAKMSK_21.pdf), 67 PDF pages; §4.2.3/Theorem 4.3 (PDF pp.34–35), §5.3.2/Definition 5.1 (pp.43–46), §5.3.6/Generated Theorem 5.7 (pp.49–50) | documentation |
| Dargent POPL 2023, article 47 | DOI `10.1145/3571240`; [author PDF](https://trustworthy.systems/publications/papers/Chen_LOKMJR_23.pdf), 27 PDF pages; §3.4/Figs.8–9 (pp.12–14), §§4.1–4.5 (pp.17–19) | documentation |
| Anneal shared models | `google/zerocopy@cce761ad53785973ec2f4a6b13715b770b340c87`, `anneal/lean/README.md`, blob `9799e4c04818c085ac9b3e95bb79dc7ddbe78cc5`, lines 5–34 | documentation |
| Rust boundary | same revision, `verification/aeneas/SEMANTICS.md`, blob `d89909750724dbafb76715e673626023b6cd49fd`, lines 40–90, 169–225 | documentation |
| Admission design | same revision, `verification/aeneas/ADMISSION_DESIGN.md`, blob `bb01b1d5df63f53dd427f9f3dbde84cfa8dd5cdf`, lines 17–111, 134–232, 520–635 | documentation |
| Finite witness | `layout_witness.py`, deterministic Python standard library only; `layout-results.json` records output and bounds | execution |

Local snapshot files were read with clean path-limited Git status. These checks establish the examined bytes' identity, not truth of every documented implementation claim.

## Revalidation

Run `python3 layout_witness.py` from this package. It enumerates every 4-bit word and every 2-bit field value and checks the stated algebra for both accessors. This is a complete finite witness for those definitions, not a proof about other layouts.

For an actual operation certificate, check the value relation, owned/read footprints, entry coverage, mutation frame, and complete bad-input behavior separately. For an actual packed representation, additionally compare getters to an independent type/layout decoder and check setters against the intended preserved/changed bits. For runtime byte observations, inspect the transfer primitive and chosen Rust memory semantics; a pure round-trip lemma cannot revalidate that boundary.

*Authored by an AI agent acting on joshlf's behalf.*
