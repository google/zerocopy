# MiniRust representation laws, copy observations and provenance coherence

## Summary

MiniRust's representation round trips preserve typed values but can forget padding and provenance. Typed load/store, byte-preserving transfer and integer load/store therefore have different later observations. Decoding a raw pointer's numeric address also does not establish permission to access memory.

The generic representation laws are stated requirements, not proved consequences of every executable well-formedness check. Direct source inspection and a performed branch transcription identify a checker-admitted enum shape whose tagger/discriminator disagree, breaking value round-trip. This is a concrete missing coherence condition for generic proofs, not a claim that rustc produces the specimen. Our bounded search checks seven coherent shapes, and Lean proves selected scalar/projection laws and the isolated enum counterexample.

## Applicability

The principal subject is MiniRust `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, especially `spec/lang/representation.md`, `well-formed.md`, `spec/mem/interface.md`, `basic.md`, `tree_borrows/memory.md` and `intptrcast.md`. The memory implementation, target and access operation are part of any operational claim. MiniRust values contain mathematical integers; machine-sized representation and operator checks impose bounds separately.

A selected comparison uses RefinedRust's 2026 artifact `34573bac60de68c3597c23136cd5221a7129f89a24b69340f8e361750f331d53`, specifically Radium representation helpers. It is not an assertion that either whole language refines the other. Rust pointer documentation was consulted at std 1.99.0, compiler commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`; those APIs describe a comparison boundary rather than defining MiniRust at its earlier pin.

The executed Python model independently transcribes selected equations; it is not generated MiniRust or Miri. Its pointer target is explicitly a two-byte little-endian illustrative target. The bounded byte alphabet is data `{0,1,2,255}`, Uninit, and five fragment forms: absent, A0, A1, B0, B1. Larger exhaustive scalar/value checks are separately recorded. Lean 4.34.1 checks owned structural fragments. No invalid Rust or upstream interpreter was executed.

## Findings

### 1. Decode, validity and permission are three separate judgments

`Type::decode` requires a well-formed sized type and exactly its layout size. Failure means bytes are not a representation at that type. A decoded pointer can still fail `Machine::check_value`: safe pointers require bounded address/metadata, bounded total dynamic size, nonnull, alignment, inhabited pointee and current dereferenceability. The source explicitly does not inspect the pointee's stored value there.

Permission to perform the next access is a further operational matter. BasicMemory's nonzero `check_ptr` requires provenance naming a live allocation and an in-bounds range. Its zero-size path returns before those checks, while load/store alignment is checked first. TreeBorrowsMemory adds allocation/path provenance and access transitions. Its `dereferenceable` does not itself perform an aliasing access. Thus successfully decoding a reference, checking dereferenceability and successfully exercising a tagged pointer are not one interchangeable fact.

These distinctions constrain any zerocopy contract. A byte-validity proof must be combined with the physical range, initialization, lifetime/alignment and actual access interpretation. This report does not close the earlier P131 access/granularity question.

Basis: **source**, `representation.md:468–594`, BasicMemory `check_ptr/load/store`, Tree Borrows memory operations; **derived**, contract obligations.

### 2. The generic laws are information-order laws

The source's byte order allows Uninit to become any byte, and an initialized byte with no provenance to gain provenance while preserving its numeric data. Already present provenance cannot change. Lists are ordered pointwise at equal length. Pointer values can gain absent provenance; integer and Boolean values compare only by equality.

For well-formed values/types and exact-size byte lists, the stated requirements are:

```text
decode(encode(v)) = Some(v)
decode(b) = Some(v) implies encode(v) <= b
v1 <= v2 implies encode(v1) <= encode(v2)
b1 <= b2 implies decode(b1) <= decode(b2)
```

The second equation is a deflation law, not byte equality. Tuples start their encoded buffer with Uninit and write only fields. Union encoding does the same but restores the configured chunks, including their Uninit and provenance fragments. Arrays concatenate element encodings. An enum encodes its selected payload and then writes tags into bytes intended not to hold encoded payload data.

`Representation.lean` proves: reflexivity of the selected byte order; provenance stripping is below the original byte; arbitrary-length masks that retain selected byte positions are deflationary and idempotent; kept positions are unchanged; and provenance-free scalar digit encode/decode has a round trip and deflation. The scalar uses a natural-number digit; restricting it to 0–255 gives the corresponding single-byte domain, but it is not a general proof of multi-byte endianness or bounded integer arithmetic.

The mask law handles the storage projection underlying padding/chunk forgetting. It does not prove that an arbitrary recursive type's actual encoder equals that mask, nor that subsequent alias transitions commute with it. Such an equality/refinement still needs the concrete codec and access proof.

Basis: MiniRust **source** definitions and stated consistency requirements; **execution**, checked owned Lean fragments.

### 3. An enum counterexample separates stated laws from executable WF checks

The enum branch of `Type::check_wf` checks representable discriminants, recursively well-formed equal-sized payload types, sufficient enum alignment, representable in-bounds tag writes and a well-formed discriminator. `Discriminator::Known(d)` only requires that the variant map contain `d`. The source does not compare each variant's tagger with the discriminator; it also retains a FIXME for tagger overlap.

The specimen in `support/enum-wf-counterexample.json` has:

- size/alignment one byte;
- variants 0 and 1, each an empty tuple with a one-byte all-padding layout;
- in-bounds u8 taggers writing 0 and 1 respectively; and
- `Discriminator::Known(0)`.

Both discriminants/tags fit, payloads have the correct size/alignment, and the known discriminator names an existing variant. Layout size is aligned, and no payload field overlaps a tag. A value of variant 1 with an empty payload passes the selected `check_value` structure. Encoding it produces byte 1. Decoding ignores that byte when choosing the known discriminant, then decodes variant 0's empty payload. The result is variant 0, not variant 1.

`enum_wf_probe.py` transcribes the relevant WF, payload, tagger and discriminator branches and confirms this result. `EnumCoherence.lean` checks the arithmetic side conditions and the isolated non-round-trip witness, with no axioms in either final theorem. Neither program invokes the upstream well-formedness checker; the conclusion about checker admission is a **derived** source argument, with all relevant branches retained in the source index.

This does not show that a source-Rust enum or minimize-produced enum has the bad layout. A frontend may maintain an additional invariant. It does show that a proof quantified over arbitrary checker-admitted MiniRust enum types cannot assume the generic round-trip law without a coherence premise or stronger check. Useful coherence requires each tagger to cause decoding to return its own discriminant and preserve the payload's representation. Overlap, nested discriminators and gaps need separate conditions.

Basis: **source**, `well-formed.md:215–243,262–284`, `representation.md:346–433,check_value`; **execution**, owned branch transcription and Lean witness; **derived**, missing executable-WF implication.

### 4. Performed bounded checks support coherent fragments without hiding the counterexample

For each selected shape, the Python model checks successful decoded values round-trip, byte-to-value-to-byte deflation and decode monotonicity over every pointwise ordered pair of the stated alphabet:

| Shape | Byte vectors | Successful decodes | Ordered pairs |
| --- | ---: | ---: | ---: |
| Boolean | 21 | 10 | 57 |
| u8 | 21 | 20 | 57 |
| Thin two-byte pointer | 441 | 400 | 3,249 |
| u8 plus padding | 441 | 420 | 3,249 |
| Two-element u8 array | 441 | 400 | 3,249 |
| Union with one preserved chunk and one gap | 441 | 441 | 3,249 |
| Coherent two-variant enum | 441 | 150 | 3,249 |

Additionally, all 256 numeric byte values with three chosen provenance forms give 768 initialized Boolean cases: six decode successfully, and Uninit does not. All 65,536 two-byte numeric addresses with absent/A/B provenance give 196,608 pointer value round trips. There were no failures in those checks.

Four negative controls reject full byte-round-trip equality, position-insensitive fragment reconstruction, provenance preservation through integer load/store and unrestricted Boolean byte validity. These controls demonstrate that the probe observes the intended distinctions. They are not formal proofs for all arrays, layouts, enums, unions, targets or memory models. In particular, the coherent enum search does not include arbitrary tagger/discriminator pairs; the separate counterexample deliberately does.

Basis: **execution**, `support/probe.py`, `results.json`, `python.log`.

### 5. Equal typed values do not imply equal unsafe storage observations

Consider a tuple containing one u8 field and one padding byte. Starting from initialized bytes [7,99], decode produces the field value 7; encode produces [7,Uninit]. A byte-preserving transfer retains 99. A later integer load from the padding succeeds with 99 after the byte route but fails after the typed route. The Python specimen and `padding_observer_distinguishes` check this distinction.

This is a storage-observation counterexample, not a claim that an arbitrary Rust padding read is permitted. Such a client must first satisfy the relevant access, initialization and alias conditions. It is precisely why replacing typed operations by byte operations, or vice versa, needs a specified observation interface.

Pointers have a second discriminator. MiniRust pointer encoding distributes provenance fragments carrying original byte positions. Complete position-consistent fragments recover provenance. Missing fragments, conflicting provenance or wrong positions decode the same numeric address with absent provenance; Uninit prevents decoding altogether. The probe uses address 0x0101 so swapping the two identical numeric bytes preserves the address while changing fragment positions. Numeric equality therefore cannot conceal what the fragment-position check decides.

Integer decoding ignores provenance and encoding creates absent-provenance bytes. A pointer-to-integer-to-pointer *transmutation* through that codec loses authority even if numeric bytes are unchanged. A byte copy or a typed raw-pointer copy can preserve complete fragments. The report models storage transfers by these equations; overlapping-copy intrinsic behavior and alias effects are not implemented in the probe.

Basis: **source**, `representation.md:50–142,245–342`; **execution**, padding/pointer route specimens and Lean witness.

### 6. Exposure does not restore invalidated allocation or alias authority

MiniRust's `IntPtrCast` records exposed provenances. `int2ptr` predicts absent or previously exposed provenance and combines it with a supplied address. This is separate state from pointer/integer transmutation. BasicMemory still checks allocation liveness/range on a nonzero access; Tree Borrows provenance contains the allocation identity and tree path whose permissions matter.

Our finite compatibility example gives A and B the same numeric address, with A invalidated and B usable. An existential usable exposed choice succeeds, while requiring all exposed tags to work fails. If only A was exposed, there is no usable witness. An address-only wildcard acceptance would incorrectly accept that last case in this toy model. The probe does not implement Miri wildcard provenance or prove it wrong; it identifies the theorem such an approximation must satisfy.

The std 1.99.0 [exposed-provenance API](https://doc.rust-lang.org/std/ptr/fn.with_exposed_provenance.html) leaves exact provenance choice unspecified and states that alias invalidation still applies. Its ambiguity is not an equivalence theorem with MiniRust's predictive semantics. A compatibility theorem must preserve the set/scope of exposed choices, liveness, tree-path authority, address reuse and all continuation accesses. It cannot recover allocation identity solely by matching an address.

Basis: MiniRust **source**, `intptrcast.md`, BasicMemory and Tree Borrows provenance; std **documentation**; **execution**, owned finite example; **derived**, compatibility obligations.

### 7. Radium's helper laws are available, but differ at the import boundary

Radium `val.v:128–140` accepts a location only from an exact pointer-fragment list; `val_to_loc_n` and adjacent lemmas prove exact helper round trips. `val_to_Z_go:342–347` accepts ordinary bytes and rejects other memory-byte constructors; `val_to_Z_val_of_loc_n_None:595–603` explicitly proves rejection of pointer encodings as integer values. MiniRust's integer decoder instead reads numeric data while discarding provenance, and its raw-pointer decoder can return an absent-provenance address.

These directly inspected helper rules preclude treating the representations as the same codec by renaming constructors. They do not decide every cast/load behavior in Radium, which may use other primitive rules. Reusing its already-mechanized arithmetic/fragment lemmas requires a representation relation and correct domain restriction.

Basis: **source**, exact Radium artifact members. The [spatial linking report](../minirust-rustbelt-spatial-linking-obligations-2026/REPORT.md) gives the corresponding adequacy direction.

### 8. Zerocopy-style trait contracts need separate representation and spatial premises

The source laws suggest a conditional interface, rather than automatically proving existing Rust traits:

| Intended contract | Representation premise | Additional operational premise |
| --- | --- | --- |
| FromBytes-style admission | Every admitted initialized byte pattern decodes to a valid value | Correct size/alignment, live readable range and source/API correspondence |
| TryFromBytes-style validation | Checker acceptance implies full representation/value validity | Checker reads permitted initialized bytes and handles metadata/state-dependent validity |
| IntoBytes-style exposure | Exposed bytes are initialized and represent the value | Padding/chunk coverage, permission and permitted byte observations |
| Typed/byte replacement | Observations respect the selected abstraction/refinement | Matching access granularity, alias effects, overlap and lifetime conditions |

The enum counterexample requires a coherence premise before using even the generic codec laws. The projection proof permits loss of padding; it cannot establish that a Rust API may expose that padding as initialized data. These remain separate from zerocopy's exact trait definitions and P131.

Basis: **derived**, conditional mapping from the inspected representation/access interfaces. No zerocopy trait implementation is verified here.

## Boundaries

- **Established here:** performed selected representation searches, general mask/scalar fragment proofs, concrete padding/fragment/provenance discriminators, and a source-derived enum-WF coherence counterexample with executed transcription.
- **Unestablished:** general mechanized MiniRust encode/decode laws, all enum/union/layout cases, a provenance/alias compatibility theorem, context equivalence of copy routes, or Rust/zerocopy API applicability.
- **Not examined:** overlapping-copy implementation, all MaybeUninit lowerings, real union padding policy, deallocation/address-reuse traces, exposed provenance in a running interpreter, Miri wildcard source/thesis correspondence, target families beyond the illustrative pointer codec, and the physical access interpretation in P131.
- **Known limit:** raw-pointer representation success does not imply a usable pointer, and BasicMemory success does not imply Tree Borrows success.
- **Tool evidence:** an initial EnumCoherence declaration failed ordinary elaboration because `decide` did not unfold a named proposition. Its rejected output is retained separately; the final corrected file checks and prints no axioms for the enum endpoints. No rejected declaration counts as proof evidence.

## Evidence

Acquired/rechecked 2026-10-14. `source-evidence.json` records full subject hashes/pins, file/blob identities and inspected spans. Primary links: [representation](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/representation.md), [WF checks](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/well-formed.md#L215), [cast state](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/intptrcast.md), [memory interface](https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/interface.md) and [Radium artifact](https://zenodo.org/records/21636474).

Portable support comprises both Python probes, their JSON/logs, `Representation.lean`, `EnumCoherence.lean` and final/initial Lean logs. All final commands exit zero. Representation lemmas print only `propext` or `Quot.sound`, except the scalar round trip which uses no axioms; enum endpoints use no axioms. These are Lean kernel/theory assumptions, not third-party solver certificates.

## Revalidation

Rerun both Python probes from `support/` and Lean on both files using the recorded toolchain. Inspect the enum counterexample independently against every WF/layout/value branch and the actual encode/decode equations. If a newer source adds coherence checks, classify that version separately.

For a real API proof, first establish its codec/layout invariants and access relation, then use the padding and equal-address fragmented-pointer discriminators. A complete interpreter run would validate its implementation on these cases; it still would not prove general codec or provenance adequacy.

*Authored by an AI agent acting on joshlf's behalf.*

