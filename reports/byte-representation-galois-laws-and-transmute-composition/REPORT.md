# Byte representations: Galois laws, transmute totality and composition, products, and provenance (Lean, toy model)

## Summary

A Lean 4 development (core Lean and `Std` only) of a toy model of value representations over abstract bytes (`uninit` or an initialized payload), with the three representation laws `DecodeMono` (more-defined bytes never decode differently), `DecodeEncode` (`decode (encode v) = some v`) and `EncodeLeast` (`decode x = some v → encode v ⊑ x`). All 22 results below are kernel-checked using only the axioms `propext`, `Classical.choice`, `Quot.sound`; every `tight` hypothesis has a proved counterexample, every result a proved non-vacuity witness, and each impossibility a proved positive control.

- **R1a** (characterization, `threeLaws_iff_lowerAdjoint`): For a representation in fixed-length abstract-byte vectors (pointwise definedness order, flat order on decoding results), `DecodeMono`, `DecodeEncode` and `EncodeLeast` hold together exactly when `encode v ⊑ x ↔ decode x = some v` for all `v` and `x`, i.e. when the encoder is a lower adjoint of the decoder.
- **R1b** (characterization, `encode_eq_iff_decodeEncode_encodeLeast`): If `r` satisfies `DecodeEncode` and `EncodeLeast`, then `r.encode` is the only encoder that satisfies these two laws against `r.decode` (so `encode v` is the `⊑`-least byte vector decoding to `v`); `DecodeMono` is not needed, and existence of a lawful encoder for a given decoder is not guaranteed.
- **R1c** (characterization, `decode_eq_iff_threeLaws`): If `r` satisfies all three laws, then `r.decode` is the only decoder that satisfies all three laws together with `r.encode`.
- **R1d** (theorem, `encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores`): Under `DecodeEncode` and `EncodeLeast`, a byte that the decoder ignores (overwriting it never changes the decoding) is `uninit` in every encoding.
- **R1d2** (theorem, `decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit`): Under all three laws, a byte that is `uninit` in every encoding is ignored by the decoder, so for lawful representations the ignored bytes are exactly the bytes every encoding leaves `uninit`.
- **R1e** (theorem, `eq_of_encode_le_encode_of_decodeMono_decodeEncode`): In any carrier with any definedness relation, `DecodeMono` and `DecodeEncode` imply that `encode v ⊑ encode w` only when `v = w`.
- **R2a** (theorem, `transmuteTotal_of_intoBytes_of_fromBytes`): For equal-size byte representations, if every encoding of `A` is fully initialized (`IntoBytes A`) and every fully initialized byte vector decodes as `B` (`FromBytes B`), then transmuting `A` to `B` never fails; no representation law is needed.
- **R2b** (theorem, `transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode`): If transmuting `B` to `A` is total, `A` is `IntoBytes` and satisfies `EncodeLeast`, and `B` satisfies `DecodeEncode`, then transmuting any `b` to `A` and back to `B` returns `b`.
- **R3** (theorem, `transmute_comp_of_total_of_encodeLeast_of_intoBytes`): If transmuting `A` to `B` is total and the middle type `B` satisfies `EncodeLeast` and `IntoBytes`, then transmuting `A → B → C` equals transmuting `A → C` for every input, with nothing assumed about `C`.
- **R4a** (theorem, `prodRep_decodeMono_of_fields`): For the explicit-offset product construction `prodRep` (padding written `uninit`, each field decoded from its own byte range), `DecodeMono` of every field gives `DecodeMono` of the product, for any layout.
- **R4b** (theorem, `prodRep_decodeEncode_of_fields_of_disjoint`): For `prodRep`, `DecodeEncode` of every field together with pairwise disjoint field ranges gives `DecodeEncode` of the product.
- **R4c** (theorem, `prodRep_encodeLeast_of_fields`): For `prodRep`, `EncodeLeast` of every field gives `EncodeLeast` of the product, for any layout.
- **R4d** (theorem, `prodRep_intoBytes_of_fields_of_covering`): For `prodRep`, `IntoBytes` of every field together with fields covering every byte (no padding) gives `IntoBytes` of the product.
- **R4e** (theorem, `prodRep_fromBytes_of_fields`): For `prodRep`, `FromBytes` of every field gives `FromBytes` of the product, for any layout.
- **R5a** (characterization, `transmuteTotal_iff_image_subset_valid`): Transmuting `A` to `B` is total exactly when every encoding of an `A` value decodes as `B` (a definitional reference point for R5b and R5c).
- **R5b** (characterization, `transmuteTotal_iff_valid_subset_of_laws`): In any carrier with any definedness relation, if `A` satisfies `DecodeEncode` and `EncodeLeast` and `B` satisfies `DecodeMono`, then transmuting `A` to `B` is total exactly when every byte vector valid for `A` (including partially uninitialized ones) is valid for `B`.
- **R5c** (characterization, `transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast`): For equal-size byte representations, if `A` is `IntoBytes` and satisfies `DecodeEncode` and `EncodeLeast`, then transmuting `A` to `B` is total exactly when every fully initialized byte pattern valid for `A` is valid for `B`; without `IntoBytes A` this initialized-only criterion is unsound.
- **R6a** (theorem, `int_ptr_int_roundtrip_of_decodeEncode`): With provenance-carrying bytes and the canonical encoders, at every size `n + 1 ≥ 1`, if the integer decoder and the pointer decoder both satisfy `DecodeEncode`, an integer `x` transmutes to the pointer `(x, none)` and back to `x`.
- **R6b** (theorem, `ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode`): At every size `n + 1 ≥ 1`, with the provenance-stripping integer decoder and any pointer decoder satisfying `DecodeEncode`, the pointer `(a, some p)` transmutes to the integer `a` and back to the pointer `(a, none)`, which differs from `(a, some p)`.
- **R6c** (impossibility, `no_int_decoder_encodeLeast_fromBytes_of_provenance`): If bytes carry provenance ordered as plain data, some byte value and some provenance exist, and `n ≥ 1`, then no decoder for the canonical provenance-free integer encoder is both `EncodeLeast` and `FromBytes`.
- **R6d** (impossibility, `no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc`): If adding provenance makes a byte more defined and some byte value and some provenance exist, then no decoder for the canonical encoder of pointers with optional provenance (size `n + 1 ≥ 1`) satisfies both `DecodeMono` with the flat value order and `DecodeEncode`.
- **R6e** (counterexample, `transmute_comp_fails_of_provInc`): If adding provenance makes a byte more defined, R3's composition conclusion fails in a concrete instance in which all three representations satisfy all three laws, the first transmute is total, and the middle type's encodings are fully initialized.

The non-claims of every result are listed first under **Boundaries**; they rule out tempting stronger readings (value preservation, reference casts, unions, other byte or value orders, real compilers, zerocopy's exact trait semantics) and must be read together with the claims.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity.** Everything is a toy model in namespace `Toy.Repr`. No production definitions are mirrored and no code is shared with the cited systems. The definitions are meant to capture:

- the representation relation of MiniRust (`encode`/`decode` between values and lists of abstract bytes, its definedness order on abstract bytes, and its generic properties), restricted to a functional encoder and a decoder that depends only on the bytes;
- the by-value content of zerocopy's `IntoBytes`, `FromBytes` and `TryFromBytes` contracts (`Rep.IntoBytes`, `Rep.FromBytes`, `Rep.tryFrom`/`Rep.InitValid`), with the divergences stated in Findings and Boundaries (provenance-carrying bytes count as initialized; zerocopy implements neither trait for raw pointers; `TryFromBytes` is conservative where `tryFrom` is exact);
- equal-size by-value transmutes `transmute ra rb := rb.decode ∘ ra.encode`, structs with explicit field offsets (`prodRep`), and pointer provenance carried by bytes under two orders (provenance as data, `PBytes`; adding provenance increases definedness, `PBytesInc`, as in MiniRust).

**Known gaps.** No alignment, size rounding or endianness; no enums, discriminants or niches beyond single-byte examples; no unions (overlapping `prodRep` fields are not unions); no references or in-place casts, only by-value reinterpretation at a common byte length; no `UnsafeCell`; no as-casts or exposed provenance; no machine-state-dependent validity (MiniRust's `check_value`); provenance tags carry no byte position; values are ordered flatly except for the pointer order `PtrValLe` used through `Rep.DecodeMonoBy`. Results stated for an arbitrary `[Definedness α]` (R1e, R5a, R5b) use no property of the relation; the others are stated for the concrete orders, each proved to be a partial order.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std` only, no Mathlib, no Lake dependencies. Lake project in `lean/` (library `ToyRepr`, modules `Basic`, `Examples`, `Galois`, `Transmute`, `Product`, `Provenance`).

**Subjects.** The Lean toolchain release is the checker of every `execution (Lean kernel check)` claim. The papers, specifications, documentation and source revisions listed under Evidence are prior art and the systems the toy definitions are meant to capture; claims about them are separate `derived (modeling bridge)` claims. Open (unmerged) pull requests are mentioned as context only.

## Findings

### Definitions (unfolded)

```lean
class Definedness (α : Type) where le : α → α → Prop          -- notation x ⊑ y

inductive AByte (D : Type) | uninit | init (d : D)
-- D = payload of an initialized byte: UInt8 (no provenance) or β × Option P (provenance)

AByte.le : uninit ⊑ x;  init a ⊑ init b ↔ a = b;  init a ⋢ uninit       -- flat above uninit
Bytes D n := Vector (AByte D) n;   x ⊑ y ↔ ∀ i < n, x[i] ⊑ y[i]
OptLe on Option V : none ⊑ o;  some v ⊑ some w ↔ v = w;  some v ⋢ none  -- flat

structure Rep (α V : Type) where
  encode : V → α
  decode : α → Option V

Rep.DecodeMono   r := ∀ x y, x ⊑ y → r.decode x ⊑ r.decode y
                    -- i.e. r.decode x = some v → x ⊑ y → r.decode y = some v
Rep.DecodeMonoBy r leV := ∀ x y, x ⊑ y → leV (r.decode x) (r.decode y)   -- for a non-flat value order leV
Rep.DecodeEncode r := ∀ v, r.decode (r.encode v) = some v
Rep.EncodeLeast  r := ∀ x v, r.decode x = some v → r.encode v ⊑ x
Rep.LowerAdjoint r := ∀ v x, r.encode v ⊑ x ↔ r.decode x = some v
Rep.liftEncode r   : Option V → Bytes D n;  none ↦ all-uninit, some v ↦ r.encode v
  -- LowerAdjoint r ↔ (liftEncode r, decode) is a Galois connection (Rep.lowerAdjoint_iff_galois_liftEncode)
Rep.Valid r x      := ∃ v, r.decode x = some v
Rep.Image r x      := ∃ v, r.encode v = x
Rep.DecodeIgnores r i := ∀ x b, r.decode (x.set i b) = r.decode x       -- byte i is padding
Bytes.IsInit x     := ∀ i < n, x[i].isInit = true   -- i.e. x[i] ≠ uninit
Bytes.ofData ds    := [init ds[i]]ᵢ                  -- Vector D n → Bytes D n
Bytes.toData? x    := if x.IsInit then some [dᵢ]ᵢ (where x[i] = init dᵢ) else none
Rep.IntoBytes r    := ∀ v, (r.encode v).IsInit
Rep.FromBytes r    := ∀ x, x.IsInit → ∃ v, r.decode x = some v
Rep.tryFrom r ds   := r.decode (ds.map init)                             -- partial cast from data
Rep.InitValid r ds := ∃ v, r.tryFrom ds = some v
transmute ra rb a  := rb.decode (ra.encode a)                            -- same carrier = same size
TransmuteTotal ra rb := ∀ a, ∃ b, transmute ra rb a = some b
```

Products with explicit field offsets (`Product.lean`; a `Layout` fixes offsets in any order and
without alignment, e.g. the layout chosen by `repr(C)`, `repr(packed)`, or by the compiler for
`repr(Rust)`; overlapping ranges are allowed by the definition but do not model unions):

```lean
structure Layout (n k : Nat) where size : Fin k → Nat; off : Fin k → Nat; fits : ∀ j, off j + size j ≤ n
L.InField j i := off j ≤ i ∧ i < off j + size j
L.owner i     := first j (in index order) with L.InField j i, if any
L.Disjoint    := ∀ j ≠ j', ∀ i, ¬ (L.InField j i ∧ L.InField j' i)
L.Covering    := ∀ i < n, ∃ j, L.InField j i
prodEncode L r v : byte i = ((r j).encode (v j))[i - off j] if L.owner i = some j, else uninit
prodDecode L r x := some (fun j => vⱼ) if every field j decodes its slice x[off j, off j + size j) to vⱼ, else none
prodRep L r := ⟨prodEncode L r, prodDecode L r⟩ : Rep (Bytes D n) ((j : Fin k) → V j)
```

Provenance (`Provenance.lean`), with `PBytes β P n := Bytes (β × Option P) n` (flat order: provenance is data):

```lean
intEncode x       := [init (x[i], none)]ᵢ              -- integers: Vector β n
ptrEncode (a, q)  := [init (a[i], q)]ᵢ                 -- pointers: Vector β n × Option P
intDecodeStrip x  := if x fully initialized then some [x[i].1.1]ᵢ else none     -- forgets provenance
intDecodeStrict x := as intDecodeStrip, but none if some byte carries provenance
ptrDecodeStrict x := if fully initialized and all provenances equal q then some (addr, q) else none
ptrDecodeReqProv x := as ptrDecodeStrict, but additionally requires q = some p
intStripRep       := ⟨intEncode, intDecodeStrip⟩  : Rep (PBytes β P n) (Vector β n)
intStrictRep      := ⟨intEncode, intDecodeStrict⟩ : Rep (PBytes β P n) (Vector β n)
provIntRep        := ⟨Bytes.ofData, Bytes.toData?⟩ : Rep (PBytes β P n) (Vector (β × Option P) n)
                     -- integers whose values carry provenance (provenance via integers)
AByte.leProvInc   : uninit ⊑ x; init (b, none) ⊑ init (b', q) ↔ b = b'; init (b, some p) ⊑ init (b', q) ↔ b = b' ∧ q = some p
PBytesInc β P n   := ⟨bytes : PBytes β P n⟩ with the pointwise leProvInc order  -- "adding provenance is more defined"
                     -- a partial order: PBytesInc.le_refl / le_trans / le_antisymm
ptrEncodeInc p    := ⟨ptrEncode p⟩ : PBytesInc β P n;   intEncodeInc x := ⟨intEncode x⟩ : PBytesInc β P n
intStripRepInc    := ⟨intEncodeInc, intDecodeStrip ∘ bytes⟩ : Rep (PBytesInc β P n) (Vector β n)
reqProvPtrRepInc  : Rep (PBytesInc β P (n+1)) (Vector β (n+1) × P)   -- pointers that always carry provenance
  encode (a, p) := ptrEncode (a, some p);  decode x := some (a, p) iff ptrDecodeStrict x = some (a, some p)
PtrValLe on Option (Vector β m × Option P) : none ⊑ o; some (a, none) ⊑ some (b, _) ↔ a = b;
  some (a, some p) ⊑ some (b, q) ↔ a = b ∧ q = some p; some _ ⋢ none          -- MiniRust-style value order
ptrDecodeDegrade x := none if some byte is uninit; otherwise some (addr, q), where q is the common
                     provenance if all bytes carry the same one and q = none otherwise
                     (missing or mixed provenance degrades to none instead of failing)
ptrDegradeRepInc  := ⟨ptrEncodeInc, ptrDecodeDegrade ∘ bytes⟩ : Rep (PBytesInc β P (n+1)) (Vector β (n+1) × Option P)
```

Concrete representations (byte payload `Byte := UInt8`): `u8Rep` (one byte, every value valid), `boolRep` (one byte, only 0 and 1 valid), `boolNZRep` (every nonzero byte decodes to `true`, `true` encoded as 1), `padUnitRep` (`Unit` in one ignored byte, encoded `uninit`), `exactUnitRep` (as `padUnitRep`, but only `[uninit]` decodes), `boolUninitRep` (`false ↦ [uninit]`, `true ↦ [init 0]`), `u8PadRep` (a `u8` followed by one padding byte encoded `uninit`), `u8PadInitRep` (padding encoded `init 0`), `pairRep` (two initialized bytes), `unitZeroRep` (`Unit` in one byte encoded `init 0`; only `[init 0]` decodes), `noneRep enc` (decoder always fails). Every core definition has proved positive and negative examples (`ex_*_pos` / `ex_*_neg` in `Examples.lean`, `Galois.lean`, `Product.lean`, `Provenance.lean`).

In the unfolded statements below, `Mono r`, `DE r`, `EL r` abbreviate `r.DecodeMono`, `r.DecodeEncode`, `r.EncodeLeast`, and `x[i] ≠ uninit` abbreviates `x[i].isInit = true`.

### R1a: R1a-three-laws-iff-lower-adjoint

- **Lean:** `Toy.Repr.threeLaws_iff_lowerAdjoint` (`lean/ToyRepr/Galois.lean`); kind `characterization`; tier `T0`; depth `shallow`.
- **Tier:** `T0`. Instance of the textbook characterization of a Galois connection by monotonicity and the two unit inequalities (Ore 1944; mechanized for preorders in Mathlib's GaloisConnection); MiniRust states informally that its generic properties form an adjoint relationship.
- **Plain claim:** For a representation in fixed-length abstract-byte vectors (pointwise definedness order, flat order on decoding results), DecodeMono, DecodeEncode and EncodeLeast hold together exactly when encode v ⊑ bytes ⟺ decode bytes = some v for all v and bytes. Equivalently (Rep.lowerAdjoint_iff_galois_liftEncode), extending encode to Option V by none ↦ all-uninit gives a Galois connection with decode.

```lean
theorem threeLaws_iff_lowerAdjoint {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    (r.DecodeMono ∧ r.DecodeEncode ∧ r.EncodeLeast) ↔ r.LowerAdjoint
```

Unfolded:

```lean
(∀ x y, x ⊑ y → r.decode x ⊑ r.decode y) ∧ (∀ v, r.decode (r.encode v) = some v) ∧
(∀ x v, r.decode x = some v → r.encode v ⊑ x)
  ↔ ∀ v x, r.encode v ⊑ x ↔ r.decode x = some v
-- where x ⊑ y on Bytes D n is ∀ i < n, x[i] ⊑ y[i] (uninit ⊑ _, init a ⊑ init b ↔ a = b),
-- and on Option V: none ⊑ o, some v ⊑ some w ↔ v = w, some v ⋢ none
```

Hypothesis ledger: no hypotheses beyond the objects quantified over.

- **Depth:** `shallow`.
- **Non-vacuity witness:** u8Rep (one initialized byte, every byte value valid) satisfies both sides; boolNZRep fails both (`threeLaws_iff_lowerAdjoint_nonvacuous`).
- **Prior art:**
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
  - P. Cousot and R. Cousot, 'Systematic design of program analysis frameworks', POPL 1979, pp. 269-282, doi:10.1145/567752.567778 (Galois connections between assertion spaces and representations)
  - O. Ore, 'Galois connexions', Transactions of the American Mathematical Society 55, pp. 493-513, 1944, doi:10.1090/S0002-9947-1944-0010555-7
  - Mathlib, Mathlib/Order/GaloisConnection/Defs.lean and Basic.lean and Mathlib/Order/Bounds/Basic.lean, repository leanprover-community/mathlib4, commit f5d65c00d8545e4d082536ede4239761af2eea2a: GaloisConnection (Defs.lean L40), uniqueness of adjoints u_unique and its order dual l_unique (Defs.lean L109-112, generated by to_dual), the lower adjoint as a least element isLeast_l (Basic.lean L77-79), and IsLeast.unique (Bounds/Basic.lean L879); mechanized order theory over preorders, not over byte representations
  - J. Hostert, '[WIP] Layouts, machine types, low-level representations.', AeneasVerif/aeneas pull request 1447 (open draft), head commit 2a1dd75567517e078f90b1df746af7373fe24cbc (fork JoJoDeveloping/aeneas, branch layouts; Apache-2.0): backends/lean/Aeneas/Data/Layout/EncodeDecode.lean L121-145 defines DecodeValid, DecodeMono, DecodeEncode and EncodeDecodeLeDefined over provenance-free abstract bytes; GaloisConnection.lean L101-256 proves them for every Layout.Valid layout of its machine types (integers, tuples with explicit field offsets, enums with tags and niches). It does not state a lower-adjoint equivalence or uniqueness of the encoder or decoder; https://github.com/AeneasVerif/aeneas/pull/1447
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `threeLaws_iff_lowerAdjoint` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge), for R1a-R1e: MiniRust's representation relation (`spec/lang/representation.md` at commit `063d784186d3252bee242217f218223205c0b568`, L754-763) lists four generic properties of `encode`/`decode` and calls them an adjoint relationship (L765-766). For a MiniRust type whose values are ordered flatly and whose bytes carry no provenance, MiniRust's abstract-byte order restricted to provenance-free bytes is `AByte.le` (`Uninit` below everything, an initialized byte comparable only with itself), so MiniRust's properties 2-4 are `DecodeMono`, `DecodeEncode` and `EncodeLeast` for that type and property 1 (encode monotone) holds trivially; R1a-R1e then apply to it. This transfer is an argument, not a kernel check: `Rep.decode` omits MiniRust's separate machine-state-dependent `check_value` step, and for values MiniRust orders non-flatly (pointers, and aggregates containing them) nothing is claimed. For R1d/R1d2, `DecodeIgnores` is the functional analogue of the Unsafe Code Guidelines glossary's relational definition of a padding byte ("entirely ignored by Vrel_T").

### R1b: R1b-encode-determined-by-decode

- **Lean:** `Toy.Repr.encode_eq_iff_decodeEncode_encodeLeast` (`lean/ToyRepr/Galois.lean`); kind `characterization`; tier `T0`; depth `shallow`.
- **Tier:** `T0`. Pointwise uniqueness of the least element of decode^-1(some v) in a partial order (as IsLeast.unique / GaloisConnection.isLeast_l in Mathlib), restated for byte representations; MiniRust remarks informally that its generic properties make uninitialized padding 'the only possible choice for encode'. Recorded because it isolates the two laws needed (DecodeMono is not).
- **Plain claim:** If r satisfies DecodeEncode and EncodeLeast, an encoder e satisfies both laws against r's decoder if and only if e = r.encode; i.e. encode v is the unique ⊑-least byte vector that decodes to v, and DecodeMono is not needed for this.

```lean
theorem encode_eq_iff_decodeEncode_encodeLeast {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (e : V → Bytes D n) :
    ((⟨e, r.decode⟩ : Rep (Bytes D n) V).DecodeEncode ∧
      (⟨e, r.decode⟩ : Rep (Bytes D n) V).EncodeLeast) ↔ e = r.encode
```

Unfolded:

```lean
(∀ v, r.decode (r.encode v) = some v) → (∀ x v, r.decode x = some v → r.encode v ⊑ x) →
∀ e, ((∀ v, r.decode (e v) = some v) ∧ (∀ x v, r.decode x = some v → e v ⊑ x)) ↔ e = r.encode
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDE` | r.encode v decodes to v, so r.encode v is a candidate least element. | `tight` | `encode_eq_iff_decodeEncode_encodeLeast_tight_hDE` |
| `hEL` | r.encode v lies below every byte vector decoding to v, so it is the least one. | `tight` | `encode_eq_iff_decodeEncode_encodeLeast_tight_hEL` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** u8PadRep (a u8 followed by one padding byte that is left uninit) (`encode_eq_iff_decodeEncode_encodeLeast_nonvacuous`).
- **Prior art:**
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
  - J. Hostert, review comment on AeneasVerif/aeneas pull request 1497 (2026-11-06), https://github.com/AeneasVerif/aeneas/pull/1497#discussion_r4494829173: 'Can we prove that forall a b, decode a = .some b ↔ encode b a? ... So why have both? We can define encode using the identity above.' The question concerns that pull request's relational encoder, which has no least-encoding law; there the identity already fails for u8 (u8 decode accepts a pointer-lane byte that u8 encode never produces; Repr.lean L42-48, L209-214 at head d17ca83fc07d712d1785f650840cb2073c259e69). R1b answers the analogous question for a functional encoder: with EncodeLeast, encode v is determined as the least element of decode^-1(some v), not as the whole preimage.
  - Mathlib, Mathlib/Order/GaloisConnection/Defs.lean and Basic.lean and Mathlib/Order/Bounds/Basic.lean, repository leanprover-community/mathlib4, commit f5d65c00d8545e4d082536ede4239761af2eea2a: GaloisConnection (Defs.lean L40), uniqueness of adjoints u_unique and its order dual l_unique (Defs.lean L109-112, generated by to_dual), the lower adjoint as a least element isLeast_l (Basic.lean L77-79), and IsLeast.unique (Bounds/Basic.lean L879); mechanized order theory over preorders, not over byte representations
  - J. Hostert, '[WIP] Layouts, machine types, low-level representations.', AeneasVerif/aeneas pull request 1447 (open draft), head commit 2a1dd75567517e078f90b1df746af7373fe24cbc (fork JoJoDeveloping/aeneas, branch layouts; Apache-2.0): backends/lean/Aeneas/Data/Layout/EncodeDecode.lean L121-145 defines DecodeValid, DecodeMono, DecodeEncode and EncodeDecodeLeDefined over provenance-free abstract bytes; GaloisConnection.lean L101-256 proves them for every Layout.Valid layout of its machine types (integers, tuples with explicit field offsets, enums with tags and niches). It does not state a lower-adjoint equivalence or uniqueness of the encoder or decoder; https://github.com/AeneasVerif/aeneas/pull/1447
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `encode_eq_iff_decodeEncode_encodeLeast` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R1a-R1e under R1a above.

### R1c: R1c-decode-determined-by-encode

- **Lean:** `Toy.Repr.decode_eq_iff_threeLaws` (`lean/ToyRepr/Galois.lean`); kind `characterization`; tier `T0`; depth `shallow`.
- **Tier:** `T0`. Instance of the uniqueness of adjoints (Mathlib GaloisConnection.u_unique / l_unique), via R1a.
- **Plain claim:** If r satisfies DecodeMono, DecodeEncode and EncodeLeast, a decoder d makes (r.encode, d) satisfy all three laws if and only if d = r.decode; with all three laws the encoder determines the decoder.

```lean
theorem decode_eq_iff_threeLaws {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast)
    (d : Bytes D n → Option V) :
    ((⟨r.encode, d⟩ : Rep (Bytes D n) V).DecodeMono ∧
      (⟨r.encode, d⟩ : Rep (Bytes D n) V).DecodeEncode ∧
      (⟨r.encode, d⟩ : Rep (Bytes D n) V).EncodeLeast) ↔ d = r.decode
```

Unfolded:

```lean
Mono r → DE r → EL r → ∀ d, (Mono ⟨r.encode, d⟩ ∧ DE ⟨r.encode, d⟩ ∧ EL ⟨r.encode, d⟩) ↔ d = r.decode
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hM` | Forces every byte vector above encode v to decode to v. | `tight` | `decode_eq_iff_threeLaws_tight_hM` |
| `hDE` | Forces the encodings themselves to decode. | `tight` | `decode_eq_iff_threeLaws_tight_hDE` |
| `hEL` | Forbids decoding to v anything not above encode v. | `tight` | `decode_eq_iff_threeLaws_tight_hEL` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** boolRep (bool-like byte with a niche) (`decode_eq_iff_threeLaws_nonvacuous`).
- **Prior art:**
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
  - P. Cousot and R. Cousot, 'Systematic design of program analysis frameworks', POPL 1979, pp. 269-282, doi:10.1145/567752.567778 (Galois connections between assertion spaces and representations)
  - Mathlib, Mathlib/Order/GaloisConnection/Defs.lean and Basic.lean and Mathlib/Order/Bounds/Basic.lean, repository leanprover-community/mathlib4, commit f5d65c00d8545e4d082536ede4239761af2eea2a: GaloisConnection (Defs.lean L40), uniqueness of adjoints u_unique and its order dual l_unique (Defs.lean L109-112, generated by to_dual), the lower adjoint as a least element isLeast_l (Basic.lean L77-79), and IsLeast.unique (Bounds/Basic.lean L879); mechanized order theory over preorders, not over byte representations
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `decode_eq_iff_threeLaws` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R1a-R1e under R1a above.

### R1d: R1d-ignored-byte-is-uninit-in-encoding

- **Lean:** `Toy.Repr.encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores` (`lean/ToyRepr/Galois.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Makes precise MiniRust's remark that the generic properties force padding to be Uninit and the UCG glossary's definition of padding as bytes ignored by the value relation.
- **Plain claim:** Under DecodeEncode and EncodeLeast, if overwriting byte i never changes the decoding (decode ignores byte i), then byte i of every encoding is uninit.

```lean
theorem encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (i : Nat) (hi : i < n)
    (hIgn : r.DecodeIgnores i hi) (v : V) : (r.encode v)[i] = .uninit
```

Unfolded:

```lean
DE r → EL r → (∀ x b, r.decode (x.set i b) = r.decode x) → ∀ v, (r.encode v)[i] = uninit
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDE` | Lets encode v itself (with byte i reset) be a vector decoding to v. | `tight` | `encode_getElem_eq_uninit_of_decodeIgnores_tight_hDE` |
| `hEL` | Forces encode v below that reset vector. | `tight` | `encode_getElem_eq_uninit_of_decodeIgnores_tight_hEL` |
| `hi` | Byte index in range (needed to state DecodeIgnores and to index the encoding). | `harmless` | — |
| `hIgn` | Byte i is padding for this decoder (overwriting it with any abstract byte leaves the result unchanged). | `tight` | `encode_getElem_eq_uninit_of_decodeIgnores_tight_hIgn` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** u8PadRep at byte 1 (`encode_getElem_eq_uninit_of_decodeIgnores_nonvacuous`).
- **Prior art:**
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R1a-R1e under R1a above.

### R1d2: R1d2-uninit-in-every-encoding-is-ignored

- **Lean:** `Toy.Repr.decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit` (`lean/ToyRepr/Galois.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Converse of R1d; together they identify padding (bytes the decoder ignores) with bytes left uninit by every encoding, as the UCG glossary's informal definition of padding suggests.
- **Plain claim:** Under DecodeMono, DecodeEncode and EncodeLeast, if byte i is uninit in every encoding, then decode ignores byte i; so for a lawful representation the ignored bytes are exactly the bytes that every encoding leaves uninit.

```lean
theorem decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (hDE : r.DecodeEncode) (hEL : r.EncodeLeast) (i : Nat) (hi : i < n)
    (hU : ∀ v : V, (r.encode v)[i] = .uninit) : r.DecodeIgnores i hi
```

Unfolded:

```lean
Mono r → DE r → EL r → (∀ v, (r.encode v)[i] = uninit) → ∀ x b, r.decode (x.set i b) = r.decode x
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hM` | Bytes above an encoding keep decoding to its value whatever sits at byte i. | `tight` | `decodeIgnores_of_encode_uninit_tight_hM` |
| `hDE` | Encodings decode, so the decoder's success set is anchored at the encodings. | `tight` | `decodeIgnores_of_encode_uninit_tight_hDE` |
| `hEL` | Nothing outside the up-sets of encodings decodes. | `tight` | `decodeIgnores_of_encode_uninit_tight_hEL` |
| `hi` | Byte index in range (needed to state DecodeIgnores and to index the encodings). | `harmless` | — |
| `hU` | Byte i is uninit in every encoding. | `tight` | `decodeIgnores_of_encode_uninit_tight_hU` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** u8PadRep at byte 1 (`decodeIgnores_of_encode_uninit_nonvacuous`).
- **Prior art:**
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R1a-R1e under R1a above.

### R1e: R1e-comparable-encodings-are-equal

- **Lean:** `Toy.Repr.eq_of_encode_le_encode_of_decodeMono_decodeEncode` (`lean/ToyRepr/Galois.lean`); kind `theorem`; tier `T0`; depth `shallow`.
- **Tier:** `T0`. Elementary order-theoretic consequence; recorded because the provenance impossibility (R6d) is an instance.
- **Plain claim:** In any carrier with any definedness relation, DecodeMono (flat value order) and DecodeEncode imply that encode v ⊑ encode w only if v = w: distinct values have incomparable encodings.

```lean
theorem eq_of_encode_le_encode_of_decodeMono_decodeEncode {α V : Type} [Definedness α]
    (r : Rep α V) (hM : r.DecodeMono) (hDE : r.DecodeEncode) :
    ∀ v w : V, r.encode v ⊑ r.encode w → v = w
```

Unfolded:

```lean
[any carrier α, any relation ⊑ on α] Mono r → DE r → ∀ v w, r.encode v ⊑ r.encode w → v = w
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hM` | Transfers the successful decode of encode v up to encode w. | `tight` | `eq_of_encode_le_encode_tight_hM` |
| `hDE` | Makes both encodings decode to their own values. | `tight` | `eq_of_encode_le_encode_tight_hDE` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** u8Rep (`eq_of_encode_le_encode_nonvacuous`).
- **Prior art:**
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
- **Design question:** Which laws should a verifier's trusted relation between typed values and their bytes satisfy, and how much of that relation do the laws pin down (is the encoder redundant given the decoder; must padding be uninitialized)?
- **Basis:** execution (Lean kernel check): `eq_of_encode_le_encode_of_decodeMono_decodeEncode` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R1a-R1e under R1a above.

### R2a: R2a-transmute-total-of-intoBytes-fromBytes

- **Lean:** `Toy.Repr.transmuteTotal_of_intoBytes_of_fromBytes` (`lean/ToyRepr/Transmute.lean`); kind `theorem`; tier `T1`; depth `definitional`.
- **Tier:** `T1`. The IntoBytes-source / FromBytes-destination rule for byte reinterpretation is documented practice (zerocopy); stated here over abstract bytes with uninit.
- **Plain claim:** For representations of equal size, if no encoding of A contains an uninit byte (IntoBytes A) and every fully initialized byte vector decodes as B (FromBytes B), then transmute A→B (decode_B after encode_A) never fails; no representation law is needed.

```lean
theorem transmuteTotal_of_intoBytes_of_fromBytes {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hA : ra.IntoBytes) (hB : rb.FromBytes) : TransmuteTotal ra rb
```

Unfolded:

```lean
(∀ a i, (ra.encode a)[i] ≠ uninit) → (∀ x, (∀ i, x[i] ≠ uninit) → ∃ b, rb.decode x = some b) →
∀ a, ∃ b, rb.decode (ra.encode a) = some b
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hA` | Every encoding of A is fully initialized. | `tight` | `transmuteTotal_of_intoBytes_of_fromBytes_tight_hA` |
| `hB` | Every fully initialized vector decodes as B. | `tight` | `transmuteTotal_of_intoBytes_of_fromBytes_tight_hB` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `definitional`.
- **Non-vacuity witness:** Two-byte integer to the padded u8 struct (`transmuteTotal_of_intoBytes_of_fromBytes_nonvacuous`).
- **Prior art:**
  - zerocopy 0.8.63 documentation (docs.rs): FromBytes ('sound to produce a T whose bytes are initialized to any sequence of valid u8s'), IntoBytes ('sound to treat any t: T as an immutable [u8]'), TryFromBytes (runtime validity check; 'not symmetrical with IntoBytes'); https://docs.rs/zerocopy/0.8.63/zerocopy/trait.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.IntoBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.TryFromBytes.html
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: the compiler guarantees that Src is soundly union-transmutable into Dst under the given assumptions (L14-17); union-transmutes 'permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44); Assume::SAFETY (L319); https://github.com/rust-lang/rust/blob/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/library/core/src/mem/transmutability.rs
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
- **Design question:** Which conditions make a by-value byte reinterpretation (transmute, from_bytes-style cast) total and value-preserving, and when do chains of reinterpretations compose?
- **Basis:** execution (Lean kernel check): `transmuteTotal_of_intoBytes_of_fromBytes` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge), for R2a, R2b and R3: zerocopy 0.8.63 documents `IntoBytes` as "sound to treat any t: T as an immutable [u8]" and `FromBytes` as "sound to produce a T whose bytes are initialized to any sequence of valid u8s". Over provenance-free bytes (`D = UInt8`), `Rep.IntoBytes` (no encoding contains `uninit`) and `Rep.FromBytes` (every fully initialized vector decodes) state the by-value content of these contracts for one representation, so R2a is the toy form of the IntoBytes-source / FromBytes-destination rule for equal-size by-value reinterpretation. Known divergences: (i) zerocopy defines both traits relative to plain `u8` bytes, whereas when the payload `D` carries provenance (`PBytes`) the model counts bytes with provenance as initialized; zerocopy implements neither `IntoBytes` nor `FromBytes` for raw pointers (`*const T`, `*mut T`), while a pointer representation can satisfy `Rep.IntoBytes` here; (ii) zerocopy's `TryFromBytes` runtime check may reject bit-valid values and is documented as not symmetrical with `IntoBytes`, whereas `Rep.tryFrom` and `Rep.InitValid` use the exact decoder; (iii) zerocopy's traits also govern reference casts, alignment and dynamically sized types, none of which is modeled. R2b and R3 have no direct zerocopy counterpart; they are statements about representations satisfying the laws.

### R2b: R2b-roundtrip-B-A-B

- **Lean:** `Toy.Repr.transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode` (`lean/ToyRepr/Transmute.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Folklore that reinterpretation between plain-old-data types is lossless; made precise with a minimal hypothesis set over abstract bytes.
- **Plain claim:** For equal-size representations rb of B and ra of A: if transmute B→A is total, A is IntoBytes and satisfies EncodeLeast, and B satisfies DecodeEncode, then for every b, transmuting b to A and the result back to B returns b (B→A→B is lossless). By R2a, totality of B→A holds in particular when B is IntoBytes and A is FromBytes; FromBytes B and the other laws are not needed.

```lean
theorem transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode {D A B : Type}
    {n : Nat} (rb : Rep (Bytes D n) B) (ra : Rep (Bytes D n) A)
    (htot : TransmuteTotal rb ra) (hIB_A : ra.IntoBytes) (hEL_A : ra.EncodeLeast)
    (hDE_B : rb.DecodeEncode) :
    ∀ b : B, (transmute rb ra b).bind (transmute ra rb) = some b
```

Unfolded:

```lean
TransmuteTotal rb ra → IntoBytes ra → EL ra → DE rb →
∀ b, (ra.decode (rb.encode b)).bind (fun a => rb.decode (ra.encode a)) = some b
-- TransmuteTotal rb ra := ∀ b, ∃ a, ra.decode (rb.encode b) = some a  (holds if IntoBytes rb ∧ FromBytes ra, R2a)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `htot` | B→A succeeds on every b (implied by IntoBytes B and FromBytes A, R2a). | `tight` | `transmute_roundtrip_tight_htot` |
| `hIB_A` | With EncodeLeast, forces encode_A a = encode_B b exactly. | `tight` | `transmute_roundtrip_tight_hIB_A` |
| `hEL_A` | encode_A a is below encode_B b. | `tight` | `transmute_roundtrip_tight_hEL_A` |
| `hDE_B` | Decoding encode_B b recovers b. | `tight` | `transmute_roundtrip_tight_hDE_B` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** B = bool-like type with a niche (not FromBytes), A = u8 (bool → u8 → bool) (`transmute_roundtrip_nonvacuous`).
- **Prior art:**
  - zerocopy 0.8.63 documentation (docs.rs): FromBytes ('sound to produce a T whose bytes are initialized to any sequence of valid u8s'), IntoBytes ('sound to treat any t: T as an immutable [u8]'), TryFromBytes (runtime validity check; 'not symmetrical with IntoBytes'); https://docs.rs/zerocopy/0.8.63/zerocopy/trait.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.IntoBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.TryFromBytes.html
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
- **Design question:** Which conditions make a by-value byte reinterpretation (transmute, from_bytes-style cast) total and value-preserving, and when do chains of reinterpretations compose?
- **Basis:** execution (Lean kernel check): `transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R2a, R2b and R3 under R2a above.

### R3: R3-transmute-composition

- **Lean:** `Toy.Repr.transmute_comp_of_total_of_encodeLeast_of_intoBytes` (`lean/ToyRepr/Transmute.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Composition of reinterpretations is folklore; the precise middle-type conditions over abstract bytes are stated here.
- **Plain claim:** For equal-size representations, if transmute A→B is total and the middle type B satisfies EncodeLeast and IntoBytes, then transmuting A→B and then B→C equals transmuting A→C, for every a; nothing is assumed about C.

```lean
theorem transmute_comp_of_total_of_encodeLeast_of_intoBytes {D A B C : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B) (rc : Rep (Bytes D n) C)
    (htot : TransmuteTotal ra rb) (hEL : rb.EncodeLeast) (hIB : rb.IntoBytes) :
    ∀ a : A, (transmute ra rb a).bind (transmute rb rc) = transmute ra rc a
```

Unfolded:

```lean
(∀ a, ∃ b, rb.decode (ra.encode a) = some b) → EL rb → IntoBytes rb →
∀ a, (rb.decode (ra.encode a)).bind (fun b => rc.decode (rb.encode b)) = rc.decode (ra.encode a)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `htot` | Rules out A→B failing where A→C succeeds. | `tight` | `transmute_comp_tight_htot` |
| `hEL` | Re-encoding the intermediate value is below the original bytes. | `tight` | `transmute_comp_tight_hEL` |
| `hIB` | Together with hEL, the re-encoding equals the original bytes (B has no padding C could read). | `tight` | `transmute_comp_tight_hIB` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** A = bool-like type with a niche, B = u8 (any C) (`transmute_comp_nonvacuous`).
- **Prior art:**
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
  - zerocopy 0.8.63 documentation (docs.rs): FromBytes ('sound to produce a T whose bytes are initialized to any sequence of valid u8s'), IntoBytes ('sound to treat any t: T as an immutable [u8]'), TryFromBytes (runtime validity check; 'not symmetrical with IntoBytes'); https://docs.rs/zerocopy/0.8.63/zerocopy/trait.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.IntoBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.TryFromBytes.html
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: the compiler guarantees that Src is soundly union-transmutable into Dst under the given assumptions (L14-17); union-transmutes 'permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44); Assume::SAFETY (L319); https://github.com/rust-lang/rust/blob/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/library/core/src/mem/transmutability.rs
- **Design question:** Which conditions make a by-value byte reinterpretation (transmute, from_bytes-style cast) total and value-preserving, and when do chains of reinterpretations compose?
- **Basis:** execution (Lean kernel check): `transmute_comp_of_total_of_encodeLeast_of_intoBytes` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R2a, R2b and R3 under R2a above.

### R4a: R4a-product-decodeMono

- **Lean:** `Toy.Repr.prodRep_decodeMono_of_fields` (`lean/ToyRepr/Product.lean`); kind `theorem`; tier `T2`; depth `shallow`.
- **Tier:** `T2`. AeneasVerif/aeneas pull request 1447 proves the laws for every valid layout of its own machine types; stated here per law, parametric in arbitrary field representations (not tied to a fixed type language), for an explicit product construction, recording which layout condition each law needs. DecodeMono needs none (pull request 1447's tuple case does not use disjointness either).
- **Plain claim:** For the explicit product construction prodRep (fields at given offsets, padding uninit, each field decoded from its own range), if every field satisfies DecodeMono then so does the product, for any layout, even with overlapping fields.

```lean
theorem prodRep_decodeMono_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hM : ∀ j, (r j).DecodeMono) : (prodRep L r).DecodeMono
```

Unfolded:

```lean
(∀ j, Mono (r j)) → Mono (prodRep L r)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hM` | Each field's decode is monotone on its slice. | `tight` | `prodRep_decodeMono_tight_hM` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Two u8 fields at offsets 0 and 2 with one padding byte (`prodRep_laws_nonvacuous`).
- **Prior art:**
  - J. Hostert, '[WIP] Layouts, machine types, low-level representations.', AeneasVerif/aeneas pull request 1447 (open draft), head commit 2a1dd75567517e078f90b1df746af7373fe24cbc (fork JoJoDeveloping/aeneas, branch layouts; Apache-2.0): GaloisConnection.lean L101-256 proves DecodeMono, DecodeEncode and EncodeDecodeLeDefined for every Layout.Valid layout (integers, tuples with explicit field offsets under its validity conditions, enums with tags and niches) of its own machine types; its tuple helper encode_tuple_le_defined (L88-97) assumes field bounds but no disjointness. Tuple encoding there writes fields left to right (on overlap the last field wins), unlike prodEncode here; https://github.com/AeneasVerif/aeneas/pull/1447
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
  - H. Tuch, G. Klein, M. Norrish, 'Types, bytes, and separation logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234: Isabelle/HOL axiomatic type class with to-bytes / from-bytes between values and plain byte lists, requiring from-bytes (to-bytes v) = v; there are no uninitialized bytes, and structs with padding are left to extensions of the model
- **Design question:** Do the representation laws and the IntoBytes/FromBytes predicates compose through structs with explicit field offsets, and which layout conditions does each one need?
- **Basis:** execution (Lean kernel check): `prodRep_decodeMono_of_fields` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge), for R4a-R4e: A `Layout` is a fixed placement of fields (sizes and offsets in any order, no alignment), as chosen by `repr(C)`, `repr(packed)`, or by the compiler for a `repr(Rust)` struct once its layout is fixed; it is an input, not derived. zerocopy 0.8.63 documents that `derive(FromBytes)` on a struct requires all fields `FromBytes` ("padding bytes do not have any validity constraints") and that `derive(IntoBytes)` requires fields `IntoBytes` and no padding; R4e and R4d are the toy analogues for `prodRep` over provenance-free bytes, with the divergences listed for R2a. MiniRust's tuple encode writes padding as `Uninit` and its decode ignores padding (L279-281), which is what `prodEncode`/`prodDecode` do. The open AeneasVerif/aeneas pull request 1447 (not merged) is context only: it proves the laws for the valid layouts of its own machine types.

### R4b: R4b-product-decodeEncode

- **Lean:** `Toy.Repr.prodRep_decodeEncode_of_fields_of_disjoint` (`lean/ToyRepr/Product.lean`); kind `theorem`; tier `T2`; depth `shallow`.
- **Tier:** `T2`. AeneasVerif/aeneas pull request 1447 proves the laws for every valid layout of its own machine types; stated here per law, parametric in arbitrary field representations (not tied to a fixed type language), for an explicit product construction, recording which layout condition each law needs. Disjointness is the one layout condition needed, and only for this law.
- **Plain claim:** For prodRep, if every field satisfies DecodeEncode and the field byte ranges are pairwise disjoint, then the product satisfies DecodeEncode.

```lean
theorem prodRep_decodeEncode_of_fields_of_disjoint (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hDE : ∀ j, (r j).DecodeEncode) (hD : L.Disjoint) : (prodRep L r).DecodeEncode
```

Unfolded:

```lean
(∀ j, DE (r j)) → (∀ j ≠ j', ∀ i, ¬ (i ∈ [off j, off j + size j) ∧ i ∈ [off j', off j' + size j'))) → DE (prodRep L r)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDE` | Each field round-trips on its own slice. | `tight` | `prodRep_decodeEncode_tight_hDE` |
| `hD` | No byte is shared by two fields, so each slice of the encoding is that field's encoding. | `tight` | `prodRep_decodeEncode_tight_hD` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Two u8 fields at offsets 0 and 2 (`prodRep_laws_nonvacuous`).
- **Prior art:**
  - J. Hostert, '[WIP] Layouts, machine types, low-level representations.', AeneasVerif/aeneas pull request 1447 (open draft), head commit 2a1dd75567517e078f90b1df746af7373fe24cbc (fork JoJoDeveloping/aeneas, branch layouts; Apache-2.0): GaloisConnection.lean L101-256 proves DecodeMono, DecodeEncode and EncodeDecodeLeDefined for every Layout.Valid layout (integers, tuples with explicit field offsets under its validity conditions, enums with tags and niches) of its own machine types; its tuple helper encode_tuple_le_defined (L88-97) assumes field bounds but no disjointness. Tuple encoding there writes fields left to right (on overlap the last field wins), unlike prodEncode here; https://github.com/AeneasVerif/aeneas/pull/1447
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
  - H. Tuch, G. Klein, M. Norrish, 'Types, bytes, and separation logic', POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234: Isabelle/HOL axiomatic type class with to-bytes / from-bytes between values and plain byte lists, requiring from-bytes (to-bytes v) = v; there are no uninitialized bytes, and structs with padding are left to extensions of the model
- **Design question:** Do the representation laws and the IntoBytes/FromBytes predicates compose through structs with explicit field offsets, and which layout conditions does each one need?
- **Basis:** execution (Lean kernel check): `prodRep_decodeEncode_of_fields_of_disjoint` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R4a-R4e under R4a above.

### R4c: R4c-product-encodeLeast

- **Lean:** `Toy.Repr.prodRep_encodeLeast_of_fields` (`lean/ToyRepr/Product.lean`); kind `theorem`; tier `T2`; depth `shallow`.
- **Tier:** `T2`. AeneasVerif/aeneas pull request 1447 proves the laws for every valid layout of its own machine types; stated here per law, parametric in arbitrary field representations (not tied to a fixed type language), for an explicit product construction, recording which layout condition each law needs. EncodeLeast needs none (as pull request 1447's encode_tuple_le_defined).
- **Plain claim:** For prodRep, if every field satisfies EncodeLeast then so does the product, for any layout, even with overlapping fields.

```lean
theorem prodRep_encodeLeast_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hEL : ∀ j, (r j).EncodeLeast) : (prodRep L r).EncodeLeast
```

Unfolded:

```lean
(∀ j, EL (r j)) → EL (prodRep L r)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hEL` | Each field's encoding is below every slice decoding to its value. | `tight` | `prodRep_encodeLeast_tight_hEL` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Two u8 fields at offsets 0 and 2 (`prodRep_laws_nonvacuous`).
- **Prior art:**
  - J. Hostert, '[WIP] Layouts, machine types, low-level representations.', AeneasVerif/aeneas pull request 1447 (open draft), head commit 2a1dd75567517e078f90b1df746af7373fe24cbc (fork JoJoDeveloping/aeneas, branch layouts; Apache-2.0): GaloisConnection.lean L101-256 proves DecodeMono, DecodeEncode and EncodeDecodeLeDefined for every Layout.Valid layout (integers, tuples with explicit field offsets under its validity conditions, enums with tags and niches) of its own machine types; its tuple helper encode_tuple_le_defined (L88-97) assumes field bounds but no disjointness. Tuple encoding there writes fields left to right (on overlap the last field wins), unlike prodEncode here; https://github.com/AeneasVerif/aeneas/pull/1447
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568, L279-281: tuple decode ignores padding and encode makes it Uninit; 'The generic properties defined below make this the only possible choice for encode.'
- **Design question:** Do the representation laws and the IntoBytes/FromBytes predicates compose through structs with explicit field offsets, and which layout conditions does each one need?
- **Basis:** execution (Lean kernel check): `prodRep_encodeLeast_of_fields` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R4a-R4e under R4a above.

### R4d: R4d-product-intoBytes

- **Lean:** `Toy.Repr.prodRep_intoBytes_of_fields_of_covering` (`lean/ToyRepr/Product.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Matches zerocopy's documented derive rule for IntoBytes (fields IntoBytes, no padding).
- **Plain claim:** For prodRep, if every field is IntoBytes and the fields cover every byte (no padding), the product is IntoBytes.

```lean
theorem prodRep_intoBytes_of_fields_of_covering (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hIB : ∀ j, (r j).IntoBytes) (hC : L.Covering) : (prodRep L r).IntoBytes
```

Unfolded:

```lean
(∀ j, IntoBytes (r j)) → (∀ i < n, ∃ j, i ∈ [off j, off j + size j)) → IntoBytes (prodRep L r)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hIB` | Field bytes are initialized. | `tight` | `prodRep_intoBytes_tight_hIB` |
| `hC` | No byte is padding (padding is encoded uninit). | `tight` | `prodRep_intoBytes_tight_hC` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Two u8 fields at offsets 0 and 1 (`prodRep_intoBytes_nonvacuous`).
- **Prior art:**
  - zerocopy 0.8.63 derive documentation (docs.rs): derive(FromBytes) for structs requires all fields FromBytes ('padding bytes do not have any validity constraints'); derive(IntoBytes) for structs requires fields IntoBytes and no padding bytes; https://docs.rs/zerocopy/0.8.63/zerocopy/derive.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/derive.IntoBytes.html
- **Design question:** Do the representation laws and the IntoBytes/FromBytes predicates compose through structs with explicit field offsets, and which layout conditions does each one need?
- **Basis:** execution (Lean kernel check): `prodRep_intoBytes_of_fields_of_covering` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R4a-R4e under R4a above.

### R4e: R4e-product-fromBytes

- **Lean:** `Toy.Repr.prodRep_fromBytes_of_fields` (`lean/ToyRepr/Product.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Matches zerocopy's documented derive rule for FromBytes (all fields FromBytes; padding unconstrained).
- **Plain claim:** For prodRep, if every field is FromBytes then the product is FromBytes, for any layout.

```lean
theorem prodRep_fromBytes_of_fields (L : Layout n k)
    (r : (j : Fin k) → Rep (Bytes D (L.size j)) (V j))
    (hFB : ∀ j, (r j).FromBytes) : (prodRep L r).FromBytes
```

Unfolded:

```lean
(∀ j, FromBytes (r j)) → FromBytes (prodRep L r)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hFB` | Every field decodes from any initialized slice. | `tight` | `prodRep_fromBytes_tight_hFB` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Two u8 fields at offsets 0 and 2 (`prodRep_laws_nonvacuous`).
- **Prior art:**
  - zerocopy 0.8.63 derive documentation (docs.rs): derive(FromBytes) for structs requires all fields FromBytes ('padding bytes do not have any validity constraints'); derive(IntoBytes) for structs requires fields IntoBytes and no padding bytes; https://docs.rs/zerocopy/0.8.63/zerocopy/derive.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/derive.IntoBytes.html
- **Design question:** Do the representation laws and the IntoBytes/FromBytes predicates compose through structs with explicit field offsets, and which layout conditions does each one need?
- **Basis:** execution (Lean kernel check): `prodRep_fromBytes_of_fields` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R4a-R4e under R4a above.

### R5a: R5a-total-iff-image-in-validity-set

- **Lean:** `Toy.Repr.transmuteTotal_iff_image_subset_valid` (`lean/ToyRepr/Transmute.lean`); kind `characterization`; tier `T0`; depth `definitional`.
- **Tier:** `T0`. Definitional reference point: a reindexing of quantifiers in the definition of transmute; recorded as the baseline that R5b and R5c refine (when the image of encode_A may be replaced by A's whole validity set).
- **Plain claim:** In any carrier, transmute A→B is total iff every encoding of an A value lies in B's validity set (decodes as B). (Reference point for R5b and R5c.)

```lean
theorem transmuteTotal_iff_image_subset_valid {α A B : Type} (ra : Rep α A) (rb : Rep α B) :
    TransmuteTotal ra rb ↔ ∀ x : α, ra.Image x → rb.Valid x
```

Unfolded:

```lean
(∀ a, ∃ b, rb.decode (ra.encode a) = some b) ↔ ∀ x, (∃ a, ra.encode a = x) → ∃ b, rb.decode x = some b
```

Hypothesis ledger: no hypotheses beyond the objects quantified over.

- **Depth:** `definitional`.
- **Non-vacuity witness:** u8→u8 (both sides hold) and u8→bool (both fail) (`transmuteTotal_iff_image_subset_valid_nonvacuous`).
- **Prior art:**
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: the compiler guarantees that Src is soundly union-transmutable into Dst under the given assumptions (L14-17); union-transmutes 'permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44); Assume::SAFETY (L319); https://github.com/rust-lang/rust/blob/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/library/core/src/mem/transmutability.rs
- **Design question:** Is a transmute-totality check that compares validity sets sound once uninitialized padding exists, and over which byte patterns must the comparison range?
- **Basis:** execution (Lean kernel check): `transmuteTotal_iff_image_subset_valid` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge), for R5a-R5c: rustc's transmutability checker (`compiler/rustc_transmute` at rust-lang/rust commit `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`) represents each byte as a value range in which 0..=255 are initialized values and 256 is an uninitialized byte, and checks that every source byte sequence has a compatible destination continuation. R5b states, for representations satisfying the stated laws, that totality of a by-value transmute coincides with validity-set inclusion over such abstract bytes, and R5c that the comparison may be restricted to initialized bytes only when the source has no padding. Nothing here claims that rustc's checker, or any real type's representation, satisfies these laws; reference transmutes, alignment, safety invariants (`Assume::SAFETY`) and size-extending union-transmutes are not modeled.

### R5b: R5b-total-iff-validity-set-inclusion

- **Lean:** `Toy.Repr.transmuteTotal_iff_valid_subset_of_laws` (`lean/ToyRepr/Transmute.lean`); kind `characterization`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Validity-set inclusion is the standard soundness criterion for value transmutes; this states the exact laws under which it coincides with totality once uninit bytes exist. The production transmutability checker in rustc compares validity over abstract bytes that include an uninitialized byte value, the setting of this result.
- **Plain claim:** In any carrier with any definedness relation, if A satisfies DecodeEncode and EncodeLeast and B satisfies DecodeMono, then transmute A→B is total iff every byte vector valid for A (including partially uninitialized ones) is valid for B.

```lean
theorem transmuteTotal_iff_valid_subset_of_laws {α A B : Type} [Definedness α]
    (ra : Rep α A) (rb : Rep α B)
    (hDE_A : ra.DecodeEncode) (hEL_A : ra.EncodeLeast) (hM_B : rb.DecodeMono) :
    TransmuteTotal ra rb ↔ ∀ x : α, ra.Valid x → rb.Valid x
```

Unfolded:

```lean
DE ra → EL ra → Mono rb →
((∀ a, ∃ b, rb.decode (ra.encode a) = some b) ↔ ∀ x, (∃ a, ra.decode x = some a) → ∃ b, rb.decode x = some b)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDE_A` | Encodings of A are valid for A (inclusion implies totality). | `tight` | `transmuteTotal_iff_valid_subset_tight_hDE_A` |
| `hEL_A` | Every A-valid vector lies above an encoding (totality implies inclusion). | `tight` | `transmuteTotal_iff_valid_subset_tight_hEL_A` |
| `hM_B` | B-validity propagates from the encoding up to the vector above it. | `tight` | `transmuteTotal_iff_valid_subset_tight_hM_B` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** A = two-byte integer, B = padded u8 struct (`transmuteTotal_iff_valid_subset_nonvacuous`).
- **Prior art:**
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: the compiler guarantees that Src is soundly union-transmutable into Dst under the given assumptions (L14-17); union-transmutes 'permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44); Assume::SAFETY (L319); https://github.com/rust-lang/rust/blob/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/library/core/src/mem/transmutability.rs
  - rust-lang/rust compiler/rustc_transmute at commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: src/layout/mod.rs L14-27 represents abstract bytes as value ranges where 0..=255 are initialized bytes and 256 (Byte::UNINIT) is an uninitialized byte; src/maybe_transmutable/mod.rs walks source and destination layout automata and, unless validity is assumed, requires every source transition to admit a compatible destination continuation (L170-205), prunes destination paths that may carry safety invariants unless safety is assumed (L102-107), and adds a reverse obligation for mutable destination references (L91-93); https://github.com/rust-lang/rust/tree/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/compiler/rustc_transmute/src
  - MiniRust, spec/lang/representation.md, repository minirust/minirust, commit 063d784186d3252bee242217f218223205c0b568: generic properties (encode/decode monotone, decode(encode(v)) == Some(v), decode(bytes) == Some(v) implies encode(v) <= bytes) at L754-763, described as an adjoint relationship / Galois connection at L765-766; https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
- **Design question:** Is a transmute-totality check that compares validity sets sound once uninitialized padding exists, and over which byte patterns must the comparison range?
- **Basis:** execution (Lean kernel check): `transmuteTotal_iff_valid_subset_of_laws` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R5a-R5c under R5a above.

### R5c: R5c-total-iff-initialized-validity-inclusion

- **Lean:** `Toy.Repr.transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast` (`lean/ToyRepr/Transmute.lean`); kind `characterization`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. States when the uninit-free 'bit validity' criterion is exact; the padded-source counterexample shows it is unsound otherwise.
- **Plain claim:** For equal-size byte representations, if A is IntoBytes and satisfies DecodeEncode and EncodeLeast, then transmute A→B is total iff every fully initialized byte pattern valid for A is valid for B; no law on B is needed, and without IntoBytes A the criterion can hold while every transmute fails.

```lean
theorem transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hIB_A : ra.IntoBytes) (hDE_A : ra.DecodeEncode) (hEL_A : ra.EncodeLeast) :
    TransmuteTotal ra rb ↔ ∀ ds : Vector D n, ra.InitValid ds → rb.InitValid ds
```

Unfolded:

```lean
IntoBytes ra → DE ra → EL ra →
((∀ a, ∃ b, rb.decode (ra.encode a) = some b) ↔
 ∀ ds : Vector D n, (∃ a, ra.decode (ds.map init) = some a) → ∃ b, rb.decode (ds.map init) = some b)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hIB_A` | Encodings of A are initialized patterns, so initialized validity sees them. | `tight` | `transmuteTotal_iff_initValid_subset_tight_hIB_A` |
| `hDE_A` | Encodings of A are A-valid patterns. | `tight` | `transmuteTotal_iff_initValid_subset_tight_hDE_A` |
| `hEL_A` | With hIB_A, every A-valid initialized pattern is exactly an encoding. | `tight` | `transmuteTotal_iff_initValid_subset_tight_hEL_A` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** A = two-byte integer (`transmuteTotal_iff_initValid_subset_nonvacuous`).
- **Prior art:**
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
  - zerocopy 0.8.63 documentation (docs.rs): FromBytes ('sound to produce a T whose bytes are initialized to any sequence of valid u8s'), IntoBytes ('sound to treat any t: T as an immutable [u8]'), TryFromBytes (runtime validity check; 'not symmetrical with IntoBytes'); https://docs.rs/zerocopy/0.8.63/zerocopy/trait.FromBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.IntoBytes.html, https://docs.rs/zerocopy/0.8.63/zerocopy/trait.TryFromBytes.html
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: the compiler guarantees that Src is soundly union-transmutable into Dst under the given assumptions (L14-17); union-transmutes 'permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44); Assume::SAFETY (L319); https://github.com/rust-lang/rust/blob/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/library/core/src/mem/transmutability.rs
  - rust-lang/rust compiler/rustc_transmute at commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: src/layout/mod.rs L14-27 represents abstract bytes as value ranges where 0..=255 are initialized bytes and 256 (Byte::UNINIT) is an uninitialized byte; src/maybe_transmutable/mod.rs walks source and destination layout automata and, unless validity is assumed, requires every source transition to admit a compatible destination continuation (L170-205), prunes destination paths that may carry safety invariants unless safety is assumed (L102-107), and adds a reverse obligation for mutable destination references (L91-93); https://github.com/rust-lang/rust/tree/6905905bb7727fd0f9223f5fdc9ad4e62236d5a2/compiler/rustc_transmute/src
- **Design question:** Is a transmute-totality check that compares validity sets sound once uninitialized padding exists, and over which byte patterns must the comparison range?
- **Basis:** execution (Lean kernel check): `transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R5a-R5c under R5a above.

### R6a: R6a-int-ptr-int-roundtrip-lossless

- **Lean:** `Toy.Repr.int_ptr_int_roundtrip_of_decodeEncode` (`lean/ToyRepr/Provenance.lean`); kind `theorem`; tier `T1`; depth `definitional`.
- **Tier:** `T1`. The Rust standard library documentation states that integers can be converted to pointers and back without loss; made precise for byte representations with provenance.
- **Plain claim:** With provenance-carrying bytes and the canonical encoders (integers without provenance, pointers tagging every byte with their provenance), at any size n + 1 >= 1, for any integer and pointer decoders that both satisfy DecodeEncode, integer x transmutes to the pointer (x, none) and back to x.

```lean
theorem int_ptr_int_roundtrip_of_decodeEncode {β P : Type} {n : Nat}
    (di : PBytes β P (n + 1) → Option (Vector β (n + 1)))
    (dp : PBytes β P (n + 1) → Option (Vector β (n + 1) × Option P))
    (hDEi : (⟨intEncode, di⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1))).DecodeEncode)
    (hDEp : (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode)
    (x : Vector β (n + 1)) :
    transmute (⟨intEncode, di⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1))) ⟨ptrEncode, dp⟩ x =
      some (x, none) ∧
    transmute (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      ⟨intEncode, di⟩ (x, none) = some x
```

Unfolded:

```lean
-- sizes n + 1 ≥ 1
(∀ x, di (intEncode x) = some x) → (∀ p, dp (ptrEncode p) = some p) →
∀ x, dp (intEncode x) = some (x, none) ∧ di (ptrEncode (x, none)) = some x
-- intEncode x = [init (x[i], none)]ᵢ = ptrEncode (x, none)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDEi` | The integer decoder recovers integers from their encodings. | `tight` | `int_ptr_int_roundtrip_tight_hDEi` |
| `hDEp` | The pointer decoder recovers provenance-free pointers from their encodings (pointer values without provenance exist and are decoded). | `tight` | `int_ptr_int_roundtrip_tight_hDEp` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `definitional`.
- **Non-vacuity witness:** Provenance-stripping integers and strict (uniform-provenance) pointers, size 1 (`int_ptr_int_roundtrip_nonvacuous`).
- **Prior art:**
  - Rust core 1.100.0 documentation, core::mem::transmute, section 'Transmutation between pointers and integers': 'doing a pointer-to-integer-to-pointer roundtrip via transmute is not a lossless process' and, for *mut (), 'integers can be converted to pointers and back without any loss (via as casts or via transmute)'; core::ptr::without_provenance ('Creates a pointer with the given address and no provenance'); https://doc.rust-lang.org/1.100.0/core/mem/fn.transmute.html
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568: AbstractByte::le_defined (L649-670, 'adding provenance makes it more defined'), Value::le_defined with the pointer provenance order (L672-699, L713-734), integer decode ignores provenance and encode emits none (L77-93: ptr-to-int transmute behaves like addr, 'required to achieve a "monotonicity" with respect to provenance'), pointer decode yields no provenance for missing or mixed provenance (L102-131)
  - AeneasVerif/aeneas pull request 1497 ('Fournet/wip memory model', open draft), head commit d17ca83fc07d712d1785f650840cb2073c259e69, backends/lean/Aeneas/Std/Heap/Repr.lean: pointers always carry a provenance (RawPtr, L17-20); bytes are uninit | data | pointer lane (L33-37); Repr has a relational encode : ty → Vector Byte size → Prop with encode_complete, encode_decode and decode_mono and no least-encoding law (L97-118); u8 decode reads pointer lanes numerically while u8 encode writes data bytes (L42-48, L209-214); pointer decode accepts only a coherent pointer encoding and rejects integer bytes (L234-250); https://github.com/AeneasVerif/aeneas/pull/1497
- **Design question:** What changes once bytes carry pointer provenance: which order on bytes, which integer and pointer decoders are compatible with the laws, and which integer/pointer round trips are lossless?
- **Basis:** execution (Lean kernel check): `int_ptr_int_roundtrip_of_decodeEncode` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge), for R6a-R6e: MiniRust (commit `063d784186d3252bee242217f218223205c0b568`) orders abstract bytes so that "adding provenance makes it more defined" (L649-670); `AByte.leProvInc` on `PBytesInc` is that order without the byte position MiniRust stores in each provenance fragment. MiniRust's integer decode ignores provenance and its encode writes none (L77-93), which is `intDecodeStrip` / `intEncode`; its pointer decode yields no provenance when provenance is missing or mixed (L102-131), which is `ptrDecodeDegrade`; and it orders pointer values non-flatly (a pointer without provenance below the same address with provenance, L672-699), which is `PtrValLe`. R6d therefore explains why such a non-flat value order (or pointers that always carry provenance) is needed under that byte order; it does not refute MiniRust. R6a and R6b match the Rust core 1.100.0 documentation of `core::mem::transmute` (integers can be transmuted to pointers and back without loss; a pointer-to-integer-to-pointer transmute round trip is not lossless). The flat "provenance as data" order of R6c corresponds to designs in which integer loads of pointer bytes are rejected or must preserve provenance (Lee et al. 2018; CompCert's `Memdata.v`). The open AeneasVerif/aeneas pull request 1497 (not merged) is context only. All of this is argument from the cited sources, not a kernel check.

### R6b: R6b-ptr-int-ptr-roundtrip-drops-provenance

- **Lean:** `Toy.Repr.ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode` (`lean/ToyRepr/Provenance.lean`); kind `theorem`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. The Rust standard library documentation states the pointer-to-integer-to-pointer transmute round trip is lossy; MiniRust's integer decode strips provenance.
- **Plain claim:** At any pointer size n + 1 >= 1, with the provenance-stripping integer decoder and any pointer decoder satisfying DecodeEncode (canonical encoders), the pointer (a, some p) transmutes to the integer a, which transmutes back to (a, none), and (a, none) differs from (a, some p).

```lean
theorem ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode {β P : Type} {n : Nat}
    (dp : PBytes β P (n + 1) → Option (Vector β (n + 1) × Option P))
    (hDEp : (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode)
    (a : Vector β (n + 1)) (p : P) :
    transmute (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      intStripRep (a, some p) = some a ∧
    transmute intStripRep (⟨ptrEncode, dp⟩ : Rep (PBytes β P (n + 1)) (Vector β (n + 1) × Option P))
      a = some (a, none) ∧
    ((a, none) : Vector β (n + 1) × Option P) ≠ (a, some p)
```

Unfolded:

```lean
-- sizes n + 1 ≥ 1
(∀ p, dp (ptrEncode p) = some p) → ∀ a p,
intDecodeStrip (ptrEncode (a, some p)) = some a ∧ dp (intEncode a) = some (a, none) ∧ (a, none) ≠ (a, some p)
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `hDEp` | The pointer decoder recovers the provenance-free pointer (a, none) from its encoding (which is also the integer encoding of a). | `tight` | `ptr_intStrip_ptr_roundtrip_tight_hDEp` |
| `a` | The address of the pointer whose round trip is examined (a universally quantified value; it makes Vector β (n + 1), and hence β, inhabited). | `harmless` | — |
| `p` | The provenance of the pointer whose round trip is examined (a universally quantified value; it makes P inhabited). | `harmless` | — |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Strict (uniform-provenance) pointer decoder at size 1 with provenance type Unit (`ptr_intStrip_ptr_roundtrip_nonvacuous`).
- **Prior art:**
  - Rust core 1.100.0 documentation, core::mem::transmute, section 'Transmutation between pointers and integers': 'doing a pointer-to-integer-to-pointer roundtrip via transmute is not a lossless process' and, for *mut (), 'integers can be converted to pointers and back without any loss (via as casts or via transmute)'; core::ptr::without_provenance ('Creates a pointer with the given address and no provenance'); https://doc.rust-lang.org/1.100.0/core/mem/fn.transmute.html Same page: 'Transmuting pointers to integers in a const context is undefined behavior, unless the pointer was originally created from an integer.'
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568: AbstractByte::le_defined (L649-670, 'adding provenance makes it more defined'), Value::le_defined with the pointer provenance order (L672-699, L713-734), integer decode ignores provenance and encode emits none (L77-93: ptr-to-int transmute behaves like addr, 'required to achieve a "monotonicity" with respect to provenance'), pointer decode yields no provenance for missing or mixed provenance (L102-131)
  - K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, 'Exploring C semantics and pointer provenance', Proc. ACM Program. Lang. 3 (POPL), Article 67, pp. 67:1-67:32, 2019, doi:10.1145/3290380: two semantics, PVI (provenance tracked via integers: all integer values carry a provenance) and PNVI (integers carry no provenance; provenance is recreated at integer-to-pointer casts) (p. 67:7); bytewise copies of pointers work in PVI because each byte carries the pointer's provenance, and in PNVI because reading a pointer from provenance-free bytes uses the integer-to-pointer cast semantics (p. 67:10); abstract bytes are triples of a provenance, a byte value or unspec, and an optional pointer-byte index; pointer bytes carry the pointer's provenance and their index 0..sizeof-1; integer bytes carry provenance in PVI and empty provenance in PNVI; padding bytes are unspecified; when a pointer or integer value is read from abstract bytes in PVI, a pointer with address 0 gets the empty provenance; for non-zero pointer values and integer values, if at least one byte has non-empty provenance and all other bytes have either that same provenance or empty provenance, that provenance is taken, and otherwise (e.g. two different non-empty provenances) the empty provenance is taken (pp. 67:15-67:16)
- **Design question:** What changes once bytes carry pointer provenance: which order on bytes, which integer and pointer decoders are compatible with the laws, and which integer/pointer round trips are lossless?
- **Basis:** execution (Lean kernel check): `ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R6a-R6e under R6a above.

### R6c: R6c-provenance-as-data-integers-not-lawful-and-fromBytes

- **Lean:** `Toy.Repr.no_int_decoder_encodeLeast_fromBytes_of_provenance` (`lean/ToyRepr/Provenance.lean`); kind `impossibility`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Corresponds to the known design split between stripping provenance on integer loads (MiniRust; PNVI-style integers) and treating pointer-to-integer type punning as invalid (Lee et al.); stated here as an impossibility for the flat order.
- **Plain claim:** If bytes carry provenance ordered as plain data (init (b,q) ⊑ init (b',q') only when equal), a byte value and a provenance exist, and n ≥ 1, then no decoder for the canonical (provenance-free) integer encoder satisfies both EncodeLeast and FromBytes over provenance-carrying bytes.

```lean
theorem no_int_decoder_encodeLeast_fromBytes_of_provenance {β P : Type} {n : Nat}
    (b0 : β) (p0 : P) (hn : 0 < n) (d : PBytes β P n → Option (Vector β n)) :
    ¬ ((⟨intEncode, d⟩ : Rep (PBytes β P n) (Vector β n)).EncodeLeast ∧
       (⟨intEncode, d⟩ : Rep (PBytes β P n) (Vector β n)).FromBytes)
```

Unfolded:

```lean
β inhabited (b0) → P inhabited (p0) → 0 < n → ∀ d,
¬ ((∀ x v, d x = some v → intEncode v ⊑ x) ∧ (∀ x, (∀ i, x[i] ≠ uninit) → ∃ v, d x = some v))
-- ⊑ is the flat order on AByte (β × Option P): init (b, q) ⊑ init (b', q') ↔ (b, q) = (b', q')
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `b0` | Some byte value exists, so initialized bytes exist. | `tight` | `no_int_decoder_tight_b0` |
| `p0` | Some provenance exists, so initialized bytes can differ from integer encodings. | `tight` | `no_int_decoder_tight_p0` |
| `hn` | At least one byte. | `tight` | `no_int_decoder_tight_hn` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Byte = UInt8, provenance type Unit, n = 1 (`no_int_decoder_nonvacuous`).
- **Positive control:** `no_int_decoder_positive_control`: dropping `EncodeLeast`, the stripping decoder `intStripRep` is `FromBytes` (and satisfies `DecodeMono` and `DecodeEncode`); dropping `FromBytes`, the rejecting decoder `intStrictRep` satisfies all three laws (size 1, provenance `Unit`).
- **Prior art:**
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568: AbstractByte::le_defined (L649-670, 'adding provenance makes it more defined'), Value::le_defined with the pointer provenance order (L672-699, L713-734), integer decode ignores provenance and encode emits none (L77-93: ptr-to-int transmute behaves like addr, 'required to achieve a "monotonicity" with respect to provenance'), pointer decode yields no provenance for missing or mixed provenance (L102-131)
  - J. Lee, C.-K. Hur, R. Jung, Z. Liu, J. Regehr, N. P. Lopes, 'Reconciling high-level optimizations and low-level code in LLVM', Proc. ACM Program. Lang. 2 (OOPSLA), Article 125, pp. 125:1-125:28, 2018, doi:10.1145/3276495 (loading an integer from pointer bytes without an explicit cast yields poison, i.e. the provenance-rejecting design)
  - AeneasVerif/aeneas pull request 1497 ('Fournet/wip memory model', open draft), head commit d17ca83fc07d712d1785f650840cb2073c259e69, backends/lean/Aeneas/Std/Heap/Repr.lean: pointers always carry a provenance (RawPtr, L17-20); bytes are uninit | data | pointer lane (L33-37); Repr has a relational encode : ty → Vector Byte size → Prop with encode_complete, encode_decode and decode_mono and no least-encoding law (L97-118); u8 decode reads pointer lanes numerically while u8 encode writes data bytes (L42-48, L209-214); pointer decode accepts only a coherent pointer encoding and rejects integer bytes (L234-250); https://github.com/AeneasVerif/aeneas/pull/1497
  - K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, 'Exploring C semantics and pointer provenance', Proc. ACM Program. Lang. 3 (POPL), Article 67, pp. 67:1-67:32, 2019, doi:10.1145/3290380: two semantics, PVI (provenance tracked via integers: all integer values carry a provenance) and PNVI (integers carry no provenance; provenance is recreated at integer-to-pointer casts) (p. 67:7); bytewise copies of pointers work in PVI because each byte carries the pointer's provenance, and in PNVI because reading a pointer from provenance-free bytes uses the integer-to-pointer cast semantics (p. 67:10); abstract bytes are triples of a provenance, a byte value or unspec, and an optional pointer-byte index; pointer bytes carry the pointer's provenance and their index 0..sizeof-1; integer bytes carry provenance in PVI and empty provenance in PNVI; padding bytes are unspecified; when a pointer or integer value is read from abstract bytes in PVI, a pointer with address 0 gets the empty provenance; for non-zero pointer values and integer values, if at least one byte has non-empty provenance and all other bytes have either that same provenance or empty provenance, that provenance is taken, and otherwise (e.g. two different non-empty provenances) the empty provenance is taken (pp. 67:15-67:16)
  - X. Leroy, A. W. Appel, S. Blazy, G. Stewart, CompCert memory model, common/Memdata.v in repository AbsInt/CompCert at commit 2685140bf72c959446981fb99b5e44a8975021bc: memval := Undef | Byte | Fragment (pointer fragment with index) (L209-212); decode_val (L437-461) reads byte-level chunks only from Byte memvals via proj_bytes (L368) and yields Vundef on pointer fragments except for pointer-sized chunks, which reassemble the pointer value (no stripping); memval_inject / memval_lessdef put Undef below every memval and relate Byte and Fragment memvals only to matching ones (L813-821, L985), with monotonicity of decoding decode_val_inject (L908); https://github.com/AbsInt/CompCert/blob/2685140bf72c959446981fb99b5e44a8975021bc/common/Memdata.v
  - J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis, 'A formal C memory model supporting integer-pointer casts', PLDI 2015, pp. 326-335, doi:10.1145/2737924.2738005 (quasi-concrete model: a block gets a concrete address when a pointer to it is cast to an integer; a state-dependent alternative outside the state-free representations modeled here)
- **Design question:** What changes once bytes carry pointer provenance: which order on bytes, which integer and pointer decoders are compatible with the laws, and which integer/pointer round trips are lossless?
- **Basis:** execution (Lean kernel check): `no_int_decoder_encodeLeast_fromBytes_of_provenance` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R6a-R6e under R6a above.

### R6d: R6d-provenance-increasing-order-no-lawful-optional-provenance-pointers

- **Lean:** `Toy.Repr.no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc` (`lean/ToyRepr/Provenance.lean`); kind `impossibility`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Explains MiniRust's use of a non-flat value order for pointers (no provenance below provenance); stated as an impossibility for the flat value order and pointer values with optional provenance.
- **Plain claim:** If adding provenance makes a byte more defined (MiniRust's byte order), pointer values have optional provenance (Vector β (n + 1) × Option P, size n + 1 >= 1), and some byte value and some provenance exist, then no decoder for the canonical pointer encoder satisfies both DecodeMono with the flat value order and DecodeEncode.

```lean
theorem no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc {β P : Type} {n : Nat}
    (b0 : β) (p0 : P) (d : PBytesInc β P (n + 1) → Option (Vector β (n + 1) × Option P)) :
    ¬ ((⟨ptrEncodeInc, d⟩ : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeMono ∧
       (⟨ptrEncodeInc, d⟩ : Rep (PBytesInc β P (n + 1)) (Vector β (n + 1) × Option P)).DecodeEncode)
```

Unfolded:

```lean
-- sizes n + 1 ≥ 1; pointer values Vector β (n + 1) × Option P (optional provenance)
β inhabited (b0) → P inhabited (p0) → ∀ d,
¬ ((∀ x y, x ⊑ y → d x ⊑ d y) ∧ (∀ p, d (ptrEncodeInc p) = some p))
-- ⊑ on PBytesInc: init (b, none) ⊑ init (b', q) ↔ b = b'; init (b, some p) ⊑ init (b', q) ↔ b = b' ∧ q = some p
-- ⊑ on Option values: flat
```

Hypothesis ledger:

| hypothesis | purpose | tightness | counterexample |
| :--- | :--- | :--- | :--- |
| `b0` | Some byte value exists, so pointer addresses exist. | `tight` | `no_ptr_decoder_tight_b0` |
| `p0` | Some provenance exists. | `tight` | `no_ptr_decoder_tight_p0` |

Each counterexample theorem states that a concrete instance satisfies all the other hypotheses and the conclusion fails.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Byte = UInt8, provenance type Unit, size 1 (`no_ptr_decoder_nonvacuous`).
- **Positive control:** `no_ptr_decoder_positive_control`: (1) with provenance as data the strict pointer representation satisfies all three laws; (2) under the provenance-increasing order each law alone is satisfiable for the canonical pointer encoder (`DecodeMono` by the always-failing decoder; `DecodeEncode`, with `EncodeLeast`, by the strict decoder); (3) pointers that always carry provenance (`reqProvPtrRepInc`) satisfy all three laws under the provenance-increasing order; (4) with the value order `PtrValLe` the degrading decoder `ptrDegradeRepInc` is monotone and satisfies `DecodeEncode` and `EncodeLeast` (the positive control instantiates this at size 2, where mixed provenance can occur; `ptrDegradeRepInc_lawful_by_ptrValLe` proves it at every pointer size n + 1 ≥ 1); (5) the stripping integer representation satisfies all three laws under the provenance-increasing order.
- **Prior art:**
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568: AbstractByte::le_defined (L649-670, 'adding provenance makes it more defined'), Value::le_defined with the pointer provenance order (L672-699, L713-734), integer decode ignores provenance and encode emits none (L77-93: ptr-to-int transmute behaves like addr, 'required to achieve a "monotonicity" with respect to provenance'), pointer decode yields no provenance for missing or mixed provenance (L102-131)
  - K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, 'Exploring C semantics and pointer provenance', Proc. ACM Program. Lang. 3 (POPL), Article 67, pp. 67:1-67:32, 2019, doi:10.1145/3290380: two semantics, PVI (provenance tracked via integers: all integer values carry a provenance) and PNVI (integers carry no provenance; provenance is recreated at integer-to-pointer casts) (p. 67:7); bytewise copies of pointers work in PVI because each byte carries the pointer's provenance, and in PNVI because reading a pointer from provenance-free bytes uses the integer-to-pointer cast semantics (p. 67:10); abstract bytes are triples of a provenance, a byte value or unspec, and an optional pointer-byte index; pointer bytes carry the pointer's provenance and their index 0..sizeof-1; integer bytes carry provenance in PVI and empty provenance in PNVI; padding bytes are unspecified; when a pointer or integer value is read from abstract bytes in PVI, a pointer with address 0 gets the empty provenance; for non-zero pointer values and integer values, if at least one byte has non-empty provenance and all other bytes have either that same provenance or empty provenance, that provenance is taken, and otherwise (e.g. two different non-empty provenances) the empty provenance is taken (pp. 67:15-67:16)
  - AeneasVerif/aeneas pull request 1497 ('Fournet/wip memory model', open draft), head commit d17ca83fc07d712d1785f650840cb2073c259e69, backends/lean/Aeneas/Std/Heap/Repr.lean: pointers always carry a provenance (RawPtr, L17-20); bytes are uninit | data | pointer lane (L33-37); Repr has a relational encode : ty → Vector Byte size → Prop with encode_complete, encode_decode and decode_mono and no least-encoding law (L97-118); u8 decode reads pointer lanes numerically while u8 encode writes data bytes (L42-48, L209-214); pointer decode accepts only a coherent pointer encoding and rejects integer bytes (L234-250); https://github.com/AeneasVerif/aeneas/pull/1497
  - Rust Unsafe Code Guidelines Reference, Glossary (reference/src/glossary.md), rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce: validity invariant (L280-312), padding: 'the byte at index i is entirely ignored by Vrel_T' (L168-184), abstract bytes Uninit | Init(u8, Option<Provenance>) (L26-40), representation relation (L246-249)
- **Design question:** What changes once bytes carry pointer provenance: which order on bytes, which integer and pointer decoders are compatible with the laws, and which integer/pointer round trips are lossless?
- **Basis:** execution (Lean kernel check): `no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R6a-R6e under R6a above.

### R6e: R6e-composition-fails-under-provenance-increasing-order

- **Lean:** `Toy.Repr.transmute_comp_fails_of_provInc` (`lean/ToyRepr/Provenance.lean`); kind `counterexample`; tier `T1`; depth `shallow`.
- **Tier:** `T1`. Concrete instance showing that R3 depends on the flat byte order.
- **Plain claim:** When adding provenance increases definedness, R3's conclusion fails even though all three representations satisfy all three laws: with A = C = pointers that always carry provenance and B = provenance-stripping integers (size 1, provenance Unit), A→B is total and B's encodings are fully initialized, yet A→B→C fails at (#v[0], ()) while A→C returns (#v[0], ()).

```lean
theorem transmute_comp_fails_of_provInc :
    ((reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeMono ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).DecodeEncode ∧
      (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit)).EncodeLeast) ∧
    ((intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeMono ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).DecodeEncode ∧
      (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).EncodeLeast) ∧
    (∀ x : Vector Byte 1,
      ((intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1)).encode x).bytes.IsInit) ∧
    TransmuteTotal (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
      intStripRepInc ∧
    (transmute (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
        intStripRepInc (#v[0], ())).bind
        (transmute (intStripRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1))
          (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))) = none ∧
    transmute (reqProvPtrRepInc : Rep (PBytesInc Byte Unit 1) (Vector Byte 1 × Unit))
        reqProvPtrRepInc (#v[0], ()) = some (#v[0], ())
```

Unfolded:

```lean
-- A = C = reqProvPtrRepInc (values Vector Byte 1 × Unit), B = intStripRepInc, over PBytesInc Byte Unit 1
(Mono A ∧ DE A ∧ EL A) ∧ (Mono B ∧ DE B ∧ EL B) ∧ (∀ x, B.encode x fully initialized) ∧ TransmuteTotal A B ∧
(A → B → C) (#v[0], ()) = none ∧ (A → C) (#v[0], ()) = some (#v[0], ())
```

Hypothesis ledger: no hypotheses beyond the objects quantified over.

- **Depth:** `shallow`.
- **Non-vacuity witness:** Concrete instance (size 1, provenance type Unit) (`transmute_comp_fails_of_provInc`).
- **Prior art:**
  - MiniRust representation.md at commit 063d784186d3252bee242217f218223205c0b568: AbstractByte::le_defined (L649-670, 'adding provenance makes it more defined'), Value::le_defined with the pointer provenance order (L672-699, L713-734), integer decode ignores provenance and encode emits none (L77-93: ptr-to-int transmute behaves like addr, 'required to achieve a "monotonicity" with respect to provenance'), pointer decode yields no provenance for missing or mixed provenance (L102-131)
  - Rust core 1.100.0 documentation, core::mem::transmute, section 'Transmutation between pointers and integers': 'doing a pointer-to-integer-to-pointer roundtrip via transmute is not a lossless process' and, for *mut (), 'integers can be converted to pointers and back without any loss (via as casts or via transmute)'; core::ptr::without_provenance ('Creates a pointer with the given address and no provenance'); https://doc.rust-lang.org/1.100.0/core/mem/fn.transmute.html
- **Design question:** What changes once bytes carry pointer provenance: which order on bytes, which integer and pointer decoders are compatible with the laws, and which integer/pointer round trips are lossless?
- **Basis:** execution (Lean kernel check): `transmute_comp_fails_of_provInc` and every witness and counterexample named above build without `sorry` and depend only on standard axioms (see Evidence).
- **Basis:** derived (modeling bridge): see the modeling-bridge paragraph for R6a-R6e under R6a above.

## Boundaries

### Non-claims

Known not to apply or not established, per result:

**R1a** (`threeLaws_iff_lowerAdjoint`)

- The value order is flat (some v ⊑ some w only when v = w); the equivalence is not claimed for value orders where distinct values are comparable (e.g. MiniRust's pointer provenance order).
- Stated only for the flat byte order on Bytes D n; the proof uses only reflexivity and transitivity, but no theorem here covers other byte orders.
- Says nothing about which concrete decoders are lawful; lawfulness of any particular type's representation must be established separately.
- The lifted pair (encode extended by none ↦ all-uninit, decode) need not be a Galois insertion or coinsertion: decode of the all-uninit vector need not be none (for the pure-padding type padUnitRep it is some ()), so decode after the lifted encode is not the identity on Option V at none.
- Does not capture machine-state-dependent validity checks (such as MiniRust's check_value for dereferenceability of references): decode depends only on the bytes.
- MiniRust's fourth generic law (encode monotone for a value order) is absent because values are ordered flatly here; with a non-flat value order the three laws are not claimed to characterize anything.

**R1b** (`encode_eq_iff_decodeEncode_encodeLeast`)

- Does not say that decode bytes = some v implies bytes = encode v (that fails as soon as the decoder ignores a padding byte); encode is the least element of the preimage, not its only element.
- Does not make the decoder redundant: different decoders can share an encoder unless all three laws hold (see R1c).
- The uniqueness uses antisymmetry of the flat byte order; it is stated only for Bytes D n.
- Proves uniqueness of a lawful encoder when one exists, not existence: a monotone decoder with non-empty preimages need not admit any encoder satisfying DecodeEncode and EncodeLeast (orUnitDec on two bytes accepts [init 0, uninit] and [uninit, init 0] but not [uninit, uninit], so the preimage has two minimal elements and no least one; no_lawful_encoder_for_monotone_orUnitRep). So the encoder cannot in general be defined from the decoder.

**R1c** (`decode_eq_iff_threeLaws`)

- Without DecodeMono the decoder is not determined: a decoder accepting only the exact encoding and one accepting all bytes above it can share an encoder.
- Flat value order only.
- Proves uniqueness of a lawful decoder when one exists, not existence: an injective encoder whose two encodings are incomparable need not admit any decoder satisfying DecodeMono and DecodeEncode if the encodings have a common upper bound (conflictBoolEnc: true ↦ [init 0, uninit], false ↦ [uninit, init 0], both below [init 0, init 0]; no_lawful_decoder_for_conflictBoolEnc).

**R1d** (`encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores`)

- This result is one direction only. The converse (uninit in every encoding implies ignored) needs all three laws (R1d2-uninit-in-every-encoding-is-ignored); without DecodeMono it fails (exactUnitRep: encoding uninit at byte 0, decoder reads byte 0).
- Bytes that are padding only for some values (e.g. bytes outside the active variant of an enum) are not covered: DecodeIgnores quantifies over all inputs.
- Says nothing about what a compiled program writes into padding; it constrains the abstract encoder only.

**R1d2** (`decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit`)

- Byte-by-byte only; it does not identify which bytes are padding for a particular variant of an enum-like type.
- Flat value order and flat byte order only.
- For an uninhabited value type every byte is ignored by every decoder (decode always returns none) and, vacuously, uninit in every encoding, independently of any field layout (decodeIgnores_of_empty).

**R1e** (`eq_of_encode_le_encode_of_decodeMono_decodeEncode`)

- Uses no order axioms and so says nothing about the carrier's order beyond the two encodings compared.
- With a non-flat value order (comparable distinct values) the conclusion is not claimed.
- Does not state injectivity of the encoder: for a non-reflexive relation the conclusion does not imply it. Injectivity follows from DecodeEncode alone (Rep.encode_injective_of_decodeEncode).

**R2a** (`transmuteTotal_of_intoBytes_of_fromBytes`)

- Totality only: the result need not be related to the source value in any way (no value preservation).
- Sufficient, not necessary: totality can hold without IntoBytes A or FromBytes B (R5a gives the exact criterion).
- Nothing about alignment, references, or in-place casts; only by-value reinterpretation of equal-size byte vectors is modeled.
- Establishes language-level validity (decode succeeds) only, not library safety invariants (what TransmuteFrom calls Assume::SAFETY): if B carries a safety invariant beyond validity (such as UTF-8 for str or a sortedness invariant), producing a B this way can still break safe code.
- When the byte payload carries pointer provenance (PBytes), Rep.IntoBytes and Rep.FromBytes count bytes with provenance as initialized; zerocopy's IntoBytes/FromBytes are defined relative to plain u8 bytes (zerocopy does not implement IntoBytes or FromBytes for raw pointers), so the two notions differ on provenance-carrying bytes.
- Fixes a common byte-vector length n: unlike core::mem::TransmuteFrom union-transmutes, it does not cover conversions where Src is smaller than Dst and the trailing destination bytes accept uninit.

**R2b** (`transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode`)

- IntoBytes and FromBytes on both sides do NOT suffice without EncodeLeast for A, even together with DecodeMono and DecodeEncode on both sides: u8 → boolNZ → u8 maps 2 to 1 (transmute_roundtrip_tight_hEL_A).
- Does not claim A→B→A is lossless (that is the same theorem with roles swapped and needs the swapped hypotheses).
- The intermediate value is transmute rb ra b itself and hence unique, but transmute A→B need not be injective under R2b's hypotheses: with B = boolNZRep and A = u8Rep (all hypotheses of R2b hold), true ↦ 1 ↦ true while 2 also maps to true (transmute_roundtrip_second_step_not_injective). There A = u8Rep satisfies all three laws, including DecodeEncode; the non-injectivity comes from B = boolNZRep violating EncodeLeast. Omitting DecodeEncode A instead also admits a non-injective second step (transmute_roundtrip_second_step_not_injective_of_not_decodeEncode, with B = unitZeroRep, Unit stored as [init 0] with only [init 0] decoding, which satisfies all three laws). Adding both DecodeEncode A and EncodeLeast B to R2b's hypotheses makes transmute A→B injective on successful results (transmute_injective_of_bab_hyps_of_decodeEncode_of_encodeLeast).
- Does not apply to value types A that identify several bit patterns (which violates EncodeLeast for A), such as a floating-point model that collapses distinct NaN payloads into one abstract NaN; for those the round trip can lose the original bit pattern, as boolNZRep does.
- Concerns equal-size by-value transmutes only; nothing about reference casts (&A to &B, &mut A to &mut B), alignment, or interior mutability is modeled.

**R3** (`transmute_comp_of_total_of_encodeLeast_of_intoBytes`)

- 'The conditions of R2 for each step' (IntoBytes/FromBytes for every type) do not suffice: the hEL counterexample satisfies them for all three types.
- Stated for the flat byte order; when adding provenance increases definedness the composition law fails even when all three representations satisfy all three laws (R6e-composition-fails-under-provenance-increasing-order).
- Does not assert that A→C is total.
- Requires totality of A→B on all of A: routing through a middle type with a niche (such as boolRep) makes the composite fail on inputs outside B's validity set even where A→C succeeds (transmute_comp_tight_htot).
- IntoBytes B is sufficient uniformly over all C, not necessary for a fixed C: if C ignores every byte that B leaves uninit, the composition can hold although B has padding.

**R4a** (`prodRep_decodeMono_of_fields`)

- Covers only the prodRep construction (owner = first field containing the byte); other product encoders are not covered.
- No alignment or size rounding is modeled; offsets are given (any order), so the layout chosen by repr(C), repr(packed) or the compiler for repr(Rust) is an input, not derived.
- Overlapping field ranges in prodRep do not model C or Rust unions: prodDecode requires all fields to decode simultaneously (intersecting their validity sets) and prodEncode writes every field (the first field wins on overlap), rather than encoding or decoding a single active variant.

**R4b** (`prodRep_decodeEncode_of_fields_of_disjoint`)

- Covers only prodRep; with overlapping fields DecodeEncode fails (tightness counterexample for hD).
- Overlapping field ranges in prodRep do not model C or Rust unions: prodDecode requires all fields to decode simultaneously (intersecting their validity sets) and prodEncode writes every field (the first field wins on overlap), rather than encoding or decoding a single active variant.

**R4c** (`prodRep_encodeLeast_of_fields`)

- Covers only prodRep (padding written as uninit is part of the construction, not derived).
- Overlapping field ranges in prodRep do not model C or Rust unions: prodDecode requires all fields to decode simultaneously (intersecting their validity sets) and prodEncode writes every field (the first field wins on overlap), rather than encoding or decoding a single active variant.

**R4d** (`prodRep_intoBytes_of_fields_of_covering`)

- Sufficient only; the converse (product IntoBytes implies fields IntoBytes and covering) is not stated (it needs every field type inhabited).
- Does not apply to C or Rust unions: even if the variant ranges cover all n bytes and every variant type is IntoBytes, a union initialized through a variant smaller than n leaves trailing bytes uninitialized.
- Takes a concrete layout satisfying Covering as input; in Rust, field sizes adding up to the struct size is not guaranteed for the default repr(Rust) without explicit layout guarantees (such as repr(C), repr(packed) or repr(transparent)).

**R4e** (`prodRep_fromBytes_of_fields`)

- Covers only prodRep. With overlapping fields prodRep is still FromBytes but violates DecodeEncode (R4b tightness) and does not model unions; for disjoint fields, independence from the offsets matches zerocopy's derive(FromBytes) not requiring repr(C).

**R5a** (`transmuteTotal_iff_image_subset_valid`)

- No value preservation is implied.
- Has no content beyond the definitions; it is not evidence for any checking algorithm.

**R5b** (`transmuteTotal_iff_valid_subset_of_laws`)

- Totality only; no value preservation.
- The validity sets here range over abstract byte vectors including uninit bytes; inclusion of validity sets over initialized bytes only is a different criterion (R5c).
- Applies to equal-size by-value transmutes only. It is not a criterion for mutable reference casts (&mut A to &mut B), which also need the reverse inclusion (writing any B through the reference must leave a valid A), nor for shared reference casts (&A to &B) when interior mutability (UnsafeCell) is present; alignment and lifetimes are not modeled.
- Fixes a common byte-vector length n: unlike core::mem::TransmuteFrom union-transmutes, it does not cover conversions where Src is smaller than Dst and the trailing destination bytes accept uninit.
- Establishes language-level validity (decode succeeds) only, not library safety invariants (what TransmuteFrom calls Assume::SAFETY): if B carries a safety invariant beyond validity (such as UTF-8 for str or a sortedness invariant), producing a B this way can still break safe code.

**R5c** (`transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast`)

- For sources with padding (not IntoBytes) the initialized-only criterion is unsound (tightness counterexample for hIB_A, with A = u8PadRep and B = pairRep; this B also satisfies DecodeMono, pairRep_decodeMono, so the initialized-only criterion fails even when all hypotheses of R5b hold); this does not say how real compilers treat padding.
- Totality only; no value preservation.
- InitValid is defined from the exact decoder on initialized bytes, not from zerocopy's TryFromBytes runtime check: TryFromBytes may conservatively reject valid values or enforce extra field invariants (it is documented as not symmetrical with IntoBytes), and substituting it for InitValid breaks the biconditional.
- Applies to equal-size by-value transmutes only. It is not a criterion for mutable reference casts (&mut A to &mut B), which also need the reverse inclusion (writing any B through the reference must leave a valid A), nor for shared reference casts (&A to &B) when interior mutability (UnsafeCell) is present; alignment and lifetimes are not modeled.

**R6a** (`int_ptr_int_roundtrip_of_decodeEncode`)

- Does not hold for pointer representations whose decoder rejects provenance-free bytes (then integer→pointer fails; tightness counterexample for hDEp).
- Independent of the byte order; it says nothing about which order or which decoders are lawful.
- The intermediate pointer has no provenance and grants no memory access; nothing about dereferencing is modeled.
- As-casts and exposed provenance are not modeled; only transmutes.
- Stated for sizes n + 1 >= 1: at size 0 the canonical pointer encoder forgets provenance, so no pointer decoder satisfies DecodeEncode once a provenance exists (no_ptr_decodeEncode_size_zero).
- Models raw thin pointers whose values may lack provenance (such as *const T / *mut T for sized T). It does not apply to types with further validity requirements (references, Box, NonNull, function pointers: non-null, and for references alignment and dereferenceability) or to wide pointers with metadata.
- Provenance tags carry no byte position, so the decoders considered may accept permuted or duplicated pointer bytes (ex_ptrDecodeStrict_accepts_duplicated_byte); the result does not depend on this.

**R6b** (`ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode`)

- With a provenance-rejecting integer decoder the round trip is not lossy but undefined: pointer→integer fails (transmute_ptr_intStrict_eq_none).
- Says nothing about as-casts with exposed provenance.
- Concerns the stripping integer decoder only; it says nothing about integer decoders that keep provenance (PVI-style integers, provIntRep_escape_hatch).
- Stated for sizes n + 1 >= 1 (no_ptr_decodeEncode_size_zero shows why).
- Does not model const evaluation, where transmuting a pointer with provenance to an integer is undefined behavior in Rust.

**R6c** (`no_int_decoder_encodeLeast_fromBytes_of_provenance`)

- Each property alone is achievable: the stripping decoder is FromBytes (and satisfies DecodeMono and DecodeEncode), the rejecting decoder satisfies all three laws (positive control).
- Does not concern the order where provenance increases definedness; there the stripping decoder is lawful (positive control of R6d).
- Concerns only the canonical integer encoder that writes no provenance.
- Does NOT show that integer types cannot implement zerocopy's FromBytes in provenance-as-data models: Rep.FromBytes over PBytes quantifies over all initialized abstract bytes including bytes with provenance (reading pointer bytes as an integer), whereas zerocopy's FromBytes is about plain u8 bytes and zerocopy does not implement IntoBytes for raw pointers.
- Escape hatches: integers whose values carry provenance per byte (value type Vector (β × Option P) n, provIntRep) satisfy all three laws and are FromBytes and IntoBytes (provIntRep_escape_hatch at size 1; the component lemmas provIntRep_decodeMono, provIntRep_decodeEncode, provIntRep_encodeLeast, provIntRep_fromBytes, provIntRep_intoBytes hold at every size). This is not the same as integers whose values carry a single provenance for the whole integer (value type Vector β n × Option P, encoded uniformly by ptrEncode, as for PVI integers in Memarian et al. 2019): at every size n + 2 ≥ 2, under this flat byte order and once a byte value and a provenance exist, no decoder for that encoder is both EncodeLeast and FromBytes (no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le), because an initialized vector with mixed provenance must decode but lies above no uniformly tagged encoding; combining a single provenance with degradation of mixed provenance needs the provenance-increasing byte order and a non-flat value order (as for ptrDegradeRepInc in R6d). A relational encoder without EncodeLeast (as in the UCG glossary's representation relation and AeneasVerif/aeneas pull request 1497) is outside the statement; a state-dependent model (Kang et al.) is outside the state-free Rep.

**R6d** (`no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc`)

- Depends on including provenance-free pointers (a, none) in the pointer value type: pointers that always carry provenance (value type Vector β (n + 1) × P, as RawPtr in AeneasVerif/aeneas pull request 1497) satisfy all three laws under this byte order with the flat value order (reqProvPtrRepInc_threeLaws).
- Does not refute MiniRust: with the value order PtrValLe ((a, none) below (a, some p)) a decoder that degrades missing or mixed provenance to none is monotone and satisfies DecodeEncode and EncodeLeast (ptrDegradeRepInc_lawful_by_ptrValLe).
- The non-flat value order alone is not enough at multi-byte sizes: the strict decoder, which fails on mixed provenance, is not monotone even for PtrValLe at size 2 (ptrStrictRepInc_not_decodeMonoBy_ptrValLe).
- Under the flat byte order (provenance as data) the strict pointer decoder satisfies all three laws (positive control).
- Stated for sizes n + 1 >= 1; at size 0 DecodeEncode alone already fails for every byte and value order (no_ptr_decodeEncode_size_zero), so size 0 says nothing about orders.
- Concerns only the canonical pointer encoder; provenance tags carry no byte position (MiniRust and Cerberus record one), so the strict decoder accepts duplicated or permuted pointer bytes (ex_ptrDecodeStrict_accepts_duplicated_byte).

**R6e** (`transmute_comp_fails_of_provInc`)

- The failure comes from the byte order: fully initialized bytes without provenance are not maximal when adding provenance increases definedness, so R3's IntoBytes-based argument does not apply; it does not come from any representation being unlawful.
- Says nothing about the flat byte order, where R3 applies to provenance-carrying bytes unchanged.

Across the package: nothing here is a statement about compiled code, a real compiler's transmutability checker, or the exact semantics of zerocopy's traits; each such connection is a `derived (modeling bridge)` argument in Findings.

### Escape hatches of the impossibility results

- **R6c:** integers whose values carry provenance per byte (`provIntRep`, value type `Vector (β × Option P) n`) satisfy all three laws and are `FromBytes` and `IntoBytes` (`provIntRep_escape_hatch`; component lemmas at every size). Integers carrying a single provenance per value (`Vector β n × Option P`, encoded uniformly by `ptrEncode`) do not escape at sizes `≥ 2` (`no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le`).
- **R6c:** dropping `EncodeLeast` (the stripping decoder is `FromBytes`) or dropping `FromBytes` (the rejecting decoder is lawful): `no_int_decoder_positive_control`.
- **R6c:** provenance type `Empty`, size 0, or byte type `Empty` (tightness counterexamples `no_int_decoder_tight_p0`, `no_int_decoder_tight_hn`, `no_int_decoder_tight_b0`).
- **R6c:** relational encoders without `EncodeLeast` and state-dependent models are outside the statement (they are not instances of the state-free functional `Rep`).
- **R6d:** pointer values that always carry provenance (`reqProvPtrRepInc_threeLaws`).
- **R6d:** a non-flat value order: with `PtrValLe` the degrading decoder is lawful in the sense of `DecodeMonoBy PtrValLe`, `DecodeEncode`, `EncodeLeast` (`ptrDegradeRepInc_lawful_by_ptrValLe`); the strict decoder is not monotone even for `PtrValLe` at size 2 (`ptrStrictRepInc_not_decodeMonoBy_ptrValLe`).
- **R6d:** the flat byte order (provenance as data), where the strict pointer representation is lawful (item 1 of `no_ptr_decoder_positive_control`); byte type `Empty` or provenance type `Empty` (`no_ptr_decoder_tight_b0`, `no_ptr_decoder_tight_p0`).

### Hypotheses with `unknown` tightness

None. Every hypothesis is either `tight` (with a proved counterexample) or `harmless` (`hi` in R1d and R1d2: the index bound needed to state the claim; `p` in R6b: the provenance whose round trip is examined).

### Disproved or dropped statements

None. All 22 statements were proved exactly as stated; none was found false, weakened, or dropped.

### Not examined

The modeling gaps listed under Applicability (alignment, enums and niches beyond single bytes, unions, references, `UnsafeCell`, as-casts and exposed provenance, machine-state-dependent validity, provenance byte positions, non-flat value orders other than `PtrValLe`) were not examined. No novelty search was performed; no result is claimed novel (no tier `T3`).

## Evidence

Kernel check: `lake build` of `lean/` under `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), observed 2026-11-20. The build has no warnings and no `sorry`. Axioms are computed with Lean's `collectAxioms` for every declaration of the library and recorded in `audit/axioms.json`; statement hashes are recorded in `audit/statements.json`: `statement_sha256` is the SHA-256 of the Lean `repr` of the declaration's type, and `closure_sha256` is the SHA-256 of the sorted, newline-joined list of `name : repr(type)` (plus ` := repr(value)` for non-theorems) of every package-local constant reachable from that type (theorem bodies excluded).

Main results:

| result | theorem | axioms | statement_sha256 | closure_sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| R1a | `threeLaws_iff_lowerAdjoint` | `propext` | `95904993e9fda9416cd14b99859c4ad8e789b8fc677dee87eeb3553b6cccd3c7` | `7552d2f5e3df97749d9e0cf9ffc6caf85dfd89e75beb0c30974c5171f81f6ff8` (24) |
| R1b | `encode_eq_iff_decodeEncode_encodeLeast` | `Quot.sound`, `propext` | `21b57b57c99eeacf19790dd7b7e8d9d90e562a85beb05259830fce040361ea4a` | `fd99ffa763bfb98d4757eb9c80ad34261b715277a5560b656b17bbb4c238ae6a` (19) |
| R1c | `decode_eq_iff_threeLaws` | `Quot.sound`, `propext` | `27ead02e02f0e9ceddbc48b273605e9fb19f09a2908b7499a964264dd848cf95` | `470959d751c68c53deaa707043d41675592cf81de1eca737c487527288f8e4d5` (23) |
| R1d | `encode_getElem_eq_uninit_of_decodeEncode_encodeLeast_of_decodeIgnores` | `Quot.sound`, `propext` | `6af0dda01f169602056f81f2e683f32b3e507fa01432e56b1bebea9df54a98e1` | `92e6fde20313c6ba2fd858e4233ef2811e362d233cf175c7f6facffe26266021` (20) |
| R1d2 | `decodeIgnores_of_threeLaws_of_encode_getElem_eq_uninit` | `Quot.sound`, `propext` | `7fc310c08f7796342c83a3d505a2da69cf012fef732e0060106f86ad2a38d2b2` | `15967a06779b05fb9ae926356d6557319d54376bb9d3e7151c1cc0d72b7b9318` (24) |
| R1e | `eq_of_encode_le_encode_of_decodeMono_decodeEncode` | none | `8d7c4ccae89b82d5255965a7c3085819907248347221d57871c6cb3e326684ea` | `547a3a9b153f30f55ab79ddc556801718d78bcca593f528907eb37aa989c15cd` (12) |
| R2a | `transmuteTotal_of_intoBytes_of_fromBytes` | `propext` | `b02108bcfb651f0def0df13ae10902020634a22e46cdaa0d592cccd9195ca7d6` | `5189d25e4d8092130ddd4e832fdc1a589267154f6eb7896676f826cd7951d7bb` (17) |
| R2b | `transmute_bab_roundtrip_of_total_of_intoBytes_encodeLeast_decodeEncode` | `propext` | `a227e32c01a3455f5c50e191c4b7657ad9ea595b3b77ce670e11125474048281` | `54c9ffae3cc5fb6f65abee8d3aa2415136ad8a8a04aedfa1170e9e31a08adb53` (25) |
| R3 | `transmute_comp_of_total_of_encodeLeast_of_intoBytes` | `propext` | `80359977e993d1a207eae6bbb5ee95f15fbc02764faed4f87c239dad44082fc1` | `ff40fa97817f2017117f474f96039e298e4f26497d719b7f07fcba58b0209710` (24) |
| R4a | `prodRep_decodeMono_of_fields` | `Classical.choice`, `Quot.sound`, `propext` | `fdf6378edee321d74717483ecf61394acb0ab49a80e18d5c515c7dee06e14aea` | `40fa3b57060f34b939d27af33c39128bb5ef24de894d990ba1b80bf782ec762b` (37) |
| R4b | `prodRep_decodeEncode_of_fields_of_disjoint` | `Classical.choice`, `Quot.sound`, `propext` | `80cbe2a57d523e5cb670d8f3ea5681537ca675852b3926fd352d62e9775fe90b` | `7378ee9d219016d7b6d0ab2ae0135a27b4621825a8439c15e3c1066f959743b5` (26) |
| R4c | `prodRep_encodeLeast_of_fields` | `Classical.choice`, `Quot.sound`, `propext` | `128368cf22c05ca44d355c3e29e585fc66003235ca6925368ed763747cb2d71a` | `220e754c85a31a94146403f9b97783ec78d788c5085ecacb6651c331f2757b00` (34) |
| R4d | `prodRep_intoBytes_of_fields_of_covering` | `Classical.choice`, `Quot.sound`, `propext` | `9138db307cab950c4401b249b824cdf1bd6a174f2ef5a4b5b79dada5387e7e03` | `71ee73bf888b71fd3f81e5b3dc70d000231716f5101794aadb7992bd96b488b5` (31) |
| R4e | `prodRep_fromBytes_of_fields` | `Classical.choice`, `Quot.sound`, `propext` | `183524a340a9f414ccdffbaa852f5a63b871e45748cf046c8045212adfee2e04` | `628892bc93f27879181bb0a757d055b653260c40b42c357c1e3bb8e1577270b2` (30) |
| R5a | `transmuteTotal_iff_image_subset_valid` | none | `ca89cd49861b12738efef0e1f2263e5ca502cecbbe3ef91f0547c65d9e4023c6` | `3912cd32b35bb8b4debe53799f16f33ddb715e58dbab605c01780b7d395f21e7` (8) |
| R5b | `transmuteTotal_iff_valid_subset_of_laws` | none | `4b3c25adffb1f3d55411c7b47876582d2dcc6b8e0b7803fb3d241a6833a95e27` | `6b07f6974d52602358cbb44949b2bf46253628dd9e6caf66b954ae471e37e175` (16) |
| R5c | `transmuteTotal_iff_initValid_subset_of_intoBytes_decodeEncode_encodeLeast` | `Classical.choice`, `Quot.sound`, `propext` | `de175473b02c799d355216164b31d8536da6726af83937d3992d5347bacfa11a` | `206bf326ff14b08f0d53320636168bbc318b50c3bf9207cfe1c86cbc3391c4eb` (28) |
| R6a | `int_ptr_int_roundtrip_of_decodeEncode` | `Quot.sound`, `propext` | `5be4837f6cb689eeb0628c3fce7985b8ca7f7b217aa83b2171c365bcbe48f85a` | `2643b18f76255f1c0d644721e8a9780b97d22a46a7bcddde5b21614262eed927` (14) |
| R6b | `ptr_intStrip_ptr_roundtrip_drops_provenance_of_decodeEncode` | `Classical.choice`, `Quot.sound`, `propext` | `9388bc96040d9a89f407f7d3e420d6f2a7521063c99594fd2454087692a0978f` | `3b0e7ac9fffc5867c2ed3723431fb5cb34a5db8bd1dcf5ef498d2043a0ac9bd3` (28) |
| R6c | `no_int_decoder_encodeLeast_fromBytes_of_provenance` | `Quot.sound`, `propext` | `6a31a995b404b665df5ca6945e8b5697bcafb85c49342031710e656387a987a5` | `0a38ffdb77e3fc86b1db321793d1f9cd68b6303b423c9387e553485a9a043d92` (25) |
| R6d | `no_optProvPtr_decoder_decodeMono_decodeEncode_of_provInc` | `Quot.sound`, `propext` | `39a657c53dcc3d37fb822ea896fa6a0c58975558c19efc22cd64803e155a9d60` | `65217d19956404d8a8691f3d3bff3a39bf8a290ddf12ab1f8ac823a399a742b0` (28) |
| R6e | `transmute_comp_fails_of_provInc` | `Classical.choice`, `Quot.sound`, `propext` | `0f7a7f176111b517c471beae42f5d5ca5f3b587eebb6e6950a2b5fb39a35cc5a` | `bec25d9b32998a34c979d619f36842d29fea2d2a8836cf04207466ad17dfcc05` (52) |

Non-vacuity witnesses, tightness counterexamples and positive controls referenced by the cards:

| theorem | role | axioms | statement_sha256 | closure_sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `decodeIgnores_of_encode_uninit_nonvacuous` | R1d2 non-vacuity | `Quot.sound`, `propext` | `a4823105254ef6ea86a4ae0a64a5ead4fe3746d067b316720144dc8cd857ce33` | `2719c326e600aec9e8e5794a85b16e5be7be9885ca12a42cc35b3729d975402d` (30) |
| `decodeIgnores_of_encode_uninit_tight_hDE` | R1d2 `hDE` counterexample | `Quot.sound`, `propext` | `8759e541d28ee20463d5ea91b954e68efb57cbf020b88115327f521029c5afe6` | `3a1e9f3bd081af4010eec6043a005bb952ef787475298a1fb2877271b25f0cd6` (36) |
| `decodeIgnores_of_encode_uninit_tight_hEL` | R1d2 `hEL` counterexample | `Quot.sound`, `propext` | `77a7341654b5c27718be00c037cd131879efc424917a03339a7b4e447d4eb0c8` | `49a6dc6391614900a28140229ea7ea488106d8f2f5acd12348fe7bb9660ef978` (37) |
| `decodeIgnores_of_encode_uninit_tight_hM` | R1d2 `hM` counterexample | `Quot.sound`, `propext` | `bcdbdaec51786725e49772271110a573b7a2803ae9d4fafa6c28b2d965569afe` | `80662a7df5385321f6d0889833bd725ba37946acc38255e83d4cae7a20b1d6f4` (26) |
| `decodeIgnores_of_encode_uninit_tight_hU` | R1d2 `hU` counterexample | `Quot.sound`, `propext` | `28d87a03b97958a265ee04e74d80c8f2593940b98c6f96630c317a5fe899837d` | `8d92e33c92c775a21546093db91d680e126ac5347797215c10661d10154400c3` (30) |
| `decode_eq_iff_threeLaws_nonvacuous` | R1c non-vacuity | `Quot.sound`, `propext` | `3ce378024e1cb148eb251997bba8c7776c8d5458a7ecf1d766bf95388a8c3cf3` | `801d975174ac9bf0ee15022d0aa54d0e8a97c8cf425e2661ec71c5d73cfb78ca` (31) |
| `decode_eq_iff_threeLaws_tight_hDE` | R1c `hDE` counterexample | `Quot.sound`, `propext` | `4c07e943ee0a387d915548c68632d2b03d68ccb954530a71e924be36c5cdb0dc` | `5e7699236bc81eb4e3ac43043619e46fff29a5986f8dfee7f26258a4b2cda9c7` (32) |
| `decode_eq_iff_threeLaws_tight_hEL` | R1c `hEL` counterexample | `Quot.sound`, `propext` | `8365c3b848656e11c9af612b344592fd7a0126dbe9fe8b1a9755b39c5c2ae563` | `ae86228665a9b3ab395a1fd74a7663bdb2dc2d5020cdc6a5d0097d271c1ea553` (32) |
| `decode_eq_iff_threeLaws_tight_hM` | R1c `hM` counterexample | `Quot.sound`, `propext` | `2368d356cd8706f7055c620eb5f8a5d9191b37336fdca8b5643f1a21d9a810c9` | `9a9d33bda7030d13a1fb8f0ae931d16b1034c9698c8f1786b9d3d2c2df1df019` (29) |
| `encode_eq_iff_decodeEncode_encodeLeast_nonvacuous` | R1b non-vacuity | `Quot.sound`, `propext` | `a89fa58865474d04d302d88810c08b5b1d416c825fbb266ec0e0bd91fc2e8f3b` | `be599f623e368d6b046501e4dbf719525213155b431c9dbda9453c75f65ee03c` (25) |
| `encode_eq_iff_decodeEncode_encodeLeast_tight_hDE` | R1b `hDE` counterexample | `Quot.sound`, `propext` | `1cb1886ae0f8777ef23b37826e1bdac552a533669be686577f738da6f89c571d` | `a9f56d33471bdfb58394d9b7edf08f028a193f50adcfbd1a55038f741dddded0` (26) |
| `encode_eq_iff_decodeEncode_encodeLeast_tight_hEL` | R1b `hEL` counterexample | `Quot.sound`, `propext` | `e14eb143fe389a70144f794871c751279e594c730ae0cc9b2faabee1651fd8ea` | `e7b189998681f0b3e8c286e89f8f58e9f02e9e82ebd25cc330f701feb6c81571` (26) |
| `encode_getElem_eq_uninit_of_decodeIgnores_nonvacuous` | R1d non-vacuity | `Quot.sound`, `propext` | `e1bea59e0a4288fd73b6e79e49e2bc30f081fecb72e57f370a7289059b343b25` | `67eabcae86f06c68cedceab5c527854b9fa5152c6c205edfa8cd81eb98bf1b1f` (26) |
| `encode_getElem_eq_uninit_of_decodeIgnores_tight_hDE` | R1d `hDE` counterexample | `Quot.sound`, `propext` | `55c5b19558b714040845867b507b9c70d4e1c4a1da0a6bb6556a76baf10b0849` | `d30552f1365dbb2069fb96cf779c55b92252d410a07ff9f2a0de8465d58714bd` (22) |
| `encode_getElem_eq_uninit_of_decodeIgnores_tight_hEL` | R1d `hEL` counterexample | `Quot.sound`, `propext` | `7e3ebe52adddc4f83d80dbbdb3a70d9d070aa58fab5ff443fa99c4127de28238` | `3bdff4bd7767df514b1fd35eb47e6b6590a1fac3edec374c70f2980a0d05c322` (19) |
| `encode_getElem_eq_uninit_of_decodeIgnores_tight_hIgn` | R1d `hIgn` counterexample | `Quot.sound`, `propext` | `0d8fa7c2d9c3eaef60a9ac244e8b274e1dfcab654cb9e713a8904538f6259118` | `0192997cd41229d5bd09ed0ca1d943d6c18738fd5f748b6f5abdb5040463d5b2` (26) |
| `eq_of_encode_le_encode_nonvacuous` | R1e non-vacuity | `Quot.sound`, `propext` | `7a1bcdc818c553223113a146bc238abc31f73e3eec06e7f4608acca874ba4177` | `f4abeff0e0655f5dc30a7d7ed0a1e003824bd7526bcaee6d603028d284f44796` (28) |
| `eq_of_encode_le_encode_tight_hDE` | R1e `hDE` counterexample | `Quot.sound`, `propext` | `8c436396cf8617c7c4d21668f256604fde2db5cc75f019c278295cf8e8c12d27` | `6d92602647caa810a49d6f91f34d9707cd79eb785ac174f0d32b28aace549eea` (28) |
| `eq_of_encode_le_encode_tight_hM` | R1e `hM` counterexample | `Quot.sound`, `propext` | `25e71417074f99e4330698bc74d1b3a658d230f8306dc7c6680303c44d9469b7` | `eb1d72d66c67aabdf49ae95fc802e75bc48b2adfa99ee9c8198746b43924fa0f` (24) |
| `int_ptr_int_roundtrip_nonvacuous` | R6a non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `5bf64de210694138ef66273d272af56847ebb16b16d760d8b499a964fbf16f89` | `dd5327449dd3349a502f47f52ecc5350e6ea73444bf18fe87e09c3473fda0d21` (31) |
| `int_ptr_int_roundtrip_tight_hDEi` | R6a `hDEi` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `8ddcbad274f26c45c4a908d1f2d30cebfe8c5c53c44ce7b5087b84cf3ea16d42` | `a929a2acbfc57aec6cfd9b9ef553328341ea327697107dcac85df96db18ae176` (31) |
| `int_ptr_int_roundtrip_tight_hDEp` | R6a `hDEp` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `f513dc7b2e7f86cf3ff7ce37f77e0ea23c62fbf34de080a491b6d6b2272d0189` | `c65cb5afb6cdc1248f753400e33f627dc10bfbb60002d40d0ed6b18144f7ed4a` (32) |
| `no_int_decoder_nonvacuous` | R6c non-vacuity | none | `1f92905fb8f0522480bf6ed854de1dba9030bacaa730fdce616842171ce5e1cf` | `40481544b25336cb1c4e1f8f5f615733465910867a14b68445ccc56c66409314` (1) |
| `no_int_decoder_positive_control` | R6c positive control | `Classical.choice`, `Quot.sound`, `propext` | `3938d3dd0321ef3fe6479b2b01b9ed586a903fe9d1ea055767ad8d1ca4335cdf` | `a11f8d1b3224a925e5a65556f68f3f43777831c83306acfbbb15d1896dd7f912` (43) |
| `no_int_decoder_tight_b0` | R6c `b0` counterexample | `Quot.sound`, `propext` | `7d283df165563a2d4e1a9bfc5ae786cbf0163c5e8fa9bea5f632a605fb047b05` | `0a38ffdb77e3fc86b1db321793d1f9cd68b6303b423c9387e553485a9a043d92` (25) |
| `no_int_decoder_tight_hn` | R6c `hn` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `30c46a25e984ebc1031b01c3c9a81f3b94be995c934d21d647109fd1eeb9fdcd` | `066a2a37b94a865cdb92a2c1225eacd48669cc95aa2dee784196f1aea0894de5` (26) |
| `no_int_decoder_tight_p0` | R6c `p0` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `10cf8a84556d92a16186762c838025fef6ef8ad5bcfea1fffca1960fca9f94e2` | `066a2a37b94a865cdb92a2c1225eacd48669cc95aa2dee784196f1aea0894de5` (26) |
| `no_ptr_decoder_nonvacuous` | R6d non-vacuity | none | `19d73201b3666b288d5c55ab45afa780140875b29e78b9f9c33f7df70d085a1d` | `40481544b25336cb1c4e1f8f5f615733465910867a14b68445ccc56c66409314` (1) |
| `no_ptr_decoder_positive_control` | R6d positive control | `Classical.choice`, `Quot.sound`, `propext` | `53b9036691b344b43a71c16b4205ad1b6a7fe92dfa772128b7a718a15c89feb2` | `e4b681f884d8ff81cd410d04e9d966f99de1881c2680f559e56d03f01706fb24` (63) |
| `no_ptr_decoder_tight_b0` | R6d `b0` counterexample | `Quot.sound`, `propext` | `4c44e59451eefd2fe6919ae5b005f8fd4a12c6b50c4be18909017c5200d679c0` | `65217d19956404d8a8691f3d3bff3a39bf8a290ddf12ab1f8ac823a399a742b0` (28) |
| `no_ptr_decoder_tight_p0` | R6d `p0` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `9127f5f224d7db4719b2ae1fada2c5741235d7810435c82d26b4dafc5d3b4af7` | `24626cd792749ad13c474e10972dc0e3f0b5a18fde93a42122054b864c2f933e` (29) |
| `prodRep_decodeEncode_tight_hD` | R4b `hD` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `a17e84b8fd213efdc9a0f5af703a640b23b0e5b86acbfa52d6dcef431b80c50a` | `301cc2fa37a0a49d42cc565353df13f663ccab2695707079ce43a760ffaa8d6b` (36) |
| `prodRep_decodeEncode_tight_hDE` | R4b `hDE` counterexample | `Quot.sound`, `propext` | `8fce2c92c7440a93130e307c851bd18d3539116fad3a415fa1c0d46f005028fa` | `ea71385960a0587499ba93273da880b6c8bbc1d4600e095d21b06fc6ec9d820b` (38) |
| `prodRep_decodeMono_tight_hM` | R4a `hM` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `ad0f4bfd8aceb3cfa273b3a942def9b60e59eb9077ef3ae0f58a29a89878d4d6` | `b90f8b3cf3b90f5b41654b167a96681961984950cf69e962fc3653d3677a05d3` (45) |
| `prodRep_encodeLeast_tight_hEL` | R4c `hEL` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `eb62b8d776cd0a5ac8a61ac86cab49387d52bf09325aac62121b5007c6bac451` | `031ac2a5c7cb8bbf73a7bc0c61e7615db9f5b93f787cc7f4a2454b5cc254b5f2` (44) |
| `prodRep_fromBytes_tight_hFB` | R4e `hFB` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `ca2940ea638a3a895a10f0cea486e5ee760721e3c73f76545081e87e5e26cafd` | `82e926b6b325c5fa76c1fa3d9f31e30642cb380102d6311f984af7189a75a2c0` (41) |
| `prodRep_intoBytes_nonvacuous` | R4d non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `5bb07b24a58e2be66cb79db980b317f17282993d21e3ff494231e1f749dbeef9` | `7797a779fd4f0caa2138f7b4f1641aff8131a509d87fd68a5fc964373607c7e3` (28) |
| `prodRep_intoBytes_tight_hC` | R4d `hC` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `311b553e39ac1727ffdf6021544a13c27a4c415aac541654ac0b345864ab33b4` | `ff52410a4005a77e192a3ff488c85aa3dd1c10f15c385495783f80d6a2391697` (39) |
| `prodRep_intoBytes_tight_hIB` | R4d `hIB` counterexample | `Classical.choice`, `Quot.sound`, `propext` | `c111e752420c6c979154c7d0760427c130378d3fccc98e08634a9a19aad6c709` | `d39470ef26f15b589c808a2db25cd7891d6d69b59994d83b66c4ed99e74b848d` (37) |
| `prodRep_laws_nonvacuous` | R4a non-vacuity; R4b non-vacuity; R4c non-vacuity; R4e non-vacuity | `Quot.sound`, `propext` | `34cfe0ef62dc6f66ebd4f088d8fd4f5d7ea9f03ba855b4dd16dec8d0d9b4a49b` | `358a9f58a3853032e5c97f672931ef2868a4c15dc95b4e4515845ad98ed533f0` (42) |
| `ptr_intStrip_ptr_roundtrip_nonvacuous` | R6b non-vacuity | `Classical.choice`, `Quot.sound`, `propext` | `f838ba71f9bf3561b6ecef6f75e0274426a125256fa411f5a9781d83eb7f17be` | `97a4da91060298b7b57cbe0557fbb571739ef945d7796512a0b2358cdc9e0794` (29) |
| `ptr_intStrip_ptr_roundtrip_tight_hDEp` | R6b `hDEp` counterexample | `Quot.sound`, `propext` | `c34f26701a8638f59de88a3c81d986db9205c09c1f51a463e7b4e96a6d42716b` | `89a5e713ee3ade9f1a09bc1368162427b60eb7df2ded040f0d7f49d04d694a47` (28) |
| `threeLaws_iff_lowerAdjoint_nonvacuous` | R1a non-vacuity | `Quot.sound`, `propext` | `d926e8d7121c7c34df01fc4d59a45048611cc5f413ba78e3596c4ed01ad08f10` | `7ee460c8f507f83f86869f13c65a4c24f07b63c818db1aba4ab285c5c391ad22` (32) |
| `transmuteTotal_iff_image_subset_valid_nonvacuous` | R5a non-vacuity | `Quot.sound`, `propext` | `d659deecc7047adbc27fd3fe7887c17dbeb2b75bf5a96be4456e33001dab95e2` | `3b991f491e382fb42ca0db0d5e29b31a7c78f8929765c49c49a4e0deb3c693a2` (23) |
| `transmuteTotal_iff_initValid_subset_nonvacuous` | R5c non-vacuity | `Quot.sound`, `propext` | `0b07eac7ad9b2ec5b697b8b61c69ead91b9b47da2d2141c5817f903b785187b0` | `68b6196b14dcc55d1bcc862f2684b098a319e390d28542e1985dad5bf0fced25` (31) |
| `transmuteTotal_iff_initValid_subset_tight_hDE_A` | R5c `hDE_A` counterexample | `Quot.sound`, `propext` | `d0807bdaf42a17ac9957c8f631c1a0c4d33459f57be6e1676c679c19f801d9d4` | `940ea91892a3c13fdf30c80be39080cf1d6ee7ed4617d18b11ff42d77362f66f` (34) |
| `transmuteTotal_iff_initValid_subset_tight_hEL_A` | R5c `hEL_A` counterexample | `Quot.sound`, `propext` | `013301f2e683036d406e21637a7559165e93d3fcda2f69b36c7d6c4cb6b1b443` | `7293e07d3c5bd338e9edcede5cd2e8fe9bcf03c9a1298e9920c6066d95f1c822` (29) |
| `transmuteTotal_iff_initValid_subset_tight_hIB_A` | R5c `hIB_A` counterexample | `Quot.sound`, `propext` | `a62109874a79c0ea49a0519473f0c2b764906e7cad3b37d6e431b4b535e62560` | `ef0637f28c1859aa8fc5d237ddad9c1fec4c8777d617871e21d93c58644de9b7` (36) |
| `transmuteTotal_iff_valid_subset_nonvacuous` | R5b non-vacuity | `Quot.sound`, `propext` | `75085ab81121c0674b488d4c2aa9ec25266977a1f446542c6b4feeaa32a5081b` | `696da82e7686410eef4066926f207ef1a81ad8b9421cde565c4cb7ca581bd702` (35) |
| `transmuteTotal_iff_valid_subset_tight_hDE_A` | R5b `hDE_A` counterexample | `Quot.sound`, `propext` | `e5a433bb6c9c279c7001a02b8745949ccff12c371a46e644d3705102450ac4d7` | `b6514c34037ec44f6bebc68ebb61fa687687cd371ad58c249d14e18cf4267adb` (32) |
| `transmuteTotal_iff_valid_subset_tight_hEL_A` | R5b `hEL_A` counterexample | `Quot.sound`, `propext` | `af80763c09d8bc34f0a7e7726113e39d04e031bfa0b1e4c4b2f0f0b79fdb7a34` | `520acc172344dd459b46b4bc0cd9d754964a1d3dc0e744fe68400bbb51b4aba7` (34) |
| `transmuteTotal_iff_valid_subset_tight_hM_B` | R5b `hM_B` counterexample | `Quot.sound`, `propext` | `716d816f60cc438af0b6f8fb796cd3b8cc0b2bcb41615822cc181eeb226e9890` | `cac4a693cb8c91cab70421bbb3ffb70c27bc1e4235a03735776fd9ee61da52dc` (28) |
| `transmuteTotal_of_intoBytes_of_fromBytes_nonvacuous` | R2a non-vacuity | `Quot.sound`, `propext` | `ea61d14b6c5c370ff88c9dec1d38658907dc018c44dfc070b72fe598a055897e` | `213e91fa66190feec99518016223494d3e6422d07414ea2f0628e9f0c8c364e2` (27) |
| `transmuteTotal_of_intoBytes_of_fromBytes_tight_hA` | R2a `hA` counterexample | `Quot.sound`, `propext` | `3b24410581ba9a2f4b0c52f1c74c3e296446e7e96981b42b96dc08e2ce792cf4` | `e8e3448dbec02bf11cc5f00e2605f449b6e45b98e2e49789d4def60fd103d73f` (24) |
| `transmuteTotal_of_intoBytes_of_fromBytes_tight_hB` | R2a `hB` counterexample | `Quot.sound`, `propext` | `e92995bd821d25bb9d14410709e1a56baef5d904d6bc3426f61123b99c4a08ac` | `e1a9557b85a1e7fe2d3d9447d8ac863527154f483158d5fedd7b1997e609286d` (25) |
| `transmute_comp_nonvacuous` | R3 non-vacuity | `Quot.sound`, `propext` | `8234456794bba94923ce5bff184a49d9e9203c41c44fcc8a3a63294ba015fb20` | `01b413d496c3896f5bdb65f4fe64d32adfdacda6a26657447ce845817aa10ede` (33) |
| `transmute_comp_tight_hEL` | R3 `hEL` counterexample | `Quot.sound`, `propext` | `2eda8288e2c616aae7bb6c5baf933ca0a760641340401f22a6b9f9a8fdd4d1e3` | `829376023ebfc48c1a4c05c4600f1efb659885d57592ba8c200b1ad5da028fce` (24) |
| `transmute_comp_tight_hIB` | R3 `hIB` counterexample | `Quot.sound`, `propext` | `50a9f256b34ef806da64bd2eb02ff7ef3ff1903c20c177776658bcdd4ba1ca3b` | `a79ef1a7cc7cca9ea85f3d159a6551bfe06abc3061c2b3aef58e887ec67bd435` (32) |
| `transmute_comp_tight_htot` | R3 `htot` counterexample | `Quot.sound`, `propext` | `62b1a3691507e881d8ed28b08452ee84557509ca05a4f191b842074b84c1d751` | `4ec1fefdbc470d53d4125d8a6764ac8228b81ad72dbacdb453fef885abf30258` (32) |
| `transmute_roundtrip_nonvacuous` | R2b non-vacuity | `Quot.sound`, `propext` | `3f554f0ef9358ca485715e5c23a44e874073b83a047b1f79436500e1fc1c9948` | `b519ac53f5a451178fea9e89ce28a5e60ff4bbb0b37429fe5a807d662be1775a` (35) |
| `transmute_roundtrip_tight_hDE_B` | R2b `hDE_B` counterexample | `Quot.sound`, `propext` | `6a2f180794c912e21a9cd4f073722fa46ead69e70c67928b79f8cf7b85a6be90` | `051d95fc65a01b92dfd703592845692f6c31c6358895b21253292c061299a247` (31) |
| `transmute_roundtrip_tight_hEL_A` | R2b `hEL_A` counterexample | `Quot.sound`, `propext` | `11cbd1658662488d6ecaf4b7cfb13d415753a207067fbc2d90e0652158618005` | `5d638bd5186806702e8ad934c8df23868872c3692654552cb9a376b82b2d6a2d` (38) |
| `transmute_roundtrip_tight_hIB_A` | R2b `hIB_A` counterexample | `Quot.sound`, `propext` | `2120db86a194ed91b70e845c9ca241cff0eb71ae1727ddc634cb86b7ce56e312` | `7eb6ea2fa27ac40597637eea754de94e762b5bd971ae656b25be91c9df9969c3` (33) |
| `transmute_roundtrip_tight_htot` | R2b `htot` counterexample | `Quot.sound`, `propext` | `61eb44b1c8163992cc9a5d5b645b5faebbf19454de429f72e3ce2a90ae638283` | `bd5aa86d2273c01f4aa51bf60a724cda8684f66f50cf2b55a09dc96ecff9c4b1` (33) |

Supporting theorems cited in the definitions, the R1a card, the non-claims and the escape hatches (axioms only; not hashed):

| theorem | axioms |
| :--- | :--- |
| `Rep.lowerAdjoint_iff_galois_liftEncode` | `Quot.sound`, `propext` |
| `Rep.encode_injective_of_decodeEncode` | none |
| `no_lawful_encoder_for_monotone_orUnitRep` | `Quot.sound`, `propext` |
| `no_lawful_decoder_for_conflictBoolEnc` | `Quot.sound`, `propext` |
| `decodeIgnores_of_empty` | `propext` |
| `transmute_roundtrip_second_step_not_injective` | `Quot.sound`, `propext` |
| `transmute_roundtrip_second_step_not_injective_of_not_decodeEncode` | `Quot.sound`, `propext` |
| `transmute_injective_of_bab_hyps_of_decodeEncode_of_encodeLeast` | `propext` |
| `pairRep_decodeMono` | `Quot.sound`, `propext` |
| `no_ptr_decodeEncode_size_zero` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_escape_hatch` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_decodeMono` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_decodeEncode` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_encodeLeast` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_fromBytes` | `Classical.choice`, `Quot.sound`, `propext` |
| `provIntRep_intoBytes` | `Quot.sound`, `propext` |
| `no_singleProvInt_decoder_encodeLeast_fromBytes_of_two_le` | `Classical.choice`, `Quot.sound`, `propext` |
| `reqProvPtrRepInc_threeLaws` | `Classical.choice`, `Quot.sound`, `propext` |
| `ptrDegradeRepInc_lawful_by_ptrValLe` | `Classical.choice`, `Quot.sound`, `propext` |
| `ptrStrictRepInc_not_decodeMonoBy_ptrValLe` | `Classical.choice`, `Quot.sound`, `propext` |
| `ex_ptrDecodeStrict_accepts_duplicated_byte` | `Classical.choice`, `Quot.sound`, `propext` |
| `transmute_ptr_intStrict_eq_none` | `Classical.choice`, `Quot.sound`, `propext` |

All 557 declarations of the library depend only on subsets of `propext`, `Classical.choice`, `Quot.sound` (`audit/axioms.json`).

Primary sources (exact records; these are the sources the prior-art entries and modeling bridges rely on):

- MiniRust, `spec/lang/representation.md`, repository `minirust/minirust`, commit `063d784186d3252bee242217f218223205c0b568`: integer encode/decode (L74-94), pointer encode/decode (L102-142), tuple encode/decode and padding (L249-281), abstract-byte and value orders (L649-746), generic properties (L754-766); https://github.com/minirust/minirust/blob/063d784186d3252bee242217f218223205c0b568/spec/lang/representation.md
- Rust Unsafe Code Guidelines Reference, `reference/src/glossary.md`, repository `rust-lang/unsafe-code-guidelines`, commit `d809f91e62968913d808e53397fbcf7cea762cce`: abstract bytes (L26-40), padding (L168-184), representation relation (L246-249), validity invariant (L280-312).
- zerocopy 0.8.63 documentation (docs.rs): `FromBytes`, `IntoBytes`, `TryFromBytes` traits and `derive(FromBytes)`, `derive(IntoBytes)`; https://docs.rs/zerocopy/0.8.63/zerocopy/
- rust-lang/rust commit `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`: `library/core/src/mem/transmutability.rs` (`TransmuteFrom`, union-transmutes, `Assume`) and `compiler/rustc_transmute/src` (`layout/mod.rs`, `maybe_transmutable/mod.rs`).
- Rust core 1.100.0 documentation: `core::mem::transmute` (section "Transmutation between pointers and integers") and `core::ptr::without_provenance`; https://doc.rust-lang.org/1.100.0/core/mem/fn.transmute.html
- O. Ore, "Galois connexions", Transactions of the American Mathematical Society 55, pp. 493-513, 1944, doi:10.1090/S0002-9947-1944-0010555-7.
- P. Cousot and R. Cousot, "Systematic design of program analysis frameworks", POPL 1979, pp. 269-282, doi:10.1145/567752.567778.
- H. Tuch, G. Klein, M. Norrish, "Types, bytes, and separation logic", POPL 2007, pp. 97-108, doi:10.1145/1190216.1190234.
- K. Memarian, V. B. F. Gomes, B. Davis, S. Kell, A. Richardson, R. N. M. Watson, P. Sewell, "Exploring C semantics and pointer provenance", Proc. ACM Program. Lang. 3 (POPL), Article 67, 2019, doi:10.1145/3290380.
- J. Lee, C.-K. Hur, R. Jung, Z. Liu, J. Regehr, N. P. Lopes, "Reconciling high-level optimizations and low-level code in LLVM", Proc. ACM Program. Lang. 2 (OOPSLA), Article 125, 2018, doi:10.1145/3276495.
- J. Kang, C.-K. Hur, W. Mansky, D. Garbuzov, S. Zdancewic, V. Vafeiadis, "A formal C memory model supporting integer-pointer casts", PLDI 2015, pp. 326-335, doi:10.1145/2737924.2738005.
- CompCert, `common/Memdata.v`, repository `AbsInt/CompCert`, commit `2685140bf72c959446981fb99b5e44a8975021bc`.
- Mathlib, `Mathlib/Order/GaloisConnection/Defs.lean`, `Basic.lean`, `Mathlib/Order/Bounds/Basic.lean`, repository `leanprover-community/mathlib4`, commit `f5d65c00d8545e4d082536ede4239761af2eea2a` (cited as mechanized prior art only; not a dependency).
- Context only (open, unmerged): AeneasVerif/aeneas pull request 1447 (head `2a1dd75567517e078f90b1df746af7373fe24cbc`) and pull request 1497 (head `d17ca83fc07d712d1785f650840cb2073c259e69`) with review comment https://github.com/AeneasVerif/aeneas/pull/1497#discussion_r4494829173.

The line ranges and quotations in the prior-art entries refer to the recorded revisions; the DOIs, venues and page ranges were checked against public bibliographic records (2026-11-20).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects `sorry`/`admit`/`native_decide`/`axiom` in the Lean sources, generates and runs a small Lean program that computes `collectAxioms` for every library declaration (failing on any axiom other than `propext`, `Classical.choice`, `Quot.sound`), and recomputes, for every Lean name referenced by `results.json` and every name in `audit/statements.json`, the SHA-256 of the `repr` of its type and of its definition closure (the sorted, newline-joined `name : repr(type)` lines, with ` := repr(value)` for non-theorems, of every package-local constant reachable from the type; theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` on success.

A manual axiom audit without Python:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean   # prints '#print axioms' for every card-referenced theorem
```

`lean/RevalidationAudit.lean` is outside the library target. Each printed line must read `'<name>' depends on axioms: [...]` with a subset of `propext`, `Classical.choice`, `Quot.sound` (or `does not depend on any axioms`); this manual check covers axioms only. A passing `revalidate.py` run re-establishes the kernel checks and the statement identities only; the modeling-bridge claims are re-checked by re-reading the cited sources at the recorded revisions.
