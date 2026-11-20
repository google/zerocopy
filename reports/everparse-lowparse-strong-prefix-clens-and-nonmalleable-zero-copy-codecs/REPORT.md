# Strong-Prefix Zero-Copy Parsers, Conditional Lenses, and Non-Malleable Binary Codecs across EverParse/LowParse, Narcissus, zerocopy, and Anneal

## Summary

Proving only round-trip correctness (`parse (serialize x) == Some (x, len)`) leaves binary decoders vulnerable to **malleability** (multiple byte sequences decoding to the same value `x`), **lookahead framing failures** (prefix parsers peeking beyond their consumed slice), and **trailing-byte smuggling**. Project Everest's **EverParse / LowParse** (`project-everest/everparse` at `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`) rules out all three via a `parser_kind` algebra built on two independent laws—**`no_lookahead`** (`ParserStrong`, giving slice-extension invariance `parse_strong_prefix`) and **`injective`** (distinct prefixes never map to equal values)—plus **`consumes_all`** (`ParserConsumesAll`). Together they imply **`serializer_correct_implies_complete`**: every injective parser paired with a right-inverse serializer automatically satisfies `serializer_complete`, guaranteeing every accepted byte prefix equals `serialize x` (`LowParse.Spec.Base.fst:L78–100`).

To read or update validated wire buffers in place without copying, LowParse uses **conditional lenses (`LowParse.CLens`)** paired in Pulse with zero-copy slice **accessors** returning linear separation-logic **`Trade.trade`** views (`LowParse.PulseParse.Base.fst:L749–777`). Conversely, MIT's **Narcissus** (`mit-plv/fiat` at `77f43f5d5408b3543f8dd01d4d43f4c4c70f1213`) models formats relationally (`FormatM := S -> CacheFormat -> Comp (T * CacheFormat)`, `Specs.v:L20–68`), trading canonical uniqueness for one-to-many legacy encodings.

Mapped to Rust (`google/zerocopy` at `ec133ce4d7993775413d852f91c9e3eb2a2a0897`) and **Anneal** (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, Lean `v4.34.1`):
- `T: zerocopy::FromBytes + IntoBytes + Immutable` induces a `total_constant_size_parser_kind (size_of::<T>())` bijection (`read_from_prefix` as `ParserStrong`; `read_from_bytes` as `ParserConsumesAll`), whereas `FromBytes` *without* `IntoBytes` (struct padding or unconstrained bitfields) violates `injective`.
- The `ParserStrong` + `serializer_complete` + `CLens` algebra mechanizes outside Anneal's TCB inside the 51-module `Init.*` foundation ceiling and closed pure-tactic allowlist (`TrustedBoundary.lean:L442–596`), while end-to-end Rust `&[u8]` slice entry points depend on extending `Trusted.MirSemantics` beyond empty caller memory and scalar-only locals (`MirSemantics.lean:L803, L1686–1694`).

## Applicability

This report synthesizes five directly inspected repositories, three peer-reviewed primary papers, and one finite execution environment:

1. **EverParse / LowParse** (`project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`): `LowParse.Spec.Base.{fsti,fst}`, `LowParse.Spec.Combinators.{fsti,fst}`, `LowParse.Spec.BCVLI.fst`, `LowParse.BitFields.fsti`, `LowParse.CLens.fst`, `LowParse.Pulse.Base.fst`, `LowParse.PulseParse.Base.fst`, `LowParse.PulseParse.Combinators.fst`, `LowParse.PulseParse.BCVLI.fst`, and `EverParse3d.Actions.Base.fsti`, paired with Ramananandro et al. (USENIX Security 2019) and Swamy et al. (PLDI 2022, DOI `10.1145/3519939.3523708`).
2. **MIT Narcissus** (`mit-plv/fiat@77f43f5d5408b3543f8dd01d4d43f4c4c70f1213`, cross-checked against `df1565d187de242fdf822111a23e3f6b71049c9c`): `src/Narcissus/Common/{Specs,ComposeIf}.v`, paired with Delaware et al. (ICFP 2019, DOI `10.1145/3341686`).
3. **`zerocopy`** (`google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`): `zerocopy/src/lib.rs` (`TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Immutable`, `ProjectField`, `read_from_bytes`, `read_from_prefix`) and `zerocopy/src/ref.rs` (`Ref`).
4. **Anneal & Lean 4** (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`): `trusted/audit/TrustedBoundary.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `theory/Anneal/PureLift/{Lens,SpatialPin,MirBridge}.lean`. Non-TCB `theory/` modules must open with `prelude`, import only the 51 locked `Init.*` modules plus `Trusted.*` and `Anneal.*`, omit general recursion (`._unsafe_rec`) and banned tactics (`omega`, `ring`, `linarith`, `norm_num`, `bv_decide`, `native_decide`, `decide!`, `grind`, `sorry`), depend only on `{propext, Quot.sound, Classical.choice}`, and satisfy Statement-Origin Separation against `Trusted.MirSemantics`.

**Corpus relationship:** Companion reports `zerocopy-byte-apis-cross-target-layout-and-packet-certificates` and `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics` cover `zerocopy`'s Rust layout invariants; `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` provides a broad parser overview; and `verified-amir-binary-wire-format-llbc-decoding-and-parser-admission` addresses compiler-IR deserialization. This package captures the exact `ParserStrong`/`injective`/`CLens` predicate lattice, non-malleability theorem, `Narcissus` comparison, and Lean 4 `theory/` transfer.

## Findings

### 1. `LowParse.Spec.Base` Predicate Lattice, `ParserStrong`, and Non-Malleability

Basis: normative (Ramananandro et al., USENIX Security 2019) + source (`everparse@f3e4ce51...`, `LowParse.Spec.Base.{fsti,fst}`, `LowParse.Spec.Combinators.fst`) + execution (`Probe 1`)

In `LowParse.Spec.Base.fsti:L23–33`, a specification parser consumes a bounded prefix of F\* `bytes` (`Seq.seq U8.t`):

```fstar
let consumed_length (b: bytes) : Tot Type = (n: nat { n <= Seq.length b } )
let bare_parser (t:Type) : Tot Type = (b: bytes) -> GTot (option (t & consumed_length b))
```

LowParse qualifies `bare_parser` with a 5-field `parser_kind'` contract (`LowParse.Spec.Base.fsti:L277–340`):
1. **Length bounds (`parser_kind_low`, `parser_kind_high`)**: `parses_at_least lo p` and `parses_at_most hi p` (`L197–248`, with `lo <= hi`; `1 <= lo` is required for list element parsers to ensure termination, `L230–237`).
2. **Subkind framing (`ParserStrong | ParserConsumesAll`)** (`L117–193, L277–287`):
   - `ParserStrong` means **`no_lookahead p`**: if `parse p b1 = Some (v, n)`, `n <= Seq.length b2`, and `Seq.slice b1 0 n == Seq.slice b2 0 n`, then `parse p b2 == Some (v, n)` (`parse_strong_prefix`, `LowParse.Spec.Base.fst:L53–76`).
   - `ParserConsumesAll` means **`consumes_all p`**: whenever `parse p b = Some (_, n)`, `n == Seq.length b` (`L186–193`).
3. **Injectivity (`parser_kind_injective : bool`)** (`L46–103`): If `parse p b1 = Some (v1, n1)`, `parse p b2 = Some (v2, n2)`, and `v1 == v2`, then `n1 == n2` and `Seq.slice b1 0 n1 == Seq.slice b2 0 n2`.
4. **Metadata (`parser_kind_metadata`)**: `Some ParserKindMetadataTotal` (total constant-size parsers failing iff `Seq.length s < lo`, `L269–275, L331`) or `Some ParserKindMetadataFail` (`L325–332`).

Three algebraic theorems in `LowParse.Spec.Base` follow directly from these primitives:
- **Non-Malleability (`serializer_correct_implies_complete`, `LowParse.Spec.Base.fst:L78–100`)**: A `bare_serializer t := t -> GTot bytes` satisfies `serializer_correct p f` when `∀ x, parse p (f x) == Some (x, Seq.length (f x))` (`L715–721`) and `serializer_complete p f` when `∀ s, Some? (parse p s) ==> f x == Seq.slice s 0 len` (`L753–763`). Under `k.parser_kind_injective == true /\ serializer_correct p f`, instantiating `injective p` on `f x` and `s` immediately forces `f x == Seq.slice s 0 len`.
- **Canonical Uniqueness (`serializer_unique`, `serializer_parser_unique`, `serialize_strong_prefix`)** (`Spec.Base.fsti:L938–1117`): Any two serializers for an injective parser agree pointwise (`L938–950`); any two **`ParserStrong` and `injective`** parsers sharing a correct serializer `s` are extensionally equal (`p1 x == p2 x`, `L999–1023`); and under `ParserStrong`, `serialize s x1 ++ q1 == serialize s x2 ++ q2` implies `x1 == x2 /\ q1 == q2` (`L1065–1080`), while strict truncation always fails (`parse_truncate`, `L1097–1117`).
- **Logical Independence of `Injective` vs. `ParserStrong`**: `serializer_correct_implies_complete` requires `injective` (not `ParserStrong`), whereas sequential `and_then` (`LowParse.Spec.Combinators.fst:L10–50`) requires `ParserStrong` on the prefix parser so parsing `p1` cannot inspect bytes reserved for `p2 v`. Conversely, `parse_ret c` is `ParserStrong` yet non-injective on non-singleton types; and in `Probe 1`, `p_greedy` (`[0x01, 0x01, ...] -> (2, 2)`, `[0x01]` at EOF `-> (1, 1)`) passes exhaustive `injective` and `serializer_correct` verification across all 121 ternary buffers of length $\le 4$, yet fails `no_lookahead` (`p_greedy([0x01]) = (1, 1)` vs `p_greedy([0x01, 0x01]) = (2, 2)`).
- **Normalizer Scaling in `glb` (`LowParse.Spec.Base.fsti:L505–558`)**: `L514–522` documents that accessing `k1.parser_kind_*` seven times causes F\*'s normalizer to re-evaluate unreduced scrutinees once per stuck projection, producing exponential blowup across $N$-variant enum chains (`glb_list_of`). Destructuring `k1` and `k2` once via `match k1 with | Mkparser_kind' ... -> ...` keeps kind joins linear.

---

### 2. Contrast with MIT `Narcissus` Relational Formats

Basis: normative (Delaware et al., ICFP 2019 `10.1145/3341686`) + source (`mit-plv/fiat@77f43f5d...`, `src/Narcissus/Common/{Specs,ComposeIf}.v`) + derived

`Narcissus` (`Specs.v:L20–68`) models a format as a **nondeterministic computation** returning valid byte representations under an explicit encoder/decoder cache invariant (`Equiv env env' /\ decode_inv env'`):

```coq
Definition FormatM : Type := S -> CacheFormat -> Comp (T * CacheFormat).
```

| Dimension | `LowParse` (`everparse@f3e4ce51`) | `Narcissus` (`fiat@77f43f5d`) | Rust / Anneal Implication |
| :--- | :--- | :--- | :--- |
| **Format Model** | Deterministic `t -> GTot bytes` with `serializer_correct` (`Spec.Base.fsti:L710–721`). | Relational `S -> CacheFormat -> Comp (T * CacheFormat)` (`Specs.v:L20–68`). | `LowParse` fixes one canonical wire encoding; `Narcissus` permits encoding sets. |
| **Non-Malleability** | `k.parser_kind_injective == true` + `serializer_correct_implies_complete` (`Spec.Base.fst:L78–100`). | **Permits one-to-many encodings** (`composeIf` / `Union_Format` in `ComposeIf.v:L7–100`, e.g., optional DNS compression or don't-care bits). | Signed/authenticated headers require `LowParse` injectivity; permissive decoders use `Narcissus` `CorrectDecoder`. |
| **Prefix Framing** | `no_lookahead` (`ParserStrong`) vs `consumes_all` (`ParserConsumesAll`). | Baked into `CorrectDecoder` via `mappend t ext` (`Specs.v:L55, L66`) plus strict `decode_strict` (`L304–313`). | Maps to `zerocopy::FromBytes` `read_from_prefix` vs `read_from_bytes`. |
| **Statefulness** | Stateless forward slice slicing via `and_then`. | Dual `CacheFormat` / `CacheDecode` (`Specs.v:L50–68`). | `CacheDecode` handles backward DNS pointers outside `LowParse`'s forward model (`Spec.Base.fsti:L15–16`). |

Derived link: specializing a `Narcissus` `FormatM` to a singleton deterministic relation (`view := eq`) reduces the second clause of `CorrectDecoder` (`Specs.v:L59–68`) to `serializer_complete`.

---

### 3. Four Wire-Format Vulnerability Classes Neutralized by `ParserStrong` + `Injective` + `ConsumesAll`

Basis: source (`everparse@f3e4ce51`: `LowParse.Spec.BCVLI.fst`, `LowParse.PulseParse.BCVLI.fst`, `LowParse.BitFields.fsti`, `EverParse3d.Actions.Base.fsti`; `zerocopy@ec133ce4`: `zerocopy/src/lib.rs`) + execution (`Probe 1`) + derived

1. **Overlong Variable-Length Integers (`LowParse.Spec.BCVLI.fst:L8–101`, `LowParse.PulseParse.BCVLI.fst:L23–85`)**:
   Compact varints encode `x <= 252` in 1 byte, `253 <= x <= 65535` with tag `253` + 2 LE bytes, and `x >= 65536` with tag `254` + 4 LE bytes. `parse_bcvli_payload` (`L17–21`) adds `parse_filter (fun x -> U32.v x >= 253)` and `U32.v x >= 65536`, and `parse_bcvli_payload_and_then_cases_injective` (`L25–31`) proves arm disjointness so `serialize_bcvli` (`L100`) is complete. `Probe 1` confirms canonical BCVLI rejects `b"\xfd\xfc\x00"` (overlong `252`) and `b"\xfe\xff\xff\x00\x00"` (overlong `65535`) while unfiltered decoding accepts both.
2. **Dirty Bitfields and Struct Padding (`LowParse.BitFields.fsti:L4–204`, `zerocopy/src/lib.rs:L4358–4430, L6005–6085`)**:
   `LowParse.BitFields.fsti` partitions integers into LSB-first slices (`get_bitfield_partition_3`, `L188–204`). Ignoring reserved bits (`Probe 1`: `0b01_1111_10` vs `0b01_0000_10`) breaks `injective`. In `zerocopy`, `T: FromBytes` (`lib.rs:L4358`) permits inter-field/trailing padding (`#[repr(C)] struct Padded { a: u8, b: u16 }`), so distinct padding bytes decode to equal Rust structs, breaking parser injectivity. Requiring **`T: FromBytes + IntoBytes + Immutable`** (`lib.rs:L6005–6085`) guarantees zero padding and no interior mutability, inducing a `total_constant_size_parser_kind (size_of::<T>())` bijection whose inverse is `as_bytes` (`L6065`).
3. **Trailing Unauthenticated Bytes**: `zerocopy::FromBytes::read_from_prefix` (`lib.rs:L5569–5584`) implements **`ParserStrong`** (`(Self, &[u8])`), whereas `FromBytes::read_from_bytes` (`L5511–5526`) and `Narcissus` `decode_strict` (`Specs.v:L304–313`) implement **`ParserConsumesAll`**, rejecting unauthenticated trailing bytes at message boundaries.
4. **Double-Fetch TOCTOU (`EverParse3d.Actions.Base.fsti:L42–240`, PLDI 2022 `10.1145/3519939.3523708`)**:
   `validate_with_action_no_read` (`allow_reading = true`) vs `validate_with_action_read` (`allow_reading = false`, `L75–90`) plus single-pass `leaf_reader` prevent re-reading concurrent DMA/shared memory after tag/length validation, mirroring `zerocopy::Immutable` on `as_bytes` (`lib.rs:L6067`).

---

### 4. Zero-Copy Sub-Slice Projection via `LowParse.CLens`, Pulse `accessor`, and `Trade.trade`

Basis: source (`everparse@f3e4ce51`: `LowParse.CLens.fst`, `LowParse.PulseParse.{Base,Combinators}.fst`; `zerocopy@ec133ce4`: `zerocopy/src/lib.rs`; `joshlf/anneal@c131b320`: `theory/Anneal/PureLift/{Lens,SpatialPin}.lean`) + derived

To navigate inside validated packet slices in place, `LowParse.CLens.fst:L5–225` defines conditional projections:

```fstar
type clens (t1: Type) (t2: Type) = {
  clens_cond: t1 -> GTot prop;
  clens_get: (x1: t1) -> Ghost t2 (requires (clens_cond x1)) (ensures (fun _ -> True));
}
```

1. **Conditional vs. Strong Composition (`LowParse.CLens.fst:L173–225`)**: Tagged unions (`clens_tagged_union_payload`, `PulseParse.Combinators.fst:L1468–1477`) and dependent pairs (`clens_dtuple2_snd`, `L1557–1566`) guard projections with `tag_of_data d == t` or `dfst d == x1`. `clens_compose` (`L183–203`) conjoins conditions, while `clens_compose_strong` (`L205–224`) drops the inner guard when implied by `l12.clens_cond`. Notice `clens_put` and `clens_disjoint` (`CLens.fst:L8–171`) are commented out; Pulse replaces functional updates with separation-logic **`Trade.trade`** closures.
2. **Injectivity Unlocks Full Permission (`pts_to_parsed_intro_injective`, `LowParse.PulseParse.Base.fst:L34–93`)**: Introducing `pts_to_parsed p input #pm v` from `S.pts_to input #pm w` halves permission to `pm /. 2.0R` for non-injective parsers (`L34–61`) because recovering `w` requires keeping a half-permission witness inside the trade, whereas **`k.parser_kind_injective == true` retains full `pm` permission** with an `#emp` trade frame via `parse_injective` (`L63–93`).
3. **Sub-Slice `accessor` (`LowParse.PulseParse.Base.fst:L751–777`, `Combinators.fst:L1481–1590`)**: An `accessor p1 p2 cl` accepts `pts_to_parsed p1 input #pm v ** pure (cl.clens_cond v)` and returns sub-slice `result : slice byte` with `pts_to_parsed p2 result #pm' (cl.clens_get v)` plus `Trade.trade` back to the outer slice.
4. **Rust / `zerocopy` & `PureLift` Analogue**: `zerocopy::ProjectField` (`lib.rs:L1419–1510`) likewise distinguishes infallible struct/union projections (`Error = Infallible`, `L1471–1480`) from tag-conditional enum projections (`is_projectable` returning `Result<(), Self::Error>` under `ValidityKind::AsInitialized | ValidityKind::Safe`, `L1495`). In Anneal, `PureLift.Lens` (`Lens.lean:L112–141`) models partiality with `Option`, while `SpatialPin` (`SpatialPin.lean:L75, L187`) tracks `activeSubSplits` as a scalar counter not yet generalized to slice sub-range splitting.

---

### 5. Transfer to 3-Axiom Lean 4 (`v4.34.1`) `theory/` and Seven-Dimension Evaluation

Basis: source (`joshlf/anneal@c131b320...`: `TrustedBoundary.lean`, `Trusted/MirSemantics.lean`, `PureLift/{Lens,SpatialPin,MirBridge}.lean`) + derived

The core LowParse specification algebra fits cleanly inside Anneal's non-TCB `theory/` envelope (`prelude` + `Init.*`, zero `omega`/`bv_decide`/`native_decide`/`sorry`/`._unsafe_rec`, three axioms `{propext, Quot.sound, Classical.choice}`):

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.Format

abbrev Bytes := List UInt8

structure ParseOut (α : Type) where
  val      : α
  consumed : Nat

abbrev BareParser (α : Type) := Bytes → Option (ParseOut α)
abbrev BareSerializer (α : Type) := α → Bytes

def slicePrefix (bs : Bytes) (n : Nat) : Bytes :=
  bs.take n

def NoLookahead {α : Type} (p : BareParser α) : Prop :=
  ∀ b1 b2 out,
    p b1 = some out →
    out.consumed ≤ b2.length →
    slicePrefix b1 out.consumed = slicePrefix b2 out.consumed →
    p b2 = some out

def Injective {α : Type} (p : BareParser α) : Prop :=
  ∀ b1 b2 o1 o2,
    p b1 = some o1 →
    p b2 = some o2 →
    o1.val = o2.val →
    o1.consumed = o2.consumed ∧
      slicePrefix b1 o1.consumed = slicePrefix b2 o2.consumed

structure StrongParser (α : Type) where
  parse     : BareParser α
  bounded   : ∀ b out, parse b = some out → out.consumed ≤ b.length
  noLook    : NoLookahead parse
  injective : Injective parse

def SerializerCorrect {α : Type} (p : BareParser α) (s : BareSerializer α) : Prop :=
  ∀ x : α, p (s x) = some ⟨x, (s x).length⟩

def SerializerComplete {α : Type} (p : BareParser α) (s : BareSerializer α) : Prop :=
  ∀ b out, p b = some out → s out.val = slicePrefix b out.consumed

def takeAll : ∀ (xs : Bytes) (n : Nat), n = xs.length → xs.take n = xs
  | [], 0, _ => rfl
  | [], _ + 1, h => nomatch h
  | _ :: _, 0, h => nomatch h
  | x :: xs, n + 1, h => by
    have hTail : n = xs.length := Nat.succ.inj h
    dsimp [List.take]
    rw [takeAll xs n hTail]

theorem serializer_correct_implies_complete {α : Type}
    {p : BareParser α} {s : BareSerializer α}
    (hInj : Injective p) (hCorr : SerializerCorrect p s) :
    SerializerComplete p s := by
  intro b out hParse
  have hSer := hCorr out.val
  have hPair := hInj (s out.val) b ⟨out.val, (s out.val).length⟩ out hSer hParse rfl
  have hTake : slicePrefix (s out.val) (s out.val).length = s out.val :=
    takeAll (s out.val) (s out.val).length rfl
  rw [← hTake]
  exact hPair.2

theorem parse_strong_prefix {α : Type}
    (sp : StrongParser α) {b1 b2 : Bytes} {out : ParseOut α}
    (hParse : sp.parse b1 = some out)
    (hLen : out.consumed ≤ b2.length)
    (hEq : slicePrefix b1 out.consumed = slicePrefix b2 out.consumed) :
    sp.parse b2 = some out :=
  sp.noLook b1 b2 out hParse hLen hEq

structure CLens (S A : Type) where
  cond : S → Prop
  get  : (s : S) → cond s → A

def CLens.comp {S A B : Type} (l1 : CLens S A) (l2 : CLens A B) : CLens S B where
  cond s := Exists fun (h1 : l1.cond s) => l2.cond (l1.get s h1)
  get s h :=
    match h with
    | ⟨h1, h2⟩ => l2.get (l1.get s h1) h2

end Anneal.Format
```

Evaluating this design across Anneal's seven engineering criteria:
1. **Zero-TCB Bridge & `Trusted.*` Gap Analysis**: `Anneal.Format` requires zero TCB changes. End-to-end verification of `zerocopy` `&[u8]` slice APIs in Rust, however, is currently gated on `Trusted.MirSemantics` (`MirSemantics.lean:L803, L1686–1694`), which rejects non-empty `q.callerMem.allocations`, non-scalar parameters (`isSupportedScalarOrUnitTy`), raw pointer dereferences, `CastKind.transmute`, structural ADTs, and `!Freeze` (`UnsafeCell`) tracking. Once those `Trusted.*` extensions are correspondence-verified against `lean-miri`, `SpatialPin` bridges Rust `&[u8]` allocations to `Bytes` specifications cleanly outside the TCB.
2. **Human Specification Auditability**: Under Statement-Origin Separation, `Specs.property` reduces to readable round-trip/canonicality obligations (`Bytes -> Option α`) without low-level bitmask or slice-split arithmetic clutter.
3. **Authoring & Day-2 Edit Locality**: `ParserStrong` and `Injective` propagate compositionally across fields; inserting or reordering fields touches only adjacent `and_then`/`CLens` combinators.
4. **Lean 4 (`v4.34.1`) Kernel & `<50 ms` LSP Scaling**: Applying `LowParse.Spec.Base.fsti:L514–522`'s single-`match` destructuring to kind joins avoids stuck-projection blowup in `whnf`, complementing `@[irreducible]` abstraction boundaries (`TrustedBoundary.lean:L595`) and bounded `Nat` checks (`≤ 128` bits).
5. **Heterogeneous Composability**: `Bytes` parsers bridge `PureLift` pure values (`MirBridge.lean`) to `SpatialPin` byte blocks (`SpatialPin.lean`), `MaybeUninit` output serialization (`l2r_writer`), and fallible `?` / unwind paths (`TerminalOut.unwound` satisfies `WellFormed` at `MirSemantics.lean:L1646`). `zerocopy::Immutable` marks the exact `!UnsafeCell` boundary where single-read stability prevents concurrent double-fetch TOCTOU.
6. **Failure Legibility**: Separating `Injective`, `NoLookahead`, `consumes_all`, and `clens_cond` yields concrete counterexamples—two prefixes with equal values (malleability), prefix extension mismatches (lookahead), unconsumed trailing slices, or inactive variant guards.
7. **Conceptual Minimality & Refuted Premature Collapses**: Unifying validator, jumper, and reader contracts under `StrongParser + SerializerCorrect` eliminates redundant per-pass axioms, while three collapses are refuted: (i) collapsing `ParserStrong` into `Injective` (`p_greedy` counterexample); (ii) collapsing `ParserStrong` and `ParserConsumesAll` (breaks sequencing prefix headers vs authenticating whole messages); and (iii) collapsing `CLens` into total `PureLift.Lens` without `Option`/prism guards (exposes inactive union variants).

## Boundaries

- **not examined**: Recursive/indefinite-length encodings (e.g., ASN.1 BER/DER `LowParse.Pulse.DER`) and stateful dictionary compression (`DEFLATE` back-references exceeding local prefix windows).
- **unknown**: The concrete `#[repr(u8)]` enum variant threshold at which inline Lean 4.34.1 `glb` / `and_then_cases_injective` elaboration exceeds a `<50 ms` LSP target without pre-indexed dispatch tries.
- **known not to apply**:
  - `zerocopy::FromBytes` *without* `IntoBytes` (e.g., `#[repr(C)] struct Padded { a: u8, b: u16 }`) does **not** satisfy `Injective` or `serializer_complete` because distinct padding bytes yield identical Rust values.
  - `ParserStrong` over shared mutable `!Freeze` (`UnsafeCell`) memory does **not** prevent concurrent TOCTOU double-fetch malleability without `Immutable` or single-fetch discipline (`allow_reading = false`).
  - `Narcissus` nondeterministic `FormatM` encoders (`mit-plv/fiat`) do **not** satisfy `serializer_unique` or `serializer_complete`.
- **unsupported**: In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirSemantics` fails closed (`FaultKind.unsupported`) on non-empty `CallerMemory`, `&[u8]` slice/reference arguments (`isSupportedScalarOrUnitTy`), raw pointer dereferences, `CastKind.transmute`, and structural ADTs (`MirSemantics.lean:L332, L803, L1686–1694`).

## Evidence

| Subject | Exact Identity | Inspected Paths & Anchors |
| :--- | :--- | :--- |
| **EverParse / LowParse** | `project-everest/everparse` @ `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` | `lib/everparse/lowparse/LowParse.Spec.Base.fsti` (`L23–363`, `L505–558`, `L669–1117`); `LowParse.Spec.Base.fst` (`L53–160`); `LowParse.CLens.fst` (`L5–225`); `LowParse.Spec.Combinators.fst` (`L10–150`); `LowParse.Spec.BCVLI.fst` (`L8–151`); `LowParse.BitFields.fsti` (`L4–204`); `LowParse.Pulse.Base.fst` (`L12–231`); `LowParse.PulseParse.Base.fst` (`L15–93`, `L749–804`); `LowParse.PulseParse.Combinators.fst` (`L1246–1590`); `LowParse.PulseParse.BCVLI.fst` (`L23–85`); `lib/everparse/3d/EverParse3d.Actions.Base.fsti` (`L42–240`) |
| **MIT Narcissus** | `mit-plv/fiat` @ `77f43f5d5408b3543f8dd01d4d43f4c4c70f1213` (also `df1565d187de242fdf822111a23e3f6b71049c9c`) | `src/Narcissus/Common/Specs.v` (`L20–320`); `src/Narcissus/Common/ComposeIf.v` (`L7–100`) |
| **zerocopy** | `google/zerocopy` @ `ec133ce4d7993775413d852f91c9e3eb2a2a0897` | `zerocopy/src/lib.rs` (`L1419–1510`, `L4358–4430`, `L5511–5584`, `L6005–6085`); `zerocopy/src/ref.rs` (`L24–160`) |
| **Anneal & Lean 4** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/Trusted/MirSemantics.lean` (`L332`, `L803`, `L949–977`, `L1646–1809`); `theory/Anneal/PureLift/{Lens,SpatialPin,MirBridge}.lean` |
| **Literature** | USENIX Security 2019 (`ISBN 978-1-939133-06-9`); PLDI 2022 (`10.1145/3519939.3523708`); ICFP 2019 (`10.1145/3341686`) | Ramananandro et al. (*EverParse*), Swamy et al. (*EverParse3D*), Delaware et al. (*Narcissus*) |

### Executable Probe 1 (`CPython 3.13.15`, `x86_64`, `2026-11-19`)

```python
from itertools import product

def parse_bcvli_canonical(buf: bytes):
    if len(buf) < 1: return None
    b0 = buf[0]
    if b0 <= 252: return (b0, 1)
    if b0 == 253 and len(buf) >= 3:
        v = int.from_bytes(buf[1:3], "little")
        return (v, 3) if v >= 253 else None
    if b0 == 254 and len(buf) >= 5:
        v = int.from_bytes(buf[1:5], "little")
        return (v, 5) if v >= 65536 else None
    return None

def parse_bcvli_naive(buf: bytes):
    if len(buf) < 1: return None
    b0 = buf[0]
    if b0 <= 252: return (b0, 1)
    if b0 == 253 and len(buf) >= 3: return (int.from_bytes(buf[1:3], "little"), 3)
    if b0 == 254 and len(buf) >= 5: return (int.from_bytes(buf[1:5], "little"), 5)
    return None

def serialize_bcvli(x: int) -> bytes:
    if x <= 252: return bytes([x])
    if x <= 65535: return bytes([253]) + x.to_bytes(2, "little")
    return bytes([254]) + x.to_bytes(4, "little")

for v in [0, 1, 252, 253, 65535, 65536, 0xFFFFFFFF]:
    enc = serialize_bcvli(v)
    assert parse_bcvli_canonical(enc) == (v, len(enc))
    assert parse_bcvli_canonical(enc + b"\xde\xad") == (v, len(enc))

assert parse_bcvli_naive(b"\xfd\xfc\x00") == (252, 3)
assert parse_bcvli_canonical(b"\xfd\xfc\x00") is None
assert parse_bcvli_canonical(b"\xfe\xff\xff\x00\x00") is None

def p_greedy(buf: bytes):
    if buf[:2] == b"\x01\x01": return (2, 2)
    if buf == b"\x01": return (1, 1)
    return None

def s_greedy(v: int) -> bytes:
    return b"\x01" if v == 1 else b"\x01\x01"

all_bufs = [bytes(t) for n in range(5) for t in product([0, 1, 2], repeat=n)]
for b1 in all_bufs:
    r1 = p_greedy(b1)
    if r1 is None: continue
    for b2 in all_bufs:
        r2 = p_greedy(b2)
        if r2 is not None and r1[0] == r2[0]:
            assert r1[1] == r2[1] and b1[:r1[1]] == b2[:r2[1]]

assert p_greedy(s_greedy(1)) == (1, 1) and p_greedy(s_greedy(2)) == (2, 2)
assert (p_greedy(b"\x01"), p_greedy(b"\x01\x01")) == ((1, 1), (2, 2))
dirty_a, canonical_a = 0b01_1111_10, 0b01_0000_10
naive_bf = lambda b: (b & 0x3, (b >> 6) & 0x3)
strict_bf = lambda b: (b & 0x3, (b >> 6) & 0x3) if ((b >> 2) & 0xF) == 0 else None
assert naive_bf(dirty_a) == naive_bf(canonical_a) == (2, 1)
assert strict_bf(dirty_a) is None and strict_bf(canonical_a) == (2, 1)
print("PROBE_1_OK", {
    "canonical_252_len": len(serialize_bcvli(252)),
    "canonical_253_len": len(serialize_bcvli(253)),
    "canonical_65536_len": len(serialize_bcvli(65536)),
    "overlong_3_rejected": parse_bcvli_canonical(b"\xfd\xfc\x00") is None,
    "overlong_5_rejected": parse_bcvli_canonical(b"\xfe\xff\xff\x00\x00") is None,
    "greedy_injective_bufs_checked": len(all_bufs),
    "greedy_prefix_violation": (p_greedy(b"\x01"), p_greedy(b"\x01\x01")),
    "dirty_bitfield_rejected": strict_bf(dirty_a) is None,
})
```

Observed output (`2026-11-19`, `CPython 3.13.15`): `PROBE_1_OK {'canonical_252_len': 1, 'canonical_253_len': 3, 'canonical_65536_len': 5, 'overlong_3_rejected': True, 'overlong_5_rejected': True, 'greedy_injective_bufs_checked': 121, 'greedy_prefix_violation': ((1, 1), (2, 2)), 'dirty_bitfield_rejected': True}`.

## Revalidation

1. **EverParse / LowParse source check:** Fetch `LowParse.Spec.Base.{fsti,fst}`, `LowParse.CLens.fst`, and `LowParse.PulseParse.Base.fst` from a newer `project-everest/everparse` commit and diff against `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` to check whether `clens_put` / `clens_disjoint` or `glb` destructuring changed.
2. **`zerocopy` trait audit:** Re-inspect `ProjectField`, `FromBytes::read_from_{bytes,prefix}`, `IntoBytes::as_bytes`, and `Immutable` in `google/zerocopy` (`zerocopy/src/lib.rs`).
3. **Anneal MIR & Lean kernel check:** Inspect `Trusted/MirSemantics.lean` for `callerMem` and `&[u8]` slice support, and run `lean` (`v4.34.1`) under `--trust=0` on the `Anneal.Format` module in Section 5 to confirm zero errors and `{propext, Quot.sound, Classical.choice}` closure.
4. **Executable probe:** Run the Python 3 script in **Evidence** (`python3` $\ge 3.10$) and verify `PROBE_1_OK` prints with exit code `0`.
