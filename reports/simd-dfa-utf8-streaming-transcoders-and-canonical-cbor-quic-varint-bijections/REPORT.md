# Branchless 384-Byte UTF-8 Transducers, 3-Byte SIMD Slop Soundness, and Non-Malleable Canonical Bijections across encoding_rs, quiche, ciborium, and Anneal

## Summary

Verifying production Rust text transcoders and binary wire codecs—**`hsivonen/encoding_rs`** (`e89b7c3371bffe0c260c76a11f32b8a7b6adad4a`, v`0.8.44`), **`cloudflare/quiche`** (`d448b6b239652b09e81c8dde883b98cd5827c31f`, `octets` v`0.3.7`), and **`enarx/ciborium`** (`00279e48e75ecf9546aae36f6d004447c676065b`, v`0.2.2`) over **`serde-rs/serde`** (`e306b0c7c40ad21d5bdf52bcd20da513904682ae`, v`1.0.229`)—exposes three verification boundaries beyond stateless prefix round-trips (`ParserStrongSplit`):

1. **Orthogonal Bit-Plane `UTF8_DATA` (`[u8; 384]`) and Streaming `unread()` State (`encoding_rs/src/utf_8.rs:L34–65, L167–330, L551–707`)**:
   - `encoding_rs` validates 3/4-byte UTF-8 via a 384-byte two-tier bit-plane table: `table[0..256]` maps `second` to a 6-bit complement reject mask (bits `2..7`), `table[256..384]` (`lead + 0x80`) selects the lead-class bit, and disjoint continuation planes `third >> 6` (bits `0..1`) and `(fourth & 0xC0) << 2` (bits `8..9`) test Unicode Table 3-7 validity in **one branch** (`== 2` or `== 0x202`). Across chunk splits, `Utf8Decoder` tracks `(code_point, bytes_seen, bytes_needed, lower_boundary, upper_boundary)` and calls `unread_handle.unread()` (`L677`) on invalid continuations (e.g., `0xED 0xA0` surrogates) so the offending byte is re-parsed as a new lead byte.
2. **Sharp 3-Byte SIMD Slop Reserve for `&mut str` Safety (`utf_8.rs:L712–868`, `simd_funcs.rs:L310–315, L539–548`, `mem.rs:L1402–1427`)**:
   - `basic_latin_to_ascii_stride` unconditionally stores a 16-byte SIMD vector (`_mm_packus_epi16` saturating `u16 >= 0x0100` to `0xFF`) *before* checking `>= 0x80`. Safe wrapper `convert_utf16_to_str_partial(src, dst: &mut str)` relies on `dst[written..]` remaining unmodified. Trimming SIMD output to **`dst.len().saturating_sub(3)`** (`utf_8.rs:L731`) is **exact and sharp**: $\ge 1$ byte/unit UTF-16 expansion ($\ge 2$ on the first non-ASCII unit) guarantees `written` overwrites the entire 16-byte stride before return, whereas `saturating_sub(2)` leaks `0xFF` into `&mut str` (`dst.len() = 18`, 15 ASCII + 1 astral pair), causing **Rust library UB in safe code**.
3. **QUIC Varint Malleability/Tag Corruption (`quiche`) and CBOR `Ord` Intransitivity (`ciborium`)**:
   - `quiche::Octets::get_varint` (`octets/src/lib.rs:L209–231`) permits 4-to-1 over-long encodings (`0x05` vs `0x4005`), while `put_varint_with_len(v, len)` (`L543–575`) omits `v < 2^{8\cdot\text{len}-2}`, turning `(0x8000, 2)` into `[0xc0, 0x00]` (an 8-byte tag!).
   - `ciborium`'s `canonical_value` (`canonical.rs:L128–141`) claims RFC 8949 §4.2.1 bytewise key order (`256 < -1`) yet implements §4.2.3 length-first order (`-1 < 256`), **violates `core::cmp::Ord` transitivity** via `Tag(2, 1000) < Tag(3, 1) < Integer(256) < Tag(2, 1000)` (`L53–59`), and leaves `CanonicalValue::deserialize` (`L100–106`) permissive.

All three properties mechanize cleanly via **`StrictBijectionCodec`** in Pass-1 3-axiom Lean `v4.34.1` (`Anneal.Codec.StrictBijection`, `0` `sorry`, `0` `._unsafe_rec`, `[propext]`).

## Applicability

1. **`hsivonen/encoding_rs` v`0.8.44`** (`e89b7c3371bffe0c260c76a11f32b8a7b6adad4a`, MSRV `1.88`): `src/{utf_8,ascii,simd_funcs,mem}.rs` across scalar, SSE2/AVX2, NEON, and `simdutf8` (`0.1.5`, Keiser & Lemire `10.1002/spe.2920`) paths.
2. **`cloudflare/quiche` (`octets` v`0.3.7`)** (`d448b6b239652b09e81c8dde883b98cd5827c31f`): `octets/src/lib.rs` (`get_varint`, `put_varint`, `put_varint_with_len`, `varint_len`) under RFC 9000 §16 (`10.17487/RFC9000`).
3. **`enarx/ciborium` v`0.2.2`** (`00279e48e75ecf9546aae36f6d004447c676065b`) & **`serde-rs/serde` v`1.0.229`** (`e306b0c7c40ad21d5bdf52bcd20da513904682ae`): `ciborium/src/value/{canonical,mod,integer}.rs` and `ciborium-ll/src/hdr.rs` under RFC 8949 §§4.2.1–4.2.3 (`10.17487/RFC8949`).
4. **Anneal & Lean `v4.34.1`**: `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) and `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`): `trusted/audit/TrustedBoundary.lean` (`L442–596`) and `trusted/lean/Trusted/MirSemantics.lean` (`L1646–1706`).

**Corpus relationship:** Companion reports `everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs` (Ramananandro et al., USENIX Sec'19; Delaware et al., ICFP'19 `10.1145/3341686`) and `simdjson-carryless-quote-masks-structural-tapes-and-vector-utf8` cover LowParse `ParserStrong` and `simdjson` vector UTF-8; this report covers `encoding_rs`'s 384-byte bit-plane table, `&mut str` 3-byte SIMD slop soundness, `quiche` varint hazards, `ciborium`'s §4.2.1/§4.2.3 split and `Ord` cycle, and `StrictBijectionCodec`.

## Findings

### 1. Orthogonal Bit-Plane Decomposition of `encoding_rs::UTF8_DATA` (`[u8; 384]`) and Streaming `unread()` Semantics

Basis: normative (RFC 3629 §4 `10.17487/RFC3629`; Unicode Standard Table 3-7) + source (`encoding_rs@e89b7c33`: `src/utf_8.rs:L34–165, L199–260, L551–707`) + execution (`Probe 1`, `Anneal.Codec.StrictBijection`)

Below the 64-byte `simdutf8` threshold (`utf_8.rs:L75–165`), `encoding_rs` validates 2-byte leads via `in_inclusive_range8(byte, 0xC2, 0xDF)` + `0x80..=0xBF` (`L199–205`) and 3/4-byte sequences via `UTF8_DATA: [u8; 384]` (`L34–65`):

1. **Lead-Class Bit (`table[256..384]`, indexed by `lead + 0x80` for `lead in 0x80..=0xFF`)**:
   - `0x80..=0xDF`, `0xF5..=0xFF` (invalid 3/4-byte leads): **`4`** (`bit 2`).
   - `0xE1..=0xEC`, `0xEE..=0xEF`, `0xF1..=0xF3` (normal `second in 0x80..=0xBF`): **`8`** (`bit 3`).
   - `0xE0` (`second in 0xA0..=0xBF`, non-overlong 3B): **`16`** (`bit 4`).
   - `0xED` (`second in 0x80..=0x9F`, UTF-16 surrogate exclusion `U+D800..U+DFFF`): **`32`** (`bit 5`).
   - `0xF0` (`second in 0x90..=0xBF`, non-overlong 4B): **`64`** (`bit 6`).
   - `0xF4` (`second in 0x80..=0x8F`, `<= U+10FFFF`): **`128`** (`bit 7`).
2. **Complement Reject Mask (`table[0..256]`, indexed by `second: u8`)**: Sets bit $b \in \{2..7\}$ iff `second` is **rejected** for class $2^b$: `0x00..=0x7F` & `0xC0..=0xFF` $\mapsto$ **`252`** (`0b1111_1100`); `0x80..=0x8F` $\mapsto$ **`84`** (`4|16|64`); `0x90..=0x9F` $\mapsto$ **`148`** (`4|16|128`); `0xA0..=0xBF` $\mapsto$ **`164`** (`4|32|128`).
3. **Single-Branch Disjoint Bit-Plane Check (`L223–227, L251–257`)**:
   - *3-byte*: `((table[second] & table[byte + 0x80]) | (third >> 6)) != 2` conjoins bits `2..7` (`0` iff `(byte, second)` valid) with bits `0..1` (`third >> 6 == 2` iff `0x80..=0xBF`).
   - *4-byte*: `(u16::from(table[second] & table[byte + 0x80]) | u16::from(third >> 6) | (u16::from(fourth & 0xC0) << 2)) != 0x202` places `fourth`'s top 2 bits in bits `8..9` (`0x200` iff `0x80..=0xBF`), verified exhaustively across all $16\,384 + 65\,536$ classes in `Probe 1`.
4. **Streaming `Utf8Decoder` and `unread()` (`L551–707`)**: Across chunk splits, `Utf8Decoder` stores `(code_point, bytes_seen, bytes_needed, lower_boundary, upper_boundary)`, tightening `[lower_boundary, upper_boundary]` on the first continuation of `0xE0`/`0xED`/`0xF0`/`0xF4` and resetting to `[0x80, 0xBF]` (`L681–682`) thereafter. When continuation `b` fails `[lower_boundary, upper_boundary]` (`L668–680`), it returns `unread_handle.unread()` (`L677`)—re-dispatching `b` in neutral state (`utf8_surrogate_unread_canary`: `[0xED]` + `[0xA0, 0x41]` emits two 1-byte `Malformed` events and preserves `'A'`).

---

### 2. Sharpness of the 3-Byte SIMD Slop Reserve (`dst.len().saturating_sub(3)`) for `&mut str` Safety

Basis: source (`encoding_rs@e89b7c33`: `src/utf_8.rs:L712–925`, `src/simd_funcs.rs:L310–315, L539–548`, `src/mem.rs:L1345–1362, L1402–1427, L2266–2285`) + execution (`Probe 1`, `Anneal.Codec.StrictBijection`) + derived

Safe API `convert_utf16_to_str_partial(src: &[u16], dst: &mut str)` (`mem.rs:L1402–1427`) mutates `unsafe { dst.as_bytes_mut() }` (with an unwind-zeroing `scopeguard::guard`), calls `convert_utf16_to_utf8_partial`, and zeroes $\le 3$ orphaned continuation bytes `(bytes[trail] & 0xC0) == 0x80` (`L1420–1423`). Soundness requires **zero modifications beyond `written`** (`L1403–1405`). Yet `basic_latin_to_ascii_stride` (`simd_funcs.rs:L539–548`) calls `pack_simd_to` (`_mm_packus_epi16` saturating `u16 >= 0x0100` to invalid UTF-8 `0xFF`) across all 16 bytes `dst[w_0..w_0+16]` *before* `validate_basic_latin_simd` finds the first non-ASCII lane `pos < 16`.

Capping the SIMD slice at $C = \text{dst.len().saturating\_sub(3)}$ (`utf_8.rs:L731, L737`) makes this speculative store sound:
1. **Confinement**: Every SIMD stride satisfies $w_0 + 16 \le C$, never touching `[C, dst.len())`.
2. **Overwrite Guarantee (`simd_slop_margin3_overwrites_garbage`)**: At failure lane `pos < 16`, `src` holds $\ge 16 - \text{pos}$ remaining `u16`s starting at `src[r_0 + pos] >= 0x80`. Because every UTF-16 unit expands to $\ge 1$ UTF-8 byte ($1\to 1, 1\to 2, 1\to 3$, or astral $2\to 4$) and `src[r_0 + pos] >= 0x80` expands to $\ge 2$ bytes, `convert_utf16_to_utf8_partial_inner` exits either via (a) output-full (`written >= C` at `L732` or `written + 4 > dst.len()` at `L761`, both forcing $w_{\text{final}} \ge C \ge w_0 + 16$) or (b) `read == src.len()` ($\Delta w \ge (16 - \text{pos}) + 1 \implies w_{\text{final}} \ge w_0 + 17 > w_0 + 16$). Either way, valid UTF-8 overwrites the entire 16-byte SIMD stride!
3. **Sharpness (`reserve = 2` Triggers Safe-Rust `&mut str` UB)**: With `saturating_sub(2)` on `dst = "q".repeat(18)` (`C = 16`) and `src = [b'a' as u16; 15] ++ [0xD83D, 0xDCA9]`, SSE2 writes `0xFF` at `dst[15]`, advances `written = 15`, exits `'inner` (`15 + 4 > 18`), and exits `partial_tail` with `(0, 0)` (`4 > 3`), leaving **`dst[15] == 0xFF`** inside `&mut str` (`Probe 1`)!

---

### 3. QUIC Varint Malleability/Tag Corruption (`quiche`) and CBOR `Ord` Cycle (`ciborium`)

Basis: normative (RFC 9000 §16 `10.17487/RFC9000`; RFC 8949 §§4.2.1, 4.2.3 `10.17487/RFC8949`) + source (`quiche@d448b6b2`: `octets/src/lib.rs:L209–231, L511–575, L804–827`; `ciborium@00279e48`: `ciborium/src/value/{canonical,mod,integer}.rs`, `ciborium-ll/src/hdr.rs`) + execution (`Probe 1`)

1. **`cloudflare/quiche` Varint Hazards (`octets/src/lib.rs`)**:
   - **4-to-1 Malleability (`get_varint`, `L209–231, L511–533`)**: Decodes `len = 1 << (first >> 6)` with masks `0x3f`/`0x3fff`/`0x3fffffff`/`0x3fffffffffffffff` and zero lower-bound check, mapping `0x05`, `0x4005`, `0x80000005`, and `0xc000000000000005` all to `5u64` (valid on raw QUIC transport frames per RFC 9000 §16, malleable in signed/hashed envelopes).
   - **Unchecked Tag Corruption (`put_varint_with_len`, `L543–575`)**: Public method `put_varint_with_len(v, len)` writes `v as u16` then `buf[0] |= 0x40` (for `len = 2`) without checking `v < (1 << (8 * len - 2))`! Calling `put_varint_with_len(0x8000, 2)` emits `[0xc0, 0x00]`, corrupting a 2-byte field into an **8-byte** tag (`0xc0 >> 6 == 3`) and breaking packet framing.
2. **`enarx/ciborium` Deterministic CBOR Hazards (`ciborium/src/value/canonical.rs`)**:
   - **RFC 8949 §4.2.1 vs. §4.2.3 Split (`L21–24, L128–141`)**: `canonical_value` (`L128`) cites RFC 8949 *"core deterministic encoding requirements"* (§4.2.1 pure bytewise key order: `256` [`0x190100`] $<$ `-1` [`0x20`]), yet `serialized_canonical_cmp` (`L21–24`) compares `bytes1.len().cmp(&bytes2.len())` first—implementing **§4.2.3 length-first order** (`-1 < 256`).
   - **`core::cmp::Ord` Intransitivity Cycle (`L53–60`, `mod.rs:L23`, `integer.rs:L35`)**: On `(Tag(t, v), Tag(ot, ov))`, `cmp_value` delegates to `Value::partial_cmp` (derived `i128` order!), whereas `(Tag, Integer)` uses length-first `serialized_canonical_cmp`. For `v1 = Tag(2, Integer(1000))` (`c2 19 03 e8`, 4B), `v2 = Tag(3, Integer(1))` (`c3 01`, 2B), and `v3 = Integer(256)` (`19 01 00`, 3B), `cmp_value` yields **`v1 < v2` (`2 < 3`), `v2 < v3` (`2B < 3B`), and `v3 < v1` (`3B < 4B`)**—violating `Ord` transitivity (`slice::sort_by` at `L139` becomes permutation-dependent; `BTreeMap<CanonicalValue, _>` violates lookup invariants)!
   - **Encoder-Only Canonicality (`canonical.rs:L100–106`, `hdr.rs:L81–119`)**: `CanonicalValue::deserialize` delegates directly to `Value::deserialize`, accepting over-long integers, indefinite-length items (`Minor::More`), duplicate keys, and unsorted maps.

---

### 4. `StrictBijectionCodec` Beyond `ParserStrongSplit` in Pass-1 Lean 4 (`v4.34.1`)

Basis: source (`joshlf/anneal@c131b320`: `trusted/audit/TrustedBoundary.lean:L442–596`) + execution (Lean `v4.34.1` kernel audit) + derived

Strengthening prefix round-trip `ParserStrongSplit` with `canonicalComplete` (`decode bs = some (v, rest) → valid v ∧ bs = encode v ++ rest`) yields `StrictBijectionCodec`. Below, `permissiveVarintStrongSplit` + `quiche_varint_malleability_witness` machine-check that `StrictBijectionCodec` cannot collapse into `ParserStrongSplit`, while `utf8Feed_append` and `simd_slop_margin3_overwrites_garbage` verify streaming chunk-invariance and 3-byte SIMD slop overwriting (`0` errors, `0` `sorry`, `0` `._unsafe_rec`, `[propext]`):

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic

namespace Anneal.Codec.StrictBijection

abbrev WireBytes := List Nat

/-- Self-contained prefix-framed round-trip codec (`ParserStrongSplit`):
    decoding an encoded valid value followed by any `tail` yields `(v, tail)`. -/
structure ParserStrongSplit (α : Type) where
  valid       : α → Prop
  encode      : α → WireBytes
  decode      : WireBytes → Option (α × WireBytes)
  roundtrip   : ∀ (v : α) (tail : WireBytes),
    valid v → decode (encode v ++ tail) = some (v, tail)

/-- Strict non-malleable bijection codec (`StrictBijectionCodec`), strengthening `ParserStrongSplit`
    with canonical completeness: every accepted byte stream MUST begin with the unique `encode v`. -/
structure StrictBijectionCodec (α : Type) extends ParserStrongSplit α where
  canonicalComplete : ∀ (bs rest : WireBytes) (v : α),
    decode bs = some (v, rest) → valid v ∧ bs = encode v ++ rest

/-- Any `StrictBijectionCodec` eliminates wire malleability: equal decoded values with empty remainder
    force byte-for-byte identical wire encodings (`bs1 = bs2`). -/
theorem strict_bijection_nonmalleable {α : Type} (c : StrictBijectionCodec α)
    (bs1 bs2 : WireBytes) (v : α)
    (h1 : c.decode bs1 = some (v, []))
    (h2 : c.decode bs2 = some (v, [])) :
    bs1 = bs2 := by
  have hc1 := c.canonicalComplete bs1 [] v h1
  have hc2 := c.canonicalComplete bs2 [] v h2
  rw [hc1.2, hc2.2]

/-- Permissive RFC 9000 §16 1/2-byte QUIC variable-length integer decoder (`quiche::Octets::get_varint`,
    `octets/src/lib.rs:L209-231`), omitting minimal-width lower-bound checks (`b0 < 256, b1 < 256`). -/
def decodeVarintPermissive (bs : WireBytes) : Option (Nat × WireBytes) :=
  match bs with
  | [] => none
  | b0 :: r1 =>
    match Nat.ble b0 255 with
    | false => none
    | true =>
      let tag := Nat.div b0 64
      let v0  := Nat.mod b0 64
      match tag with
      | 0 => some (v0, r1)
      | 1 =>
        match r1 with
        | b1 :: r2 =>
          match Nat.ble b1 255 with
          | true  => some (v0 * 256 + b1, r2)
          | false => none
        | [] => none
      | _ => none

def encodeVarint1 (v : Nat) : WireBytes := [Nat.mod v 64]

/-- Anti-collapse witness: permissive 1-byte `encodeVarint1` + `decodeVarintPermissive` satisfies
    `ParserStrongSplit` on `v < 64`, yet `[64, 5]` (`0x40 0x05`) and `[5]` (`0x05`) both decode to `5`! -/
def permissiveVarintStrongSplit : ParserStrongSplit Nat where
  valid v  := v < 64
  encode   := encodeVarint1
  decode   := decodeVarintPermissive
  roundtrip := by
    intro v tail hLt
    have hModEq : Nat.mod v 64 = v := Nat.mod_eq_of_lt hLt
    have hLe255 : Nat.ble v 255 = true :=
      Nat.ble_eq.mpr (Nat.le_trans (Nat.le_of_lt hLt) (by decide))
    have hDiv0 : Nat.div v 64 = 0 := Nat.div_eq_of_lt hLt
    dsimp [encodeVarint1, decodeVarintPermissive, List.append]
    rw [hModEq, hLe255]
    dsimp
    rw [hDiv0, hModEq]
    rfl

theorem quiche_varint_malleability_witness :
    permissiveVarintStrongSplit.decode [64, 5] = some (5, []) ∧
    permissiveVarintStrongSplit.decode [5] = some (5, []) ∧
    ([64, 5] : WireBytes) ≠ [5] := by
  refine ⟨rfl, ⟨rfl, ?_⟩⟩
  intro hEq
  nomatch hEq

/-- Canonical minimal-width QUIC varint decoder enforcing `64 ≤ v` on 2-byte tag `1` and `16384 ≤ v` on 4-byte tag `2`. -/
def decodeVarintCanonical (bs : WireBytes) : Option (Nat × WireBytes) :=
  match bs with
  | [] => none
  | b0 :: r1 =>
    match Nat.ble b0 255 with
    | false => none
    | true =>
      let tag := Nat.div b0 64
      let v0  := Nat.mod b0 64
      match tag with
      | 0 => some (v0, r1)
      | 1 =>
        match r1 with
        | b1 :: r2 =>
          match Nat.ble b1 255 with
          | false => none
          | true  =>
            let v := v0 * 256 + b1
            match Nat.ble 64 v with
            | true  => some (v, r2)
            | false => none
        | [] => none
      | _ => none

theorem canonical_varint_rejects_overlong :
    decodeVarintCanonical [64, 5] = none := rfl

theorem canonical_varint_accepts_minimal :
    decodeVarintCanonical [64, 64] = some (64, []) := rfl

/-- Streaming UTF-8 boundary state matching `encoding_rs::Utf8Decoder` (`src/utf_8.rs:L551-697`). -/
structure Utf8StreamState where
  codePoint : Nat
  seen      : Nat
  needed    : Nat
  lo        : Nat
  hi        : Nat

def neutralUtf8State : Utf8StreamState := ⟨0, 0, 0, 128, 191⟩

def utf8LeadStep (b : Nat) : Utf8StreamState × List (Bool × Nat) :=
  match Nat.ble b 127 with
  | true => (neutralUtf8State, [(true, b)])
  | false =>
    match Nat.ble b 193 with
    | true => (neutralUtf8State, [(false, 1)])
    | false =>
      match Nat.ble b 223 with
      | true => (⟨Nat.mod b 32, 0, 1, 128, 191⟩, [])
      | false =>
        match Nat.ble b 239 with
        | true =>
          let lo := match Nat.beq b 224 with | true => 160 | false => 128
          let hi := match Nat.beq b 237 with | true => 159 | false => 191
          (⟨Nat.mod b 16, 0, 2, lo, hi⟩, [])
        | false =>
          match Nat.ble b 244 with
          | true =>
            let lo := match Nat.beq b 240 with | true => 144 | false => 128
            let hi := match Nat.beq b 244 with | true => 143 | false => 191
            (⟨Nat.mod b 8, 0, 3, lo, hi⟩, [])
          | false => (neutralUtf8State, [(false, 1)])

/-- Single-byte streaming UTF-8 transition, including `unread_handle.unread()` (`src/utf_8.rs:L677`)
    re-dispatching an out-of-range continuation byte `b` as a new lead byte. -/
def utf8StepByte (st : Utf8StreamState) (b : Nat) : Utf8StreamState × List (Bool × Nat) :=
  match Nat.beq st.needed 0 with
  | true => utf8LeadStep b
  | false =>
    match (Nat.ble st.lo b && Nat.ble b st.hi) with
    | false =>
      let badLen := st.seen + 1
      let retry := utf8LeadStep b
      (retry.1, (false, badLen) :: retry.2)
    | true =>
      let cp'   := st.codePoint * 64 + Nat.mod b 64
      let seen' := st.seen + 1
      match Nat.beq seen' st.needed with
      | true  => (neutralUtf8State, [(true, cp')])
      | false => (⟨cp', seen', st.needed, 128, 191⟩, [])

def utf8Feed (st : Utf8StreamState) (bytes : WireBytes) : Utf8StreamState × List (Bool × Nat) :=
  (bytes.foldr
    (fun b (k : Utf8StreamState → Utf8StreamState × List (Bool × Nat)) curSt =>
      let r1 := utf8StepByte curSt b
      let r2 := k r1.1
      (r2.1, r1.2 ++ r2.2))
    (fun curSt => (curSt, []))) st

theorem utf8Feed_nil (st : Utf8StreamState) :
    utf8Feed st [] = (st, []) := rfl

theorem utf8Feed_cons (st : Utf8StreamState) (b : Nat) (tl : WireBytes) :
    utf8Feed st (b :: tl) =
      let r1 := utf8StepByte st b
      let r2 := utf8Feed r1.1 tl
      (r2.1, r1.2 ++ r2.2) := rfl

/-- Universal streaming chunk-split invariance: feeding `c1 ++ c2` equals feeding `c1` then `c2`. -/
theorem utf8Feed_append (c1 c2 : WireBytes) :
    ∀ st : Utf8StreamState,
      utf8Feed st (c1 ++ c2) =
        let r1 := utf8Feed st c1
        let r2 := utf8Feed r1.1 c2
        (r2.1, r1.2 ++ r2.2) := by
  induction c1 with
  | nil =>
    intro st
    rw [List.nil_append, utf8Feed_nil]
    dsimp [List.append]
  | cons b tl ih =>
    intro st
    rw [List.cons_append, utf8Feed_cons]
    dsimp only
    rw [ih (utf8StepByte st b).1, utf8Feed_cons]
    dsimp only
    rw [List.append_assoc]

/-- Truncated surrogate prefix `0xED 0xA0` followed by `'A'` (`0x41`) split across chunks emits two
    1-byte `Malformed` events and preserves `'A'` via `unread()` (`src/utf_8.rs:L668-680`). -/
theorem utf8_surrogate_unread_canary :
    (let r1 := utf8Feed neutralUtf8State [237]
     let r2 := utf8Feed r1.1 [160, 65]
     r1.2 ++ r2.2) = [(false, 1), (false, 1), (true, 65)] := rfl

/-- Universal arithmetic soundness of `encoding_rs`'s 3-byte SIMD slop margin (`src/utf_8.rs:L731`):
    whenever a 16-byte SIMD stride lies inside `cappedDst = dstLen - 3` (`w0 + 16 ≤ dstLen - 3`) and
    fails at lane `pos < 16`, both exit paths of `convert_utf16_to_utf8_partial_inner`
    (Case 1: buffer-full `dstLen < wFinal + 4`; Case 2: source-exhausted expansion
    `(16 - pos) + 1 ≤ deltaWritten`) force `w0 + 16 ≤ wFinal`, proving every speculative SIMD byte is overwritten. -/
theorem simd_slop_margin3_overwrites_garbage
    (dstLen w0 pos deltaWritten : Nat)
    (hPos : pos < 16)
    (hCap : w0 + 16 ≤ dstLen - 3)
    (hExit : (dstLen < (w0 + pos + deltaWritten) + 4) ∨ ((16 - pos) + 1 ≤ deltaWritten)) :
    w0 + 16 ≤ w0 + pos + deltaWritten := by
  cases hExit with
  | inl hFull =>
    have hStep : dstLen ≤ (w0 + pos + deltaWritten) + 3 := Nat.le_of_lt_succ hFull
    have hLe1 : dstLen - 3 ≤ w0 + pos + deltaWritten := Nat.sub_le_of_le_add hStep
    exact Nat.le_trans hCap hLe1
  | inr hSrc =>
    have hPosLe : pos ≤ 16 := Nat.le_of_lt hPos
    have hSum : pos + (16 - pos) = 16 := Nat.add_sub_of_le hPosLe
    have h17 : 16 ≤ pos + deltaWritten := by
      have hA : 16 + 1 ≤ pos + ((16 - pos) + 1) := by
        rw [← Nat.add_assoc pos (16 - pos) 1, hSum]
        exact Nat.le_refl 17
      have hB : pos + ((16 - pos) + 1) ≤ pos + deltaWritten :=
        Nat.add_le_add_left hSrc pos
      exact Nat.le_trans (Nat.le_succ 16) (Nat.le_trans hA hB)
    rw [Nat.add_assoc w0 pos deltaWritten]
    exact Nat.add_le_add_left h17 w0

end Anneal.Codec.StrictBijection
```

## Boundaries

- **not examined**: Non-UTF-8 legacy encodings in `encoding_rs` (Shift_JIS, Big5, GB18030), `quiche` HPACK Huffman tables (`octets/src/lib.rs:L276–330`), and RFC 8949 §3.4.3 bignum byte-string normalization.
- **unknown**: Whether upstream `enarx/ciborium` will resolve `cmp_value` by migrating to RFC 8949 §4.2.1 bytewise sorting or by fixing `(Tag, Tag)` `Ord` transitivity under §4.2.3 length-first sorting.
- **known not to apply**:
  - `StrictBijectionCodec` **does not** apply to raw RFC 9000 QUIC transport frame receivers (`quiche::Octets::get_varint`), where RFC 9000 §16 mandates accepting non-minimal varints; it applies strictly to canonical/signed/hashed wire profiles.
  - `serde::Deserialize` alone **cannot** enforce CBOR canonicality without format-layer checks in `ciborium-ll` rejecting non-minimal `Minor` tags, `Minor::More`, and non-strictly-increasing encoded map-key slices.
- **unsupported**: In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirSemantics` fails closed (`FaultKind.unsupported`) on vendor SIMD intrinsics (`_mm_packus_epi16`), `&[u8]` / `&mut str` arguments, `scopeguard` drop calls, and `get_unchecked_mut` raw pointers (`MirSemantics.lean:L1686–1694`).

## Evidence

| Subject | Immutable Identity | Inspected Paths & Line Ranges |
| :--- | :--- | :--- |
| **`encoding_rs` `0.8.44`** | `hsivonen/encoding_rs` @ `e89b7c3371bffe0c260c76a11f32b8a7b6adad4a` | `Cargo.toml` (`L1–66`); `src/utf_8.rs` (`L34–165`, `L167–330`, `L551–925`); `src/ascii.rs` (`L189–277`); `src/simd_funcs.rs` (`L288–410`, `L474–549`); `src/mem.rs` (`L1345–1445`, `L2266–2309`) |
| **`quiche` (`octets` `0.3.7`)** | `cloudflare/quiche` @ `d448b6b239652b09e81c8dde883b98cd5827c31f` | `octets/Cargo.toml` (`L1–17`); `octets/src/lib.rs` (`L207–232`, `L509–576`, `L802–827`) |
| **`ciborium` `0.2.2` & `serde` `1.0.229`** | `enarx/ciborium` @ `00279e48e75ecf9546aae36f6d004447c676065b`; `serde-rs/serde` @ `e306b0c7c40ad21d5bdf52bcd20da513904682ae` | `ciborium/src/value/canonical.rs` (`L11–186`); `value/mod.rs` (`L21–52`); `value/integer.rs` (`L35–94`); `ciborium-ll/src/hdr.rs` (`L78–173`); `serde/Cargo.toml` (`L1–62`) |
| **Anneal & Lean `v4.34.1`** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/Trusted/MirSemantics.lean` (`L1646–1706`) |
| **Specs & Literature** | `10.17487/RFC3629`; `10.1002/spe.2920`; `10.17487/RFC9000`; `10.17487/RFC8949`; USENIX Sec'19 (`978-1-939133-06-9`); `10.1145/3341686` | Yergeau (RFC 3629); Keiser & Lemire (2021); Iyengar & Thomson (RFC 9000); Bormann & Hoffman (RFC 8949); Ramananandro et al.; Delaware et al. |

### Standalone Executable Probe 1 (`CPython 3.13.15`, `x86_64`, `2026-11-20`)

```python
UTF8_TABLE = (
    [252] * 128 + [84] * 16 + [148] * 16 + [164] * 32 + [252] * 64
    + [4] * 64 + [8] * 30 + [4, 4] + [16] + [8] * 12 + [32] + [8] * 2
    + [64] + [8] * 3 + [128] + [4] * 11
)
assert len(UTF8_TABLE) == 384

def spec3(b0: int, b1: int, b2: int) -> bool:
    if not (0x80 <= b2 <= 0xBF): return False
    return (0xA0 <= b1 <= 0xBF) if b0 == 0xE0 else ((0x80 <= b1 <= 0x9F) if b0 == 0xED else (0x80 <= b1 <= 0xBF and 0xE1 <= b0 <= 0xEF))

def spec4(b0: int, b1: int, b2: int, b3: int) -> bool:
    if not (0x80 <= b2 <= 0xBF and 0x80 <= b3 <= 0xBF): return False
    return (0x90 <= b1 <= 0xBF) if b0 == 0xF0 else ((0x80 <= b1 <= 0x8F) if b0 == 0xF4 else (0x80 <= b1 <= 0xBF and 0xF1 <= b0 <= 0xF3))

c3 = sum(1 for b0 in range(0xE0, 0xF0) for b1 in range(256) for b2 in [0, 0x40, 0x80, 0xC0]
         if (((UTF8_TABLE[b1] & UTF8_TABLE[b0 + 0x80]) | (b2 >> 6)) == 2) == spec3(b0, b1, b2))
c4 = sum(1 for b0 in range(0xF0, 0x100) for b1 in range(256) for b2 in [0, 0x40, 0x80, 0xC0] for b3 in [0, 0x40, 0x80, 0xC0]
         if (((UTF8_TABLE[b1] & UTF8_TABLE[b0 + 0x80]) | (b2 >> 6) | ((b3 & 0xC0) << 2)) == 0x202) == spec4(b0, b1, b2, b3))
assert (c3, c4) == (16384, 65536)

def simd_u16_to_u8(src: list[int], dst: bytearray, resv: int) -> tuple[int, int]:
    r = w = 0
    while True:
        cap = max(0, len(dst) - resv)
        if w >= cap: break
        rem, na = min(len(src) - r, cap - w), None
        while rem >= 16:
            for l in range(16): dst[w + l] = min(src[r + l], 0xFF)
            bad = next((l for l in range(16) if src[r + l] >= 0x80), None)
            if bad is not None: r += bad; w += bad; na = src[r]; break
            r += 16; w += 16; rem -= 16
        if na is None:
            while rem > 0:
                if src[r] >= 0x80: na = src[r]; break
                dst[w] = src[r]; r += 1; w += 1; rem -= 1
        if na is None or w + 4 > len(dst): break
        u = na; r += 1
        if u < 0x800: dst[w : w + 2] = bytes([(u >> 6) | 0xC0, (u & 0x3F) | 0x80]); w += 2
        elif not (0xD800 <= u <= 0xDFFF): dst[w : w + 3] = bytes([(u >> 12) | 0xE0, ((u >> 6) & 0x3F) | 0x80, (u & 0x3F) | 0x80]); w += 3
        elif u <= 0xDBFF and r < len(src) and 0xDC00 <= src[r] <= 0xDFFF:
            a = (u << 10) + src[r] - (((0xD800 << 10) - 0x10000) + 0xDC00); r += 1
            dst[w : w + 4] = bytes([(a >> 18) | 0xF0, ((a >> 12) & 0x3F) | 0x80, ((a >> 6) & 0x3F) | 0x80, (a & 0x3F) | 0x80]); w += 4
        else: dst[w : w + 3] = b"\xef\xbf\xbd"; w += 3
    while r < len(src):
        u = src[r]
        if u < 0x80:
            if w + 1 > len(dst): break
            dst[w] = u; r += 1; w += 1
        elif u < 0x800:
            if w + 2 > len(dst): break
            dst[w : w + 2] = bytes([(u >> 6) | 0xC0, (u & 0x3F) | 0x80]); r += 1; w += 2
        elif 0xD800 <= u <= 0xDBFF and r + 1 < len(src) and 0xDC00 <= src[r + 1] <= 0xDFFF:
            if w + 4 > len(dst): break
            a = (u << 10) + src[r + 1] - (((0xD800 << 10) - 0x10000) + 0xDC00)
            dst[w : w + 4] = bytes([(a >> 18) | 0xF0, ((a >> 12) & 0x3F) | 0x80, ((a >> 6) & 0x3F) | 0x80, (a & 0x3F) | 0x80]); r += 2; w += 4
        else:
            if w + 3 > len(dst): break
            dst[w : w + 3] = bytes([(u >> 12) | 0xE0, ((u >> 6) & 0x3F) | 0x80, (u & 0x3F) | 0x80]) if not (0xD800 <= u <= 0xDFFF) else b"\xef\xbf\xbd"
            r += 1; w += 3
    return (r, w)

simd_ok = 0
for seq in [[0x00CA], [0x4E00], [0xD83D, 0xDCA9]]:
    for pfx in range(36):
        s = [ord("a")] * pfx + seq + [ord("b")] * 20
        for dlen in range(60):
            d = bytearray(b"q" * dlen)
            _, w = simd_u16_to_u8(s, d, 3)
            assert all(b == ord("q") for b in d[w:]) and d.decode("utf-8") is not None
            simd_ok += 1

dst_ub = bytearray(b"q" * 18)
_, w_ub = simd_u16_to_u8([ord("a")] * 15 + [0xD83D, 0xDCA9], dst_ub, 2)
assert w_ub == 15 and dst_ub[15] == 0xFF

def q_get(buf: bytes) -> int:
    ln = 1 << (buf[0] >> 6)
    return int.from_bytes(buf[:ln], "big") & {1: 0x3F, 2: 0x3FFF, 4: 0x3FFFFFFF, 8: 0x3FFFFFFFFFFFFFFF}[ln]

def q_put_len(v: int, ln: int) -> bytes:
    raw = bytearray((v & ((1 << (8 * ln)) - 1)).to_bytes(ln, "big"))
    raw[0] |= {1: 0, 2: 0x40, 4: 0x80, 8: 0xC0}[ln]
    return bytes(raw)

assert all(q_get(x) == 5 for x in [b"\x05", b"\x40\x05", b"\x80\x00\x00\x05", b"\xc0\x00\x00\x00\x00\x00\x00\x05"])
assert q_put_len(0x8000, 2) == b"\xc0\x00"

def enc_cbor(v) -> bytes:
    def hdr(m: int, n: int) -> bytes:
        return bytes([(m << 5) | n]) if n <= 23 else (bytes([(m << 5) | 24, n]) if n <= 0xFF else bytes([(m << 5) | 25]) + n.to_bytes(2, "big"))
    return (hdr(0, v[1]) if v[1] >= 0 else hdr(1, -1 - v[1])) if v[0] == "int" else hdr(6, v[1]) + enc_cbor(v[2])

def cib_cmp(v1, v2) -> int:
    if v1[0] == "tag" and v2[0] == "tag" and v1[1] != v2[1]: return -1 if v1[1] < v2[1] else 1
    b1, b2 = enc_cbor(v1), enc_cbor(v2)
    return -1 if (len(b1), b1) < (len(b2), b2) else int((len(b1), b1) > (len(b2), b2))

v1, v2, v3 = ("tag", 2, ("int", 1000)), ("tag", 3, ("int", 1)), ("int", 256)
assert enc_cbor(("int", 256)) < enc_cbor(("int", -1)) and cib_cmp(("int", -1), ("int", 256)) == -1
assert cib_cmp(v1, v2) == -1 and cib_cmp(v2, v3) == -1 and cib_cmp(v3, v1) == -1
print("PROBE_WIRE_OK", {"utf8_3": c3, "utf8_4": c4, "simd_ok": simd_ok, "ub_byte": hex(dst_ub[15]), "ord_cycle": True})
```

Observed output (`2026-11-20`, `CPython 3.13.15`):
`PROBE_WIRE_OK {'utf8_3': 16384, 'utf8_4': 65536, 'simd_ok': 6480, 'ub_byte': '0xff', 'ord_cycle': True}`

## Revalidation

1. **Upstream diffs**: Diff `encoding_rs` (`src/{utf_8,simd_funcs,mem}.rs` vs `e89b7c3371bffe0c260c76a11f32b8a7b6adad4a`), `quiche` (`octets/src/lib.rs` vs `d448b6b239652b09e81c8dde883b98cd5827c31f`), and `ciborium` (`ciborium/src/value/canonical.rs` vs `00279e48e75ecf9546aae36f6d004447c676065b`).
2. **Lean `v4.34.1` kernel audit**: Check Section 4's `Anneal.Codec.StrictBijection` module with `lean -DElab.async=false -Ddebug.skipKernelTC=false` (`0` errors, `0` `sorry`, axioms $\subseteq \{\texttt{propext}\}$).
3. **Executable probe**: Run Python 3 (`>= 3.10`) on **Standalone Executable Probe 1** (`< 0.3 s`) and verify `PROBE_WIRE_OK` exits `0`.
