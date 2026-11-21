# Dual-Context Bitstream Transcoding Lenses, Overflow-Free Rational Timestamp Rescaling, and ISO BMFF Chunk-Offset Relocation

## Summary

Formal verification of stateful container and elementary-bitstream transcoding pipelines—spanning `CodedBitstream` (`cbs_*`) syntax filters, rational presentation/decoding timestamp (`PTS`/`DTS`) rescaling, and ISO Base Media File Format (`ISOBMFF` / `MP4`) `faststart` relocation—requires three abstractions beyond stateless parser-serializer combinators:

1. **Dual-Context Parameterized Transcoding Optics Over $(S_{\text{in}}, S_{\text{out}})$ (`Basis: normative + source + derived + execution`):**
   Classical lenses (`Foster et al.`, `doi:10.1145/1232420.1232424`) and single-context dependent combinators (`Bind<A, B>` in `secure-foundations/vest@026867a37d4b918153058df2c8db6c52fc62ba35`, `project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`) share a single grammar state $S$ across parse and serialize. When a bitstream filter rewrites an `SPS` or `PPS` header ($S_{\text{in}} \mapsto S_{\text{out}}$), subsequent upstream packets remain encoded against $S_{\text{in}}$ while downstream packets must serialize against $S_{\text{out}}$. `FFmpeg/FFmpeg@e8574d0b22b126acc76007babce536c68bc07d0a` (`libavcodec/cbs_bsf.c:97-189`, `libavcodec/bsf/h264_redundant_pps.c:39-101`) resolves this via twin contexts `(CBSBSFContext.input, CBSBSFContext.output)` paired with `AVRefStruct` copy-on-write (`ff_cbs_make_unit_writable`, `cbs.c:1032-1047`). Categorically, lawful header-rewriting filters are **state-indexed parameterized quotient lenses** coupled by a simulation relation $R \subseteq \mathcal{S} \times \mathcal{S}$, factored cleanly above a strict 3-state `0x000003` RBSP byte-stuffing bijection with tight expansion $|\text{escape}(p)| \le \lfloor 3|p|/2 \rfloor$.
2. **Overflow-Free `u64 * u64 / u64` vs. Signed `int64_t` Rational Timestamp Rescaling (`Basis: source + derived + execution`):**
   `FFmpeg`'s 64-step 128-by-64 divider in `av_rescale_rnd` (`libavutil/mathematics.c:94-117`) is overflow-sound on signed $0 \le a, b \le 2^{63}-1, 1 \le c \le 2^{63}-1$ *despite intermediate `a1` wraparound modulo $2^{64}$* because step `i = 63` never wraps ($2 a_1 + b_{63} \le 2^{63}-1$) and permanently latches bit `63` of `t1` (`> INT64_MAX`) whenever the true quotient $Q \ge 2^{64}$. Porting that limb code to unsigned `u64 * u64 / u64` breaks three ways (`a0*b1 + a1*b0` carry wrap, `2*a1` remainder wrap for $c \ge 2^{63}$, and loss of bit `63` as overflow sentinel). Sound `u64` rescaling forms $N = (a : \text{u128}) \cdot b + r \le 2^{128} - 2^{64} - 1 < 2^{128}$ and checks `(N >> 64) as u64 >= c` prior to division. Source audit and execution also expose a `+1`-tick clamp on `a == INT64_MIN` without `AV_ROUND_PASS_MINMAX` (`-FFMAX(INT64_MIN, -INT64_MAX)` at `mathematics.c:75`) and non-compositionality of chained rescaling.
3. **Finite-Lattice Kleene Fixed Point for ISO BMFF `stco`/`co64` Relocation (`Basis: normative + source + derived + execution`):**
   Relocating `moov` ahead of `mdat` shifts chunk offsets by $\Delta(u) = M_0 + \sum_{k=0}^{K-1} 4 C_k u_k$, where $u \in \{0, 1\}^K$ tracks `stco` $\to$ `co64` promotion (`ISO/IEC 14496-12:2022` §8.7.5). Monotonicity of $T(u)_k = \mathbf{1}[P_k + \Delta(u) > 2^{32}-1]$ on $(\{0, 1\}^K, \le)$ guarantees Kleene convergence to the unique size-minimal fixed point $u^* = \mu u.\, T(u)$ in $\le K + 1$ steps (and $O(K \log K)$ via sorted thresholds). `movenc.c:9289-9312` (`compute_moov_size`) truncates at 2 evaluations—overwriting `mdat` on depth-$\ge 2$ cascades—whereas `tools/qt-faststart.c:372-428` computes the sound post-fixed point $u = \mathbf{1}$ via $(\mathbb{Z}/2^{32}\mathbb{Z}, +)$ inversion (`line 321`) while omitting `saio` (§8.7.13), `iloc` (§8.11.3), and `tfhd` (§8.8.7) file-offset tables.

---

## Applicability

This report governs formal specification, verified parser-serializer combinator design, and mechanized soundness proofs for media bitstream filtering, timestamp rescaling, and ISO BMFF container relocation across eight pinned primary subjects:

- **`FFmpeg/FFmpeg`** at `e8574d0b22b126acc76007babce536c68bc07d0a` (`libavcodec/cbs.c`, `cbs_bsf.{h,c}`, `cbs_h2645.c`, `cbs_h264_syntax_template.c`, `bsf/h264_redundant_pps.c`, `libavutil/mathematics.{h,c}`, `libavformat/movenc.c`, `tools/qt-faststart.c`);
- **`secure-foundations/vest`** at `026867a37d4b918153058df2c8db6c52fc62ba35` (`vest_lib/src/core/{spec,proof}.rs`, `combinators/tuple/{mod,spec}.rs`; Cai et al., USENIX Security 2025) and **`project-everest/everparse`** at `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` (Ramananandro et al., USENIX Security 2019), alongside **Narcissus** (`Delaware et al.`, `doi:10.1145/3341686`);
- **ITU-T Rec. H.264 (08/2024)** (§§7.3.1–7.3.3, 7.4.1), **ISO/IEC 14496-12:2022** (§§4.2, 8.7.5, 8.7.13, 8.8.7, 8.11.3), and bidirectional/profunctor optics (`Foster et al.`, `doi:10.1145/1232420.1232424` & `doi:10.1145/1411203.1411257`; `Pickering, Gibbons, and Wu`, `doi:10.22152/programming-journal.org/2017/1/7`; `Clarke et al.`, `doi:10.32408/compositionality-6-1`).

**Companion corpus cross-references:** Subsystem inventories of FFmpeg's parsers, BSFs, and muxers appear in `ffmpeg-coded-bitstream-cbs-bitstream-filters-bsf-parsers-and-side-data-lenses` and `isobmff-matroska-mpegts-hls-dash-muxers-interleaving-faststart-and-cenc-crypto`; stateless partial isomorphisms and profunctor optics appear in `codec-round-trip-laws-and-partial-isomorphisms`, `everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs`, and `profunctor-optics-prisms-affine-traversals-and-enum-slice-reborrows`. This report establishes the formal dual-context transcoding laws, 128-bit rescaling invariants, and finite-lattice relocation proofs omitted from those surveys.

---

## Findings

### 1. Why Single-Context Bidirectional Lenses Fail Under Parameter-Set Rewriting $(S_{\text{in}} \to S_{\text{out}})$

`Basis: normative + source + derived + execution`

#### 1.1 Structural Limits of Single-Context Dependent Combinators (`Vest`, `EverParse`, `Narcissus`)

In classical bidirectional lenses (`Foster et al.`, `doi:10.1145/1232420.1232424`) and verified format combinators (`secure-foundations/vest@026867a37d4b918153058df2c8db6c52fc62ba35` `vest_lib/src/core/proof.rs:24-174`; `project-everest/everparse@f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`; `Narcissus`, `doi:10.1145/3341686`), a non-malleable codec for $A$ obeys `SPRoundTrip` ($\text{consistent}(v) \implies \text{parse}(\text{ser}(v)) = \text{Some}(|\text{ser}(v)|, v)$) and `PSRoundTrip` ($\text{parse}(b) = \text{Some}(n, v) \implies \text{ser}(v) = b[0..n]$). Intra-packet context dependency is modeled in `Vest` (`vest_lib/src/combinators/tuple/spec.rs:185-196, 282-285`) via `Bind<A, B>`:

```rust
open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
    match self.0.spec_parse(ibuf) {
        Some((n1, key)) => self.1.spec_map(key).spec_parse(ibuf[n1..])
            .map(|(n2, val)| (n1 + n2, (key, val))),
        None => None,
    }
}
open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
    let (key, val) = value;
    self.0.spec_serialize_dps(key, self.1.spec_map(key).spec_serialize_dps(val, obuf))
}
```

Both directions apply the **identical** continuation `self.1.spec_map(key)` to a single `key` within one buffer. Elementary video bitstreams (`ITU-T H.264` §§7.3.2–7.3.3, `H.265`, `H.266`, `AV1`) violate both premises:
1. **Cross-packet state persistence:** `SPS` (`0..31`) and `PPS` (`0..255`) tables persist across access units in `CodedBitstreamH264Context`; slices reference them indirectly by integer ID (`pic_parameter_set_id`), determining bit-widths (`frame_num` width `sps->log2_max_frame_num_minus4 + 4` at `cbs_h264_syntax_template.c:1121`) and subtree presence (`pred_weight_table()` gated by `pps->weighted_pred_flag` at `lines 1192-1194`).
2. **Reader/writer environment split ($S_{\text{in}} \ne S_{\text{out}}$):** Once a BSF rewrites a parameter set at $t_0$ ($P_{\text{in}} \mapsto P_{\text{out}}$), upstream packets at $t_1, t_2, \dots$ are still bit-packed under $P_{\text{in}}$, whereas serialized packets emitted downstream must be bit-packed under $P_{\text{out}}$.

#### 1.2 Production Failure Witness in `libavcodec/bsf/h264_redundant_pps.c`

`FFmpeg`'s `h264_redundant_pps` filter (`libavcodec/bsf/h264_redundant_pps.c:39-101`) demonstrates why any single-context codec $(S, \text{parse}_S, \text{ser}_S)$ fails:
- `h264_redundant_pps_fixup_pps` (`lines 39-62`) sets `pps->pic_init_qp_minus26 = 0` (`NEW_GLOBAL_PIC_INIT_QP - 26`) and **`pps->weighted_pred_flag = 1`** (`line 59`), while `h264_redundant_pps_fixup_slice` (`lines 64-76`) adjusts every slice's `slice_qp_delta` using the **unmutated input context**:
  ```c
  const CodedBitstreamH264Context *const in = ctx->common.input->priv_data;
  const H264RawPPS *const pps = in->pps[slice->pic_parameter_set_id];
  slice->slice_qp_delta += pps->pic_init_qp_minus26 - (NEW_GLOBAL_PIC_INIT_QP - 26);
  ```
- On a 2-packet input `pkt1 = [PPS(id=0, wp=0, init_qp=+8), P_SLICE(pps=0, qp_delta=-2)]`, `pkt2 = [P_SLICE(pps=0, qp_delta=+1)]` (encoded without `pred_weight_table` bits since `wp == 0`):
  - **Single-context $S$ failure:** Updating `S.pps[0]` during `pkt1` sets `S.pps[0].weighted_pred_flag = 1` and `init_qp = 0`. Parsing `pkt2` under $S$ then executes `pred_weight_table()` (`cbs_h264_syntax_template.c:1192-1194`) over macroblock payload bits (raising `AVERROR_INVALIDDATA` or desynchronizing entropy decoding) and adds `0` instead of `+8` to `slice_qp_delta` (`-8` QP error).
  - **Mandatory `AVRefStruct` Copy-on-Write (`cbs.c:1032-1047`):** Because `cbs_h2645` initially shares the parsed `H264RawPPS` allocation between `unit->content` and `ctx->input->priv_data->pps[0]`, `h264_redundant_pps.c:48` must call `ff_cbs_make_unit_writable(ctx->common.input, unit)` before mutating `unit->content`; omitting that clone mutates `in->pps[0]` in place and recreates the single-context failure inside a nominally dual-context filter.

---

### 2. Indexed Parameterized Quotient Lenses and Strict `0x000003` RBSP Factoring

`Basis: normative + derived + execution`

#### 2.1 Three-Layer Factorization and Strict `0x000003` RBSP Bijection

`CodedBitstream` conflates container framing (`AVCC` length prefixes vs. Annex B start codes), RBSP emulation-prevention byte stuffing, and parameter-set AST encoding into one pass. Factoring these into three layers restores exact compositional laws:

$$\text{Packet} \;\underset{\mathcal{L}_{\text{frame}}}{\longleftrightarrow}\; \text{List}\langle\text{EBSP}\rangle \;\underset{\text{escape}}{\stackrel{\text{unescape}_{\text{strict}}}{\longleftrightarrow}}\; \text{List}\langle\text{RBSP}\rangle \;\underset{\text{put}_{S_{\text{out}}}}{\stackrel{\text{get}_{S_{\text{in}}}}{\longleftrightarrow}}\; \text{Frag}\langle A\rangle$$

Under `ITU-T Rec. H.264` §§7.3.1, 7.4.1, `EBSP` forbids `0x00 0x00 {0x00, 0x01, 0x02}`, unescaped `0x00 0x00 0x03`, and trailing `0x00 0x00 0x03`. Let $z \in \{0, 1, 2\}$ count consecutive `0x00` bytes:
- **$\text{escape}(p)$:** From $z = 0$, for each $b \in p$: if $z = 2 \land b \le 3$, emit `0x03` and set $z \leftarrow 0$; emit $b$ and set $z \leftarrow (z + 1 \text{ if } b = 0 \text{ else } 0)$.
- **$\text{unescape}_{\text{strict}}(e)$:** From $z = 0$, at $e[i]$: if $z = 2 \land e[i] \in \{0, 1, 2\}$, return `None`; if $z = 2 \land e[i] = 3$, require $i + 1 < |e| \land e[i+1] \le 3$ (else `None`), emit $e[i+1]$, set $z \leftarrow (1 \text{ if } e[i+1] = 0 \text{ else } 0)$, and $i \mathrel{+}= 2$; else emit $e[i]$, set $z \leftarrow (z + 1 \text{ if } b = 0 \text{ else } 0)$, and $i \mathrel{+}= 1$.

Four exact properties hold (verified exhaustively over all $0..4$-byte words in §Evidence):
1. **Total `PutGet` & Non-Malleable `GetPut`:** $\text{unescape}_{\text{strict}}(\text{escape}(p)) = \text{Some}(p)$ and $\text{unescape}_{\text{strict}}(e) = \text{Some}(p) \implies \text{escape}(p) = e$.
2. **Lenient `GetPut` Failure:** Stripping `0x03` before `>= 0x04` maps `[0x00, 0x00, 0x03, 0x04] -> Some([0x00, 0x00, 0x04])`, whose re-encoding `[0x00, 0x00, 0x04]` shrinks byte length by `1`—satisfying only quotient `GetPut` (`Foster, Pilkiewicz, and Pierce`, `doi:10.1145/1411203.1411257`) and breaking external CENC `senc` subsample byte counts unless recomputed.
3. **Tight $\lfloor 3n/2 \rfloor$ Expansion Bound:** Potential induction on $2|\text{out}| + z_{\text{out}} \le 3|\text{in}| + z_{\text{in}}$ yields $|\text{escape}(p)| \le \lfloor 3|p|/2 \rfloor$ (achieved at $p = [0, 0, 0, 0, 0] \mapsto [0, 0, 3, 0, 0, 3, 0]$ of length $7 = \lfloor 15/2 \rfloor$, matching `cbs_h2645.c:340`'s `4 + unit->data_size * 3 / 2`).

#### 2.2 Parameterized Optics and Simulation-Coupled Transducer Soundness

In profunctor/categorical optics (`Pickering, Gibbons, and Wu`, `doi:10.22152/programming-journal.org/2017/1/7`; `Clarke et al.`, `doi:10.32408/compositionality-6-1`), a polymorphic adapter $\text{Optic}((S_{\text{in}} \times B_{\text{in}}, S'_{\text{out}} \times B_{\text{out}}), (S'_{\text{in}} \times A_{\text{in}}, S_{\text{out}} \times A_{\text{out}}))$ separates input and output state indices. Modeling parameter-set stores $\mathcal{S}$ as persistent functional maps eliminates C aliasing (`make_unit_writable`) by construction. Each index $S \in \mathcal{S}$ defines $(\text{get}_S : \text{RBSP} \rightharpoonup S \times A,\; \text{put}_S : A \rightharpoonup S \times \text{RBSP})$ obeying **Indexed `PutGet`** ($\text{put}_S(a) = \text{Some}(S', b) \implies \text{get}_S(b) = \text{Some}(S', a)$) and **Indexed Quotient `GetPut`** ($\text{get}_S(b) = \text{Some}(S', a) \implies \exists b_c \sim_S b,\; \text{put}_S(a) = \text{Some}(S', b_c)$).

Given codec semantics $\text{sem} : \mathcal{S} \times A \rightharpoonup \mathcal{V}$ and AST filter $\tau : \mathcal{S} \times \mathcal{S} \times A \rightharpoonup A$, a **Dual-Context Bitstream Filter** $\text{step}_\tau(S_{\text{in}}, S_{\text{out}}, b_{\text{in}})$ parses $(S'_{\text{in}}, a_{\text{in}}) \leftarrow \text{get}_{S_{\text{in}}}(b_{\text{in}})$, transforms $a_{\text{out}} \leftarrow \tau(S'_{\text{in}}, S_{\text{out}}, a_{\text{in}})$, and serializes $(S'_{\text{out}}, b_{\text{out}}) \leftarrow \text{put}_{S_{\text{out}}}(a_{\text{out}})$.

**Theorem (Simulation-Coupled Transcoding Soundness):** If a relation $R \subseteq \mathcal{S} \times \mathcal{S}$ holds after extradata initialization (`cbs_bsf.c:167-183`) and for every $(S_{\text{in}}, S_{\text{out}}) \in R$ and $\text{get}_{S_{\text{in}}}(b_{\text{in}}) = \text{Some}(S'_{\text{in}}, a_{\text{in}})$: (1) $\tau(S'_{\text{in}}, S_{\text{out}}, a_{\text{in}}) = \text{Some}(a_{\text{out}}) \in \text{dom}(\text{put}_{S_{\text{out}}})$ yielding $(S'_{\text{out}}, b_{\text{out}})$, (2) $(S'_{\text{in}}, S'_{\text{out}}) \in R$, and (3) $\text{sem}(S'_{\text{out}}, a_{\text{out}}) = g(\text{sem}(S'_{\text{in}}, a_{\text{in}}))$, then **by Indexed `PutGet` on $S_{\text{out}}$**, any compliant downstream decoder starting at $S_{\text{out}}$ parses $\text{get}_{S_{\text{out}}}(b_{\text{out}}) = \text{Some}(S'_{\text{out}}, a_{\text{out}})$, preserves $(S'_{\text{in}}, S'_{\text{out}}) \in R$ across arbitrary packet sequences, and reconstructs $g(\text{sem}(S'_{\text{in}}, a_{\text{in}}))$. For `BSF_ELEMENT_PASS` ($\tau = \text{id}$), $R$ restricts to the diagonal $S_{\text{in}} = S_{\text{out}}$ and recovers standard single-context round-tripping.

---

### 3. Overflow-Free `u64 * u64 / u64` vs. Signed `int64_t` Rational Timestamp Rescaling

`Basis: source + derived + execution`

#### 3.1 `FFmpeg` `av_rescale_rnd` (`libavutil/mathematics.c:58-145`): Boundary Clamp & Step-63 MSB Proof

`av_rescale_q_rnd(a, bq, cq, rnd)` (`mathematics.c:134-140`) computes `int64_t b = bq.num * (int64_t)cq.den; int64_t c = cq.num * (int64_t)bq.den;` (never overflowing `int64_t` since $(-2^{31})^2 = 2^{62} \le \text{INT64\_MAX}$, though negative rationals yield $b < 0$ or $c \le 0 \mapsto \text{INT64\_MIN}$) and calls `av_rescale_rnd(a, b, c, rnd)`:

| `enum AVRounding` | Code | Bias $r$ ($a \ge 0$) | Exact Mathematical Rule ($x = ab/c$) | Sign-Flip `rnd ^ ((rnd >> 1) & 1)` (`line 75`) |
| :--- | :---: | :---: | :--- | :--- |
| `AV_ROUND_ZERO` | `0` | $0$ | $\operatorname{sgn}(x)\lfloor |x| \rfloor$ | `0` (invariant) |
| `AV_ROUND_INF` | `1` | $c - 1$ | $\operatorname{sgn}(x)\lceil |x| \rceil$ | `1` (invariant) |
| `AV_ROUND_DOWN` | `2` | $0$ | $\lfloor x \rfloor$ ($-\infty$) | `3` (`AV_ROUND_UP`: $-\lceil |x| \rceil = \lfloor -|x| \rfloor$) |
| `AV_ROUND_UP` | `3` | $c - 1$ | $\lceil x \rceil$ ($+\infty$) | `2` (`AV_ROUND_DOWN`: $-\lfloor |x| \rfloor = \lceil -|x| \rceil$) |
| `AV_ROUND_NEAR_INF` | `5` | $\lfloor c/2 \rfloor$ | $\operatorname{sgn}(x)\lfloor |x| + \tfrac{1}{2} \rfloor$ | `5` (invariant; code `4` rejected at `L65`) |

Two exact properties govern `libavutil/mathematics.c:68-118`:
1. **`INT64_MIN` `+1` Clamp Without `AV_ROUND_PASS_MINMAX` (`line 75`):** `if (a < 0) return -(uint64_t)av_rescale_rnd(-FFMAX(a, -INT64_MAX), b, c, ...);` clamps `a == INT64_MIN` (`-2^{63}`) to `-INT64_MAX` (`-(2^{63}-1)`), causing `av_rescale_rnd(INT64_MIN, 1, 1, AV_ROUND_ZERO)` to return `-9223372036854775807` (`INT64_MIN + 1`) unless `AV_ROUND_PASS_MINMAX` is set.
2. **Why the 64-Step 128-by-64 Loop (`lines 94-117`) Is Sound on $0 \le a, b \le 2^{63}-1, 1 \le c \le 2^{63}-1$ Despite `a1` Wraparound:**
   When `b > INT_MAX || c > INT_MAX`, `lines 98-105` compute `(a1 : a0) = a * b + r` (`t1 = a0*b1 + a1*b0 <= 2(2^{32}-1)(2^{31}-1) < 2^{64}`, zero carry loss), leave `t1` unzeroed, and run 64 iterations (`i = 63..0`) of `a1 += a1 + ((a0 >> i) & 1); t1 += t1; if (c <= a1) { a1 -= c; t1++; }`. Even though `a1 += a1` wraps modulo $2^{64}$ when $Q = \lfloor (ab+r)/c \rfloor \ge 2^{64}$ (e.g., at `i = 60` for $a = 23 \cdot 2^{58}, b = 2^{62}, c = 2^{59}$, `a1` wraps to `0`), `t1` undergoes 64 carry-free left shifts that evict all old `t1` bits and place the bit decided at **`i = 63`** permanently at **bit `63`** of final `t1`. Since $ab + r \le (2^{63}-1)^2 + (2^{63}-2) < 2^{126}$, initial $a_1 \le 2^{62}-1$, so at `i = 63` $2a_1 + b_{63} \le 2^{63}-1 < 2^{64}$ **never wraps**. Whenever $Q \ge 2^{64}$, $2a_1 + b_{63} = \lfloor (ab+r)/2^{63} \rfloor \ge 2c > c$, setting `t1` bit `0` to `1` at `i = 63` and guaranteeing final `t1 >= 2^{63} > INT64_MAX -> INT64_MIN`; whenever $Q < 2^{64}$, $a_1 < c \le 2^{63}-1$ prevents `a1` wrap at every step (`2(c-1)+1 < 2^{64}`) and yields exact `t1 = Q`.

#### 3.2 Unsigned `u64 * u64 / u64` Contract and Chained Non-Compositionality

Generalizing `FFmpeg`'s limb loop to unsigned `a, b, c: u64` ($c \ge 1$) fails three ways: (1) `a0*b1 + a1*b0` wraps `u64` when $a, b \ge 2^{63}$; (2) for $c = 2^{63}+1$ and valid remainder $a_1 = 2^{63} < c$, `2*a1` wraps `u64` to `0`; and (3) bit `63` is a valid `u64` output bit, not an overflow flag. Instead, verified `u64` rescaling uses:
- **Exact `u128` Non-Overflow:** For all $a, b \le 2^{64}-1$ and $0 \le r \le c - 1 \le 2^{64}-2$, $N = a \cdot b + r \le (2^{64}-1)^2 + (2^{64}-2) = 2^{128} - 2^{64} - 1 < \texttt{u128::MAX}$.
- **Single-Guard Quotient Overflow Check:** $Q = \lfloor N/c \rfloor \ge 2^{64} \iff \lfloor N/2^{64} \rfloor \ge c$ (`(N >> 64) as u64 >= c`), which simultaneously guards x86-64 hardware `DIV r64` against `#DE` (`RDX >= divisor`).
- **Monotonicity vs. Non-Associativity:** Single-step rescaling is monotone ($a_1 \le a_2 \implies \text{rescale}(a_1) \le \text{rescale}(a_2)$ across all 5 rounding modes), whereas chained rescaling fails associativity ($t = 44$ from `1/90000 -> 1/1000 -> 1/48000` rounds $44 \mapsto 0 \mapsto 0$ vs. direct $23$).

---

### 4. ISO BMFF `stco` / `co64` Chunk-Offset Relocation Invariants (`faststart`)

`Basis: normative + source + derived + execution`

In progressive MP4/ISOBMFF (`ISO/IEC 14496-12:2022` §8.7.5), `stco` (32-bit) and `co64` (64-bit) store file-origin byte offsets into `mdat`. Moving `moov` ahead of `mdat` shifts every chunk offset by $|\text{moov}'|$, preserving chunk slices $\text{file}'[\text{off}_{k,j} + \Delta .. + \text{len}_{k,j}) = \text{file}[\text{off}_{k,j} .. + \text{len}_{k,j})$ iff $p_{\text{ins}} \le \text{off}_{k,j}$ and $|\text{moov}'| = \Delta$.

For $K$ `stco`-eligible streams with chunk counts $C_k$ and maximum pre-shift chunk offset $P_k = \max_j \text{off}_{k,j}$, let $u \in \{0, 1\}^K$ denote promotion to `co64` ($+4 C_k$ bytes per promoted stream, base `moov` size $M_0$):

$$\Delta(u) = M_0 + \sum_{k=0}^{K-1} 4 C_k u_k, \qquad T(u)_k = \mathbf{1}\bigl[\,P_k + \Delta(u) > 2^{32} - 1\,\bigr]$$

Because $T$ is monotone on the finite lattice $(\{0, 1\}^K, \le)$ of height $K$, Kleene iteration $u^{(0)} = \mathbf{0}, u^{(m+1)} = T(u^{(m)})$ reaches the **unique least fixed point** $u^* = \mu u.\, T(u)$ in $\le K + 1$ evaluations—and sorting streams by descending $P_{\pi(0)} \ge \dots \ge P_{\pi(K-1)}$ computes $u^*$ in **$O(K \log K)$ time** in a single scan (stopping at the first $r$ with $P_{\pi(r)} + \Delta \le 2^{32}-1$).

| Implementation | Vector $u$ | Post-Fixed ($T(u) \le u$)? | Minimal ($u = u^*$)? | Exact Behavior & Secondary Box Hazards |
| :--- | :--- | :---: | :---: | :--- |
| **`movenc.c:9289-9312`** (`compute_moov_size`) | Hardcoded 2-step unroll | **NO** ($K \ge 2$) | No | Shifts `mdat` by $\Delta(u^{(1)})$ while `mov_write_moov_tag` emits $\Delta(u^{(2)})$—**overwriting $4 \sum_{u^{(2)}_k > u^{(1)}_k} C_k$ leading bytes of `mdat`** on depth-$\ge 2$ cascades! |
| **`tools/qt-faststart.c:372-428`** (`update_moov_atom`) | $\mathbf{0}$ or $\mathbf{1}$ (all-or-nothing) | **YES** | Only if $u^* \in \{\mathbf{0}, \mathbf{1}\}$ | Sound over-approximation ($+4 \sum_{u^*_k = 0} C_k$ extra bytes); recovers wrapped pass-1 32-bit offsets via exact $(\mathbb{Z}/2^{32}\mathbb{Z}, +)$ subtraction `BE_32(pos) - original_moov_size` (`L321`). **Silently omits** file-origin offsets in CENC `saio` (§8.7.13), HEIF/AVIF `iloc` (`construction_method == 0`, §8.11.3), and explicit `tfhd` `base_data_offset` (§8.8.7)! |
| **Kleene / Sorted Thresholds** | $u^* = \mu u.\, T(u)$ | **YES** | **YES** | Exact minimum shift + fail-closed rejection (or joint promotion) of `saio`/`iloc`/`tfhd` file-offset boxes. |

---

## Boundaries

1. **Entropy-Coded Slice Payloads (`CABAC` / `msac` / VP8 Bool-Coder) (`unsupported` by `CodedBitstream` AST lenses):**
   Dual-context syntax lenses in §§1–2 cover byte/bit-aligned header and SEI/OBU grammars; rewriting macroblock/CTU syntax inside arithmetic-coded slice bodies without full decode/re-encode is **unsupported** (`cbs_vp8.c` returns `AVERROR_PATCHWELCOME` on write).
2. **Floating-Point Timestamp Expressions (`bsf/setts.c`) (`known not to apply`):**
   Exact integer monotonicity and overflow bounds in §3 **are known not to apply** to `FFmpeg`'s `setts` filter, which evaluates timestamps in IEEE-754 `binary64` (`av_expr_eval` + `llrint`), losing precision above $2^{53}$.
3. **64-Bit Extended Box Header Promotion (`largesize`, `size == 1`) Inside `moov` (`not examined` empirically):**
   Inputs where `stco -> co64` expansion pushes `moov` itself across `4 GiB` (`+8` bytes per promoted parent box header) were **not examined** in execution probes, though adding $+8 \cdot \mathbf{1}[\text{size}_{\text{box}}(u) > 2^{32}-1]$ preserves monotonicity of $\Delta(u)$ and Kleene fixed-point existence.
4. **Historical Intent of `-FFMAX(a, -INT64_MAX)` on `INT64_MIN` (`unknown`):**
   Whether `mathematics.c:75`'s `+1` clamp on `a == INT64_MIN` without `AV_ROUND_PASS_MINMAX` was a deliberate C89 signed-negation guard or an unintended boundary error on valid `-2^{63}` timestamps is **unknown** from repository comments.

---

## Evidence

### 1. Primary Source Code and Normative Citations (Observed 2026-11-21)

- **`FFmpeg/FFmpeg` (`e8574d0b22b126acc76007babce536c68bc07d0a`):**
  - `libavcodec/cbs_bsf.h:31-60`, `libavcodec/cbs_bsf.c:59-189` (`CBSBSFContext` twin `input`/`output` contexts, `ff_cbs_bsf_generic_filter` `L97-144`, `ff_cbs_bsf_generic_init` `L146-189`); `libavcodec/bsf/h264_redundant_pps.c:39-101` (`ff_cbs_make_unit_writable` `L48`, `weighted_pred_flag = 1` `L59`, `in->pps[...]` lookup `L67-73`).
  - `libavcodec/cbs.c:179-186, 1032-1047` (`ff_cbs_make_unit_writable`); `libavcodec/cbs_h264_syntax_template.c:326, 468, 471, 951, 1121, 1192-1194`; `libavcodec/cbs_h2645.c:245-251, 323-404` (`0x03` RBSP unescaping and `4 + unit->data_size * 3 / 2` sizing).
  - `libavutil/mathematics.c:58-189` (`av_rescale_rnd` `L58-127`, `av_rescale_q_rnd` `L134-140`, `av_compare_ts` `L147-158`, `av_rescale_delta` `L168-189`).
  - `libavformat/movenc.c:179-225, 9289-9342` (`co64_required`, `compute_moov_size`, `shift_data`); `tools/qt-faststart.c:185-428` (`update_stco_offsets`, `upgrade_stco_atom` modulo-$2^{32}$ subtraction `L321`).
- **Verified Combinators & Optics:** `secure-foundations/vest` (`026867a37d4b918153058df2c8db6c52fc62ba35`: `vest_lib/src/core/{spec.rs:7-195, proof.rs:24-174}`, `combinators/tuple/{mod.rs:30-37, spec.rs:178-285}`; Cai et al., *USENIX Security '25*, pp. 6917–6935); `project-everest/everparse` (`f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`); Delaware et al., `doi:10.1145/3341686`; Foster et al., `doi:10.1145/1232420.1232424` & `doi:10.1145/1411203.1411257`; Pickering et al., `doi:10.22152/programming-journal.org/2017/1/7`; Clarke et al., `doi:10.32408/compositionality-6-1`.

### 2. Executed Standalone C and Python Verification Probes (`Basis: execution`)

Executed on Linux `x86_64` (`gcc 15.2.0 -O2 -Wall`, `Python 3.13`, `2026-11-21`):

```bash
cat > /tmp/verify_rescale_and_lenses.c <<'EOF'
#include <stdio.h>
#include <stdint.h>
#include <limits.h>
#include <assert.h>

enum AVRounding { AV_ROUND_ZERO = 0, AV_ROUND_INF = 1, AV_ROUND_DOWN = 2,
                  AV_ROUND_UP = 3, AV_ROUND_NEAR_INF = 5, AV_ROUND_PASS_MINMAX = 8192 };
#define FFMAX(a,b) ((a) > (b) ? (a) : (b))

int64_t av_rescale_rnd(int64_t a, int64_t b, int64_t c, enum AVRounding rnd) {
    int64_t r = 0;
    if (c <= 0 || b < 0 || !((unsigned)(rnd&~AV_ROUND_PASS_MINMAX)<=5 && (rnd&~AV_ROUND_PASS_MINMAX)!=4))
        return INT64_MIN;
    if (rnd & AV_ROUND_PASS_MINMAX) {
        if (a == INT64_MIN || a == INT64_MAX) return a;
        rnd -= AV_ROUND_PASS_MINMAX;
    }
    if (a < 0)
        return -(uint64_t)av_rescale_rnd(-FFMAX(a, -INT64_MAX), b, c, rnd ^ ((rnd >> 1) & 1));
    if (rnd == AV_ROUND_NEAR_INF) r = c / 2;
    else if (rnd & 1) r = c - 1;
    if (b <= INT_MAX && c <= INT_MAX) {
        if (a <= INT_MAX) return (a * b + r) / c;
        int64_t ad = a / c, a2 = (a % c * b + r) / c;
        if (ad >= INT32_MAX && b && ad > (INT64_MAX - a2) / b) return INT64_MIN;
        return ad * b + a2;
    } else {
        uint64_t a0 = a & 0xFFFFFFFF, a1 = a >> 32, b0 = b & 0xFFFFFFFF, b1 = b >> 32;
        uint64_t t1 = a0 * b1 + a1 * b0, t1a = t1 << 32;
        a0 = a0 * b0 + t1a;
        a1 = a1 * b1 + (t1 >> 32) + (a0 < t1a);
        a0 += r; a1 += (uint64_t)a0 < (uint64_t)r;
        for (int i = 63; i >= 0; i--) {
            a1 += a1 + ((a0 >> i) & 1);
            t1 += t1;
            if ((uint64_t)c <= a1) { a1 -= c; t1++; }
        }
        return (t1 > INT64_MAX) ? INT64_MIN : (int64_t)t1;
    }
}

int rescale_u64_checked(uint64_t a, uint64_t b, uint64_t c, enum AVRounding rnd, uint64_t *out) {
    if (c == 0) return -1;
    uint64_t r = (rnd == AV_ROUND_NEAR_INF) ? (c / 2) : ((rnd == AV_ROUND_UP || rnd == AV_ROUND_INF) ? (c - 1) : 0);
    __uint128_t num = (__uint128_t)a * (__uint128_t)b + (__uint128_t)r;
    if ((uint64_t)(num >> 64) >= c) return -1;
    *out = (uint64_t)(num / c);
    return 0;
}

int main(void) {
    assert(av_rescale_rnd(INT64_MIN, 1, 1, AV_ROUND_ZERO) == -INT64_MAX);
    assert(av_rescale_rnd(23LL << 58, 1LL << 62, 1LL << 59, AV_ROUND_ZERO) == INT64_MIN);
    assert(av_rescale_rnd(44, 48000, 90000, AV_ROUND_NEAR_INF) == 23);
    assert(av_rescale_rnd(av_rescale_rnd(44, 1000, 90000, AV_ROUND_NEAR_INF), 48000, 1000, AV_ROUND_NEAR_INF) == 0);
    uint64_t u = 0;
    assert(rescale_u64_checked(UINT64_MAX, UINT64_MAX, UINT64_MAX, AV_ROUND_ZERO, &u) == 0 && u == UINT64_MAX);
    assert(rescale_u64_checked(UINT64_MAX, UINT64_MAX, UINT64_MAX - 1, AV_ROUND_ZERO, &u) == -1);
    puts("ALL_C_RESCALE_PROBES_OK");
    return 0;
}
EOF
gcc -O2 -Wall /tmp/verify_rescale_and_lenses.c -o /tmp/verify_rescale_and_lenses && /tmp/verify_rescale_and_lenses
```

Recorded output: `ALL_C_RESCALE_PROBES_OK`, paired with exhaustive Python verification over all $781$ byte sequences of length $0..4$ over `{0..4}` confirming strict RBSP `PutGet`/`GetPut` and $|\text{escape}(p)| \le \lfloor 3|p|/2 \rfloor$, single-context `PPS -> P_SLICE` parse failure on Packet 2 vs. dual-context QP preservation `[(32, 0xAA), (35, 0xBB)]`, and the 3-stream `movenc.c` `40,000`-byte `mdat` overwrite (`shift = 120,000`, written `moov = 160,000`, Kleene LFP `200,000`).

---

## Revalidation

1. **Dual-Context `CBSBSFContext` & Copy-on-Write Check (`< 5 s`):**
   Inspect `libavcodec/cbs_bsf.{h,c}`, `libavcodec/cbs.c`, and `libavcodec/bsf/h264_redundant_pps.c` at the target `FFmpeg/FFmpeg` commit to verify separate `(input, output)` `CodedBitstreamContext` instances and `ff_cbs_make_unit_writable` copy-on-write before parameter-set mutation.
2. **`av_rescale_rnd` Arithmetic & Boundary Probe (`< 2 s`):**
   Diff `libavutil/mathematics.c` (`av_rescale_rnd`, `av_rescale_q_rnd`) against `e8574d0b22b126acc76007babce536c68bc07d0a` and run `/tmp/verify_rescale_and_lenses`; check whether `-FFMAX(a, -INT64_MAX)` at `line 75` has been replaced by `-(uint64_t)a`.
3. **`faststart` Fixed-Point & `saio`/`iloc` Coverage Check (`< 5 s`):**
   Check whether `compute_moov_size` in `libavformat/movenc.c` replaces its 2-step check with a fixed-point loop (`while (new_moov_size != moov_size)`), and whether `update_chunk_offsets_callback` in `tools/qt-faststart.c` handles or rejects `saio`, `iloc`, and `tfhd`.
