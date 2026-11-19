# HTTP Request Smuggling, HPACK/QPACK Header Compression Synchronization, and WHATWG vs. RFC 3986 URL Parser Differentials

## Summary

Cross-layer protocol gateways—such as reverse proxies, CDN edge routers, load balancers, and FFI wrappers bridging HTTP/3, HTTP/2, HTTP/1.1, and URL validators—suffer systematic semantic desynchronization whenever adjacent hops interpret framing boundaries, stateful header-compression tables, or URI syntax under incompatible rules:

1. **HTTP Framing & Version-Downgrade Desynchronization (`CL.TE`, `TE.CL`, `H2.CL`, `H2.TE`):** Under RFC 9112 §6.3, message-body length in HTTP/1.1 is governed by `Transfer-Encoding` taking precedence over `Content-Length`, yet lenient parser flags (such as `nodejs/llhttp`'s `LENIENT_FLAGS.CHUNKED_LENGTH`, `TRANSFER_ENCODING`, `HEADERS`, `OPTIONAL_CR_BEFORE_LF`, and `OPTIONAL_LF_AFTER_CR`) re-enable legacy ambiguities across proxy-origin pairs. In HTTP/2 (`nghttp2/nghttp2`), binary `DATA` framing eliminates wire-level chunking, but translating HTTP/2 back to HTTP/1.1 re-introduces smuggling whenever intermediaries fail to reject CRLF/whitespace in field values, stream `DATA` frames upstream before verifying `Content-Length` against `END_STREAM`, or fail to reconcile `:authority` against `Host` (`nghttp2` tracks both only as presence flags in `lib/nghttp2_http.c:456-484` and does not check value equality).
2. **HPACK (RFC 7541) vs. QPACK (RFC 9204) Stateful Compression Synchronization & Side-Channel Boundaries:** Both HPACK and QPACK define dynamic table entry size as `len(name) + len(value) + 32` octets, but diverge fundamentally in transport ordering. HPACK relies on TCP's total order and in-band dynamic table size updates at the head of a header block (`nghttp2` rejects mid-block size updates with `NGHTTP2_ERR_HEADER_COMP`), whereas QPACK decouples table mutations onto unidirectional QUIC encoder/decoder control streams and coordinates out-of-order request streams via modular `Required Insert Count` (`RIC`) watermarks (`EncInsertCount = (RIC mod 2*MaxEntries) + 1`), bounded `SETTINGS_QPACK_BLOCKED_STREAMS` queues, and eviction-safe draining indices (`litespeedtech/ls-qpack`). Notably, `ls-qpack`'s prefix decoder validates `RIC` against a circular half-ring and defers impossible-entry detection (`RIC > TotalInserts + MaxEntries` when `TotalInserts == 0`) to dynamic-table dereference and `HBRC_LARGEST_REF_USED` end-of-block checks rather than failing inside `parse_header_prefix`. For CRIME/BREACH compression-oracle mitigation, HPACK/QPACK restrict matching to whole field lines and provide a sticky `never-indexed` wire bit (`N`), yet `nghttp2` auto-marks only `Authorization` and `Cookie` values shorter than 20 bytes (`lib/nghttp2_hd.c:1399-1403`), leaving longer sensitive headers unprotected unless explicitly flagged `NGHTTP2_NV_FLAG_NO_INDEX`.
3. **Irreconcilable WHATWG URL vs. RFC 3986 Algebra:** The WHATWG URL Living Standard (implemented in `ada-url/ada` and `servo/rust-url`) and RFC 3986 (approximated by `hyperium/http` and Python's `urllib.parse`) disagree structurally on five non-reducible axes: (a) backslash `\` authority termination and slash normalization in the six WHATWG special schemes (`http`, `https`, `ws`, `wss`, `ftp`, `file`), (b) multi-`@` userinfo scanning and empty-host rejection, (c) silent stripping of ASCII `\t`/`\r`/`\n` and leading/trailing C0 controls, (d) radix/shorthand IPv4 canonicalization (`0177.0.0.1`, `2130706433`, `0x7f.1`, `127.0.0.1.`), and (e) UTS #46 IDNA host mapping. Verified execution confirms that on `http://allowed.example\@other.example/p`, WHATWG parsers extract host `allowed.example` while Python 3.13.15 `urllib.parse.urlsplit` extracts `other.example` and `hyperium/http` rejects `\` outright with `InvalidUriChar`.

Gateway architectures that guarantee zero cross-layer differential must enforce a **parse-once, re-serialize-from-AST** discipline, reject ambiguous framing outright (`400 Bad Request` rather than heuristic recovery), disable HTTP/1.1 lenient flags on security boundaries, check exact `:authority == Host` equality during HTTP/2-to-HTTP/1.1 translation, and require every URL consumer downstream of a policy check to consume the validator's own canonicalized structured output.

## Applicability

These findings govern the specification, implementation, auditing, and formal verification of HTTP protocol parsers, reverse-proxy downgrade translators, header-compression codecs, and URI/URL validators operating at network or FFI boundaries.

### Examined Subjects and Relationships

The subjects in `REPORT.json` form three cross-referenced comparative clusters:

1. **HTTP Framing & Downgrade Cluster (Normative vs. Implementations vs. Differential Fuzzing):**
   - **Normative specifications:** IETF RFC 9112 (HTTP/1.1, June 2022) and IETF RFC 9113 (HTTP/2, June 2022).
   - **Implementations inspected:** `nodejs/llhttp` (`0ae8c68c3c5a8fce13dbff87190e1ba40d8f9666`, HTTP/1.1 state-machine generator in `src/llhttp/http.ts`) and `nghttp2/nghttp2` (`9633d1d960c147578183760232fe32e55a6ee3f5`, HTTP/2 semantic validation in `lib/nghttp2_http.c`).
   - **Empirical methodology:** `T-Reqs` (Jabiyev et al., ACM CCS 2021, DOI `10.1145/3460120.3485384`) and its published grammar-mutation harness `bahruzjabiyev/t-reqs-http-fuzzer` (`b90f97e4f39afbe39c66ecfe99fae1b832b20f62`).
2. **Stateful Header Compression Cluster (Ordered vs. Out-of-Order Codecs):**
   - **HPACK:** RFC 7541 (May 2015) interpreted alongside `nghttp2/nghttp2` (`9633d1d960c147578183760232fe32e55a6ee3f5`, `lib/nghttp2_hd.h`, `lib/nghttp2_hd.c`, `lib/nghttp2_hd_huffman.c`).
   - **QPACK:** RFC 9204 (June 2022) interpreted alongside `litespeedtech/ls-qpack` (`1aeb4f2c73a41318cb726bc1a3d603f43abe509e`, `lsqpack.h`, `lsqpack.c`) and validated via a standalone Python modular-arithmetic cross-check probe.
3. **URL / URI Parser Differential Cluster (WHATWG vs. RFC 3986 vs. Hybrid Stdlib):**
   - **WHATWG URL Standard implementations:** `ada-url/ada` (`d1fcb0b93c0d17436303384708ecdab2d003068c`, C++ state machine in `src/parser.cpp`) and `servo/rust-url` (`e219288fc2702301803e72f7efb66d3c5c25c980`, Rust implementation in `url/src/parser.rs` and `url/src/host.rs`).
   - **Strict RFC 3986 URI authority validator:** `hyperium/http` (`a8309a93ce24c19c89cf36bfac504ebed7b96dc7`, `src/uri/authority.rs`).
   - **Executed hybrid stdlib baseline:** CPython `3.13.15` `urllib.parse.urlsplit`.

### Scope Conditions and Extension Arguments

- **Exact observations** apply strictly to the pinned commit SHAs, RFC editions, and CPython `3.13.15` runtime listed above. Configuration knobs matter decisively: `llhttp` defaults to strict RFC 9112 rejection of `Content-Length` + `Transfer-Encoding` coexistence, and its permissive differentials activate only when callers opt into `LENIENT_FLAGS.*`. Similarly, `nghttp2` enforces strict RFC 9113 leading/trailing whitespace validation on header values unless `NGHTTP2_STREAM_FLAG_NO_RFC9113_LEADING_AND_TRAILING_WS_VALIDATION` is set.
- **Broader applicability:** Architectural conclusions—such as the non-composability of lenient and strict framing parsers, the necessity of a two-stream watermark protocol in QPACK over unordered QUIC streams, and the impossibility of unifying WHATWG special-scheme backslash/IPv4 semantics with strict RFC 3986 ABNF without changing one specification's language—hold across all conforming implementations of those standards because they are structural consequences of the normative specifications themselves (`Basis: derived` from normative grammar definitions).

## Findings

### 1. HTTP/1.1 Framing Ambiguity and `CL.TE` / `TE.CL` / `TE.TE` Desynchronization

`Basis: normative + source + documentation`

HTTP/1.1 multiplexes sequential request/response exchanges over a persistent TCP byte stream (`Connection: keep-alive`), making exact agreement on message-body termination mandatory between every front-end proxy $P$ and back-end origin $O$. Formally, if an input byte sequence $B$ is parsed into request sequences $\mathcal{P}_P(B) = [r_1, \dots, r_k]$ and $\mathcal{P}_O(B) = [r'_1, \dots, r'_m]$ where a framing length discrepancy causes $\text{end}(r_1) \neq \text{end}(r'_1)$, then the residual suffix of $r_1$ (or prefix of $r_2$) crosses the request boundary on the disagreeing peer—producing request smuggling, cache poisoning, or cross-tenant response desynchronization.

#### Normative RFC 9112 §6.3 Precedence and Rejection Rules

RFC 9112 §6.3 establishes a strict decision hierarchy for HTTP/1.1 message framing:
1. Responses to `HEAD`, `1xx`, `204`, `304`, and `2xx` responses to `CONNECT` have zero-length framed bodies regardless of header fields.
2. If both `Transfer-Encoding` and `Content-Length` are received in the same message, `Transfer-Encoding` overrides `Content-Length`, **and** a receiver SHOULD reject the message with `400 (Bad Request)` and close the connection because the combination indicates an attempted smuggling desync or broken intermediary (RFC 9112 §6.3 item 3).
3. If `Transfer-Encoding` is present in a **request**, the final transfer coding MUST be `chunked`; otherwise the receiver MUST respond with `400 (Bad Request)` and close the connection (RFC 9112 §6.3 item 4).
4. If multiple `Content-Length` fields exist with differing values (or a single comma-separated list with non-identical decimal values), the message is invalid and MUST be rejected with `400 (Bad Request)` (RFC 9112 §6.3 item 5).
5. Line termination is strictly `CRLF` (`\r\n`, RFC 9112 §2.2), and no whitespace (`obs-fold` or `SP`/`HTAB`) is permitted between a header field-name and its colon `:` (`field-name ":"`, RFC 9112 §5.1).

#### Source Inspection: Strict Defaults vs. Lenient Knobs in `nodejs/llhttp`

Inspection of `nodejs/llhttp` (`0ae8c68c3c5a8fce13dbff87190e1ba40d8f9666`, `src/llhttp/http.ts`) reveals how a modern state-machine parser enforces RFC 9112 in strict mode while exposing explicit configuration flags (`lenient_flags`, line 240) that re-open classical smuggling differentials whenever front-end and back-end configurations diverge:

| Framing Edge Case | `llhttp` Strict Default (`lenient_flags == 0`) | `llhttp` Opt-In Relaxation Flag | Smuggling Risk Under Asymmetric Proxy/Origin Config |
| :--- | :--- | :--- | :--- |
| `Transfer-Encoding` + `Content-Length` both present | Rejects with `ERROR.INVALID_TRANSFER_ENCODING` (`L600-L603`) or `ERROR.INVALID_CONTENT_LENGTH` (`L609-L611`) | `LENIENT_FLAGS.CHUNKED_LENGTH` allows coexistence (`Transfer-Encoding` overrides `CL`) | **CL.TE / TE.CL:** If one hop enables `CHUNKED_LENGTH` and the other ignores obscured `TE`, body boundaries diverge. |
| Coding after `chunked` in request `Transfer-Encoding` | Rejects in `TYPE.REQUEST` via `forbidAfterChunkedInRequest` (`L712-L730`, `L752`) | `LENIENT_FLAGS.TRANSFER_ENCODING` permits non-final `chunked` | **TE.TE:** Proxy sees `chunked` anywhere in `TE`; origin rejects `TE` as non-final and falls back to `CL`. |
| Duplicate `Content-Length` headers | Rejects unconditionally in `header_value_content_length_once` (`L775-L778`, `ERROR.UNEXPECTED_CONTENT_LENGTH`) | None in `header_value_content_length_once` (always rejected) | Protects against `CL.CL` desync even when two identical `CL` headers appear. |
| Whitespace before colon (`Name : value`) | Rejected in header-name state (`L624-L637`) | `LENIENT_FLAGS.HEADERS` accepts space before `:` (`L625`, `L637`) | **Header obfuscation:** One hop strips `Transfer-Encoding : chunked` as invalid/unknown while another parses it as `TE`. |
| Bare `LF` (`\n`) without preceding `CR` (`\r`) | Rejected at request line, headers, and chunk boundaries (`L328`, `L572`, `L669`, `L837`) | `LENIENT_FLAGS.OPTIONAL_CR_BEFORE_LF` permits bare `\n` | **Line-delimiter desync:** Hop accepting bare `\n` treats embedded `\nHeader: val` as a separate header; strict `CRLF`-only hop folds it into the prior value. |
| Bare `CR` (`\r`) without following `LF` (`\n`) | Rejected (`L426`, `L537`, `L898`) | `LENIENT_FLAGS.OPTIONAL_LF_AFTER_CR` permits bare `\r` | **Bare-CR line splitting:** Enables hidden header injection across hops disagreeing on `CR`-only line breaks. |
| Non-VCHAR / control octets in header values | Rejected; `HEADER_VALUE_RELAXED` admits narrow legacy subset (`L840-L844`) | `LENIENT_FLAGS.HEADERS` jumps to `header_value_lenient` accepting arbitrary octets (`L842-L864`) | Permits control characters (`\x00`, `\x0b`, `\x0c`) inside `TE` or `CL` values that downstream parsers strip or treat as delimiters. |

#### Grammar-Based Differential Fuzzing Taxonomy (`T-Reqs`, CCS 2021)

Jabiyev, Sprecher, Onarlioglu, and Kirda (*T-Reqs: HTTP Request Smuggling with Differential Fuzzing*, ACM CCS 2021, DOI `10.1145/3460120.3485384`, pp. 1805–1820; artifact `bahruzjabiyev/t-reqs-http-fuzzer @ b90f97e4f39afbe39c66ecfe99fae1b832b20f62`) formalized HTTP smuggling discovery as a **two-level grammar-mutation differential problem** across 10 reverse proxies, CDNs, and origin servers:
- **Structured generation (`README.md:22-50`):** A Context-Free Grammar partitions an HTTP/1.x request into individually addressable syntactic nodes (`<request-line>`, `<method-name>`, `<space>`, `<uri>`, `<protocol>`, `<separator>`, `<version>`, `<newline>`, `<base>`, `<the-rest>`).
- **Dual mutation operators (`README.md:51-54`):**
  1. *String-mutable leaves* undergo single-character insertion, deletion, or replacement (synthesizing malformed delimiters such as `\r` without `\n`, vertical tabs `\x0b`, `HTTP/1.0`, or corrupted `Transfer-Encoding` tokens).
  2. *Tree-mutable nonterminals* undergo AST-level deletion, duplication, or component swapping (synthesizing duplicate framing headers, reordered request-line tokens, or absent version components).
- **Feedback oracle (`README.md:88-93`):** Rather than testing exploitability directly, T-Reqs places each server in reverse-proxy mode forwarding to a body-length measuring feedback service. Any mutated seed for which two servers report different forwarded body lengths (or where one forwards a body and another drops/splits it) proves a framing differential capable of inducing desynchronization in a proxy-origin pair.

---

### 2. HTTP/2-to-HTTP/1.1 Downgrade Smuggling and `nghttp2` Validation Gaps

`Basis: normative + source + derived`

HTTP/2 (RFC 9113) frames message bodies using explicit binary `DATA` frames terminated by the `END_STREAM` (`0x01`) flag on an isolated `stream_id`. Within pure end-to-end HTTP/2, framing ambiguity cannot occur because `Transfer-Encoding` is forbidden (RFC 9113 §8.2.2) and `DATA` length is carried out-of-band in the 9-octet frame header. However, real deployments routinely terminate HTTP/2 at an edge proxy and **downgrade** requests onto pooled HTTP/1.1 keep-alive connections to origin servers. This downgrade re-introduces three severe failure modes:

1. **`H2.CL` Framing Desync (Streaming Before `END_STREAM`):** Because HTTP/2 allows an optional `content-length` header alongside `DATA` frames, a proxy that forwards the client's `content-length: N` header verbatim to an HTTP/1.1 origin—and streams `DATA` payload bytes as they arrive without waiting for `END_STREAM` or overwriting `Content-Length` with the true re-framed length (or re-encoding as HTTP/1.1 `Transfer-Encoding: chunked`)—allows a client to send more than `N` bytes across `DATA` frames. Even when the HTTP/2 library rejects the stream upon seeing `recv_content_length > content_length`, bytes already flushed to the upstream TCP socket may already have been parsed by the origin as the prefix of a subsequent pipelined HTTP/1.1 request.
2. **`H2.TE` & Header-Value Injection:** Binary HPACK encoding can carry arbitrary octets—including `CR` (`0x0D`), `LF` (`0x0A`), `NUL` (`0x00`), uppercase names, spaces, or forbidden hop-by-hop headers like `transfer-encoding: chunked`—inside length-delimited strings. If an H2→H1 translator serializes HPACK-decoded names/values into ASCII `Name: Value\r\n` lines without strict RFC 9113 §8.2.1 character validation, an embedded `\r\n` inside a header value or `:path` pseudo-header splits into forged HTTP/1.1 headers or a second HTTP/1.1 request line.
3. **`:authority` vs. `Host` Routing/Cache Confusion:** RFC 9113 §8.3.1 mandates that HTTP/2 requests with an authority use `:authority` (and if `Host` is also present, RFC 9110 §7.2 / RFC 9113 §8.3.1 requires consistency). If an H2→H1 gateway routes or enforces ACLs using `:authority` while forwarding a distinct client-supplied `Host` header to an HTTP/1.1 origin, front-end access control and back-end virtual-host dispatch disagree.

#### Exact Source Audit of `nghttp2/nghttp2` (`lib/nghttp2_http.c`)

Direct inspection of `nghttp2/nghttp2` (`9633d1d960c147578183760232fe32e55a6ee3f5`, `lib/nghttp2_http.c`) establishes the exact verification invariants `nghttp2` enforces and the exact invariants left to the caller/gateway:

| Validation Property | Implementation Location | Enforced Behavior in `nghttp2` | Residual Gateway Obligation |
| :--- | :--- | :--- | :--- |
| Forbidden connection-specific headers (`connection`, `keep-alive`, `proxy-connection`, `transfer-encoding`, `upgrade`) | `http_request_on_header` (`L295-L300`), `http_response_on_header` (`L388-L393`) | Hard rejection returning `NGHTTP2_ERR_HTTP_HEADER` (stream reset `PROTOCOL_ERROR`). | None if `nghttp2` built-in HTTP messaging validation is enabled (do not disable via `nghttp2_option_set_no_http_messaging`). |
| `te` header | `L301-L305`, `L394-L398` | Strictly rejects any value other than case-insensitive `"trailers"`. | Strip `te: trailers` or translate cleanly when downgrading to HTTP/1.1. |
| Pseudo-header order, uniqueness, non-empty value, lowercase names | `nghttp2_http_on_header` (`L422-L443`), `check_pseudo_header` (`L91-L93`) | Any uppercase character in field name returns hard `NGHTTP2_ERR_HTTP_HEADER` (`L439-L441`); pseudo-headers after regular headers or in trailers return `NGHTTP2_ERR_HTTP_HEADER` (`L427-L432`). | Watch silent ignoring: **illegal regular header names** (`case 0` at `L437-L438`), empty names (`L422-L424`), and **invalid regular header values** (`L335-L337`) return `NGHTTP2_ERR_IGN_HTTP_HEADER` (silently dropped instead of resetting the stream!). |
| Invalid `Host` vs. invalid `:authority` | `L199-L204` vs. `L276-L283` | Invalid `:authority` fails hard (`NGHTTP2_ERR_HTTP_HEADER`), whereas invalid `Host` syntax returns `NGHTTP2_ERR_IGN_HTTP_HEADER` (dropped silently unless duplicate/empty). | **Critical asymmetry:** A gateway must NOT fall back silently if `Host` was dropped or malformed. |
| `:authority` vs. `Host` equality | `nghttp2_http_on_request_headers` (`L467-L472`) | Checks only `(http_flags & (NGHTTP2_HTTP_FLAG__AUTHORITY \| NGHTTP2_HTTP_FLAG_HOST)) == 0`. **Neither string is stored or compared.** | **Mandatory gateway check:** When both `:authority` and `Host` are present, the H2→H1 translator MUST verify ASCII case-insensitive equality (or reject `400`) and emit a single canonical `Host` header. |
| Duplicate `Content-Length` & `DATA` length matching | `L284-L292`, `nghttp2_http_on_data_chunk` (`L548-L558`), `nghttp2_http_on_remote_end_stream` (`L535-L546`) | Rejects duplicate `content-length` (`stream->content_length != -1`), aborts immediately if `recv_content_length > content_length`, and fails at `END_STREAM` if `recv_content_length != content_length`. | **Streaming hazard:** Because mismatch is detected only *after* exceeding `CL` or at `END_STREAM`, a streaming H2→H1 proxy MUST frame downgraded requests with HTTP/1.1 `Transfer-Encoding: chunked` (omitting client `Content-Length`) or buffer until `END_STREAM` before forwarding `Content-Length`. |
| Leading/trailing OWS in header values (RFC 9113 §8.2.1) | `L262-L274` (`nghttp2_check_header_value_rfc9113`) | Enforced by default; bypassed only if `NGHTTP2_STREAM_FLAG_NO_RFC9113_LEADING_AND_TRAILING_WS_VALIDATION` is set. | Keep RFC 9113 whitespace validation enabled on security boundaries. |

---

### 3. Stateful Header Compression Synchronization: HPACK (RFC 7541) vs. QPACK (RFC 9204)

`Basis: normative + source + execution`

Both HPACK (HTTP/2) and QPACK (HTTP/3) reduce HTTP header overhead using (1) a fixed static table (61 entries in HPACK RFC 7541 Appendix A; 99 entries in QPACK RFC 9204 Appendix A), (2) a fixed canonical Huffman code for strings, and (3) a bounded FIFO dynamic table whose abstract byte size counts `32` octets of metadata overhead per entry (`NGHTTP2_HD_ENTRY_OVERHEAD = 32` in `nghttp2/nghttp2` `lib/nghttp2_hd.h:40`, `entry_room` at `lib/nghttp2_hd.c:811-813`; `DYNAMIC_ENTRY_OVERHEAD = 32u` in `litespeedtech/ls-qpack` `lsqpack.c:220`).

Despite sharing this table-sizing algebra, HPACK and QPACK solve fundamentally different distributed synchronization problems:

| Dimension | HPACK (RFC 7541, `nghttp2/nghttp2`) | QPACK (RFC 9204, `litespeedtech/ls-qpack`) |
| :--- | :--- | :--- |
| **Transport Ordering Assumption** | Total FIFO order over a single TCP stream (`HEADERS` + `CONTINUATION` frames processed strictly sequentially). | Out-of-order independent QUIC streams; packet loss on stream $A$ must not stall stream $B$ unless $B$ explicitly opts into dynamic-table references. |
| **Table Mutation Channel** | **In-band** inside request/response `HEADERS` blocks (`01xxxxxx` incremental indexing; `001xxxxx` dynamic table size update). | **Out-of-band** unidirectional QPACK **Encoder Stream** (`0x02`) carrying `Set Dynamic Table Capacity`, `Insert With Name Reference`, `Insert Without Name Reference`, and `Duplicate`. |
| **Feedback / Acknowledgment Channel** | None (implicit via TCP delivery order and `SETTINGS_HEADER_TABLE_SIZE` ACK). | Unidirectional QPACK **Decoder Stream** (`0x03`) carrying `Section Acknowledgment` (`1xxxxxxx`, 7-bit stream ID), `Stream Cancellation` (`01xxxxxx`), and `Insert Count Increment` (`00xxxxxx`). |
| **Indexing Scheme** | **Relative FIFO index** (newest entry is index `62`; every insertion shifts all existing dynamic indices by `+1`). | **Absolute Insert Count** (monotonically increasing `0, 1, 2, ...`) encoded relative to a per-block `Base` (pre-base relative index `Base - 1 - abs` or post-base index `abs - Base`). |
| **Table Resize Sequencing** | Must appear strictly at the **beginning** of a header block (`nghttp2_hd.c:1965-1972` rejects mid-block `0x20` updates with `NGHTTP2_ERR_HEADER_COMP`), bounded by `min(min_hd_table_bufsize_max, settings_hd_table_bufsize_max)` (`L2002-L2005`). | Sent asynchronously on Encoder Stream (`Set Dynamic Table Capacity`), bounded by peer's `SETTINGS_QPACK_MAX_TABLE_CAPACITY`. |
| **Eviction Safety Against In-Flight References** | Trivial: because blocks decode in strict sequence, evicting an old entry during block $k$ never affects block $k-1$. | **Reference-counted + draining watermark:** Encoder MUST NOT evict any entry with active unacknowledged stream references; `ls-qpack` marks entries in the oldest 25% of capacity as *draining* (`qenc_entry_is_draining`, `lsqpack.c:1523-1532`: `dist < qpe_cur_max_capacity / 4`) and proactively duplicates hot draining entries (`qenc_dup_draining`, `L1550-L1580`) to prevent eviction deadlocks. |
| **Huffman Padding Check** | RFC 7541 §5.2: trailing padding $\le 7$ bits of all `1`s (EOS prefix); `nghttp2_hd_huffman.c:138-140` enforces `final && !(ctx->flags & NGHTTP2_HUFF_ACCEPTED) => NGHTTP2_ERR_HEADER_COMP`. | Identical RFC 7541 Huffman table and EOS-padding rule enforced in `lsqpack_huff_decode` (`lsqpack.c:3520-3529`). |

#### QPACK `Required Insert Count` Watermarks, Wraparound Math, and Blocked-Stream Limits

Every QPACK Encoded Field Section begins with a two-integer prefix (`Required Insert Count` and `Sign` + `Delta Base`, RFC 9204 §4.5.1). Let $C_{\max}$ be `SETTINGS_QPACK_MAX_TABLE_CAPACITY`, $\text{MaxEntries} = \lfloor C_{\max} / 32 \rfloor$, and $\text{FullRange} = 2 \cdot \text{MaxEntries}$.

- **Encoder transform (RFC 9204 §4.5.1.1; `lsqpack.c:1268-1269`):**
  $$\text{EncRIC} = \begin{cases} 0 & \text{if } \text{RIC} = 0 \\ (\text{RIC} \bmod (2 \cdot \text{MaxEntries})) + 1 & \text{if } \text{RIC} > 0 \end{cases}$$
- **Normative decoder reconstruction (RFC 9204 §4.5.1.1):** Given `TotalInserts` ($T$, entries currently inserted from the encoder stream):
  1. If $\text{EncRIC} = 0$, $\text{RIC} = 0$.
  2. If $\text{EncRIC} > \text{FullRange}$, signal `QPACK_DECOMPRESSION_FAILED`.
  3. Set $\text{MaxValue} = T + \text{MaxEntries}$ and $\text{MaxWrapped} = \lfloor \text{MaxValue} / \text{FullRange} \rfloor \cdot \text{FullRange}$.
  4. Set $\text{RIC} = \text{MaxWrapped} + \text{EncRIC} - 1$.
  5. If $\text{RIC} > \text{MaxValue}$: if $\text{RIC} \le \text{FullRange}$, signal `QPACK_DECOMPRESSION_FAILED` (underflow/invalid future jump); else $\text{RIC} \leftarrow \text{RIC} - \text{FullRange}$.
  6. If $\text{RIC} = 0$, signal `QPACK_DECOMPRESSION_FAILED`.
  7. If $\text{RIC} > T$, the stream is **blocked** awaiting encoder-stream inserts; once the blocked stream count would exceed `SETTINGS_QPACK_BLOCKED_STREAMS`, the decoder MUST close the connection with `QPACK_DECOMPRESSION_FAILED` (RFC 9204 §2.1.2).

#### Source & Execution Finding: `ls-qpack` Circular Half-Ring Reconstruction vs. Normative Prefix Check

Direct inspection of `litespeedtech/ls-qpack` (`1aeb4f2c73a41318cb726bc1a3d603f43abe509e`, `lsqpack.c`) and execution of a cross-check probe (`Basis: source + execution`) reveal an important implementation distinction in how `ls-qpack` encodes the RFC 9204 watermark:
- `ls-qpack` tracks 0-based circular IDs modulo `FullRange = 2 * qpd_max_entries` (`ID_MINUS`/`ID_PLUS`, `L2744-L2748`), initializing `qpd_last_id = 2 * qpd_max_entries - 1` (`L2785`).
- In `parse_header_prefix` (`L3966-L3978`), when `RIC.value > 0`, it checks `RIC.value <= 2 * qpd_max_entries`, computes `hbrc_largest_ref = ID_MINUS(RIC.value, 2)`, and checks `qdec_in_future(dec, hbrc_largest_ref)` (`L3910-L3918`). If in the future, it returns `LQRHS_BLOCKED` and invokes `stash_blocked_header` (`L4136-L4155`), which enforces `dec->qpd_n_blocked < dec->qpd_max_risked_streams`.
- **Subtle divergence at initial underflow boundary (`RIC = MaxEntries + 1`, `TotalInserts = 0`):** For $C_{\max} = 4096$ ($\text{MaxEntries} = 128$, $\text{FullRange} = 256$), an invalid wire value `EncRIC = 130` (corresponding to `RIC = 129` when `TotalInserts = 0`, which exceeds `MaxValue = 128`) is rejected immediately by RFC 9204 §4.5.1.1 step 5 (`RIC <= FullRange` underflow). In `ls-qpack`, because `qpd_last_id = 255 >= 128` and `largest_ref = 128` lies in `[255 - 128 + 1, 255] = [128, 255]`, `qdec_in_future` evaluates to `0` (`LQRHS_READY`) inside `parse_header_prefix`. Soundness is still preserved—no uninserted entry can be read—because `parse_header_data` subsequently rejects either the missing dynamic-table entry lookup or the end-of-section invariant (`L3886-L3891`, `check_dyn_table_errors` at `L3534-L3542`), which requires that (a) if `HBRC_LARGEST_REF_SET` is set, at least one field line actually referenced `hbrc_largest_ref` (`HBRC_LARGEST_REF_USED`), and (b) if `EncodedInsertCount == 0`, zero dynamic references occurred (`HBRC_DYN_USED_IN_ERR`). However, any formal equivalence proof or differential fuzzer comparing prefix-stage error codes between RFC 9204 and `ls-qpack` must account for this deferred rejection point.

Observed execution output for $C_{\max} = 4096$ ($\text{MaxEntries} = 128$):

```text
RIC=  0 Total=  0 -> Enc=  0 | RFC9204=(0, ok) | ls-qpack=ready
RIC=  1 Total=  0 -> Enc=  2 | RFC9204=(1, blocked) | ls-qpack=LQRHS_BLOCKED
RIC=128 Total=  0 -> Enc=129 | RFC9204=(128, blocked) | ls-qpack=LQRHS_BLOCKED
RIC=129 Total=  0 -> Enc=130 | RFC9204=(None, QPACK_DECOMPRESSION_FAILED(underflow)) | ls-qpack=LQRHS_READY
RIC=255 Total=250 -> Enc=256 | RFC9204=(255, blocked) | ls-qpack=LQRHS_BLOCKED
RIC=256 Total=250 -> Enc=  1 | RFC9204=(256, blocked) | ls-qpack=LQRHS_BLOCKED
RIC=257 Total=250 -> Enc=  2 | RFC9204=(257, blocked) | ls-qpack=LQRHS_BLOCKED
RIC=250 Total=256 -> Enc=251 | RFC9204=(250, ready) | ls-qpack=LQRHS_READY
RIC=129 Total=256 -> Enc=130 | RFC9204=(129, ready) | ls-qpack=LQRHS_READY
RIC=128 Total=256 -> Enc=129 | RFC9204=(384, blocked) | ls-qpack=LQRHS_BLOCKED
```

Note the final row (`RIC=128, Total=256`): an entry that is `MaxEntries` (128) steps behind `TotalInserts` wraps *forward* modulo `256` to `RIC = 384` (blocked), proving that the valid un-wrapped history window is strictly `[TotalInserts - MaxEntries + 1, TotalInserts]` (size `MaxEntries`), while the valid future-blocking window is `[TotalInserts + 1, TotalInserts + MaxEntries]` (size `MaxEntries`).

#### CRIME / BREACH Compression-Oracle Defense Boundaries in HPACK and QPACK

`Basis: normative + source`

Unlike stream-level DEFLATE (exploited byte-by-byte by CRIME/BREACH), both RFC 7541 §7.1 and RFC 9204 §7.1 restrict dynamic-table matching to **entire field values** (or static/dynamic name-only matches) plus fixed static Huffman coding. This eliminates character-by-character prefix probing for high-entropy secrets, *but* leaves two real compression-oracle channels open:
1. **Whole-value equality oracles on low-entropy secrets** (short PINs, CSRF tokens, session flags, or short cookies) if indexed in a shared dynamic table across cross-origin requests.
2. **Huffman length-difference oracles** if a secret value is Huffman-encoded alongside attacker-controlled headers and different secret characters have different canonical Huffman bit lengths (ranging from 5 bits for `'0'..'9'`, `'a'`, `'e'`, `'i'`, `'o'`, `'s'`, `'t'` up to 30 bits for non-ASCII/control bytes).

To prevent intermediaries from re-compressing sensitive fields across multi-hop proxies, both protocols provide a **sticky never-indexed wire representation**:
- **HPACK (RFC 7541 §6.2.3):** 4-bit prefix `0001xxxx` (`0x10` in `nghttp2_hd.c:1052-1053`, `1980`, `1990`). On decode, `nghttp2` propagates `NGHTTP2_NV_FLAG_NO_INDEX` (`L1815-L1817`, `L1862-L1864`) so downstream proxies preserve never-indexed semantics.
- **QPACK (RFC 9204 §4.5.4–§4.5.6):** Dedicated `N` bit in three literal representations (`lsqpack.c:2056-2094`): Literal Field Line with Literal Name (`0x20 | (N << 4)`), Literal Field Line with Name Reference (`0x40 | (N << 5)`), and Post-Base Name Reference (`0x00 | (N << 3)`), activated via `LQEF_NEVER_INDEX` / `LSXPACK_NEVER_INDEX` (`lsqpack.h:201`, `lsqpack.c:1663-1664`, `1720`).
- **Critical implementation boundary in `nghttp2` (`lib/nghttp2_hd.c:1395-1403`):** `nghttp2`'s default deflater automatically selects `NGHTTP2_HD_NEVER_INDEXING` *only* when `token == NGHTTP2_TOKEN_AUTHORIZATION || (token == NGHTTP2_TOKEN_COOKIE && nv->valuelen < 20) || (nv->flags & NGHTTP2_NV_FLAG_NO_INDEX)`. Consequently, custom auth headers (`X-API-Key`, `X-Session-Token`), `Set-Cookie` responses, and `Cookie` headers with `valuelen >= 20` **are dynamically indexed by default** unless the application explicitly sets `NGHTTP2_NV_FLAG_NO_INDEX` (and disables Huffman encoding if even exact byte-length leakage of low-entropy secrets violates the threat model). Similarly, `ls-qpack` performs **no** automatic header-name sensitivity heuristic in `lsqpack.c:1663-1722`—never-indexing relies wholly on callers setting `LSXPACK_NEVER_INDEX` or `LQEF_NEVER_INDEX`.

---

### 4. Irreconcilable WHATWG URL vs. RFC 3986 URI Parser Differentials

`Basis: normative + source + execution`

Security controls such as SSRF egress allowlists, OAuth `redirect_uri` verifiers, CORS origin checks, and reverse-proxy ACL routers frequently parse an untrusted URL string with one library to authorize the target host, then pass the raw string to a second HTTP client or browser parser to execute the request. Because the **WHATWG URL Living Standard** (specifying error-recovering browser parsing) and **IETF RFC 3986** (specifying declarative ABNF URI grammar) define mathematically incompatible languages, no syntax-only regex or raw-string filter can make both agree on adversarial inputs.

#### Five Non-Reducible Differential Axes Verified in Source and Execution

1. **Special Schemes and Backslash (`\`) Authority Termination:**
   - **WHATWG (`ada-url/ada` `src/parser.cpp:2168-2170, 2242-2245`; `servo/rust-url` `url/src/parser.rs:159-162, 437-458, 878-880`):** Designates exactly six *special schemes*: `http`, `https`, `ws`, `wss`, `ftp`, `file`. In special schemes, `U+005C` (`\`) is normalized to `/` and terminates the `authority` state identically to `/`, `?`, and `#` (`rust-url`: `'\\' if scheme_type.is_special() => break` at `L879`; `ada`: `url.is_special() && url_data[end_of_authority] == '\\'` at `L2245`). In non-special schemes (e.g., `custom://`), `\` is *not* an authority delimiter.
   - **RFC 3986 (`hyperium/http` `src/uri/authority.rs:492-516`):** `\` is forbidden in RFC 3986 URIs (`URI_CHARS[b'\\'] == 0` -> `Err(AuthorityError::InvalidUriChar)`).
   - **Lenient RFC 3986 hybrids (Python `3.13.15` `urllib.parse.urlsplit`):** Does *not* treat `\` as an authority delimiter and does not reject it; on `http://allowed.example\@other.example/p`, `urllib.parse` treats `allowed.example\` as userinfo and extracts `hostname = 'other.example'`, whereas WHATWG (`ada`, `rust-url`) terminates authority at `\` before `@` and extracts `hostname = 'allowed.example'`, `path = '/@other.example/p'`.

2. **Slash-Count Recovery After Special Scheme (`http:/`, `http:///`, `http:\\`):**
   - **WHATWG (`ada` `src/parser.cpp:2269-2285, 2395-2454` `SPECIAL_AUTHORITY_IGNORE_SLASHES`; `rust-url` `url/src/parser.rs:437-459`):** Consumes **any** sequence of `/` and `\` after `http:` (0, 1, 2, 3, or more, mixed with `\`) when no same-scheme base URL triggers relative resolution, parsing `http:/example.com/p`, `http:///example.com/p`, and `http:\\example.com/p` all with host `example.com`.
   - **RFC 3986 / Python `urllib.parse`:** Authority exists **if and only if** the scheme colon is immediately followed by `//` (RFC 3986 §3). Thus Python `3.13.15` parses `http:/example.com/p`, `http:///example.com/p`, and `http:\\example.com/p` with `hostname = None` and places `example.com` inside `path`.

3. **Multiple `@` Signs and Empty-Host Authority Rules:**
   - **WHATWG (`ada` `src/parser.cpp:2158-2253`; `rust-url` `url/src/parser.rs:860-898`):** Scans forward to the **rightmost** `@` before the first authority delimiter, percent-encoding all earlier `@` characters as `%40` into `username`/`password` (`ada` `L2177-L2191`), and failing if the resulting host after `@` is empty (`ada` `L2248-L2251`; `rust-url` `L891-L895`).
   - **RFC 3986 §3.2.1:** Prohibits unencoded `@` inside `userinfo` (`userinfo = *( unreserved / pct-encoded / sub-delims / ":" )`). Yet many real RFC-oriented parsers deviate: `hyperium/http` (`src/uri/authority.rs:429-432, 537-544`) resets `at_sign_pos`, `colon_cnt`, and `has_percent` on each `@` and splits via `rsplit('@')`, so it accepts multiple `@` and selects the rightmost host (matching WHATWG), whereas naive first-`@` splitters (historically seen in regex validators and older client libraries) select the segment after the *first* `@` as host—creating classic SSRF allowlist bypasses on `http://u@allowed.example@other.example/p`.

4. **ASCII Whitespace / Control Character Pre-Stripping:**
   - **WHATWG (`ada` `src/parser.cpp:1956-1964`; `rust-url` `url/src/parser.rs:375`):** Unconditionally removes all `U+0009` (`\t`), `U+000A` (`\n`), and `U+000D` (`\r`) anywhere in the input string *and* trims leading and trailing C0 controls + space (`U+0000..=U+0020`) prior to state-machine execution.
   - **RFC 3986 (`hyperium/http`):** Rejects C0 controls, spaces, tabs, and newlines anywhere (`InvalidUriChar`).
   - **Python `3.13.15` `urllib.parse` (hybrid hardening):** Strips embedded `\t`/`\r`/`\n` (returning `hostname='example.com'`, `path='/ab'` on `http://exa\tmple.com/a\nb`) and trims *leading* C0/space (`' \x01http://...' -> scheme='http'`), **yet preserves trailing C0/space** inside `path` (`'/\x1f '` on `' \x01http://example.com/\x1f '`), diverging from both pure RFC 3986 and pure WHATWG!

5. **Non-Canonical IPv4 Literals and UTS #46 IDNA Domain Normalization:**
   - **WHATWG (`servo/rust-url` `url/src/host.rs:297-361` `parse_ipv4number` / `parse_ipv4addr`):** Parses 1–4 dot-separated numeric parts (allowing one optional trailing empty part, `L335-L337`), supporting `0x`/`0X` hexadecimal (`L303-L305`), leading-`0` octal (`L306-L309`), and 32-bit packed last-part integers (`L351`: `ipv4 <= u32::MAX >> (8 * numbers.len())`). Thus `0177.0.0.1`, `2130706433`, `0x7f.1`, and `127.0.0.1.` all normalize deterministically to `127.0.0.1`. Furthermore, WHATWG applies UTS #46 `domain_to_ascii` (converting fullwidth dots `。` `U+3002` to `.` and non-ASCII Unicode labels to Punycode `xn--...`, as implemented in `servo/rust-url` `idna/src/uts46.rs`).
   - **RFC 3986 §3.2.2 & Python `3.13.15` `urllib.parse`:** RFC 3986 `IPv4address` strictly admits only four decimal octets without leading zeros; non-matching strings fall through to `reg-name` without canonicalization. In Python `3.13.15`, `urllib.parse.urlsplit` returns `'0177.0.0.1'`, `'2130706433'`, `'0x7f.1'`, `'127.0.0.1.'`, and `'example。com'` verbatim as `hostname` strings. If an allowlist/blocklist checks `hostname in {"127.0.0.1", "localhost"}` on `urllib.parse` output before passing the raw URL to a WHATWG-compliant fetcher or `inet_aton`-backed resolver, loopback/private-network checks fail completely.

#### Cross-Parser Differential Matrix

`Basis: source + execution`

| Test Vector | WHATWG (`ada-url/ada`, `servo/rust-url`) | Strict RFC 3986 (`hyperium/http` `Authority`/`Uri`) | CPython `3.13.15` `urllib.parse.urlsplit` (Executed) |
| :--- | :--- | :--- | :--- |
| `http://allowed.example\@other.example/p` | `host="allowed.example"`, `path="/@other.example/p"` | **Error** (`InvalidUriChar` on `\`) | `host="other.example"`, `netloc="allowed.example\\@other.example"`, `path="/p"` |
| `http://u@allowed.example@other.example/p` | `user="u%40allowed.example"`, `host="other.example"` | Accepted; `host()="other.example"` (`rsplit('@')`) | `host="other.example"`, `netloc="u@allowed.example@other.example"` |
| `http:/example.com/p` | `host="example.com"`, `path="/p"` | No authority (`path="/example.com/p"`) | `host=None`, `path="/example.com/p"` |
| `http:///example.com/p` | `host="example.com"`, `path="/p"` | Empty authority rejected / path-only | `host=None`, `path="/example.com/p"` |
| `http:\\example.com/p` | `host="example.com"`, `path="/p"` | **Error** (`InvalidUriChar` on `\`) | `host=None`, `path="\\\\example.com/p"` |
| `http://exa\tmple.com/a\nb` | `host="example.com"`, `path="/ab"` | **Error** (`InvalidUriChar`) | `host="example.com"`, `path="/ab"` |
| ` \x01http://example.com/\x1f ` | `host="example.com"`, `path="/"` | **Error** (`InvalidUriChar`) | `host="example.com"`, `path="/\x1f "` (trailing C0 retained) |
| `http://0177.0.0.1/` | `host="127.0.0.1"` (IPv4 octal) | `reg-name="0177.0.0.1"` (no numeric normalization) | `host="0177.0.0.1"` (unnormalized) |
| `http://2130706433/` | `host="127.0.0.1"` (packed u32 IPv4) | `reg-name="2130706433"` | `host="2130706433"` (unnormalized) |
| `http://0x7f.1/` | `host="127.0.0.1"` (hex + 2-part IPv4) | `reg-name="0x7f.1"` | `host="0x7f.1"` (unnormalized) |
| `http://127.0.0.1./` | `host="127.0.0.1"` (trailing dot stripped) | `reg-name="127.0.0.1."` | `host="127.0.0.1."` (trailing dot retained) |
| `custom://a\@b/p` | `user="a\\"`, `host="b"` (non-special: `\` not delimiter) | **Error** (`InvalidUriChar` on `\`) | `host="b"`, `netloc="a\\@b"` |
| `http://example。com/` | `host="example.com"` (UTS #46 fullwidth dot `U+3002` -> `.`) | **Error** (non-ASCII byte `InvalidUriChar`) | `host="example。com"` (no IDNA mapping) |

---

### 5. Defensive Verification & Protocol Gateway Invariants

`Basis: derived` (from RFC 9112/9113/7541/9204, WHATWG URL, and inspected implementations)

To eliminate parser differentials across FFI boundaries and multi-hop protocol gateways, system designs and formal verification specifications should enforce six machine-checkable invariants:

1. **Strict Single-Framing Canonicalization at Ingress:** Reject any HTTP/1.1 message containing both `Transfer-Encoding` and `Content-Length`, duplicate `Content-Length` headers, non-final `chunked` in requests, bare `CR`/`LF`, or `SP`/`HTAB` before `:` with `400 Bad Request` and connection close. Disable all `LENIENT_FLAGS.*` on security-critical HTTP/1.1 parsers.
2. **Safe HTTP/2 & HTTP/3 Downgrade Translation:** Never pass raw client `Content-Length` onto a pooled HTTP/1.1 connection while streaming unverified HTTP/2 or HTTP/3 `DATA` frames. Either re-frame the downgraded request using HTTP/1.1 `Transfer-Encoding: chunked` (stripping client `Content-Length`) or buffer the full stream to `END_STREAM` and compute `Content-Length` from exact observed payload byte count. Independently verify `:authority` vs. `Host` equality before emitting `Host`, reject any request containing ignored/malformed headers rather than dropping them silently (closing `nghttp2`'s `NGHTTP2_ERR_IGN_HTTP_HEADER` gap), and validate all serialized header names/values against RFC 9110 `tchar` / RFC 9113 §8.2.1 field-value rules.
3. **QPACK Bounded-State & Watermark Invariants:** Enforce strict upper bounds on `SETTINGS_QPACK_MAX_TABLE_CAPACITY` and `SETTINGS_QPACK_BLOCKED_STREAMS` (setting `SETTINGS_QPACK_BLOCKED_STREAMS = 0` on memory-constrained or DoS-exposed gateways forces non-blocking mode where `RIC <= Known Received Count` for every frame). Verify both modular `RIC` bounds and end-of-block `HBRC_LARGEST_REF_USED` / zero-dynamic-reference invariants.
4. **Explicit Compression-Oracle Policy:** Never rely on codec-internal heuristics (such as `nghttp2`'s `valuelen < 20` cookie rule or `ls-qpack`'s absence of defaults) to protect secrets. Maintain an explicit allowlist of indexable header names (or an explicit denylist covering `Authorization`, `Proxy-Authorization`, `Cookie`, `Set-Cookie`, and application token headers) and set `NGHTTP2_NV_FLAG_NO_INDEX` / `LQEF_NEVER_INDEX` unconditionally across all hops.
5. **Parse-Once, Forward-Structured-AST URL Architecture:** Never validate a URL string with Parser $A$ and hand the original string to HTTP client / Parser $B$. Parse once into a typed URL record (preferring WHATWG for web-facing inputs or strict RFC 3986 with explicit rejection of `\`, userinfo `@`, non-ASCII, and C0 controls for internal service-to-service traffic), resolve DNS once and validate the resolved IP against CIDR blocklists at socket-connect time (eliminating both IPv4 radix tricks and DNS-rebinding TOCTOU), and serialize strictly from the validated structured components.
6. **Differential Fuzzing Harness as Regression Gate:** Mirror T-Reqs's grammar-based string+tree mutation architecture across every front-end/back-end parser pair deployed in a gateway topology, asserting exact equivalence of `(method, canonical_authority, canonical_path, header_multiset, body_length)` or synchronized rejection.

## Boundaries

- **HTTP/3 (`RFC 9114`) framing & QUIC transport packetization (`RFC 9000`):** **not examined** in implementation source beyond QPACK (`RFC 9204`) and `litespeedtech/ls-qpack`. HTTP/3 `DATA`/`HEADERS` frame-type smuggling or QUIC stream-FIN vs. `Content-Length` interactions in specific HTTP/3 servers (e.g., `quiche`, `nghttp3`, `lsquic`) were not directly audited.
- **Commercial CDN & reverse-proxy C/Rust servers (`nginx`, `envoy`, `haproxy`, `varnish`, `apache httpd`):** **not examined** at pinned source commits in this report; T-Reqs empirical server-pair results are cited solely from the published CCS 2021 paper (`DOI: 10.1145/3460120.3485384`) and repository `README.md`.
- **Execution of C/C++/Rust parser binaries (`ada`, `rust-url`, `nghttp2`, `ls-qpack`, `llhttp`, `hyperium/http`):** **not examined** by compiling and executing their native binaries in this environment; findings for those six repositories rest on direct source inspection (`Basis: source`) cross-checked against normative RFC/WHATWG rules (`Basis: normative`) and Python `3.13.15` executable probes (`Basis: execution`).
- **`ls-qpack` prefix underflow exploitability (`RIC = MaxEntries + 1` at `TotalInserts = 0`):** **known not to apply** as a table-corruption vulnerability in `ls-qpack @ 1aeb4f2c73a41318cb726bc1a3d603f43abe509e`, because `parse_header_data` (`lsqpack.c:3534-3542, 3885-3892`) rejects the block if `hbrc_largest_ref` is missing or unreferenced; the divergence from RFC 9204 §4.5.1.1 is strictly the *stage* at which the error is raised (header-data vs. header-prefix).
- **HTTP/1.1 `Transfer-Encoding` chunk-extension & trailer-section smuggling (`RFC 9112 §7.1.1-§7.1.2`):** **not examined** in full cross-implementation detail beyond `llhttp`'s state list (`src/llhttp/http.ts:94-108`).
- **DNS rebinding and IPv6-mapped IPv4 (`[::ffff:127.0.0.1]`) SSRF bypasses:** **not examined** experimentally; note that WHATWG `parse_ipv6addr` (`servo/rust-url` `url/src/host.rs:364-430`) supports embedded dotted-decimal IPv4 suffixes inside IPv6 literals, so host-level IP blocklists must normalize IPv4-mapped IPv6 addresses to IPv4 before CIDR matching.
- **RFC 3986 strict compliance of `urllib.parse`:** **known not to apply** — Python `3.13.15`'s `urllib.parse` is a hybrid parser that applies partial WHATWG-style stripping (embedded `\t`/`\r`/`\n` and leading C0/space) while retaining RFC-like `//` authority rules and unnormalized IPv4/backslash behavior.

## Evidence

### Primary Git Repository Sources (Observed 2026-11-19)

1. **`nghttp2/nghttp2`** @ `9633d1d960c147578183760232fe32e55a6ee3f5`
   - `lib/nghttp2_hd.h:40, 200-212`: `NGHTTP2_HD_ENTRY_OVERHEAD = 32`, `nghttp2_hd_context`.
   - `lib/nghttp2_hd.c:811-813`: `entry_room(namelen, valuelen)` returning `32 + namelen + valuelen`.
   - `lib/nghttp2_hd.c:1052-1053, 1395-1403`: automatic `NGHTTP2_HD_NEVER_INDEXING` (`0x10`) heuristic for `NGHTTP2_TOKEN_AUTHORIZATION`, `NGHTTP2_TOKEN_COOKIE` with `nv->valuelen < 20`, or explicit `NGHTTP2_NV_FLAG_NO_INDEX`.
   - `lib/nghttp2_hd.c:1815-1817, 1862-1864`: propagation of decoded `no_index` bit to `NGHTTP2_NV_FLAG_NO_INDEX`.
   - `lib/nghttp2_hd.c:1963-2018`: enforcement that dynamic table size updates (`(*in & 0xE0U) == 0x20U`) occur only in `NGHTTP2_HD_STATE_INFLATE_START` and stay within `min(min_hd_table_bufsize_max, settings_hd_table_bufsize_max)`.
   - `lib/nghttp2_hd_huffman.c:136-140`: Huffman EOS padding validation (`final && !(ctx->flags & NGHTTP2_HUFF_ACCEPTED)` -> `NGHTTP2_ERR_HEADER_COMP`).
   - `lib/nghttp2_http.c:194-341, 412-494, 535-558`: `http_request_on_header` (disallowed connection headers `L295-L300`, `te: trailers` `L301-L305`, duplicate `content-length` `L284-L292`, `:authority` hard failure vs. `Host` `NGHTTP2_ERR_IGN_HTTP_HEADER` at `L199-L204` vs. `L276-L283`), `nghttp2_http_on_request_headers` (`L467-L472` showing presence-only check without `:authority == Host` comparison), and `nghttp2_http_on_data_chunk` / `nghttp2_http_on_remote_end_stream` (`L535-L558`).
2. **`litespeedtech/ls-qpack`** @ `1aeb4f2c73a41318cb726bc1a3d603f43abe509e`
   - `lsqpack.h:54-55, 70-105, 199-201, 263-265, 781-784`: encoder options, `LQEF_NEVER_INDEX`, `qpd_max_risked_streams`, `qpd_max_entries`.
   - `lsqpack.c:220, 581, 1268-1269`: `DYNAMIC_ENTRY_OVERHEAD = 32u`, `qpe_max_entries = max_table_size / 32`, `encoded_largest_ref = hinfo->qhi_max_id % (2 * enc->qpe_max_entries) + 1`.
   - `lsqpack.c:1522-1580`: `qenc_entry_is_draining` (25% capacity threshold) and `qenc_dup_draining`.
   - `lsqpack.c:1663-1664, 1720, 2056-2094`: `LSXPACK_NEVER_INDEX` / `LQEF_NEVER_INDEX` propagation and wire `N`-bit encoding (`0x20 | (N<<4)`, `0x40 | (N<<5)`, `N<<3`).
   - `lsqpack.c:2744-2748, 2784-2787, 3533-3542, 3885-3895, 3909-4051, 4135-4225`: `ID_MINUS`/`ID_PLUS`, `qdec_in_future`, `parse_header_prefix`, `stash_blocked_header` (`qpd_n_blocked < qpd_max_risked_streams`), `qdec_try_writing_header_ack` (`0x80` + 7-bit stream ID), and `check_dyn_table_errors` (`HBRC_LARGEST_REF_USED` / `HBRC_DYN_USED_IN_ERR`).
3. **`nodejs/llhttp`** @ `0ae8c68c3c5a8fce13dbff87190e1ba40d8f9666`
   - `src/llhttp/http.ts:240, 328, 426, 537, 563, 572, 590-637, 669, 710-731, 752, 775-778, 837-864, 898`: `CL`+`TE` mutual exclusion (`LENIENT_FLAGS.CHUNKED_LENGTH`), non-final `chunked` rejection (`LENIENT_FLAGS.TRANSFER_ENCODING`), duplicate `Content-Length` rejection, space-before-colon (`LENIENT_FLAGS.HEADERS`), and bare `CR`/`LF` flags (`OPTIONAL_CR_BEFORE_LF`, `OPTIONAL_LF_AFTER_CR`).
4. **`ada-url/ada`** @ `d1fcb0b93c0d17436303384708ecdab2d003068c`
   - `src/parser.cpp:1956-1964`: `remove_ascii_tab_or_newline` and `trim_c0_whitespace`.
   - `src/parser.cpp:2142-2285, 2395-2454`: `state::AUTHORITY` (multi-`@` `%40` encoding, special-scheme `\` termination, empty-host failure) and `state::SPECIAL_AUTHORITY_IGNORE_SLASHES`.
5. **`servo/rust-url`** @ `e219288fc2702301803e72f7efb66d3c5c25c980`
   - `url/src/parser.rs:159-162, 374-475, 824-899`: `SchemeType`, `Input::new_trim_c0_control_and_space`, `parse_with_scheme` (`count_matching(|c| matches!(c, '/' | '\\'))`), and `parse_userinfo` (rightmost `@`, `'\\' if scheme_type.is_special() => break`, empty-host error).
   - `url/src/host.rs:297-361`: `parse_ipv4number` (base 8/10/16) and `parse_ipv4addr` (1–4 parts, trailing dot pop, `u32::MAX >> (8 * numbers.len())`).
   - `idna/src/uts46.rs`: UTS #46 IDNA domain processing.
6. **`hyperium/http`** @ `a8309a93ce24c19c89cf36bfac504ebed7b96dc7`
   - `src/uri/authority.rs:428-446, 474-569`: `host()` (`rsplit('@')`) and `validate_authority_bytes` (strict `URI_CHARS` rejection of `\`, whitespace, C0, and non-ASCII; `%` rejected outside userinfo and IPv6 zones; multiple `@` resetting `at_sign_pos`/`colon_cnt`/`has_percent`).
7. **`bahruzjabiyev/t-reqs-http-fuzzer`** @ `b90f97e4f39afbe39c66ecfe99fae1b832b20f62`
   - `README.md:1-96`: CFG grammar specification, string-mutable vs. tree-mutable operators, and reverse-proxy body-length differential feedback oracle.

### Normative Standards and Peer-Reviewed Literature

- Jabiyev, B., Sprecher, S., Onarlioglu, K., & Kirda, E. (2021). *T-Reqs: HTTP Request Smuggling with Differential Fuzzing.* ACM CCS 2021, pp. 1805–1820. DOI: `10.1145/3460120.3485384`.
- IETF RFC 9112 (*HTTP/1.1*, June 2022), §2.2, §5.1, §6.3.
- IETF RFC 9113 (*HTTP/2*, June 2022), §8.2.1, §8.2.2, §8.3.1.
- IETF RFC 7541 (*HPACK: Header Compression for HTTP/2*, May 2015), §4.1–§4.4, §5.2, §6.2.3, §6.3, §7.1.
- IETF RFC 9204 (*QPACK: Field Compression for HTTP/3*, June 2022), §2.1.2, §4.4–§4.5.6, §5, §7.1.
- IETF RFC 3986 (*Uniform Resource Identifier (URI): Generic Syntax*, January 2005), §3, §3.2.1–§3.2.2.
- WHATWG URL Living Standard (`https://url.spec.whatwg.org/`), Basic URL Parser, Authority State, IPv4 Parser.

### Reproducible Execution Probe (`CPython 3.13.15`, Observed 2026-11-19)

Command executed on Linux x86_64 with `Python 3.13.15`:

```bash
python3 - <<'PY'
import urllib.parse

def rfc9204_encode_ric(ric, cap):
    me = cap // 32
    return 0 if ric == 0 else (ric % (2 * me)) + 1

def rfc9204_decode_ric(enc, total, cap):
    me = cap // 32
    if enc == 0:
        return 0, "ok"
    fr = 2 * me
    if enc > fr:
        return None, "QPACK_DECOMPRESSION_FAILED(encoded > FullRange)"
    mv = total + me
    mw = (mv // fr) * fr
    ric = mw + enc - 1
    if ric > mv:
        if ric <= fr:
            return None, "QPACK_DECOMPRESSION_FAILED(underflow)"
        ric -= fr
    if ric == 0:
        return None, "QPACK_DECOMPRESSION_FAILED(ric==0)"
    return ric, ("blocked" if ric > total else "ready")

def lsqpack_in_future(enc, total, cap):
    me = cap // 32
    fr = 2 * me
    if enc == 0:
        return "ready"
    if enc > fr:
        return "LQRHS_ERROR"
    last_id = (total - 1) % fr
    largest_ref = (enc + fr - 2) % fr
    if last_id < me:
        fut = (largest_ref > last_id) and (largest_ref <= last_id + me)
    else:
        fut = not (largest_ref <= last_id and largest_ref >= last_id - me + 1)
    return "LQRHS_BLOCKED" if fut else "LQRHS_READY"

for ric, total in [(0,0),(1,0),(128,0),(129,0),(256,250),(250,256),(129,256),(128,256)]:
    enc = rfc9204_encode_ric(ric, 4096)
    print(ric, total, enc, rfc9204_decode_ric(enc, total, 4096), lsqpack_in_future(enc, total, 4096))

for u in [
    "http://allowed.example\\@other.example/p",
    "http://u@allowed.example@other.example/p",
    "http:/example.com/p",
    "http:///example.com/p",
    "http:\\\\example.com/p",
    "http://exa\tmple.com/a\nb",
    " \x01http://example.com/\x1f ",
    "http://0177.0.0.1/",
    "http://2130706433/",
    "http://0x7f.1/",
    "http://127.0.0.1./",
    "custom://a\\@b/p",
    "http://example\u3002com/",
]:
    r = urllib.parse.urlsplit(u)
    print(repr(u), "->", r.scheme, repr(r.netloc), repr(r.hostname), repr(r.path))
PY
```

Observed HPACK RFC 7541 dynamic table probe (`max_size = 128`, `overhead = 32`): inserting `(x-a, 8B)` takes `43B` (`43/128`), `(x-b, 8B)` takes `43B` (`86/128`), `(x-c, 16B)` takes `51B` evicting `x-a` (`94/128`, 2 entries), and `(x-big, 100B)` (`137B > 128B`) evicts all entries leaving `0/128` without raising a protocol error (RFC 7541 §4.4).

## Revalidation

To revalidate these findings against newer upstream commits or an alternative gateway stack with minimal effort:

1. **HTTP/1.1 & HTTP/2 Validation Diff Check:**
   - Diff `nodejs/llhttp` `src/llhttp/http.ts` around `LENIENT_FLAGS` (`CHUNKED_LENGTH`, `TRANSFER_ENCODING`, `HEADERS`, `OPTIONAL_CR_BEFORE_LF`, `OPTIONAL_LF_AFTER_CR`) to verify whether strict defaults remain unchanged.
   - Diff `nghttp2/nghttp2` `lib/nghttp2_http.c` (`http_request_on_header`, `nghttp2_http_on_request_headers`) to check whether `:authority == Host` validation has been added or whether invalid regular headers still return `NGHTTP2_ERR_IGN_HTTP_HEADER`.
2. **HPACK/QPACK Policy & Watermark Check:**
   - Diff `nghttp2/nghttp2` `lib/nghttp2_hd.c` around `NGHTTP2_HD_NEVER_INDEXING` (`L1399-L1403`) to verify automatic sensitive-header rules.
   - Diff `litespeedtech/ls-qpack` `lsqpack.c` around `qdec_in_future`, `parse_header_prefix`, and `check_dyn_table_errors` to confirm whether initial-state `RIC > MaxEntries` underflow is now caught in `parse_header_prefix` or remains deferred to `parse_header_data`.
3. **URL Parser Differential Smoke Suite:**
   - Execute the 13-vector URL table from Section 4 against both the policy-validator parser and the HTTP-client parser in any target stack. Any pair that returns differing `(scheme, host, port)` triples—or where one returns a valid host while the other normalizes IPv4/IDNA differently—invalidates raw-string forwarding between them.
4. **Limitation of Cheap Probes:** Passing the 13 URL vectors or the QPACK modular check verifies only those specific invariants; validating an entire proxy-origin deployment requires running a grammar-based differential fuzzer (such as T-Reqs) against the exact compiled server pair and configuration flags in staging.
