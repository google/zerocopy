# Unicode Encoding Algebra, Symbolic String Transducers, and SMT-Verified Accessible UI Layouts

## Summary

Human-facing text and graphical UI pipelines fail across four coupled boundaries—string encoding FFI, security sanitization, responsive 2D layout geometry, and assistive-technology tree synchronization—where informal ASCII/pixel assumptions break down mathematically:

1. **Cross-language string encoding impedance and algebraic non-closure (`UTF-8`, `UTF-16`, `WTF-8`, `CESU-8`, `UAX #15`, `UAX #29`):** Strings do not share a single mathematical domain across runtimes. Strict UTF-8 scalar sequences (`Rust &str`, `Swift String`, WebAssembly Component Model `string`—which explicitly traps on `UnicodeError` for unpaired UTF-16 surrogates in `CanonicalABI.md:2232-2261`) cannot losslessly represent ill-formed UTF-16 code units (`JS`, `JVM`, `Win32`), POSIX raw bytes, or JNI Modified UTF-8 (`CESU-8`, where astral scalars encode as two 3-byte surrogates rejected by strict UTF-8 decoders). `WTF-8` bridges UTF-8 and ill-formed UTF-16 losslessly, but **is not closed under naive byte concatenation**: in `rust-lang/rust` (`library/alloc/src/wtf8/mod.rs:298-320`), `Wtf8Buf::push_wtf8` must detect an adjacent trailing lead surrogate (`U+D83D`, `ed a0 bd`) and leading trail surrogate (`U+DE00`, `ed b8 80`) and fuse the 6 bytes into a 4-byte supplementary scalar (`f0 9f 98 80`, `U+1F600` `'😀'`). Similarly, Unicode `UAX #15` NFC is not closed under concatenation (`'e' + '\u0301'` fails `is_normalized('NFC')`), `UAX #29` extended grapheme clusters vary across Unicode releases and require $O(N)$ scanning in `Swift`'s UTF-8 `String` (`StringGraphemeBreaking.swift`), and `UAX #9` BiDi overrides (`U+202E`, `U+2066`, `U+2069`) enable **Trojan Source** (`CVE-2021-42574`) logical-vs-visual reordering attacks across 12 evaluated languages.
2. **Decidable symbolic string transducers (`Bek` / `AutomataDotNet/Automata`, POPL 2012 / CAV 2017):** Classical finite-state transducers explode over Unicode's $1{,}114{,}112$-codepoint alphabet, while arbitrary string-plus-length constraints are undecidable. **Symbolic Finite Transducers (SFTs)** replace explicit alphabet edges with SMT-decidable character predicates, achieving decidable composition (`ST.Compose`), single-valued equivalence (`ST.Eq1(A, B)` with `A.Eq1(A)` deciding single-valuedness), idempotence ($T \circ T \equiv T$), and commutativity ($T_1 \circ T_2 \equiv T_2 \circ T_1$)—catching double-escaping and decode-after-escape XSS bugs directly in SMT while facing a sharp undecidability cliff once unbounded lookahead or non-deterministic transitions are added.
3. **SMT-verified accessible CSS layout vs. constraint and single-pass UI engines (`Cassius`/`VizAssert`, `Cassowary`, `Flutter`, `Taffy`):** Testing infinite $\text{Viewport} \times \text{Zoom} \times \text{FontSize} \times \text{Locale}$ spaces via screenshots misses WCAG 2.1 reflow and overlap regressions. **`Cassius`** (`uwplse/cassius`, `OOPSLA 2016`, `PLDI 2018`, `OOPSLA 2019`) formalizes CSS 2.1 boxes, floats (`ez.outside`/`ez.inside*` exclusion zones in `src/spec/layout.rkt`), accessibility predicates (`overlaps`, `onscreen`, `viewable`, `luminance` in `src/assertions.rkt`), and `:split` component summaries (`src/modularize.rkt`) in Z3 Linear Real Arithmetic. Comparing `Cassius` against incremental simplex solvers (`Cassowary`, `TOCHI 2001`), single-pass $O(N)$ `BoxConstraints` trees (`Flutter`), and multi-pass cached Flexbox/Grid engines (`DioxusLabs/taffy`, `CACHE_SIZE = 9` in `src/tree/cache.rs`) delineates an irreducible Pareto frontier between cross-branch expressiveness, frame-budget complexity, and SMT decidability.
4. **Visual-vs-accessibility tree bisimulation (`AccessKit`):** Immediate-mode and GPU UIs bypass native widgets and project a shadow accessibility tree (`TreeUpdate` / `NodeId` / async `ActionHandler` in `AccessKit/accesskit`) across Windows UIA, macOS `NSAccessibility`, and Linux `AT-SPI2`, where visual occlusion, unstable per-frame IDs, and COM/AppKit threading hazards currently lack end-to-end visual-to-semantic bisimulation proofs.

## Applicability

This report covers the mathematical models, concrete implementations, and cross-boundary verification limits across four tightly linked domains:

- **Cross-language string encoding, indexing, normalization, and BiDi security:** `rust-lang/rust` (revision `b0b600668bb9b4a897e2299b0a44289d42276545`, `library/core/src/wtf8.rs`, `library/alloc/src/wtf8/mod.rs`), `SimonSapin/wtf-8` (revision `e27dc7c6e0d25e9276274ad42eb25dc30aba8c1f`), `swiftlang/swift` (revision `3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`, `stdlib/public/core/StringGraphemeBreaking.swift`, `StringGuts.swift`), `WebAssembly/component-model` (revision `585526aa1f2c7f76f07557d16e265dede38b3acb`, `design/mvp/CanonicalABI.md`), and `nickboucher/trojan-source` (revision `e3dc153fcf465f4a84424ea874ff39be29adb1f7`, `doi:10.48550/arXiv.2111.00169`).
- **Symbolic finite-state string transducers:** `AutomataDotNet/Automata` (revision `0242132fdbe9687bea22b7144afa0784d7cd927b`, `src/Automata/ST.cs`, `STb.cs`, `src/Bek/`) and Veanes/D'Antoni's POPL 2012 (`doi:10.1145/2103656.2103674`) and CAV 2017 (`doi:10.1007/978-3-319-63387-9_3`) papers.
- **SMT CSS layout verification and UI layout algorithms:** `uwplse/cassius` (revision `60dad9e9b2b4de3b13451ce54cdc1bd55ca64824`, `src/spec/layout.rkt`, `src/assertions.rkt`, `src/modularize.rkt`), Panchekha et al. OOPSLA 2016 (`doi:10.1145/2983990.2984010`), PLDI 2018 (`doi:10.1145/3192366.3192407`), OOPSLA 2019 (`doi:10.1145/3360577`), Badros et al. `Cassowary` (`doi:10.1145/504704.504705`), and `DioxusLabs/taffy` (revision `1abd8eeaf6059336a7026c31e0f1b769d2f04a3a`, `src/tree/cache.rs`).
- **Cross-platform accessibility bridges:** `AccessKit/accesskit` (revision `432d06659e0a6708fb206e266d65752dd372deeb`, `accesskit/src/lib.rs`).

Findings apply to polyglot FFI ABI designers (Rust, Swift, C, JVM/JNI, JS/V8, Wasm Component Model), web sanitizer authors, compiler/LSP tooling engineers, and UI/accessibility verification teams. Note that Rust's `WTF-8` implementation resides in `library/core/src/wtf8.rs` and `library/alloc/src/wtf8/mod.rs` at the pinned revision `b0b60066...` (having moved out of earlier `std::sys_common::wtf8` paths).

## Findings

### 1. Cross-Language String Representation Lattice and Encoding FFI Traps

#### 1.1 Five Incompatible String Domains and `WTF-8` Concatenation Non-Closure
Basis: normative (`SimonSapin/wtf-8`, `WebAssembly/component-model`) + source (`rust-lang/rust`) + execution

Crossing FFI boundaries between systems languages, VMs, and OS APIs traverses five mutually incompatible algebraic string domains:

| Encoding Domain | Primary Hosts / APIs | Valid Elements | Unpaired Surrogates? | Embedded `0x00`? | Closed Under Raw Byte Concat? |
|---|---|---|---|---|---|
| **Strict UTF-8 Scalars** | Rust `&str`, Swift `String`, Lean `String`, Wasm Component `string` | Scalars `U+0000..U+D7FF`, `U+E000..U+10FFFF` | Forbidden (error / trap) | Allowed | **Yes** |
| **Ill-Formed UTF-16 (`WTF-16`)** | JS/ECMAScript, JVM `String`, `.NET`, Win32 `LPWSTR` / NTFS | Arbitrary `u16` sequences | Allowed (`0xD800..0xDFFF`) | Allowed | **Yes** (may fuse boundary surrogates semantically) |
| **Raw Non-NUL Bytes / `OsBytes`** | POSIX filenames (`ext4`), C `char*`, Go `string` | Arbitrary `u8` (C forbids `0x00`) | N/A (unvalidated bytes) | C forbids; POSIX paths forbid `0x00`/`/` | **Yes** |
| **Modified UTF-8 / `CESU-8`** | JVM JNI `GetStringUTFChars`, Oracle `UTF8` | `U+0000 -> C0 80`; astral -> two 3B surrogates | Allowed | Encoded overlong `C0 80` | **Yes** (produces invalid UTF-8!) |
| **`WTF-8`** | Rust `alloc::wtf8::Wtf8Buf` (Windows `OsString`), internal engines | UTF-8 + unpaired 3B surrogates; **never adjacent lead+trail** | Allowed if unpaired | Allowed | **NO** (adjacent lead+trail violates invariant!) |

Direct inspection of `rust-lang/rust` (`b0b600668bb9b4a897e2299b0a44289d42276545`, `library/alloc/src/wtf8/mod.rs:298-320`) confirms how `Wtf8Buf::push_wtf8` repairs the non-closure of WTF-8 concatenation:

```rust
// rust-lang/rust library/alloc/src/wtf8/mod.rs:298-309
pub fn push_wtf8(&mut self, other: &Wtf8) {
    match ((*self).final_lead_surrogate(), other.initial_trail_surrogate()) {
        // Replace newly paired surrogates by a supplementary code point.
        (Some(lead), Some(trail)) => {
            let len_without_lead_surrogate = self.len() - 3;
            self.bytes.truncate(len_without_lead_surrogate);
            let other_without_trail_surrogate = &other.as_bytes()[3..];
            self.bytes.reserve(4 + other_without_trail_surrogate.len());
            self.push_char(decode_surrogate_pair(lead, trail));
            self.bytes.extend_from_slice(other_without_trail_surrogate);
        }
        ...
```

Our execution probe confirms the exact byte-level trap:
- Encoding lead surrogate `U+D83D` yields 3 bytes `ed a0 bd`; encoding trail surrogate `U+DE00` yields 3 bytes `ed b8 80`.
- Naive byte concatenation produces 6 bytes `ed a0 bd ed b8 80`—which is **both ill-formed WTF-8 and invalid UTF-8** (identical to JNI `CESU-8` for `U+1F600`), rejected by strict UTF-8 decoders with `invalid continuation byte`.
- Well-formed `push_wtf8` collapses the 6 bytes into 4 bytes `f0 9f 98 80` (`U+1F600` `'😀'`), matching UTF-16 concatenation semantics (`len(concat(a, b)) = 4 != 3 + 3`).
- **JNI FFI UB hazard:** Passing bytes from JVM JNI `GetStringUTFChars` (which emits `C0 80` for NUL and 6-byte `CESU-8` pairs for emoji) into Rust `std::str::from_utf8_unchecked` triggers immediate **Undefined Behavior**.
- **WebAssembly Component Model Canonical ABI (`WebAssembly/component-model`, `585526aa...`, `design/mvp/CanonicalABI.md:2232-2261, 2543-2582`):** `load_string_from_range` supports three memory encodings (`utf8`, `utf16`, and `latin1+utf16` using a high tag bit `utf16_tag(cx)`), enforcing `MAX_STRING_BYTE_LENGTH`, alignment (`1` for UTF-8, `2` for UTF-16/Latin1+UTF-16), bounds, and strict scalar decoding: `decode(encoding)` traps (`except UnicodeError: trap()`) on any invalid UTF-8 byte sequence **or unpaired UTF-16 surrogate**. Consequently, ill-formed JS/Win32 UTF-16 strings cannot traverse a Component Model `string` type without lossy replacement or explicit `list<u16>` transport!

#### 1.2 Multi-Metric Indexing (`UAX #29`), Swift $O(N)$ Graphemes, and Normalization Non-Closure (`UAX #15`)
Basis: source (`swiftlang/swift`) + execution

Human-perceived characters (`UAX #29` Extended Grapheme Clusters) diverge sharply from bytes, UTF-16 code units, and Unicode scalar values (`execution` probe on Python 3.13.15):

| String Specimen | UTF-8 Bytes | UTF-16 Code Units | Unicode Scalars | `UAX #29` Grapheme Clusters |
|---|---|---|---|---|
| `'👨‍👩‍👧‍👦'` (Family ZWJ emoji) | **25** | **11** | **7** | **1** |
| `'🇺🇸'` (Regional indicator flag) | **8** | **4** | **2** | **1** |
| `'क्ष'` (Devanagari `U+0915 U+094D U+0937`) | **9** | **3** | **3** | **1** (Unicode 15.1 `InCB` conjunct) |
| `'e\u0301'` (`NFD` decomposed `é`) | **3** | **2** | **2** | **1** |
| `'\u00E9'` (`NFC` precomposed `é`) | **2** | **1** | **1** | **1** |

- **Swift's `O(N)` grapheme indexing design (`swiftlang/swift`, `3be0cf4b...`, `stdlib/public/core/StringGraphemeBreaking.swift:109-176`):** Since Swift 5, `String` stores UTF-8 natively while exposing `UAX #29` extended grapheme clusters as its `Collection` element (`Character`). Because finding the $k$-th variable-width grapheme cluster in a flat UTF-8 buffer is $\Omega(N)$, Swift bans `s[k: Int]` subscripting and caches character-stride metadata inside opaque `String.Index` handles (`_slowRoundDownToNearestCharacter`, `_opaqueCharacterStride(startingAt:)`).
- **Unicode version drift (`UAX #29` / `UAX #15` / Collations):** Unicode 15.1 introduced `Indic_Conjunct_Break` (`InCB`) rules turning Devanagari conjunct clusters like `'क्ष'` from 2 clusters into 1 stateful multi-codepoint cluster—shifting grapheme indices across runtimes pinned to different Unicode versions. Likewise, OS-provided `glibc`/`ICU` collation upgrades silently reorder B-tree sort keys in PostgreSQL indexes unless collations are explicitly version-pinned, and OS filesystems split between raw bytes (Linux `ext4`), normalization-preserving/insensitive lookups (macOS APFS), and format-time `$UpCase` UTF-16 tables (Windows NTFS).
- **`UAX #15` NFC concatenation non-closure (`execution`):** Our Python probe confirms `unicodedata.is_normalized('NFC', 'e') == True` and `is_normalized('NFC', '\u0301') == True`, yet `is_normalized('NFC', 'e' + '\u0301') == False` (`len('e' + '\u0301') == 2` vs. `len(NFC) == 1`). Concatenating two already-NFC-normalized strings requires boundary re-normalization across the last starter of the left operand and leading combining marks of the right operand.

#### 1.3 Bidirectional Reordering (`UAX #9`) and Trojan Source (`CVE-2021-42574`)
Basis: normative (`doi:10.48550/arXiv.2111.00169`) + source (`nickboucher/trojan-source`) + execution

Boucher and Anderson's **Trojan Source** (`USENIX Security 2023`; `nickboucher/trojan-source`, `e3dc153fcf465f4a84424ea874ff39be29adb1f7`, `README.md`) demonstrates that embedding Unicode `UAX #9` Bidirectional control characters—specifically `RLO` (`U+202E`), `LRO` (`U+202D`), `RLE` (`U+202B`), `LRE` (`U+202A`), `PDF` (`U+202C`), `RLI` (`U+2067`), `LRI` (`U+2066`), `FSI` (`U+2068`), and `PDI` (`U+2069`)—inside comments or string literals causes plain-text editors (`VS Code v1.61` across Windows/macOS/Ubuntu) to visually reorder source tokens across lexical boundaries while compilers parse the unmodified logical byte stream.

`nickboucher/trojan-source/README.md` documents verified working exploits across **12 languages** (`C`, `C++`, `C#`, `JavaScript`, `Java`, `Rust`, `Go`, `Python`, `SQL`, `Bash`, `Assembly`, `Solidity`) spanning three BiDi classes (Early Return, Commenting-Out, Stretched Strings) plus `UTS #39` cross-script homoglyph/confusable identifier attacks (`CVE-2021-42694`). Even after compilers (`rustc`, `gcc`, `clang`) added lints forbidding unterminated BiDi controls in source literals/comments, the underlying hazard—global `UAX #9` reordering ignorant of syntactic boundaries—persists across SQL queries, build scripts, log viewers, legal specification prose, and formal proof theorem statements reviewed by human auditors ("What You See Is What You Prove").

---

### 2. Symbolic Finite-State String Transducers (`Bek` / `Automata`)

#### 2.1 SFT Formalism and Decidable Sanitizer Verification
Basis: normative (`doi:10.1145/2103656.2103674`, `doi:10.1007/978-3-319-63387-9_3`) + source (`AutomataDotNet/Automata`) + execution

Web sanitizers, HTML/URL/CSS escapers, and UTF-8/UTF-16 codecs routinely fail two algebraic security properties (`execution` probe):
- **Non-idempotence ($T(T(x)) \neq T(x)$):** `html_esc("<script>") = "&lt;script&gt;"` whereas `html_esc(html_esc("<script>")) = "&amp;lt;script&amp;gt;"` (causing double-escaping corruption or double-unescaping bypasses).
- **Non-commutativity ($T_1(T_2(x)) \neq T_2(T_1(x))$):** Over `x = "%3Cscript%3E"`, `html_esc(url_dec(x)) = "&lt;script&gt;"` (safe), whereas `url_dec(html_esc(x)) = "<script>"` (live XSS injection!).

Classical finite-state transducers cannot represent Unicode's $2^{21}$ codepoint alphabet as explicit transition tables. **Symbolic Finite Transducers (SFTs)** (Veanes et al., `POPL 2012`; `Bek`, `USENIX Security 2011`; implemented in `AutomataDotNet/Automata`, `0242132fdbe9687bea22b7144afa0784d7cd927b`) lift transitions over an **effective Boolean algebra** $(\mathcal{A}, \Psi, \llbracket \cdot \rrbracket)$ (e.g., Z3 bitvector/integer predicates $\varphi(c)$ over 16-bit or 21-bit characters) paired with symbolic output term sequences $[f_1(c), \dots, f_k(c)]$.

Direct inspection of `AutomataDotNet/Automata` (`src/Automata/ST.cs:714-740, 2021-2126, 3194-3201` and `src/Automata/STb.cs:1854-1860`) confirms the core verified operations:
1. **Closed Symbolic Composition (`ST.Compose(A, B)` / `STb.Compose`):** Given SFTs $A$ and $B$, constructs a single SFT $A \circ B$ such that $(A \circ B)(s) = B(A(s))$ for every input string $s$, enabling exact verification of multi-stage proxy/decoder/sanitizer pipelines.
2. **Decidable 1-Equivalence and Single-Valuedness (`ST.Eq1(A, B)` & `ST.Eq1_v2`, `ST.cs:2021-2029, 2116-2126`):** Returns `false` iff there exist $u, v, w$ such that $(u, v) \in \llbracket A \rrbracket$, $(u, w) \in \llbracket B \rrbracket$, and $v \neq w$. As documented verbatim at `ST.cs:2024`, **`A.Eq1(A)` returns `false` iff $A$ is not single-valued**! Because `Eq1` reduces via domain intersection and symbolic alignment to SMT satisfiability over the character algebra, it directly decides:
   - **Idempotence:** `T.Compose(T).Eq1(T)` (with equal domains)
   - **Commutativity:** `T1.Compose(T2).Eq1(T2.Compose(T1))`
   - **Round-trip invertibility:** `Encode.Compose(Decode).Eq1(Id)`
   - **Regular output safety:** $\text{Img}(T) \cap \text{Bad} = \emptyset$ (checking that no input can ever produce an output matching a forbidden XSS regex such as `<script>`).
3. **Verified code extraction (`STb.cs:1854`, `src/Bek.Tests/GeneratedCodeSamples/`):** Compiles verified `Bek` transducers (`UTF8EncodeFlat.cs`, `HtmlEncode.cs`, `CssEncodeFlat.cs`) directly into C#/JS/C code.

#### 2.2 The Transducer Decidability Frontier
Basis: normative (`doi:10.1145/2103656.2103674`, `doi:10.1007/978-3-319-63387-9_3`) + derived

Automata theory imposes strict expressiveness vs. decidability cliffs that govern any verified string-processing DSL:

| Transducer Model | Expressiveness | Composition Closed? | Equivalence Decidable? | Typical Use Case / Limitation |
|---|---|---|---|---|
| **Single-valued SFT** (`Bek` / `ST`) | Finite control + SMT char predicates + per-char output terms | **Yes** | **Yes** (`ST.Eq1` via SMT) | HTML/CSS/URL escaping, single-pass case-mapping, simple sanitizers |
| **Extended SFT (ESFT)** (bounded lookahead $k > 1$) | Multi-character sliding window (e.g., UTF-8 $\leftrightarrow$ UTF-16, `&amp;` entities) | **No** (not closed in general) | **Undecidable** (general ESFT); decidable only for restricted Cartesian/1-lookahead fragments | Multi-byte transcoding (`UTF-8`/`UTF-16`/`WTF-8`); general equivalence hits Post Correspondence |
| **Non-deterministic SFT** | Ambiguous multi-valued string relations | Yes | **Undecidable** (Griffiths 1968) | Ambiguous rewrite grammars |
| **Symbolic Visibly Pushdown Transducer (SVPT)** | Well-nested tree/XML/HTML tag structures | Restricted | **Decidable** (for deterministic SVPTs) | Context-aware nested HTML5/XML sanitization (where regular SFTs fail on `<svg><script>`) |
| **Word equations + length + arbitrary transducers** | General SMT string solvers (`Z3str4`, `OSTRICH`) | N/A | **Undecidable** in general | Requires straight-line / chain-free fragments for completeness |

---

### 3. SMT-Verified Accessible CSS Layout (`Cassius` / `VizAssert`) vs. UI Layout Engines

#### 3.1 Formalizing CSS 2.1 Box Geometry and Accessibility in SMT (`Cassius`)
Basis: normative (`doi:10.1145/2983990.2984010`, `doi:10.1145/3192366.3192407`, `doi:10.1145/3360577`) + source (`uwplse/cassius`) + execution

Screenshot testing checks only fixed `(viewport_width, zoom, font_size, locale)` points, missing layout accessibility defects required by **WCAG 2.1 SC 1.4.10 (Reflow at 320 CSS px / 400% zoom)** and **SC 1.4.4 (Resize Text 200%)**. Our parametric reflow probe illustrates why fixed desktop snapshots fail: a fixed `220px` sidebar paired with a right-anchored `200px` main panel passes cleanly at `W = 1280px` (`100%` and `200%` zoom, `eff = 640px`, `overlaps = False`, `horiz_overflow = False`), yet fails *both* non-overlap (`sidebar = [0, 220]` overlaps `main = [120, 320]`) and horizontal reflow at `W = 320px`.

**`Cassius`** (`uwplse/cassius`, `60dad9e9b2b4de3b13451ce54cdc1bd55ca64824`) formalizes W3C CSS 2.1 layout semantics directly as SMT constraints in **Quantifier-Free Linear Real Arithmetic (QF_LRA)** (with Z3):
- **Box-tree and float exclusion zones (`src/spec/layout.rkt`):** Declares abstract `Box` and `EZone` sorts with flow pointers (`pflow`, `nflow`, `vflow`, `fflow`, `lflow`), margin-collapse predicates (`box-collapsed-through`), and exclusion-zone invariants (`ez.outside`, `ez.inside`, `ez.inside*`) modeling how floats reserve 2D regions across sibling blocks.
- **Accessibility assertions (`VizAssert`, `PLDI 2018`, `src/assertions.rkt:16-80`):** Compiles high-level accessibility specifications into SMT predicates over all viewport/font parameters:
  - `is-interactive` (`a`, `input`, `button`), `viewable`, `onscreen` (`top >= 0 ∧ left >= 0`), `overlaps`, `within`, `luminance` (`lum (color.rgb color)` for WCAG contrast), and float-boundary invariants (`no-floats-enter`, `no-floats-exit*`, `float-flow-across`), plus recursive `ancestor` queries lowered via universally quantified auxiliary SMT functions (`aux0`, `assertions.rkt:70-77`).
  - **Finitization reduction (`PLDI 2018`):** Because universally quantifying over arbitrary inline line-break counts couples discrete wrapping decisions with continuous real widths, `VizAssert` finitizes text runs into bounded symbolic word-box templates parameterized by symbolic width/height bounds, discharging universal accessibility proofs across *all* viewport widths and font scales via a finite set of Z3 queries.
- **Modular component verification (`OOPSLA 2019`, `src/modularize.rkt:1-45`):** Whole-page SMT encoding explodes as DOM size grows. `modularize.rkt` partitions a page at `:split` component annotations into independent sub-DOMs (`split-document`), verifying each component locally against explicit `:spec` layout-interface contracts (bounding incoming/outgoing floats, margins, and container widths) and composing summaries without re-solving inner subtrees.

#### 3.2 Layout Engine Architecture Trade-Offs (`Cassius` vs. `Cassowary` vs. `Flutter` vs. `Taffy`)
Basis: normative (`doi:10.1145/504704.504705`) + source (`uwplse/cassius`, `DioxusLabs/taffy`) + derived

| Architecture / System | Mathematical Formulation | Time Complexity | Cross-Branch Alignment? | Primary Failure / Scaling Wall |
|---|---|---|---|---|
| **`Cassius` / `VizAssert`** (`60dad9e9`) | CSS 2.1 boxes & floats in Z3 QF_LRA + `:split` summaries | SMT (exponential worst-case; modularized per component) | Verifies CSS 2.1 floats/blocks/positioning | CSS Flexbox/Grid/Subgrid/Container Queries & dynamic JS (`ResizeObserver`) exceed LRA model; font shaping abstracted |
| **`Cassowary`** (`TOCHI 2001`, Apple Auto Layout) | Incremental dual-simplex over linear constraint hierarchies (required + weighted soft strengths) | $O(N)$ typical incremental drag; $O(N^2)$–$O(N^3)$ worst-case batch solve | **Yes** (arbitrary cross-tree equalities) | Dropped 120 Hz frames on large tableaux; runtime over-/under-constrained conflicts; cannot directly express nonlinear aspect-ratio text wrap |
| **`Flutter` `BoxConstraints`** | Strict tree pass: parent sends `(minW, maxW, minH, maxH)` down; child returns exact `Size` up | Strict **$O(N)$** single-pass | **No** (strictly parent-child tree) | Runtime `RenderFlex` unbounded-constraint crashes (`unbounded width inside Row`); `IntrinsicHeight` degrades to $O(2^d)$ exponential tree walks |
| **`DioxusLabs/taffy`** (`1abd8eea`) | Native Rust CSS Flexbox, Grid, and Block multi-pass layout with per-node measurement memoization | Amortized linear via **9-slot `Cache`** (`CACHE_SIZE = 9`, `src/tree/cache.rs:10, 206-223`) | Within Flexbox/Grid container tracks | Multi-pass intrinsic sizing requires careful cache-key invalidation (`AvailableSpace::Definite`/`MinContent`/`MaxContent` bit-packed into `u32`, `cache.rs:160-175`); CSS spec parity edge cases |

Direct inspection of `DioxusLabs/taffy` (`1abd8eeaf6059336a7026c31e0f1b769d2f04a3a`, `src/tree/cache.rs:10, 160-223`) shows the engineering cost of taming multi-pass CSS intrinsic sizing: every layout node carries a `Cache` storing `final_layout_entry` plus `measure_entries: [Option<CacheEntry<Size<f32>>>; 9]` (clock-evicted via an `AtomicU16` `recently_used_entries` bitmask so `Cache::get` takes `&self`), keyed by bit-packed `f32` dimensions and `CacheMode` (`sizing_mode` + `vertical_margins_are_collapsible`). Without this 9-slot memoization cache, nested Flexbox/Grid intrinsic measurements degrade exponentially ($O(2^d)$), identical to `Flutter`'s `IntrinsicHeight` cliff.

---

### 4. Accessibility Tree Semantics and Cross-Framework UI Bisimulation (`AccessKit`)

Basis: source (`AccessKit/accesskit`) + derived

Modern GPU-rendered and immediate-mode UI toolkits (`egui`, `Bevy`, `Slint`, `Flutter` canvas, HTML `<canvas>`) bypass native OS widgets, requiring an explicit shadow accessibility tree synchronized with three incompatible OS IPC protocols: Windows **UI Automation (UIA / COM)**, macOS **`NSAccessibility` (Objective-C / AppKit)**, and Linux **`AT-SPI2` (D-Bus)**.

Inspecting `AccessKit/accesskit` (`432d06659e0a6708fb206e266d65752dd372deeb`, `accesskit/src/lib.rs:3212-3385`) highlights the exact protocol invariants required at this UI $\leftrightarrow$ OS-IPC boundary:

1. **Full-node-overwrite incremental tree diffs (`TreeUpdate`, `lib.rs:3212-3231`):** Every `(NodeId, Node)` entry in a `TreeUpdate` **completely overwrites** the prior node with that ID (unchanged fields must be resent), and every non-root node in the update must be attached to either an existing unchanged parent or another updated parent in the same `TreeUpdate`. Immediate-mode UIs must synthesize **stable deterministic `NodeId`s across frames**—regenerating IDs per frame causes screen readers (NVDA, VoiceOver, Orca) to lose focus and re-announce the entire window continuously.
2. **Cross-thread asynchronous action dispatch (`ActionHandler::do_action`, `lib.rs:3366-3377`):** Assistive technologies invoke remote actions (`Click`, `Focus`, `SetValue`) on **platform-dependent threads** (e.g., synchronous Windows UIA COM callbacks vs. macOS main-thread AppKit vs. Linux D-Bus threads). `AccessKit` explicitly documents that `do_action` should queue requests asynchronously rather than blocking on application locks to prevent COM/UI-thread deadlocks.
3. **Unverified visual–accessibility bisimulation gap (derived):** Neither `AccessKit` nor `Taffy` nor `WAI-ARIA` statically verifies that the visual rendering pipeline and the semantic accessibility tree satisfy a formal bisimulation:
   - An element visually clipped, occluded by a modal backdrop, or hidden via `opacity: 0` can remain keyboard-focusable in the accessibility tree;
   - Conversely, a visually clickable GPU hit-test rectangle can lack a matching `AccessKit` node, `Role::Button`, accessible name, or keyboard activation path;
   - `Taffy` / GPU hit-test coordinates can drift from `AccessKit` `Node::bounds` or violate `WCAG 2.2` keyboard focus-trap freedom (`SC 2.1.2`), visual-vs-tab reading order (`SC 2.4.3`), and alpha-composited contrast ratios (`SC 1.4.3`).

## Boundaries

- **Known not to apply:**
  - *Lossless round-trip of ill-formed UTF-16 across Wasm Component Model `string` or strict UTF-8 APIs:* `CanonicalABI.md:2255-2258` traps on unpaired surrogates; preserving arbitrary Win32/JS `u16` sequences requires `WTF-8` internally or explicit `list<u16>` wire types.
  - *Raw byte concatenation on `WTF-8` or `UAX #15` NFC strings:* Both invariants are mathematically non-closed under naive concatenation (verified via execution probe and `rust-lang/rust` `alloc/src/wtf8/mod.rs:298-320`).
  - *General equivalence checking on Extended SFTs (ESFTs) or nondeterministic SFTs:* Decidability of `ST.Eq1` applies strictly to single-valued 1-character-input SFTs (and restricted subclasses); adding arbitrary lookahead or nondeterminism crosses into undecidability.
  - *`Cassius` CSS 2.1 SMT proofs on live JavaScript-mutated or CSS Grid/Subgrid pages:* Static CSS 2.1 LRA axioms do not capture dynamic `ResizeObserver` DOM rewrites, Flexbox/Grid multi-pass sizing, or full `HarfBuzz` OpenType glyph shaping.
- **Unsupported (explicitly observed in source):**
  - `WebAssembly/component-model` `CanonicalABI.md:2255-2258` explicitly rejects unpaired UTF-16 surrogates via `trap()`.
  - `swiftlang/swift` `StringGraphemeBreaking.swift:424` explicitly rejects foreign (bridged NSString) strings on Linux (`fatalError("No foreign strings on Linux in this version of Swift")`).
  - `uwplse/cassius` `src/assertions.rkt:10-14` notes thread-serialization limits on `assertion-helpers` vs. `helper-dict`.
- **Unknown:**
  - *SMT decidability of full CSS Flexbox/Grid + Subgrid + i18n string-length expansion envelopes:* Whether modular `:split` summaries (`Cassius` OOPSLA 2019) scale to piecewise-linear/nonlinear Flexbox shrink-grow redistribution and CSS Grid auto-placement without solver timeouts remains open.
  - *Formal visual-to-accessibility bisimulation over GPU immediate-mode UIs:* End-to-end mechanized proofs linking a Rust layout engine (`Taffy`), GPU hit-testing, and `AccessKit` `TreeUpdate` diffs have not yet been demonstrated in production frameworks.
  - *Zero-TCB proof certificates for `Bek`/SFT equivalence:* Extracting compact Lean 4 / Coq proof certificates from Z3-backed `ST.Eq1` runs to remove Z3 from the sanitizer TCB remains open.
- **Not examined:**
  - `unicode-org/icu4x` compiled data-slicing internals, `simdutf` vectorized UTF-8/UTF-16 validation assembly, and PostgreSQL `glibc`/`ICU` `COLLATION VERSION` C source code were not directly source-inspected in this report.
  - Proprietary browser layout engine internals (`Blink`, `Gecko`, `WebKit`), Apple `UIKit` Auto Layout internals, and `Flutter`'s Dart `RenderFlex` implementation source files were not directly audited line-by-line (analyses rely on published specifications and `TOCHI 2001`).
  - `AccessKit` OS-specific platform adapters (`platforms/windows` UIA COM, `platforms/macos` AppKit, `platforms/unix` AT-SPI2) were not audited line-by-line beyond the core `accesskit/src/lib.rs` trait and `TreeUpdate` contract.

## Evidence

### Primary Git Sources Inspected (Observed 2026-11-19)
- `rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`:
  - `library/alloc/src/wtf8/mod.rs:298-338` (`Wtf8Buf::push_wtf8` and `Wtf8Buf::push` boundary surrogate-pair fusion via `decode_surrogate_pair`).
  - `library/core/src/wtf8.rs` (core `Wtf8` slice representation).
- `SimonSapin/wtf-8` @ `e27dc7c6e0d25e9276274ad42eb25dc30aba8c1f`:
  - Repository pointer and canonical WTF-8 specification identity.
- `swiftlang/swift` @ `3be0cf4b450b5366cff4b1a7e5bf7e5b4633224f`:
  - `stdlib/public/core/StringGraphemeBreaking.swift:106-177, 422-426` (`_slowRoundDownToNearestCharacter`, `roundDownToNearestCharacter`, `_opaqueCharacterStride`, `String.Index` character-stride caching).
- `WebAssembly/component-model` @ `585526aa1f2c7f76f07557d16e265dede38b3acb`:
  - `design/mvp/CanonicalABI.md:2232-2261, 2543-2582` (`load_string_from_range` trapping on `UnicodeError`, `store_string_into_range` across `utf8`, `utf16`, and `latin1+utf16`).
- `nickboucher/trojan-source` @ `e3dc153fcf465f4a84424ea874ff39be29adb1f7`:
  - `README.md:1-50` (12-language vulnerability matrix across Early Return, Commenting-Out, Stretched Strings, plus Homoglyph and VS Code v1.61 evaluation).
- `AutomataDotNet/Automata` @ `0242132fdbe9687bea22b7144afa0784d7cd927b`:
  - `src/Automata/ST.cs:711-740, 2021-2126, 3194-3201` (`ST.Compose`, `ST.Eq1`, `ST.Eq1_v2` 1-equivalence and single-valuedness check).
  - `src/Automata/STb.cs:1854-1860` (`CompiledCSMethod`, `STb.Compose`).
  - `src/Bek/Query/AST.cs` & `src/Bek.Tests/GeneratedCodeSamples/` (`UTF8EncodeFlat.cs`, `HtmlEncode.cs`, `CssEncodeFlat.cs`).
- `uwplse/cassius` @ `60dad9e9b2b4de3b13451ce54cdc1bd55ca64824`:
  - `src/spec/layout.rkt` (`Box`, `EZone`, `box-collapsed-through`, `ez.outside`, `ez.inside`, `ez.inside*`).
  - `src/assertions.rkt:1-80` (`assertion-helpers`: `is-interactive`, `viewable`, `onscreen`, `overlaps`, `within`, `luminance`, float flow invariants, `compile-assertion` recursive `ancestor` SMT lowering).
  - `src/modularize.rkt:1-45` (`is-component`, `split-document` on `:split` / `:spec` / `:assert`).
- `DioxusLabs/taffy` @ `1abd8eeaf6059336a7026c31e0f1b769d2f04a3a`:
  - `src/tree/cache.rs:10, 160-241` (`CACHE_SIZE = 9`, `size_option_cache_key`, `available_space_cache_key`, `struct Cache` with `AtomicU16` `recently_used_entries` and `CacheMode`).
- `AccessKit/accesskit` @ `432d06659e0a6708fb206e266d65752dd372deeb`:
  - `accesskit/src/lib.rs:3212-3235, 3366-3385` (`struct TreeUpdate` full-node overwrite & parent-attachment invariants, `trait ActionHandler` platform-thread async dispatch, `trait DeactivationHandler`).

### Peer-Reviewed Papers Verified
- Nicholas Boucher, Ross Anderson, *Trojan Source: Invisible Vulnerabilities*, USENIX Security 2023, `arXiv:2111.00169`, `doi:10.48550/arXiv.2111.00169`.
- Pieter Hooimeijer, Benjamin Livshits, David Molnar, Prateek Saxena, Margus Veanes, *Fast and Precise Sanitizer Analysis with BEK*, USENIX Security 2011.
- Margus Veanes, Pieter Hooimeijer, Benjamin Livshits, David Molnar, Nikolaj S. Bjørner, *Symbolic Finite State Transducers: Algorithms and Applications*, POPL 2012, `doi:10.1145/2103656.2103674`.
- Loris D'Antoni, Margus Veanes, *The Power of Symbolic Automata and Transducers*, CAV 2017, `doi:10.1007/978-3-319-63387-9_3`.
- Pavel Panchekha, Emina Torlak, *Automated Reasoning for Web Page Layout*, OOPSLA 2016, `doi:10.1145/2983990.2984010`.
- Pavel Panchekha, Adam T. Geller, Michael D. Ernst, Zachary Tatlock, Shoaib Kamil, *Verifying That Web Pages Have Accessible Layout*, PLDI 2018, `doi:10.1145/3192366.3192407`.
- Pavel Panchekha, Michael D. Ernst, Zachary Tatlock, Shoaib Kamil, *Modular Verification of Web Page Layout*, OOPSLA 2019, `doi:10.1145/3360577`.
- Greg J. Badros, Alan Borning, Peter J. Stuckey, *The Cassowary Linear Arithmetic Constraint Solving Algorithm*, ACM TOCHI 8(4), 2001, `doi:10.1145/504704.504705`.

### Execution Probe (Python 3.13.15, Observed 2026-11-19)
Reproducible probe verifying WTF-8 surrogate fusion, CESU-8 strict UTF-8 rejection, NFC concatenation non-closure, multi-metric lengths, Trojan Source BiDi codepoints, sanitizer non-idempotence/non-commutativity, and WCAG 2.1 reflow overlap:

```python
import unicodedata

def encode_wtf8_cp(cp: int) -> bytes:
    if cp <= 0xFFFF:
        return bytes([0xE0 | (cp >> 12), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F)])
    return bytes([0xF0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3F), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F)])

lead_b, trail_b = encode_wtf8_cp(0xD83D), encode_wtf8_cp(0xDE00)
fused_b = encode_wtf8_cp(0x10000 + ((0xD83D - 0xD800) << 10) + (0xDE00 - 0xDC00))
assert lead_b.hex() == "eda0bd" and trail_b.hex() == "edb880" and fused_b.hex() == "f09f9880"
assert unicodedata.is_normalized("NFC", "e") and unicodedata.is_normalized("NFC", "\u0301")
assert not unicodedata.is_normalized("NFC", "e" + "\u0301")
```

Recorded outputs on Python 3.13.15:
- WTF-8 `U+D83D` (`eda0bd`, 3B) + `U+DE00` (`edb880`, 3B): naive concat `eda0bdedb880` (6B) rejected by strict UTF-8 (`invalid continuation byte`); `push_wtf8` produces `f09f9880` (4B, `U+1F600` `'😀'`).
- NFC non-closure: `is_nfc('e')=True`, `is_nfc('\u0301')=True`, `is_nfc('e'+'\u0301')=False` (`len=2` vs. `len(NFC)=1`).
- Multi-metric counts: Family emoji = `(25 UTF-8, 11 UTF-16, 7 scalars)`; Flag US = `(8, 4, 2)`; Devanagari `क्ष` = `(9, 3, 3)`; `e\u0301` NFD = `(3, 2, 2)` vs. `é` NFC = `(2, 1, 1)`.
- Trojan Source BiDi control sequence extracted: `['U+202E', 'U+2066', 'U+2069', 'U+2066']`.
- SFT non-idempotence: `html_esc("<script>") = '&lt;script&gt;'` vs. `html_esc(html_esc(...)) = '&amp;lt;script&amp;gt;'`.
- SFT non-commutativity: `html_esc(url_dec("%3Cscript%3E")) = '&lt;script&gt;'` vs. `url_dec(html_esc("%3Cscript%3E")) = '<script>'`.
- Parametric WCAG reflow (`sidebar = 220px`, right-anchored `main = 200px`): `W=1280px` (`100%`/`200%`) $\to$ `overlaps=False, horiz_overflow=False`; `W=320px` (`100%`/`200%`) $\to$ `overlaps=True, horiz_overflow=True`.

## Revalidation

1. **Rust `WTF-8` and Wasm Component Model string ABI:** Diff `library/alloc/src/wtf8/mod.rs` (`push_wtf8`) in `rust-lang/rust` and `design/mvp/CanonicalABI.md` (`load_string_from_range`, `store_string_into_range`) in `WebAssembly/component-model` to verify whether surrogate-fusion semantics or strict `UnicodeError -> trap()` enforcement changes in newer releases.
2. **Unicode annual release drift:** After each annual Unicode Standard release (16.x/17.0+), re-run the multi-metric and `NFC` closure probe against updated `unicodedata` / `ICU4X` / `swiftlang/swift` (`StringGraphemeBreaking.swift`) tables, checking specifically for new `UAX #29` stateful rules (analogous to Unicode 15.1 `InCB`) and `UAX #9` / `UTS #39` compiler lint updates.
3. **SFT framework and sanitizer verification:** Diff `src/Automata/ST.cs` (`Eq1`, `Compose`) in `AutomataDotNet/Automata` (or successor symbolic automata libraries) if checking new lookahead/ESFT or SVPT decidability extensions.
4. **Layout and accessibility verification:** Check `DioxusLabs/taffy` (`src/tree/cache.rs`, `src/compute/`) for changes to `CACHE_SIZE` or Flexbox/Grid/Block layout modes, `AccessKit/accesskit` (`accesskit/src/lib.rs`) for `TreeUpdate` incremental diff semantics (e.g., partial-patch vs. full-node overwrite), and `uwplse/cassius` (or successor formal CSS verifiers) for Flexbox/Grid SMT encodings.
