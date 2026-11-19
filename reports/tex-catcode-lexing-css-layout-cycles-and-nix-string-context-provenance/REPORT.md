# Runtime Lexer Mutation, Cyclic Layout/Stream Constraints, Hidden String Provenance, and Staging-Graph Semantics in Document, Build, and Configuration Languages

## Summary

Document-typesetting, layout, build-graph, and infrastructure-configuration languages routinely violate standard compiler phase-separation assumptions (stateless lexing, acyclic bottom-up evaluation, extensional value equality, and AST-typed interpolation). Across four representative industrial language families inspected directly from primary implementations and specifications:

1. **TeX / XeTeX (`tex.web`, Tectonic):** Lexing is coupled bidirectionally to execution through a mutable 16-value `\catcode` table read only when `get_next` consumes raw characters from external files (`state <> token_list`), whereas tokens already absorbed into macro bodies or arguments carry permanently frozen `(catcode, charcode)` pairs (`256 * cmd + chr` in 8-bit TeX; `(cmd << 21) + chr` in 21-bit Unicode XeTeX/Tectonic). Macro expansion (the Turing-complete *mouth/gullet*) and stateful execution (*stomach*) interleave as a coroutine in which stomach scanners (`scan_keyword`) pull expanded tokens (`get_x_token`) and push unmatched tokens back onto the input stack, while `\globaldefs` dynamically overrides lexical/explicit `\global` scoping across `save_stack` groups.
2. **CSS Layout & `@container` vs. XSLT 3.0 Streaming (`w3c/csswg-drafts`, Blink `LayoutNG`, `Cassius`, W3C XSLT 3.0):** CSS Flexbox and Grid break single-pass linear-arithmetic layout models (such as `Cassius`'s Z3 LRA encoding of CSS 2.1) by coupling container available sizes, child `min-content`/`max-content` intrinsic contributions, cyclic percentages, and baseline alignment. Adding `@container` size queries introduces non-monotone style-affects-size-affects-style fixed-point oscillations that specifications break structurally by requiring explicit containment (`container-type: size | inline-size`), isolating a container's own sizing from its descendants. By contrast, W3C XSLT 3.0 guarantees single-pass constant-memory evaluation statically through a two-dimensional effect type system of **posture** (`grounded`, `climbing`, `striding`, `crawling`, `roaming`) and **sweep** (`motionless`, `consuming`, `free-ranging`).
3. **Nix / Tvix String-Context Provenance vs. GNU Guix G-Expressions (`NixOS/nix`, `tvlfyi/tvix`, `guix`):** Nix and Tvix represent runtime strings as pairs `(Bytes, Set<ContextElem>)` carrying invisible store-path and derivation-output provenance (`Opaque`/`Plain`, `Built`/`Single`, `DrvDeep`/`Derivation`). Crucially, string equality (`==` in `EvalState::eqValues` and `PartialEq for NixString`) compares raw byte slices while ignoring context, violating Leibniz's Law ($s_1 = s_2 \not\implies f(s_1) = f(s_2)$) under context-observing primitives (`builtins.hasContext`, `builtins.getContext`, `builtins.derivationStrict`, and zero-length context-preserving `builtins.substring 0 0 s`). Simultaneously, Nix's `ExprVar::bindVars` resolves all enclosing lexical bindings (`let`, lambda parameters) before falling back to any dynamically scoped `with` chain. GNU Guix avoids hidden string provenance altogether by keeping Scheme strings context-free and staging cross-derivation references inside typed `<gexp>` / `<gexp-input>` AST records.
4. **Helm Text-Templated YAML vs. Terraform HCL/cty Unknown-Value Graphs & CUE (`helm/helm`, `hashicorp/hcl`, `zclconf/go-cty`, `hashicorp/terraform`, `cue-lang/cue`):** Helm evaluates Go `text/template` directly into raw text buffers and splits multi-document streams via a line-anchored regex (`(?m)^---[ \t]*` in `SplitManifests`) before YAML parsing, permitting unquoted multiline values to inject arbitrary sibling Kubernetes manifests and exposing downstream consumers to YAML 1.1 scalar coercions (`NO -> false`, `on -> true`, `010 -> 8`). Terraform's HCL2/`go-cty` instead operates over a typed 3-valued lattice (`Known`, `Null`, `Unknown` with optional refinements and orthogonal `ValueMarks` for `Sensitive`/`Ephemeral`), propagating unknowns through expressions while enforcing a strict plan-time graph boundary in `for_each`: map keys (and all set elements) must be known and non-ephemeral during plan expansion, whereas map values may remain unknown until apply.

## Applicability

This report synthesizes and contrasts four non-traditional static/dynamic language semantics domains whose edge cases directly impact compiler design, static analysis, verification tooling, and security boundaries:

| Domain | Primary Subjects Examined | Relationship Among Subjects | Scope of Claims |
| :--- | :--- | :--- | :--- |
| **Runtime-mutable lexing & macro coroutines** | `TeX-Live/texlive-source@b4e37b58` (`texk/web2c/tex.web`); `tectonic-typesetting/tectonic@d2224d9b` (`crates/engine_xetex/xetex/xetex-constants.h`, `xetex-xetex0.c`) | Classical 8-bit TeX specification/implementation (`tex.web`) compared with its 21-bit Unicode XeTeX/Tectonic derivative | Applies to Knuth TeX 3.x engines (pdfTeX, XeTeX, Tectonic, LuaTeX macro core). LuaTeX Lua callbacks (`process_input_buffer`, token library) add further hooks not examined here. |
| **Cyclic layout vs. static streaming analysis** | `w3c/csswg-drafts@5e83e63e` (`css-flexbox-1`, `css-grid-1`, `css-contain-3`, `css-conditional-5`); `chromium/chromium@a96bb315` (Blink `LayoutNG` & `ContainerQueryEvaluator`); `uwplse/cassius@60dad9e9` (OOPSLA 2016 / PLDI 2018); W3C XSLT 3.0 Recommendation (2017-06-08) | Normative W3C CSS drafts compared against Blink implementation and Cassius SMT formalization; contrasted structurally against XSLT 3.0 static streamability | CSS findings apply to modern CSS Flexbox 1, Grid 1, and Conditional 5 (`@container`) drafts and Chromium Blink LayoutNG at pinned revisions; Cassius claims apply strictly to its CSS 2.1 block/inline/float fragment. XSLT 3.0 claims reflect the 2017 W3C Recommendation. |
| **Hidden value provenance vs. staged ASTs** | `NixOS/nix@69653925` (`src/libexpr`); `tvlfyi/tvix@74566823` (`eval/src/value/string`); `codeberg.org/guix/guix@d19bb5cf` (`guix/gexp.scm`) | C++ reference Nix evaluator compared with independent Rust reimplementation Tvix (verifying semantic parity), contrasted with GNU Guix's staged `<gexp>` architecture | Applies to Nix evaluator `libexpr` and Tvix `tvix-eval` at pinned revisions (excluding experimental dynamic-derivations extensions beyond standard `NixStringContextElem`), and GNU Guix's `(guix gexp)` module. |
| **Text-templated config vs. partial-eval IaC graphs** | `helm/helm@01b541c8` (`pkg/engine`, `pkg/release/v1/util/manifest.go`); `hashicorp/hcl@94e232b5`; `zclconf/go-cty@5203df26`; `hashicorp/terraform@a1246154` (`internal/terraform/eval_for_each.go`); `cue-lang/cue@b38d73e3` (`doc/ref/spec.md`); PyYAML `6.0.3` execution probe | Helm v4 Go-template/YAML rendering contrasted against HCL2/`go-cty`/Terraform's typed 3-valued plan-time graph semantics and CUE's lattice unification | Helm findings apply to Helm v4 (`helm.sh/helm/v4`, `SplitManifests` regex inherited from Helm v3) and YAML 1.1 parsers (demonstrated with PyYAML 6.0.3). HCL/Terraform findings apply to HCL2, `go-cty`, and Terraform's `forEachEvaluator` including ephemeral/sensitive value marks. |

All cross-domain architectural comparisons in **Findings** are derived from the primary artifacts above and verified with standalone execution probes recorded in **Evidence**.

## Findings

### 1. TeX / XeTeX: Runtime `\catcode` Lexer Mutation and Mouth/Stomach Coroutines

#### 1.1 Mutable 16-Category Lexical State vs. Permanently Frozen Token Pairs

`Basis: normative + source + execution`

In classical TeX (`TeX-Live/texlive-source@b4e37b58`, `texk/web2c/tex.web:4063-4083`), every input character code is dynamically classified into one of 16 category codes (`0..15`):

| Catcode | `tex.web` Symbol | Default TeX Char(s) | Lexical / Semantic Role |
| :---: | :--- | :--- | :--- |
| `0` | `escape` | `\` | Begins a control sequence (`\foo` or `\%`) |
| `1` | `left_brace` | `{` | Group open / macro argument delimiter |
| `2` | `right_brace` | `}` | Group close / macro argument delimiter |
| `3` | `math_shift` | `$` | Enter/exit inline or display math mode |
| `4` | `tab_mark` | `&` | Alignment cell separator (`\halign`) |
| `5` | `car_ret` | CR (`^^M`) | End-of-line (inserts space or `\par` depending on line state) |
| `6` | `mac_param` | `#` | Macro parameter prefix in definitions |
| `7` | `sup_mark` | `^` | Math superscript and `^^` hex/shifted character escapes |
| `8` | `sub_mark` | `_` | Math subscript |
| `9` | `ignore` | NUL | Silently discarded during external scanning |
| `10` | `spacer` | space, tab | Collapsed whitespace token (`space_token = (10 << 8) + 32`) |
| `11` | `letter` | `A..Z`, `a..z` | Multi-character control-word constituents |
| `12` | `other_char` | digits, punct. | Non-letter character tokens (cannot form multi-char control words) |
| `13` | `active_char` | `~` | Single-character token that invokes a macro directly like a control sequence |
| `14` | `comment` | `%` | Discards remainder of current physical input line |
| `15` | `invalid_char` | DEL | Triggers lexical error in external input |

TeX does **not** run a separate lexing pass before parsing or execution. Instead, `get_next` (`tex.web:7237-7275`) branches directly on whether the top of the input stack (`state`) is an external text file or an internal token list:

1. **External character stream (`state <> token_list`, `tex.web:7250-7271`):** Reads the next raw byte `cur_chr := buffer[loc]` and immediately consults the live equivalence table `cur_cmd := cat_code(cur_chr)`. Because `\catcode` assignments modify `eqtb` during execution (stomach), changing `\catcode` immediately alters how subsequent unread characters in the external buffer are tokenized—including which characters terminate a control sequence name (`start_cs` at `tex.web:7418` loops while `cat_code(cur_chr) = letter`, which is why LaTeX uses `\makeatletter` / `\catcode`\@=11` to access internal `@`-named macros).
2. **Internal token list (`state = token_list`, `tex.web:7477-7498`):** Reads a pre-encoded integer token `t := info(loc)`. If `t >= cs_token_flag` (`@'7777` = `4095` in 8-bit `tex.web:6169`; `0x1FFFFFF` in 21-bit Unicode Tectonic `xetex-constants.h:348`), it decodes a control-sequence pointer `cur_cs := t - cs_token_flag`. Otherwise, it unpacks a **frozen** `(catcode, charcode)` pair directly via bit-field / radix splitting:
   - In 8-bit `tex.web:7490`: `cur_cmd := t div @'400; cur_chr := t mod @'400;` ($2^8 = 256$).
   - In Unicode XeTeX / Tectonic (`xetex-constants.h:347-360`): `MAX_CHAR_VAL = 0x200000` ($2^{21}$), encoding character tokens as `(catcode << 21) + unicode_scalar` (e.g., `LETTER_TOKEN = 0x1600000`, `OTHER_TOKEN = 0x1800000`, `SPACE_TOKEN = 0x1400020`).

Because `state = token_list` **never consults `cat_code(cur_chr)`**, any character scanned into a macro definition body (`\def`) or absorbed as a macro argument before a `\catcode` assignment executes has its `(cmd, chr)` pair permanently frozen.

**Canonical Failure Case (`\verb` inside macro arguments):**
Consider `\def\showcode#1{\catcode`\\=12 #1}` invoked as `\showcode{\bar}`. When TeX parses the argument to `\showcode`, the stomach has not yet executed `\catcode`\\=12`. The mouth tokenizes `\bar` under default catcodes into the single control-sequence token `('CS', "bar")` and stores it in `#1`. When `\showcode` expands, `\catcode`\\=12` mutates `eqtb`, and then `#1` is pushed onto the input stack as a `token_list`. `get_next` reads `('CS', "bar")` via the `t >= cs_token_flag` branch, never re-lexing `\` as `other_char` (catcode 12), and attempts to execute `\bar` as a macro (verified in Probe 1A). This is the exact structural reason LaTeX's `\verb|...|` fails inside the argument of `\footnote{...}` or `\textbf{...}` unless re-tokenized explicitly via e-TeX's `\scantokens`.

#### 1.2 Mouth/Gullet Expansion vs. Stomach Coroutine and Dynamic Scoping

`Basis: normative + source`

TeX partitions evaluation into two tightly interleaved coroutines rather than sequential compiler stages:

- **Mouth & Gullet (Expansion-Only Subsystem, `expand` at `tex.web:7663-7679`):** Expands macros (`cur_cmd >= call`), conditionals (`\if`, `\ifx`, `\ifnum`), `\expandafter`, `\csname...\endcsname`, `\the`, and `\romannumeral` (`roman_numeral_code = 1`, `tex.web:9221`). Crucially, the expansion subsystem alone is **Turing-complete** without ever executing a stomach assignment: `\expandafter` reorders expansion in the token stream, delimited macro parameters perform pattern matching on token lists, and `\romannumeral` triggers full iterative tail-expansion until a non-digit terminates the scanned integer (exploited by LaTeX3/`expl3` `\romannumeral-`0` full-expansion tricks).
- **Stomach (Execution & Backtracking Scanners, `scan_keyword` at `tex.web:8240-8256`):** Unexpandable primitives (`\def`, `\catcode`, `\hskip`, `\advance`, boxes) execute in the stomach, yet reach back into the gullet via `get_x_token` (`tex.web:7825`, which loops calling `get_next` and `expand` until an unexpandable token arrives). For example, `scan_keyword` (`tex.web:8240-8256`) calls `get_x_token` repeatedly to match case-insensitive keywords such as `plus`, `minus`, or `pt`; if a partial match fails, it restores every consumed token back onto the input stream via `back_input` and `back_list(link(backup_head))`. Because `get_x_token` already expanded macros while probing for a keyword, macro expansion side effects in the gullet (such as consuming lookahead tokens or failing on unexpandable tokens) are **not** rolled back when `scan_keyword` backtracks!
- **Dynamic Scoping (`save_stack`) and `\globaldefs` Override (`tex.web:5992-6008, 22776-22782`):** Every `\def`, `\let`, `\catcode`, and register update records prior `eqtb` state onto `save_stack` via `eq_define` / `eq_word_define` when `eq_level(p) <> cur_level`, restoring all local bindings upon `}` or `\endgroup`—making all TeX macros and catcodes dynamically scoped by execution nesting rather than lexical definition site. Worse for modular reasoning, `prefixed_command` checks `\globaldefs` (`tex.web:22776-22782`): if `global_defs > 0`, **every** local assignment is silently promoted to `\global` (`a := a + 4`), leaking group-local catcode and macro mutations out of encapsulated macros; if `global_defs < 0`, explicit `\global` prefixes are silently stripped (`a := a - 4`), breaking macros that rely on global state propagation.

---

### 2. CSS Intrinsic Sizing Cycles, `@container` Circularity, and XSLT 3.0 Streamability

#### 2.1 Why Flexbox and Grid Break Single-Pass Linear-Arithmetic Models (`Cassius` vs. `LayoutNG`)

`Basis: normative + source + documentation`

Panchekha and Torlak's `Cassius` (`uwplse/cassius@60dad9e9`, OOPSLA 2016 DOI `10.1145/2983990.2984010`; extended in VizAssert, PLDI 2018 DOI `10.1145/3192366.3192407`) demonstrated that a core fragment of CSS 2.1 (block flow, inline line boxes, floats, positioning, and margins) reduces to decidable quantifier-free Linear Real Arithmetic (LRA) in Z3 (`src/spec/layout.rkt:105-136`, defining box geometry predicates, `ppflow`, `pbflow`, and `contains-content`). That reduction succeeds because CSS 2.1 normal block flow is predominantly top-down for widths (parent containing block width determines child line wrapping) and bottom-up for heights (child line heights sum into parent block height).

CSS Flexbox Level 1 (`w3c/csswg-drafts@5e83e63e`, `css-flexbox-1/Overview.bs`) and CSS Grid Level 1 (`css-grid-1/Overview.bs`) fundamentally destroy that single-pass DAG structure via multi-axis intrinsic sizing feedback:

1. **Flexbox Multi-Pass Coupling (`css-flexbox-1/Overview.bs:3588-4290`, Blink `flex_layout_algorithm.cc:827-1750`):**
   - Section 9.2 (`#line-sizing`, line 3667) resolves flexible lengths (`flex-grow` / `flex-shrink`) from items' hypothetical main sizes, which may themselves depend on intrinsic `min-content`/`max-content` widths or aspect-ratio transfers from the cross axis (`ConstructAndAppendFlexItems`, `flex_layout_algorithm.cc:827-917`).
   - Section 9.4 (`#cross-sizing`, line 3892) computes line cross sizes from laid-out items, stretches items, and can re-trigger layout for wrapped text or orthogonal writing modes (`GiveItemsFinalPositionAndSize`, `flex_layout_algorithm.cc:1747`).
   - Section 9.9 (`#intrinsic-sizes`, line 4288; cyclic percentage note at line 1481) requires back-propagating flex-item base sizes and flex factors to determine the flex container's own `min-content` and `max-content` contributions when nested inside another shrink-to-fit container, creating worst-case $O(2^d)$ nested measurement passes unless engines cache intrinsic/layout results per constraint space.
2. **Grid Track Sizing and Cyclic Dependencies (`css-grid-1/Overview.bs:3619-3651, 3797-4615`, Blink `grid_layout_algorithm.cc:78-1175`):**
   - The Grid Track Sizing Algorithm (`#algo-track-sizing`, line 4015) runs five coupled phases: initialize track sizes (`#algo-init`), resolve intrinsic track sizes across spanning items (`#algo-content`), maximize tracks (`#algo-grow-tracks`), expand flexible `fr` tracks (`#algo-flex-tracks`), and stretch `auto` tracks (`#algo-stretch`).
   - Because row heights depend on column widths (via text wrapping and aspect ratios) while column widths can depend on row heights (via orthogonal writing modes, aspect ratios, or percentage heights), Blink's `GridLayoutAlgorithm::ComputeGridGeometry` (`grid_layout_algorithm.cc:78-97, 358`) must perform multi-pass track sizing (`ComputeUsedTrackSizes`, line 1172) and re-run geometry resolution when inline sizes change.
   - **Normative Cycle-Breaking Rules in CSS Grid 1:** Where genuine fixed-point circularities occur, the specification explicitly cuts the cycle rather than iterating to a fixed point:
     - **Cyclic percentage tracks (`css-grid-1/Overview.bs:3814`):** Percentage track sizes against an indefinite container size are treated as `auto` during intrinsic sizing.
     - **Baseline-alignment vs. intrinsic-track cycles (`css-grid-1/Overview.bs:3619-3651`):** If baseline alignment is requested on a grid item whose size in that axis depends on an intrinsically-sized track (including `fr` tracks under an indefinite container size), baseline alignment depends on item size which depends on track size which depends on baseline alignment; the spec mandates that the item **does not participate in baseline alignment** and deterministically reverts to its fallback alignment.

#### 2.2 `@container` Style-Size Circularity and Structural Containment DAG Cuts

`Basis: normative + source + execution`

CSS Container Queries (`w3c/csswg-drafts@5e83e63e`, moved from `css-contain-3/Overview.bs:57-60` into `css-conditional-5/Overview.bs:495-720`) allow descendant style rules to branch on an ancestor box's laid-out dimensions (`@container (inline-size < 500px) { ... }`). Without containment, combining conditional styles with shrink-to-fit intrinsic sizing produces a **non-monotone fixed-point operator with no fixed point** (a 2-cycle oscillation):

- Suppose container $C$ shrinks to fit descendant $D$, and `@container (inline-size < 500px)` sets $D$'s `font-size: 40px` (intrinsic width $600\text{px}$), while the default rule sets `font-size: 10px` (intrinsic width $150\text{px}$).
- Starting at $w = 400\text{px}$, the query matches $\implies$ `font-size = 40px` $\implies w' = 600\text{px} \implies$ query fails $\implies$ `font-size = 10px` $\implies w'' = 150\text{px} \implies$ infinite 2-cycle `600 -> 150 -> 600 -> 150 ...` (reproduced in Probe 1B).

To guarantee single-direction dependency resolution between style recalculation and layout, CSS Conditional 5 enforces **structural DAG cuts** (`css-conditional-5/Overview.bs:507-509, 548, 668-708`):

1. **Mandatory Size Containment:** An element is **not** eligible as a size query container unless the author explicitly opts into `container-type: size` (applies `style` + `size` containment on both axes and establishes an independent formatting context) or `container-type: inline-size` (applies `style` + `inline-size` containment on the inline axis only, allowing block height to still grow with content while forbidding block-size queries).
2. **Strict Ancestor Separation:** A querying element cannot query its own size box (`css-conditional-5/Overview.bs:507-509`), and an ancestor box cannot query sibling boxes (`line 548`). Because `inline-size` containment forces the container's inline size to be determined solely by extrinsic constraints (ignoring all descendant intrinsic contributions), Blink's `ContainerQueryEvaluator` (`third_party/blink/renderer/core/css/container_query_evaluator.cc:32-41, 242-260`) evaluates `ContainerTypeAxes(style)` strictly top-down: lay out container $C$ $\to$ freeze $C$'s contained axis size $\to$ evaluate `@container` queries and restyle $C$'s subtree $\to$ lay out descendants.
3. **Style Queries (`container-type: normal`):** Every element is a container for `@container style(--prop: val)` without size containment (`css-conditional-5/Overview.bs:497-498, 704-707`), because CSS custom-property inheritance flows strictly top-down along the DOM/flat tree and never depends on descendant layout geometry.

#### 2.3 Contrast: XSLT 3.0 Template Priority and Static Streamability (`Posture × Sweep`)

`Basis: normative + documentation`

Whereas CSS relies on runtime multi-pass layout with explicit containment cuts, W3C **XSLT 3.0** (W3C Recommendation, 8 June 2017, `https://www.w3.org/TR/xslt-30/`) solves two orthogonal declarative-tree challenges statically at stylesheet compile time:

1. **Non-Lexical Template Rule Conflict Resolution (Section 6.4):** When multiple `<xsl:template match="...">` rules match an XML node, XSLT resolves conflicts by import precedence first, then explicit `priority` attribute, then syntactic **default priority** derived from the pattern structure (`-0.5` for wildcard `*` or `node()`, `-0.25` for namespace wildcards `ns:*`, `0.0` for simple element/attribute QNames `foo`, `+0.5` for path patterns `a/b` or predicates `a[@x]`). If equal-priority rules still conflict within the same import precedence, default recovery selects the **last** matching template in document order (or raises dynamic error `XTDE0540` if configured for strict reporting).
2. **Static Streamability Type System (Section 19):** To guarantee $O(1)$ tree-buffering (single forward pass over gigabyte XML documents without materializing the DOM), XSLT 3.0 assigns every expression a static pair `(Posture, Sweep)`:

| Property | Lattice Values (Ordered Weakest / Safest $\to$ Unstreamable) | Operational Meaning Over Forward XML Event Stream |
| :--- | :--- | :--- |
| **Posture** (where selected nodes sit relative to cursor) | `grounded` $\prec$ `climbing` / `striding` $\prec$ `crawling` $\prec$ `roaming` | **Grounded**: atomic values or in-memory temporary trees (no streamed nodes). **Climbing**: ancestors, attributes, or namespaces (already buffered on open-element stack). **Striding**: non-overlapping forward children/descendants in document order. **Crawling**: potentially overlapping downward selections (e.g., `descendant::x` where one `x` may contain another `x`). **Roaming**: arbitrary backward/mixed navigation (unstreamable). |
| **Sweep** (stream advancement effect) | `motionless` $\prec$ `consuming` $\prec$ `free-ranging` | **Motionless**: reads only current start-tag/attribute/ancestor stack without advancing the parser. **Consuming**: advances the forward stream once (cannot be composed in parallel with a second consuming sibling operand such as `sum(a) + sum(b)` without explicit `xsl:fork` or `copy-of()`). **Free-ranging**: requires random access / backtracking (unstreamable). |

Any expression inside a declared streamable construct (`<xsl:mode streamable="yes">`, `<xsl:stream>`) whose inferred posture is `roaming` or whose sweep is `free-ranging`—or any binary/sequence operator attempting **two** `consuming` sub-expressions over the same streamed node—is statically rejected at compile time with error `XTSE3430`. Unlike CSS's containment opt-in (which shifts runtime layout semantics when enabled), XSLT's `(Posture, Sweep)` analysis is a conservative static effect discipline guaranteeing bounded-memory equivalence to full-tree evaluation.

---

### 3. Nix / Tvix Hidden String-Context Provenance vs. GNU Guix G-Expressions

#### 3.1 The Hidden `(Bytes, ContextSet)` Representation

`Basis: source + execution`

Nix is commonly described as a pure, lazy, dynamically typed functional language. At the value representation level, however, Nix strings are **not** mere byte sequences: every string carries an invisible, mutable-through-composition set of build-graph provenance tags (`NixStringContext`).

Direct inspection of `NixOS/nix@69653925` (`src/libexpr/include/nix/expr/value/context.hh:37-103`) and its independent Rust reimplementation `tvlfyi/tvix@74566823` (`eval/src/value/string/context.rs:6-28`, `eval/src/value/string/mod.rs:32-48`) confirms exact semantic convergence on a 3-variant tagged union stored alongside the string's bytes:

| Provenance Variant | `NixOS/nix` (`context.hh:44-69`) | Internal Wire Encoding (`context.hh:78-82`) | `tvlfyi/tvix` (`context.rs:7-20`) | Build-Graph Effect in `builtins.derivationStrict` |
| :--- | :--- | :--- | :--- | :--- |
| Plain store path (copied source / `toFile`) | `Opaque` (`SingleDerivedPath::Opaque`) | `<store-path>` | `Plain(String)` | Adds `<store-path>` to `inputSrcs` of the resulting `.drv` |
| Single derivation output | `Built` (`SingleDerivedPath::Built`) | `!<output>!<drv-path>` | `Single { name, derivation }` | Adds `(<drv-path>, <output>)` to `inputDrvs` |
| Full derivation & transitive build closure | `DrvDeep { StorePath drvPath }` | `=<drv-path>` | `Derivation(String)` | Adds full derivation closure reference (used for `.drvPath` interpolation) |

In `tvlfyi/tvix` (`eval/src/value/string/mod.rs:32-48`), the inline heap allocation header explicitly stores `context: Option<Box<NixContext>>` alongside `length: usize` and `data: [u8]`. String concatenation (`s1 + s2`) and antiquotation (`"${s1}/bin"`) take the set union of operand contexts (`ctx1 ∪ ctx2`).

#### 3.2 Breaking Leibniz's Law and Naive Referential Transparency

`Basis: source + execution`

Crucially, **value equality (`==`) in both Nix and Tvix deliberately ignores string context**:

- In `NixOS/nix@69653925`, `src/libexpr/eval.cc:3013-3014` (`EvalState::eqValues`):
  ```cpp
  case nString:
      return v1.string_view() == v2.string_view();
  ```
  (And identically in `assertEqValues` at `eval.cc:2825-2826`.)
- In `tvlfyi/tvix@74566823`, `eval/src/value/string/mod.rs:375-379`:
  ```rust
  impl PartialEq for NixString {
      fn eq(&self, other: &Self) -> bool {
          self.0 == other.0 || self.as_bstr() == other.as_bstr()
      }
  }
  ```

Yet multiple built-in functions **do** observe or mutate string context (`NixOS/nix`, `src/libexpr/primops/context.cc:10-32, 290-325` and `src/libexpr/primops.cc:4671-4695`):
- `builtins.unsafeDiscardStringContext s` (`context.cc:10-16`): returns a fresh string with identical bytes and an empty context `∅`.
- `builtins.hasContext s` (`context.cc:27-32`): returns `true` iff `!context.empty()`.
- `builtins.getContext s` / `builtins.appendContext s attrs` (`context.cc:290-325`): reify the hidden provenance set into a Nix attribute set (`{ "<path>" = { path = true; allOutputs = true; outputs = [...]; }; }`) and vice versa.
- `builtins.substring start len s` (`primops.cc:4690-4695`): **preserves the entire context of `s` even when `len == 0`**, as explicitly documented in upstream source comments: *"Special-case on empty substring to avoid O(n) strlen; This allows for the use of empty substrings to efficiently capture string context."* Thus `builtins.substring 0 0 "${drv}"` evaluates to a string equal (`==`) to `""`, yet still drags `drv` into any derivation's `inputDrvs`!
- Attribute set keys (`{ ${k} = v; }`): reject strings carrying non-empty context (throwing an evaluation error), even if `k == "foo"` holds!

Consequently, Nix's `==` is **not a congruence** over Nix expressions (violating Leibniz's Law, $s_1 = s_2 \implies \forall C[\cdot],\; C[s_1] = C[s_2]$): letting `s1 = "${pkg}"` and `s2 = builtins.unsafeDiscardStringContext s1`, we have `s1 == s2` evaluating to `true`, while `builtins.hasContext s1 != builtins.hasContext s2`, `{ ${s2} = 1; }` succeeds whereas `{ ${s1} = 1; }` aborts evaluation, and passing `s1` vs `s2` to `builtins.derivation` synthesizes different `.drv` dependency graphs (verified in Probe 1C). Any optimizer, memoizer, or formal semantics for Nix that canonicalizes strings solely by `Bytes` (or applies `==`-based substitution) is **unsound** with respect to build-graph generation.

#### 3.3 Lexical `let` Shadowing Inner Dynamic `with` Scopes

`Basis: source + execution`

A second non-obvious Nix semantic trap is the interaction between lexical scopes (`let`, function arguments) and dynamically computed attribute-set injection (`with e1; e2`). In `NixOS/nix@69653925`, `src/libexpr/nixexpr.cc:315-349` (`ExprVar::bindVars`):

```cpp
for (curEnv = env.get(), level = 0; curEnv; curEnv = curEnv->up.get(), level++) {
    if (curEnv->isWith) {
        if (withLevel == -1)
            withLevel = level;
    } else {
        auto i = curEnv->find(name);
        if (i != curEnv->vars.end()) {
            this->level = level;
            displ = i->second;
            return;
        }
    }
}
```

Because `ExprVar::bindVars` walks the **entire** static scope chain searching non-`isWith` lexical frames before ever committing to `withLevel`, an **outer** lexical binding strictly shadows an **inner** `with` binding:

```nix
let x = 1; in with { x = 2; y = 3; }; [ x y ]  # evaluates to [ 1 3 ], NOT [ 2 3 ]!
```

Only nested `with` expressions shadow one another innermost-first (linked via `ExprWith::prevWith` at `nixexpr.cc:543-549`). This breaks naive alpha-renaming intuition when refactoring `let` bindings around `with pkgs;` blocks: adding an outer `let foo = ...;` silently hijacks every unqualified `foo` inside an inner `with pkgs;` without warning.

#### 3.4 Architectural Alternative: GNU Guix Staged G-Expressions (`<gexp>`)

`Basis: source`

GNU Guix (`codeberg.org/guix/guix@d19bb5cf`, `guix/gexp.scm:165-190, 854-876, 1131-1155`) eliminates hidden string provenance completely by splitting staging into a distinct algebraic record type:

- `<gexp>` (`guix/gexp.scm:165-172`) stores `(references modules extensions proc location)`, where `references` is an explicit list of `<gexp-input>` records (`thing`, `output`, `native?` at lines 854-859).
- Plain Guile Scheme strings carry **zero** hidden dependency metadata; `string=?` is a true congruence on strings.
- Cross-stage references to packages or derivations are introduced explicitly via syntax (`#~` / `#$pkg` for target inputs, `#+pkg` for native cross-compilation inputs) and resolved to concrete store paths plus derivation inputs strictly during monadic lowering (`lower-gexp`, line 1131).

The trade-off is explicitness vs. string-manipulation ergonomics: Nix allows arbitrary string functions (`concatStringsSep`, `replaceStrings`, regexes) to propagate build dependencies transparently at the cost of hidden provenance and broken congruence, whereas Guix preserves pure Scheme string semantics and cross-compilation distinction (`native?`) at the cost of requiring authors to stay inside `<gexp>` combinators whenever composing build-script fragments.

---

### 4. Text-Templated YAML Injection (Helm) vs. Typed Unknown-Value Graphs (Terraform HCL/cty & CUE)

#### 4.1 Helm's Unparsed Go-Template Pipeline and Regex Manifest Splitting

`Basis: source + execution`

Helm (`helm/helm@01b541c8`) treats Kubernetes YAML manifests as unstructured character streams during template evaluation:

1. **String-Level Template Execution (`pkg/engine/engine.go:30, 301-323`):** `Engine.render` instantiates Go's `text/template` (not a YAML AST builder), setting `missingkey=zero` by default unless `Strict` is enabled (`lines 315-321`). Helper functions `toYAML` (`pkg/engine/funcs.go:108-115`) and `fromYAML` (`line 148`) bridge structured values and raw text via `sigs.k8s.io/yaml` (`funcs.go:34-35`), **swallowing marshaling errors silently** inside `toYAML` (returning `""` on error; callers must explicitly opt into `mustToYAML`, lines 122-127).
2. **Indentation Sensitivity & Regex Document Splitting (`pkg/release/v1/util/manifest.go:37-69`):** Before Kubernetes parses the rendered output as YAML, Helm splits multi-resource streams using a pure line-anchored regular expression:
   ```go
   var sep = regexp.MustCompile(`(?m)^---[ \t]*`)
   ```
   As documented directly in Helm's own upstream source comment (`manifest.go:41-48`), this regex operates over raw text without YAML lexical awareness—it even splits malformed lines like `---apiVersion: v1` (without a newline after `---`) into separate documents. Consequently:
   - **Manifest Injection:** Any user-supplied string interpolated without strict `quote` or `toYaml | nindent N` that contains a newline followed by `---` (or unindented YAML keys) breaks out of its containing scalar/field and causes `SplitManifests` to emit a **brand-new top-level Kubernetes object** (e.g., an injected `ClusterRoleBinding`, demonstrated in Probe 1D).
   - **YAML 1.1 vs. YAML 1.2 Coercion ("Norway Problem"):** While Helm v4's `go.mod` uses `sigs.k8s.io/yaml v1.6.0` backed by `sigs.k8s.io/yaml/goyaml.v3` (`funcs.go:35`, YAML 1.2 Core Schema), it still carries `go.yaml.in/yaml/v2 v2.4.4` indirectly, and any chart output or `values.yaml` processed by YAML 1.1 parsers (such as Python's `PyYAML 6.0.3`, verified live in Probe 1D) silently coerces unquoted scalars: `country: NO` $\to$ `False`, `flag_on: on` $\to$ `True`, `flag_off: off` $\to$ `False`, and leading-zero integers `010` $\to$ octal `8` (whereas `0800` remains a string or errors depending on parser!).

#### 4.2 Terraform HCL2 / `go-cty`: Typed 3-Valued Partial Evaluation, Refinements, and Value Marks

`Basis: source + execution`

HashiCorp's HCL2 (`hashicorp/hcl@94e232b5`) and its underlying type/value library `go-cty` (`zclconf/go-cty@5203df26`) reject text templating in favor of an AST-typed, **3-valued partial evaluation algebra** designed for two-phase Infrastructure-as-Code (`plan` then `apply`):

1. **Three-Valued Value Domain (`zclconf/go-cty`, `cty/unknown.go`, `cty/unknown_refinement.go`):** Every typed `cty.Value` is either:
   - **Known non-null** (a concrete value of type $T$),
   - **Known null** (`cty.NullVal(T)`), or
   - **Unknown** (`cty.UnknownVal(T)` or dynamically-typed `cty.DynamicVal`), representing an attribute computable only after cloud-API execution during `apply`.
   Modern `go-cty` further equips unknown values with **abstract-interpretation refinements** (`cty/unknown_refinement.go`: `NotNull()`, `Null()`, `StringPrefix(...)`, `NumberRange(...)`, `CollectionLengthLowerBound(...)`), allowing expressions like `length(unknown_list) > 0` or `x != null` to fold statically during `plan` whenever the refinement suffices.
2. **Orthogonal Provenance Marks (`cty/marks.go:37-490`):** Unlike Nix's hidden string-only context, `go-cty` attaches arbitrary `ValueMarks` (such as Terraform's `marks.Sensitive` and `marks.Ephemeral`) to any value or nested path (`PathValueMarks`). Calling operations on marked values requires explicit unmarking (`Unmark`, `UnmarkDeep`) and re-applying marks (`WithMarks`, `WithSameMarks`), enforced dynamically by `assertUnmarked()` (`cty/marks.go:211`).
3. **Unknown Propagation in Expressions (`hashicorp/hcl`, `hclsyntax/expression.go:726-747, 1392-1413`):**
   - `ConditionalExpr.Value`: if the condition is unknown, evaluates both branches for type unification (`convert.UnifyUnsafe`) and returns an unknown value of the unified type (preserving marks).
   - `ForExpr.Value`: if the iterated collection is `cty.DynamicPseudoType` or unknown, returns an unknown collection rather than crashing; iterating over `null` raises a typed diagnostic (`Iteration over null value`, line 1402).
4. **Plan-Time Graph Expansion Boundary (`hashicorp/terraform@a1246154`, `internal/terraform/eval_for_each.go:201-280`):** Because Terraform must materialize the static resource-instance DAG during `plan` before calling cloud APIs, `forEachEvaluator` enforces a sharp asymmetric knownness and persistence boundary:

| `for_each` Expression Shape | `IsKnown()` | `IsWhollyKnown()` | `marks.Ephemeral` | Terraform `plan` Outcome (`eval_for_each.go`) |
| :--- | :---: | :---: | :---: | :--- |
| Map with static keys, known values `{ "a" = 1 }` | `true` | `true` | `false` | **Accepted** — creates instances `["a"]` |
| Map with static keys, unknown values `{ "a" = aws_vpc.x.id }` | `true` | `false` | `false` | **Accepted** (`lines 226-258`) — map keys are known; unknown values flow into resource attributes |
| Map itself unknown (e.g., conditional on apply-time value) | `false` | `false` | `false` | **Rejected** (`line 226`, `Invalid for_each argument`) |
| Set containing any unknown element `toset([aws_vpc.x.id])` | `true` | `false` | `false` | **Rejected** (`line 247`, `ty.IsSetType() && !forEachVal.IsWhollyKnown()`) — set elements *are* the instance keys |
| Any `for_each` derived from an `ephemeral` value | `true` | `true` | `true` | **Rejected** (`line 267`, `ensureNotEphemeral`) — ephemeral values cannot persist across plan/apply rounds |
| `import` block `for_each` with any unknown component | `true` | `false` | `false` | **Rejected** (`line 204`, `!forEachVal.IsWhollyKnown()`) — import targets must be wholly known |

#### 4.3 Contrast: CUE and Dhall (Typed Unification vs. Text Interpolation)

`Basis: normative + source`

CUE (`cue-lang/cue@b38d73e3`, `doc/ref/spec.md`) eliminates both Helm's unparsed-text injection hazard and Nix's hidden-context equality break by unifying schemas and data inside a **single commutative, associative, idempotent value lattice** ($\top$ = any value, concrete scalars/structs as leaves, $\bot$ = conflict error). Every structural constraint is merged by unification (`&`) on typed AST values before serialization to JSON/YAML, eliminating indentation/delimiter injection by construction; however, unlike Terraform's two-phase `Unknown` partial evaluator, CUE has no native built-in notion of apply-time cloud state mutations or impure DAG staging without an external orchestrator.

---

### 5. Cross-Domain Synthesis: Non-Standard Language Invariants and Verification Hazards

`Basis: derived`

Despite belonging to disparate ecosystems (typesetting, browser layout, build systems, and cloud infrastructure), all four language families exhibit recurring structural hazards that break conventional compiler and formal-verification assumptions:

| System | Violated Classical Assumption | Concrete Mechanism (Pinned Source) | Canonical Failure Mode | Structural Mitigation / Alternative |
| :--- | :--- | :--- | :--- | :--- |
| **TeX / XeTeX** | Stateless lexing prior to parsing; lexical scoping | `tex.web:7250-7497` (`cat_code` consulted only when `state <> token_list`); `tex.web:22776-22782` (`\globaldefs`) | `\verb` / `\catcode` mutations fail on pre-tokenized macro arguments; `\globaldefs=1` leaks local state | Re-tokenization (`\scantokens`), or phase-separated parsers with fixed lexers (Typst, Pandoc) |
| **CSS Flexbox / Grid / `@container`** | Single-pass acyclic attribute grammar | `css-grid-1/Overview.bs:3619-3651, 3814`; `css-conditional-5/Overview.bs:668-708`; Blink `grid_layout_algorithm.cc:78-97` | Non-monotone `@container` 2-cycle oscillation (`600 <-> 150`); exponential nested flex/grid intrinsic measurement | Mandatory `container-type: inline-size \| size` DAG cuts; normative fallback rules for cyclic percentages & baselines |
| **XSLT 3.0** | Arbitrary tree random access | W3C XSLT 3.0 Section 19 `(Posture, Sweep)` static analysis | Multiple consuming operands over a stream or `roaming`/`free-ranging` navigation | Compile-time rejection (`XTSE3430`), forcing explicit `xsl:fork` or bounded `copy-of()` |
| **Nix / Tvix** | Extensional equality (`==` as congruence); inner scope shadows outer scope | `NixOS/nix` `eval.cc:3013-3014`, `primops.cc:4690-4695`, `nixexpr.cc:315-349`; `tvlfyi/tvix` `string/mod.rs:375-379` | `s1 == s2` true yet `derivation` / `hasContext` / attr-key diverge; outer `let` shadows inner `with` | Typed staged ASTs keeping strings context-free (GNU Guix `<gexp>` / `<gexp-input>` in `guix/gexp.scm:165-172`) |
| **Helm + YAML** | Typed AST interpolation; schema-stable scalar syntax | `helm/helm` `engine.go:301-323`, `manifest.go:37-69` (`(?m)^---[ \t]*`), `funcs.go:108-115` | Multiline string injects extra Kubernetes manifest via `---`; YAML 1.1 `NO -> false`, `010 -> 8` | Strict AST-level configuration unification (CUE `doc/ref/spec.md`, Dhall, Jsonnet) or Kubernetes Server-Side Apply typed builders |
| **Terraform HCL / `go-cty`** | Total 2-valued evaluation | `go-cty` `unknown.go`, `unknown_refinement.go`, `marks.go`; `terraform` `eval_for_each.go:220-280` | `Invalid for_each argument` when set elements or map keys depend on apply-time attributes or ephemeral marks | Separate static topology keys from unknown values (`{ "static_key" = unknown_val }`), or staged `-target` applies |

**Engineering and Verification Takeaway:** Any static analyzer, optimizer, linter, or formal verifier targeting these languages must explicitly model their **hidden side channels in values and syntax**:
- Token representations in TeX analyzers must be `(catcode, charcode)` pairs coupled to a mutable `eqtb` + `save_stack`, not raw strings.
- Formal CSS layout solvers extending `Cassius` beyond CSS 2.1 must encode multi-pass intrinsic sizing and explicit containment boundaries rather than a single flat LRA pass.
- Nix program transformations and evaluators must treat string equivalence as a **pair** `(bytes, context_set)` whenever context-sensitive builtins or derivations remain in scope.
- Security scanners for Helm charts must inspect **post-render** YAML streams *and* `SplitManifests` boundaries rather than auditing Go templates or raw YAML in isolation.

## Boundaries

- **LuaTeX Lua-level lexer and node-list callbacks (`not examined`):** While LuaTeX shares TeX's core `\catcode` and mouth/stomach token model, its Lua extension hooks (`process_input_buffer`, `token.scan_*`, `pre_linebreak_filter`) allow arbitrary programmatic rewriting of input buffers and node lists before and after tokenization; those Lua-specific APIs were not inspected at source level here.
- **CSS Subgrid, Anchor Positioning, and Scroll-State Container Queries (`not examined`):** CSS Conditional 5 (`css-conditional-5/Overview.bs:692-703`) introduces `container-type: scroll-state`, and CSS Grid Level 2 adds `subgrid` cross-tree track participation (`ComputeMinMaxSizesForSubgrid` in Blink `grid_layout_algorithm.cc:616`). Their full cycle-avoidance proofs and interaction with CSS Anchor Positioning were not examined in depth.
- **Nix experimental `dynamic-derivations` and `ca-derivations` (`not examined`):** `NixOS/nix` supports experimental recursive/built-output `SingleDerivedPath` nesting under `--extra-experimental-features dynamic-derivations`. The 3-variant `NixStringContextElem` table above covers the stable `Opaque` / `Built` / `DrvDeep` model; recursive `Built` chains under experimental flags were not exercised.
- **Helm post-renderer `kio.ParseAll` interaction in Chart API v3 (`unknown`):** `helm/helm@01b541c8` (`pkg/release/v1/util/manifest.go:41-48`) notes an unresolved tension between the legacy `(?m)^---[ \t]*` splitter and `kio.ParseAll` annotation injection in Helm 4 post-renderers, flagging removal of the regex for a future Chart API v3; whether a future release will break backward compatibility with charts emitting `---apiVersion: v1` remains open upstream.
- **Cassius SMT encoding of CSS Flexbox/Grid (`unsupported`):** `uwplse/cassius@60dad9e9` explicitly models a CSS 2.1 fragment (blocks, inline line layout, floats, positioning) and does not support CSS Flexbox, Grid, or `@container` queries.
- **Extension of YAML 1.1 Norway coercion to Helm v4 internal `toYAML` (`known not to apply` unconditionally):** Because `helm/helm@01b541c8` (`pkg/engine/funcs.go:34-35`) uses `sigs.k8s.io/yaml v1.6.0` (`goyaml.v3`, YAML 1.2 Core Schema), unquoted `NO` is not coerced to `false` inside Helm v4's `goyaml.v3` parser itself; the YAML 1.1 coercion hazard applies when manifests or values pass through YAML 1.1 tools (such as Python `PyYAML 6.0.3`, legacy Go `yaml.v2`, or older Helm/Kubernetes client libraries).

## Evidence

### Primary Repositories and Specifications Inspected (Observed 2026-11-19)

1. **TeX (`TeX-Live/texlive-source`, commit `b4e37b58bfc6352cc3223ed26384cae01a28b234`):**
   - `texk/web2c/tex.web:4063-4083`: 16 character category code definitions (`escape=0` through `invalid_char=15`).
   - `texk/web2c/tex.web:5992-6008`: `eq_define` / `eq_word_define` saving previous `eqtb` values onto `save_stack` on group entry.
   - `texk/web2c/tex.web:6169-6182`: `cs_token_flag = @'7777`, character token encoding `256 * cmd + chr`.
   - `texk/web2c/tex.web:7237-7275, 7418, 7477-7515`: `get_next` branching on `state <> token_list` (`cur_cmd := cat_code(cur_chr)`) vs `state = token_list` (`cur_cmd := t div @'400; cur_chr := t mod @'400`), skipping `cat_code` lookup on already-tokenized token lists.
   - `texk/web2c/tex.web:7663-7679, 7825, 8240-8256, 9221`: `expand`, `get_x_token`, `scan_keyword` (expanding tokens and pushing back via `back_input` / `back_list(link(backup_head))`), and `roman_numeral_code`.
   - `texk/web2c/tex.web:22776-22782`: `\globaldefs` overriding local/global prefix flags (`a := a + 4` / `a := a - 4`).
2. **Tectonic (`tectonic-typesetting/tectonic`, commit `d2224d9ba4185f952fd3d982eccd1f444dbdf895`):**
   - `crates/engine_xetex/xetex/xetex-constants.h:347-361`: Unicode 21-bit token encoding (`MAX_CHAR_VAL = 0x200000`, `CS_TOKEN_FLAG = 0x1FFFFFF`, `LETTER_TOKEN = 0x1600000`, `OTHER_TOKEN = 0x1800000`).
3. **W3C CSS Drafts (`w3c/csswg-drafts`, commit `5e83e63e7561e02f24fdccf30b08ebd222eb794c`):**
   - `css-flexbox-1/Overview.bs:1481, 3588-4290`: Section 9 Flex Layout Algorithm (`#line-sizing`, `#cross-sizing`, `#intrinsic-sizes`, cyclic percentage handling).
   - `css-grid-1/Overview.bs:3619-3651, 3797-4615`: Baseline-alignment vs. intrinsic-track cyclic fallback rules (`lines 3619-3651`), cyclic percentage tracks (`line 3814`), and Track Sizing Algorithm (`#algo-track-sizing`, `line 4015`).
   - `css-contain-3/Overview.bs:57-60` and `css-conditional-5/Overview.bs:495-720`: Relocation of `@container` to CSS Conditional 5, mandatory `size`/`inline-size` containment on `container-type` (`lines 677-708`), ancestor eligibility (`lines 507-509`), and sibling-cycle prohibition (`line 548`).
4. **Chromium Blink (`chromium/chromium`, commit `a96bb3157067818fef60e0c0635a8dee3d87893a`):**
   - `third_party/blink/renderer/core/css/container_query_evaluator.cc:32-41, 242-260`: `ContainerTypeAxes` mapping `container-type` to physical contained axes and unit-flag-guarded query evaluation caching.
   - `third_party/blink/renderer/core/layout/flex/flex_layout_algorithm.cc:827-917, 1747`: `ConstructAndAppendFlexItems` intrinsic `ComputeMinMaxSizes` and `GiveItemsFinalPositionAndSize`.
   - `third_party/blink/renderer/core/layout/grid/grid_layout_algorithm.cc:78-97, 262, 358, 1172`: Multi-pass `ComputeGridGeometry` and `ComputeUsedTrackSizes`.
5. **Cassius (`uwplse/cassius`, commit `60dad9e9b2b4de3b13451ce54cdc1bd55ca64824`):**
   - `src/spec/layout.rkt:105-136`: SMT-LIB2 / Z3 LRA formalization of CSS 2.1 box geometry (`ppflow`, `pbflow`, `contains-content`).
   - Peer-reviewed papers: Pavel Panchekha and Emina Torlak, *Automated Reasoning for Web Page Layout*, OOPSLA 2016, pp. 181–194, DOI `10.1145/2983990.2984010`; Pavel Panchekha, Adam T. Geller, Michael D. Ernst, Zachary Tatlock, and Shoaib Kamil, *Verifying That Web Pages Have Accessible Layout*, PLDI 2018, DOI `10.1145/3192366.3192407`.
6. **W3C XSLT 3.0 Recommendation (`2017-06-08`, `https://www.w3.org/TR/xslt-30/`):**
   - Section 6.4 (Conflict Resolution for Template Rules) and Section 19 (Extensibility and Streamability: postures `{grounded, climbing, striding, crawling, roaming}` and sweeps `{motionless, consuming, free-ranging}`).
7. **Nix (`NixOS/nix`, commit `6965392507e19998de706aa15e514f81e9b7ce11`):**
   - `src/libexpr/include/nix/expr/value/context.hh:37-103`: `NixStringContextElem` (`Opaque`, `DrvDeep`, `Built`) and `NixStringContext`.
   - `src/libexpr/eval.cc:2825-2833, 2983-3015`: `assertEqValues` and `EvalState::eqValues` comparing `v1.string_view() == v2.string_view()` while ignoring string context.
   - `src/libexpr/primops/context.cc:10-32, 290-325`: `prim_unsafeDiscardStringContext`, `prim_hasContext`, `prim_appendContext`.
   - `src/libexpr/primops.cc:4671-4695`: `prim_substring` preserving string context on zero-length substrings (`len == 0`).
   - `src/libexpr/nixexpr.cc:315-349, 529-554`: `ExprVar::bindVars` resolving all lexical frames prior to any `isWith` frame, and `ExprWith::bindVars` chaining `prevWith`.
8. **Tvix (`tvlfyi/tvix`, commit `745668238b829ef56131d198560c2c7471b94458`):**
   - `eval/src/value/string/context.rs:6-28`: `NixContextElement::{Plain, Single, Derivation}` and `NixContext(FxHashSet<NixContextElement>)`.
   - `eval/src/value/string/mod.rs:32-48, 375-380`: `NixStringInner` inline layout and `PartialEq for NixString` comparing `self.as_bstr() == other.as_bstr()`.
9. **GNU Guix (`https://codeberg.org/guix/guix`, commit `d19bb5cf43f2fb41793813c6a43c7f77856ae0bd`):**
   - `guix/gexp.scm:165-190, 854-876, 1131-1155`: `<gexp>`, `<gexp-input>`, and `lower-gexp`.
10. **Helm (`helm/helm`, commit `01b541c8e4e15ac2f1fa4616234d1cb9883fc381`):**
    - `pkg/engine/engine.go:30, 205-209, 301-323`: `text/template` rendering and `missingkey=zero`.
    - `pkg/engine/funcs.go:34-35, 108-127, 148`: `sigs.k8s.io/yaml` / `goyaml.v3`, error-swallowing `toYAML` vs panicking `mustToYAML`.
    - `pkg/release/v1/util/manifest.go:37-69`: `sep = regexp.MustCompile("(?m)^---[ \t]*")` and `SplitManifests`.
    - `go.mod`: `sigs.k8s.io/yaml v1.6.0`, `go.yaml.in/yaml/v3 v3.0.6`, indirect `go.yaml.in/yaml/v2 v2.4.4`.
11. **HCL2, `go-cty`, Terraform, and CUE:**
    - `zclconf/go-cty@5203df261916a8da241b127bf8c7b13f6f684854`: `cty/unknown.go`, `cty/unknown_refinement.go`, `cty/marks.go:37-490`.
    - `hashicorp/hcl@94e232b58b12531a80299e3aa7566f345e17c21b`: `hclsyntax/expression.go:726-747` (`ConditionalExpr.Value`), `1392-1413` (`ForExpr.Value`).
    - `hashicorp/terraform@a1246154d166f0647e398b823f0d9a3b9b64e920`: `internal/terraform/eval_for_each.go:201-280` (`ensureKnownForImport`, `ensureKnownForResource`, `ensureNotEphemeral`).
    - `cue-lang/cue@b38d73e3f13559da0ba290e7e61d21ae7230a6ae`: `doc/ref/spec.md`.

### Execution Probes (Observed 2026-11-19, Python 3.13.15, PyYAML 6.0.3, Linux x86_64)

Running a standalone Python verification script modeling `tex.web:7250-7497`, `@container` fixed-point iteration, Nix `eqValues`/`prim_substring`/`ExprVar::bindVars`, Helm's exact `(?m)^---[ \t]*` `SplitManifests` regex plus live `PyYAML 6.0.3` `yaml.safe_load`, and Terraform's `for_each` knownness rules produced the following verbatim witness outputs:

```text
=== PROBE 1A: TeX catcode-freezing (tex.web:7250-7497) ===
Direct scan after \catcode`\\=12 : [(12, '\\'), (11, 'b'), (11, 'a'), (11, 'r')]
Frozen macro arg token list       : [('CS', 'bar')]

=== PROBE 1B: CSS @container style-size oscillation vs inline-size containment ===
Uncontained cycle trace (step, font_size, width): [(0, 40, 600), (1, 10, 150), (2, 40, 600), (3, 10, 150), (4, 40, 600), (5, 10, 150)]
Contained (inline-size) trace (font_size, width): [(40, 400), (40, 400), (40, 400)]

=== PROBE 1C: Nix/Tvix (Bytes, ContextSet) Leibniz's Law violation & let/with precedence ===
s1 == s2 (Nix ==)                     : True
hasContext(s1) vs hasContext(s2)      : True vs False
substring(0,0,s1) == '' & hasContext  : True True
derivation inputDrvs from s1 vs s2    : ['!out!/nix/store/00000000000000000000000000000000-hello.drv'] vs []
let x=1; in with {x=2; y=3;}; lookup x: ('lexical', 1) lookup y: ('with', 3)

=== PROBE 1D: Helm SplitManifests regex injection & YAML 1.1 Norway coercion ===
Helm SplitManifests produced 2 documents from 1 ConfigMap template:
  manifest-0: apiVersion: v1 | kind: ConfigMap
  manifest-1: apiVersion: rbac.authorization.k8s.io/v1 | kind: ClusterRoleBinding
PyYAML (YAML 1.1) safe_load: {'country': False, 'flag_on': True, 'flag_off': False, 'sexagesimal_or_octal': 8}

=== PROBE 1E: Terraform HCL/cty Unknown propagation & for_each key-knownness ===
for_each = { a = UNKNOWN, b = 'x' } -> OK: static instance keys ['a', 'b'] (values may be unknown: True)
for_each = toset([UNKNOWN, 'x'])    -> ERROR: Invalid for_each argument (unknown set element)
```

## Revalidation

To verify whether these invariants still hold against newer upstream revisions without repeating the full multi-repository audit, run the following narrow discriminating checks:

1. **TeX / Tectonic Token-Freezing Check:** Diff `texk/web2c/tex.web` around `procedure get_next` (and Tectonic's `xetex-constants.h` `CS_TOKEN_FLAG`) to verify that `state = token_list` still decodes pre-tokenized `(cmd, chr)` integers without consulting `cat_code`. If a TeX binary (`pdftex` or `tectonic`) is installed locally, compile `\def\f#1{\catcode`\\=12 \meaning#1}\f{\bar}\bye` and confirm it prints `undefined` (control sequence) rather than `the character \`.
2. **CSS `@container` & Grid Cycle Checks:** Diff `w3c/csswg-drafts` `css-conditional-5/Overview.bs` around `dfn-for=container-type` (confirming `size` and `inline-size` still mandate size/inline-size containment) and `chromium/chromium` `container_query_evaluator.cc` (`ContainerTypeAxes`).
3. **Nix / Tvix Context-Blind Equality & `with` Precedence Check:** Diff `NixOS/nix` `src/libexpr/eval.cc` (`EvalState::eqValues`, `case nString`), `src/libexpr/nixexpr.cc` (`ExprVar::bindVars`), and `tvlfyi/tvix` `eval/src/value/string/mod.rs` (`impl PartialEq for NixString`). If `nix-instantiate` is available, run:
   ```bash
   nix-instantiate --eval -E 'let s = builtins.placeholder "out"; d = builtins.unsafeDiscardStringContext s; in [ (s == d) (builtins.hasContext s) (builtins.hasContext d) (builtins.hasContext (builtins.substring 0 0 s)) ]'
   ```
   and confirm the output `[ true true false true ]`, plus:
   ```bash
   nix-instantiate --eval -E 'let x = 1; in with { x = 2; y = 3; }; [ x y ]'
   ```
   confirming `[ 1 3 ]`.
4. **Helm Regex Splitter & YAML 1.1 Check:** Inspect `helm/helm` `pkg/release/v1/util/manifest.go` for `var sep = regexp.MustCompile(...)` (tracking whether Helm Chart API v3 replaces regex splitting with AST-aware YAML document parsing) and re-run:
   ```bash
   python3 -c 'import re, yaml; sep=re.compile(r"(?m)^---[ \t]*"); print(len([d for d in sep.split("a: 1\n---\nb: 2") if d.strip()]), yaml.safe_load("country: NO\nflag: on\noct: 010"))'
   ```
5. **Terraform `for_each` Boundary Check:** Diff `hashicorp/terraform` `internal/terraform/eval_for_each.go` (`ensureKnownForResource` and `ensureNotEphemeral`) to verify whether future Terraform versions relax set-element knownness or introduce deferred plan phases (e.g., `-defer` stacks) that alter plan-time `IsWhollyKnown()` enforcement.
