# Verified Lexing, CST Parsing, and Closing the Bytes-to-AST Front-End Gap

## Summary

End-to-end compiler and verifier soundness theorems routinely begin at an internal abstract syntax tree (AST) or intermediate representation (IR), leaving a critical **bytes-to-AST trusted computing base (TCB) gap** in preprocessing, lexical disambiguation, parsing, precedence resolution, and source elaboration. Even in CompCert (`AbsInt/CompCert`), the Menhir-generated LR(1) parser (`Parser.vy`) is validated in Rocq for safety and completeness (`MenhirLib/Validator_safe.v`, `Validator_complete.v`, `Interpreter_correct.v`, `Interpreter_complete.v`), yet it still sits downstream of an unverified preprocessor-line check (`Parse.ml`), an ocamllex scanner (`Lexer.mll`), an unverified OCaml pre-parser (`pre_parser.mly`) that mutates identifier-classification cells (`VarId | TypedefId | OtherId`) to resolve C11's `typedef` ambiguity, and a 3,377-line unverified type elaborator (`Elab.ml`) before reaching verified `Csyntax` (`Csem.v`) and its relational evaluation-order lowering (`SimplExpr.v`, `Cshmgen.v`). By contrast, `CakeML/cakeml` verifies its entire byte-stream front end in HOL4—refining a functional lexer specification (`lexer_fun`) to a merged state-machine lexer (`lexer_impl`), proving PEG soundness, completeness, and context-free grammar unambiguity (`peg_sound`, `completeness`, `cmlG_unambiguous`), and proving Hindley-Milner type inference soundness (`infer_prog_sound`)—at the cost of a 5.9x manual proof-to-grammar expansion ratio (5,047 proof lines for an 850-line PEG).

Outside verified compilers, lossless Concrete Syntax Trees (`rust-analyzer/rowan`, `tree-sitter/tree-sitter`) preserve byte-exact round-tripping (`render(parse_cst(bytes)) == bytes`) via immutable shared green trees (`GreenNode`, 16-byte `GreenChild` entries) and trivia-attached tokens (`GreenTokenHead`), while verified binary codec frameworks (`Vest`, `EverParse`) establish machine-checked non-malleable wire bijections (`PSRoundTrip`: `spec_serialize(v) == ibuf[0..n]`) that general programming-language grammars rarely achieve due to comments, whitespace, and precedence ambiguity. Crucially, visual-to-parsed mismatches—including Trojan Source Unicode Bidi/homoglyph attacks (CVE-2021-42574, CVE-2021-42694), C/Rust vs. Python/Go bitwise-vs-comparison precedence inversions (`a & b == c` diverging on 44.89% of enumerated unparenthesized 3/4-leaf expressions in a Python probe, with naive AST printing passing only 22.73% of round-trips), dangling-`else` shifts, and non-compositional off-side layout rules—arise directly from syntactic conventions rather than IR defects. Separating pure tree structure from historical lexer-feedback hacks and adopting partial-order operator precedence alongside lossless green CSTs or invertible syntax descriptions removes these front-end surprises without shifting complexity into downstream verifiers.

## Applicability

This report synthesizes source inspection, normative specification analysis, peer-reviewed verification literature, and executable Python probes across six pinned repositories and eight published specifications/papers, observed on 2026-11-19:

- **Full-stack C and ML verified front ends:** `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`) covers verified LR(1) parsing via MenhirLib (`Validator_safe.v`, `Validator_complete.v`, `Interpreter_correct.v`, `Interpreter_complete.v`), unverified C11 lexical feedback (`cparser/Lexer.mll`, `pre_parser.mly`, `Parse.ml`, `Elab.ml`), and verified C AST lowering (`cfrontend/Csem.v`, `SimplExpr.v`, `SimplExprproof.v`, `Cshmgen.v`, `Cshmgenproof.v`). `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`) covers verified lexing (`semantics/lexer_funScript.sml`, `compiler/parsing/lexer_implScript.sml`), verified PEG parsing (`compiler/parsing/cmlPEGScript.sml`, `proofs/pegSoundScript.sml`, `proofs/pegCompleteScript.sml`), and verified type inference (`compiler/inference/proofs/inferSoundScript.sml`, `inferCompleteScript.sml`).
- **CST representations and incremental parsers:** `rust-analyzer/rowan` (`d601b195d7bcb9f643c218b2ba113257880d2cdd`) defines red-green lossless syntax trees (`src/green/node.rs`, `src/green/token.rs`, `src/green/element.rs`, `src/cursor.rs`); `tree-sitter/tree-sitter` (`f0090e112482d66653b43ca73e85668db1cde794`) defines bounded GLR incremental CST parsing (`lib/src/parser.c`).
- **Verified wire-format bijections (contrasted with programming-language text parsing):** `secure-foundations/vest` (`026867a37d4b918153058df2c8db6c52fc62ba35`, `vest_lib/src/core/{spec.rs,proof.rs}`) and `project-everest/everparse` (`270f5aab699ac284d8777d4f01be20a5d91ea47c`, `README.md`) characterize lossless binary serialization/parsing round-trips.
- **Standalone execution probe scope:** The embedded Python 3.13.15 probe establishes exact round-trip percentages (`80/352` naive vs. `352/352` guarded) and cross-language AST divergence (`158/352`) over a restricted operator subset `{|, &, ==, +}` with 3–4 leaves, plus a discrete simulation of CompCert's C11 `typedef` scope stack vs. naive 1-token LR(1) lookahead. These probe measurements apply literally to the enumerated expression grammar and modeled state transitions, illustrating structural properties of C/Rust/Python/Go operator tables rather than benchmarking full production C11/Rust compilers.

Findings for CompCert's Rocq parser validator generalize to any Menhir `--coq` grammar meeting the `safe` and `complete` validation checks, whereas CompCert's two-pass `Pre_parser` design is specific to C's context-sensitive `typedef` grammar. CakeML's `cmlPEG` theorems apply strictly to the CakeML concrete syntax grammar proved unambiguous in `cmlG_unambiguous`.

## Findings

### 1. Anatomy of the Bytes-to-AST Trusted Computing Base Gap

`Basis: source + normative + literature`

A verified middle-end or backend proves simulation from a typed AST or IR to target machine code, but humans and auditors write and review UTF-8/ASCII bytes. Any silent divergence between what a reader perceives in source text and the AST fed into the verified compiler invalidates downstream guarantees:

| Stage | CompCert (`2685140bf7`) | CakeML (`2874b664e1`) | CoStar + Verbatim (Literature) | Primary Trust Boundary |
|---|---|---|---|---|
| **Source encoding / preprocessing** | External `cpp` + unverified OCaml `check_preprocessed` (`Parse.ml:72-77`) rejecting leftover `\\\n` and `??/\n` | Direct HOL4 character `string` input to `lexer_fun` | Character/byte stream into DFA lexer | Invisible Bidi overrides (CVE-2021-42574) and homoglyphs (CVE-2021-42694) reorder visual tokens without parser rejection |
| **Lexing** | Unverified `ocamllex` (`Lexer.mll`, 751 lines) + mutable `ident_type ref` | **Verified** `lexer_impl` refining `lexer_fun` (`lexer_correct`, `lexer_implScript.sml:631-635`) | **Verified** regex DFA (`Verbatim`, `doi:10.1109/SPW53761.2021.00022`) | Lexical ambiguity (`typedef` vs. `var`, maximal munch `>>` vs. nested templates, Unicode normalization) |
| **Context disambiguation** | Unverified OCaml LR(1) `pre_parser.mly` (958 lines) with 2 precedence-resolved shift/reduce conflicts | Not needed (ML namespaces separate constructors/variables lexically without `typedef`) | Grammar-level ALL(*) adaptive lookahead (`CoStar`, `doi:10.1145/3453483.3454053`) | Any divergence between pre-parser scope rules and verified parser grammar causes `Fail_pr` or misparsed identifiers |
| **Parsing (Tokens -> AST)** | **Verified** Rocq LR(1) interpreter (`Parser.vy`, 1,038 lines) + MenhirLib validator | **Verified** PEG engine (`cmlPEG`, 850 lines) proved sound, complete, and unambiguous | **Verified** ALL(*) ATN simulator in Rocq (`CoStar`) | Fuel exhaustion (`2^50` steps in CompCert `Parse.ml:45`) or unverified PEG ordered-choice prefix capture |
| **Elaboration / Typechecking** | Unverified OCaml `Elab.ml` (3,377 lines) + `Unblock`/`SwitchNorm` (`Parse.ml:19-35`) -> `Csyntax` | **Verified** HM inferencer (`infer_prog_sound`, `inferSoundScript.sml:1355`) | Unverified or external downstream checker | Implicit casts, integer promotions, overloaded declarations; empirical target of early CSmith bugs in CompCert (`doi:10.1145/1993498.1993532`) |

Empirically, Yang et al. (PLDI 2011, `doi:10.1145/1993498.1993532`) tested CompCert 1.6 with CSmith and found zero wrong-code bugs in the Rocq-verified middle-end and backend, while the small number of defects discovered sat in the unverified front-end/elaboration layer and unverified hardware/ABI models—empirically validating the practical significance of closing the bytes-to-AST gap.

Furthermore, Boucher and Anderson's Trojan Source disclosure (`arXiv:2111.00169`, CVE-2021-42574 and CVE-2021-42694) demonstrated that even an *exact* verified parser over Unicode codepoints suffers a human-perception gap if lexers accept invisible Bidirectional (Bidi) isolate/override controls (`U+202E` RLO, `U+2066`–`U+2069` LRI/RLI/FSI/PDI) inside comments or string literals, or non-ASCII homoglyphs in identifiers: an editor implementing the Unicode Bidirectional Algorithm renders tokens in visual order contradicting logical token order. Mitigating this at the lexing boundary requires either rejecting unterminated/unscoped Bidi formatting characters inside tokens and banning mixed-script confusable identifiers at lex time.

---

### 2. CompCert + Menhir: Translation Validation of LR(1) Automata and the C11 Lexer-Feedback Seam

`Basis: source + literature`

Rather than formally verifying Menhir's complex OCaml LALR(1)/LR(1) automaton construction algorithm, Jourdan, Pottier, and Leroy (ESOP 2012, `doi:10.1007/978-3-642-28869-2_20`) introduced **a posteriori translation validation** in `MenhirLib`: Menhir emits an untrusted Rocq automaton module (`Parser.vy` compiled to LR tables + LR(1) item-set certificates `items_map`), and a small verified Rocq checker (`Validator_safe.v`, 233 lines; `Validator_complete.v`, 393 lines) checks Boolean invariants by computational reflection before the verified interpreter (`Interpreter_correct.v`, 174 lines; `Interpreter_complete.v`) executes.

#### 2.1 Safety and Completeness Certificates in `MenhirLib`

1. **LR(1) Stack-Typing Safety (`MenhirLib/Validator_safe.v`):**
   - `Validator_safe.v:224-226` defines `safe := shift_head_symbs /\ goto_head_symbs /\ shift_past_state /\ goto_past_state /\ reduce_ok`.
   - Every state carries invariant annotations (`head_symbs_of_state`, `head_states_of_state`, `past_state_of_state`). For every `Reduce_act p` or `Default_reduce_act p`, `valid_for_reduce` (`lines 197-209`) statically verifies that `prod_rhs_rev prod` is a prefix of `head_symbs_of_state state`, and that for any `state_new` matching `state_valid_after_pop`, `goto_table state_new (prod_lhs prod)` either transitions to a valid state or hits `Init i` with `prod_lhs prod = start_nt i`.
   - `Interpreter_correct.v:157-164` proves `parse_correct`: whenever `safe` holds and `parse safe init buffer log_n_steps` returns `Parsed_pr sem buffer_new`, there exists a valid grammar `parse_tree (NT (start_nt init)) word_new` with `buffer = (word_new ++ buffer_new)%buf` and `pt_sem pt = sem`.

2. **LR(1) Completeness (`MenhirLib/Validator_complete.v` & `Interpreter_complete.v`):**
   - Safety alone allows a trivial parser that always returns `Fail_pr`. Completeness requires verifying that the automaton's state space covers Knuth's canonical LR(1) item closure without missing shift or reduce transitions.
   - `Validator_complete.v:380-382` checks `complete := nullable_stable /\ first_stable /\ start_future /\ terminal_shift /\ end_reduce /\ non_terminal_goto /\ start_goto /\ non_terminal_closed` against a Menhir-supplied witness `items_map : unit -> StateProdPosMap.t TerminalSet.t` (`line 77`).
   - Using `IsValidator` typeclasses (`complete_is_validator`, `lines 389-391`), Rocq verifies the Boolean `is_complete ()` reflection predicate over the concrete automaton.
   - `Interpreter_complete.v:800-805` proves `parse_complete`: for any valid parse tree `full_pt` over `full_word ++ buffer_end`, `parse safe init (full_word ++ buffer_end) log_n_steps` never returns `Fail_pr`; it either returns `Parsed_pr (pt_sem full_pt) buffer_end` (when `pt_size full_pt <= 2^log_n_steps`) or `Timeout_pr`. In `cparser/Parse.ml:45`, CompCert passes `log_fuel = 50` (`2^50` steps).

#### 2.2 C11 `typedef` Ambiguity and the Unverified `Pre_parser` Seam

In ISO C11, `T * x;` is either a pointer declaration (if `T` is a `TYPEDEF_NAME` in the current lexical scope) or a multiplication expression (if `T` is a `VAR_NAME`). As Jourdan and Pottier detail in TOPLAS 2017 (`doi:10.1145/3064848`) and implement in `cparser/Lexer.mll`, `pre_parser.mly`, and `pre_parser_aux.ml`, naive 1-token LR(1) lexer feedback breaks when the parser fetches lookahead before executing the semantic action that updates the scope table (for example, `typedef int T; void f(void) { { int T = 1; } T * p; }`, where peeking `T` before reducing `compound_statement` on `}` would misclassify `T` as `VarId` instead of `TypedefId`, or `int f(int (t))` documented at `pre_parser.mly:639-672`).

CompCert resolves this with a **two-pass front-end split** (`Lexer.mll:580-750` & `pre_parser.mly`):
1. `Lexer.tokens_stream` runs an unverified OCaml `Pre_parser` (`pre_parser.mly`, 958 lines) using Menhir's incremental API (`Pre_parser.Incremental.translation_unit_file`) over a live `ocamllex` token stream.
2. Whenever `Lexer.lexer` scans an identifier (`PRE_NAME id`), it inserts `PRE_NAME id` into the stream immediately followed by a fresh mutable reference token `Pre_parser.TYPEDEF_NAME (id, ref TypedefId, loc)` or `VAR_NAME (id, ref VarId, loc)` (`Lexer.mll:588-592`), while pushing that token into a FIFO `Queue.t`.
3. `Pre_parser` uses `PRE_NAME` as a lookahead sentinel to force early scope-checkpoint reductions (`save_context` at `pre_parser.mly:221-222, 742-780, 822`) and mutates `r := VarId | TypedefId | OtherId` (`set_id_type`, `declare_varname`, `declare_typename` in `pre_parser.mly:29-36`) *before* `PRE_NAME`'s paired token is consumed as lookahead.
4. Once `Pre_parser` succeeds, `tokens_stream` pops the FIFO queue (`Lexer.mll:627-749`), reading each frozen `!typ` cell to emit `Parser.VAR_NAME`, `Parser.TYPEDEF_NAME`, or `Parser.OTHER_NAME` into the Rocq-verified `Parser.vy` (`Lexer.mll:729-735`), and merges adjacent `STRING_LITERAL` tokens (`lines 709-723`).

**Residual TCB seam:** Notice that `Parser.vy` splits `statement_safe` and `statement_dangerous` (`Parser.vy:94-100, 879-893`) to eliminate the dangling-`else` shift/reduce conflict completely (zero unresolved conflicts in the verified grammar), whereas `pre_parser.mly:19-24, 76-82` still uses `%nonassoc TYPEDEF_NAME` and `%nonassoc ELSE` to resolve 2 shift/reduce conflicts and remains **outside** Rocq's proof. If `Pre_parser` misclassifies a token or emits an unexpected token sequence, `Parse.ml:51-56` aborts with `"internal error while parsing"` (`Fail_pr`), or worse, classifies a variable as a typedef or vice versa identically to how the verified parser expects—without Rocq checking C11's scope rules!

---

### 3. CompCert `Csyntax -> Clight -> Csharpminor` Evaluation-Order Lowering

`Basis: source`

Even after `Parser.vy` yields a `Cabs` AST and unverified `Elab.ml` (3,377 lines) typechecks and resolves overloading into `Csyntax`, CompCert must bridge a substantial semantic gap between C surface expressions (which permit arbitrary interleaving of side effects between sequence points) and structured IRs:

1. **Nondeterministic Reduction Contexts in `Csyntax` (`cfrontend/Csem.v`):**
   - `Csem.v` splits expression semantics into lvalue head reductions (`lred`, `lines 214-236`), rvalue head reductions (`rred`, `lines 240-310`), function-call head reductions (`callred`), and composable evaluation contexts (`context : kind -> kind -> (expr -> expr) -> Prop`, `lines 351-401`), where `ctx_binop_left` and `ctx_binop_right` allow *either* operand of a binary operator or assignment (`ctx_assign_left` / `ctx_assign_right`) to reduce first.
   - To prove deterministic compilation safe under ISO C's unspecified evaluation order, `Csem.v:403-443` defines `not_stuck e m`: *all* reducible subexpressions under any context `C` must be `imm_safe`, so `(x = 1) + (10 / x)` (with `x = 0`) is rejected as undefined rather than rescued by left-to-right luck.
2. **Determinization and Side-Effect Hoisting (`Cstrategy.v`, `SimplExpr.v`, `SimplExprproof.v`):**
   - `Cstrategy.v` defines a deterministic evaluation strategy (a sound subset of `Csem` reductions when expressions are safe).
   - `SimplExpr.v` (643 lines) uses a fresh-variable state monad (`gensym`, `lines 24-75`) to hoist assignments, post-increments, and function calls out of expressions into `Clight` statements (`Ssequence`, `Sset`, `Scall`), leaving `Clight` expressions completely side-effect-free.
   - `SimplExprproof.v:2428-2437` proves `transl_program_correct : forward_simulation (Cstrategy.semantics prog) (Clight.semantics1 tprog)`.
3. **Byte-Offset and Memory Addressing Lowering (`Cshmgen.v`, `Cshmgenproof.v`):**
   - `Cshmgen.v` (793 lines) translates C types, structs/unions, array indexing, and signed/unsigned promotions into explicit address arithmetic and memory chunks in `Csharpminor`, proved via `Cshmgenproof.v:2015-2023` (`forward_simulation (Clight.semantics2 prog) (Csharpminor.semantics tprog)`).

---

### 4. CakeML: End-to-End Verified Byte-Stream Lexing, PEG Parsing, and Type Inference

`Basis: source + literature`

Unlike CompCert's unverified OCaml lexer/pre-parser/elaborator, `CakeML/cakeml` (`2874b664e1`) verifies the entire path from a raw character list (`string`) to typed AST in HOL4 (Kumar et al., POPL 2014, `doi:10.1145/2535838.2535841`):

1. **Two-Phase Functional Lexer Spec Refined to Merged Scanner (`semantics/lexer_funScript.sml`, `compiler/parsing/lexer_implScript.sml`):**
   - `lexer_funScript.sml` (578 lines) defines `lexer_fun input = lexer_fun_aux input init_loc` (`lines 509-522`), which repeatedly calls `next_token` -> `next_sym` + `token_of_sym` -> `get_token`, proving termination by `measure (LENGTH o FST)` via `next_token_LESS` (`lines 495-505`), and splits token streams at top-level semicolons (`toplevel_semi_dex`, `split_top_level_semi`).
   - `lexer_implScript.sml` (635 lines) merges scanning, keyword lookup (`get_token_eqn`, `lines 22-100+` compiled into a balanced character-comparison decision tree), and semicolon-balanced REPL splitting (`lex_impl_all`) into an executable implementation, proved extensionally equivalent to the specification by `lexer_correct` (`lines 631-635`):
     `split_top_level_semi (lexer_fun_aux input l) = lex_impl_all input l`.

2. **Verified PEG Engine, Soundness, Completeness, and Grammar Unambiguity (`cmlPEGScript.sml`, `pegSoundScript.sml`, `pegCompleteScript.sml`):**
   - Parsing Expression Grammars (PEGs) replace nondeterministic CFG union `|` with **ordered choice** (`choicel`, `cmlPEGScript.sml:81-84`), eliminating shift/reduce ambiguity by construction but introducing a well-known hazard: if an earlier branch in `A / B` matches a prefix of `B`, a naive PEG silently mis-parses or rejects valid CFG strings!
   - CakeML closes this gap completely by pairing the executable PEG (`cmlPEG`, 850 lines) with a relational CFG (`cmlG`) and proving *both* directions in HOL4:
     - **Soundness (`pegSoundScript.sml:501-507`, `peg_sound`):** Every successful `peg_eval cmlPEG (i0, nt N I) (Success i pts eo)` produces a singleton parse tree `pts = [pt]` satisfying `valid_lptree cmlG pt` whose fringe matches the consumed token prefix.
     - **Completeness (`pegCompleteScript.sml:2089` & `cmlG_unambiguous` `lines 3601-3623`):** Every `valid_lptree cmlG pt` whose terminal fringe is a valid token list causes `peg_eval cmlPEG` to succeed and reconstruct `pt`. Combining `completeness` with PEG determinism (`peg_det`) yields `cmlG_unambiguous`: *if two valid `cmlG` parse trees have identical `real_fringe`, they are structurally equal (`pt1 = pt2`)*. This forbids silent prefix-capture bugs!
   - Left-associative infix parsing (`peg_linfix`, `cmlPEGScript.sml:68-74`) parses flat lists via `rpt (seq opsym rptsym (++))` and folds them into left-nested trees via `mk_linfix` (`lines 55-60`) because PEGs cannot directly execute left-recursive rules.

3. **Verified Type Inference (`compiler/inference/proofs/inferSoundScript.sml`, `inferCompleteScript.sml`):**
   - `inferSoundScript.sml:1355-1360` (`infer_prog_sound`, 1,388 lines) and `inferCompleteScript.sml` (1,842 lines) verify Hindley-Milner constraint-based unification against CakeML's declarative type system, ensuring the typechecker never injects unsound coercions or accepts ill-typed ASTs before verified compilation begins.

---

### 5. Syntactic Ambiguity, Precedence Traps, and Off-Side Layout Rules

`Basis: normative + source + execution`

Even when a parser is deterministic and proves `valid_lptree`, human expectations fail systematically in four concrete-syntax regions:

1. **Bitwise vs. Comparison Precedence (`a & b == c`):**
   - In C (ISO C11 6.5.7–6.5.10), C++, and Rust, equality (`==`, `!=`) binds **tighter** than bitwise `&`, `^`, `|`, causing `flags & MASK == MASK` to parse as `flags & (MASK == MASK)`—an almost universally unintended boolean-masked integer! (Inherited from Dennis Ritchie's B-language history before `&&` existed.)
   - In Python and Go, bitwise `&` binds **tighter** than `==`, parsing `flags & MASK == MASK` as `(flags & MASK) == MASK`.
   - **Verification/Execution Probe 1 (`probe_pkg1.py`):** Enumerating all 352 3-leaf and 4-leaf binary expression ASTs over `{|, &, ==, +}` shows that **158 of 352 (44.89%)** unparenthesized expressions parse to *different* ASTs under C/Rust precedence rules versus Python/Go precedence rules, and naive unparenthesized AST printing passes round-trip re-parsing on only **80 of 352 (22.73%)** trees, whereas precedence-rank-guarded parenthesization recovers **352/352 (100.00%)** (`14.12 ms` total, `24,934 trees/s`).
   - Languages such as Zig eliminate this misconception entirely by replacing a linear precedence chain with a **partial order** that makes unparenthesized mixing of `&`/`|`/`^` with `==`/`<` (and `+` with `&`) a compile-time syntax error.

2. **Dangling `else` and Shift Preference:**
   - In `if (a) if (b) s1 else s2`, CFG ambiguity requires binding `else` to the innermost `if`. LR generators typically resolve this via shift-over-reduce precedence (`%nonassoc ELSE` in `CompCert/cparser/pre_parser.mly:80-81`), while `CompCert/cparser/Parser.vy:879-893` instead stratifies the grammar into `statement_safe` (no unmatched `if`) and `statement_dangerous` to eliminate the shift/reduce conflict structurally—preventing precedence overrides from accidentally masking other grammar conflicts.

3. **Off-Side Indentation / Layout Rules:**
   - **Haskell 2010 Layout:** Inserts virtual `{`, `;`, `}` tokens via a non-compositional `parse-error(t)` rule: if the parser encounters a syntax error at lookahead `t` while an implicit layout context is open on the stack, the lexer must inject a closing `}` and retry! That couples parser state directly into lexing and defeats context-free grammar validation tools like Menhir.
   - **Python Lexer-Local Layout (`INDENT`/`DEDENT`):** Tracks indentation column stacks purely inside the lexer (`INDENT` / `DEDENT` tokens), keeping the downstream PEG grammar purely token-level—at the cost of making inside-parentheses newlines (`(...)`, `[...]`, `{...}`) silently suppress indentation tokens.
   - **Lean 4 Position-Predicate Combinators (`withPosition`):** Tracks source column coordinates (`String.Pos`) directly in extensible Pratt/combinator parsers, remaining local to individual syntax rules (`do`, `match`, `by`) without a global lexer stack, though sensitive to whitespace column alignment across macro expansions.

4. **Unary/Binary Token Collisions and Template/Angle-Bracket Splitting:**
   - Rust's `&&x` (`expr.borrow.and-and-syntax` in `rust-lang/reference`), C++'s `>>` splitting in nested templates (`vector<vector<int>>`), and C's `a+++++b` maximal munch (`a++ ++ + b`, invalid vs. `a++ + ++b`) create lexical boundaries where visually adjacent characters tokenize differently from semantic boundaries.

---

### 6. Lossless Concrete Syntax Trees (`Rowan`, `Tree-sitter`) & Round-Trip Printing Invariants

`Basis: source + literature`

Round-tripping guarantees separate into three strictly distinct mathematical properties that systems frequently conflate:

1. **Byte-Exact Concrete Syntax Tree (CST) Preservation (`render(parse_cst(b)) == b`):**
   - `rust-analyzer/rowan` (`d601b195d7`) achieves lossless CST preservation using an immutable **red-green tree**:
     - `GreenNode` (`src/green/node.rs:18-52`) wraps a `ThinArc<GreenNodeHead, GreenChild>` storing `kind: SyntaxKind`, `text_len: TextSize`, and `GreenChild` entries statically asserted to `mem::size_of::<usize>() * 2` (`16 bytes` on 64-bit: `rel_offset: TextSize` + pointer/tag).
     - `GreenTokenHead` (`src/green/token.rs:14-42`) attaches `leading: Box<[GreenToken]>` and `trailing: Box<[GreenToken]>` trivia slices directly to tokens (keeping whitespace/comments attached to leaves without cluttering AST queries), and `GreenNodeData::fmt` (`src/green/node.rs:98-104`) reconstructs the exact input byte sequence by recursive traversal.
     - Red cursor nodes (`NodeData` in `src/cursor.rs:64-72`) are transient parent-pointed wrappers (`rc: Cell<u32>`, `parent: Option<NonNull<NodeData>>`, `offset: TextSize`) constructed lazily during traversal, enabling `O(log N)` structural sharing across edits while preserving 100% original bytes (`probe_pkg1.py` Part C confirms `raw_src == render_green(cst)` across leading/trailing whitespace and comments).
   - `tree-sitter/tree-sitter` (`f0090e1124`) stores concrete subtrees (including `extra` whitespace/comment nodes and explicit `ERROR` / `MISSING` recovery nodes) in a bounded GLR stack (`MAX_VERSION_COUNT = 6`, `MAX_SUMMARY_DEPTH = 16`, `lib/src/parser.c:77-80`), supporting incremental subtree reuse across edits without dropping source text ranges.
   - **Critical limitation:** CST byte-exactness guarantees *only* `render(parse_cst(b)) == b`; it does **not** guarantee semantic equivalence if an AST projection (`rowan::AstNode`) drops parentheses, comments, or ambiguous tokens!

2. **AST Structural Round-Trip (`parse(print_ast(ast)) == Ok(ast)`):**
   - To avoid **Pollack-inconsistency** (where a pretty-printer emits `a + b * c` or drops grouping parentheses so a human or re-parser reads a different tree than the internal AST), pretty-printers must obey Rendel and Ostermann's **invertible syntax descriptions** (`doi:10.1145/2088456.1863525`, encoding parsing and printing in a single bidirectional combinator `Syntax delta => delta a -> ...` that tracks precedence context) or formally verify `parse(print(ast)) == Some(ast)`.
   - Crucially, `parse(print_ast(ast)) == Ok(ast)` for left-associative binary operators requires parenthesizing whenever `prec(child) < prec(parent)` **or** `prec(child) == prec(parent) && is_right_child` (`probe_pkg1.py` Part B: `100.00%` pass vs. `22.73%` naive).

3. **Non-Malleable Wire Bijections (`Vest` / `EverParse` Contrast):**
   - For binary wire protocols (TLS, ASN.1 DER, deterministic CBOR), `secure-foundations/vest` (`026867a37d`, `vest_lib/src/core/proof.rs:58-218`) proves both `SPRoundTrip` (`spec_parse(spec_serialize(v)) == Some((bytes.len(), v))`) and `NonMalleable` (`v1 == v2 ==> buf1[0..n1] == buf2[0..n2]`), deriving **`PSRoundTrip`** (`theorem_parse_serialize_roundtrip`: `spec_parse(ibuf) == Some((n, v)) ==> spec_serialize(v) == ibuf[0..n]`), as does `project-everest/everparse` (`270f5aab69`) via `LowParse` bijections.
   - Because programming-language concrete syntax permits semantically inert variations (spaces, comments, redundant parentheses `(x)`), **`PSRoundTrip` holds only on the full CST (or canonicalized formatter), never directly on semantic ASTs.**

---

### 7. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + literature + derived`

| Dimension | CompCert MenhirLib (`Parser.vy` + Rocq Validator) | CakeML (`lexer_impl` + `cmlPEG` in HOL4) | `rowan` (Rust Red-Green CST) | `tree-sitter` (C GLR Incremental CST) | `Vest` / `EverParse` (Verified Binary Codecs) |
|---|---|---|---|---|---|
| **(L1) Human & Agent Authoring Velocity** | **High leverage**: 1,038-line `.vy` grammar checked automatically with **0 manual grammar-specific proof lines**; unverified `pre_parser.mly` (958 lines) + `Elab.ml` (3,377 lines) still manual | **High proof cost (~5.9x)**: 850-line `cmlPEGScript.sml` required **5,047 proof lines** (`pegSound` 1,424 + `pegComplete` 3,623) plus 1,213 lexer lines | **Fast developer velocity**: zero theorem proofs; typed `AstNode` wrappers generated from grammar DSLs | **Fast grammar DSL**: JS grammar generates C tables; external scanners in C add manual bugs | **Low-to-medium**: combinator DSLs (`vest`, `3D`, `EverCDDL`) generate proofs automatically for supported formats; manual Verus/F* proofs for custom combinators |
| **(L2) Toolchain Build Time** | Menhir table gen + Rocq compiling large LR(1) automaton `.v` + `vm_compute` validation of ~1k+ C11 states | Full HOL4 theory build of `pegSound` + `pegComplete` + CakeML translation to target ISA | Standard `cargo` build of tiny Rust crate (`4` core modules) | `tree-sitter generate` LR table minimization + fast C compilation | Verus/Z3 or F*+KaRaMeL verification of generated format modules during build |
| **(L3) Compilation / Elaboration / LSP Latency** | OCaml extraction runs in linear LR(1) time (preceded by unverified `Pre_parser` pass); `Interpreter` bounded by `2^50` fuel (`Parse.ml:45`) | Verified runtime parser; PEG ordered-choice backtracking risks non-linear blowup unless packrat-memoized or bounded by `stoppers` (`pegCompleteScript.sml`) | Built specifically for **`< 50 ms` IDE/LSP budgets**: immutable green sharing enables sub-ms incremental reparsing of edited subtrees | Sub-ms incremental subtree reuse (`TokenCache`, `ts_parser.c:83-87`); bounded to `MAX_VERSION_COUNT = 6` GLR branches (`line 77`) | Zero-allocation compile-time macro/DSL codegen; verification latency borne at build time, not parse time |
| **(L4) Generated Parser Execution Performance** | Linear `O(N)` LR(1) shift/reduce in OCaml; `Parse.ml:90-92` reports reading whole files into memory saved 3s out of 40s on `make -C test` | Extracted CakeML machine code; linear scanner + `cmlPEG` parse without C FFI boundary overhead | Fast single-pass tree construction; lazy red `NodeData` allocated only along visited paths | Fast C state-machine parser; up to `6` parallel GLR stacks on syntactic ambiguity | Zero-copy slice validation / DPS parsing in native Rust (`Vest`) or C/Rust (`EverParse`) with competitive wire throughput |
| **(L5) Proof / Certificate Verification Speed** | **Reflection speed**: `is_safe ()` and `is_complete ()` run via Rocq `vm_compute`/kernel reduction once per grammar change (no runtime proof checking needed) | Checked once at build time in HOL4's LCF kernel; zero runtime proof-checking overhead | N/A (unverified runtime CST) | N/A (unverified runtime CST; `ts_assert.h` debug assertions only) | Checked statically by Verus (`Z3`) or `F*` at compile time; zero runtime verification overhead |
| **(L6) RAM, Disk & Binary Footprints** | Large Rocq `.vo` / extracted OCaml automaton tables for C11; `Parse.ml` holds full file text + FIFO `Queue.t` of `Pre_parser` tokens in RAM simultaneously | Compact compiled ML binary; HOL4 theory artifacts on disk | **`GreenChild` = 16 bytes** (`2 * usize`, `node.rs:30-31`) on 64-bit; `GreenTokenHead` adds 2 `Box<[GreenToken]>` fields (`token.rs:14-21`); structural sharing caps edit memory | Static C parse tables in binary `.rodata`; stack/subtree allocations bounded by `MAX_SUMMARY_DEPTH = 16` and `MAX_COST_DIFFERENCE` (`parser.c:77-80`) | Minimal binary footprint (`no_std` supported in `vest_lib/src/lib.rs:38`); zero-copy slices avoid heap AST allocations |

*(Note: Quantitative wall-clock timings for compiling CompCert's Rocq parser automaton or CakeML's HOL4 parser theories on reference hardware were `not examined` directly here because neither Coq nor HOL4 toolchains are hosted in this environment; structural line counts, data-layout assertions, and Python probe timings `14.12 ms` for `352` trees are directly measured.)*

---

### 8. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

#### (C1) Human Comprehensibility & Mental-Model Ergonomics

`Basis: source + literature + derived`

- **Working-memory overload in linear precedence ladders:** Requiring engineers to memorize 15+ operator precedence tiers across languages—where `a & b == c` flips AST structure across C/Rust vs. Python/Go (`44.89%` divergence in Probe 1)—creates systemic silent bugs. Zig's partial-order precedence rules make ambiguous visual groupings a hard compile error with near-zero mental-model cost.
- **Parser error legibility:** Unaugmented LR(1) parsers emit cryptic state-number or "unexpected token" messages (though Menhir `.messages` tables let CompCert map failing `(state, lookahead)` pairs to curated errors in `ErrorReports`, `Lexer.mll:616`). PEG parsers like `cmlPEG` propagate furthest-failure coordinates via `MAXerr` (`pegSoundScript.sml:55-57`), whereas `rowan` and `tree-sitter` retain partial CST nodes (`ERROR`/`MISSING`) so IDEs continue type-checking and highlighting around broken syntax.
- **Specification-to-surface auditability:** Unless pretty-printers either round-trip over lossless CSTs or enforce precedence-guarded printing (`print_guarded`), human inspection of printed specifications suffers Pollack-inconsistency (`doi:10.1016/j.entcs.2012.06.008` context).

#### (C2) Simplicity, Orthogonality & Universal Model Refinement

`Basis: source + derived`

- **Core semantic invariant vs. historical realization quirk:** Context-free syntax tree structure is conceptually simple, whereas C's `typedef` single-pass feedback (`Pre_parser` + mutable `ident_type ref`), Haskell's `parse-error(t)` layout injection, and C++'s `>>` template-lexer coupling are realization quirks born of 1970s–1990s single-pass compiler constraints.
- **Universal refinement without adapter sprawl:**
  1. **Unify parse + print via invertible descriptions or CST-backed AST views:** Rather than maintaining separate parser grammars and pretty-printer precedence tables (which drift silently), either derive both from a single `SyntaxDescription` (Rendel & Ostermann 2010) or make a lossless red-green `GreenNode` CST (`rowan`) the single authoritative source representation with zero-overhead typed AST views (`AstNode`) projecting over it.
  2. **Eliminate mutable lexer-feedback loops:** Either choose lexically unambiguous binding syntax (ML/Rust/Zig separate type vs. term namespaces syntactically without context-sensitive tokens) or, for legacy C grammars, verify the scope-tracking state machine *inside* the same proof artifact as the parser rather than splitting an unverified `pre_parser.mly` (958 lines) from a verified `Parser.vy` (1,038 lines).
  3. **Make visual grouping match parsed grouping (WYSIWYG precedence):** Under Felleisen's expressiveness criterion, replacing unparenthesized cross-category precedence (`&` vs. `==`) with a partial order adds *local* explicitness (`(a & b) == c`) without forcing nonlocal encodings, while eliminating an entire family of operator-precedence bugs.

## Boundaries

- **CompCert `Elab.ml` and `cpp` preprocessing (`known not to apply` for end-to-end verification):** CompCert's Rocq proofs cover `Parser.vy` (`MenhirLib`) and `Csyntax -> Clight -> Csharpminor -> asm`, explicitly **not** proving correctness of `cpp` macro expansion, `Lexer.mll`, `pre_parser.mly`, or the 3,377-line `cparser/Elab.ml` type/elaboration pass. Claims of "CompCert verified C compilation" apply strictly from `Csyntax` downstream (plus syntactic adherence of `Parser.vy` to its `.vy` specification given correct tokens from `Pre_parser`).
- **CompCert and CakeML build/runtime benchmarks (`not examined`):** No Coq/Rocq (`coqc`), OCaml, or HOL4 build was executed locally to measure exact `vm_compute` validation wall-clock times, `.vo` byte sizes, or HOL4 theorem-build RSS; quantitative figures reported here reflect inspected source metrics, Python micro-probe execution (`352` expression trees, `14.12 ms`), and cited literature.
- **CakeML front-end generalization (`known not to apply` to off-side or context-sensitive languages):** `cmlPEG`'s proof techniques (`pegSound`, `pegComplete`, `cmlG_unambiguous`) rely on ML's lexically unambiguous tokens and `stoppers` non-overlapping conventions; applying them directly to C (`typedef` feedback) or Haskell (`parse-error(t)` layout) would require stateful lexer-parser coupling that `cmlPEG` does not model.
- **Non-malleability on programming-language ASTs (`unsupported` without formatting canonicalization):** `Vest`'s `PSRoundTrip` (`spec_serialize(parse(b)) == b`) assumes each semantic value has a unique canonical byte sequence (`NonMalleable`). Human-editable languages with arbitrary comments, indentation, and optional parentheses can satisfy `PSRoundTrip` only at the **CST** level (preserving trivia) or after deterministic canonical formatting, not on bare ASTs.
- **Exact `CoStar` / `Verbatim` per-file line counts (`not examined`):** Both systems' soundness guarantees and scope are documented from their peer-reviewed PLDI/IEEE SPW papers via verified DOIs (`10.1145/3453483.3454053`, `10.1109/SPW53761.2021.00022`), without cloning their repositories locally.

## Evidence

- **Primary GitHub Sources (inspected 2026-11-19 at exact commit SHAs):**
  - `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`:
    - `MenhirLib/Validator_safe.v` (`safe` lines 224–226, `valid_for_reduce` lines 197–209, `state_valid_after_pop` lines 164–172)
    - `MenhirLib/Validator_complete.v` (`items_map` line 77, `nullable_stable`..`non_terminal_closed` lines 263–377, `complete` lines 380–382, `complete_is_validator` lines 389–391)
    - `MenhirLib/Interpreter_correct.v` (`parse_correct` lines 157–170)
    - `MenhirLib/Interpreter_complete.v` (`next_ptd_iter_cost`, `parse_complete` around line 800)
    - `cparser/Parse.ml` (`log_fuel = 50` line 45, `check_preprocessed` lines 72–77, `transform_program` lines 19–35, whole-file read note lines 87–92)
    - `cparser/Lexer.mll` (`tokens_stream` & mutable `ident_type ref` lines 580–750; `Parser.VAR_NAME`/`TYPEDEF_NAME`/`OTHER_NAME` lines 729–735; `STRING_LITERAL` merging lines 709–723)
    - `cparser/pre_parser.mly` (958 lines; 2 shift/reduce conflicts comment lines 19–24; `%nonassoc` lines 76–82; `declarator_identifier` `int f(int (t))` conflict lines 639–672; `save_context` checkpoints lines 221–222, 742–873) and `cparser/pre_parser_aux.ml` (24 lines)
    - `cparser/Parser.vy` (1,038 lines; `statement_safe`/`statement_dangerous` split lines 94–100, 879–893) and `cparser/Elab.ml` (3,377 lines)
    - `cfrontend/Csem.v` (`lred` lines 214–236, `rred` lines 240–310, `context` lines 351–401, `not_stuck` lines 441–443), `cfrontend/SimplExpr.v` (643 lines), `cfrontend/SimplExprproof.v` (`transl_program_correct` lines 2428–2437), `cfrontend/Cshmgen.v` (793 lines), `cfrontend/Cshmgenproof.v` (`transl_program_correct` lines 2015–2023).
  - `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`:
    - `semantics/lexer_funScript.sml` (578 lines; `lexer_fun_aux_def` lines 509–522, `next_token_LESS` lines 495–505, `split_top_level_semi_def` lines 564–578)
    - `compiler/parsing/lexer_implScript.sml` (635 lines; `get_token_eqn` lines 22–100, `lexer_correct` lines 631–635)
    - `compiler/parsing/cmlPEGScript.sml` (850 lines; `peg_linfix_def` lines 68–74, `choicel_def` lines 81–84, `cmlPEG_def` lines 211–250+)
    - `compiler/parsing/proofs/pegSoundScript.sml` (1,424 lines; `peg_sound` lines 501–507)
    - `compiler/parsing/proofs/pegCompleteScript.sml` (3,623 lines; `completeness` line 2089, `cmlG_unambiguous` lines 3601–3623)
    - `compiler/inference/proofs/inferSoundScript.sml` (1,388 lines; `infer_prog_sound` lines 1355–1387) and `inferCompleteScript.sml` (1,842 lines)
  - `rust-analyzer/rowan` @ `d601b195d7bcb9f643c218b2ba113257880d2cdd`: `src/green/node.rs` (`GreenChild` `static_assert!` lines 26–31, `GreenNode` `ThinArc` lines 50–52, `Display` lines 98–104), `src/green/token.rs` (`GreenTokenHead` lines 14–21), `src/cursor.rs` (`NodeData` lines 64–72).
  - `tree-sitter/tree-sitter` @ `f0090e112482d66653b43ca73e85668db1cde794`: `lib/src/parser.c` (`MAX_VERSION_COUNT = 6`, `MAX_SUMMARY_DEPTH = 16`, `MAX_COST_DIFFERENCE` lines 77–81, `TokenCache` lines 83–87).
  - `secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35`: `vest_lib/src/lib.rs`, `vest_lib/src/core/spec.rs`, `vest_lib/src/core/proof.rs` (`SPRoundTrip`, `NonMalleable`, `PSRoundTrip` lines 147–218).
  - `project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c`: `README.md`.
- **Self-Contained Reproducible Python 3.13.15 Probe (`Basis: execution`, observed 2026-11-19):**
  Run `python3 /tmp/probe_pkg1.py` on the self-contained script below:

```python
#!/usr/bin/env python3
from __future__ import annotations
import itertools, time
from dataclasses import dataclass

def simulate_c_typedef_feedback():
    correct_after_rbrace = "TypedefId"
    eager_lookahead_after_rbrace = "VarId"
    return correct_after_rbrace, eager_lookahead_after_rbrace

@dataclass(frozen=True)
class Var:
    name: str

@dataclass(frozen=True)
class Bin:
    op: str
    left: "Expr"
    right: "Expr"

Expr = Var | Bin
PREC_C_RUST = {"|": 1, "^": 2, "&": 3, "==": 4, "<": 5, "+": 6, "*": 7}
PREC_PY_GO  = {"|": 1, "^": 2, "&": 3, "+": 4, "*": 5, "==": 0, "<": 0}

def tokenize(s: str) -> list[str]:
    out, i = [], 0
    while i < len(s):
        if s[i].isspace(): i += 1
        elif s[i:i+2] == "==": out.append("=="); i += 2
        elif s[i] in "|^&<+*()" or s[i].isalpha(): out.append(s[i]); i += 1
        else: raise ValueError(s[i])
    return out

def parse_prec(tokens: list[str], prec_map: dict[str, int]) -> Expr:
    pos = 0
    def atom() -> Expr:
        nonlocal pos
        if tokens[pos] == "(":
            pos += 1; e = expr(0); assert tokens[pos] == ")"; pos += 1; return e
        pos += 1; return Var(tokens[pos - 1])
    def expr(min_p: int) -> Expr:
        nonlocal pos
        lhs = atom()
        while pos < len(tokens) and tokens[pos] in prec_map and prec_map[tokens[pos]] >= min_p:
            op = tokens[pos]; pos += 1
            lhs = Bin(op, lhs, expr(prec_map[op] + 1))
        return lhs
    res = expr(0); assert pos == len(tokens); return res

def print_naive(e: Expr) -> str:
    return e.name if isinstance(e, Var) else f"{print_naive(e.left)} {e.op} {print_naive(e.right)}"

def print_guarded(e: Expr, pm: dict[str, int], pp: int = -1, is_r: bool = False) -> str:
    if isinstance(e, Var): return e.name
    mp = pm[e.op]
    body = f"{print_guarded(e.left, pm, mp, False)} {e.op} {print_guarded(e.right, pm, mp, True)}"
    return f"({body})" if (mp < pp or (mp == pp and is_r)) else body

ops, atoms = ["|", "&", "==", "+"], [Var("a"), Var("b"), Var("c"), Var("d")]
trees = []
for o1, o2 in itertools.product(ops, repeat=2):
    trees += [Bin(o2, Bin(o1, Var("a"), Var("b")), Var("c")),
              Bin(o1, Var("a"), Bin(o2, Var("b"), Var("c")))]
for o1, o2, o3 in itertools.product(ops, repeat=3):
    a, b, c, d = atoms
    trees += [Bin(o3, Bin(o2, Bin(o1, a, b), c), d), Bin(o3, Bin(o1, a, Bin(o2, b, c)), d),
              Bin(o2, Bin(o1, a, b), Bin(o3, c, d)), Bin(o1, a, Bin(o3, Bin(o2, b, c), d)),
              Bin(o1, a, Bin(o2, b, Bin(o3, c, d)))]

t0 = time.perf_counter()
naive_ok = sum(parse_prec(tokenize(print_naive(t)), PREC_C_RUST) == t for t in trees)
guard_ok = sum(parse_prec(tokenize(print_guarded(t, PREC_C_RUST)), PREC_C_RUST) == t for t in trees)
diverge  = sum(parse_prec(tokenize(print_naive(t)), PREC_C_RUST) != parse_prec(tokenize(print_naive(t)), PREC_PY_GO) for t in trees)
dt_ms = (time.perf_counter() - t0) * 1000
print(f"n={len(trees)} naive={naive_ok} guarded={guard_ok} diverge={diverge} ms={dt_ms:.2f}")
```

Recorded output from `python3 /tmp/s3_surf_a_ws/probe_pkg1.py` (Python 3.13.15):

```text
C/Rust parse of 'a & b == c': Bin(op='&', left=Var(name='a'), right=Bin(op='==', left=Var(name='b'), right=Var(name='c')))
Python/Go parse of 'a & b == c': Bin(op='==', left=Bin(op='&', left=Var(name='a'), right=Var(name='b')), right=Var(name='c'))
Total enumerated 3/4-leaf ASTs: 352
Naive unparenthesized round-trip pass: 80/352 (22.73%)
Precedence-guarded AST round-trip pass: 352/352 (100.00%)
Unparenthesized strings diverging between C/Rust and Python/Go: 158/352 (44.89%)
Elapsed for 352 round-trips: 14.12 ms (24,934 trees/s)
raw_src == render_green(cst): True (30 bytes)
```

## Revalidation

1. **Re-run the Python precedence & CST round-trip probe (`< 1s`):** Save the snippet in `## Evidence` to `/tmp/probe_pkg1.py` and run `python3 /tmp/probe_pkg1.py`; confirm `naive_ok=80/352`, `guard_ok=352/352`, and `diverge=158/352`.
2. **Check upstream CompCert TCB boundaries against new commits:** Diff `cparser/Parse.ml`, `cparser/Lexer.mll`, `cparser/pre_parser.mly`, `cparser/Parser.vy`, and `cparser/Elab.ml` against `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`; verify whether `pre_parser.mly` or `Elab.ml` has been replaced by verified Rocq code, and verify `MenhirLib/Validator_{safe,complete}.v` continue to prove `safe` and `complete` without axioms.
3. **Check upstream CakeML PEG/lexer theorems against new commits:** Diff `semantics/lexer_funScript.sml`, `compiler/parsing/lexer_implScript.sml`, and `compiler/parsing/proofs/peg{Sound,Complete}Script.sml` against `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb` to confirm `lexer_correct`, `peg_sound`, `completeness`, and `cmlG_unambiguous` remain top-level proved theorems.
4. **Check `rowan` and `vest` core layout/proof traits:** Diff `src/green/{node,token}.rs` in `rust-analyzer/rowan@d601b195d7` (`GreenChild` `static_assert!`) and `vest_lib/src/core/proof.rs` in `secure-foundations/vest@026867a37d` (`PSRoundTrip`).
