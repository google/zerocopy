# Bidirectional Lenses, Hygienic Resugaring, and Verified Non-Malleable Format Compilers

## Summary

Bidirectional programming, hygienic compiler resugaring, and verified binary format compilation are three projections of one algebraic problem: **maintaining exact semantic correspondence across forward projections and backward reconstructions without losing hidden structure or admitting representation differentials**.

Key invariants and architectural distinctions established from primary specifications, source trees, and executable witnesses:

1. **Lens law trilemma and complement conservation.** For an asymmetric state-based lens $(\text{get} : S \to V,\; \text{put} : V \times S \to S)$, whenever $\text{get}$ is non-injective (discarding comments, layout, filtered records, or metadata), strict well-behavedness (`GetPut` + `PutGet`) composes cleanly, but history-independence (`PutPut`) routinely fails on deletion-then-reinsertion sequences because deleted complement data cannot be reconstructed from states alone. Preserving per-element provenance requires explicit **matching/alignment** (`Boomerang`), **complement state** (`Symmetric` / `Edit` lenses), or **provenance links** (`Retentive` lenses).
2. **Symmetric-lens complements vs. zero-complement wire codecs.** Synchronizing two mutually partial representations $X \leftrightarrow Y$ irreducibly requires a stateful complement $C$ storing the symmetric difference $(X \setminus Y) \oplus (Y \setminus X)$. By contrast, cryptographic and security-critical wire formats must collapse $C$ to a unit type ($C \cong 1$) on the accepted domain: **non-malleability** requires `parse` to be injective on consumed byte prefixes, turning `(parse, serialize)` into a partial bijection (`PSRoundTrip` + `SPRoundTrip`).
3. **Strong prefix (`NoLookAhead`) is mandatory for compositional format verification.** In both EverParse's `LowParse` (`ParserStrong` / `no_lookahead`) and `Vest` (`NoLookAhead` / `SPRoundTripDps`), individual non-malleability does not compose across sequential concatenation (`Pair(P1, P2)`) unless `P1` satisfies prefix-extension invariance (`parse(b1) = Some(n, v) ==> parse(b1 ++ b2) = Some(n, v)`).
4. **Non-malleability separates verified format compilers sharply.** `EverParse`/`LowParse` (`F*`/`Pulse`), `ASN1*` (inside `project-everest/everparse`), and `Vest` (`Verus`/Rust, redesigned in `v0.2` / Vest 2.0 with `Prepare` + infallible `serialize` + `vest_asn1` + `cbor`) machine-check non-malleability (`parse_injective` / `NonMalleable`) and prefix-freedom (`ParserStrong` / `NoLookAhead`). By contrast, `Narcissus` (`mit-plv/fiat`) specifies formats as non-deterministic `Comp` relations—proving round-trip soundness (`CorrectDecoder`) without ruling out multiple valid wire encodings for one semantic value—and mainstream schema tools (`Protocol Buffers`, `Kaitai Struct`) explicitly disclaim canonical wire representation.
5. **Hygienic resugaring vs. optimizing lowerings.** Pombrio and Krishnamurthi's provenance-carrying desugaring lifts core evaluation steps (PLDI 2014, ICFP 2015), scope rules (ICFP 2017), and surface type rules (PLDI 2018) through compositional syntactic sugar under **Emulation** and **Abstraction**, with Zhu et al.'s Retentive Lenses (`arXiv:2001.02031`) formalizing resugaring as a provenance-retaining lens. However, local syntactic DAG provenance breaks across whole-function optimizing passes (CSE, loop fusion, CPS/`async` state-machine splitting) and opaque Turing-complete procedural macros.

## Applicability

This report synthesizes and compares four groups of durable upstream subjects pinned in `REPORT.json`:

1. **Bidirectional lens theory and implementations:** Foundational papers on asymmetric tree lenses (Foster et al., TOPLAS 2007), dictionary/quotient/matching string lenses (`boomerang-lang/boomerang` @ `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`; Bohannon et al., POPL 2008; Foster et al., ICFP 2008; Barbosa et al., ICFP 2010), symmetric and edit lenses (Hofmann, Pierce, Wagner, POPL 2011 / POPL 2012), retentive lenses (Zhu et al., `arXiv:2001.02031`), putback-based programming (`BiGUL`, PEPM 2016), higher-order uncombinator lenses (`HOBiT`, ESOP 2018), lens synthesis (`Optician-Tool/Optician-Tool` @ `4aa9d9d0f0511bf559abdc73dbef3b888d371d3a`; POPL 2018), and invertible syntax descriptions (Rendel & Ostermann, Haskell 2010).
2. **Hygienic compiler resugaring:** Pombrio & Krishnamurthi's four-paper sequence spanning evaluation-trace resugaring (PLDI 2014), hygienic compositional DAG resugaring (ICFP 2015), scope inference through sugar (ICFP 2017), and type-rule inference through sugar (PLDI 2018).
3. **Verified non-malleable binary format compilers:**
   - **EverParse / LowParse / 3D / ASN1\* / EverCBOR / EverCDDL** (`project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c`; USENIX Security 2019, PLDI 2022, CPP 2023). Note that `LowParse` lives under `lib/everparse/lowparse/` and `ASN1*` lives under `lib/everparse/asn1/{spec,pulse}` + `src/ASN1/tool` in this revision, alongside `Pulse`-based `EverCBOR`/`EverCDDL`/`EverCOSign` C and Rust extraction.
   - **Vest** (`secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35`; USENIX Security 2025). This report distinguishes **Vest 1.0** (the USENIX Security 2025 design with separate `parse_X`/`X_len`/`serialize_X` functions) from **Vest 2.0 (`v0.2.0`)** at the pinned revision, which introduces a three-layer `vest_lib::core::{spec,exec,proof}` trait hierarchy, `Prepare` + infallible `serialize`, `vest_asn1` (DER/BER), and `cbor`.
   - **Narcissus** (`mit-plv/fiat` @ `77f43f5d5408b3543f8dd01d4d43f4c4c70f1213`, `src/Narcissus/Common/Specs.v`; ICFP 2019).
4. **LangSec and comparative unverified/non-canonical format ecosystems:** LangSec foundations (Sassaman et al., IEEE Systems J. 2013; Momot et al., IEEE SPW 2016), `GaloisInc/daedalus` (`8ff2fadc981800c0457406d44fa55f8d270dfc71`), `jbangert/nail` (`4bd9cc29c4092abe7a77f8294aff2337bba02ec5`; OSDI 2014), `kaitai-io/kaitai_struct` (`4fb24924d21317dfba9209c47c892770d2834d7a`), and `protocolbuffers/protobuf` (`158df6107b2469fc3d2d66e11e5ada76efddfaa4`, `src/google/protobuf/io/coded_stream.h`).

Findings on `Vest`, `LowParse`, `Narcissus`, `Boomerang`, and `Protocol Buffers` apply directly to the pinned revisions; architectural laws (`GetPut`/`PutGet`/`PutPut`, `NoLookAhead` sequential composition, ASN.1 DER vs. BER canonicality) apply generally to any codec or bidirectional transformation obeying the stated mathematical signatures.

## Findings

### 1. Bidirectional Lens Taxonomy, Algebraic Laws, and Complement Conservation

Basis: normative + source + execution + derived

#### 1.1 Asymmetric State-Based Lenses and the Law Trilemma

Following Foster et al. (TOPLAS 2007, DOI `10.1145/1232420.1232424`), an **asymmetric state-based lens** $l : S \Leftrightarrow V$ between concrete source set $S$ and abstract view set $V$ consists of three functions:

$$\text{get} : S \to V, \qquad \text{put} : V \times S \to S, \qquad \text{create} : V \to S$$

subject to the canonical round-trip laws (with `CreateGet`: $\text{get}(\text{create}(v)) = v$):

- **GetPut (Acceptability / Hippocraticness):** $\forall s \in S.\; \text{put}(\text{get}(s), s) = s$. An unchanged view leaves hidden source information untouched.
- **PutGet (Consistency / Correctness):** $\forall v \in V, s \in S.\; \text{get}(\text{put}(v, s)) = v$. Every view edit is reflected faithfully in the updated source.
- **PutPut (History-Independence / Very Well-Behavedness):** $\forall v, v' \in V, s \in S.\; \text{put}(v', \text{put}(v, s)) = \text{put}(v', s)$. Two sequential puts equal the second put alone.

A lens satisfying `GetPut` and `PutGet` is **well-behaved**; adding `PutPut` makes it **very well-behaved**. Composition of lenses $l_1 : A \Leftrightarrow B$ and $l_2 : B \Leftrightarrow C$ defined by $\text{get}_{1;2}(a) = \text{get}_2(\text{get}_1(a))$ and $\text{put}_{1;2}(c, a) = \text{put}_1(\text{put}_2(c, \text{get}_1(a)), a)$ preserves both well-behavedness and very well-behavedness.

**Why `PutPut` fails in practice (derived + execution):** Whenever $\text{get} : S \to V$ is non-injective—for example, filtering a keyed record list while hiding per-entry comments—`GetPut` and `PutGet` hold, yet deleting a key in view edit $v_1$ discards its complement comment in $s_1 = \text{put}(v_1, s_0)$, so re-inserting that key in $v_2$ synthesizes a default comment rather than recovering $s_0$'s comment: $\text{put}(v_2, \text{put}(v_1, s_0)) \neq \text{put}(v_2, s_0)$. Probe 1 in **Evidence** witnesses this exact separation (`GetPut = True`, `PutGet = True`, `PutPut = False`) on concrete keyed records.

#### 1.2 Quotient, Matching, Symmetric, Edit, Retentive, and Dependent Lenses

Practical synchronization domains repeatedly violate the assumptions of plain asymmetric state-based lenses (total equality, positional correspondence, strict source subsumption, stateless updates, or non-dependent schemas). Six formal generalizations address distinct structural limits:

| Lens Family | Primary Reference / Source | Signature & Extra Structure | Relaxed / Added Laws | Core Failure Mode / Cost |
|---|---|---|---|---|
| **Asymmetric State Lens** | Foster et al. (TOPLAS 2007, `10.1145/1232420.1232424`) | $\text{get}: S \to V$, $\text{put}: V \times S \to S$ | `GetPut`, `PutGet`, optional `PutPut` | `PutPut` fails under lossy filtering/deletions; positional misalignment on list edits; assumes $S$ subsumes $V$. |
| **Quotient Lens** | Foster, Pilkiewicz, Pierce (ICFP 2008, `10.1145/1411203.1411257`) | Equivalence relations $\sim_S, \sim_V$ | `GetPut`/`PutGet` hold up to $\sim_S, \sim_V$ ($s' \sim_S s$, $v' \sim_V v$) | Quotienting whitespace/order breaks byte-exact cryptographic signing/hashing; unsafe on authenticated wire formats. |
| **Matching / Dictionary Lens** | Bohannon et al. (POPL 2008, `10.1145/1328897.1328487`); Barbosa et al. (ICFP 2010, `10.1145/1863543.1863572`); `boomerang-lang/boomerang` | Chunk alignment (`Balign.Alignment`, `Balign.Permutation`), `mtype` keyed containers, explicit `complement` ADT | Alignment-aware `GetPut`/`PutGet` preserving complements across reorder/insert | Regular string lenses require unambiguous regex checking (EXPTIME DFA/NFA checks); cannot express arbitrary context-free nesting. |
| **Symmetric Lens** | Hofmann, Pierce, Wagner (POPL 2011, `10.1145/1926385.1926428`) | Explicit complement $C$, `missing` $c_0 \in C$, $\text{putr}: X \times C \to Y \times C$, $\text{putl}: Y \times C \to X \times C$ | `PutRL`, `PutLR` (equivalent to a span of two asymmetric lenses $X \Leftarrow S \Rightarrow Y$) | Chaining $k$ lenses multiplies complement state $C_1 \times \dots \times C_k$; requires complement lifecycle/GC management across boundaries. |
| **Edit / Delta Lens** | Hofmann, Pierce, Wagner (POPL 2012, `10.1145/2103656.2103715`) | Monoids of edits $\partial X, \partial Y$ acting on $X, Y$; $\text{dputr}: \partial X \times C \to \partial Y \times C$ | Identity & composition preservation over edit monoids | Concurrent edits on both sides require CRDT/OT conflict resolution; edit scripts must be captured at the authoring tool. |
| **Retentive Lens** | Zhu, Yang, Ko, Hu (`arXiv:2001.02031`) | Provenance link sets $l \subseteq \text{Regions}(S) \times \text{Regions}(V)$; $\text{get}: S \to (V, L)$, $\text{put}: S \times V \times L \to S$ | **Retentiveness:** every unchanged linked view region preserves its corresponding source region | Requires maintaining region-level link maps across view transformations; tree-DSL restricted to structural linkable patterns. |
| **Dependent Lens ($\mathbf{Poly}$)** | Spivak / Myers; Clarke et al. profunctor optics | Forward $f: I \to J$; backward fiber $f^\sharp_i : B_{f(i)} \to A_i$ depending on state $i \in I$ | Indexed `GetPut`/`PutGet` over state-dependent fiber | Standard higher-kinded profunctor optics in non-dependent host languages cannot express tag-dependent payload updates without type-inference collapse. |

#### 1.3 Direct Source Inspection: Boomerang Complement & Alignment Machinery

Basis: source (`boomerang-lang/boomerang` @ `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`, `lib/blenses.ml:28-159`)

Inspection of `lib/blenses.ml` shows that Boomerang materializes structural complements directly as an algebraic data type (`lines 50-59`):

```ocaml
type union_side = Union_left | Union_right
type complement =
  | C_box
  | C_string of Bstring.t
  | C_concat of complement * int * complement
  | C_compose of complement * complement
  | C_list of complement list
  | C_star of complement list * int list
  | C_union of union_side * complement
  | C_group of complement list
```

And tracks key-alignment match types via `mtype = ktype TmA.t` (`line 151`) alongside `Balign.Alignment` and `Balign.Permutation` (`lines 32-33`). Notice the structural cost directly visible in `C_compose of complement * complement` (`line 55`) and `C_star of complement list * int list` (`line 57`): every composition operator pairs its operands' complements, and every Kleene-star lens retains both per-element complements and permutation/alignment indices.

#### 1.4 Authoring Paradigms: Putback-First (`BiGUL`), Uncombinator (`HOBiT`), Synthesis (`Optician`), and Invertible Syntax

Basis: normative + documentation + source

Writing `get` alone under-determines `put` (infinitely many `put` behaviors satisfy `GetPut`/`PutGet` for a single non-injective `get`), whereas writing both separately invites silent law violations. Four principal authoring strategies trade off expressivity, proof burden, and usability:

1. **Putback-Based Programming (`BiGUL`, Ko, Zan & Hu, PEPM 2016, DOI `10.1145/2847538.2847544`):** Because a well-behaved `put` uniquely determines its compatible `get`, programmers write only `put` in a core DSL verified in Agda (implemented as a Haskell EDSL). Every well-typed `BiGUL` program is well-behaved by construction, at the cost of requiring authors to think backward in terms of source-update alignment.
2. **Higher-Order Bidirectional Programming (`HOBiT`, Matsuda & Wang, ESOP 2018, DOI `10.1007/978-3-319-89884-1_2`):** Replaces point-free lens combinators with standard functional programming idioms (variables, `case` expressions with reconciliation branches, higher-order functions) using an explicit `B` (bidirectional) type constructor to separate static/unidirectional control from bidirectional dataflow.
3. **Type- and Example-Directed Synthesis (`Optician`, Miltner et al., POPL 2018, DOI `10.1145/3158089`; `Optician-Tool/Optician-Tool` @ `4aa9d9d0f0511bf559abdc73dbef3b888d371d3a`):** Given source and target regular expressions plus I/O examples, Optician searches over DNF regex equivalences to synthesize provably bijective string lenses (and later quotient/symmetric lenses in ICFP 2018 / ICFP 2019), also integrated into `boomerang-lang/boomerang` (`optician/` directory). Synthesis is confined to regular string languages and cannot synthesize arithmetic checksums, dependent length prefixes, or context-free recursive ASTs.
4. **Invertible Syntax Descriptions (Rendel & Ostermann, Haskell 2010, DOI `10.1145/2088456.1863525`):** Unifies parsing and pretty-printing using partial isomorphisms (`Iso α β`) and symmetric applicative/alternative combinators (`Syntax`), avoiding duplicate grammars at the cost of awkward left-recursion factoring and tension with many-to-one layout optimization (e.g., Wadler-Lindig optimal line breaking).

**Information-theoretic lower bound for cross-language FFI (derived):** When synchronizing a Rust struct $X$ (carrying lifetimes, alignment padding, or ghost invariants) with a dynamic runtime object $Y$ (carrying refcounts, prototype pointers, or dynamic attributes), neither subsumes the other. By symmetric-lens theory, lossless synchronization irreducibly requires storing the symmetric difference in a complement $C$ (in real bridges like PyO3/JNI/Wasm handles, this manifests as unverified shadow wrapper tables). Conversely, whenever an FFI or wire boundary must be **stateless and tamper-evident** (cryptographic verification, IPC framing), the format must eliminate hidden variation so $C \cong 1$.

---

### 2. Hygienic Resugaring for Evaluation Traces, Scopes, and Types

Basis: normative + execution + derived

Compilers and macro systems desugar surface languages into small core languages (`Surface -> Core`), destroying the inverse mapping needed by step-debuggers, type-error reporters, and formal-verification diagnostics. Pombrio and Krishnamurthi formalized **resugaring** as a disciplined bidirectional inversion of desugaring across four stages:

#### 2.1 Dynamic Evaluation-Trace Resugaring (PLDI 2014 & ICFP 2015)

- **Lifting Reduction Sequences (PLDI 2014, DOI `10.1145/2594291.2594319`):** Given a core small-step operational semantics $\to_c$ and declarative desugaring rules $\mathcal{D}$, resugaring maps a core reduction trace $e_0 \to_c e_1 \to_c \dots \to_c e_n$ into a surface evaluation trace $s_0 \to_s s_1 \to_s \dots \to_s s_m$ ($m \le n$) satisfying two formal properties:
  1. **Emulation:** Every surface step corresponds faithfully to one or more underlying core steps (preserving observable evaluation behavior and intermediate values).
  2. **Abstraction:** Internal administrative steps introduced solely by macro expansions (such as binding a fresh temporary variable to avoid re-evaluating a short-circuit `or` operand) are hidden (stuttered/skipped) so programmers never observe compiler-synthesized temporaries.
- **Hygienic Compositional DAG Resugaring (ICFP 2015, DOI `10.1145/2784731.2784755`):** Plain AST trees lose provenance when substitution duplicates a subexpression or macro-introduced binders collide with user variables. Pombrio and Krishnamurthi represent desugared terms as **labeled DAGs** preserving syntactic-sugar provenance tags and hygiene scopes through core $\beta$-reduction, ensuring that:
  - macro-introduced temporaries cannot capture identically named user identifiers (witnessed in Probe 2 in **Evidence**, where `or(tmp, 99)` with user variable `tmp = 0` desugars using `__hyg_1`, skips the internal `if` step, and resugars cleanly to `('or', ('var', 'tmp'), ('val', 99)) -> ('or', ('val', 0), ('val', 99)) -> ('val', 99)`), and
  - multiple independent desugaring rules compose without colliding.
- **Bridge to Retentive Lenses (`arXiv:2001.02031`):** Zhu et al. explicitly cast Pombrio–Krishnamurthi resugaring as an instance of **retentive lenses**, where `get` is desugaring (producing core AST + region provenance links) and `put` uses retained links after a core evaluation step to reconstruct the unchanged surface sugar context around the reduced subterm.

#### 2.2 Static Semantics: Inferring Scope and Type Rules Through Sugar (ICFP 2017 & PLDI 2018)

- **Scope Inference (ICFP 2017, DOI `10.1145/3110288`):** Given a core language's binding specification and declarative desugaring rules, static analysis automatically infers the **surface scope rules** (which surface positions bind variables and which positions fall under those bindings), enabling IDE go-to-definition, hygienic renaming, and unbound-variable errors purely in surface terms.
- **Type-Rule Inference (`SweetT`, PLDI 2018, DOI `10.1145/3192366.3192398`):** Given a declarative core type system and desugaring rules, symbolic execution of the core type checker over schematic desugared templates synthesizes **surface-level typing rules** that are provably **sound and complete** with respect to checking the desugared core term—eliminating opaque core-IR type errors (such as reporting an internal thunk or closure mismatch inside a surface `for`/`or` construct).

#### 2.3 Structural Limits of Resugaring Under Compilation and Verification

Basis: derived

Resugaring succeeds cleanly on **local, compositional, declarative syntactic desugaring**, but hits three hard walls in optimizing compilers and formal verification toolchains:

1. **Information-destroying optimizations:** Common subexpression elimination (CSE), loop fusion, dead-store elimination, and SROA merge or split core nodes originating from distinct surface expressions. The provenance relation ceases to be a tree-homomorphic lens and becomes a many-to-many relation where no single surface step exists for a fused instruction.
2. **Non-local whole-function transformations:** CPS conversion, `async`/`await` state-machine elaboration, closure conversion, and SSA phi-insertion scatter one surface construct across disjoint struct fields and CFG basic blocks that local DAG pattern matching cannot reassemble without explicit bidirectional frame/state-map metadata.
3. **Turing-complete procedural macros:** Arbitrary token-stream computation (e.g., Rust `proc_macro`) provides no declarative rewrite schema to invert or symbolically type-check, forcing fallback to lossy source spans unless macros emit explicit provenance/hygiene graphs.

---

### 3. LangSec, Parser Differentials, and the Algebra of Non-Malleable Codecs

Basis: normative + documentation + source + execution

#### 3.1 LangSec and the Chomsky-Hierarchy Boundary

Sassaman et al. (IEEE Systems Journal 2013, DOI `10.1109/JSYST.2012.2222000`) and Momot et al. ("The Seven Turrets of Babel", IEEE SPW 2016, DOI `10.1109/SPW.2016.39`) establish the foundational **Language-Theoretic Security (LangSec)** principles:

- **Shotgun parsing** (interleaving ad-hoc input validation checks with state-mutating application logic) creates an implicit Turing-complete recognizer whose accepted language is unanalyzable.
- **Undecidability of parser equivalence:** Equivalence ($L(P_1) = L(P_2)$) and non-ambiguity are undecidable for general context-free and context-sensitive grammars, and decidable only for restricted grammar classes (regular / deterministic finite automata, visibly pushdown languages). Consequently, following Postel's Law ("be liberal in what you accept") guarantees **parser differentials** across independent implementations (historically yielding X.509 null-byte CN spoofing, duplicate ZIP entry Android Master Key exploits, HTTP/1.1 `Content-Length`/`Transfer-Encoding` request smuggling, and ASN.1 BER signature malleability).
- **Cryptographic necessity of non-malleability:** For signed, MAC-authenticated, or content-addressed wire messages, signature unforgeability protects *raw byte sequences*, not abstract ASTs. If two distinct byte strings $b_1 \neq b_2$ both parse to the same semantic message $m$ (violation of parser injectivity), an adversary can forge a distinct wire encoding or trigger signer/verifier confusion.

#### 3.2 Exact Algebraic Laws of Verified Non-Malleable Parser/Serializer Pairs

Direct inspection of `project-everest/everparse` (`lib/everparse/lowparse/LowParse.Spec.Base.{fsti,fst}`) and `secure-foundations/vest` (`vest_lib/src/core/{spec,proof}.rs`) reveals that **both independent verification ecosystems converged on the exact same core algebraic contract**, despite using different proof assistants (`F*`/`Pulse` vs. `Verus`/Rust):

1. **Serialize-Parse Round-Trip (`serializer_correct` / `SPRoundTrip`):**
   - `LowParse.Spec.Base.fsti:715-721`:
     ```fstar
     let serializer_correct (#k: parser_kind) (#t: Type) (p: parser k t) (f: bare_serializer t) : GTot prop =
       forall (x: t) . parse p (f x) == Some (x, Seq.length (f x))
     ```
   - `vest_lib/src/core/proof.rs:66-75` (`SPRoundTrip`):
     ```rust
     requires self.sp_roundtrip_inv(), self.consistent(v),
     ensures ({ let bytes = self.spec_serialize(v);
                self.spec_parse(bytes) == Some((bytes.len() as int, v)) })
     ```
   - **Consequence (`NonAmbiguous`):** `SPRoundTrip` immediately implies serializer injectivity (`v1 != v2 ==> serialize(v1) != serialize(v2)`), proven via a blanket `impl<C: SPRoundTrip> NonAmbiguous for C` in `vest_lib/src/core/proof.rs:128-137`.

2. **Parser Injectivity / Non-Malleability (`injective` / `NonMalleable`):**
   - `LowParse.Spec.Base.fsti:46-102`:
     ```fstar
     (* injective_precond: parse p b1 = Some(v1, len1) /\ parse p b2 = Some(v2, len2) /\ v1 == v2 *)
     (* injective_postcond: len1 == len2 /\ Seq.slice b1 0 len1 == Seq.slice b2 0 len2 *)
     let injective (#t: Type) (p: bare_parser t) : GTot prop =
       forall (b1 b2: bytes) . injective_precond p b1 b2 ==> injective_postcond p b1 b2
     ```
   - `vest_lib/src/core/proof.rs:201-218` (`NonMalleable`):
     ```rust
     ensures
         self.spec_parse(buf1) matches Some((n1, v1)) ==>
         self.spec_parse(buf2) matches Some((n2, v2)) ==>
         v1 == v2 ==> buf1[0..n1] == buf2[0..n2]
     ```

3. **Parse-Serialize Round-Trip (`serializer_complete` / `PSRoundTrip`) Derived Automatically:**
   - Both libraries prove the exact same meta-theorem: **`SPRoundTrip` + `NonMalleable` $\implies$ `PSRoundTrip`** ($\text{parse}(b) = \text{Some}(n, v) \implies \text{serialize}(v) = b[0..n)$):
     - `LowParse.Spec.Base.fst:78-100` (`serializer_correct_implies_complete`)
     - `vest_lib/src/core/proof.rs:176-195` (`impl<C: SPRoundTrip + NonMalleable + SoundParser> PSRoundTrip for C`)
   - **Uniqueness of parsers (`LowParse.Spec.Base.fst:102-133`):** `LowParse` additionally proves `serializer_parser_unique'`: if two strong parsers `p1, p2` are both correct for the same serializer `s` and `p1` is injective, then `p1` and `p2` agree identically on every input accepted by `p1`—directly eliminating parser differentials by theorem!

4. **Strong Prefix / No-Lookahead (`ParserStrong` / `no_lookahead` / `NoLookAhead`):**
   - `LowParse.Spec.Base.fsti:117-169` (`no_lookahead`) and `LowParse.Spec.Base.fst:53-76` (`parse_strong_prefix`): if `parse p x = Some (y, off)` and `x'` agrees with `x` on bytes `0..off`, then `parse p x' = Some (y, off)`.
   - `vest_lib/src/core/proof.rs:226-256` (`NoLookAhead`, deriving `corollary_non_extensible`: `spec_parse(i1) == Some((n, v)) ==> spec_parse(i1 + i2) == Some((n, v))`).
   - **Why `NoLookAhead` is essential for sequential composition (execution):** Probe 3 in **Evidence** constructs a parser `P1` that is individually `SPRoundTrip` and `NonMalleable`, but peeks one byte past its consumed prefix (`b"abc"` consumes `b"ab" -> 2`, while `b"a"` consumes `b"a" -> 1`). Composing `Pair(P1, P2)` breaks `SPRoundTrip`: serializing `(1, "bc")` yields `b"abc"`, which parses back as `(2, "c")`.
   - **Vest 2.0's compositional refinement (`SPRoundTripDps`):** In `vest_lib/src/core/proof.rs:24-45`, Vest 2.0 expresses round-trip in **destination-passing style** (`spec_parse(spec_serialize_dps(v, obuf)) == Some((byte_len(v), v))` for *arbitrary* trailing buffer `obuf`), bundling prefix-extension safety directly into the inductive round-trip theorem for all `NonTailFmt` combinators.

5. **Productivity (`parses_at_least 1` / `Productive`) and Choice Disjointness:**
   - Repetition combinators (`Star`/`Repeat`) require consuming at least one byte per element (`LowParse.Spec.Base.fsti:230-237`; `vest_lib/src/core/proof.rs:258-284`, noting that `Empty`, `Eof`, `Tail`, `Opt`, `Star`, `OptionalEnd`, `RepeatTillEnd` set `productive_inv() = false`).
   - Sum/choice combinators (`Alt`) preserve non-malleability only under **domain disjointness** (`disjoint_domains`, `vest_lib/src/core/spec.rs:23-26`) and **value disjointness** (`disjoint_values`, lines 31-36); discarding combinators (`Preceded`/`Terminated`) require the discarded side to satisfy `AdmitsUniqueVal` (lines 124-130) so discarded padding/tags cannot carry malleable bits!

---

### 4. Comparative Architecture of Verified and Unverified Format Compilers

Basis: normative + documentation + source + execution

#### 4.1 System-by-System Deep Dive

1. **EverParse / LowParse / 3D / ASN1\* / EverCBOR / EverCDDL (`project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c`):**
   - **Architecture:** `LowParse` (`lib/everparse/lowparse/`) provides the F\* specification and `Low*`/`Pulse` imperative combinators indexed by `parser_kind` (`parser_kind_low`, `parser_kind_high`, `parser_kind_subkind: option (ParserStrong | ParserConsumesAll)`, `parser_kind_metadata`, `parser_kind_injective`, `LowParse.Spec.Base.fsti:277-305`). Frontends compile to `LowParse`:
     - **`3D`** (PLDI 2022, DOI `10.1145/3519939.3523708`): C-like dependent-struct DSL generating zero-copy, zero-allocation (`O(1)` stack) C validators used in Windows Hyper-V VMBus, SMB, and TCP/IP.
     - **`QuackyDucky`**: RFC-style DSL generating F\* parsers/serializers (TLS 1.3, QUIC, Bitcoin) requiring explicit F\* + KaRaMeL extraction.
     - **`ASN1*`** (CPP 2023, DOI `10.1145/3573105.3575684`; integrated at `lib/everparse/asn1/{spec,pulse}` + `src/ASN1/tool` per `Makefile:40, 104-119`): formally verified non-malleable ASN.1 DER parser/serializer enforcing ITU-T X.690 DER canonicality (minimal short/long length encoding, minimal two's-complement integer encoding, canonical `BOOLEAN`, unused-bit masking in `BIT STRING`, canonical `SET OF` ordering).
     - **`EverCBOR` / `EverCDDL` / `EverCOSign`** (`README.md:15-19, 74-185`): Pulse-verified CBOR (`CBORDet` implementing RFC 8949 §4.2.1 deterministic encoding—note `README.md:127` writes "RFC 8979" as a typo for RFC 8949—and `CBORNondet` for definite-length CBOR, excluding floating-point values pending IETF NaN map-key standardization) plus CDDL compiler (`everparse-cddl.exe --rust` for standalone Rust or C) and COSE signing.
   - **TCB and trade-offs:** Verification runs in F\* + Z3; C/Rust code is extracted via `KaRaMeL` (and compiled by an unverified C or Rust compiler). Zero-copy `3D` validators avoid allocation, but callers integrating `3D` across a C FFI seam must ensure the validated buffer is not concurrently mutated (double-fetch / TOCTOU) and that field accessors match the validated offsets.

2. **Vest (`secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35`; USENIX Security 2025):**
   - **Native Rust verification via Verus:** Eliminates F\*-to-C / Coq-to-OCaml extraction by verifying native `#![no_std]`-capable Rust parsers and serializers directly in Verus (`vest_lib` + `VestDSL`).
   - **Vest 1.0 (USENIX Security 2025) vs. Vest 2.0 (`v0.2.0`, `RELEASE_NOTES-v0.2.0.md:1-96`):**
     - *Vest 1.0* emitted free functions (`parse_packet`, `packet_len`, fallible `serialize_packet(&v, &mut buf, pos)?`), requiring callers to manually prove value validity and `byte_len(v) <= usize::MAX` before serialization.
     - *Vest 2.0* redesigns `vest_lib` into three layers (`core::spec`, `core::exec`, `core::proof`) and emits a nominal format type (`PacketFmt`) implementing `Parser`, `Prepare`, and `SerializerExt`. `PacketFmt.prepare(&value)?` dynamically checks format consistency and computes exact wire length, making `PacketFmt.serialize(&packet, &mut slice)` **infallible** into an exact-sized slice.
     - *Vest 2.0 additions (`RELEASE_NOTES-v0.2.0.md:7-26`, `vest_lib/src/lib.rs:46-53`):* Bitfields, stack-allocated `[fmt; N]`, exhaustive dependent `choose`, `Nothing`/`Never`, experimental mutually recursive formats (`FixWith`), a dedicated **ASN.1 DER/BER compiler (`vest_asn1`)**, and general + deterministic **RFC 8949 CBOR (`cbor`)**.
   - **Constant-time caveat:** Vest's USENIX Security 2025 secret-independence guarantees (no secret-dependent branches or memory accesses) are verified at the **Rust source level** in Verus; unverified `rustc`/LLVM lowering passes (e.g., `SelectOpt` branchification, speculative execution) are outside Verus's TCB and can break machine-code constant-time execution.

3. **Narcissus (`mit-plv/fiat` @ `77f43f5d5408b3543f8dd01d4d43f4c4c70f1213`; ICFP 2019, DOI `10.1145/3341686`):**
   - **Deductive synthesis in Coq:** Synthesizes matched encoders and decoders from a single relational format `FormatM := S -> CacheFormat -> Comp (T * CacheFormat)` (`src/Narcissus/Common/Specs.v:20-21`), handling stateful cross-field dependencies such as Internet checksums, total-length headers, DNS compression pointers (via `CacheFormat`/`CacheDecode`), and bit-level alignment for Ethernet, IPv4, TCP, UDP, and DNS.
   - **Critical non-malleability gap (`Specs.v:40-79`):** Because `FormatM` returns a non-deterministic `Comp` set of valid target encodings, `CorrectDecoder` (`lines 40-68`) proves:
     1. *Completeness with arbitrary suffix `ext`:* `format s env ∋ (t, xenv) -> decode (mappend t ext) env' = Some (v, ext, xenv') /\ view s v /\ ...`
     2. *Soundness:* `decode t env' = Some (v, t', xenv') -> exists t'' xenv, view_format v env ∋ (t'', xenv) /\ t = mappend t'' t' /\ ...`
     Notice that **two distinct byte strings `t1 != t2` can both inhabit `format s env`**, so `CorrectDecoder` guarantees round-trip compatibility and prefix stability (`mappend t ext`), **not** canonical non-malleability! Moreover, Coq-extracted OCaml decoders incur GC/copy overhead when crossing into C/Rust kernels.

4. **Nail (`jbangert/nail` @ `4bd9cc29c4092abe7a77f8294aff2337bba02ec5`; OSDI 2014) and DaeDaLus (`GaloisInc/daedalus` @ `8ff2fadc981800c0457406d44fa55f8d270dfc71`):**
   - **`Nail`** unifies parsing and generation from one grammar extended with explicit **stream transforms** (handling offset tables, DNS label compression, ZIP directories, and checksums), generating C parsers/serializers; however, stream transforms are unverified C hooks and no formal non-malleability proof is generated.
   - **`DaeDaLus`** (DARPA SafeDocs) compiles declarative, length- and context-dependent data descriptions (PDF, ICC, ELF, MAVLink) into C++, Haskell, and Rust (`rts-c`, `rts-hs`, `rts-rust`) recognizers and pairs with `talos` (input synthesis), prioritizing LangSec determinism and ambiguity diagnostics over mechanized bijectivity proofs.

5. **Kaitai Struct (`kaitai-io/kaitai_struct` @ `4fb24924d21317dfba9209c47c892770d2834d7a`) and Protocol Buffers (`protocolbuffers/protobuf` @ `158df6107b2469fc3d2d66e11e5ada76efddfaa4`):**
   - **`Kaitai Struct`** compiles declarative `.ksy` YAML schemas into parsers across 10+ languages (`README.md`), designed primarily for **unidirectional reading** (serialization support is experimental/restricted to select targets) with zero formal ambiguity or non-malleability proofs—making cross-language parser differentials possible whenever target language arithmetic/overflow or offset checks differ.
   - **`Protocol Buffers`** is **structurally malleable by design**: varints allow overlong encodings (if accepted by permissive decoders), field tags may appear in arbitrary order, unknown fields may be interleaved, and repeated scalar fields merge via last-value-wins (witnessed in Probe 4b in **Evidence**: `08 05`, `08 85 00`, and `08 01 08 05` all decode to `{field1: 5}`). Direct source inspection of `src/google/protobuf/io/coded_stream.h:1309-1318` confirms this normatively:
     > *"There is no canonical representation of Protobuf messages: this representation is not consistent between languages, it may change when you rebuild your binary. Users who need canonical serialization (e.g. persistent storage in a canonical form, fingerprinting) should define their own canonicalization specification and implement the serializer using reflection APIs rather than relying on this API."*

#### 4.2 Cross-System Theorem, Capability, and TCB Comparison Matrix

| System (Pinned Rev.) | Prover / Lang | Target Output | `SPRoundTrip` | `NonMalleable` / `PSRoundTrip` | Strong Prefix (`NoLookAhead`) | Context-Sensitive (Offsets / Checksums / Sets) | Zero-Copy Validation | Side-Channel Guarantee | Primary TCB |
|---|---|---|---|---|---|---|---|---|---|
| **LowParse / 3D** (`everparse` `270f5aab`) | F\* / Low\* / Pulse | C (`3D`, `QuackyDucky`) & Rust (`EverCBOR`/`EverCDDL`) | Yes (`serializer_correct`) | Yes (`injective` $\implies$ `serializer_complete`) | Yes (`ParserStrong` / `no_lookahead`) | Dependent fields, bitfields; `ASN1*` DER; `CBORDet`; no arbitrary back-pointers | Yes (`3D` zero-alloc C validators) | Not verified in general `3D` | F\*, Z3, KaRaMeL, C/Rust compiler |
| **ASN1\*** (`everparse` `270f5aab`, CPP 2023) | F\* / Low\* / Pulse | C / Pulse | Yes | Yes (strict X.690 DER) | Yes | Minimal lengths, minimal 2's-comp ints, `SET OF` order, unused-bit masks | Yes | Not verified | F\*, Z3, KaRaMeL, C compiler |
| **Vest v0.2** (`vest` `026867a3`, USENIX Sec 2025) | Verus (Rust + Z3) | Native `#![no_std]` Rust | Yes (`SPRoundTripDps` $\implies$ `SPRoundTrip`) | Yes (`NonMalleable` $\implies$ `PSRoundTrip`) | Yes (`NoLookAhead` / DPS) | Dependent `Bind`/`choose`, bitfields, `vest_asn1` (DER/BER), `cbor`, experimental `FixWith` | Yes (zero-copy slices + in-place DPS) | Source-level secret-independence (Rust/Verus only) | Verus, Z3, `rustc` + LLVM |
| **Narcissus** (`fiat` `77f43f5d`, ICFP 2019) | Coq (Ltac synthesis) | Coq $\to$ OCaml | Yes (relational `CorrectDecoder` + `CorrectEncoder`) | **No** (`Comp` allows multiple encodings per value) | Yes (`mappend t ext` in `CorrectDecoder`) | Checksums, total lengths, bit alignment, DNS compression via `Cache` | No (OCaml extraction / allocation) | None | Coq kernel, extraction, OCaml runtime |
| **Nail** (`nail` `4bd9cc29`, OSDI 2014) | Unverified C generator | C parser + generator | Tested only | No | Grammar-dependent | Stream transforms (ZIP, DNS, checksums via C hooks) | Partial | None | Generator, handwritten C transforms, C compiler |
| **DaeDaLus** (`daedalus` `8ff2fadc`) | Haskell compiler | C++, Haskell, Rust recognizers | Parser-focused (no verified serializer) | Ambiguity checks (unverified) | Grammar-dependent | Dependent lengths, bitfields, offsets, PDF/ELF/ICC | Partial | None | DaeDaLus compiler + target RTS |
| **Kaitai Struct** (`kaitai_struct` `4fb24924`) | Scala compiler | 10+ languages | Unidirectional (serialization experimental) | No | No | Arbitrary expressions, seeks, instances | No | None | Compiler + per-language runtimes |
| **Protocol Buffers** (`protobuf` `158df610`) | Unverified codegen | C++, Rust, Go, Java, Python, ... | Semantic round-trip only | **Explicitly no** (`coded_stream.h:1309-1315`) | Length-delimited submessages only | Unknown fields, last-wins scalar merge, maps | Partial (string views) | None | Codegen + per-language runtimes |

---

### 5. Unifying Architectural Invariants for Verified Boundaries

Basis: derived

Synthesizing Sections 1–4 yields four reusable design rules for compilers, FFI bridges, and wire protocols:

1. **Separate quotient domains from zero-complement domains explicitly.** Human-authored formats (source code, configs, ASTs) legitimately require **quotient/retentive lenses** (preserving whitespace, comments, and layout across edits). Authenticated wire formats, RPC frames, and cross-trust FFI payloads must enforce **zero-complement non-malleability** (`NonMalleable` + `SPRoundTrip` + `NoLookAhead`). Never place a quotient lens inside a cryptographic signing perimeter without hashing the canonical wire bytes.
2. **Enforce `NoLookAhead` (`ParserStrong`) + `Productive` + `AdmitsUniqueVal` at every combinator seam.** Sequential composition preserves non-malleability iff prefixes are non-extensible; repetition terminates iff element parsers are productive (`n > 0`); discarded padding/delimiters preserve non-malleability iff their consistency predicate admits a unique byte sequence (`AdmitsUniqueVal`).
3. **Separate buffer validation from concurrent mutation (TOCTOU immunity).** Zero-copy verified validators (`3D`, `Vest`) prove invariants over a mathematical `Seq<u8>` snapshot. Across shared-memory IPC/DMA or C FFI seams, callers must either hold an immutable borrow (`&'a [u8]` with no concurrent writers) or copy once via volatile reads before validation—otherwise an adversary can mutate validated bytes between validation and field read.
4. **Preserve provenance through lowering via explicit bidirectional maps.** Whenever a compiler lowers surface syntax or a verifier encodes MIR/AST into SMT/prover terms, local declarative desugarings can reuse Pombrio–Krishnamurthi DAG resugaring (or retentive link lenses), whereas non-local lowerings (SSA, `async` state machines, VCG encodings) require explicit inverse frame/witness maps certified against the surface semantics to avoid spurious counterexamples.

## Boundaries

- **Known not to apply:**
  - `PutPut` (very well-behavedness) does **not** hold for lossy state-based asymmetric lenses over filtering/deletion-reinsertion edits without explicit complement retention or provenance links (witnessed in Probe 1).
  - `Narcissus`'s `CorrectDecoder` (`mit-plv/fiat` @ `77f43f5d`, `src/Narcissus/Common/Specs.v:40-68`) does **not** establish cryptographic non-malleability because `FormatM` is a non-deterministic `Comp` relation admitting multiple wire bytes per value.
  - `Protocol Buffers`' `CodedOutputStream::SetSerializationDeterministic` (`protocolbuffers/protobuf` @ `158df610`, `coded_stream.h:1309-1318`) does **not** provide canonical or cross-language/cross-build non-malleable wire encoding.
  - `Vest`'s source-level constant-time / secret-independence proofs do **not** automatically survive unverified `rustc`/LLVM optimization passes (e.g., branch insertion during `SelectOpt` or machine lowering).
- **Unsupported:**
  - `EverParse`'s `EverCBOR` (`project-everest/everparse` @ `270f5aab`, `README.md:129-136`) explicitly does **not** support CBOR floating-point values (pending IETF NaN map-key equivalence standardization) or combining `CBORDet` and `CBORNondet` in the same build; `EverCDDL` currently supports only deterministic CBOR (`README.md:96-99`).
  - `Optician` (`Optician-Tool/Optician-Tool` @ `4aa9d9d0`) and `Boomerang` (`boomerang-lang/boomerang` @ `24a309a6`) do **not** support arbitrary context-free recursive grammars, dependent length-prefixed binary frames, or arithmetic checksums.
  - Pombrio–Krishnamurthi resugaring does **not** support opaque Turing-complete procedural macros or arbitrary optimizing SSA/loop-fusion passes without auxiliary provenance specifications.
- **Not examined:**
  - Direct build/execution benchmarks of `EverParse` (`F*`/`KaRaMeL`), `Vest` (`Verus`), `Narcissus` (`Coq`), or `DaeDaLus` toolchains were not executed on this host; runtime performance and SMT verification-time comparisons rely on published peer-reviewed evaluations (`USENIX Security 2019/2025`, `PLDI 2022`, `CPP 2023`, `ICFP 2019`).
  - Lean 4 `InfoTree`/delaborator internals, `Comparse` (`F*` non-malleable parsers for MLS), and `Synbit` (`HOBiT`-based synthesis) were not directly inspected at pinned source revisions.
- **Unknown:**
  - Whether Pombrio–Krishnamurthi PLDI 2018 type-rule inference generalizes completely to substructural ownership/borrow checkers (e.g., Rust borrow checking / Polonius) or separation-logic proof obligations remains an open research problem.
  - How to certify end-to-end machine-code constant-time preservation of `Vest`-verified parsers through an optimizing LLVM or verified compiler backend without manual assembly auditing remains open.
  - Minimal decidable grammar fragments simultaneously supporting bidirectional non-malleability, arbitrary back-pointer decompression (DNS/ZIP), and linear-time zero-copy parsing remain unresolved.

## Evidence

### Primary Source Locations Inspected (Observed 2026-11-19)

- `secure-foundations/vest` @ `026867a37d4b918153058df2c8db6c52fc62ba35`:
  - `vest_lib/src/lib.rs:1-53` — three-layer architecture (`core::spec`, `core::exec`, `core::proof`), `#![no_std]` support, modules `asn1`, `cbor`, `combinators`, `core`, `primitives`.
  - `vest_lib/src/core/spec.rs:7-325` — `SpecParser`, `disjoint_domains` (`23-26`), `disjoint_values` (`31-36`), `SafeParser`, `SoundParser`, `StrictParser` (`83-102`), `Consistency`, `AdmitsUniqueVal` (`124-130`), `SpecSerializerDps` (`156-162`), `MinMaxByteLen` (`173-195`), `NonTailFmt` (`267-291`), `GoodSerializer` (`294-307`), `SpecCombinator` (`310-322`).
  - `vest_lib/src/core/proof.rs:24-397` — `SPRoundTripDps` (`24-45`), `SPRoundTrip` + blanket impl (`56-89`), `NonAmbiguous` + blanket impl (`97-137`), `PSRoundTrip` + blanket impl from `SPRoundTrip + NonMalleable + SoundParser` (`147-195`), `NonMalleable` (`201-218`), `NoLookAhead` + `corollary_non_extensible` (`226-256`), `Productive` (`258-284`), `StrictCombinator` (`321-345`), `Leaf` / `LeafNonMalleable` (`356-395`).
  - `RELEASE_NOTES-v0.2.0.md:1-96` — Vest 1.0 to Vest 2.0 (`v0.2.0`) redesign (`PacketFmt`, `Prepare` + infallible `serialize`, bitfields, exhaustive `choose`, `vest_asn1`, `cbor`).
- `project-everest/everparse` @ `270f5aab699ac284d8777d4f01be20a5d91ea47c`:
  - `lib/everparse/lowparse/LowParse.Spec.Base.fsti:23-470, 715-778` — `bare_parser`, `injective` (`46-102`), `no_lookahead` (`117-169`), `consumes_all` (`186-193`), `parser_subkind` (`277-279`), `parser_kind'` (`295-305`), `serializer_correct` (`715-721`), `serializer_complete` (`753-763`).
  - `lib/everparse/lowparse/LowParse.Spec.Base.fst:37-160` — `parse_injective` (`37-51`), `parse_strong_prefix` (`53-76`), `serializer_correct_implies_complete` (`78-100`), `serializer_parser_unique'` (`102-133`).
  - `Makefile:5-120` & `README.md:1-185` — repository layout integrating `LowParse`, `3D`, `QuackyDucky`, `ASN1*` (`lib/everparse/asn1/{spec,pulse}`, `src/ASN1/tool`), `EverCBOR` (`CBORDet`/`CBORNondet` in C and Rust `cborrs`), `EverCDDL`, and `EverCOSign`.
- `mit-plv/fiat` @ `77f43f5d5408b3543f8dd01d4d43f4c4c70f1213`:
  - `src/Narcissus/Common/Specs.v:18-158` — non-deterministic `FormatM := S -> CacheFormat -> Comp (T * CacheFormat)`, `CorrectDecoder` (`40-68`), `CorrectEncoder` (`70-79`), `CorrectDecoder_id` (`113-136`).
- `boomerang-lang/boomerang` @ `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`:
  - `lib/blenses.ml:28-159` — explicit `complement` ADT (`50-59`), `ktype` (`109-118`), `mtype` (`151`), alignment modules `Balign.Alignment` / `Balign.Permutation` (`32-33`).
- `protocolbuffers/protobuf` @ `158df6107b2469fc3d2d66e11e5ada76efddfaa4`:
  - `src/google/protobuf/io/coded_stream.h:849-852, 1294-1326` — `CodedOutputStream::SetSerializationDeterministic` explicit disclaimer of canonicality across languages and rebuilds.

### Executable Verification Probe (Observed 2026-11-19, Python 3)

Command: `python3 /tmp/probe_lenses_codecs.py` (self-contained script below):

```python
#!/usr/bin/env python3
"""Executable micro-probes for lens laws, hygienic resugaring, NoLookAhead composition, and wire malleability."""
from __future__ import annotations

# Probe 1: Asymmetric Lens Trilemma (GetPut, PutGet, PutPut) vs Retentive Links
def get_even(src: list[tuple[str, int, str]]) -> list[tuple[str, int]]:
    return [(k, v) for (k, v, _c) in src if v % 2 == 0]

def put_even(view: list[tuple[str, int]], src: list[tuple[str, int, str]]) -> list[tuple[str, int, str]]:
    assert all(v % 2 == 0 for _, v in view)
    comments = {k: c for (k, _v, c) in src}
    odds = [(k, v, c) for (k, v, c) in src if v % 2 != 0]
    return [(k, v, comments.get(k, "# default")) for (k, v) in view] + odds

s0 = [("a", 2, "# alpha"), ("b", 4, "# beta"), ("odd", 3, "# keep-odd")]
v0, v1, v2 = get_even(s0), [("a", 2)], [("a", 2), ("b", 4)]
assert put_even(v0, s0) == s0
assert get_even(put_even(v1, s0)) == v1 and get_even(put_even(v2, s0)) == v2
s_seq, s_direct = put_even(v2, put_even(v1, s0)), put_even(v2, s0)
print(f"[Probe 1] GetPut=True, PutGet=True, PutPut={s_seq == s_direct}")
print(f"  put(v2, put(v1, s0)) = {s_seq}")
print(f"  put(v2, s0)          = {s_direct}")

def put_retentive(view, links, src):
    odds = [(k, v, c) for (k, v, c) in src if v % 2 != 0]
    return [(k, v, links[k][2] if k in links else "# default") for (k, v) in view] + odds

links_s0 = {rec[0]: rec for rec in s0}
print(f"  retentive_put(v2, links_s0, put(v1, s0)) == s_direct: {put_retentive(v2, links_s0, put_even(v1, s0)) == s_direct}")

# Probe 2: Hygienic Resugaring (Emulation + Abstraction + Hygiene)
def desugar(expr, counter=[0]):
    if isinstance(expr, tuple) and expr[0] == "or":
        _, e1, e2 = expr
        counter[0] += 1
        hv = f"__hyg_{counter[0]}"
        d1, d2 = desugar(e1, counter), desugar(e2, counter)
        return ("tag", "or", hv, d2, ("let", hv, d1, ("if", ("var", hv), ("var", hv), d2)))
    return expr

def core_steps(term, env):
    trace, cur = [term], term
    while True:
        if isinstance(cur, tuple) and cur[0] == "tag":
            _, name, hv, d2, inner = cur
            if inner[0] == "let":
                _, x, rhs, body = inner
                if rhs[0] == "var":
                    cur = ("tag", name, hv, d2, ("let", x, ("val", env[rhs[1]]), body))
                    trace.append(cur)
                elif rhs[0] == "val":
                    cur = ("tag", name, hv, d2, ("if", rhs, rhs, d2))
                    trace.append(cur)
            elif inner[0] == "if":
                _, cond, thn, els = inner
                cur = thn if cond[1] else els
                trace.append(cur)
        else:
            break
    return trace

def resugar_step(term):
    if isinstance(term, tuple) and term[0] == "tag" and term[1] == "or":
        _, _, _hv, d2, inner = term
        return ("or", inner[2], d2) if inner[0] == "let" else None
    return term

core_trace = core_steps(desugar(("or", ("var", "tmp"), ("val", 99))), {"tmp": 0})
resugared_trace = [r for r in (resugar_step(t) for t in core_trace) if r is not None]
print(f"[Probe 2] Hygienic resugaring (user var 'tmp'=0):")
print(f"  core steps ({len(core_trace)}):      {core_trace}")
print(f"  resugared steps ({len(resugared_trace)}): {resugared_trace}")

# Probe 3: Sequential Composition Requires NoLookAhead (Strong Prefix)
def p1_parse(buf: bytes):
    if buf.startswith(b"abc"): return (2, 2)
    if buf.startswith(b"a"): return (1, 1)
    return None

def p1_serialize(v: int) -> bytes: return b"a" if v == 1 else b"ab"
def p2_parse(buf: bytes):
    if buf.startswith(b"bc"): return (2, "bc")
    if buf.startswith(b"c"): return (1, "c")
    return None

def pair_parse(buf: bytes):
    r1 = p1_parse(buf)
    if r1 is None: return None
    r2 = p2_parse(buf[r1[0]:])
    return None if r2 is None else (r1[0] + r2[0], (r1[1], r2[1]))

wire = p1_serialize(1) + b"bc"
print(f"[Probe 3] P1 NoLookAhead={p1_parse(b'a') == p1_parse(b'abc')}; Pair SPRoundTrip on (1, 'bc'): wire={wire!r} -> {pair_parse(wire)}")

# Probe 4: ASN.1 BER vs DER & Protobuf Malleability
def parse_asn1_int(buf: bytes, strict_der: bool):
    if len(buf) < 2 or buf[0] != 0x02: return None
    lbyte = buf[1]
    if lbyte < 0x80: length, hdr = lbyte, 2
    else:
        nlen = lbyte & 0x7F
        if nlen == 0 or len(buf) < 2 + nlen: return None
        length = int.from_bytes(buf[2:2+nlen], "big")
        if strict_der and (length < 0x80 or buf[2] == 0x00): return None
        hdr = 2 + nlen
    if length == 0 or len(buf) < hdr + length: return None
    payload = buf[hdr:hdr+length]
    if strict_der and length > 1:
        if (payload[0] == 0x00 and (payload[1] & 0x80) == 0) or (payload[0] == 0xFF and (payload[1] & 0x80) != 0):
            return None
    return (hdr + length, int.from_bytes(payload, "big", signed=True))

asn1 = {"canonical_der": bytes.fromhex("02 01 05"), "non_minimal_len": bytes.fromhex("02 81 01 05"), "non_minimal_sign_pad": bytes.fromhex("02 02 00 05")}
print(f"[Probe 4a] ASN.1 BER accepts all 3 as val=5: { {k: parse_asn1_int(b, False) for k, b in asn1.items()} }")
print(f"[Probe 4a] ASN.1 DER rejects non-canonical:  { {k: parse_asn1_int(b, True) for k, b in asn1.items()} }")

def parse_pb_field1_varint(buf: bytes):
    i, val = 0, None
    while i < len(buf):
        assert buf[i] == 0x08; i += 1
        shift, acc = 0, 0
        while True:
            b = buf[i]; i += 1
            acc |= (b & 0x7F) << shift
            if not (b & 0x80): break
            shift += 7
        val = acc
    return val

pb = {"minimal": bytes.fromhex("08 05"), "overlong_varint": bytes.fromhex("08 85 00"), "duplicate_scalar_tag": bytes.fromhex("08 01 08 05")}
print(f"[Probe 4b] Protobuf malleable wire forms all decode to field1=5: { {k: parse_pb_field1_varint(b) for k, b in pb.items()} }")
```

Verbatim observed output:

```text
[Probe 1] GetPut=True, PutGet=True, PutPut=False
  put(v2, put(v1, s0)) = [('a', 2, '# alpha'), ('b', 4, '# default'), ('odd', 3, '# keep-odd')]
  put(v2, s0)          = [('a', 2, '# alpha'), ('b', 4, '# beta'), ('odd', 3, '# keep-odd')]
  retentive_put(v2, links_s0, put(v1, s0)) == s_direct: True
[Probe 2] Hygienic resugaring (user var 'tmp'=0):
  core steps (4):      [('tag', 'or', '__hyg_1', ('val', 99), ('let', '__hyg_1', ('var', 'tmp'), ('if', ('var', '__hyg_1'), ('var', '__hyg_1'), ('val', 99)))), ('tag', 'or', '__hyg_1', ('val', 99), ('let', '__hyg_1', ('val', 0), ('if', ('var', '__hyg_1'), ('var', '__hyg_1'), ('val', 99)))), ('tag', 'or', '__hyg_1', ('val', 99), ('if', ('val', 0), ('val', 0), ('val', 99))), ('val', 99)]
  resugared steps (3): [('or', ('var', 'tmp'), ('val', 99)), ('or', ('val', 0), ('val', 99)), ('val', 99)]
[Probe 3] P1 NoLookAhead=False; Pair SPRoundTrip on (1, 'bc'): wire=b'abc' -> (3, (2, 'c'))
[Probe 4a] ASN.1 BER accepts all 3 as val=5: {'canonical_der': (3, 5), 'non_minimal_len': (4, 5), 'non_minimal_sign_pad': (4, 5)}
[Probe 4a] ASN.1 DER rejects non-canonical:  {'canonical_der': (3, 5), 'non_minimal_len': None, 'non_minimal_sign_pad': None}
[Probe 4b] Protobuf malleable wire forms all decode to field1=5: {'minimal': 5, 'overlong_varint': 5, 'duplicate_scalar_tag': 5}
```

## Revalidation

1. **Executable laws and counterexamples:** Re-run the self-contained Python 3 probe under **Evidence** (`python3 /tmp/probe_lenses_codecs.py`). All four assertions (`PutPut=False` vs. retentive equality, hygienic resugaring Emulation/Abstraction, `NoLookAhead` sequential counterexample, and ASN.1 DER vs. BER + Protobuf malleability witnesses) must pass cleanly.
2. **Vest trait contract drift:** Against a newer `secure-foundations/vest` commit, diff `vest_lib/src/core/spec.rs` and `vest_lib/src/core/proof.rs` to verify whether `SPRoundTripDps`, `NonMalleable`, `PSRoundTrip`, `NoLookAhead`, `Productive`, `AdmitsUniqueVal`, and `StrictCombinator` retain the same algebraic implications, and check `vest_asn1/` and `vest_lib/src/cbor/` for canonical-encoding coverage and recursive `FixWith` stabilization.
3. **EverParse / LowParse / ASN1\* / EverCBOR drift:** Against a newer `project-everest/everparse` commit, diff `lib/everparse/lowparse/LowParse.Spec.Base.fsti` (`parser_kind`, `injective`, `no_lookahead`, `serializer_correct`, `serializer_complete`), `lib/everparse/lowparse/LowParse.Spec.Base.fst` (`serializer_correct_implies_complete`, `serializer_parser_unique'`), and `README.md` (specifically whether `EverCBOR` adds floating-point support or `EverCDDL` adds non-deterministic CBOR).
4. **Narcissus non-malleability status:** Against a newer `mit-plv/fiat` commit, inspect `src/Narcissus/Common/Specs.v` (`FormatM`, `CorrectDecoder`) to check whether a deterministic/functional encoding predicate or parser-injectivity theorem has been added.
5. **Protocol Buffers canonicalization policy:** Against a newer `protocolbuffers/protobuf` commit, inspect `src/google/protobuf/io/coded_stream.h` around `SetSerializationDeterministic` to confirm whether canonical cross-language serialization remains explicitly unsupported.
