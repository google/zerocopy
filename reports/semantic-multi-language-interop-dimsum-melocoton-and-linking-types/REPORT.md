# Semantic multi-language interoperability: boundary terms, linking types, realizability, DimSum, Melocoton, VeriFFI, and robust property preservation

## Summary

- Multi-language programs have been given a formal meaning in four
  structurally different ways, each fixing something globally: (1) a *syntactic
  multi-language* with boundary terms (Matthews and Findler) fixes the set of
  languages; (2) *linking types* (Patterson and Ahmed) enrich one language's
  types at boundaries and fix a typed common target with fully abstract
  compilers; (3) *realizability after compilation* (Patterson, Mushtak, Wagner
  and Ahmed) interprets the types of both sources as sets of terms of one
  target and proves glue code sound, fixing that target; (4) *decentralized
  modules* (DimSum) make each library a labelled transition system over
  language-specific events and move every cross-language concern into
  combinators, fixing only an event alphabet per language.
- The reusable device of style (4) is a *stateful wrapper with two kinds of
  non-determinism*: what the peer or the runtime may do is a demonic choice (a
  proof covers all outcomes); information the wrapper cannot compute, such as
  which high-level value a machine word denotes, is an angelic choice (a proof
  supplies it). DimSum uses it for a C-like language against assembly;
  Melocoton reuses it for OCaml against C with a moving garbage collector.
- DimSum and Melocoton attach *opposite polarity* to the same data shape
  `state -> set of states -> Prop`: in DimSum "no transition" is no behaviour
  (bottom of refinement) and "transition to the empty set" is undefined
  behaviour; in Melocoton "no transition" is stuck (undefined behaviour) and
  "transition to the empty set" is no behaviour. Porting a definition between
  them without flipping this is a silent error.
- Melocoton models the OCaml runtime as a block store that never moves plus an
  address map `theta` from logical blocks to C addresses, re-chosen demonically
  at every allocation primitive, every return from an OCaml callback, and every
  OCaml-to-C call, subject only to reachability closure and liveness of
  registered roots. A C word obtained before such a point denotes nothing
  afterwards unless it sits in a registered root cell and is re-read. Integers
  are `2n+1`; closure and custom blocks have tags 247 and 255. Exceptions,
  threads, finalizers and direct pointer access into blocks are not modelled.
- VeriFFI (Coq/CertiCoq against C/VST) needs no multi-language semantics
  because compiled functional code and foreign code are both C; its soundness
  argument is conditional on a CertiCoq end-to-end theorem that its authors
  describe as not yet complete.
- Against adversarial foreign code, full abstraction is not sufficient and is
  argued to be excessive for safety goals: Abate et al. exhibit a correct
  compilation chain that preserves trace equivalence yet breaks a robustly
  satisfied safety property, and order the 26 criteria of their Figure 1 by
  what must be protected (integrity, data confidentiality, code
  confidentiality).
- Coordinates that circulate in wrong form: the DimSum DOI is `10.1145/3571220`
  (authors Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer); the
  Melocoton DOI is `10.1145/3622823`; the PLDI 2022 paper is by Patterson,
  Mushtak, Wagner and Ahmed; VeriFFI is a POPL 2025 paper by Korkut, Stark and
  Appel.
- A 46-check bounded probe preserved here executes the DimSum refinement laws,
  a Melocoton-style runtime under every admissible GC outcome, a
  well-bracketedness attack, and the Abate et al. counterexample.

## Applicability

The findings describe published formal systems and three Coq developments at
fixed revisions: statements about those calculi and proofs, not about
production compilers or runtimes. The subjects in `REPORT.json` relate as
follows.

- Three papers form a lineage on *type-safe or equivalence-preserving*
  interoperability: Matthews and Findler (source-level boundaries), Patterson
  and Ahmed (linking types), Patterson, Mushtak, Wagner and Ahmed
  (realizability). Dreyer, Neis and Birkedal is used only for the
  well-bracketed variant of the "awkward" example.
- DimSum (paper, artifact record, development guide) and Melocoton (paper, Coq
  development at one commit) form a lineage on *refinement and program-logic*
  reasoning; Melocoton states that its operational semantics is inspired by
  DimSum.
- VeriFFI (paper and repository at one commit) is the contrasting design for a
  garbage-collected functional language against C.
- Abate et al. (paper and Coq development at one commit) supplies the security
  criteria for boundaries with untrusted code.
- The OCaml 4.14.1 headers serve only to compare Melocoton's constants and
  root primitives with one concrete runtime.

Scope limits for every finding: all cited calculi are sequential; the
languages are core calculi (lambda calculi with references, a C-like `Rec`, an
assembly language `Asm`, `lambda_ML`, `lambda_C`), not OCaml, C, or Rust; no
Coq development was built, so statements about them come from reading sources;
papers were read in the author-hosted or arXiv versions listed under Evidence.

This report is language-pair independent and contains no Rust-specific ABI,
unwinding, or layout tables. Three neighbouring packages of this corpus are
cited by slug rather than repeated; per their catalog entries they cover
`compositional-correctness-linking-and-whole-program-optimization` (CompCert
linking, CompCertO, CompCertM, SepCompCert, Conditional Contextual Refinement,
DimSum and the Abate et al. paper, in the setting of Rust compilation),
`compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026`
(CompCert external calls, CakeML FFI oracles, VeriFFI, unwinding), and
`anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` (constant-time tooling
and FFI boundaries). This report is meant as the detailed account of the
multi-language semantics that those packages draw on.

Applying a finding to another language pair (Rust and C, or a managed runtime
other than the modelled one) is an extrapolation whose only support is
structural: the wrapper pattern, the root discipline and the property hierarchy
do not mention OCaml or `Rec`. Nothing here shows that the proofs carry over.

## Findings

### 1. Coordinates of the primary sources

| Work | Verified coordinates |
| --- | --- |
| Matthews, Findler. *Operational semantics for multi-language programs* | ACM TOPLAS 31(3), Article 12, April 2009, DOI `10.1145/1498926.1498930`. Conference version: POPL 2007, DOI `10.1145/1190216.1190220`. |
| Patterson, Ahmed. *Linking Types for Multi-Language Software: Have Your Cake and Eat It Too* | SNAPL 2017, LIPIcs vol. 71, pp. 12:1-12:15, DOI `10.4230/LIPIcs.SNAPL.2017.12`; arXiv `1711.04559v1`. |
| Patterson, Mushtak, Wagner, Ahmed. *Semantic Soundness for Language Interoperability* | PLDI 2022, pp. 609-624, DOI `10.1145/3519939.3523703`; arXiv `2202.13158v2`. |
| Sammler, Spies, Song, D'Osualdo, Krebbers, Garg, Dreyer. *DimSum: A Decentralized Approach to Multi-language Semantics and Verification* | Proc. ACM Program. Lang. 7(POPL), Article 27, pp. 775-805, January 2023, DOI `10.1145/3571220`. Artifact and appendix: DOI `10.5281/zenodo.7306312` (version v1, published 9 November 2022). |
| Guéneau, Hostert, Spies, Sammler, Birkedal, Dreyer. *Melocoton: A Program Logic for Verified Interoperability Between OCaml and C* | Proc. ACM Program. Lang. 7(OOPSLA2), Article 247, pp. 716-744, October 2023, DOI `10.1145/3622823`. |
| Korkut, Stark, Appel. *A Verified Foreign Function Interface between Coq and C* | Proc. ACM Program. Lang. 9(POPL), Article 24, pp. 687-717, January 2025, DOI `10.1145/3704860`. |
| Abate, Blanco, Garg, Hrițcu, Patrignani, Thibault. *Journey Beyond Full Abstraction: Exploring Robust Property Preservation for Secure Compilation* | IEEE CSF 2019, pp. 256-271, DOI `10.1109/CSF.2019.00025`; arXiv `1807.04603v6`. |
| Dreyer, Neis, Birkedal. *The impact of higher-order state and control effects on local relational reasoning* | JFP 22(4-5), pp. 477-528, 2012, DOI `10.1017/S095679681200024X`; ICFP 2010, DOI `10.1145/1863543.1863566`. |

Near-miss identifiers resolve to unrelated articles: `10.1145/3571200` is
"From SMT to ASP: Solver-Based Approaches to Solving Datalog
Synthesis-as-Rule-Selection Problems" and `10.1145/3622816` is "Fast and
Efficient Boolean Unification for Hindley-Milner-Style Type and Effect
Systems". Metadata only (not text) was checked for CompCertM (Song, Cho, Kim,
Kim, Kang, Hur; POPL 2020; `10.1145/3371091`), CompCertO (Koenig, Shao; PLDI
2021; `10.1145/3453483.3454097`), Conditional Contextual Refinement (POPL 2023;
`10.1145/3571232`) and StkTokens (Skorstengaard, Devriese, Birkedal; POPL 2019;
`10.1145/3290332`).

Basis: documentation (Crossref records, the DROPS page for the LIPIcs DOI, the
Zenodo record, and the front matter of each paper text). Crossref prints a
garbled page range for the CSF paper; the range above is from the README of its
Coq development.

### 2. Four semantic styles compared

| | Syntactic multi-language | Linking types | Realizability after compilation | Decentralized modules |
| --- | --- | --- | --- | --- |
| Representative | Matthews-Findler | Patterson-Ahmed | Patterson-Mushtak-Wagner-Ahmed | DimSum; Melocoton |
| Where the boundary lives | A term former in a combined source syntax | A type annotation in one source language | Source boundary syntax, given meaning by target glue code | A combinator on transition systems |
| What a component denotes | A term of the combined calculus | A term of the extended language at a linking type | A target term in the interpretation of a source type | A transition system over the events of its language |
| Fixed up front | The set of languages | A typed target and fully abstract compilers to it | One (untyped) target language and both compilers | The event alphabet of each language |
| Memory representation | Abstracted away | Abstracted away | Explicit in the target | Explicit, and may differ per language |
| Main theorem shape | Type soundness; operational equivalences of boundary encodings | (Proposed) equivalence preservation and reflection | Convertibility soundness, fundamental property, type safety | Refinement that is transitive and compatible with linking; adequacy of a program logic |
| Mechanized in the cited work | No | No | No (paper proofs in a technical appendix) | Yes, Coq |

DimSum's own placement of the earlier work: syntactic multi-languages "scale
well to typed, higher-order languages" but fix the set of languages; the
realizability approach is "effective for type safety" but reasons at the target.

Basis: documentation (the cited papers; the last row reflects the absence of
any proof-assistant claim in the first three texts and the explicit Coq claims
of DimSum and Melocoton) + derived (the tabulation).

### 3. Syntactic boundaries: lump and natural embeddings

Matthews and Findler combine an untyped call-by-value calculus ("Scheme") with
a simply typed one ("ML") and add boundary terms whose reduction rules are the
interoperability semantics. The article states that the technique "abstracts
away the low-level details of interoperability like garbage collection and
representation coherence".

- *Lump embedding.* Foreign values are opaque: ML may hold a Scheme value and
  hand it back but cannot use it. Theorem 1 is type soundness (a well-typed
  program reduces to a value or an error, or diverges). The authors relate it
  to FFIs that give C native values only as pointers to hand back.
- *Natural embedding.* Boundaries convert by type: numbers to numbers, and a
  function at `t1 -> t2` to a proxy that converts its argument in the opposite
  direction, applies the foreign function, and converts the result. Unchecked,
  this has stuck states. First-order checks at the boundary restore soundness
  (Theorem 5); separating conversion from checking yields guards, which are
  exactly higher-order contracts between the languages, and the checks on the
  statically typed side can be dropped (Theorems 8, 12, 14 are operational
  equivalences between these formulations).
- *Expressiveness.* The lump embedding can simulate the natural one (section
  4.1). Embedding the terminating ML stand-in into a copy of itself with lumps
  yields a non-terminating language (Theorem 19), because the two sides can
  pack a function type into a lump type and unpack it again.
- *Polymorphism.* The natural embedding extended to polymorphism is type sound
  but not parametric: an untyped term can inspect the value passed at a type
  variable. Parametricity is restored by dynamic sealing of values whose type
  was a type variable (section 6.1).
- *Effects.* Two exception systems are given, one where an exception reaching a
  boundary aborts the program and one where it propagates (Theorems 23, 24).

Basis: documentation (TOPLAS article, sections 2-7).

### 4. Linking types

Linking with a more expressive language changes which programs are
contextually equivalent, so reasoning inside one language is unsound for linked
code. A *linking-types extension* of a source language is an extended language
with two type-level functions, `kappa+` (embed a source type as its default
linking type) and `kappa-` (project back), such that:

1. source terms are a subset of extended terms;
2. `kappa-(kappa+(t)) = t` for every source type `t`;
3. `kappa+` preserves and reflects contextual equivalence: two source terms are
   equivalent at `t` in the source iff they are equivalent at `kappa+(t)` in
   the extended language;
4. a term built only from source constructs that has extended type `t` also
   has source type `kappa-(t)`;
5. the compiler for the extended language should be fully abstract, but need
   only compile source terms.

The worked example links a simply typed lambda calculus with a variant that has
ML-style references, through a target whose computation types record whether
the heap may be used and which exceptions may be raised. Three programs of type
`(int -> int) -> int` (ignore the argument, call it once, call it twice) are
equivalent in the pure language. At the linking type that marks the argument
pure they stay equivalent; at the type that marks argument and result impure
they fall into three classes; at the type "impure argument, pure result" only
the program that never calls its argument is typable. The extra terms of the
extended language are "intended only for reasoning". Applications are also
sketched for linearity, terminating parsers, cost, and gradual typing.

Status: a research proposal; its section "Research Plan and Challenges" lists
implementing fully abstract compilers and combining extensions as open work.

Basis: documentation (arXiv rendering of the SNAPL paper, sections 2, 2.1, 3, 5).

### 5. Realizability after compilation

Patterson, Mushtak, Wagner and Ahmed keep boundary syntax in the sources but
assign meaning after both languages are compiled to one target. The framework
has five steps: boundary syntax; a declarative *convertibility* judgment
`tA ~ tB` whose rules name target glue code `C[tA -> tB]` and `C[tB -> tA]`; a
*realizability model* interpreting each source type as a set of target values,
with an expression relation of target terms that evaluate into it, diverge, or
stop at a well-defined error; *convertibility soundness*; and compatibility
lemmas for every typing rule of both sources.

```text
Lemma 3.1 (Convertibility Soundness)
  If tA ~ tB then  for all (W, P) in E[tA]:  (W, (P, C[tA -> tB])) in E[tB]
              and  for all (W, P) in E[tB]:  (W, (P, C[tB -> tA])) in E[tA].
```

| Case study | Sources and target | What the model forces |
| --- | --- | --- |
| Shared memory | Two simply typed languages with references (one with sums and products, one with arrays), compiled to an untyped stack language | Reference types convert by a no-op, without copying or proxies, only when both pointee types have the *same* interpretation: `ref bool ~ ref int` is sound because compiled booleans and integers are the same set of target values. |
| Affine and unrestricted | An affine language and an ML-like language, compiled to an untyped Scheme-like language | Affine use is enforced dynamically by thunks with a flag that fail on a second force, only where static knowledge is missing; the model tracks "phantom" flags for statically affine variables. |
| Memory management and polymorphism | An ML-like language with collected references and core L3 (linear capabilities, manual memory), same target plus manual allocation | A manually managed linear reference can be handed to the collected language without copying; generic code can be used from the language without polymorphism. |

The type-safety theorems are about compiled programs and allow termination in
a designated conversion (or bounds) failure, so dynamic checks in glue code are
part of the guarantee. Control-flow differences and concurrency are named as
future challenges.

Basis: documentation (arXiv version 2 of the PLDI paper, sections 1-5).

### 6. DimSum: modules, dual non-determinism, wrappers

**Definitions.** A module over an event set `E` is `M = (S, ->, s0)` with
`-> subset of S x (E + {tau}) x P(S)`. Several transitions from one state are a
demonic choice; the states inside one target set are an angelic choice.
Multi-step execution and refinement are:

```text
s --nil-->* Sigma               if  s in Sigma
s --(a ::? k)-->* Sigma         if  exists Sigma'. s --a--> Sigma'  and
                                    forall s' in Sigma'. s' --k-->* Sigma
(M1, s1) <= (M2, s2)   :=coind  forall a, Sigma1. s1 --a--> Sigma1  implies
                                exists Sigma2. s2 ==a==>* Sigma2  and
                                forall s2' in Sigma2. exists s1' in Sigma1. (M1, s1') <= (M2, s2')
```

Refinement is a preorder (Lemma 3.1) and implies whole-program trace inclusion
(Theorem 3.2). It is deliberately branching-sensitive, because linking can
substitute a whole module for a visible event.

**The specification language** has three coinductive constructs, `vis(e); p`,
`exists x:T; p(x)` (demonic) and `forall x:T; p(x)` (angelic), with

```text
(exists x:T; p(x)) --tau--> { p(y) }            one transition per y in T
(forall x:T; p(x)) --tau--> { p(y) | y in T }   one transition to the set
any = ub  :=  forall x:Empty; ...      assume(phi); p  :=  if phi then p else ub
nb        :=  exists x:Empty; ...      assert(phi); p  :=  if phi then p else nb
```

In a goal `M1 <= M2`, demonic choice on the left and angelic choice on the
right mean "consider all"; demonic on the right and angelic on the left mean
"provide one". Admissible commutations: `exists/exists`, `forall/forall`,
`exists x; forall y <= forall y; exists x`, `exists x; vis e <= vis e; exists x`,
`vis e; forall x <= forall x; vis e`. The three converses are inadmissible;
admitting the last would make every specification refine every other.

**Combinators.** Product (a flag in `{E, L, R}` records whose turn it is; turns
change only at visible events), filter (a transducer module rewriting events,
with its own state and both kinds of choice), linking, and stateful wrappers.
Each is monotone for refinement, proved once, for modules that make no
non-trivial angelic choice on a step with a visible event.

**Instantiation.** `Rec` has structured values, calls, and a block-and-offset
memory; its events are `Call`/`Return`, incoming and outgoing, each carrying
the *entire* memory. `Asm` has integers only, a flat memory, jumps and
syscalls; its events are `Jump` (registers and memory) and `Syscall`. The
wrapper from `Rec` to `Asm` translates calling convention, values and memory:

```text
z ~w z        b ~w (if b then 1 else 0)        l ~w  w(l.blockid) + l.offset
Call!(f, v, m) => Jump!(r, m')   iff  r(pc) = a_f,  v ~w r(x0..x8),  |v| <= 9,  m ~w m'
Return?(v, m) <= Jump?(r, m')    iff  r(pc) = r'(x30),  v ~w r(x0),  m ~w m',
                                      r(x19..x29, sp) = r'(x19..x29, sp)
```

The map `w` from block identifiers to addresses is wrapper state that only
grows (a Kripke world, encoded in Iris). Going down is a proof obligation.
Going up, the wrapper cannot know whether a returned `0` is `false`, an integer
or a location, so the choice is angelic; it is discharged when proving that two
wrapped modules linked in `Asm` refine the wrapper of their `Rec` linking,
where the value one module chose demonically is forwarded to the other.

**Results.** A running example is proved by a numbered chain of refinements
(the paper's Figure 4) that replaces syntactic linking by semantic linking,
compiled code by wrapped source modules, assembly libraries by specifications,
and finally reasons in `Rec` alone. A coroutine library written in `Asm` yields
a new `Rec`-level linking operator in which a call can behave as a return. The
compiler has four passes (SSA, Linearize, Mem2Reg, Codegen) and satisfies: if
the compilation of `R` is defined, its `Asm` module refines the wrapper applied
to the `Rec` module of `R` (Theorem 5.1); Mem2Reg needs an additional
`Rec`-to-`Rec` wrapper.

**The CompCert family, as characterised by the DimSum paper.** Compositional
CompCert, CompCertX, CompCertM and CompCertO are described as assuming that all
interoperating languages use the CompCert memory model; for CompCertO the
assumption "may not be crucial" but the approach "has not been applied to a
different memory model", it has one linking operator enforcing well-bracketed
calls, and it studies transition systems without private cross-call state.

**Stated limits.** Safety only (no liveness); sequential interleaving only;
closures, garbage collection, types and concurrency are future work. The
development's guide lists its axioms (functional choice, functional
extensionality, proof irrelevance, excluded middle, uniqueness of identity
proofs) and Coq names: `module`, simulation `sim` (mostly used through an
equivalent `trefines`), wrappers `prepost_mod`, linking `link_mod`, and the
`Rec`-to-`Asm` wrapper `rec_to_asm`.

Basis: documentation (DimSum paper sections 1-7; guide of the Coq development)
+ execution (probe Part A re-checks the laws on finite terms; finding 13).

### 7. Melocoton: the operational model of the OCaml FFI

Melocoton defines small languages `lambda_ML` and `lambda_C`, each with an
ordinary relational semantics and external calls, and builds the combined
language as `link (wrap e) p`: a *wrapper* that runs the ML expression `e` and
implements the runtime primitives, linked with the C program `p`. Only the
wrapper and the linker use dual non-determinism.

Runtime values, blocks and the two GC constraints (abridged from
`theories/interop/basics.v`; Greek identifiers transliterated here and below):

```coq
Inductive lval := Lint : Z -> lval | Lloc : lloc -> lval.
Inductive block :=
  | Bvblock  (vblk : ismut * (vblock_tag * list lval))   (* tags: TagDefault | TagInjRV *)
  | Bclosure (clos_f clos_x : binder) (clos_body : ML_lang.expr)
  | Bforeign (fblk : ismut * option C_intf.val).         (* limited "custom block" *)
(* tag_as_int: TagDefault => 0, TagInjRV => 1, TagClosure => 247, TagForeign => 255 *)
Definition code_int (z : Z) : word := C_intf.LitV (C_intf.LitInt (2*z + 1)).
Inductive repr_lval : addr_map -> lval -> C_intf.val -> Prop :=
  | repr_lint theta x : repr_lval theta (Lint x) (code_int x)
  | repr_lloc theta g a : theta !! g = Some a -> repr_lval theta (Lloc g) (LitV (LitLoc a)).
Definition GC_correct (zeta : lstore) (theta : addr_map) : Prop :=
  gmap_inj theta /\
  forall g blk g', g ∈ dom theta -> zeta !! g = Some blk ->
                   lval_in_block blk (Lloc g') -> g' ∈ dom theta.
Definition roots_are_live (theta : addr_map) (roots : roots_map) : Prop :=
  forall a g, roots !! a = Some (Lloc g) -> g ∈ dom theta.
```

The wrapper state has two modes. In C mode it holds `chi` (logical location to
ML location, or "private"), `zeta` (block store), `theta` (logical location to
current C address) and the set of root addresses; in ML mode `theta` is absent
and roots map to the values they track. Blocks never move or disappear in
`zeta`; the collector is visible only as a change of `theta`.

How ML values become blocks (`is_val`): integers, booleans and unit are
immediates (`true` is 1, `false` and unit are 0); pairs and the left injection
are immutable default-tag blocks, the right injection an immutable block with
tag 1; references and arrays are mutable default-tag blocks with a public ML
location. The encoding is not injective, so the C-to-ML direction must *choose*
the ML value; that choice is angelic, as are freezing a mutable block and
exposing a private block under a fresh ML location. The ML-to-C direction
demonically extends `chi`, materialises immutable ML values as private blocks,
and picks `theta`.

The allocation primitive shows the whole GC model (abridged from
`c_prim_step` in `theories/interop/lang.v`):

```coq
| PrimAllocS rho mem tgnum sz tg roots privmem Y :
    tgnum = vblock_tag_as_int tg -> (0 <= sz)%Z ->
    dom roots = rootsC rho -> repr_mem (thetaC rho) roots privmem mem ->
    GC_correct (zetaC rho) (thetaC rho) -> roots_are_live (thetaC rho) roots ->
    (forall g chi' zeta' theta' a mem',
       chiC rho !! g = None ->
       chi'  = <[ g := LlocPrivate ]> (chiC rho) ->
       zeta' = <[ g := Bvblock (Mut, (tg, repeat (Lint 0) (Z.to_nat sz))) ]> (zetaC rho) ->
       GC_correct zeta' theta' -> repr_mem theta' roots privmem mem' ->
       roots_are_live theta' roots -> theta' !! g = Some a ->
       Y (LitV (LitLoc a)) (WrapstateC chi' zeta' theta' (rootsC rho)) mem') ->
    c_prim_step Palloc [LitV (LitInt tgnum); LitV (LitInt sz)] rho mem Y
```

Three consequences follow. (i) `theta'` is universally quantified and
constrained only by closure and root liveness, so a block not reachable from a
registered root may be absent from `theta'` or at another address. (ii) Root
cells are re-represented under `theta'` (`repr_mem theta' roots privmem mem'`):
the collector updates roots and nothing else. (iii) The premises require every
root cell to hold the representation of a value under the *current* map, so a
root cell holding a stale or arbitrary word leaves the primitive without a rule.

| Wrapper primitive | OCaml FFI counterpart named in the paper or development | GC point |
| --- | --- | --- |
| `alloc` (value-block tags 0 and 1 only), `alloc_foreign` | `caml_alloc`, `caml_alloc_custom` | yes |
| `readfield`, `modify` (mutable value blocks only) | `Field`, `Store_field` | no |
| `read_foreign`, `write_foreign` | reading and writing `Custom_contents` | no |
| `isblock`, `length`, `read_tag`, `val2int`, `int2val` | `Is_block`, `Wosize_val`, `Tag_val`, `Int_val`, `Val_int` | no |
| `registerroot`, `unregisterroot` | what `CAMLparam`, `CAMLlocal`, `CAMLreturn` do | no |
| `callback` (and `main`, which starts the ML program) | running an OCaml closure from C | when ML returns to C |

Every block access goes through a primitive whose rule demands
`repr_lval theta (Lloc g) w`; even `isblock` on a stale address has no rule.

**Roots: model versus one real runtime.** The development defines the macro it
calls `CAMLlocal` as heap allocation plus registration, and `CAMLreturn` as
explicit unregistration plus `free`; it defines no `CAMLparam` (examples root a
parameter by copying it into a `CAMLlocal`):

```coq
Definition CAMLlocal (n : string) (e : expr) : expr :=
  (let: n := malloc (#1) in
    (Var n <- (call: &"int2val" with (Val (#0))));;
    (call: &"registerroot" with (Var n));; e).
Definition CAMLunregister1 ek := (call: &"unregisterroot" with ( ek ) ;; free (ek, #1)).
```

In the OCaml 4.14.1 headers the same names are stack discipline: `CAMLparam0`
saves the head of a list, each rooted variable adds a stack-allocated record
holding the *address of the C local*, and `CAMLreturn` restores the saved head,
dropping all records of the frame at once (abridged):

```c
#define Val_long(x)     ((intnat) (((uintnat)(x) << 1)) + 1)
#define Closure_tag 247
#define Custom_tag 255
#define CAMLparam0() struct caml__roots_block *caml__frame = Caml_state_field(local_roots)
#define CAMLxparam1(x) struct caml__roots_block caml__roots_##x; ... \
    (caml__roots_##x.next = Caml_state_field(local_roots)), \
    (Caml_state_field(local_roots) = &caml__roots_##x), ... (caml__roots_##x.tables [0] = &x), ...
#define CAMLdrop Caml_state_field(local_roots) = caml__frame
```

The integer encoding and the two tag constants of the model coincide with
these headers. The model's roots are, as the paper says, a more elementary API:
it captures "the collector updates this cell" but not the frame list, so
macro-specific mistakes (returning without `CAMLreturn`) have no counterpart.

**Declared omissions.** Direct pointer access to block contents, exceptions and
multithreading are not modelled; custom blocks always store one C pointer and
have no comparison methods; the collector is over-approximated by the demonic
choice of `theta`, not verified; compiler and runtime are assumed correct. A
text search of the development finds no mention of finalizers.

Basis: source (`logsem/melocoton` and `ocaml/ocaml` 4.14.1 at the pinned
commits) + documentation (Melocoton paper sections 2.3-3.1, 6) + derived (the
consequences and the model-versus-runtime comparison) + execution (probe Part B).

### 8. Melocoton: program logic and theorems

There are three Iris logics: one per language, with ordinary weakest
preconditions plus a case for external calls, and an umbrella logic for the
combined language. External functions are specified by *interfaces* (`protocol`
in Coq); `Psi |= p : Pi` says program `p` implements `Pi` assuming `Psi`. The
composition rules are implementation, consequence, embedding of either
language-local logic, and

```text
Link:   Pi |= p1 : Psi     Psi |= p2 : Pi     dom(p1) # dom(p2)
        ---------------------------------------------------------
                     Empty |= p1 (+) p2 : Psi |_| Pi
```

Runtime reasoning uses a token `GC(theta)` naming the current address map.
Every primitive specification takes it; GC points return `GC(theta')` for an
unknown `theta'`, so a fact `repr_lval theta (Lloc g) w` proved earlier is
useless afterwards. A registered root is owned as `a |->root v`, which does not
mention `theta`; unregistering returns the C points-to and a word representing
`v` under the current map. Roots may stay registered forever, so the logic does
not rule out leaks.

*View reconciliation* converts ownership of one piece of state between the ML
view and the block view, given the token (Coq `ml_to_mut`, `mut_to_ml`):

```text
GC(theta) * l |->ML vs                 ==*  exists lvs g. GC(theta) * g |->blk[0|mut] lvs * l ~ g * vs ~ lvs
GC(theta) * g |->blk[0|mut] lvs * vs ~ lvs  ==*  exists l. GC(theta) * l |->ML vs * l ~ g
```

Exclusive ownership guarantees a single view of a given location at a time,
which is what lets each language-local logic keep its usual frame rule.

The two top-level results in Coq (`combined/rules.v`, `combined/adequacy.v`;
binder types elided):

```coq
Lemma combined_correct e p Psi Pret P :
  Psi on prim_names ⊑ ⊥ -> dom p ## prim_names ->
  (⊢ P -∗ WP e at ⟨ ∅ , Psi ⟩ {{ k, ⌜∃ x, k = OVal (LitV (LitInt x)) ∧ Pret x⌝ }}) ->
  prims_proto Psi ||- p :: wrap_proto Psi ->
  ⊥ |- combined_prog e p :: main_proto Pret P.
Lemma main_adequacy_trace (p : mlang_prog combined_lang) Phi :
  (∀ `{!ffiG Σ}, ⊥ |- p :: main_proto Phi na_tok) ->
  umrel.trace (prim_step p) (LkCall "main" [], σ_init)
    (λ '(e, σ), ∃ x, to_outcome e = Some (OVal (code_int x)) ∧ Phi x).
```

The first joins a language-local proof of the ML client against an interface
with a language-local proof that the C program implements the wrapped interface
from the runtime primitives. The second is adequacy: the linked program is safe
and can only end in an integer satisfying the postcondition. Adequacy is the
delicate part: the weakest precondition existentially quantifies the
angelically chosen successor set inside a step-indexed logic, and replaying
those choices outside needs witness extraction that ordinary step-indexing does
not provide; hence the development is built on Transfinite Iris.

Case studies: a buffer and compression library binding, structural equality
written in C, a list alternating OCaml and C blocks, Landin's knot through the
FFI, an event-listener type storing OCaml callbacks in C memory, and a logical
relation showing C-implemented functions safe to use from well-typed ML code.

At the pinned commit: 111 Coq files and 23,316 lines under `theories/`; no
`Admitted.` or `admit.` and no `Axiom` declaration; the package file pins Coq
8.16.1 and commits of an Iris fork with parametric step-indexing; the
documented axioms are those of Transfinite Iris (propositional and functional
extensionality, proof irrelevance, excluded middle, a choice principle).

Basis: documentation (Melocoton paper sections 2.4, 2.5, 4, 5) + source
(`prims_proto.v`, `update_laws.v`, `combined/rules.v`, `combined/adequacy.v`,
`OVERVIEW.md`, `coq-melocoton.opam`; counts by text search, not by building).

### 9. The polarity of dual non-determinism differs between DimSum and Melocoton

Both use a step relation of shape `state -> (set of states) -> Prop`, and both
quantify "there is a step to a set, and for all members of the set". The
judgments built on it are dual, and so are the names.

| | DimSum module | Melocoton `umrel` (wrapper, linker) |
| --- | --- | --- |
| Top-level judgment | "may exhibit trace `k`" and refinement `impl <= spec` | "all executions end in `X`" (weakest precondition, adequacy) |
| Choice *among* transitions | demonic | angelic (the proof picks the rule instance and set) |
| Choice *inside* the target set | angelic | demonic (the proof covers every member) |
| No transition at all | NB, no behaviour: refines everything | stuck: undefined behaviour; the weakest precondition demands a step |
| Transition to the empty set | UB: refined by everything | NB, vacuous: the language interface forbids it for unfinished expressions (`prim_step_no_NB`) and allows it only for finished outcomes |
| Example | the `Asm`-to-`Rec` value choice is inside a set | the GC outcome `theta'` is inside the set `Y` of `PrimAllocS`; the C-to-ML value choice is an existential premise |

Basis: documentation (DimSum sections 3.1-3.2; Melocoton section 4.3) + source
(`multirelations.v`, `mlanguage/`, `interop/lang.v`) + derived (the
side-by-side reading; neither paper states the comparison).

### 10. VeriFFI: a verified FFI without a multi-language semantics

VeriFFI connects Coq programs compiled by CertiCoq with C functions verified in
VST. Foreign types and functions are declared as Coq axioms with *functional
models*; from a reified description of the (possibly dependent) Coq type
VeriFFI derives a VST function specification, and proving the C function
against it justifies the axiom. No combined language is defined: CertiCoq's
output and the foreign code are both C, so "all of our reasoning about foreign
functions can be achieved within the Verifiable C program logic".

- Representation: constant constructors are unboxed `2n+1`; boxed constructors
  are aligned pointers to records whose header holds length and tag (the
  repository's `c/values.h` has the same `Val_long`, `Is_long`, `Is_block` as
  OCaml). Because of sharing, the heap is described propositionally as a
  labelled graph rather than as a separating conjunction of subtrees.
- The key type class `InGraph A` asks, per Coq type, for a predicate
  `graph -> outlier_t -> A -> rep_type -> Prop` and for its invariance: a field
  `is_monotone` (adding nodes) and a field `gc_preserved` (if the predicate
  holds in `g` for a value reachable from the roots, it holds in the
  post-collection graph `g'` at the relocated position, given a label-preserving
  isomorphism of the reachable subgraphs).
- A generated specification takes the whole collected heap and thread
  information, requires each argument to be in the graph, and returns a new
  graph, isomorphic on the old roots, in which the result represents the
  functional model applied to the arguments (`fn_desc_to_funspec`).
- Guarantee and conditions: type safety and partial correctness of foreign
  functions. The soundness section begins "Assuming that the CertiCoq compiler
  is correct", says the composed end-to-end theorem is under construction and
  that the theorem for open programs "has not yet even been stated"; proofs for
  the mutable-array and input/output monads are future work.
- At the pinned commit the Coq files contain 59 textual `Admitted.` and 167
  `admit.` occurrences (nine `Admitted.` in
  `verification/proofs_library_general.v` alone); counted, not classified.

| | Melocoton | VeriFFI |
| --- | --- | --- |
| High-level side | toy ML with mutable state, verified in a separation logic | all of Gallina, verified directly in Coq |
| Low-level side | toy C in Iris | CompCert C in VST |
| Combined semantics | yes (wrapper plus linking, dual non-determinism) | none needed |
| Collector | abstract, non-deterministic model | a verified generational collector and its graph model |
| Callbacks into the high-level side | yes, with a proof rule | closures can be called from C; proofs about effectful monads incomplete |
| End-to-end statement | adequacy theorem, no admitted proofs found | conditional on unfinished compiler theorems |

Basis: documentation (VeriFFI paper sections 1-3, 13-15) + source
(`CertiCoq/VeriFFI` at the pinned commit: `library/meta.v`,
`verification/specs_general.v`, `c/values.h`; counts by text search).

### 11. Robust property preservation and its relation to full abstraction

Setting: source and target each have partial programs `P`, contexts `C`,
linking `C[P]`, and a trace semantics for whole programs; a compiler maps `P`
to `P↓`. The paper assumes the same traces in source and target, and that any
program links with any context. `P` *robustly satisfies* a property when
`C[P]` satisfies it for every context. Each criterion has a property-full form
and an equivalent property-free form that shows what a proof must construct:

```text
RTP / RTC   forall P CT t.  CT[P↓] ~> t   =>  exists CS.  CS[P] ~> t
RSP / RSC   forall P CT m.  CT[P↓] ~> m   =>  exists CS.  CS[P] ~> m        (m a finite prefix)
RHP / RHC   forall P CT.  exists CS.  forall t.  CT[P↓] ~> t  <=>  CS[P] ~> t
RSCHC       forall P CT.  exists CS.  forall t.  CT[P↓] ~> t   =>  CS[P] ~> t
RHSC        forall P CT o.  o <= Behav(CT[P↓])  =>  exists CS.  o <= Behav(CS[P])   (o a finite set of prefixes)
R2HSC       as RHSC with observations of two prefixes
```

The same shapes appear in the Coq development, for example

```coq
Definition RSC : Prop :=
  forall (P:par src i) C' t, sem tgt (C' [ P ↓ ] ) t ->
    forall m, (prefix m t -> exists C t', sem src (C [ P ] ) t' /\ prefix m t').
```

with `RTC`, `RHC`, `R2HSC` alongside, proved equivalences `RSC_RSP`, `RTC_RTP`,
`RHC_RHP`, `R2HSC_R2HSP` and the implication `R2HSC_RSC` in `Criteria.v` (no
`Admitted.` in that file; ten in three other files of the repository).

What the quantifier order means in practice, in the paper's words: criteria
for trace properties "only require sandboxing the context ... and protecting
the internal invariants of the program from it, i.e., only data integrity";
those for hyperproperties "require additionally hiding the data of the program
from the context, i.e., data confidentiality"; those for relational
hyperproperties "additionally hiding the code". For safety a different source
context may explain each bad prefix and "can guess any secret"; for
2-hypersafety (which contains termination-insensitive noninterference) one
source context must explain two runs, so guessing no longer works.

Separations and collapses proved: RTP implies RSP but not conversely (Theorem
2.1); RTP does not imply robust preservation of termination-insensitive
noninterference (Theorem 3.1); K-hypersafety preservation does not imply
(K+1)-hypersafety preservation (Theorem 3.2); RHP does not imply robust
2-relational safety preservation (Theorem 4.1); robust hyperliveness
preservation is equivalent to RHP; with source reflection or internal
non-determinism several stronger criteria collapse onto weaker ones.

Relation to full abstraction, taken as robust trace-equivalence preservation
for determinate languages: it follows from robust 2-relational relaxed safety
preservation under determinacy and input totality (Theorem 5.1), but it implies
none of RSP, the dense-property criterion, or noninterference preservation,
even together with compiler correctness (Theorem 5.2). The witness compiles
`f(x:Bool) |-> e` to `f(x:Nat) |-> if x<2 then e↓ else if x<3 then f(x) else 42`:
the extra behaviour does not depend on `e`, so no target context separates two
compiled programs, yet "never output 42" is lost. RTP is also shown
incomparable with two compositional compiler-correctness criteria.

Proof techniques shown to transfer: a universal embedding proves the strongest
criterion for a typed-to-untyped first-order translation; trace-based
back-translation of finite sets of finite prefixes proves robust
finite-relational relaxed safety preservation and all criteria below it.

Basis: documentation (arXiv version 6 of the CSF paper, sections 1-6) + source
(`Criteria.v`, `Robustdef.v`, `Properties.v` at the pinned commit) + execution
(probe Part D re-runs the Theorem 5.2 witness).

### 12. Well-bracketed control flow as a target-only observation

Dreyer, Neis and Birkedal give the pair

```text
e1 = let x = ref 0 in  fun f -> (x := 0; f (); x := 1; f (); !x)
e2 =                   fun f -> (f (); f (); 1)
```

and show that it is not an equivalence in a language with first-class
continuations: a context captures the continuation of the *second* call to `f`
and, from inside the first callback of a nested call (when `x` is 0), throws
back to it, so `e1` yields 0 and `e2` yields 1. Without `call/cc` computations
are well-bracketed and the authors treat the pair as an equivalence, extending
their state-transition-system method to exploit well-bracketing. An FFI target
in which a foreign caller can transfer control to an older return address is in
the position of that context, even if neither source language has
continuations: one concrete instance of the statement opening the Abate et al.
paper that linked target code may "read and write the compiled program's data
and code, jump to arbitrary memory locations, or smash the stack".

StkTokens (abstract only examined) targets this on a capability machine: a
calling convention based on linear capabilities that "provably enforces
well-bracketed control flow and local state encapsulation", proved through a
"fully abstract overlay semantics".

Basis: documentation (JFP article section 5; StkTokens abstract) + derived (the
transfer from continuations to FFI return addresses) + execution (probe Part C).

### 13. Executable probe

`support/verify_dimsum_and_melocoton_wrappers.py` (Python 3.10 or newer,
standard library only, about one second) runs 46 checks and exits 0 only if all
hold; `support/expected_output.txt` is its complete output.

| Part | Model | Result |
| --- | --- | --- |
| A | DimSum transition rules and refinement on a generated family of 132 finite acyclic specification terms | UB is top, NB is bottom; reflexive; transitive on a 48-term subfamily (52,656 instances); the five admissible commutations hold and the three converses fail; refinement implies trace inclusion on all 5,693 related pairs; two trace-equal terms are not refinement-related. |
| B | Block store, address map, root set and C cells; at each GC point *all* admissible new maps are enumerated (any reachability-closed live set containing the rooted blocks; each survivor stays or moves) | Glue copying a field into a new block: unrooted local, 4 of 7 executions stuck; rooted cell re-read after the allocation, 6 of 6 correct; rooted but using a copy taken earlier, 3 of 6 stuck. With an allocating callback first: no roots, 920 of 984 stuck; one of two locals rooted, 512 of 768 stuck; both rooted, 512 of 512 correct. |
| B, reuse | As B, but a moved block may take a vacated address | Unrooted: of 23 executions 9 are stuck and 9 finish with the *wrong* block stored; rooted: 20 of 20 correct. Without reuse nothing is silently wrong. |
| C | The pair of finding 12 as a component `g`; contexts enumerated to 6 moves and call depth 3 under five disciplines | Well-bracketed contexts: `g` never returns 0, variants indistinguishable. Free choice of saved continuation: the shortest attack (call; return from the first callback; call; return to the outer second callback) yields 0. Accepting any issued token, or any token of a still-pending frame, does not stop it. One-shot tokens checked in LIFO order restore both facts, with 79 fail-stop rejections in the bound. |
| D | The Theorem 5.2 chain over 9 source programs, target inputs 0 to 5 | Source-equal programs stay target-equal; compiled code agrees with the source on valid inputs; inputs 3, 4, 5 output 42 although the source robustly never does. |

Two observations go beyond the cited sources. In the model of finding 7 a stale
address is not always stuck: if the address was reused, a primitive's decoding
premise is satisfied by a *different* block and the step is defined but wrong;
only a specification naming the intended block rejects it. And for return
tokens, unforgeability is not the relevant property; ordering and single use
are.

Discriminating power was checked with eight single-edit mutations (exact
strings in `support/mutation_table.json`): every mutant exits non-zero with the
expected checks failing, for example a collector that leaves root cells
untouched fails the rooted-glue checks.

Basis: execution (Python 3.13.15 on Linux, deterministic) + derived
(interpretation). The models were written for this report, not extracted from
Coq.

### 14. Engineering rules that follow

1. Choose the preserved property class before the mechanism: integrity-only
   goals have per-trace proofs and tolerate fail-stop dynamic checks;
   confidentiality goals forbid the foreign side from reading what a source
   context could not; equivalence preservation alone guarantees neither.
2. In a wrapper, quantify universally over what the peer or runtime does, and
   let the prover supply reconstructed high-level structure, typically when two
   wrapped components are linked and one side's choice can be forwarded.
3. Against a moving collector, treat every allocation primitive, callback and
   call into the managed side as invalidating all words that denote managed
   blocks; keep them only in registered root cells and re-read after each point.
4. Convert a reference type without copying only if both interpretations of the
   pointee coincide; otherwise copy, proxy, or check.
5. A dynamic return check must be ordered and one-shot.

Basis: derived (from findings 11; 6 and 9; 7 and 13; 5; 13 respectively).

## Boundaries

- **Not examined.** The Coq sources of DimSum (only the paper, the artifact
  record and the development's guide, the last from a moving branch whose
  commit could not be resolved). The texts of CompCertM, CompCertO, Conditional
  Contextual Refinement, Compositional CompCert, and the Patrignani, Ahmed and
  Clarke survey of secure compilation (metadata only; statements about the
  CompCert family are DimSum's characterisations). The body of the StkTokens
  paper. The OCaml 5 runtime. The technical appendices of the PLDI 2022 and
  Melocoton papers. No Coq development was compiled and no `Print Assumptions`
  was run.
- **Unknown.** Whether the admitted proofs counted in the VeriFFI repository
  lie on the path of its headline examples. Whether Melocoton's adequacy
  argument extends to exceptions crossing the FFI, threads, or a multicore
  runtime. Whether linking types have been realised for a full language. Which
  commit of the DimSum repository corresponds to the artifact record.
- **Known not to apply.** DimSum's instantiation is `Rec`, `Asm` and a
  specification language: no C, closures, collector or concurrency, and no
  liveness. Melocoton does not model the `CAMLparam` frame list, direct access
  to block contents, exceptions, threads, or the comparison and finalisation
  hooks of custom blocks, and verifies no collector. Full abstraction, as
  trace-equivalence preservation, does not imply robust safety preservation.
  The realizability guarantee is type safety up to designated conversion
  failures, not equivalence preservation. The probe's token wrapper is not
  StkTokens: it is a check in an abstract machine without memory and says
  nothing about local-state encapsulation or side channels.
- **Unsupported.** In the Melocoton wrapper there is no transition for
  allocation with a tag other than the two value-block tags, for writes to
  immutable blocks, or for a primitive applied to a word that represents no
  value under the current map. The robust-preservation criteria assume
  identical trace alphabets in source and target and unrestricted linking.
- **Not established.** That any production toolchain satisfies these theorems;
  that the rooting discipline checked in the probe implies safety of real glue
  code (the model has no macros, write barrier, or direct field access); that
  CompCertO cannot handle different memory models (DimSum says only that it has
  not been done); that a passing probe validates the Coq proofs.

## Evidence

All evidence was acquired on 2026-11-19.

- **Metadata.** Crossref REST records (`https://api.crossref.org/works/<DOI>`)
  for every DOI in finding 1 except the LIPIcs DOI, which was confirmed on
  `https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SNAPL.2017.12`;
  Zenodo record `7306312`.
- **Paper texts.** Matthews-Findler: a hosted copy of the TOPLAS article
  carrying journal, volume, article number and DOI
  (`https://ics.uci.edu/~lopes/teaching/inf212W12/readings/mathews.pdf`).
  Linking types: `https://arxiv.org/html/1711.04559v1`. PLDI 2022: arXiv
  `2202.13158v2`. DimSum: `https://iris-project.org/pdfs/2023-popl-dimsum.pdf`
  (Article 27, with appendices). Melocoton:
  `https://cs.au.dk/~birke/papers/melocoton-2023.pdf` (Article 247). VeriFFI:
  `https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf` (Article 24). Abate
  et al.: arXiv `1807.04603v6`. Dreyer, Neis, Birkedal:
  `https://people.mpi-sws.org/~dreyer/papers/stslr/journal.pdf`. StkTokens:
  abstract page of arXiv `1811.02787v1`.
- **`logsem/melocoton` at `039dae32893a33bc70d668a7abcd25d54587dc3c`**
  (committed 2025-04-28), under `theories/`. `interop/basics.v`: `lval` 49-51,
  `tag_as_int` 78-83, `block` 106-110, `GC_correct` 249-255, `roots_are_live`
  257-258, `code_int` 262, `repr_lval` 264-269, `is_val` 294-330.
  `interop/state.v`: `wrapstateC` 13, `wrapstateML` 25. `interop/lang.v`:
  `ml_to_c_heap` 85-122, `c_to_ml_heap` 273-298, `c_prim_step` 344-445
  (`PrimAllocS` 348-364), `c_prim_step_no_NB` 453, `prim_step_mrel` 525-587.
  `interop/prims.v`: `prim` 5-11. `interop/prims_proto.v`: `wrap_proto` 20-32,
  `registerroot_proto` 53-61, `alloc_proto` 136-145, `callback_proto` 175-187.
  `interop/update_laws.v`: `ml_to_mut` 18, `mut_to_ml` 30. `interop/gctoken.v`:
  `GC` 57. `c_interop/notation.v`: `CAMLlocal` 5-8, `CAMLunregister1` 46.
  `combined/rules.v`: `combined_correct` 37. `combined/adequacy.v`:
  `main_adequacy_trace` 258-261. `multirelations.v`: `umrel` 10-13.
`mlanguage/mlanguage.v`: `prim_step_no_NB` 230. `mlanguage/weakestpre.v`:
`wp_pre_cases` 26-39. Also `PAPER.md`, `OVERVIEW.md`, `coq-melocoton.opam`.
- **`ocaml/ocaml` at `99cb5d93fc30f1a6f3e69f5aa5d2063994d33a93`** (4.14.1).
  `runtime/caml/mlvalues.h`: 70-71, 75-76, `Closure_tag` 244, `Custom_tag` 365.
  `runtime/caml/memory.h`: `struct caml__roots_block` 253-258, `CAMLparam0`
  294-295, `CAMLxparam1` 343-353, `CAMLlocal1` 425-427, `CAMLdrop` 454,
  `CAMLreturnT` 461-465.
- **`CertiCoq/VeriFFI` at `7e8cd8e7b631be066407f86c82ff60b6fc63ae0b`**
  (committed 2024-12-31). `library/meta.v`: `InGraph` 49-75, `is_in_graph` 77,
  `reified` 148. `verification/specs_general.v`: `fn_desc_to_funspec` 83.
  `c/values.h`: 64-70.
- **`secure-compilation/exploring-robust-property-preservation` at
  `c68187cbaba763d88cbb3509df4ca9cf49cc6338`** (committed 2026-03-22).
  `Criteria.v`: `RTC` 19, `RSC` 73, `RSC_RSP` 81, `RHC` 197, `R2HSC` 315,
  `R2HSC_RSC` 337. `Robustdef.v`: `RTP` 21, `RSP` 78, `RHP` 94, `R2HSP` 178,
  `RTEP` 366. `Properties.v`: `Safety` 21, `H2Safe` 298.
- **DimSum guide.** `README.md` of `https://gitlab.mpi-sws.org/iris/dimsum`,
  branch `master`, as served on the observation date.
- **Execution.** Probe, output and mutation table are preserved under
  `support/`.

This report's own synthesis, not source fact: the tables of findings 2 and 9,
the model-versus-runtime comparison in finding 7, the transfer argument of
finding 12, the probe, and finding 14.

## Revalidation

- **Cheapest check.** From the corpus root run
  `python3 -B reports/semantic-multi-language-interop-dimsum-melocoton-and-linking-types/support/verify_dimsum_and_melocoton_wrappers.py`
  and compare with `support/expected_output.txt` (expect `ALL CHECKS PASSED`,
  exit 0). This revalidates the bounded models only. To confirm the checks
  still discriminate, apply each entry of `support/mutation_table.json` to a
  scratch copy and expect a non-zero exit.
- **Melocoton drift.** For another revision, diff `tag_as_int`, `code_int`,
  `GC_correct` and `roots_are_live` in `theories/interop/basics.v`,
  `Inductive prim` in `theories/interop/prims.v`, and `c_prim_step` in
  `theories/interop/lang.v`. A new primitive, a third GC constraint, or new
  block kinds change findings 7-9. Search for `Admitted.`.
- **Runtime comparison.** For another OCaml version re-read `Val_long`,
  `Closure_tag`, `Custom_tag` and the `CAMLparam`/`CAMLreturn` macros under
  `runtime/caml/`; finding 7 compares against 4.14.1 only.
- **VeriFFI status.** Re-count `Admitted.` and look for a completed CertiCoq
  end-to-end or open-program theorem; either changes finding 10.
- **Criteria.** Confirm that `RSC`, `RHC` and `R2HSC` in `Criteria.v` keep the
  quoted quantifier shapes and that the equivalences still end in `Qed`.
- **Coordinates.** Re-resolve the DOIs of finding 1.
- **No cheap check exists** for the DimSum statements (they rest on the paper;
  checking against Coq means obtaining artifact `10.5281/zenodo.7306312`) or
  for the syntactic, linking-type and realizability results (paper proofs).
