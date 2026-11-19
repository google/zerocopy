# Content-Addressed Typed IR Stores: Definition Hashing, Alpha-Equivalence, Interface Hashes, Scheme Migration, and Erasure

## Summary

A content-addressed program store names each elaborated definition by a hash of a canonical, name-free form. Five things determine whether such names are sound and durable, and the examined systems make different choices on each:

- **What is erased before hashing.** Unison hashes resolved references, positional variable indices, literals and the definition's type; it does not hash binder names, source annotations, human-readable names, or the order of mutually recursive bindings, effect sets and data constructors. Every digest is SHA3-512 over a token stream whose first byte is a scheme-version tag (`2` at the pinned revision).
- **How recursion is closed.** Unison hashes a strongly connected component as one unit and identifies a member as `(component hash, position)`. Position comes from sorting members by a hash in which all in-cycle references are indistinguishable; when two members tie, the order silently falls back to variable-name order, so the algorithm reports `IncompleteElementOrderingError` and the top-level callers abort. A port of the algorithm shows that proceeding past a tie makes the hash depend on names. GHC's interface fingerprinting had a long-lived bug of the same family and now sorts a recursive group by declaration name instead, which is sound only because GHC's identity is name-based.
- **Alpha-equivalence is easy for closed definitions and hard for subterms.** Index-based hashing of a whole closed definition is alpha-invariant. Hashing every subterm in a global de Bruijn encoding is both incomplete and unsound for subterm identification (reproduced by execution). E-summaries fix this in `O(n (log n)^2)` with a proved collision bound of `5|e|^3 * 2^-b`; a context-sensitive refinement runs in `O(n log n)`.
- **No examined interface hash is simultaneously body-invariant and safe for cross-definition optimization unless exposure of bodies is recorded separately.** Unison's reference and rustc's Strict Version Hash both cover bodies. GHC's per-declaration ABI fingerprint includes a body only when an unfolding is exported. OCaml keeps separate digests for `.cmi` interfaces and `.cmx` implementation information. C++ has no hash at all: the one-definition rule requires token-identical definitions with no diagnostic required outside named modules.
- **The hashing scheme and the elaborator are part of the ABI, and immutability conflicts with erasure.** Dhall's changelog records normal-form changes that perturbed every affected hash; Unison's codebase migrations record two repairs caused by hashes that were not pure functions of content; Git's SHA-256 transition relies on a locally generated bidirectional name table and on conversions that round-trip. Reachability-based collection (Git, Nix, Unison) is not erasure. A tombstone that keeps a name and drops the body preserves Merkle verification of ancestors, but an unsalted name of low-entropy content still re-identifies that content.

## Applicability

The report compares mechanisms across independent systems and derives design rules for a store of typed intermediate-representation definitions. It is not a description of one integrated system.

- **Unison** findings are source readings of `unisonweb/unison` at commit `b5c5188d99f31820d0cc012f194948d2876c14e7`, mainly the `unison-hashing-v2` package (whose token stream is prefixed with hashing version `2`), the type checker's name-resolution driver, the SQLite codebase schema and migrations, and the merge package. No Unison binary was executed. The official "big idea" documentation page was read on 2026-11-19 for the stated intent.
- **Alpha-equivalence** findings come from arXiv:2105.02856v1 (full text), its supporting repository at `9deb049bce534c8b630c85102cf24da78619441a`, and the abstract of arXiv:2401.02948v3.
- **E-graph** findings are source readings of `egraphs-good/egg` at `73975c9819efb4af2f3c6c1b44fa53f8c5742574` (crate version `0.11.0`).
- **Interface-hash** findings are source readings of `rust-lang/rust` at `b0b600668bb9b4a897e2299b0a44289d42276545`, `ghc/ghc` at `83038fbee5efea8e3ebd5090b2ff5537462e169d`, `ocaml/ocaml` at `d921d1e86c56baa7b30e890ced455c12255793f5`, and the C++ working draft at `0ab325d274a1ad610cef1099ec528fb0bed6ee18`. These are development-branch heads on the observation date, not releases; behaviour of released toolchains may differ, and the rustc mechanism described is controlled by an unstable `-Z` option.
- **Migration and collection** findings are documentation and source readings of `git/git` at `e1ec09b23c8e0deb21a0b95ac5996422277395d4`, `NixOS/nix` at `6965392507e19998de706aa15e514f81e9b7ce11`, `dhall-lang/dhall-lang` at `56b0997a4800bfc815ea221529a6bb2bfd6723dc` (standard version `23.1.0`), and `multiformats/multihash` at `b43ec1026a610fa87878e53b3daecf3a14b3ef6f`.
- **Execution** evidence is one self-contained Python probe reproduced in full under Findings. It executes *models*: a port of the control structure of Unison's component hashing (not byte-compatible with Unison), a toy build cache, a toy migration and a toy Merkle store. It characterizes the algorithms and invariants, not the behaviour of any upstream binary.

Statements labelled `derived` extend beyond what any subject states; the reasoning is given in place.

## Findings

### 1. Model and vocabulary

```text
Sigma |- d  ==>  core(d) : tau              elaboration: names become references, the type is explicit
ref ::= builtin(name) | derived(h, i)       h names a recursive component, i a position inside it
eta_impl(C) = H(v || canon(core(C)))        C a strongly connected component, v the scheme version
eta_ifc(d)  = H(v || canon(tau) || exposed(d))
```

`canon` removes everything that must not affect identity; `exposed(d)` is whatever a dependent may observe beyond the type (an inlinable body, a layout, a specialization rule). The five design axes are: (a) the definition of `canon`; (b) how `C` is ordered so that `i` is well defined; (c) whether dependents key on `eta_impl` or `eta_ifc`; (d) what happens when `v`, `H`, `canon` or the elaborator changes; (e) how an entry leaves the store.

### 2. Unison definition hashing at the pinned revision

Basis: source (all of section 2 unless marked otherwise).

#### 2.1 Token stream

`Unison.Hashing.V2.Tokenizable.accumulate` feeds SHA3-512 with the version token followed by the encoded tokens:

| Token | Encoding fed to SHA3-512 |
|---|---|
| `Tag w8` | one byte |
| `Nat w64`, `Int i64`, `Double d` | 8 bytes big-endian |
| `Text t` | 8-byte big-endian length, then UTF-8 bytes |
| `Bytes b` | 8-byte big-endian length, then bytes |
| `Hashed h` | the raw digest bytes, no length prefix |

`hashingVersion = Tag 2` is prepended to every `accumulate` call. The source comment gives the reason: "if a change to the hashing function changes the hashes for _some_ values, it should change it for _all_ values so that we don't have collisions between different hashing function versions." A further comment on the `Tokenizable` class states that "changing the hash of a value is a major breaking change and requires a complete codebase migration."

Each syntactic layer starts with a sort tag so that sorts cannot collide: types use leading `Tag 0`, terms `Tag 1`, declarations `Tag 2`.

#### 2.2 What is and is not part of identity

| Ingredient | In the hash? | Mechanism |
|---|---|---|
| Bound variable names | no | `hash' env (Var' v)` hashes `Nat i`, the index of the first environment entry binding `v`; `Abs'' v t` only pushes `Right v` |
| Source annotations and locations | no | comment on `hash`: "We ignore annotations in the `Term`, as these should never affect the meaning of the term." |
| Human-readable names of definitions | no | top-level names are free variables replaced by `ReferenceId`s; documentation: "names are just separately stored metadata that don't affect the function's hash" |
| Order of `let rec` bindings | no | `TermLetRec` goes through `hashCycle`; comment: "we use `hashCycle` to ensure result is independent of let binding order" |
| Order of plain `let` bindings | yes | comment: "here, order is significant, so don't use hashCycle" |
| Order of effects in an effect set | no | `TypeEffects es` sorts member hashes |
| Order and names of data constructors | no | `toABT` keeps only the constructor types; the declaration layer `Constructors cs` sorts their hashes |
| Dependencies | yes | `TermRef`, `TermConstructor`, `TermRequest`, `TypeRef` carry references |
| The definition's type | yes | `hashTermComponents` rewrites each term to `TermAnn e typ` before hashing |
| Structural versus unique declaration | yes | `Modifier` tokens: `Structural` is `[Tag 0]`, `Unique txt` is `[Tag 1, Text txt]` |
| Builtins | by name only | `ReferenceBuiltin txt` is `[Tag 0, Text txt]` |
| Record field names, text and numeric literals | yes | hashed as `Text`, `Nat`, `Int`, `Double` tokens |

Consequences:

- Two `Structural` declarations that differ only in the names of the type and of its constructors have the same reference; a `Unique` declaration is distinguished solely by its GUID text. The parser obtains that text from a callback `uniqueTypeGuid :: Name -> m (Maybe Text)` ("if the function returns a Just, that GUID is used; otherwise, a random one is generated"), so nominal identity is recovered by a name-keyed lookup outside the hash. Basis: source + derived.
- A builtin's identity is its name. A change in a builtin's behaviour does not change any hash. Basis: derived from the token definition.
- `hashTermComponentsWithoutTypes` exists and is documented as "shouldn't be used when storing terms in the codebase, as it doesn't incorporate the type into the hash." The stored identity therefore distinguishes one body at two types.
- The term-level case `TermRef (ReferenceDerived h 0)` returns `h` itself, while position `i > 0` yields `accumulate [Tag 1, Hashed h, Nat i]`. The source comment calls references "transparent" ("`x = 1 + 1` and `y = x` hash the same"). This is a statement about expression hashes. The stored reference of `y` is still different from that of `x`, because a reference is the component hash computed in 2.3 and the stored term is wrapped in a type annotation. Basis: derived from the cited functions.

#### 2.3 Hashing a set of top-level definitions

```text
hashComponents(defs):                        -- requires: no free variables other than the defs
  for each strongly connected component C of defs, dependencies first:
    C'  := C with earlier definitions replaced by derived(h, i) references
    (h, order) := hashComponent(C')
    assign derived(h, i) to order[i]

hashComponent(C):
  names  := keys of C in ascending variable order
  key(m) := hash'( [Left names], body(m) )   -- every in-cycle variable hashes as the same index
  perm   := stable sort of members by key    -- ties keep ascending variable order
  env    := [Right m | m in perm]
  hs     := [hash'(env, body(m)) | m in perm]
  hname(m) := accumulate( Tag 1 : map Hashed hs ++ [Hashed (hash'(env, var m))] )
  order  := members sorted by hname
  h      := accumulate( map Hashed (sorted hname values) )
```

`hash'` is the recursive hash in which a variable is `accumulate [Nat i]` with `i` the index of the first environment entry that binds it; an entry `Left vs` binds every variable in `vs`.

#### 2.4 Failure case: members that tie under the collapsed-cycle key

`doHashCycle` detects members with equal `key` and emits `IncompleteElementOrderingError`, whose rendered text says "This happens when multiple definitions in a mutually recursive cycle have a very similar structure" and suggests adding a distinguishing expression. Handling differs by caller:

| Caller | Behaviour on a tie |
|---|---|
| Declaration hashing (`hashDecls0`) | `crashOnHashingWarning` throws |
| Typechecked-file term hashing (`typecheckedUnisonFile`) | `crashOnHashingWarning` throws |
| `let rec` inside a term (`hashCycle` within `hash'`) | warning discarded; comment: "we don't want to error on that when hashing internal let-bindings" |

Basis: source.

Why the tie matters is shown by the probe (section 9, lines `P2`). With `a = f b b; b = f a b` both members collapse to `f * *`. Proceeding with the stable-sort fallback yields `#5830368c3f`; renaming `a -> q, b -> p` (so that ascending name order swaps the members) yields `#7844ca73a7`. The two components are alpha-equivalent, so past a tie the "content" address depends on names. The same probe shows the scheme is rename-invariant when keys are distinct, and that an automorphic tie (`a = g b; b = g a`) happens to produce a name-independent hash while still raising the warning. Basis: execution of a port + derived. For the discarded-warning `let rec` path, the fallback order is the binding order in the term, so two alpha-equivalent terms that list tied bindings in different orders can hash differently; this was not executed against Unison.

#### 2.5 Constructor numbering

`hashDecls` "normalize[s] the order of the constructors based on a hash of their types" with a stable `sortOn`. Constructors with identical types therefore keep declaration order, while the declaration hash (which sorts constructor hashes) is the same for either order. A constructor reference is `(type reference, constructor index)`, so for a declaration with same-typed constructors (an enumeration, for example) the hash does not determine which source name is attached to index 0. Because names are metadata this is consistent, but it means a `Structural` enumeration and the same enumeration with its constructors listed in another order are one type under two namings. The source also records: "technical limitation, this implementation gives diff results if ctors have the same FQN as one of the types." Basis: source + derived; not executed.

#### 2.6 Type-directed name resolution precedes hashing

`synthesizeAndResolve` type-checks a term, then `typeDirectedNameResolution` examines unresolved names: "There's more than one name that matches, but only one that typechecks. Substitute that one into the code" and "No match at all. Throw an unresolved symbol at the user." Resolutions are substituted with `substBlanks` and synthesis is re-run until no resolution remains. `typecheckedUnisonFile` then hashes the resulting components together with their inferred types. Identity is therefore a function of the *elaborated* term: the same source text hashes differently in namespaces where a short name resolves, by type, to different references. The hashing code still has a case for an unresolved placeholder (`B.Recorded (B.Resolve _ s)` hashes the string `s`); whether any storing path can reach it was not examined. Basis: source + derived.

#### 2.7 Neighbouring hashes that are deliberately not identity

- **Syntactic hash for merge.** `Unison.Merge.Synhash` hashes a definition "after substituting references to other terms and decls with names from a pretty-print environment" to decide "whether an update was performed by a human, or was the result of auto-propagation." This exists because a dependent's reference changes whenever a dependency's does.
- **Store schema.** `hash_object(hash_id, object_id, hash_version)` carries the comment "hashes are UNIQUE, many hashes correspond to one object": the object table is not keyed by a single scheme.

### 3. Hashing modulo alpha-equivalence

#### 3.1 Closed definitions versus all subterms

For a closed term, replacing each bound occurrence by a binder index gives equal encodings exactly for alpha-equivalent terms, and one linear pass hashes it. This is what section 2 does for whole definitions. The hard problem is assigning hashes to *every subterm* so that equal hashes identify alpha-equivalent open subterms, as needed for common-subexpression elimination, structure sharing and hash-consed IR. Basis: paper (problem statement); derived for the mapping to Unison.

#### 3.2 Global de Bruijn indices fail in both directions

The paper's section 2.4 gives two witnesses, reproduced by the probe (`P1`):

| Case | Term | Subterms compared | Global de Bruijn | Correct answer |
|---|---|---|---|---|
| False negative | `\t. foo (\x.x+t) (\y.\x.x+t)` | the two `\x.x+t` | `\.%0+%1` versus `\.%0+%2` (unequal) | equivalent |
| False positive | `\t. foo (\x.t*(x+1)) (\y.\x.y*(x+1))` | `\x.t*(x+1)` and `\x.y*(x+1)` | both `\.%1*(%0+1)` (equal) | different |

The paper notes that the false positives "cannot be eliminated by giving every binder a unique name – with de Bruijn there are no binders". Rendering each subterm with indices only for its own binders and names for its free variables ("locally nameless") gives the right answers in the probe, at the cost of re-rendering each subterm. Basis: paper + execution.

#### 3.3 E-summaries

The paper's construction summarizes an expression as a pair: a *structure* (the tree shape with variable occurrences anonymized, each lambda recording the positions of its bound variable) and a *free-variable map* from each free variable name to a tree of its occurrence positions. Two expressions are alpha-equivalent iff their summaries are equal, and a summary can be converted back to an expression up to bound names. Efficiency comes from always merging the smaller variable map into the larger and from hashing the map with a commutative combiner; in the supporting code the map hash is maintained as an XOR of per-entry hashes (``existingHash `xor` entryHash key pt``). Stated results:

- Theorem 6.3: total running time `O(|e| log^2 |e|)`.
- Theorem 6.8: the correct equivalence classes of all subexpressions are recovered with probability at least `1 - 5|e|^3 * 2^-b` for `b`-bit hashes; the paper concludes that 128-bit hashes give a failure bound below `10^-10` for expressions of up to `10^9` nodes.

Basis: paper + source of the supporting repository.

#### 3.4 Context-sensitive alpha-equivalence

arXiv:2401.02948 argues that ordinary alpha-equivalence, applied to subterms in context, "will equate either too few or too many subterms" depending on the binder-naming convention, defines an equivalence for open terms relative to a context that resolves their free variables, shows it "coincides exactly with the notion of bisimulation equivalence", and gives an `O(n log n)` hashing scheme "improving upon a previously established O(n log^2 n) bound". Basis: paper abstract only.

#### 3.5 Choosing a scheme

| Need | Sufficient scheme | Cost | Limit |
|---|---|---|---|
| Identity of a closed definition | binder-index hashing in one pass | `O(n)` | says nothing about shared subterms |
| Identity of every subterm, names of free variables significant | e-summaries | `O(n log^2 n)` | probabilistic, bound above |
| Identity of every subterm relative to its binding context | context-sensitive scheme | `O(n log n)` | abstract only examined |
| Per-subterm baseline for testing | locally nameless re-rendering | `O(n^2)` worst case | used in the probe |

Basis: derived from 3.1-3.4.

### 4. E-graph hash-consing is not a content address

Basis: source (egg).

egg stores `memo: HashMap<L, Id>` mapping an e-node (operator plus child e-class ids) to an id, with the documented caveat "Enodes in the memo are canonicalized at each rebuild, but after rebuilding new unions can cause them to become out of date." Lookup first rewrites children through the union-find (`enode.update_children(|id| self.find(id))`). `rebuild` "Restores the egraph invariants of congruence and enode uniqueness"; after `add` or `union`, "you must call `rebuild` to restore invariants before any query operations, otherwise the results may be stale or incorrect."

Three properties separate this from a content address (derived):

1. The key contains e-class ids, which are allocation-order integers local to one e-graph value.
2. The key's meaning changes when classes are unioned; uniqueness holds only between rebuilds.
3. Binders get no special treatment. egg's lambda-calculus test language uses named variables with a per-class free-variable analysis, so alpha-equivalent terms with different names are distinct e-nodes.

A store may use an e-graph as a session-local optimizer and must compute durable names from an extracted term by a scheme from section 3.

### 5. Which hash may a dependent key on?

#### 5.1 Comparison matrix

| System (pinned revision) | Hashed unit | Bodies included | Digest | Behaviour on mismatch |
|---|---|---|---|---|
| Unison reference | recursive component of typed terms | always | SHA3-512 | none possible: a different hash is a different definition |
| rustc Strict Version Hash | whole crate | always | XXH3-128 over encoded metadata plus a supplement | loader filters candidates by SVH; error if none matches |
| GHC ABI fingerprint | recursive group of interface declarations | only if exported as an unfolding | MD5 | consumed by the recompilation check (not read in detail) |
| OCaml `.cmi` digest | compiled interface file | never | `Digest.BLAKE128` | "make inconsistent assumptions over interface" |
| OCaml `.cmx` digest | implementation information | cross-module optimization information | recorded per import | "make inconsistent assumptions over implementation" |
| C++ one-definition rule | definable item across translation units | n/a (no hash) | none | ill-formed, diagnostic required only for named modules |

Basis: source for each row; normative for C++.

Details behind the rows:

- **rustc.** The module documentation gives the SVH two uses: noticing changed HIR nodes between compilations for incremental compilation, and "to detect mismatches where we have two versions of the same crate that were compiled from distinct sources." By default the SVH is "an XXH3-128 digest of the encoded metadata bytes", seeded with a fingerprint of the tracked command-line options and of `compute_hir_hash`, "an order-independent combine of each owner's fingerprint". An owner's node hash is the "Pre-computed hash of the full HIR, including bodies. Used in the crate hash." A body-only edit therefore changes the SVH (derived; not executed). `-Z metadata-crate-hash=no` "opts back into computing the SVH from the HIR"; the option is declared `[TRACKED]`, so toggling it changes the SVH. When no metadata is encoded, an "HIR based approximation" over the HIR hash, the upstream `(StableCrateId, Svh)` list, the option hash and the crate's `StableCrateId` is used. The digest is explicitly non-cryptographic: "the SVH is only a change detector". The loader documentation states the consequence: "when a library is compiled, it is only compatible with the *exact same* version of the upstream libraries it was compiled against."
- **rustc crate identity** is separate from content: `StableCrateId` is "a 64-bit hash of a crate name, together with all `-Cmetadata` arguments, and some other data" (crate type and compiler version string in the pinned source), and collisions "abort compilation".
- **GHC.** "The ABI of a declaration consists of: (a) the full name of the identifier ... (b) the declaration itself, as exposed to clients. That is, the definition of an Id is included in the fingerprint only if it is made available as an unfolding in the interface." Fingerprints are computed over recursive groups in dependency order, serializing "the hash of a 'Name' instead of the 'Name' itself" so that "the fingerprint of a decl changes if anything in its transitive closure changes."
- **OCaml.** `output_cmi` computes `Digest.BLAKE128.file filename` over the written interface and stores it in the unit's CRC list. A compilation unit's information records two import lists: `ui_imports_cmi` ("Interfaces imported") and `ui_imports_cmx` ("Infos imported").
- **C++.** For a definable item with definitions in multiple translation units, "Each such definition shall consist of the same sequence of tokens" and "corresponding names ... shall denote the same entity"; on violation "the program is ill-formed; a diagnostic is required only if the definable item is attached to a named module and a prior definition is reachable". When the rule holds, "the behavior is as if there is a single entity with a single definition". Identity is by name, and content equality is an unchecked obligation on the program.

#### 5.2 Rule for early cutoff

Derived rule, checked on a model by the probe (`P3`): a dependent's cache key may use `eta_ifc` of a dependency only for uses that did not consume the dependency's body; every dependency whose body (or body-derived fact) was consumed must contribute `eta_impl`.

| Key policy in the probe | Rebuilt after a body-only edit of `f` (chain `h -> g -> f`, `g` inlines `f`) | Stale inlined copies |
|---|---|---|
| implementation hashes | `f`, `g`, `h` | none |
| interface hashes only | `f` | `g` |
| interface, plus implementation for consumed bodies | `f`, `g` | none |

GHC's item (b) and OCaml's two import lists are instances of the third policy. Unison and rustc at the pinned revisions implement the first: there, an early cutoff must come from a layer above identity.

### 6. Fingerprinting recursive groups: three independent reports

| System | Scheme | Recorded failure |
|---|---|---|
| GHC (Note "Fingerprinting recursive groups") | sort group by declaration name, give members sequential placeholder fingerprints, hash the group | the earlier scheme gave every member placeholder `0` and then the same group fingerprint, so "the group's fingerprint won't change if we change an occurrence of A to B"; the note says the bug "lurked for many years" |
| Unison | sort by structural key, then by per-member hash (section 2.3) | ties under the collapsed key (section 2.4) |
| Nix content-addressed store objects | replace occurrences of the object's own store path by a sentinel before hashing | the alternative "would require finding as hash function fixed point ... which is computationally infeasible"; the result must not depend on the provisional path, a property the manual calls "informal at this stage" |

Basis: source and documentation. Derived reading: a name-free canonical order of a cycle requires a total order on members that is invariant under renaming, which is a graph canonicalization problem; collapsing in-cycle references discards exactly the information needed to break symmetric ties. A name-based order (GHC) is total but only valid where names are part of identity.

### 7. When the scheme or the elaborator changes

| Change class | Example | What the system does | Invariant it relies on |
|---|---|---|---|
| Digest function, same pre-image structure | Git SHA-1 to SHA-256 | new repository format storing "a bidirectional mapping between SHA-256 and SHA-1 object names" that "is generated locally and can be verified using" `git fsck`; objects are re-encoded with references renamed | "The format allows round-trip conversion between SHA-256 content and SHA-1 content"; conversion "retains any brokenness in the original object ... to allow the conversion to round-trip" |
| Encoding or scheme version | Unison `hashingVersion` | version byte in every pre-image; `hash_version` column; full migration | no two schemes share a pre-image prefix |
| Version string inside the pre-image | Dhall before `v6.0.0` | "every new release of the standard required upgrading semantic integrity checks since the standard version is included in the input to the hash"; `v6.0.0` removed it | hash stability now depends on normal forms and binary encoding not changing |
| Normal form (elaborator) change | Dhall `v8.0.0`, `v11.0.0`, `v19.0.0` | recorded as "technically a breaking change" (`v8.0.0`, `v19.0.0`) or as a normal-form change that "perturbs their hash" (`v11.0.0`) | none: every affected hash moves |
| Self-describing names | multihash; Dhall cache files prefixed `1220` | `<varint hash function code><varint digest size in bytes><hash function output>` | identifies the digest function only, not `canon` or the elaborator |
| Store repair | Unison schema migrations | see below | migration must be a pure function of content |

Basis: documentation and source.

Unison's migration comments record two concrete hazards:

- "The 1 to 2 migration kept around hash objects of hash version 1 ... When a branch object was determined to be missing, the migration would replace it with the empty branch ... if a different codebase migrated the same branch and wasn't missing the branch in question ... each database now have the same v1 hash object mapped to two distinct v2 objects, which rightfully causes a crash when syncing." The fix "drops all the v1 hash objects".
- The 3-to-4 migration fixes stored namespace hashes that were not hashes of their content ("incorrectly used causal hashes as branch hashes"), which "remained undetected because there was never a need for this hash to be verifiable" and surfaced once sync required verification; re-hashing made distinct rows collide on one hash and required choosing "exactly one 'canonical' object for each hash".

Git's non-goals bound what its design offers: "Intermixing objects using multiple hash functions in a single repository" and "Transparently improving the security of existing SHA-1 signed objects" are excluded.

Derived requirements for a typed-IR store, checked on a model by the probe (`P4`):

1. Domain-separate schemes in the pre-image, not only in the name.
2. A translation table between schemes is trustworthy only if recomputable from complete local content; a migration that substitutes placeholders for missing children yields a table that differs between replicas (probe: one old name, two new names).
3. Changing `canon` or the elaborator is a different kind of change from changing `H`: there is no content-preserving re-encoding, so old and new names are related only by re-elaboration from a retained input, and equality of meaning across the change needs a separate equivalence argument.
4. Compilers already treat hashing-scheme switches as tracked inputs (rustc's `[TRACKED]` option; in the OCaml and GHC sources read, the digest function is fixed in the compiler).

### 8. Garbage collection and erasure

#### 8.1 Reachability-based collection

| System | Roots | Collection rule | Grace or retention |
|---|---|---|---|
| Git | refs, reflogs, index | `git gc` prunes unreachable loose objects | `gc.pruneExpire` default `2.weeks.ago`; `gc.reflogExpire` "defaults to 90 days" |
| Nix | symlinks under `gcroots`, profile generations | "remove from the Nix store any package not used (directly or indirectly) by any generation of any profile" | "as long as old generations reference a package, it will not be deleted" |
| Unison (3-to-4 migration) | root namespace | "deletes all causals and namespaces which are unreachable" | noted side effect: "may orphan some definitions" |

Basis: documentation and source. None of these removes an object that is still referenced.

Git also has a redirection mechanism: `git replace` adds a ref whose "name ... is the SHA-1 of the object that is replaced", used "by default by all Git commands except those doing reachability traversal (prune, pack transfer and fsck)". Readers see the replacement; the original stays stored and transferable, and the replacement does not hash to the name it answers for. Basis: documentation + derived.

#### 8.2 The erasure requirement

Regulation (EU) 2016/679, Article 17(1): "The data subject shall have the right to obtain from the controller the erasure of personal data concerning him or her without undue delay and the controller shall have the obligation to erase personal data without undue delay where one of the following grounds applies". Article 17(2) adds that a controller that made the data public "taking account of available technology and the cost of implementation, shall take reasonable steps, including technical measures, to inform controllers which are processing the personal data". Basis: normative legal text. Whether a particular store entry is personal data, and whether a digest of it is, are legal questions this report does not answer.

#### 8.3 Design invariants

Derived, with model evidence from the probe (`P5`):

- **E1. Unreferencing is not erasure.** In a Merkle store a node referenced by any retained ancestor is reachable. Removing it by collection requires rewriting every ancestor, which changes their names.
- **E2. Tombstones preserve ancestor verification.** An ancestor's pre-image contains child *names*, not child bodies. Replacing a body by a tombstone leaves every ancestor verifiable (probe: `True`), while the erased node itself can no longer be verified or used. Consumers that need the body must fail closed with a typed "erased" result.
- **E3. A name is a commitment to its content.** For low-entropy content, an unsalted name allows recovery by enumeration (probe: a 10^4-candidate dictionary recovers the erased string). Mixing a per-object secret into the pre-image and destroying it with the body defeats the same enumeration (probe: `False`), at the price of losing, for salted objects, the property that equal content implies equal name.
- **E4. Keep erasable data out of pre-images where possible.** Unison's separation of names and annotations from hashed content (section 2.2) means renaming or deleting a name does not touch any hash. Literals inside bodies, and a unique type's GUID text, are inside pre-images.
- **E5. Erasure must replicate.** Stores of this kind synchronize by name; an erasure is effective only if the tombstone propagates and replicas refuse to re-supply the body.

### 9. Reproducible probe

Environment: CPython 3.13.15 on x86_64 Linux, standard library only. Save the source as `/tmp/probe_cas.py` and run `python3 /tmp/probe_cas.py`; exit status 0. SHA-256 of the source file (ending in a single newline): `e7f800970c3aa2f12e3776ba1cf1cf1ad79ef2e6c9807c4364be14474be41674`.

Fidelity note for `P2`: the port preserves the control structure of section 2.3 (collapsed-cycle keys, stable sort in ascending name order, per-member hash, final sort) and uses SHA3-512, but its token encoding is simplified. Its digests are not Unison's digests.

```python
#!/usr/bin/env python3
"""Micro-probes for content-addressed definition identity (Python 3.10+, stdlib only)."""
import hashlib

def H(*parts, v=2):
    """Length-prefixed accumulate with a leading scheme-version byte."""
    h = hashlib.sha3_512(bytes([v]))
    for p in parts:
        b = p if isinstance(p, bytes) else str(p).encode()
        h.update(len(b).to_bytes(8, "big")); h.update(b)
    return h.digest()
hx = lambda b: b.hex()[:10]

# ---- P1: hashing every subterm: global de Bruijn vs locally nameless ----------------
def render(t, env=()):
    k = t[0]
    if k == "var": return f"%{env.index(t[1])}" if t[1] in env else t[1]
    if k == "con": return t[1]
    if k == "lam": return "(\\." + render(t[2], (t[1],) + env) + ")"
    return "(" + render(t[1], env) + " " + render(t[2], env) + ")"
V, C = (lambda x: ("var", x)), (lambda x: ("con", x))
L, A = (lambda x, b: ("lam", x, b)), (lambda f, *a: f if not a else A(("app", f, a[0]), *a[1:]))
def p1():
    plus_t = lambda x: L(x, A(C("+"), V(x), V("t")))                      # \x. x+t
    mul = lambda x, w: L(x, A(C("*"), V(w), A(C("+"), V(x), C("1"))))     # \x. w*(x+1)
    cases = {"false-negative pair (\\x.x+t under [t] and under [y,t])":
                 ((plus_t("x"), ("t",)), (plus_t("x2"), ("y", "t"))),
             "false-positive pair (\\x.t*(x+1) under [t]; \\x.y*(x+1) under [y,t])":
                 ((mul("x", "t"), ("t",)), (mul("x2", "y"), ("y", "t")))}
    for name, ((a, ea), (b, eb)) in cases.items():
        print("P1", name)
        print("   global de Bruijn equal:", render(a, ea) == render(b, eb), "|", render(a, ea), "/", render(b, eb))
        print("   locally nameless equal:", render(a) == render(b), "|", render(a), "/", render(b))

# ---- P2: port of the cycle-hashing shape used by Unison's hashing-v2 ABT module ------
def hterm(t, env):
    k = t[0]
    if k == "ref":   # in-cycle variable: index of the first environment entry binding it
        for i, e in enumerate(env):
            if (isinstance(e, tuple) and t[1] in e) or e == t[1]: return H("var", i)
        raise KeyError(t[1])
    if k == "dref": return t[1] if t[2] == 0 else H("tm", 1, t[1], t[2])
    if k == "bi": return H("tm", 2, t[1])
    if k == "nat": return H("tm", 64, t[1])
    return H("tm", 3, hterm(t[1], env), hterm(t[2], env))
def hash_component(defs):
    named = sorted(defs.items())                                   # Map.toList: name order
    perm_env = [tuple(n for n, _ in named)]                        # Left names: members collapse
    keyed = [(hterm(t, perm_env), n, t) for n, t in named]
    ties = len({k for k, _, _ in keyed}) < len(keyed)
    ordered = sorted(keyed, key=lambda x: x[0])                    # stable sort, like sortOn
    env = [n for _, n, _ in ordered]                               # Right v for each member
    hashes = [hterm(t, env) for _, _, t in ordered]
    by_name = sorted((H(b"\x01", *hashes, hterm(("ref", n), env)), n) for n, _ in named)
    return H(*[h for h, _ in by_name]), [n for _, n in by_name], ties
def refs(t):
    if t[0] == "ref": yield t[1]
    elif t[0] == "app": yield from refs(t[1]); yield from refs(t[2])
def subst(t, m):
    if t[0] == "ref": return m.get(t[1], t)
    return ("app", subst(t[1], m), subst(t[2], m)) if t[0] == "app" else t
def sccs(defs):                                                    # Tarjan: dependencies first
    idx, low, st, on, out, n = {}, {}, [], set(), [], [0]
    def go(v):
        idx[v] = low[v] = n[0]; n[0] += 1; st.append(v); on.add(v)
        for w in refs(defs[v]):
            if w not in idx: go(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v: break
            out.append(comp)
    for v in sorted(defs):
        if v not in idx: go(v)
    return out
def hash_components(defs):
    done, out, warn = {}, {}, []
    for comp in sccs(defs):
        h, order, ties = hash_component({n: subst(defs[n], done) for n in comp})
        if ties: warn.append(sorted(comp))
        for i, n in enumerate(order): done[n] = ("dref", h, i); out[n] = f"#{hx(h)}.{i}"
    return out, warn
R, B, N = (lambda x: ("ref", x)), (lambda x: ("bi", x)), (lambda x: ("nat", x))
AP = lambda f, *a: f if not a else AP(("app", f, a[0]), *a[1:])
def p2():
    one = {"isEven": AP(B("ifz"), N(1), R("isOdd")), "isOdd": AP(B("ifz"), N(0), R("isEven")),
           "user": AP(R("isEven"), N(7))}
    two = {"pong": AP(B("ifz"), N(1), R("ping")), "ping": AP(B("ifz"), N(0), R("pong")),
           "client": AP(R("pong"), N(7))}
    print("P2 asymmetric cycle     :", hash_components(one))
    print("P2 same cycle, renamed  :", hash_components(two))
    sym = lambda a, b: {a: AP(B("g"), R(b)), b: AP(B("g"), R(a))}
    print("P2 automorphic tie      :", hash_components(sym("a", "b")), hash_components(sym("q", "p")))
    tie = lambda a, b: {a: AP(B("f"), R(b), R(b)), b: AP(B("f"), R(a), R(b))}
    print("P2 non-automorphic tie  :", hash_components(tie("a", "b")))
    print("P2 same tie, a->q b->p  :", hash_components(tie("q", "p")))

# ---- P3: which dependency hash goes into a dependent's cache key ---------------------
def p3():
    def run(policy):
        src = {"f": ("Nat->Nat", "x+1", [], []), "g": ("Nat->Nat", "f(x)*2", ["f"], ["f"]),
               "h": ("Nat->Nat", "g(x)-1", ["g"], [])}
        cache, builds, stale = {}, [], []
        def pass_():
            impl, ifc = {}, {}
            for n in ("f", "g", "h"):
                sig, body, deps, inl = src[n]
                ifc[n] = H("ifc", sig); impl[n] = H("impl", sig, body, *[impl[d] for d in deps])
                dep_key = {"impl": [impl[d] for d in deps], "ifc": [ifc[d] for d in deps],
                           "ifc+unfolding": [impl[d] if d in inl else ifc[d] for d in deps]}[policy]
                key = H("key", sig, body, *dep_key)
                if cache.get(n, (None,))[0] != key:
                    cache[n] = (key, {d: src[d][1] for d in inl}); builds.append(n)
                for d, seen in cache[n][1].items():
                    if seen != src[d][1]: stale.append(n)
        pass_(); builds.clear()
        src["f"] = ("Nat->Nat", "x+2", [], [])                      # body-only edit of f
        pass_()
        return f"rebuilt={builds} stale_inlined_copies={stale}"
    for policy in ("impl", "ifc", "ifc+unfolding"): print(f"P3 {policy:14}:", run(policy))

# ---- P4: scheme migration ------------------------------------------------------------
def p4():
    print("P4 version byte separates schemes:", hx(H("nat", 7, v=1)), "!=", hx(H("nat", 7, v=2)))
    def put(store, v, kind, payload, children=()):
        name = H(kind, payload, *children, v=v); store[name] = (kind, payload, tuple(children)); return name
    def migrate(old, root, missing=()):
        new, table = {}, {}
        def go(name):
            if name in table: return table[name]
            kind, payload, kids = old[name]
            if name in missing: kind, payload, kids = "tree", "", ()   # "replace with empty"
            table[name] = put(new, 2, kind, payload, [go(k) for k in kids]); return table[name]
        return go(root), table
    v1 = {}; leaf = put(v1, 1, "blob", "x = 1"); sub = put(v1, 1, "tree", "lib", [leaf])
    root = put(v1, 1, "tree", "main", [sub])
    full, t_full = migrate(v1, root); part, t_part = migrate(v1, root, missing={sub})
    print("P4 table is a bijection on a complete store:", len(set(t_full.values())) == len(t_full) == 3)
    print("P4 one v1 name, two v2 names after a partial-store migration:",
          hx(root), "->", hx(full), "vs", hx(part), "| conflict:", full != part)

# ---- P5: erasure in a Merkle store ---------------------------------------------------
def p5():
    store = {}
    def put(kind, payload, children=()):
        name = H(kind, payload, *children); store[name] = (kind, payload, tuple(children)); return name
    secret = "user4711@example.org"
    leaf = put("blob", secret); root = put("tree", "profile", [leaf])
    store[leaf] = None                                              # tombstone: name kept, body gone
    kind, payload, kids = store[root]
    print("P5 parent still verifies after tombstoning child:", H(kind, payload, *kids) == root,
          "| child body present:", store[leaf] is not None)
    guess = next(c for c in (f"user{i}@example.org" for i in range(10000)) if H("blob", c) == leaf)
    print("P5 unsalted name re-identifies low-entropy erased content:", guess == secret)
    salt = hashlib.sha3_256(b"per-object secret, destroyed on erasure").digest()
    salted = H("blob", salt, secret)
    hit = any(H("blob", c) == salted for c in (f"user{i}@example.org" for i in range(10000)))
    print("P5 same dictionary against salted name after the salt is destroyed:", hit)

if __name__ == "__main__":
    p1(); p2(); p3(); p4(); p5()
```

Observed output (2026-11-19):

```text
P1 false-negative pair (\x.x+t under [t] and under [y,t])
   global de Bruijn equal: False | (\.((+ %0) %1)) / (\.((+ %0) %2))
   locally nameless equal: True | (\.((+ %0) t)) / (\.((+ %0) t))
P1 false-positive pair (\x.t*(x+1) under [t]; \x.y*(x+1) under [y,t])
   global de Bruijn equal: True | (\.((* %1) ((+ %0) 1))) / (\.((* %1) ((+ %0) 1)))
   locally nameless equal: False | (\.((* t) ((+ %0) 1))) / (\.((* y) ((+ %0) 1)))
P2 asymmetric cycle     : ({'isOdd': '#084524ed26.0', 'isEven': '#084524ed26.1', 'user': '#762c752dfe.0'}, [])
P2 same cycle, renamed  : ({'ping': '#084524ed26.0', 'pong': '#084524ed26.1', 'client': '#762c752dfe.0'}, [])
P2 automorphic tie      : ({'b': '#62d24956fc.0', 'a': '#62d24956fc.1'}, [['a', 'b']]) ({'q': '#62d24956fc.0', 'p': '#62d24956fc.1'}, [['p', 'q']])
P2 non-automorphic tie  : ({'a': '#5830368c3f.0', 'b': '#5830368c3f.1'}, [['a', 'b']])
P2 same tie, a->q b->p  : ({'q': '#7844ca73a7.0', 'p': '#7844ca73a7.1'}, [['p', 'q']])
P3 impl          : rebuilt=['f', 'g', 'h'] stale_inlined_copies=[]
P3 ifc           : rebuilt=['f'] stale_inlined_copies=['g']
P3 ifc+unfolding : rebuilt=['f', 'g'] stale_inlined_copies=[]
P4 version byte separates schemes: 78bfb68ad7 != 647cbd661f
P4 table is a bijection on a complete store: True
P4 one v1 name, two v2 names after a partial-store migration: c5b7c11e6f -> f9c7524c05 vs 26595d7bbd | conflict: True
P5 parent still verifies after tombstoning child: True | child body present: False
P5 unsalted name re-identifies low-entropy erased content: True
P5 same dictionary against salted name after the salt is destroyed: False
```

Reading the output: `P1` reproduces section 3.2. `P2` lines 1-2 show rename invariance of a cycle and its client; line 3 shows an automorphic tie with a warning and equal hashes; lines 4-5 show a non-automorphic tie producing different hashes for alpha-equivalent components. `P3` is the table in 5.2. `P4` and `P5` support sections 7 and 8.3.

## Boundaries

- **Not examined:** execution of Unison, rustc, GHC or OCaml. In particular, that a body-only edit changes rustc's SVH at the pinned revision is inferred from source, and Unison's behaviour on tied `let rec` bindings is inferred from the discarded-warning path.
- **Not examined:** Unison's hosted sharing service, its server-side deletion or retention behaviour, and the sync protocol beyond the migration comments quoted.
- **Not examined:** the full text of arXiv:2401.02948; only the abstract supports section 3.4. Slotted e-graphs (PLDI 2025), which make bound variables a first-class e-graph feature, were identified but not read.
- **Not examined:** Nix content-addressed derivations and their early-cutoff behaviour, OCI registries, IPFS pinning, language package registries, transparency logs, and Git's partial-clone and shallow-clone interactions with missing objects.
- **Not examined:** whether released toolchains match the development-branch revisions read here; the history of digest algorithms in any of the compilers.
- **Unknown:** whether a total, rename-invariant, efficiently computable member order exists for Unison's component hashing that removes the tie failure. The source says "In the future we will hopefully prevent this error entirely."
- **Unknown:** whether any Unison storing path can hash a term that still contains an unresolved name placeholder.
- **Known not to apply:** e-class ids or e-node memo keys as durable identifiers (section 4); global de Bruijn hashing as a subterm-identification method (section 3.2); `StableCrateId` as a content hash (it is derived from the crate name, `-Cmetadata` and compiler version).
- **Unsupported by the subject:** mixing two hash functions in one Git repository and retroactively strengthening SHA-1 signatures are stated non-goals of Git's transition design.
- **Stronger conclusions not established:** the probe does not show that Unison assigns name-dependent hashes in practice; it shows that the algorithm would if the tie warning were ignored, which the examined top-level callers do not do. The early-cutoff table is a property of a toy model, not a measurement of any compiler. Nothing here establishes that tombstoning or salting satisfies any legal erasure obligation.

## Evidence

All repository evidence was read on 2026-11-19 from the stated commits. Line numbers refer to those commits.

**Unison** (`unisonweb/unison` @ `b5c5188d99f31820d0cc012f194948d2876c14e7`)

- `unison-hashing-v2/src/Unison/Hashing/V2/Tokenizable.hs`: version comment and `hashingVersion` (28-38), `Token` (40-47), breaking-change comment (56-58), `accumulate` (122-137).
- `unison-hashing-v2/src/Unison/Hashing/V2/ABT.hs`: `HashingWarning` and message (33-63), `crashOnHashingWarning` (68-71), `hashComponent` (74-100), `hashComponents` (106-134), `hash'` (145-174), `doHashCycle` (178-217).
- `unison-hashing-v2/src/Unison/Hashing/V2/Term.hs`: `hashTermComponents` and `incorporateType` (99-116), `Hashable1` instance including reference transparency and `let rec` versus `let` comments (134-232).
- `unison-hashing-v2/src/Unison/Hashing/V2/Type.hs`: `Hashable1 TypeF` (142-171).
- `unison-hashing-v2/src/Unison/Hashing/V2/DataDeclaration.hs`: `Modifier` (29), `hashDecls0` (57-62), limitation note and `hashDecls` (71-91), `Hashable1 F` and `Modifier` tokens (112-132).
- `unison-hashing-v2/src/Unison/Hashing/V2/Reference.hs`: `Reference`, `ReferenceId`, tokens (21-51).
- `parser-typechecker/src/Unison/Hashing/V2/Convert.hs`: `hashTermComponentsWithoutTypes` warning (87-94).
- `parser-typechecker/src/Unison/Typechecker.hs`: `synthesizeAndResolve` (204-226), `typeDirectedNameResolution` (255-289).
- `parser-typechecker/src/Unison/UnisonFile.hs`: `typecheckedUnisonFile` hashing site (268-284).
- `unison-syntax/src/Unison/Syntax/Parser.hs`: `uniqueTypeGuid` (121-129).
- `unison-merge/src/Unison/Merge/Synhash.hs`: module comment (1-25).
- `codebase2/codebase-sqlite/sql/create.sql`: `hash_object` (43-49).
- `parser-typechecker/src/Unison/Codebase/SqliteCodebase/Migrations.hs`: migration table and comment (57-81); `Migrations/MigrateSchema3To4.hs`: comment (52-80).
- Documentation: `https://www.unison-lang.org/docs/the-big-idea/`, read 2026-11-19 ("Each Unison definition is identified by a hash of its syntax tree"; "Unison uses 512-bit SHA3 hashes").

**Alpha-equivalence**

- arXiv:2105.02856v1, sections 2.4, 4-6 (Theorems 6.3 and 6.8); full text fetched 2026-11-19.
- `microsoft/hash-modulo-alpha` @ `9deb049bce534c8b630c85102cf24da78619441a`: `README.md` (repository structure), `src/AlphaHashOptimizedHash.hs` (XOR-maintained map hash, 19 and 50-70).
- arXiv:2401.02948v3 abstract page (related DOI `10.1145/3656459`).
- arXiv:2004.03082v3 abstract page (journal reference POPL 2021, related DOI `10.1145/3434304`).

**egg** (`egraphs-good/egg` @ `73975c9819efb4af2f3c6c1b44fa53f8c5742574`): `src/egraph.rs` `memo` (63-66), `lookup_internal` (930-937), `process_unions` (1346-1357), `rebuild` documentation (1378-1416); `tests/lambda.rs` (language and free-variable analysis, 7-82).

**rustc** (`rust-lang/rust` @ `b0b600668bb9b4a897e2299b0a44289d42276545`)

- `compiler/rustc_data_structures/src/svh.rs` (1-18).
- `compiler/rustc_middle/src/hir/map.rs`: `crate_hash` (1182-1215), `compute_hir_hash` (1299-1310).
- `compiler/rustc_metadata/src/rmeta/encoder.rs`: SVH from metadata hasher (835-846), dependency hash field (2237), hasher seeding and non-cryptographic rationale (2725-2752).
- `compiler/rustc_hir/src/hir.rs`: `OwnerNodes::opt_hash` (1315-1329), `OwnerInfo::fingerprint` (1405-1413).
- `compiler/rustc_session/src/options.rs`: `metadata_crate_hash` (2762-2764).
- `compiler/rustc_span/src/def_id.rs`: `StableCrateId` (141-201).
- `compiler/rustc_metadata/src/locator.rs`: selection criteria and SVH (71-84, 196-204).

**GHC** (`ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`): `compiler/GHC/Iface/Recomp.hs` Notes "Fingerprinting IfaceDecls" and "Fingerprinting recursive groups" (1109-1190), "The ABI of an IfaceDecl" (1632-1650); `compiler/GHC/Unit/Module/ModIface.hs` `IfaceAbiHashes` (174-197).

**OCaml** (`ocaml/ocaml` @ `d921d1e86c56baa7b30e890ced455c12255793f5`): `file_formats/cmi_format.ml` `output_cmi` (84-93); `file_formats/cmx_format.mli` import lists (42-43); `asmcomp/asmlink.ml` error text (382-394); `typing/persistent_env.ml` (368-370).

**C++ working draft** (`cplusplus/draft` @ `0ab325d274a1ad610cef1099ec528fb0bed6ee18`): `source/basic.tex`, section `[basic.def.odr]` (768-812, 905-915).

**Dhall** (`dhall-lang/dhall-lang` @ `56b0997a4800bfc815ea221529a6bb2bfd6723dc`): `standard/imports.md` integrity checks and cache naming (844-889); `standard/versioning.md` (10-12); `CHANGELOG.md` entries under `v6.0.0` (2494-2510), `v8.0.0` (2152-2168), `v11.0.0` (1402-1408), `v19.0.0` (546-553).

**Git** (`git/git` @ `e1ec09b23c8e0deb21a0b95ac5996422277395d4`): `Documentation/technical/hash-function-transition.adoc` goals, non-goals, overview (86-146), object names and format (178-205), translation table (316-342), invalid objects (524-536); `Documentation/config/gc.adoc` (96-118); `Documentation/git-gc.adoc` (83-84, 144-150); `Documentation/git-replace.adoc` description.

**Nix** (`NixOS/nix` @ `6965392507e19998de706aa15e514f81e9b7ce11`): `doc/manual/source/store/store-object/content-address.md` (36-65); `doc/manual/source/package-management/garbage-collection.md`; `doc/manual/source/package-management/garbage-collector-roots.md`.

**multihash** (`multiformats/multihash` @ `b43ec1026a610fa87878e53b3daecf3a14b3ef6f`): `README.md`, "Format".

**Regulation (EU) 2016/679, Article 17.** The quoted text of paragraphs 1 and 2 was read on 2026-11-19 from the copy at `https://www.legislation.gov.uk/eur/2016/679/article/17`, where those two paragraphs carry no amendment markers; the EUR-Lex page for CELEX `32016R0679` was located by search but could not be retrieved in full. This is the weakest-pinned evidence in the report.

**Execution.** The probe source and output in Findings section 9 are complete; no other file is required.

## Revalidation

- **Probe.** Re-run the script in section 9 and compare the output byte for byte; it is deterministic. A different result under another CPython version would indicate a change in `hashlib` or sort stability, not in any subject.
- **Unison scheme version and algorithm.** In a newer checkout, check `hashingVersion` in `Tokenizable.hs`; diff `ABT.hs` between the pinned commit and the new one. If `doHashCycle` no longer builds `permutationEnv = Left names : env` or no longer reports `IncompleteElementOrderingError`, sections 2.3-2.4 need re-reading. Search for `crashOnHashingWarning` call sites to re-derive the table in 2.4.
- **Unison type inclusion.** Check that `hashTermComponents` still wraps terms with `TermAnn`.
- **Decisive Unison experiment not performed here.** With a Unison codebase manager, add `a = f b b` and `b = f a b` (for any binary `f`) and observe whether the tie error is raised; then add a `let rec` with the same shape inside one definition in two binding orders and compare the resulting hashes.
- **rustc.** Search `compiler/rustc_metadata/src/rmeta/encoder.rs` for `metadata_crate_hash` and `compiler/rustc_middle/src/hir/map.rs` for `compute_hir_hash`. Empirically: compile a library crate twice with a body-only edit to a private function and compare the SVH reported in the crate metadata.
- **GHC and OCaml.** Re-read the two GHC Notes by title; for OCaml, check `output_cmi` and the two `ui_imports_*` fields.
- **Dhall, Git, Nix.** Check `standard/imports.md` for the integrity-check algorithm and scan `CHANGELOG.md` for "semantic integrity"; re-read the "Goals", "Non-Goals" and "Translation table" sections of Git's transition document; re-read the "Self-references" section of the Nix manual page.
- **Papers.** The theorem numbers and bounds are those of arXiv:2105.02856v1; a later version or the proceedings version may renumber them.
