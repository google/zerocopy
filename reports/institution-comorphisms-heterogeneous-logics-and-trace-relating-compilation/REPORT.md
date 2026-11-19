# Institution comorphisms, heterogeneous logic graphs, and trace-relating compiler correctness

## Summary

Two independent bodies of theory answer the same engineering question — *what survives when a
verified claim crosses a boundary?* — once for logics and once for languages.

**Logic boundary (institutions).** An institution is a logic presented as signatures, sentences,
models and a satisfaction relation invariant under change of signature. An institution
*comorphism* `(Φ, α, β) : I → J` sends signatures and sentences forward and models backward,
subject to one condition: `N ⊨_J α(φ) ⇔ β(N) ⊨_I φ`. From that condition alone, entailment is
always *preserved* (`Γ ⊨_I φ ⇒ α(Γ) ⊨_J α(φ)`) and models/counter-models found in `J` always
*reduce* to `I`. The converse uses — proving an `I`-goal with a `J`-prover, or declaring an
`I`-theory inconsistent because its translation is — are sound only with **model expansion**
(every `I`-model is `β` of some `J`-model of the translated signature and its infrastructure
axioms). Linking separately verified theories additionally needs **amalgamation** (compatible
models over a shared interface glue to a model of the pushout signature).

**Language boundary (trace-relating compilation).** When source and target traces differ, compiler
correctness is stated against a relation `∼ ⊆ Trace_S × Trace_T`: `CC∼ ≡ ∀W t. W↓ ⇝ t ⇒ ∃s ∼ t.
W ⇝ s`. Every relation induces a Galois connection `τ̃ ⊣ σ̃` on trace properties
(`τ̃(π_S) = {t | ∃s ∼ t. s ∈ π_S}`, `σ̃(π_T) = {s | ∀t. s ∼ t ⇒ t ∈ π_T}`), and
`CC∼ ⇔ TP^τ̃ ⇔ TP^σ̃`: `τ̃` is the strongest target guarantee for a proved source property, `σ̃`
the weakest source obligation for a wanted target property. The relation, not the theorem's name,
decides what is lost: with undefined behaviour a source claim that tolerates going wrong after
a prefix `m` guarantees nothing about the target after `m`; with target-only resource exhaustion
every target property that forbids exhaustion has source
obligation `∅`; with a timing side channel, source noninterference becomes only
timing-insensitive noninterference.

**Retain these distinctions.**

1. At the pinned Hets revision the comorphism flags `has_model_expansion` and
   `is_weakly_amalgamable` default to `False`; automatic *prover* selection only uses comorphisms
   with model expansion, but the comorphism search used for consistency checkers and theory
   translation does not filter; heterogeneous amalgamability checking is not implemented, the
   per-logic default check answers "amalgamates" with a warning, and the table of weakly
   amalgamable squares is empty.
2. Trace relations compose along a pass pipeline (relational composition; `τ̃` composes covariantly
   and `σ̃` contravariantly) and unions are harmless, but two `CC∼` results for the same compiler
   do **not** give `CC` for the intersected relation.
3. Preservation of subset-closed hyperproperties needs a subset closure after `τ̃`; preservation
   of arbitrary hyperproperties against adversarial contexts is equivalent only to the `τ̃` form,
   and the `σ̃` form needs a Galois insertion or reflection.
4. A `CC∼` compiler is exactly one half of an institution morphism between the trace-property
   logics of source and target (sentence map `σ̃`, model map compilation); the other half is a
   forward completeness property that soundness never needs.
5. Cross-language link-time optimisation removes the boundary at which per-module claims are
   stated. The sound order is: transport each claim to the common IR semantics with a *robust*
   (context-quantified) criterion, compose with an amalgamation/linking argument, hide the
   boundary, and only then appeal to whole-program correctness of the optimiser. Front-end-emitted
   IR attributes (`noundef`, `nonnull`, `noalias`) are part of the boundary contract.

## Applicability

The report concerns the *combination* of the subjects listed in `REPORT.json`; no subject is
compared against another.

- **Institution definitions** are taken from the author manuscript of Mossakowski, Codescu,
  Neuhaus and Kutz, *The Distributed Ontology, Modeling and Specification Language – DOL*
  (Definitions 2.1, 2.4, 2.5 and the classification of mappings in its Section 2.2). The
  transport laws in Findings §2 are derived from those definitions and hold for every institution
  and comorphism, including simple theoroidal ones when "model of `Φ(Σ)`" is read as "model of the
  signature part satisfying the axiom part".
- **Tool behaviour** is that of `spechub/Hets` at revision
  `65ca27f4fcafd57f94fbb0908f2d88a16b0977ea`, read from source. Nothing was built or run; the
  findings describe code paths, not observed executions, and are not claimed for other revisions.
- **Trace-relating results** are those of Abate, Blanco, Ciobâcă, Durier, Garg, Hriţcu, Patrignani,
  Tanter and Thibault (ESOP 2020; arXiv 1907.05320v4) and of the Coq development at
  `secure-compilation/different_traces@e74dd632057b846d5ebca273dc218de968de3279` (README: Coq
  8.8/8.9 with Mathematical Components 1.8/1.9). The Coq files were read, not recompiled. Unless
  stated, the results make no assumption on the structure of traces. Robust and relational
  criteria additionally use Abate, Blanco, Garg, Hriţcu, Patrignani and Thibault (CSF 2019; arXiv
  1807.04603v6).
- **CompCert** statements are quoted from `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`
  (`driver/Complements.v`, `common/Behaviors.v`).
- **LTO facts** come from the rustc book page `src/doc/rustc/src/linker-plugin-lto.md` and from
  `compiler/rustc_ty_utils/src/abi.rs` at
  `rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545`, and from `llvm/docs/LangRef.md` at
  `llvm/llvm-project@2bee3e393405d26213834265dd4478e88ff96d30`.
- **Executable evidence** is two standard-library Python programs reproduced in full in Findings
  §3 and §10 (run with CPython 3.13.15). They check finite models exhaustively; they illustrate
  and cross-check the general statements but do not prove them for infinite trace sets or
  arbitrary logics.
- Findings §11 (link-time optimisation) is a synthesis derived from the other findings. No
  examined artifact mechanises it.

## Findings

### 1. Vocabulary

Basis: documentation (DOL manuscript, Defs. 2.1, 2.4, 2.5, Section 2.2).

- **Institution** `I = (Sign, Sen, Mod, ⊨)`: a category of signatures; `Sen : Sign → Set` with
  sentence translation `σ(φ)`; `Mod : Sign^op → Cat` with reduct `M'|σ`; and for every
  `σ : Σ → Σ'` the *satisfaction condition* `M' ⊨_{Σ'} σ(φ) iff M'|σ ⊨_Σ φ`.
- **Comorphism** `(Φ, α, β) : I → J`: functor `Φ : Sign^I → Sign^J`, natural transformations
  `α : Sen^I ⇒ Sen^J ∘ Φ` and `β : Mod^J ∘ Φ ⇒ Mod^I`, with `N ⊨^J_{Φ(Σ)} α_Σ(φ) ⇔ β_Σ(N) ⊨^I_Σ φ`.
  Used for *translations* (encodings).
- **Morphism** `(Φ, α, β) : I → J`: sentences go backward (`α : Sen^J ∘ Φ ⇒ Sen^I`) and models
  forward (`β : Mod^I ⇒ Mod^J ∘ Φ`), with `M ⊨^I α_Σ(φ) ⇔ β_Σ(M) ⊨^J φ`. Used for *projections*
  (forgetful maps).
- **Simple theoroidal** mapping: `Φ` maps signatures to *theories*, so the translation may add
  "infrastructure axioms".
- **Faithful** mapping: logical consequence is preserved *and reflected*, "that is, inference
  systems and reasoning engines for the target logic can be reused for the source logic".
  "(Weak) exactness is a technical property that guarantees this faithfulness even in the
  presence of … structuring operations."
- Terms used below with the following meaning (standard in the institution literature; the Hets
  source uses the same names without defining the first two): a comorphism has **model
  expansion** if every `β_Σ` is surjective on models; a commuting square (or cocone) of signature
  morphisms is **(weakly) amalgamable** if any family of models with equal reducts along the
  shared part has a unique (at least one) common expansion over the apex.

A **Grothendieck signature morphism** in Hets is the pair "comorphism plus target-logic signature
morphism": `GMorphism { gMorphismComor :: cid, gMorphismSign :: ExtSign sign1 symbol1, …,
gMorphismMor :: morphism2 }` (`Logic/Grothendieck.hs`), i.e. `(I, Σ) → (J, Σ')` is `ρ : I → J`
together with `σ : Φ_ρ(Σ) → Σ'` in `J`. The module header describes the Grothendieck logic as the
"flattening of logic graph to a single logic". Basis: source.

### 2. What a comorphism transports

Basis: derived (each row is a two-line argument from the comorphism condition); the rows marked ✱
are additionally exercised by the probe in §3.

Let `ρ = (Φ, α, β) : I → J`, `Γ ∪ {φ} ⊆ Sen^I(Σ)`, and write `α(Γ)` for the translated set (plus
the axioms of `Φ(Σ)` in the theoroidal case).

| Fact established in `J` | Conclusion in `I` | Requires | Why |
|---|---|---|---|
| — (fact known in `I`: `Γ ⊨ φ`) | `α(Γ) ⊨ α(φ)` in `J` | nothing | if `N ⊨ α(Γ)` then `β(N) ⊨ Γ`, so `β(N) ⊨ φ`, so `N ⊨ α(φ)` |
| `α(Γ) ⊨ α(φ)` (prover success) ✱ | `Γ ⊨ φ` | model expansion | for `M ⊨ Γ` pick `N` with `β(N) = M`; then `N ⊨ α(Γ)`, hence `N ⊨ α(φ)`, hence `M ⊨ φ` |
| `N ⊨ α(Γ)`, `N ⊭ α(φ)` (counter-model) | `Γ ⊭ φ` | nothing | `β(N)` is a counter-model |
| `N ⊨ α(Γ)` (consistency witness) ✱ | `Γ` satisfiable | nothing | `β(N) ⊨ Γ` |
| `α(Γ)` unsatisfiable ✱ | `Γ` unsatisfiable | model expansion | a model of `Γ` would expand to a model of `α(Γ)` |

Consequences:

- A translation can satisfy the comorphism condition perfectly and still be **unsound for
  proving**. The condition constrains only the target models that exist; infrastructure axioms
  that are too strong silently delete source models. "Too strong" is not detectable by testing
  the satisfaction condition.
- The asymmetry is the opposite of the usual intuition about encodings: *finding* something in
  the target (a model, a counter-example) is always safe; *failing to find* (a proof by
  refutation, an inconsistency verdict) needs expansion.
- Model expansion composes (surjections compose). The satisfaction condition composes as well, so
  a path of model-expansive comorphisms is model-expansive.
- For **linking** two theories `T1`, `T2` over a shared interface `Σ0`, the combined signature is
  the pushout of `Σ1 ← Σ0 → Σ2`. Amalgamation at that pushout is what turns "`M1 ⊨ T1`,
  `M2 ⊨ T2`, equal on `Σ0`" into "a model of `T1 ∪ T2` exists". If the tool unifies symbols *by
  name* that are not in the declared interface, the cocone is not the pushout and amalgamation
  can fail (§3: 4 of 8 compatible model pairs have no common expansion) — the logical form of a
  duplicate-definition link error that the interface failed to declare.

### 3. Executable probe: comorphism condition versus model expansion

Basis: execution.

The source logic `K3` is strong-Kleene three-valued propositional logic with a definedness
connective (models map atoms to true/false/undefined; `M ⊨ f` iff `f` evaluates to true). The
target is classical propositional logic `PL`. The comorphism maps each atom `p` to two atoms `p+`
("known true") and `p-` ("known false") under the axiom `¬(p+ ∧ p-)`; sentences are translated by
a positive/negative pair of translations. Three variants are compared: the correct one; a "naive"
sentence translation that applies classical negation after encoding; and the correct sentence
translation with one extra infrastructure axiom `p+ ∨ p-` ("everything is defined").

```python
#!/usr/bin/env python3
"""Finite-model checks for institutions and comorphisms (stdlib only).

PL : classical propositional logic.  K3 : strong-Kleene three-valued logic with a
definedness connective; a K3 model maps atoms to True / False / None (undefined) and
M |= f iff f evaluates to True.  Formulas: ('at',p) ('not',f) ('and',f,g) ('or',f,g)
('def',f); ('top',) occurs only in translated sentences.
"""
from itertools import product


def forms(atoms, depth, with_def=True):
    fs = [('at', p) for p in atoms]
    for _ in range(depth):
        new = [('not', f) for f in fs]
        new += [(op, f, g) for op in ('and', 'or') for f in fs for g in fs]
        if with_def:
            new += [('def', f) for f in fs]
        fs = list(dict.fromkeys(fs + new))
    return fs


def ev3(f, m):                      # strong Kleene; also classical when m is two-valued
    k = f[0]
    if k == 'top':
        return True
    if k == 'at':
        return m[f[1]]
    if k == 'not':
        v = ev3(f[1], m)
        return None if v is None else (not v)
    if k == 'def':
        return ev3(f[1], m) is not None
    a, b = ev3(f[1], m), ev3(f[2], m)
    if k == 'and':
        return False if (a is False or b is False) else (True if (a and b) else None)
    return True if (a is True or b is True) else (False if (a is False and b is False) else None)


def models(atoms, values):
    return [dict(zip(atoms, vs)) for vs in product(values, repeat=len(atoms))]


def rename(f, sig):
    return ('at', sig[f[1]]) if f[0] == 'at' else (f[0],) + tuple(rename(g, sig) for g in f[1:])


def sat_condition(values):
    ok = n = 0
    for src, tgt in ((['p', 'q'], ['x', 'y']), (['p', 'q'], ['x']), (['p'], ['x', 'y'])):
        for image in product(tgt, repeat=len(src)):
            sig = dict(zip(src, image))
            for m2 in models(tgt, values):
                reduct = {p: m2[sig[p]] for p in src}
                for f in forms(src, 2):
                    n += 1
                    ok += (ev3(rename(f, sig), m2) is True) == (ev3(f, reduct) is True)
    return ok, n


print("satisfaction condition PL: %d/%d" % sat_condition([True, False]))
print("satisfaction condition K3: %d/%d" % sat_condition([True, False, None]))


# Comorphism K3 -> PL: Phi(Sigma) = {p+, p-} with axioms not(p+ and p-).
def pos(f):
    k = f[0]
    if k == 'at':
        return ('at', f[1] + '+')
    if k == 'not':
        return neg(f[1])
    if k == 'def':
        return ('or', pos(f[1]), neg(f[1]))
    return (k, pos(f[1]), pos(f[2]))


def neg(f):
    k = f[0]
    if k == 'at':
        return ('at', f[1] + '-')
    if k == 'not':
        return pos(f[1])
    if k == 'def':
        return ('not', ('or', pos(f[1]), neg(f[1])))
    return ('or' if k == 'and' else 'and', neg(f[1]), neg(f[2]))


def naive(f):                       # broken translation: classical negation after encoding
    k = f[0]
    if k == 'at':
        return ('at', f[1] + '+')
    if k == 'def':
        return ('top',)
    return (k,) + tuple(naive(g) for g in f[1:])


def beta(n, atoms):
    return {p: True if n[p + '+'] else (False if n[p + '-'] else None) for p in atoms}


ATOMS = ['p', 'q']
PHI = [p + s for p in ATOMS for s in '+-']
AX = [m for m in models(PHI, [True, False]) if not any(m[p + '+'] and m[p + '-'] for p in ATOMS)]
AX_TOTAL = [m for m in AX if all(m[p + '+'] or m[p + '-'] for p in ATOMS)]
K3 = models(ATOMS, [True, False, None])
F2, F1 = forms(ATOMS, 2), forms(ATOMS, 1)


def comorphism_condition(alpha, target_models):
    return sum((ev3(alpha(f), n) is True) == (ev3(f, beta(n, ATOMS)) is True)
               for n in target_models for f in F2), len(target_models) * len(F2)


def borrowing(alpha, target_models):
    unsound = incomplete = 0
    example = None
    for g in [None] + F1:
        for f in F1:
            src = all(ev3(f, m) is True for m in K3 if g is None or ev3(g, m) is True)
            tgt = all(ev3(alpha(f), n) is True for n in target_models
                      if g is None or ev3(alpha(g), n) is True)
            unsound += tgt and not src
            incomplete += src and not tgt
            if tgt and not src and example is None:
                example = (g, f)
    return unsound, incomplete, example


def expansive(target_models):
    image = {tuple(beta(n, ATOMS).items()) for n in target_models}
    return len(image), len(K3)


for name, alpha, tm in (("pos/neg, axioms not(p+ & p-)", pos, AX),
                        ("naive negation, same axioms", naive, AX),
                        ("pos/neg, extra axioms p+ | p-", pos, AX_TOTAL)):
    print("[%s]" % name)
    print("  comorphism condition %d/%d" % comorphism_condition(alpha, tm))
    print("  beta image %d of %d source models" % expansive(tm))
    print("  borrowing over %d (premise, goal) pairs: unsound=%d incomplete=%d first=%s"
          % (((len(F1) + 1) * len(F1),) + borrowing(alpha, tm)))
    lem = ('or', ('at', 'p'), ('not', ('at', 'p')))
    print("  p or not p: valid in K3=%s, translation valid in target theory=%s"
          % (all(ev3(lem, m) is True for m in K3), all(ev3(alpha(lem), n) is True for n in tm)))
g = ('not', ('def', ('at', 'p')))
print("K3-satisfiable 'not def p': source models %d, AX models %d, AX_TOTAL models %d"
      % (sum(ev3(g, m) is True for m in K3), sum(ev3(pos(g), n) is True for n in AX),
         sum(ev3(pos(g), n) is True for n in AX_TOTAL)))

# Amalgamation in PL: interface {i}; pushout (disjoint private symbols) vs name-merged union.
B = [True, False]
pairs = [(m1, m2) for m1 in models(['i', 'a'], B) for m2 in models(['i', 'b'], B)
         if m1['i'] == m2['i']]
uniq = sum(sum(all(m[k] == v for k, v in list(m1.items()) + list(m2.items()))
               for m in models(['i', 'a', 'b'], B)) == 1 for m1, m2 in pairs)
print("pushout {i,a} <- {i} -> {i,b}: unique amalgamation for %d/%d compatible pairs"
      % (uniq, len(pairs)))
pairs = [(m1, m2) for m1 in models(['i', 'x'], B) for m2 in models(['i', 'x'], B)
         if m1['i'] == m2['i']]
print("name-merged union with hidden shared x: amalgamable %d/%d compatible pairs"
      % (sum(m1['x'] == m2['x'] for m1, m2 in pairs), len(pairs)))

# Weak amalgamation of the comorphism along the inclusion {p} -> {p,q}.
AX1 = [m for m in models(['p+', 'p-'], B) if not (m['p+'] and m['p-'])]
cases = wit = uni = 0
for m2 in K3:
    for n1 in AX1:
        if beta(n1, ['p']) == {'p': m2['p']}:
            cases += 1
            c = sum(beta(n2, ATOMS) == m2 and all(n2[k] == n1[k] for k in n1) for n2 in AX)
            wit += c >= 1
            uni += c == 1
print("comorphism amalgamation along {p} -> {p,q}: witness %d/%d, unique %d/%d"
      % (wit, cases, uni, cases))
```

Output of `python3 institution_probe.py` (exit status 0):

```text
satisfaction condition PL: 8084/8084
satisfaction condition K3: 17556/17556
[pos/neg, axioms not(p+ & p-)]
  comorphism condition 3798/3798
  beta image 9 of 9 source models
  borrowing over 210 (premise, goal) pairs: unsound=0 incomplete=0 first=None
  p or not p: valid in K3=False, translation valid in target theory=False
[naive negation, same axioms]
  comorphism condition 3390/3798
  beta image 9 of 9 source models
  borrowing over 210 (premise, goal) pairs: unsound=16 incomplete=0 first=(None, ('def', ('at', 'p')))
  p or not p: valid in K3=False, translation valid in target theory=True
[pos/neg, extra axioms p+ | p-]
  comorphism condition 1688/1688
  beta image 4 of 9 source models
  borrowing over 210 (premise, goal) pairs: unsound=16 incomplete=0 first=(None, ('def', ('at', 'p')))
  p or not p: valid in K3=False, translation valid in target theory=True
K3-satisfiable 'not def p': source models 3, AX models 3, AX_TOTAL models 0
pushout {i,a} <- {i} -> {i,b}: unique amalgamation for 8/8 compatible pairs
name-merged union with hidden shared x: amalgamable 4/8 compatible pairs
comorphism amalgamation along {p} -> {p,q}: witness 9/9, unique 9/9
```

Reading: the third variant passes the comorphism condition on every target model (1688/1688) yet
proves excluded middle for a logic in which it is invalid, and reports a satisfiable source
theory (`not def p`) as unsatisfiable — the two failures predicted by the rows of §2 that require
model expansion. The second variant fails the comorphism condition itself (408 violations).
`incomplete=0` in all three is the first row of the table: preservation needs nothing.

### 4. Hets at the pinned revision: what the logic graph enforces

Basis: source (`spechub/Hets@65ca27f4…`), paths relative to the repository root.

**Comorphism interface** (`Logic/Comorphism.hs`, class `Comorphism`). Besides `map_theory`,
`map_sentence`, `map_morphism`, `map_symbol` and `extractModel`, the class carries semantic
*declarations* with these defaults:

```haskell
    is_model_transportable _ = False
    has_model_expansion _ = False
    is_weakly_amalgamable _ = False
    isInclusionComorphism _ = False
    -- reduction preserves satisfaction
    rps _ = True
    -- expansion preserves satisfaction
    eps _ = True
    isGTC _ = False
```

- The flags are author assertions; no code checks them against the translation functions.
- `map_theory` takes and returns a *theory* (`(sign, [Named sentence])`), so theoroidal
  comorphisms are the general case ("cover theoroidal comorphisms as well").
- `extractModel` (target proof tree → source theory) is the implemented form of `β`; its default
  fails with "extractModel not implemented".
- Sublogic inclusions (`InclComorphism`) set model transport, model expansion, weak amalgamation
  and inclusion to `True`.
- Composition (`CompComorphism`) conjoins `is_model_transportable`, `has_model_expansion`,
  `is_weakly_amalgamable` and `isInclusionComorphism` of the components. It does **not** define
  `rps`, `eps` or `isGTC`, so a composite reports the class defaults (`True`, `True`, `False`)
  whatever its components say. `compComorphism` checks only that logics and sublogics line up.
- Tree-wide census: 65 `instance Comorphism` declarations; 75 entries in `comorphismList`
  (`Comorphisms/LogicGraph.hs`, all CPP branches counted); 53 instances declare
  `has_model_expansion … = True`, 37 declare `is_weakly_amalgamable … = True`, 11 declare
  `is_model_transportable … = True`. `CASL2Prop` declares `has_model_expansion = False`
  explicitly. Twelve comorphism modules declare no model-expansion flag and therefore inherit
  `False`: `CommonLogicModuleElimination`, `CspCASL2Modal`, `ExtModal2OWL`, `HasCASL2HasCASL`,
  `HasCASL2Haskell`, `HasCASL2IsabelleHOL`, `HolLight2Isabelle`, `Prop2CommonLogic`,
  `RelScheme2CASL`, `SoftFOL2CommonLogic`, `OWL2/CASL2OWL`, `OWL2/OWL22NeSyPatterns`.
  The only non-default `rps`/`eps`/`isGTC` declarations are `eps CASL2Skolem = False` and
  `isGTC OWL22NeSyPatterns = True`. (Derived reading of the first: `rps` and `eps` name the two
  directions of the comorphism condition, and after Skolemisation an arbitrary expansion by
  Skolem symbols need not satisfy the translated sentence, so only the "reduction" direction
  holds.)

**Two comorphism searches with different soundness filters** (`Logic/Grothendieck.hs`,
`Proofs/AbstractState.hs`):

| Search | Filter | Callers observed |
|---|---|---|
| `logicGraph2Graph` | `filter (\x -> hasModelExpansion x && isRps x && isEps x)` over `comorphisms lg` | `getAllProvers` / `getUsableProvers` (`Proofs/AbstractState.hs`), which every prover-selection front end observed calls (`Proofs/InferBasic.hs`, `PGIP/Server.hs` `getAllAutomaticProvers`, `HetsAPI/ProveCommands.hs`, `GUI/GtkAutomaticProofs.hs`, `CMDL/Shell.hs`, `CMDL/ProveConsistency.hs`, `CMDL/DgCommands.hs`); also `CMDL/InfoCommands.hs` |
| `findComorphismPaths` = `findComorphismCompositions` | none on semantic flags; bounded by `weight_limit = 4`, `times_logic_in_branch = 3` and a hand-written `comorphismWeight` table over **all** `comorphisms lg` | consistency checkers (`getConsCheckers . findComorphismPaths` in `PGIP/Server.hs`, `GUI/GtkConsistencyChecker.hs`, `CMDL/ProveConsistency.hs`, `HetsAPI/ProveCommands.hs`), theory/library translation menus (`GUI/GraphLogic.hs`), `PGIP/Server.hs` `showGlobalTh` |

Derived reading against §2: the prover route applies exactly the condition needed for borrowing.
The unfiltered route is adequate for *model finding* (a model reduces along `β`), but an
"inconsistent" verdict obtained along a path containing a non-expansive comorphism (for example
`CASL2Prop`, registered as `CASL2Propositional` with weight 4, admissible under
`weight_limit = 4`) does not transfer to the source
theory. Whether the user interfaces present such verdicts as source-level facts was not examined.

**Amalgamation.**

- `Logic/Logic.hs`: the per-logic method `ensures_amalgamability` defaults to
  `warning Amalgamates ("amalgamability test not implemented for logic " ++ show l)` — the
  default result is the *positive* answer with a warning. The comment above it reads "it suffices
  to compute a cocone that is weakly amalgamable".
- `Static/GTheory.hs`, `gEnsuresAmalgamability`: "currently only checks whether the diagram is
  homogeneous and if so, calls amalgamability check for the specific logic"; otherwise
  `error "heterogeneous amalgability check not yet implemented"`.
- `Static/WACocone.hs`, `weakly_amalgamable_colimit`: returns `signature_colimit` directly, with
  the comment "until amalgamability check is fixed, just return a colimit".
- `Comorphisms/LogicGraph.hs`: `squareMap = Map.empty -- for now`, `unionList = []`,
  `morphismList = [] -- for now`; `modificationList` has one entry.
- `is_weakly_amalgamable` is consumed only by exporters (`Logic/LGToJson.hs`, `Logic/LGToXml.hs`,
  `Persistence/LogicGraph.hs`); no proof-calculus or static-analysis code reads it.
- `isTransportable` on Grothendieck morphisms carries the comment "currently returns false for
  heterogeneous morphisms".

So, at this revision, the model-expansion half of heterogeneous soundness is enforced for prover
selection by a declared flag, and the amalgamation half is declared but not enforced across
logics.

### 5. Trace-relating compiler correctness: the trinity

Basis: normative for the theory (ESOP 2020 paper, Defs. 1.2, 2.1, 2.5; Thms. 2.4, 2.6, 2.8;
Lemma 2.7) + source (`Def.v`, `Galois.v`, `TraceCriterion.v`).

- `CC∼ ≡ ∀W. ∀t. W↓ ⇝ t ⇒ ∃s ∼ t. W ⇝ s`. Coq: `rel_TC := forall W t, sem__T (W ↓) t -> exists
  s, rel s t /\ sem__S W s`.
- `TP^τ ≡ ∀π_S. ∀W. W ⊨ π_S ⇒ W↓ ⊨ τ(π_S)`; `TP^σ ≡ ∀π_T. ∀W. W ⊨ σ(π_T) ⇒ W↓ ⊨ π_T`, where
  `W ⊨ π` means every trace of `W` is in `π` (Coq `τTP`, `σTP`).
- If `τ ⊣ σ` is a Galois connection on properties ordered by inclusion
  (`τ(π_S) ⊆ π_T ⇔ π_S ⊆ σ(π_T)`), then `TP^τ ⇔ TP^σ` (Thm. 2.4; Coq `Adj_σTP_iff_τTP`).
- The existential and universal images of a relation (Coq `low_rel`, `up_rel`) form a Galois
  connection (`induced_adj_law`), and `TP^τ̃ ⇔ CC∼ ⇔ TP^σ̃` (Thm. 2.6; Coq `rel_TC_τTP`,
  `rel_TC_σTP`).
- `∼ ↦ (τ̃, σ̃)` is a bijection between trace relations and Galois connections on trace
  properties, with inverse `s ∼̂ t ≡ t ∈ τ({s})` (Lemma 2.7). One may therefore *design* a
  compiler-correctness statement by choosing the property mapping first.
- Direction of abstraction (paper footnote 4): properties are contravariant in traces, so target
  *properties* form the abstract domain even though target *traces* are more concrete.
- Degenerate relations make the theorem vacuous. For the "cheating" relation
  `s ∼ t ≡ ∃W. W ⇝ s ∧ W↓ ⇝ t`, every compiler is `CC∼` (Coq `cmp_is_rel_TC` in
  `Relation4Correctness.v`), and if some program has every trace then `τ̃(π) = ⊤` for every
  non-empty `π` (`abstraction_lemma`, `no_trg_guarantee` in `NoTrgGuarantees.v`). Inspecting `τ̃`
  and `σ̃` is the paper's proposed test of whether a chosen `∼` is meaningful.

### 6. Closed forms for the standard relations

Basis: normative (paper §1, §3.1–§3.4, §4, §5.2); rows marked ✱ re-derived by the probe in §10.

`m ≤ t` is the prefix order; `·` is concatenation.

| Mismatch | Relation `s ∼ t` | `τ̃(π_S)` (target guarantee) | `σ̃(π_T)` (source obligation) | Consequence |
|---|---|---|---|---|
| Undefined behaviour (CompCert style) ✱ | `s = t ∨ ∃m ≤ t. s = m·Goes_wrong` | `π_S ∪ {t ∣ ∃m ≤ t. m·Goes_wrong ∈ π_S}` | `{s ∈ π_T ∣ s ≠ m·Goes_wrong} ∪ {m·Goes_wrong ∣ ∀t ≥ m. t ∈ π_T}` | "event never happens in the target" additionally requires absence of UB in the source |
| Target resource exhaustion (CakeML style) ✱ | `s = t ∨ ∃m ≤ s. t = m·Resource_Limit_Hit` | `π_S ∪ {m·Resource_Limit_Hit ∣ ∃s ∈ π_S. m ≤ s}` | `π_T ∩ {s ∣ ∀m ≤ s. m·Resource_Limit_Hit ∈ π_T}` | if `π_T` forbids exhaustion then `σ̃(π_T) = ∅`; safety maps to safety in both directions |
| Value representation (bool ↦ nat) | `true ∼ n` for `n > 0`, `false ∼ 0`, `n ∼ n`, lifted pointwise | any non-zero stands for `true` | `0` must be acceptable as both `0` and `false` | relation not injective: forward simulation cannot be flipped without the extra "flippable" condition |
| Granularity (one source send of a nested pair ↦ several target sends) | inductive flattening of pairs | forgets nesting, keeps values | source may regroup target events freely | a source safety property about a *particular nesting* maps to `⊤` |
| Timing side channel ✱ | `s ∼ t ≡ ∃n. t = (s, n)` | `π_S × ℕ^ω` | `{s ∣ ∀n. (s, n) ∈ π_T}` | source noninterference yields only timing-insensitive noninterference |
| Target-only events (linked adversarial context) | `s = t↾Σ_S` (`t` with target-only events erased) | source behaviour "sprinkled with arbitrary target-level behavior" | all enrichments of `s` must be in `π_T` | nothing can be claimed about target-only events from the source |

Unions: for relations on the same trace sets, a compiler that is `CC∼UB` or `CC∼RE` is `CC` for
`∼UB ∪ ∼RE`; the converse fails (paper §3.2).

### 7. Hyperproperties, noninterference and adversarial contexts

Basis: normative (ESOP 2020 §2.3, §4, §5; CSF 2019 §4).

- A hyperproperty is a set of behaviours (sets of traces); `W ⊨ H iff beh(W) ∈ H`. `CC=`
  preserves all *subset-closed* hyperproperties. For `CC∼` the direct image does not preserve
  subset closure, so the statement is `CC∼ ⇔ SCHP^{Cl⊆∘τ̃} ⇔ SCHP^{Cl⊆∘σ̃}` with
  `Cl⊆(H) = {π ∣ ∃π' ∈ H. π ⊆ π'}` (Thm. 2.11).
- With target traces `(s, n)` carrying execution time, `Cl⊆∘τ̃(NI_S)` is strictly weaker than
  target noninterference and equals an abstract-noninterference instance whose observer cannot
  distinguish execution times. In general (Thm. 4.1), when input and output relations are total
  maps from target to source and the input relation is surjective, source `ANI^{ρ_S}_{φ_S}` is
  compiled to `ANI^{ρ#_T}_{φ#_T}` with `φ#_T = g° ∘ φ_S ∘ f°`, `ρ#_T = g• ∘ ρ_S ∘ f•`. With
  undefined behaviour the output relation is not a total map and only a *family* of admissible
  target observers is characterised (Thm. 4.2).
- **Discrepancy found by execution.** The paper's display `Cl⊆∘τ̃(NI_S) = {π_S × I ∣ π_S ∈ NI_S ∧
  I ⊆ ℕ^ω}` (as extracted from the arXiv v4 PDF text) does not hold literally in the finite model
  of §10: the left side has 31 members, 12 of which — e.g. `{(s1, 0), (s2, 1)}` — are not
  products. The left side does equal the timing-insensitive noninterference set (31 = 31), so the
  paper's conclusion is unaffected; the product form should be read as "subsets of such products".
- **Robust (context-quantified) criteria.** `RTC∼ ≡ ∀P ∀C_T ∀t. C_T[P↓] ⇝ t ⇒ ∃C_S ∃s ∼ t.
  C_S[P] ⇝ s`, and `RTP^τ̃ ⇔ RTC∼ ⇔ RTP^σ̃` (Thm. 5.1). For safety: `RTP^{Safe∘τ̃} ⇔ RSC∼ ⇔
  RSP^σ̃` (Thm. 5.2), where `Safe(π_T)` is the smallest safety property containing `π_T`. The
  two property-full forms are asymmetric: the `σ̃` form quantifies over target safety
  properties, the `τ̃` form over *all* source properties followed by `Safe`, because a mapped
  property need not be a safety property. For arbitrary hyperproperties the trinity is weak:
  `RHC∼ ⇔ RHP^τ̃` unconditionally; `RHC∼ ⇒ RHP^σ̃` needs `τ̃ ∘ σ̃ = id` (Galois insertion);
  `RHP^σ̃ ⇒ RHC∼` needs `σ̃ ∘ τ̃ = id` (Galois reflection) (Thm. 5.3).
- **Order of quantifiers is the strength** (CSF 2019 §4.1): in `RTC` the simulating source
  context may depend on the target context, the program and the trace; in `RHC` only on the
  target context and the program; in `RrHC ≡ ∀C_T. ∃C_S. ∀P. Behav(C_T[P↓]) = Behav(C_S[P])` only
  on the target context. Relational hyperproperties (predicates on the behaviours of several
  programs, e.g. "`P1` runs faster than `P2` on all inputs", trace equivalence) need the last
  form; 2-relational *trace* properties need one source context simulating one trace of each of
  two programs (`R2rTC`).

| Property class to preserve | Property-free criterion | Source context may depend on |
|---|---|---|
| trace properties (integrity) | `RTC∼` | `C_T`, `P`, `t` |
| safety | `RSC∼` | `C_T`, `P`, finite prefix `m` |
| subset-closed hyperproperties / hypersafety (data confidentiality) | `RSCHC∼`, `RHSC∼` (named in the paper's Figure 2; definitions in its online appendix, not reproduced here) | — |
| arbitrary hyperproperties | `RHC∼` | `C_T`, `P` |
| 2-relational trace properties | `R2rTC∼` | `C_T`, `P1`, `P2`, `t1`, `t2` |
| relational hyperproperties (code confidentiality) | `RrHC` | `C_T` only |

### 8. CompCert as an instance

Basis: source (`AbsInt/CompCert@2685140b…`).

- `common/Behaviors.v`: `behavior_improves beh1 beh2 := beh1 = beh2 \/ exists t, beh1 =
  Goes_wrong t /\ behavior_prefix t beh2` — the undefined-behaviour relation of §6 with source
  first.
- `driver/Complements.v`, `transf_c_program_preservation`: for `transf_c_program p = OK tp` and
  `program_behaves (Asm.semantics tp) beh` there is `beh'` with `program_behaves (Csem.semantics
  p) beh' /\ behavior_improves beh' beh` — literally `CC∼` for that relation.
- `transf_c_program_preserves_spec` is stated only for `safety_enforcing_specification spec :=
  forall beh, spec beh -> not_wrong beh`. In the vocabulary of §5 this is the fragment on which
  `σ̃(π) = π` (the probe confirms it for all 8 safety-enforcing specifications of its finite
  model), i.e. where the source obligation is the property itself. The file's own counter-example
  for other specifications ("the program goes wrong on an undefined behavior") is the `τ̃`
  degradation of §6.
- Separate compilation (`separate_transf_c_program_preservation`) assumes a list of *C* units all
  compiled by `transf_c_program`, a source-level link `link_list c_units = Some c_program`, and
  derives that the Asm units link. It is a statement about same-compiler, same-language linking.

### 9. Composition laws for trace relations

Basis: derived + execution (§10), and source for the conjunction case.

- **Sequential passes.** If pass 1 is `CC∼1` (`S → I`) and pass 2 is `CC∼2` (`I → T`), the
  pipeline is `CC` for the relational composition `∼1;∼2`: a target trace `t` has a related
  intermediate trace `i` of `W↓1`, which has a related source trace `s` of `W`. The induced maps
  compose: `τ̃_{∼1;∼2} = τ̃_2 ∘ τ̃_1` and `σ̃_{∼1;∼2} = σ̃_1 ∘ σ̃_2`. End-to-end guarantees are
  therefore computed pass by pass, and *loss accumulates monotonically*: once a property has
  degraded to `⊤` no later pass restores it.
- **Union.** `CC∼1 ⇒ CC_{∼1 ∪ ∼2}`.
- **Intersection fails.** `CC∼1 ∧ CC∼2` does not imply `CC_{∼1 ∩ ∼2}`: the two witnesses may be
  different source traces. In `Composition.v` only `TPtau_for_conjunction : CCtilde1 /\ CCtilde2
  -> τTP` is proved, for the pointwise conjunction `τ(π) = τ1(π) ∩ τ2(π)`; the converse and the
  statement `conjunction_intersection : CCtilde1 /\ CCtilde2 <-> CCtilde_cap` are commented out,
  with the remark that "τ does not coincide with the abstraction of the galois connection
  induced by ~". Engineering reading: proving "values are refined" and "resources may run out"
  as two separate theorems about one compiler gives, for each source property, the conjunction
  of the two target guarantees — but not a single simulation that explains each target trace in
  both respects at once, which is what a later pass composed onto it would need.

### 10. Executable probe: Galois connection, trinity, hyperproperties, composition

Basis: execution.

```python
#!/usr/bin/env python3
"""Finite-model checks for trace-relating compiler correctness (stdlib only).

tau(pi_S)   = { t | exists s. s ~ t and s in pi_S }      (existential image)
sigma(pi_T) = { s | forall t. s ~ t implies t in pi_T }  (universal image)
CC~(B_S, B_T): every t in B_T has some s in B_S with s ~ t, where B_S / B_T
are the trace sets (behaviours) of a source program and of its compilation.
"""
from itertools import combinations, product


def subsets(xs):
    xs = sorted(xs)
    return [frozenset(c) for r in range(len(xs) + 1) for c in combinations(xs, r)]


def tau(rel, pi_s):
    return frozenset(t for (s, t) in rel if s in pi_s)


def sigma(rel, pi_t, src):
    return frozenset(s for s in src if all(t in pi_t for (s2, t) in rel if s2 == s))


def cc(rel, beh_s, beh_t):
    return all(any((s, t) in rel for s in beh_s) for t in beh_t)


def check_universe(name, src, tgt, rel):
    ps, pt = subsets(src), subsets(tgt)
    adj = sum((tau(rel, a) <= b) == (a <= sigma(rel, b, src)) for a in ps for b in pt)
    tri = mor = 0
    for bs in ps:
        for bt in pt:
            c = cc(rel, bs, bt)
            tp_tau = all(bt <= tau(rel, a) for a in ps if bs <= a)
            tp_sig = all(bt <= b for b in pt if bs <= sigma(rel, b, src))
            tri += (c == tp_tau == tp_sig)
            fc2 = all(t in bt for (s, t) in rel if s in bs)   # forward, universal
            iff = all((bs <= sigma(rel, b, src)) == (bt <= b) for b in pt)
            mor += (iff == (c and fc2))
    back = frozenset((s, t) for s in src for t in tau(rel, frozenset([s])))
    ins = all(tau(rel, sigma(rel, b, src)) == b for b in pt)   # tau . sigma = id
    refl = all(sigma(rel, tau(rel, a), src) == a for a in ps)  # sigma . tau = id
    print(f"[{name}] |S|={len(src)} |T|={len(tgt)} |~|={len(rel)} "
          f"adjunction {adj}/{len(ps) * len(pt)} trinity {tri}/{len(ps) * len(pt)} "
          f"morphism-iff-CC-and-FC2 {mor}/{len(ps) * len(pt)} "
          f"rel-recovered={back == rel} insertion={ins} reflection={refl}")
    return ps, pt


# U1: resource exhaustion.  '!' = Resource_Limit_Hit, target-only terminal event.
S1 = ["", "a", "b"]
T1 = S1 + [m + "!" for m in S1]
R1 = frozenset((s, t) for s in S1 for t in T1
               if s == t or (t.endswith("!") and s.startswith(t[:-1])))
ps1, pt1 = check_universe("resource-exhaustion", S1, T1, R1)
no_oom = [b for b in pt1 if not any(t.endswith("!") for t in b)]
print("  target properties forbidding '!':", len(no_oom), "; with empty source obligation:",
      sum(sigma(R1, b, S1) == frozenset() for b in no_oom))
print("  tau({'a'}) =", sorted(tau(R1, frozenset(["a"]))))

# U2: CompCert-style undefined behaviour.  '?' = Goes_wrong, same traces both sides.
U2 = ["", "a", "b", "?", "a?", "b?"]
R2 = frozenset((s, t) for s in U2 for t in U2
               if s == t or (s.endswith("?") and t.startswith(s[:-1])))
ps2, pt2 = check_universe("undefined-behaviour", U2, U2, R2)
safe = [b for b in pt2 if not any(t.endswith("?") for t in b)]
print("  safety-enforcing target specs:", len(safe), "; sigma(spec) == spec for",
      sum(sigma(R2, b, U2) == b for b in safe))
no_b_src = frozenset(t for t in U2 if "b" not in t)
print("  tau(source 'never b') == all target traces:", tau(R2, no_b_src) == frozenset(U2))

# U3: timing side channel.  Source trace = (secret, low_out); target adds a time in {0,1}.
S3 = [(h, o) for h in (0, 1) for o in (0, 1)]
T3 = [(s, n) for s in S3 for n in (0, 1)]
R3 = frozenset((s, (s, n)) for s in S3 for n in (0, 1))
ps3, pt3 = check_universe("timing", S3, T3, R3)
ni_s = frozenset(p for p in ps3 if len({o for (_, o) in p}) <= 1)
ni_t = frozenset(p for p in pt3 if len({(o, n) for ((_, o), n) in p}) <= 1)
img = frozenset(tau(R3, p) for p in ni_s)
cl_img = frozenset(q for q in pt3 if any(q <= p for p in img))
ani_t = frozenset(p for p in pt3 if len({o for ((_, o), _) in p}) <= 1)
products = frozenset(frozenset((s, n) for s in p for n in i)
                     for p in ni_s for i in subsets([0, 1]))
print("  |NI_S|=%d |NI_T|=%d |tau(NI_S)|=%d |Cl(tau(NI_S))|=%d" %
      (len(ni_s), len(ni_t), len(img), len(cl_img)))
print("  tau(NI_S) subset-closed:", all(q in img for p in img for q in subsets(p)))
print("  NI_T strictly inside Cl(tau(NI_S)):", ni_t < cl_img)
print("  Cl(tau(NI_S)) == timing-insensitive NI:", cl_img == ani_t)
print("  Cl(tau(NI_S)) == {pi_S x I}:", cl_img == products,
      "; non-product members:", len(cl_img - products))

# U4: all relations on 2-element trace sets: composition and conjunction.
A = [0, 1]
rels = subsets(list(product(A, A)))
pa = subsets(A)
comp_ok = comp_n = cc_comp_ok = cc_comp_n = 0
for r1 in rels:
    for r2 in rels:
        r12 = frozenset((s, t) for (s, i) in r1 for (i2, t) in r2 if i == i2)
        for p in pa:
            comp_n += 2
            comp_ok += tau(r12, p) == tau(r2, tau(r1, p))
            comp_ok += sigma(r12, p, A) == sigma(r1, sigma(r2, p, A), A)
        for bs, bi, bt in product(pa, pa, pa):
            if cc(r1, bs, bi) and cc(r2, bi, bt):
                cc_comp_n += 1
                cc_comp_ok += cc(r12, bs, bt)
print(f"[composition] functoriality {comp_ok}/{comp_n}; "
      f"CC~1 and CC~2 imply CC~1;~2 in {cc_comp_ok}/{cc_comp_n} cases")
both = bad = 0
witness = None
for r1 in rels:
    for r2 in rels:
        for bs, bt in product(pa, pa):
            if cc(r1, bs, bt) and cc(r2, bs, bt):
                both += 1
                if not cc(r1 & r2, bs, bt):
                    bad += 1
                    witness = witness or (sorted(r1), sorted(r2), sorted(bs), sorted(bt))
print(f"[conjunction] CC~1 and CC~2 both hold in {both} cases; CC for ~1 & ~2 fails in {bad}")
print("  first witness (~1, ~2, B_S, B_T):", witness)
```

Output of `python3 trace_galois_probe.py` (exit status 0, about 5 s):

```text
[resource-exhaustion] |S|=3 |T|=6 |~|=8 adjunction 512/512 trinity 512/512 morphism-iff-CC-and-FC2 512/512 rel-recovered=True insertion=False reflection=True
  target properties forbidding '!': 8 ; with empty source obligation: 8
  tau({'a'}) = ['!', 'a', 'a!']
[undefined-behaviour] |S|=6 |T|=6 |~|=13 adjunction 4096/4096 trinity 4096/4096 morphism-iff-CC-and-FC2 4096/4096 rel-recovered=True insertion=False reflection=False
  safety-enforcing target specs: 8 ; sigma(spec) == spec for 8
  tau(source 'never b') == all target traces: True
[timing] |S|=4 |T|=8 |~|=8 adjunction 4096/4096 trinity 4096/4096 morphism-iff-CC-and-FC2 4096/4096 rel-recovered=True insertion=False reflection=True
  |NI_S|=7 |NI_T|=13 |tau(NI_S)|=7 |Cl(tau(NI_S))|=31
  tau(NI_S) subset-closed: False
  NI_T strictly inside Cl(tau(NI_S)): True
  Cl(tau(NI_S)) == timing-insensitive NI: True
  Cl(tau(NI_S)) == {pi_S x I}: False ; non-product members: 12
[composition] functoriality 2048/2048; CC~1 and CC~2 imply CC~1;~2 in 3873/3873 cases
[conjunction] CC~1 and CC~2 both hold in 1681 cases; CC for ~1 & ~2 fails in 96
  first witness (~1, ~2, B_S, B_T): ([(0, 0)], [(1, 0)], [0, 1], [0])
```

Reading:

- `adjunction` and `trinity` quantify over *all* property pairs and *all* pairs of source/target
  behaviours of the finite universe (no sampling).
- `insertion` / `reflection` report whether `τ̃∘σ̃ = id` / `σ̃∘τ̃ = id`, the side conditions of
  the weak hyperproperty trinity (§7). Resource exhaustion and timing are reflections (source
  properties survive a round trip), neither is an insertion, and the undefined-behaviour
  relation is neither — so for it neither extra implication of Thm. 5.3 is available.
- `morphism-iff-CC-and-FC2`: for every behaviour pair, "`B_S ⊆ σ̃(π_T) ⇔ B_T ⊆ π_T` for all
  `π_T`" holds exactly when `CC∼` holds together with the forward-universal condition `FC2`
  (`∀s ∈ B_S. ∀t. s ∼ t ⇒ t ∈ B_T`; Coq `rel_FC2`, with `rel_FC2' : rel_FC2 <-> forall W,
  beh__S W ⊆ σ' (beh__T (W ↓))`). In institution terms (§1): taking single-signature logics whose
  sentences are trace properties and whose models are programs, the pair (sentence map `σ̃`,
  model map `↓`) is an institution *morphism* from the source logic to the target logic iff the
  compiler is `CC∼` and `FC2`; `CC∼` alone is the half "`W ⊨ σ̃(π_T) ⇒ W↓ ⊨ π_T`". Basis:
  derived + execution.

### 11. Cross-language linking and link-time optimisation

Basis: derived from §2, §5–§9, plus documentation/source/normative facts cited inline.

**System facts.**

- rustc documents `-C linker-plugin-lto` as "performing interprocedural optimizations across
  programming language boundaries if all the object files being linked were created by
  LLVM-based toolchains using the **same** LTO mode", with the rule of thumb "use an LLVM linker
  plugin whose version is at least as new as the newest compiler involved" and a table of known
  good rustc/Clang pairs (Rust 1.91–1.94 with Clang 21 at the pinned revision). Basis:
  documentation.
- rustc computes parameter attributes from the *Rust type* before any ABI-specific adjustment:
  `fn_abi_new_uncached` builds every argument with `arg_attrs_for_rust_scalar` and only then
  calls `fn_abi_adjust_for_abi`. That function sets `NoUndef` unless the scalar admits
  uninitialised values, `NonNull` when the pointer validity range excludes zero, `NoAlias` for
  frozen shared references, `Unpin` mutable references and (flag-dependent) boxes — never in
  return position — and `ReadOnly` for frozen shared references. Basis:
  source. Whether a given foreign-ABI adjustment later drops them was not examined.
- LLVM defines `noundef`: "If the value representation contains any undefined or poison bits,
  the behavior is undefined"; `nonnull`: a null argument becomes poison and "should be combined
  with the `noundef` attribute to ensure a pointer is not null or otherwise the behavior is
  undefined"; `noalias`: "If there are other accesses not based on the argument or return value,
  the behavior is undefined … Both the caller and the callee share the responsibility". Basis:
  normative (LangRef).

**Derived transport recipe.** Let module `M1` (language `L1`) carry claim `π1` proved in logic
`I1`, module `M2` (language `L2`) carry `π2` proved in `I2`, both lowered to a common IR and
linked across a boundary alphabet `Σ_b` (cross-module calls and returns).

1. *Logic bridge.* Choose a target institution `J` and comorphisms `I1 → J ← I2`. Translated
   claims are true in `J` wherever the originals were (preservation needs nothing). Anything
   subsequently *proved* in `J` is a fact about `J`-models; reading it back as a fact about
   `I1`/`I2` models needs model expansion on that side (§2).
2. *Language bridge, per module.* The other module is a target context that is not the
   compilation of any `L1` context, so whole-program `CC∼` is the wrong criterion; the needed
   statement is the robust one (`RTP^τ̃` for trace properties, stronger rows of §7 for
   confidentiality or relational claims) against IR-level contexts. CompCert-style separate
   compilation (§8) does not supply it for foreign contexts.
3. *Contract at the IR level.* Each claim must be re-stated against the IR open semantics
   *including the attributes the front ends emit*. An `L2` proof that treats a pointer parameter
   as possibly null, combined with an `L1` front end that marks the corresponding argument
   `nonnull noundef`, describes an IR program with undefined behaviour on that input; by the
   undefined-behaviour row of §6 nothing is then guaranteed about the target after that call.
4. *Compose, then hide.* With both claims over IR interaction traces, the linked program's
   behaviours lie in the synchronised product on `Σ_b`; this step is an amalgamation argument
   (§2) and fails in the same way when the two sides share state or symbols outside the declared
   boundary. Inlining across the boundary erases `Σ_b` events; as a trace relation this is
   `s ∼ t ≡ t = s↾Σ_ext` (erase boundary events), a total surjective function, so `τ̃` is the
   direct image, `σ̃` the
   pre-image, and `τ̃∘σ̃ = id`: every post-inlining property has an exact pre-inlining obligation,
   while a pre-inlining claim keeps only its `Σ_b`-insensitive content. In specification terms
   the re-anchored claim is the *hiding* of `Σ_b` from the combined specification; the DOL
   manuscript notes that hiding "has only a model-level semantics", whereas a theory-level
   replacement (`keep`/`forget`, a uniform interpolant) "need not always exist".
5. *Only then optimise.* After steps 1–4 the claim is a closed-program property over `Σ_ext`,
   and ordinary whole-program correctness of each LTO pass (composed as in §9) carries it to the
   final binary. Attempting the steps in the other order — optimise first, then look for the
   module claims — fails because the boundary at which they were stated no longer exists.

### 12. Choosing a criterion

Basis: derived (summary of the findings above).

| You hold | You want | Use | Watch for |
|---|---|---|---|
| a theorem in logic `I`, a stronger prover for `J` | the theorem in `I` | comorphism path with model expansion on every edge | infrastructure axioms; flags are declarations, not checks |
| a theory in `I`, a model finder for `J` | a model / counter-example | any comorphism with an implemented model reduct | "no model found" proves nothing without expansion |
| two theories over a shared interface | a consistent union | pushout signature + amalgamation | symbols unified by name outside the interface |
| a source trace property, a `CC∼` compiler | a target guarantee | `τ̃` of the property, pass by pass | properties that mention what `∼` forgets become `⊤` |
| a required target property | a source proof goal | `σ̃` of the property | `σ̃ = ∅` when the target can fail in ways the source cannot express |
| source noninterference | target noninterference | `Cl⊆∘τ̃`, or Thm. 4.1 form | target observer strictly stronger than source observer |
| a claim that must survive foreign or adversarial linked code | the same | robust criterion of the matching class (§7) | whole-program or same-compiler separate-compilation theorems do not apply |
| two separately proved relations for one compiler | a single relation for further composition | re-prove for the intersection | conjunction of guarantees ≠ `CC` for the intersection |

## Boundaries

- **Not examined:** the full texts of Goguen and Burstall (JACM 1992), Goguen and Roşu (2002),
  Diaconescu (2002), Mossakowski (MFCS 2002), Cerioli and Meseguer (1997) and the OMG DOL 1.0
  standard document (formal/18-09-02) could not be retrieved in the authoring environment; only
  their bibliographic records were verified. Definitions were therefore taken from the DOL
  manuscript and from Hets source comments. The published conditions under which Grothendieck
  institutions inherit amalgamation or interpolation are not reproduced here.
- **Not examined:** MMT/LATIN-style logical frameworks, the Hets development-graph proof calculus
  (`Proofs/*`) beyond prover selection, Hets conservativity checkers, and any Hets execution.
  Whether Hets front ends surface an "inconsistent" verdict obtained along a non-model-expansive
  path as a fact about the source theory is not examined.
- **Not examined:** correctness of individual Hets comorphism implementations against their
  declared flags. The census counts declarations only.
- **Not examined:** the remaining files of the Coq development (robust, hypersafety, relational
  and example compilers); it was not recompiled, so "proved" means "stated with a `Qed` proof
  script in the file read".
- **Not examined:** whether rustc's Rust-type-derived attributes survive
  `adjust_for_foreign_abi` on particular targets, and the behaviour of any actual cross-language
  LTO build. No compiler was run.
- **Unknown:** a most-powerful target observer for noninterference in the presence of undefined
  behaviour (the paper leaves its characterisation open after Thm. 4.2).
- **Unknown:** whether a mechanised development exists that composes per-module robust
  trace-relating results from two different source languages and then discharges cross-module
  inlining; none was found among the examined subjects. §11 is a derived recipe, not a reported
  theorem.
- **Known not to apply:** CompCert's separate-compilation theorems to mixed-language linking
  (they quantify over C units compiled by the same `transf_c_program`); whole-program `CC∼` to
  claims that must hold when linked with code that is not the compilation of a source context.
- **Known not to apply:** the finite-model probes to liveness-specific or topological statements
  (their trace sets are finite, so every property is a safety property), and to the `Safe`
  closure results.
- **Unsupported (by the subject):** heterogeneous amalgamability checking in Hets at the pinned
  revision (`error "heterogeneous amalgability check not yet implemented"`).
- **Stronger conclusions not established:** that a comorphism path chosen by Hets is sound
  because Hets offered it (prover paths rely on declared flags; other paths are unfiltered); that
  `CC∼` for a natural-looking relation preserves any particular property (compute `τ̃`); that
  preserving trace properties robustly preserves confidentiality (it does not; see the class
  table in §7).

## Evidence

All evidence was acquired on 2026-11-19.

**Repositories** (revision = commit resolved from the default branch head on that date; files
fetched from `raw.githubusercontent.com/<repo>/<revision>/<path>` or the revision's source
archive).

| Repository @ revision | Paths and anchors |
|---|---|
| `spechub/Hets@65ca27f4fcafd57f94fbb0908f2d88a16b0977ea` | `Logic/Comorphism.hs` (class `Comorphism` l.60–145; `InclComorphism` instance l.292–322; `CompComorphism` instance l.332–419; `compComorphism` l.488–506); `Logic/Grothendieck.hs` (`GMorphism` l.619 ff.; `findComorphismPaths` l.891; `logicGraph2Graph` l.895–914; `isTransportable` l.926–932; `weight_limit`, `times_logic_in_branch` l.1004–1008; `findComorphismCompositions` l.1067; `mapLogicsToComorphisms` l.1178; `comorphismWeight` l.1194 ff.); `Proofs/AbstractState.hs` (`getConsCheckers` l.371; `getAllProvers` l.491–499); `Logic/Logic.hs` (`ensures_amalgamability` l.493–508); `Static/GTheory.hs` (`gEnsuresAmalgamability` l.416–433, error at l.433); `Static/WACocone.hs` (`weakly_amalgamable_colimit` l.46–55); `Comorphisms/LogicGraph.hs` (`comorphismList` l.162 ff.; `unionList`, `morphismList`, `modificationList`, `squareMap` l.272–282); `Comorphisms/CASL2Prop.hs` l.88; `Comorphisms/CASL2Skolem.hs` l.65; `doc/UserGuide.tex` (section "Logic translations supported by Hets") |
| `secure-compilation/different_traces@e74dd632057b846d5ebca273dc218de968de3279` | `README.md`; `Def.v` (`σTP`, `τTP`, `G_σTP_iff_τTP`, `Adj_σTP_iff_τTP`); `Galois.v` (`low_rel`, `up_rel`, `induced_adj_law`, `induced_connection`); `TraceCriterion.v` (`rel_TC`, `rel_TC_τTP`, `rel_TC_σTP`, `rel_FC1`, `rel_FC2`, `rel_FC2'`); `Composition.v` (`TPtau_for_conjunction`; commented-out `conjunction_intersection`); `Relation4Correctness.v` (`cmp_is_rel_TC`); `NoTrgGuarantees.v` (`abstraction_lemma`, `no_trg_guarantee`) |
| `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc` | `common/Behaviors.v` l.41–82 (`program_behavior`, `not_wrong`, `behavior_improves`); `driver/Complements.v` l.31–52, l.130–171, l.205–275 |
| `rust-lang/rust@b0b600668bb9b4a897e2299b0a44289d42276545` | `src/doc/rustc/src/linker-plugin-lto.md`; `compiler/rustc_ty_utils/src/abi.rs` (`arg_attrs_for_rust_scalar` l.318 ff.; `fn_abi_new_uncached` l.532–621, with the call to `fn_abi_adjust_for_abi` at l.617; `fn_abi_adjust_for_abi` l.624 ff.) |
| `llvm/llvm-project@2bee3e393405d26213834265dd4478e88ff96d30` | `llvm/docs/LangRef.md` (parameter attributes `noalias` l.1510, `nonnull` l.1637, `noundef` l.1727) |

**Papers read in full text.**

- C. Abate, R. Blanco, Ş. Ciobâcă, A. Durier, D. Garg, C. Hriţcu, M. Patrignani, É. Tanter,
  J. Thibault, "Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020 (in
  *Programming Languages and Systems*, Lecture Notes in Computer Science), pp. 1–28, DOI
  10.1007/978-3-030-44914-8_1; text of arXiv:1907.05320v4 (camera-ready with
  online appendix).
- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani, J. Thibault, "Journey Beyond Full
  Abstraction: Exploring Robust Property Preservation for Secure Compilation", IEEE CSF 2019, DOI
  10.1109/CSF.2019.00025; text of arXiv:1807.04603v6.
- T. Mossakowski, M. Codescu, F. Neuhaus, O. Kutz, "The Distributed Ontology, Modeling and
  Specification Language – DOL", in *The Road to Universal Logic*, Studies in Universal Logic,
  2015, pp. 489–520, DOI 10.1007/978-3-319-15368-1_21; author manuscript at
  `https://www.inf.unibz.it/~okutz/resources/DOL-Manifesto.pdf`.

**Bibliographic records verified through the Crossref REST API (full text not read).**
Goguen and Burstall, "Institutions: abstract model theory for specification and programming",
J. ACM 39(1):95–146, 1992, DOI 10.1145/147508.147524. Goguen and Roşu, "Institution Morphisms",
Formal Aspects of Computing 13(3–5):274–307, 2002, DOI 10.1007/s001650200013. Diaconescu,
"Grothendieck Institutions", Applied Categorical Structures 10(4):383–402, 2002, DOI
10.1023/A:1016330812768. Mossakowski, "Comorphism-Based Grothendieck Logics", MFCS 2002, LNCS
2420, pp. 593–604, DOI 10.1007/3-540-45687-2_49 (abstract read: "amalgamation properties play a
rôle" for completeness of the heterogeneous proof calculus). Mossakowski, Maeder, Lüttich, "The
Heterogeneous Tool Set, Hets", TACAS 2007, LNCS 4424, pp. 519–522, DOI
10.1007/978-3-540-71209-1_40. Cerioli and Meseguer, "May I borrow your logic? (Transporting
logical structures along maps)", Theoretical Computer Science 173(2):311–347, 1997, DOI
10.1016/S0304-3975(96)00160-0. Mossakowski, "Relating CASL with other specification languages:
the institution level", Theoretical Computer Science 286(2):367–475, 2002, DOI
10.1016/S0304-3975(01)00369-3. Gardiner, Martin, de Moor, "An algebraic construction of predicate
transformers", Science of Computer Programming 22(1–2):21–44, 1994, DOI
10.1016/0167-6423(94)90006-X (cited by the ESOP paper for the relation/predicate-transformer
bijection). Clarkson and Schneider, "Hyperproperties", J. Computer Security 18(6):1157–1210,
2010, DOI 10.3233/JCS-2009-0393. The OMG page for DOL 1.0 lists document formal/18-09-02
(publication date March 2018).

**Execution.** CPython 3.13.15 on Linux, standard library only. The two programs are reproduced
verbatim in Findings §3 and §10; SHA-256 of the files as run:
`4d26b01a9086114e69d6603714dadaf82dd4a15c1ab2a14a5403bf535d03c0e9` (`institution_probe.py`) and
`016393cfc956f45cb169e01006e783b6d27164e0acc53ae52265937e2dfad69f` (`trace_galois_probe.py`).
Both are deterministic (no randomness, no I/O besides stdout).

**Census commands** (run in the extracted Hets source archive):

```bash
grep -rn --include=*.hs -E '^\s*instance Comorphism' . | wc -l                 # 65
grep -rn --include=*.hs -E '^\s+has_model_expansion .*= True' . | wc -l        # 53
grep -rn --include=*.hs -E '^\s+is_weakly_amalgamable .*= True' . | wc -l      # 37
grep -rn --include=*.hs -E '^\s+is_model_transportable .*= True' . | wc -l     # 11
grep -rn --include=*.hs -E '^\s+(rps|eps|isGTC) ' . | grep -v Logic/Comorphism.hs
grep -rn --include=*.hs -E '\b(hasModelExpansion|isWeaklyAmalgamable|isEps|isRps)\b' .
```

## Revalidation

- **Hets soundness filters** (cheapest, most likely to drift): at a new revision, re-read
  `logicGraph2Graph` and `findComorphismCompositions` in `Logic/Grothendieck.hs` and check
  (a) whether the `hasModelExpansion && isRps && isEps` filter is still present, (b) whether the
  second search acquired a filter, (c) the default values in class `Comorphism`. Re-run the
  census commands in Evidence; a change in the 53/37/11 counts or in the list of flag-less
  modules signals that the per-comorphism table needs refreshing.
- **Hets amalgamation**: grep for `heterogeneous amalgability check not yet implemented`,
  `just return a colimit` and `squareMap = Map.empty`. Disappearance of any of the three
  invalidates the corresponding bullet of §4.
- **Transport laws and trace-relation laws**: copy the two programs from §3 and §10 into files
  and run `python3 institution_probe.py` and `python3 trace_galois_probe.py`; outputs must match
  the blocks above byte for byte. To test a *new* trace relation, add its universe to the second
  program through `check_universe` and read off `insertion`/`reflection` and the closed forms; to
  test a new logic encoding, supply its `alpha`, `beta` and target-model list to
  `comorphism_condition`, `expansive` and `borrowing`. A passing probe establishes the laws only
  for the finite models it enumerates.
- **Coq development**: `make -j4` in the repository with the Coq/MathComp versions named in its
  README replays the proofs; `grep -n "Admitted\|conjunction_intersection" Composition.v` shows
  whether the intersection result has been completed.
- **CompCert**: `grep -n "behavior_improves\|safety_enforcing_specification" common/Behaviors.v
  driver/Complements.v` and compare with §8.
- **LTO facts**: re-read `arg_attrs_for_rust_scalar` and the call order in `fn_abi_new_uncached`;
  re-read the three LangRef attribute entries; compare the toolchain table at the end of
  `linker-plugin-lto.md`. To turn the "not examined" boundary on attribute survival into a
  finding, compile a two-line `extern "C" fn f(x: &u8)` with `--emit=llvm-ir` for the target of
  interest and inspect the parameter attributes.
- **No cheap revalidation exists** for §11's recipe as a whole; establishing it for a concrete
  language pair requires the robust per-module theorems and a linking theorem for the IR's open
  semantics.
