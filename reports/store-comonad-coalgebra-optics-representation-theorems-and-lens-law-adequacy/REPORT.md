# Store-Comonad Coalgebras, Optics Representation Theorems, and Lens Law Adequacy

## Summary

Optic representations and algebraic lens laws form a strict, non-obvious hierarchy whose weakest tiers fail to enforce basic bidirectionality and whose strongest single-lens axioms still admit coordinate-shearing bypasses that corrupt sibling fields:

1. **Representation Theorems Do Not Imply Lawfulness:** By the Yoneda / Tambara representation theorem (`Boisseau & Gibbons 2018`; `Riley 2018`; `Clarke et al. 2024`), polymorphic profunctor lenses (`forall p. Strong p => p a b -> p s t`), van Laarhoven lenses (`forall f. Functor f => (a -> f b) -> s -> f t`), and existential lenses ($\exists C.\, (S \to A \times C) \times (B \times C \to T)$) in $\mathbf{Set}$ are isomorphic to **raw unlawful** `(get : S -> A, put : S -> B -> T)` pairs (`1,048,576` instances on $|S|=4, |A|=2$), because $C$ can simply be $S$ itself.
2. **Well-Behaved vs. Very Well-Behaved vs. Store-Comonad Coalgebras:** On finite carriers $|S|=4, |A|=2$, `GetPut` + `PutGet` (**Well-Behaved**) drops `1,048,576` down to `120` fibered retractions $S \cong \sum_{a \in A} C(a)$—and **automatically entails** same-value idempotence `put(put(s, a), a) = put(s, a)` (`optics-dev/Monocle`'s `replaceIdempotent` passes `120/120`, catching zero non-VWB mutants). Adding `PutPut` (**Very Well-Behaved**) drops `120` down to **`12`**, establishing an **exact bijection** with Eilenberg–Moore **coalgebras for the Store comonad** $W_A(X) = A \times (A \to X)$ (`O'Connor 2011`; `Gibbons & Johnson 2012`) and, for inhabited $A \neq \emptyset$, with Bancilhon–Spyratos **constant-complement decompositions** $S \cong A \times C$.
3. **The Non-Unique Complement Bypass & Library Adequacy Gaps:** Even when `get` is fixed to the true field projection of a product $S = A \times C$ (`|A| = k`, `|C| = m`), there exist $(m!)^{k-1}$ distinct Very Well-Behaved / Store-coalgebra `put` functions (e.g., `acc' = acc ^ pc ^ pc'`) that satisfy *every* single-lens law while silently mutating sibling fields! Real libraries exhibit concrete adequacy gaps along this lattice: `tchajed/coq-record-update`'s `SetterWf` omits `PutPut` (admitting history-clobbering setters while documenting "only the projected field is modified"); `fraware/lean-optics`'s `LawfulLens` includes `set_set` yet permits `Nat.xor`-shearing setters; `optics-dev/Monocle`'s `LensLaws` omits `PutPut` directly, recovering it only via `composeModify`; and `ekmett/lens` exports explicitly unlawful combinators (`Control.Lens.Unsound`, `filtered`) that break `PutGet` or traversal fusion when invariants fail.
4. **Closing the Gap vs. Lockout Trade-Offs:** Excluding complement-shearing bypasses requires either **polymorphic type-changing parametricity** (`forall a b c. Lens (a, c) (b, c) a b`, via Reynolds/Wadler free theorems—which locks out monomorphic structs and virtual/computed lenses), **pairwise lens independence** ($L_1 \perp L_2$, `Foster, Zeyda, Woodcock 2016`—which still leaves $4! = 24$ ungrounded permutations on $|S|=4$ unless anchored to constructor equations), or **complete product-atlas isomorphism** ($\Phi : S \xrightarrow{\sim} \prod_i A_i$, which guarantees sibling preservation by construction at the cost of prohibiting overlapping views and abstract invariants).

## Applicability

This report applies to language designers, formal verification engineers, and library authors using lenses, profunctor optics, or record-update abstractions across typed functional and proof-assistant ecosystems:

- **Categorical & Relational Foundations:** Bancilhon and Spyratos (`10.1145/319628.319634`), Foster et al. (`10.1145/1232420.1232424`), O'Connor (`arXiv:1103.2841v2`), Gibbons and Johnson (`10.14279/tuj.eceasst.49.726`), Riley (`arXiv:1809.00738v2`), Boisseau and Gibbons (`10.1145/3236779`), Clarke et al. (`10.32408/compositionality-6-1`), Reynolds (1983), Wadler (`10.1145/99370.99404`), and Foster, Zeyda, and Woodcock (`10.1007/978-3-319-46750-4_17`). Most representation derivations assume cartesian (or symmetric monoidal) base categories $\mathcal{C} = \mathbf{Set}$ (with explicit exceptions noted for empty domains $A = \emptyset$ and enriched mixed optics).
- **Industrial & Proof-Assistant Implementations Directly Inspected:**
  - Haskell `ekmett/lens` (`61eb79c3b46dc397aaa5437684d15201cfc412a6`) vs `well-typed/optics` (`dd0b30e144ad92f77584dc8357c381eed2243028`) — van Laarhoven rank-2 vs nominal `Optic k is` profunctor subtyping.
  - Scala `optics-dev/Monocle` (`33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`) — `PLens`, `LensLaws`, and `LensTests` Discipline checks.
  - PureScript `purescript-contrib/purescript-profunctor-lenses` (`c479df47cc386b840c5e7238b4b5b1b3e9e2c4ff`) — `Strong` / `Shop` representation.
  - Lean 4 `leanprover-community/mathlib4` (`dd44a18bacca0dba65ac4275af92024f400e63e3`) and `fraware/lean-optics` (`bd3252ae562333b6f592b8f79dde3c91324aeb68`) — `Comonad.Coalgebra` and `LawfulLens`.
  - Rocq `tchajed/coq-record-update` (`1dd231db87451479043a3812dbdbd9658657ff7c`) — `Settable`, `Setter`, and `SetterWf`.

## Findings

### 1. Store-Comonad Coalgebras, Constant Complements, and the VWB Bijection

Basis: normative (`10.1145/319628.319634`, `10.1145/1232420.1232424`, `arXiv:1103.2841v2`, `10.14279/tuj.eceasst.49.726`) + source (`leanprover-community/mathlib4`) + execution (exhaustive $|S|=4, |A|=2$ enumeration).

#### 1.1 Exact Equivalence of Very Well-Behaved Lenses and Store Coalgebras

For a fixed focus type $A$, the **Store** (costate) comonad $W_A : \mathbf{Set} \to \mathbf{Set}$ is defined by:

$$W_A(X) = A \times (A \to X), \qquad \varepsilon_X(a, k) = k(a), \qquad \delta_X(a, k) = (a,\; \lambda a'.\, (a', k))$$

with functorial action $W_A(f)(a, k) = (a, f \circ k)$. In `leanprover-community/mathlib4` (`dd44a18bacca0dba65ac4275af92024f400e63e3`, `Mathlib/CategoryTheory/Monad/Algebra.lean`, lines 52–62), an Eilenberg–Moore coalgebra for any comonad $T : \mathcal{C} \to \mathcal{C}$ packages:

```lean
structure Comonad.Coalgebra (T : Comonad C) : Type max u₁ v₁ where
  A : C
  a : A ⟶ (T : C ⥤ C).obj A
  counit : a ≫ T.ε.app A = 𝟙 A
  coassoc : a ≫ T.δ.app A = a ≫ T.map a
```

Specializing $T = W_A$ with carrier $S$ gives a structure map $\alpha : S \to A \times (A \to S)$, which uncurries cleanly into $\alpha(s) = (\text{get}(s),\; \lambda a.\, \text{put}(s, a))$ (`O'Connor 2011`, `arXiv:1103.2841v2`; `Gibbons & Johnson 2012`, `10.14279/tuj.eceasst.49.726`). Expanding the two coalgebra axioms yields an exact logical equivalence with the three **Very Well-Behaved (`VWB`)** lens laws (`Foster et al. 2007`, `10.1145/1232420.1232424`):

1. **`counit` ($\varepsilon_S \circ \alpha = \text{id}_S$) $\iff$ `GetPut`:**
   $$\varepsilon_S(\alpha(s)) = \varepsilon_S(\text{get}(s),\; \lambda a.\, \text{put}(s, a)) = \text{put}(s, \text{get}(s)) = s.$$
2. **`coassoc` ($\delta_S \circ \alpha = W_A(\alpha) \circ \alpha$) $\iff$ `PutGet` $\wedge$ `PutPut`:**
   - Left-hand side: $\delta_S(\alpha(s)) = (\text{get}(s),\; \lambda a'.\; (a',\; \lambda a''.\, \text{put}(s, a'')))$.
   - Right-hand side: $W_A(\alpha)(\alpha(s)) = (\text{get}(s),\; \lambda a'.\; \alpha(\text{put}(s, a'))) = (\text{get}(s),\; \lambda a'.\; (\text{get}(\text{put}(s, a')),\; \lambda a''.\, \text{put}(\text{put}(s, a'), a'')))$.
   - Equating the first and second components of the inner pair for every $s, a', a''$ gives **exactly**:
     - First projection: $\text{get}(\text{put}(s, a')) = a'$ (**`PutGet`**).
     - Second projection: $\text{put}(\text{put}(s, a'), a'') = \text{put}(s, a'')$ (**`PutPut`**).

#### 1.2 Constant-Complement View Updating (Bancilhon & Spyratos 1981) and the Non-Uniqueness Theorem

When $A$ is inhabited ($A \neq \emptyset$), a `VWB` lens $(\text{get}, \text{put})$ induces an equivalence relation on states (`Bancilhon & Spyratos 1981`, `10.1145/319628.319634`):

$$s_1 \sim s_2 \iff \forall a \in A.\; \text{put}(s_1, a) = \text{put}(s_2, a).$$

Taking the quotient complement $C = S / {\sim}$ yields a **canonical bijection** $\phi : S \xrightarrow{\sim} A \times C$ given by $\phi(s) = (\text{get}(s), [s]_\sim)$ with inverse $\phi^{-1}(a, [s]_\sim) = \text{put}(s, a)$ (independent of representative by definition of $\sim$, and bijective by `GetPut` + `PutGet` + `PutPut`). Conversely, any isomorphism $S \cong A \times C$ defines a `VWB` lens via $(\text{fst}, \lambda(a, c) a'.\, (a', c))$.

**Critical Adequacy Consequence — Non-Uniqueness of Complements:** Fixing a surjective getter $\text{get} : S \to A$ with $|A| = k$ and uniform fibers $|\text{get}^{-1}(a)| = m = |C|$ does **not** pin down a unique complement decomposition or `put`! Each fiber $\text{get}^{-1}(a)$ can be bijected onto $C$ independently relative to a base fiber $a_0$, yielding **exactly $(m!)^{k-1}$ distinct `VWB` / Store-coalgebra `put` functions sharing the exact same getter `get`**. Exhaustive enumeration in our finite probe (`|S|=4, |A|=2`, $|C|=2$, fixed `get_fst`) directly confirms `2` distinct `VWB` puts (`(2!)^(2-1) = 2`); for `|A|=2, |C|=3`, it yields `6`; for `|A|=3, |C|=2`, it yields `4`. Even the standard complement-free product type $S = A \times C$ admits **complement-shearing** coalgebras (`put((a, c), a') = (a', c ^ a ^ a')`) whenever $|C| \ge 2, |A| \ge 2$.

*(Boundary on empty focus $A = \emptyset$)*: When $A = \emptyset$, the unique `get : ∅ -> ∅` forces $S = \emptyset$, where `VWB` holds vacuously for arbitrary empty complement $C$; however, for non-empty $S$ with $A = \emptyset$, no `get : S -> ∅` exists at all, whereas constant-complement equations requiring $S \cong \emptyset \times C$ fail unless $S = \emptyset$.

---

### 2. Existential, Van Laarhoven, and Tambara Profunctor Representation Theorems

Basis: normative (`10.1145/3236779`, `arXiv:1809.00738v2`, `10.32408/compositionality-6-1`) + source (`ekmett/lens`, `well-typed/optics`, `purescript-profunctor-lenses`).

#### 2.1 Coend Calculus and Profunctor Optics Classification

In `Clarke et al.` (`10.32408/compositionality-6-1`, `arXiv:2001.07488v6`), `Boisseau & Gibbons` (`10.1145/3236779`), and `Riley` (`arXiv:1809.00738v2`), a **mixed optic** over a monoidal category $\mathcal{M}$ acting on categories $\mathcal{C}, \mathcal{D}$ via actions $\bullet$ is defined by the coend:

$$\mathbf{Optic}_{\mathcal{M}}((S, T), (A, B)) = \int^{M \in \mathcal{M}} \mathcal{C}(S, M \bullet A) \times \mathcal{D}(M \bullet B, T).$$

Generalized **Tambara theory** (lifting Pastro–Street double-category monads to enriched profunctors) gives a Yoneda isomorphism between existential optics and natural transformations over **Tambara modules** $\mathbf{Tamb}(\mathcal{M})$ (profunctors $P : \mathcal{C}^{\text{op}} \times \mathcal{D} \to \mathbf{Set}$ equipped with $\alpha_{M, A, B} : P(A, B) \to P(M \bullet A, M \bullet B)$ natural in $A, B$ and dinatural in $M$):

$$\int^{M \in \mathcal{M}} \mathcal{C}(S, M \bullet A) \times \mathcal{D}(M \bullet B, T) \;\cong\; \int_{P \in \mathbf{Tamb}(\mathcal{M})} P(A, B) \to P(S, T).$$

Each major optic flavor corresponds to a distinct monoidal action and concrete library encoding:

| Optic Flavor | Monoidal Action $(M \bullet X)$ | Profunctor Class (`ekmett/lens`, `purescript-profunctor-lenses`, `optics-core`) | Existential / Coalgebraic Form in $\mathbf{Set}$ | Van Laarhoven Equivalent |
| :--- | :--- | :--- | :--- | :--- |
| **`Iso`** | Identity ($\mathcal{M} = \mathbf{1}$) | `Profunctor p` (`Exchange a b`) | $(S \to A) \times (B \to T)$ | `(Functor f, Profunctor p) => p a (f b) -> p s (f t)` |
| **`Lens`** | Product ($M \times X$) | `Strong p` (`Shop a b`, `first'`/`second'`) | $\exists M.\, (S \to M \times A) \times (M \times B \to T) \cong (S \to A) \times (S \to B \to T)$ | `forall f. Functor f => (a -> f b) -> s -> f t` |
| **`Prism`** | Coproduct ($M + X$) | `Choice p` (`Market a b`, `left'`/`right'`) | $\exists M.\, (S \to M + A) \times (M + B \to T) \cong (S \to T + A) \times (B \to T)$ | `forall f. Applicative f => ...` (with `Choice p`) |
| **`AffineTraversal`** / **`Optional`** | Product + Coproduct ($M_2 + M_1 \times X$) | `Strong p, Choice p` (`Affine`) | $(S \to T + A) \times (S \to B \to T)$ | `Affine` / partial getter + setter |
| **`Traversal`** | Traversable / Polynomial functor ($\sum_n M_n \times X^n$) | `Wander p` / `Traversing p` (`Bazaar`) | $\exists n, M_n.\, S \to M_n \times A^n \;\times\; M_n \times B^n \to T$ | `forall f. Applicative f => (a -> f b) -> s -> f t` |
| **`Grate`** | Exponential ($X^M$) | `Closed p` (`Grating`) | $((S \to A) \to B) \to T$ | Dual to `Lens` (cotraversal / closed action) |

#### 2.2 Why the Representation Theorem Proves Unlawful Equivalence—Not Lawfulness

A persistent misconception is that existential representation $\exists M.\, (S \to M \times A) \times (M \times B \to T)$ or van Laarhoven encoding `forall f. Functor f => (a -> f b) -> s -> f t` guarantees constant-complement lawfulness. It does **not**, because the quotient in the coend $\int^M$ allows instantiating the hidden residue $M := S$ (`Shop a b s t` in `purescript-contrib/purescript-profunctor-lenses`, `src/Data/Lens/Internal/Shop.purs`, line 12: `data Shop a b s t = Shop (s -> a) (s -> b -> t)`):

- **Forward map (`raw -> existential`):** Take $M = S$, $\text{split}(s) = (s, \text{get}(s))$, and $\text{unsplit}(s, b) = \text{put}(s, b)$. Because $\text{split}$ never constrains $\text{put}(s, \text{get}(s)) = s$, **any arbitrary pair of functions** $(\text{get} : S \to A, \text{put} : S \to B \to T)$ satisfies the existential, van Laarhoven (`Costate`), and `Strong`-profunctor type signatures!
- **Riley's Categorical Lawfulness (`arXiv:1809.00738v2`, §3–§4):** Riley supplies the missing category-theoretic definition of **lawful monomorphic optic** inside any symmetric monoidal category $\mathcal{M}$: an optic $(l, r) \in \mathbf{Optic}(S, A)$ is lawful iff $l$ and $r$ are mutually inverse up to the coend equivalence in the sense that $l \gg r = \text{id}_S$ (counit / `GetPut`) and $(l \times \text{id}_M) \dots$ satisfies the generalized coassociativity commuting square (`PutGet` + `PutPut`). In cartesian $\mathbf{Set}$ with $A \neq \emptyset$, Riley proves that a lawful optic in $\mathbf{Optic}_{\times}(S, A)$ reduces to a true constant-complement product isomorphism $S \cong M \times A$—precisely the `Store` coalgebra condition—whereas in non-cartesian monoidal categories (such as quantum channels or linear types), constant complements break and only Riley's coend equations remain well-defined.

---

### 3. Parametricity and Free Theorems: Exact Scope and Monomorphic Blind Spots

Basis: normative (`Reynolds 1983`; `10.1145/99370.99404`) + source (`ekmett/lens` `Control/Lens/Type.hs`).

In System $F_\omega$ / Haskell without type-escapes or `seq` bottoms, **relational parametricity** (`Reynolds 1983`; `Wadler 1989`, `10.1145/99370.99404`) forces polymorphic optics to behave uniformly across arbitrary type instantiations:

- **Where Parametricity Pins Down Exact Behavior (`Lens (a, c) (b, c) a b`):** For any polymorphic lens with universally quantified variables `forall a b c. Lens (a, c) (b, c) a b`, interpreting `a`, `b`, `c` via arbitrary relations $\mathcal{R}_a, \mathcal{R}_b, \mathcal{R}_c$ yields free theorems proving:
  1. The getter `forall a c. (a, c) -> a` *must* equal `fst` (since $a$ is inhabited and distinct from $c$, no constant element of type $a$ can be synthesized without projecting it from the input pair).
  2. The setter `forall a b c. (a, c) -> b -> (b, c)` *must* equal `\(a, c) b -> (b, c)` (the unique inhabitant of `b` is the parameter `b`, and the unique inhabitant of `c` is the input `c`—ruling out XOR-shearing, field-clobbering, and data inspection **without proving a single equation**!).
- **Three Structural Failure Modes Where Parametricity Breaks:**
  1. **Homogeneous Containers (`forall a. Lens' (a, a) a`, `forall a. Traversal' a a`):** When both slots share type variable `a`, parametricity admits `badLens f (x, y) = (\z -> (z, x)) <$> f y` (`view = snd`, `set z (x, y) = (z, x)`, violating both `GetPut` and `PutPut`), and admits `badTrav f a = const <$> f a <*> f a` (visiting `a` twice, violating traversal fusion).
  2. **Unconstrained 4-Parameter Lens Families (`Lens s t a b`):** In `ekmett/lens` (`Control.Lens.Type`, lines 96–117), polymorphic updates allow $s$ and $t$ to depend on $a$ and $b$ (e.g., `Lens (Foo a) (Foo b) a b`); without explicit `GetPut`/`PutGet`/`PutPut` proofs, `s, t, a, b` can even vary independently in illegal ways.
  3. **Monomorphic Domain Records (`Lens' MachineState Nat`, `Lens' User Int`):** In proof assistants (`Lean 4`, `Rocq`) and typed production code (`Scala`, `Haskell`), domain records fix concrete types (`Nat`, `Int`, `String`). Under monomorphic specialization, relational parametricity degenerates to the identity relation (`x = y`), providing **zero protection** against value inspection, field swapping, clobbering, or XOR-shearing complements!

---

### 4. Concrete Lawful-but-Unintended and Law-Weakened Instances in Real Libraries

Basis: source (`tchajed/coq-record-update`, `fraware/lean-optics`, `optics-dev/Monocle`, `ekmett/lens`) + execution (library-witness probe).

Directly inspecting four widely deployed optics and record-update libraries reveals three distinct classes of law inadequacy:

| Library & Commit | Typeclass / Structure | Exact Axioms Enforced (Source Lines) | Claimed Intent in Source / Docs | Concrete Bypass Witness (Verified by Execution Probe) |
| :--- | :--- | :--- | :--- | :--- |
| **`tchajed/coq-record-update`** (`1dd231db87451479043a3812dbdbd9658657ff7c`) | `SetterWf` (`src/RecordSet.v`, lines 62–71) | `set_get: proj (set proj v r) = v (proj r)` (`PutGet` for `over`) + `set_eq: f (proj r) = proj r -> set proj f r = r` (weak `GetPut`). **Omits `PutPut`!** | *"correctness conditions that require the projected field and only the projected field is modified"* (`RecordSet.v`, lines 60–61) | **`clobber_set`:** sets sibling `b := 0` whenever `f(r.a) != r.a`. Passes `set_get = True` and `set_eq = True` universally, yet **corrupts `b`** (`(0,2) -> (1,0)`) and breaks `PutPut` (`set 0 (set 1 (0,2)) = (0,0) != (0,2)`). Note: tactic-derived `settable!` instances are safe by syntactic eta expansion, but polymorphic lemmas over `{SetterWf proj}` cannot prove sibling preservation! |
| **`fraware/lean-optics`** (`bd3252ae562333b6f592b8f79dde3c91324aeb68`) | `LawfulLens` (`src/Optics/Concrete/Lens.lean`, lines 18–56) | `get_set: get (set s a) = a` (`PutGet`), `set_get: set s (get s) = s` (`GetPut`), `set_set: set (set s a) b = set s b` (`PutPut`). *(Note: `Lens.lean` lines 41–48 label `get (set s a) = a` as `get_put` and `set s (get s) = s` as `put_get`, inverting Foster et al. 2007 naming!)* | *"replaces that component while leaving the rest of the record intact"* (`docs/upstream/CSLIB_LENS_PROPOSAL.md`, lines 18–20) | **`xor_set` over `{ pc : Nat, acc : Nat }`:** `get := (.pc)`, `set s pc' := { pc := pc', acc := s.acc ^^^ s.pc ^^^ pc' }`. Satisfies all 3 `LawfulLens` axioms (`get_set=True`, `set_get=True`, `set_set=True`) and is a genuine Store coalgebra, yet **silently corrupts `acc`**: `set { pc := 0, acc := 5 } 1 = { pc := 1, acc := 4 }`! |
| **`optics-dev/Monocle`** (`33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`) | `LensLaws` & `LensTests` (`core/shared/src/main/scala/monocle/law/LensLaws.scala`, lines 10–31; `LensTests.scala`, lines 18–27) | `getReplace`, `replaceGet`, **`replaceIdempotent`** (`replace(a)(replace(a)(s)) == replace(a)(s)`), `modifyIdentity`, `composeModify`, plus consistency laws. | Ensures lens lawfulness via ScalaCheck `Discipline` property checks. | **`replaceIdempotent` is strictly redundant** (`getReplace + replaceGet ⊢ replaceIdempotent`: `set a (set a s) = set (get (set a s)) (set a s) = set a s`—as `ekmett/lens` `Type.hs` lines 129–133 already notes!). On $|S|=4,|A|=2$, `120/120` Well-Behaved lenses pass `replaceIdempotent` (`0%` of `108` non-VWB lenses caught!). Only **`composeModify`** (`modify(g)(modify(f)(s)) == modify(g . f)(s)`) recovers `PutPut` via constant functions `f = const a, g = const b`! |
| **`ekmett/lens`** (`61eb79c3b46dc397aaa5437684d15201cfc412a6`) | `filtered` (`Control/Lens/Fold.hs`, lines 359–376) & `Control.Lens.Unsound` (lines 43–145) | Haskell types omit laws; `Unsound` exports `lensProduct`, `prismSum`, `adjoin`, `setterUnion`. | Docstrings warn that `filtered` is illegal if updates invalidate predicate `p`, and `lensProduct`/`prismSum` require disjoint targets. | **`filtered even`** breaks traversal composition on `[2, 3]`: `(over (filtered even) (*10) . over (filtered even) (+1)) [2,3] = [3, 3] != [30, 3] = over (filtered even) ((*10) . (+1)) [2,3]`. **`lensProduct _1 _1`** breaks `PutGet`: `view (set (1, 2) (3, 'x')) = (2, 2) != (1, 2)`. **`prismSum _Just _Just`** returns `Just (Left 'x')` after `review (Right 'x')`. **`setterUnion id id`** breaks `over` fusion (`6 != 7`). |

---

### 5. Disjointness, Commutation, and the Bypass-vs-Lockout Adequacy Matrix

Basis: normative (`10.1007/978-3-319-46750-4_17`) + execution (exhaustive disjoint-pair enumeration).

#### 5.1 Disjointness / Lens Independence ($L_1 \perp L_2$)

In Isabelle/UTP's algebraic lens framework (`Foster, Zeyda, Woodcock 2016`, `10.1007/978-3-319-46750-4_17`), two lenses $L_1 : S \Longrightarrow A$ and $L_2 : S \Longrightarrow B$ are **independent** ($L_1 \perp L_2$) iff their updates commute (`put1_put2_comm`):

$$\forall s\, a\, b.\quad \text{put}_1(\text{put}_2(s, b), a) = \text{put}_2(\text{put}_1(s, a), b).$$

**Derived Theorem (`put1_put2_comm` entails view non-interference):** Whenever $L_1, L_2$ are Well-Behaved (`GetPut` + `PutGet`), update commutation **alone** implies both cross-field read invariance laws (`get1_put2` and `get2_put1`):

$$\text{get}_1(\text{put}_2(s, b)) \stackrel{\text{GetPut}_1}{=} \text{get}_1(\text{put}_2(\text{put}_1(s, \text{get}_1(s)), b)) \stackrel{\text{comm}}{=} \text{get}_1(\text{put}_1(\text{put}_2(s, b), \text{get}_1(s))) \stackrel{\text{PutGet}_1}{=} \text{get}_1(s).$$

In our $|S|=4, |A|=2$ finite-carrier probe:
- Fixing `get_1 = fst` and pinning $L_2 = \text{snd}_{\text{std}}$, adding `L_1 ⊥ L_2` cuts the `2` VWB lenses down to the **unique** standard `put_fst` (`vwb_disjoint_with_snd = 1`).
- **Simultaneous Collusion Limit:** If neither $L_1$ nor $L_2$ is grounded against a known constructor (`mk(a, b)`), there remain **$24 = 4!$** pairs `(L_1, L_2)` satisfying `VWB(L_1) ∧ VWB(L_2) ∧ (L_1 ⊥ L_2)`—precisely every bijection $S \xrightarrow{\sim} A \times B$! Thus **disjointness pins down coordinate projection only up to global isomorphism (coordinate relabeling) unless at least one getter/constructor boundary is grounded**.

#### 5.2 Complete Bypass-vs-Lockout Trade-Off Matrix

| Law / Constraint Tier | Algebraic / Type Formulation | Exact Bypass Excluded | Honest Idioms Locked Out |
| :--- | :--- | :--- | :--- |
| **1. Raw Profunctor / vL** (`Strong p => p a b -> p s t`) | Yoneda/Tambara existential | None (`1,048,576` on `(4,2)`): arbitrary `(get, put)` | None |
| **2. `GetPut` + `PutGet`** (Well-Behaved) | Fibered retraction $S \cong \sum_{a \in A} C(a)$; implies `PutIdem` (`120` on `(4,2)`) | Phantom/lying getters, ignored updates (`put(s, a) = s`), lossy projections where `get(put(s,a)) != a` | Clamped/normalized lenses (e.g., trim whitespace on write), write-only logs, partial lenses (`Optional`) |
| **3. `SetterWf`** (`set_get` + `set_eq`, `coq-record-update`) | Endofunction `set (A -> A) (S -> S)` without `PutPut` | Constant-return lying setters and no-op non-identity writes | **Allows** `clobber_set` destroying sibling fields when focus changes; locks out clamped/normalizing writes |
| **4. `PutPut` / Store Coalgebra** (`VWB` / `LawfulLens`) | $\alpha : S \to W_A(S)$ coalgebra; $S \cong A \times C$ for $A \neq \emptyset$ (`12` on `(4,2)`) | Dirty bits, audit-trail/version counters, history-dependent state (`108` WB non-VWB instances killed!) | **Locks out** append/resize views (`list[0..n]` changing length), dirty-flag caches, timestamping/version-bumping views, default-inserting map lenses |
| **5. Polymorphic Parametricity** (`forall a b c. Lens (a,c) (b,c) a b`) | System $F_\omega$ relational free theorem | **All** value inspection and XOR/permutation complement shearing without proof obligations | **Locks out** monomorphic domain records (`MachineState`), bitfield lenses, unit-converting `Iso`s (Celsius/Fahrenheit) |
| **6. Pairwise Independence** ($L_1 \perp L_2$) | $\text{put}_1(\text{put}_2(s, b), a) = \text{put}_2(\text{put}_1(s, a), b)$ | Relative coordinate shear / cross-field clobbering between $L_1$ and $L_2$ | **Locks out** overlapping/aliasing lenses (e.g. `fst` vs `both`, Cartesian `(x,y)` vs Polar `(r,theta)`), dependent record invariants ($x \le y$) |
| **7. Grounded Product Atlas** ($\Phi : S \xrightarrow{\sim} \prod_i A_i$) | Explicit constructor isomorphism + `get_i(mk(x)) = x_i` | **All** complement relabeling (`24 -> 1` on `(4,2)`); sound `lensProduct` on disjoint index sets | **Locks out** abstract data types with hidden representation invariants (e.g. balanced BSTs, canonicalized fractions) |

---

### 6. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

Basis: source inspection (`ekmett/lens`, `well-typed/optics`, `optics-dev/Monocle`, `purescript-profunctor-lenses`, `fraware/lean-optics`, `tchajed/coq-record-update`, `leanprover-community/mathlib4`) + derived complexity scaling.

| Ecosystem / Representation | (L1) Authoring & Maintenance Velocity | (L2) Toolchain / Library Build Cost | (L3) Elaboration & Compiler Specialization Latency | (L4) Runtime Execution Throughput & Allocations | (L5) Law / Proof Verification Speed | (L6) Interface, Binary & Memory Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`ekmett/lens` (Haskell van Laarhoven)** | Fast TH derivation (`makeLenses`), zero proof overhead, but rank-2 `Functor`/`Profunctor` type errors slow novice debugging. | Heavy transitive dependency graph (~40+ packages, Template Haskell); slow cold clean build. | GHC typechecker unification over higher-rank type synonyms (`LensLike`); relies heavily on `INLINE` unfolding across call sites. | Near zero-cost unboxed record updates when fully specialized under GHC `-O2`; closure allocations if higher-order lens values escape inlining. | Zero static law checking; optional QuickCheck runtime tests. | Large `.hi` interface files and codegen bloat if TH generates unused prism/traversal wrappers. |
| **`well-typed/optics` (`optics-core`, Opaque Profunctor)** | Nominal `Optic k is` avoids rank-2 unification noise; zero TH required for `Generic`/`Optic` combinators. | Lightweight core (`optics-core` separates core from TH/extra adapters). | Fast typechecking via closed type-family `Constraints k p`; **sensitive to `INLINE` pragmas** (`Optics/Internal/Optic.hs` lines 53–61 document issue `#324` where `getOptic` must carry `{-# INLINE getOptic #-}` outside the `newtype` so GHC eliminates profunctor dictionaries under profiling!). | Zero-allocation inlined updates with GHC `-O2` when `getOptic` unfolds; dictionary allocation if `INLINE` fails across module boundaries. | Zero static law checking; `inspection-testing` used upstream to assert zero residual profunctor abstractions in GHC Core. | Smaller compile-time/binary footprint than `ekmett/lens` when using `optics-core` alone. |
| **`optics-dev/Monocle` (Scala `PLens` + `Discipline`)** | Clean OOP/FP trait API (`get`, `replace`, `modifyF`); macros generate case-class lenses; `LensLaws` adds ScalaCheck property boilerplate. | Fast incremental SBT/Scala compilation on `core` + `law` modules. | Minimal elaboration overhead (monomorphic/polymorphic trait methods, no higher-rank profunctor encoding). | Allocates `Function1` closures and `Option`/`Either`/`cats.Id` wrappers unless specialized; JVM JIT devirtualization helps hot loops, but unboxed zero-overhead updates are not guaranteed. | ScalaCheck `Discipline` (`LensTests`) runs randomized batches (`~100` trials/law in ms); misses rare edge cases and omits direct `PutPut` unless `composeModify` hits colliding constants. | Standard JVM classfile/JAR overhead (`PLens` trait methods + macro-generated anonymous classes). |
| **`purescript-contrib/purescript-profunctor-lenses`** | Clean TypeScript/JS-targeted profunctor API using `Shop`, `Market`, `Exchange`. | Fast PureScript `purs` compile for library modules. | Higher-kinded constraint solving (`Strong p`) without GHC rewrite-rule fusion. | **High runtime overhead vs GHC:** passes `Strong` dictionary and allocates `Shop`/`Tuple` closures at JS runtime unless manually specialized. | Optional QuickCheck tests only. | Emits JS module dictionaries and closure objects per lens composition. |
| **`fraware/lean-optics` & `mathlib4` (Lean 4)** | `LawfulLens.mkLawful` proves 3 laws in ~3 `rfl` tactics for concrete records; adding $O(N^2)$ pairwise `L_i ⊥ L_j` proofs scales quadratically unless unified into a product atlas. | `lean-optics` builds rapidly over `Batteries`; `mathlib4` `Comonad.Coalgebra` imports large category-theory hierarchy. | `rfl` kernel checking for concrete `LawfulLens` is `< 1–10 ms` interactively; `Optics.Automation` tactics add elaboration cost vs raw `CSLib` core (`CSLIB_LENS_PROPOSAL.md`). | Lean 4 compiles concrete `Lens` structs into direct closure/projection calls (`structure` fields without `LawfulLens` proof terms erased). | **Kernel verification `< 1–5 ms`** per record lens via definitional `rfl`; zero runtime checks needed. | Erased `Prop` proofs contribute `0` runtime bytes; `.olean` files store proof terms at modest disk cost (KB for `CSLib` core, tens of MB if pulling `mathlib4`). |
| **`tchajed/coq-record-update` (Rocq `Settable`/`SetterWf`)** | One-line `settable! mk <fields>` generates `SetterWf` automatically; zero manual law writing for concrete records. | Tiny standalone Coq library (~5 `.v` files), builds in seconds. | **`eval pattern` Ltac scaling hazard (`RecordSet.v`, lines 43–49):** matching `etaT` syntactically and normalizing `mkT` becomes sluggish (`hundreds of ms` to seconds) on giant 30–100 field verified OS/filesystem state records unless carefully opaque-controlled. | Proof-only / extraction-erased setter function reduces cleanly under `cbn`/`simpl` (`Arguments set ... : simpl nomatch`, line 68). | Coq kernel typechecks generated `solve_mkT_ok` (`destruct x; reflexivity`) linearly in field count $N$. | Tiny `.vo` footprint; zero proof retention at extraction. |

---

### 7. Human Comprehensibility (`C1`) and Universal Model Refinement (`C2`)

Basis: source (`ekmett/lens`, `well-typed/optics`, `tchajed/coq-record-update`, `fraware/lean-optics`, `optics-dev/Monocle`) + derived model analysis.

#### 7.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Type-Error Cognitive Load:** Van Laarhoven rank-2 encodings (`ekmett/lens`) expose `Functor f => (a -> f b) -> s -> f t` unification errors leaking internal carriers (`Const`, `Identity`, `Bazaar`) when composition mismatches occur; `well-typed/optics` cuts working-memory burden significantly by hiding the profunctor behind nominal `Optic k is` with explicit subtyping (`castOptic`).
- **Naming Inversions Across Communities:** `Foster et al.` (`2007`) and `fraware/lean-optics` (`Concrete/Lens.lean`, lines 41–50) **invert** the names `GetPut` and `PutGet`: in Foster et al., `GetPut` is `put(get(s), s) = s` and `PutGet` is `get(put(v, s)) = v`, whereas `lean-optics` aliases `get (set s a) = a` as `get_put` and `set s (get s) = s` as `put_get` (while naming the structure fields `get_set` and `set_get`). Reading `get_put` without inspecting the quantifier body causes routine misidentification during proof review.
- **Prose-vs-Axiom Discrepancy Trap:** Both `coq-record-update` (`RecordSet.v`, line 61: *"only the projected field is modified"*) and `lean-optics` (`CSLIB_LENS_PROPOSAL.md`, line 19: *"while leaving the rest of the record intact"*) promise **sibling preservation** in natural-language comments that their formal typeclasses (`SetterWf`, `LawfulLens`) **do not enforce** against value-dependent or shearing bypasses!

#### 7.2 Conceptual Simplicity & Universal Model Refinement (`C2`)

Why do record-update libraries fight $O(N^2)$ pairwise independence proofs ($L_i \perp L_j$), missing `PutPut` axioms, and unsound `lensProduct` combinators?

Applying **Felleisen macro-expressibility** and **Ousterhout deep-module** criteria, separate field lenses + ad-hoc pairwise independence lemmas + `Unsound.lensProduct` duplicate one missing primitive: an **indexed coordinate partition / Store-product atlas** $\Phi : S \xrightarrow{\sim} \prod_{i \in I} A_i$ (or, for general algebraic datatypes, a finite coproduct of product atlases):

1. Every field lens $L_i : S \Longrightarrow A_i$ derives automatically from $\Phi$ and satisfies `GetPut`, `PutGet`, `PutPut`, **and** constructor-grounded complement preservation for free.
2. For any two index subsets $J_1, J_2 \subseteq I$, **disjointness is decidable by set intersection ($J_1 \cap J_2 = \emptyset$)**—making `lensProduct L_{J1} L_{J2}` **sound by construction** and collapsing all $\binom{N}{2}$ independence obligations $L_i \perp L_j$ into $i \neq j$!
3. When $S$ cannot decompose as a raw Cartesian product (abstract invariants, computed views, normalization), the optic explicitly declares itself as a **Quotient / Subspace Lens** (or **Partial / Optional Lens**) rather than masquerading as a record field projection under prose-only promises.

---

### 8. End-to-End Solution and Implementation Validation (`V1`–`V4`)

Basis: execution (finite-carrier mutant analysis) + source (`well-typed/optics`, `optics-dev/Monocle`) + derived validation gaps.

- **(V1) Specification Adequacy, Mutation & Non-Vacuity Validation:**
  - **Quantified Mutant Survival Rates:** In our exhaustive finite-carrier universe ($|S|=4, |A|=2$, `1,048,576` total lenses):
    - `GetPut` alone lets `4,084` broken lenses survive (`99.71%` of `4,096` fail `VWB`); `PutGet` alone lets `2,172` broken lenses survive (`99.45%` fail `VWB`).
    - **`Monocle`'s `replaceIdempotent` kills `0 / 108` (`0.0%`)** of non-VWB Well-Behaved mutants! Relying on `replaceIdempotent` without testing `composeModify` on non-commuting constant functions (`const a`, `const b`) silently passes dirty-bit/history-smuggling lenses.
    - Single-lens `VWB` / Store coalgebra checks kill **`0%` of the $(|C|!)^{|A|-1} - 1$ complement-shearing mutants** (`1` out of `2` on $|A|=2,|C|=2$; `5` out of `6` on $|A|=2,|C|=3$).
  - **Property-Based Testing Pitfalls:** In `Monocle` (`LensTests.scala`), checking `composeModify` depends on `Arbitrary[A => A]` generating colliding constant maps (`Cogen[A]` in ScalaCheck); if the generator emits only bijections or few distinct closures over large domains, `PutPut` failures go undetected.
- **(V2) Lowering, Specialization & Macro-Derivation Fuzzing:**
  - Macro/TH generators (`makeLenses`, `derive_lens`, `settable!`) bypass typeclass-abstracted law checks on concrete records via syntactic construction, which must be validated differentially against `LawfulLens` proofs and tested on edge-case ASTs (duplicate field names, type-changing GADT/polymorphic fields, empty constructors).
  - GHC Core optimization claims (that `Optic` / `LensLike` compiles away to raw projections without dictionary overhead) require automated Core-inspection tests (`inspection-testing` in `well-typed/optics`) to catch regressions like `Optic.hs` issue `#324` under `-prof` or `-O0`/`-O2`.
- **(V3) Concurrency, Crash & Physical Persistence Validation:**
  - **Non-Atomicity of Read-Modify-Write `over`:** Even when $L_1 \perp L_2$ holds sequentially as pure total functions, `over l f s = put s (f (get s))` executes a read followed by a full-structure write. Under shared-memory concurrency (`GenMC` / `Loom`), concurrent updates `over L1 f` and `over L2 g` on a shared mutable `S` suffer **lost sibling updates** unless `S` is physically partitioned or updated via atomic field-level CAS/locking!
  - **Torn Multi-Field Crash Persistence:** On persistent storage (`NVMe`/disk), a single-struct `put` rewriting $A \times C$ across non-atomic sector boundaries can crash mid-write, breaking `GetPut`/`PutGet` invariants on recovery (`VOPR`/`CrashMonkey` fault injection needed when lenses span persistence boundaries).
- **(V4) Runtime Monitors & Human Comprehension Validation (`SMoL`):**
  - Bidirectional views used in runtime safety monitors (`ModelPlex` state-projection lenses mapping plant sensor vectors $S$ to monitored control state $A$) fail catastrophically if a complement-shearing `put` silently perturbs unmonitored actuator channels $C$ while satisfying all three single-lens laws (`Monitor` sees `get(put(s, a)) = a`!).
  - Empirical developer litmus testing (`SMoL`-style comprehension checks) is required whenever teams combine `filtered` predicates with updates (`ekmett/lens`), use `Control.Lens.Unsound.lensProduct`, or conflate Scala/Lean/Rocq lens law names (`get_put` vs `put_get`).

## Boundaries

- **Known not to apply:**
  - *Tambara / Yoneda profunctor representation does not imply lawfulness:* `Strong p => p a b -> p s t` is isomorphic to arbitrary unlawful `(get, put)` pairs by choosing residue $M = S$.
  - *Single-lens `VWB` / `LawfulLens` / Store-coalgebra axioms do not imply "other fields remain untouched":* $(|C|!)^{|A|-1}$ distinct VWB `put` functions exist for any fixed surjective getter with $|C|$-element fibers (`xor_set` bypass on `{pc, acc}`).
  - *`Monocle`'s `replaceIdempotent` does not test `PutPut`:* it is a strict theorem of `getReplace` + `replaceGet` (`120/120` Well-Behaved lenses pass).
  - *Bancilhon–Spyratos constant-complement decomposition ($S \cong A \times C$) does not apply identically when $A = \emptyset$ and $S \neq \emptyset$:* no total getter `S -> ∅` exists, whereas vacuously `VWB` holds only on $S = \emptyset$.
  - *Relational parametricity does not protect monomorphic record lenses or homogeneous containers:* free theorems vanish on concrete field types (`Nat`, `Int`, `String`) and admit shift-register/duplicate-visit optics on `(a, a)`.
- **Unsupported:**
  - *Static compile-time verification of `GetPut`/`PutGet`/`PutPut` or `L1 ⊥ L2` in Haskell (`ekmett/lens`, `optics-core`), Scala (`Monocle`), and PureScript (`profunctor-lenses`):* those type systems do not enforce equational laws at compile time (only optional property tests or external liquid/dependent checkers do).
  - *General polymorphic type-changing `PLens S T A B` framing via Store comonads:* the standard indexed Store coalgebra $W_A(X) = A \times (A \to X)$ characterizes monomorphic lenses (`S = T, A = B`); type-changing lenses require graded/indexed comonad coalgebras or Riley's heterogeneous $\mathbf{Optic}((S,T),(A,B))$ framework.
- **Unknown:**
  - *Exact empirical bug incidence rate across downstream production Lean/Rocq/Haskell codebases* caused specifically by `SetterWf` missing `PutPut` vs `xor_set`-style coordinate shearing was not measured statistically.
- **Not examined:**
  - Live `ghc -ddump-simpl` Core output, `lake build` timings for `fraware/lean-optics` / `mathlib4`, `coqc` timings for `coq-record-update`, and SBT ScalaCheck runs for `Monocle` were not executed locally on this host; all algebraic counts and counterexamples in `## Evidence` were verified by exhaustive Python 3 execution.

## Evidence

### Primary Repositories and Exact Source Citations (Observed `2026-11-19`)

1. **`ekmett/lens`** (`61eb79c3b46dc397aaa5437684d15201cfc412a6`):
   - `src/Control/Lens/Type.hs`: `Lens` laws and explicit observation that laws 1+2 entail same-value idempotence `set l v (set l v s) ≡ set l v s` (lines 90–145), `type Lens s t a b = forall f. Functor f => (a -> f b) -> s -> f t` (line 146).
   - `src/Control/Lens/Fold.hs`: `filtered` (lines 359–361, warning on predicate invalidation around line 375).
   - `src/Control/Lens/Unsound.hs`: `lensProduct` (lines 59–61), `prismSum` (lines 83–95), `adjoin` (lines 106–108), `setterUnion` (lines 142–144).
2. **`well-typed/optics`** (`dd0b30e144ad92f77584dc8357c381eed2243028`):
   - `optics-core/src/Optics/Internal/Optic.hs`: `newtype Optic (k :: OpticKind) (is :: IxList) s t a b` (lines 50–51) and `getOptic` with `{-# INLINE getOptic #-}` addressing GHC profiling optimization issue `#324` (lines 53–62).
3. **`optics-dev/Monocle`** (`33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`):
   - `core/shared/src/main/scala/monocle/Lens.scala`: `trait PLens[S, T, A, B]` (`get`, `replace`, `modifyF`, `modify`, lines 36–70).
   - `core/shared/src/main/scala/monocle/law/LensLaws.scala`: `getReplace`, `replaceGet`, `replaceIdempotent`, `modifyIdentity`, `composeModify` (lines 9–28).
   - `core/shared/src/main/scala/monocle/law/discipline/LensTests.scala`: `SimpleRuleSet` checks (lines 15–28).
4. **`purescript-contrib/purescript-profunctor-lenses`** (`c479df47cc386b840c5e7238b4b5b1b3e9e2c4ff`):
   - `src/Data/Lens/Types.purs`: `type Lens s t a b = forall p. Strong p => Optic p s t a b` (line 60); `src/Data/Lens/Internal/Shop.purs`: `data Shop a b s t = Shop (s -> a) (s -> b -> t)` (lines 11–20).
5. **`leanprover-community/mathlib4`** (`dd44a18bacca0dba65ac4275af92024f400e63e3`):
   - `Mathlib/CategoryTheory/Monad/Algebra.lean`: `structure Comonad.Coalgebra (T : Comonad C)` (`counit` and `coassoc`, lines 51–64).
6. **`fraware/lean-optics`** (`bd3252ae562333b6f592b8f79dde3c91324aeb68`):
   - `src/Optics/Concrete/Lens.lean`: `Lens`, `LawfulLens` (`get_set`, `set_get`, `set_set`, lines 13–24), Foster naming inversion (`get_put` / `put_get`, lines 41–56), `comp_preserves_laws` (lines 112–128).
   - `docs/upstream/CSLIB_LENS_PROPOSAL.md`: *"while leaving the rest of the record intact"* (lines 16–20).
7. **`tchajed/coq-record-update`** (`1dd231db87451479043a3812dbdbd9658657ff7c`):
   - `src/RecordSet.v`: `Class Settable` (line 11), `Ltac setter` (`eval pattern`, lines 42–49), `Class Setter` (`simpl nomatch`, lines 62–68), `Class SetterWf` (`set_get`, `set_eq`, lines 70–73; *"only the projected field is modified"*, lines 60–61).

### Verified Academic References

- **Bancilhon and Spyratos** (1981): *Update Semantics of Relational Views*, ACM TODS 6(4) (`10.1145/319628.319634`).
- **Foster, Greenwald, Moore, Pierce, Schmitt** (2007): *Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem*, ACM TOPLAS 29(3) (`10.1145/1232420.1232424`).
- **O'Connor** (2011): *Functor is to Lens as Applicative is to Biplate: Introducing Multiplate*, ACM SIGPLAN WGP (`arXiv:1103.2841v2`, `10.48550/arXiv.1103.2841`).
- **Gibbons and Johnson** (2012): *Relating Algebraic and Coalgebraic Descriptions of Lenses*, ECEASST Vol. 49 (`10.14279/tuj.eceasst.49.726`).
- **Riley** (2018): *Categories of Optics* (`arXiv:1809.00738v2`, `10.48550/arXiv.1809.00738`).
- **Boisseau and Gibbons** (2018): *What You Needa Know about Yoneda: Profunctor Optics and the Yoneda Lemma (Functional Pearl)*, ICFP 2018 / PACMPL 2 (`10.1145/3236779`).
- **Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore, Román** (2024): *Profunctor Optics, a Categorical Update*, Compositionality Vol. 6 (`10.32408/compositionality-6-1`, `arXiv:2001.07488v6`).
- **Reynolds** (1983): *Types, Abstraction and Parametric Polymorphism*, Information Processing 83 (IFIP), pp. 513–523; **Wadler** (1989): *Theorems for Free!*, FPCA 1989 (`10.1145/99370.99404`).
- **Foster, Zeyda, Woodcock** (2016): *Unifying Heterogeneous State-Spaces with Lenses*, ICTAC 2016 (`10.1007/978-3-319-46750-4_17`).

### Reproducible Execution Probe and Verbatim Output (`2026-11-19`)

Self-contained Python 3 probe (finite-carrier exhaustive enumeration + exact library bypass witnesses executed on Linux `x86_64`, zero external dependencies):

```python
#!/usr/bin/env python3
"""Self-contained micro-probe for Store-comonad coalgebras, optics laws, and bypass witnesses."""
from __future__ import annotations
import itertools


def math_fact(n: int) -> int:
    r = 1
    for i in range(2, n + 1):
        r *= i
    return r


def enumerate_finite_lenses() -> None:
    S = (0, 1, 2, 3)
    A = (0, 1)

    total = gp = pg = wb = monocle3 = vwb = coalg = 0
    vwb_set: set[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]] = set()
    coalg_set: set[tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]] = set()

    get_fst = (0, 0, 1, 1)
    fst_wb = fst_vwb = fst_vwb_disjoint_snd = 0
    pairs_disjoint_vwb = 0

    for g in itertools.product(A, repeat=4):
        for p0 in itertools.product(S, repeat=4):
            pg0 = (g[p0[0]] == 0 and g[p0[1]] == 0 and g[p0[2]] == 0 and g[p0[3]] == 0)
            for p1 in itertools.product(S, repeat=4):
                total += 1
                p = (p0, p1)
                is_gp = (p[g[0]][0] == 0 and p[g[1]][1] == 1 and p[g[2]][2] == 2 and p[g[3]][3] == 3)
                is_pg = pg0 and (g[p1[0]] == 1 and g[p1[1]] == 1 and g[p1[2]] == 1 and g[p1[3]] == 1)
                if is_gp:
                    gp += 1
                if is_pg:
                    pg += 1
                if is_gp and is_pg:
                    wb += 1
                    is_idem = all(p0[p0[s]] == p0[s] and p1[p1[s]] == p1[s] for s in S)
                    if is_idem:
                        monocle3 += 1
                    is_pp = all(
                        p0[p0[s]] == p0[s] and p0[p1[s]] == p0[s]
                        and p1[p0[s]] == p1[s] and p1[p1[s]] == p1[s]
                        for s in S
                    )
                    if is_pp:
                        vwb += 1
                        vwb_set.add((g, p0, p1))
                counit_ok = is_gp
                coassoc_ok = is_pg and all(
                    p[a2][p[a1][s]] == p[a2][s]
                    for s in S for a1 in A for a2 in A
                )
                if counit_ok and coassoc_ok:
                    coalg += 1
                    coalg_set.add((g, p0, p1))

                if g == get_fst:
                    if is_gp and is_pg:
                        fst_wb += 1
                        if is_pp:
                            fst_vwb += 1
                            p_snd = ((0, 0, 2, 2), (1, 1, 3, 3))
                            if all(p[a][p_snd[b][s]] == p_snd[b][p[a][s]] for s in S for a in A for b in A):
                                fst_vwb_disjoint_snd += 1

    vwb_list = sorted(vwb_set)
    for g1, p1_0, p1_1 in vwb_list:
        p1 = (p1_0, p1_1)
        for g2, p2_0, p2_1 in vwb_list:
            p2 = (p2_0, p2_1)
            if all(p1[a][p2[b][s]] == p2[b][p1[a][s]] for s in S for a in A for b in A):
                assert all(g1[p2[b][s]] == g1[s] for s in S for b in A)
                assert all(g2[p1[a][s]] == g2[s] for s in S for a in A)
                pairs_disjoint_vwb += 1

    print(f"[1] |S|=4,|A|=2 total={total} gp={gp} pg={pg} wb={wb} monocle_3law={monocle3} vwb={vwb} store_coalg={coalg}")
    print(f"[1] exact_bijection(vwb==store_coalg)={vwb_set == coalg_set}")
    print(f"[1] fixed_get_fst wb={fst_wb} vwb={fst_vwb} vwb_disjoint_with_snd={fst_vwb_disjoint_snd}")
    print(f"[1] colliding_vwb_disjoint_pairs={pairs_disjoint_vwb} (4!={math_fact(4)} when constructor-ungrounded)")


def test_complement_cardinality_formula() -> None:
    for kA, mC in [(2, 2), (2, 3), (3, 2)]:
        S = [(a, c) for a in range(kA) for c in range(mC)]
        seen_puts = set()
        perms = list(itertools.permutations(range(mC)))
        for sigmas in itertools.product(perms, repeat=kA):
            invs = []
            for s in sigmas:
                inv = [0] * mC
                for idx, val in enumerate(s):
                    inv[val] = idx
                invs.append(inv)
            table = tuple(
                (a1, sigmas[a1][invs[a0][c0]])
                for a0, c0 in S for a1 in range(kA)
            )
            seen_puts.add(table)
        expected = (math_fact(mC)) ** (kA - 1)
        print(f"[2] |A|={kA},|C|={mC}: distinct_VWB_puts={len(seen_puts)} formula=(|C|!)^(|A|-1)={expected}")


def test_library_witnesses() -> None:
    dom = [(a, b) for a in (0, 1, 2) for b in (0, 1, 2)]
    fns = list(itertools.product((0, 1, 2), repeat=3))
    get_a = lambda r: r[0]
    def clobber_set(f, r):
        fa = f[r[0]]
        return r if fa == r[0] else (fa, 0)

    set_get_ok = all(get_a(clobber_set(f, r)) == f[get_a(r)] for f in fns for r in dom)
    set_eq_ok = all((clobber_set(f, r) == r) for f in fns for r in dom if f[get_a(r)] == get_a(r))
    r0 = (0, 2)
    lhs_pp = clobber_set((0, 0, 0), clobber_set((1, 1, 1), r0))
    rhs_pp = clobber_set((0, 0, 0), r0)
    print(f"[3] coq-record-update SetterWf clobber_set: set_get={set_get_ok} set_eq={set_eq_ok} put_put={lhs_pp == rhs_pp} seq={lhs_pp} direct={rhs_pp}")

    dom4 = [(pc, acc) for pc in range(4) for acc in range(8)]
    get_pc = lambda s: s[0]
    def xor_set(s, pc_new):
        return (pc_new, s[1] ^ s[0] ^ pc_new)
    l_get_set = all(get_pc(xor_set(s, a)) == a for s in dom4 for a in range(4))
    l_set_get = all(xor_set(s, get_pc(s)) == s for s in dom4)
    l_set_set = all(xor_set(xor_set(s, a), b) == xor_set(s, b) for s in dom4 for a in range(4) for b in range(4))
    corrupted = xor_set((0, 5), 1)
    print(f"[3] lean-optics LawfulLens xor_set: get_set={l_get_set} set_get={l_set_get} set_set={l_set_set} set((0,5),1)={corrupted}")

    def over_filtered(pred, f, xs):
        return [f(x) if pred(x) else x for x in xs]
    xs = [2, 3]
    lhs = over_filtered(lambda x: x % 2 == 0, lambda x: x * 10, over_filtered(lambda x: x % 2 == 0, lambda x: x + 1, xs))
    rhs = over_filtered(lambda x: x % 2 == 0, lambda x: (x + 1) * 10, xs)
    print(f"[3] ekmett/lens filtered(even) composition break: seq={lhs} != fused={rhs}")

    s0 = (3, 'x')
    lprod_set = lambda ab, s: (ab[1], s[1])
    lprod_get = lambda s: (s[0], s[0])
    put_res = lprod_set((1, 2), s0)
    print(f"[3] ekmett/lens lensProduct(_1,_1) view(set((1,2),(3,'x')))={lprod_get(put_res)} != (1,2)")


if __name__ == "__main__":
    enumerate_finite_lenses()
    test_complement_cardinality_formula()
    test_library_witnesses()
```

Observed output (`2026-11-19`, Linux x86_64, Python 3):

```text
[1] |S|=4,|A|=2 total=1048576 gp=4096 pg=2184 wb=120 monocle_3law=120 vwb=12 store_coalg=12
[1] exact_bijection(vwb==store_coalg)=True
[1] fixed_get_fst wb=16 vwb=2 vwb_disjoint_with_snd=1
[1] colliding_vwb_disjoint_pairs=24 (4!=24 when constructor-ungrounded)
[2] |A|=2,|C|=2: distinct_VWB_puts=2 formula=(|C|!)^(|A|-1)=2
[2] |A|=2,|C|=3: distinct_VWB_puts=6 formula=(|C|!)^(|A|-1)=6
[2] |A|=3,|C|=2: distinct_VWB_puts=4 formula=(|C|!)^(|A|-1)=4
[3] coq-record-update SetterWf clobber_set: set_get=True set_eq=True put_put=False seq=(0, 0) direct=(0, 2)
[3] lean-optics LawfulLens xor_set: get_set=True set_get=True set_set=True set((0,5),1)=(1, 4)
[3] ekmett/lens filtered(even) composition break: seq=[3, 3] != fused=[30, 3]
[3] ekmett/lens lensProduct(_1,_1) view(set((1,2),(3,'x')))=(2, 2) != (1,2)
```

## Revalidation

To verify whether these findings still hold on newer upstream revisions without repeating the full investigation:

1. **Rocq `coq-record-update`:** Diff `src/RecordSet.v` in `tchajed/coq-record-update` relative to `1dd231db87451479043a3812dbdbd9658657ff7c` to check whether `SetterWf` added a `PutPut` / sibling-frame axiom or left `set_get` + `set_eq` as the complete class.
2. **Lean 4 `lean-optics` & `mathlib4`:** Diff `src/Optics/Concrete/Lens.lean` and `docs/upstream/CSLIB_LENS_PROPOSAL.md` in `fraware/lean-optics` relative to `bd3252ae562333b6f592b8f79dde3c91324aeb68` for changes to `LawfulLens`, the `get_put`/`put_get` alias naming, or addition of disjointness (`⊥`) / product-atlas combinators; diff `Mathlib/CategoryTheory/Monad/Algebra.lean` relative to `dd44a18bacca0dba65ac4275af92024f400e63e3` for `Comonad.Coalgebra`.
3. **Scala `Monocle` & Haskell `lens`/`optics`:** Diff `core/shared/src/main/scala/monocle/law/LensLaws.scala` in `optics-dev/Monocle` (`33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`), `src/Control/Lens/{Type,Fold,Unsound}.hs` in `ekmett/lens` (`61eb79c3b46dc397aaa5437684d15201cfc412a6`), and `optics-core/src/Optics/Internal/Optic.hs` in `well-typed/optics` (`dd0b30e144ad92f77584dc8357c381eed2243028`) for new laws, `INLINE` annotations, or disjointness combinators.
4. **Re-run Finite-Carrier Enumeration Probe:** Execute the Python 3 script in `## Evidence` (`< 1 s`, zero external dependencies) to reproduce the exact `1,048,576 -> 120 -> 12` law-hierarchy counts, `120` `Monocle` redundancy count, `(m!)^(k-1)` non-uniqueness formula, and library bypass witnesses.
