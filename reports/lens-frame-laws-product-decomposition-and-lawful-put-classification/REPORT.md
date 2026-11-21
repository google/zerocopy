# Lens frame laws in Lean 4: product decomposition, constant complements, variant-scoped partial lenses, and the classification of lawful setters

## Summary

This package is a kernel-checked Lean 4 toy model (namespace `Toy.Lens`) of field getters and setters, i.e. lenses `get : S → A`, `put : S → A → S`, built to settle **which law set pins down "setting one field changes that field and nothing else"**. The answer depends on whether the listed fields are all of the state:

- **When the listed fields are all of the state**, the law set *PutGet for each field* (`get (put s a) = a`), *PutIndep in both directions* (writing one field leaves the other field's view unchanged), *JointExt* (the field views together determine the state) and the condition *"the state type is nonempty whenever the product of the view types is"* is **equivalent** to: the specific map `s ↦ (get₁ s, get₂ s)` is a bijection onto `A × B` under which each `put` is a coordinate update (F1). GetPut, PutPut and commuting writes then follow and need not be stated (F1-laws). The same holds for a finite list of fields (F2) and, scoped to one variant, for the fields of a variant of a sum type (F5).
- **When the field is not all of the state**, the single-lens laws GetPut, PutGet and PutPut ("very well-behaved") do **not** pin the setter down: the state-twisting setter on `Bool × Bool` satisfies all three and flips the sibling field whenever it changes the first one. For a fixed getter the lawful setters are exactly the coherent families of bijections between fibres (F6), and when the view type `A` has exactly `k` elements and every fibre of the getter has exactly `m` elements there are `(m!)^(k-1)` of them (F6-count). What pins the setter down is a **frame law against an explicitly named complement view `m`**: PutGet plus `m.get (put s a) = m.get s`, where `get` and `m.get` together determine the state and every pair of values occurs, admits exactly one setter, and that setter is very well-behaved (F6-unique). For two fields among others, "both very well-behaved and their writes commute" is exactly "they are two fields of a record with an untouched remainder" (F3-pair); commuting writes must then be stated, because it no longer follows (F4-derived-putComm).
- **The preserved sibling must be named.** A law set that says only that *some* complement is preserved (very well-behaved, equivalently a constant complement, F3) admits the twisting setter, whose preserved complement is `a xor b` rather than the sibling field `b`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One sentence per result (identifiers are package-local labels; the Lean names are in Findings):

- **F1** — For two total lenses `l₁ : Lens S A`, `l₂ : Lens S B`, the conjunction of PutGet for each, PutIndep in both directions, JointExt and `Nonempty (A × B) → Nonempty S` holds **if and only if** `s ↦ (l₁.get s, l₂.get s)` is a bijection `S → A × B` under which `l₁.put` and `l₂.put` are first- and second-coordinate update; GetPut, PutPut and commuting puts are not assumed.
- **F1-inverse** — If both lenses satisfy PutGet, writing through `l₂` leaves `l₁`'s view unchanged (one direction of PutIndep only) and JointExt holds, then for every base state `s₀` the map `p ↦ l₂.put (l₁.put s₀ p.1) p.2` is a two-sided inverse of `s ↦ (l₁.get s, l₂.get s)`; this does not make the puts coordinate updates.
- **F1-laws** — PutGet `l₁`, PutIndep `l₁ l₂` and JointExt already imply GetPut `l₁` and PutPut `l₁`, and the five laws of F1 imply that the two puts commute; no nonemptiness assumption is needed.
- **F2** — For lenses `l i : Lens S (A i)` indexed by a type `ι` enumerated by a list, PutGet for each, pairwise PutIndep, joint extensionality of the family and `Nonempty ((i : ι) → A i) → Nonempty S` hold **if and only if** `s ↦ (fun i => (l i).get s)` is a bijection onto the dependent product with each `(l i).put` the update of coordinate `i`; finiteness of `ι` cannot be dropped.
- **F2-laws** — In a jointly extensional family, PutGet and the frame law at an index `i` give GetPut and PutPut at `i`, and for `i ≠ j` PutGet and the frame laws at `i` and `j` give commuting puts; no decidable equality on `ι` is needed.
- **F3** — A total lens is very well-behaved **if and only if** there are a type `C` in the universe of `S` and a bijection `S ≃ A × C` turning `get` into the first projection and `put` into first-coordinate update; no inhabitedness is assumed, and `C` is some type, not a prescribed sibling field.
- **F3-sharp** — An injective, not necessarily surjective, map `f : S → A × C` (with `C` in any universe) under which `l` is the first-projection lens makes `l` very well-behaved.
- **F3-fiber** — If `l` is very well-behaved and a base view `a₀` is given, then `s ↦ (l.get s, l.put s a₀)` and `(a, c) ↦ l.put c a` form a bijection `S ≃ A × {s // l.get s = a₀}` under which `l` is the first-projection lens.
- **F3-pair** — Two total lenses are both very well-behaved and have commuting puts **if and only if**, for some type `G` in the universe of `S` and a bijection `S ≃ A × B × G`, they are the first and second field lenses and neither touches the `G` component; joint extensionality is not assumed.
- **F4-derived-putComm** — Without joint extensionality commuting puts is an independent law: two lenses on `Bool × Bool × Bool` are both very well-behaved and cross-independent in both directions, yet their puts do not commute.
- **F4-aliasing** — A lens satisfying PutGet on an inhabited state type whose view type has two distinct values is not cross-independent of itself, so two names for one field violate both directions of PutIndep at once.
- **F4-bare-bijection** — `Nat × Nat × Bool` is in bijection with `Nat × Nat` although its two `Nat` field lenses are not jointly extensional, so a conclusion "some bijection `S ≃ A × B` exists" cannot express "no hidden state".
- **F4-F2-finite** — The coordinate lenses on eventually-false Boolean sequences, indexed by `Nat`, satisfy every hypothesis of F2 except finiteness, and the tuple-of-views map is not surjective.
- **F5** — For partial lenses (`Option`-valued `get` and `put`) and a variant `V : S → Prop`, totality on `V`, PutGet on `V`, PutIndep on `V` in both directions, joint extensionality on `V` and `Nonempty (A × B) → ∃ s, V s` hold **if and only if** on `V` the two lenses present the states as `A × B` with coordinate-update puts; nothing is said about states outside `V`.
- **F5-unscoped** — Unscoped joint extensionality for partial lenses identifies all states lacking both fields, so it fails on every state type with two distinct such states, including the intended sum-type model.
- **F5-switch** — The variant-scoped laws do not constrain writes outside the variant, and even unscoped PutGet, GetPut, PutPut and two-way PutIndep admit a setter that switches the variant.
- **F6** — For a fixed getter `get : S → A`, very well-behaved puts correspond bijectively, through the explicit constructions `toPut` and `ofPut`, to coherent families of maps between the fibres of `get` (identity on each fibre, closed under composition); for a put with PutGet, GetPut is the identity law and PutPut the composition law.
- **F6-count** — With a base view `a₀`, very well-behaved puts for `get` correspond to families of bijections from the fibre over `a₀` to every other fibre; if `A` has exactly `k` elements and every fibre exactly `m`, there are exactly `(m!)^(k-1)` of them (one when `k = 0`).
- **F6-unique** — If `get` together with a second view `m.get` determines the state and every pair of values occurs, then exactly one put satisfies PutGet and the frame law `m.get (put s a) = m.get s`, and it is very well-behaved; the condition that every pair of values occurs is sufficient for this, not necessary.

The non-claims of every result are listed first under **Boundaries**, after the lawful-but-unintended instances; read them before relying on a result.

## Applicability

**Model fidelity: this is a toy model.** All definitions live in the Lean namespace `Toy.Lens` and are written from scratch for this package; no production definitions are mirrored. They are meant to capture the field getters and setters of a *value-algebra interface* — reading and writing one field of a record or struct (F1, F3, F6), of a value with a fixed finite list of fields (F2), and of one variant of a sum-typed value (F5) — and the question of which equational laws such an interface should state. The model is:

- **Total, pure, monomorphic functions.** `Lens S A` is a pair `get : S → A`, `put : S → A → S`; writing can change neither the type of the state nor the type of the field. Partiality is modelled only by `Option` in `PLens S A` (`get : S → Option A`, `put : S → A → Option S`). There are no effects, panics, exceptions, nontermination, aliasing of mutable storage, or concurrency.
- **Lean propositional equality.** Every law is an equation in `=`. Real value algebras may compare values observationally, carry padding bytes, provenance, or uninitialised memory, or have several representations of one abstract value; none of this is modelled.
- **Typed fields.** The field type `A` is a type of its own. A unityped interface (`getField : Val → Option Val`) fits F5 only after restricting the field type to well-typed values, because `TotalOn` requires every `a : A` to be writable.
- **Fixed field lists.** F2 needs a finite index type fixed across all states, with field types depending on the index only (no dependent records, no dynamically keyed maps).
- **Universes.** Complements in F3 and ghosts in F3-pair are required to live in the universe of `S`; F3-sharp has no universe restriction.

Every claim of the form "this tells us something about a real interface" is a separate *derived (modeling bridge)* claim, stated per result under Findings with its reasoning; a kernel-checked theorem is never by itself a statement about a real system.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`; the same commit is reported by `lean --version` of the toolchain used). No Mathlib and no other dependency: the Lake project in `lean/` declares one `[[lean_lib]]` (`Toy`) and no `[[require]]`, and imports only core Lean.

**Relationship among the subjects in `REPORT.json`.** The Lean toolchain is the system that checked every theorem. The papers, the Isabelle Archive of Formal Proofs entry and the Agda development are prior-art sources: results tiered T0 restate a known result, T1 make folklore or a result from another formalism precise; the package does not re-examine their proofs. Whether each source was read in full, only in abstract, or not consulted is recorded under Evidence, either in the list of full texts read or in the citation itself; citations under Findings carry the same annotation for every source that was not read in full.

**Proof status.** All 16 main statements of F1, F1-inverse, F2, F3, F3-sharp, F3-fiber, F3-pair, F5, F6, F6-count and F6-unique, and every supporting lemma, counterexample, non-vacuity witness and positive control, are proved; every declaration of the library depends at most on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Findings

### How to read this section

- Every Lean block in a result card is the output of Lean's pretty-printer (`#check`, with `pp.fieldNotation.generalized false`) on the compiled project; nothing in those blocks is typed by hand. Nine entries are printed with one further option (`pp.funBinderTypes true`, `pp.analyze true` or `pp.proofs true`) so that the printed text elaborates to the theorem's statement; the line before each such block names the option and, where the block has several entries, the entry. Universe variables print as `u_1`, `u_2`, ...; `Lens.JointExt` is the total-lens `JointExt`.
- "Unfolded" blocks are hand-written elementary readings in which law names are replaced by their one-line definitions (quoted under Definitions). For the bundled conclusions of F1, F2, F3 and F3-pair the unfolding is itself a proved lemma (listed under "Elementary readings").
- Hypothesis ledgers give each hypothesis, why it is needed, and its tightness: `tight` with the name of a proved counterexample in which all other hypotheses hold and the conclusion fails, or `harmless` with a reason. No hypothesis has tightness `unknown`.
- Every theorem below has `Basis: execution (Lean kernel check)`: it was elaborated and kernel-checked by the toolchain above. The separate `Basis: derived (modeling bridge)` line of each card is an argument, not a kernel check.
- All Lean names are in namespace `Toy.Lens` (prefix omitted where unambiguous); partial-lens names are in `Toy.Lens.PLens`.

### Definitions

Each core definition is quoted as printed by Lean (`#print`), with what it is meant to capture and the names of its proved positive and negative examples (intended instances it admits and intended non-instances it rejects).

#### 1.1 Lenses and the three classical laws

##### `Toy.Lens`

```lean
structure Toy.Lens.{u, v} (S : Type u) (A : Type v) : Type (max u v)
number of parameters: 2
fields:
  Toy.Lens.get : S → A
  Toy.Lens.put : S → A → S
constructor:
  Toy.Lens.mk.{u, v} {S : Type u} {A : Type v} (get : S → A) (put : S → A → S) : Lens S A
```

*Meant to capture.* The bare interface of a field: a total getter and a total setter. Monomorphic: writing cannot change the type of the state or of the field. The structure carries no laws.

*Positive examples (proved).* `fst`, `snd`

*Negative examples (proved).* `not_lens_of_empty_view`

*Remark.* The structure is law-free, so every pair of functions is a lens; the one thing the type rejects is a field that some state lacks.

##### `GetPut`

```lean
def Toy.Lens.GetPut.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => ∀ (s : S), l.put s (l.get s) = s
```

*Meant to capture.* Writing back what you just read changes nothing. Name as in Foster et al. 2007; several libraries call this equation `set-get`/`put_get`.

*Positive examples (proved).* `fst_getPut`, `snd_getPut`

*Negative examples (proved).* `resetSibling_not_getPut`

##### `PutGet`

```lean
def Toy.Lens.PutGet.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => ∀ (s : S) (a : A), l.get (l.put s a) = a
```

*Meant to capture.* You read what you just wrote: the setter really stores the value. Some libraries call this equation `get-set`/`get_put`.

*Positive examples (proved).* `fst_putGet`, `snd_putGet`

*Negative examples (proved).* `ignorePut_not_putGet`

##### `PutPut`

```lean
def Toy.Lens.PutPut.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => ∀ (s : S) (a a' : A), l.put (l.put s a) a' = l.put s a'
```

*Meant to capture.* The second write wins; the first leaves no trace.

*Positive examples (proved).* `fst_putPut`, `snd_putPut`

*Negative examples (proved).* `dirtyFlag_not_putPut`

*Remark.* The three negative examples each violate exactly one law and satisfy the other two: the laws are mutually independent.

##### `WellBehaved`

```lean
def Toy.Lens.WellBehaved.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => GetPut l ∧ PutGet l
```

*Meant to capture.* `GetPut ∧ PutGet` (Foster et al.: well-behaved). Deliberately without `PutPut`.

*Positive examples (proved).* `fst_wellBehaved`, `dirtyFlag_wellBehaved`

*Negative examples (proved).* `ignorePut_not_wellBehaved`, `resetSibling_not_wellBehaved`

##### `VeryWellBehaved`

```lean
def Toy.Lens.VeryWellBehaved.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => GetPut l ∧ PutGet l ∧ PutPut l
```

*Meant to capture.* `GetPut ∧ PutGet ∧ PutPut`. A property of one lens in isolation: it does not say what `put` does to the rest of the state.

*Positive examples (proved).* `fst_veryWellBehaved`, `snd_veryWellBehaved`, `twist_veryWellBehaved`, `xorView_veryWellBehaved`

*Negative examples (proved).* `dirtyFlag_not_veryWellBehaved`

*Remark.* `twist_veryWellBehaved` is a positive example that is nevertheless unintended: the setter flips a sibling field.

#### 1.2 Two lenses on one state

##### `PutIndep`

```lean
def Toy.Lens.PutIndep.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → Prop :=
fun {S} {A} {B} l₁ l₂ => ∀ (s : S) (a : A), l₂.get (l₁.put s a) = l₂.get s
```

*Meant to capture.* Cross-independence, one direction: writing through `l₁` leaves the view of `l₂` unchanged. Not the `⋈` of AFP Optics / Foster–Zeyda–Woodcock, which also includes commuting puts.

*Positive examples (proved).* `fst_snd_putIndep`, `snd_fst_putIndep`, `xorView_fst_putIndep`, `snd_twist_putIndep`

*Negative examples (proved).* `fst_fst_not_putIndep`, `fst_xorView_not_putIndep`, `twist_snd_not_putIndep`

*Remark.* The two directions are genuinely different conditions.

##### `PutComm`

```lean
def Toy.Lens.PutComm.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → Prop :=
fun {S} {A} {B} l₁ l₂ => ∀ (s : S) (a : A) (b : B), l₂.put (l₁.put s a) b = l₁.put (l₂.put s b) a
```

*Meant to capture.* Commuting puts.

*Positive examples (proved).* `fst_snd_putComm`

*Negative examples (proved).* `fst_fst_not_putComm`, `twist_snd_not_putComm`

##### `JointExt`

```lean
def Toy.Lens.JointExt.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → Prop :=
fun {S} {A} {B} l₁ l₂ => ∀ (s t : S), l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t
```

*Meant to capture.* The two views together determine the state (no hidden component). Exactly injectivity of the pairing map.

*Positive examples (proved).* `fst_snd_jointExt`

*Negative examples (proved).* `ghostFst_ghostSnd_not_jointExt`, `fst_fst_not_jointExt`

#### 1.3 Families of lenses

##### `update`

```lean
def Toy.Lens.update.{v, w} : {ι : Type w} →
  {A : ι → Type v} → [DecidableEq ι] → ((i : ι) → A i) → (i : ι) → A i → (j : ι) → A j :=
fun {ι} {A} [DecidableEq ι] f i a j => if h : j = i then ⋯ ▸ a else f j
```

*Meant to capture.* Overwrite one coordinate of a dependent function. `DecidableEq ι` is needed to state it, hence to state `coord` and `IsPiDecomposition`; the laws and the derived-law lemmas for families do not need it.

*Positive examples (proved).* `update_same`, `update_of_ne`

*Negative examples (proved).* `update_ne_self`

##### `PairwiseIndep`

```lean
def Toy.Lens.PairwiseIndep.{u, v, w} : {S : Type u} →
  {ι : Type w} → {A : ι → Type v} → ((i : ι) → Lens S (A i)) → Prop :=
fun {S} {ι} {A} l => ∀ (i j : ι), i ≠ j → PutIndep (l i) (l j)
```

*Meant to capture.* For all distinct indices, writing through `l i` leaves the view of `l j` unchanged (both directions for each unordered pair). Does not include commuting puts.

*Positive examples (proved).* `coord_pairwiseIndep`

*Negative examples (proved).* `const_fst_not_pairwiseIndep`

##### `FamJointExt`

```lean
def Toy.Lens.FamJointExt.{u, v, w} : {S : Type u} → {ι : Type w} → {A : ι → Type v} → ((i : ι) → Lens S (A i)) → Prop :=
fun {S} {ι} {A} l => ∀ (s t : S), (∀ (i : ι), (l i).get s = (l i).get t) → s = t
```

*Meant to capture.* All views together determine the state.

*Positive examples (proved).* `coord_famJointExt`

*Negative examples (proved).* `ghostFam_not_famJointExt`

##### `famGet`

```lean
def Toy.Lens.famGet.{u, v, w} : {S : Type u} →
  {ι : Type w} → {A : ι → Type v} → ((i : ι) → Lens S (A i)) → S → (i : ι) → A i :=
fun {S} {ι} {A} l s i => (l i).get s
```

*Meant to capture.* The tuple of all views: the specific candidate isomorphism of F2.

*Positive examples (proved).* `famGet_coord`

*Negative examples (proved).* `famGet_ghostFam_not_injective`

##### `coord`

```lean
def Toy.Lens.coord.{v, w} : {ι : Type w} → {A : ι → Type v} → [DecidableEq ι] → (i : ι) → Lens ((j : ι) → A j) (A i) :=
fun {ι} {A} [DecidableEq ι] i => { get := fun f => f i, put := fun f a => update f i a }
```

*Meant to capture.* The intended model for families: the `i`-th coordinate lens on the full dependent product.

*Positive examples (proved).* `coord_veryWellBehaved`

*Negative examples (proved).* —

*Remark.* A model, not a law.

#### 1.4 The notions that phrase the conclusions of F1 and F2

##### `Intertwines`

```lean
structure Toy.Lens.Intertwines.{u, v, x} {S : Type u} {T : Type x} {A : Type v} (f : S → T) (l : Lens S A)
  (m : Lens T A) : Prop
number of parameters: 6
fields:
  Toy.Lens.Intertwines.get_eq : ∀ (s : S), m.get (f s) = l.get s
  Toy.Lens.Intertwines.put_eq : ∀ (s : S) (a : A), f (l.put s a) = m.put (f s) a
constructor:
  Toy.Lens.Intertwines.mk.{u, v, x} {S : Type u} {T : Type x} {A : Type v} {f : S → T} {l : Lens S A} {m : Lens T A}
    (get_eq : ∀ (s : S), m.get (f s) = l.get s) (put_eq : ∀ (s : S) (a : A), f (l.put s a) = m.put (f s) a) :
    Intertwines f l m
```

*Meant to capture.* `f` carries the lens `l` to the lens `m`: it preserves `get` and commutes with `put`.

*Positive examples (proved).* `intertwines_id`, `intertwines_swap`

*Negative examples (proved).* `not_intertwines_id_twist_fst`

##### `pairGet`

```lean
def Toy.Lens.pairGet.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → S → A × B :=
fun {S} {A} {B} l₁ l₂ s => (l₁.get s, l₂.get s)
```

*Meant to capture.* The specific candidate isomorphism of F1.

*Positive examples (proved).* `pairGet_fst_snd`

*Negative examples (proved).* `pairGet_fst_fst_not_injective`

##### `pairPut`

```lean
def Toy.Lens.pairPut.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → S → A × B → S :=
fun {S} {A} {B} l₁ l₂ s₀ p => l₂.put (l₁.put s₀ p.fst) p.snd
```

*Meant to capture.* The specific candidate inverse of F1: overwrite both fields of a base state (first through `l₁`, then through `l₂`).

*Positive examples (proved).* `pairPut_fst_snd`

*Negative examples (proved).* `pairGet_pairPut_fst_fst_ne`

##### `IsProductDecomposition`

```lean
structure Toy.Lens.IsProductDecomposition.{u, v, w} {S : Type u} {A : Type v} {B : Type w} (l₁ : Lens S A)
  (l₂ : Lens S B) : Prop
number of parameters: 5
fields:
  Toy.Lens.IsProductDecomposition.injective : Function.Injective (pairGet l₁ l₂)
  Toy.Lens.IsProductDecomposition.surjective : Function.Surjective (pairGet l₁ l₂)
  Toy.Lens.IsProductDecomposition.intertwines_fst : Intertwines (pairGet l₁ l₂) l₁ fst
  Toy.Lens.IsProductDecomposition.intertwines_snd : Intertwines (pairGet l₁ l₂) l₂ snd
constructor:
  Toy.Lens.IsProductDecomposition.mk.{u, v, w} {S : Type u} {A : Type v} {B : Type w} {l₁ : Lens S A} {l₂ : Lens S B}
    (injective : Function.Injective (pairGet l₁ l₂)) (surjective : Function.Surjective (pairGet l₁ l₂))
    (intertwines_fst : Intertwines (pairGet l₁ l₂) l₁ fst) (intertwines_snd : Intertwines (pairGet l₁ l₂) l₂ snd) :
    IsProductDecomposition l₁ l₂
```

*Meant to capture.* The conclusion of F1: `pairGet l₁ l₂` is a bijection onto `A × B` under which `l₁` and `l₂` are the projection lenses.

*Positive examples (proved).* `fst_snd_isProductDecomposition`

*Negative examples (proved).* `fst_fst_not_isProductDecomposition`

*Remark.* Elementary reading, proved: `isProductDecomposition_iff_elementary`.

##### `IsPiDecomposition`

```lean
structure Toy.Lens.IsPiDecomposition.{u, v, w} {S : Type u} {ι : Type w} {A : ι → Type v} [DecidableEq ι]
  (l : (i : ι) → Lens S (A i)) : Prop
number of parameters: 5
fields:
  Toy.Lens.IsPiDecomposition.injective : Function.Injective (famGet l)
  Toy.Lens.IsPiDecomposition.surjective : Function.Surjective (famGet l)
  Toy.Lens.IsPiDecomposition.intertwines : ∀ (i : ι), Intertwines (famGet l) (l i) (coord i)
constructor:
  Toy.Lens.IsPiDecomposition.mk.{u, v, w} {S : Type u} {ι : Type w} {A : ι → Type v} [DecidableEq ι]
    {l : (i : ι) → Lens S (A i)} (injective : Function.Injective (famGet l))
    (surjective : Function.Surjective (famGet l)) (intertwines : ∀ (i : ι), Intertwines (famGet l) (l i) (coord i)) :
    IsPiDecomposition l
```

*Meant to capture.* The conclusion of F2.

*Positive examples (proved).* `coord_isPiDecomposition`

*Negative examples (proved).* `ghostFam_not_isPiDecomposition`, `evCoord_tight_finite_index`

*Remark.* Elementary reading, proved: `isPiDecomposition_iff_elementary`.

#### 1.5 Complements

##### `Equiv`

```lean
structure Toy.Lens.Equiv.{u, v} (α : Type u) (β : Type v) : Type (max u v)
number of parameters: 2
fields:
  Toy.Lens.Equiv.toFun : α → β
  Toy.Lens.Equiv.invFun : β → α
  Toy.Lens.Equiv.left_inv : ∀ (a : α), self.invFun (self.toFun a) = a
  Toy.Lens.Equiv.right_inv : ∀ (b : β), self.toFun (self.invFun b) = b
constructor:
  Toy.Lens.Equiv.mk.{u, v} {α : Type u} {β : Type v} (toFun : α → β) (invFun : β → α)
    (left_inv : ∀ (a : α), invFun (toFun a) = a) (right_inv : ∀ (b : β), toFun (invFun b) = b) : Equiv α β
```

*Meant to capture.* A bijection bundled with its inverse (core Lean has no `Equiv`).

*Positive examples (proved).* `Equiv.refl`

*Negative examples (proved).* `not_equiv_bool_unit`

##### `HasConstantComplement`

```lean
def Toy.Lens.HasConstantComplement.{u, v} : {S : Type u} → {A : Type v} → Lens S A → Prop :=
fun {S} {A} l => ∃ C e, Intertwines e.toFun l fst
```

*Meant to capture.* Constant complement in lens form: the state splits as view × rest (rest in the universe of `S`) and `put` replaces the view and keeps the rest. Bancilhon–Spyratos require only an injective pairing; the bijection is the total-update specialisation.

*Positive examples (proved).* `fst_hasConstantComplement`, `twist_hasConstantComplement`

*Negative examples (proved).* `dirtyFlag_not_hasConstantComplement`, `ignorePut_not_hasConstantComplement`, `resetSibling_not_hasConstantComplement`

*Remark.* Elementary reading, proved: `hasConstantComplement_iff_elementary`.

##### `Fiber`

```lean
def Toy.Lens.Fiber.{u, v} : {S : Type u} → {A : Type v} → Lens S A → A → Type u :=
fun {S} {A} l a₀ => { s // l.get s = a₀ }
```

*Meant to capture.* The fibre of `get` over a base view: the canonical complement when a base view is available.

*Positive examples (proved).* `fiberFstMk`

*Negative examples (proved).* `fiber_fst_true_val_ne`

##### `fiberFrom`

```lean
def Toy.Lens.fiberFrom.{u, v} : {S : Type u} → {A : Type v} → (l : Lens S A) → (a₀ : A) → A × Fiber l a₀ → S :=
fun {S} {A} l a₀ p => l.put p.snd.val p.fst
```

*Meant to capture.* The explicit inverse map of the fibre complement, `(a, c) ↦ l.put c a`.

*Positive examples (proved).* `fiberFrom_fst`

*Negative examples (proved).* `fiberFrom_ignorePut_ne`

##### `HasGhostComplement`

```lean
def Toy.Lens.HasGhostComplement.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → Lens S A → Lens S B → Prop :=
fun {S} {A} {B} l₁ l₂ => ∃ G e, Intertwines e.toFun l₁ ghostFst ∧ Intertwines e.toFun l₂ ghostSnd
```

*Meant to capture.* The two lenses are, up to a bijection `S ≃ A × B × G`, the two visible fields of a record with an untouched third component. A one-point ghost corresponds to `IsProductDecomposition`.

*Positive examples (proved).* `ghost_hasGhostComplement`, `fst_snd_hasGhostComplement`

*Negative examples (proved).* `twist_snd_not_hasGhostComplement`, `fstB_fstB_not_hasGhostComplement`

*Remark.* Elementary reading, proved: `hasGhostComplement_iff_elementary`.

#### 1.6 Partial lenses and variant-scoped laws (namespace `Toy.Lens.PLens`)

##### `PLens`

```lean
structure Toy.Lens.PLens.{u, v} (S : Type u) (A : Type v) : Type (max u v)
number of parameters: 2
fields:
  Toy.Lens.PLens.get : S → Option A
  Toy.Lens.PLens.put : S → A → Option S
constructor:
  Toy.Lens.PLens.mk.{u, v} {S : Type u} {A : Type v} (get : S → Option A) (put : S → A → Option S) : PLens S A
```

*Meant to capture.* A field that need not exist in every state: `get` and `put` return `Option`. The field type is typed; a unityped interface fits after restricting the field type to well-typed values. Differs from affine traversals (total setter), AFP `mwb_lens` and prisms.

*Positive examples (proved).* `PLens.absent`, `PLens.pairFst`, `PLens.pairSnd`

*Negative examples (proved).* —

*Remark.* Law-free, like `Lens`.

##### `PLens.TotalOn`

```lean
structure Toy.Lens.PLens.TotalOn.{u, v} {S : Type u} {A : Type v} (V : S → Prop) (l : PLens S A) : Prop
number of parameters: 4
fields:
  Toy.Lens.PLens.TotalOn.get_defined : ∀ (s : S), V s → ∃ a, l.get s = some a
  Toy.Lens.PLens.TotalOn.put_defined : ∀ (s : S) (a : A), V s → ∃ s', l.put s a = some s' ∧ V s'
constructor:
  Toy.Lens.PLens.TotalOn.mk.{u, v} {S : Type u} {A : Type v} {V : S → Prop} {l : PLens S A}
    (get_defined : ∀ (s : S), V s → ∃ a, l.get s = some a)
    (put_defined : ∀ (s : S) (a : A), V s → ∃ s', l.put s a = some s' ∧ V s') : TotalOn V l
```

*Meant to capture.* On the variant, the field can be read and written, and writes stay in the variant. The variant is an arbitrary predicate, not the domain of `get` (see `twin_jointExtOn_fails_on_union`).

*Positive examples (proved).* `pairFst_totalOn`, `pairSnd_totalOn`

*Negative examples (proved).* `pairFst_not_totalOn_univ`

*Remark.* Its three components are independently needed for F5 (`totalOn_components_tight`).

##### `PLens.PutGetOn`

```lean
def Toy.Lens.PLens.PutGetOn.{u, v} : {S : Type u} → {A : Type v} → (S → Prop) → PLens S A → Prop :=
fun {S} {A} V l => ∀ (s : S) (a : A) (s' : S), V s → l.put s a = some s' → l.get s' = some a
```

*Meant to capture.* Variant-scoped PutGet.

*Positive examples (proved).* `pairFst_putGetOn`, `pairSnd_putGetOn`

*Negative examples (proved).* `pairIgnore_not_putGetOn`

##### `PLens.PutIndepOn`

```lean
def Toy.Lens.PLens.PutIndepOn.{u, v, w} : {S : Type u} →
  {A : Type v} → {B : Type w} → (S → Prop) → PLens S A → PLens S B → Prop :=
fun {S} {A} {B} V l₁ l₂ => ∀ (s : S) (a : A) (s' : S), V s → l₁.put s a = some s' → l₂.get s' = l₂.get s
```

*Meant to capture.* Variant-scoped cross-independence, one direction.

*Positive examples (proved).* `pairFst_pairSnd_putIndepOn`, `pairSnd_pairFst_putIndepOn`

*Negative examples (proved).* `pairFst_pairFst_not_putIndepOn`

##### `PLens.JointExtOn`

```lean
def Toy.Lens.PLens.JointExtOn.{u, v, w} : {S : Type u} →
  {A : Type v} → {B : Type w} → (S → Prop) → PLens S A → PLens S B → Prop :=
fun {S} {A} {B} V l₁ l₂ => ∀ (s t : S), V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t
```

*Meant to capture.* Variant-scoped joint extensionality.

*Positive examples (proved).* `pairFst_pairSnd_jointExtOn`

*Negative examples (proved).* `pairFst_pairFst_not_jointExtOn`

##### `PLens.JointExt`

```lean
def Toy.Lens.PLens.JointExt.{u, v, w} : {S : Type u} → {A : Type v} → {B : Type w} → PLens S A → PLens S B → Prop :=
fun {S} {A} {B} l₁ l₂ => ∀ (s t : S), l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t
```

*Meant to capture.* Unscoped joint extensionality for partial lenses; recorded only to show that it is the wrong law for sum types.

*Positive examples (proved).* `optFst_optSnd_jointExt`, `shape3_jointExt`

*Negative examples (proved).* `pairFst_pairSnd_not_jointExt`, `otherFst_otherSnd_not_jointExt`

##### `PLens.IsProductDecompositionOn`

```lean
structure Toy.Lens.PLens.IsProductDecompositionOn.{u, v, w} {S : Type u} {A : Type v} {B : Type w} (V : S → Prop)
  (l₁ : PLens S A) (l₂ : PLens S B) : Prop
number of parameters: 6
fields:
  Toy.Lens.PLens.IsProductDecompositionOn.get_defined : ∀ (s : S), V s → ∃ a b, l₁.get s = some a ∧ l₂.get s = some b
  Toy.Lens.PLens.IsProductDecompositionOn.injective : ∀ (s t : S),
      V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t
  Toy.Lens.PLens.IsProductDecompositionOn.surjective : ∀ (a : A) (b : B),
      ∃ s, V s ∧ l₁.get s = some a ∧ l₂.get s = some b
  Toy.Lens.PLens.IsProductDecompositionOn.put_fst : ∀ (s : S) (a : A),
      V s → ∃ s', l₁.put s a = some s' ∧ V s' ∧ l₁.get s' = some a ∧ l₂.get s' = l₂.get s
  Toy.Lens.PLens.IsProductDecompositionOn.put_snd : ∀ (s : S) (b : B),
      V s → ∃ s', l₂.put s b = some s' ∧ V s' ∧ l₁.get s' = l₁.get s ∧ l₂.get s' = some b
constructor:
  Toy.Lens.PLens.IsProductDecompositionOn.mk.{u, v, w} {S : Type u} {A : Type v} {B : Type w} {V : S → Prop}
    {l₁ : PLens S A} {l₂ : PLens S B} (get_defined : ∀ (s : S), V s → ∃ a b, l₁.get s = some a ∧ l₂.get s = some b)
    (injective : ∀ (s t : S), V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t)
    (surjective : ∀ (a : A) (b : B), ∃ s, V s ∧ l₁.get s = some a ∧ l₂.get s = some b)
    (put_fst : ∀ (s : S) (a : A), V s → ∃ s', l₁.put s a = some s' ∧ V s' ∧ l₁.get s' = some a ∧ l₂.get s' = l₂.get s)
    (put_snd : ∀ (s : S) (b : B), V s → ∃ s', l₂.put s b = some s' ∧ V s' ∧ l₁.get s' = l₁.get s ∧ l₂.get s' = some b) :
    IsProductDecompositionOn V l₁ l₂
```

*Meant to capture.* The conclusion of F5: on the variant, the two lenses present the states as `A × B`. Says nothing outside the variant.

*Positive examples (proved).* `pairFst_pairSnd_isProductDecompositionOn`

*Negative examples (proved).* `pairFst_pairFst_not_isProductDecompositionOn`

##### `PLens.Shape`

```lean
inductive Toy.Lens.PLens.Shape : Type
number of parameters: 0
constructors:
Toy.Lens.PLens.Shape.nil : Shape
Toy.Lens.PLens.Shape.unit : Shape
Toy.Lens.PLens.Shape.pair : Bool → Bool → Shape
```

*Meant to capture.* A small sum type: two nullary tags and one binary record variant.

*Positive examples (proved).* —

*Negative examples (proved).* —

*Remark.* Example object.

##### `PLens.Shape.IsPair`

```lean
def Toy.Lens.PLens.Shape.IsPair : Shape → Prop :=
fun s => ∃ a b, s = Shape.pair a b
```

*Meant to capture.* The record variant of `Shape`.

*Positive examples (proved).* `Shape.isPair_pair`

*Negative examples (proved).* `Shape.not_isPair_nil`

##### `toPLens`

```lean
def Toy.Lens.toPLens.{u, v} : {S : Type u} → {A : Type v} → Lens S A → PLens S A :=
fun {S} {A} l => { get := fun s => some (l.get s), put := fun s a => some (l.put s a) }
```

*Meant to capture.* A total lens as a partial lens that never fails.

*Positive examples (proved).* `totalOn_toPLens`

*Negative examples (proved).* —

*Remark.* Bridge: every scoped notion on the whole type reduces to the total one (`isProductDecompositionOn_toPLens_iff` and companions).

##### `PLens.GetPutOn`

```lean
def Toy.Lens.PLens.GetPutOn.{u, v} : {S : Type u} → {A : Type v} → (S → Prop) → PLens S A → Prop :=
fun {S} {A} V l => ∀ (s : S) (a : A), V s → l.get s = some a → l.put s a = some s
```

*Meant to capture.* Variant-scoped GetPut.

*Positive examples (proved).* `pairFst_getPutOn`

*Negative examples (proved).* `pairResetSnd_not_getPutOn`

##### `PLens.PutPutOn`

```lean
def Toy.Lens.PLens.PutPutOn.{u, v} : {S : Type u} → {A : Type v} → (S → Prop) → PLens S A → Prop :=
fun {S} {A} V l => ∀ (s : S) (a a' : A) (s₁ : S), V s → l.put s a = some s₁ → l.put s₁ a' = l.put s a'
```

*Meant to capture.* Variant-scoped PutPut.

*Positive examples (proved).* `pairFst_putPutOn`

*Negative examples (proved).* `pairDirty_not_putPutOn`

##### `PLens.PutCommOn`

```lean
def Toy.Lens.PLens.PutCommOn.{u, v, w} : {S : Type u} →
  {A : Type v} → {B : Type w} → (S → Prop) → PLens S A → PLens S B → Prop :=
fun {S} {A} {B} V l₁ l₂ =>
  ∀ (s : S) (a : A) (b : B),
    V s → (Option.bind (l₁.put s a) fun t => l₂.put t b) = Option.bind (l₂.put s b) fun t => l₁.put t a
```

*Meant to capture.* Variant-scoped commuting puts.

*Positive examples (proved).* `pairFst_pairSnd_putCommOn`

*Negative examples (proved).* `pairFst_pairFst_not_putCommOn`

#### 1.7 Fibre maps for a fixed getter (F6)

##### `GetFiber`

```lean
def Toy.Lens.GetFiber.{u, v} : {S : Type u} → {A : Type v} → (S → A) → A → Type u :=
fun {S} {A} get a => { s // get s = a }
```

*Meant to capture.* The states in which the field has a given value. `Fiber l a = GetFiber l.get a` (`fiber_eq_getFiber`).

*Positive examples (proved).* `getFiberFstMk`

*Negative examples (proved).* `getFiber_const_false_true_empty`

##### `FiberMaps`

```lean
def Toy.Lens.FiberMaps.{u, v} : {S : Type u} → {A : Type v} → (S → A) → Type (max u v) :=
fun {S} {A} get => (a a' : A) → GetFiber get a → GetFiber get a'
```

*Meant to capture.* Raw data of a setter that stores the written value: for every ordered pair of views, a map between the fibres.

*Positive examples (proved).* `ofPut_fst_coherent` (the fibre maps of `fst`)

*Negative examples (proved).* `fiberMaps_empty_of_empty_fiber`

##### `FiberMaps.Coherent`

```lean
structure Toy.Lens.FiberMaps.Coherent.{u, v} {S : Type u} {A : Type v} {get : S → A} (φ : FiberMaps get) : Prop
number of parameters: 4
fields:
  Toy.Lens.FiberMaps.Coherent.map_self : ∀ (a : A) (x : GetFiber get a), φ a a x = x
  Toy.Lens.FiberMaps.Coherent.map_comp : ∀ (a a' a'' : A) (x : GetFiber get a), φ a' a'' (φ a a' x) = φ a a'' x
constructor:
  Toy.Lens.FiberMaps.Coherent.mk.{u, v} {S : Type u} {A : Type v} {get : S → A} {φ : FiberMaps get}
    (map_self : ∀ (a : A) (x : GetFiber get a), φ a a x = x)
    (map_comp : ∀ (a a' a'' : A) (x : GetFiber get a), φ a' a'' (φ a a' x) = φ a a'' x) : FiberMaps.Coherent φ
```

*Meant to capture.* Identity on each fibre and closed under composition; each map is then a bijection (`FiberMaps.Coherent.leftInverse`).

*Positive examples (proved).* `ofPut_fst_coherent`, `ofPut_twist_coherent`

*Negative examples (proved).* `ofPut_resetSibling_not_coherent`, `ofPut_dirtyFlag_not_coherent`

##### `FiberMaps.toPut`

```lean
def Toy.Lens.FiberMaps.toPut.{u, v} : {S : Type u} → {A : Type v} → {get : S → A} → FiberMaps get → S → A → S :=
fun {S} {A} {get} φ s a => (φ (get s) a ⟨s, ⋯⟩).val
```

*Meant to capture.* The put induced by fibre maps: move a state to the fibre of the written view.

*Positive examples (proved).* `toPut_ofPut_fst`

*Negative examples (proved).* `toPut_ofPut_dirtyFlag_not_veryWellBehaved`

*Remark.* Always satisfies PutGet (`toPut_putGet`).

##### `ofPut`

```lean
def Toy.Lens.ofPut.{u, v} : {S : Type u} →
  {A : Type v} → (get : S → A) → (put : S → A → S) → PutGet { get := get, put := put } → FiberMaps get :=
fun {S} {A} get put h x a' x_1 => ⟨put x_1.val a', ⋯⟩
```

*Meant to capture.* The fibre maps induced by a put with PutGet: `x ↦ put x a'`.

*Positive examples (proved).* `ofPut_fst_coherent`

*Negative examples (proved).* `ofPut_dirtyFlag_not_coherent`

*Remark.* `toPut (ofPut get put h) = put` by definition (`toPut_ofPut`).

##### `factorial`

```lean
def Toy.Lens.factorial : Nat → Nat :=
fun x => Nat.brecOn x factorial._f
```

*Meant to capture.* The factorial function (core Lean has none).

*Positive examples (proved).* `factorial_three`

*Negative examples (proved).* `factorial_pos`

*Remark.* The `#print` output above shows only the compiled structural recursion. The defining equations are `factorial 0 = 1` and `factorial (n + 1) = (n + 1) * factorial n`; both hold by `rfl`.

#### 1.8 Example objects used by the examples and witnesses

```lean
def Toy.Lens.fst.{v, w} : {A : Type v} → {B : Type w} → Lens (A × B) A :=
fun {A} {B} => { get := fun p => p.fst, put := fun p a => (a, p.snd) }
def Toy.Lens.snd.{v, w} : {A : Type v} → {B : Type w} → Lens (A × B) B :=
fun {A} {B} => { get := fun p => p.snd, put := fun p b => (p.fst, b) }
def Toy.Lens.ignorePut : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun p x => p }
def Toy.Lens.resetSibling : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun x a => (a, false) }
def Toy.Lens.dirtyFlag : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun p a => if p.fst = a then p else (a, true) }
def Toy.Lens.twist : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun p a => (a, p.snd ^^ (p.fst ^^ a)) }
def Toy.Lens.xorView : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst ^^ p.snd, put := fun p v => (p.fst, p.fst ^^ v) }
def Toy.Lens.ghostFst.{v, w, x} : {A : Type v} → {B : Type w} → {G : Type x} → Lens (A × B × G) A :=
fun {A} {B} {G} => { get := fun s => s.fst, put := fun s a => (a, s.snd.fst, s.snd.snd) }
def Toy.Lens.ghostSnd.{v, w, x} : {A : Type v} → {B : Type w} → {G : Type x} → Lens (A × B × G) B :=
fun {A} {B} {G} => { get := fun s => s.snd.fst, put := fun s b => (s.fst, b, s.snd.snd) }
def Toy.Lens.ignorePutSnd : Lens (Bool × Bool) Bool :=
{ get := fun p => p.snd, put := fun p x => p }
def Toy.Lens.idB : Lens Bool Bool :=
{ get := fun s => s, put := fun x a => a }
def Toy.Lens.emptyLens : Lens Empty Unit :=
{ get := fun x => (), put := fun s x => s }
def Toy.Lens.emptyViewLens : Lens Empty Empty :=
{ get := fun s => s, put := fun s x => s }
def Toy.Lens.emptyBoolLens : Lens Empty Bool :=
{ get := fun s => Empty.elim s, put := fun s x => s }
def Toy.Lens.unitLensB : Lens (Bool × Bool) Unit :=
{ get := fun x => (), put := fun s x => s }
def Toy.Lens.flipPut : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun p x => (!p.fst, p.snd) }
def Toy.Lens.copySibling : Lens (Bool × Bool) Bool :=
{ get := fun p => p.fst, put := fun p x => (p.snd, p.snd) }
def Toy.Lens.ghostReset : Lens (Bool × Bool × Bool) Bool :=
{ get := fun s => s.fst, put := fun s a => (a, s.snd.fst, false) }
def Toy.Lens.ghostDirty : Lens (Bool × Bool × Bool) Bool :=
{ get := fun s => s.fst, put := fun s a => if s.fst = a then s else (a, s.snd.fst, true) }
def Toy.Lens.ghostTwistSnd : Lens (Bool × Bool × Bool) Bool :=
{ get := fun s => s.snd.fst, put := fun s b => (s.fst, b, s.snd.snd ^^ s.fst && (s.snd.fst ^^ b)) }
def Toy.Lens.unitLens.{u_1} : {S : Type u_1} → Lens S Unit :=
fun {S} => { get := fun x => (), put := fun s x => s }
def Toy.Lens.fam2.{u_1, u_2} : {S : Type u_1} → {A : Type u_2} → Lens S A → Lens S A → Bool → Lens S A :=
fun {S} {A} l₁ l₂ x =>
  match x with
  | false => l₁
  | true => l₂
def Toy.Lens.ghostFam : Bool → Lens (Bool × Bool × Bool) Bool :=
fun x =>
  match x with
  | false => ghostFst
  | true => ghostSnd
def Toy.Lens.ghostEquiv : Equiv (Nat × Nat × Bool) (Nat × Nat) :=
{ toFun := fun s => (2 * s.fst + if s.snd.snd = true then 1 else 0, s.snd.fst),
  invFun := fun p => (p.fst / 2, p.snd, p.fst % 2 == 1), left_inv := ghostEquiv._proof_1,
  right_inv := ghostEquiv._proof_2 }
def Toy.Lens.EvFalse : Type :=
{ f // ∃ N, ∀ (n : Nat), N ≤ n → f n = false }
def Toy.Lens.evCoord : Nat → Lens EvFalse Bool :=
fun i => { get := fun f => f.val i, put := fun f a => ⟨update f.val i a, ⋯⟩ }
@[reducible] def Toy.Lens.getFst : Bool × Bool → Bool :=
fun p => p.fst
@[reducible] def Toy.Lens.getIsSome : Option Bool → Bool :=
fun o => Option.isSome o
def Toy.Lens.PLens.absent.{u, v} : {S : Type u} → {A : Type v} → PLens S A :=
fun {S} {A} => { get := fun x => none, put := fun x x_1 => none }
def Toy.Lens.PLens.pairFst : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, a' => some (Shape.pair a' b)
    | x, x_2 => none }
def Toy.Lens.PLens.pairSnd : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some b
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, b' => some (Shape.pair a b')
    | x, x_2 => none }
def Toy.Lens.PLens.pairIgnore : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, x => some (Shape.pair a b)
    | x, x_2 => none }
def Toy.Lens.PLens.pairFstSwitch : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, a' => some (Shape.pair a' b)
    | Shape.nil, a' => some (Shape.pair a' false)
    | Shape.unit, x => none }
def Toy.Lens.PLens.optFst : PLens (Option (Bool × Bool)) Bool :=
{
  get := fun x =>
    match x with
    | some p => some p.fst
    | none => none,
  put := fun x x_1 =>
    match x, x_1 with
    | some p, a' => some (some (a', p.snd))
    | none, x => none }
def Toy.Lens.PLens.optSnd : PLens (Option (Bool × Bool)) Bool :=
{
  get := fun x =>
    match x with
    | some p => some p.snd
    | none => none,
  put := fun x x_1 =>
    match x, x_1 with
    | some p, b' => some (some (p.fst, b'))
    | none, x => none }
def Toy.Lens.PLens.optWriteAll : PLens (Option Bool) Bool :=
{ get := fun s => s, put := fun x a => some (some a) }
def Toy.Lens.PLens.readOnlyUnit : PLens Unit Bool :=
{ get := fun x => some false, put := fun x x_1 => none }
def Toy.Lens.PLens.leaveVariant : PLens Bool Unit :=
{ get := fun x => some (), put := fun x x_1 => some true }
def Toy.Lens.PLens.pairFstTagSwitch : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, a' => some (Shape.pair a' b)
    | Shape.nil, x => some Shape.unit
    | Shape.unit, x => none }
inductive Toy.Lens.PLens.ShapeShared : Type
number of parameters: 0
constructors:
Toy.Lens.PLens.ShapeShared.onlyB : Bool → ShapeShared
Toy.Lens.PLens.ShapeShared.pair : Bool → Bool → ShapeShared
def Toy.Lens.PLens.sharedFstSwitch : PLens ShapeShared Bool :=
{
  get := fun x =>
    match x with
    | ShapeShared.pair a b => some a
    | ShapeShared.onlyB b => none,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeShared.pair a b, a' => some (ShapeShared.pair a' b)
    | ShapeShared.onlyB b, a' => some (ShapeShared.pair a' b) }
def Toy.Lens.PLens.sharedSnd : PLens ShapeShared Bool :=
{
  get := fun x =>
    match x with
    | ShapeShared.pair a b => some b
    | ShapeShared.onlyB b => some b,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeShared.pair a b, b' => some (ShapeShared.pair a b')
    | ShapeShared.onlyB b, b' => some (ShapeShared.onlyB b') }
def Toy.Lens.PLens.presentAt : Bool → PLens Bool Unit :=
fun b => { get := fun s => if s = b then some () else none, put := fun x x_1 => none }
inductive Toy.Lens.PLens.Shape3 : Type
number of parameters: 0
constructors:
Toy.Lens.PLens.Shape3.nil : Shape3
Toy.Lens.PLens.Shape3.onlyA : Bool → Shape3
Toy.Lens.PLens.Shape3.pair : Bool → Bool → Shape3
def Toy.Lens.PLens.shape3A : PLens Shape3 Bool :=
{
  get := fun x =>
    match x with
    | Shape3.onlyA a => some a
    | Shape3.pair a b => some a
    | Shape3.nil => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape3.onlyA a, a' => some (Shape3.onlyA a')
    | Shape3.pair a b, a' => some (Shape3.pair a' b)
    | Shape3.nil, x => none }
def Toy.Lens.PLens.shape3B : PLens Shape3 Bool :=
{
  get := fun x =>
    match x with
    | Shape3.pair a b => some b
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape3.pair a b, b' => some (Shape3.pair a b')
    | x, x_2 => none }
inductive Toy.Lens.PLens.ShapeOther : Type
number of parameters: 0
constructors:
Toy.Lens.PLens.ShapeOther.other : Bool → ShapeOther
Toy.Lens.PLens.ShapeOther.pair : Bool → Bool → ShapeOther
def Toy.Lens.PLens.otherFst : PLens ShapeOther Bool :=
{
  get := fun x =>
    match x with
    | ShapeOther.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeOther.pair a b, a' => some (ShapeOther.pair a' b)
    | x, x_2 => none }
def Toy.Lens.PLens.otherSnd : PLens ShapeOther Bool :=
{
  get := fun x =>
    match x with
    | ShapeOther.pair a b => some b
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeOther.pair a b, b' => some (ShapeOther.pair a b')
    | x, x_2 => none }
inductive Toy.Lens.PLens.ShapeTwin : Type
number of parameters: 0
constructors:
Toy.Lens.PLens.ShapeTwin.pair1 : Bool → Bool → ShapeTwin
Toy.Lens.PLens.ShapeTwin.pair2 : Bool → Bool → ShapeTwin
def Toy.Lens.PLens.twinA : PLens ShapeTwin Bool :=
{
  get := fun x =>
    match x with
    | ShapeTwin.pair1 a b => some a
    | ShapeTwin.pair2 a b => some a,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeTwin.pair1 a b, a' => some (ShapeTwin.pair1 a' b)
    | ShapeTwin.pair2 a b, a' => some (ShapeTwin.pair2 a' b) }
def Toy.Lens.PLens.twinB : PLens ShapeTwin Bool :=
{
  get := fun x =>
    match x with
    | ShapeTwin.pair1 a b => some b
    | ShapeTwin.pair2 a b => some b,
  put := fun x x_1 =>
    match x, x_1 with
    | ShapeTwin.pair1 a b, b' => some (ShapeTwin.pair1 a b')
    | ShapeTwin.pair2 a b, b' => some (ShapeTwin.pair2 a b') }
def Toy.Lens.PLens.pairResetSnd : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, a' => some (Shape.pair a' false)
    | x, x_2 => none }
def Toy.Lens.PLens.pairDirty : PLens Shape Bool :=
{
  get := fun x =>
    match x with
    | Shape.pair a b => some a
    | x => none,
  put := fun x x_1 =>
    match x, x_1 with
    | Shape.pair a b, a' => if a = a' then some (Shape.pair a b) else some (Shape.pair a' true)
    | x, x_2 => none }
```

Monomorphic abbreviations and a variant predicate used in the cards (`fstB`, `sndB` and `ghostFstB` are `fst`, `snd` and `ghostFst` at `Bool`):

```lean
@[reducible] def Toy.Lens.fstB : Lens (Bool × Bool) Bool :=
fst
@[reducible] def Toy.Lens.sndB : Lens (Bool × Bool) Bool :=
snd
@[reducible] def Toy.Lens.ghostFstB : Lens (Bool × Bool × Bool) Bool :=
ghostFst
def Toy.Lens.PLens.ShapeShared.IsPair : ShapeShared → Prop :=
fun s => ∃ a b, s = ShapeShared.pair a b
```

#### Elementary readings of the bundled conclusions (proved)

`hasConstantComplement_iff_elementary` and `hasGhostComplement_iff_elementary` are printed with `pp.funBinderTypes true` in addition, which shows the types of the `∃`-bound complement and bijection.

```lean
@intertwines_fst_iff : ∀ {S : Type u_1} {A : Type u_2} {C : Type u_3} (f : S → A × C) (l : Lens S A),
  Intertwines f l fst ↔ (∀ (s : S), (f s).fst = l.get s) ∧ ∀ (s : S) (a : A), f (l.put s a) = (a, (f s).snd)
@isProductDecomposition_iff_elementary : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} (l₁ : Lens S A) (l₂ : Lens S B),
  IsProductDecomposition l₁ l₂ ↔
    (∀ (s t : S), l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t) ∧
      (∀ (a : A) (b : B), ∃ s, l₁.get s = a ∧ l₂.get s = b) ∧
        (∀ (s : S) (a : A), l₁.get (l₁.put s a) = a ∧ l₂.get (l₁.put s a) = l₂.get s) ∧
          ∀ (s : S) (b : B), l₁.get (l₂.put s b) = l₁.get s ∧ l₂.get (l₂.put s b) = b
@isPiDecomposition_iff_elementary : ∀ {S : Type u_1} {ι : Type u_3} {A : ι → Type u_2} [inst : DecidableEq ι]
  (l : (i : ι) → Lens S (A i)),
  IsPiDecomposition l ↔
    (∀ (s t : S), (∀ (i : ι), (l i).get s = (l i).get t) → s = t) ∧
      (∀ (f : (i : ι) → A i), ∃ s, ∀ (i : ι), (l i).get s = f i) ∧
        (∀ (i : ι) (s : S) (a : A i), (l i).get ((l i).put s a) = a) ∧
          ∀ (i j : ι), i ≠ j → ∀ (s : S) (a : A i), (l j).get ((l i).put s a) = (l j).get s
@hasConstantComplement_iff_elementary : ∀ {S : Type u_1} {A : Type u_2} (l : Lens S A),
  HasConstantComplement l ↔
    ∃ (C : Type u_1),
      ∃ (e : Equiv S (A × C)),
        (∀ (s : S), (e.toFun s).fst = l.get s) ∧ ∀ (s : S) (a : A), e.toFun (l.put s a) = (a, (e.toFun s).snd)
@hasGhostComplement_iff_elementary : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} (l₁ : Lens S A) (l₂ : Lens S B),
  HasGhostComplement l₁ l₂ ↔
    ∃ (G : Type u_1),
      ∃ (e : Equiv S (A × B × G)),
        (∀ (s : S), (e.toFun s).fst = l₁.get s) ∧
          (∀ (s : S) (a : A), e.toFun (l₁.put s a) = (a, (e.toFun s).snd.fst, (e.toFun s).snd.snd)) ∧
            (∀ (s : S), (e.toFun s).snd.fst = l₂.get s) ∧
              ∀ (s : S) (b : B), e.toFun (l₂.put s b) = ((e.toFun s).fst, b, (e.toFun s).snd.snd)
```

#### Supporting lemmas referred to in the cards (proved)

`f5_hyps_toPLens` is printed with `pp.funBinderTypes true` in addition, which shows the binder types of `fun` and `∃`.

```lean
@eq_pairGet_of_get_eq : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B} (f : S → A × B),
  (∀ (s : S), (f s).fst = l₁.get s) → (∀ (s : S), (f s).snd = l₂.get s) → f = pairGet l₁ l₂
@JointExt.symm : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B},
  Lens.JointExt l₁ l₂ → Lens.JointExt l₂ l₁
@PutComm.symm : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B},
  PutComm l₁ l₂ → PutComm l₂ l₁
@fiberEquiv_eq_of_equations : ∀ {S : Type u_1} {A : Type u_2} (l : Lens S A) (a₀ : A) (e e' : Equiv S (A × Fiber l a₀)),
  (Intertwines e.toFun l fst ∧
      (∀ (s : S), (e.toFun s).snd.val = l.put s a₀) ∧ ∀ (a : A) (c : Fiber l a₀), e.invFun (a, c) = l.put c.val a) →
    (Intertwines e'.toFun l fst ∧
        (∀ (s : S), (e'.toFun s).snd.val = l.put s a₀) ∧ ∀ (a : A) (c : Fiber l a₀), e'.invFun (a, c) = l.put c.val a) →
      e.toFun = e'.toFun ∧ e.invFun = e'.invFun
@hasConstantComplement_left_of_hasGhostComplement : ∀ {S A B : Type u_1} {l₁ : Lens S A} {l₂ : Lens S B},
  HasGhostComplement l₁ l₂ → HasConstantComplement l₁
@hasConstantComplement_right_of_hasGhostComplement : ∀ {S A B : Type u_1} {l₁ : Lens S A} {l₂ : Lens S B},
  HasGhostComplement l₁ l₂ → HasConstantComplement l₂
@toPut_putGet : ∀ {S : Type u_1} {A : Type u_2} {get : S → A} (φ : FiberMaps get),
  PutGet { get := get, put := FiberMaps.toPut φ }
@toPut_ofPut : ∀ {S : Type u_1} {A : Type u_2} (get : S → A) (put : S → A → S) (h : PutGet { get := get, put := put }),
  FiberMaps.toPut (ofPut get put h) = put
@FiberMaps.Coherent.leftInverse : ∀ {S : Type u_1} {A : Type u_2} {get : S → A} {φ : FiberMaps get},
  FiberMaps.Coherent φ → ∀ (a a' : A) (x : GetFiber get a), φ a' a (φ a a' x) = x
@surjective_of_putGet_of_nonempty : ∀ {S : Type u_1} {A : Type u_2} (get : S → A) (put : S → A → S),
  PutGet { get := get, put := put } → Nonempty S → Function.Surjective get
@veryWellBehaved_put_unique_of_isEmpty : ∀ {S : Type u_1} {A : Type u_2} (get : S → A),
  (∀ (a : S), False) →
    (∀ (put : S → A → S), VeryWellBehaved { get := get, put := put }) ∧ ∀ (put put' : S → A → S), put = put'
@getPutOn_of_totalOn_putGetOn_putIndepOn_jointExtOn : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {V : S → Prop}
  {l₁ : PLens S A} {l₂ : PLens S B},
  TotalOn V l₁ → PutGetOn V l₁ → PutIndepOn V l₁ l₂ → JointExtOn V l₁ l₂ → GetPutOn V l₁
@putPutOn_of_totalOn_putGetOn_putIndepOn_jointExtOn : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {V : S → Prop}
  {l₁ : PLens S A} {l₂ : PLens S B},
  TotalOn V l₁ → PutGetOn V l₁ → PutIndepOn V l₁ l₂ → JointExtOn V l₁ l₂ → PutPutOn V l₁
@putCommOn_of_totalOn_putGetOn_putIndepOn_jointExtOn : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {V : S → Prop}
  {l₁ : PLens S A} {l₂ : PLens S B},
  TotalOn V l₁ →
    TotalOn V l₂ →
      PutGetOn V l₁ → PutGetOn V l₂ → PutIndepOn V l₁ l₂ → PutIndepOn V l₂ l₁ → JointExtOn V l₁ l₂ → PutCommOn V l₁ l₂
@isProductDecompositionOn_toPLens_iff : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} (l₁ : Lens S A) (l₂ : Lens S B),
  IsProductDecompositionOn (fun x => True) (toPLens l₁) (toPLens l₂) ↔ IsProductDecomposition l₁ l₂
@f5_hyps_toPLens : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} (l₁ : Lens S A) (l₂ : Lens S B),
  TotalOn (fun (x : S) => True) (toPLens l₁) ∧
    TotalOn (fun (x : S) => True) (toPLens l₂) ∧
      (PutGetOn (fun (x : S) => True) (toPLens l₁) ↔ PutGet l₁) ∧
        (PutGetOn (fun (x : S) => True) (toPLens l₂) ↔ PutGet l₂) ∧
          (PutIndepOn (fun (x : S) => True) (toPLens l₁) (toPLens l₂) ↔ PutIndep l₁ l₂) ∧
            (PutIndepOn (fun (x : S) => True) (toPLens l₂) (toPLens l₁) ↔ PutIndep l₂ l₁) ∧
              (JointExtOn (fun (x : S) => True) (toPLens l₁) (toPLens l₂) ↔ Lens.JointExt l₁ l₂) ∧
                ((Nonempty (A × B) → ∃ (s : S), (fun (x : S) => True) s) ↔ Nonempty (A × B) → Nonempty S) ∧
                  (IsProductDecompositionOn (fun (x : S) => True) (toPLens l₁) (toPLens l₂) ↔
                    IsProductDecomposition l₁ l₂)
```

Edge-case and over-reading lemmas for F6 (proved). `card_veryWellBehaved_puts_empty_state_two_views` is printed with `pp.analyze true` in addition, which supplies the codomain `Bool` of `Empty.elim`:

```lean
existsUnique_put_drop_jointExt_admits_unlawful_puts : (¬∀ (s t : Bool × Bool),
      getFst s = getFst t → unitLensB.get s = unitLensB.get t → s = t) ∧
  (∀ (a : Bool) (c : Unit), ∃ s, getFst s = a ∧ unitLensB.get s = c) ∧
    (PutGet { get := getFst, put := dirtyFlag.put } ∧
        PutIndep { get := getFst, put := dirtyFlag.put } unitLensB ∧ ¬PutPut { get := getFst, put := dirtyFlag.put }) ∧
      (PutGet { get := getFst, put := resetSibling.put } ∧
          PutIndep { get := getFst, put := resetSibling.put } unitLensB ∧
            ¬GetPut { get := getFst, put := resetSibling.put }) ∧
        ¬∀ (put : Bool × Bool → Bool → Bool × Bool),
            PutGet { get := getFst, put := put } →
              PutIndep { get := getFst, put := put } unitLensB → VeryWellBehaved { get := getFst, put := put }
existsUnique_put_hsurj_not_necessary : (∀ (s t : Bool),
    id s = id t → constFalseView.get s = constFalseView.get t → s = t) ∧
  (¬∀ (a c : Bool), ∃ s, id s = a ∧ constFalseView.get s = c) ∧
    (∃ put, PutGet { get := id, put := put } ∧ PutIndep { get := id, put := put } constFalseView) ∧
      (∀ (put put' : Bool → Bool → Bool),
          PutGet { get := id, put := put } →
            PutIndep { get := id, put := put } constFalseView →
              PutGet { get := id, put := put' } → PutIndep { get := id, put := put' } constFalseView → put = put') ∧
        ∀ (put : Bool → Bool → Bool),
          PutGet { get := id, put := put } →
            PutIndep { get := id, put := put } constFalseView → VeryWellBehaved { get := id, put := put }
@exists_put_putGet_putIndep_iff : ∀ {S : Type u_1} {A : Type u_2} {C : Type u_3} (get : S → A) (m : Lens S C),
  (∃ put, PutGet { get := get, put := put } ∧ PutIndep { get := get, put := put } m) ↔
    ∀ (s : S) (a : A), ∃ s', get s' = a ∧ m.get s' = m.get s
card_veryWellBehaved_puts_empty_state_two_views : Nonempty (Equiv Bool (Fin 2)) ∧
  (∀ (a : Bool), Nonempty (Equiv (GetFiber Empty.elim a) (Fin 0))) ∧
    ¬Function.Surjective (β := Bool) Empty.elim ∧
      Nonempty
        (Equiv { put : Empty → Bool → Empty // VeryWellBehaved { get := Empty.elim, put := put : Lens Empty Bool } }
          (Fin (factorial 0 ^ (2 - 1))))
@veryWellBehaved_put_eq_self_of_subsingleton_view : ∀ {S : Type u_1} {A : Type u_2} (get : S → A),
  (∀ (a a' : A), a = a') →
    VeryWellBehaved { get := get, put := fun s x => s } ∧
      ∀ (put : S → A → S), VeryWellBehaved { get := get, put := put } → put = fun s x => s
```

where `constFalseView : Lens Bool Bool := { get := fun _ => false, put := fun s _ => s }`.

### Result cards

#### F1 — pair decomposition from PutGet, two-way PutIndep and JointExt

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Decomposition.lean`.
- **Lean:** `Toy.Lens.isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty`, `Toy.Lens.isProductDecomposition_iff_putGet_putIndep_jointExt_imp_nonempty`

**Plain claim.** For two total lenses l₁ : Lens S A and l₂ : Lens S B: if each satisfies PutGet, neither put changes the other's view (PutIndep in both directions), the two views together determine the state (JointExt), and S is nonempty whenever A × B is, then the specific map s ↦ (l₁.get s, l₂.get s) is a bijection S → A × B under which l₁.put is first-coordinate update and l₂.put is second-coordinate update; conversely, this conclusion implies all five laws and the nonemptiness condition. GetPut, PutPut and commuting puts are not assumed.

```lean
@isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3}
  {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ →
    PutGet l₂ →
      PutIndep l₁ l₂ →
        PutIndep l₂ l₁ → Lens.JointExt l₁ l₂ → (Nonempty (A × B) → Nonempty S) → IsProductDecomposition l₁ l₂
@isProductDecomposition_iff_putGet_putIndep_jointExt_imp_nonempty : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3}
  {l₁ : Lens S A} {l₂ : Lens S B},
  IsProductDecomposition l₁ l₂ ↔
    PutGet l₁ ∧ PutGet l₂ ∧ PutIndep l₁ l₂ ∧ PutIndep l₂ l₁ ∧ Lens.JointExt l₁ l₂ ∧ (Nonempty (A × B) → Nonempty S)
```

Unfolded:

```
for all types S A B and lenses l₁ : Lens S A, l₂ : Lens S B:

  (∀ s a, l₁.get (l₁.put s a) = a)                                   -- PutGet l₁
→ (∀ s b, l₂.get (l₂.put s b) = b)                                   -- PutGet l₂
→ (∀ s a, l₂.get (l₁.put s a) = l₂.get s)                            -- PutIndep l₁ l₂
→ (∀ s b, l₁.get (l₂.put s b) = l₁.get s)                            -- PutIndep l₂ l₁
→ (∀ s t, l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t)         -- JointExt l₁ l₂
→ (Nonempty (A × B) → Nonempty S)
→   (∀ s t, l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t)       -- (1) the pairing map is injective
  ∧ (∀ a b, ∃ s, l₁.get s = a ∧ l₂.get s = b)                        -- (2) the pairing map is surjective
  ∧ (∀ s a, l₁.get (l₁.put s a) = a ∧ l₂.get (l₁.put s a) = l₂.get s) -- (3) l₁.put = first-coordinate update
  ∧ (∀ s b, l₁.get (l₂.put s b) = l₁.get s ∧ l₂.get (l₂.put s b) = b) -- (4) l₂.put = second-coordinate update

and, second statement, (1) ∧ (2) ∧ (3) ∧ (4) ↔ the five laws ∧ (Nonempty (A × B) → Nonempty S).
The conclusion is IsProductDecomposition l₁ l₂ unfolded by the proved lemma
isProductDecomposition_iff_elementary.  Conjuncts (1), (3), (4) restate hypotheses.
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h₁ : PutGet l₁` | l₁.put really stores the written value: first component of 'l₁.put is first-coordinate update'. | tight | `Toy.Lens.ignorePut_tight_putGet_left` |
| `h₂ : PutGet l₂` | l₂.put really stores the written value. | tight | `Toy.Lens.ignorePutSnd_tight_putGet_right` |
| `h₁₂ : PutIndep l₁ l₂` | Frame law: writing through l₁ leaves the l₂-view alone (second component of 'l₁.put is first-coordinate update'). | tight | `Toy.Lens.twist_tight_putIndep_left`, `Toy.Lens.xorView_tight_putIndep_left` |
| `h₂₁ : PutIndep l₂ l₁` | Frame law in the other direction; also what makes the base-state construction hit every pair. | tight | `Toy.Lens.twist_tight_putIndep_right`, `Toy.Lens.xorView_tight_putIndep_right` |
| `hext : JointExt l₁ l₂` | No hidden state: injectivity of the pairing map. | tight | `Toy.Lens.ghost_tight_jointExt` |
| `hS : Nonempty (A × B) → Nonempty S` | A base state from which a given pair of views can be built (surjectivity of the pairing map). Exactly the nonemptiness condition of the equivalence; implied by Nonempty S (pass `fun _ => hS`), but holds also when A × B is empty, e.g. for an empty state type with an empty view (Toy.Lens.emptyView_isProductDecomposition_without_nonempty). | tight | `Toy.Lens.empty_tight_nonempty` |
| `S A B : arbitrary types in arbitrary universes` | No finiteness or decidability is assumed, and no inhabitedness of S, A or B beyond hS; in particular the result applies when A or B is empty. | harmless | — |

**Depth: shallow.** Three of the four conjuncts of the unfolded conclusion restate hypotheses: injectivity of the pairing map is JointExt, and 'l₁.put is first-coordinate update' unfolds to PutGet l₁ ∧ PutIndep l₁ l₂ (Toy.Lens.isProductDecomposition_iff_elementary). The only non-definitional content is surjectivity: from a base state, put through l₁ and then through l₂. The converse direction is unfolding.

**Non-vacuity witness.** fst and snd on Bool × Bool (and on any product) satisfy all six hypotheses and the conclusion. (Lean: `Toy.Lens.f1_nonvacuity_bool`, `Toy.Lens.fst_snd_satisfy_f1_hypotheses`, `Toy.Lens.fst_snd_isProductDecomposition`)

**Tier T1.** Folklore made precise. The conclusion is the situation that FZW16 describe as 'X ⋈ Y and X ⊕ Y ∈ bij-lens' and that AFP Optics assumes in locale `sym_lens`; it is also the two-location instance of the global-state theory of PP02. None of the sources checked derives it from PutGet, get-invariance in both directions and joint injectivity of the getters, or isolates that as an equivalent and irredundant law set. Not claimed novel.

**Prior art.**

- [FZW16] S. Foster, F. Zeyda, J. Woodcock. Unifying Heterogeneous State-Spaces with Lenses. ICTAC 2016, LNCS 9965, pp. 295-314, Springer, 2016. doi:10.1007/978-3-319-46750-4_17 -- Section 3.3: Definition 4 (lens independence, bundling commuting puts with both directions of get-invariance), Definition 6 (lens sum), and the description of a source divided into two disjoint views as 'X ⊕ Y ≈ 1, or equivalently X ⊕ Y ∈ bij-lens'. The situation F1 concludes is described there, not derived from a minimal law set.
- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy: locale `lens_indep` (assumptions `lens_put_comm`, `lens_put_irr1`, `lens_put_irr2`), lemma `lens_indep_vwb_iff`; Lens_Algebra.thy: `lens_plus` (get = pairing of the gets; put σ (u, v) = put_X (put_Y σ v) u), `plus_vwb_lens`; Lens_Symmetric.thy: locale `sym_lens` assumes vwb V, vwb C, V ⋈ C and bij_lens (V +_L C). Isabelle/HOL types are nonempty, so empty-type cases do not arise there.
- [PP02] G. D. Plotkin, J. Power. Notions of Computation Determine Monads. FoSSaCS 2002, LNCS 2303, pp. 342-356, Springer, 2002. doi:10.1007/3-540-45931-6_24 (full text not consulted) -- Global state over finitely many locations: the equations relating lookup and update at equal and distinct locations are the lens laws, cross-independence and commuting puts for coordinate lenses.
- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424 -- Section 3: GetPut, PutGet, PutPut for a single lens.
- [BvW98] R.-J. Back, J. von Wright. Refinement Calculus: A Systematic Introduction. Springer, 1998. doi:10.1007/978-1-4612-1674-2 (not consulted; cited in AFP Optics, Lens_Laws.thy, for the same variable axioms) -- Program variables axiomatised by access/update pairs with laws for distinct variables.
- [ACGMS18] F. Abou-Saleh, J. Cheney, J. Gibbons, J. McKinna, P. Stevens. Introduction to Bidirectional Transformations. In: Bidirectional Transformations, LNCS 9715, pp. 1-28, Springer, 2018. doi:10.1007/978-3-319-79108-1_1 (not consulted) -- Textbook introduction to lens laws.

**Design question.** Which minimal law set for two field getters/setters of a value-algebra interface yields 'setting one field changes that field and nothing else, and there is nothing else'?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For a value-algebra interface whose fields are modelled faithfully as total functions on values compared with propositional equality, stating PutGet per field, PutIndep in both directions and JointExt over the complete field list (plus inhabitedness) is necessary and sufficient for coordinate-update semantics, and GetPut, PutPut and commuting writes need not be stated separately. Reasoning: the second Lean statement is an equivalence, so the law set neither loses instances of the intended semantics nor admits others. The transfer fails wherever the model gaps listed under Applicability apply (observational rather than propositional equality, padding, partial or effectful operations).

#### F1-inverse — explicit inverse of the pairing map

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Decomposition.lean`.
- **Lean:** `Toy.Lens.pairPut_leftInverse_rightInverse_of_putGet_putIndep_jointExt`

**Plain claim.** If both lenses satisfy PutGet, writing through l₂ does not change the l₁-view (one direction of cross-independence) and the lenses are jointly extensional, then for every base state s₀ the explicit map p ↦ l₂.put (l₁.put s₀ p.1) p.2 is a two-sided inverse of s ↦ (l₁.get s, l₂.get s).

```lean
@pairPut_leftInverse_rightInverse_of_putGet_putIndep_jointExt : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3}
  {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ →
    PutGet l₂ →
      PutIndep l₂ l₁ →
        Lens.JointExt l₁ l₂ →
          ∀ (s₀ : S),
            Function.LeftInverse (pairPut l₁ l₂ s₀) (pairGet l₁ l₂) ∧
              Function.RightInverse (pairPut l₁ l₂ s₀) (pairGet l₁ l₂)
```

Unfolded:

```
for all lenses l₁ : Lens S A, l₂ : Lens S B and every s₀ : S:

  PutGet l₁ → PutGet l₂ → (∀ s b, l₁.get (l₂.put s b) = l₁.get s) → JointExt l₁ l₂
→   (∀ s, l₂.put (l₁.put s₀ (l₁.get s)) (l₂.get s) = s)
  ∧ (∀ p : A × B, (l₁.get (l₂.put (l₁.put s₀ p.1) p.2), l₂.get (l₂.put (l₁.put s₀ p.1) p.2)) = p)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h₁ : PutGet l₁` | The first write stores the first component. | tight | `Toy.Lens.pairPut_inverse_tight` |
| `h₂ : PutGet l₂` | The second write stores the second component. | tight | `Toy.Lens.pairPut_inverse_tight` |
| `h₂₁ : PutIndep l₂ l₁` | The second write must not disturb the first view. | tight | `Toy.Lens.pairPut_inverse_tight` |
| `hext : JointExt l₁ l₂` | Left-inverse half: a state is recovered from its two views. | tight | `Toy.Lens.pairPut_inverse_tight` |
| `s₀ : S` | The base state written into; any state works. | harmless | — |

**Depth: shallow.** Right inverse: three rewrites. Left inverse: joint extensionality applied to the right-inverse equations.

**Non-vacuity witness.** fst and the XOR view on Bool × Bool satisfy all hypotheses although they violate PutIndep fst xorView. (Lean: `Toy.Lens.f1_inverse_nonvacuity_bool`)

**Tier T1.** In AFP Optics vocabulary the conclusion is StrongGetPut for a lens sum (bij_lens); there it follows from assumptions. That one direction of get-invariance suffices was not found in the sources checked.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Algebra.thy `lens_plus` (put σ (u, v) = put_X (put_Y σ v) u); Lens_Laws.thy locale `bij_lens` (PutGet and StrongGetPut).
- [FZW16] S. Foster, F. Zeyda, J. Woodcock. Unifying Heterogeneous State-Spaces with Lenses. ICTAC 2016, LNCS 9965, pp. 295-314, Springer, 2016. doi:10.1007/978-3-319-46750-4_17 -- Section 3.3, lens sum and bij-lens.

**Design question.** Which law is needed for the canonical 'write both fields into a base state' constructor to invert the pair of getters?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — A "construct from field values" operation implemented as "write each field into a default value" inverts the field getters as soon as the setters store their values, the later write preserves the earlier field, and the fields determine the value. Reasoning: direct instance of the theorem with s₀ the default value; it says nothing about whether the setters are coordinate updates.

#### F1-laws — GetPut, PutPut and commuting puts are derived laws

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Decomposition.lean`.
- **Lean:** `Toy.Lens.veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt`, `Toy.Lens.getPut_of_putGet_putIndep_jointExt`, `Toy.Lens.putPut_of_putGet_putIndep_jointExt`, `Toy.Lens.putComm_of_putGet_putIndep_jointExt`

**Plain claim.** PutGet for both lenses, cross-independence in both directions and joint extensionality imply that both lenses are very well-behaved and that their puts commute; no nonemptiness assumption is needed. More precisely, GetPut l₁ and PutPut l₁ already follow from PutGet l₁, PutIndep l₁ l₂ and JointExt l₁ l₂ (no law of l₂), and commuting puts follows from the five laws.

```lean
@veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3}
  {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ →
    PutGet l₂ →
      PutIndep l₁ l₂ → PutIndep l₂ l₁ → Lens.JointExt l₁ l₂ → VeryWellBehaved l₁ ∧ VeryWellBehaved l₂ ∧ PutComm l₁ l₂
@getPut_of_putGet_putIndep_jointExt : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ → PutIndep l₁ l₂ → Lens.JointExt l₁ l₂ → GetPut l₁
@putPut_of_putGet_putIndep_jointExt : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ → PutIndep l₁ l₂ → Lens.JointExt l₁ l₂ → PutPut l₁
@putComm_of_putGet_putIndep_jointExt : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : Lens S A} {l₂ : Lens S B},
  PutGet l₁ → PutGet l₂ → PutIndep l₁ l₂ → PutIndep l₂ l₁ → Lens.JointExt l₁ l₂ → PutComm l₁ l₂
```

Unfolded:

```
under PutGet l₁, PutGet l₂, PutIndep l₁ l₂, PutIndep l₂ l₁, JointExt l₁ l₂ (no nonemptiness):

    (∀ s, l₁.put s (l₁.get s) = s) ∧ (∀ s a a', l₁.put (l₁.put s a) a' = l₁.put s a')
  ∧ (∀ s, l₂.put s (l₂.get s) = s) ∧ (∀ s b b', l₂.put (l₂.put s b) b' = l₂.put s b')
  ∧ (∀ s a b, l₂.put (l₁.put s a) b = l₁.put (l₂.put s b) a)
(GetPut l₁ and PutPut l₁ already from PutGet l₁, PutIndep l₁ l₂, JointExt l₁ l₂.)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h₁ : PutGet l₁ (bundled lemma)` | Read-back of l₁; used for GetPut l₁, PutPut l₁ and PutComm. | tight | `Toy.Lens.f1_laws_bundled_tight` |
| `h₂ : PutGet l₂ (bundled lemma)` | Read-back of l₂; used for GetPut l₂, PutPut l₂ and PutComm. | tight | `Toy.Lens.f1_laws_bundled_tight` |
| `h₁₂ : PutIndep l₁ l₂ (bundled lemma)` | Lets joint extensionality compare states after a write through l₁. | tight | `Toy.Lens.f1_laws_bundled_tight` |
| `h₂₁ : PutIndep l₂ l₁ (bundled lemma)` | Same for writes through l₂. | tight | `Toy.Lens.f1_laws_bundled_tight` |
| `hext : JointExt l₁ l₂ (bundled lemma)` | Turns equality of both views into equality of states. | tight | `Toy.Lens.f1_laws_bundled_tight` |
| `h₁, h₁₂, hext (component lemmas for GetPut l₁ and PutPut l₁)` | The three laws used by the component lemmas; each is needed. | tight | `Toy.Lens.derived_getPut_tight`, `Toy.Lens.derived_putPut_tight` |
| `h₁, h₂, h₁₂, h₂₁, hext (component lemma for PutComm)` | All five laws are used; each is needed. | tight | `Toy.Lens.derived_putComm_tight`, `Toy.Lens.derived_putComm_tight_mirror` |

**Depth: shallow.** Each conclusion is one application of joint extensionality to two states whose views agree by PutGet and PutIndep.

**Non-vacuity witness.** fst and snd on Bool × Bool. (Lean: `Toy.Lens.f1_nonvacuity_bool`)

**Tier T1.** The single-lens fact that StrongGetPut and PutGet give a very well-behaved (bijective) lens is in FHP15 and Nakano19 (and AFP Optics proves `bij_lens_vwb`). The two-lens derivation here — GetPut and PutPut of l₁ from PutGet l₁, PutIndep l₁ l₂ and JointExt, and commuting puts from the five laws — was not found in the sources checked; it is an elementary derivation and is not attributed to them.

**Prior art.**

- [FHP15] S. Fischer, Z. Hu, H. Pacheco. A Clear Picture of Lens Laws - Functional Pearl. MPC 2015, LNCS 9129, pp. 215-223, Springer, 2015. doi:10.1007/978-3-319-19797-5_10 (full text not consulted; characterised through Nakano 2019) -- Implications among single-lens laws; PutGet implies PutInjectivity (injectivity of put s, not of get) and StrongGetPut with PutInjectivity implies PutPut, so bijective lenses are very well-behaved.
- [Nakano19] K. Nakano. Towards a Complete Picture of Lens Laws. Third Workshop on Software Foundations for Data Interoperability (SFDI2019+), Fukuoka, 2019. arXiv:1910.10421v1, doi:10.48550/arXiv.1910.10421 -- Sections 1-3: the implication web among eleven single-lens laws; no law involving the getter's injectivity and no two-lens law.
- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy: locale `bij_lens` (PutGet + StrongGetPut) and lemma `bij_lens_vwb` (bijective lenses are very well-behaved); `lens_indep` bundles commuting puts with both get-invariance laws.

**Design question.** Which of GetPut, PutPut and commuting puts may be dropped from a field interface because they follow from the others?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — An interface that already requires PutGet, two-way PutIndep and JointExt for its complete field list does not need to state GetPut, PutPut or commuting writes. Reasoning: they are proved consequences; the converse warning (they must be stated when JointExt is absent) is F4-derived-putComm.

#### F2 — finite indexed decomposition

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Decomposition.lean`.
- **Lean:** `Toy.Lens.isPiDecomposition_of_putGet_pairwiseIndep_famJointExt_finite_imp_nonempty`, `Toy.Lens.isPiDecomposition_iff_putGet_pairwiseIndep_famJointExt_imp_nonempty_of_finite`

**Plain claim.** For a family of total lenses l i : Lens S (A i) indexed by a finite type ι (enumerated by a list, duplicates allowed): if every lens satisfies PutGet, writing through any lens leaves every other view unchanged, the views together determine the state, and S is nonempty whenever the product (i : ι) → A i is, then the specific map s ↦ (fun i => (l i).get s) is a bijection S → (i : ι) → A i under which each (l i).put is update of coordinate i; conversely, this conclusion implies the three laws and the nonemptiness condition.

```lean
@isPiDecomposition_of_putGet_pairwiseIndep_famJointExt_finite_imp_nonempty : ∀ {S : Type u_1} {ι : Type u_3}
  {A : ι → Type u_2} [inst : DecidableEq ι] {l : (i : ι) → Lens S (A i)},
  (∀ (i : ι), PutGet (l i)) →
    PairwiseIndep l →
      FamJointExt l →
        ∀ (elems : List ι), (∀ (i : ι), i ∈ elems) → (Nonempty ((i : ι) → A i) → Nonempty S) → IsPiDecomposition l
@isPiDecomposition_iff_putGet_pairwiseIndep_famJointExt_imp_nonempty_of_finite : ∀ {S : Type u_1} {ι : Type u_3}
  {A : ι → Type u_2} [inst : DecidableEq ι] {l : (i : ι) → Lens S (A i)} (elems : List ι),
  (∀ (i : ι), i ∈ elems) →
    (IsPiDecomposition l ↔
      (∀ (i : ι), PutGet (l i)) ∧ PairwiseIndep l ∧ FamJointExt l ∧ (Nonempty ((i : ι) → A i) → Nonempty S))
```

Unfolded:

```
for a finite index type ι (∀ i, i ∈ elems) and lenses l i : Lens S (A i):

  (∀ i s a, (l i).get ((l i).put s a) = a)
→ (∀ i j, i ≠ j → ∀ s a, (l j).get ((l i).put s a) = (l j).get s)
→ (∀ s t, (∀ i, (l i).get s = (l i).get t) → s = t)
→ (Nonempty ((i : ι) → A i) → Nonempty S)
→   (∀ s t, (∀ i, (l i).get s = (l i).get t) → s = t)
  ∧ (∀ f : (i : ι) → A i, ∃ s, ∀ i, (l i).get s = f i)
  ∧ (∀ i s a, (l i).get ((l i).put s a) = a)
  ∧ (∀ i j, i ≠ j → ∀ s a, (l j).get ((l i).put s a) = (l j).get s)
(by the proved lemma isPiDecomposition_iff_elementary); second statement: the converse.
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hpg : ∀ i, PutGet (l i)` | Each write stores its value. | tight | `Toy.Lens.fam2_ignorePut_tight_putGet` |
| `hind : PairwiseIndep l` | Frame law for every ordered pair of distinct indices. | tight | `Toy.Lens.fam2_twist_tight_pairwiseIndep` |
| `hext : FamJointExt l` | No hidden state. | tight | `Toy.Lens.ghostFam_tight_famJointExt` |
| `elems : List ι, helems : ∀ i, i ∈ elems` | Finiteness of the index type: the target tuple is reached by finitely many writes. | tight | `Toy.Lens.evCoord_tight_finite_index` |
| `hS : Nonempty ((i : ι) → A i) → Nonempty S` | A base state from which a given tuple can be built; exactly the nonemptiness condition of the equivalence; implied by Nonempty S. | tight | `Toy.Lens.emptyFam_tight_nonempty` |
| `[DecidableEq ι]` | Needed only to state coordinate update (`update`, `coord`, `IsPiDecomposition`). | harmless | — |

**Depth: shallow.** As for F1, all conjuncts except surjectivity restate hypotheses (Toy.Lens.isPiDecomposition_iff_elementary). Surjectivity: write the target tuple index by index along the enumeration; a list induction.

**Non-vacuity witness.** The coordinate lenses on Bool → Bool. (Lean: `Toy.Lens.coord_bool_satisfy_f2_hypotheses`, `Toy.Lens.coord_isPiDecomposition`)

**Tier T1.** Same status as F1, for finitely many fields. AFP Optics assumes finite spanning families of pairwise independent lenses (and FIP26 describes such state spaces); the coordinate-lens instance is AFP `fun_lens`. The derivation from PutGet, pairwise get-invariance, joint injectivity, finiteness and the nonemptiness condition was not found. Not claimed novel.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Instances.thy: `fun_lens x` (requires the value type in class `two`, i.e. at least two elements) and `fun_lens_indep`; Scene_Spaces.thy and Frames.thy in the same commit treat finite spanning families of independent scenes (not read in detail).
- [PP02] G. D. Plotkin, J. Power. Notions of Computation Determine Monads. FoSSaCS 2002, LNCS 2303, pp. 342-356, Springer, 2002. doi:10.1007/3-540-45931-6_24 (full text not consulted) -- Global state over a finite set of locations generates the state monad on V^Loc.
- [PSh04] A. J. Power, O. Shkaravska. From Comodels to Coalgebras: State and Arrays. CMCS 2004, ENTCS 106, pp. 297-314, 2004. doi:10.1016/j.entcs.2004.02.041 (full text not consulted) -- Comodels of global state and arrays; the finite-versus-infinite-locations distinction parallels the finiteness hypothesis.
- [FIP26] S. Foster, C. Isasa, C. Pardillo Laursen. Scenes: A Meta-Logical Algebra for Mutable State. arXiv:2609.29380v1, 2026 (not consulted) -- State spaces as finite families of pairwise independent lenses whose sum is bijective.

**Design question.** When do n field getters/setters with frame laws present the value as the product of the fields?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For a value type with a fixed finite list of fields (all fields listed), per-field PutGet, pairwise PutIndep and family-wide JointExt characterise "the value is the tuple of its fields and each setter updates one coordinate". Reasoning: instance of the equivalence; requires the field list to be finite and fixed for all values (not dynamically keyed) and the field types to be independent of other fields' values.

#### F2-laws — derived laws for families

- **Kind:** theorem. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Decomposition.lean`.
- **Lean:** `Toy.Lens.getPut_of_putGet_pairwiseIndep_famJointExt`, `Toy.Lens.putPut_of_putGet_pairwiseIndep_famJointExt`, `Toy.Lens.putComm_of_putGet_pairwiseIndep_famJointExt`

**Plain claim.** For a family of lenses and an index i: if l i satisfies PutGet, writing through l i leaves every other view unchanged, and the family is jointly extensional, then l i satisfies GetPut and PutPut; for distinct indices i ≠ j, if l i and l j satisfy PutGet, writes through either leave every other view unchanged, and the family is jointly extensional, then the puts of l i and l j commute. No decidable equality on the index type is needed.

```lean
@getPut_of_putGet_pairwiseIndep_famJointExt : ∀ {S : Type u_1} {ι : Type u_3} {A : ι → Type u_2}
  {l : (i : ι) → Lens S (A i)} {i : ι},
  PutGet (l i) → (∀ (j : ι), i ≠ j → PutIndep (l i) (l j)) → FamJointExt l → GetPut (l i)
@putPut_of_putGet_pairwiseIndep_famJointExt : ∀ {S : Type u_1} {ι : Type u_3} {A : ι → Type u_2}
  {l : (i : ι) → Lens S (A i)} {i : ι},
  PutGet (l i) → (∀ (j : ι), i ≠ j → PutIndep (l i) (l j)) → FamJointExt l → PutPut (l i)
@putComm_of_putGet_pairwiseIndep_famJointExt : ∀ {S : Type u_1} {ι : Type u_3} {A : ι → Type u_2}
  {l : (i : ι) → Lens S (A i)} {i j : ι},
  i ≠ j →
    PutGet (l i) →
      PutGet (l j) →
        (∀ (k : ι), i ≠ k → PutIndep (l i) (l k)) →
          (∀ (k : ι), j ≠ k → PutIndep (l j) (l k)) → FamJointExt l → PutComm (l i) (l j)
```

Unfolded:

```
for an index i:   PutGet (l i) → (∀ j, i ≠ j → PutIndep (l i) (l j)) → FamJointExt l → GetPut (l i) ∧ PutPut (l i)
for i ≠ j:        PutGet (l i) → PutGet (l j) → frame laws at i and at j → FamJointExt l → PutComm (l i) (l j)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hpg : PutGet (l i) (GetPut, PutPut)` | Read-back at the index concerned. | tight | `Toy.Lens.f2_getPut_tight`, `Toy.Lens.f2_putPut_tight` |
| `hind : ∀ j, i ≠ j → PutIndep (l i) (l j) (GetPut, PutPut)` | Writes through l i keep the other views. | tight | `Toy.Lens.f2_getPut_tight`, `Toy.Lens.f2_putPut_tight` |
| `hext : FamJointExt l (all three)` | Equal views give equal states. | tight | `Toy.Lens.f2_getPut_tight`, `Toy.Lens.f2_putPut_tight`, `Toy.Lens.f2_putComm_tight` |
| `hij : i ≠ j (PutComm)` | Two writes through the same lens do not commute. | tight | `Toy.Lens.f2_putComm_tight` |
| `hpi : PutGet (l i), hpj : PutGet (l j) (PutComm)` | Read-back at both indices. | tight | `Toy.Lens.f2_putComm_tight` |
| `hindi, hindj : frame laws at i and at j (PutComm)` | Writes through l i and through l j keep the other views. | tight | `Toy.Lens.f2_putComm_tight` |

**Depth: shallow.** One application of joint extensionality, with a classical case split on index equality.

**Non-vacuity witness.** The coordinate lenses on Bool → Bool at the indices false and true. (Lean: `Toy.Lens.f2_laws_nonvacuity_bool`)

**Tier T1.** Indexed analogue of F1-laws; not found in the sources checked.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy `lens_indep_vwb_iff`; Lens_Instances.thy `fun_lens_indep`.

**Design question.** Which per-field laws may be dropped from an n-field interface?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Per-field GetPut, PutPut and pairwise commuting writes are redundant in an interface that requires PutGet, frame laws and family-wide JointExt. Reasoning: proved consequences; family-wide JointExt is essential.

#### F3 — very well-behaved iff constant complement

- **Kind:** characterization. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Complement.lean`.
- **Lean:** `Toy.Lens.veryWellBehaved_iff_hasConstantComplement`

**Plain claim.** A total lens l : Lens S A is very well-behaved if and only if it has a constant complement: a type C in the universe of S and a bijection S ≃ A × C under which get is the first projection and put is first-coordinate update. Neither S nor A is assumed nonempty.

```lean
@veryWellBehaved_iff_hasConstantComplement : ∀ {S : Type u_1} {A : Type u_2} (l : Lens S A),
  VeryWellBehaved l ↔ HasConstantComplement l
```

Unfolded:

```
for every lens l : Lens S A:

  (GetPut l ∧ PutGet l ∧ PutPut l)
↔ ∃ (C : Type u) (e : Equiv S (A × C)),
      (∀ s, (e.toFun s).1 = l.get s) ∧ (∀ s a, e.toFun (l.put s a) = (a, (e.toFun s).2))
(by the proved lemma hasConstantComplement_iff_elementary)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `left-hand side, GetPut l` | Needed: without it no constant complement exists. | tight | `Toy.Lens.f3_laws_tight` |
| `left-hand side, PutGet l` | Needed: without it no constant complement exists. | tight | `Toy.Lens.f3_laws_tight` |
| `left-hand side, PutPut l` | Needed: without it no constant complement exists. | tight | `Toy.Lens.f3_laws_tight` |
| `C : Type u (universe of S) inside HasConstantComplement` | Lets the forward direction use the quotient construction; for complements in other universes the backward direction is F3-sharp. | harmless | — |

**Depth: shallow.** Backward: compute under the bijection and cancel it (F3-sharp). Forward: take C to be S modulo 'put s = put t', map s ↦ (get s, [s]) and (a, [s]) ↦ put s a; GetPut gives one inverse law, PutGet and PutPut the other.

**Non-vacuity witness.** fst on Bool × Bool (complement: the second field); the state-twisting lens (complement: a xor b). (Lean: `Toy.Lens.f3_nonvacuity_bool`, `Toy.Lens.fst_hasConstantComplement`, `Toy.Lens.twist_hasConstantComplement`)

**Tier T0.** Known result restated. PS03 Theorem 2.3.9 states it with no inhabitedness assumption (via the put-orbit construction), and CDV21 mechanise it in Agda for sources that are sets (`≃Σ∥set⁻¹∥×`, no inhabitedness assumption on the source or the view). FGMPS07 footnote 9 and JRW10 Theorem 12 / Corollary 13 state it for a non-empty view set. What differs here is only the Lean formulation: the complement is required to live in the universe of S, where the quotient of S by 'put s = put t' provides one; the CDV21 complement is a subtype of the function type B → A.

**Prior art.**

- [PS03] B. C. Pierce, A. Schmitt. Lenses and View Update Translation. Working draft of April 3, 2003, University of Pennsylvania. https://www.cis.upenn.edu/~bcpierce/papers/dblenses.pdf (full text read) -- Theorem 2.3.9: for a fully total very-well-behaved lens on C and A, the set C is isomorphic to A × {λx. put(x, c) | c ∈ C} (the set of put-orbit functions, which is in bijection with C modulo 'put s = put t', the complement used here); no inhabitedness assumption in the theorem (Lemma 2.3.8 treats C ≠ ∅ separately). Also cited as the basis of the Agda lemma `≃Σ∥set⁻¹∥×` of CDV21.
- [CDV21] P. Capriotti, N. A. Danielsson, A. Vezzosi. Higher Lenses. 36th ACM/IEEE Symposium on Logic in Computer Science (LICS 2021), pp. 1-13. doi:10.1109/LICS52264.2021.9470613; Agda development https://github.com/nad/dependent-lenses commit c09739a91f522074c9b3508e56252013219f359c (abstract and src/Lens/Non-dependent/Traditional.agda read; the paper's own lemma numbering not checked) -- src/Lens/Non-dependent/Traditional.agda: `≃Σ∥set⁻¹∥×` (source a set; complement {f : B → A | f in the image of set, truncated}); the higher-lens formulation in the paper.
- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424 -- Section 10 and footnote 9: very well-behaved total lenses characterise the source as isomorphic to A × B for some B; stated without proof.
- [JRW10] M. Johnson, R. D. Rosebrugh, R. J. Wood. Algebras and Update Strategies. J. Univers. Comput. Sci. 16(5):729-748, 2010. doi:10.3217/jucs-016-05-0729 -- Proposition 9, Theorem 12 (non-empty view set), Corollary 13.
- [BS81] F. Bancilhon, N. Spyratos. Update semantics of relational views. ACM Trans. Database Syst. 6(4):557-575, 1981. doi:10.1145/319628.319634 (full text not consulted) -- Origin of update translation under a constant complement (a complement need only make s ↦ (f s, g s) injective).
- [GJ12] J. Gibbons, M. Johnson. Relating Algebraic and Coalgebraic Descriptions of Lenses. Electronic Communications of the EASST 49 (BX 2012), 2012. doi:10.14279/tuj.eceasst.49.726 (full text not consulted) -- Very well-behaved lenses as coalgebras for the store comonad.
- [JR12] M. Johnson, R. D. Rosebrugh. Lens put-put laws: monotonic and mixed. Electronic Communications of the EASST 49 (BX 2012), 2012. doi:10.14279/tuj.eceasst.49.729 (abstract read; full text not consulted) -- Monotonic and mixed put-put laws, weaker than PutPut; F3 assumes the classical PutPut and says nothing about these laws.
- [JRW12] M. Johnson, R. D. Rosebrugh, R. J. Wood. Lenses, fibrations and universal translations. Math. Struct. Comput. Sci. 22(1):25-42, 2012. doi:10.1017/S0960129511000442 (abstract read; full text not consulted) -- Constant-complement lenses in general categories (split opfibrations).
- [HPW11] M. Hofmann, B. C. Pierce, D. Wagner. Symmetric lenses. POPL 2011, pp. 371-384. doi:10.1145/1926385.1926428 (not consulted) -- Symmetric lenses with an explicit complement.
- [Mech] Other mechanisations: the Lean 4 repository fraware/lean-optics and the Coq repository bedrocksystems/coq-lens provide basic lens definitions; Mathlib has no lens library. Not inspected here; no decomposition, complement or classification theorem is known to be in them. -- Mechanised F3 found only in AFP Optics (as scenes) and in the CDV21 Agda development.

**Design question.** Is 'very well-behaved' the same as 'the state splits as field × rest and the setter replaces the field'?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — A setter that satisfies the three single-lens laws behaves, up to a change of representation, like "replace the field, keep the rest" — but the rest is some type determined by the setter itself, not a sibling field chosen by the interface designer. Reasoning: the equivalence plus the twist example; it does not support the reading "a lawful setter preserves the sibling fields".

#### F3-sharp — an injective field × rest representation suffices

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Complement.lean`.
- **Lean:** `Toy.Lens.veryWellBehaved_of_injective_intertwines_fst`

**Plain claim.** If some injective map f : S → A × C (C in any universe) carries l to the first-projection lens (get is the first component and put is first-coordinate update under f), then l is very well-behaved.

```lean
@veryWellBehaved_of_injective_intertwines_fst : ∀ {S : Type u_1} {A : Type u_2} {C : Type u_3} (l : Lens S A)
  (f : S → A × C), Function.Injective f → Intertwines f l fst → VeryWellBehaved l
```

Unfolded:

```
for f : S → A × C (C in any universe):
  Function.Injective f → (∀ s, (f s).1 = l.get s) → (∀ s a, f (l.put s a) = (a, (f s).2)) → VeryWellBehaved l
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hf : Function.Injective f` | Needed to cancel f in GetPut and PutPut. | tight | `Toy.Lens.dirtyFlag_intertwines_fst_noninjective` |
| `h : Intertwines f l fst` | The map must turn l into first-coordinate update. | tight | `Toy.Lens.f3_sharp_intertwines_tight` |
| `C : Type x (any universe)` | No universe restriction. | harmless | — |

**Depth: shallow.** Three short computations under f, two of them finished by injectivity.

**Non-vacuity witness.** The identity map on Bool × Bool and fst. (Lean: `Toy.Lens.f3_sharp_nonvacuity_bool`)

**Tier T0.** The backward direction of F3 in sharpened form (injectivity instead of bijectivity); this is the form of the constant-complement condition in BS81 as described in FGMPS07 and JRW10.

**Prior art.**

- [BS81] F. Bancilhon, N. Spyratos. Update semantics of relational views. ACM Trans. Database Syst. 6(4):557-575, 1981. doi:10.1145/319628.319634 (full text not consulted) -- Constant complement with injective (not necessarily bijective) pairing.
- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424 -- Section 10, footnote 9.

**Design question.** Is an injective field × rest representation enough to make a setter lawful?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Exhibiting an injective encoding of values as (field, rest) under which the setter replaces the field and keeps the rest is enough to establish the three single-lens laws. Reasoning: direct instance.

#### F3-fiber — the fibre over a base view is a complement

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Complement.lean`.
- **Lean:** `Toy.Lens.fiber_isConstantComplement_of_veryWellBehaved`

**Plain claim.** If l is very well-behaved and a base view a₀ is given, there is a bijection S ≃ A × Fiber l a₀ that turns get into the first projection and put into first-coordinate update, whose forward map sends s to (l.get s, l.put s a₀) and whose inverse sends (a, c) to l.put c a. (That these equations determine the bijection uniquely is the proved lemma Toy.Lens.fiberEquiv_eq_of_equations.)

Printed with `pp.funBinderTypes true` in addition, which shows the type of the `∃`-bound `e`:

```lean
@fiber_isConstantComplement_of_veryWellBehaved : ∀ {S : Type u_1} {A : Type u_2} (l : Lens S A),
  VeryWellBehaved l →
    ∀ (a₀ : A),
      ∃ (e : Equiv S (A × Fiber l a₀)),
        Intertwines e.toFun l fst ∧
          (∀ (s : S), (e.toFun s).snd.val = l.put s a₀) ∧ ∀ (a : A) (c : Fiber l a₀), e.invFun (a, c) = l.put c.val a
```

Unfolded:

```
VeryWellBehaved l → ∀ a₀ : A, ∃ e : Equiv S (A × {s // l.get s = a₀}),
      (∀ s, (e.toFun s).1 = l.get s) ∧ (∀ s a, e.toFun (l.put s a) = (a, (e.toFun s).2))
    ∧ (∀ s, (e.toFun s).2.1 = l.put s a₀) ∧ (∀ a c, e.invFun (a, c) = l.put c.1 a)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hl : VeryWellBehaved l` | Each of the three laws is needed. | tight | `Toy.Lens.f3_laws_tight` |
| `a₀ : A` | A base view, used to park the field; the statement is vacuous when A is empty. | harmless | — |

**Depth: shallow.** PutPut gives put (put s a) a₀ = put s a₀; GetPut and PutGet close both inverse laws.

**Non-vacuity witness.** fst on Bool × Bool with base view false. (Lean: `Toy.Lens.f3_nonvacuity_bool`)

**Tier T0.** JRW10 Corollary 13; mechanised in Agda as `≃get⁻¹×` in the CDV21 development (which cites JRW10 Corollary 13).

**Prior art.**

- [JRW10] M. Johnson, R. D. Rosebrugh, R. J. Wood. Algebras and Update Strategies. J. Univers. Comput. Sci. 16(5):729-748, 2010. doi:10.3217/jucs-016-05-0729 -- Corollary 13: for V non-empty, v0 in V and C = g⁻¹(v0), ⟨g, p(v0, -)⟩ : S → V × C is an isomorphism inverse to p restricted to V × C.
- [CDV21] P. Capriotti, N. A. Danielsson, A. Vezzosi. Higher Lenses. 36th ACM/IEEE Symposium on Logic in Computer Science (LICS 2021), pp. 1-13. doi:10.1109/LICS52264.2021.9470613; Agda development https://github.com/nad/dependent-lenses commit c09739a91f522074c9b3508e56252013219f359c (abstract and src/Lens/Non-dependent/Traditional.agda read; the paper's own lemma numbering not checked) -- src/Lens/Non-dependent/Traditional.agda: `≃get⁻¹×` (given b₀ : B, view type a set).
- [Riley18] M. Riley. Categories of Optics. arXiv:1809.00738v2, doi:10.48550/arXiv.1809.00738, 2018 (full text not consulted; Proposition 4.1.3 and Section 4.10 as cited in the literature) -- Proposition 4.1.3: the categorical form of the fibre splitting.

**Design question.** Given a default field value, what is the concrete 'rest of the state'?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Given a default value of the field, "the rest of the value" can be represented concretely as the values whose field equals the default (write the default into the value). Reasoning: direct instance; the parked value need not equal the intended sibling fields (twist_put_park).

#### F3-pair — very well-behaved and commuting iff ghost complement

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Complement.lean`.
- **Lean:** `Toy.Lens.veryWellBehaved_and_putComm_iff_hasGhostComplement`

**Plain claim.** Two lenses l₁ : Lens S A and l₂ : Lens S B are both very well-behaved and have commuting puts if and only if there are a type G in the universe of S and a bijection S ≃ A × B × G under which l₁ and l₂ are the first and second field lenses and neither touches the G component.

```lean
@veryWellBehaved_and_putComm_iff_hasGhostComplement : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} (l₁ : Lens S A)
  (l₂ : Lens S B), VeryWellBehaved l₁ ∧ VeryWellBehaved l₂ ∧ PutComm l₁ l₂ ↔ HasGhostComplement l₁ l₂
```

Unfolded:

```
  (VeryWellBehaved l₁ ∧ VeryWellBehaved l₂ ∧ ∀ s a b, l₂.put (l₁.put s a) b = l₁.put (l₂.put s b) a)
↔ ∃ (G : Type u) (e : Equiv S (A × B × G)),
      (∀ s, (e.toFun s).1 = l₁.get s) ∧ (∀ s a, e.toFun (l₁.put s a) = (a, (e.toFun s).2.1, (e.toFun s).2.2))
    ∧ (∀ s, (e.toFun s).2.1 = l₂.get s) ∧ (∀ s b, e.toFun (l₂.put s b) = ((e.toFun s).1, b, (e.toFun s).2.2))
(by the proved lemma hasGhostComplement_iff_elementary)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `left-hand side, VeryWellBehaved l₁ (GetPut, PutGet, PutPut)` | Each law of l₁ is needed (instances next to a trivial lens). | tight | `Toy.Lens.ghostComplement_laws_tight` |
| `left-hand side, VeryWellBehaved l₂ (GetPut, PutGet, PutPut)` | Each law of l₂ is needed (mirror instances). | tight | `Toy.Lens.ghostComplement_laws_tight` |
| `left-hand side, PutComm l₁ l₂` | Needed: two copies of fst, or twist with snd, are very well-behaved but have no ghost complement. | tight | `Toy.Lens.ghostComplement_laws_tight`, `Toy.Lens.twist_snd_not_hasGhostComplement` |
| `G : Type u (universe of S) inside HasGhostComplement` | Universe of the ghost. | harmless | — |

**Depth: shallow.** Forward: the sum lens s ↦ (l₁.get s, l₂.get s) is very well-behaved; apply F3 and reassociate. Backward: compute under the bijection.

**Non-vacuity witness.** fst and snd on Bool × Bool (one-point ghost); ghostFst and ghostSnd (ghost the third component). (Lean: `Toy.Lens.f3_pair_nonvacuity_bool`, `Toy.Lens.ghost_hasGhostComplement`)

**Tier T1.** A two-step corollary of known results: AFP `lens_indep_vwb_iff` (for very well-behaved lenses, independence is equivalent to commuting puts) and `plus_vwb_lens` make the sum lens very well-behaved, and F3 applied to it gives the ghost complement; it is also the two-location case of comodels of global state (PSh04). The statement itself, with an explicit ghost type and no inhabitedness assumption, was not found in the sources checked; hence T1 rather than T0.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy line 446, `lens_indep_vwb_iff`; Lens_Algebra.thy `plus_vwb_lens`.
- [PSh04] A. J. Power, O. Shkaravska. From Comodels to Coalgebras: State and Arrays. CMCS 2004, ENTCS 106, pp. 297-314, 2004. doi:10.1016/j.entcs.2004.02.041 (full text not consulted) -- Comodels of global state with finitely many locations.
- [PP02] G. D. Plotkin, J. Power. Notions of Computation Determine Monads. FoSSaCS 2002, LNCS 2303, pp. 342-356, Springer, 2002. doi:10.1007/3-540-45931-6_24 (full text not consulted) -- Equations for distinct locations (commuting updates).

**Design question.** Without assuming the listed fields are all there is, what do the frame laws for two fields guarantee, and which law must then be stated explicitly?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Two field setters that each satisfy the single-lens laws and whose writes commute are two fields of a record with an untouched remainder, even when the two fields are not all of the value; commuting writes must then be stated explicitly. Reasoning: the equivalence, together with F4-derived-putComm showing that two-way PutIndep does not imply commuting writes.

#### F4-derived-putComm — commuting puts is independent without JointExt

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Tightness.lean`.
- **Lean:** `Toy.Lens.derived_putComm_tight`, `Toy.Lens.derived_putComm_tight_mirror`

**Plain claim.** Without joint extensionality, commuting puts is an independent law: ghostFst and ghostTwistSnd on Bool × Bool × Bool are both very well-behaved and cross-independent in both directions, yet their puts do not commute; together with the other instances, each of the five hypotheses of putComm_of_putGet_putIndep_jointExt is needed.

```lean
derived_putComm_tight : (¬PutGet copySibling ∧
    PutGet sndB ∧
      PutIndep copySibling sndB ∧
        PutIndep sndB copySibling ∧ Lens.JointExt copySibling sndB ∧ ¬PutComm copySibling sndB) ∧
  (PutGet twist ∧
      PutGet sndB ∧ ¬PutIndep twist sndB ∧ PutIndep sndB twist ∧ Lens.JointExt twist sndB ∧ ¬PutComm twist sndB) ∧
    VeryWellBehaved ghostFstB ∧
      VeryWellBehaved ghostTwistSnd ∧
        PutIndep ghostFstB ghostTwistSnd ∧
          PutIndep ghostTwistSnd ghostFstB ∧ ¬Lens.JointExt ghostFstB ghostTwistSnd ∧ ¬PutComm ghostFstB ghostTwistSnd
derived_putComm_tight_mirror : (PutGet sndB ∧
    ¬PutGet copySibling ∧
      PutIndep sndB copySibling ∧
        PutIndep copySibling sndB ∧ Lens.JointExt sndB copySibling ∧ ¬PutComm sndB copySibling) ∧
  PutGet sndB ∧
    PutGet twist ∧ PutIndep sndB twist ∧ ¬PutIndep twist sndB ∧ Lens.JointExt sndB twist ∧ ¬PutComm sndB twist
```

**Hypothesis ledger.** None: this result is a closed statement about concrete instances.

**Depth: shallow.** Finite case analysis on Booleans.

**Tier T1.** Concrete instances constructed for this package; no source located that exhibits very well-behaved, two-way cross-independent but non-commuting lenses.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy `lens_indep_vwb_iff`: for very well-behaved lenses, commuting puts implies get-invariance in both directions; the converse fails by this instance.

**Design question.** Must a field interface without 'no other fields' state commuting writes explicitly?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — An interface for a subset of the fields of a value (with other fields present) must state commuting writes explicitly. Reasoning: the instance is a three-field record restricted to two fields.

#### F4-aliasing — a field is not independent of itself

- **Kind:** impossibility. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Tightness.lean`.
- **Lean:** `Toy.Lens.not_putIndep_self_of_putGet`, `Toy.Lens.aliasing_fails_putIndep_both_directions`

**Plain claim.** A lens satisfying PutGet on an inhabited state type whose view type has two distinct values is not cross-independent of itself; in particular two aliasing copies of a field violate both directions of PutIndep at once.

```lean
@not_putIndep_self_of_putGet : ∀ {S : Type u_1} {A : Type u_2} (l : Lens S A),
  PutGet l → ∀ (s₀ : S) {a a' : A}, a ≠ a' → ¬PutIndep l l
aliasing_fails_putIndep_both_directions : PutGet idB ∧
  Lens.JointExt idB idB ∧ (Nonempty (Bool × Bool) → Nonempty Bool) ∧ ¬PutIndep idB idB ∧ ¬IsProductDecomposition idB idB
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `h : PutGet l` | The write must be visible to the read. | tight | `Toy.Lens.not_putIndep_self_tight` |
| `s₀ : S` | An inhabited state type. | tight | `Toy.Lens.not_putIndep_self_tight` |
| `hne : a ≠ a'` | Two distinct view values. | tight | `Toy.Lens.not_putIndep_self_tight` |

**Depth: shallow.** Two applications of PutGet and PutIndep at one state.

**Non-vacuity witness.** fst on Bool × Bool. (Lean: `Toy.Lens.aliasing_nonvacuity_bool`)

**Positive control.** The one-point view unitLensB satisfies PutGet on an inhabited state type and is cross-independent of itself (third instance of not_putIndep_self_tight). (Lean: `Toy.Lens.not_putIndep_self_tight`)

**Tier T0.** Irreflexivity of independence for effectual lenses: AFP `lens_indep_quasi_irrefl`; FZW16 Section 3.3.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Algebra.thy `lens_indep_quasi_irrefl`.
- [FZW16] S. Foster, F. Zeyda, J. Woodcock. Unifying Heterogeneous State-Spaces with Lenses. ICTAC 2016, LNCS 9965, pp. 295-314, Springer, 2016. doi:10.1007/978-3-319-46750-4_17 -- Section 3.3: independence is irreflexive unless the lens is ineffectual.

**Design question.** Do the frame laws exclude two names for the same field?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Frame laws between two field names exclude the case that the two names alias one field (whenever the field has two distinct values and values exist). Reasoning: direct instance of the impossibility.

#### F4-bare-bijection — a bare bijection cannot express "no hidden state"

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Tightness.lean`.
- **Lean:** `Toy.Lens.ghost_admits_unrelated_bijection`

**Plain claim.** The ghost record Nat × Nat × Bool is in bijection with Nat × Nat although its two Nat field lenses are not jointly extensional and do not form a product decomposition; so a conclusion of the form 'some bijection S ≃ A × B exists' cannot express 'no hidden state'.

Printed with `pp.analyze true` in addition, which supplies the state type `Nat × Nat × Bool` of `ghostFst` and `ghostSnd`:

```lean
ghost_admits_unrelated_bijection : Nonempty (Equiv (Nat × Nat × Bool) (Nat × Nat)) ∧
  ¬Lens.JointExt (S := Nat × Nat × Bool) ghostFst ghostSnd ∧
    ¬IsProductDecomposition (S := Nat × Nat × Bool) ghostFst ghostSnd
```

**Hypothesis ledger.** None: this result is a closed statement about concrete instances.

**Depth: shallow.** An explicit bijection on infinite types (parity of the first number encodes the ghost bit), proved with division and remainder by 2; the failure of joint extensionality is a two-state check.

**Tier T0.** Textbook fact (Nat × Nat × Bool and Nat × Nat are in bijection), used as a methodological warning.

**Prior art.**

- [FZW16] S. Foster, F. Zeyda, J. Woodcock. Unifying Heterogeneous State-Spaces with Lenses. ICTAC 2016, LNCS 9965, pp. 295-314, Springer, 2016. doi:10.1007/978-3-319-46750-4_17 -- Section 3.3: bij-lens is stated for the specific sum lens, not for an arbitrary bijection.

**Design question.** How must a decomposition theorem be phrased so that it excludes hidden state?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — A specification that says only "values are in bijection with tuples of field values" does not exclude hidden state; the specific tuple-of-getters map must be named. Reasoning: the counterexample.

#### F4-F2-finite — finiteness is needed in F2

- **Kind:** counterexample. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Tightness.lean`.
- **Lean:** `Toy.Lens.evCoord_tight_finite_index`

**Plain claim.** The coordinate lenses on eventually-false Boolean sequences, indexed by Nat, satisfy PutGet, pairwise cross-independence, joint extensionality and the nonemptiness condition, Nat is not enumerated by any list, and the tuple-of-views map is not surjective; so finiteness cannot be dropped from F2.

Printed with `pp.funBinderTypes true` in addition, which shows the type `List Nat` of `elems`:

```lean
evCoord_tight_finite_index : (∀ (i : Nat), PutGet (evCoord i)) ∧
  PairwiseIndep evCoord ∧
    FamJointExt evCoord ∧
      (¬∃ (elems : List Nat), ∀ (i : Nat), i ∈ elems) ∧
        (Nonempty (Nat → Bool) → Nonempty EvFalse) ∧ ¬Function.Surjective (famGet evCoord) ∧ ¬IsPiDecomposition evCoord
```

**Hypothesis ledger.** None: this result is a closed statement about concrete instances.

**Depth: shallow.** Infinite types: the constant-true sequence is not eventually false; the non-finiteness of Nat uses that every element of a list is at most its sum.

**Tier T0.** The direct sum versus direct product phenomenon; textbook.

**Prior art.**

- [PSh04] A. J. Power, O. Shkaravska. From Comodels to Coalgebras: State and Arrays. CMCS 2004, ENTCS 106, pp. 297-314, 2004. doi:10.1016/j.entcs.2004.02.041 (full text not consulted) -- Finite versus infinite arrays of locations.

**Design question.** Can the n-field decomposition be stated for an unbounded set of fields?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — The n-field decomposition cannot be stated for an unbounded set of fields without losing surjectivity. Reasoning: the counterexample on eventually-false sequences.

#### F5 — variant-scoped pair decomposition for partial lenses

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Partial.lean`.
- **Lean:** `Toy.Lens.PLens.isProductDecompositionOn_of_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty`, `Toy.Lens.PLens.isProductDecompositionOn_iff_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty`

**Plain claim.** For partial lenses l₁ : PLens S A and l₂ : PLens S B and a variant V : S → Prop: if both lenses are total on V (get and put succeed there and put stays in V), each satisfies PutGet on V, they are cross-independent on V in both directions, they are jointly extensional on V, and V is inhabited whenever A × B is, then on V the two lenses present the states as A × B with l₁.put and l₂.put acting as coordinate updates; conversely, this conclusion implies all these hypotheses.

```lean
@isProductDecompositionOn_of_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty : ∀ {S : Type u_1} {A : Type u_2}
  {B : Type u_3} {V : S → Prop} {l₁ : PLens S A} {l₂ : PLens S B},
  TotalOn V l₁ →
    TotalOn V l₂ →
      PutGetOn V l₁ →
        PutGetOn V l₂ →
          PutIndepOn V l₁ l₂ →
            PutIndepOn V l₂ l₁ → JointExtOn V l₁ l₂ → (Nonempty (A × B) → ∃ s, V s) → IsProductDecompositionOn V l₁ l₂
@isProductDecompositionOn_iff_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty : ∀ {S : Type u_1} {A : Type u_2}
  {B : Type u_3} {V : S → Prop} {l₁ : PLens S A} {l₂ : PLens S B},
  IsProductDecompositionOn V l₁ l₂ ↔
    TotalOn V l₁ ∧
      TotalOn V l₂ ∧
        PutGetOn V l₁ ∧
          PutGetOn V l₂ ∧ PutIndepOn V l₁ l₂ ∧ PutIndepOn V l₂ l₁ ∧ JointExtOn V l₁ l₂ ∧ (Nonempty (A × B) → ∃ s, V s)
```

Unfolded:

```
  TotalOn V l₁ → TotalOn V l₂ → PutGetOn V l₁ → PutGetOn V l₂ → PutIndepOn V l₁ l₂ → PutIndepOn V l₂ l₁
→ JointExtOn V l₁ l₂ → (Nonempty (A × B) → ∃ s, V s)
→   (∀ s, V s → ∃ a b, l₁.get s = some a ∧ l₂.get s = some b)
  ∧ (∀ s t, V s → V t → l₁.get s = l₁.get t → l₂.get s = l₂.get t → s = t)
  ∧ (∀ a b, ∃ s, V s ∧ l₁.get s = some a ∧ l₂.get s = some b)
  ∧ (∀ s a, V s → ∃ s', l₁.put s a = some s' ∧ V s' ∧ l₁.get s' = some a ∧ l₂.get s' = l₂.get s)
  ∧ (∀ s b, V s → ∃ s', l₂.put s b = some s' ∧ V s' ∧ l₁.get s' = l₁.get s ∧ l₂.get s' = some b)
second statement: the conclusion ↔ the eight hypotheses.
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `ht₁ : TotalOn V l₁` | The first field exists and is writable on V, and writes stay in V. | tight | `Toy.Lens.PLens.absent_tight_totalOn` |
| `ht₂ : TotalOn V l₂` | Same for the second field. | tight | `Toy.Lens.PLens.absent_tight_totalOn_right` |
| `components of TotalOn (get defined; put defined; put stays in V)` | Each of the three components is needed separately. | tight | `Toy.Lens.PLens.totalOn_components_tight` |
| `h₁ : PutGetOn V l₁` | Read-back of the first field on V. | tight | `Toy.Lens.PLens.f5_tight_putGetOn_left` |
| `h₂ : PutGetOn V l₂` | Read-back of the second field on V. | tight | `Toy.Lens.PLens.f5_tight_putGetOn_right` |
| `h₁₂ : PutIndepOn V l₁ l₂` | Frame law on V. | tight | `Toy.Lens.PLens.f5_tight_putIndepOn_left` |
| `h₂₁ : PutIndepOn V l₂ l₁` | Frame law on V, other direction. | tight | `Toy.Lens.PLens.f5_tight_putIndepOn_right` |
| `hext : JointExtOn V l₁ l₂` | No hidden state within the variant. | tight | `Toy.Lens.PLens.f5_tight_jointExtOn` |
| `hV : Nonempty (A × B) → ∃ s, V s` | A base state in the variant; exactly the nonemptiness condition of the equivalence. | tight | `Toy.Lens.PLens.f5_tight_nonempty` |

**Depth: shallow.** Four of the five fields of IsProductDecompositionOn restate hypotheses (get_defined from TotalOn, injective is JointExtOn, put_fst and put_snd from TotalOn, PutGetOn and PutIndepOn); only surjectivity needs an argument, F1's argument with Option bookkeeping inside V.

**Non-vacuity witness.** The two fields of the pair variant of Shape (two nullary tags and one binary variant). (Lean: `Toy.Lens.PLens.pairFst_pairSnd_satisfy_f5_hypotheses`, `Toy.Lens.PLens.pairFst_pairSnd_isProductDecompositionOn`)

**Tier T1.** Totality of a partial lens on a subset is FGMPS07 Section 3 (Definitions 3.2-3.3); the two-lens decomposition on a variant was not found in the sources checked.

**Prior art.**

- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424 -- Section 3, Definitions 3.2-3.3 (a partial lens total on a subset C and closed on it) and footnote 3 (an everywhere-undefined putback makes the laws trivial, which is why totality is required).
- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Lens_Laws.thy `mwb_lens` (total put, partial domain via `lens_source`); Prisms.thy `wb_prism`, which also fixes behaviour outside the variant.
- [Riley18] M. Riley. Categories of Optics. arXiv:1809.00738v2, doi:10.48550/arXiv.1809.00738, 2018 (full text not consulted; Proposition 4.1.3 and Section 4.10 as cited in the literature) -- Section 4.10, affine traversals.
- [PGW17] M. Pickering, J. Gibbons, N. Wu. Profunctor Optics: Modular Data Accessors. The Art, Science, and Engineering of Programming 1(2), Article 7, 2017. doi:10.22152/programming-journal.org/2017/1/7 (full text not consulted) -- Affine traversals / optionals as the composite of a lens and a prism; their setter is total.
- [Clarke24] B. Clarke, D. Elkins, J. Gibbons, F. Loregian, B. Milewski, E. Pillmore, M. Román. Profunctor Optics, a Categorical Update. Compositionality 6(1), 2024. doi:10.32408/compositionality-6-1 (not consulted) -- Survey of profunctor optics, including affine traversals and prisms.

**Design question.** How should frame and extensionality laws for fields of one variant of a sum-typed value be scoped?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For fields that exist only on one variant of a sum-typed value, the frame and extensionality laws must be scoped to that variant; with variant-scoped laws the variant behaves as the product of its fields. Reasoning: instance of the equivalence; requires the field types to be the typed field domains (a unityped value algebra needs the field type restricted to well-typed values).

#### F5-unscoped — unscoped joint extensionality is wrong for sum types

- **Kind:** impossibility. **Tier:** T1. **Depth:** definitional. **Module:** `lean/Toy/Lens/Partial.lean`.
- **Lean:** `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields`, `Toy.Lens.PLens.eq_of_jointExt_of_get_eq_none`, `Toy.Lens.PLens.scoped_decomposition_holds_but_unscoped_jointExt_fails`

**Plain claim.** Unscoped joint extensionality for partial lenses (any two states with equal Option-valued fields are equal) identifies all states lacking both fields, so it fails as soon as two distinct states lack both fields; the intended model with two nullary tags satisfies the variant-scoped conclusion and violates it.

```lean
@not_jointExt_of_two_states_without_fields : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : PLens S A}
  {l₂ : PLens S B} {s t : S},
  s ≠ t → l₁.get s = none → l₂.get s = none → l₁.get t = none → l₂.get t = none → ¬PLens.JointExt l₁ l₂
@eq_of_jointExt_of_get_eq_none : ∀ {S : Type u_1} {A : Type u_2} {B : Type u_3} {l₁ : PLens S A} {l₂ : PLens S B},
  PLens.JointExt l₁ l₂ → ∀ {s t : S}, l₁.get s = none → l₂.get s = none → l₁.get t = none → l₂.get t = none → s = t
scoped_decomposition_holds_but_unscoped_jointExt_fails : IsProductDecompositionOn Shape.IsPair pairFst pairSnd ∧
  ¬PLens.JointExt pairFst pairSnd
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hne : s ≠ t` | Two distinct states. | tight | `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` |
| `hs₁ : l₁.get s = none` | s lacks the first field. | tight | `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` |
| `hs₂ : l₂.get s = none` | s lacks the second field. | tight | `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` |
| `ht₁ : l₁.get t = none` | t lacks the first field. | tight | `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` |
| `ht₂ : l₂.get t = none` | t lacks the second field. | tight | `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` |

**Depth: definitional.** One application of the unscoped law to none = none.

**Non-vacuity witness.** The nullary tags nil and unit of Shape. (Lean: `Toy.Lens.PLens.f5_unscoped_nonvacuity`)

**Positive control.** On a sum type with a single field-less state (Option (Bool × Bool), or nil | onlyA a | pair a b) unscoped joint extensionality holds. (Lean: `Toy.Lens.PLens.shape3_jointExt`, `Toy.Lens.PLens.optFst_optSnd_jointExt`)

**Tier T1.** Elementary observation; no source located that discusses unscoped joint extensionality for partial lenses.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Prisms.thy: sum types handled by prisms, which avoid this law.

**Design question.** Must a value-algebra extensionality law be scoped to a variant?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — An extensionality law for a value algebra with sum types must be scoped to a variant. Reasoning: the impossibility applies to every type with two distinct values lacking both fields.

#### F5-switch — scoped laws do not prevent variant switching

- **Kind:** counterexample. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Partial.lean`.
- **Lean:** `Toy.Lens.PLens.scoped_laws_admit_variant_switching_put`, `Toy.Lens.PLens.unscoped_putIndep_admits_tag_switch`, `Toy.Lens.PLens.unscoped_laws_admit_variant_switch`, `Toy.Lens.PLens.pairFstSwitch_violates_unscoped_putIndep`

**Plain claim.** The variant-scoped laws do not constrain writes outside the variant: a setter whose write on a nullary tag succeeds and produces a pair satisfies the variant-scoped conclusion; an unscoped frame law excludes that particular setter, but unscoped PutIndep in both directions still admits a write turning one nullary tag into another, and on a sum type with a one-field variant sharing a field, unscoped PutGet, GetPut, PutPut and two-way PutIndep still admit a variant-switching write.

```lean
scoped_laws_admit_variant_switching_put : IsProductDecompositionOn Shape.IsPair pairFstSwitch pairSnd ∧
  pairFstSwitch.put Shape.nil true = some (Shape.pair true false)
unscoped_putIndep_admits_tag_switch : IsProductDecompositionOn Shape.IsPair pairFstTagSwitch pairSnd ∧
  PutIndepOn (fun x => True) pairFstTagSwitch pairSnd ∧
    PutIndepOn (fun x => True) pairSnd pairFstTagSwitch ∧ pairFstTagSwitch.put Shape.nil true = some Shape.unit
unscoped_laws_admit_variant_switch : IsProductDecompositionOn ShapeShared.IsPair sharedFstSwitch sharedSnd ∧
  PutGetOn (fun x => True) sharedFstSwitch ∧
    PutGetOn (fun x => True) sharedSnd ∧
      PutIndepOn (fun x => True) sharedFstSwitch sharedSnd ∧
        PutIndepOn (fun x => True) sharedSnd sharedFstSwitch ∧
          (∀ (s : ShapeShared) (a : Bool), sharedFstSwitch.get s = some a → sharedFstSwitch.put s a = some s) ∧
            (∀ (s : ShapeShared) (a a' : Bool) (s₁ : ShapeShared),
                sharedFstSwitch.put s a = some s₁ → sharedFstSwitch.put s₁ a' = sharedFstSwitch.put s a') ∧
              sharedFstSwitch.put (ShapeShared.onlyB false) true = some (ShapeShared.pair true false)
pairFstSwitch_violates_unscoped_putIndep : ¬PutIndepOn (fun x => True) pairFstSwitch pairSnd
```

**Hypothesis ledger.** None: this result is a closed statement about concrete instances.

**Depth: shallow.** Case analysis on small inductive types.

**Tier T1.** Concrete instances constructed for this package; no source located.

**Prior art.**

- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc -- Prisms.thy `wb_prism`: build/match laws fix behaviour outside the variant.

**Design question.** Which law prevents a field setter from changing the variant of a sum-typed value?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — A separate law is needed to stop a field setter from changing the variant of a sum-typed value. Reasoning: the counterexamples satisfy the scoped (and even several unscoped) laws while switching variants.

#### F6 — classification of very well-behaved puts for a fixed getter

- **Kind:** characterization. **Tier:** T1. **Depth:** shallow. **Module:** `lean/Toy/Lens/Classification.lean`.
- **Lean:** `Toy.Lens.coherent_fiberMaps_correspond_veryWellBehaved_puts`, `Toy.Lens.getPut_iff_ofPut_map_self_and_putPut_iff_ofPut_map_comp`

**Plain claim.** Fix a getter get : S → A, and call a family of maps between the fibres of get (one map for every ordered pair of views) coherent if each fibre's map to itself is the identity and maps compose. Then the construction toPut (move a state to the fibre of the written view) sends every coherent family to a very well-behaved put for get, the construction ofPut (x ↦ put x a') sends every very well-behaved put to a coherent family, and ofPut undoes toPut on every family (toPut undoes ofPut by definition, Toy.Lens.toPut_ofPut), so coherent families and very well-behaved puts correspond bijectively. Law by law, for a put with PutGet, GetPut holds iff its fibre maps satisfy the identity law and PutPut holds iff they compose. (Each map of a coherent family is a bijection: the proved lemma Toy.Lens.FiberMaps.Coherent.leftInverse.)

`coherent_fiberMaps_correspond_veryWellBehaved_puts` is printed with `pp.proofs true` in addition, which shows the proof arguments of `ofPut` in place of `⋯`:

```lean
@coherent_fiberMaps_correspond_veryWellBehaved_puts : ∀ {S : Type u_1} {A : Type u_2} (get : S → A),
  (∀ (φ : FiberMaps get), FiberMaps.Coherent φ → VeryWellBehaved { get := get, put := FiberMaps.toPut φ }) ∧
    (∀ (put : S → A → S) (h : VeryWellBehaved { get := get, put := put }),
        FiberMaps.Coherent (ofPut get put h.right.left)) ∧
      ∀ (φ : FiberMaps get), ofPut get (FiberMaps.toPut φ) (toPut_putGet φ) = φ
@getPut_iff_ofPut_map_self_and_putPut_iff_ofPut_map_comp : ∀ {S : Type u_1} {A : Type u_2} (get : S → A)
  (put : S → A → S) (h : PutGet { get := get, put := put }),
  (GetPut { get := get, put := put } ↔ ∀ (a : A) (x : GetFiber get a), ofPut get put h a a x = x) ∧
    (PutPut { get := get, put := put } ↔
      ∀ (a a' a'' : A) (x : GetFiber get a), ofPut get put h a' a'' (ofPut get put h a a' x) = ofPut get put h a a'' x)
```

Unfolded:

```
for get : S → A, writing Fib a = {s // get s = a}, φ : (a a' : A) → Fib a → Fib a',
toPut φ s a = (φ (get s) a ⟨s, rfl⟩).1 and ofPut put h a a' x = ⟨put x.1 a', h x.1 a'⟩:

  (∀ φ, (∀ a x, φ a a x = x) → (∀ a a' a'' x, φ a' a'' (φ a a' x) = φ a a'' x)
        → VeryWellBehaved ⟨get, toPut φ⟩)
∧ (∀ put (h : VeryWellBehaved ⟨get, put⟩), ofPut put h.2.1 is coherent)
∧ (∀ φ, ofPut (toPut φ) _ = φ)                    [and toPut (ofPut put h) = put by definition]
law by law, for put with PutGet:
  GetPut ⟨get, put⟩ ↔ ∀ a x, ⟨put x.1 a, _⟩ = x
  PutPut ⟨get, put⟩ ↔ ∀ a a' a'' x, put (put x.1 a') a'' = put x.1 a''   (as fibre elements)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `get : S → A (arbitrary)` | No inhabitedness or surjectivity assumption; for empty S or non-surjective get see the non-claims. | harmless | — |
| `h : PutGet (Lens.mk get put) (law-by-law statement)` | Needed to form ofPut (the maps must land in the fibres); a put without PutGet is not of the form toPut φ (Toy.Lens.toPut_putGet). | harmless | — |

**Depth: shallow.** Both directions are computations; the only subtle step is transporting a fibre element along an equality of views (get (put s a) = a) inside the dependent family.

**Non-vacuity witness.** For the first projection on Bool × Bool, the fibre maps of fst (and of the state-twisting lens) are coherent. (Lean: `Toy.Lens.f6_nonvacuity`, `Toy.Lens.ofPut_twist_coherent`)

**Tier T1.** Known in other formalisms: JRW10 Proposition 9 (a very well behaved lens with getter g is exactly an algebra structure on g for a monad on Set/V, so for a fixed getter the puts are those algebra structures); Clarke20 Example 25 (a state-based lens is an internal lens between codiscrete categories whose Put part is a discrete opfibration, with GetPut and PutPut as the identity and composition laws of a functor); and CDV21 (a higher lens is a getter together with a proof that its family of fibres is coherently constant; higher lenses are equivalent to traditional lenses for types satisfying UIP). In categorical terms a coherent family of fibre maps is a functor from the codiscrete category on A to Set, whose category of elements is a discrete opfibration over that codiscrete category with object set S. The explicit set-level form with coherent fibre maps, the exposed constructions toPut/ofPut and the law-by-law correspondence, mechanised, was not found stated in the sources consulted.

**Prior art.**

- [JRW10] M. Johnson, R. D. Rosebrugh, R. J. Wood. Algebras and Update Strategies. J. Univers. Comput. Sci. 16(5):729-748, 2010. doi:10.3217/jucs-016-05-0729 -- Proposition 9: a very well behaved lens (S, V, g, p) is exactly the data for an algebra (g, p) for the monad ΔΣ on set/V.
- [CDV21] P. Capriotti, N. A. Danielsson, A. Vezzosi. Higher Lenses. 36th ACM/IEEE Symposium on Logic in Computer Science (LICS 2021), pp. 1-13. doi:10.1109/LICS52264.2021.9470613; Agda development https://github.com/nad/dependent-lenses commit c09739a91f522074c9b3508e56252013219f359c (abstract and src/Lens/Non-dependent/Traditional.agda read; the paper's own lemma numbering not checked) -- Abstract: a higher lens can equivalently be formulated as a getter function and a proof that its family of fibres is coherently constant; higher lenses are equivalent to traditional ones for types that satisfy uniqueness of identity proofs.
- [Clarke20] B. Clarke. Internal lenses as functors and cofunctors. In: J. Baez, B. Coecke (eds.), Applied Category Theory 2019, EPTCS 323, pp. 183-195, 2020. doi:10.4204/EPTCS.323.13, arXiv:2009.06835v1 (full text read) -- Section 4, Corollary 20 and Example 25: a state-based lens with Get f : A -> B and Put p induces an internal lens between the codiscrete categories on A and B, whose Put part is a discrete opfibration over the codiscrete category on B; PutGet is the statement that lifts are genuine lifts, and GetPut and PutPut hold because the induced functor respects identities and composition. This is the categorical form of the law-by-law statement of F6.
- [JRW12] M. Johnson, R. D. Rosebrugh, R. J. Wood. Lenses, fibrations and universal translations. Math. Struct. Comput. Sci. 22(1):25-42, 2012. doi:10.1017/S0960129511000442 (abstract read; full text not consulted) -- c-lenses, lenses between categories, correspond to Grothendieck opfibrations; for codiscrete categories these reduce to state-based lenses.
- [DXC11] Z. Diskin, Y. Xiong, K. Czarnecki. From State- to Delta-Based Bidirectional Model Transformations: the Asymmetric Case. Journal of Object Technology 10, pp. 6:1-25, 2011. doi:10.5381/jot.2011.10.1.a6 (abstract read; full text not consulted) -- delta lenses, in which model spaces are categories and updates are arrows, and their relationship with ordinary state-based lenses.

**Design question.** For a fixed field getter, what exactly is the freedom in choosing a lawful setter?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For a given field getter, the freedom in choosing a lawful setter is exactly the choice of a coherent family of bijections between the sets of values with a given field value. Reasoning: direct instance; it explains why the single-lens laws cannot fix the setter.

#### F6-count — base-fibre form and count (m!)^(k-1)

- **Kind:** theorem. **Tier:** T1. **Depth:** substantive. **Module:** `lean/Toy/Lens/Classification.lean`.
- **Lean:** `Toy.Lens.veryWellBehaved_puts_equiv_baseFiber_bijections`, `Toy.Lens.card_veryWellBehaved_puts_of_card_views_card_fibers`

**Plain claim.** Fix a getter get and a base view a₀: very well-behaved puts for get correspond bijectively to families of bijections from the fibre over a₀ to each other fibre, via put ↦ (x ↦ put x a). Consequently, if the view type has exactly k elements and every fibre of get has exactly m elements, the very well-behaved puts are in bijection with Fin (k − 1) → Equiv (Fin m) (Fin m) and there are exactly (m!)^(k − 1) of them (with truncated subtraction, also correct for k = 0).

`veryWellBehaved_puts_equiv_baseFiber_bijections` is printed with `pp.funBinderTypes true` in addition, which shows the type of the `∃`-bound `e`:

```lean
@veryWellBehaved_puts_equiv_baseFiber_bijections : ∀ {S : Type u_1} {A : Type u_2} (get : S → A) (a₀ : A),
  ∃ (e :
    Equiv { put : S → A → S // VeryWellBehaved { get := get, put := put } }
      ((a : { a : A // a ≠ a₀ }) → Equiv (GetFiber get a₀) (GetFiber get a.val))),
    ∀ (p : { put : S → A → S // VeryWellBehaved { get := get, put := put } }) (a : { a : A // a ≠ a₀ })
      (x : GetFiber get a₀), ((e.toFun p a).toFun x).val = p.val x.val a.val
@card_veryWellBehaved_puts_of_card_views_card_fibers : ∀ {S : Type u_1} {A : Type u_2} (get : S → A) (k m : Nat),
  Nonempty (Equiv A (Fin k)) →
    (∀ (a : A), Nonempty (Equiv (GetFiber get a) (Fin m))) →
      Nonempty (Equiv { put // VeryWellBehaved { get := get, put := put } } (Fin (k - 1) → Equiv (Fin m) (Fin m))) ∧
        Nonempty (Equiv { put // VeryWellBehaved { get := get, put := put } } (Fin (factorial m ^ (k - 1))))
```

Unfolded:

```
base-fibre form, for a₀ : A:
  ∃ e : {put // VeryWellBehaved ⟨get, put⟩} ≃ ((a : {a // a ≠ a₀}) → Fib a₀ ≃ Fib a),
      ∀ p a x, ((e p) a x).1 = p.1 x.1 a
counting form:
  A ≃ Fin k → (∀ a, Fib a ≃ Fin m) →
      {put // VeryWellBehaved ⟨get, put⟩} ≃ (Fin (k - 1) → Fin m ≃ Fin m)
    ∧ {put // VeryWellBehaved ⟨get, put⟩} ≃ Fin (m! ^ (k - 1))      (as Nonempty of local Equivs)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `a₀ : A (base-fibre form)` | Base view; the base-fibre form is vacuous for empty A, which the counting form covers with k = 0. | harmless | — |
| `hA : Nonempty (Equiv A (Fin k))` | The number of views. | tight | `Toy.Lens.card_tight_views` |
| `hF : ∀ a, Nonempty (Equiv (GetFiber get a) (Fin m))` | Uniform fibre size; with non-uniform fibres there is no very well-behaved put. | tight | `Toy.Lens.card_tight_uniform_fibers` |

**Depth: substantive.** Base-fibre form (shallow): from a coherent family take the maps out of the fibre over a₀; conversely compose the bijections through the base fibre. Counting form (substantive without a library of finite cardinalities): transport along the given bijections and build an explicit bijection between the self-bijections of Fin m and Fin m!.

**Non-vacuity witness.** First projection on Bool × Bool: k = 2, m = 2, base view false; there are exactly 2 = 2!^1 very well-behaved puts (fst and twist). (Lean: `Toy.Lens.f6_count_nonvacuity`, `Toy.Lens.veryWellBehaved_puts_getFst_eq_fst_or_twist`)

**Tier T1.** Follows from F6 by elementary counting; no source located that states the count.

**Prior art.**

- [JRW10] M. Johnson, R. D. Rosebrugh, R. J. Wood. Algebras and Update Strategies. J. Univers. Comput. Sci. 16(5):729-748, 2010. doi:10.3217/jucs-016-05-0729 -- Theorem 12 and Corollary 13 (for a non-empty view set, very well behaved lenses are product projections), from which the count follows.

**Design question.** How much freedom does a lawful setter have for a given getter, quantitatively?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For finite value spaces with uniform fibres the number of lawful setters for a getter is (m!)^(k-1), so for k ≥ 2 and m ≥ 2 the single-lens laws never determine the setter. Reasoning: direct instance.

#### F6-unique — a frame law against a complement view pins down the put

- **Kind:** theorem. **Tier:** T0. **Depth:** shallow. **Module:** `lean/Toy/Lens/Classification.lean`.
- **Lean:** `Toy.Lens.existsUnique_put_putGet_putIndep_of_jointExt_surjective`

**Plain claim.** Fix get : S → A and a second lens m : Lens S C whose view together with get determines the state and such that every pair of values is realised. Then there is exactly one put for get that satisfies PutGet and leaves the m-view unchanged (the frame law PutIndep (Lens.mk get put) m), and it is very well-behaved.

```lean
@existsUnique_put_putGet_putIndep_of_jointExt_surjective : ∀ {S : Type u_1} {A : Type u_2} {C : Type u_3} (get : S → A)
  (m : Lens S C),
  (∀ (s t : S), get s = get t → m.get s = m.get t → s = t) →
    (∀ (a : A) (c : C), ∃ s, get s = a ∧ m.get s = c) →
      (∃ put, PutGet { get := get, put := put } ∧ PutIndep { get := get, put := put } m) ∧
        (∀ (put put' : S → A → S),
            PutGet { get := get, put := put } →
              PutIndep { get := get, put := put } m →
                PutGet { get := get, put := put' } → PutIndep { get := get, put := put' } m → put = put') ∧
          ∀ (put : S → A → S),
            PutGet { get := get, put := put } →
              PutIndep { get := get, put := put } m → VeryWellBehaved { get := get, put := put }
```

Unfolded:

```
for get : S → A and m : Lens S C with
  hext : ∀ s t, get s = get t → m.get s = m.get t → s = t   and   hsurj : ∀ a c, ∃ s, get s = a ∧ m.get s = c:
    (∃ put, (∀ s a, get (put s a) = a) ∧ (∀ s a, m.get (put s a) = m.get s))
  ∧ (any two such puts are equal)
  ∧ (any such put is very well-behaved)
```

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness | counterexample (other hypotheses hold, conclusion fails) |
| --- | --- | --- | --- |
| `hext : ∀ s t, get s = get t → m.get s = m.get t → s = t` | The complement view and get together determine the state. Used for uniqueness (second conjunct) and for very-well-behavedness (third conjunct); dropping it breaks both: with a one-point complement view, fst and twist both satisfy PutGet and the frame law, and so do the dirty-flag setter (not PutPut) and the sibling-resetting setter (not GetPut). | tight | `Toy.Lens.existsUnique_put_tight_jointExt`, `Toy.Lens.existsUnique_put_drop_jointExt_admits_unlawful_puts` |
| `hsurj : ∀ a c, ∃ s, get s = a ∧ m.get s = c` | Every pair of values is realised; a sufficient condition used for existence (first conjunct). It is not necessary for the conclusion: see the non-claims. | tight | `Toy.Lens.existsUnique_put_tight_surjective` |
| `m.put` | Not used: only the getter of m matters. | harmless | — |

**Depth: shallow.** Existence: put s a is the state realising (a, m.get s) (choice). Uniqueness: two such states agree on both views. Very well-behaved: F1-laws' derived laws.

**Non-vacuity witness.** The first projection with complement view snd on Bool × Bool. (Lean: `Toy.Lens.f6_unique_nonvacuity`)

**Tier T0.** Known: an update translation under a constant complement is unique once the complement is fixed (BS81, as recalled in FGMPS07 Section 10). Restated as a frame law against a complement view.

**Prior art.**

- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424 -- Section 10 (Foundations of View Update): when a complement is fixed, there exists at most one update of the database that reflects a given update on the view while leaving the complement unmodified. That is the uniqueness half; existence under hsurj and very-well-behavedness are not stated there.
- [BS81] F. Bancilhon, N. Spyratos. Update semantics of relational views. ACM Trans. Database Syst. 6(4):557-575, 1981. doi:10.1145/319628.319634 (full text not consulted) -- Update translation under a constant complement.

**Design question.** Which law in a field interface pins down the setter once the getter is fixed?

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — The law that pins down "setting one field changes that field and nothing else" is a frame law against an explicitly named complement view (for a record, the tuple of the other fields): PutGet plus "the complement view is unchanged" determines the setter uniquely and makes it very well-behaved, provided the field and the complement together determine the value and every combination occurs. Reasoning: direct instance; which setter is singled out depends on the named complement (twist_putIndep_xorView_complement).

## Boundaries

### Non-claims I: lawful but unintended instances exhibited by the package

These proved instances satisfy laws that are often taken to mean "the setter changes its field and nothing else", yet are not the intended field update. Each is a reason why a weaker law set or a weaker conclusion was rejected.

- **The state-twisting setter.** `twist : Lens (Bool × Bool) Bool` reads the first field, and writing `a` into the state `(a', b)` gives `(a, b xor (a' xor a))`: it flips the second field whenever it changes the first. It is very well-behaved (`twist_veryWellBehaved`), has a constant complement (`twist_hasConstantComplement`, complement `a xor b`), has coherent fibre maps (`ofPut_twist_coherent`), has the same getter as `fst` (`fst_twist_two_veryWellBehaved_puts`; these are the only two very well-behaved puts for that getter, `veryWellBehaved_puts_getFst_eq_fst_or_twist`), and it satisfies PutGet and the frame law against the XOR view `a xor b`, which together with the first field determines the state, while `fst.put` violates that frame law (`twist_putIndep_xorView_complement`); since every pair of values of the first field and the XOR view occurs, F6-unique makes `twist.put` the one setter that this frame law singles out (derived from the two theorems). Parking at base view `false` through F3-fiber still flips the second bit (`twist_put_park`).
- **A second view that is not a sibling field.** `xorView` (view `a xor b`) together with `fst` has a bijective pairing map, yet the pair is not a product decomposition, because `fst.put` changes the XOR view (`xorView_pairGet_bijective_but_not_decomposition`, `xorView_tight_putIndep_left`). Both lenses are very well-behaved and `PutIndep xorView fst` holds, so the hypotheses of F1-inverse hold (`f1_inverse_nonvacuity_bool`).
- **A bare bijection with hidden state.** `Nat × Nat × Bool` is in bijection with `Nat × Nat` (`ghost_admits_unrelated_bijection`) although the two `Nat` fields do not determine the state; and on `Bool × Bool × Bool` the lenses `ghostFst` and `ghostTwistSnd` are very well-behaved and cross-independent in both directions but do not commute (`derived_putComm_tight`, third instance).
- **Setters that store the value but break a classical law.** Against the one-point view `unitLensB`, the dirty-flag setter (well-behaved, not PutPut) and the sibling-resetting setter (PutGet and PutPut, not GetPut) satisfy PutGet and the frame law (`existsUnique_put_drop_jointExt_admits_unlawful_puts`). Paired with `snd`, both satisfy all hypotheses of F1-inverse (`f1_inverse_hypotheses_do_not_imply_laws`).
- **Variant-switching setters on sum types.** A setter that turns a nullary tag into a pair satisfies the variant-scoped conclusion (`scoped_laws_admit_variant_switching_put`); a setter that turns one nullary tag into another satisfies unscoped PutIndep in both directions (`unscoped_putIndep_admits_tag_switch`); and with a second variant sharing a field, unscoped PutGet, GetPut, PutPut and two-way PutIndep admit a variant switch (`unscoped_laws_admit_variant_switch`).
- **Empty types.** On the empty state type every lens is very well-behaved and `get` need not be surjective (`emptyState_veryWellBehaved_not_surjective`); for the lens on the empty state type with the empty view type, every `C : Type` is a constant complement (`emptyView_hasConstantComplement_any`); an empty ghost gives a ghost complement without a product decomposition (`emptyGhost_hasGhostComplement_not_isProductDecomposition`); F6-count counts the unique empty put when `m = 0` (`card_veryWellBehaved_puts_empty_state_two_views`).
- **Infinite families.** The coordinate lenses on eventually-false Boolean sequences are very well-behaved, pairwise commuting and jointly extensional, yet the tuple-of-views map is not surjective (`evCoord_tight_finite_index`) and there is no bijection `EvFalse ≃ ((i : Nat) → Bool) × G` whose first component is the tuple of views (`evCoord_veryWellBehaved_putComm_no_pi_complement`).
- **Aliasing.** Two copies of the identity lens on `Bool` satisfy PutGet and JointExt (`aliasing_fails_putIndep_both_directions`); only PutIndep, in both directions at once, excludes them.

### Non-claims II: by result

**F1.**

- The six hypotheses are sufficient (first Lean statement), jointly equivalent to the conclusion (second Lean statement) and irredundant (each has a counterexample in canonical form). The common stronger hypothesis `Nonempty S` implies `hS` but is not necessary: when A × B is empty the conclusion can hold on an empty state type (Toy.Lens.emptyView_isProductDecomposition_without_nonempty).
- Does not constructively build an `Equiv S (A × B)` in `Type`: `hS` and `IsProductDecomposition l₁ l₂` live in `Prop`, so obtaining a computable inverse requires a concrete base state `s₀ : S` (see F1-inverse) or `Classical.choice`.
- Does not apply to a proper subset of fields of a record with three or more fields (or hidden metadata/padding): `JointExt` fails whenever any unprojected state component exists; use F3-pair (with `VeryWellBehaved` and `PutComm`) or F2 over all fields instead.
- Dropping `PutGet l₁`, `PutGet l₂`, `PutIndep l₁ l₂` or `PutIndep l₂ l₁` breaks the coordinate-update (`Intertwines`) part of `IsProductDecomposition`, not necessarily the bijectivity of `pairGet`: for ignorePut/snd, fst/ignorePutSnd and snd/twist (Toy.Lens.pairGet_bijective_in_inverse_witnesses) and for fst/xorView (Toy.Lens.xorView_pairGet_bijective_but_not_decomposition), `pairGet` is still a bijection.
- The 'puts are coordinate updates' half of the conclusion carries no information beyond PutGet and PutIndep; see the depth note.
- Attractive but inadequate weakening of the conclusion: 'some bijection S ≃ A × B exists'. A record with a ghost component admits such a bijection (Toy.Lens.ghost_admits_unrelated_bijection); the specific map must appear in the statement. Any map whose components are the two getters is `pairGet` (Toy.Lens.eq_pairGet_of_get_eq; each of its two hypotheses is needed: Toy.Lens.eq_pairGet_tight_left, Toy.Lens.eq_pairGet_tight_right).
- Attractive but false variant of the hypotheses: both lenses very well-behaved, jointly extensional, and independent in one direction only (Toy.Lens.xorView_tight_putIndep_left).
- Says nothing about partial lenses or sum types (see F5), about more than two fields (see F2), or about type-changing lenses.
- Proved only over pure total functions and Lean propositional equality `=`; it does not by itself establish properties of a real programming-language value algebra with observational equality, padding bytes, provenance, aliasing, panics, or side effects (any such transfer requires a separate modeling bridge).

**F1-inverse.**

- Does not conclude that the puts are coordinate updates: for fst/xorView the hypotheses hold but fst.put changes the XOR view (Toy.Lens.xorView_tight_putIndep_left).
- Does not imply that `l₁` satisfies `GetPut` or `PutPut`, or commutes with `l₂`: the pair `(resetSibling, snd)` satisfies all hypotheses (and `pairPut` is a two-sided inverse of `pairGet` there), yet `resetSibling` violates `GetPut` and does not commute with `snd`; the pair `(dirtyFlag, snd)` satisfies all hypotheses and `dirtyFlag` violates `PutPut` (Toy.Lens.f1_inverse_hypotheses_do_not_imply_laws).
- The tightness witnesses for `PutGet l₁`, `PutGet l₂` and `PutIndep l₂ l₁` show only that the specific formula `pairPut` fails to be an inverse of `pairGet`, not that `pairGet` ceases to be a bijection: in ignorePut/snd, fst/ignorePutSnd and snd/twist, `pairGet` remains a bijection (Toy.Lens.pairGet_bijective_in_inverse_witnesses).
- The order of the two writes matters when only one direction of independence is assumed: pairPut writes through l₁ first and then through l₂, the reverse of the order used by the AFP Optics sum lens `X +_L Y` (which writes Y first).
- Proved only over pure total functions and Lean propositional equality `=`; it does not by itself establish properties of a real programming-language value algebra with observational equality, padding bytes, provenance, aliasing, panics, or side effects (any such transfer requires a separate modeling bridge).

**F1-laws.**

- Under the weaker three-hypothesis component lemmas (`PutGet l₁`, `PutIndep l₁ l₂`, `JointExt l₁ l₂`), nothing is concluded about `l₂`'s laws or about `PutComm l₁ l₂`.
- Does not allow dropping `GetPut`, `PutPut`, or `PutComm` from a multi-field value-algebra interface unless `FamJointExt` holds over all fields together; for any two fields of a ≥ 3-field struct, the remaining fields act as a ghost component (Toy.Lens.derived_putComm_tight, third instance).
- Joint extensionality is essential: without it, two very well-behaved lenses that are cross-independent in both directions need not commute (Toy.Lens.derived_putComm_tight, third instance).
- Proved only over pure total functions and Lean propositional equality `=`; it does not by itself establish properties of a real programming-language value algebra with observational equality, padding bytes, provenance, aliasing, panics, or side effects (any such transfer requires a separate modeling bridge).

**F2.**

- Does not cover dependent records (telescopes) where the type of one field depends on the *value* of another field: `A : ι → Type v` depends only on the fixed index `i : ι`.
- Does not cover dynamically-keyed finite maps or heaps whose set of present keys varies from state to state: the finite index type `ι` is fixed globally across all states `S`.
- Does not constructively produce an `Equiv S ((i : ι) → A i)` in `Type`: the nonemptiness hypothesis and the conclusion are propositions.
- Does not claim that `Nonempty S` is necessary: when `ι` is nonempty and some `A i` is empty, the product is empty and the conclusion can hold on an empty `S`; the theorem therefore uses the conditional hypothesis `hS`.
- False for infinite index types: the coordinate lenses on eventually-false Boolean sequences satisfy every other hypothesis but the tuple-of-views map is not surjective (Toy.Lens.evCoord_tight_finite_index). For infinite ι only injectivity and the coordinate-update equations survive.
- Proved only over pure total functions and Lean propositional equality `=`; it does not by itself establish properties of a real programming-language value algebra with observational equality, padding bytes, provenance, aliasing, panics, or side effects (any such transfer requires a separate modeling bridge).

**F2-laws.**

- The laws at indices other than those concerned are not used; the lemmas do not say anything about the other lenses.
- Joint extensionality over the whole family is used; for a sub-family of fields it generally fails and commuting puts must then be assumed (see F3-pair).

**F3.**

- Does not imply that `l.get` is surjective when `S` is empty (with nonempty `A`, `VeryWellBehaved l` holds vacuously while `l.get : Empty → A` is not surjective; Toy.Lens.emptyState_veryWellBehaved_not_surjective).
- The complement `C` is non-unique in two distinct senses: when `A` is inhabited, `C` is unique up to bijection (`C ≃ Fiber l a₀`) but the embedding/projection is not unique (e.g., `twist` splits with complement `a xor b` rather than `b`); when `A` is empty (hence `S` is empty), `C` is not even unique up to bijection (every `C : Type u` is a constant complement; Toy.Lens.emptyView_hasConstantComplement_any).
- The backward direction of `HasConstantComplement` requires `C : Type u` (the universe of `S`); for a complement in an arbitrary universe `Type x`, use `veryWellBehaved_of_injective_intertwines_fst` (F3-sharp).
- By the backward direction, any lens failing `GetPut`, `PutGet`, or `PutPut` has no constant complement at all; F3 gives no weaker decomposition for well-behaved lenses that fail `PutPut`.
- Does not say that a very well-behaved put leaves a *given* sibling field alone: the complement is some type, not a prescribed field (Toy.Lens.twist_hasConstantComplement).
- Says nothing about weaker put-put laws (JR12).

**F3-sharp.**

- Does not require f to be surjective, and says nothing about whether f is.
- Does not identify the complement with a sibling field (Toy.Lens.twist_hasConstantComplement).

**F3-fiber.**

- The bijection is given by explicit formulas but is stated inside an existential in `Prop`: the equations determine it uniquely (Toy.Lens.fiberEquiv_eq_of_equations) and its inverse is the explicit map Toy.Lens.fiberFrom, but a `Type`-level `Equiv` is not extracted without proving the theorem.
- Choosing a base view `a₀ : A` makes the complement a concrete subtype of `S`, not necessarily the intended sibling field: for `twist` with `a₀ = false`, `s ↦ twist.put s false` still flips the second bit whenever the first bit is `true` (Toy.Lens.twist_put_park).
- The theorem holds vacuously when `A` is empty (taking `a₀ : A` as an argument), but cannot be instantiated to exhibit a complement without a term of `A`.

**F3-pair.**

- Does NOT generalize to an infinite family of pairwise-commuting very well-behaved lenses: `evCoord` on `EvFalse` satisfies `VeryWellBehaved` for every `i : Nat` and pairwise `PutComm`, yet admits no bijection `EvFalse ≃ ((i : Nat) → Bool) × G` (Toy.Lens.evCoord_veryWellBehaved_putComm_no_pi_complement).
- F1 corresponds specifically to a one-point ghost (`G ≃ PUnit`), not an arbitrary 'trivial' or empty ghost: when `S = Empty` and `A × B` is inhabited, `HasGhostComplement` holds with an empty `G` while `IsProductDecomposition` fails (Toy.Lens.emptyGhost_hasGhostComplement_not_isProductDecomposition).
- As in F3, the ghost complement `G` need not coincide with the syntactic remaining fields of a record (both `l₁` and `l₂` may jointly reparameterize hidden state consistently), and `G` is restricted to `Type u` (the universe of `S`).
- Commuting puts cannot be replaced by cross-independence in both directions: two very well-behaved lenses can be cross-independent both ways without commuting (Toy.Lens.derived_putComm_tight, third instance).

**F4-derived-putComm.**

- With joint extensionality, commuting puts does follow (F1-laws).
- Says nothing about lenses that are not cross-independent; the instances are on Bool-valued records only.

**F4-aliasing.**

- Escape hatch 1 (subsingleton view): fails if `A` has at most one element (`unitLensB : Lens (Bool × Bool) Unit` satisfies both `PutGet` and `PutIndep unitLensB unitLensB`).
- Escape hatch 2 (empty state): fails if `S` is empty (the lens on `Empty` with view `Bool` satisfies `PutGet` and `PutIndep` with itself even though `Bool` has two elements).
- Escape hatch 3 (drop `PutGet`): fails without `PutGet` (`ignorePut` on `Bool × Bool` satisfies `PutIndep ignorePut ignorePut` even though `Bool` has two distinct values and `Bool × Bool` is nonempty).
- Aliasing is not a single-hypothesis tightness witness for F1: it drops both directions of PutIndep together (Toy.Lens.aliasing_fails_putIndep_both_directions).

**F4-bare-bijection.**

- Does not say anything about finite types, where a bijection S ≃ A × B forces |S| = |A| · |B| but still does not relate to the getters.
- The remedy is to name the pairing map in the conclusion (F1).

**F4-F2-finite.**

- Injectivity of the tuple-of-views map and the coordinate-update equations do survive for infinite index types.
- Says nothing about other infinite families; it is one instance.

**F5.**

- Says nothing constraining `l₁.get` or `l₂.get` outside `V`: either getter may return `some _` on states not satisfying `V` (for example, on a second variant that shares the same field name, or arbitrarily on nullary tags).
- Does not apply directly to a unityped value algebra `getField : Val → Option Val`, `setField : Val → Val → Option Val` with `A = B = Val`: `TotalOn V l` requires `l.put s a` to succeed for EVERY `a : A`, whereas a typed record field rejects ill-typed `Val` inputs. Applying F5 to a unityped value algebra requires restricting `A` and `B` to typed subtypes `{v : Val // HasType v τ}` or additionally scoping `TotalOn` to valid field values.
- Does not assume `V` equals `dom(l₁.get) ∩ dom(l₂.get)` — indeed, when two distinct variants share the same field names, `JointExtOn` fails on `dom(l₁.get) ∩ dom(l₂.get)` and holds only on each individual variant predicate `V` (Toy.Lens.PLens.twin_jointExtOn_fails_on_union).
- Says nothing about writes outside V; such writes may switch the variant (F5-switch).
- Unscoped joint extensionality must not replace JointExtOn (F5-unscoped).
- The variant-scoped GetPut, PutPut and commuting puts follow from these hypotheses without the nonemptiness condition (Toy.Lens.PLens.getPutOn_of_totalOn_putGetOn_putIndepOn_jointExtOn, putPutOn_of_..., putCommOn_of_...); they are proved supporting lemmas, not part of this statement.
- With V the whole state type and lenses that never fail, F5 specialises to F1 (Toy.Lens.PLens.isProductDecompositionOn_toPLens_iff and companions).
- Proved only over pure total functions and Lean propositional equality `=`; it does not by itself establish properties of a real programming-language value algebra with observational equality, padding bytes, provenance, aliasing, panics, or side effects (any such transfer requires a separate modeling bridge).

**F5-unscoped.**

- Escape hatch 1 (at most one field-less state): unscoped `JointExt` holds on `Option (Bool × Bool)` (`optFst_optSnd_jointExt`), and even holds on a three-variant sum type `| nil | onlyA (a : Bool) | pair (a b : Bool)` where `l₁` is defined on `onlyA` and `pair`, `l₂` on `pair`, and `nil` is the unique state lacking both fields (`shape3_jointExt`).
- Escape hatch 2 (drop any single `get = none` hypothesis): if `s` and `t` differ on either `l₁.get` or `l₂.get` (e.g., `(some a, none)` vs. `(none, none)`), unscoped `JointExt` is not refuted (`not_jointExt_of_two_states_without_fields_tight`).
- Conversely, failure does NOT require two nullary tags or ≥ 3 variants: even a two-variant sum type `| other (c : Bool) | pair (a b : Bool)` violates unscoped `JointExt` because `other false ≠ other true` are two distinct states lacking both fields (`otherFst_otherSnd_not_jointExt`).
- Escape hatch 3 (scope to variant): replacing unscoped `JointExt` by `JointExtOn V` restores satisfiability on arbitrary multi-variant sum types (`scoped_decomposition_holds_but_unscoped_jointExt_fails`).
- A law set containing unscoped joint extensionality passes tests on option-like types and fails on the first sum type with two field-less states.

**F5-switch.**

- An unscoped frame law `PutIndepOn (fun _ => True) l₁ l₂` does NOT exclude all variant-switching puts, even for a variant with two fields: a setter with `put .nil _ = some .unit` (switching between two states both lacking `l₂`) satisfies `PutIndepOn (fun _ => True) l₁ l₂` (`unscoped_putIndep_admits_tag_switch`), and on a sum type with a second variant carrying a field shared with the record variant, a setter that switches variants satisfies unscoped `PutGetOn`, `PutIndepOn` in both directions, `GetPut` and `PutPut` (`unscoped_laws_admit_variant_switch`).
- To rule out all writes outside `V` uniformly (including for 1-field variants and multi-variant sum types), require `∀ s a, ¬ V s → l.put s a = none` (or `l.put s a = some s' → V s`) directly; this package does not state or prove a theorem about that law.

**F6.**

- Does not single out an intended put: for a fixed getter there are in general many very well-behaved puts (two for the first projection on Bool × Bool: Toy.Lens.fst_twist_two_veryWellBehaved_puts, Toy.Lens.veryWellBehaved_puts_getFst_eq_fst_or_twist); see F6-unique for the extra law that does.
- Empty fibres: if one fibre is empty and another is not, there is no family of fibre maps and hence no very well-behaved put (Toy.Lens.fiberMaps_empty_of_empty_fiber); in particular, on an inhabited state type a put with PutGet forces get to be surjective (Toy.Lens.surjective_of_putGet_of_nonempty). On an empty state type there is exactly one put and it is very well-behaved, whatever A is (Toy.Lens.veryWellBehaved_put_unique_of_isEmpty).
- Does not by itself say when a very well-behaved put exists; for an inhabited view type the base-fibre form (F6-count) shows that one exists exactly when every fibre is in bijection with the fibre over a base view.
- The correspondence is between puts for one fixed getter; it does not classify lenses up to isomorphism of the state type.
- toPut is also a bijection from all families of fibre maps (coherent or not) onto puts satisfying PutGet (third conjunct together with Toy.Lens.toPut_ofPut and Toy.Lens.toPut_putGet).
- The two coherence conditions are independent and each is needed for very-well-behavedness: the fibre maps of the sibling-resetting setter satisfy map_comp (the setter satisfies PutPut, Toy.Lens.resetSibling_putPut) but not map_self (Toy.Lens.ofPut_resetSibling_not_coherent; the setter violates GetPut), and the fibre maps of the dirty-flag setter satisfy map_self (Toy.Lens.dirtyFlag_getPut) but not map_comp (Toy.Lens.ofPut_dirtyFlag_not_coherent; the induced put is not very well-behaved, Toy.Lens.toPut_ofPut_dirtyFlag_not_veryWellBehaved).
- The categorical reading (coherent families as functors from the codiscrete category on A to Set, very well-behaved lenses as discrete opfibrations or delta lenses over codiscrete categories) is a correspondence with the literature, not a Lean statement of this package; no category theory is formalised here.

**F6-count.**

- Counts puts for one fixed getter, not lenses up to isomorphism.
- Only for finite view types and finite, uniform fibres; for non-uniform fibres the count is 0 (Toy.Lens.card_tight_uniform_fibers).
- Says nothing about which of the (m!)^(k − 1) puts is intended; see F6-unique.
- Edge case m = 0, k >= 1: for the empty state type with a nonempty finite view type every fibre has 0 elements and the formula gives (0!)^(k - 1) = 1, counting the unique (empty) put, which is very well-behaved even though get is not surjective (Toy.Lens.card_veryWellBehaved_puts_empty_state_two_views, instance k = 2). The count does not require get to be surjective.
- Edge case k = 1: with a one-element view type the formula gives (m!)^0 = 1 for every fibre size m; the unique very well-behaved put is the write that changes nothing, put s a = s, forced by GetPut (Toy.Lens.veryWellBehaved_put_eq_self_of_subsingleton_view).
- Both conclusions are propositions: `∃ e : Equiv ...` in the base-fibre form and `Nonempty (Equiv ...)` in the counting form live in Prop. The proofs use Classical.choice (to pick the fibre bijections given by hF, and a classical decidable equality on A when A has no DecidableEq instance); no computable enumeration of the very well-behaved puts is extracted.

**F6-unique.**

- PutGet, GetPut and PutPut alone do not determine the put (Toy.Lens.fst_twist_two_veryWellBehaved_puts: fst and twist have the same getter).
- Which put is singled out depends on the complement view: with complement view snd it is fst.put; with the XOR view (which together with the first projection also determines the state) it is the state-twisting put, and fst.put violates the frame law (Toy.Lens.twist_putIndep_xorView_complement).
- Does not assert that a complement view exists; by F3, one exists exactly for very well-behaved lenses.
- With a complement view that does not determine the state (e.g. a one-point view), uniqueness fails (Toy.Lens.existsUnique_put_tight_jointExt).
- Dropping hext breaks more than uniqueness: with the one-point complement view unitLensB on Bool × Bool (hsurj holds), the dirty-flag setter and the sibling-resetting setter satisfy PutGet and the frame law but violate PutPut and GetPut respectively, so the third conjunct fails too (Toy.Lens.existsUnique_put_drop_jointExt_admits_unlawful_puts).
- hsurj is a sufficient condition, not a necessary one: for the identity getter on Bool with a constant complement view, hext holds and hsurj fails, yet there is exactly one put with PutGet and the frame law, and it is very well-behaved (Toy.Lens.existsUnique_put_hsurj_not_necessary). The exact existence condition, for any second view m, is `∀ s a, ∃ s', get s' = a ∧ m.get s' = m.get s` (Toy.Lens.exists_put_putGet_putIndep_iff).
- The existence conjunct `∃ put, ...` lives in Prop and its proof uses Classical.choice; the theorem does not construct a computable put. A computable put needs an explicit function picking, for each (a, m.get s), the state realising it.

### Escape hatches of the impossibility results

- **F4-aliasing** fails (a lens is independent of itself) if the view type has at most one element (`unitLensB`), if the state type is empty, or without PutGet (`ignorePut`); all three are instances of `not_putIndep_self_tight`.
- **F5-unscoped** fails to refute unscoped JointExt if at most one state lacks both fields (`optFst_optSnd_jointExt`, `shape3_jointExt`) or if any one of the four `get = none` hypotheses is dropped (`not_jointExt_of_two_states_without_fields_tight`); scoping the law to a variant restores satisfiability (`scoped_decomposition_holds_but_unscoped_jointExt_fails`).
- **F4-F2-finite** and **F4-bare-bijection** are single counterexamples, not impossibility theorems; F2 holds for every finite index type, and naming the pairing map (F1) removes the hidden-state problem.

### Hypotheses with unknown tightness

None. Every hypothesis of every result is either `tight`, with a proved counterexample in canonical form, or `harmless`, with the reason given in its ledger row.

### Disproved or dropped statements

None. All 16 main statements were proved as stated; no statement was found false and none was dropped.

### Not examined

- Type-changing (polymorphic) lenses, symmetric lenses, delta lenses and lenses between categories are cited as prior art but not formalised.
- Weaker put-put laws (monotonic or mixed PutPut) and order-theoretic update strategies.
- Any concrete programming language, value representation, memory model or verification tool; every connection to a real interface is a modeling bridge.
- Complements outside the universe of the state type for F3 and F3-pair (F3-sharp covers the backward direction in any universe).

## Evidence

**Kernel check.** Built with Lean `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) on 2026-11-20: `lake build` of the project in `lean/` succeeds with no errors and no warnings, and the source contains no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. `Lean.collectAxioms` over all 716 non-internal declarations of the library reports only subsets of `{propext, Classical.choice, Quot.sound}`; the per-declaration lists are recorded in `audit/axioms.json`.

**Statement and closure hashes.** For every Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of `toString (repr type)` of its statement and the SHA-256 of its definition closure (the sorted, newline-joined list of `name : repr type` and, for definitions, ` := repr value`, over all library constants reachable from the statement through types, definition bodies and the constructors of inductive types; proofs of theorems are excluded). Changing a definition that a statement depends on changes its closure hash. `support/revalidate.py`, and equivalently `lean/scripts/audit/Audit.lean` with `lean/scripts/audit/check_audit.py`, recompute both hashes and check the axioms (see Revalidation).

| Lean name | used by | axioms | statement SHA-256 | closure SHA-256 (size) |
| --- | --- | --- | --- | --- |
| `Toy.Lens.isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty` | F1 result | none | `49c63f45d41f10328ef44e4a5e76a33dd28bc405808438ba11ad8c13a39b5636` | `e2317a4e804d1acc9436b49eb11fd13ca5915ac78c6d2b7dd1e37322a2a868a0` (14) |
| `Toy.Lens.isProductDecomposition_iff_putGet_putIndep_jointExt_imp_nonempty` | F1 result | none | `87a79d3ac71472716ef90e6873ea5d9ee8ad66981ecac78afd8cb970ab787409` | `e2317a4e804d1acc9436b49eb11fd13ca5915ac78c6d2b7dd1e37322a2a868a0` (14) |
| `Toy.Lens.pairPut_leftInverse_rightInverse_of_putGet_putIndep_jointExt` | F1-inverse result | none | `08b6cb971c2fa8b584ac15a19d90176ccac0553473353365e471d8a9c7f99873` | `8698372c1a9e4f671b0877c1c71ea526bc7c1b7586dab57681b98e8146f91e4e` (9) |
| `Toy.Lens.veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt` | F1-laws result | none | `a0717a5c7e35998a6c14f723837d26dff1dc078509b894c80967811333a1fdce` | `98667dc8fc22f83612d4a4453b83fc90184b50936db7718140d4ca629069fa2e` (11) |
| `Toy.Lens.getPut_of_putGet_putIndep_jointExt` | F1-laws result | none | `37a463cc945b157e9e423cf54f0dcbd1836e7665a8f8996f21b3e8af77d823dc` | `4e8e562f4d9fd5ea59376d285858f1be32d9192612005d9ed091f48efa5c44d9` (8) |
| `Toy.Lens.putPut_of_putGet_putIndep_jointExt` | F1-laws result | none | `e4e2147f35e8ab16f2aab51233dca1a851aa2d92d618bed39b0fbed32589269c` | `4430096ca33746ee1111575c79377d61cd953d17a1221eb5d164af81bb444294` (8) |
| `Toy.Lens.putComm_of_putGet_putIndep_jointExt` | F1-laws result | none | `8d5fa3bd721aed32b61d3c63a83ed8e14ea5381919164574f8b627a79a36f3fa` | `9d59e46b2cd19e97f48b7464e3714cdef6fcfd26ff9cf3b2e5530d07b7ad0b27` (8) |
| `Toy.Lens.isPiDecomposition_of_putGet_pairwiseIndep_famJointExt_finite_imp_nonempty` | F2 result | Quot.sound, propext | `c8753fa6861e073ccf4416f53bc4e9f5f1c571a305617511af00d2278a0001b0` | `7c66a7f5da2a958b2054651d6bae572097a658138b55b1bc1e196aed00daa9b6` (15) |
| `Toy.Lens.isPiDecomposition_iff_putGet_pairwiseIndep_famJointExt_imp_nonempty_of_finite` | F2 result | Quot.sound, propext | `237290cdabcc01e179b28897eb00d19712505d35bce71e8ebc84f9fc43fe47c1` | `7c66a7f5da2a958b2054651d6bae572097a658138b55b1bc1e196aed00daa9b6` (15) |
| `Toy.Lens.getPut_of_putGet_pairwiseIndep_famJointExt` | F2-laws result | Classical.choice, Quot.sound, propext | `f07d5468bd7726dad2165318cb9b1c5add68ebb090f1eb78ac95b77a55fc6e27` | `182645a13734018b1cdb132ff83a84cf8ad9e10b44bb1f3e66a3c7e130569394` (8) |
| `Toy.Lens.putPut_of_putGet_pairwiseIndep_famJointExt` | F2-laws result | Classical.choice, Quot.sound, propext | `c46b0d99a30c8aeb2a3c554e18850d0e108a3a249c29a9ee5ca10eb3de4c6cd3` | `783ebce7920869c9c25727cc231ca2bfab863319032e26a9e4ff31a39ddf70c5` (8) |
| `Toy.Lens.putComm_of_putGet_pairwiseIndep_famJointExt` | F2-laws result | Classical.choice, Quot.sound, propext | `f3f852247b553e41eb94c0a237328ffbebe7db2a5a5249ee728f9902f2eb3502` | `7ab73c6ccf0d86142ce09bc5aa407b7c4ead02757f57be8f210b1aec66049c14` (8) |
| `Toy.Lens.veryWellBehaved_iff_hasConstantComplement` | F3 result | Quot.sound | `37de5124efed6e7a2fb3e1d2d2227bf3885a3d3f9c4779ec16223b60e4c8c91e` | `9eb8ece152ca11e0ca94293c59a2481ae8b9eadffe220cf326ef97cfe6542d95` (15) |
| `Toy.Lens.veryWellBehaved_of_injective_intertwines_fst` | F3-sharp result | none | `c30d268695c262d14e192087cafa6d0e08c47f8b290629818bf69f381cecd35b` | `5cc01b4858553ce70f0052848712d0e2f3008a611a9a6ad6cc4f645ab4e117e2` (11) |
| `Toy.Lens.fiber_isConstantComplement_of_veryWellBehaved` | F3-fiber result | none | `4385d6a832129fccb848db043a126c7d52725de9880f5eb532c84db19d07b263` | `85804caf227eca5fff5a3699c74109b0d3605f71a1ee9c9f9444e7eb614bc3b0` (16) |
| `Toy.Lens.veryWellBehaved_and_putComm_iff_hasGhostComplement` | F3-pair result | Quot.sound | `a50d3fe4803486706e3487d78ddacdf8591e737cef75ddd39449a285bb13ea40` | `b765e53144e08b0b6fd9f7bda8b85a6574c5a4fdc6235c06f81f817f4db3d1bc` (17) |
| `Toy.Lens.derived_putComm_tight` | F1-laws counterexample; F4-derived-putComm result | none | `74d223ffba84ced9d5b00477e87c1805d469c025f76335fa16f7fbe05f50f4aa` | `4cdee453b6d906f3b44ab465ee00270098e01d5dd5c962d0e3395ef6ec5b586b` (18) |
| `Toy.Lens.derived_putComm_tight_mirror` | F1-laws counterexample; F4-derived-putComm result | none | `685a63871fe31cfaf5561484144dc5cba7fc3570fd67b43581887c25fb20817b` | `5ec6c4abb16bc273d3580c9c211082cb4c31de274c6c6c3d2e352d276c87b31b` (12) |
| `Toy.Lens.not_putIndep_self_of_putGet` | F4-aliasing result | none | `1c065e2100733f28c8dd3e3803038488850228a62335ac6e0fc6ef490ebd3201` | `e6b440250e2754bc66b04be1e0d44e7f85f3dbf9551be72b8e7f079cf7dc3a33` (6) |
| `Toy.Lens.aliasing_fails_putIndep_both_directions` | F4-aliasing result | none | `45ff2d23481d51a313996bfd5a6b93700f49ad8f2f25ac02ccc073f6cfa37e64` | `1ea41047e3849e96ba485f37aebf638673ae86e788f0c3298b1045b5adf5d153` (15) |
| `Toy.Lens.ghost_admits_unrelated_bijection` | F4-bare-bijection result | Classical.choice, Quot.sound, propext | `a8dd788a09c66af13e97e9020fd7bcc1c44cf9ea8412baea394858e2fda18281` | `46727be3ac5e786eb5837cd46654049640dd368f94ea8df58c9a4b94ff3a4cf4` (16) |
| `Toy.Lens.evCoord_tight_finite_index` | F2 counterexample; F4-F2-finite result | Quot.sound, propext | `01f6a8b5c43439becdcf1e907c1afd188ae4ff109681b63e0faee97949a324e9` | `4754985fb9dbe4e46862f4904a2e9b26bf1d1ff40a7bb824de14c226839ea436` (18) |
| `Toy.Lens.PLens.isProductDecompositionOn_of_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty` | F5 result | none | `4073598cc542a787d63e7c214e59bfd9b01e75e1430ddc2f1e6057538840d833` | `5c57052d7bb45917c54186f82d1b32f44f2249f372621d54d598abf974f3a77c` (11) |
| `Toy.Lens.PLens.isProductDecompositionOn_iff_totalOn_putGetOn_putIndepOn_jointExtOn_imp_nonempty` | F5 result | none | `d1ef7874e088226941940d738146a997f433b5267858f0f071024ab81683eb81` | `5c57052d7bb45917c54186f82d1b32f44f2249f372621d54d598abf974f3a77c` (11) |
| `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields` | F5-unscoped result | none | `fda0109e8cff07c3e91f9b3d39dd9b872bb7f6acb2ef705fc0d6c2ed007c5186` | `c504f4df4896ef58f07302a49d890877c8c48121b159607651d41c35c8cdfd48` (4) |
| `Toy.Lens.PLens.eq_of_jointExt_of_get_eq_none` | F5-unscoped result | none | `2b2ad69473e83db371d90b9318cfdbcaa0fb5fc149baf1281b696c8b47c01759` | `c504f4df4896ef58f07302a49d890877c8c48121b159607651d41c35c8cdfd48` (4) |
| `Toy.Lens.PLens.scoped_decomposition_holds_but_unscoped_jointExt_fails` | F5-unscoped result | propext | `cc449d9ebd22218c0f3b8c73245894017ae0d0c6daaeb94293e295b3c02987d3` | `9914e51851a9bd7343a65144ee8409ae7d214773123a7b62d3e919908962aa45` (20) |
| `Toy.Lens.PLens.scoped_laws_admit_variant_switching_put` | F5-switch result | propext | `156fe69663580257c3aa10df6f152b4a030b63f3d66e34782a39b91eea459649` | `a73efe804881ffa0301d991b506e6a1d093d673a472c1656bef1b7c03eb87aa6` (20) |
| `Toy.Lens.PLens.unscoped_putIndep_admits_tag_switch` | F5-switch result | propext | `88a2cc4a9943787a487e458e8d77486247ac88692b73e30239cc96afafa2b27a` | `4f321adb4cc7e93c6101d358ff1b3c1e0664aae96bdf7214e54a11bf48b60470` (21) |
| `Toy.Lens.PLens.unscoped_laws_admit_variant_switch` | F5-switch result | none | `10dbc2dbbf169552c4045c95631533ab574a597de7426aa5f1ccef92c56ff159` | `345ad3d21835cfe418a9049206835e1f937749a720bddf8d08b666b7e8314b87` (18) |
| `Toy.Lens.PLens.pairFstSwitch_violates_unscoped_putIndep` | F5-switch result | propext | `97fbc5043d4c8d791e19de99a12db5f515214d868bfdb8ce09db41521ec21d3b` | `a5dca12b6df8e273b970f978f64a9cede877cf2fe612712b15f200a019c6b6aa` (18) |
| `Toy.Lens.coherent_fiberMaps_correspond_veryWellBehaved_puts` | F6 result | Quot.sound | `b7592f2be09209d217d8d5b9ec63b4d8cf1a6bdfb6e62609c7a3be634ba21e36` | `de999766235122fe679c7ee0fed351ab0d9ebaabafb4f59441eff19c1af8e6ea` (17) |
| `Toy.Lens.getPut_iff_ofPut_map_self_and_putPut_iff_ofPut_map_comp` | F6 result | none | `16ccf14700b4f20045e1e5474e712105131b399015f761f994c0ff8ab7046bf9` | `5611a784968ee1941acdf9118347837e6e9cdb238271a35fa79bd43d143cdb1c` (11) |
| `Toy.Lens.veryWellBehaved_puts_equiv_baseFiber_bijections` | F6-count result | Classical.choice, Quot.sound, propext | `fb5082d11c9b1a7f53b9e726af511b107485349d5b4bbbde57c06e23b1b5cbde` | `0970b0db58b2cdf9392caa00308d9b1d262a6b3292f3289a675eb54de14589e8` (12) |
| `Toy.Lens.card_veryWellBehaved_puts_of_card_views_card_fibers` | F6-count result | Classical.choice, Quot.sound, propext | `597045e0af618c0dd538d6927d8989f6223bbd9ee12c7cc1bbdcf6f36cb04c08` | `c9a687c3952d69e3ab3e4cfb507db7fe455a77880345b2ab6a99084c7eac4a40` (14) |
| `Toy.Lens.existsUnique_put_putGet_putIndep_of_jointExt_surjective` | F6-unique result | Classical.choice, Quot.sound | `2f1512b2d2500196b671301b6e5d835493bddfba1cddfd00d0c8e5a7a039a44f` | `0ca14858e0f27c8d2d0b6d349b82e3586e24066a960a65e2a0f9470638023fe0` (9) |
| `Toy.Lens.PLens.absent_tight_totalOn` | F5 counterexample | none | `f095a23aff37f6cc8bd8310ea3f41f2a353a3048e9cccfb8f7fba602361269dd` | `f572c1bb29a3c1b346ca754daf572b40eff9d0d093f13226ea76b51fb17aa932` (18) |
| `Toy.Lens.PLens.absent_tight_totalOn_right` | F5 counterexample | none | `a9d5d1aaa2f8759210873317291a7552f27d7ffe4a60c3c8318c6d5ce77bd0ca` | `f572c1bb29a3c1b346ca754daf572b40eff9d0d093f13226ea76b51fb17aa932` (18) |
| `Toy.Lens.PLens.f5_tight_jointExtOn` | F5 counterexample | none | `11e67a63e83166675c62e7a1dee374c7204e4556aee125c4c399d22cee7b7bb1` | `f8b4de635027d03ed60df0696cfbfde1407adc198f48be0b8a40aef300ee6233` (20) |
| `Toy.Lens.PLens.f5_tight_nonempty` | F5 counterexample | none | `8667262ece9e76cb3425602d67b83a54f848090752f4d9a8817816dbf1e1942b` | `dc7a36bc7c7f78f1e4e198a8fbf14338cb52faf174a6393284740794cc3623cc` (17) |
| `Toy.Lens.PLens.f5_tight_putGetOn_left` | F5 counterexample | none | `1d4c5ea520917a9ee4e4cbdd2d6e0d3384e1b6e81dd56a7c857bb798fd6367fe` | `4c25ebe6045ecba0a828284be49e604d54cb723519b9e7060da0ede634b9b608` (19) |
| `Toy.Lens.PLens.f5_tight_putGetOn_right` | F5 counterexample | none | `f47b06dca938fb3558aa62209f39b5e7fcfe995f0fcdf99073a6570000f4adab` | `7a02b2f0685589621c0af6190869452dc007bb6e47fe5c66aea9099f8bf87e31` (19) |
| `Toy.Lens.PLens.f5_tight_putIndepOn_left` | F5 counterexample | none | `36ec8adbd986cda41431b5284eb2adbe1688b527d7d5430b87c6284be085c1c4` | `ad675944adc1d7d431703add616bb5fec9368ceaac3d50190c06e3712c64627b` (19) |
| `Toy.Lens.PLens.f5_tight_putIndepOn_right` | F5 counterexample | none | `42e45f4ba2dff75b3bcd71ae4ca89a5b71825ac3c3c6f0dfdbc8462622085f71` | `ad675944adc1d7d431703add616bb5fec9368ceaac3d50190c06e3712c64627b` (19) |
| `Toy.Lens.PLens.f5_unscoped_nonvacuity` | F5-unscoped non-vacuity | propext | `e937bbaaaeefc2be86422eaae809a7ac8fe3c4a47d476583bf73da9f4b36b171` | `f56c1761ccd93830a733db96388f195bf9140434fe426629f682301718f53f08` (15) |
| `Toy.Lens.PLens.not_jointExt_of_two_states_without_fields_tight` | F5-unscoped counterexample | none | `3a84c1260cab489fd313922cb02f2cb3aa0487fc85a6350a55d4fa2348b581e6` | `3a373aea78b04b765187b727520458f0c3ccd325f437c28924a13077f7c52f85` (6) |
| `Toy.Lens.PLens.optFst_optSnd_jointExt` | F5-unscoped positive control | propext | `01a3658dfe1c058baeb39ec48d07b23565be29b68c2ffbda20b4c021d56569de` | `774ee60efe6f74ca35248932df2fb0d3712fb3b2fc3ff87c0d429d57bbd20e4f` (8) |
| `Toy.Lens.PLens.pairFst_pairSnd_isProductDecompositionOn` | F5 non-vacuity | propext | `089a21198cf2428939784ea2334062caec4b47b5718aef59d74bcebb13f16f1c` | `bb439e6dd72fd93d9ca49999f09a8f48ddc6e958ba1a3c8b65d0cf1c1de2b319` (19) |
| `Toy.Lens.PLens.pairFst_pairSnd_satisfy_f5_hypotheses` | F5 non-vacuity | propext | `8b6e5339f98095e84fa2f5363d0b736853d94aecc054620435220ae1800024d6` | `a87ff05d63d42c622d99353fa50a8e45bbebb901e72c2dd0c86adfccdd57c3a2` (22) |
| `Toy.Lens.PLens.shape3_jointExt` | F5-unscoped positive control | propext | `d1dfc269b915e54e407b6ae8899bccbcb26cb686718de7fa4ae447ad2ee6c6b7` | `a0bcad33f40810be13c5728d56f6a64a07c9e2ad4c6c0905db7366f02c94de2b` (18) |
| `Toy.Lens.PLens.totalOn_components_tight` | F5 counterexample | none | `808c18743ba37f42516bef13ef626de18c9abaaeaee5a6dd865c884f49d54e77` | `6f30b5e3ca83a43410561d832b377b27ce8843b65cbaa64a509aa7dd04d7ae42` (20) |
| `Toy.Lens.aliasing_nonvacuity_bool` | F4-aliasing non-vacuity | none | `90b9317c87f840d9307bdb37c8edeebebbe08d7b3fb19f7e0ec7076d3c69ff54` | `74aa65fbb85e93fd66259507f99b9bbaeb3898226e4fd3de3e1f97a8f9997ba1` (7) |
| `Toy.Lens.card_tight_uniform_fibers` | F6-count counterexample | propext | `f1cf1e53fa5aa8e176ee444e42871b609e0c0ccca8e408bd4c69b89cac7211f8` | `c915ca7f2450dea0b01f5ef90898154b2dc76f7c8e118862a0a12509c4ad2f22` (15) |
| `Toy.Lens.card_tight_views` | F6-count counterexample | Quot.sound, propext | `1fc987548670a1082fbd61ff2668ec5b5d4e2f9eb14fa217c1c03a47a5d2912c` | `b79ad98ed7f81699e4380ad3f5f8d8bb6030fdd1dc65d326dcc71ce8ea11168b` (15) |
| `Toy.Lens.coord_bool_satisfy_f2_hypotheses` | F2 non-vacuity | Quot.sound, propext | `7e158895cb430c14ed3ab457e15c09d1ea2dc7add38131093819b5d61b320100` | `7b983e11285f9e72804a73e0f775feb98760bb83efab5d05d779928710959abf` (10) |
| `Toy.Lens.coord_isPiDecomposition` | F2 non-vacuity | none | `618401adcab8c50c1dc3fa86d4b22020fd3db600f2970f7867dddb18049034dd` | `85172bb48586c526e3f8e5f304239f8a1bf5cfd4a291f8627f3b65d4f4744fa6` (11) |
| `Toy.Lens.derived_getPut_tight` | F1-laws counterexample | none | `df1d809cb15371bb130a1055db9588233c66b64f48480fe48b9fa6a1bcedefc2` | `7fd49013f5f3595f2adac30c89e1374b88e2be8e6ccbd3ee3dbb73f11bc4ae50` (15) |
| `Toy.Lens.derived_putPut_tight` | F1-laws counterexample | none | `106d2943fd5677c7bbd3d585293ff159dd322d29d4d4e9520437250f78ee3704` | `37469747987e62b3476f62e415593a8021017b993b2a2ad2ad0d2c968990bddb` (15) |
| `Toy.Lens.dirtyFlag_intertwines_fst_noninjective` | F3-sharp counterexample | none | `0a4a890bd7de7dbe79c3a915869a4a2f6527df04d01b6d98805d3adf29ac1f64` | `44412cdad61260174f60d77d62955e1ead075062e4fa78d55121da5fa5305d5d` (12) |
| `Toy.Lens.emptyFam_tight_nonempty` | F2 counterexample | none | `b99b0657a3659c2e9cdd53be139313a30fc489b8aaa524eaca7f78acfa7f3714` | `8f3e3839fb6896dfeee883d1f85250a307a7c6d3074e50f2ba5948c16bb1113e` (16) |
| `Toy.Lens.empty_tight_nonempty` | F1 counterexample | none | `520274bbec294981014184dd90db54741531bca72bc6b1e6dc6651baaf0dc578` | `c0e7bb9728186878c7d49a0903c9a2ae0857aa9b57db09ce2c8ca19915d77b66` (15) |
| `Toy.Lens.existsUnique_put_drop_jointExt_admits_unlawful_puts` | F6-unique counterexample | none | `fd673fc980f94a3d2cab520aaa5d09f3f46207476021798597280cf32a503746` | `874c7d36b59f6efc7920e51a851294cebd36c74094557a154648c6e405eee474` (13) |
| `Toy.Lens.existsUnique_put_tight_jointExt` | F6-unique counterexample | none | `77da2e73fda760103ca55ed087d5f13f6231288da0187510fb401f988c0037ee` | `cd3a8db120d7369bba674fe3a0d5bc2d4b07ce511894f216c1d6700fa7b8002e` (8) |
| `Toy.Lens.existsUnique_put_tight_surjective` | F6-unique counterexample | none | `ccfb41f08cddd3b9107a791a291a196fdb38336c629fa2b1e0e7b451bfb682c7` | `0cbaa533067bd0924551044ac87f4caefa2ee3578026dd23bfe6344324a71fd3` (7) |
| `Toy.Lens.f1_inverse_nonvacuity_bool` | F1-inverse non-vacuity | none | `f1a6cd8633d988aed4d997a96fde5f75c61d5ce0093877aca48fbdf156f4d586` | `4b978095a9548d0e199fc3c13609d341fe6da5da47b59a9936475b56ffa356b3` (10) |
| `Toy.Lens.f1_laws_bundled_tight` | F1-laws counterexample | none | `ab87b1c3743e9fefd11fae36f864d4e457332feae83b6485baf57a9644d51350` | `cbddec49258393724c0f85aba9d0571e3d6f6afe21333dd9814b58e5a2208bb0` (18) |
| `Toy.Lens.f1_nonvacuity_bool` | F1 non-vacuity; F1-laws non-vacuity | none | `32b60dac098aae0d02d50db5a8d41b6294e730ebaf73e231b63f01f0ca47b9fc` | `904fc6969ef751f3790fa8174b3d9b05d26d6aed2ae81a3fa0cb722932bc3bc9` (11) |
| `Toy.Lens.f2_getPut_tight` | F2-laws counterexample | none | `d61cdae874293e03f840ab61e226a6c1730959c18408e53ee7af02934f47fa3a` | `a5495d65faeb6e4dae0c37a9bd4a8fd4ab238f1b829a1a3e62bd0c7ad3d0fcb1` (18) |
| `Toy.Lens.f2_laws_nonvacuity_bool` | F2-laws non-vacuity | Quot.sound, propext | `e91d35254c8f150e6615cfb990b272eacfe467cab7a3e1dfb66efd062563baf7` | `d9b27f6203f979bdd3474e5663876f4957eb4d7f666470b6dafaebbb05d5a9be` (9) |
| `Toy.Lens.f2_putComm_tight` | F2-laws counterexample | none | `d25f89b5785c801fa2f11d9b92317feb3726d988bd97416d66f7dacc92be09b3` | `00689abe6e2f4b3ad28eb084029e3c4a6900db999cfd76ccada1a3767ab4ae4a` (19) |
| `Toy.Lens.f2_putPut_tight` | F2-laws counterexample | none | `ae5938f2682701897df6e537d6576dcff6e7851c1d25b0606937c4802fbcb474` | `34c072e081492b80a802f941ba5baa3369557657bff59726f76a1484fd5378ae` (18) |
| `Toy.Lens.f3_laws_tight` | F3 counterexample; F3-fiber counterexample | none | `632e24429453e479b50adfaec591f4c722d2e48b35afb748532c292378efc90b` | `aca36c9fbcc7ad08756c57b7fa8902f9d20f0f41aedb8f2384686a41b307cd81` (19) |
| `Toy.Lens.f3_nonvacuity_bool` | F3 non-vacuity; F3-fiber non-vacuity | none | `2236a8e64504882c85a3c6aacb75b142735e94121969e01bad2157a9aad5c73c` | `ab7a84ab7bb5afa8bca6b664d881125f0126f4b1efff606be9413259639c04b6` (16) |
| `Toy.Lens.f3_pair_nonvacuity_bool` | F3-pair non-vacuity | none | `464b4f7f882f2f7dc5576c6085161d94055da2cd8e9d09cdca0bab8dd1d04f8c` | `65500cbb8500b96f4504fa77601ff6e2bc86e8e357e2678955076981fede4a61` (21) |
| `Toy.Lens.f3_sharp_intertwines_tight` | F3-sharp counterexample | none | `1045f498f3cf240612f9f5bcd03245667a5d13ab51f9de8c954b772187aeb3cc` | `44412cdad61260174f60d77d62955e1ead075062e4fa78d55121da5fa5305d5d` (12) |
| `Toy.Lens.f3_sharp_nonvacuity_bool` | F3-sharp non-vacuity | none | `2c28fc1f6e7b786687bdb31363ee121c13b57be2c1c9ac50bd378362763e9825` | `61324bb31b482e55b457af99e691516a18a164636cd8b10f05ab0138c91be975` (8) |
| `Toy.Lens.f6_count_nonvacuity` | F6-count non-vacuity | propext | `cfeb14c654f831da9ee95b4674e9e5e66d706ce583c91db64f45fae99be2ee51` | `9d7bba88a7a25ea76727c2784e36eb63d9eab0a635e22178658a54d315ce9fb5` (4) |
| `Toy.Lens.f6_nonvacuity` | F6 non-vacuity | none | `7f5a8b66678bafb7e27db5c7225b0db2a69d27afcb83ece7cb2a396f55ff0788` | `ba558f647c457ab691ecf67c34c763295c29932bd74080b5930901f2a1a632dd` (17) |
| `Toy.Lens.f6_unique_nonvacuity` | F6-unique non-vacuity | none | `65e1bb15ed044a8e8fa2ea0fc6a712e76d6999b1692e3ba5fff8e589953a3841` | `6cae5d57c940929bdcda3e4d8cd05d5142b64e18b26783945685cafc082266ad` (6) |
| `Toy.Lens.fam2_ignorePut_tight_putGet` | F2 counterexample | propext | `340e092e1bd5936e59e345ac13852b582e3b85c8a4f91ff1b610aa8b0cf53d52` | `2d47125951f564c1acaf62e0113239460b4c6042e687f49902833243707f90eb` (20) |
| `Toy.Lens.fam2_twist_tight_pairwiseIndep` | F2 counterexample | propext | `1c982fc59c4c1ac344d42db800142280390affbef1e4bdbc23289dbabb1a9b5a` | `2f5e3dbdf5474ca67f84b20500faa8c730a5614d15f2188ea7644ec8ce16a60b` (20) |
| `Toy.Lens.fst_hasConstantComplement` | F3 non-vacuity | none | `e1141adc91e74998443537cd326d1f19f4e73f103d85c031213289e7db59033f` | `73caf29defd306df0df12081148595eedff569c4dd065476a4480bb28397d8e7` (11) |
| `Toy.Lens.fst_snd_isProductDecomposition` | F1 non-vacuity | none | `f8f0149509844347695654c21dc123ed9d900b0f77cfd9fe701f9183b847be06` | `47b501e8f6ddb153c51064531d5d0a684a81b42b41f13a36de589971ebc11018` (11) |
| `Toy.Lens.fst_snd_satisfy_f1_hypotheses` | F1 non-vacuity | none | `0dfbfaa683aab06cb697f6d18676b2b07e0181f6ecf9d7803a442e9f5fe7da4f` | `34144cc3c0dde0cf869d1c44806614d2ee514e3afac80a3840cfa4e3adb0b143` (9) |
| `Toy.Lens.ghostComplement_laws_tight` | F3-pair counterexample | none | `0cac5584cd98ca977597eb39b35caab7f1d53a94de6013b11974bf3825e53002` | `10b35e5adab9b5d5cc97e52092a82da5a005a5c86861640fc7d248ff90758c4e` (23) |
| `Toy.Lens.ghostFam_tight_famJointExt` | F2 counterexample | Quot.sound, propext | `8a9147346eac60729793bfcde05ca25b8aad24d3c0d0852652aff46fbe1ffc5e` | `c1697b581a6928ad7c0d78a55d457a410929a033d14c8222d6fac33c12da2231` (19) |
| `Toy.Lens.ghost_hasGhostComplement` | F3-pair non-vacuity | none | `ae71153b9853cc241ea695ad2e342108fd98158f50d61a264b2149c70f16e540` | `d9fded224d9762044459535a06c1510b89974eeabe7e3e9e9f21f66f9adb06b8` (12) |
| `Toy.Lens.ghost_tight_jointExt` | F1 counterexample | none | `cc268fd498d446759da06a09c33aec7c24dd8bb3e483f98253afcd6aeda9353a` | `de1f77c23f6a2c164f95fdc0cf0e8785f67c8fda3e66f2725624272191941e5f` (16) |
| `Toy.Lens.ignorePutSnd_tight_putGet_right` | F1 counterexample | none | `6c5addcc12175f78f8dbb9d709dcfa1a9658aac6407c1a4174b30610cb4d2353` | `cdb7d6f125f64e3d4012474a7cff39e50cc52e79b91a7f08b28294d4a26b9a5b` (16) |
| `Toy.Lens.ignorePut_tight_putGet_left` | F1 counterexample | none | `4b1072bc911fb6bf1976d855fde7094f4df3d0356c0ae413005b11d3ac477120` | `62e6f1fd053df9267b2a8445e68ee8bc54fe21dfa226db5b1657eee03c55717b` (16) |
| `Toy.Lens.not_putIndep_self_tight` | F4-aliasing positive control; F4-aliasing counterexample | none | `0ce638ebf09e18d971c5e1d0941c7e1c44dfa81bca64988f8f9e0af0555ba846` | `1bbeac62fbbb8ff10acced195c81fd439b80ba6ec618a87f0ae027ca4e26e232` (9) |
| `Toy.Lens.ofPut_twist_coherent` | F6 non-vacuity | none | `b75a2a725110684028a86ae3e11aa69272312c249a476add57ae2ebe5f3510cb` | `16bd70a2535c4216740ee14c243f8518a458bc766e68478b8f09563118494f3a` (17) |
| `Toy.Lens.pairPut_inverse_tight` | F1-inverse counterexample | none | `2b030a458763f0c52fcfded22055f6fe7abef6e4c64a366b6070f13b2d671392` | `a3b86b7f4cabafc4c77798d0db28dba4a5bcdc9687d50eb62f5fd2d6e79afed2` (20) |
| `Toy.Lens.twist_hasConstantComplement` | F3 non-vacuity | none | `a82b55fe36c68ffdec8bd54b07999826e0a6218ee470202aae25a2f29a1bac5b` | `ff6420aec628257b9758dfbd80046f4a7ee1d3b2e09b1ae3a372b8c358570729` (12) |
| `Toy.Lens.twist_snd_not_hasGhostComplement` | F3-pair counterexample | none | `444cbdce17052980f263eaecfcb639cfb731e5a56568baebac258456de27fe4a` | `45f9127a926f3f9d8ea17c4fe0f022f4e03cad5caaa5ef3d11a689741231fba1` (14) |
| `Toy.Lens.twist_tight_putIndep_left` | F1 counterexample | none | `4ec0edc7562dd8db111e9c551e8cf71f6eb8f8d507efdce9b6537e4368a617ed` | `aa56f74a77b5f26d83605c6560ef88dbd3c65910f72245b56f4b9f6f6dba8037` (16) |
| `Toy.Lens.twist_tight_putIndep_right` | F1 counterexample | none | `f401b4e6ed5684c22b71baf8cd8812cc760a3e5cf7ecb5601c0943c74ea3159a` | `aa56f74a77b5f26d83605c6560ef88dbd3c65910f72245b56f4b9f6f6dba8037` (16) |
| `Toy.Lens.veryWellBehaved_puts_getFst_eq_fst_or_twist` | F6-count non-vacuity | Quot.sound | `bbe7768c873a399c4b43e3c8db39a4d4cb1a54fad9a365797c19d389b26d2bc6` | `1dd2787dd2a0b7c5f4c809d32351dc33752471ffe471928b53a0138eb84f7826` (12) |
| `Toy.Lens.xorView_tight_putIndep_left` | F1 counterexample | none | `3ad5b8600a82bbe5cce3f26a69bbb47af6a7e9c9c5afa2f6fb412131af2dde2b` | `7fc2e4ea3e9884afa88737f4c2dba229900d2cde4843f57bf435192a05156eb5` (16) |
| `Toy.Lens.xorView_tight_putIndep_right` | F1 counterexample | none | `dff26dd871e683ff0cb02b2151c84e6d54187aa5f89b5be30c9d0dcde7f17b0d` | `7fc2e4ea3e9884afa88737f4c2dba229900d2cde4843f57bf435192a05156eb5` (16) |

**Supplementary finite-model tests (not proofs).** `lean/scripts/finite_model_checks/` contains Python scripts that enumerate lenses on tiny finite types and test F1, F1-exact, the derived laws, F1-inverse, F3, F2, the pair form of F3, and the counting form of F6 for refutation; their recorded outputs are kept next to them. They can refute a statement but establish nothing; the kernel check above is the evidence.

**Primary sources.** Bibliographic records were checked on 2026-11-20: every DOI below resolved through the DOI system, and Crossref metadata (title, authors, venue, pages) matched the record where Crossref holds it; the arXiv records and the two Git commits were checked on arXiv and GitHub. Full texts read on that date: FGMPS07 (author-final PDF, Section 10 and footnote 9), PS03 (Theorem 2.3.9), JRW10 (Proposition 9, Theorem 12, Corollary 13), Clarke20 (Section 4), FZW16 (author-accepted version, Section 3.3) and Nakano19 (Sections 1-3). Characterisations of the other sources are as recorded in each citation, which states whether the source was read in full, read in abstract, or not consulted. arXiv identifiers carry the version current on that date: Riley18 has two versions (v2 of 7 September 2018 is cited); Nakano19, Clarke20 and FIP26 have a single version (v1).

**Identity of PS03.** PS03 is an unpublished working draft distributed from the first author's web page. It has no DOI, arXiv record or other immutable identifier (searches of Crossref and arXiv on 2026-11-20 found none), so it is identified by its URL together with the SHA-256 of the file: the PDF retrieved from that URL on 2026-11-20 has 139,723 bytes and SHA-256 `1e464cbf2027f4ea88e05bf10e2c81866e1cdd8449bcc2e97021044f252bdc5a` (7 pages, headed "Working draft of April 3, 2003"; Lemma 2.3.8 and Theorem 2.3.9 on page 6). The Internet Archive capture of the same URL dated 2004-07-19 (https://web.archive.org/web/20040719131443/http://www.cis.upenn.edu:80/%7Ebcpierce/papers/dblenses.pdf) is byte-identical to it. `REPORT.json` records the URL, the hash and the archived copy.

- [ACGMS18] F. Abou-Saleh, J. Cheney, J. Gibbons, J. McKinna, P. Stevens. Introduction to Bidirectional Transformations. In: Bidirectional Transformations, LNCS 9715, pp. 1-28, Springer, 2018. doi:10.1007/978-3-319-79108-1_1 (not consulted)
- [AFP] S. Foster, C. Pardillo-Laursen, F. Zeyda. Optics. Archive of Formal Proofs, May 2017. https://isa-afp.org/entries/Optics.html; theory sources at https://github.com/isabelle-utp/Optics commit b98aa6c1bd7b11a0c6f6de1b61589f00fb148bcc (the theory files named in the cards were read at that commit)
- [BS81] F. Bancilhon, N. Spyratos. Update semantics of relational views. ACM Trans. Database Syst. 6(4):557-575, 1981. doi:10.1145/319628.319634 (full text not consulted)
- [BvW98] R.-J. Back, J. von Wright. Refinement Calculus: A Systematic Introduction. Springer, 1998. doi:10.1007/978-1-4612-1674-2 (not consulted; cited in AFP Optics, Lens_Laws.thy, for the same variable axioms)
- [CDV21] P. Capriotti, N. A. Danielsson, A. Vezzosi. Higher Lenses. 36th ACM/IEEE Symposium on Logic in Computer Science (LICS 2021), pp. 1-13. doi:10.1109/LICS52264.2021.9470613; Agda development https://github.com/nad/dependent-lenses commit c09739a91f522074c9b3508e56252013219f359c (abstract and src/Lens/Non-dependent/Traditional.agda read; the paper's own lemma numbering not checked)
- [Clarke20] B. Clarke. Internal lenses as functors and cofunctors. In: J. Baez, B. Coecke (eds.), Applied Category Theory 2019, EPTCS 323, pp. 183-195, 2020. doi:10.4204/EPTCS.323.13, arXiv:2009.06835v1 (full text read)
- [Clarke24] B. Clarke, D. Elkins, J. Gibbons, F. Loregian, B. Milewski, E. Pillmore, M. Román. Profunctor Optics, a Categorical Update. Compositionality 6(1), 2024. doi:10.32408/compositionality-6-1 (not consulted)
- [DXC11] Z. Diskin, Y. Xiong, K. Czarnecki. From State- to Delta-Based Bidirectional Model Transformations: the Asymmetric Case. Journal of Object Technology 10, pp. 6:1-25, 2011. doi:10.5381/jot.2011.10.1.a6 (abstract read; full text not consulted)
- [FGMPS07] J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt. Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem. ACM Trans. Program. Lang. Syst. 29(3), Article 17, 2007. doi:10.1145/1232420.1232424
- [FHP15] S. Fischer, Z. Hu, H. Pacheco. A Clear Picture of Lens Laws - Functional Pearl. MPC 2015, LNCS 9129, pp. 215-223, Springer, 2015. doi:10.1007/978-3-319-19797-5_10 (full text not consulted; characterised through Nakano 2019)
- [FIP26] S. Foster, C. Isasa, C. Pardillo Laursen. Scenes: A Meta-Logical Algebra for Mutable State. arXiv:2609.29380v1, 2026 (not consulted)
- [FZW16] S. Foster, F. Zeyda, J. Woodcock. Unifying Heterogeneous State-Spaces with Lenses. ICTAC 2016, LNCS 9965, pp. 295-314, Springer, 2016. doi:10.1007/978-3-319-46750-4_17 (full text read: author-accepted version, https://eprints.whiterose.ac.uk/id/eprint/105106/)
- [GJ12] J. Gibbons, M. Johnson. Relating Algebraic and Coalgebraic Descriptions of Lenses. Electronic Communications of the EASST 49 (BX 2012), 2012. doi:10.14279/tuj.eceasst.49.726 (full text not consulted)
- [HPW11] M. Hofmann, B. C. Pierce, D. Wagner. Symmetric lenses. POPL 2011, pp. 371-384. doi:10.1145/1926385.1926428 (not consulted)
- [JR12] M. Johnson, R. D. Rosebrugh. Lens put-put laws: monotonic and mixed. Electronic Communications of the EASST 49 (BX 2012), 2012. doi:10.14279/tuj.eceasst.49.729 (abstract read; full text not consulted)
- [JRW10] M. Johnson, R. D. Rosebrugh, R. J. Wood. Algebras and Update Strategies. J. Univers. Comput. Sci. 16(5):729-748, 2010. doi:10.3217/jucs-016-05-0729
- [JRW12] M. Johnson, R. D. Rosebrugh, R. J. Wood. Lenses, fibrations and universal translations. Math. Struct. Comput. Sci. 22(1):25-42, 2012. doi:10.1017/S0960129511000442 (abstract read; full text not consulted)
- [Mech] Other mechanisations: the Lean 4 repository fraware/lean-optics and the Coq repository bedrocksystems/coq-lens provide basic lens definitions; Mathlib has no lens library. Not inspected here; no decomposition, complement or classification theorem is known to be in them.
- [Nakano19] K. Nakano. Towards a Complete Picture of Lens Laws. Third Workshop on Software Foundations for Data Interoperability (SFDI2019+), Fukuoka, 2019. arXiv:1910.10421v1, doi:10.48550/arXiv.1910.10421 (full text read)
- [PGW17] M. Pickering, J. Gibbons, N. Wu. Profunctor Optics: Modular Data Accessors. The Art, Science, and Engineering of Programming 1(2), Article 7, 2017. doi:10.22152/programming-journal.org/2017/1/7 (full text not consulted)
- [PP02] G. D. Plotkin, J. Power. Notions of Computation Determine Monads. FoSSaCS 2002, LNCS 2303, pp. 342-356, Springer, 2002. doi:10.1007/3-540-45931-6_24 (full text not consulted)
- [PS03] B. C. Pierce, A. Schmitt. Lenses and View Update Translation. Working draft of April 3, 2003, University of Pennsylvania. https://www.cis.upenn.edu/~bcpierce/papers/dblenses.pdf, SHA-256 1e464cbf2027f4ea88e05bf10e2c81866e1cdd8449bcc2e97021044f252bdc5a (full text read)
- [PSh04] A. J. Power, O. Shkaravska. From Comodels to Coalgebras: State and Arrays. CMCS 2004, ENTCS 106, pp. 297-314, 2004. doi:10.1016/j.entcs.2004.02.041 (full text not consulted)
- [Riley18] M. Riley. Categories of Optics. arXiv:1809.00738v2, doi:10.48550/arXiv.1809.00738, 2018 (full text not consulted; Proposition 4.1.3 and Section 4.10 as cited in the literature)

Observation date: 2026-11-20 (build, axiom audit, hashes, and source checks).

## Revalidation

From the package directory, with `elan` (which installs the toolchain pinned in `lean/lean-toolchain`) and `python3` available:

```sh
python3 support/revalidate.py .
```

The script copies `lean/` to a temporary directory (the package is not modified), prints one line per check, and ends with `REVALIDATED` and exit status 0 iff every check passes. It performs exactly these checks, and hashes exactly what item 4 describes:

1. `lake build` of the Lean project succeeds.
2. No Lean source under `lean/` contains `sorry`, `admit` or `native_decide`, or declares an `axiom` (comments are ignored).
3. Every declaration of the library (the modules of the `[[lean_lib]]` `Toy`) depends at most on the axioms `propext`, `Classical.choice` and `Quot.sound`, as computed by Lean's `collectAxioms`.
4. For every name recorded in `audit/statements.json`, which includes every Lean name referenced by `results.json`, the SHA-256 of `toString (repr type)` of its statement, the SHA-256 of its definition closure, and the closure size equal the recorded values. The closure is the sorted, newline-joined list of `name : repr type` (followed by ` := repr value` for definitions) over all library constants reachable from the statement through types, definition bodies and the constructors of inductive types; proofs of theorems are excluded.

The same checks can be run step by step with the package's own audit program, which lies outside the library target and in addition compares the per-declaration axiom lists with `audit/axioms.json`:

```sh
cd lean
lake build                                                   # no errors, no warnings
lake env lean scripts/audit/Audit.lean > /tmp/lens_audit.out # fails on any non-standard axiom
python3 scripts/audit/check_audit.py /tmp/lens_audit.out ../audit
```

The last command prints `"statement_drift": []` and `"axiom_drift": []` and exits with status 0 iff every recorded statement hash, closure hash and axiom list in `audit/` is reproduced. To spot-check one result:

```sh
printf 'import Toy\n#print axioms Toy.Lens.existsUnique_put_putGet_putIndep_of_jointExt_surjective\n' > /tmp/Ax.lean
lake env lean /tmp/Ax.lean
```

which must list at most `propext`, `Classical.choice` and `Quot.sound`. On a different Lean release the proofs may need repair and the `repr`-based statement hashes may change even when the statements are unchanged; in that case compare the pretty-printed statements in Findings with `#check` output instead of the hashes.
