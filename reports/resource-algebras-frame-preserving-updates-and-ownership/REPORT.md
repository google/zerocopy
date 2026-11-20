# Resource Algebras, Frame-Preserving Updates, and Ownership

## Summary

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

This package (`Toy.RA`, Lean `leanprover/lean4:v4.34.1`, core Lean only, Mathlib-free) formalizes discrete resource algebras and right-frame-preserving updates (`fpUpdate R a b :≡ ∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)`), characterizes the admissible updates of four canonical ownership algebras (exclusive, agreement, fractional-value, and authoritative/fragment), and identifies, for each general theorem, individually irredundant (tight) laws among `OpAssoc`, `OpComm`, `ValidOpL`, `IsRightUnit`, and `HasRightIdOnValid` that suffice for right-framing, parallel composition, resource dropping, and omitting the empty frame (tightness is not global necessity; see **Boundaries**, NC-G2). Every formal claim is subject to the package-wide non-claims in **Boundaries** (especially one-sided vs. single-left vs. simultaneous two-sided frame preservation, tightness vs. global necessity, discrete Leibniz equality without step-indexing, invalid-source vacuity, and the absence of an internalized program-logic adequacy bridge) as well as each card's individual non-claims in **Findings**.

Summary of the 18 kernel-checked results (all tier `T0`):

1. **`excl_no_valid_frame` (`Toy.RA.excl_no_valid_frame`, `impossibility`):** [Reference point] In the discrete non-unital exclusive resource algebra exclRA α, no carrier element f : Excl α composes validly with Excl.excl x.
2. **`excl_fpUpdate_iff` (`Toy.RA.excl_fpUpdate_iff`, `characterization`):** In exclRA α, Excl.excl x admits a right-frame-preserving update (fpUpdate) to e : Excl α if and only if e = Excl.excl y for some y : α; in particular, excl x ⤳ excl y holds for all x and y while excl x ⤳ invalid fails. Because exclRA α satisfies OpAssoc and OpComm (Toy.RA.exclRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
3. **`exclusive_fpUpdate` (`Toy.RA.exclusive_fpUpdate`, `theorem`):** In any raw resource algebra R : RawRA α (with no associativity, commutativity, or validity-closure laws required), if a is right-exclusive (IsExclusive R a) and b is valid (R.valid b), then a admits a right-frame-preserving update (fpUpdate R a b) to b.
4. **`agree_fpUpdate_iff` (`Toy.RA.agree_fpUpdate_iff`, `characterization`):** In the discrete agreement resource algebra agreeRA α (over any type α, without decidable equality), Agree.ag x admits a right-frame-preserving update (fpUpdate) to any carrier target s : Agree α if and only if s = Agree.ag x (with singleton specialization agree_ag_fpUpdate_iff). Because agreeRA α satisfies OpAssoc and OpComm (Toy.RA.agreeRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
5. **`agree_distinct_not_fpUpdate` (`Toy.RA.agree_distinct_not_fpUpdate`, `impossibility`):** [Reference point] In agreeRA α, whenever x ≠ y, the duplicate right frame Agree.ag x composes validly with Agree.ag x and invalidly with Agree.ag y, refuting right-frame preservation fpUpdate (agreeRA α) (Agree.ag x) (Agree.ag y) (ground Bool instance: Toy.RA.agree_naive_update_bool_counterexample). Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
6. **`fracVal_full_fpUpdate_iff` (`Toy.RA.fracVal_full_fpUpdate_iff`, `characterization`):** In the fractional-value algebra fracValRA α = prodRA fracRA (agreeRA α), a full share fracVal PosRat.one x admits a right-frame-preserving update (fpUpdate) to any carrier target (q', s) : PosRat × Agree α if and only if q' ≤ 1 and s = Agree.ag y for some y : α (with singleton specialization fracVal_full_ag_fpUpdate_iff). Because fracValRA α satisfies OpAssoc and OpComm (Toy.RA.fracValRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
7. **`fracVal_partial_fpUpdate_iff` (`Toy.RA.fracVal_partial_fpUpdate_iff`, `characterization`):** In fracValRA α, whenever q < 1 (PosRat.lt q PosRat.one), a partial share fracVal q x admits a right-frame-preserving update (fpUpdate) to any carrier target (q', s) : PosRat × Agree α if and only if q' ≤ q and s = Agree.ag x (with singleton specialization fracVal_partial_ag_fpUpdate_iff). Because fracValRA α satisfies OpAssoc and OpComm (Toy.RA.fracValRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
8. **`fracVal_partial_value_change_impossible` (`Toy.RA.fracVal_partial_value_change_impossible`, `impossibility`):** [Reference point] In fracValRA α, whenever q < 1 (PosRat.lt q PosRat.one) and x ≠ y, no update from fracVal q x to fracVal q' y (for any q' : PosRat) is right-frame-preserving (fpUpdate); an explicit witness right frame (1 - q, ag x) is given by the companion theorem Toy.RA.fracVal_partial_complement_observes_change. Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
9. **`auth_both_fpUpdate_iff` (`Toy.RA.auth_both_fpUpdate_iff`, `characterization`):** For any raw resource algebra R : RawRA α (requiring zero algebraic laws on R), authElem a · fragElem b admits a right-frame-preserving update to authElem a' · fragElem b' in authRA R if and only if for every optional external fragment frame mbf : Option α, R.valid a ∧ (b ·? mbf) ≼? a implies R.valid a' ∧ (b' ·? mbf) ≼? a'.
10. **`auth_localUpdate_fpUpdate` (`Toy.RA.auth_localUpdate_fpUpdate`, `theorem`):** For any associative raw resource algebra R : RawRA α (OpAssoc R) — without requiring ValidOpL or a unit in R — if (a, b) admits a local update to (a', b') (LocalUpdate R a b a' b'), then authElem a · fragElem b admits a right-frame-preserving update (fpUpdate (authRA R)) to authElem a' · fragElem b' (which also preserves simultaneous two-sided frames when OpComm R holds alongside OpAssoc R: both laws lift to authRA R by Toy.RA.authRA_opComm and Toy.RA.authRA_opAssoc, and Toy.RA.fpUpdate2_of_assoc_comm then applies to authRA R).
11. **`auth_counter_inc_fpUpdate` (`Toy.RA.auth_counter_inc_fpUpdate`, `theorem`):** In authRA counterRA (where auth a · frag b is valid iff b ≤ a), incrementing both the authoritative counter and an owned fragment by any k : Nat yields a right-frame-preserving update (fpUpdate (authRA counterRA)) authElem a · fragElem b ⤳ authElem (a + k) · fragElem (b + k) (backed by Toy.RA.counter_inc_localUpdate). Because counterRA satisfies OpAssoc and OpComm and these lift to authRA counterRA (Toy.RA.counterRA_isCoreFreeRA, Toy.RA.authRA_isCoreFreeRA), the update also preserves simultaneous two-sided frames (Toy.RA.fpUpdate2_of_assoc_comm).
12. **`auth_counter_dec_auth_only_fails` (`Toy.RA.auth_counter_dec_auth_only_fails`, `counterexample`):** In counterRA (which satisfies OpAssoc, OpComm, and ValidOpL, lifted to authRA counterRA by Toy.RA.authRA_isCoreFreeRA), decrementing the authoritative counter from 2 to 1 while retaining fragment 1 violates LocalUpdate and breaks compatibility with the right frame fragElem 1, so the right-frame-preserving update (fpUpdate) auth 2 · frag 1 ⤳ auth 1 · frag 1 fails. Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
13. **`fpUpdate_frame_right` (`Toy.RA.fpUpdate_frame_right`, `theorem`):** In any associative raw resource algebra R : RawRA α (OpAssoc R) — with neither OpComm nor ValidOpL needed — a right-frame-preserving update a ⤳ b implies the right-framed update a · c ⤳ b · c for every c : α.
14. **`fpUpdate_op` (`Toy.RA.fpUpdate_op`, `theorem`):** In any raw resource algebra R : RawRA α satisfying associativity (OpAssoc R) and commutativity (OpComm R) — without requiring ValidOpL — deterministic right-frame-preserving updates (fpUpdate) compose in parallel: a₁ ⤳ b₁ and a₂ ⤳ b₂ imply a₁ · a₂ ⤳ b₁ · b₂. Under the same two laws, the composite update also preserves simultaneous two-sided frames (Toy.RA.fpUpdate2_of_assoc_comm).
15. **`fpUpdateP_op` (`Toy.RA.fpUpdateP_op`, `theorem`):** In any raw resource algebra R : RawRA α satisfying OpAssoc R and OpComm R (without ValidOpL), non-deterministic right-frame-preserving updates (fpUpdateP) a₁ ⤳: P₁ and a₂ ⤳: P₂ compose into a₁ · a₂ ⤳: Q whenever P₁ b₁ and P₂ b₂ imply Q (b₁ · b₂). No two-sided variant of fpUpdateP is defined in this package.
16. **`fpUpdate_drop_right` (`Toy.RA.fpUpdate_drop_right`, `theorem`):** In any raw resource algebra R : RawRA α satisfying all three discrete core-free RA laws (OpAssoc R, OpComm R, and ValidOpL R), discarding part of a composite resource is always right-frame-preserving: a · b ⤳ a for all a b : α (with ValidOpL R globally necessary for universal dropping via Toy.RA.validOpL_of_fpUpdate_drop_right_all).
17. **`fpUpdate_iff_bare_of_rightUnit` (`Toy.RA.fpUpdate_iff_bare_of_rightUnit`, `characterization`):** In any raw resource algebra R : RawRA α possessing a global right identity e (IsRightUnit R e) — with none of OpAssoc, OpComm, ValidOpL, or R.valid e required — optional right-frame fpUpdate R a b is equivalent to bare non-empty right-frame fpUpdateBare R a b.
18. **`fpUpdate_iff_bare_of_rightIdOnValid_validOpL` (`Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL`, `characterization`):** In any raw resource algebra R : RawRA α where every valid element admits a right identity (HasRightIdOnValid R) and validity is downward closed on the left (ValidOpL R) — without requiring a global unit, right identities on invalid elements, core laws, OpAssoc, or OpComm — optional right-frame fpUpdate R a b is equivalent to bare non-empty right-frame fpUpdateBare R a b.

For what these results do *not* establish—including why `OpComm` alone preserves single left frames (`f · a`) but **not** simultaneous two-sided contexts (`l · (a · r)`) without `OpAssoc`, why `LocalUpdate` is sufficient but not necessary for authoritative updates, and why `tight` hypotheses are not globally necessary across all algebras—see **Boundaries** first.

## Applicability

### Model Fidelity and Scope

`Toy.RA` is a self-contained **toy model** of discrete, unbundled resource algebras implemented in Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) using only core Lean (`Init`/`Lean` for standalone audit reflection) with **no Mathlib** and no external Lake dependencies (`[[require]]` is absent). Rather than bundling all resource-algebra axioms into a single typeclass, `RawRA α` records only a total binary composition `op : α → α → α` and a validity predicate `valid : α → Prop`, while each algebraic law (`OpAssoc`, `OpComm`, `ValidOpL`, `IsRightUnit`, `HasRightIdOnValid`, `HasLocalRightUnits`) is a standalone `Prop`. This unbundled design allows concrete algebras (`exclRA`, `agreeRA`, `fracRA`, `fracValRA`, `authRA`, `counterRA`) to be certified against the core-free discrete law bundle `IsCoreFreeRA R := OpAssoc R ∧ OpComm R ∧ ValidOpL R`, while each general update theorem states only the exact individual hypotheses its proof uses and pairs every hypothesis with a proved tightness counterexample.

### Relationship Among Identified Subjects

The subjects recorded in `REPORT.json` play distinct roles:

- **Execution toolchain (`leanprover/lean4`, `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`):** Compiles and kernel-checks every definition, theorem, non-vacuity witness, positive control, and counterexample in `lean/`.
- **Primary mechanized reference systems:**
  - **Iris in Rocq (`rocq-iris/iris`, tag `iris-4.4.0`, commit `82dbf5e7a11d7ffaafe78e95186b5b376f4df732`):** Supplies the canonical mechanized CMRA definitions, constructions (`iris/algebra/{cmra,updates,local_updates,excl,agree,frac,auth}.v`, `iris/algebra/lib/dfrac_agree.v`), and LaTeX technical documentation (`tex/{algebra,constructions}.tex`) whose discrete slice `Toy.RA` re-derives and decomposes by law.
  - **`iris-lean` (`leanprover-community/iris-lean`, commit `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b`):** Supplies the Lean 4 ordered-resource-algebra mechanization (`Iris/Iris/Algebra/{CMRA,Updates,LocalUpdates,Excl,Agree,Frac,Auth,Lib/DFracAgree}.lean`), including `Iris.Update.discrete_total` and the frame-inclusion sufficiency lemma `auth_update_ord`.
  - **F\* `FStar.PCM` (`FStarLang/FStar`, `ulib/FStar.PCM.fst` at commit `6089523e69201bb5844200c74b1eabfc640f31ab`, associated with Swamy et al., SteelCore, PACMPL 4 (ICFP 2020), DOI `10.1145/3409003`):** Provides a contrasting unital partial commutative monoid (PCM) formulation where composition is partial with a mandatory unit `one` and exclusivity rules out only non-unit frames.
- **Primary mathematical and historical literature:** Jung et al. (POPL 2015, DOI `10.1145/2676726.2676980`; JFP 2018, DOI `10.1017/S0956796818000151`) define Iris resource algebras, option-framed updates, `EX(X)`, `FRAC(X)`, and `AUTH`; Boyland (SAS 2003, DOI `10.1007/3-540-44898-5_4`) and Bornat et al. (POPL 2005, DOI `10.1145/1040305.1040327`) originate fractional read/write permissions; Dockins, Hobor, and Appel (APLAS 2009, DOI `10.1007/978-3-642-10672-9_13`) formulate multi-unit separation algebras (axiom (15), mirrored without cancellativity by `HasLocalRightUnits`); Krebbers et al. (ESOP 2017, DOI `10.1007/978-3-662-54434-1_26`) and Calcagno, O'Hearn, and Yang (LICS 2007, DOI `10.1109/LICS.2007.30`) provide background on `Ag(X)`, unital `Auth(M)`, and separation-algebra local actions.

### Known Gaps Between `Toy.RA` and Production Verification Frameworks

1. **Discrete Leibniz equality vs. step-indexed cameras (OFEs):** All definitions use Lean propositional equality (`=`) and a single validity predicate `valid : α → Prop`. Step-indexed validity (`✓{n}`), step-indexed equivalence (`≡{n}≡`), non-expansive operations, and higher-order recursive domain equations in Iris cameras are not modeled.
2. **Omission of bundled partial cores (`pcore`):** Iris RAs carry a partial core map `pcore : α → Option α` satisfying idempotence, inclusion, and monotonicity laws for persistent propositions (`□ P`). `Toy.RA` omits `pcore`; where Iris's `cmra_discrete_total_update` uses `CmraTotal` (`cmra_core_r`), Result 18 instead assumes the existential condition `HasRightIdOnValid R` (`∀ x, R.valid x → ∃ c, R.op x c = x`), together with `ValidOpL R`, without core laws.
3. **Unit-optional, non-cancellative composition:** Unlike F\* PCMs and Calcagno–O'Hearn–Yang / Dockins–Hobor–Appel separation algebras, `RawRA` and `IsCoreFreeRA` assume neither a global unit nor cancellativity (`exclRA`, `agreeRA`, and `fracValRA` have no global unit and are non-cancellative).
4. **Omission of discardable fractions and generalized views:** `fracValRA α` models owned positive rational shares `(0, 1] ∩ ℚ` paired with `Agree α` (`FRAC(α)` / `DfracOwn`), omitting Iris's `DFracDiscarded` persistent fractions, fractional authoritative tokens (`●{dq} a`), and general `View` cameras.
5. **Pure algebra vs. program-logic adequacy:** `Toy.RA` formalizes no separation-logic assertion language, ghost-state allocation rule, update modality, thread-pool operational semantics, or adequacy theorem.

### Evidence-Role Convention

- `Basis: execution (Lean kernel check)` designates theorems, characterizations, impossibilities, counterexamples, non-vacuity witnesses, and positive controls verified by the Lean 4.34.1 kernel in `lean/`.
- `Basis: source` and `Basis: normative` / `Basis: documentation` designate direct inspection of pinned upstream repository sources and published papers.
- `Basis: derived (modeling bridge)` designates any interpretive statement connecting algebraic frame preservation (`∀ mf, valid (a ·? mf) → valid (b ·? mf)`) to concurrent threads, readers, writers, or program-logic invariants; every such bridge is stated separately with its external soundness assumption made explicit.
- `Basis: derived` (without the modeling-bridge qualifier) designates a short argument from the stated definitions that is given inline and has no separate Lean declaration.

## Findings

### 1. Core Definitions, Algebraic Laws, and Concrete Algebras

`Basis: execution (Lean kernel check)` — Every core definition in `lean/Toy/RA/` is accompanied by kernel-checked positive examples (intended instances admitted) and negative examples (instances rejected).

#### 1.1 Raw Resource Algebras, Optional Composition, and Inclusion (`lean/Toy/RA/Core.lean`, `lean/Toy/RA/Laws.lean`)

```lean
structure RawRA (α : Type) where
  op    : α → α → α
  valid : α → Prop

def opOpt {α : Type} (R : RawRA α) (a : α) : Option α → α
  | none   => a
  | some f => R.op a f

def opOptL {α : Type} (R : RawRA α) : Option α → α → α
  | none,   x => x
  | some l, x => R.op l x

def included {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∃ c : α, R.op a c = b

def includedRefl {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∃ mc : Option α, opOpt R a mc = b
```

- **Captured notion:** `RawRA` isolates carrier-operation-validity data prior to algebraic laws; `opOpt` (`a ·? mf`, Iris's `opM`) and `includedRefl` (`a ≼? b`) handle optional right frames and reflexive inclusion uniformly across unital and non-unital algebras, while `opOptL` composes optional frames on the left.
- **Proved positive/negative examples:** `Toy.RA.included_pos_example` (`2 ≼ 5` in `natAddRA`), `Toy.RA.included_neg_example` (`¬ (5 ≼ 2)` in `natAddRA`); `Toy.RA.includedRefl_pos_example` (`some () ≼? some ()` in non-unital `exclUnitRA`), `Toy.RA.includedRefl_neg_example` (`¬ (5 ≼? 2)` in `natAddRA`).

#### 1.2 Separate Named Algebraic Laws (`lean/Toy/RA/Core.lean`)

```lean
def OpAssoc {α : Type} (R : RawRA α) : Prop :=
  ∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)

def OpComm {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, R.op x y = R.op y x

def ValidOpL {α : Type} (R : RawRA α) : Prop :=
  ∀ x y : α, R.valid (R.op x y) → R.valid x

def IsRightUnit {α : Type} (R : RawRA α) (e : α) : Prop :=
  ∀ x : α, R.op x e = x

def HasRightIdOnValid {α : Type} (R : RawRA α) : Prop :=
  ∀ x : α, R.valid x → ∃ c : α, R.op x c = x

def HasLocalRightUnits {α : Type} (R : RawRA α) : Prop :=
  ∀ x : α, ∃ c : α, R.op x c = x

def IsExclusive {α : Type} (R : RawRA α) (a : α) : Prop :=
  ∀ f : α, ¬ R.valid (R.op a f)

def IsCoreFreeRA {α : Type} (R : RawRA α) : Prop :=
  OpAssoc R ∧ OpComm R ∧ ValidOpL R
```

- **Captured notions and equivalences:** `ValidOpL` captures downward validity closure (`cmra_valid_op_l`) and is proved equivalent to closure under `included` (`Toy.RA.validOpL_iff_validClosedUnderIncluded`) and `includedRefl` (`Toy.RA.validOpL_iff_validClosedUnderIncludedRefl`). `HasLocalRightUnits` captures Dockins–Hobor–Appel multi-unit axiom (15) up to side and without cancellativity; `HasRightIdOnValid` weakens it to valid elements only (`Toy.RA.hasRightIdOnValid_of_hasLocalRightUnits`, strictly separated by `Toy.RA.rightIdOnValidOnlyRA_props`). `IsExclusive` rules out compatible right frames.
- **Proved positive/negative examples:**
  - `OpAssoc`: `Toy.RA.opAssoc_pos_example` (`natAddRA`), `Toy.RA.opAssoc_neg_example` (`natSubRA`).
  - `OpComm`: `Toy.RA.opComm_pos_example` (`natAddRA`), `Toy.RA.opComm_neg_example` (`boolLeftProjRA`).
  - `ValidOpL` (and inclusion-closure equivalents): `Toy.RA.validOpL_pos_example` (`cappedNatRA`), `Toy.RA.validOpL_neg_example` (`xorValidFalseRA`); `Toy.RA.validClosedUnderIncluded_pos_example` / `Toy.RA.validClosedUnderIncluded_neg_example`; `Toy.RA.validClosedUnderIncludedRefl_pos_example` / `Toy.RA.validClosedUnderIncludedRefl_neg_example`.
  - `IsCoreFreeRA`: `Toy.RA.isCoreFreeRA_pos_example` (`cappedNatRA`), `Toy.RA.isCoreFreeRA_neg_example` (`xorValidFalseRA`).
  - `IsRightUnit`: `Toy.RA.isRightUnit_pos_example` (`0` in `natAddRA`), `Toy.RA.isRightUnit_neg_example` (`1` in `natAddRA`).
  - `HasLocalRightUnits`: `Toy.RA.hasLocalRightUnits_pos_example` (`cappedNatRA`), `Toy.RA.hasLocalRightUnits_neg_example` (`natSuccAddRA`).
  - `HasRightIdOnValid`: `Toy.RA.hasRightIdOnValid_pos_example` (`cappedNatRA`), `Toy.RA.hasRightIdOnValid_neg_example` (`exclUnitRA`).
  - `IsExclusive`: `Toy.RA.isExclusive_pos_example` (`some ()` in `exclUnitRA`), `Toy.RA.isExclusive_neg_example` (`0` in `natAddRA`).

#### 1.3 Frame-Preserving Updates, Local Updates, and Product Combinator (`lean/Toy/RA/Core.lean`, `lean/Toy/RA/Laws.lean`)

```lean
def fpUpdate {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)

def fpUpdate2 {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ ml mr : Option α, R.valid (opOptL R ml (opOpt R a mr)) → R.valid (opOptL R ml (opOpt R b mr))

def fpUpdateP {α : Type} (R : RawRA α) (a : α) (P : α → Prop) : Prop :=
  ∀ mf : Option α, R.valid (opOpt R a mf) → ∃ b : α, P b ∧ R.valid (opOpt R b mf)

def fpUpdateBare {α : Type} (R : RawRA α) (a b : α) : Prop :=
  ∀ f : α, R.valid (R.op a f) → R.valid (R.op b f)

def LocalUpdate {α : Type} (R : RawRA α) (a b a' b' : α) : Prop :=
  ∀ mz : Option α, R.valid a → opOpt R b mz = a → R.valid a' ∧ opOpt R b' mz = a'

def prodRA {α β : Type} (R₁ : RawRA α) (R₂ : RawRA β) : RawRA (α × β) where
  op p q  := (R₁.op p.1 q.1, R₂.op p.2 q.2)
  valid p := R₁.valid p.1 ∧ R₂.valid p.2
```

- **Captured notions:** `fpUpdate` (`a ⤳ b`) is optional right-frame preservation (matching Iris's discrete `cmra_update` when `OpAssoc ∧ OpComm` hold); `fpUpdate2` tests simultaneous optional left and right frames `ml ·? (a ·? mr)`; `fpUpdateP` (`a ⤳: P`) is the non-deterministic set-valued update (`cmra_updateP`); `fpUpdateBare` quantifies only over non-empty right frames `f : α`; `LocalUpdate` captures discrete `local_update`; `prodRA` forms componentwise products (`prodRA_isCoreFreeRA`).
- **Proved positive/negative examples:** `Toy.RA.fpUpdate_pos_example` (`2 ⤳ 1` in `cappedNatRA`) and `Toy.RA.fpUpdate_neg_example` (`¬ (1 ⤳ 2)` in `cappedNatRA`); `Toy.RA.fpUpdate2_pos_example` and `Toy.RA.fpUpdate2_neg_example`; `Toy.RA.fpUpdateP_pos_example` and `Toy.RA.fpUpdateP_neg_example`; `Toy.RA.fpUpdateBare_pos_example` and `Toy.RA.fpUpdateBare_neg_example`; `Toy.RA.localUpdate_pos_example` (`(2, 1) → (3, 2)` in `natAddRA`) and `Toy.RA.localUpdate_neg_example` (`¬ LocalUpdate natAddRA 2 1 1 1`); `Toy.RA.prodRA_pos_example` and `Toy.RA.prodRA_neg_example`.
- **Law-free structural lemmas (`lean/Toy/RA/Core.lean`):** `fpUpdate_refl`, `fpUpdate_trans`, `fpUpdate_iff_fpUpdateP`, `fpUpdateP_id`, `fpUpdateP_compose`, `fpUpdateP_weaken`, `fpUpdate_imp_fpUpdateBare`, `localUpdate_refl`, `localUpdate_trans`, `localUpdate_unital_iff` (under `IsRightUnit`), plus single-left-frame transfer `fpUpdate_preserve_left_of_opComm` (under `OpComm`) and simultaneous two-sided transfer `fpUpdate2_of_assoc_comm` (under `OpAssoc ∧ OpComm`).

#### 1.4 Canonical Concrete Ownership Algebras (`Excl`, `Agree`, `PosRat`/`Frac`, `Auth`)

```lean
inductive Excl (α : Type) where | excl (x : α) | invalid
def exclRA (α : Type) : RawRA (Excl α) where
  op _ _ := .invalid
  valid | .excl _ => True | .invalid => False

structure Agree (α : Type) where
  mem : α → Prop
  nonempty : ∃ x : α, mem x
def Agree.ag {α : Type} (x : α) : Agree α := ⟨fun y => y = x, ⟨x, rfl⟩⟩
def agreeRA (α : Type) : RawRA (Agree α) where
  op a b := ⟨fun x => a.mem x ∨ b.mem x, let ⟨x, hx⟩ := a.nonempty; ⟨x, Or.inl hx⟩⟩
  valid a := ∀ x y : α, a.mem x → a.mem y → x = y

def fracRA : RawRA PosRat where op := PosRat.add; valid q := PosRat.le q PosRat.one
def fracValRA (α : Type) : RawRA (PosRat × Agree α) := prodRA fracRA (agreeRA α)
def fracVal {α : Type} (q : PosRat) (x : α) : PosRat × Agree α := (q, Agree.ag x)

inductive AuthPart (α : Type) where | none | excl (a : α) | conflict
structure AuthElem (α : Type) where auth : AuthPart α; frag : Option α
def authElem {α : Type} (a : α) : AuthElem α := ⟨.excl a, none⟩
def fragElem {α : Type} (b : α) : AuthElem α := ⟨.none, some b⟩
def authRA {α : Type} (R : RawRA α) : RawRA (AuthElem α) where
  op x y := ⟨AuthPart.op x.auth y.auth, optOp R.op x.frag y.frag⟩
  valid x := match x.auth, x.frag with
    | .conflict, _ => False | .none, none => True | .none, some b => R.valid b
    | .excl a, none => R.valid a | .excl a, some b => R.valid a ∧ includedRefl R b a
abbrev counterRA : RawRA Nat := natAddRA
```

- **Exclusive (`lean/Toy/RA/Excl.lean`):** Unique non-shareable ownership (`exclRA_isCoreFreeRA`; positive/negative examples `exclRA_valid_pos_example`, `exclRA_valid_neg_example`, `exclRA_op_neg_example`).
- **Agreement (`lean/Toy/RA/Agree.lean`):** Duplicable immutable consensus without `[DecidableEq α]` (`agreeRA_isCoreFreeRA`, non-unital `agreeRA_bool_no_rightUnit`, local right units `agree_hasLocalRightUnits`; positive/negative examples `agreeRA_valid_pos_example`, `agreeRA_valid_neg_example`).
- **Positive Rationals & Fractional Values (`lean/Toy/RA/PosRat.lean`, `lean/Toy/RA/Frac.lean`):** Quotient construction `PosRat` of `ℚ_{>0}` (`posRat_le_pos_example`, `posRat_le_neg_example`, `posRat_lt_pos_example`, `posRat_lt_neg_example`), pure fractions `fracRA` (`fracRA_isCoreFreeRA`, `fracRA_valid_pos_example`, `fracRA_valid_neg_example`), and fractional-agreement pairs `fracValRA α` (`fracValRA_isCoreFreeRA`, `fracValRA_valid_pos_example`, `fracValRA_valid_neg_example`) with exact complement `fracValComplement q hq x := (PosRat.sub PosRat.one q hq, Agree.ag x)`.
- **Authoritative / Fragment (`lean/Toy/RA/Auth.lean`):** Exclusive authoritative snapshot `authElem a` paired with optional fragments `fragElem b` (`authRA_isCoreFreeRA`, right unit `authRA_rightUnit`; positive/negative examples `authRA_pos_example`, `authRA_neg_example`), specialized to `counterRA` where `valid (auth a · frag b) ↔ b ≤ a` (`auth_counter_both_valid_iff`).

#### 1.5 Auxiliary Algebras Used by Examples, Counterexamples, and Boundary Theorems

The authoritative construction in §1.4 relies on three helpers from `lean/Toy/RA/Auth.lean`:

```lean
def AuthPart.op {α : Type} : AuthPart α → AuthPart α → AuthPart α
  | .none, p => p
  | p, .none => p
  | _, _ => .conflict

def optOp {α : Type} (f : α → α → α) : Option α → Option α → Option α
  | none, y => y
  | x, none => x
  | some a, some b => some (f a b)

def authUnit {α : Type} : AuthElem α := ⟨.none, none⟩
```

`AuthPart.op` sends any two non-empty authoritative parts to `.conflict`, which `authRA` treats as invalid; this is what makes the authoritative part exclusive. `optOp` adjoins `none` as an identity for fragments, and `authUnit` is the right unit of `authRA R` (`Toy.RA.authRA_rightUnit`).

The named auxiliary algebras below are all `RawRA` instances; each entry gives the carrier, the operation `x · y`, and the valid elements exactly as defined in Lean. Properties listed are those proved by the cited Lean declarations.

| Algebra | File | Carrier | Operation `x · y` | Valid elements | Proved properties / role |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `natAddRA` (`counterRA` is an abbreviation for it) | `Core.lean` | `Nat` | `x + y` | all | `opAssoc_pos_example`, `opComm_pos_example`, `isRightUnit_pos_example` (`0` is a right unit), `counterRA_isCoreFreeRA` |
| `cappedNatRA` | `Core.lean` | `Nat` | `x + y` | `n ≤ 2` | `isCoreFreeRA_pos_example`, `hasLocalRightUnits_pos_example` |
| `natSubRA` | `Core.lean` | `Nat` | truncated subtraction `x - y` | all | `opAssoc_neg_example`; universally valid (NC-G2) |
| `boolLeftProjRA` | `Core.lean` | `Bool` | `x` (left projection) | all | `opComm_neg_example`; universally valid (NC-G2) |
| `xorValidFalseRA` | `Core.lean` | `Bool` | `xor x y` | `false` only | `xorValidFalseRA_opAssoc`, `xorValidFalseRA_opComm`, `validOpL_neg_example` |
| `natSuccAddRA` | `Core.lean` | `Nat` | `x + y + 1` | all | `hasLocalRightUnits_neg_example` |
| `exclUnitRA` | `Core.lean` | `Option Unit` | always `none` | `some ()` only | `isExclusive_pos_example`, `hasRightIdOnValid_neg_example` |
| `pathCatRA` | `Laws.lean` | `Option (Bool × Bool)` | `some (s₁, t₁) · some (s₂, t₂) = some (s₁, t₂)` if `t₁ = s₂`, otherwise `none`; `none` is absorbing | `some _` only | `pathCatRA_opAssoc`, `pathCatRA_validOpL`, `pathCatRA_not_opComm` (NC-G1) |
| `nonAssocCommValidRA` | `Laws.lean` | `Four` = {`e0`, `e1`, `e2`, `e3`} | symmetric table: `e0 · e0 = e0 · e1 = e0 · e2 = e0`; `e1 · e1 = e1 · e2 = e2`; `e2 · e2 = e3`; `e3` is absorbing | all but `e3` | `nonAssocCommValidRA_opComm`, `nonAssocCommValidRA_validOpL`, `nonAssocCommValidRA_not_opAssoc` (NC-G1) |
| `authNonAssocRA` | `Auth.lean` | `Four` | symmetric table: `e0 · e0 = e0 · e1 = e0 · e3 = e0`; `e0 · e2 = e2`; `e1 · e1 = e1 · e2 = e1 · e3 = e3`; `e2 · e2 = e2`; `e2 · e3 = e3`; `e3 · e3 = e0` | all | `authNonAssocRA_opComm`, `authNonAssocRA_validOpL`, `authNonAssocRA_not_opAssoc` (Card 10 `hAssoc` counterexample) |
| `fiveLocalUnitsNoValidOpLRA` | `Laws.lean` | `Five` = {`z0`, …, `z4`} | symmetric table: `z0` is absorbing; `z1 · z1 = z1 · z2 = z1 · z3 = z0`; `z1 · z4 = z1`; `z2 · z2 = z2 · z3 = z2 · z4 = z2`; `z3 · z3 = z3`; `z3 · z4 = z2`; `z4 · z4 = z4` | `z1`, `z2` | `fiveLocalUnitsNoValidOpLRA_opAssoc`, `fiveLocalUnitsNoValidOpLRA_opComm`, `fiveLocalUnitsNoValidOpLRA_hasLocalRightUnits`, `fiveLocalUnitsNoValidOpLRA_hasRightIdOnValid`, `fiveLocalUnitsNoValidOpLRA_not_validOpL` (Card 18 `hValidOpL` counterexample) |
| `rightIdOnValidOnlyRA` | `Laws.lean` | `ThreeRightIdValid` = {`e`, `z`, `w`} | `e · e = e`; every other product is `w` | `e` only | `rightIdOnValidOnlyRA_props` (NC-G5) |
| `rightZeroBoolRA` | `Laws.lean` | `Bool` | `y` (right projection) | `true` only | `idempotent_noncomm_validOpL_witness` (NC-G6) |
| `zeroBoolRA` | `Laws.lean` | `Bool` | always `false` | `false` only | `two_element_comm_validOpL_witness` (NC-G6) |

### 2. Law-Usage Summary Matrix

`Basis: execution (Lean kernel check)` — In the table below, **Tight** means deleting that hypothesis from *that* theorem's hypothesis list yields a false general statement (refuted by a proved counterexample in `lean/`). It does **not** mean the law is globally necessary in every algebra (see **Boundaries §1, NC-G2**). Frame scope distinguishes right-composed frames (`a ·? mr`), single left frames (`l · a`, preserved when `OpComm` holds via `fpUpdate_preserve_left_of_opComm`), and simultaneous two-sided frames (`ml ·? (a ·? mr)`, preserved when `OpAssoc ∧ OpComm` hold via `fpUpdate2_of_assoc_comm`, and refuted under `OpComm` alone by `opComm_alone_not_two_sided` and `auth_opComm_alone_not_two_sided`).

| Declaration | `OpAssoc` | `OpComm` | `ValidOpL` | Other hypotheses | Frame scope established |
| :--- | :---: | :---: | :---: | :--- | :--- |
| `fpUpdate_refl`, `fpUpdate_trans` (helpers) | — | — | — | none | right frames |
| `auth_both_fpUpdate_iff` (Card 9) | — | — | — | none | right frames (`OpComm R` adds single-left; `OpAssoc R ∧ OpComm R` adds two-sided; the laws lift to `authRA R` by `authRA_opComm` and `authRA_opAssoc`) |
| `exclusive_fpUpdate` (Card 3) | — | — | — | `IsExclusive R a` (**Tight**), `R.valid b` (**Tight**) | right frames |
| `fpUpdate_iff_bare_of_rightUnit` (Card 17) | — | — | — | `IsRightUnit R e` (**Tight**) | right frames |
| `fpUpdate_iff_bare_of_rightIdOnValid_validOpL` (Card 18) | — | — | **Tight** | `HasRightIdOnValid R` (**Tight**) | right frames |
| `fpUpdate_frame_right` (Card 13) | **Tight** | — | — | `fpUpdate R a b` (**Tight**) | right frames (two-sided if `OpComm` also holds) |
| `auth_localUpdate_fpUpdate` (Card 10) | **Tight** | — | — | `LocalUpdate R a b a' b'` (**Tight**) | right frames (two-sided if `OpComm R` also holds, via `authRA_opComm`, `authRA_opAssoc`, and `fpUpdate2_of_assoc_comm`) |
| `fpUpdate_op` (Card 14), `fpUpdateP_op` (Card 15) | **Tight** | **Tight** | — | component updates (+ `hQ`, all **Tight**) | right frames; for `fpUpdate_op` also simultaneous two-sided frames (`fpUpdate2_of_assoc_comm`; no two-sided variant of `fpUpdateP` is defined) |
| `fpUpdate_drop_right` (Card 16) | **Tight** | **Tight** | **Tight** | none (`ValidOpL` also globally necessary for `∀ a b, a · b ⤳ a`) | right and simultaneous two-sided frames |

### 3. Formalized Result Cards

#### Card 1: `excl_no_valid_frame`

- **Lean declaration:** `Toy.RA.excl_no_valid_frame` in `lean/Toy/RA/Excl.lean`
- **Kind / Tier / Depth:** `impossibility` | `T0` — T0 (re-derivation of discrete `EX(X)` exclusivity from Jung et al., POPL 2015 §3.1 and JFP 2018 §3.1, and `excl_exclusive` in Iris, with the corresponding anonymous `Exclusive` instance aliased `excl_exclusive` in `iris-lean`). | `definitional`
- **Plain-language claim:** [Reference point] In the discrete non-unital exclusive resource algebra exclRA α, no carrier element f : Excl α composes validly with Excl.excl x.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.excl_no_valid_frame` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Connecting `¬ (exclRA α).valid ((exclRA α).op (.excl x) f)` to mutual exclusion or absence of aliasing in a concurrent program requires an external separation-logic soundness theorem mapping thread-local ghost assertions to composed algebraic states under a global validity invariant; no program logic or operational heap is formalized in `Toy.RA`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.excl_no_valid_frame {α : Type} (x : α) (f : Excl α) :
    ¬ (exclRA α).valid ((exclRA α).op (.excl x) f)
-- Unfolded:
--   (exclRA α).op (.excl x) f = Excl.invalid
--   (exclRA α).valid Excl.invalid = False
--   so the statement reduces definitionally to ¬ False.
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.excl_no_valid_frame_nonvacuity` — Over α = Nat, exclRA Nat satisfies IsCoreFreeRA and both Excl.excl 0 and Excl.excl 1 are individually valid.
- **Positive control:** `Toy.RA.excl_no_valid_frame_positive_control` — In the shareable core-free algebra `cappedNatRA` (`Nat` under `+` with `valid n := n ≤ 2`), `IsCoreFreeRA` holds and valid elements `0` and `1` compose validly (`0 + 1 ≤ 2`).
- **Non-claims:**
  - Does not apply to the unit-adjoined algebra Option (Excl α), where the empty unit none composes validly with some (Excl.excl x); in that unital setting, exclusivity rules out only non-unit frames.
  - Does not establish that owning Excl.excl x prevents aliasing in a physical memory model; any connection to concurrent programs is derived (modeling bridge): if two threads separately held Excl.excl x and f in a sound separation logic, their joint state would compose via R.op and violate validity, which is ruled out here only at the discrete algebra level (no program logic or heap semantics is formalized).
- **Prior art:**
  - Jung, Swasey, Sieczkowski, Svendsen, Turon, Birkedal, Dreyer, 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.1 EX(X))
  - Jung, Krebbers, Jourdan, Bizjak, Birkedal, Dreyer, 'Iris from the ground up: A modular foundation for higher-order concurrent separation logic', JFP 28 (2018), e20, pp. 1-73, DOI 10.1017/S0956796818000151 (§3.1, p. 18)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/excl.v (excl_exclusive), https://github.com/rocq-iris/iris/blob/82dbf5e7a11d7ffaafe78e95186b5b376f4df732/iris/algebra/excl.v
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Excl.lean (anonymous Exclusive instance for Excl carrying rocq_alias excl_exclusive, lines 225-226)
- **Design question:** Reference point: what frames can coexist with exclusive ownership in a discrete resource algebra, and why does exclusivity rule out composed observers?

#### Card 2: `excl_fpUpdate_iff`

- **Lean declaration:** `Toy.RA.excl_fpUpdate_iff` in `lean/Toy/RA/Excl.lean`
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (re-derivation of exclusive update rules `ex-update` / `cmra_update_exclusive` in Iris and `Iris.Update.exclusive` in `iris-lean`, stated as a two-way characterization over all `Excl α` targets). | `shallow`
- **Plain-language claim:** In exclRA α, Excl.excl x admits a right-frame-preserving update (fpUpdate) to e : Excl α if and only if e = Excl.excl y for some y : α; in particular, excl x ⤳ excl y holds for all x and y while excl x ⤳ invalid fails. Because exclRA α satisfies OpAssoc and OpComm (Toy.RA.exclRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.excl_fpUpdate_iff` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.excl_fpUpdate_iff {α : Type} (x : α) (e : Excl α) :
    fpUpdate (exclRA α) (.excl x) e ↔ ∃ y : α, e = .excl y
-- Unfolded:
--   (∀ mf : Option (Excl α),
--      (exclRA α).valid (opOpt (exclRA α) (.excl x) mf) →
--      (exclRA α).valid (opOpt (exclRA α) e mf))
--   ↔ ∃ y : α, e = Excl.excl y
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.excl_fpUpdate_iff_nonvacuity` — Over α = Bool, exclRA Bool satisfies IsCoreFreeRA and both Excl.excl false and Excl.excl true are valid.
- **Companion and boundary theorems:** `Toy.RA.excl_fpUpdate` (`excl x ⤳ excl y`), `Toy.RA.excl_invalid_target_fails` (`¬ (excl x ⤳ invalid)`).
- **Non-claims:**
  - Does not allow updating Excl.excl x to Excl.invalid; the optional empty frame mf = none enforces validity preservation even without a unit element.
  - Does not characterize updates out of Excl.invalid, which vacuously updates to any element because Excl.invalid is incompatible with every optional frame.
  - Does not cover step-indexed or OFE-non-expansive exclusive cameras over higher-order payloads.
- **Prior art:**
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (p. 4 FPUPD; §3.1 EX(X))
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§2.1 fn. 6, §3.1)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/algebra.tex (§RA) and tex/constructions.tex (§Exclusive Camera, ex-update)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/excl.v and iris/algebra/updates.v (cmra_update_exclusive)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Excl.lean and Iris/Iris/Algebra/Updates.lean (Iris.Update.exclusive)
- **Design question:** Which updates are frame-preserving under exclusive ownership, and why must the empty frame be checked?

#### Card 3: `exclusive_fpUpdate`

- **Lean declaration:** `Toy.RA.exclusive_fpUpdate` in `lean/Toy/RA/Core.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (re-derivation of Iris's `cmra_update_exclusive` and `Iris.Update.exclusive`; F*'s `FStar.PCM.exclusive_is_frame_preserving` is a unital-PCM special case proving only an update `x ⤳ one` to the unit under unital exclusivity). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α (with no associativity, commutativity, or validity-closure laws required), if a is right-exclusive (IsExclusive R a) and b is valid (R.valid b), then a admits a right-frame-preserving update (fpUpdate R a b) to b.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.exclusive_fpUpdate` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.exclusive_fpUpdate {α : Type} (R : RawRA α) (a b : α)
    (hExcl : IsExclusive R a) (hb : R.valid b) :
    fpUpdate R a b
-- Unfolded:
--   (∀ f : α, ¬ R.valid (R.op a f)) →
--   R.valid b →
--   (∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf))
```
- **Hypothesis ledger:**
  - `hExcl` — Guarantees no non-empty right frame f can compose validly with a, discharging the mf = some f branch. Tightness: `tight` (`Toy.RA.exclusive_fpUpdate_not_exclusive_counterexample`).
  - `hb` — Guarantees the target b is valid, discharging the empty-frame branch mf = none. Tightness: `tight` (`Toy.RA.exclusive_fpUpdate_invalid_target_counterexample`).
- **Non-vacuity witness:** `Toy.RA.exclusive_fpUpdate_nonvacuity` — In exclRA Bool, IsCoreFreeRA holds, Excl.excl false satisfies IsExclusive, and Excl.excl true is valid.
- **Companion and boundary theorems:** `Toy.RA.fpUpdate_preserve_left_of_opComm`, `Toy.RA.pathCat_fpUpdate_breaks_left_frame`.
- **Non-claims:**
  - 'No laws required' includes no commutativity. In a non-commutative algebra, IsExclusive R a rules out only right frames, and the resulting update need not preserve left frames (see Toy.RA.fpUpdate_preserve_left_of_opComm and Toy.RA.pathCat_fpUpdate_breaks_left_frame).
  - Does not imply that a is itself valid; if a is invalid and exclusive, fpUpdate R a b holds even without hb, whereas hb is necessary whenever a is valid.
  - Does not imply that b is exclusive or that the update is reversible.
  - Does not generalize to step-indexed validity or OFE cameras without step-indexed exclusivity (✓{0} (a · f) → False).
- **Prior art:**
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.1 EX(X))
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§3.1 p. 19 EXCLUSIVE-UPDATE)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Exclusive Camera, ex-update)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_update_exclusive)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.exclusive)
  - F* standard library FStar.PCM (github.com/FStarLang/FStar, ulib/FStar.PCM.fst at commit 6089523e69201bb5844200c74b1eabfc640f31ab, lines 187-195): unital-PCM special case exclusive_is_frame_preserving (proving only frame_preserving p x p.p.one, an update to the unit, under unital exclusivity where only one composes with x; associated with Swamy et al., SteelCore, PACMPL 4 (ICFP 2020), DOI 10.1145/3409003)
- **Design question:** What abstract property unifies unrestricted updates for exclusive tokens and full fractional permissions, and which RA laws suffice for right-frame preservation?

#### Card 4: `agree_fpUpdate_iff`

- **Lean declaration:** `Toy.RA.agree_fpUpdate_iff` in `lean/Toy/RA/Agree.lean`
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete re-derivation of agreement immutability from Jung et al., JFP 2018 §3.1 p. 18 and Iris `tex/constructions.tex` §Agreement, proved without `[DecidableEq α]`). | `shallow`
- **Plain-language claim:** In the discrete agreement resource algebra agreeRA α (over any type α, without decidable equality), Agree.ag x admits a right-frame-preserving update (fpUpdate) to any carrier target s : Agree α if and only if s = Agree.ag x (with singleton specialization agree_ag_fpUpdate_iff). Because agreeRA α satisfies OpAssoc and OpComm (Toy.RA.agreeRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.agree_fpUpdate_iff` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.agree_fpUpdate_iff {α : Type} (x : α) (s : Agree α) :
    fpUpdate (agreeRA α) (.ag x) s ↔ s = .ag x
-- Unfolded:
--   Agree.ag x = ⟨fun y => y = x, ⟨x, rfl⟩⟩
--   (agreeRA α).op a b = ⟨fun z => a.mem z ∨ b.mem z, ...⟩
--   (agreeRA α).valid a = (∀ u v : α, a.mem u → a.mem v → u = v)
--   (∀ mf : Option (Agree α),
--      (agreeRA α).valid (opOpt (agreeRA α) (Agree.ag x) mf) →
--      (agreeRA α).valid (opOpt (agreeRA α) s mf))
--   ↔ s = Agree.ag x
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.agree_fpUpdate_iff_nonvacuity` — Over α = Bool, agreeRA Bool satisfies IsCoreFreeRA and both Agree.ag false and Agree.ag true are valid.
- **Companion and boundary theorems:** `Toy.RA.agree_ag_fpUpdate_iff` (singleton specialization `ag x ⤳ ag y ↔ x = y`), `Toy.RA.agree_fpUpdateP_imp_mem` (set-valued updates cannot escape agreement).
- **Non-claims:**
  - Does not apply to invalid (multi-element) elements of Agree α, which vacuously admit frame-preserving updates to every element.
  - Set-valued frame-preserving updates do not escape agreement immutability: Toy.RA.agree_fpUpdateP_imp_mem proves that fpUpdateP (agreeRA α) (Agree.ag x) P forces P (Agree.ag x).
  - Does not model step-indexed agreement up to equivalence (≡{n}≡) or OFE non-expansiveness.
  - Does not rule out replacing an agreed value in a compound algebra where the agreement lives inside an exclusive or full-fraction component (such as fracValRA at share 1).
- **Prior art:**
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§3.1 p. 18: 'The agreement RA permits no non-trivial frame-preserving updates')
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Agreement: 'There are no interesting frame-preserving updates for Ag')
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/agree.v (to_agree_op_valid_L, agree_op_inv, agree_idemp)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Agree.lean (toAgree_op_valid_iff_eq, Agree.op_inv)
  - Background only (defines Ag(X) and ag(x)·ag(y) ∈ V ⇒ x = y without an update-characterization theorem): Krebbers, Jung, Bizjak, Jourdan, Dreyer, Birkedal, 'The Essence of Higher-Order Concurrent Separation Logic', ESOP 2017, LNCS 10201, pp. 696-723, DOI 10.1007/978-3-662-54434-1_26 (§4.2, p. 17)
- **Design question:** Which updates are permitted on duplicable agreement resources?

#### Card 5: `agree_distinct_not_fpUpdate`

- **Lean declaration:** `Toy.RA.agree_distinct_not_fpUpdate` in `lean/Toy/RA/Agree.lean`
- **Kind / Tier / Depth:** `impossibility` | `T0` — T0 (impossibility reading of `agree_fpUpdate_iff` exposing the duplicate frame `Agree.ag x` directly in a 3-conjunct statement). | `shallow`
- **Plain-language claim:** [Reference point] In agreeRA α, whenever x ≠ y, the duplicate right frame Agree.ag x composes validly with Agree.ag x and invalidly with Agree.ag y, refuting right-frame preservation fpUpdate (agreeRA α) (Agree.ag x) (Agree.ag y) (ground Bool instance: Toy.RA.agree_naive_update_bool_counterexample). Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.agree_distinct_not_fpUpdate` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Interpreting the algebraic witness frame `Agree.ag x` as 'another thread or client holding a duplicate read-only agreement token' relies on an external separation-logic adequacy bridge linking ghost ownership composition to concurrent executions; inside `Toy.RA`, `Agree.ag x` is purely a universally quantified carrier element.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.agree_distinct_not_fpUpdate {α : Type} {x y : α} (hxy : x ≠ y) :
    (agreeRA α).valid ((agreeRA α).op (.ag x) (.ag x)) ∧
    ¬ (agreeRA α).valid ((agreeRA α).op (.ag y) (.ag x)) ∧
    ¬ fpUpdate (agreeRA α) (.ag x) (.ag y)
-- Unfolded:
--   x ≠ y →
--     (agreeRA α).valid ((agreeRA α).op (Agree.ag x) (Agree.ag x)) ∧
--     ¬ (agreeRA α).valid ((agreeRA α).op (Agree.ag y) (Agree.ag x)) ∧
--     ¬ (∀ mf : Option (Agree α),
--          (agreeRA α).valid (opOpt (agreeRA α) (Agree.ag x) mf) →
--          (agreeRA α).valid (opOpt (agreeRA α) (Agree.ag y) mf))
```
- **Hypothesis ledger:**
  - `hxy` — Ensures the target value y differs from x so that the duplicate frame ag x conflicts with ag y. Tightness: `tight` (`Toy.RA.agree_same_fpUpdate_counterexample`).
- **Non-vacuity witness:** `Toy.RA.agree_distinct_not_fpUpdate_nonvacuity` — Over α = Bool, agreeRA Bool satisfies IsCoreFreeRA and false ≠ true.
- **Positive control:** `Toy.RA.agree_distinct_positive_control_excl` — Replacing duplicable consensus (`agreeRA Bool`) with exclusive ownership (`exclRA Bool`) while keeping `IsCoreFreeRA` and `false ≠ true` makes the value-changing update `Excl.excl false ⤳ Excl.excl true` frame-preserving.
- **Companion and boundary theorems:** `Toy.RA.agree_naive_update_witness_frame`, `Toy.RA.agree_naive_update_bool_counterexample`.
- **Non-claims:**
  - The duplicate frame ag x is a hypothetical frame. The theorem does not assert that any party holds it.
  - Immutability is relative to agreeRA alone; the same value placed under an exclusive, full-fraction, or authoritative construction can be changed (as shown by the positive control Toy.RA.agree_distinct_positive_control_excl and Toy.RA.fracVal_full_fpUpdate).
  - Set-valued updates do not escape: ag x ⤳: P already requires P (ag x) (Toy.RA.agree_fpUpdateP_imp_mem).
  - Does not establish immutability of an invalid agreement element containing multiple distinct values, and does not model step-indexed agreement where two values may agree at index n while differing globally.
  - Derived (modeling bridge): interpreting the hypothetical frame ag x as 'another thread holding a duplicate copy' relies on an external separation-logic soundness theorem connecting ghost ownership composition to operational thread safety; no program logic or thread semantics is formalized here.
- **Prior art:**
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§3.1 p. 18)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Agreement)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/agree.v (to_agree_op_valid_L, agree_op_inv, agree_idemp)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Agree.lean
- **Design question:** Reference point (impossibility reading of agree_fpUpdate_iff): why does a naive mutation of an agreed value fail frame preservation against duplicate copies (which, under a modeling bridge, represent concurrent observers)?

#### Card 6: `fracVal_full_fpUpdate_iff`

- **Lean declaration:** `Toy.RA.fracVal_full_fpUpdate_iff` in `lean/Toy/RA/Frac.lean`
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete re-derivation of full-share updates in `FRAC(X)` from Jung et al., POPL 2015 §3.2 and `pair-frac-change` / `to_dfrac_agree_exclusive` in Iris and `iris-lean`). | `shallow`
- **Plain-language claim:** In the fractional-value algebra fracValRA α = prodRA fracRA (agreeRA α), a full share fracVal PosRat.one x admits a right-frame-preserving update (fpUpdate) to any carrier target (q', s) : PosRat × Agree α if and only if q' ≤ 1 and s = Agree.ag y for some y : α (with singleton specialization fracVal_full_ag_fpUpdate_iff). Because fracValRA α satisfies OpAssoc and OpComm (Toy.RA.fracValRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fracVal_full_fpUpdate_iff` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Interpreting share `PosRat.one` in `fracValRA α` as 'unique write permission after collecting all read shares' depends on an external program-logic points-to interpretation tying heap mutation rules to frame-preserving updates on `fracValRA α`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fracVal_full_fpUpdate_iff {α : Type} (x : α) (q' : PosRat) (s : Agree α) :
    fpUpdate (fracValRA α) (fracVal PosRat.one x) (q', s) ↔
      PosRat.le q' PosRat.one ∧ ∃ y : α, s = .ag y
-- Unfolded:
--   fracValRA α = prodRA fracRA (agreeRA α)
--   fracVal PosRat.one x = (PosRat.one, Agree.ag x)
--   (fracValRA α).valid (q, a) = (PosRat.le q PosRat.one ∧ (agreeRA α).valid a)
--   fpUpdate (prodRA fracRA (agreeRA α)) (PosRat.one, Agree.ag x) (q', s) ↔
--     PosRat.le q' PosRat.one ∧ ∃ y : α, s = Agree.ag y
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.fracVal_full_fpUpdate_iff_nonvacuity` — Over α = Bool, fracValRA Bool satisfies IsCoreFreeRA and both fracVal PosRat.one false and fracVal PosRat.one true are valid.
- **Companion and boundary theorems:** `Toy.RA.fracVal_full_ag_fpUpdate_iff`, `Toy.RA.fracVal_full_fpUpdate`, `Toy.RA.fracVal_recombine_fpUpdate`.
- **Non-claims:**
  - Does not allow updating a full share to an over-full invalid share q' > 1 or to a non-singleton invalid agreement element.
  - Does not cover discardable/persistent fractions (Iris's DFracDiscarded) or fractional unpersisting updates.
  - Does not cover step-indexed OFEs or non-expansiveness.
  - Derived (modeling bridge): interpreting share 1 as 'exclusive write permission over a shared-read resource' assumes an external program-logic interpretation of fracValRA ownership assertions.
- **Prior art:**
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.2, p. 5 FRAC(X) and '(1, x) ⇝ ...')
  - Bornat, Calcagno, O'Hearn, Parkinson, 'Permission accounting in separation logic', POPL 2005, pp. 259-270, DOI 10.1145/1040305.1040327 (fractional/counting permissions for read vs. write/dispose)
  - Boyland, 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, DOI 10.1007/3-540-44898-5_4 (conceptual origin of fractional read/write permissions)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Fractions, pair-frac-change '(1, a) ⤳ (1, b)')
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/frac.v (frac_full_exclusive) and iris/algebra/lib/dfrac_agree.v (dfrac_agreeR at DfracOwn via to_frac_agree, to_dfrac_agree_exclusive, frac_agree_update_2)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Frac.lean (instExclusiveQp1) and Iris/Iris/Algebra/Lib/DFracAgree.lean (DFracAgree.mk_exclusive, Frac.update₂)
  - Background only (tree-share separation algebras without frame-preserving updates): Dockins, Hobor, Appel, 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, DOI 10.1007/978-3-642-10672-9_13
- **Design question:** Why does full fractional ownership (q = 1) permit arbitrary updates to valid targets over the carried agreement value?

#### Card 7: `fracVal_partial_fpUpdate_iff`

- **Lean declaration:** `Toy.RA.fracVal_partial_fpUpdate_iff` in `lean/Toy/RA/Frac.lean`
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete characterization of partial-share updates in `FRAC(X)` from Jung et al., POPL 2015 §3.2 and `dfrac_agreeR` at `DfracOwn` in Iris and `iris-lean`). | `shallow`
- **Plain-language claim:** In fracValRA α, whenever q < 1 (PosRat.lt q PosRat.one), a partial share fracVal q x admits a right-frame-preserving update (fpUpdate) to any carrier target (q', s) : PosRat × Agree α if and only if q' ≤ q and s = Agree.ag x (with singleton specialization fracVal_partial_ag_fpUpdate_iff). Because fracValRA α satisfies OpAssoc and OpComm (Toy.RA.fracValRA_isCoreFreeRA), right-frame preservation here is equivalent to simultaneous two-sided frame preservation (Toy.RA.fpUpdate2_of_assoc_comm; the converse direction takes the empty left frame ml = none).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fracVal_partial_fpUpdate_iff` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fracVal_partial_fpUpdate_iff {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) (x : α) (s : Agree α) :
    fpUpdate (fracValRA α) (fracVal q x) (q', s) ↔
      PosRat.le q' q ∧ s = .ag x
-- Unfolded:
--   PosRat.lt q PosRat.one →
--     (fpUpdate (prodRA fracRA (agreeRA α)) (q, Agree.ag x) (q', s) ↔
--       PosRat.le q' q ∧ s = Agree.ag x)
```
- **Hypothesis ledger:**
  - `hq` — Ensures q is strictly below 1 so the source is valid and admits a positive complementary frame 1 - q that detects both value changes and share increases. Tightness: `tight` (`Toy.RA.fracVal_partial_iff_full_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fracVal_partial_fpUpdate_iff_nonvacuity` — Over α = Bool, fracValRA Bool satisfies IsCoreFreeRA and PosRat.half < PosRat.one.
- **Companion and boundary theorems:** `Toy.RA.fracVal_partial_ag_fpUpdate_iff`, `Toy.RA.fracVal_partial_iff_overfull_counterexample` (over-full `q = 2` vacuity trap).
- **Non-claims:**
  - Does not hold when q = 1 (full share allows arbitrary value change; Toy.RA.fracVal_partial_iff_full_counterexample) or when q > 1 (invalid over-full share vacuously updates to any value; Toy.RA.fracVal_partial_iff_overfull_counterexample).
  - Does not forbid decreasing a partial share (q' < q) while keeping x unchanged.
  - Does not model discardable fractions (DFracDiscarded), step-indexed cameras, or share-tree models (such as Dockins-Hobor-Appel binary tree shares), which differ in algebraic structure from ℚ_{>0}.
- **Prior art:**
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.2, p. 5 FRAC(X))
  - Bornat et al., 'Permission accounting in separation logic', POPL 2005, pp. 259-270, DOI 10.1145/1040305.1040327
  - Boyland, 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, DOI 10.1007/3-540-44898-5_4
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Fractions)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/frac.v and iris/algebra/lib/dfrac_agree.v (dfrac_agreeR at DfracOwn)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Frac.lean and Iris/Iris/Algebra/Lib/DFracAgree.lean
  - Background only (tree-share separation algebras without frame-preserving updates): Dockins, Hobor, Appel, APLAS 2009, LNCS 5904, pp. 161-177, DOI 10.1007/978-3-642-10672-9_13
- **Design question:** What exact updates are allowed or forbidden when a client holds only a partial fractional share?

#### Card 8: `fracVal_partial_value_change_impossible`

- **Lean declaration:** `Toy.RA.fracVal_partial_value_change_impossible` in `lean/Toy/RA/Frac.lean`
- **Kind / Tier / Depth:** `impossibility` | `T0` — T0 (impossibility reading of `fracVal_partial_fpUpdate_iff` paired with the explicit complementary-share witness `Toy.RA.fracVal_partial_complement_observes_change`). | `shallow`
- **Plain-language claim:** [Reference point] In fracValRA α, whenever q < 1 (PosRat.lt q PosRat.one) and x ≠ y, no update from fracVal q x to fracVal q' y (for any q' : PosRat) is right-frame-preserving (fpUpdate); an explicit witness right frame (1 - q, ag x) is given by the companion theorem Toy.RA.fracVal_partial_complement_observes_change. Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fracVal_partial_value_change_impossible` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Interpreting the complementary share `fracValComplement q hq x = (1 - q, Agree.ag x)` as 'concurrent readers holding the remaining permission' relies on an external separation-logic soundness theorem; algebraically, the theorem proves only that the hypothetical frame `(1 - q, Agree.ag x)` is compatible with `(q, Agree.ag x)` and incompatible with `(q', Agree.ag y)`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fracVal_partial_value_change_impossible {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) {x y : α} (hxy : x ≠ y) :
    ¬ fpUpdate (fracValRA α) (fracVal q x) (fracVal q' y)
-- Unfolded:
--   PosRat.lt q PosRat.one → x ≠ y →
--     ¬ (∀ mf : Option (PosRat × Agree α),
--          (prodRA fracRA (agreeRA α)).valid (opOpt (fracValRA α) (q, Agree.ag x) mf) →
--          (prodRA fracRA (agreeRA α)).valid (opOpt (fracValRA α) (q', Agree.ag y) mf))
```
- **Hypothesis ledger:**
  - `hq` — Guarantees q is a strictly partial valid share so the positive complement 1 - q exists; fails both at q = 1 (full write ownership) and at q > 1 (invalid source). Tightness: `tight` (`Toy.RA.fracVal_full_value_change_control`).
  - `hxy` — Ensures the target value differs from x; keeping x unchanged with q' ≤ q is frame-preserving. Tightness: `tight` (`Toy.RA.fracVal_partial_same_value_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fracVal_partial_value_change_impossible_nonvacuity` — Over α = Bool, fracValRA Bool satisfies IsCoreFreeRA, PosRat.half < PosRat.one, and false ≠ true.
- **Positive control:** `Toy.RA.fracVal_full_value_change_control` — Upgrading the partial share `q < 1` to the full share `q = PosRat.one` in `fracValRA Bool` while keeping `false ≠ true` makes `fracVal PosRat.one false ⤳ fracVal PosRat.one true` frame-preserving.
- **Companion and boundary theorems:** `Toy.RA.fracVal_partial_complement_observes_change` (exposes witness frame `fracValComplement q hq x`).
- **Non-claims:**
  - The complementary frame (1 - q, ag x) is hypothetical; nothing asserts that any party holds it. Escape hatches: q = 1 (full share), q > 1 (invalid source, vacuous), x = y, recombining shares that sum to 1 (Toy.RA.fracVal_recombine_fpUpdate), or placing the value in a different construction.
  - Does not prevent shrinking the share q' ≤ q while preserving x.
  - Does not cover discardable fractions or step-indexed cameras.
  - Derived (modeling bridge): interpreting the hypothetical complementary frame (1 - q, ag x) as 'concurrent readers holding the remaining fraction' depends on an external separation-logic adequacy bridge; no thread semantics or heap points-to connective is formalized.
- **Prior art:**
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.2 FRAC(X))
  - Bornat et al., 'Permission accounting in separation logic', POPL 2005, pp. 259-270, DOI 10.1145/1040305.1040327
  - Boyland, 'Checking Interference with Fractional Permissions', SAS 2003, LNCS 2694, pp. 55-72, DOI 10.1007/3-540-44898-5_4
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/frac.v and iris/algebra/lib/dfrac_agree.v
- **Design question:** Reference point (impossibility reading of fracVal_partial_fpUpdate_iff): why does mutating a value under a partial fraction break compatibility with the complementary share (and, under a modeling bridge, concurrent readers)?

#### Card 9: `auth_both_fpUpdate_iff`

- **Lean declaration:** `Toy.RA.auth_both_fpUpdate_iff` in `lean/Toy/RA/Auth.lean` (additional hashed theorems in `lean_names`: `Toy.RA.auth_opComm_alone_not_two_sided`, `Toy.RA.opComm_alone_not_two_sided`, `Toy.RA.fpUpdate2_of_assoc_comm`)
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete counterpart of `iris-lean`'s `auth_update_ord` in `Iris/Iris/Algebra/Auth.lean` lines 536–542, which states the sufficiency direction; the converse follows directly by instantiating optional fragment frames). | `shallow`
- **Plain-language claim:** For any raw resource algebra R : RawRA α (requiring zero algebraic laws on R), authElem a · fragElem b admits a right-frame-preserving update to authElem a' · fragElem b' in authRA R if and only if for every optional external fragment frame mbf : Option α, R.valid a ∧ (b ·? mbf) ≼? a implies R.valid a' ∧ (b' ·? mbf) ≼? a'.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.auth_both_fpUpdate_iff` (axioms: `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.auth_both_fpUpdate_iff {α : Type} (R : RawRA α) (a b a' b' : α) :
    fpUpdate (authRA R) ((authRA R).op (authElem a) (fragElem b))
                        ((authRA R).op (authElem a') (fragElem b')) ↔
      ∀ mbf : Option α, R.valid a ∧ includedRefl R (opOpt R b mbf) a →
        R.valid a' ∧ includedRefl R (opOpt R b' mbf) a'
-- Unfolded:
--   (authRA R).op (authElem a) (fragElem b) = ⟨AuthPart.excl a, some b⟩
--   (authRA R).valid ⟨AuthPart.excl a, some c⟩ = (R.valid a ∧ ∃ mc : Option α, opOpt R c mc = a)
--   Right-hand side:
--     ∀ mbf : Option α,
--       (R.valid a ∧ ∃ mc : Option α, opOpt R (opOpt R b mbf) mc = a) →
--       (R.valid a' ∧ ∃ mc' : Option α, opOpt R (opOpt R b' mbf) mc' = a')
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.auth_both_fpUpdate_iff_nonvacuity` — In authRA counterRA, IsCoreFreeRA holds, auth 2 · frag 1 is valid, and (2, 1) → (3, 1) satisfies the exact frame-inclusion condition even though ¬ LocalUpdate counterRA 2 1 3 1.
- **Companion and boundary theorems:** `Toy.RA.auth_opComm_alone_not_two_sided` (simultaneous two-sided fragment failure in `authRA nonAssocCommValidRA` under `OpComm` without `OpAssoc`), `Toy.RA.opComm_alone_not_two_sided`, `Toy.RA.fpUpdate2_of_assoc_comm`, `Toy.RA.auth_pathCat_localUpdate_breaks_left_frame`.
- **Non-claims:**
  - Quantifies over right-composed frames only; without OpComm R, left-composed fragment frames need not be preserved (Toy.RA.auth_pathCat_localUpdate_breaks_left_frame). Under OpComm R, which lifts to OpComm (authRA R) (Toy.RA.authRA_opComm), right-frame preservation also preserves each single left-composed frame (f · x; Toy.RA.fpUpdate_preserve_left_of_opComm applied to authRA R). Simultaneous two-sided contexts l · (x · r) are preserved under OpComm R ∧ OpAssoc R (both laws lift to authRA R by Toy.RA.authRA_opComm and Toy.RA.authRA_opAssoc, and Toy.RA.fpUpdate2_of_assoc_comm then applies to authRA R), not under OpComm R alone (counterexamples: Toy.RA.auth_opComm_alone_not_two_sided in authRA nonAssocCommValidRA, and Toy.RA.opComm_alone_not_two_sided in the base algebra).
  - Does not require checking a single concrete remainder (as LocalUpdate does); instead, each external fragment frame mbf may witness inclusion in a' differently.
  - Does not cover fractional/persistent authoritative tokens (●{dq} a) or step-indexed view cameras.
- **Prior art:**
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Auth.lean (auth_update_ord, lines 536-542, stating the sufficiency direction; the converse follows directly by instantiating optional fragment frames)
  - Background: Jung et al., POPL 2015 §3.6 (AUTH); Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/auth.v (auth_both_valid_discrete)
- **Design question:** What exact, law-free condition on external fragment frames characterizes right-frame-preserving updates of authElem a · fragElem b in authRA R?

#### Card 10: `auth_localUpdate_fpUpdate`

- **Lean declaration:** `Toy.RA.auth_localUpdate_fpUpdate` in `lean/Toy/RA/Auth.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (discrete re-derivation of Iris's `auth_update` in `iris/algebra/auth.v` lines 321–327 instantiated via `optionUR` and `option_local_update`, using only `OpAssoc R` for right-composed frames). | `shallow`
- **Plain-language claim:** For any associative raw resource algebra R : RawRA α (OpAssoc R) — without requiring ValidOpL or a unit in R — if (a, b) admits a local update to (a', b') (LocalUpdate R a b a' b'), then authElem a · fragElem b admits a right-frame-preserving update (fpUpdate (authRA R)) to authElem a' · fragElem b' (which also preserves simultaneous two-sided frames when OpComm R holds alongside OpAssoc R: both laws lift to authRA R by Toy.RA.authRA_opComm and Toy.RA.authRA_opAssoc, and Toy.RA.fpUpdate2_of_assoc_comm then applies to authRA R).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.auth_localUpdate_fpUpdate` (axioms: `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.auth_localUpdate_fpUpdate {α : Type} (R : RawRA α) (hAssoc : OpAssoc R)
    (a b a' b' : α) (hLoc : LocalUpdate R a b a' b') :
    fpUpdate (authRA R) ((authRA R).op (authElem a) (fragElem b))
                        ((authRA R).op (authElem a') (fragElem b'))
-- Unfolded:
--   (∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)) →
--   (∀ mz : Option α, R.valid a → opOpt R b mz = a → R.valid a' ∧ opOpt R b' mz = a') →
--   fpUpdate (authRA R) ⟨AuthPart.excl a, some b⟩ ⟨AuthPart.excl a', some b'⟩
```
- **Hypothesis ledger:**
  - `hAssoc` — Reassociates (b · bf) · c into b · (bf · c) so LocalUpdate reduces to the exact frame-inclusion condition of Toy.RA.auth_both_fpUpdate_iff; OpAssoc is needed for this reduction from LocalUpdate rather than for authoritative updates themselves. Tightness: `tight` (`Toy.RA.auth_localUpdate_nonAssoc_counterexample`).
  - `hLoc` — Ensures every valid decomposition of a into b plus a remainder preserves validity and the same remainder when moving to (a', b'). Tightness: `tight` (`Toy.RA.auth_counter_dec_auth_only_fails`).
- **Non-vacuity witness:** `Toy.RA.auth_localUpdate_fpUpdate_nonvacuity` — Over counterRA (Nat with +), OpAssoc holds, LocalUpdate counterRA 2 1 3 2 holds, and auth 2 · frag 1 is valid in authRA counterRA.
- **Companion and boundary theorems:** `Toy.RA.auth_both_fpUpdate_iff`, `Toy.RA.auth_counter_alloc_only_not_localUpdate` (shows `LocalUpdate` is not necessary), `Toy.RA.auth_pathCat_localUpdate_breaks_left_frame`.
- **Non-claims:**
  - Without OpComm, the conclusion protects only right-composed frames. Over the associative, non-commutative pathCatRA, the local update (ff, ff) → (tf, tf) lifts to a right-frame fpUpdate in authRA pathCatRA, but the left-composed fragment frame fragElem ff is invalidated (Toy.RA.auth_pathCat_localUpdate_breaks_left_frame).
  - LocalUpdate is one sufficient condition. The exact condition is law-free: auth a · frag b ⤳ auth a' · frag b' iff for every optional fragment frame mbf, valid a ∧ (b ·? mbf) ≼? a implies valid a' ∧ (b' ·? mbf) ≼? a' (Toy.RA.auth_both_fpUpdate_iff, cf. iris-lean auth_update_ord). OpAssoc is needed only to derive this from LocalUpdate. Concrete counterexample: Toy.RA.auth_counter_alloc_only_not_localUpdate.
  - 'No unit in R' does not generalize Iris. Iris obtains the same statement by instantiating auth at optionUR R and using option_local_update.
  - Does not establish that authRA R satisfies OpComm or ValidOpL unless R also satisfies OpComm and ValidOpL.
  - Does not cover fractional or persistent authoritative tokens (Iris's ●{dq} a) or step-indexed view cameras.
- **Prior art:**
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/constructions.tex (§Authoritative, local update definition and auth-update rule)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/auth.v (auth_update, lines 321-327, using only assoc) and iris/algebra/local_updates.v (local_update, option_local_update, lines 191-200)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Auth.lean (auth_update, lines 566-567; auth_update_ord, lines 536-542) and Iris/Iris/Algebra/LocalUpdates.lean (LocalUpdate.option)
  - Jung et al., 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning', POPL 2015, pp. 637-650, DOI 10.1145/2676726.2676980 (§3.6 AUTH and AUTHUPD over cancellative monoids, predecessor to local updates)
  - Background only (defines Auth(M) over a uRA with heap-specific updates, without general local_update / auth_update): Krebbers et al., ESOP 2017, LNCS 10201, pp. 696-723, DOI 10.1007/978-3-662-54434-1_26 (§3.3, p. 14); Jung et al., JFP 28 (2018), e20 (§6.3.3, p. 49, which defers generic updates to appendix and Coq)
- **Design question:** What sufficient local-update condition justifies synchronized authoritative/fragment updates, and which base-algebra laws does lifting it to right-frame preservation require?

#### Card 11: `auth_counter_inc_fpUpdate`

- **Lean declaration:** `Toy.RA.auth_counter_inc_fpUpdate` in `lean/Toy/RA/Auth.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (standard concrete authoritative counter increment instance of Iris's `auth_update` + `op_local_update_discrete` over `(Nat, +)`). | `shallow`
- **Plain-language claim:** In authRA counterRA (where auth a · frag b is valid iff b ≤ a), incrementing both the authoritative counter and an owned fragment by any k : Nat yields a right-frame-preserving update (fpUpdate (authRA counterRA)) authElem a · fragElem b ⤳ authElem (a + k) · fragElem (b + k) (backed by Toy.RA.counter_inc_localUpdate). Because counterRA satisfies OpAssoc and OpComm and these lift to authRA counterRA (Toy.RA.counterRA_isCoreFreeRA, Toy.RA.authRA_isCoreFreeRA), the update also preserves simultaneous two-sided frames (Toy.RA.fpUpdate2_of_assoc_comm).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.auth_counter_inc_fpUpdate` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Interpreting compatibility with every optional fragment frame `mbf` as 'monotonically advancing shared state without invalidating concurrent threads' fragment invariants' requires an external program-logic invariant and update-modality soundness theorem.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.auth_counter_inc_fpUpdate (a b k : Nat) :
    fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem a) (fragElem b))
      ((authRA counterRA).op (authElem (a + k)) (fragElem (b + k)))
-- Unfolded:
--   counterRA = natAddRA = ⟨Nat.add, fun _ => True⟩
--   (authRA counterRA).valid ((authRA counterRA).op (authElem a) (fragElem b)) ↔ b ≤ a
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.auth_counter_inc_fpUpdate_nonvacuity` — authRA counterRA satisfies IsCoreFreeRA, auth 2 · frag 1 is valid, and counter_inc_localUpdate 2 1 3 holds.
- **Companion and boundary theorems:** `Toy.RA.counter_inc_localUpdate`, `Toy.RA.counter_dec_both_localUpdate`, `Toy.RA.auth_counter_inc_frag_only_fails`.
- **Non-claims:**
  - Does not justify incrementing only the fragment without owning the authoritative snapshot (refuted by Toy.RA.auth_counter_inc_frag_only_fails).
  - Does not justify decrementing the authoritative counter without decrementing the owned fragment by the same amount: auth 2 · frag 1 ⤳ auth 1 · frag 1 fails (Toy.RA.auth_counter_dec_auth_only_fails), whereas (2, 1) → (1, 0) is a local update (Toy.RA.counter_dec_both_localUpdate).
  - Models an unbounded Nat counter; does not account for fixed-width integer overflow or wrap-around.
  - Derived (modeling bridge): interpreting compatibility with all fragment frames as 'without invalidating external fragment holders' relies on an external separation-logic soundness bridge; no concurrent protocol or thread semantics is formalized.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/auth.v and iris/algebra/local_updates.v (op_local_update_discrete)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Auth.lean and Iris/Iris/Algebra/LocalUpdates.lean
  - Background: Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§6.3.3)
- **Design question:** How does a concrete authoritative/fragment protocol preserve compatibility across all fragment frames during coordinated state growth?

#### Card 12: `auth_counter_dec_auth_only_fails`

- **Lean declaration:** `Toy.RA.auth_counter_dec_auth_only_fails` in `lean/Toy/RA/Auth.lean`
- **Kind / Tier / Depth:** `counterexample` | `T0` — T0 (canonical concrete counterexample showing why local fragment inclusion `1 ≤ 1` does not suffice when an external fragment frame `fragElem 1` is present). | `shallow`
- **Plain-language claim:** In counterRA (which satisfies OpAssoc, OpComm, and ValidOpL, lifted to authRA counterRA by Toy.RA.authRA_isCoreFreeRA), decrementing the authoritative counter from 2 to 1 while retaining fragment 1 violates LocalUpdate and breaks compatibility with the right frame fragElem 1, so the right-frame-preserving update (fpUpdate) auth 2 · frag 1 ⤳ auth 1 · frag 1 fails. Since simultaneous two-sided frame preservation with the empty left frame ml = none is right-frame preservation, the update is not two-sided frame-preserving either.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.auth_counter_dec_auth_only_fails` (axioms: `Quot.sound`, `propext`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Modeling bridge:** `Basis: derived (modeling bridge)` — Reading the conflicting frame `fragElem 1` as 'another thread's contributed count' is a modeling bridge through an external separation logic; the Lean theorem establishes the discrete algebraic validity failure `(1 + 1 ≤ 2)` vs. `¬ (1 + 1 ≤ 1)`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.auth_counter_dec_auth_only_fails :
    OpAssoc counterRA ∧ OpComm counterRA ∧ ValidOpL counterRA ∧
    ¬ LocalUpdate counterRA 2 1 1 1 ∧
    (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 2) (fragElem 1)) (fragElem 1)) ∧
    ¬ (authRA counterRA).valid
      ((authRA counterRA).op ((authRA counterRA).op (authElem 1) (fragElem 1)) (fragElem 1)) ∧
    ¬ fpUpdate (authRA counterRA)
      ((authRA counterRA).op (authElem 2) (fragElem 1))
      ((authRA counterRA).op (authElem 1) (fragElem 1))
```
- **Hypothesis ledger:** None beyond type/element parameters (no algebraic-law or side-condition hypotheses).
- **Non-vacuity witness:** `Toy.RA.auth_counter_dec_auth_only_fails` — Self-contained ground counterexample on counterRA and authRA counterRA with explicit witness frame fragElem 1.
- **Companion and boundary theorems:** `Toy.RA.counter_dec_both_localUpdate` (matched decrement `(2, 1) → (1, 0)` succeeds), `Toy.RA.auth_counter_alloc_only_not_localUpdate`.
- **Non-claims:**
  - Does not rule out decrementing both auth and frag simultaneously when the owned fragment covers the decrement (Toy.RA.counter_dec_both_localUpdate proves LocalUpdate counterRA 2 1 1 0).
  - Does not imply every non-LocalUpdate fails to be frame-preserving in authRA counterRA (see Toy.RA.auth_counter_alloc_only_not_localUpdate).
  - Derived (modeling bridge): reading the witness frame fragElem 1 as 'another thread's fragment invariant' relies on an external program-logic interpretation; only the discrete algebraic validity failure is proved.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/auth.v
  - Background: Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§6.3.3)
- **Design question:** Which naive authoritative updates break external fragment-frame compatibility even when the locally held fragment remains ≤ the new authoritative value?

#### Card 13: `fpUpdate_frame_right`

- **Lean declaration:** `Toy.RA.fpUpdate_frame_right` in `lean/Toy/RA/Laws.lean` (additional hashed theorems in `lean_names`: `Toy.RA.opComm_alone_not_two_sided`, `Toy.RA.fpUpdate2_of_assoc_comm`)
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (discrete right-framing specialization of Iris's `cmra_update_op` and `Iris.Update.op`, isolating `OpAssoc` as the sole law needed for right-composed frames; cf. `FStar.PCM.frame_preserving_subframe` in unital PCMs). | `shallow`
- **Plain-language claim:** In any associative raw resource algebra R : RawRA α (OpAssoc R) — with neither OpComm nor ValidOpL needed — a right-frame-preserving update a ⤳ b implies the right-framed update a · c ⤳ b · c for every c : α.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdate_frame_right` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdate_frame_right {α : Type} (R : RawRA α) (hAssoc : OpAssoc R)
    {a b : α} (c : α) (hab : fpUpdate R a b) :
    fpUpdate R (R.op a c) (R.op b c)
-- Unfolded:
--   (∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)) →
--   (∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)) →
--   (∀ mf : Option α, R.valid (opOpt R (R.op a c) mf) → R.valid (opOpt R (R.op b c) mf))
```
- **Hypothesis ledger:**
  - `hAssoc` — Reassociates (a · c) · f to a · (c · f) and back to (b · c) · f so the frame c · f can be passed to hab. Tightness: `tight` (`Toy.RA.fpUpdate_frame_right_nonAssoc_counterexample`).
  - `hab` — Supplies the underlying right-frame-preserving update from a to b. Tightness: `tight` (`Toy.RA.fpUpdate_frame_right_noUpdate_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdate_frame_right_nonvacuity` — In authRA counterRA (where validity is selective and frag 1 ⤳ frag 2 fails), OpAssoc holds, auth 2 · frag 1 ⤳ auth 3 · frag 2 holds, and right-framing with frag 1 keeps the source valid.
- **Companion and boundary theorems:** `Toy.RA.opComm_alone_not_two_sided`, `Toy.RA.fpUpdate2_of_assoc_comm`, `Toy.RA.pathCat_fpUpdate_breaks_left_frame`, `Toy.RA.frame_right_holds_without_opAssoc_example`.
- **Non-claims:**
  - Does not establish left-framing (c · a ⤳ c · b) or left-frame protection without OpComm; the asymmetry comes from defining fpUpdate via right-composed frames opOpt R a mf (witnessed by Toy.RA.pathCat_fpUpdate_breaks_left_frame). Under OpComm alone, right-frame preservation also preserves each single left-composed frame (f · a; Toy.RA.fpUpdate_preserve_left_of_opComm), whereas simultaneous two-sided contexts l · (a · r) require both OpComm and OpAssoc (Toy.RA.fpUpdate2_of_assoc_comm; refuted under OpComm alone by Toy.RA.opComm_alone_not_two_sided).
  - Does not show that OpAssoc is globally necessary for right-framing: in any algebra where every element is valid (such as natSubRA, Toy.RA.frame_right_holds_without_opAssoc_example), universal right-framing holds without OpAssoc. Tightness shows only that OpAssoc cannot be dropped from this general statement.
  - Does not require or establish that a, b, or c are valid elements.
  - Discrete only: does not cover step-indexed CMRAs, OFE non-expansiveness, or operational program-logic frame rules without a modeling bridge.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_update_op, lines 93-96, derived from cmra_updateP_op using only assoc and comm)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.op)
  - F* standard library FStar.PCM (github.com/FStarLang/FStar, ulib/FStar.PCM.fst at commit 6089523e69201bb5844200c74b1eabfc640f31ab): frame_preserving_subframe (unital PCM analogue of framing an update)
  - Background only (separation algebras with frame property for local actions, without resource frame-preserving updates): Calcagno, O'Hearn, Yang, 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, DOI 10.1109/LICS.2007.30; Jung et al., JFP 28 (2018), e20 (§2.1)
- **Design question:** Which algebraic law suffices to frame a right-frame-preserving update by a sibling resource on the right?

#### Card 14: `fpUpdate_op`

- **Lean declaration:** `Toy.RA.fpUpdate_op` in `lean/Toy/RA/Laws.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (discrete re-derivation of Iris's `cmra_update_op` in `iris/algebra/updates.v` lines 93–96 and `Iris.Update.op`, using only `OpAssoc` and `OpComm`). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α satisfying associativity (OpAssoc R) and commutativity (OpComm R) — without requiring ValidOpL — deterministic right-frame-preserving updates (fpUpdate) compose in parallel: a₁ ⤳ b₁ and a₂ ⤳ b₂ imply a₁ · a₂ ⤳ b₁ · b₂. Under the same two laws, the composite update also preserves simultaneous two-sided frames (Toy.RA.fpUpdate2_of_assoc_comm).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdate_op` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdate_op {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) (hComm : OpComm R)
    {a₁ b₁ a₂ b₂ : α}
    (h₁ : fpUpdate R a₁ b₁) (h₂ : fpUpdate R a₂ b₂) :
    fpUpdate R (R.op a₁ a₂) (R.op b₁ b₂)
-- Unfolded:
--   (∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)) →
--   (∀ x y : α, R.op x y = R.op y x) →
--   fpUpdate R a₁ b₁ → fpUpdate R a₂ b₂ →
--   (∀ mf : Option α,
--      R.valid (opOpt R (R.op a₁ a₂) mf) → R.valid (opOpt R (R.op b₁ b₂) mf))
```
- **Hypothesis ledger:**
  - `hAssoc` — Reassociates nested frames around a₁ · a₂ during both update steps. Tightness: `tight` (`Toy.RA.fpUpdate_op_nonAssoc_counterexample`).
  - `hComm` — Moves a₂ to the left of b₁ so the right-framed update h₂ applies to a₂. Tightness: `tight` (`Toy.RA.fpUpdate_op_nonComm_counterexample`).
  - `h₁` — Supplies the left-component frame-preserving update a₁ ⤳ b₁. Tightness: `tight` (`Toy.RA.fpUpdate_op_noUpdate1_counterexample`).
  - `h₂` — Supplies the right-component frame-preserving update a₂ ⤳ b₂. Tightness: `tight` (`Toy.RA.fpUpdate_op_noUpdate2_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdate_op_nonvacuity` — In authRA counterRA, OpAssoc and OpComm hold, auth 2 · frag 1 ⤳ auth 3 · frag 2 holds, frag 1 ⤳ frag 1 holds, their composition with frame frag 1 is valid, and frag 1 ⤳ frag 2 fails.
- **Companion and boundary theorems:** `Toy.RA.fpUpdate_trans` (law-free sequential composition).
- **Non-claims:**
  - Does not show that OpAssoc and OpComm are globally necessary for parallel composition: in universally valid algebras, parallel composition holds without OpComm (boolLeftProjRA) or without either law (natSubRA) (derived: every element of these algebras is valid, so fpUpdate holds for all pairs; no separate Lean declaration is given). Tightness shows only that neither hypothesis can be deleted from this general statement.
  - May fail without OpComm (e.g., in pathCatRA, Toy.RA.fpUpdate_op_nonComm_counterexample).
  - Does not apply to sequential composition (Toy.RA.fpUpdate_trans), which requires zero algebraic laws on R.
  - Does not require or imply ValidOpL, and covers only discrete algebras without step-indexing or OFE metrics.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_update_op, lines 93-96, proved via cmra_updateP_op using only assoc and comm)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.op)
  - Background only (separation algebras with local actions, without resource frame-preserving updates): Calcagno, O'Hearn, Yang, LICS 2007, pp. 366-378, DOI 10.1109/LICS.2007.30; Jung et al., JFP 28 (2018), e20 (§2.1)
- **Design question:** Which RA laws suffice to compose two independent frame-preserving updates in parallel?

#### Card 15: `fpUpdateP_op`

- **Lean declaration:** `Toy.RA.fpUpdateP_op` in `lean/Toy/RA/Laws.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (discrete re-derivation of Iris's `cmra_updateP_op` in `iris/algebra/updates.v` lines 78–88 and `Iris.UpdateP.op`, using only `OpAssoc` and `OpComm`). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α satisfying OpAssoc R and OpComm R (without ValidOpL), non-deterministic right-frame-preserving updates (fpUpdateP) a₁ ⤳: P₁ and a₂ ⤳: P₂ compose into a₁ · a₂ ⤳: Q whenever P₁ b₁ and P₂ b₂ imply Q (b₁ · b₂). No two-sided variant of fpUpdateP is defined in this package.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdateP_op` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdateP_op {α : Type} (R : RawRA α) (hAssoc : OpAssoc R) (hComm : OpComm R)
    {a₁ a₂ : α} {P₁ P₂ Q : α → Prop}
    (h₁ : fpUpdateP R a₁ P₁) (h₂ : fpUpdateP R a₂ P₂)
    (hQ : ∀ b₁ b₂, P₁ b₁ → P₂ b₂ → Q (R.op b₁ b₂)) :
    fpUpdateP R (R.op a₁ a₂) Q
-- Unfolded:
--   OpAssoc R → OpComm R →
--   (∀ mf : Option α, R.valid (opOpt R a₁ mf) → ∃ b₁, P₁ b₁ ∧ R.valid (opOpt R b₁ mf)) →
--   (∀ mf : Option α, R.valid (opOpt R a₂ mf) → ∃ b₂, P₂ b₂ ∧ R.valid (opOpt R b₂ mf)) →
--   (∀ b₁ b₂, P₁ b₁ → P₂ b₂ → Q (R.op b₁ b₂)) →
--   (∀ mf : Option α, R.valid (opOpt R (R.op a₁ a₂) mf) → ∃ b, Q b ∧ R.valid (opOpt R b mf))
```
- **Hypothesis ledger:**
  - `hAssoc` — Reassociates frames during sequential elimination of the two non-deterministic updates. Tightness: `tight` (`Toy.RA.fpUpdateP_op_nonAssoc_counterexample`).
  - `hComm` — Swaps the chosen intermediate b₁ past a₂ so h₂ applies with frame b₁ ·? mf. Tightness: `tight` (`Toy.RA.fpUpdateP_op_nonComm_counterexample`).
  - `h₁` — Produces a frame-compatible target b₁ satisfying P₁. Tightness: `tight` (`Toy.RA.fpUpdateP_op_noUpdate1_counterexample`).
  - `h₂` — Produces a frame-compatible target b₂ satisfying P₂ after b₁ is chosen. Tightness: `tight` (`Toy.RA.fpUpdateP_op_noUpdate2_counterexample`).
  - `hQ` — Transfers P₁ b₁ ∧ P₂ b₂ to the combined target postcondition Q (b₁ · b₂); needed even when Q is inhabited by a valid element. Tightness: `tight` (`Toy.RA.fpUpdateP_op_noPost_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdateP_op_nonvacuity` — In authRA counterRA, OpAssoc and OpComm hold, singleton updates from auth 2 · frag 1 and frag 1 satisfy the postcondition, the framed source is valid, and frag 1 ⤳: (· = frag 2) fails.
- **Non-claims:**
  - Does not show that OpAssoc and OpComm are globally necessary for parallel composition (tightness means irredundancy in this general statement, not necessity in every algebra).
  - May fail without OpComm (e.g., in pathCatRA, Toy.RA.fpUpdateP_op_nonComm_counterexample).
  - Does not force a single uniform pair (b₁, b₂) across all frames mf; each frame mf may choose different witnesses b₁, b₂ (matching Iris's cmra_updateP).
  - Discrete only: does not cover step-indexed non-deterministic updates where target choice may depend on the step index n.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_updateP_op, lines 78-88, proved using only cmra_op_opM_assoc and comm)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.UpdateP.op)
  - Background: Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§2.1)
- **Design question:** Does the set-valued generalization of parallel update composition suffice with the same RA laws (associativity and commutativity) as deterministic composition?

#### Card 16: `fpUpdate_drop_right`

- **Lean declaration:** `Toy.RA.fpUpdate_drop_right` in `lean/Toy/RA/Laws.lean`
- **Kind / Tier / Depth:** `theorem` | `T0` — T0 (discrete re-derivation of Iris's `cmra_update_op_l` / `cmra_update_included` and `Iris.Update.op_l`, paired with per-law tightness witnesses and global `ValidOpL` necessity). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α satisfying all three discrete core-free RA laws (OpAssoc R, OpComm R, and ValidOpL R), discarding part of a composite resource is always right-frame-preserving: a · b ⤳ a for all a b : α (with ValidOpL R globally necessary for universal dropping via Toy.RA.validOpL_of_fpUpdate_drop_right_all).
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdate_drop_right` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdate_drop_right {α : Type} (R : RawRA α)
    (hAssoc : OpAssoc R) (hComm : OpComm R) (hValidOpL : ValidOpL R)
    (a b : α) :
    fpUpdate R (R.op a b) a
-- Unfolded:
--   (∀ x y z : α, R.op (R.op x y) z = R.op x (R.op y z)) →
--   (∀ x y : α, R.op x y = R.op y x) →
--   (∀ x y : α, R.valid (R.op x y) → R.valid x) →
--   (∀ mf : Option α, R.valid (opOpt R (R.op a b) mf) → R.valid (opOpt R a mf))
```
- **Hypothesis ledger:**
  - `hAssoc` — Regroups (a · b) · f into (a · f) · b before projecting validity with ValidOpL. Tightness: `tight` (`Toy.RA.fpUpdate_drop_right_nonAssoc_counterexample`).
  - `hComm` — Moves the discarded piece b past the frame f so b sits on the outside of (a · f) · b; without commutativity, b can act as a compatibility bridge between a and f. Tightness: `tight` (`Toy.RA.fpUpdate_drop_right_nonComm_counterexample`).
  - `hValidOpL` — Projects validity of a · b to validity of a (empty frame) and validity of (a · f) · b to validity of a · f (non-empty frame); globally necessary for universal dropping (Toy.RA.validOpL_of_fpUpdate_drop_right_all). Tightness: `tight` (`Toy.RA.fpUpdate_drop_right_noValidOpL_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdate_drop_right_nonvacuity` — authRA counterRA satisfies OpAssoc, OpComm, and ValidOpL simultaneously while distinguishing valid auth 2 · frag 1 from invalid auth 2 · frag 3.
- **Companion and boundary theorems:** `Toy.RA.validOpL_of_fpUpdate_drop_right_all` (global necessity of `ValidOpL`), `Toy.RA.drop_right_holds_without_opComm_example`, `Toy.RA.drop_right_holds_without_opAssoc_example`.
- **Non-claims:**
  - Does not show that weakening requires OpAssoc or OpComm. ∀ a b, a · b ⤳ a holds in the non-commutative boolLeftProjRA (Toy.RA.drop_right_holds_without_opComm_example) and in the non-associative natSubRA (Toy.RA.drop_right_holds_without_opAssoc_example). ValidOpL is the only globally necessary law: (∀ a b, a · b ⤳ a) → ValidOpL R (Toy.RA.validOpL_of_fpUpdate_drop_right_all).
  - May fail without OpComm (e.g., in pathCatRA, Toy.RA.fpUpdate_drop_right_nonComm_counterexample).
  - Discrete algebraic frame preservation only: does not imply that discarding resources is sound in linear (non-affine) separation logics where forgetting ownership leaks obligations, and does not cover step-indexed CMRAs without a modeling bridge.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_update_op_l, cmra_update_included)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.op_l)
  - Background: Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§2.1)
- **Design question:** Which discrete RA laws suffice for resource dropping (weakening), and which single law is globally necessary?

#### Card 17: `fpUpdate_iff_bare_of_rightUnit`

- **Lean declaration:** `Toy.RA.fpUpdate_iff_bare_of_rightUnit` in `lean/Toy/RA/Laws.lean`
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete unital specialization of Iris's `cmra_discrete_total_update` + `cmra_unit_cmra_total`, formalizing Jung et al., JFP 2018 §2.1 fn. 6 and `tex/algebra.tex` §RA lines 149–156). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α possessing a global right identity e (IsRightUnit R e) — with none of OpAssoc, OpComm, ValidOpL, or R.valid e required — optional right-frame fpUpdate R a b is equivalent to bare non-empty right-frame fpUpdateBare R a b.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdate_iff_bare_of_rightUnit` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdate_iff_bare_of_rightUnit {α : Type} (R : RawRA α) (e : α)
    (hUnit : IsRightUnit R e) (a b : α) :
    fpUpdate R a b ↔ fpUpdateBare R a b
-- Unfolded:
--   (∀ x : α, R.op x e = x) →
--   ((∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)) ↔
--    (∀ f : α, R.valid (R.op a f) → R.valid (R.op b f)))
```
- **Hypothesis ledger:**
  - `hUnit` — Supplies a single carrier element e with a · e = a and b · e = b so the empty-frame check reduces to instantiating fpUpdateBare at f = e. Tightness: `tight` (`Toy.RA.fpUpdate_bare_noUnit_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdate_iff_bare_of_rightUnit_nonvacuity` — In authRA counterRA, authUnit is a right unit (IsRightUnit (authRA counterRA) authUnit), IsCoreFreeRA holds, auth 2 · frag 1 is valid, and frag 1 ⤳ frag 2 fails.
- **Companion and boundary theorems:** `Toy.RA.opComm_alone_not_two_sided`, `Toy.RA.agreeRA_bool_no_rightUnit`.
- **Non-claims:**
  - The equivalence with the bare form is for right-composed frames only; without OpComm, neither fpUpdate nor fpUpdateBare need protect left-composed frames (and even with OpComm, simultaneous two-sided contexts l · (a · r) additionally require OpAssoc; Toy.RA.opComm_alone_not_two_sided).
  - IsRightUnit is sufficient, not necessary, for fpUpdate ↔ fpUpdateBare: non-unital algebras with right identities on valid elements and ValidOpL (such as agreeRA Bool) also satisfy the equivalence via Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL.
  - Does not permit dropping the optional empty frame in non-unital algebras without right identities on valid elements, such as exclRA or fracValRA, where fpUpdateBare erroneously permits updating valid elements to invalid ones.
  - Discrete only: does not cover step-indexed CMRAs (✓{n}) or OFE cameras.
- **Prior art:**
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§2.1 fn. 6, p. 12: optional frame needed because non-unital RAs lack a global unit ε)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/algebra.tex (§RA, lines 149-156)
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/cmra.v (cmra_unit_cmra_total, line 695) and iris/algebra/updates.v (header comment lines 4-8, cmra_discrete_total_update)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.discrete_total, lines 169-174)
- **Design question:** When does the bare non-empty right-frame quantifier ∀ f, valid (a · f) → valid (b · f) coincide with optional-frame fpUpdate, and when does omitting the empty frame silently allow valid-to-invalid transitions?

#### Card 18: `fpUpdate_iff_bare_of_rightIdOnValid_validOpL`

- **Lean declaration:** `Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL` in `lean/Toy/RA/Laws.lean` (additional hashed theorems in `lean_names`: `Toy.RA.idempotent_noncomm_validOpL_witness`, `Toy.RA.two_element_comm_validOpL_witness`)
- **Kind / Tier / Depth:** `characterization` | `T0` — T0 (discrete re-derivation of Iris's `cmra_discrete_total_update` and `Iris.Update.discrete_total` isolating per-element right identities on valid elements plus `ValidOpL`). | `shallow`
- **Plain-language claim:** In any raw resource algebra R : RawRA α where every valid element admits a right identity (HasRightIdOnValid R) and validity is downward closed on the left (ValidOpL R) — without requiring a global unit, right identities on invalid elements, core laws, OpAssoc, or OpComm — optional right-frame fpUpdate R a b is equivalent to bare non-empty right-frame fpUpdateBare R a b.
- **Basis:** `execution (Lean kernel check)` — `Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL` (axioms: `none`) and all referenced witnesses and counterexamples compile under `leanprover/lean4:v4.34.1` without `sorry`.
- **Lean statement (with key definitions unfolded):**
```lean
theorem Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL {α : Type} (R : RawRA α)
    (hRightId : HasRightIdOnValid R) (hValidOpL : ValidOpL R) (a b : α) :
    fpUpdate R a b ↔ fpUpdateBare R a b
-- Unfolded:
--   (∀ x : α, R.valid x → ∃ c : α, R.op x c = x) →
--   (∀ x y : α, R.valid (R.op x y) → R.valid x) →
--   ((∀ mf : Option α, R.valid (opOpt R a mf) → R.valid (opOpt R b mf)) ↔
--    (∀ f : α, R.valid (R.op a f) → R.valid (R.op b f)))
```
- **Hypothesis ledger:**
  - `hRightId` — Supplies a right identity c for a valid source a (a · c = a) so R.valid a triggers fpUpdateBare at f = c to yield R.valid (b · c); weakens HasLocalRightUnits to valid elements only. Tightness: `tight` (`Toy.RA.fpUpdate_bare_noRightIdOnValid_counterexample`).
  - `hValidOpL` — Projects R.valid (b · c) to R.valid b when a's right identity c is not a right identity for b; tight at size 2 under HasRightIdOnValid, OpAssoc, and OpComm (Toy.RA.two_element_comm_validOpL_witness), and tight at size 5 even when HasLocalRightUnits, OpAssoc, and OpComm all hold (witnessed by fiveLocalUnitsNoValidOpLRA; nothing is claimed about smaller witnesses). Tightness: `tight` (`Toy.RA.fpUpdate_bare_rightIdOnValid_noValidOpL_counterexample`).
- **Non-vacuity witness:** `Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL_nonvacuity` — agreeRA Bool has no global right unit (Toy.RA.agreeRA_bool_no_rightUnit), satisfies HasRightIdOnValid and ValidOpL, and rejects ag false ⤳ ag true.
- **Companion and boundary theorems:** `Toy.RA.two_element_comm_validOpL_witness` (2-element commutative associative tightness witness under `HasRightIdOnValid`), `Toy.RA.idempotent_noncomm_validOpL_witness` (2-element idempotent non-commutative tightness witness with `HasLocalRightUnits`), `Toy.RA.fpUpdate_iff_bare_of_idemp_opComm`, `Toy.RA.localRightUnits_alone_not_iff_bare`, `Toy.RA.rightIdOnValidOnlyRA_props`.
- **Non-claims:**
  - The equivalence with the bare form is for right-composed frames only; without OpComm, neither fpUpdate nor fpUpdateBare need protect left-composed frames (and even with OpComm, simultaneous two-sided contexts l · (a · r) additionally require OpAssoc; Toy.RA.opComm_alone_not_two_sided). HasRightIdOnValid (and HasLocalRightUnits) is not Iris's CmraTotal: it asks only for some right identity per valid (resp. arbitrary) element, which need not be idempotent, canonical, or monotone. HasLocalRightUnits corresponds to the multi-unit axiom of Dockins-Hobor-Appel (APLAS 2009, axiom (15)), without cancellativity.
  - Does not apply to non-total, non-unital algebras without right identities on valid elements (such as exclRA or fracRA), where fpUpdateBare is strictly weaker than fpUpdate.
  - When every element is idempotent (x · x = x) and OpComm holds, fpUpdate coincides with fpUpdateBare without ValidOpL (Toy.RA.fpUpdate_iff_bare_of_idemp_opComm). So no commutative algebra in which every element is idempotent is a tightness witness for ValidOpL; a commutative witness may still contain idempotent elements (in zeroBoolRA, false · false = false, and false is the source of the separating pair (false, true) of Toy.RA.two_element_comm_validOpL_witness). Without OpComm, an idempotent, associative 2-element tightness witness with HasLocalRightUnits exists (Toy.RA.idempotent_noncomm_validOpL_witness).
  - Does not show that HasLocalRightUnits is required on invalid elements (Toy.RA.rightIdOnValidOnlyRA_props constructs a 3-element commutative, associative, ValidOpL algebra meeting HasRightIdOnValid where HasLocalRightUnits fails).
  - Discrete only: does not cover step-indexed CMRAs (✓{n}) or OFE cameras.
- **Prior art:**
  - Iris (Rocq) tag iris-4.4.0 (commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732): iris/algebra/updates.v (cmra_total_update lines 123-133 and cmra_discrete_total_update line 155, using only cmra_core_r and cmra_validN_op_l)
  - iris-lean (Lean 4) commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b: Iris/Iris/Algebra/Updates.lean (Iris.Update.discrete_total, lines 169-174)
  - Dockins, Hobor, Appel, 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, DOI 10.1007/978-3-642-10672-9_13 (§2, axiom (15): multi-unit separation algebras ∀ x, ∃ u_x, u_x ⊕ x = x)
  - Jung et al., 'Iris from the ground up', JFP 28 (2018), e20, DOI 10.1017/S0956796818000151 (§2.1 fn. 6, p. 12; Fig. 3 p. 9)
  - Iris technical documentation at commit 82dbf5e7a11d7ffaafe78e95186b5b376f4df732: tex/algebra.tex (§RA, lines 149-156)
- **Design question:** In non-unital algebras with per-element right identities on valid elements (like agreement), which laws suffice so bare right-frame quantification cannot leak invalid targets?

## Boundaries

### 1. Package-Level Non-Claims

- **NC-G1 (one-sided right frames vs. single left frames vs. simultaneous two-sided frames — known not to apply without the corresponding laws).** `fpUpdate`, `fpUpdateP`, `fpUpdateBare`, and `IsExclusive` compose frames on the **right** (`a ·? mf`).
  - Without `OpComm`, right-frame preservation need not preserve a left-composed frame `f · a`: in the associative, `ValidOpL`-satisfying, non-commutative 2-object category algebra `pathCatRA`, `some (false, true) ⤳ some (true, true)` holds for all right frames while invalidating the left frame `some (true, false)` (`Toy.RA.pathCat_fpUpdate_breaks_left_frame`), and in `authRA pathCatRA` a lifted `LocalUpdate` holds for right frames while invalidating a left-composed fragment (`Toy.RA.auth_pathCat_localUpdate_breaks_left_frame`).
  - Under `OpComm` alone, right-frame preservation also preserves each **single** left-composed frame `f · a` (`Toy.RA.fpUpdate_preserve_left_of_opComm`), **not** simultaneous two-sided contexts `l · (a · r)` or `(l · a) · r`. Over the commutative, `ValidOpL`-satisfying, non-associative algebra `nonAssocCommValidRA`, `e0 ⤳ e1` holds for all right frames, yet `e2 · (e0 · e1)` is valid while `e2 · (e1 · e1)` is invalid (and `(e1 · e0) · e2` is valid while `(e1 · e1) · e2` is invalid), refuting `fpUpdate2` (`Toy.RA.opComm_alone_not_two_sided`). The exact same failure arises inside `authRA nonAssocCommValidRA` for `authElem .e0 · fragElem .e0 ⤳ authElem .e0 · fragElem .e1` under the two-sided fragment context `fragElem .e2 · (_ · fragElem .e1)` (`Toy.RA.auth_opComm_alone_not_two_sided`). Simultaneous two-sided contexts `l · (a · r)` are preserved under `OpComm ∧ OpAssoc` (`Toy.RA.fpUpdate2_of_assoc_comm`).
- **NC-G2 (tightness is irredundancy, not global necessity).** Marking a hypothesis `tight` means only that deleting it from *that* general theorem while keeping the remaining hypotheses makes the general theorem false. It does **not** mean the law is required in every individual algebra: in universally valid algebras, universal right-framing holds without `OpAssoc` (`natSubRA`, `Toy.RA.frame_right_holds_without_opAssoc_example`), parallel composition holds without `OpComm` (`boolLeftProjRA`) or without either law (`natSubRA`) (`Basis: derived` — every element of these algebras is valid, so `fpUpdate` holds for all pairs; no separate Lean declaration is given), and universal right-dropping `∀ a b, a · b ⤳ a` holds without `OpComm` (`Toy.RA.drop_right_holds_without_opComm_example`) and without `OpAssoc` (`Toy.RA.drop_right_holds_without_opAssoc_example`). Across all raw algebras, **only `ValidOpL` is globally necessary** for universal right-dropping (`Toy.RA.validOpL_of_fpUpdate_drop_right_all`).
- **NC-G3 (no internalized program logic or concurrency semantics).** No assertion language, points-to predicate, invariant mechanism, update modality, or operational thread semantics is formalized here. Every reference to 'concurrent readers', 'another thread's frame', or 'external fragment holders' is an external `derived (modeling bridge)` claim contingent on a separate separation-logic adequacy theorem.
- **NC-G4 (discrete Leibniz equality only — step-indexed cameras not examined).** Every type and law in `Toy.RA` is discrete. Results do not establish theorems about step-indexed Iris cameras (OFEs with `≡{n}≡` and `✓{n}`; cf. Jung et al., JFP 2018, and Jung, Krebbers, Birkedal, and Dreyer, *Higher-order ghost state*, ICFP 2016, DOI `10.1145/2951913.2951943` as background context) without restricting to discrete cameras.
- **NC-G5 (core-free, unit-optional, non-cancellative vocabulary).** `IsCoreFreeRA` (`OpAssoc ∧ OpComm ∧ ValidOpL`) omits Iris's partial core `pcore` and core monotonicity/idempotence axioms, and imposes neither a unit nor cancellativity (unlike F\* PCMs and Calcagno–O'Hearn–Yang / Dockins–Hobor–Appel separation algebras). Likewise, `HasRightIdOnValid` and `HasLocalRightUnits` assert existential per-element right identities without canonical core laws, and `HasRightIdOnValid` is strictly weaker than `HasLocalRightUnits` (`Toy.RA.rightIdOnValidOnlyRA_props`).
- **NC-G6 (`ValidOpL` tightness witness structure on Card 18 — known not to apply without qualifiers).** While `OpComm` plus idempotence (`∀ x, x · x = x`) implies `fpUpdate ↔ fpUpdateBare` without `ValidOpL` (`Toy.RA.fpUpdate_iff_bare_of_idemp_opComm`), so that no commutative algebra in which every element is idempotent is a tightness witness for `ValidOpL`, a commutative witness may still contain idempotent elements (in `zeroBoolRA`, `false · false = false`), and non-commutative tightness witnesses for `ValidOpL` *can* have every element idempotent (`Toy.RA.idempotent_noncomm_validOpL_witness` on the 2-element right-zero band `rightZeroBoolRA`). The 5-element canonical witness `fiveLocalUnitsNoValidOpLRA` (`Toy.RA.fpUpdate_bare_rightIdOnValid_noValidOpL_counterexample`) additionally satisfies `HasLocalRightUnits` on every element alongside `OpAssoc` and `OpComm`; nothing is claimed about whether a smaller witness with these properties exists. Under Card 18's actual hypothesis `HasRightIdOnValid`, a 2-element commutative associative zero semigroup already separates `fpUpdateBare` from `fpUpdate` (`Toy.RA.two_element_comm_validOpL_witness`).
- **NC-G7 (invalid-source vacuity and `LocalUpdate` non-necessity).** Updates out of invalid sources (`Excl.invalid`, multi-element `Agree α` predicates, over-full shares `q > 1` as in `Toy.RA.fracVal_partial_iff_overfull_counterexample`) hold vacuously because no optional frame makes the source valid. In `authRA R`, `LocalUpdate R a b a' b'` is sufficient under `OpAssoc R` (`Toy.RA.auth_localUpdate_fpUpdate`) but **not** necessary (`Toy.RA.auth_counter_alloc_only_not_localUpdate`); the exact condition is `Toy.RA.auth_both_fpUpdate_iff`.

### 2. Escape Hatches for Impossibility and Negative Results

- **`excl_no_valid_frame` (Card 1):** Adjoining an external unit `Option (Excl α)` allows the empty unit `none` to compose validly with `some (.excl x)`; replacing `exclRA` with a shareable algebra (`cappedNatRA`, `Toy.RA.excl_no_valid_frame_positive_control`) admits non-trivial valid frames.
- **`agree_distinct_not_fpUpdate` (Card 5):** Keeping `x = y` (`Toy.RA.agree_same_fpUpdate_counterexample`), starting from an invalid multi-element carrier value, or wrapping the payload in `exclRA` (`Toy.RA.agree_distinct_positive_control_excl`), full-share `fracValRA` (`Toy.RA.fracVal_full_fpUpdate`), or `authRA` (`Toy.RA.auth_counter_inc_fpUpdate`) enables updates; switching to non-deterministic `fpUpdateP` on `agreeRA α` itself does **not** escape (`Toy.RA.agree_fpUpdateP_imp_mem`).
- **`fracVal_partial_value_change_impossible` (Card 8):** Holding the full share `q = PosRat.one` (`Toy.RA.fracVal_full_value_change_control`), recombining complementary shares summing to `1` (`Toy.RA.fracVal_recombine_fpUpdate`), keeping `x = y` with `q' ≤ q` (`Toy.RA.fracVal_partial_same_value_counterexample`), or starting from an invalid over-full share `q > 1` (`Toy.RA.fracVal_partial_iff_overfull_counterexample`) defeats the impossibility.
- **`auth_counter_dec_auth_only_fails` (Card 12):** Decrementing the owned fragment by the same amount as the authoritative counter (`(2, 1) → (1, 0)`) restores `LocalUpdate` and frame preservation (`Toy.RA.counter_dec_both_localUpdate`).

### 3. Scope Classification, `unknown` Tightness, and Statements Found False

- **Known not to apply:** Left-frame preservation without `OpComm`; simultaneous two-sided frame preservation under `OpComm` without `OpAssoc`; bare frame quantification `fpUpdateBare` on `exclRA` or `fracValRA`; partial-fraction characterization at `q = 1` or `q > 1`; necessity of `LocalUpdate` for `authRA` updates; weakening admissibility in strictly linear (non-affine) logics from `fpUpdate_drop_right` alone.
- **Not examined / unsupported:** Step-indexed CMRAs and OFE contractive functors, persistent cores (`pcore`), discardable fractions (`DFrac`), fractional authoritative ownership (`●{dq} a`), general `View` cameras, fixed-width machine-integer overflow in `counterRA`, and operational program-logic soundness.
- **Hypotheses with `unknown` tightness:** None. Every hypothesis of every result in `results.json` is proved `tight` with a kernel-checked canonical counterexample.
- **Statements found false:** None. `Toy.RA.agree_naive_update_bool_counterexample` (a ground `Bool` instance) is kept as a companion lemma of Card 5 rather than as a separate result.

## Evidence

### 1. Lean Kernel Verification and Axiom Summary

- **Toolchain:** `leanprover/lean4:v4.34.1` (Git tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).
- **Dependencies:** None (`lean/lakefile.toml` declares a single `[[lean_lib]]` named `"Toy"` with zero `[[require]]` entries; Mathlib-free).
- **Axiom audit (`audit/axioms.json`):** `Lean.collectAxioms` was run over all **556** non-internal declarations in `Toy` (`Toy`, `Toy.RA`, `Toy.RA.Core`, `Toy.RA.PosRat`, `Toy.RA.Excl`, `Toy.RA.Agree`, `Toy.RA.Frac`, `Toy.RA.Auth`, `Toy.RA.Laws`). Across the entire library, the only axioms used are `propext` and `Quot.sound` (`Classical.choice` is unused; `sorryAx` and `Lean.ofReduceBool` / `native_decide` do not occur). Ten of the 18 main theorems (`excl_no_valid_frame`, `excl_fpUpdate_iff`, `exclusive_fpUpdate`, `agree_distinct_not_fpUpdate`, `fpUpdate_frame_right`, `fpUpdate_op`, `fpUpdateP_op`, `fpUpdate_drop_right`, `fpUpdate_iff_bare_of_rightUnit`, `fpUpdate_iff_bare_of_rightIdOnValid_validOpL`), as well as the boundary theorems `fpUpdate2_of_assoc_comm`, `idempotent_noncomm_validOpL_witness`, and `two_element_comm_validOpL_witness`, depend on **zero** axioms (`[]`).
- **Hash audit (`audit/statements.json`):** Records SHA-256 digests of the kernel `Expr` representation of each declaration's statement (`statement_sha256`) and of its sorted package-local definition closure (`closure_sha256`, with theorem proof bodies excluded) for all **66** card-referenced Lean declarations.

#### Table 1: Main Result Declarations (Cards 1–18)

| # | Result ID | Lean Name | Axioms | Closure Size | `statement_sha256` | `closure_sha256` |
| :---: | :--- | :--- | :--- | :---: | :--- | :--- |
| 1 | `excl_no_valid_frame` | `Toy.RA.excl_no_valid_frame` | `none` | 11 | `96cb5aa6f3d545e37d582a0503c5293884e496eef4eceb7f9d75963ef2848fec` | `05d4fe1d0cc04345fbdc9c6002e58a92396834d43aa1a689caf4defb4e2e979c` |
| 2 | `excl_fpUpdate_iff` | `Toy.RA.excl_fpUpdate_iff` | `none` | 14 | `54750301c0fbe99e1f483465ca800332ed9f82c2ba98abe99dfd78890b420a29` | `1b2703dce24c9bfd0574cfc30c29ff39057b84ccaab734f6c31775a6c0e1dccf` |
| 3 | `exclusive_fpUpdate` | `Toy.RA.exclusive_fpUpdate` | `none` | 8 | `bf4c46f868fdc6e664ca582d4a00ba732551d848f4d22f22e800256390441c2c` | `c3c058e1783783fa5dcc6063ef526baa02f5d475e8912c2551c5b33bbbb8790b` |
| 4 | `agree_fpUpdate_iff` | `Toy.RA.agree_fpUpdate_iff` | `Quot.sound`, `propext` | 14 | `fe95921e77913c74c7d0c656bbc9f4892a6502a5af570d7137efa6f3e03c0d30` | `f5686586aee087703a41c800b89ca4491fb7e1445ab77d575fb53629aa931649` |
| 5 | `agree_distinct_not_fpUpdate` | `Toy.RA.agree_distinct_not_fpUpdate` | `none` | 14 | `609ba45cdc9e5d1c00031bbec330253154def26013f0094e41fbac414eb9cc52` | `f5686586aee087703a41c800b89ca4491fb7e1445ab77d575fb53629aa931649` |
| 6 | `fracVal_full_fpUpdate_iff` | `Toy.RA.fracVal_full_fpUpdate_iff` | `Quot.sound`, `propext` | 36 | `f80ebf8b9f8dee734c0801883430fd01eb0566e23b2dc4b12442fa41bf8aa4bf` | `971d86b84111c659f7b1c80983036a143ca00f5045397cba139da5021c7afcd4` |
| 7 | `fracVal_partial_fpUpdate_iff` | `Toy.RA.fracVal_partial_fpUpdate_iff` | `Quot.sound`, `propext` | 38 | `34e66d7f0453ad70128196bd4154be414041b80bb2ced71d86c308acb5ab39b6` | `5059367b7923e6665555387e297e5934406b6399eda0051dc92935aabd5b8922` |
| 8 | `fracVal_partial_value_change_impossible` | `Toy.RA.fracVal_partial_value_change_impossible` | `Quot.sound`, `propext` | 38 | `acb23b0088203c813cd690af62d662c89344bdd2519b39e69048ab3251cc8066` | `5059367b7923e6665555387e297e5934406b6399eda0051dc92935aabd5b8922` |
| 9 | `auth_both_fpUpdate_iff` | `Toy.RA.auth_both_fpUpdate_iff` | `propext` | 28 | `d1a9b629eda31129d9e97f46643c03d3599e86c7314701d838876a0e7919b3e0` | `b384df848be893b72da772a41fb96494fd7a945dc6e58663292bcf2413c1ce21` |
| 10 | `auth_localUpdate_fpUpdate` | `Toy.RA.auth_localUpdate_fpUpdate` | `propext` | 30 | `78b905f6ea0376e5c1caa92c71be8865933b622f105e721756478af6d44a5c0c` | `2e815b054044e9736e0c74718ca268da64bd8c2e21c5f0d9d69e0ac8d9812a60` |
| 11 | `auth_counter_inc_fpUpdate` | `Toy.RA.auth_counter_inc_fpUpdate` | `Quot.sound`, `propext` | 30 | `280ecdc9816fef9a0fe1ee9ab7282a71d20115e3a814cf6b849f0cfc6562c2cf` | `cee14ce3b794749da1fa37756c2be8c18376214e18f48bdd6b802f16174c0916` |
| 12 | `auth_counter_dec_auth_only_fails` | `Toy.RA.auth_counter_dec_auth_only_fails` | `Quot.sound`, `propext` | 34 | `168267c43dbafcd16f31440831253c9e69bf523d73de0b13d2210e28b6c107b1` | `d3cf660c25ced037de60e77cb3d186df4d43aa179573a39c542b78af074f909a` |
| 13 | `fpUpdate_frame_right` | `Toy.RA.fpUpdate_frame_right` | `none` | 8 | `b67baa23ff5bf14fc3ababbe5d5ad0e3660fa91159c7d8f43262dc7815dc9756` | `0f71ceb22e9ddaea008753198799ddb3d518bc71d651d9083a0ab97bd6ae0898` |
| 14 | `fpUpdate_op` | `Toy.RA.fpUpdate_op` | `none` | 9 | `12030c187dcc4266844a1cc0008807a54b16cffcad8f6e6adc3c1b077199386d` | `c82cbc69c9535ba955b7e5c49ee56dcba0978cb56348fe16536ffb7f98cff9b8` |
| 15 | `fpUpdateP_op` | `Toy.RA.fpUpdateP_op` | `none` | 9 | `1f516225ca280c59a375756616462270dd5c8aaea445f27f1037bcf129c531d8` | `915ab5ade4e80245870428ee5096c52bfa53d93ef50d21af7bbe69b80eca9540` |
| 16 | `fpUpdate_drop_right` | `Toy.RA.fpUpdate_drop_right` | `none` | 10 | `829113f71c6adc67f4326cae232852364aa767c4bbba8c4fd38f05115d1e80de` | `80a09985ea2cd89668de5621f08dd7bedd8c989144c0323b11b4d129d5844de9` |
| 17 | `fpUpdate_iff_bare_of_rightUnit` | `Toy.RA.fpUpdate_iff_bare_of_rightUnit` | `none` | 9 | `451501e743554dfa57974033accaa2b132e665de6e973f92dfb9b00f09acf3a7` | `1016902dee8eeeef152d3baab8f4a432b441e61422ae2fd22a78f6098da249eb` |
| 18 | `fpUpdate_iff_bare_of_rightIdOnValid_validOpL` | `Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL` | `none` | 10 | `5b80e401bc09a4ee63d864ed3aaf1f11ff21e88dc04c1d030e228a070476fd37` | `bd005a0bb3a9738b613274902cfd2229ecdea430f50191afdabda16acec36684` |

#### Table 2: Supporting Non-Vacuity Witnesses, Positive Controls, Tightness Counterexamples, and Boundary Theorems

| Lean Name | Axioms | Closure Size | `statement_sha256` | `closure_sha256` |
| :--- | :--- | :---: | :--- | :--- |
| `Toy.RA.agree_distinct_not_fpUpdate_nonvacuity` | `Quot.sound`, `propext` | 13 | `a0dc34ca35bac4195f4d21d6c71fd369ecf12238b40849f27f8a9791ce9565fe` | `6381f892663c1cc76f85c3fa3fac83281f8476abd1085ddc88bcb5246e670e5a` |
| `Toy.RA.agree_distinct_positive_control_excl` | `none` | 18 | `e7888bc6c94dcd0662a8f20417ed4609297621f97bbbe317bf9954c301ca3ea1` | `124ce1d7eb57fed1c9d14243ce5031aea28da95669344cb30740171ca866fdb7` |
| `Toy.RA.agree_fpUpdate_iff_nonvacuity` | `Quot.sound`, `propext` | 15 | `8c08e90756377a5f0c1b5e8fdc04115b682e8561f0f56f74cd09672b90160d24` | `5f9bd34390f88c0df35fbb8f425fb7de754cc4035eb5c1e65d33cb85615b937c` |
| `Toy.RA.agree_same_fpUpdate_counterexample` | `Quot.sound`, `propext` | 18 | `05ad2360e50b91e10f9c826949ac4cc5a2a5064ab8a9c0db9236992d7cc5a08a` | `425549cd074a554ebe8892ff32a2c41a210a2859153f96f6370fe870a80c846d` |
| `Toy.RA.auth_both_fpUpdate_iff_nonvacuity` | `Quot.sound`, `propext` | 34 | `0b27deab7bb1debe011b1cc6d3fbc7216cd77ab3353a5f873e7679c9eef23d7a` | `dd7202783bb4cdb3e137585da12c6146d63b210e4a689244b575ec409128a411` |
| `Toy.RA.auth_counter_inc_fpUpdate_nonvacuity` | `Quot.sound`, `propext` | 34 | `c09098e15a59c420000d776fdf0132e5e0f5c9a54474df29da8eeb7a498e9e5b` | `dd7202783bb4cdb3e137585da12c6146d63b210e4a689244b575ec409128a411` |
| `Toy.RA.auth_localUpdate_fpUpdate_nonvacuity` | `Quot.sound`, `propext` | 31 | `60598507084e502909d88764248e9cd71a11c0b350a4a4c24c5b1b501d127da1` | `6d826a066d0d3fb224c7cfb887a6397b139d96cc4726b5cf7aeabefc4fa91a8a` |
| `Toy.RA.auth_localUpdate_nonAssoc_counterexample` | `propext` | 41 | `b7b39e92d2f87d63986dbc3511e514366b54960c2c550527047ca0d8a3d17cfa` | `eff98bc5114ad3c5acfa53dc022925cbce47a63a84926ab37777f4b21188af86` |
| `Toy.RA.auth_opComm_alone_not_two_sided` | `propext` | 42 | `7d85021378563909a10906c8a7990e2bcaca7c3d74843c564e47df90cc08bee7` | `ff263e92ab4f7e95fcf68d48fefaa490a0f6cb86aad5d1501734677c47192ecb` |
| `Toy.RA.excl_fpUpdate_iff_nonvacuity` | `none` | 15 | `220a1ade9726b7a2827d43c210764b6eeb20cc71ba91427e95c025f17720064b` | `2057c278bc9165b094dd7f2e6fe64b25e18bb99b0d919b34efd03472510e233f` |
| `Toy.RA.excl_no_valid_frame_nonvacuity` | `none` | 15 | `d8f5dd553054cb0962ec417c2d67b2aeba0bed3bdb0146301f607a277c23be68` | `2057c278bc9165b094dd7f2e6fe64b25e18bb99b0d919b34efd03472510e233f` |
| `Toy.RA.excl_no_valid_frame_positive_control` | `Quot.sound`, `propext` | 9 | `15b46f1709b758bcf91a5111edefbf711b5844cf88dfca080e434b78a430695f` | `f916324212d2b44850198dfa2bb83613ec3614d21b556e3332af601fcd40dd36` |
| `Toy.RA.exclusive_fpUpdate_invalid_target_counterexample` | `none` | 19 | `855c9aa2e00f1365fa6cfe68fe8593f4385b3d9814727320d471f30d85ec2927` | `39194a4a635cc4573ee1cef7dd6e592eb65fce4e936b0f76a467de2faa691c70` |
| `Toy.RA.exclusive_fpUpdate_nonvacuity` | `none` | 16 | `02472c3f22fb5b2819c17a4fd94af02f48009b8045f515bdcc1c516ea1257256` | `dea2a3dfcc14b700694b83a7b65259dba76efb1cc93f325faa28d6ebc260a48d` |
| `Toy.RA.exclusive_fpUpdate_not_exclusive_counterexample` | `Quot.sound`, `propext` | 19 | `1f690dd5307057daa0e55027abc6dea221b3fc35f8aa7b09ccd66dc3a75b02ea` | `98d39d63be29e5a143349bc26a7e66acca0f44ba4019ddc80cd289fee95d6d06` |
| `Toy.RA.fpUpdate2_of_assoc_comm` | `none` | 12 | `90dc6e54ee174317229ddbe2ec9e4efbb913f42c1d61889c95fc11e432fe7dc9` | `2d1638f4949ebee833a4bafa45560060b64a83f930bcd7a248f603c78b0cf725` |
| `Toy.RA.fpUpdateP_op_noPost_counterexample` | `Quot.sound`, `propext` | 16 | `075d72b039adc0649781d9d5156377f9f03cc78ecc7ac107c610c491b4d8cc16` | `62973505d4ad9a41a2807032bf8ddd2d22761e583d7bf9a5ac441743cf4afb86` |
| `Toy.RA.fpUpdateP_op_noUpdate1_counterexample` | `Quot.sound`, `propext` | 16 | `92963e50ac5d029ee5333da2ab51009c6a3db7221d3660e45c42c071457a9072` | `62973505d4ad9a41a2807032bf8ddd2d22761e583d7bf9a5ac441743cf4afb86` |
| `Toy.RA.fpUpdateP_op_noUpdate2_counterexample` | `Quot.sound`, `propext` | 16 | `90a62b8769b97accb87072399b27b08a252b143e3c3cdb920d7e5983b1f3936c` | `62973505d4ad9a41a2807032bf8ddd2d22761e583d7bf9a5ac441743cf4afb86` |
| `Toy.RA.fpUpdateP_op_nonAssoc_counterexample` | `propext` | 19 | `340a9ff40a6cd4aceaffc4409accc8f5b3cea4027fbef1da5322393e5c1ef54f` | `5883cdf2575ef926af68d63733c6f743fe70c6202e8f79817bb9a42ee51904ab` |
| `Toy.RA.fpUpdateP_op_nonComm_counterexample` | `propext` | 13 | `dd5f455e26d7089e51244fc84d0af26d996b25679b9bacf05f4d14e5087bc062` | `f879c3e63f48910ac825e833042bda21cd4b87cbb483ddaeb0e1a0ace1c48770` |
| `Toy.RA.fpUpdateP_op_nonvacuity` | `Quot.sound`, `propext` | 32 | `b4194b83755f90ea7f578aa4bf34062ac71affdb6dbcc6f9c62996ed23a90463` | `2a139d42c991a20315dcbeb208af8c70c0d9e7fe167f47a87cd7d96538f466ad` |
| `Toy.RA.fpUpdate_bare_noRightIdOnValid_counterexample` | `none` | 20 | `f771c20d45e15539456834b5a12c0523d8d483757b2d569585c25b49651ab5ff` | `e0aa32f22ec3d50c39a28d185bcfbb8b1287da6deeecaf031d91f04678f7be7c` |
| `Toy.RA.fpUpdate_bare_noUnit_counterexample` | `none` | 20 | `512c7f87ab224391371df0124cf6075656831e9803c20c7cfe4c237faec97d4a` | `4bce38ba53bb1a9fd4d43503a134529fd4824b4847f7eec480940a8e4e707e9f` |
| `Toy.RA.fpUpdate_bare_rightIdOnValid_noValidOpL_counterexample` | `propext` | 23 | `3ab0fbf602960813ae48f476f8d1b3b16e2678b49348e4ed7e5630298d37d8a4` | `fd9f0a28bb0d4491af3cbb945b75847546521a1f514adf7c4d92fce3aed223e5` |
| `Toy.RA.fpUpdate_drop_right_noValidOpL_counterexample` | `propext` | 11 | `174a0f7fa306faf40564f8fb871784cacce9dd3c564b69aece363de88941ee0f` | `c7caaa32af8aba06b110ef5ea2ec79e8af85b0256ba45859f8c714d48c62f3d1` |
| `Toy.RA.fpUpdate_drop_right_nonAssoc_counterexample` | `propext` | 19 | `60756af14e2512e2fdd7f3d24420c32a7823d77334e07016f500c6be14e44ada` | `aa114ad03b4c05733ea693d0b8468aac9bba06dd2fdfb9225e1018f0cc8fa1e1` |
| `Toy.RA.fpUpdate_drop_right_nonComm_counterexample` | `propext` | 13 | `cd2536f3288ebd3b504690daeb8a733c6f12537b17fd63088a2fc7c3b0a5e7d2` | `58c20bf3cb9b4191f459c7bd0cb5554ddfdcd39ba724c4e6b311eed9665340a0` |
| `Toy.RA.fpUpdate_drop_right_nonvacuity` | `Quot.sound`, `propext` | 32 | `bbbd7633d6979d6e6284f21bc4c14e2bb4d1d9692b1881f7debe14bae4a98a6f` | `94c83327cd76e57171776fbf92a39ebb2d11a81bd36f32c2d7eda21ca786e9c0` |
| `Toy.RA.fpUpdate_frame_right_noUpdate_counterexample` | `Quot.sound`, `propext` | 15 | `caa2f4caf73d0fef3e7483b46ffa4859b2a156d2abf8346d6e98de6f2a0ed912` | `d58518121f6be9f92c1758f7564131d797c98e510a27fc55f0c37146ede0f960` |
| `Toy.RA.fpUpdate_frame_right_nonAssoc_counterexample` | `propext` | 19 | `14bd8868d622a6e8095fdb32aee5bc8b08eea0a387c27d2a49614a5acb84f977` | `aa114ad03b4c05733ea693d0b8468aac9bba06dd2fdfb9225e1018f0cc8fa1e1` |
| `Toy.RA.fpUpdate_frame_right_nonvacuity` | `Quot.sound`, `propext` | 31 | `e9ce22caef2536181d0ef27beaa53efab7dc777079b8cc62551e33c0c99907fa` | `c3a07ec40f443e56acff52aa6c34e0a08489e1c4f3d04793ec15a0b83346c87c` |
| `Toy.RA.fpUpdate_iff_bare_of_rightIdOnValid_validOpL_nonvacuity` | `Quot.sound`, `propext` | 17 | `7b11eade67244259a675f545c4d69e3361af27c0abb3f4afec1ddb308153a16e` | `16c103467d1dbac8a2bb11cf22b3dda412e3593431f0bf2d78ea1e111f792264` |
| `Toy.RA.fpUpdate_iff_bare_of_rightUnit_nonvacuity` | `Quot.sound`, `propext` | 36 | `4ad97175bad9ba521ca48958b14a699fe4f4b1ef97f34b2476e0b838ac96d20c` | `fabd764fe4c46c47f1d173998e6dfcf049fad86e0aab996b9983b6273ddfef9a` |
| `Toy.RA.fpUpdate_op_noUpdate1_counterexample` | `Quot.sound`, `propext` | 16 | `a19a766a08dea183ae06097bdc4975cdd4039f7a06b0bc87c8e7850dd77081a8` | `bae1d99ebc7f3189b8d97c42df4d774c4636437e381dd65df09507e24cd63ca8` |
| `Toy.RA.fpUpdate_op_noUpdate2_counterexample` | `Quot.sound`, `propext` | 16 | `a20400dafbae852e66d49f8161aded3378e331beca71f853601c7a9a88893afd` | `bae1d99ebc7f3189b8d97c42df4d774c4636437e381dd65df09507e24cd63ca8` |
| `Toy.RA.fpUpdate_op_nonAssoc_counterexample` | `propext` | 19 | `8290a6a0f20e03ce986010f6af920569f53a6e928ef59d96ee18650b549658ff` | `aa114ad03b4c05733ea693d0b8468aac9bba06dd2fdfb9225e1018f0cc8fa1e1` |
| `Toy.RA.fpUpdate_op_nonComm_counterexample` | `propext` | 13 | `c909fae27408d800dba1cea5b99fe9112d5b6e34e39fa30b4038c13c69e4243d` | `58c20bf3cb9b4191f459c7bd0cb5554ddfdcd39ba724c4e6b311eed9665340a0` |
| `Toy.RA.fpUpdate_op_nonvacuity` | `Quot.sound`, `propext` | 32 | `7807e3960c4f22925711e07e91d34cefc3cb3806c4eb9bb8c89207750a390fe6` | `ea3b26814d0b8779f8064e9bd585e5c6de3c48d661f7ce0dfa906b415a1bdf48` |
| `Toy.RA.fracVal_full_fpUpdate_iff_nonvacuity` | `Quot.sound`, `propext` | 37 | `48fa88b41a571495b4d791210c478df02a0f520ac2a21c96fd5390d0db4d89b0` | `96c03fcabce390c03cbe787f6d6ae708ea919dee801c96840a247bf91b200f47` |
| `Toy.RA.fracVal_full_value_change_control` | `Quot.sound`, `propext` | 42 | `00b6da3986a618ed5df57c682da013447c888de8fdea5f9200f26a971cefeb46` | `ea1591bf86c8abe08e1c2804925d86898ed5247719c1b54030ad25614fa032ab` |
| `Toy.RA.fracVal_partial_fpUpdate_iff_nonvacuity` | `Quot.sound`, `propext` | 38 | `7bba321761ed76ce7f2213d67e65acd4eab441fc7fbe8862d2eed5e6dd41c81e` | `00a5ee62cb0dd274d702ddaacea5475115ccf56c3d189dce49671a1c051643d7` |
| `Toy.RA.fracVal_partial_iff_full_counterexample` | `Quot.sound`, `propext` | 42 | `8ba49b11e5b49640b280397dc19f5df6dbbc7b411dbddfb7fea4226673b4ec01` | `ea1591bf86c8abe08e1c2804925d86898ed5247719c1b54030ad25614fa032ab` |
| `Toy.RA.fracVal_partial_same_value_counterexample` | `Quot.sound`, `propext` | 44 | `6b7f586a31bfc6fbf6af85b00e884b2111bc593aad1ce87a99a94b5273c47008` | `98285bd804a26626a78295d133d4d06b44621ae38fb350b25eb250b523a9c0a2` |
| `Toy.RA.fracVal_partial_value_change_impossible_nonvacuity` | `Quot.sound`, `propext` | 38 | `840677b724300bae99759f5d19f9ce7adb598602684c3a5ba3c15f0c3f2b87cf` | `00a5ee62cb0dd274d702ddaacea5475115ccf56c3d189dce49671a1c051643d7` |
| `Toy.RA.idempotent_noncomm_validOpL_witness` | `none` | 14 | `081ef648d9368dd8fc2b6cf02e2e6ecf0acc78e618b416b3c0883b97ef0fb7bb` | `6786c3465f763360d1e8d10d1cbe8b262a16198427ff280c231e64c38fbd6eea` |
| `Toy.RA.opComm_alone_not_two_sided` | `propext` | 22 | `5dcfaae1f2d5741fd694dbe934df2bb8de0dac9e8b22719739e5b2fc50f0d69e` | `4d34887d153a10510830197f697607033b8327d89e9972d4b1751757550d9760` |
| `Toy.RA.two_element_comm_validOpL_witness` | `none` | 14 | `f760f361944b3477037ac6a4e63a1a7910167a1f60c6796b94caa54a4c234114` | `d58fddabafae8b06e30dd5a02424110d4bf50dc4ccdd7d8a3084fd252e49e7d9` |

### 2. Primary Sources and Pinned Upstream Revisions

All bibliographic records were verified via Crossref (`https://api.crossref.org/works/<DOI>`) and all Git commit/tag revisions were verified via the GitHub API (`observed_at: 2026-11-20`):

1. **Iris (Rocq) & LaTeX Technical Documentation:** `github.com/rocq-iris/iris`, tag `iris-4.4.0`, commit `82dbf5e7a11d7ffaafe78e95186b5b376f4df732` — `iris/algebra/cmra.v` (`cmra_unit_cmra_total`, l. 695), `iris/algebra/updates.v` (`cmra_update` / `cmra_updateP` option-frame note ll. 4–17, `cmra_update_exclusive` l. 50, `cmra_updateP_op` ll. 78–88, `cmra_update_op` ll. 93–96, `cmra_update_op_l` l. 105, `cmra_update_included` l. 110, `cmra_total_update` ll. 123–133, `cmra_discrete_total_update` l. 155), `iris/algebra/local_updates.v` (`local_update` l. 5, `op_local_update_discrete` l. 34, `local_update_unital_discrete` l. 124, `option_local_update` ll. 191–200), `iris/algebra/excl.v` (`excl_exclusive` l. 111), `iris/algebra/agree.v` (`agree_idemp` l. 107, `agree_op_inv` l. 189, `to_agree_uninj` l. 207, `to_agree_op_valid_L` l. 269), `iris/algebra/frac.v` (`frac_full_exclusive` l. 45), `iris/algebra/lib/dfrac_agree.v` (`to_dfrac_agree_exclusive` l. 26, `frac_agree_update_2` l. 115), `iris/algebra/auth.v` (`auth_both_valid_discrete` l. 278, `auth_update` ll. 321–327), `tex/algebra.tex` (§RA ll. 149–156), and `tex/constructions.tex` (§Exclusive Camera, §Agreement, §Fractions, §Authoritative).
2. **`iris-lean` (Lean 4):** `github.com/leanprover-community/iris-lean`, commit `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` — `Iris/Iris/Algebra/Updates.lean` (`Iris.Update.exclusive`, `Iris.UpdateP.op`, `Iris.Update.op`, `Iris.Update.op_l`, `Iris.Update.discrete_total` ll. 169–174), `Iris/Iris/Algebra/Excl.lean` (anonymous `Exclusive` instance for `Excl` carrying `@[rocq_alias excl_exclusive]`, ll. 225–226), `Iris/Iris/Algebra/Agree.lean` (`toAgree_op_valid_iff_eq`, `Agree.op_inv`), `Iris/Iris/Algebra/Frac.lean` (`instExclusiveQp1`), `Iris/Iris/Algebra/Lib/DFracAgree.lean` (`DFracAgree.mk_exclusive`, `Frac.update₂`), `Iris/Iris/Algebra/Auth.lean` (`auth_update_ord` ll. 536–542, `auth_update` ll. 566–567), and `Iris/Iris/Algebra/LocalUpdates.lean` (`LocalUpdate.option`).
3. **F\* `FStar.PCM`:** `github.com/FStarLang/FStar`, `ulib/FStar.PCM.fst` at commit `6089523e69201bb5844200c74b1eabfc640f31ab` — `pcm`, `frame_preserving_upd`, `exclusive` and `exclusive_is_frame_preserving` (ll. 187–195, unital update `x ⤳ one`), `compose_frame_preserving_updates`, `frame_preserving_subframe`. Associated paper: N. Swamy, A. Rastogi, A. Fromherz, D. Merigoux, D. Ahman, and G. Martínez, *SteelCore: An Extensible Concurrent Separation Logic for Effectful Dependently Typed Programs*, PACMPL 4 (ICFP), 2020, DOI `10.1145/3409003`.
4. **Jung et al. (POPL 2015):** R. Jung, D. Swasey, F. Sieczkowski, K. Svendsen, A. Turon, L. Birkedal, and D. Dreyer, *Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning*, POPL 2015, pp. 637–650, DOI `10.1145/2676726.2676980` (`FPUPD` p. 4, §3.1 `EX(X)`, §3.2 `FRAC(X)`, §3.6 `AUTH`/`AUTHUPD`).
5. **Jung et al. (JFP 2018):** R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal, and D. Dreyer, *Iris from the ground up: A modular foundation for higher-order concurrent separation logic*, Journal of Functional Programming 28 (2018), e20, pp. 1–73, DOI `10.1017/S0956796818000151` (Fig. 3 p. 9, §2.1 fn. 6 p. 12, §3.1 pp. 18–19, §6.3.3 p. 49 background).
6. **Dockins, Hobor, and Appel (APLAS 2009):** R. Dockins, A. Hobor, and A. W. Appel, *A Fresh Look at Separation Algebras and Share Accounting*, APLAS 2009, pp. 161–177 (ISBN `978-3-642-10671-2` / `978-3-642-10672-9`), DOI `10.1007/978-3-642-10672-9_13` (§2 multi-unit separation algebras axiom (15), tree-share background).
7. **Bornat, Calcagno, O'Hearn, and Parkinson (POPL 2005):** R. Bornat, C. Calcagno, P. O'Hearn, and M. Parkinson, *Permission accounting in separation logic*, POPL 2005, pp. 259–270, DOI `10.1145/1040305.1040327`.
8. **Boyland (SAS 2003):** J. Boyland, *Checking Interference with Fractional Permissions*, SAS 2003, pp. 55–72 (ISBN `978-3-540-40325-8` / `978-3-540-44898-3`), DOI `10.1007/3-540-44898-5_4`.
9. **Krebbers et al. (ESOP 2017, background):** R. Krebbers, R. Jung, A. Bizjak, J.-H. Jourdan, D. Dreyer, and L. Birkedal, *The Essence of Higher-Order Concurrent Separation Logic*, ESOP 2017, pp. 696–723 (ISBN `978-3-662-54433-4` / `978-3-662-54434-1`), DOI `10.1007/978-3-662-54434-1_26` (§3.3 unital `Auth(M)`, §4.2 `Ag(X)` validity).
10. **Calcagno, O'Hearn, and Yang (LICS 2007, background):** C. Calcagno, P. W. O'Hearn, and H. Yang, *Local Action and Abstract Separation Logic*, LICS 2007, pp. 366–378, DOI `10.1109/LICS.2007.30`.
11. **Jung, Krebbers, Birkedal, and Dreyer (ICFP 2016, background):** R. Jung, R. Krebbers, L. Birkedal, and D. Dreyer, *Higher-order ghost state*, ICFP 2016, pp. 256–269, DOI `10.1145/2951913.2951943` (bibliographic context for higher-order cameras excluded by **NC-G4**).

## Revalidation

### 1. Primary Automated Revalidation (`support/revalidate.py`)

Prerequisites: `elan` (so `lake` selects `leanprover/lean4:v4.34.1` from `lean/lean-toolchain`) and `python3` (standard library only). Run from this package's root directory:

```bash
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package directory: it copies `lean/` into a fresh temporary directory and checks four invariants:

1. **Clean build:** `lake build` succeeds under `leanprover/lean4:v4.34.1`.
2. **Token hygiene:** No `.lean` source (outside comments) contains `sorry`, `admit`, `native_decide`, or an `axiom` declaration.
3. **Kernel axiom audit:** Via `Lean.collectAxioms`, every non-internal declaration in the `Toy` library depends only on `{propext, Classical.choice, Quot.sound}`.
4. **Statement and definition-closure hash integrity:** For every Lean declaration referenced in `results.json` (`lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` fields) and recorded in `audit/statements.json`, it recomputes:
   - `statement_sha256`: SHA-256 of `toString (repr ci.type)` (the kernel `Expr` structure of the declaration's type, including binder names and binder kinds); and
   - `closure_sha256` (plus `closure_size`): SHA-256 of the sorted, newline-joined strings `"<name> : <repr type>"` (for package theorems/inductives/constructors) and `"<name> : <repr type> := <repr value>"` (for package definitions, excluding theorem proof terms) across all `Toy.*` constants transitively reachable from the statement type, verifying exact equality with `audit/statements.json`.

Exit status `0` and final line `REVALIDATED` confirm that every check passed.

### 2. Standalone CLI Revalidation (`elan` / `lake` / `python3` + `lean/RevalidationAudit.lean`)

To run the build and kernel audit directly without `support/revalidate.py`, copy `lean/` to a scratch directory (or work inside `lean/`), build the `Toy` library, execute the standalone reflection script `lean/RevalidationAudit.lean` (which lies outside the `Toy` library target in `lean/lakefile.toml`), and compare its JSON output against `audit/axioms.json` and `audit/statements.json`:

```bash
 WORK=$(mktemp -d)
 cp -R lean "$WORK/lean"
 cp results.json "$WORK/results.json"
 cp -R audit "$WORK/audit"
 (cd "$WORK/lean" && lake build && lake env lean RevalidationAudit.lean) > "$WORK/audit_out.txt"
 python3 - "$WORK" <<'PY'
import hashlib, json, pathlib, re, sys
root = pathlib.Path(sys.argv[1])
m = re.search(r'REVALIDATION_AUDIT_JSON (\{.*\})', (root / 'audit_out.txt').read_text())
assert m, 'missing REVALIDATION_AUDIT_JSON line'
payload = json.loads(m.group(1))
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
got_axioms = {d['name']: sorted(d['axioms']) for d in payload['decls']}
bad = {k: v for k, v in got_axioms.items() if set(v) - allowed}
assert not bad, f'disallowed axioms: {bad}'
rec_axioms = json.loads((root / 'audit/axioms.json').read_text())['declarations']
assert got_axioms == rec_axioms, 'axiom table drift'
rec_stmts = json.loads((root / 'audit/statements.json').read_text())['statements']
for s in payload['stmts']:
    assert not s.get('missing'), f"missing declaration: {s['name']}"
    got = {
        'statement_sha256': hashlib.sha256(s['type_repr'].encode()).hexdigest(),
        'closure_sha256': hashlib.sha256('\n'.join(s['closure']).encode()).hexdigest(),
        'closure_size': len(s['closure']),
    }
    assert rec_stmts[s['name']] == got, f"hash mismatch for {s['name']}: {got}"
print(f"OK: {len(got_axioms)} declarations audited; {len(payload['stmts'])} statement/closure hashes verified.")
PY
 rm -rf "$WORK"
```
