# Permission accounting in Lean 4: fractional permissions, counting permissions, and per-byte sharing depth

## Summary

This package is a self-contained, Mathlib-free Lean 4 development (namespace `Toy.Perm`, Lean `v4.34.1`) of three permission-accounting designs at the level of partial algebras: fractional permissions, counting permissions (sources and read tokens), and a per-byte sharing-depth design in which each view of an address holds a cell `shared d v` or `borrowed`. It states and kernel-checks 21 results about their algebraic laws, how permissions split, whether the sharing-depth design admits a separation-algebra reading, which structure-preserving translations exist between counting and fractions, and who can bound the number of outstanding readers. Every result is a theorem about a toy model; connections to real logics or tools are separate, labelled modeling bridges.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The plain-language claim of each result, verbatim from `results.json` (each states its key hypotheses):

- **R1a-frac-count-pcm-laws** (theorem, T0, shallow). The fractional algebra on [0,1] intersected with the rationals (unit 0, composite = sum when it is at most 1) and the counting algebra on Option Int (unit none, Dockins-Hobor-Appel Definition 9) are each commutative, (strongly) associative, unital, cancellative and positive (a . b = unit implies a = unit) partial commutative monoids.
- **R1b-disjointness-fails** (counterexample, T0, definitional). Disjointness (a . a = b implies a = b) fails in the fractional algebra, in the counting algebra, and in the depth-sum algebra on cells over every inhabited payload type V; over the empty payload type the depth-sum algebra satisfies disjointness (proved separately, as the tightness counterexample Toy.Perm.cellSumAlg_empty_disjointness for the hypothesis Nonempty V).
- **R2a-frac-no-atoms** (theorem, T0, shallow). Every non-empty fractional permission q is the composite of two non-empty permissions, namely half q . half q = q with half q non-zero.
- **R2b-frac-halving-split** (theorem, T0, shallow). For every fractional permission q and every n >= 1, the halving split halvingSplit q n (which is [q] for n = 1 and [q/2, q/4, ..., q/2^(n-1), q/2^(n-1)] for n >= 2) has exactly n pieces and composes in list order to exactly q, and if q is non-empty every piece is non-empty (first theorem); for q = 1 the pieces recombine to the full permission, which is exclusive (second theorem).
- **R2c-count-token-atomic** (theorem, T0, shallow). In the counting algebra a single read token is atomic: whenever a . b equals one read token, a or b is the empty permission.
- **R2d-count-split-through-source** (theorem, T0, shallow). If a source permission with count n is the composite of two non-empty parts, then one part is a source with count n + k and the other is a bundle of exactly k >= 1 tokens.
- **R3b-depth-fpu-characterization** (characterization, T1, shallow). With respect to the sharing-depth compatibility relation, a cell update a to b is frame-preserving (every cell compatible with a is compatible with b) iff b is borrowed, or a is a writer (depth 0), or a and b are both readers (positive depth) with the same payload.
- **R3c-depth-sum-pcm-exists** (theorem, T1, shallow). The depth-sum algebra on cells (borrowed is the unit; two readers with equal payload compose to a reader whose depth is the sum; everything else undefined) is a commutative, associative, unital, cancellative and positive partial commutative monoid whose definedness relation is exactly the sharing-depth compatibility relation.
- **R3d-restoring-steps-not-frame-preserving** (impossibility, T1, definitional). For any partial algebra A on any carrier and any interpretation e of cells in it: if two depth-1 readers with payload v are compatible, a depth-0 writer with payload v is incompatible with a depth-1 reader with payload v, and borrowed is compatible with a depth-1 reader (all after interpretation by e), then neither the last end-share e(shared 1 v) to e(shared 0 v) nor the end-borrow e(borrowed) to e(shared 0 v) is a frame-preserving update (single right frames).
- **R3e-no-local-token-return-beside-other-reader** (impossibility, T1, definitional). In an associative partial algebra (strong associativity; commutativity and the unit law not assumed), there is no interpretation e of cells and token t such that the state 'two depth-1 views with payload v and the outstanding share t' is consistent when written with the two views composed first ((e(shared 1 v) . e(shared 1 v)) . t is defined), absorbing t turns a depth-1 view into the depth-0 cell (e(shared 1 v) . t = e(shared 0 v)), and a depth-1 reader cannot be composed with the depth-0 cell (e(shared 1 v) . e(shared 0 v) undefined).
- **R3f-depth-transition-characterization** (characterization, T1, shallow). In a valid configuration (pairwise-compatible cells of the views at one address), applying a per-view operation t to view i whose cell is c, where t is defined on c with result c', yields a valid configuration iff, in case t restores exclusivity on c, every other view at that address is borrowed; the steps that restore exclusivity are exactly the last end-share (endShare on shared 1 v) and the end-borrow (endBorrow on borrowed), so write, borrow, share and end-share from depth at least 2, when defined on view i's cell, always yield a valid configuration; equivalently, stepAt cfg i t is enabled iff view i exists, t is defined on its cell, and the borrowed condition holds for restoring steps.
- **R3g-depth-sum-not-faithful** (counterexample, T1, definitional). For every payload v, the configurations [shared 2 v] and [shared 1 v, shared 1 v] have the same depth-sum composite shared 2 v, yet from the first the single view regains exclusivity by two enabled end-shares, while in the second neither view's end-share is enabled (immediate enabledness of one step).
- **R4a-bounded-count-embeds-in-frac** (theorem, T1, shallow). For every bound N, counting permissions with counts at most N form a partial commutative monoid, and the explicit map countEmbed N (bundle of k tokens to k/(3N+1), source with n outstanding tokens to 1 - n/(3N+1), empty to 0) is injective, sends the unit to 0, satisfies a . b = c iff f a . f b = f c for all a, b, c (it preserves every defined composite and reflects every fractional composite that lands in its image), maps exactly the exclusive elements to exclusive fractions, and maps exactly the non-empty permissions to non-zero fractions.
- **R4b-bounded-embedding-not-reflecting** (impossibility, T1, shallow). For every bound N >= 1, there is no map f from N-bounded counting permissions to fractional permissions that preserves every defined composite and reflects compatibility (any two permissions whose images are compatible fractions are compatible in N-bounded counting). More precisely, for every N >= 1 and every map f that preserves every defined composite: two sources source N are incompatible and two bundles tokens N are incompatible in N-bounded counting, yet source N . tokens N = total forces f(source N) + f(tokens N) <= 1, so at least one of the two pairs (two copies of source N, or two copies of tokens N) has compatible fractional images. Which pair it is depends on f: for every N >= 1 there is a composition-preserving map that also sends the unit to 0 and total to 1 under which two bundles tokens N have incompatible images (tokens N to 2/3, source N to 1/3), and another under which two sources source N have incompatible images (tokens N to 1/3, source N to 2/3).
- **R4c-no-count-to-frac-with-readable-token** (impossibility, T1, shallow). There is no map from (unbounded) counting permissions to fractional permissions that preserves every defined composite and sends the single read token to a non-zero fraction, because bundles of n tokens exist for every n while fractions are bounded by 1.
- **R4d-no-frac-to-count-preserving-exclusivity** (impossibility, T1, shallow). In any partial algebra A, if h . h = a then no map from A to counting permissions that preserves every defined composite sends a to the total counting permission, because the total counting permission is never a composite x . x; in particular no such map from the fractions, or from the finitely divisible half-grid {0, 1/2, 1}, sends 1 = 1/2 . 1/2 to the total permission.
- **R4e-no-frac-to-count-preserving-nonemptiness** (characterization, T1, shallow). Every map from fractional to counting permissions that preserves every defined composite sends every fraction to the empty counting permission; in particular no such map sends even a single fraction (for instance 1) to a non-empty counting permission, because repeated halving would require token bundles whose size halves forever.
- **R5a-count-source-bounds-outstanding-holders** (theorem, T1, shallow). If a counting source with count n together with a list of non-empty counting permissions has a defined composite (the configuration is consistent; it need not account for the whole permission), the list has at most n elements; if moreover the configuration pools to the total permission and n > 0, the list has at least one element; so in a complete configuration a source with count 1 has exactly one other non-empty piece.
- **R5b-count-atomic-complete-iff** (theorem, T0, shallow). If every outstanding piece is a single read token, then a source with count n together with them pools to the total permission iff there are exactly n of them; in particular, for every n, the total counting permission is the composite of a source with count n and n single read tokens (second theorem).
- **R5d-frac-no-element-bounds-holders** (impossibility, T1, shallow). There is no non-exclusive fractional permission p and number N such that every list of non-empty pieces completing p to the full permission has at most N elements; explicitly, for every p other than 1 and every n >= 1, the halving split of 1 - p into n pieces gives n non-empty pieces that together with p pool to 1. Unlike a counting source, no non-exclusive fractional piece bounds the number of other holders (the exclusive piece 1 bounds them by 0).
- **R5e-reader-side-lastness-undetermined** (theorem, T1, shallow). In both designs a returning reader's own piece does not determine whether it is the last one out: for every token bundle tokens k, it completes source k alone, does not complete source (k+1) alone, and does complete source (k+1) together with one more read token; for every fraction q other than 1, it completes 1 - q alone, does not complete (1 - q)/2 alone, and does complete it together with a second piece (1 - q)/2.

Each result has explicit non-claims, listed first under **Boundaries**; read them before relying on a result. All 21 results are fully proved; none was disproved or dropped, and no hypothesis has `unknown` tightness.

## Applicability

**Model fidelity: toy model.** Every result concerns definitions in the Lean namespace `Toy.Perm`, not a production verifier, program logic or memory model. The definitions are meant to capture:

- *Fractional permissions*: rationals in `[0, 1]` with `0` adjoined as an explicit unit and composition = sum when the sum is at most `1` (Boyland-style fractions; Dockins–Hobor–Appel Definition 8). Gaps: Bornat et al. use `(0, 1]` and treat an absent heap cell as the unit; real-valued fractions are not treated separately.
- *Counting permissions*: `Option Int`, where `some n` (`n ≥ 0`) is a source with `n` split-off read tokens (`some 0` is the total permission), `some (-k)` (`k ≥ 1`) a bundle of `k` tokens, and `none` the empty permission (Bornat et al.'s `(Z, ⋆1)` with an explicit unit; exactly Dockins–Hobor–Appel Definition 9). `N`-bounded counting (`CountB N`) restricts magnitudes to at most `N`.
- *Per-byte sharing depth*: a single-address restatement of the permission cells of a heap-model prototype for the Aeneas Lean backend (an open, unmerged pull request, quoted under **Evidence**; it is context, not a subject). A cell is `shared d v` (readable; exclusive iff `d = 0`; `d` counts local outstanding shares) or `borrowed`; a configuration lists the cells of all active views at the address, and an operation is enabled iff it is defined on the cell and the resulting configuration is pairwise compatible. Gaps: allocation, multi-byte ranges, provenance, view creation and retirement (the prototype retires an independent shared exposure at depth 1 instead of decrementing it to depth 0), scoped return authority, and permissions held implicitly outside the explicit heap are not modelled.

**Algebraic conventions.** A partial algebra (`PartialAlg`) has a partial binary operation (`Option`-valued) and a designated unit; associativity is the strong (Kleene) form; each law is a separate proposition and is assumed only where stated. Frame-preserving updates are stated with single right frames (`PartialAlg.FramePreserving`); set-valued updates and Iris-style total-operation-plus-validity cameras with step-indexing are not modelled. Translations are maps into the plain fractional or counting algebra; enriched carriers (for example fractions paired with a token count, or authoritative elements) are not considered. There is no concurrency semantics and no program logic: operational words such as *holder*, *reader*, *returns* or *hands on* describe modeling bridges, labelled `derived (modeling bridge)` where they occur.

**Subjects and their relationship.** `REPORT.json` lists the Lean 4 toolchain release that kernel-checked every theorem, and the two papers whose models the definitions restate (Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; Dockins, Hobor & Appel, APLAS 2009). The theorems are statements about the Lean definitions, checked by that toolchain; their reading as statements about the papers' models rests on the definitional correspondence stated under **Findings → Definitions** (a derived claim). Other works are prior art for individual results and are cited per result.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only: no Mathlib and no Lake dependencies (`lean/lakefile.toml` declares one `[[lean_lib]]`, `ToyPerm`, and no `[[require]]`). Results were not checked under other Lean versions.

## Findings

Evidence roles: every theorem below has `Basis: execution (Lean kernel check)`: the Lake project builds under the pinned toolchain and every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound` (per-declaration record under **Evidence**). Any claim connecting a statement to a real system is a separate line `Basis: derived (modeling bridge)` with its reasoning.

### Definitions

The blocks below are abridged signatures (implicit arguments and proofs elided); the exact source is `lean/ToyPerm/*.lean`, and every definition in the closure of a result's statement is hashed under **Evidence**. Each core definition has proved positive and negative examples, named in place.


#### D1. Partial algebras and their laws (`ToyPerm/PCM.lean`)

```lean
structure PartialAlg (α : Type) where
  op : α → α → Option α      -- `none` = composite undefined
  unit : α

def Compat (A) (a b) : Prop      := (A.op a b).isSome = true
def Comm (A) : Prop              := ∀ a b, A.op a b = A.op b a
def Assoc (A) : Prop             := ∀ a b c, (A.op a b).bind (fun ab => A.op ab c)
                                            = (A.op b c).bind (fun bc => A.op a bc)
def UnitLeft (A) : Prop          := ∀ a, A.op A.unit a = some a
def IsPCM (A) : Prop             := A.Comm ∧ A.Assoc ∧ A.UnitLeft
def Cancel (A) : Prop            := ∀ a b c d, A.op a b = some d → A.op a c = some d → b = c
def Positive (A) : Prop          := ∀ a b, A.op a b = some A.unit → a = A.unit
def PositiveDHA (A) : Prop       := ∀ a b c, A.op a b = some c → A.op c c = some c → A.op a a = some a
                                                                    -- Dockins–Hobor–Appel (21)
def Disjointness (A) : Prop      := ∀ a b, A.op a a = some b → a = b     -- Dockins–Hobor–Appel (23)
def Exclusive (A) (a) : Prop     := ∀ b, A.Compat a b → b = A.unit
def opList (A) : List α → Option α
  | []      => some A.unit
  | a :: as => (A.opList as).bind (A.op a)                -- a₁ · (a₂ · (… · (aₙ · unit)))
def FramePreserving (A) (a b) : Prop := ∀ f, A.Compat a f → A.Compat b f
def PreservesUnit (A) (B) (f) : Prop := f A.unit = B.unit
def PreservesOp (A) (B) (f) : Prop   := ∀ a b c, A.op a b = some c → B.op (f a) (f b) = some (f c)
```

* `Assoc` is associativity in the strong sense: `(a·b)·c` is defined iff `a·(b·c)` is, and then they agree.
* `Positive` is the form used throughout. `PositiveDHA` is Dockins–Hobor–Appel's axiom (21); the two are
  equivalent in commutative, unital, cancellative algebras (`PartialAlg.positive_iff_positiveDHA`) but not in
  general (`z2UnitAlg`, the group ℤ/2ℤ with a fresh unit adjoined, is a PCM that is `Positive` but not
  `PositiveDHA`: `PartialAlg.z2UnitAlg_positive_not_positiveDHA`).
* `Exclusive a` captures a write (full) permission: whoever holds it knows nobody else holds anything. It is
  intended for unital algebras with at least one non-unit element (in an algebra where nothing is compatible
  with `a`, `a` is vacuously exclusive).
* `FramePreserving a b` captures a local ghost update with single right frames (the unit stands for the empty
  frame). Any notion of frame-preserving update that includes this single-frame condition implies it, so
  refuting `FramePreserving` refutes such notions too; set-valued updates are not covered.
* `PreservesOp f` is the composition-preserving half of a morphism; it says nothing about undefined composites.

Reference algebras used as examples: `exclAlg` (Bool; `false` unit, `true·true` undefined — the
whole-or-nothing model), `mod3Alg` (addition mod 3, Dockins–Hobor–Appel's anti-resource example),
`orAlg` (idempotent "or"), `leftAlg` (left-biased, non-commutative), `nonAssocAlg`, `emptyOpAlg`,
`z2UnitAlg`.

Definition examples (all proved): `exclAlg_compat_examples`, `exclAlg_comm` / `leftAlg_not_comm`,
`exclAlg_assoc` / `nonAssocAlg_not_assoc`, `exclAlg_unitLeft` / `emptyOpAlg_not_unitLeft`,
`exclAlg_isPCM` / `leftAlg_not_isPCM`, `exclAlg_cancel` / `orAlg_not_cancel`,
`exclAlg_positive` / `mod3Alg_not_positive`, `exclAlg_positiveDHA` / `z2UnitAlg_positive_not_positiveDHA`,
`exclAlg_disjointness` / `mod3Alg_not_disjointness`,
`exclAlg_true_exclusive` / `orAlg_true_not_exclusive`, `opList_examples` / `opList_exclAlg_true_true`,
`exclAlg_drop_framePreserving` / `exclAlg_create_not_framePreserving`, `id_preserves` /
`const_true_not_preserves`.

Signatures of the declarations named in this subsection that are not printed elsewhere in this report (exact output of Lean's `PrettyPrinter.ppSignature`, with the namespaces opened as under **Results**; for the reference algebras, which are definitions, the signature gives the carrier, and the operation is as described above and in `ToyPerm/PCM.lean`):

```lean
Toy.Perm.z2UnitAlg : PartialAlg (Fin 3)

Toy.Perm.exclAlg : PartialAlg Bool

Toy.Perm.mod3Alg : PartialAlg (Fin 3)

Toy.Perm.orAlg : PartialAlg Bool

Toy.Perm.leftAlg : PartialAlg Nat

Toy.Perm.nonAssocAlg : PartialAlg (Fin 3)

Toy.Perm.emptyOpAlg : PartialAlg Nat

Toy.Perm.PartialAlg.exclAlg_compat_examples : exclAlg.Compat true false ∧ ¬exclAlg.Compat true true

Toy.Perm.PartialAlg.exclAlg_comm : exclAlg.Comm

Toy.Perm.PartialAlg.leftAlg_not_comm : ¬leftAlg.Comm

Toy.Perm.PartialAlg.exclAlg_assoc : exclAlg.Assoc

Toy.Perm.PartialAlg.nonAssocAlg_not_assoc : ¬nonAssocAlg.Assoc

Toy.Perm.PartialAlg.exclAlg_unitLeft : exclAlg.UnitLeft

Toy.Perm.PartialAlg.emptyOpAlg_not_unitLeft : ¬emptyOpAlg.UnitLeft

Toy.Perm.PartialAlg.exclAlg_isPCM : exclAlg.IsPCM

Toy.Perm.PartialAlg.leftAlg_not_isPCM : ¬leftAlg.IsPCM

Toy.Perm.PartialAlg.exclAlg_cancel : exclAlg.Cancel

Toy.Perm.PartialAlg.orAlg_not_cancel : ¬orAlg.Cancel

Toy.Perm.PartialAlg.exclAlg_positive : exclAlg.Positive

Toy.Perm.PartialAlg.mod3Alg_not_positive : ¬mod3Alg.Positive

Toy.Perm.PartialAlg.exclAlg_positiveDHA : exclAlg.PositiveDHA

Toy.Perm.PartialAlg.exclAlg_disjointness : exclAlg.Disjointness

Toy.Perm.PartialAlg.mod3Alg_not_disjointness : ¬mod3Alg.Disjointness

Toy.Perm.PartialAlg.exclAlg_true_exclusive : exclAlg.Exclusive true

Toy.Perm.PartialAlg.orAlg_true_not_exclusive : ¬orAlg.Exclusive true

Toy.Perm.PartialAlg.opList_examples :
  exclAlg.opList [] = some false ∧
    exclAlg.opList [false, true] = some true ∧ mod3Alg.opList [1, 1, 1] = some 0

Toy.Perm.PartialAlg.opList_exclAlg_true_true : exclAlg.opList [true, true] = none

Toy.Perm.PartialAlg.exclAlg_drop_framePreserving : exclAlg.FramePreserving true false

Toy.Perm.PartialAlg.exclAlg_create_not_framePreserving : ¬exclAlg.FramePreserving false true

Toy.Perm.PartialAlg.id_preserves {α : Type} (A : PartialAlg α) :
  A.PreservesUnit A id ∧ A.PreservesOp A id

Toy.Perm.PartialAlg.const_true_not_preserves :
  (¬exclAlg.PreservesUnit exclAlg fun x => true) ∧ ¬exclAlg.PreservesOp exclAlg fun x => true
```

#### D2. Fractional permissions (`ToyPerm/Frac.lean`)

```lean
structure FracPerm where
  val : Rat
  nonneg : 0 ≤ val
  le_one : val ≤ 1

FracPerm.zero := ⟨0, _, _⟩      FracPerm.full := ⟨1, _, _⟩
FracPerm.half q := ⟨q.val / 2, _, _⟩        FracPerm.compl q := ⟨1 - q.val, _, _⟩
FracPerm.halfPow 0 = full,  halfPow (k+1) = half (halfPow k)          -- 1/2^k
FracPerm.ofRat r := if h : 0 ≤ r ∧ r ≤ 1 then ⟨r, h.1, h.2⟩ else zero   -- clamp

def fracOp (p q : FracPerm) : Option FracPerm :=
  if h : p.val + q.val ≤ 1 then some ⟨p.val + q.val, _, h⟩ else none
def fracAlg : PartialAlg FracPerm := { op := fracOp, unit := zero }

def halvingSplit (q : FracPerm) : Nat → List FracPerm
  | 0 => []
  | 1 => [q]
  | n + 2 => half q :: halvingSplit (half q) (n + 1)      -- [q/2, q/4, …, q/2^(n-1), q/2^(n-1)] for n ≥ 2
```

Meaning: Boyland-style fractional permissions with `0` adjoined as the empty permission
(Dockins–Hobor–Appel Definition 8). Representation choice: Lean core `Rat` is stored normalised
(coprime numerator, positive denominator), so `=` on `FracPerm` is equality of rational values and
laws such as cancellation are stated with plain `=`; core supplies ordered-field reasoning. The
fractions used in the splitting, disjointness and holder-counting results are dyadic, so those
results apply to the dyadic sub-algebra too; the bounded-counting map (D5, R4a) uses multiples of
`1/(3N+1)`.

Supporting lemmas (proved): `fracOp_eq_some_iff : fracOp p q = some r ↔ p.val + q.val = r.val`;
`fracOp_eq_none_iff`; `fracAlg_compat_iff : Compat p q ↔ p.val + q.val ≤ 1`;
`fracAlg_opList ps = if Σ ≤ 1 then some (ofRat Σ) else none` (Σ = sum of amounts);
`fracAlg_exclusive_iff : Exclusive fracAlg p ↔ p = full`.

Definition examples (proved): `ofRat_half_val` / `not_fracPerm_amounts` (3/2 and −1/2 rejected,
clamped to 0), `half_compl_halfPow_examples`, `fracAlg_half_half` (1/2·1/2 = 1) /
`fracAlg_full_half` (1·1/2 undefined), `halvingSplit_full_three` ([1/2, 1/4, 1/4]).

Signatures of the declarations named in this subsection that are not printed elsewhere in this report (exact output of Lean's `PrettyPrinter.ppSignature`, with the namespaces opened as under **Results**; `Toy.Perm.FracPerm.not_fracPerm_amounts` is printed with `set_option pp.numericTypes true`, so that the type `Rat` of its numerals is shown):

```lean
Toy.Perm.fracOp_eq_some_iff {p q r : FracPerm} : fracOp p q = some r ↔ p.val + q.val = r.val

Toy.Perm.fracOp_eq_none_iff {p q : FracPerm} : fracOp p q = none ↔ 1 < p.val + q.val

Toy.Perm.fracAlg_compat_iff {p q : FracPerm} : fracAlg.Compat p q ↔ p.val + q.val ≤ 1

Toy.Perm.fracAlg_opList (ps : List FracPerm) :
  fracAlg.opList ps = if (List.map val ps).sum ≤ 1 then some (ofRat (List.map val ps).sum) else none

Toy.Perm.fracAlg_exclusive_iff (p : FracPerm) : fracAlg.Exclusive p ↔ p = full

Toy.Perm.FracPerm.ofRat_half_val : (ofRat (1 / 2)).val = 1 / 2

Toy.Perm.FracPerm.not_fracPerm_amounts :
  ¬((0 : Rat) ≤ (3 / 2 : Rat) ∧ (3 / 2 : Rat) ≤ (1 : Rat)) ∧
    ¬((0 : Rat) ≤ (-1 / 2 : Rat) ∧ (-1 / 2 : Rat) ≤ (1 : Rat)) ∧ ofRat (3 / 2 : Rat) = zero

Toy.Perm.FracPerm.half_compl_halfPow_examples :
  full.half.val = 1 / 2 ∧ full.half.compl.val = 1 / 2 ∧ (halfPow 2).val = 1 / 4 ∧ full.compl = zero

Toy.Perm.fracAlg_full_half : fracAlg.op full full.half = none

Toy.Perm.halvingSplit_full_three : List.map val (halvingSplit full 3) = [1 / 2, 1 / 4, 1 / 4]
```

#### D3. Counting permissions (`ToyPerm/Count.lean`)

```lean
abbrev Count := Option Int
Count.total := some 0       Count.source n := some (n : Int)       Count.readToken := some (-1)
def Count.tokens : Nat → Count          -- a bundle of k tokens; the empty bundle is the empty permission
  | 0 => none
  | k + 1 => some (-((k + 1 : Nat) : Int))

def countOp : Count → Count → Option Count
  | none, b => some b
  | a, none => some a
  | some i, some j =>
    if (i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ (i < 0 ∧ j < 0)) then some (some (i + j)) else none
def countAlg : PartialAlg Count := { op := countOp, unit := none }
```

Meaning: Bornat et al.'s counting permissions (§10.2, `(Z, ⋆1)`) with an explicit unit, exactly
Dockins–Hobor–Appel Definition 9: `some n` (`n ≥ 0`) is a source with `n` split-off read tokens
(`some 0` is total), `some (-k)` (`k ≥ 1`) is a bundle of `k` tokens. Two sources never compose; a
source never absorbs more tokens than it issued. `tokens 0` is the empty permission, never the total
permission (`tokens_examples`).

Supporting lemmas (proved): `countOp_some_some_eq_some`, `countAlg_exclusive_iff : Exclusive countAlg a ↔ a = total`,
`tokens_of_pos`, `countAlg_opList_replicate_readToken`, `countAlg_opList_eq_unit`,
`countAlg_opList_tokens_length_le`.

Definition examples (proved): `countAlg_examples` (source 1 · readToken = total; readToken · readToken = tokens 2),
`countAlg_negative_examples` (total·total, total·readToken, source 1 · tokens 2, source 3 · source 4 all undefined),
`tokens_examples`.

Signatures of the declarations named in this subsection that are not printed elsewhere in this report (exact output of Lean's `PrettyPrinter.ppSignature`, with the namespaces opened as under **Results**):

```lean
Toy.Perm.Count.tokens_examples :
  tokens 0 = none ∧ tokens 2 = some (-2) ∧ tokens 0 ≠ total ∧ ∀ (k : Nat), tokens k ≠ total

Toy.Perm.countOp_some_some_eq_some {i j : Int} {c : Count} :
  countOp (some i) (some j) = some c ↔
    ((i < 0 ∨ j < 0) ∧ (0 ≤ i + j ∨ i < 0 ∧ j < 0)) ∧ c = some (i + j)

Toy.Perm.countAlg_exclusive_iff (a : Count) : countAlg.Exclusive a ↔ a = total

Toy.Perm.Count.tokens_of_pos {k : Nat} (hk : 0 < k) : tokens k = some (-↑k)

Toy.Perm.countAlg_opList_replicate_readToken (m : Nat) :
  countAlg.opList (List.replicate m readToken) = some (tokens m)

Toy.Perm.countAlg_opList_eq_unit (ts : List Count) (hts : ∀ (t : Count), t ∈ ts → t ≠ none)
  (h : countAlg.opList ts = some none) : ts = []

Toy.Perm.countAlg_opList_tokens_length_le (ts : List Count) (hts : ∀ (t : Count), t ∈ ts → t ≠ none)
  (w : Int) (h : countAlg.opList ts = some (some w)) (hw : w < 0) : ↑ts.length ≤ -w

Toy.Perm.countAlg_negative_examples :
  countAlg.op total total = none ∧
    countAlg.op total readToken = none ∧
      countAlg.op (source 1) (tokens 2) = none ∧ countAlg.op (source 3) (source 4) = none
```

#### D4. The sharing-depth design (`ToyPerm/Depth.lean`)

```lean
inductive Cell (V : Type) where
  | shared (depth : Nat) (value : V)     -- readable; exclusive iff depth = 0; depth = local outstanding shares
  | borrowed                            -- permission lent away; contributes none

def Cell.compat : Cell V → Cell V → Bool              -- two distinct views at one address
  | .borrowed, _ => true
  | _, .borrowed => true
  | .shared n x, .shared m y => decide (0 < n) && decide (0 < m) && decide (x = y)

inductive CellStep (V : Type) | write (v : V) | borrow | endBorrow (v : V) | share | endShare
def CellStep.apply : CellStep V → Cell V → Option (Cell V)
  | .write v, .shared 0 _ => some (.shared 0 v)
  | .borrow, .shared 0 _ => some .borrowed
  | .endBorrow v, .borrowed => some (.shared 0 v)
  | .share, .shared d v => some (.shared (d + 1) v)
  | .endShare, .shared (d + 1) v => some (.shared d v)
  | _, _ => none
def CellStep.RestoresExclusive (t) (c) : Prop :=
  (∃ v, t.apply c = some (.shared 0 v)) ∧ ∀ w, c ≠ .shared 0 w

def Cell.Valid (cfg : List (Cell V)) : Prop := cfg.Pairwise (fun a b => compat a b = true)
def Cell.stepAt (cfg) (i) (t) : Option (List (Cell V)) :=
  match cfg[i]? with
  | none => none
  | some c => match t.apply c with
    | none => none
    | some c' => if Valid (cfg.set i c') then some (cfg.set i c') else none
def Cell.CompatFPU (a b : Cell V) : Prop := ∀ f, compat a f = true → compat b f = true

def cellSumOp : Cell V → Cell V → Option (Cell V)      -- depth-sum composition
  | .borrowed, c => some c
  | c, .borrowed => some c
  | .shared (n + 1) x, .shared (m + 1) y => if x = y then some (.shared (n + m + 2) x) else none
  | _, _ => none
def cellSumAlg (V) : PartialAlg (Cell V) := { op := cellSumOp, unit := .borrowed }
def cellAgreeOp …  -- as cellSumOp, but two readers with equal payload compose to `shared 1 x`

inductive Wit | u | w | r | k                -- carrier of small witness algebras
def Wit.ofCell : Cell V → Wit                -- interpretation of cells in Wit
  | .borrowed => .u
  | .shared 0 _ => .w
  | .shared (_ + 1) _ => .r
inductive Wit5 | u | s0 | s1 | s2 | tok      -- five-element witness carrier
def Wit5.ofCell : Cell V → Wit5              -- payloads ignored; depths at least 2 identified
  | .borrowed => .u
  | .shared 0 _ => .s0
  | .shared 1 _ => .s1
  | .shared (_ + 2) _ => .s2
```

Meaning: a single-address restatement of the per-byte permission cells of the Aeneas memory-model
prototype (pull request 1497, head `d17ca83fc07d712d1785f650840cb2073c259e69`;
`backends/lean/Aeneas/Std/Heap/Repr.lean`: `Cell`, `Cell.write`, `Cell.borrow`, `Cell.endBorrow`,
`Cell.share`, `Cell.endShare`, `Cell.compatible`). The prototype's README says positive depths
"preserve read permission and record local outstanding shares; they are not fractions". A
configuration lists the cells of all active views at one address; an operation is enabled iff
it is defined on the cell and the resulting configuration is pairwise compatible (mirroring the
prototype's post-update `check`). `Cell.CompatFPU` is the same predicate as the prototype's
`Cell.PermWeakens` (`Heap/Lemmas.lean`). Not modelled: allocation, multi-byte ranges, provenance,
view creation and retirement (in particular the prototype retires an independent shared exposure at
depth 1 instead of decrementing it to depth 0), scoped return authority (`RootReturn`), and
permissions held implicitly outside the explicit heap.

Auxiliary algebras used only as witnesses: `singleHolderAlg` (composites defined only with a
`borrowed` side), `twoClassAlg` (borrowed+writers vs. readers; not unital), `allCompatAlg`,
`allZeroAlg`, `cellAgreeAlg`, and on the small carriers `Wit` (`u, w, r, k`) and `Wit5`
(`u, s0, s1, s2, tok`): `exclAgreeAlg` (`r·r = r`), `tokenReturnAlg` (`r·k = k·r = w`; a PCM),
`nonAssocDepthAlg` (`s1·tok = s0`, `s1·s1 = s2`, `s2·tok = s1`; commutative, unital, not
associative).

Definition examples (proved): `Cell.compat_examples` / `Cell.compat_negative_examples`,
`CellStep.apply_examples` / `CellStep.apply_negative_examples`,
`CellStep.restoresExclusive_examples` / `CellStep.restoresExclusive_negative_examples`,
`Cell.valid_examples`, `Cell.stepAt_examples`, `Cell.compatFPU_examples`, `cellSumAlg_examples`.

Signatures of the declarations named in this subsection that are not printed elsewhere in this report (exact output of Lean's `PrettyPrinter.ppSignature`, with the namespaces opened as under **Results**; for the witness algebras, which are definitions, the signature gives the carrier, and the operation is as described above and in `ToyPerm/Depth.lean`):

```lean
Toy.Perm.singleHolderAlg (V : Type) : PartialAlg (Cell V)

Toy.Perm.twoClassAlg : PartialAlg (Cell Nat)

Toy.Perm.allCompatAlg (V : Type) : PartialAlg (Cell V)

Toy.Perm.allZeroAlg : PartialAlg (Cell Nat)

Toy.Perm.cellAgreeAlg (V : Type) [DecidableEq V] : PartialAlg (Cell V)

Toy.Perm.exclAgreeAlg : PartialAlg Wit

Toy.Perm.tokenReturnAlg : PartialAlg Wit

Toy.Perm.nonAssocDepthAlg : PartialAlg Wit5

Toy.Perm.Cell.compat_negative_examples {V : Type} [DecidableEq V] (v w : V) (hvw : v ≠ w) :
  (shared 0 v).compat (shared 1 v) = false ∧
    (shared 0 v).compat (shared 0 v) = false ∧ (shared 1 v).compat (shared 1 w) = false

Toy.Perm.Cell.valid_examples :
  Valid [shared 1 7, shared 2 7, borrowed] ∧ ¬Valid [shared 0 7, shared 1 7]

Toy.Perm.Cell.stepAt_examples :
  stepAt [shared 1 7] 0 CellStep.endShare = some [shared 0 7] ∧
    stepAt [shared 1 7, shared 1 7] 0 CellStep.endShare = none

Toy.Perm.Cell.compatFPU_examples {V : Type} [DecidableEq V] (v : V) :
  (shared 0 v).CompatFPU (shared 1 v) ∧ ¬(shared 1 v).CompatFPU (shared 0 v)

Toy.Perm.cellSumAlg_examples :
  (cellSumAlg Nat).op (shared 1 7) (shared 2 7) = some (shared 3 7) ∧
    (cellSumAlg Nat).op (shared 0 7) borrowed = some (shared 0 7) ∧
      (cellSumAlg Nat).op (shared 0 7) (shared 1 7) = none ∧
        (cellSumAlg Nat).op (shared 1 7) (shared 1 8) = none
```

The statements of `Toy.Perm.Cell.compat_examples` and `Toy.Perm.CellStep.apply_negative_examples` are quoted from the source (in `namespace Toy.Perm.Cell` with `variable {V : Type} [DecidableEq V]`, and in `namespace Toy.Perm.CellStep` with `variable {V : Type}`, respectively), because their printed signatures leave the payload type of `borrowed` undetermined. The statements of `Toy.Perm.CellStep.apply_examples`, `Toy.Perm.CellStep.restoresExclusive_examples` and `Toy.Perm.CellStep.restoresExclusive_negative_examples` are also quoted from the source (in `namespace Toy.Perm.CellStep` with `variable {V : Type}`):

```lean
-- lean/ToyPerm/Depth.lean:75-77
theorem compat_examples (v : V) :
    compat (.shared 1 v) (.shared 2 v) = true ∧ compat (.shared 0 v) .borrowed = true ∧
      compat .borrowed (.borrowed : Cell V) = true

-- lean/ToyPerm/Depth.lean:126-129
theorem apply_negative_examples (v w : V) :
    (CellStep.write w).apply (.shared 1 v) = none ∧ (CellStep.borrow).apply (.shared 1 v) = none ∧
      (CellStep.endShare).apply (.shared 0 v) = none ∧
      (CellStep.share).apply (.borrowed : Cell V) = none

-- lean/ToyPerm/Depth.lean:117-121
theorem apply_examples (v w : V) :
    (CellStep.endShare).apply (.shared 1 v) = some (.shared 0 v) ∧
      (CellStep.share).apply (.shared 0 v) = some (.shared 1 v) ∧
      (CellStep.write w).apply (.shared 0 v) = some (.shared 0 w) ∧
      (CellStep.endBorrow w).apply (.borrowed : Cell V) = some (.shared 0 w)

-- lean/ToyPerm/Depth.lean:139-141
theorem restoresExclusive_examples (v w : V) :
    (CellStep.endShare).RestoresExclusive (.shared 1 v) ∧
      (CellStep.endBorrow w).RestoresExclusive (.borrowed : Cell V)

-- lean/ToyPerm/Depth.lean:146-148
theorem restoresExclusive_negative_examples (v w : V) :
    ¬ (CellStep.write w).RestoresExclusive (.shared 0 v) ∧
      ¬ (CellStep.endShare).RestoresExclusive (.shared 2 v)
```

#### D5. Bounded counting and maps between designs (`ToyPerm/Translate.lean`)

```lean
def inRange (N : Nat) : Count → Bool
  | none => true
  | some z => decide (-(N : Int) ≤ z) && decide (z ≤ (N : Int))
abbrev CountB (N : Nat) := { a : Count // inRange N a = true }
def countBOp (N) (a b : CountB N) : Option (CountB N) :=
  match countOp a.1 b.1 with
  | none => none
  | some c => if hc : inRange N c = true then some ⟨c, hc⟩ else none
def countBAlg (N) : PartialAlg (CountB N) := { op := countBOp N, unit := ⟨none, rfl⟩ }

def countEmbedVal (N : Nat) : Count → Rat                 -- step ε = 1/(3N+1)
  | none => 0
  | some z => if 0 ≤ z then 1 - (z : Rat) / (3 * N + 1) else (-(z : Rat)) / (3 * N + 1)
def countEmbed (N) (a : CountB N) : FracPerm := ofRat (countEmbedVal N a.1)
def countEmbedThirds (a : CountB 1) : FracPerm  -- step 1/3 instead of 1/4 (token ↦ 1/3, source 1 ↦ 2/3)
def countB1AllFull (a : CountB 1) : FracPerm := if a.1 = none then zero else full
def CountB.srcN (N) : CountB N := ⟨source N, _⟩          -- source with N outstanding tokens
def CountB.bundleN (N) : CountB N := ⟨some (-(N : Int)), _⟩  -- = tokens N for N ≥ 1; = total for N = 0
def CountB.totalN (N) : CountB N := ⟨total, _⟩
def CountB.tok1 : CountB 1 := ⟨readToken, rfl⟩          -- the instances used at N = 1
def CountB.src1 : CountB 1 := ⟨source 1, rfl⟩
def CountB.total1 : CountB 1 := ⟨total, rfl⟩
def countLinVal (e : Rat) : Count → Rat                   -- linear values with step e
  | none => 0
  | some z => if 0 ≤ z then 1 - (z : Rat) * e else (-(z : Rat)) * e
def countLin (N) (e : Rat) (a : CountB N) : FracPerm := ofRat (countLinVal e a.1)
def countToFracSourcesOnly : Count → FracPerm   -- none ↦ 0, some z ↦ (if 0 ≤ z then 1 else 0)

def exclToFrac (b : Bool) : FracPerm := if b then full else zero
def exclToCount (b : Bool) : Count := if b then total else none
def halfGridAlg : PartialAlg (Fin 3) :=          -- {0, 1/2, 1}, i stands for i/2
  { op := fun i j => if h : i.val + j.val ≤ 2 then some ⟨i.val + j.val, _⟩ else none, unit := 0 }
def halfGridToFrac (i : Fin 3) : FracPerm := ofRat ((i.val : Rat) / 2)
def halfGridToCount (i : Fin 3) : Count := tokens i.val
def asymGridAlg : PartialAlg (Fin 4)            -- {0, 1/4, 3/4, 1}: 0 unit, 1/4 · 3/4 = 1, else undefined
def asymGridToFrac (i : Fin 4) : FracPerm       -- 0, 1/4, 3/4, 1
def asymGridToCount : Fin 4 → Count             -- none, readToken, source 1, total
```

`CountB.bundleN_val : 1 ≤ N → (CountB.bundleN N).val = tokens N` (proved). `countLin N e` preserves the unit,
every defined composite and `total ↦ 1` whenever `1 ≤ N`, `0 ≤ e` and `N·e ≤ 1`, with `source N ↦ 1 − N·e` and
`tokens N ↦ N·e` (`countLin_preservesUnit_op_values`, proved).

Definition examples (proved): `countBAlg_examples` (in `CountB 1`, two single tokens do not pool),
`countEmbed_one_values` (token ↦ 1/4, source 1 ↦ 3/4, total ↦ 1), `exclToFrac_preserves_reflects`
(`exclAlg` is exactly the sub-algebra {0, 1} of fractions), `halfGridToFrac_preserves_reflects`
(`halfGridAlg` is exactly the sub-algebra {0, 1/2, 1}), `asymGridToFrac_preserves_reflects`
(`asymGridAlg` is exactly the sub-algebra {0, 1/4, 3/4, 1}).

Signatures of the declarations named in this subsection that are not printed elsewhere in this report (exact output of Lean's `PrettyPrinter.ppSignature`, with the namespaces opened as under **Results**):

```lean
Toy.Perm.countBAlg_examples :
  (countBAlg 1).op CountB.src1 CountB.tok1 = some CountB.total1 ∧
    (countBAlg 1).op CountB.tok1 CountB.tok1 = none ∧ inRange 1 (tokens 2) = false

Toy.Perm.countEmbed_one_values :
  (countEmbed 1 CountB.tok1).val = 1 / 4 ∧
    (countEmbed 1 CountB.src1).val = 3 / 4 ∧ countEmbed 1 CountB.total1 = full

Toy.Perm.exclToFrac_preserves_reflects :
  Function.Injective exclToFrac ∧
    ∀ (a b c : Bool),
      exclAlg.op a b = some c ↔ fracOp (exclToFrac a) (exclToFrac b) = some (exclToFrac c)

Toy.Perm.halfGridToFrac_preserves_reflects :
  Function.Injective halfGridToFrac ∧
    ∀ (i j k : Fin 3),
      halfGridAlg.op i j = some k ↔
        fracOp (halfGridToFrac i) (halfGridToFrac j) = some (halfGridToFrac k)

Toy.Perm.asymGridToFrac_preserves_reflects :
  Function.Injective asymGridToFrac ∧
    ∀ (i j k : Fin 4),
      asymGridAlg.op i j = some k ↔
        fracOp (asymGridToFrac i) (asymGridToFrac j) = some (asymGridToFrac k)
```

#### D6. Cross-design interpretation (`ToyPerm/Comparison.lean`)

```lean
def cellToCount : Cell V → Count
  | .shared d _ => source d
  | .borrowed => none
```


Basis: execution (Lean kernel check) for the named definition examples. Basis: derived (modeling bridge) for the correspondences with Dockins–Hobor–Appel Definitions 8 and 9 and with Bornat et al.'s counting model (by comparison of the definitions quoted in the prior-art records P1 and P2) and with the Aeneas prototype's cells (by inspection of the quoted source at the stated head commit of an unmerged pull request, which may change).

### Key statements with definitions unfolded


* **R4c** `¬ ∃ f : Count → FracPerm, PreservesOp countAlg fracAlg f ∧ f readToken ≠ zero` unfolds to:
  there is no `f` with `(∀ a b c, countOp a b = some c → fracOp (f a) (f b) = some (f c))` and
  `(f (some (-1))).val ≠ 0`.
* **R4d** (parametric form) unfolds to: if `A.op h h = some a` then there is no `g` with
  `(∀ x y z, A.op x y = some z → countOp (g x) (g y) = some (g z))` and `g a = some 0`.
* **R4e** unfolds to: if `∀ p q r, p.val + q.val ≤ 1 ∧ p.val + q.val = r.val → countOp (g p) (g q) = some (g r)`
  then `∀ q, g q = none`.
* **R4b** with `Compat` unfolded: no `f` that preserves composites and satisfies
  `∀ a b, (f a).val + (f b).val ≤ 1 → (countBOp N a b).isSome = true`. The disjunction unfolds to: for `N ≥ 1`
  and every composite-preserving `f`, `¬ (countBOp N srcN srcN).isSome = true`,
  `¬ (countBOp N bundleN bundleN).isSome = true` and
  `(f srcN).val + (f srcN).val ≤ 1 ∨ (f bundleN).val + (f bundleN).val ≤ 1`, where `srcN = ⟨source N, _⟩` and
  `bundleN = ⟨some (-N), _⟩`, whose value is `tokens N` for `N ≥ 1` (`CountB.bundleN_val`).
* **R3d** with `FramePreserving` unfolded: the conclusion is
  `¬ (∀ f, (A.op (e (shared 1 v)) f).isSome → (A.op (e (shared 0 v)) f).isSome) ∧ ¬ (∀ f, (A.op (e borrowed) f).isSome → (A.op (e (shared 0 v)) f).isSome)`.
* **R3e**: by `Assoc`, `(e₁ · e₁) · t` equals `e₁ · (e₁ · t)`; with `hret` this is `e₁ · e₀`, which `hexcl`
  says is undefined (`e₁ = e (shared 1 v)`, `e₀ = e (shared 0 v)`).
* **R5d** with `Exclusive` unfolded: no `p` such that `∃ b, b ≠ zero ∧ p.val + b.val ≤ 1` and some `N`
  bounds the length of every list of non-zero fractions whose amounts sum with `p.val` to exactly `1`.
* **R3f**: `Valid` is pairwise `compat`. `RestoresExclusive t c` is, by definition,
  `(∃ v, t.apply c = some (.shared 0 v)) ∧ ∀ w, c ≠ .shared 0 w`; the separate theorem
  `CellStep.restoresExclusive_iff` proves that this holds exactly when
  `(t = .endShare ∧ ∃ v, c = .shared 1 v) ∨ (∃ v, t = .endBorrow v ∧ c = .borrowed)`.


### Results

Lean statements are printed by Lean's `PrettyPrinter.ppSignature` with `open Toy.Perm Toy.Perm.PartialAlg Toy.Perm.FracPerm Toy.Perm.Count Toy.Perm.Cell`, except those introduced as quoted from the source, which are verbatim source text under a `-- file:lines` citation. Prior-art keys `P1`–`P20` refer to the full records under **Evidence → Primary sources**.

#### R1a-frac-count-pcm-laws

**Plain claim.** The fractional algebra on [0,1] intersected with the rationals (unit 0, composite = sum when it is at most 1) and the counting algebra on Option Int (unit none, Dockins-Hobor-Appel Definition 9) are each commutative, (strongly) associative, unital, cancellative and positive (a . b = unit implies a = unit) partial commutative monoids.

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* Dockins-Hobor-Appel present both models (Definitions 8 and 9) as separation algebras, whose axioms include cancellation, and state positivity for both; Iris proves frac cancelable, and iris-lean mechanizes the same facts for its Lean fractional camera. Restated here as a Lean statement over explicit carriers with a partial operation.

**Lean statement.**

```lean
Toy.Perm.fracAlg_isPCM_cancel_positive : fracAlg.IsPCM ∧ fracAlg.Cancel ∧ fracAlg.Positive

Toy.Perm.countAlg_isPCM_cancel_positive : countAlg.IsPCM ∧ countAlg.Cancel ∧ countAlg.Positive
```

**Hypothesis ledger.**

- None: the statement is closed (no hypotheses beyond universally quantified data).

**Depth.** `shallow`.

**Non-vacuity witness.** Closed statement (no hypotheses). Non-trivial composites exist: 1/2 . 1/2 = 1 in fractions; source 1 . readToken = total in counting. Lean: `Toy.Perm.fracAlg_half_half`, `Toy.Perm.countAlg_examples`.

**Supporting lemmas.** `Toy.Perm.PartialAlg.positive_iff_positiveDHA`, `Toy.Perm.PartialAlg.z2UnitAlg_positive_not_positiveDHA`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.fracAlg_half_half : fracAlg.op full.half full.half = some full

Toy.Perm.countAlg_examples :
  countAlg.op (source 1) readToken = some total ∧ countAlg.op readToken readToken = some (tokens 2)

Toy.Perm.PartialAlg.positive_iff_positiveDHA {α : Type} (A : PartialAlg α) (hcomm : A.Comm)
  (hunit : A.UnitLeft) (hcancel : A.Cancel) : A.Positive ↔ A.PositiveDHA

Toy.Perm.PartialAlg.z2UnitAlg_positive_not_positiveDHA :
  z2UnitAlg.IsPCM ∧ z2UnitAlg.Positive ∧ ¬z2UnitAlg.PositiveDHA ∧ ¬z2UnitAlg.Cancel
```

**Prior art.** [P1] Dockins, Hobor & Appel, APLAS 2009; [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P3] Boyland, SAS 2003; [P4] Iris 4.3.0, iris/algebra/frac.v and dfrac.v; [P5] Calcagno, O'Hearn & Yang, LICS 2007; [P6] iris-lean, Iris/Iris/Algebra/Frac.lean; [P7] VST, msl/sepalg.v and msl/tree_shares.v; [P8] fcsl-pcm, pcm/pcm.v; [P9] Klein, Kolanski & Boyton, Separation Algebra (AFP and ITP 2012); [P10] Appel et al., Program Logics for Certified Compilers, 2014; [P11] Further related work on share models (titles only); [P12] Heule, Leino, Müller & Summers, VMCAI 2013 (cited for a non-claim); [P13] Charguéraud & Pottier, ESOP 2017.

**Design question.** Which partial-commutative-monoid laws does each permission design satisfy, and which law-based reasoning (cancellation, positivity, disjointness) can a logic built on it rely on?

**Non-claims.** Listed under **Boundaries → Non-claims → R1a-frac-count-pcm-laws**.

Basis: execution (Lean kernel check): `Toy.Perm.fracAlg_isPCM_cancel_positive`, `Toy.Perm.countAlg_isPCM_cancel_positive` and every declaration named above.

#### R1b-disjointness-fails

**Plain claim.** Disjointness (a . a = b implies a = b) fails in the fractional algebra, in the counting algebra, and in the depth-sum algebra on cells over every inhabited payload type V; over the empty payload type the depth-sum algebra satisfies disjointness (proved separately, as the tightness counterexample Toy.Perm.cellSumAlg_empty_disjointness for the hypothesis Nonempty V).

**Kind / tier / depth.** counterexample / T0 / definitional. *Tier justification:* Dockins-Hobor-Appel state that both the fractional and the counting share models fail disjointness. The depth-sum algebra on cells fails it for the same reason (two equal non-empty readers compose).

**Lean statement.**

```lean
Toy.Perm.fracAlg_countAlg_cellSumAlg_violate_disjointness :
  ¬fracAlg.Disjointness ∧
    ¬countAlg.Disjointness ∧
      ∀ (V : Type) [inst : DecidableEq V], Nonempty V → ¬(cellSumAlg V).Disjointness
```

**Hypothesis ledger.**

- `[DecidableEq V] (third conjunct)`: Payload equality must be decidable to define the depth-sum algebra. Tightness: `harmless`.
- `Nonempty V (third conjunct)`: A reader cell needs a payload; over Empty the only cell is borrowed. Tightness: `tight`: counterexample `Toy.Perm.cellSumAlg_empty_disjointness`.

**Depth.** `definitional`.

**Non-vacuity witness.** The witnesses: 1/2 . 1/2 = 1 with 1/2 != 1; readToken . readToken = tokens 2 with readToken != tokens 2; for every payload v, shared 1 v . shared 1 v = shared 2 v. At the concrete inhabited payload type Nat (payload 7), Nonempty Nat holds, shared 1 7 . shared 1 7 = shared 2 7 with shared 1 7 != shared 2 7, and the depth-sum algebra over Nat violates disjointness. Lean: `Toy.Perm.disjointness_violation_witnesses`, `Toy.Perm.disjointness_violation_witness_nat`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.cellSumAlg_empty_disjointness : ¬Nonempty Empty ∧ (cellSumAlg Empty).Disjointness

Toy.Perm.disjointness_violation_witnesses :
  fracAlg.op full.half full.half = some full ∧
    full.half ≠ full ∧
      countAlg.op readToken readToken = some (tokens 2) ∧
        readToken ≠ tokens 2 ∧
          ∀ (V : Type) [inst : DecidableEq V] (v : V),
            (cellSumAlg V).op (shared 1 v) (shared 1 v) = some (shared 2 v) ∧
              shared 1 v ≠ shared 2 v

Toy.Perm.disjointness_violation_witness_nat :
  Nonempty Nat ∧
    (cellSumAlg Nat).op (shared 1 7) (shared 1 7) = some (shared 2 7) ∧
      shared 1 7 ≠ shared 2 7 ∧ ¬(cellSumAlg Nat).Disjointness
```

**Prior art.** [P1] Dockins, Hobor & Appel, APLAS 2009; [P7] VST, msl/sepalg.v and msl/tree_shares.v; [P11] Further related work on share models (titles only).

**Design question.** Which partial-commutative-monoid laws does each permission design satisfy, and which law-based reasoning (cancellation, positivity, disjointness) can a logic built on it rely on?

**Non-claims.** Listed under **Boundaries → Non-claims → R1b-disjointness-fails**.

Basis: execution (Lean kernel check): `Toy.Perm.fracAlg_countAlg_cellSumAlg_violate_disjointness` and every declaration named above.

#### R2a-frac-no-atoms

**Plain claim.** Every non-empty fractional permission q is the composite of two non-empty permissions, namely half q . half q = q with half q non-zero.

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* Dockins-Hobor-Appel Definition 8 gives the splitting function s1 = s2 = s/2; Iris is_op_frac and iris-lean Qp.half_add_half prove q = q/2 + q/2. This is the n = 2 case of R2b, kept separately as the two-way infinite-splittability property.

**Lean statement.**

```lean
Toy.Perm.fracAlg_nonzero_splits_into_two_nonzero_halves (q : FracPerm) (hq : q ≠ zero) :
  fracAlg.op q.half q.half = some q ∧ q.half ≠ zero
```

**Hypothesis ledger.**

- `hq : q ≠ zero`: Needed only for half q ≠ zero; the composite equation holds for every q. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_nonzero_splits_needs_hq`.

**Depth.** `shallow`.

**Non-vacuity witness.** q = 1 is non-empty. Lean: `Toy.Perm.fracAlg_nonzero_splits_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.fracAlg_nonzero_splits_needs_hq :
  ¬zero ≠ zero ∧ ¬(fracAlg.op zero.half zero.half = some zero ∧ zero.half ≠ zero)

Toy.Perm.fracAlg_nonzero_splits_nonvacuous : full ≠ zero
```

**Prior art.** [P1] Dockins, Hobor & Appel, APLAS 2009; [P4] Iris 4.3.0, iris/algebra/frac.v and dfrac.v; [P6] iris-lean, Iris/Iris/Algebra/Frac.lean.

**Design question.** Can a reader sub-delegate read access without involving the original owner (fractions), or must every split go through a counting authority (counting)?

**Non-claims.** Listed under **Boundaries → Non-claims → R2a-frac-no-atoms**.

Basis: execution (Lean kernel check): `Toy.Perm.fracAlg_nonzero_splits_into_two_nonzero_halves` and every declaration named above.

Basis: derived (modeling bridge): If holding a fractional permission entitles a holder to replace it by any two permissions composing to it, then any holder of a non-empty fraction can hand on a non-empty read permission without involving any other party; this reading is not part of the Lean statement.

#### R2b-frac-halving-split

**Plain claim.** For every fractional permission q and every n >= 1, the halving split halvingSplit q n (which is [q] for n = 1 and [q/2, q/4, ..., q/2^(n-1), q/2^(n-1)] for n >= 2) has exactly n pieces and composes in list order to exactly q, and if q is non-empty every piece is non-empty (first theorem); for q = 1 the pieces recombine to the full permission, which is exclusive (second theorem).

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* Unbounded splitting and recombination of fractions is standard (Bornat et al. Sections 3 and 9; Dockins-Hobor-Appel infinite splittability) and n-way splitting is already mechanized (iris-lean Qp.divide_even; Iris big-operator splitting). Restated here with an explicit dyadic witness.

**Lean statement.**

```lean
Toy.Perm.fracAlg_halvingSplit_composes (q : FracPerm) (n : Nat) (hn : 0 < n) :
  (halvingSplit q n).length = n ∧
    fracAlg.opList (halvingSplit q n) = some q ∧
      (q ≠ zero → ∀ (x : FracPerm), x ∈ halvingSplit q n → x ≠ zero)

Toy.Perm.fracAlg_halvingSplit_full_recombines_to_exclusive (n : Nat) (hn : 0 < n) :
  fracAlg.opList (halvingSplit full n) = some full ∧ fracAlg.Exclusive full
```

**Hypothesis ledger.**

- `hn : 0 < n`: A split into zero pieces is empty and composes to 0. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_halvingSplit_zero_pieces`. Applies to: `fracAlg_halvingSplit_composes`, `fracAlg_halvingSplit_full_recombines_to_exclusive`.
- `q ≠ zero (inner premise of the third conjunct)`: Pieces of a split of 0 are 0. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_halvingSplit_of_zero_has_empty_piece`. Applies to: `fracAlg_halvingSplit_composes`.

**Depth.** `shallow`.

**Non-vacuity witness.** q = 1, n = 3: pieces [1/2, 1/4, 1/4], all non-empty. Lean: `Toy.Perm.fracAlg_halvingSplit_composes_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.fracAlg_halvingSplit_zero_pieces :
  ¬0 < 0 ∧
    ¬((halvingSplit full 0).length = 0 ∧
          fracAlg.opList (halvingSplit full 0) = some full ∧
            (full ≠ zero → ∀ (x : FracPerm), x ∈ halvingSplit full 0 → x ≠ zero)) ∧
      ¬(fracAlg.opList (halvingSplit full 0) = some full ∧ fracAlg.Exclusive full)

Toy.Perm.fracAlg_halvingSplit_of_zero_has_empty_piece :
  0 < 2 ∧
    ¬((halvingSplit zero 2).length = 2 ∧
        fracAlg.opList (halvingSplit zero 2) = some zero ∧
          ∀ (x : FracPerm), x ∈ halvingSplit zero 2 → x ≠ zero)

Toy.Perm.fracAlg_halvingSplit_composes_nonvacuous :
  0 < 3 ∧ full ≠ zero ∧ List.map val (halvingSplit full 3) = [1 / 2, 1 / 4, 1 / 4]
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009; [P4] Iris 4.3.0, iris/algebra/frac.v and dfrac.v; [P6] iris-lean, Iris/Iris/Algebra/Frac.lean.

**Design question.** Can a reader sub-delegate read access without involving the original owner (fractions), or must every split go through a counting authority (counting)?

**Non-claims.** Listed under **Boundaries → Non-claims → R2b-frac-halving-split**.

Basis: execution (Lean kernel check): `Toy.Perm.fracAlg_halvingSplit_composes`, `Toy.Perm.fracAlg_halvingSplit_full_recombines_to_exclusive` and every declaration named above.

#### R2c-count-token-atomic

**Plain claim.** In the counting algebra a single read token is atomic: whenever a . b equals one read token, a or b is the empty permission.

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* Bornat et al. Section 6: 'the split-off read permissions can't be split further'.

**Lean statement.**

```lean
Toy.Perm.countAlg_readToken_atomic (a b : Count) (h : countAlg.op a b = some readToken) :
  a = none ∨ b = none
```

**Hypothesis ledger.**

- `h : countAlg.op a b = some readToken`: The premise being analysed; atomicity is specific to single tokens (a 2-bundle splits). Tightness: `tight`: counterexample `Toy.Perm.countAlg_readToken_atomic_needs_h`.

**Depth.** `shallow`.

**Non-vacuity witness.** none . readToken = readToken. Lean: `Toy.Perm.countAlg_readToken_atomic_nonvacuous`.

**Supporting lemmas.** `Toy.Perm.countAlg_two_tokens_split`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.countAlg_readToken_atomic_needs_h :
  countAlg.op readToken readToken = some (tokens 2) ∧
    countAlg.op readToken readToken ≠ some readToken ∧ ¬(readToken = none ∨ readToken = none)

Toy.Perm.countAlg_readToken_atomic_nonvacuous : countAlg.op none readToken = some readToken

Toy.Perm.countAlg_two_tokens_split : countAlg.op readToken readToken = some (tokens 2)
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a reader sub-delegate read access without involving the original owner (fractions), or must every split go through a counting authority (counting)?

**Non-claims.** Listed under **Boundaries → Non-claims → R2c-count-token-atomic**.

Basis: execution (Lean kernel check): `Toy.Perm.countAlg_readToken_atomic` and every declaration named above.

Basis: derived (modeling bridge): If sharing read access means splitting one's permission into two non-empty permissions, a party holding exactly one read token cannot share read access onward without a source; this reading is not part of the Lean statement.

#### R2d-count-split-through-source

**Plain claim.** If a source permission with count n is the composite of two non-empty parts, then one part is a source with count n + k and the other is a bundle of exactly k >= 1 tokens.

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* A direct case inversion of the counting composition of Bornat et al. Section 10.2 and Dockins-Hobor-Appel Definition 9 (Bornat et al. equation (16) gives source n = source (n+m) . m tokens).

**Lean statement.**

```lean
Toy.Perm.countAlg_split_of_source (n : Nat) (a b : Count) (h : countAlg.op a b = some (source n))
  (ha : a ≠ none) (hb : b ≠ none) :
  (∃ k, 0 < k ∧ a = source (n + k) ∧ b = tokens k) ∨ ∃ k, 0 < k ∧ b = source (n + k) ∧ a = tokens k
```

**Hypothesis ledger.**

- `h : countAlg.op a b = some (source n)`: The premise being analysed: the composite is a source. Tightness: `tight`: counterexample `Toy.Perm.countAlg_split_of_source_needs_h`.
- `ha : a ≠ none`: Excludes the trivial split unit . source n. Tightness: `tight`: counterexample `Toy.Perm.countAlg_split_of_source_needs_ha`.
- `hb : b ≠ none`: Excludes the trivial split source n . unit. Tightness: `tight`: counterexample `Toy.Perm.countAlg_split_of_source_needs_hb`.

**Depth.** `shallow`.

**Non-vacuity witness.** source 1 . readToken = source 0. Lean: `Toy.Perm.countAlg_split_of_source_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.countAlg_split_of_source_needs_h :
  readToken ≠ none ∧
    readToken ≠ none ∧
      countAlg.op readToken readToken ≠ some (source 0) ∧
        ¬((∃ k, 0 < k ∧ readToken = source (0 + k) ∧ readToken = tokens k) ∨
            ∃ k, 0 < k ∧ readToken = source (0 + k) ∧ readToken = tokens k)

Toy.Perm.countAlg_split_of_source_needs_ha :
  countAlg.op none (source 0) = some (source 0) ∧
    source 0 ≠ none ∧
      ¬((∃ k, 0 < k ∧ none = source (0 + k) ∧ source 0 = tokens k) ∨
          ∃ k, 0 < k ∧ source 0 = source (0 + k) ∧ none = tokens k)

Toy.Perm.countAlg_split_of_source_needs_hb :
  countAlg.op (source 0) none = some (source 0) ∧
    source 0 ≠ none ∧
      ¬((∃ k, 0 < k ∧ source 0 = source (0 + k) ∧ none = tokens k) ∨
          ∃ k, 0 < k ∧ none = source (0 + k) ∧ source 0 = tokens k)

Toy.Perm.countAlg_split_of_source_nonvacuous :
  countAlg.op (source 1) readToken = some (source 0) ∧ source 1 ≠ none ∧ readToken ≠ none
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a reader sub-delegate read access without involving the original owner (fractions), or must every split go through a counting authority (counting)?

**Non-claims.** Listed under **Boundaries → Non-claims → R2d-count-split-through-source**.

Basis: execution (Lean kernel check): `Toy.Perm.countAlg_split_of_source` and every declaration named above.

#### R3b-depth-fpu-characterization

**Plain claim.** With respect to the sharing-depth compatibility relation, a cell update a to b is frame-preserving (every cell compatible with a is compatible with b) iff b is borrowed, or a is a writer (depth 0), or a and b are both readers (positive depth) with the same payload.

**Kind / tier / depth.** characterization / T1 / shallow. *Tier justification:* The predicate is the prototype's own Cell.PermWeakens, whose sufficient cases (writer to writer, any cell to borrowed, share, end-share above depth 1) are proved there; the converse and the resulting characterization are made precise here.

**Lean statement.**

```lean
Toy.Perm.Cell.compatFPU_iff {V : Type} [DecidableEq V] (a b : Cell V) :
  a.CompatFPU b ↔
    b = borrowed ∨ (∃ v, a = shared 0 v) ∨ ∃ n m v, a = shared (n + 1) v ∧ b = shared (m + 1) v
```

**Hypothesis ledger.**

- `[DecidableEq V]`: Payload equality must be decidable to compute compatibility. Tightness: `harmless`.

**Depth.** `shallow`.

**Non-vacuity witness.** At V = Nat: each disjunct is inhabited (share from depth 0; end-share from depth 2 to 1; any update to borrowed) and the last end-share satisfies none of them. Lean: `Toy.Perm.Cell.compatFPU_iff_nonvacuous`.

**Supporting lemmas.** `Toy.Perm.Cell.compat_positive_depth_irrelevant`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.Cell.compatFPU_iff_nonvacuous :
  (∃ w, shared 0 7 = shared 0 w) ∧
    (∃ n m w, shared 2 7 = shared (n + 1) w ∧ shared 1 7 = shared (m + 1) w) ∧
      ¬(shared 0 7 = borrowed ∨
          (∃ w, shared 1 7 = shared 0 w) ∨
            ∃ n m w, shared 1 7 = shared (n + 1) w ∧ shared 0 7 = shared (m + 1) w)

Toy.Perm.Cell.compat_positive_depth_irrelevant {V : Type} [DecidableEq V] (n m : Nat) (v : V)
  (f : Cell V) : (shared (n + 1) v).compat f = (shared (m + 1) v).compat f
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility; [P15] Aeneas heap prototype (unmerged pull request 1497): Cell.PermWeakens; [P16] Iris 4.3.0, iris/algebra/updates.v; Jung et al., JFP 2018.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3b-depth-fpu-characterization**.

Basis: execution (Lean kernel check): `Toy.Perm.Cell.compatFPU_iff` and every declaration named above.

#### R3c-depth-sum-pcm-exists

**Plain claim.** The depth-sum algebra on cells (borrowed is the unit; two readers with equal payload compose to a reader whose depth is the sum; everything else undefined) is a commutative, associative, unital, cancellative and positive partial commutative monoid whose definedness relation is exactly the sharing-depth compatibility relation.

**Kind / tier / depth.** theorem / T1 / shallow. *Tier justification:* Constructing a PCM whose definedness is a given compatibility relation is routine; recorded because it shows the impossibilities R3d and R3e are not about the mere existence of a PCM.

**Lean statement.**

```lean
Toy.Perm.cellSumAlg_isPCM_cancel_positive_compat_iff (V : Type) [DecidableEq V] :
  (cellSumAlg V).IsPCM ∧
    (cellSumAlg V).Cancel ∧
      (cellSumAlg V).Positive ∧ ∀ (a b : Cell V), (cellSumAlg V).Compat a b ↔ a.compat b = true
```

**Hypothesis ledger.**

- `[DecidableEq V]`: Payload equality must be decidable. Tightness: `harmless`.

**Depth.** `shallow`.

**Non-vacuity witness.** shared 1 7 . shared 2 7 is defined; shared 0 7 . shared 1 7 is not, matching compatibility. Lean: `Toy.Perm.cellSumAlg_compat_examples`.

**Supporting lemmas.** `Toy.Perm.cellAgreeAlg_comm_unit_compat_iff_not_cancel`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.cellSumAlg_compat_examples :
  (cellSumAlg Nat).Compat (shared 1 7) (shared 2 7) ∧
    (shared 1 7).compat (shared 2 7) = true ∧
      ¬(cellSumAlg Nat).Compat (shared 0 7) (shared 1 7) ∧ (shared 0 7).compat (shared 1 7) = false

Toy.Perm.cellAgreeAlg_comm_unit_compat_iff_not_cancel :
  (∀ (V : Type) [inst : DecidableEq V],
      (cellAgreeAlg V).Comm ∧
        (cellAgreeAlg V).UnitLeft ∧
          ∀ (a b : Cell V), (cellAgreeAlg V).Compat a b ↔ a.compat b = true) ∧
    ¬(cellAgreeAlg Nat).Cancel
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3c-depth-sum-pcm-exists**.

Basis: execution (Lean kernel check): `Toy.Perm.cellSumAlg_isPCM_cancel_positive_compat_iff` and every declaration named above.

#### R3d-restoring-steps-not-frame-preserving

**Plain claim.** For any partial algebra A on any carrier and any interpretation e of cells in it: if two depth-1 readers with payload v are compatible, a depth-0 writer with payload v is incompatible with a depth-1 reader with payload v, and borrowed is compatible with a depth-1 reader (all after interpretation by e), then neither the last end-share e(shared 1 v) to e(shared 0 v) nor the end-borrow e(borrowed) to e(shared 0 v) is a frame-preserving update (single right frames).

**Kind / tier / depth.** impossibility / T1 / definitional. *Tier justification:* That a frame-preserving update cannot depend on the frame is folklore of PCM-based logics; applied here to the specific exclusivity-restoring steps of the sharing-depth design.

**Lean statement.**

```lean
Toy.Perm.restoring_steps_not_framePreserving_of_sharing_exclusion_neutral {M V : Type}
  (A : PartialAlg M) (e : Cell V → M) (v : V)
  (h_readers : A.Compat (e (shared 1 v)) (e (shared 1 v)))
  (h_excl : ¬A.Compat (e (shared 0 v)) (e (shared 1 v)))
  (h_neutral : A.Compat (e borrowed) (e (shared 1 v))) :
  ¬A.FramePreserving (e (shared 1 v)) (e (shared 0 v)) ∧
    ¬A.FramePreserving (e borrowed) (e (shared 0 v))
```

**Hypothesis ledger.**

- `h_readers : A.Compat (e (shared 1 v)) (e (shared 1 v))`: Used for the end-share conjunct: another view's depth-1 reader is a frame compatible with e(shared 1 v). Tightness: `tight`: counterexample `Toy.Perm.singleHolderAlg_last_endShare_framePreserving`.
- `h_excl : ¬ A.Compat (e (shared 0 v)) (e (shared 1 v))`: A writer excludes readers; used for both conjuncts. Tightness: `tight`: counterexample `Toy.Perm.allCompatAlg_restoring_steps_framePreserving`.
- `h_neutral : A.Compat (e borrowed) (e (shared 1 v))`: Used for the end-borrow conjunct: a borrowed view coexists with a reader. Automatic when A satisfies UnitLeft and e(borrowed) is the unit (h_neutral_of_unitLeft); its tightness witness twoClassAlg is not unital. Tightness: `tight`: counterexample `Toy.Perm.twoClassAlg_endBorrow_framePreserving`.

**Depth.** `definitional`.

**Non-vacuity witness.** The depth-sum algebra with e = id and v = 7 satisfies all three hypotheses. Lean: `Toy.Perm.restoring_steps_not_framePreserving_nonvacuous`.

**Positive control.** `Toy.Perm.singleHolderAlg_last_endShare_framePreserving` (a nearby setting in which the conclusion fails; its statement is printed below).

**Supporting lemmas.** `Toy.Perm.h_neutral_of_unitLeft`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.singleHolderAlg_last_endShare_framePreserving :
  ¬(singleHolderAlg Nat).Compat (id (shared 1 7)) (id (shared 1 7)) ∧
    ¬(singleHolderAlg Nat).Compat (id (shared 0 7)) (id (shared 1 7)) ∧
      (singleHolderAlg Nat).Compat (id borrowed) (id (shared 1 7)) ∧
        (singleHolderAlg Nat).FramePreserving (id (shared 1 7)) (id (shared 0 7)) ∧
          ¬(singleHolderAlg Nat).FramePreserving (id borrowed) (id (shared 0 7))

Toy.Perm.allCompatAlg_restoring_steps_framePreserving :
  (allCompatAlg Nat).Compat (id (shared 1 7)) (id (shared 1 7)) ∧
    (allCompatAlg Nat).Compat (id borrowed) (id (shared 1 7)) ∧
      (allCompatAlg Nat).Compat (id (shared 0 7)) (id (shared 1 7)) ∧
        (allCompatAlg Nat).FramePreserving (id (shared 1 7)) (id (shared 0 7)) ∧
          (allCompatAlg Nat).FramePreserving (id borrowed) (id (shared 0 7))

Toy.Perm.twoClassAlg_endBorrow_framePreserving :
  twoClassAlg.Compat (id (shared 1 7)) (id (shared 1 7)) ∧
    ¬twoClassAlg.Compat (id (shared 0 7)) (id (shared 1 7)) ∧
      ¬twoClassAlg.Compat (id borrowed) (id (shared 1 7)) ∧
        twoClassAlg.FramePreserving (id borrowed) (id (shared 0 7)) ∧ ¬twoClassAlg.UnitLeft

Toy.Perm.restoring_steps_not_framePreserving_nonvacuous :
  (cellSumAlg Nat).Compat (id (shared 1 7)) (id (shared 1 7)) ∧
    ¬(cellSumAlg Nat).Compat (id (shared 0 7)) (id (shared 1 7)) ∧
      (cellSumAlg Nat).Compat (id borrowed) (id (shared 1 7))

Toy.Perm.h_neutral_of_unitLeft {M V : Type} (A : PartialAlg M) (e : Cell V → M) (hunit : A.UnitLeft)
  (hb : e borrowed = A.unit) (x : M) : A.Compat (e borrowed) x
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility; [P17] Aeneas heap prototype (unmerged pull request 1497): raw restoration vs. scoped return authority; [P16] Iris 4.3.0, iris/algebra/updates.v; Jung et al., JFP 2018; [P18] Iris 4.3.0, iris/algebra/auth.v.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3d-restoring-steps-not-frame-preserving**.

Basis: execution (Lean kernel check): `Toy.Perm.restoring_steps_not_framePreserving_of_sharing_exclusion_neutral` and every declaration named above.

#### R3e-no-local-token-return-beside-other-reader

**Plain claim.** In an associative partial algebra (strong associativity; commutativity and the unit law not assumed), there is no interpretation e of cells and token t such that the state 'two depth-1 views with payload v and the outstanding share t' is consistent when written with the two views composed first ((e(shared 1 v) . e(shared 1 v)) . t is defined), absorbing t turns a depth-1 view into the depth-0 cell (e(shared 1 v) . t = e(shared 0 v)), and a depth-1 reader cannot be composed with the depth-0 cell (e(shared 1 v) . e(shared 0 v) undefined).

**Kind / tier / depth.** impossibility / T1 / definitional. *Tier justification:* Elementary; it makes precise the prototype's own remark that conflicting readers may exist in other views, and contrasts it with counting permissions, where the source counts every reader.

**Lean statement.**

```lean
Toy.Perm.no_assoc_alg_returns_last_share_by_composition_beside_another_reader {M V : Type}
  (A : PartialAlg M) (hassoc : A.Assoc) (e : Cell V → M) (t : M) (v : V)
  (hstate : ((A.op (e (shared 1 v)) (e (shared 1 v))).bind fun x => A.op x t) ≠ none)
  (hret : A.op (e (shared 1 v)) t = some (e (shared 0 v)))
  (hexcl : ¬A.Compat (e (shared 1 v)) (e (shared 0 v))) : False
```

**Hypothesis ledger.**

- `hassoc : A.Assoc`: Moves the token next to one view: (r . r) . t = r . (r . t). Tightness: `tight`: counterexample `Toy.Perm.nonAssocDepthAlg_returns_last_share_beside_reader`.
- `hstate : ((A.op (e (shared 1 v)) (e (shared 1 v))).bind fun x => A.op x t) ≠ none`: Faithfulness to the design: two views may both be at depth 1 while one of them has an outstanding share. Tightness: `tight`: counterexample `Toy.Perm.tokenReturnAlg_returns_last_share_without_second_reader`.
- `hret : A.op (e (shared 1 v)) t = some (e (shared 0 v))`: The last-reader-returns-ownership step as a composition. Tightness: `tight`: counterexample `Toy.Perm.exclAgreeAlg_unit_token_does_not_restore`.
- `hexcl : ¬ A.Compat (e (shared 1 v)) (e (shared 0 v))`: Depth 0 is exclusive (a reader cannot sit beside it). Tightness: `tight`: counterexample `Toy.Perm.allZeroAlg_return_beside_reader`.

**Depth.** `definitional`.

**Non-vacuity witness.** The conclusion is False; non-vacuity means the hypotheses are separately satisfiable: each tightness witness satisfies all hypotheses but one, and no_assoc_alg_returns_last_share_hypotheses_satisfiable exhibits (i) with (iii) and (ii) with (iii). Lean: `Toy.Perm.no_assoc_alg_returns_last_share_hypotheses_satisfiable`, `Toy.Perm.nonAssocDepthAlg_returns_last_share_beside_reader`, `Toy.Perm.tokenReturnAlg_returns_last_share_without_second_reader`, `Toy.Perm.exclAgreeAlg_unit_token_does_not_restore`, `Toy.Perm.allZeroAlg_return_beside_reader`.

**Positive control.** `Toy.Perm.tokenReturnAlg_returns_last_share_without_second_reader` (a nearby setting in which the conclusion fails; its statement is printed below).

**Supporting lemmas.** `Toy.Perm.no_pcm_returns_last_share_by_composition_beside_another_reader`, `Toy.Perm.counting_returns_last_share_without_coexisting_reader`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.nonAssocDepthAlg_returns_last_share_beside_reader :
  ((nonAssocDepthAlg.op (Wit5.ofCell (shared 1 7)) (Wit5.ofCell (shared 1 7))).bind fun x =>
        nonAssocDepthAlg.op x Wit5.tok) ≠
      none ∧
    nonAssocDepthAlg.op (Wit5.ofCell (shared 1 7)) Wit5.tok = some (Wit5.ofCell (shared 0 7)) ∧
      ¬nonAssocDepthAlg.Compat (Wit5.ofCell (shared 1 7)) (Wit5.ofCell (shared 0 7)) ∧
        ¬nonAssocDepthAlg.Assoc ∧ nonAssocDepthAlg.Comm ∧ nonAssocDepthAlg.UnitLeft

Toy.Perm.tokenReturnAlg_returns_last_share_without_second_reader :
  tokenReturnAlg.Assoc ∧
    tokenReturnAlg.Comm ∧
      tokenReturnAlg.UnitLeft ∧
        ((tokenReturnAlg.op (Wit.ofCell (shared 1 7)) (Wit.ofCell (shared 1 7))).bind fun x =>
              tokenReturnAlg.op x Wit.k) =
            none ∧
          tokenReturnAlg.op (Wit.ofCell (shared 1 7)) Wit.k = some (Wit.ofCell (shared 0 7)) ∧
            ¬tokenReturnAlg.Compat (Wit.ofCell (shared 1 7)) (Wit.ofCell (shared 0 7))

Toy.Perm.exclAgreeAlg_unit_token_does_not_restore :
  exclAgreeAlg.Assoc ∧
    ((exclAgreeAlg.op (Wit.ofCell (shared 1 7)) (Wit.ofCell (shared 1 7))).bind fun x =>
          exclAgreeAlg.op x Wit.u) ≠
        none ∧
      exclAgreeAlg.op (Wit.ofCell (shared 1 7)) Wit.u ≠ some (Wit.ofCell (shared 0 7)) ∧
        ¬exclAgreeAlg.Compat (Wit.ofCell (shared 1 7)) (Wit.ofCell (shared 0 7))

Toy.Perm.allZeroAlg_return_beside_reader :
  allZeroAlg.Assoc ∧
    ((allZeroAlg.op (id (shared 1 7)) (id (shared 1 7))).bind fun x => allZeroAlg.op x borrowed) ≠
        none ∧
      allZeroAlg.op (id (shared 1 7)) borrowed = some (id (shared 0 7)) ∧
        allZeroAlg.Compat (id (shared 1 7)) (id (shared 0 7))

Toy.Perm.no_assoc_alg_returns_last_share_hypotheses_satisfiable :
  ((cellSumOp (shared 1 7) (shared 1 7)).bind fun x => cellSumOp x borrowed) ≠ none ∧
    cellSumOp (shared 1 7) (shared 0 7) = none ∧
      tokenReturnAlg.op (Wit.ofCell (shared 1 7)) Wit.k = some (Wit.ofCell (shared 0 7))

Toy.Perm.no_pcm_returns_last_share_by_composition_beside_another_reader {M V : Type}
  (A : PartialAlg M) (hpcm : A.IsPCM) (e : Cell V → M) (t : M) (v : V)
  (hstate : A.opList [t, e (shared 1 v), e (shared 1 v)] ≠ none)
  (hret : A.op (e (shared 1 v)) t = some (e (shared 0 v)))
  (hexcl : ¬A.Compat (e (shared 0 v)) (e (shared 1 v))) : False

Toy.Perm.counting_returns_last_share_without_coexisting_reader :
  countAlg.op (cellToCount (shared 1 7)) readToken = some (cellToCount (shared 0 7)) ∧
    ¬countAlg.Compat (cellToCount (shared 1 7)) (cellToCount (shared 0 7)) ∧
      ((countAlg.op (cellToCount (shared 1 7)) (cellToCount (shared 1 7))).bind fun x =>
          countAlg.op x readToken) =
        none
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility; [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P18] Iris 4.3.0, iris/algebra/auth.v.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3e-no-local-token-return-beside-other-reader**.

Basis: execution (Lean kernel check): `Toy.Perm.no_assoc_alg_returns_last_share_by_composition_beside_another_reader` and every declaration named above.

#### R3f-depth-transition-characterization

**Plain claim.** In a valid configuration (pairwise-compatible cells of the views at one address), applying a per-view operation t to view i whose cell is c, where t is defined on c with result c', yields a valid configuration iff, in case t restores exclusivity on c, every other view at that address is borrowed; the steps that restore exclusivity are exactly the last end-share (endShare on shared 1 v) and the end-borrow (endBorrow on borrowed), so write, borrow, share and end-share from depth at least 2, when defined on view i's cell, always yield a valid configuration; equivalently, stepAt cfg i t is enabled iff view i exists, t is defined on its cell, and the borrowed condition holds for restoring steps.

**Kind / tier / depth.** characterization / T1 / shallow. *Tier justification:* Restates the enabledness behaviour of the prototype's per-cell operations at one address as a single equivalence, with the restoring steps classified.

**Lean statement.**

```lean
Toy.Perm.Cell.valid_set_iff {V : Type} [DecidableEq V] (cfg : List (Cell V)) (hv : Valid cfg)
  (i : Nat) (c c' : Cell V) (t : CellStep V) (hi : cfg[i]? = some c) (ht : t.apply c = some c') :
  Valid (cfg.set i c') ↔
    t.RestoresExclusive c → ∀ (j : Nat) (d : Cell V), j ≠ i → cfg[j]? = some d → d = borrowed
```

The statement of `Toy.Perm.CellStep.restoresExclusive_iff` is quoted from the source (in `namespace Toy.Perm.CellStep` with `variable {V : Type}`):

```lean
-- lean/ToyPerm/Depth.lean:155-157
theorem restoresExclusive_iff (t : CellStep V) (c : Cell V) :
    t.RestoresExclusive c ↔
      (t = .endShare ∧ ∃ v, c = .shared 1 v) ∨ (∃ v, t = .endBorrow v ∧ c = .borrowed)
```

```lean
Toy.Perm.Cell.stepAt_isSome_iff {V : Type} [DecidableEq V] (cfg : List (Cell V)) (hv : Valid cfg)
  (i : Nat) (t : CellStep V) :
  (stepAt cfg i t).isSome = true ↔
    ∃ c c',
      cfg[i]? = some c ∧
        t.apply c = some c' ∧
          (t.RestoresExclusive c →
            ∀ (j : Nat) (d : Cell V), j ≠ i → cfg[j]? = some d → d = borrowed)
```

**Hypothesis ledger.**

- `[DecidableEq V]`: Payload equality must be decidable to compute compatibility (Valid, stepAt); CellStep.restoresExclusive_iff does not use it. Tightness: `harmless`. Applies to: `Cell.valid_set_iff`, `Cell.stepAt_isSome_iff`.
- `hv : Valid cfg`: Enabledness of non-restoring steps relies on the invariant already holding. Tightness: `tight`: counterexample `Toy.Perm.Cell.valid_set_iff_needs_valid`, `Toy.Perm.Cell.stepAt_isSome_iff_needs_valid`. Applies to: `Cell.valid_set_iff`, `Cell.stepAt_isSome_iff`.
- `hi : cfg[i]? = some c`: c must be the cell actually at position i. Tightness: `tight`: counterexample `Toy.Perm.Cell.valid_set_iff_needs_lookup`. Applies to: `Cell.valid_set_iff`.
- `ht : t.apply c = some c'`: c' must be the result of the operation. Tightness: `tight`: counterexample `Toy.Perm.Cell.valid_set_iff_needs_apply`. Applies to: `Cell.valid_set_iff`.

**Depth.** `shallow`.

**Non-vacuity witness.** [shared 1 7, borrowed]: ending view 0's last share restores exclusivity and is enabled. Lean: `Toy.Perm.Cell.valid_set_iff_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.Cell.valid_set_iff_needs_valid :
  ¬Valid [shared 0 7, shared 0 7] ∧
    [shared 0 7, shared 0 7][0]? = some (shared 0 7) ∧
      CellStep.share.apply (shared 0 7) = some (shared 1 7) ∧
        ¬(Valid ([shared 0 7, shared 0 7].set 0 (shared 1 7)) ↔
            CellStep.share.RestoresExclusive (shared 0 7) →
              ∀ (j : Nat) (d : Cell Nat),
                j ≠ 0 → [shared 0 7, shared 0 7][j]? = some d → d = borrowed)

Toy.Perm.Cell.stepAt_isSome_iff_needs_valid :
  ¬Valid [shared 0 7, shared 0 7] ∧
    ¬((stepAt [shared 0 7, shared 0 7] 0 CellStep.share).isSome = true ↔
        ∃ c c',
          [shared 0 7, shared 0 7][0]? = some c ∧
            CellStep.share.apply c = some c' ∧
              (CellStep.share.RestoresExclusive c →
                ∀ (j : Nat) (d : Cell Nat),
                  j ≠ 0 → [shared 0 7, shared 0 7][j]? = some d → d = borrowed))

Toy.Perm.Cell.valid_set_iff_needs_lookup :
  Valid [shared 1 7, shared 1 7] ∧
    [shared 1 7, shared 1 7][5]? ≠ some borrowed ∧
      (CellStep.endBorrow 8).apply borrowed = some (shared 0 8) ∧
        ¬(Valid ([shared 1 7, shared 1 7].set 5 (shared 0 8)) ↔
            (CellStep.endBorrow 8).RestoresExclusive borrowed →
              ∀ (j : Nat) (d : Cell Nat),
                j ≠ 5 → [shared 1 7, shared 1 7][j]? = some d → d = borrowed)

Toy.Perm.Cell.valid_set_iff_needs_apply :
  Valid [shared 1 7, shared 1 7] ∧
    [shared 1 7, shared 1 7][0]? = some (shared 1 7) ∧
      CellStep.share.apply (shared 1 7) ≠ some (shared 0 7) ∧
        ¬(Valid ([shared 1 7, shared 1 7].set 0 (shared 0 7)) ↔
            CellStep.share.RestoresExclusive (shared 1 7) →
              ∀ (j : Nat) (d : Cell Nat),
                j ≠ 0 → [shared 1 7, shared 1 7][j]? = some d → d = borrowed)

Toy.Perm.Cell.valid_set_iff_nonvacuous :
  Valid [shared 1 7, borrowed] ∧
    [shared 1 7, borrowed][0]? = some (shared 1 7) ∧
      CellStep.endShare.apply (shared 1 7) = some (shared 0 7) ∧
        CellStep.endShare.RestoresExclusive (shared 1 7) ∧
          Valid ([shared 1 7, borrowed].set 0 (shared 0 7))
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility; [P17] Aeneas heap prototype (unmerged pull request 1497): raw restoration vs. scoped return authority.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3f-depth-transition-characterization**.

Basis: execution (Lean kernel check): `Toy.Perm.Cell.valid_set_iff`, `Toy.Perm.CellStep.restoresExclusive_iff`, `Toy.Perm.Cell.stepAt_isSome_iff` and every declaration named above.

#### R3g-depth-sum-not-faithful

**Plain claim.** For every payload v, the configurations [shared 2 v] and [shared 1 v, shared 1 v] have the same depth-sum composite shared 2 v, yet from the first the single view regains exclusivity by two enabled end-shares, while in the second neither view's end-share is enabled (immediate enabledness of one step).

**Kind / tier / depth.** counterexample / T1 / definitional. *Tier justification:* Concrete computation in the toy model; it makes precise the prototype's remark that pooling just total depths would lose the per-view distinction.

**Lean statement.**

```lean
Toy.Perm.cellSumAlg_composite_does_not_determine_endShare_enabled {V : Type} [DecidableEq V]
  (v : V) :
  (cellSumAlg V).opList [shared 2 v] = some (shared 2 v) ∧
    (cellSumAlg V).opList [shared 1 v, shared 1 v] = some (shared 2 v) ∧
      ((stepAt [shared 2 v] 0 CellStep.endShare).bind fun cfg => stepAt cfg 0 CellStep.endShare) =
          some [shared 0 v] ∧
        stepAt [shared 1 v, shared 1 v] 0 CellStep.endShare = none ∧
          stepAt [shared 1 v, shared 1 v] 1 CellStep.endShare = none
```

**Hypothesis ledger.**

- `[DecidableEq V]`: Payload equality must be decidable. Tightness: `harmless`.

**Depth.** `definitional`.

**Non-vacuity witness.** Universally quantified over the payload; instantiated at the inhabited payload type Nat with payload 7 (cellSumAlg_composite_does_not_determine_endShare_enabled_nat). Over an empty payload type the statement is vacuous. Lean: `Toy.Perm.cellSumAlg_composite_does_not_determine_endShare_enabled_nat`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.cellSumAlg_composite_does_not_determine_endShare_enabled_nat :
  (cellSumAlg Nat).opList [shared 2 7] = some (shared 2 7) ∧
    (cellSumAlg Nat).opList [shared 1 7, shared 1 7] = some (shared 2 7) ∧
      ((stepAt [shared 2 7] 0 CellStep.endShare).bind fun cfg => stepAt cfg 0 CellStep.endShare) =
          some [shared 0 7] ∧
        stepAt [shared 1 7, shared 1 7] 0 CellStep.endShare = none ∧
          stepAt [shared 1 7, shared 1 7] 1 CellStep.endShare = none
```

**Prior art.** [P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility; [P19] Aeneas heap prototype (unmerged pull request 1497): view-specific authorization.

**Design question.** Can the per-byte sharing-depth design be given a separation-algebra (PCM) semantics in which ending the last share is a local step, or must it remain a transition system with a global compatibility check?

**Non-claims.** Listed under **Boundaries → Non-claims → R3g-depth-sum-not-faithful**.

Basis: execution (Lean kernel check): `Toy.Perm.cellSumAlg_composite_does_not_determine_endShare_enabled` and every declaration named above.

#### R4a-bounded-count-embeds-in-frac

**Plain claim.** For every bound N, counting permissions with counts at most N form a partial commutative monoid, and the explicit map countEmbed N (bundle of k tokens to k/(3N+1), source with n outstanding tokens to 1 - n/(3N+1), empty to 0) is injective, sends the unit to 0, satisfies a . b = c iff f a . f b = f c for all a, b, c (it preserves every defined composite and reflects every fractional composite that lands in its image), maps exactly the exclusive elements to exclusive fractions, and maps exactly the non-empty permissions to non-zero fractions.

**Kind / tier / depth.** theorem / T1 / shallow. *Tier justification:* The idea of giving each token a small fixed fraction is folklore; the exact step 1/(3N+1), which makes the map injective and makes it reflect both composition and exclusivity, is made precise here.

**Lean statement.**

```lean
Toy.Perm.countBEmbed_injective_preserves_reflects_op_exclusive_readable (N : Nat) :
  (countBAlg N).IsPCM ∧
    Function.Injective (countEmbed N) ∧
      (countBAlg N).PreservesUnit fracAlg (countEmbed N) ∧
        (∀ (a b c : CountB N),
            (countBAlg N).op a b = some c ↔
              fracAlg.op (countEmbed N a) (countEmbed N b) = some (countEmbed N c)) ∧
          (∀ (a : CountB N), (countBAlg N).Exclusive a ↔ fracAlg.Exclusive (countEmbed N a)) ∧
            ∀ (a : CountB N), a ≠ (countBAlg N).unit ↔ countEmbed N a ≠ fracAlg.unit
```

**Hypothesis ledger.**

- None: the statement is closed (no hypotheses beyond universally quantified data).

**Depth.** `shallow`.

**Non-vacuity witness.** Closed statement. N = 1, fully checked: the map is injective, preserves the unit, satisfies the composition equivalence, gives the token 1/4 and the total permission the exclusive fraction 1. Lean: `Toy.Perm.countB1Embed_injective_unit_op_iff`.

**Supporting lemmas.** `Toy.Perm.countEmbedThirds_preservesOp_not_reflecting`, `Toy.Perm.preservesOp_of_op_iff`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.countB1Embed_injective_unit_op_iff :
  Function.Injective (countEmbed 1) ∧
    (countBAlg 1).PreservesUnit fracAlg (countEmbed 1) ∧
      (∀ (a b c : CountB 1),
          (countBAlg 1).op a b = some c ↔
            fracAlg.op (countEmbed 1 a) (countEmbed 1 b) = some (countEmbed 1 c)) ∧
        countEmbed 1 CountB.tok1 ≠ zero ∧ fracAlg.Exclusive (countEmbed 1 CountB.total1)

Toy.Perm.countEmbedThirds_preservesOp_not_reflecting :
  (countBAlg 1).PreservesOp fracAlg countEmbedThirds ∧
    (countBAlg 1).op CountB.tok1 CountB.tok1 = none ∧
      fracAlg.op (countEmbedThirds CountB.tok1) (countEmbedThirds CountB.tok1) =
        some (countEmbedThirds CountB.src1)

Toy.Perm.preservesOp_of_op_iff {α β : Type} (A : PartialAlg α) (B : PartialAlg β) (f : α → β)
  (h : ∀ (a b c : α), A.op a b = some c ↔ B.op (f a) (f b) = some (f c)) : A.PreservesOp B f
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a logic built on one permission design be faithfully re-expressed in the other by a structure-preserving map, and what is lost in each direction?

**Non-claims.** Listed under **Boundaries → Non-claims → R4a-bounded-count-embeds-in-frac**.

Basis: execution (Lean kernel check): `Toy.Perm.countBEmbed_injective_preserves_reflects_op_exclusive_readable` and every declaration named above.

#### R4b-bounded-embedding-not-reflecting

**Plain claim.** For every bound N >= 1, there is no map f from N-bounded counting permissions to fractional permissions that preserves every defined composite and reflects compatibility (any two permissions whose images are compatible fractions are compatible in N-bounded counting). More precisely, for every N >= 1 and every map f that preserves every defined composite: two sources source N are incompatible and two bundles tokens N are incompatible in N-bounded counting, yet source N . tokens N = total forces f(source N) + f(tokens N) <= 1, so at least one of the two pairs (two copies of source N, or two copies of tokens N) has compatible fractional images. Which pair it is depends on f: for every N >= 1 there is a composition-preserving map that also sends the unit to 0 and total to 1 under which two bundles tokens N have incompatible images (tokens N to 2/3, source N to 1/3), and another under which two sources source N have incompatible images (tokens N to 1/3, source N to 2/3).

**Kind / tier / depth.** impossibility / T1 / shallow. *Tier justification:* Elementary; it makes precise one way in which fractions cannot enforce a bound on the number of tokens even when the bound is fixed, and which incompatible pairs are affected.

**Lean statement.**

```lean
Toy.Perm.no_opPreserving_map_countB_to_frac_reflecting_compat (N : Nat) (hN : 1 ≤ N) :
  ¬∃ f,
      (countBAlg N).PreservesOp fracAlg f ∧
        ∀ (a b : CountB N), fracAlg.Compat (f a) (f b) → (countBAlg N).Compat a b

Toy.Perm.opPreserving_map_countB_to_frac_sources_or_bundles_compat (N : Nat) (hN : 1 ≤ N)
  (f : CountB N → FracPerm) (hf : (countBAlg N).PreservesOp fracAlg f) :
  ¬(countBAlg N).Compat (CountB.srcN N) (CountB.srcN N) ∧
    ¬(countBAlg N).Compat (CountB.bundleN N) (CountB.bundleN N) ∧
      (f (CountB.srcN N)).val + (f (CountB.bundleN N)).val ≤ 1 ∧
        (fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∨
          fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N)))

Toy.Perm.opPreserving_maps_countB_to_frac_keep_either_pair_incompatible (N : Nat) (hN : 1 ≤ N) :
  (∃ f,
      (countBAlg N).PreservesUnit fracAlg f ∧
        (countBAlg N).PreservesOp fracAlg f ∧
          f (CountB.totalN N) = full ∧
            (f (CountB.bundleN N)).val = 2 / 3 ∧
              (f (CountB.srcN N)).val = 1 / 3 ∧
                fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∧
                  ¬fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N))) ∧
    ∃ f,
      (countBAlg N).PreservesUnit fracAlg f ∧
        (countBAlg N).PreservesOp fracAlg f ∧
          f (CountB.totalN N) = full ∧
            (f (CountB.bundleN N)).val = 1 / 3 ∧
              (f (CountB.srcN N)).val = 2 / 3 ∧
                ¬fracAlg.Compat (f (CountB.srcN N)) (f (CountB.srcN N)) ∧
                  fracAlg.Compat (f (CountB.bundleN N)) (f (CountB.bundleN N))
```

**Hypothesis ledger.**

- `hN : 1 ≤ N`: With N = 0 bounded counting is the two-point exclusive algebra {none, total}, which embeds faithfully; there source 0 and some (-0) are the same element total. Tightness: `tight`: counterexample `Toy.Perm.countB0Embed_preservesOp_reflects_compat`, `Toy.Perm.countB0Embed_sources_or_bundles_compat_fails`, `Toy.Perm.countB0_keep_either_pair_incompatible_fails`. Applies to: `no_opPreserving_map_countB_to_frac_reflecting_compat`, `opPreserving_map_countB_to_frac_sources_or_bundles_compat`, `opPreserving_maps_countB_to_frac_keep_either_pair_incompatible`.
- `PreservesOp (countBAlg N) fracAlg f (conjunct of the excluded map; hypothesis hf of the disjunction)`: Structure preservation; it is what links f(source N) and f(tokens N) through source N . tokens N = total. Tightness: `tight`: counterexample `Toy.Perm.countB1AllFull_reflects_compat`, `Toy.Perm.countB1AllFull_sources_or_bundles_compat_fails`. Applies to: `no_opPreserving_map_countB_to_frac_reflecting_compat`, `opPreserving_map_countB_to_frac_sources_or_bundles_compat`.
- `∀ a b, fracAlg.Compat (f a) (f b) → (countBAlg N).Compat a b (conjunct of the excluded map)`: Compatibility reflection. Tightness: `tight`: counterexample `Toy.Perm.countB1Embed_preservesOp`. Applies to: `no_opPreserving_map_countB_to_frac_reflecting_compat`.

**Depth.** `shallow`.

**Non-vacuity witness.** hN holds for N = 1, and each conjunct of the excluded map alone is satisfiable at N = 1 (the map sending every non-empty permission to 1 reflects compatibility; countEmbed 1 preserves composition), so the hypotheses of the disjunction hold for N = 1 and f = countEmbed 1; under countEmbed 1 the two single tokens are incompatible but have compatible images. At N = 1 the linear maps with steps 2/3 and 1/3 preserve composition and give the token and the source the values 2/3, 1/3 and 1/3, 2/3. Lean: `Toy.Perm.countB1AllFull_reflects_compat`, `Toy.Perm.countB1Embed_preservesOp`, `Toy.Perm.countB1Embed_compat_not_reflected`, `Toy.Perm.countB1Lin_values`.

**Positive control.** `Toy.Perm.countB0Embed_preservesOp_reflects_compat` (a nearby setting in which the conclusion fails; its statement is printed below).

**Supporting lemmas.** `Toy.Perm.CountB.bundleN_val`, `Toy.Perm.countBAlg_srcN_bundleN`, `Toy.Perm.countBAlg_not_compat_srcN_srcN`, `Toy.Perm.countBAlg_not_compat_bundleN_bundleN`, `Toy.Perm.countLin_preservesUnit_op_values`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above (printed with `set_option pp.funBinderTypes true`, so that the types of bound variables are shown):

```lean
Toy.Perm.countB0Embed_preservesOp_reflects_compat :
  ¬1 ≤ 0 ∧
    (countBAlg 0).PreservesOp fracAlg (countEmbed 0) ∧
      ∀ (a b : CountB 0),
        fracAlg.Compat (countEmbed 0 a) (countEmbed 0 b) → (countBAlg 0).Compat a b

Toy.Perm.countB0Embed_sources_or_bundles_compat_fails :
  ¬1 ≤ 0 ∧
    (countBAlg 0).PreservesOp fracAlg (countEmbed 0) ∧
      ¬(¬(countBAlg 0).Compat (CountB.srcN 0) (CountB.srcN 0) ∧
          ¬(countBAlg 0).Compat (CountB.bundleN 0) (CountB.bundleN 0) ∧
            (countEmbed 0 (CountB.srcN 0)).val + (countEmbed 0 (CountB.bundleN 0)).val ≤ 1 ∧
              (fracAlg.Compat (countEmbed 0 (CountB.srcN 0)) (countEmbed 0 (CountB.srcN 0)) ∨
                fracAlg.Compat (countEmbed 0 (CountB.bundleN 0)) (countEmbed 0 (CountB.bundleN 0))))

Toy.Perm.countB0_keep_either_pair_incompatible_fails :
  ¬1 ≤ 0 ∧
    ¬((∃ (f : CountB 0 → FracPerm),
          (countBAlg 0).PreservesUnit fracAlg f ∧
            (countBAlg 0).PreservesOp fracAlg f ∧
              f (CountB.totalN 0) = full ∧
                (f (CountB.bundleN 0)).val = 2 / 3 ∧
                  (f (CountB.srcN 0)).val = 1 / 3 ∧
                    fracAlg.Compat (f (CountB.srcN 0)) (f (CountB.srcN 0)) ∧
                      ¬fracAlg.Compat (f (CountB.bundleN 0)) (f (CountB.bundleN 0))) ∧
        ∃ (f : CountB 0 → FracPerm),
          (countBAlg 0).PreservesUnit fracAlg f ∧
            (countBAlg 0).PreservesOp fracAlg f ∧
              f (CountB.totalN 0) = full ∧
                (f (CountB.bundleN 0)).val = 1 / 3 ∧
                  (f (CountB.srcN 0)).val = 2 / 3 ∧
                    ¬fracAlg.Compat (f (CountB.srcN 0)) (f (CountB.srcN 0)) ∧
                      fracAlg.Compat (f (CountB.bundleN 0)) (f (CountB.bundleN 0)))

Toy.Perm.countB1AllFull_reflects_compat :
  1 ≤ 1 ∧
    ∃ (f : CountB 1 → FracPerm),
      ∀ (a b : CountB 1), fracAlg.Compat (f a) (f b) → (countBAlg 1).Compat a b

Toy.Perm.countB1AllFull_sources_or_bundles_compat_fails :
  1 ≤ 1 ∧
    ¬(¬(countBAlg 1).Compat (CountB.srcN 1) (CountB.srcN 1) ∧
        ¬(countBAlg 1).Compat (CountB.bundleN 1) (CountB.bundleN 1) ∧
          (countB1AllFull (CountB.srcN 1)).val + (countB1AllFull (CountB.bundleN 1)).val ≤ 1 ∧
            (fracAlg.Compat (countB1AllFull (CountB.srcN 1)) (countB1AllFull (CountB.srcN 1)) ∨
              fracAlg.Compat (countB1AllFull (CountB.bundleN 1))
                (countB1AllFull (CountB.bundleN 1))))

Toy.Perm.countB1Embed_preservesOp :
  1 ≤ 1 ∧ ∃ (f : CountB 1 → FracPerm), (countBAlg 1).PreservesOp fracAlg f

Toy.Perm.countB1Embed_compat_not_reflected :
  ¬(countBAlg 1).Compat CountB.tok1 CountB.tok1 ∧
    fracAlg.Compat (countEmbed 1 CountB.tok1) (countEmbed 1 CountB.tok1)

Toy.Perm.countB1Lin_values :
  (countLin 1 (2 / 3) CountB.tok1).val = 2 / 3 ∧
    (countLin 1 (2 / 3) CountB.src1).val = 1 / 3 ∧
      (countLin 1 (1 / 3) CountB.tok1).val = 1 / 3 ∧
        (countLin 1 (1 / 3) CountB.src1).val = 2 / 3 ∧
          (countBAlg 1).PreservesOp fracAlg (countLin 1 (2 / 3)) ∧
            (countBAlg 1).PreservesOp fracAlg (countLin 1 (1 / 3))

Toy.Perm.CountB.bundleN_val (N : Nat) (hN : 1 ≤ N) : (CountB.bundleN N).val = tokens N

Toy.Perm.countBAlg_srcN_bundleN (N : Nat) (hN : 1 ≤ N) :
  (countBAlg N).op (CountB.srcN N) (CountB.bundleN N) = some (CountB.totalN N)

Toy.Perm.countBAlg_not_compat_srcN_srcN (N : Nat) :
  ¬(countBAlg N).Compat (CountB.srcN N) (CountB.srcN N)

Toy.Perm.countBAlg_not_compat_bundleN_bundleN (N : Nat) :
  ¬(countBAlg N).Compat (CountB.bundleN N) (CountB.bundleN N)

Toy.Perm.countLin_preservesUnit_op_values (N : Nat) (hN : 1 ≤ N) (e : Rat) (he : 0 ≤ e)
  (hNe : ↑N * e ≤ 1) :
  (countBAlg N).PreservesUnit fracAlg (countLin N e) ∧
    (countBAlg N).PreservesOp fracAlg (countLin N e) ∧
      countLin N e (CountB.totalN N) = full ∧
        (countLin N e (CountB.srcN N)).val = 1 - ↑N * e ∧
          (countLin N e (CountB.bundleN N)).val = ↑N * e
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a logic built on one permission design be faithfully re-expressed in the other by a structure-preserving map, and what is lost in each direction?

**Non-claims.** Listed under **Boundaries → Non-claims → R4b-bounded-embedding-not-reflecting**.

Basis: execution (Lean kernel check): `Toy.Perm.no_opPreserving_map_countB_to_frac_reflecting_compat`, `Toy.Perm.opPreserving_map_countB_to_frac_sources_or_bundles_compat`, `Toy.Perm.opPreserving_maps_countB_to_frac_keep_either_pair_incompatible` and every declaration named above.

#### R4c-no-count-to-frac-with-readable-token

**Plain claim.** There is no map from (unbounded) counting permissions to fractional permissions that preserves every defined composite and sends the single read token to a non-zero fraction, because bundles of n tokens exist for every n while fractions are bounded by 1.

**Kind / tier / depth.** impossibility / T1 / shallow. *Tier justification:* Makes precise Bornat et al.'s informal contrast between unbounded counting and bounded divisible fractions (Section 9).

**Lean statement.**

```lean
Toy.Perm.no_opPreserving_map_count_to_frac_with_nonzero_readToken :
  ¬∃ f, countAlg.PreservesOp fracAlg f ∧ f readToken ≠ zero
```

**Hypothesis ledger.**

- `PreservesOp countAlg fracAlg f`: Structure preservation: a . b = c implies f a . f b = f c. Tightness: `tight`: counterexample `Toy.Perm.const_full_nonzero_token`.
- `f readToken ≠ zero`: Readability of a single token is preserved. Tightness: `tight`: counterexample `Toy.Perm.const_zero_preservesOp`, `Toy.Perm.countToFracSourcesOnly_preserves_unit_op_total`.

**Depth.** `shallow`.

**Non-vacuity witness.** Each hypothesis alone is satisfiable (constant maps). Lean: `Toy.Perm.const_zero_preservesOp`, `Toy.Perm.const_full_nonzero_token`.

**Positive control.** `Toy.Perm.countB1Embed_preservesOp_nonzero_token` (a nearby setting in which the conclusion fails; its statement is printed below).

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above (printed with `set_option pp.funBinderTypes true`, so that the type of the bound map `f` is shown):

```lean
Toy.Perm.const_full_nonzero_token : ∃ (f : Count → FracPerm), f readToken ≠ zero

Toy.Perm.const_zero_preservesOp : ∃ (f : Count → FracPerm), countAlg.PreservesOp fracAlg f

Toy.Perm.countToFracSourcesOnly_preserves_unit_op_total :
  countAlg.PreservesUnit fracAlg countToFracSourcesOnly ∧
    countAlg.PreservesOp fracAlg countToFracSourcesOnly ∧
      countToFracSourcesOnly total = full ∧ countToFracSourcesOnly readToken = zero

Toy.Perm.countB1Embed_preservesOp_nonzero_token :
  (countBAlg 1).PreservesOp fracAlg (countEmbed 1) ∧ countEmbed 1 CountB.tok1 ≠ zero
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009; [P20] Heule, Leino, Müller & Summers, VMCAI 2013.

**Design question.** Can a logic built on one permission design be faithfully re-expressed in the other by a structure-preserving map, and what is lost in each direction?

**Non-claims.** Listed under **Boundaries → Non-claims → R4c-no-count-to-frac-with-readable-token**.

Basis: execution (Lean kernel check): `Toy.Perm.no_opPreserving_map_count_to_frac_with_nonzero_readToken` and every declaration named above.

#### R4d-no-frac-to-count-preserving-exclusivity

**Plain claim.** In any partial algebra A, if h . h = a then no map from A to counting permissions that preserves every defined composite sends a to the total counting permission, because the total counting permission is never a composite x . x; in particular no such map from the fractions, or from the finitely divisible half-grid {0, 1/2, 1}, sends 1 = 1/2 . 1/2 to the total permission.

**Kind / tier / depth.** impossibility / T1 / shallow. *Tier justification:* Elementary; makes precise one half of Bornat et al.'s 'two distinct and somewhat incompatible properties'.

**Lean statement.**

```lean
Toy.Perm.no_opPreserving_map_to_count_sending_self_composite_to_total {α : Type} (A : PartialAlg α)
  (h a : α) (hh : A.op h h = some a) : ¬∃ g, A.PreservesOp countAlg g ∧ g a = total

Toy.Perm.no_opPreserving_map_frac_to_count_sending_full_to_total :
  ¬∃ g, fracAlg.PreservesOp countAlg g ∧ g full = total

Toy.Perm.no_opPreserving_map_halfGrid_to_count_sending_full_to_total :
  ¬∃ g, halfGridAlg.PreservesOp countAlg g ∧ g 2 = total
```

**Hypothesis ledger.**

- `hh : A.op h h = some a`: a is a self-composite (for fractions: 1 = 1/2 . 1/2). Tightness: `tight`: counterexample `Toy.Perm.exclToCount_preservesOp_full_to_total`. Applies to: `no_opPreserving_map_to_count_sending_self_composite_to_total`.
- `PreservesOp A countAlg g`: Structure preservation (a conjunct of the excluded map in all three theorems). The counterexample is stated over the fractions (A = fracAlg, h = 1/2, a = 1), so it shows tightness for the first theorem and the second only. No Lean counterexample is recorded for the third (half-grid) theorem; there, dropping this conjunct leaves only g 2 = total, which a constant map satisfies (evident, not stated in Lean). Tightness: `tight`: counterexample `Toy.Perm.indicator_full_to_total`. Applies to: `no_opPreserving_map_to_count_sending_self_composite_to_total`, `no_opPreserving_map_frac_to_count_sending_full_to_total`.
- `g a = total`: Exclusivity preserved: a = 1 in the second theorem, and a = 2 (standing for 1) in the third (by fracAlg_exclusive_iff and countAlg_exclusive_iff, 1 and total are the exclusive elements of the fractions and of counting). const_none_preservesOp_frac_half (over the fractions, where 1/2 . 1/2 = 1, some map preserves composition) shows tightness for the first theorem and the second; halfGridToCount_preservesOp_nonempty (a composition-preserving map on the half-grid, sending 2 to tokens 2 rather than total) shows it for the third. Tightness: `tight`: counterexample `Toy.Perm.const_none_preservesOp_frac_half`, `Toy.Perm.halfGridToCount_preservesOp_nonempty`. Applies to: `no_opPreserving_map_to_count_sending_self_composite_to_total`, `no_opPreserving_map_frac_to_count_sending_full_to_total`, `no_opPreserving_map_halfGrid_to_count_sending_full_to_total`.

**Depth.** `shallow`.

**Non-vacuity witness.** hh holds in the fractions (1/2 . 1/2 = 1) and in the half-grid (1/2 . 1/2 = 1). Lean: `Toy.Perm.fracAlg_half_half`, `Toy.Perm.halfGridAlg_half_half`.

**Positive control.** `Toy.Perm.asymGridToCount_preservesOp_full_to_total`, `Toy.Perm.exclToCount_preservesOp_full_to_total` (a nearby setting in which the conclusion fails; its statement is printed below).

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above (printed with `set_option pp.funBinderTypes true`, so that the types of bound variables are shown):

```lean
Toy.Perm.exclToCount_preservesOp_full_to_total :
  exclAlg.op true true ≠ some true ∧
    exclAlg.PreservesOp countAlg exclToCount ∧ exclToCount true = total

Toy.Perm.indicator_full_to_total :
  fracAlg.op full.half full.half = some full ∧ ∃ (g : FracPerm → Count), g full = total

Toy.Perm.const_none_preservesOp_frac_half :
  fracAlg.op full.half full.half = some full ∧
    ∃ (g : FracPerm → Count), fracAlg.PreservesOp countAlg g

Toy.Perm.halfGridToCount_preservesOp_nonempty :
  halfGridAlg.PreservesOp countAlg halfGridToCount ∧ ∀ (i : Fin 3), i ≠ 0 → halfGridToCount i ≠ none

Toy.Perm.fracAlg_half_half : fracAlg.op full.half full.half = some full

Toy.Perm.halfGridAlg_half_half : halfGridAlg.op 1 1 = some 2

Toy.Perm.asymGridToCount_preservesOp_full_to_total :
  asymGridAlg.op 1 2 = some 3 ∧
    (∀ (x : Fin 4), asymGridAlg.op x x ≠ some 3) ∧
      asymGridAlg.PreservesOp countAlg asymGridToCount ∧ asymGridToCount 3 = total
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a logic built on one permission design be faithfully re-expressed in the other by a structure-preserving map, and what is lost in each direction?

**Non-claims.** Listed under **Boundaries → Non-claims → R4d-no-frac-to-count-preserving-exclusivity**.

Basis: execution (Lean kernel check): `Toy.Perm.no_opPreserving_map_to_count_sending_self_composite_to_total`, `Toy.Perm.no_opPreserving_map_frac_to_count_sending_full_to_total`, `Toy.Perm.no_opPreserving_map_halfGrid_to_count_sending_full_to_total` and every declaration named above.

#### R4e-no-frac-to-count-preserving-nonemptiness

**Plain claim.** Every map from fractional to counting permissions that preserves every defined composite sends every fraction to the empty counting permission; in particular no such map sends even a single fraction (for instance 1) to a non-empty counting permission, because repeated halving would require token bundles whose size halves forever.

**Kind / tier / depth.** characterization / T1 / shallow. *Tier justification:* Makes precise the clash between infinite divisibility (Dockins-Hobor-Appel) and atomic read tokens (Bornat et al.).

**Lean statement.**

```lean
Toy.Perm.opPreserving_map_frac_to_count_eq_none (g : FracPerm → Count)
  (hg : fracAlg.PreservesOp countAlg g) (q : FracPerm) : g q = none

Toy.Perm.no_opPreserving_map_frac_to_count_with_nonempty_value :
  ¬∃ g, fracAlg.PreservesOp countAlg g ∧ ∃ q, g q ≠ none
```

**Hypothesis ledger.**

- `hg : PreservesOp fracAlg countAlg g`: Structure preservation. Tightness: `tight`: counterexample `Toy.Perm.const_readToken_not_none`. Applies to: `opPreserving_map_frac_to_count_eq_none`.
- `PreservesOp fracAlg countAlg g (conjunct of the excluded map)`: Structure preservation. Tightness: `tight`: counterexample `Toy.Perm.const_readToken_nonempty`. Applies to: `no_opPreserving_map_frac_to_count_with_nonempty_value`.
- `∃ q, g q ≠ none (conjunct of the excluded map)`: Some fraction is sent to a non-empty counting permission. Tightness: `tight`: counterexample `Toy.Perm.opPreserving_map_frac_to_count_exists`. Applies to: `no_opPreserving_map_frac_to_count_with_nonempty_value`.

**Depth.** `shallow`.

**Non-vacuity witness.** The constant map to none preserves every defined composite. Lean: `Toy.Perm.const_none_preservesOp_frac`.

**Positive control.** `Toy.Perm.halfGridToCount_preservesOp_nonempty` (a nearby setting in which the conclusion fails; its statement is printed below).

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above (printed with `set_option pp.funBinderTypes true`, so that the types of bound variables are shown):

```lean
Toy.Perm.const_readToken_not_none : ¬∀ (q : FracPerm), (fun (x : FracPerm) => readToken) q = none

Toy.Perm.const_readToken_nonempty : ∃ (g : FracPerm → Count), ∃ (q : FracPerm), g q ≠ none

Toy.Perm.opPreserving_map_frac_to_count_exists :
  ∃ (g : FracPerm → Count), fracAlg.PreservesOp countAlg g

Toy.Perm.const_none_preservesOp_frac : fracAlg.PreservesOp countAlg fun (x : FracPerm) => none

Toy.Perm.halfGridToCount_preservesOp_nonempty :
  halfGridAlg.PreservesOp countAlg halfGridToCount ∧ ∀ (i : Fin 3), i ≠ 0 → halfGridToCount i ≠ none
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can a logic built on one permission design be faithfully re-expressed in the other by a structure-preserving map, and what is lost in each direction?

**Non-claims.** Listed under **Boundaries → Non-claims → R4e-no-frac-to-count-preserving-nonemptiness**.

Basis: execution (Lean kernel check): `Toy.Perm.opPreserving_map_frac_to_count_eq_none`, `Toy.Perm.no_opPreserving_map_frac_to_count_with_nonempty_value` and every declaration named above.

#### R5a-count-source-bounds-outstanding-holders

**Plain claim.** If a counting source with count n together with a list of non-empty counting permissions has a defined composite (the configuration is consistent; it need not account for the whole permission), the list has at most n elements; if moreover the configuration pools to the total permission and n > 0, the list has at least one element; so in a complete configuration a source with count 1 has exactly one other non-empty piece.

**Kind / tier / depth.** theorem / T1 / shallow. *Tier justification:* Dockins-Hobor-Appel: 'The token factory has collected all its tokens when its share is zero'; the bound on the number of holders is made precise here.

**Lean statement.**

```lean
Toy.Perm.countAlg_source_count_bounds_outstanding_pieces (n : Nat) (ts : List Count)
  (hts : ∀ (t : Count), t ∈ ts → t ≠ none) (hdef : countAlg.opList (source n :: ts) ≠ none) :
  ts.length ≤ n

Toy.Perm.countAlg_complete_source_pos_has_outstanding_piece (n : Nat) (ts : List Count)
  (hc : countAlg.opList (source n :: ts) = some total) (hn : 0 < n) : 1 ≤ ts.length

Toy.Perm.countAlg_source_one_complete_exactly_one_piece (ts : List Count)
  (hts : ∀ (t : Count), t ∈ ts → t ≠ none) (hc : countAlg.opList (source 1 :: ts) = some total) :
  ts.length = 1
```

**Hypothesis ledger.**

- `hts : ∀ t ∈ ts, t ≠ none`: Count only genuine holders; empty pieces can pad a configuration. Tightness: `tight`: counterexample `Toy.Perm.countAlg_source_bound_needs_nonempty_pieces`, `Toy.Perm.countAlg_source_one_exactly_one_needs_nonempty`. Applies to: `countAlg_source_count_bounds_outstanding_pieces`, `countAlg_source_one_complete_exactly_one_piece`.
- `hdef : countAlg.opList (source n :: ts) ≠ none`: The configuration is consistent. Tightness: `tight`: counterexample `Toy.Perm.countAlg_source_bound_needs_defined`. Applies to: `countAlg_source_count_bounds_outstanding_pieces`.
- `hc : countAlg.opList (source n :: ts) = some total (with n = 1 in the corollary)`: The configuration accounts for the whole permission; needed for the lower bound, not for the upper bound. Tightness: `tight`: counterexample `Toy.Perm.countAlg_complete_lower_bound_needs_complete`, `Toy.Perm.countAlg_source_one_exactly_one_needs_complete`. Applies to: `countAlg_complete_source_pos_has_outstanding_piece`, `countAlg_source_one_complete_exactly_one_piece`.
- `hn : 0 < n`: The total permission alone is complete with no other piece. Tightness: `tight`: counterexample `Toy.Perm.countAlg_complete_lower_bound_needs_pos`. Applies to: `countAlg_complete_source_pos_has_outstanding_piece`.

**Depth.** `shallow`.

**Non-vacuity witness.** source 2 with two read tokens (complete) and with one read token (consistent, incomplete: it pools to source 1); source 1 with one read token (complete). Lean: `Toy.Perm.countAlg_source_count_bounds_outstanding_pieces_nonvacuous`, `Toy.Perm.countAlg_source_one_complete_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.countAlg_source_one_exactly_one_needs_nonempty :
  countAlg.opList [source 1, readToken, none] = some total ∧ ¬[readToken, none].length = 1

Toy.Perm.countAlg_source_bound_needs_defined :
  (∀ (t : Count), t ∈ [readToken] → t ≠ none) ∧
    countAlg.opList [source 0, readToken] = none ∧ ¬[readToken].length ≤ 0

Toy.Perm.countAlg_source_count_bounds_outstanding_pieces_nonvacuous :
  (∀ (t : Count), t ∈ [readToken, readToken] → t ≠ none) ∧
    countAlg.opList [source 2, readToken, readToken] ≠ none ∧
      countAlg.opList [source 2, readToken, readToken] = some total ∧
        countAlg.opList [source 2, readToken] = some (source 1)

Toy.Perm.countAlg_source_one_complete_nonvacuous :
  (∀ (t : Count), t ∈ [readToken] → t ≠ none) ∧
    countAlg.opList [source 1, readToken] = some total ∧ 0 < 1
```

The statements of `Toy.Perm.countAlg_source_bound_needs_nonempty_pieces`, `Toy.Perm.countAlg_complete_lower_bound_needs_complete`, `Toy.Perm.countAlg_source_one_exactly_one_needs_complete` and `Toy.Perm.countAlg_complete_lower_bound_needs_pos` are quoted from the source (in `namespace Toy.Perm` with `open FracPerm Count PartialAlg`), because their printed signatures leave the element type of `[none]` or `[]` undetermined:

```lean
-- lean/ToyPerm/LastReader.lean:60-62
theorem countAlg_source_bound_needs_nonempty_pieces :
    countAlg.opList (source 0 :: [none]) ≠ none ∧ countAlg.opList (source 0 :: [none]) = some total ∧
      ¬ ([none] : List Count).length ≤ 0

-- lean/ToyPerm/LastReader.lean:99-101
theorem countAlg_complete_lower_bound_needs_complete :
    countAlg.opList (source 1 :: []) = some (source 1) ∧
      countAlg.opList (source 1 :: []) ≠ some total ∧ 0 < 1 ∧ ¬ 1 ≤ ([] : List Count).length

-- lean/ToyPerm/LastReader.lean:132-134
theorem countAlg_source_one_exactly_one_needs_complete :
    (∀ t ∈ ([] : List Count), t ≠ none) ∧ countAlg.opList (source 1 :: []) ≠ some total ∧
      ¬ ([] : List Count).length = 1

-- lean/ToyPerm/LastReader.lean:107-108
theorem countAlg_complete_lower_bound_needs_pos :
    countAlg.opList (source 0 :: []) = some total ∧ ¬ 1 ≤ ([] : List Count).length
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009.

**Design question.** Can 'the last reader returns ownership' be supported locally: who can tell, from their own permission, how many readers remain?

**Non-claims.** Listed under **Boundaries → Non-claims → R5a-count-source-bounds-outstanding-holders**.

Basis: execution (Lean kernel check): `Toy.Perm.countAlg_source_count_bounds_outstanding_pieces`, `Toy.Perm.countAlg_complete_source_pos_has_outstanding_piece`, `Toy.Perm.countAlg_source_one_complete_exactly_one_piece` and every declaration named above.

Basis: derived (modeling bridge): If a counting source's count is held by the party that will regain ownership, that party knows, when its count is 1, that exactly one other holder remains, so the next return (if it is a single token) completes the whole; the operational reading is not part of the Lean statement.

#### R5b-count-atomic-complete-iff

**Plain claim.** If every outstanding piece is a single read token, then a source with count n together with them pools to the total permission iff there are exactly n of them; in particular, for every n, the total counting permission is the composite of a source with count n and n single read tokens (second theorem).

**Kind / tier / depth.** theorem / T0 / shallow. *Tier justification:* A restatement of Bornat et al.'s counting discipline (source count = number of split-off read permissions; equations (10) and (16)).

**Lean statement.**

```lean
Toy.Perm.countAlg_readTokens_complete_iff_length_eq_count (n : Nat) (ts : List Count)
  (hatom : ∀ (t : Count), t ∈ ts → t = readToken) :
  countAlg.opList (source n :: ts) = some total ↔ ts.length = n

Toy.Perm.countAlg_total_splits_into_source_and_readTokens (n : Nat) :
  countAlg.opList (source n :: List.replicate n readToken) = some total
```

**Hypothesis ledger.**

- `hatom : ∀ t ∈ ts, t = readToken`: The count tracks tokens, not holders; a 2-bundle completes source 2 alone. Tightness: `tight`: counterexample `Toy.Perm.countAlg_bundle_complete_length_ne_count`. Applies to: `countAlg_readTokens_complete_iff_length_eq_count`.

**Depth.** `shallow`.

**Non-vacuity witness.** source 2 with two read tokens; for n = 2, [source 2, readToken, readToken] composes to total. Lean: `Toy.Perm.countAlg_readTokens_complete_iff_nonvacuous`, `Toy.Perm.countAlg_total_splits_example`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.countAlg_bundle_complete_length_ne_count :
  countAlg.opList [source 2, tokens 2] = some total ∧
    [tokens 2].length ≠ 2 ∧
      ¬(countAlg.opList [source 2, tokens 2] = some total ↔ [tokens 2].length = 2)

Toy.Perm.countAlg_readTokens_complete_iff_nonvacuous :
  (∀ (t : Count), t ∈ [readToken, readToken] → t = readToken) ∧
    countAlg.opList [source 2, readToken, readToken] = some total

Toy.Perm.countAlg_total_splits_example :
  countAlg.opList [source 2, readToken, readToken] = some total
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005.

**Design question.** Can 'the last reader returns ownership' be supported locally: who can tell, from their own permission, how many readers remain? Reference point for splitting: Can a reader sub-delegate read access without involving the original owner (fractions), or must every split go through a counting authority (counting)?

**Non-claims.** Listed under **Boundaries → Non-claims → R5b-count-atomic-complete-iff**.

Basis: execution (Lean kernel check): `Toy.Perm.countAlg_readTokens_complete_iff_length_eq_count`, `Toy.Perm.countAlg_total_splits_into_source_and_readTokens` and every declaration named above.

#### R5d-frac-no-element-bounds-holders

**Plain claim.** There is no non-exclusive fractional permission p and number N such that every list of non-empty pieces completing p to the full permission has at most N elements; explicitly, for every p other than 1 and every n >= 1, the halving split of 1 - p into n pieces gives n non-empty pieces that together with p pool to 1. Unlike a counting source, no non-exclusive fractional piece bounds the number of other holders (the exclusive piece 1 bounds them by 0).

**Kind / tier / depth.** impossibility / T1 / shallow. *Tier justification:* Bornat et al. Section 9 note that fractional proofs need not know how many times a permission will be split; the impossibility contrasting with counting sources, with its explicit witness (an n-way split of the complement, itself a T0-level corollary of R2b), is made precise here.

**Lean statement.**

```lean
Toy.Perm.fracAlg_no_nonexclusive_element_bounds_outstanding_pieces :
  ¬∃ p,
      ¬fracAlg.Exclusive p ∧
        ∃ N,
          ∀ (ps : List FracPerm),
            (∀ (x : FracPerm), x ∈ ps → x ≠ zero) →
              fracAlg.opList (p :: ps) = some full → ps.length ≤ N

Toy.Perm.fracAlg_owner_complement_splits_into_any_number (p : FracPerm) (hp : p ≠ full) (n : Nat)
  (hn : 0 < n) :
  (halvingSplit p.compl n).length = n ∧
    (∀ (x : FracPerm), x ∈ halvingSplit p.compl n → x ≠ zero) ∧
      fracAlg.opList (p :: halvingSplit p.compl n) = some full
```

**Hypothesis ledger.**

- `¬ fracAlg.Exclusive p (inside the existential)`: The exclusive piece 1 trivially bounds the others by 0. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_full_bounds_outstanding_pieces`. Applies to: `fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`.
- `∀ x ∈ ps, x ≠ zero (inside the bound)`: Count only non-empty pieces; dropping it only makes the impossibility easier (pad with zeros). Tightness: `harmless`. Applies to: `fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`.
- `hp : p ≠ full`: For p = 1 the complement is 0 and has no non-empty pieces. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_full_complement_piece_is_zero`. Applies to: `fracAlg_owner_complement_splits_into_any_number`.
- `hn : 0 < n`: With zero pieces, p alone is not the whole. Tightness: `tight`: counterexample `Toy.Perm.fracAlg_owner_complement_zero_pieces`. Applies to: `fracAlg_owner_complement_splits_into_any_number`.

**Depth.** `shallow`.

**Non-vacuity witness.** p = 1/2 is not exclusive; with n = 3 the other pieces are [1/4, 1/8, 1/8]. Lean: `Toy.Perm.fracAlg_half_not_exclusive`, `Toy.Perm.fracAlg_owner_complement_splits_nonvacuous`.

**Positive control.** `Toy.Perm.countAlg_source_one_bounds_outstanding_pieces` (a nearby setting in which the conclusion fails; its statement is printed below).

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.fracAlg_full_bounds_outstanding_pieces :
  fracAlg.Exclusive full ∧
    ∀ (ps : List FracPerm),
      (∀ (x : FracPerm), x ∈ ps → x ≠ zero) →
        fracAlg.opList (full :: ps) = some full → ps.length ≤ 0

Toy.Perm.fracAlg_full_complement_piece_is_zero :
  ¬full ≠ full ∧
    0 < 1 ∧
      ¬((halvingSplit full.compl 1).length = 1 ∧
          (∀ (x : FracPerm), x ∈ halvingSplit full.compl 1 → x ≠ zero) ∧
            fracAlg.opList (full :: halvingSplit full.compl 1) = some full)

Toy.Perm.fracAlg_owner_complement_zero_pieces :
  full.half ≠ full ∧
    ¬0 < 0 ∧
      ¬((halvingSplit full.half.compl 0).length = 0 ∧
          (∀ (x : FracPerm), x ∈ halvingSplit full.half.compl 0 → x ≠ zero) ∧
            fracAlg.opList (full.half :: halvingSplit full.half.compl 0) = some full)

Toy.Perm.fracAlg_half_not_exclusive : ¬fracAlg.Exclusive full.half

Toy.Perm.fracAlg_owner_complement_splits_nonvacuous :
  full.half ≠ full ∧ 0 < 3 ∧ List.map val (halvingSplit full.half.compl 3) = [1 / 4, 1 / 8, 1 / 8]

Toy.Perm.countAlg_source_one_bounds_outstanding_pieces :
  ∃ p,
    ¬countAlg.Exclusive p ∧
      ∃ N,
        ∀ (ts : List Count),
          (∀ (t : Count), t ∈ ts → t ≠ none) →
            countAlg.opList (p :: ts) = some total → ts.length ≤ N
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005; [P1] Dockins, Hobor & Appel, APLAS 2009; [P18] Iris 4.3.0, iris/algebra/auth.v.

**Design question.** Can 'the last reader returns ownership' be supported locally: who can tell, from their own permission, how many readers remain?

**Non-claims.** Listed under **Boundaries → Non-claims → R5d-frac-no-element-bounds-holders**.

Basis: execution (Lean kernel check): `Toy.Perm.fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`, `Toy.Perm.fracAlg_owner_complement_splits_into_any_number` and every declaration named above.

#### R5e-reader-side-lastness-undetermined

**Plain claim.** In both designs a returning reader's own piece does not determine whether it is the last one out: for every token bundle tokens k, it completes source k alone, does not complete source (k+1) alone, and does complete source (k+1) together with one more read token; for every fraction q other than 1, it completes 1 - q alone, does not complete (1 - q)/2 alone, and does complete it together with a second piece (1 - q)/2.

**Kind / tier / depth.** theorem / T1 / shallow. *Tier justification:* Elementary computation; it makes precise that lastness is a property of the configuration, not of a reader's piece.

**Lean statement.**

```lean
Toy.Perm.reader_piece_does_not_determine_lastness :
  (∀ (k : Nat),
      countAlg.opList [source k, tokens k] = some total ∧
        countAlg.opList [source (k + 1), tokens k] ≠ some total ∧
          countAlg.opList [source (k + 1), tokens k, readToken] = some total) ∧
    ∀ (q : FracPerm),
      q ≠ full →
        fracAlg.opList [q.compl, q] = some full ∧
          fracAlg.opList [q.compl.half, q] ≠ some full ∧
            fracAlg.opList [q.compl.half, q, q.compl.half] = some full
```

**Hypothesis ledger.**

- `q ≠ full (inner premise of the fraction conjunct)`: For q = 1, [0, 1] already composes to the full permission. Tightness: `tight`: counterexample `Toy.Perm.reader_lastness_needs_ne_full`.

**Depth.** `shallow`.

**Non-vacuity witness.** q = 1/4 satisfies q != 1; for k = 1 the configurations [source 1, readToken] (complete) and [source 2, readToken] (incomplete, pooling to source 1). Lean: `Toy.Perm.reader_lastness_nonvacuous`.

Statements of the counterexamples, witnesses, positive controls and supporting lemmas named above:

```lean
Toy.Perm.reader_lastness_needs_ne_full :
  ¬(fracAlg.opList [full.compl, full] = some full ∧
      fracAlg.opList [full.compl.half, full] ≠ some full ∧
        fracAlg.opList [full.compl.half, full, full.compl.half] = some full)

Toy.Perm.reader_lastness_nonvacuous :
  halfPow 2 ≠ full ∧
    countAlg.opList [source 1, tokens 1] = some total ∧
      countAlg.opList [source 2, tokens 1] = some (source 1)
```

**Prior art.** [P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005.

**Design question.** Can 'the last reader returns ownership' be supported locally: who can tell, from their own permission, how many readers remain?

**Non-claims.** Listed under **Boundaries → Non-claims → R5e-reader-side-lastness-undetermined**.

Basis: execution (Lean kernel check): `Toy.Perm.reader_piece_does_not_determine_lastness` and every declaration named above.

## Boundaries

### Non-claims

What each result does *not* show, verbatim from `results.json`. Attractive stronger conclusions that are not established are stated here explicitly.

#### R1a-frac-count-pcm-laws

- Says nothing about disjointness: both algebras violate it (R1b).
- Positivity here is stated as a . b = unit -> a = unit (PartialAlg.Positive). Dockins-Hobor-Appel's axiom (21) (a . b = c and c . c = c imply a . a = a; PartialAlg.PositiveDHA) is equivalent to it in commutative, unital, cancellative algebras (PartialAlg.positive_iff_positiveDHA) but not in general: z2UnitAlg is a partial commutative monoid satisfying Positive and violating PositiveDHA (PartialAlg.z2UnitAlg_positive_not_positiveDHA). Antisymmetry of the resource preorder (VST join_positivity) is not stated here.
- Does not prove or refute the cross-split axiom of Dockins-Hobor-Appel; cross-split is not examined.
- Fractions here include 0 as an explicit unit; Bornat et al. use (0,1] and treat absence of a heap cell as the unit. Counting here adds none as unit to Bornat's (Z, *1). Results do not transfer automatically to unit-free semigroup formulations or to Iris-style total-operation-plus-validity cameras.
- Fractions are Lean core rationals; real-valued fractions and the dyadic sub-algebra are not separately treated (the dyadic sub-algebra is closed under the operation, so the laws restrict to it).
- Does not cover non-cancellative read-sharing models: discardable fractions (Iris dfrac), abstract read permissions (Heule et al., VMCAI 2013), or duplicable scoped read-only permissions (Chargueraud-Pottier, ESOP 2017).
- Associativity is the strong (Kleene) form: one side defined iff the other is.

#### R1b-disjointness-fails

- Does not show that disjointness is unattainable for shared-read permission models: Dockins-Hobor-Appel's tree-share model satisfies it (not formalized here; mechanized in VST msl/tree_shares.v).
- Does not analyse the consequences of non-disjointness (for example, the binary-tree-versus-DAG predicate issue Dockins-Hobor-Appel attribute to Bornat et al.); not examined.
- For the depth-sum algebra, disjointness fails only when the payload type is inhabited: cellSumAlg Empty satisfies disjointness (cellSumAlg_empty_disjointness).

#### R2a-frac-no-atoms

- Halving is one witness; it does not claim this is the only split, nor that equal n-way splits exist in the dyadic sub-algebra (q/3 is not dyadic).
- Says nothing about whether any party can detect that a split happened (see R5d).
- The n-piece generalization is R2b.

#### R2b-frac-halving-split

- The pieces are not equal (they are dyadic); equal splits q/n exist in the rational algebra but are not the witness here.
- Recombination is in list order through opList; other orders follow from commutativity and associativity (R1a), not from this theorem.
- Exclusivity of 1 means no other party holds anything; it does not mean the holder knows who held the pieces.
- Recombination in the fractional algebra depends only on the amounts summing to 1, not on whether the pieces came from the same split: fractions carry no split provenance.

#### R2c-count-token-atomic

- Bundles of several tokens can be split (countAlg_two_tokens_split); readers holding several tokens can pass some on.
- Atomicity rules out splitting one read token into two non-empty pieces; it does not prevent transferring (moving) a single token to another party, nor sharing read access through an external synchronization protocol or a hierarchical share model such as Dockins-Hobor-Appel tree shares.
- Says nothing about combined fraction/counting models (Bornat et al. Section 10.4), where read permissions are divisible.

#### R2d-count-split-through-source

- Does not say how a program obtains or stores the count; counting here is a ghost algebra, like fractions.
- Says nothing about splits of token bundles (they split into smaller bundles).

#### R3b-depth-fpu-characterization

- Frame-preservation is with respect to single-cell frames; frames that are composites of several views are covered only when the composite is itself a cell (as in the depth-sum algebra, R3c).
- Does not say which updates the prototype permits: it permits the non-frame-preserving end-share and end-borrow under a global check (R3f).
- A consequence used elsewhere: the value of a positive depth plays no role in compatibility (Cell.compat_positive_depth_irrelevant), so compatibility alone cannot distinguish one depth-2 view from a depth-1 view; the depth only gates per-view transitions (R3f, R3g).

#### R3c-depth-sum-pcm-exists

- Does not claim the depth-sum algebra is faithful to the prototype: it identifies one depth-2 view with two depth-1 views, which the transition system distinguishes (R3g).
- Cancellativity is a choice, not forced by the compatibility relation: the idempotent reader-join algebra cellAgreeAlg (readers compose to a depth-1 reader) is commutative and unital, has exactly the same definedness relation, and is not cancellative (cellAgreeAlg_comm_unit_compat_iff_not_cancel).
- The depth-sum algebra still violates disjointness for every inhabited payload type (R1b), and in it the last end-share and the end-borrow are still not frame-preserving (R3d).

#### R3d-restoring-steps-not-frame-preserving

- Does not show the prototype is unsound or that ending the last share is wrong: the prototype performs it under a state-specific check (R3f).
- FramePreserving quantifies over single right frames (PartialAlg.FramePreserving). Any notion of frame-preserving update that includes this single-frame condition (for example Iris cmra_update with a present frame, or notions that also quantify over left frames or composite frames) is refuted as well. Nondeterministic (set-valued) updates are not covered.
- Does not exclude logics in which the restoring step is not a single-element update e(c) to e(c'): updates that also consume or consult another resource, such as an authoritative element recording all outstanding readers (Iris auth), view-indexed separation with explicit whole-root return authority (the prototype's RootReturn rule), or other enriched carriers and multi-resource updates.
- Escape hatch (h_readers): if two views can never be at positive depth simultaneously (single-holder regime), the last end-share is frame-preserving (positive control). The single-holder regime rescues only the last end-share: the end-borrow remains non-frame-preserving there.
- Escape hatch (h_neutral): dropping h_neutral is possible only in algebras where e(borrowed) is not a unit for readers (twoClassAlg is not unital); in any unital algebra interpreting borrowed as the unit, h_neutral holds automatically (h_neutral_of_unitLeft).

#### R3e-no-local-token-return-beside-other-reader

- Associativity is required (nonAssocDepthAlg is commutative and unital, not associative, and satisfies the other hypotheses). Commutativity and the unit law are not used; in a commutative algebra the exclusion may be written in either order.
- For partial commutative monoids the same impossibility holds with the state written as opList [t, e(shared 1 v), e(shared 1 v)] != none and the exclusion as not Compat e(shared 0 v) e(shared 1 v) (no_pcm_returns_last_share_by_composition_beside_another_reader).
- Does not exclude token-based accounts in which the token-absorption composite is not exclusive by itself and exclusivity is concluded from an authoritative record of all readers (Iris auth style).
- Escape hatch (hstate): if two depth-1 readers cannot coexist, the return by composition works (tokenReturnAlg, a partial commutative monoid; also the counting algebra with cells read as sources, counting_returns_last_share_without_coexisting_reader).

#### R3f-depth-transition-characterization

- One address only; the prototype checks compatibility for every byte of every overlapping view and also checks bounds, liveness, alignment and provenance (not modelled).
- View creation and retirement (exposures, returns) and permissions held implicitly outside the explicit heap are not modelled.
- Characterizes raw per-cell compatibility only: end-borrow is enabled whenever every other active view is borrowed, including when another active view is itself a borrowed child. The prototype's scoped return contracts (RootReturn) exclude every other active view of the root, including suspended ones, and so impose strictly stronger preconditions than this enabledness condition.
- Cell.stepAt_isSome_iff is derived from Cell.valid_set_iff and inherits its proof status.

#### R3g-depth-sum-not-faithful

- Refutes faithfulness of the depth-sum algebra only; it does not show that every PCM fails to abstract the transition system (see R3d, R3e for the general statements).
- Concerns immediate enabledness of end-share in this fixed-list transition model, not multi-step reachability of a depth-0 cell.
- Does not show that two overlapping shared views can never regain exclusivity in the prototype: there an independent shared exposure retires at depth 1 (Heap.endSharedExposure removes the view instead of decrementing it to depth 0), after which the remaining view can end its share to depth 0. View retirement is not modelled here.

#### R4a-bounded-count-embeds-in-frac

- Compatibility is not reflected: for N >= 1 no composition-preserving map from N-bounded counting to fractions reflects compatibility (R4b); under countEmbed 1 two single tokens are incompatible but their images 1/4, 1/4 are compatible, with composite 1/2 outside the image.
- The step matters: with the step 1/(2N+1) (for N = 1: token 1/3, source 2/3) composition is still preserved but not reflected, because 1/3 + 1/3 = 2/3 is the image of a source (countEmbedThirds_preservesOp_not_reflecting).
- Does not preserve atomicity of single read tokens: inside the fractional algebra the image 1/(3N+1) of a token splits further into two non-zero halves (R2a).
- Does not preserve the counting source's bound on outstanding holders inside the fractional algebra: the complement of the image of a source splits into any number of non-zero fractions (R5d).
- The image lies in the dyadic sub-algebra only when 3N+1 is a power of two (for example N = 1, N = 5); variants with other steps (for example a dyadic step 1/2^k with 2^k >= 3N+1) are not stated here.
- States IsPCM for the bounded algebra only; Cancel and Positive for it are not stated here (they are inherited from the counting algebra, R1a, but this is not proved).
- Does not extend to unbounded counting: no composition-preserving map from unbounded counting gives a token a non-zero fraction (R4c).
- A different N gives a different map; there is no single map for all bounds.

#### R4b-bounded-embedding-not-reflecting

- Does not say that every composition-preserving map gives compatible images to two bundles tokens N, nor that every such map gives compatible images to two sources source N: for every N >= 1 each of the two pairs keeps incompatible images under some composition-preserving map that also sends the unit to 0 and total to 1 (opPreserving_maps_countB_to_frac_keep_either_pair_incompatible). Only the disjunction holds for every composition-preserving map.
- Classifies only the two pairs (source N, source N) and (tokens N, tokens N); which other incompatible pairs of N-bounded counting receive compatible images under a given map is not examined.
- Does not say that composition cannot be reflected: countEmbed N reflects every fractional composite that lands in its image (R4a); the failure is only for compatibility, where the fractional composite of two images may lie outside the image.
- Does not exclude translations into enriched fractional models (for example fractions paired with a token count); only maps into the plain fractional algebra are considered.
- The impossibility and the disjunction assume neither the unit law for f nor f total = 1; the two maps that keep one pair incompatible satisfy both.

#### R4c-no-count-to-frac-with-readable-token

- Only element-wise maps are excluded. Per-configuration translations exist: any finite configuration of a source and n tokens can be mirrored by n + 1 non-zero fractions summing to 1 (for example the halving split of R2b), and stateful run-level simulations that give successively issued tokens different fractions (1/2, 1/4, 1/8, ...) are not excluded.
- The unit law is not assumed for f; PreservesOp alone forces f(tokens n) = n . f(readToken).
- Exclusivity alone can be preserved: countToFracSourcesOnly (every source to 1, empty and every token bundle to 0) preserves the unit and composition and sends total to 1, failing only f readToken != 0 (countToFracSourcesOnly_preserves_unit_op_total); so f readToken != 0 cannot be replaced by f total = 1.
- Escape hatch (bounded counts): bound the counts (positive control and R4a). Bundles cannot simply be forbidden: associativity forces a source with count 2 to accept two tokens one at a time, so the 2-bundle must be defined.
- Escape hatch (target without the bound 1 or without the Archimedean property): the argument uses that fractions are at most 1 and that rationals are Archimedean; unbounded positive rationals, non-Archimedean or symbolic infinitesimal read amounts, or abstract read permissions (Heule et al., VMCAI 2013) are not covered.

#### R4d-no-frac-to-count-preserving-exclusivity

- On the full fractional algebra this is subsumed by R4e (every composition-preserving map from fractions to counting is constantly empty); the self-composite obstruction is independent of infinite divisibility and is the operative one on finitely divisible sub-algebras containing 1/2, such as the half-grid, where a composition-preserving map keeping every non-zero element non-empty does exist (halfGridToCount_preservesOp_nonempty).
- Escape hatch (asymmetric splits): the obstruction is the symmetric split 1 = 1/2 . 1/2, not splitting as such. The asymmetric grid {0, 1/4, 3/4, 1}, exactly a sub-algebra of the fractions (asymGridToFrac_preserves_reflects), maps into counting with 1/4 to readToken, 3/4 to source 1 and 1 to total, preserving composition (positive control).
- Escape hatch (no split of 1): on the non-splittable sub-algebra {0, 1} of fractions (exclAlg, embedded by exclToFrac_preserves_reflects) such a map exists (positive control).
- Does not exclude protocol-level simulations where splits are routed through a counting source.

#### R4e-no-frac-to-count-preserving-nonemptiness

- Uses only the halving chain q, q/2, q/4, ...; it applies equally to the dyadic sub-algebra.
- Relaxing 'every non-zero fraction maps to a non-empty counting permission' to 'some fraction maps to a non-empty counting permission' does not escape the impossibility on the full fractional algebra.
- Escape hatch (finite divisibility): on the finitely divisible sub-algebra {0, 1/2, 1} (embedded by halfGridToFrac_preserves_reflects), i/2 maps to i tokens, preserving composition and non-emptiness; that map sends 1 to a 2-token bundle, not to the total permission (R4d).

#### R5a-count-source-bounds-outstanding-holders

- The upper bound depends only on consistency, not on completeness: leaked or incomplete configurations still have at most n other non-empty pieces.
- Bounds the number of holders, not their identity; holders of bundles make the number smaller than n.
- Only the source has this knowledge; a token holder does not (R5e).
- Ghost-level statement; it does not say a program can read the count at run time.

#### R5b-count-atomic-complete-iff

- Does not say tokens are returned in any particular order or to any particular party.
- Nothing in the counting algebra prevents two readers from merging their single tokens into a bundle tokens 2; hatom is an external protocol invariant, not enforced by the algebra.
- The split of the total permission into a source and n tokens exists for every n, but this does not say the pieces can be produced without the source: by R2c single tokens cannot be split further, and by R2d every split of a source goes through its count.

#### R5d-frac-no-element-bounds-holders

- Escape hatch (counting and authoritative models): permissions carrying an atomic count (counting sources, positive control) or an authoritative record of all outstanding holders restore a bound. By contrast, Bornat et al.'s combined model (Q, *3) of Section 10.4 has divisible read permissions and does not restore a bound on the number of holders.
- Escape hatch (minimum quantum, not formalized here): restricting holders to pieces of at least some fixed epsilon > 0 (for example multiples of 1/M) bounds the number of other non-empty pieces by (1 - p)/epsilon, since n such pieces sum to at least n . epsilon.
- Does not say fractions cannot detect recombination: the holder of 1 is exclusive (fracAlg_exclusive_iff) and whether a returned piece completes the whole is decided by the two amounts alone (fracOp_eq_some_iff); if returned pieces are pooled at one place, the pool reaching 1 is locally detectable.
- Does not say the number of holders is unbounded in any particular run; only that the owner's piece does not bound it.

#### R5e-reader-side-lastness-undetermined

- Says nothing about designs with a shared physical counter (reference counting), which are not modelled.
- The k = 0 and q = 0 instances are degenerate (the empty permission is not a reader piece) but hold as stated.
- Does not rule out last-reader detection through a shared synchronization point: a returning reader can enter a critical region holding the source permission (or a fractional pool), combine its piece there and check whether the result is total, as in the readers-and-writers proof of Bornat et al. Section 8.1.

### Escape hatches

For each impossibility result (and for R4e, a characterization whose second theorem is an impossibility), the entries below take its `tight` hypotheses one at a time and state what the named Lean counterexample shows. An entry says that dropping a hypothesis defeats an impossibility only when the counterexample satisfies every other hypothesis of that impossibility theorem and its conclusion fails there. Where the counterexample defeats only one conjunct of the conclusion, or refutes a companion theorem (a disjunction, an existence statement or a constructive witness) rather than the impossibility, the entry says so.

- **R3d-restoring-steps-not-frame-preserving** (one theorem; its conclusion has an end-share conjunct and an end-borrow conjunct):
  - drop `h_readers : A.Compat (e (shared 1 v)) (e (shared 1 v))`: in `Toy.Perm.singleHolderAlg_last_endShare_framePreserving`, `h_excl` and `h_neutral` hold and the last end-share is frame-preserving, so the end-share conjunct fails; the end-borrow conjunct still holds there (the end-borrow is not frame-preserving). Dropping `h_readers` defeats only the end-share half of the impossibility.
  - drop `h_excl : ¬ A.Compat (e (shared 0 v)) (e (shared 1 v))`: in `Toy.Perm.allCompatAlg_restoring_steps_framePreserving`, `h_readers` and `h_neutral` hold and both restoring steps are frame-preserving, so both conjuncts fail.
  - drop `h_neutral : A.Compat (e borrowed) (e (shared 1 v))`: in `Toy.Perm.twoClassAlg_endBorrow_framePreserving`, `h_readers` and `h_excl` hold and the end-borrow is frame-preserving, so the end-borrow conjunct fails (the counterexample states nothing about the end-share step). Its algebra is not unital; in a unital algebra interpreting borrowed as the unit, `h_neutral` holds automatically (`Toy.Perm.h_neutral_of_unitLeft`).
- **R3e-no-local-token-return-beside-other-reader** (conclusion `False`): each counterexample satisfies the other three hypotheses, so dropping the named hypothesis defeats the impossibility.
  - drop `hassoc : A.Assoc`: `Toy.Perm.nonAssocDepthAlg_returns_last_share_beside_reader` (`hstate`, `hret` and `hexcl` hold; the algebra is commutative and unital but not associative).
  - drop `hstate : ((A.op (e (shared 1 v)) (e (shared 1 v))).bind fun x => A.op x t) ≠ none`: `Toy.Perm.tokenReturnAlg_returns_last_share_without_second_reader` (associative; `hret` and `hexcl` hold; the two-reader state with the token is undefined).
  - drop `hret : A.op (e (shared 1 v)) t = some (e (shared 0 v))`: `Toy.Perm.exclAgreeAlg_unit_token_does_not_restore` (associative; `hstate` and `hexcl` hold; absorbing the token does not give the depth-0 cell).
  - drop `hexcl : ¬ A.Compat (e (shared 1 v)) (e (shared 0 v))`: `Toy.Perm.allZeroAlg_return_beside_reader` (associative; `hstate` and `hret` hold; the depth-1 reader is compatible with the depth-0 cell).
- **R4b-bounded-embedding-not-reflecting** (the impossibility is the first theorem, `no_opPreserving_map_countB_to_frac_reflecting_compat`):
  - drop `hN : 1 ≤ N`: `Toy.Perm.countB0Embed_preservesOp_reflects_compat` (at N = 0, `countEmbed 0` preserves composition and reflects compatibility) defeats the impossibility.
  - drop `PreservesOp (countBAlg N) fracAlg f (conjunct of the excluded map; hypothesis hf of the disjunction)`: `Toy.Perm.countB1AllFull_reflects_compat` (at N = 1, some map reflects compatibility) defeats the impossibility.
  - drop `∀ a b, fracAlg.Compat (f a) (f b) → (countBAlg N).Compat a b (conjunct of the excluded map)`: `Toy.Perm.countB1Embed_preservesOp` (at N = 1, some map preserves composition) defeats the impossibility.
  - Companion theorems (these counterexamples are not escape hatches of the impossibility): `Toy.Perm.countB0Embed_sources_or_bundles_compat_fails` (for `hN`) and `Toy.Perm.countB1AllFull_sources_or_bundles_compat_fails` (for `hf`) show that the conclusion of the disjunction theorem `opPreserving_map_countB_to_frac_sources_or_bundles_compat` fails without those hypotheses; `Toy.Perm.countB0_keep_either_pair_incompatible_fails` (for `hN`) shows that the conclusion of the existence theorem `opPreserving_maps_countB_to_frac_keep_either_pair_incompatible` fails at N = 0.
- **R4c-no-count-to-frac-with-readable-token**:
  - drop `PreservesOp countAlg fracAlg f`: `Toy.Perm.const_full_nonzero_token` (some map sends the read token to a non-zero fraction) defeats the impossibility.
  - drop `f readToken ≠ zero`: `Toy.Perm.const_zero_preservesOp` (some map preserves composition) defeats the impossibility; `Toy.Perm.countToFracSourcesOnly_preserves_unit_op_total` gives such a map that also preserves the unit and sends total to 1.
- **R4d-no-frac-to-count-preserving-exclusivity** (three theorems: the parametric one, its instance for the fractions, and its instance for the half-grid):
  - drop `hh : A.op h h = some a` (a hypothesis of the parametric theorem only): `Toy.Perm.exclToCount_preservesOp_full_to_total` (in `exclAlg` with h = a = true, where true . true is not true, a composition-preserving map sends a to total) defeats the parametric theorem.
  - drop `PreservesOp A countAlg g`: `Toy.Perm.indicator_full_to_total` (over the fractions, where 1/2 . 1/2 = 1, some map sends 1 to total) defeats the parametric theorem (at A = fracAlg) and the fractional theorem. No Lean counterexample is recorded for the half-grid theorem.
  - drop `g a = total`: `Toy.Perm.const_none_preservesOp_frac_half` (over the fractions, where 1/2 . 1/2 = 1, some map preserves composition) defeats the parametric theorem (at A = fracAlg) and the fractional theorem; `Toy.Perm.halfGridToCount_preservesOp_nonempty` (a composition-preserving map on the half-grid) defeats the half-grid theorem.
- **R4e-no-frac-to-count-preserving-nonemptiness** (first theorem: the characterization; second theorem: the impossibility):
  - drop `hg : PreservesOp fracAlg countAlg g` (first theorem): `Toy.Perm.const_readToken_not_none` (the constant map to readToken is not constantly none) defeats the characterization.
  - drop `PreservesOp fracAlg countAlg g (conjunct of the excluded map)` (second theorem): `Toy.Perm.const_readToken_nonempty` (some map sends some fraction to a non-empty permission) defeats the impossibility.
  - drop `∃ q, g q ≠ none (conjunct of the excluded map)` (second theorem): `Toy.Perm.opPreserving_map_frac_to_count_exists` (some map preserves composition) defeats the impossibility.
- **R5d-frac-no-element-bounds-holders** (the impossibility is the first theorem, `fracAlg_no_nonexclusive_element_bounds_outstanding_pieces`):
  - drop `¬ fracAlg.Exclusive p (inside the existential)`: `Toy.Perm.fracAlg_full_bounds_outstanding_pieces` (the exclusive piece 1 bounds the other non-empty pieces by 0) defeats the impossibility.
  - `∀ x ∈ ps, x ≠ zero (inside the bound)` is `harmless` (not an escape hatch).
  - Companion theorem (these counterexamples are not escape hatches of the impossibility): `hp : p ≠ full` and `hn : 0 < n` are hypotheses of the constructive theorem `fracAlg_owner_complement_splits_into_any_number`; `Toy.Perm.fracAlg_full_complement_piece_is_zero` and `Toy.Perm.fracAlg_owner_complement_zero_pieces` show that its conclusion fails without them. They say nothing about the impossibility.

The non-claims also discuss escape hatches in prose; those items are repeated verbatim below. They are not hypothesis-ledger entries. Where an item cites a positive control or another Lean declaration, that is its kernel-checked evidence; the rest of each item, including the one marked "not formalized here", is explanatory commentary and is not kernel-checked.

- R3d-restoring-steps-not-frame-preserving: Escape hatch (h_readers): if two views can never be at positive depth simultaneously (single-holder regime), the last end-share is frame-preserving (positive control). The single-holder regime rescues only the last end-share: the end-borrow remains non-frame-preserving there.
- R3d-restoring-steps-not-frame-preserving: Escape hatch (h_neutral): dropping h_neutral is possible only in algebras where e(borrowed) is not a unit for readers (twoClassAlg is not unital); in any unital algebra interpreting borrowed as the unit, h_neutral holds automatically (h_neutral_of_unitLeft).
- R3e-no-local-token-return-beside-other-reader: Escape hatch (hstate): if two depth-1 readers cannot coexist, the return by composition works (tokenReturnAlg, a partial commutative monoid; also the counting algebra with cells read as sources, counting_returns_last_share_without_coexisting_reader).
- R4c-no-count-to-frac-with-readable-token: Escape hatch (bounded counts): bound the counts (positive control and R4a). Bundles cannot simply be forbidden: associativity forces a source with count 2 to accept two tokens one at a time, so the 2-bundle must be defined.
- R4c-no-count-to-frac-with-readable-token: Escape hatch (target without the bound 1 or without the Archimedean property): the argument uses that fractions are at most 1 and that rationals are Archimedean; unbounded positive rationals, non-Archimedean or symbolic infinitesimal read amounts, or abstract read permissions (Heule et al., VMCAI 2013) are not covered.
- R4d-no-frac-to-count-preserving-exclusivity: Escape hatch (asymmetric splits): the obstruction is the symmetric split 1 = 1/2 . 1/2, not splitting as such. The asymmetric grid {0, 1/4, 3/4, 1}, exactly a sub-algebra of the fractions (asymGridToFrac_preserves_reflects), maps into counting with 1/4 to readToken, 3/4 to source 1 and 1 to total, preserving composition (positive control).
- R4d-no-frac-to-count-preserving-exclusivity: Escape hatch (no split of 1): on the non-splittable sub-algebra {0, 1} of fractions (exclAlg, embedded by exclToFrac_preserves_reflects) such a map exists (positive control).
- R4e-no-frac-to-count-preserving-nonemptiness: Escape hatch (finite divisibility): on the finitely divisible sub-algebra {0, 1/2, 1} (embedded by halfGridToFrac_preserves_reflects), i/2 maps to i tokens, preserving composition and non-emptiness; that map sends 1 to a 2-token bundle, not to the total permission (R4d).
- R5d-frac-no-element-bounds-holders: Escape hatch (counting and authoritative models): permissions carrying an atomic count (counting sources, positive control) or an authoritative record of all outstanding holders restore a bound. By contrast, Bornat et al.'s combined model (Q, *3) of Section 10.4 has divisible read permissions and does not restore a bound on the number of holders.
- R5d-frac-no-element-bounds-holders: Escape hatch (minimum quantum, not formalized here): restricting holders to pieces of at least some fixed epsilon > 0 (for example multiples of 1/M) bounds the number of other non-empty pieces by (1 - p)/epsilon, since n such pieces sum to at least n . epsilon.

### Hypotheses with `unknown` tightness

None. Every hypothesis is `tight` (with a Lean counterexample) or `harmless` (with the reason stated in its ledger entry).

### Disproved or dropped statements

None. Every result stated for this package was proved in exactly its stated form.

### Not examined

- Other Lean versions; real-valued fractions as a separate carrier; Iris-style cameras with validity and step-indexing; set-valued (nondeterministic) frame-preserving updates; enriched translation targets; multi-address or multi-byte sharing-depth configurations; any concurrency semantics or program logic built on these algebras.

## Evidence

**Observation date.** All evidence (build, axiom audit, statement hashes, source records) was acquired or revalidated on 2026-11-20.

**Toolchain.** `leanprover/lean4:v4.34.1`; the tag `v4.34.1` resolves to commit `5045d0056413266e57c625dcd7c365b10e377c52` (GitHub API `repos/leanprover/lean4/git/ref/tags/v4.34.1`, and `lean --version` of the installed toolchain reports the same commit). No other dependencies.

**Build and axioms.** `lake build` of `lean/` succeeds with no errors and no `sorry` warnings. The Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern` or `unsafe`. Lean's `collectAxioms` was run on all 541 declarations of the library (`audit/axioms.json`); every one depends only on a subset of `propext`, `Classical.choice`, `Quot.sound`.

**Kernel-check record.** For each result theorem and each counterexample, non-vacuity witness and positive control named in `results.json`: its axioms; the SHA-256 of its statement (Lean `repr` of its type); and the SHA-256 of its definition closure (sorted `name : repr(type) := repr(value)` lines of every package-local constant reachable from the statement, theorem bodies excluded), with the closure size. Source: `audit/statements.json` and `audit/axioms.json`.

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Cell.compatFPU_iff` | R3b result | propext | `d47fcef2eba4f6e8d9c41c1432b23049193b27fbf6355d68f90606a6f5c4c73d` | `d1721a81bf46bf29d59036a8882a376d813f236cb6023d0c7f4a220721dc0336` (8) |
| `Cell.compatFPU_iff_nonvacuous` | R3b witness | none | `f9d7b85735f7c2bba1b8b199bd679e4f0352a73caa96b383fd012aab037a3639` | `9a3ccbdd9de2a82919d3162b7e5645147d0659861ca403351656b09f43b90598` (3) |
| `Cell.stepAt_isSome_iff` | R3f result | Classical.choice, Quot.sound, propext | `042608861457a998bd6007e3da977b77ff929a32faf01004fbec6193683c3b94` | `386d4e1c64faafaa00184a46391f810b30e0ed33a61eca0286931e510dacf303` (26) |
| `Cell.stepAt_isSome_iff_needs_valid` | R3f counterexample | propext | `34e2321696da3a1dadf0b89bc09c693e76c9852063afd06ce3f4d9e8360c3890` | `386d4e1c64faafaa00184a46391f810b30e0ed33a61eca0286931e510dacf303` (26) |
| `Cell.valid_set_iff` | R3f result | Classical.choice, Quot.sound, propext | `7d08d2d7b1d1744aad48e51ce8cda637ae329f8b37202290f0e3328c23b4554b` | `0df8e01d3cb9b031e21d9cf70bd74ed77492cc214e21a87c7438138cc1fa884a` (23) |
| `Cell.valid_set_iff_needs_apply` | R3f counterexample | propext | `dbb042a2341782a6c56cc78a0dcf6fa5de76c94d8e641cc23c572c0a7814f382` | `0df8e01d3cb9b031e21d9cf70bd74ed77492cc214e21a87c7438138cc1fa884a` (23) |
| `Cell.valid_set_iff_needs_lookup` | R3f counterexample | propext | `3b7d17c0c6c5615c56a74cd5b80459ad77f1c24c820faa6ca9e4f493f17fe21a` | `0df8e01d3cb9b031e21d9cf70bd74ed77492cc214e21a87c7438138cc1fa884a` (23) |
| `Cell.valid_set_iff_needs_valid` | R3f counterexample | propext | `50c8c477e1856164be48f7b9ab358875f8156774a598d3b95404cc18a811cc69` | `0df8e01d3cb9b031e21d9cf70bd74ed77492cc214e21a87c7438138cc1fa884a` (23) |
| `Cell.valid_set_iff_nonvacuous` | R3f witness | propext | `7d084c1191c7a15da293625f40fe930a23b407aac59ff99a34ecafa367dea53f` | `0df8e01d3cb9b031e21d9cf70bd74ed77492cc214e21a87c7438138cc1fa884a` (23) |
| `CellStep.restoresExclusive_iff` | R3f result | propext | `54cf34874e66f82959ad962debfba9defb3a77d279c9844bed22527b75de86e6` | `3e600125537d10aca07cc874a159e6d7773a674e8d3fc88053ecad44f7fd8cd2` (20) |
| `allCompatAlg_restoring_steps_framePreserving` | R3d counterexample | none | `1d60502e99375c24cd4a798f169106844b086d929fa968e03865ae0dbb51de31` | `32372d7b8fbdc069c3d64f887099f322aedda331ea8fe61ceb174f70d7c56ad6` (9) |
| `allZeroAlg_return_beside_reader` | R3e counterexample, R3e witness | none | `d22590026e493a104a602cc62576b0ad45ca7425a1a25b4065e7a3e993144095` | `1d48cdd1f4a276459870324d7aae3f1fe2169d3147af525197a31054142e2c7b` (9) |
| `asymGridToCount_preservesOp_full_to_total` | R4d positive control | propext | `bb89172ceb2da69521a9b1fc9663bf6e1d8eefab3aeed672165e956ab3d26aae` | `7afc2c15fdda83543eba6244e000f650dba405d0e3e945e2732f1dbf7ccc0547` (16) |
| `cellSumAlg_compat_examples` | R3c witness | propext | `f6828f0c748fd9761e7e0db875a36cacf94180c4832609a53e33933e4e65638f` | `e65d2cfa6fd89a02c360baa3bd6a4493dd59873f08ca7096b47ad87783ce62b3` (15) |
| `cellSumAlg_composite_does_not_determine_endShare_enabled` | R3g result | Quot.sound, propext | `71e905f9617d4db674941b632f4b115dc8b1ae69696c361bc326f00a96a1fbb4` | `bc249e20367e89bb48b0eeebac1714a99a10865559f310610bccc6d12b1364ef` (35) |
| `cellSumAlg_composite_does_not_determine_endShare_enabled_nat` | R3g witness | Quot.sound, propext | `8112f0caf86c6243b139315c10b4e71cb9a76fffd9834dd92e6e578a3beee75b` | `bc249e20367e89bb48b0eeebac1714a99a10865559f310610bccc6d12b1364ef` (35) |
| `cellSumAlg_empty_disjointness` | R1b counterexample | propext | `17ca8ca8ad4c0fbd26629b6741675a0db91576eb92dc75a27b40be72d1b921d0` | `0db7b90cf9dfc1fd277b3ab8fe937ad6ac8623cd635743c18677e4c55a8acbdd` (13) |
| `cellSumAlg_isPCM_cancel_positive_compat_iff` | R3c result | Quot.sound, propext | `ed13d3e763291976af5d3b7feef3309073881360f34d9eb2803fea24c7be2de1` | `8cfaaf79f406519fe5695a9c74b85bd7c560c35cf44f803934c2e0cb558c3163` (22) |
| `const_full_nonzero_token` | R4c counterexample, R4c witness | Classical.choice, Quot.sound, propext | `0d5982452cdb11906167eece298bd4fb72f515cf960132a399b7ede8219ec1e3` | `112af9b0fe3c3785ecd3bb4d64424bf1cd452366d1382af762e6bf961ae3c375` (7) |
| `const_none_preservesOp_frac` | R4e witness | Classical.choice, Quot.sound, propext | `804c86ca7f94ad8848debad89c5292f637355d5e5524d3428ed01c2e6e2179a2` | `ad9574770b9271be0659d1f34749c0ac6f6e03cc9e55976c9048b5605ba0d10b` (17) |
| `const_none_preservesOp_frac_half` | R4d counterexample | Classical.choice, Quot.sound, propext | `67431e4ac9c7f946c46d964b6806f613171e8a771262049c71969b42de11d732` | `d0414f91c3863303e0de892c97abea14784343d6321ec93341277f37625f944a` (22) |
| `const_readToken_nonempty` | R4e counterexample | Classical.choice, Quot.sound, propext | `dae5d6cd1b33926244d8f76b9d72dd4a2e794605a7ed8c14c31dba6228326056` | `d987502dca27982dc730eb8fd8c11e2bca80cac6635d4435b757d6be8a711796` (3) |
| `const_readToken_not_none` | R4e counterexample | Classical.choice, Quot.sound, propext | `06ffdf4f4c00e9c631d554fec00acc235aeac07b004331ee38e7350223899068` | `4b942d6f1ce1c499aef58e252c43589a7dcc999842cad0c059e6ac3e51f925fd` (4) |
| `const_zero_preservesOp` | R4c counterexample, R4c witness | Classical.choice, Quot.sound, propext | `8474158953327d12dac96a78da52378d6951478f3723768caf717ddfa0287b06` | `ad9574770b9271be0659d1f34749c0ac6f6e03cc9e55976c9048b5605ba0d10b` (17) |
| `countAlg_bundle_complete_length_ne_count` | R5b counterexample | none | `3d73f80dee3536e7ffc42137d618e557dbf1551c19d277b5a7ed5ba90a99aafd` | `50b1354cab543df6856d93b6678c7ac4f82980cc98e14065685509a878993632` (15) |
| `countAlg_complete_lower_bound_needs_complete` | R5a counterexample | none | `d2c12456b77662135f0e7614f6d5c2afac9b72d6ab96b0fd4a6da170d31c2e7b` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_complete_lower_bound_needs_pos` | R5a counterexample | none | `7c0df45c52ce297dd8fbbd1c90b49c203c19648263741f2032c476bb7650e425` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_complete_source_pos_has_outstanding_piece` | R5a result | Classical.choice, Quot.sound, propext | `7cbdc749a9deb1bd65a6eac993069c4efa6b3ff02fddb23273a121b2c49be55d` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_examples` | R1a witness | none | `5b68e434358698d4b95766ea3f83d49b1b8a507f1cc57a2e639433e03facdeac` | `4a373c0445eda42e0432b4cedd40c3420e876386fb25c732de1e7250bdf93e2b` (12) |
| `countAlg_isPCM_cancel_positive` | R1a result | Classical.choice, Quot.sound, propext | `10748f09e66f80e2cc2f61d4942fafed43ff8ce58d162a9c0a49e19300d5ae1c` | `be39e1b714efdf5557e521cb91126d9fca0920223b69646b3fb856e4b224cf38` (14) |
| `countAlg_readToken_atomic` | R2c result | Quot.sound, propext | `605ea59ed8f9cc84dc303f8f07ed544322713bd20fdd63204161a00d47db0a3d` | `b8efd0c669983733bea9dd7191e03b64d667db68e248676de24b5bcd6d12ae6d` (8) |
| `countAlg_readToken_atomic_needs_h` | R2c counterexample | none | `f2e4aff5823f2c049f71b10e35c597e81ee20c250732b43640d722733729b7e8` | `d9bd2a5b53366c3c534c83a945ad63ccb67377327a67f0bafda3f78038970db2` (10) |
| `countAlg_readToken_atomic_nonvacuous` | R2c witness | none | `97afa6a9a5e3455d2bae11564b840dcd5cbda9ac0c30b6a2cff2d2013f2d1131` | `b8efd0c669983733bea9dd7191e03b64d667db68e248676de24b5bcd6d12ae6d` (8) |
| `countAlg_readTokens_complete_iff_length_eq_count` | R5b result | Classical.choice, Quot.sound, propext | `256a84240da3a71ddc556969d6239776ffdf2b9c1b651d8f8a2e5c362d43a3c4` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_readTokens_complete_iff_nonvacuous` | R5b witness | none | `46377e6752012fa5cdcb2756a972eee289d6fed2d35127a5e82090f411352449` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_source_bound_needs_defined` | R5a counterexample | none | `a0c9bb5ed1d17f3e11d376ca32ef78db5db1a9ef34ff163b3d8091af3488d26d` | `db9c89f73d73c52cb58ff5237219b31885347d70364fb70d2f81eb526aaf3c54` (13) |
| `countAlg_source_bound_needs_nonempty_pieces` | R5a counterexample | none | `520e45bec99e543b5c25b827c81bc735a87011b33157fd385bceaf54a73c92ef` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_source_count_bounds_outstanding_pieces` | R5a result | Quot.sound, propext | `9559b04693717c8ff99e7bc43aa97ebebd54911d8cfdd2a1c260df7048c77e13` | `a9173e5c87bf807823549dce74a585c1e912dbc4aeba626a8df5c5397e530163` (12) |
| `countAlg_source_count_bounds_outstanding_pieces_nonvacuous` | R5a witness | none | `6c6ae189a215e63a26aeffc18518e524a81d0280cfa14caf8fb2771f18bd3d79` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_source_one_bounds_outstanding_pieces` | R5d positive control | Classical.choice, Quot.sound, propext | `96b1118f3f0f41c48971d872d5c3b72a89054272c05eb5297da9bcb64cc3dff2` | `1f3eca6b9126f5d800db12c0c032b448626b2be40da82491d55055a5838750d8` (14) |
| `countAlg_source_one_complete_exactly_one_piece` | R5a result | Classical.choice, Quot.sound, propext | `2143283ed1c944c467c6f001b5387ed6076368e506ed8d608589e98dc8c0617c` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_source_one_complete_nonvacuous` | R5a witness | none | `fba47891bac69048ba2755f4aa99c1167e2762dddc8ecd9a50f732a4ec860bce` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_source_one_exactly_one_needs_complete` | R5a counterexample | none | `96436314927b8e4c7114b82baaa2777b32bd94f10a47beb40f6ba41f88ca41ee` | `a295b32888b607e11233a4d9d7e62d0bbb8944963bd69fd469930e670c6a9ac4` (13) |
| `countAlg_source_one_exactly_one_needs_nonempty` | R5a counterexample | none | `3a79730bbd959867f21879ca9fc1e20ecaad27ed20ef97394701bf9f5f20c2a1` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_split_of_source` | R2d result | Quot.sound, propext | `ad741e7f741a25bed78e4b3caaacab52cb27087bbfb84f6780e623dd4ae9194f` | `8c91db65fe2c084cb7c57e628531b6cae27fbdfbe9b24bfa38beec92b15afd7c` (10) |
| `countAlg_split_of_source_needs_h` | R2d counterexample | propext | `ce69e2ed1a0692e1a8418e8ff9d76084b2cf60ae09b21c0db290b566d6394d0c` | `255defd13e8d62d11825829b1c6b713eab1154b0af64a5d1bb10157935d78ae5` (11) |
| `countAlg_split_of_source_needs_ha` | R2d counterexample | Quot.sound, propext | `8cdac5961725be96665087a71b856473847560fd1ea90a09bf32be6853e19986` | `8c91db65fe2c084cb7c57e628531b6cae27fbdfbe9b24bfa38beec92b15afd7c` (10) |
| `countAlg_split_of_source_needs_hb` | R2d counterexample | Quot.sound, propext | `6a15dfabaa3bc22d93f62ca93317eaf0da401e02eb01c987ac79e1e7c77dcf31` | `8c91db65fe2c084cb7c57e628531b6cae27fbdfbe9b24bfa38beec92b15afd7c` (10) |
| `countAlg_split_of_source_nonvacuous` | R2d witness | none | `3fee738720ce54cb4a9fa1e8ac1860c74a92cb7095d35beaaea403463346093f` | `d1b951d12a11e3bd2206b0a3b3fbfc562ec6e0bcfc8cd801a30afed4120b1308` (9) |
| `countAlg_total_splits_example` | R5b witness | none | `537327a635f57659e081d231aa8c491ef321e0beebe5ff1e999a4d306d3eb5a8` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countAlg_total_splits_into_source_and_readTokens` | R5b result | Classical.choice, Quot.sound, propext | `477d42c0fd855f999badcfd04c0af1c7a22d4f77dfe59344763b7ffd25a2eec7` | `f735fd75dfac8c7975f82388652605d37503e43d72b1d930ac33cfcfe8ac25c8` (14) |
| `countB0Embed_preservesOp_reflects_compat` | R4b counterexample, R4b positive control | Classical.choice, Quot.sound, propext | `6938ca58e259045be9437781d7c19d8554010f02bd5e7dbdda0d183e54f27157` | `45c835e56b1e562e131ef8f48e9b720d79762c7a6c6bd773b2736d153c31f3bf` (29) |
| `countB0Embed_sources_or_bundles_compat_fails` | R4b counterexample | Classical.choice, Quot.sound, propext | `9c2cd2c1e55b1b16e355770d57f5eddd10d2358091d99fa2e7f8e8b848ef7946` | `47aec512ea5d6c912735cf8eabe0f274c456644ec0232577a9e761f16bfc7ff4` (34) |
| `countB0_keep_either_pair_incompatible_fails` | R4b counterexample | Classical.choice, Quot.sound, propext | `e11bc1977f35add337f7677a6554030081225a9442d0db938a565f17c9d7e4ac` | `ca626c2350b3cc70f2ee01154a7d09116dda560d606beeff0d1cf3ade6b6a318` (36) |
| `countB1AllFull_reflects_compat` | R4b counterexample, R4b witness | Classical.choice, Quot.sound, propext | `9c98e25b3abf7026b5e1f376112f39594c0568b4e9b1fda9d8ecb781e515bee0` | `da3bb5512d4d97405381425e9ed485ccce8714050dc053af9436b00092e941d4` (23) |
| `countB1AllFull_sources_or_bundles_compat_fails` | R4b counterexample | Classical.choice, Quot.sound, propext | `7131f937466227a78cc4a023daf1e3e3032ae64533c119ad6ce568941e9b7f1b` | `ce7fb39a14a40e48e90c3fc702c4f3af82b423686160f5de564265238e3d221d` (31) |
| `countB1Embed_compat_not_reflected` | R4b witness | Classical.choice, Quot.sound, propext | `5418aff724b51de50e748c460e59d05ba28ee3b6a70bc815649930108950c002` | `0102837143a40b44917cba5062838bb873b8456c0553663811edeb8a6c9df645` (31) |
| `countB1Embed_injective_unit_op_iff` | R4a witness | Classical.choice, Quot.sound, propext | `585981e5b7dd0023959fe8fa578fd09bf1e9fddb9c5a06a3772882c0a392085f` | `63f2e81fe9561b5c8ea5607ec4c7a0fe2f2e5a514b7b22604efe2b1c9a745eb7` (37) |
| `countB1Embed_preservesOp` | R4b counterexample, R4b witness | Classical.choice, Quot.sound, propext | `6b761fbb61383e5ac2cec584601e901c99e4109141d5084d260a6d88107f4297` | `37e868b0d4945c95fb946b81317badc51663e7ab22404c8a25d42e89d0473d52` (23) |
| `countB1Embed_preservesOp_nonzero_token` | R4c positive control | Classical.choice, Quot.sound, propext | `8516949d532a2640658b30f516e82ed539a4b268c21399b382e460a564c2237b` | `9ceba62f3e1dfe6b9d423d206623200f0d0e6ae64ef5caeeb4a8059443836972` (31) |
| `countB1Lin_values` | R4b witness | Classical.choice, Quot.sound, propext | `4eef82b595c1c6ae4045bc9ca7b6060e31254c3771bf80fad835d533e97c8140` | `9c1ff7beecb8e5786c96a36c112bb8861fe1c5841ee7201e4492312f42f34257` (34) |
| `countBEmbed_injective_preserves_reflects_op_exclusive_readable` | R4a result | Classical.choice, Quot.sound, propext | `caa0df564464a230da3c9fc21ae4804c0cde42f24bbfcc0a5db3255fed0f716f` | `22ab0ac26921a0b2bc835de4a587cabb5424eed0ec0e0b72bf5e784433600d21` (35) |
| `countToFracSourcesOnly_preserves_unit_op_total` | R4c counterexample | Classical.choice, Quot.sound, propext | `c50f0de65d5c2beb51d4556d2dbc9163b8c5003b8ba2d6abf33aaaf7bf6e4e0e` | `809be50974882510f99abf2d9075421f7f10fe5c00db380c066992054d6e928c` (25) |
| `disjointness_violation_witness_nat` | R1b witness | Classical.choice, Quot.sound, propext | `d6d0984e1543a3235d7490d8ffa06eb6cc31a54070bda9add582459e80c786c9` | `0db7b90cf9dfc1fd277b3ab8fe937ad6ac8623cd635743c18677e4c55a8acbdd` (13) |
| `disjointness_violation_witnesses` | R1b witness | Classical.choice, Quot.sound, propext | `deba443536d61815467af519c6641b77e1840c03ce06b62bc01dc5ff688a571a` | `906de107f621281552223c8ce6af6c56a436a591484316da2a1407aa8b7181c7` (33) |
| `exclAgreeAlg_unit_token_does_not_restore` | R3e counterexample, R3e witness | propext | `2de8317890a0ab54edc7383eb838342eb7631e086025c18a7924e2aa9ebd447a` | `f18148f0f379bfb8d42b90dbae7ee15357b6da2c8fe7fe92bbe2b825bb577a65` (24) |
| `exclToCount_preservesOp_full_to_total` | R4d counterexample, R4d positive control | propext | `bc4f8ea249f735e7bc89125a1bb5e2157b512873a8170e1eda735554aad039f4` | `1474883bb6b4309ed513f2ecab7818b18ccdeeaee0f84449621444352caf3799` (12) |
| `fracAlg_countAlg_cellSumAlg_violate_disjointness` | R1b result | Classical.choice, Quot.sound, propext | `040fd67c6a3f8ea1b2ca47b1f120c7f8b0dbdc9ee68748da4bf8572ba9a3d4c3` | `6f9a9b61c6f1f657f749495e39b61945c5d7757ac7ef6f286c3de64b990f9bc8` (26) |
| `fracAlg_full_bounds_outstanding_pieces` | R5d counterexample | Classical.choice, Quot.sound, propext | `a6b96922f1abe2dd37e439514ad0ea6b43b70f2577a5c712ed90170e228ba0fc` | `f617cf0f801c019a45026d2ede04a52de34fbf2ea0f7babba09cfc6b6a4e8b81` (20) |
| `fracAlg_full_complement_piece_is_zero` | R5d counterexample | Classical.choice, Quot.sound, propext | `7595a8c52631e5f2a3362cb2d9de4c904a4641c26aa5f465c3568142ff520fb2` | `7ec3696f871580da3fa40ba2b6a7504dce1a7261335d853c979c77b572573512` (27) |
| `fracAlg_half_half` | R1a witness, R4d witness | Classical.choice, Quot.sound, propext | `20e6bc722c7bc97ffa238338f6cdd157192a9bc3cea1d3db428055a24166d5c4` | `4577b51e05c7110e734b37fee64958f63c7101be48207dc6d2316d78595a24ae` (17) |
| `fracAlg_half_not_exclusive` | R5d witness | Classical.choice, Quot.sound, propext | `bc0057ebf6c4338377cbac505c60c79b12b267010d84eb3f180b80e9459a9cb9` | `af867c8fcbeac191c661c06a5dadc812b39eda47c97ababf1491f9e59c036c4a` (20) |
| `fracAlg_halvingSplit_composes` | R2b result | Classical.choice, Quot.sound, propext | `ae44347565bb4933b03ab236244e02312dabdb74d61979c0af71727d9623c950` | `9074af6552bd377d1cfd525240ca29e29c9f15ab729bf5e899a99f55a5f82c06` (22) |
| `fracAlg_halvingSplit_composes_nonvacuous` | R2b witness | Classical.choice, Quot.sound, propext | `12267647355a68a5b435610a49b8ffd8c0175e7a56f3f6817130529e79bce30b` | `6b8dc6dbe9d1cbba0dd859c43ea0a73cb4be6afb38c238ca334145de6300b98c` (14) |
| `fracAlg_halvingSplit_full_recombines_to_exclusive` | R2b result | Classical.choice, Quot.sound, propext | `ad1f9a5bce4bc61413afef5b79765f30e95a15f927c6deb86f113baa56892709` | `886dbdcddd420bc1e30250720df07d92d4d85c99ab77ac342b125292168331a5` (26) |
| `fracAlg_halvingSplit_of_zero_has_empty_piece` | R2b counterexample | Classical.choice, Quot.sound, propext | `689b2bb697614c1c620490a32ccaf006aefa7237af75c77cadaec4c88d0d8829` | `9074af6552bd377d1cfd525240ca29e29c9f15ab729bf5e899a99f55a5f82c06` (22) |
| `fracAlg_halvingSplit_zero_pieces` | R2b counterexample | Classical.choice, Quot.sound, propext | `198cefbe6c158ac8b6fe77c8e9627695db4078b2b5fb91bf0390b91afad8cb7c` | `886dbdcddd420bc1e30250720df07d92d4d85c99ab77ac342b125292168331a5` (26) |
| `fracAlg_isPCM_cancel_positive` | R1a result | Classical.choice, Quot.sound, propext | `999df20520f449c44044111b72c43b4476e019c317abf392b4652144d890b14b` | `f60c275108a53f5e1a6eca718e35d0742c87d16607902a47b67715c05d81d86c` (19) |
| `fracAlg_no_nonexclusive_element_bounds_outstanding_pieces` | R5d result | Classical.choice, Quot.sound, propext | `052862f3223b134202eff038d8cdbf3ace49f063bc96c9db179c19a8c2b131d8` | `f617cf0f801c019a45026d2ede04a52de34fbf2ea0f7babba09cfc6b6a4e8b81` (20) |
| `fracAlg_nonzero_splits_into_two_nonzero_halves` | R2a result | Classical.choice, Quot.sound, propext | `b02be56cfc10994a8fb0110439376fc1022e1953105b2c0ecbb82d486c11f919` | `98aa752e1a21a21157ef6649d38b60aef20e2ca9dd04ff2229062507f1df8ee9` (15) |
| `fracAlg_nonzero_splits_needs_hq` | R2a counterexample | Classical.choice, Quot.sound, propext | `d7e54e0f5ddadf1abc0f425b2b8e3a9040a37fef6d94b9598f0aa587fa534b9c` | `98aa752e1a21a21157ef6649d38b60aef20e2ca9dd04ff2229062507f1df8ee9` (15) |
| `fracAlg_nonzero_splits_nonvacuous` | R2a witness | Classical.choice, Quot.sound, propext | `9472bb174224c66789c6a3e3309b8a279b7af2c900c7831a4231ffd37f79e6bb` | `8aba44641add0d3abe494f5105ea96bfd78fada3f9f994aa0b361b83f99faede` (7) |
| `fracAlg_owner_complement_splits_into_any_number` | R5d result | Classical.choice, Quot.sound, propext | `d5200a60405edb8641413813ab1da9e206166f8cc928f85abb696a94789e6653` | `7ec3696f871580da3fa40ba2b6a7504dce1a7261335d853c979c77b572573512` (27) |
| `fracAlg_owner_complement_splits_nonvacuous` | R5d witness | Classical.choice, Quot.sound, propext | `cdf93adda11223dde62e906a79c2015d69e2f49e4321d317350ad42a10c156a5` | `f296b992e7ce60fe16d61d11d66b88b89350765ea508d52f7d53fce2fe189607` (15) |
| `fracAlg_owner_complement_zero_pieces` | R5d counterexample | Classical.choice, Quot.sound, propext | `526604c17642e2c39650ff6fdc0f5cb1a3b0a7934860ba6c30d506497315c46f` | `7ec3696f871580da3fa40ba2b6a7504dce1a7261335d853c979c77b572573512` (27) |
| `halfGridAlg_half_half` | R4d witness | Quot.sound, propext | `5a322148d125585e46b799e2df02cb5192e0104b94af2d395a6bc254ab8d0ecd` | `8a4b338b9c8db7b7a8f664b577c9c52be29efb3e5d8ad2e3aecaf2aa16813967` (6) |
| `halfGridToCount_preservesOp_nonempty` | R4d counterexample, R4e positive control | Quot.sound, propext | `1a850a7814b1b54f05ce7967694b2481aebab068df8eaae5b4c4e65ff4f569cd` | `cd40234e103873bf34edff12a5028106ad85ac222f5595db0bd768d3940f13c1` (14) |
| `indicator_full_to_total` | R4d counterexample | Classical.choice, Quot.sound, propext | `219a28022342bfc4fa8f7162520f6ff5ea4200a80243ef9647bb13619158a44a` | `2326a9476391afaeca49cfa2b5c89aa359b663884c745afbd26c897ea358b317` (19) |
| `no_assoc_alg_returns_last_share_by_composition_beside_another_reader` | R3e result | propext | `d249bc495582bc10c57c9ff24e0e50b99da5059b17377393656baae7a48675bf` | `9bfbb8ce0adad563c5a552434ff322f6db80f6209212edfa9f7d702ae0d3c560` (8) |
| `no_assoc_alg_returns_last_share_hypotheses_satisfiable` | R3e witness | propext | `b025615c6e5a2c4d6aeef9bd76852ac5a6575457853fb2034ea2d1057cd17b2a` | `c0b1bda36c583bb857c4fce137122b7c99d8eeb4c42b22a8be3df935799710ba` (27) |
| `no_opPreserving_map_countB_to_frac_reflecting_compat` | R4b result | Classical.choice, Quot.sound, propext | `8892f860f305e6d2d94f08bea04812c788898a94f1ff23d8bf85896ebbadd20f` | `38b7820ea584f46dee879490bd8734b2058eb4fc947c0961fd322175d11a7e4f` (24) |
| `no_opPreserving_map_count_to_frac_with_nonzero_readToken` | R4c result | Classical.choice, Quot.sound, propext | `340321b5d0d6bb2d85fb27b4533da34818c2f4d3604b9463d82675ce42deb954` | `e2540ce91472d795563e26d72a4d28979fd128499217ddd19fbca37ef0d23463` (18) |
| `no_opPreserving_map_frac_to_count_sending_full_to_total` | R4d result | Classical.choice, Quot.sound, propext | `4a6287b6be44cc4c003bad6fb039b32d1d56d901493304850f1b5c6683304a80` | `37534572dc04b6c30b05e23deafb9bb721941ff6c3649ee94f9bcf69573e4ff2` (20) |
| `no_opPreserving_map_frac_to_count_with_nonempty_value` | R4e result | Classical.choice, Quot.sound, propext | `a643405d80cc7d53224c2ce33154a0d715403f284edb20e6fd686077f25956b0` | `ad9574770b9271be0659d1f34749c0ac6f6e03cc9e55976c9048b5605ba0d10b` (17) |
| `no_opPreserving_map_halfGrid_to_count_sending_full_to_total` | R4d result | Quot.sound, propext | `0fe0c4aa5e5ae58d43ee30976cec68a223a08a707567caee8909b5df831a519d` | `1d56ad6c1ecaacb604a1784902bb2657bd8e08c15ade9e6123189c08eb73b306` (12) |
| `no_opPreserving_map_to_count_sending_self_composite_to_total` | R4d result | Quot.sound, propext | `7b887c8be4230227cbfbe959b5d0ad4d74d67ff2ca92a50016a2820b46635d1d` | `642b9f1a14e50f66148eb19a5bec3887ee7c41e445d333529f4ec330c5cf5a46` (9) |
| `nonAssocDepthAlg_returns_last_share_beside_reader` | R3e counterexample, R3e witness | propext | `beed963de0c2c281ae153b7d9b655d229e80b0e1afefac56a7d16754009b5142` | `ba22bdc5910a3922a43cbe07af9b25dcf74169de5bd9bec59984e598ab360586` (31) |
| `opPreserving_map_countB_to_frac_sources_or_bundles_compat` | R4b result | Classical.choice, Quot.sound, propext | `a690e7b1d46aaa5d84e963996a0757f6fc32bd08908c565cab33ae2de2c9a2bd` | `d3e93ccfb41b7015c35ae368936aa90af4bc098a247efbb09fbe18aa3d057a52` (29) |
| `opPreserving_map_frac_to_count_eq_none` | R4e result | Classical.choice, Quot.sound, propext | `6c0828f0af75c3760b90eda04259e920f5e00a78d2282b6e21e5aa18ebcf55c2` | `ad9574770b9271be0659d1f34749c0ac6f6e03cc9e55976c9048b5605ba0d10b` (17) |
| `opPreserving_map_frac_to_count_exists` | R4e counterexample | Classical.choice, Quot.sound, propext | `d7dae9ea1b7b256ec36378c79b66b965aa8f594291618c6e403e44646ea09117` | `ad9574770b9271be0659d1f34749c0ac6f6e03cc9e55976c9048b5605ba0d10b` (17) |
| `opPreserving_maps_countB_to_frac_keep_either_pair_incompatible` | R4b result | Classical.choice, Quot.sound, propext | `f3b402d2035487ac2dba7640e7247193e6402b6756fa64e26b1a0a07aae29d1a` | `ca626c2350b3cc70f2ee01154a7d09116dda560d606beeff0d1cf3ade6b6a318` (36) |
| `reader_lastness_needs_ne_full` | R5e counterexample | Classical.choice, Quot.sound, propext | `ce4b50fab7b77ee9f09d2c89d3b2291d7be8de9ab07075847a64100d0402d00b` | `929316b9f6a5dda784eb288431e97d0e2ed5230c27b7ea081a43d6da0c77844f` (24) |
| `reader_lastness_nonvacuous` | R5e witness | Classical.choice, Quot.sound, propext | `cd776f13b76a452f7985004328550d3625790e11af2788bb2fdd6eb917d9da26` | `4a75c169b34650827fbbcf8e0aadd240c937e1e62648ce329f5ecce99888a40f` (27) |
| `reader_piece_does_not_determine_lastness` | R5e result | Classical.choice, Quot.sound, propext | `48c9efaac541eb2a0f3582c88124b1dc453ac5d65bffdab22604d5458f9081ad` | `42dd8cc2bdbc69098990a9aeec05356dfe4b9b3015d76d94a7f8c15955a9284f` (33) |
| `restoring_steps_not_framePreserving_nonvacuous` | R3d witness | propext | `a3b7ac97c0977f1416fd77defd636638ec1f01ba13f627880a310ef4f2a35c7e` | `585be3ddf4d7e31034149222219f31e5fbf30f964b6f2862909a784bce383f4b` (13) |
| `restoring_steps_not_framePreserving_of_sharing_exclusion_neutral` | R3d result | none | `21bbe468a2c49fe17da4fc059f5f4f5230b7a073552194ec5148a0b4ed58797b` | `92cfdde08133931ff3345df638989327cd3e124faf30259e27af0f8edabc2853` (8) |
| `singleHolderAlg_last_endShare_framePreserving` | R3d counterexample, R3d positive control | propext | `14f3c3de0c7f9bb3804d1265ff9785454daddd5b913b09dda24b6c7241d70ff3` | `e915eb4bc532e1cf146b5ccb05bdb48cc57683fb410f85a2450a79b184d53a88` (14) |
| `tokenReturnAlg_returns_last_share_without_second_reader` | R3e counterexample, R3e witness, R3e positive control | propext | `97a2e83e956352de8725f79ce33b0e0ab7431f34f5916b2e1d213d5c310b687a` | `8ea319fed5a272be2394e1d029bee04b80e5e3de8b700f6fc8a06a3e868ae3d9` (29) |
| `twoClassAlg_endBorrow_framePreserving` | R3d counterexample | propext | `495ac16b659e19a075eecd0ba457bfecaed45bda830bc07465e483fa3793543d` | `d2791629d67a88a13bc6791486f9ceac819efe86e74dd2b3a7b41578ac809f2a` (17) |

Names are relative to `Toy.Perm`. 109 names are hashed.

**Primary sources.** Full records of the prior art cited under **Findings**, with the results citing each. Bibliographic data of the two subject papers and of the Heule et al. abstract quote were re-checked on the observation date (Crossref records for DOIs 10.1007/978-3-642-10672-9_13, 10.1145/1040305.1040327 and 10.1007/978-3-642-35873-9_20; the publisher's abstract page for the quote). The Aeneas heap prototype is an open, unmerged pull request; its records pin the head commit and quote the relevant definitions, and it is context, not a subject.

- **[P1] Dockins, Hobor & Appel, APLAS 2009** (cited by R1a, R1b, R2a, R2b, R2c, R2d, R4a, R4b, R4c, R4d, R4e, R5a, R5d). Dockins, R., Hobor, A. & Appel, A. W., 'A Fresh Look at Separation Algebras and Share Accounting', APLAS 2009, LNCS 5904, pp. 161-177, doi:10.1007/978-3-642-10672-9_13. Axioms (5)-(9) include cancellation; positivity axiom (21); disjointness axiom (23) a + a = b -> a = b; infinite splittability (28)-(30). Definition 8: fractional shares on [0,1] intersected with Q with partial +, 'infinitely splittable', 'satisfies the positivity axiom but not the disjointness axiom'. Definition 9: counting shares on Z plus a unit, J(x, y, x + y) when (x < 0 or y < 0) and (x + y >= 0 or (x < 0 and y < 0)); 'Like the fractional model, the counting model satisfies positivity but not disjointness.'
- **[P2] Bornat, Calcagno, O'Hearn & Parkinson, POPL 2005** (cited by R1a, R2b, R2c, R2d, R3e, R4a, R4b, R4c, R4d, R4e, R5a, R5b, R5d, R5e). Bornat, R., Calcagno, C., O'Hearn, P. & Parkinson, M., 'Permission Accounting in Separation Logic', POPL 2005, pp. 259-270, doi:10.1145/1040305.1040327. Section 6: a central authority holds a source permission annotated with the number of split-off read permissions; 'the split-off read permissions can't be split further; only a source with no split-off children gives total read/write/dispose ownership'. Section 9: 'unbounded divisibility suits some problems; unbounded counting suits others'; fractions need not know how many times a permission will be split. Section 10.2: the counting model (Z, *1) with i *1 j undefined if i >= 0 and j >= 0, undefined if (i >= 0 or j >= 0) and i + j < 0, else i + j; write permission 0; equations (16). Section 10.3: fractions {q in Q | 0 < q <= 1}, undefined iff q + q' > 1. Section 8.1 ('A counting permission example'): in the readers-and-writers proof the readers' critical regions hold a resource whose invariant is 'if count = 0 then emp else' a source permission annotated with count; a returning reader gives its read permission back inside that critical region. Section 10.4 ('Combined Model'): the model (Q, *3) makes read permissions divisible ('By making read permissions divisible, it's possible to combine the properties of fractional and counting permissions'); equation (18) splits a read permission -(q+q') into -q and -q' for all q, q' > 0; 'it is impossible in the combined model to set up a logic in which read permissions cannot be split once issued'.
- **[P3] Boyland, SAS 2003** (cited by R1a). Boyland, J., 'Checking Interference with Fractional Permissions', Static Analysis (SAS 2003), LNCS 2694, pp. 55-72, doi:10.1007/3-540-44898-5_4 (bibliographic metadata verified via Crossref; the paper body was not inspected). As described by Bornat et al. (POPL 2005, Sections 5 and 7): a rational z per location, z = 1 exclusive ownership and total control, 0 < z < 1 shared read access. Dockins-Hobor-Appel (APLAS 2009, Section 6) instead state that Boyland works in the reals and that the rationals suffice; this disagreement is about the carrier only.
- **[P4] Iris 4.3.0, iris/algebra/frac.v and dfrac.v** (cited by R1a, R2a, R2b). Iris, commit 3d176f124f708e7325a362722c3d2b3957e3675d (tag iris-4.3.0), iris/algebra/frac.v: frac = Qp (positive rationals), valid iff q <= 1, op = +, instances frac_full_exclusive (Exclusive 1), frac_cancelable, frac_id_free, is_op_frac (q = q/2 + q/2). iris/algebra/dfrac.v: DfracOwn q | DfracDiscarded | DfracBoth q, DfracDiscarded . DfracDiscarded = DfracDiscarded (CoreId), only DfracOwn elements are Cancelable, dfrac_discard_update. Iris uses a total operation plus validity rather than a partial operation.
- **[P5] Calcagno, O'Hearn & Yang, LICS 2007** (cited by R1a). Calcagno, C., O'Hearn, P. W. & Yang, H., 'Local Action and Abstract Separation Logic', LICS 2007, pp. 366-378, doi:10.1109/LICS.2007.30 (bibliographic metadata verified via Crossref): abstract separation logic over separation algebras (cancellative partial commutative monoids), the basis of the Isabelle mechanization cited below.
- **[P6] iris-lean, Iris/Iris/Algebra/Frac.lean** (cited by R1a, R2a, R2b). iris-lean (leanprover-community/iris-lean), commit 5540ef0110fc8f6d8e495c10c2f238c3ede14f3b, Iris/Iris/Algebra/Frac.lean: a Lean 4 mechanization of the Iris fractional camera over core Lean Rat, 'abbrev Qp := { q : Rat // 0 < q }', with Qp.half_add_half (q.half + q.half = q), Qp.divide_even (q / n for n > 0), and instances instExclusiveQp1, instCancelableQp, instIdFreeQp. It builds on the iris-lean camera library, not on a partial operation.
- **[P7] VST, msl/sepalg.v and msl/tree_shares.v** (cited by R1a, R1b). VST (PrincetonUniversity/VST), commit d50ac1969f9f6586621895eb043ccf08a165f731, msl/sepalg.v (class Perm_alg with join_eq and join_positivity: join a a' b -> join b b' a -> a = b; classes Sep_alg and Disj_alg) and msl/tree_shares.v (the Coq development of Dockins-Hobor-Appel tree shares, including split lemmas such as split_disjoint and split_nontrivial).
- **[P8] fcsl-pcm, pcm/pcm.v** (cited by R1a). fcsl-pcm (imdea-software/fcsl-pcm), commit 07ca4992d53ab4a823bdd86a08d7252f32464f3b, pcm/pcm.v: partial commutative monoids in Coq presented as a total join with a validity predicate (pcm_axiom), with cancellative variants.
- **[P9] Klein, Kolanski & Boyton, Separation Algebra (AFP and ITP 2012)** (cited by R1a). Klein, G., Kolanski, R. & Boyton, A., 'Separation Algebra', Archive of Formal Proofs, May 2012, https://isa-afp.org/entries/Separation_Algebra.html (a generic Isabelle/HOL type-class implementation of separation algebra based on Calcagno et al.'s abstract separation logic), and 'Mechanised Separation Algebra', ITP 2012, LNCS 7406, pp. 332-337, doi:10.1007/978-3-642-32347-8_22 (metadata verified via Crossref).
- **[P10] Appel et al., Program Logics for Certified Compilers, 2014** (cited by R1a). Appel, A. W., Dockins, R., Hobor, A., Beringer, L., Dodds, J., Stewart, G., Blazy, S. & Leroy, X., 'Program Logics for Certified Compilers', Cambridge University Press, 2014, doi:10.1017/CBO9781107256552 (bibliographic metadata verified via Crossref; the book's treatment of separation algebras and shares was not re-inspected).
- **[P11] Further related work on share models (titles only)** (cited by R1a, R1b). Further related work on share models (bibliographic records verified; bodies not inspected, nothing beyond the titles is claimed): Boyland, J. T., 'Semantics of fractional permissions with nesting', ACM TOPLAS 32(6), 2010, pp. 1-33, doi:10.1145/1749608.1749611; Le, X.-B. & Hobor, A., 'Logical Reasoning for Disjoint Permissions', ESOP 2018, LNCS 10801, pp. 385-414, doi:10.1007/978-3-319-89884-1_14; Bierhoff, K. & Aldrich, J., 'Modular typestate checking of aliased objects', OOPSLA 2007, pp. 301-320, doi:10.1145/1297027.1297050; Parkinson, M. J., 'Local reasoning for Java', University of Cambridge Computer Laboratory Technical Report UCAM-CL-TR-654, 2005.
- **[P12] Heule, Leino, Müller & Summers, VMCAI 2013 (cited for a non-claim)** (cited by R1a). Heule, S., Leino, K. R. M., Mueller, P. & Summers, A. J., 'Abstract Read Permissions: Fractional Permissions without the Fractions', VMCAI 2013, LNCS 7737, pp. 315-334, doi:10.1007/978-3-642-35873-9_20 (bibliographic metadata verified via Crossref). From the abstract: specification using fractional permissions 'typically requires the user to pick concrete mathematical values for partial permissions'; abstract read permissions let the user 'work at the abstract level of read and write permissions' while supporting fractional permissions; implemented in Chalice. Only the abstract was inspected; cited for the non-claim that abstract read permissions are not covered.
- **[P13] Charguéraud & Pottier, ESOP 2017** (cited by R1a). Chargueraud, A. & Pottier, F., 'Temporary Read-Only Permissions for Separation Logic', ESOP 2017, LNCS 10201, pp. 260-286, doi:10.1007/978-3-662-54434-1_10 (bibliographic metadata verified via Crossref and dblp). From the abstract: an extension of Separation Logic 'with a general mechanism for temporarily converting any assertion (or "permission") to a read-only form. No accounting is required: our read-only permissions can be freely duplicated and discarded.' Only the abstract was inspected; cited for the non-claim that duplicable read-only permissions are not covered.
- **[P14] Aeneas heap prototype (unmerged pull request 1497): cells and compatibility** (cited by R3b, R3c, R3d, R3e, R3f, R3g). Aeneas pull request 1497 (AeneasVerif/aeneas, open and unmerged at observation; head commit d17ca83fc07d712d1785f650840cb2073c259e69; base de16f3cf877976e966906dc890f63dcb418884fa). backends/lean/Aeneas/Std/Heap/Repr.lean: Cell = shared (depth : Nat) (value : Byte) | borrowed; Cell.write and Cell.borrow require depth 0; Cell.share increments; Cell.endShare decrements a positive depth; Cell.endBorrow restores depth 0; Cell.compatible: borrowed is compatible with anything, two shared cells iff both depths are positive and the bytes are equal. Heap/README.md, section 'Permissions and overlapping views', lines 198-199: 'shared 0 is exclusive raw write permission. Positive sharing depths preserve read permission and record local outstanding shares; they are not fractions.' Heap/README.md, section 'Scope and checking', lines 417-418: 'Returning the final share to depth zero is deliberately not inferred from a positive-depth footprint: conflicting readers may still exist in other views.' Heap/Borrowing.lean, endShare.spec docstring (lines 51-52): 'Restoring depth zero is enabled only when physically conflicting observers have returned. A different view's positive shared contribution blocks this step.' Heap/Separation.lean: separation splits indexed per-view contributions; the heap invariant checks byte compatibility of overlapping views. An unmerged prototype: not a durable subject; the toy model restates the relevant design.
- **[P15] Aeneas heap prototype (unmerged pull request 1497): Cell.PermWeakens** (cited by R3b). Aeneas pull request 1497, head commit d17ca83fc07d712d1785f650840cb2073c259e69, backends/lean/Aeneas/Std/Heap/Lemmas.lean, lines 163-164: 'def Cell.PermWeakens (old new : Cell) : Prop := forall other, old.compatible other = true -> new.compatible other = true' (the same predicate as Cell.CompatFPU here), with lemmas Cell.PermWeakens.writer (shared 0 old to shared 0 new), Cell.PermWeakens.borrow (any cell to borrowed) and Cell.PermWeakens.share (shared d b to shared (d+1) b) at lines 175-191; Heap/Ranges.lean, endShareRange_cells.spec (lines 323-348) discharges the same weakening obligation for end-share from depth d+1 to d with 0 < d ('Decrements that retain positive sharing permission cannot introduce a writer. Returning the last shared permission instead requires continuation authority.'). These are the sufficient directions of Cell.compatFPU_iff; the converse direction and the resulting characterization are not stated there.
- **[P16] Iris 4.3.0, iris/algebra/updates.v; Jung et al., JFP 2018** (cited by R3b, R3d). Iris, commit 3d176f124f708e7325a362722c3d2b3957e3675d (tag iris-4.3.0), iris/algebra/updates.v: 'Definition cmra_update {A : cmra} (x y : A) := forall n mz, valid_n n (x op? mz) -> valid_n n (y op? mz)' (notation x ~~> y), and the set-valued cmra_updateP (x ~~>: P). Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L. & Dreyer, D., 'Iris from the ground up: A modular foundation for higher-order concurrent separation logic', Journal of Functional Programming 28, e20 (2018), doi:10.1017/S0956796818000151: the published account of Iris cameras (CMRAs), the fractional and authoritative cameras, and frame-preserving updates. With a present frame mz = Some f, cmra_update requires the single-frame condition used by PartialAlg.FramePreserving here.
- **[P17] Aeneas heap prototype (unmerged pull request 1497): raw restoration vs. scoped return authority** (cited by R3d, R3f). Aeneas pull request 1497, head commit d17ca83fc07d712d1785f650840cb2073c259e69, Heap/README.md, section 'Rust boundary, Boxes, and failure', lines 339-344: 'The low-level evaluator and the scoped proof interface have different roles. Raw restoration checks borrowed cells and heap compatibility, not a dynamic loan tree. It can restore a parent while a child view is itself borrowed. Scoped contracts instead require current-state return authority: the RootReturn rule excludes every other active view of that root, including suspended ones.'; section 'Assurance coverage', lines 50-55: a retained raw-operation trace 'prematurely restores a parent when a child is itself suspended', which 'is not a counterexample to the scoped callback contracts: the child remains an active view, so the parent's RootReturn authority is unavailable.'
- **[P18] Iris 4.3.0, iris/algebra/auth.v** (cited by R3d, R3e, R5d). Iris, commit 3d176f124f708e7325a362722c3d2b3957e3675d (tag iris-4.3.0), iris/algebra/auth.v: the authoritative camera; auth_both_valid a b : valid (auth a . frag b) <-> (forall n, b is n-included in a) /\ valid a, and for discrete cameras auth_both_valid_discrete : valid (auth a . frag b) <-> b included in a /\ valid a. This is the standard way to give one party knowledge of the composite of all outstanding pieces.
- **[P19] Aeneas heap prototype (unmerged pull request 1497): view-specific authorization** (cited by R3g). Aeneas pull request 1497, head commit d17ca83fc07d712d1785f650840cb2073c259e69, Heap/README.md, section 'Permissions and overlapping views', lines 217-219: 'Authorization remains selected-view-specific. Pooling just total depths would lose the distinction between A.borrowed/B.shared0 and A.shared0/B.borrowed.'; lines 228-230: 'Independent shared exposures retire their baseline contribution at depth one. They do not decrement it into a writer. Local nested shares decrement separately; exclusive access cannot resume until conflicting views retire.'; Heap/Model.lean, lines 361-363: Heap.endSharedExposure repr p count s = endExposureAt repr p count 1 s (retirement of a view at depth 1).
- **[P20] Heule, Leino, Müller & Summers, VMCAI 2013** (cited by R4c). Heule, S., Leino, K. R. M., Mueller, P. & Summers, A. J., 'Abstract Read Permissions: Fractional Permissions without the Fractions', VMCAI 2013, LNCS 7737, pp. 315-334, doi:10.1007/978-3-642-35873-9_20 (bibliographic metadata verified via Crossref). From the abstract: specification using fractional permissions 'typically requires the user to pick concrete mathematical values for partial permissions'; abstract read permissions let the user 'work at the abstract level of read and write permissions' while supporting fractional permissions; implemented in Chalice. Only the abstract was inspected.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations, runs Lean's `collectAxioms` on every declaration of the library, and, for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, recomputes the statement hash (SHA-256 of the Lean `repr` of the declaration's type) and the closure hash (SHA-256 of the newline-joined, sorted lines `name : repr(type)` plus ` := repr(value)` for non-theorems, over every package-local constant reachable from the statement through types, definition values and inductive constructors; theorem bodies are not hashed) and compares them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff every check passes. On the observation date its output was:

```text
ok   lake build
ok   axioms (541 declarations)
ok   statement hashes (109 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

A pass establishes that the recorded statements and their definition closures are unchanged and kernel-checked under the pinned toolchain with standard axioms; it does not re-establish the prior-art records or modeling bridges.

Narrower manual checks, from `lean/`:

```sh
lake build                      # builds library ToyPerm; must report no errors and no 'sorry' warnings
lake env lean AxiomAudit.lean   # prints '#print axioms' for every result theorem
```

`lean/AxiomAudit.lean` is outside the library target; for every result theorem its output must read `'<name>' depends on axioms: [...]` listing a subset of `propext`, `Classical.choice`, `Quot.sound`, or `'<name>' does not depend on any axioms`. To recheck a single statement hash by hand, save the following as `/tmp/HashOne.lean` (replace the name as needed):

```lean
import Lean
import ToyPerm
open Lean Elab Command in
#eval show CommandElabM Unit from do
  IO.println (toString (repr (← getConstInfo `Toy.Perm.fracAlg_isPCM_cancel_positive).type))
```

then, from `lean/` after `lake build`, run
```sh
lake env lean /tmp/HashOne.lean | python3 -c "import hashlib,sys; print(hashlib.sha256(sys.stdin.read().rstrip('\n').encode()).hexdigest())"
```

and compare the printed digest with `statement_sha256` in `audit/statements.json` (for `Toy.Perm.fracAlg_isPCM_cancel_positive` it is `999df20520f449c44044111b72c43b4476e019c317abf392b4652144d890b14b`).

If a result's statement or any definition in its closure changes, its recorded hashes change, and its plain claim, hypothesis ledger and non-claims must be checked again against the new statement; if only proofs change, the hashes are unchanged and rerunning the build and axiom audit suffices.
