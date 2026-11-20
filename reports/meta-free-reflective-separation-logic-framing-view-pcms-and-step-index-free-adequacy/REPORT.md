# Meta-Free Reflective Separation Logic, Framing, View-Indexed PCMs, and Step-Index-Free Adequacy in Lean 4 and Rocq

## Summary

First-order, step-index-free separation logic architectures in Lean 4 and Rocq achieve modular heap framing, aliasing-safe resource splitting, and closed-program adequacy without OFE/COFE step indexing, higher-order impredicative invariants, or metaprogramming tactics. Across `JoJoDeveloping/tiny-iris@5b18c311`, `AeneasVerif/aeneas` PRs `#1551` (`1d8f9aa0`), `#1497` (`d17ca83f`), and `#1180` (`39075a19`), and `joshlf/anneal@20aa2043`, four structural design patterns emerge and compose directly under strict `Init.*`-only kernel syntax allowlists:

1. **Upward-closed affine `IProp` over `PartialCommMonoid`:** Modeling assertions as predicates upward-closed under heap extension (`Subheap h h' → holds h → holds h'` in Aeneas PR `#1551` `PCM.lean`/`IProp.lean`; `σ₁ ⊆ σ₂ → holds σ₁ → holds σ₂` in `tiny-iris` `heapprop.v`) gives affine weakening (`P ∗ Q ⊢ P`) by construction, sets `later := id`, and requires zero `Classical.choice`, `grind`, or `omega` in the core logic—unlike non-affine ordered list heaplets (`SpatialProp` in `joshlf/anneal@20aa2043` `SpatialPin.lean`).
2. **View-indexed `Resource` PCMs with `Nat` sharing depth:** Separating logical resource compatibility by view ID (`a.base ≠ b.base ∨ a.key ≠ b.key` in PR `#1551` `Resource.lean`) while checking physical aliasing globally via `Heap.Inv` (`Resource.Holds.overlapCompatible`), paired with `Cell := shared (depth : Nat) Byte | borrowed` (`Repr.lean`), eliminates rational/tree fractional share arithmetic (`Qp`, VST `shares.v`) at the cost of requiring explicit view identity at return time.
3. **Pure reflective AC + frame-cancellation kernels (`SepAC.Tree`):** Separating a 46-line pure reflective core (`SepAC.Tree`, `Tree.denote_eq` proved by `List.isPerm` + `rfl` in PR `#1551` `Normalize.lean:18–64`) from `MetaM` front-ends (`IFrame.lean`, CFML `xsimpl`, MoSeL/IPM, RefinedC Lithium) allows full AC reordering, residual frame computation (`bagSub`), and affine dropping (`bagSubset`) via single-step `rfl` reduction inside `TrustedBoundary.lean`'s `Init.*`-only allowlist.
4. **Frame-quantified `wp` adequacy over fuel-bounded semantics:** Baking `∀ F s, Realizes (owns owned ∗ F) s → ...` into `iwp` (PR `#1551` `WPDef.lean`) or `wpbigstep` (`tiny-iris` `adequacy.v`) reduces closed adequacy to instantiating `F := emp` (`σ₂ := ∅`). Wrapping structural `@Nat.rec` `MirWp.wpOutcomeState` (`MirWp.lean:69–80`) in frame-quantified `sepWpState` avoids `CoInd`/`partial_fixpoint` (`#1180`) while discharging `WpSoundnessClaim` cleanly inside `Init.*` Lean.

*(Scope boundary: Higher-order concurrent Iris adequacy, transfinite ordinal step indexing, OFE/CMRA constructions, `iris-lean` `UPred`, and Simuliris refinement are documented in `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`; two-zone borrow/heap adapters and finite-heap checkers appear in `hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4`. Byte layouts and stateful backward continuations are covered in `minirust-galois-byte-layouts-stateful-lifetime-continuations-and-unsafe-raw-pointer-interop`.)*

---

## Applicability

These findings apply to the pinned revisions and literature baselines below:

| Subject / System | Pinned Identity / Citation | Inspected Scope |
|---|---|---|
| **`JoJoDeveloping/tiny-iris`** | `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9` | Rocq `theories/{heapprop,weakestpre,adequacy}.v`: `heapProp`, `later := id`, least-fixpoint `wp`, `wpbigstep` |
| **Aeneas PR `#1551`** | `AeneasVerif/aeneas` `cezar/seplogic` @ `1d8f9aa0121faca8ff113c1b9b742b333e3e1519` (base `768a0ce985c72206a9eb482b7376b0d7f19dcda2`) | `SepLogic/{PCM,IProp,Resource,Local,Specs,Borrowing,Bytes}.lean`, `Tactic/{Normalize,IFrame}.lean`, `Std/WPDef.lean`, `ITreeWP/{DWP,DWLP,Taxonomy}.lean` |
| **Aeneas PR `#1497`** | `AeneasVerif/aeneas` `fournet/wip-memory-model` @ `d17ca83fc07d712d1785f650840cb2073c259e69` (base `de16f3cf877976e966906dc890f63dcb418884fa`) | `Aeneas/Std/Heap/{Repr,Model,ExclusiveReturn}.lean`: `Cell.shared depth | borrowed`, `Heap.Inv`, `overlapCompatible` |
| **Aeneas PR `#1180`** | `AeneasVerif/aeneas` `jacob/itree-separation-logic` @ `39075a19f64c51699ec3ddde286171fb347261c8` (merge `df7059b918e91cd1ac37c6814f642a935948025e`) | `Aeneas/Data/Coinductive/{Effect,ITree}.lean`: `CoInd`, `ITreeF`, `partial_fixpoint` `ITree.bind` |
| **`joshlf/anneal`** | `20aa204315cd36aaf944778b7d33c0d609ced8e8` | `trusted/audit/TrustedBoundary.lean`, `Trusted/MirSemantics.lean`, `theory/Anneal/MirWp.lean`, `theory/Anneal/PureLift/SpatialPin.lean` |
| **Lean `v4.34.1` & `iris-lean`** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52`; `leanprover-community/iris-lean` @ `5540ef0110fc8f6d8e495c10c2f238c3ede14f3b` | `Init.*` kernel allowlist target and higher-order `UPred`/MoSeL contrast baseline |
| **Literature Baselines** | CFML (`10.1145/3408998`), MoSeL (`10.1145/3236772`), RefinedC (`10.1145/3453483.3454036`), ITrees (`10.1145/3371119`) | Normative comparison for framing tactics (`xsimpl`, IPM, Lithium) and ITree WP semantics |

**Cross-package division:** Step-indexed/transfinite Iris and `iris-lean` belong to `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`. Byte-level `AbstractByte` Galois laws, `zerocopy` trait rules, `stateful_lifetime`, and `ClosedViews` belong to `minirust-galois-byte-layouts-stateful-lifetime-continuations-and-unsafe-raw-pointer-interop`.

---

## Findings

### 1. Upward-Closed Affine `IProp` Over `PartialCommMonoid`

**Basis: source (`JoJoDeveloping/tiny-iris@5b18c311` `theories/heapprop.v`, `AeneasVerif/aeneas#1551@1d8f9aa0` `Aeneas/SepLogic/{PCM,IProp}.lean`, `joshlf/anneal@20aa2043` `SpatialPin.lean`) + derived.**

#### 1.1 Algebraic Pattern Shared by `tiny-iris` and Aeneas PR `#1551`

Both `tiny-iris` and Aeneas PR `#1551` avoid step-indexed `UPred`s and general CMRAs by defining assertions as **upward-closed predicates over a partial commutative monoid**:

- **`tiny-iris@5b18c311` (`theories/heapprop.v:7–10, 19, 107–117, 210–244`):** `heapProp` pairs `heapProp_holds : gmap loc val → Prop` with monotonicity under finite-map inclusion (`σ₁ ⊆ σ₂ → holds σ₁ → holds σ₂`). It instantiates Iris's `BiMixin`, `BiPersistentlyMixin`, and `BiLaterMixin` with discrete equality (`discreteO heapProp`), identity later (`heapProp_later P := P`), empty-heap persistence (`heapProp_persistently P := heapProp_pure (emp ⊢ P)`), the existential property via minimal unit `∅` (`heapprop.v:216–221`), and `BiAffine heapPropI` (`heapprop.v:242–243`).
- **Aeneas PR `#1551@1d8f9aa0` (`PCM.lean:13–145`, `IProp.lean:17–114`):** `PartialCommMonoid α` is a minimal 8-field typeclass (`Compatible`, `compatible_comm`, `compatible_empty_left`, `compatible_assoc`, `union_assoc`, `empty_union`, `union_empty`, `union_comm_of_compatible`). Its preorder `Subheap h h' := ∃ rest, Compatible h rest ∧ h' = h ∪ rest` (`PCM.lean:33–34`) proves `Subheap.refl`, `Subheap.trans`, `Subheap.union_left`, `Subheap.split` (`Subheap (h₁ ∪ h₂) h' → ∃ h₂', Compatible h₁ h₂' ∧ h' = h₁ ∪ h₂' ∧ Subheap h₂ h₂'`, `lines 74–86`), `Subheap.compatible`, and `Subheap.union_mono`. `IProp` mirrors `heapProp`:
  ```lean
  -- AeneasVerif/aeneas#1551: Aeneas/SepLogic/IProp.lean:17-19
  structure IProp where
    holds : Fragment → Prop
    up_closed : ∀ {h h' : Fragment}, holds h → PartialCommMonoid.Subheap h h' → holds h'
  ```
  `IProp.lean:40–113` defines `emp` (`fun _ => True`), `ipure`, `owns A` (`Subheap A h`), `iand`, `sep`, `iexists`, `iforall`, `wand`, `postSep`, `postWand`, and `upClose`. Upward closure of `sep` (`lines 74–77`) relies strictly on `Subheap.split`, and upward closure of `wand` (`lines 98–103`) relies on `Subheap.compatible` and `Subheap.union_mono_left`.

#### 1.2 Axiom Footprint and Comparison with Non-Affine `SpatialProp`

1. **Minimal axiom and tactic footprint:** Direct inspection of `PCM.lean`, `IProp.lean`, `Local.lean`, `Borrowing.lean`, and `Specs.lean` in PR `#1551` shows zero occurrences of `grind`, `omega`, `Classical.choice`, or `sorry`. Extensionality (`IProp.ext`, `IProp.lean:25–30`; `Fragment.eq_of_union_eq`, `PCM.lean:173–185`) uses only `propext` and `funext` (`Quot.sound`).
2. **Affinity avoids manual list-split rewrites:** In `joshlf/anneal@20aa2043` (`theory/Anneal/PureLift/SpatialPin.lean:63–90`), `SpatialProp Val := List (SpatialBlock Val) → Prop` defines non-affine `spatialSepConj P Q` via ordered list append (`blocks = h1 ++ h2 ∧ blocksDisjoint h1 h2 ∧ P h1 ∧ Q h2`). Framing two or more blocks forces manual `List.append` permutation/associativity proofs, and unused spatial blocks cannot be dropped. An upward-closed `IProp` over `PartialCommMonoid` makes `P ∗ Q ⊢ P` and commutativity/associativity structural properties of the assertion lattice.
3. **Map-difference elimination in `Init.*`:** `tiny-iris` proves `Subheap.split` for `sep` using `stdpp` finite-map difference `σ₂ ∖ σ₁₁` (`heapprop.v:82–89`). PR `#1551` (`PCM.lean:74–86`) derives `Subheap.split` purely from `compatible_assoc` and `union_assoc`, needing no `Std.HashMap` or map-difference primitive inside `Init.*`-only Lean.

---

### 2. View-Indexed `Resource` Splitting vs. Fractional Permissions

**Basis: source (`AeneasVerif/aeneas#1551@1d8f9aa0` `Resource.lean`, `Bytes.lean`; `AeneasVerif/aeneas#1497@d17ca83f` `Heap/{Repr,Model}.lean`) + derived.**

#### 2.1 Logical Separation of View IDs vs. Physical Compatibility (`Heap.Inv`)

Rather than forbidding physical address overlap inside `Compatible`, Aeneas PR `#1551` (`Resource.lean:19–100`) and PR `#1497` (`Model.lean:18–109`) separate **logical view-contribution disjointness** from **physical heap consistency**:

```lean
-- AeneasVerif/aeneas#1551: Aeneas/SepLogic/Resource.lean:19-41, 102
inductive Resource where
  | cell (base : Nat) (index : Nat) (bptr : BasePtr) (value : Cell)
  | cleanup (base : Nat) (size : Nat) (bptr : BasePtr) (owned : Bool)

def Resource.Compatible (a b : Resource) : Prop :=
  a.base ≠ b.base ∨ a.key ≠ b.key  -- key is `some index` for cell, `none` for cleanup

abbrev Fragment := Resource → Prop
```

Here `base` is a ghost **view ID** (`p.provenance`), not a physical address. Because `¬ a.Compatible a` (`not_compatible_self`, `Resource.lean:39–40`), `Fragment` forms a cancellative PCM (`Fragment.eq_of_union_eq`, `PCM.lean:173–184`). Two distinct views `i ≠ j` at the **same physical byte address** (`a.val + x = b.val + y`) are logically disjoint (`disjoint_views`, `Bytes.lean:163–167`). Physical safety is enforced globally by `Heap.Inv` (`Model.lean:86–109`), whose `Heap.compatible` predicate checks `Cell.compatible x y = true` whenever two active blocks coincide at a physical byte address. `Resource.Holds.overlapCompatible` (`Resource.lean:58–81`) connects both layers: any two `Resource.Holds`-satisfied cells in distinct views `i ≠ j` at identical addresses automatically satisfy `Cell.compatible c d = true`.

#### 2.2 Sharing Depth (`Cell.shared depth | borrowed`) vs. Fractional Shares

In `Aeneas/Std/Heap/Repr.lean:50–93` (PR `#1497`), each byte cell replaces rational/tree shares with a `Nat` reference-count depth:

```lean
-- AeneasVerif/aeneas#1497: Aeneas/Std/Heap/Repr.lean:50-93
inductive Cell where
  | shared (depth : Nat) (value : Byte)
  | borrowed

def Cell.compatible : Cell → Cell → Bool
  | .borrowed, _ | _, .borrowed => true
  | .shared n x, .shared m y => n > 0 && m > 0 && decide (x = y)
```

| Dimension | `Nat` Sharing Depth + View ID (`#1497` / `#1551`) | Rational / Tree Fractional Shares (`Iris Qp`, `VST shares.v`) |
|---|---|---|
| **Exclusive write** | `.shared 0 byte` (`0 > 0` is `False`, blocking any concurrent `.shared m _` view) | Full share `1` (or `⊤` tree share) |
| **Shared read** | `.shared (depth + 1) byte` (`Cell.share` increments; `Cell.endShare` decrements `depth + 1 → depth`) | Arbitrary positive split `q = q₁ + q₂` (`0 < qᵢ`) |
| **Loaned out** | `.borrowed` (`Cell.compatible .borrowed _ = true`; carries no raw permission until ended) | Separate lifetime/borrow tokens or prophecy cells |
| **Alias agreement** | `Cell.compatible` requires `n > 0 ∧ m > 0 ∧ x = y` (exact symbolic `Byte` match, including `.uninit`) | Fractional points-to splitting `l ↦{q₁+q₂} v ⊣⊢ l ↦{q₁} v ∗ l ↦{q₂} v` |
| **Algebraic cost in `Init.*`** | Structural `Nat` + `Bool`; zero rationals, GCDs, or positivity proofs | Requires `Rat`/`Pos` arithmetic or binary tree-share join laws |
| **Expressiveness limit** | Non-fungible: retiring shares requires matching view IDs (`endSharedExposure` at `Model.lean:348–364`), unsuitable for anonymous thread-pool splits without IDs | Completely fungible: any `q₁ + q₂ = 1` recombines independent of origin history |

**Finiteness observation (`PR #1497` `Model.lean:26–29, 107–108`):** `Heap` uses a total map `allocations : Nat → Option Block` plus `next : Nat` and external `Inv` invariant `∀ id, s.next ≤ id → s.allocations id = none`. Storing finite fragments via a `Nodup` association list (`List (Nat × Block)`) or `gmap` makes finiteness and fresh-ID availability intrinsic without threading `base < next` invariants through every lemma.

---

### 3. Reflective `SepAC` / `SepCancel` Proof Kernels vs. Macro/Meta Tactics

**Basis: source (`AeneasVerif/aeneas#1551@1d8f9aa0` `Aeneas/SepLogic/Tactic/{Normalize,IFrame}.lean`, `joshlf/anneal@20aa2043` `trusted/audit/TrustedBoundary.lean`) + derived.**

#### 3.1 `TrustedBoundary.lean` Closed Allowlist Constraints

In `joshlf/anneal@20aa2043` (`trusted/audit/TrustedBoundary.lean:442–596`), untrusted theory modules (`SourceRole.theory`) compile against `Init.*` (`foundation-lock.json`) and pass syntactic AST preflight checks:

- **Excluded constructs:** `allowedHeaderKinds` excludes `module`, `public`, `meta`, `all` (`lines 440–443`); `allowedCommandKinds` excludes `macro`, `syntax`, `elab`, `notation`, `infix`, `initialize`, `set_option`, `#eval` (`lines 445–453`); `allowedDeclarationKinds` excludes `axiom`, `coinductive` (`lines 455–462`); `allowedCommandSyntaxKinds` excludes `unsafe`, `partial`, `meta`, `terminationBy`, `decreasingBy`, `partialFixpoint` (`lines 464–468`); and `allowedTheoryTacticKinds` excludes `grind`, `omega`, `native_decide`, `bv_decide`, `rfl'`, `sorry`, `run_tac` (`lines 529–557`).
- **Crucial admitted primitives:** `allowedTheoryTacticKinds` explicitly admits **`Lean.Parser.Tactic.decide` (`decide`) and `Lean.Parser.Tactic.tacticRfl` (`rfl`)** alongside `apply`, `cases`, `change`, `constructor`, `dsimp`, `exact`, `induction`, `intro`, `refine`, `rw`, `simp`, `subst`, and `funext`.

Thus, metaprogrammed tactics (`public meta section` in Aeneas `IFrame.lean`, MoSeL/IPM `iIntros`/`iFrame` in `iris-lean`, CFML `xsimpl`, and RefinedC Lithium) fail syntactic admission under `Init.*`-only allowlists unless replaced by pure reflective checkers discharged via `rfl` or `decide`.

#### 3.2 Separating Pure `SepAC.Tree` From `MetaM` (`Aeneas#1551` `Normalize.lean`)

Aeneas PR `#1551` already demonstrates this separation in `Aeneas/SepLogic/Tactic/Normalize.lean`:

- **Pure kernel (`Normalize.lean:18–64`, zero `Lean.*` dependencies):**
  ```lean
  inductive Tree where | atom (i : Nat) | unit | node (l r : Tree)
  def Tree.denote (env : List IProp) : Tree → IProp
    | .atom i => env.getD i emp
    | .unit => emp
    | .node l r => l.denote env ∗ r.denote env
  def Tree.atoms : Tree → List Nat
    | .atom i => [i] | .unit => [] | .node l r => l.atoms ++ r.atoms
  theorem Tree.denote_eq (env : List IProp) (l r : Tree)
      (h : l.atoms.isPerm r.atoms = true) : l.denote env = r.denote env
  ```
  Proving AC equivalence of any two `∗` trees collapses to `Tree.denote_eq env l r rfl` via boolean `List.isPerm` evaluation inside the Lean kernel (`Normalize.lean:59–62`).
- **`MetaM` front-end (`Normalize.lean:70–381`, `IFrame.lean:14–301`):** `reifySep`, `proveEqAC`, `pullLeft`, `instantiateRightExists`, `frameByMatching`, and `provePure` (invoking `grind`) automate syntactic reification, existential metavariables, and pure residues, constructing `env`, `l`, `r` to invoke `Tree.denote_eq`.

#### 3.3 Meta-Free `SepCancel` Extension for Framing and Affine Dropping

Extending `SepAC.Tree` inside `Init.*`-only Lean removes the `MetaM` dependency completely for bounded spatial goals:

```lean
-- Derived Init.* extension of SepAC.Tree (zero Lean.* / macro / grind)
def removeFirst (x : Nat) : List Nat → Option (List Nat)
  | [] => none
  | y :: ys => if x == y then some ys else (removeFirst x ys).map (y :: ·)

def bagSub (src : List Nat) : List Nat → Option (List Nat)
  | [] => some src
  | r :: rs => match removeFirst r src with | none => none | some src' => bagSub src' rs

def bagSubset (req src : List Nat) : Bool := (bagSub src req).isSome
```

Using `denoteList (env : List IProp) (xs : List Nat) : IProp := xs.foldr (fun i acc => sep (env.getD i emp) acc) emp`, three structural lemmas hold by induction and `foldr_sep_perm` (`Normalize.lean:41–49`):
1. **`denote_ac_eq`**: `(l.atoms.isPerm r.atoms = true) → l.denote env = r.denote env` (`rfl`).
2. **`denote_frame_split`**: `bagSub src.atoms req.atoms = some rem → Entails (src.denote env) (sep (req.denote env) (denoteList env rem))` — computes the exact residual frame `rem` and discharges framing via `rfl`.
3. **`denote_affine_cancel`**: `bagSubset dst.atoms src.atoms = true → Entails (src.denote env) (dst.denote env)` — cancels matched atoms and affine-drops unused atoms from `IProp` (`sep P Q ⊢ P` via `Subheap.union_left`) in a single `rfl` application.

#### 3.4 Framing Automation Trade-Off Matrix

| Framework / Mechanism | Core Technique | `Init.*` Allowlist Status | Existentials & Evars | Primary Failure Mode |
|---|---|---|---|---|
| **Pure Reflective `SepAC` + `SepCancel`** (`#1551` kernel + `bagSub`) | Kernel `Tree` + `List.isPerm`/`bagSub` checked by `rfl` | **Admitted** (`Init.*` only; 0 `Lean.*`, 0 `grind`) | Explicit witness instantiation (`iexists_intro`) | Index-level atom identity only; arithmetic key differences (`p + (1 + 1)` vs. `p + 2`) require explicit `rw` |
| **Aeneas `iframe`** (`#1551` `IFrame.lean`, `public meta`) | `MetaM` `reifySep` + backtracking `matchAll` + `Tree.denote_eq` + `grind` | **Rejected** (`public meta`, `Lean.*`, `grind`, `Std.HashMap`) | `pullLeft` + evars + `solveWitnessEqs` | Backtracking on duplicate heads without pure witness equations |
| **CFML `xsimpl`** (`10.1145/3408998`) | Rocq Ltac + reflection/rewrite loops | N/A (Rocq Ltac) | Automatic evar instantiation + `xchange` | Opacity leaks or Ltac backtracking on folded predicates |
| **Iris / MoSeL IPM** (`10.1145/3236772`, `iris-lean`) | Typeclass search (`IntoSep`/`FromSep`, `iFrame`) | **Rejected** (`elab`, `macro`, `notation`, `Std.*`) | Named context + `iExists` | Typeclass search latency on large unordered contexts |
| **RefinedC / RefinedRust Lithium** (`10.1145/3453483.3454036`) | Zero-backtracking goal-directed `liRStep` search | N/A (Rocq typeclasses + Ltac) | Mode-directed (`FindDirect`) output witnesses | Brittle outside the deterministic fragment; strict hint-ordering dependency |

---

### 4. Step-Index-Free Frame-Quantified `wp` Adequacy vs. Coinductive ITrees

**Basis: source (`JoJoDeveloping/tiny-iris@5b18c311` `weakestpre.v` & `adequacy.v`; `AeneasVerif/aeneas#1180@39075a19` `ITree.lean`; `AeneasVerif/aeneas#1551@1d8f9aa0` `ITreeWP/{DWP,DWLP,Taxonomy}.lean`, `Local.lean`, `WPDef.lean`; `joshlf/anneal@20aa2043` `MirSemantics.lean`, `MirWp.lean`) + derived.**

#### 4.1 Baked-In Frame Quantification (`tiny-iris` `wpbigstep` and Aeneas `#1551` `iwp`)

Both `tiny-iris` and Aeneas PR `#1551` bake universal frame quantification into the weakest precondition definition itself:

- **`tiny-iris` (`weakestpre.v:19–27`, `adequacy.v:9–54`):** Total-correctness `wp` is `bi_least_fixpoint (wpre Q)` over `heapProp`. `adequacy.v:9–10` defines `wpbigstep e Q` directly over heap inclusion and disjoint union:
  ```coq
  Program Definition wpbigstep (e : expr) (Q : val → heapProp) : heapProp :=
    {| heapProp_holds σ := ∀ σ2, σ ##ₘ σ2 →
         ∃ v' σ', σ' ##ₘ σ2 ∧ ctx_steps e (σ ∪ σ2) (of_val v') (σ' ∪ σ2) ∧ Q v' σ' |}.
  ```
  `wp_tobigstep : wp e Q ⊢ wpbigstep e Q` follows by `wp_iter` (`adequacy.v:24–35`), and closed adequacy `wp_soundness` (`lines 38–46`) instantiates `σ₂ := ∅` to yield `∃ v σ', ctx_steps e σ (of_val v) σ' ∧ Q v`.
- **Aeneas PR `#1180` (`ITree.lean:15–166`) + PR `#1551` (`WPDef.lean:35–99`, `DWP.lean:33`, `DWLP.lean:33`):** PR `#1180` encodes effectful trees `ITree E R := CoInd (ITreeF E R)` (`.ret`, `.div`, `.vis`) with `ITree.bind` defined via Lean 4 `partial_fixpoint`. PR `#1551` defines total `DWP` (`OrderHom.lfp`, rejecting `.div`) and partial `DWLP` (`OrderHom.gfp`, accepting `.div`, `Taxonomy.lean:17–49`), wraps `RustEffect` in `effectWP` (accepting `.fail .oom`, rejecting panic/UB, `WPDef.lean:35–41`), defines `Realizes H s := s.Inv ∧ ∃ h, H h ∧ Fragment.Matches s h ∧ AuthOK s h` (`lines 63–64`), and defines `iwp` (`lines 76–82`):
  ```lean
  -- AeneasVerif/aeneas#1551: Aeneas/Std/WPDef.lean:76-78
  def iwp (total : Bool) (m : Result α) (Q : IPost α) : IProp where
    holds owned := ∀ F s, Realizes (owns owned ∗ F) s → rawIwp total m (Q ∗+ F) s
  ```
  Pure Aeneas specs unify cleanly as `spec m p := ispec emp m (fun v => ⌜p v⌝)` (`WPDef.lean:93–94`). Separately, `Local.lean:81–96` distinguishes global `LocalOp P c Q` (all valid heaps `s`) from input-state-dependent `LocalAt P c Q s` (needed when concrete pointer placement or return authority `AuthOK` depends on `s`, as in `endBorrow.spec` at `Borrowing.lean:74–103`).

#### 4.2 Frame-Quantified Fuel-Bounded `sepWpState` Over `MirWp.wpOutcomeState`

Because `CoInd` and `partial_fixpoint` violate `TrustedBoundary.lean:464–468`, `joshlf/anneal@20aa2043` (`MirWp.lean:69–107`) uses structural **`@Nat.rec`** fuel over `Trusted.MirSemantics.evalStep` to define `wpOutcomeState` and prove `wellFormed_and_spec_of_wp : WpSoundnessClaim wpProg` (`MirWp.lean:429–477`; `MirSemantics.lean:1831–1837`). Lifting frame quantification over `MirWp.wpState` yields an `Init.*`-compliant separation-logic WP:

```lean
-- Derived Init.* formulation over Trusted.MirSemantics and Anneal.MirWp
def sepWpState (p : Program) (fuel : Nat) (P : IProp) (Q : TerminalOut → IProp)
    (Realizes : IProp → State → Prop) : Prop :=
  ∀ (F : IProp) (s : State),
    Realizes (sep P F) s →
    MirWp.wpState p fuel s (fun out => Realizes (sep (Q out) F) (finalStateOf out))
```

- **Framing (`sepWp_frame`):** Instantiating `F := sep R F'` and rewriting with `sep_assoc` and `Realizes.mono` yields `sepWpState p fuel (sep P R) (fun out => sep (Q out) R)` directly (analogous to `LocalOp.frame`, `Local.lean:116–129`).
- **Fuel composition (`sepWp_bind`):** Sequential segments with fuel budgets `fuel₁` and `fuel₂` compose via `wpOutcomeState_fuel_mono` (`MirWp.lean:280–313`) under total fuel `fuel₁ + fuel₂`.
- **Direct adequacy (`sepWp_adequate`):** Instantiating `F := emp` reduces `sepWpState` to `MirWp.wpProg`, immediately discharging `WpSoundnessClaim` (`SatisfiesPost ∧ ¬ Diverges ∧ ∃ out, Behavior ∧ post out`) with zero coinduction, zero `partial_fixpoint`, and zero step indices.
- **Divergence boundary:** Whereas `DWLP` handles `.div` via `OrderHom.gfp`, fuel-bounded `wpOutcomeState` forbids infinite traces (`not_diverges_of_wpProg`, `MirWp.lean:406–413`). Intentional non-termination requires a separate coinductive/invariant safety predicate such as `MirWp.ProductiveInvariant` (`MirWp.lean:2344–2370`), which guarantees `SafeFrom` without termination.

| WP Architecture | Recursion / Fixpoint | Frame Quantification | Divergence & OOM | `Init.*` Allowlist Admission |
|---|---|---|---|---|
| **`tiny-iris`** (`5b18c311`) | `bi_least_fixpoint` (`wpre Q`) | `wp_frame` + `wpbigstep` (`σ₂` quant.) | Total only; no OOM | N/A (Rocq `coq-iris`) |
| **Aeneas `#1180` + `#1551`** (`iwp`) | `ITree` (`partial_fixpoint`) + `DWP`/`DWLP` | `∀ F s, Realizes (owns owned ∗ F) s` inside `iwp` | `DWP` rejects `.div`; `DWLP` accepts `.div`; `.oom` accepted | **Rejected** (`partialFixpoint`, `Lean.Order`, `Lean.*`) |
| **Fuel `sepWpState`** (derived over `20aa2043`) | `@Nat.rec` structural fuel (`MirWp.wpState`) | `∀ F s, Realizes (sep P F) s` over `MirWp.wpState` | Rejects divergence; `ProductiveInvariant` for loops | **Admitted** (`@Nat.rec`, zero `_unsafe_rec`) |

---

## Boundaries

- **Concurrency, weak memory, and impredicative invariants — known not to apply:** Upward-closed first-order `IProp` over `PartialCommMonoid` (`tiny-iris`, Aeneas PR `#1551`, `sepWpState`) collapses `later := id` and excludes impredicative stored propositions (`inv N P` holding arbitrary `IProp`s). Lock-free concurrent protocols, weak-memory atomics, and impredicative higher-order invariants cannot be encoded in this logic and require full step-indexed Iris / `iris-lean`.
- **Single-threaded re-entrant invariant gates — unsupported:** Neither `tiny-iris` (`heapprop.v`) nor Aeneas PR `#1551` (`IProp.lean`, `WPDef.lean`) supplies mask-indexed invariant protocols (`InvMask`) for re-entrant shared interior mutability (`&Cell<T>`). Supporting dynamic re-entrant aliasing requires adding an explicit open-mask state invariant or higher-order Iris `na_inv`.
- **Semantic key equality inside pure reflective `SepAC`/`SepCancel` — unsupported:** `SepAC.Tree.denote_eq` (`Normalize.lean:59–62`) and `bagSub`/`bagSubset` compare atom indices in `env : List IProp` syntactically. Semantically equal atoms at distinct indices (e.g., `pointsTo (p + (1 + 1))` vs. `pointsTo (p + 2)`) or existential witnesses require explicit `rw` normalization or manual witness instantiation prior to reflection.
- **Compiled Lean 4 execution of derived `SepCancel` and `sepWpState` — not examined:** The source artifacts of `tiny-iris@5b18c311`, Aeneas PRs `#1551`/`#1497`/`#1180`, and `joshlf/anneal@20aa2043` were directly inspected, while the `Init.*` `SepCancel` (`bagSub`/`bagSubset`) and `sepWpState` derivations were reasoned analytically from inspected definitions and not compiled through `lean` or `anneal-audit`.
- **Full Lean build status of external WIP PR branches — unknown:** Source inspection confirmed zero `sorry`/`grind`/`omega`/`Classical.choice` in PR `#1551` `PCM.lean`, `IProp.lean`, `Local.lean`, `Borrowing.lean`, and `Specs.lean`, whereas full upstream compilation of every WIP test module across `#1551`, `#1497`, and `#1180` was not executed.

---

## Evidence

Primary sources inspected (observed `2026-11-20`):

- **`JoJoDeveloping/tiny-iris@5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`:** `theories/heapprop.v:7–24, 77–118, 130–244` (`heapProp`, `heapProp_later`, `heapProp_persistently`, `BiAffine`); `theories/weakestpre.v:6–28, 37–109` (`wpre`, `wp`, `wp_iter`, `wp_frame`); `theories/adequacy.v:9–54` (`wpbigstep`, `wp_tobigstep`, `wp_soundness`, `wp_safe`).
- **`AeneasVerif/aeneas` PR `#1551` (`1d8f9aa0121faca8ff113c1b9b742b333e3e1519`):**
  - `backends/lean/Aeneas/SepLogic/PCM.lean:13–145, 155–195` (`PartialCommMonoid`, `Subheap`, `Fragment.eq_of_union_eq`)
  - `backends/lean/Aeneas/SepLogic/IProp.lean:17–114` (`IProp`, `Entails`, `sep`, `wand`, `upClose`)
  - `backends/lean/Aeneas/SepLogic/Resource.lean:19–182` (`Resource`, `Compatible`, `Holds.overlapCompatible`, `Fragment`)
  - `backends/lean/Aeneas/SepLogic/Bytes.lean:16–87, 163–222` (`pointsTo`, `SupportsValue`, `disjoint_views`, `read_of_pointsTo`)
  - `backends/lean/Aeneas/SepLogic/Local.lean:79–182` (`LocalOp`, `LocalAt`, `LocalOp.frame`, `LocalOp.bind`)
  - `backends/lean/Aeneas/SepLogic/Specs.lean:15–79, 147–230` (`read.spec`, `modify.spec`, `modify_weaken.spec`, `write_local.spec`)
  - `backends/lean/Aeneas/SepLogic/Borrowing.lean:16–160` (`borrowAt.spec`, `shareAt.spec`, `endShare.spec`, `endBorrow.spec`)
  - `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean:18–64, 70–381` (`SepAC.Tree`, `Tree.denote_eq`, `reifySep`, `proveEqAC`, `pullLeft`)
  - `backends/lean/Aeneas/SepLogic/Tactic/IFrame.lean:14–200` (`provePure`, `instantiateRightExists`, `frameByMatching`)
  - `backends/lean/Aeneas/Std/WPDef.lean:34–99` (`effectWP`, `AuthOK`, `Realizes`, `iwp`, `ispec`, `spec`)
  - `backends/lean/Aeneas/Data/Coinductive/ITreeWP/{DWP,DWLP,Taxonomy}.lean` (`DWP`, `DWLP`, `DWP.toPartial`, `dwp_no_loops`)
- **`AeneasVerif/aeneas` PR `#1497` (`d17ca83fc07d712d1785f650840cb2073c259e69`):** `Aeneas/Std/Heap/Repr.lean:50–93` (`Cell`, `Cell.compatible`), `Model.lean:18–109, 348–364` (`Block`, `Heap`, `Inv`, `endExposureAt`), `ExclusiveReturn.lean:135–216`.
- **`AeneasVerif/aeneas` PR `#1180` (`39075a19f64c51699ec3ddde286171fb347261c8`):** `Aeneas/Data/Coinductive/{Effect,ITree}.lean`.
- **`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`:** `trusted/audit/TrustedBoundary.lean:442–596`, `Trusted/MirSemantics.lean:1831–1853`, `theory/Anneal/MirWp.lean:69–107, 280–313, 406–477, 2344–2370`, `theory/Anneal/PureLift/SpatialPin.lean:63–125`.
- **DOIs:** `10.1145/3408998` (CFML `xsimpl`), `10.1145/3236772` (MoSeL), `10.1145/3453483.3454036` (RefinedC Lithium), `10.1145/3371119` (ITrees).

---

## Revalidation

1. **Upstream signature & axiom re-check:** Fetch pinned `Normalize.lean` (`1d8f9aa0`) and `tiny-iris/theories/adequacy.v` (`5b18c311`) via `curl --http1.1 -fsSL` and confirm `Tree.denote_eq` still takes `(h : l.atoms.isPerm r.atoms = true)` and `PCM.lean`/`IProp.lean` remain free of `grind`, `omega`, and `Classical.choice`.
2. **Self-contained `Init.*` Lean 4 probe:** Materialize `PartialCommMonoid`, `IProp`, `SepTree`, `removeFirst`, `bagSub`, `bagSubset`, and `denote_frame_split` in `/tmp/sep_cancel_probe.lean` importing only `Init.Core`, `Init.Data.List.Basic`, and `Init.Data.List.Perm`, compile with `lean /tmp/sep_cancel_probe.lean`, check `#print axioms denote_frame_split` prints only `[propext, Quot.sound]`, and test an `exact denote_frame_split env _ _ rfl` obligation under `anneal-audit` preflight (`TrustedBoundary.lean`).
3. **Allowlist drift check:** Before adopting any new WP or tactic combinator into an `Init.*`-locked theory layer, diff `allowedTheoryTacticKinds` and `allowedCommandSyntaxKinds` in `trusted/audit/TrustedBoundary.lean` (`lines 464–557`) to confirm `decide` and `tacticRfl` remain admitted and `partialFixpoint`/`CoInd` remain excluded.
