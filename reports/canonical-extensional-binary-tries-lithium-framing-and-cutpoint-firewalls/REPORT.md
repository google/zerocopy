# Canonical Extensional Binary Tries, Lithium Deterministic Framing, and Dual-Layer Cut-Point Firewalls in Lean `v4.34.1`

## Summary

Scaling zero-TCB MIR verification in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` on `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) hits three compounding cliffs:

1. **Order-Dependent List Maps:** `Trusted.MirSemantics.FrameState.locals` (`List LocalSlot` in `trusted/lean/Trusted/MirSemantics.lean#L633`), `Anneal.PureLift.MirBridge.mirListGet?`/`mirListSet?` (`theory/Anneal/PureLift/MirBridge.lean#L106-L120`), and `Anneal.PureLift.PermTree.split` (`entries : List (SubPath × SubPerm)` in `theory/Anneal/PureLift/PermTree.lean#L57`) perform $O(N)$ linear scans, and disjoint commutative writes leave unequal lists that defeat `rfl` across branch joins.
2. **Backtracking Spatial Framing Without Metaprogramming:** General separation-logic context splitting ($P * Q$) triggers $O(2^{|\Delta|})$ search, yet Pass 1 (`trusted/audit/TrustedBoundary.lean#L442-L596, #L1108-L1153`) prohibits `Lean.Elab`, `Std.*`, `partial`, and `opaque` declarations in `theory/`.
3. **C++ Kernel Transparency vs. `MetaM` Opacity (`type_checker.cpp`):** Primary-source inspection of Lean `v4.34.1` proves that `@[irreducible]` (`src/Lean/ReducibilityAttrs.lean`) populates `MetaM`'s `reducibilityCoreExt` table—preserving `<50ms` interactive LSP—**but the C++ kernel has no access to `reducibilityCoreExt`** (`type_checker.cpp#L1119-L1120`) and replays `.olean`s with `loadExts := false` (`TrustedBoundary.lean#L1548`). Meanwhile, free variables (`has_fvar`) bypass kernel GMP `reduce_nat` (`#L1093`) and closed `Bool.true` reflection (`#L1181`).

Three orthogonal mechanisms eliminate all three cliffs at zero TCB cost inside Pass-1 `prelude` `theory/`:

- **Appel-Leroy 7-Constructor Canonical `PTree` (`Canonical.v`, `CompCert/lib/Maps.v`, DOI `10.1007/s10817-022-09655-x`):** Separating non-empty tries (`PTree'` with `Node001..Node111`, omitting `000`) from `PTree α := empty | nodes (PTree' α)` makes empty subtrees **unrepresentable by type**. Map extensionality (`(∀ k, get k m₁ = get k m₂) → m₁ = m₂`) holds constructively with **zero axioms**, `Pos` (`xH | xO | xI`) lookup/update runs in $O(\log K)$ kernel iota-steps via `@Pos.rec` (zero `._unsafe_rec`, no `has_fvar` arithmetic), and disjoint writes commute by `rfl`.
- **Sammler et al. Lithium Deterministic Framing (`RefinedC`, PLDI 2021, DOI `10.1145/3453483.3454036`):** Restricting left-goals $H$ in $H * G$ to keyed spatial atoms eliminates $O(2^{|\Delta|})$ splits; indexing Lithium's linear context $\Delta$ by canonical `PTree` turns `find_in_context` into $O(\log |\Delta|)$ `PTree.get` + `PTree.remove` with `rfl`-canonical diamond joins.
- **Dual-Layer `CutBox` + `@[irreducible]` Firewalls:** Because `opaque` is banned outside `Trusted` (`TrustedBoundary.lean#L1142-L1143`) and `@[irreducible] def` retains `ReducibilityHints.regular`, wrapping cut-point assertions in a single-field `Prop` structure `structure CutBox (spanTag : Nat) (P : Prop) : Prop where val : P` emits `declaration_kind::Inductive` (`type_checker::is_delta == none`, `#L555-L563`), providing **unconditional C++ kernel delta-opacity** plus `is_def_eq_proof_irrel` (`#L932-L939`), while `@[irreducible]` wrappers preserve `<50ms` `MetaM` LSP latency and Rust span traceability.

## Applicability

This report documents six durable upstream subjects:

1. **Anneal Boundary Auditor & `PureLift` — `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `main`):** Governs Pass-1 allowlists (`TrustedBoundary.lean`), `FrameState.locals` (`Trusted/MirSemantics.lean#L633`), `PermTree`, and `._unsafe_rec`-free combinators (`PureLift/Lens.lean#L41-L79`).
2. **Lean `v4.34.1` Kernel & `MetaM` — `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`):** Applies to `src/kernel/{declaration.h, type_checker.cpp}`, `src/Lean/ReducibilityAttrs.lean`, `src/Lean/Elab/PreDefinition/Basic.lean`, and `src/Lean/Meta/WHNF.lean` (including `v4.34.1`'s `implicitReducible`/`instanceReducible` hierarchy).
3. **Canonical Binary Tries — Appel & Leroy (`arXiv:2110.05063v4`, JAR 67:8, 2023, DOI `10.1007/s10817-022-09655-x`), `xavierleroy/canonical-binary-tries` (`0dffeda1846d4bad47c39aa72611ab523bb8bfd5`), and `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`, `lib/Maps.v`):** Covers all six trie encodings (`Canonical.v` matches `CompCert/Maps.v#L189-L320`).
4. **RefinedC / Lithium — Sammler et al. (PLDI 2021, DOI `10.1145/3453483.3454036`, `gitlab.mpi-sws.org/iris/refinedc`):** Direct GitLab API access was unavailable in this environment, so Lithium's grammar and framing rules rest strictly on the published PLDI 2021 paper (`10.1145/3453483.3454036`).

No Lean compilation or kernel benchmark was executed (`--workload light` posture); Lean snippets are derived from `TrustedBoundary.lean` and `type_checker.cpp`.

## Findings

### 1. Appel-Leroy Canonical Binary Tries: Six-Representation Tradeoffs and Zero-Axiom Extensionality

`Basis: source + documentation + derived`

#### 1.1 Comparative Design Matrix (`xavierleroy/canonical-binary-tries` & `CompCert/lib/Maps.v`)

| Representation | Type Encoding | Extensional (`∀ k, get k m₁ = get k m₂ → m₁ = m₂`) | Axiom Requirements | Sparse Path Node Footprint | Pass-1 Lean 4 (`prelude` + `Init.*`) Fit |
| :--- | :--- | :---: | :---: | :--- | :--- |
| **`Original.v`** (Pre-CompCert 3.10) | `Leaf \| Node l (o : Option α) r` | **No** (`Node Leaf None Leaf ≠ Leaf`) | N/A | 3-field `Node` at every bit | Breaks `rfl` on `remove` and disjoint joins. |
| **`Node01.v`** | `Leaf \| Node01 (o : Option α) \| ...` | **No** (still permits empty subtrees) | N/A | Slightly smaller | Non-canonical; breaks `rfl`. |
| **`Sigma.v`** | `{ t : Original.tree α // wf t }` | **Yes** | Proof irrelevance (`wf` equality) | `Original` + proof wrapper | Rewrites thread `wf` proof terms inside `isDefEq`. |
| **`GADT.v`** | Indexed `tree : Bool → Type` | **Yes** | Dependent pattern matching / UIP | Compact, indexed tags | Heavy dependent `Eq.rec` terms without `omega`. |
| **`Patricia.v`** | Compressed prefix-jump radix nodes | **No** (split placement depends on insertion order) | N/A | $O(\text{pop})$ | Fast runtime, non-canonical across insertion orders. |
| **`Canonical.v` (`CompCert/Maps.v`)** | `Empty \| Nodes (tree' α)` with **7 constructors** (`Node001`..`Node111`, omitting `000`) | **Yes — structural (`=`)** | **Zero axioms (`[]`)** | **1-word unary (`Node100`/`Node001`)** on sparse paths | **Optimal:** First-order inductive types; zero `Prop` fields; `@Pos.rec` emits zero `._unsafe_rec`; `rfl` on concrete keys. |

By eliminating `Node000` from `PTree' α`, empty non-empty subtrees become syntactically unrepresentable (`Canonical.v#L25-L38`, `CompCert/lib/Maps.v#L189-L201`). Smart constructor `mkNode : PTree α → Option α → PTree α → PTree α` (`#L60-L70`) collapses `(.empty, none, .empty) ↦ .empty` and dispatches the remaining 7 combinations into `Node001..Node111`. Critically, `@Pos.rec` avoids both `._unsafe_rec` (rejected by `TrustedBoundary.validateRepoConstant`, `#L1149-L1152`) and `noncomputable` (which would block `rfl`), while bit-by-bit `Pos` matching avoids `Nat.div`/`Nat.mod` (`type_checker.cpp#L1093` `has_fvar` cliffs).

#### 1.2 Pass-1 `prelude` Lean 4 Implementation & Key Encodings

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Anneal.CanonicalTrie

/-- Positive binary integer (`xH = 1`, `xO p = 2*p`, `xI p = 2*p+1`). -/
inductive Pos where
  | xH : Pos
  | xO : Pos → Pos
  | xI : Pos → Pos

/-- Non-empty canonical binary trie (`Appel & Leroy, Canonical.v#L25-L32`): omits `Node000`. -/
inductive PTree' (α : Type) where
  | node001 : PTree' α → PTree' α
  | node010 : α → PTree' α
  | node011 : α → PTree' α → PTree' α
  | node100 : PTree' α → PTree' α
  | node101 : PTree' α → PTree' α → PTree' α
  | node110 : PTree' α → α → PTree' α
  | node111 : PTree' α → α → PTree' α → PTree' α

/-- Possibly-empty canonical binary trie (`Empty | Nodes t'`). -/
inductive PTree (α : Type) where
  | empty : PTree α
  | nodes : PTree' α → PTree α

/-- Canonical smart constructor (`Canonical.v#L60-L70`). -/
def PTree.mkNode {α : Type} : PTree α → Option α → PTree α → PTree α
  | .empty,   none,   .empty   => .empty
  | .empty,   none,   .nodes r => .nodes (.node001 r)
  | .empty,   some x, .empty   => .nodes (.node010 x)
  | .empty,   some x, .nodes r => .nodes (.node011 x r)
  | .nodes l, none,   .empty   => .nodes (.node100 l)
  | .nodes l, none,   .nodes r => .nodes (.node101 l r)
  | .nodes l, some x, .empty   => .nodes (.node110 l x)
  | .nodes l, some x, .nodes r => .nodes (.node111 l x r)

/-- Total `O(log K)` lookup via `@Pos.rec` (zero `._unsafe_rec`, kernel `rfl`-reducible). -/
def PTree.get' {α : Type} (p : Pos) (m : PTree' α) : Option α :=
  @Pos.rec (fun _ => PTree' α → Option α)
    (fun t => match t with
      | .node010 x | .node011 x _ | .node110 _ x | .node111 _ x _ => some x
      | _ => none)
    (fun _ ih t => match t with
      | .node100 l | .node101 l _ | .node110 l _ | .node111 l _ _ => ih l
      | _ => none)
    (fun _ ih t => match t with
      | .node001 r | .node011 _ r | .node101 _ r | .node111 _ _ r => ih r
      | _ => none)
    p m

def PTree.get {α : Type} (p : Pos) : PTree α → Option α
  | .empty   => none
  | .nodes t => PTree.get' p t

def PTree.set0 {α : Type} (p : Pos) (x : α) : PTree' α :=
  @Pos.rec (fun _ => PTree' α)
    (.node010 x) (fun _ ih => .node100 ih) (fun _ ih => .node001 ih) p

/-- Total `O(log K)` update via `@Pos.rec`. -/
def PTree.set' {α : Type} (p : Pos) (x : α) (m : PTree' α) : PTree' α :=
  @Pos.rec (fun _ => PTree' α → PTree' α)
    (fun t => match t with
      | .node001 r   => .node011 x r   | .node010 _     => .node010 x
      | .node011 _ r => .node011 x r   | .node100 l     => .node110 l x
      | .node101 l r => .node111 l x r | .node110 l _   => .node110 l x
      | .node111 l _ r => .node111 l x r)
    (fun q ih t => match t with
      | .node001 r   => .node101 (PTree.set0 q x) r
      | .node010 y   => .node110 (PTree.set0 q x) y
      | .node011 y r => .node111 (PTree.set0 q x) y r
      | .node100 l   => .node100 (ih l)   | .node101 l r   => .node101 (ih l) r
      | .node110 l y => .node110 (ih l) y | .node111 l y r => .node111 (ih l) y r)
    (fun q ih t => match t with
      | .node001 r   => .node001 (ih r)
      | .node010 y   => .node011 y (PTree.set0 q x)
      | .node011 y r => .node011 y (ih r)
      | .node100 l   => .node101 l (PTree.set0 q x)
      | .node101 l r => .node101 l (ih r)
      | .node110 l y => .node111 l y (PTree.set0 q x)
      | .node111 l y r => .node111 l y (ih r))
    p m

def PTree.set {α : Type} (p : Pos) (x : α) : PTree α → PTree α
  | .empty   => .nodes (PTree.set0 p x)
  | .nodes t => .nodes (PTree.set' p x t)

/-- Total `O(log K)` removal collapsing empty subtrees via `mkNode`. -/
def PTree.rem' {α : Type} (p : Pos) (m : PTree' α) : PTree α :=
  @Pos.rec (fun _ => PTree' α → PTree α)
    (fun t => match t with
      | .node010 _     => .empty
      | .node011 _ r   => .nodes (.node001 r)
      | .node110 l _   => .nodes (.node100 l)
      | .node111 l _ r => .nodes (.node101 l r)
      | _              => .nodes t)
    (fun _ ih t => match t with
      | .node100 l     => PTree.mkNode (ih l) none     .empty
      | .node101 l r   => PTree.mkNode (ih l) none     (.nodes r)
      | .node110 l y   => PTree.mkNode (ih l) (some y) .empty
      | .node111 l y r => PTree.mkNode (ih l) (some y) (.nodes r)
      | _              => .nodes t)
    (fun _ ih t => match t with
      | .node001 r     => PTree.mkNode .empty     none     (ih r)
      | .node011 y r   => PTree.mkNode .empty     (some y) (ih r)
      | .node101 l r   => PTree.mkNode (.nodes l) none     (ih r)
      | .node111 l y r => PTree.mkNode (.nodes l) (some y) (ih r)
      | _              => .nodes t)
    p m

def PTree.remove {α : Type} (p : Pos) : PTree α → PTree α
  | .empty   => .empty
  | .nodes t => PTree.rem' p t

/-- Disjoint writes commute to **syntactically identical** canonical trees by `rfl`. -/
theorem demo_comm_writes :
    PTree.set (.xO .xH) 10 (PTree.set (.xI .xH) 20 (.empty : PTree Nat)) =
    PTree.set (.xI .xH) 20 (PTree.set (.xO .xH) 10 (.empty : PTree Nat)) := rfl

theorem demo_remove_empty :
    PTree.remove (.xO .xH) (PTree.set (.xO .xH) 10 (.empty : PTree Nat)) = .empty := rfl

end Anneal.CanonicalTrie
```

- **Key Encodings & `Trusted.MirSemantics` Bridge:** Map `LocalId : Nat` bijectively to `Pos` via shifted binary successor (`0 ↦ xH`, `1 ↦ xO xH`, `2 ↦ xI xH`, etc.) so `PTree.get (encodeNatPos id) t = getElem? locals id` lifts `FrameState.locals` (`Trusted/MirSemantics.lean#L633`) with zero `Trusted.*` edits. Prefix-free path coding (`SubPath := List FieldIdx`) similarly maps `PermTree.split` and `(AllocId, Offset)` cells into `PTree`, replacing `O(N)` `loanIdListEq`/`subPathEq` scans (`PermTree.lean#L86-L100`).
- **Constructive Extensionality Proof (`Canonical.v#L324-L470, #L717-L757`):** First prove `tree'_nonempty : ∀ (m : PTree' α), ∃ k, PTree.get' k m ≠ none` structurally on `PTree'` (exhibit `xH` for `node*1*`, `xO p` for `node10*`, `xI p` for `node001`). Deduce `extensionality_empty : (∀ k, PTree.get k m = none) → m = .empty`. Then prove `PTree.ext : (∀ k, get k m₁ = get k m₂) → m₁ = m₂` via the 2-case `(empty, mkNode l o r)` view induction (`tree_ind`, hypothesis `NotTriviallyEmpty l o r`) using `congrArg` on `.xO`, `.xH`, and `.xI`—requiring **zero axioms** (`#print axioms PTree.ext` = `[]`).

---

### 2. Sammler et al. Lithium Goal-Directed Framing Over Canonical `PTree` Contexts

`Basis: documentation + derived`

In *RefinedC* (Sammler et al., PLDI 2021, DOI `10.1145/3453483.3454036`), **Lithium** avoids $O(2^{|\Delta|})$ heap-splitting search by asymmetrically restricting separation-logic entailments $\Gamma; \Delta \vdash G$ across unrestricted context $\Gamma$, linear resource context $\Delta$, **left-goals $H$**, and **basic goals $F$**:

$$\begin{aligned}
\Gamma &::= \emptyset \mid \Gamma, x \mid \Gamma, \phi \qquad \Delta ::= \emptyset \mid \Delta, A \\
H &::= \ulcorner \phi \urcorner \mid A \mid H_1 \ast H_2 \mid \exists x.\, H(x) \\
F &::= \text{stmt/post} \mid A_1 \mathbin{<:} A_2 \{G\} \quad (\texttt{subsume } A_1\; A_2\; G) \\
G &::= \text{True} \mid F \mid H \ast G \mid H \multimap G \mid G_1 \land G_2 \mid \forall x.\, G(x) \mid \exists x.\, G(x)
\end{aligned}$$

1. **Deterministic Framing Rules:** $(H_1 \ast H_2) \ast G$ reassociates left-to-right into $H_1 \ast (H_2 \ast G)$ without splitting $\Delta$. At $A_{\text{req}} \ast G$, `find_in_context` looks up the unique atom owning $A_{\text{req}}$'s key in $\Delta$ (removing it on exact match, or dispatching `RelatedTo`/`subsume` $A_{\text{ctx}} \multimap A_{\text{req}} \ast G$ for field/slice sub-place splits), while $H \multimap G$ inserts `H`'s atoms into $\Delta$ and proceeds to `G`.
2. **Pass-1 Lean 4 Realization Over `PTree`:** Because Pass 1 prohibits `Lean.Elab` tactics and Coq typeclass backtracking (`TrustedBoundary.lean#L448-L558`), encoding $\Delta$ as `PTree Atom` turns Lithium into a total `@LiGoal.rec` interpreter (`Section 4`):
   - `find_in_context` executes $O(\log |\Delta|)$ `PTree.get` + `PTree.remove` directly by kernel `rfl` on concrete `Pos` keys.
   - `subsume` decomposes aggregates stored at key `k`, preserves sibling sub-fields via `PTree.set`, and passes extracted values forward.
   - Branch joins writing independent keys in opposite orders yield **syntactically identical** post-branch `PTree` contexts (`rfl`).

---

### 3. Lean `v4.34.1` C++ Kernel Reduction Mechanics and Dual-Layer Cut-Point Firewalls

`Basis: source + derived`

Direct inspection of `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` establishes a vital asymmetry between `MetaM` elaboration and the C++ kernel:

1. **`MetaM` Layer (`src/Lean/ReducibilityAttrs.lean#L12-L193`, `src/Lean/Meta/WHNF.lean#L89-L116`, `src/Lean/Elab/PreDefinition/Basic.lean#L186-L216`):** `@[irreducible]` writes `ReducibilityStatus.irreducible` into `reducibilityCoreExt` (`PersistentEnvExtension`, applied `.afterTypeChecking`). `Meta.WHNF` calls `getUnfoldableConst?` and refuses to unfold `.irreducible` constants at `TransparencyMode.{reducible, instances, implicit, default}`—protecting `<50ms` LSP responsiveness during `simp`/`rw`/typeclass search.
2. **C++ Kernel Layer (`src/kernel/declaration.h#L15-L55, #L99-L237`, `src/kernel/type_checker.cpp#L468-L1253`):**
   - **Kernel Blindness to `@[irreducible]`:** `type_checker.cpp#L1119-L1120` explicitly states that the kernel *"does not have access to reducibility annotations."* Furthermore, `TrustedBoundary.lean#L1548-L1550` replays repository constants onto `base.toKernelEnv` with `loadExts := false`, dropping `reducibilityCoreExt`. Every safe `def` (including `@[irreducible] def`) carries `ReducibilityHints.regular (getMaxHeight env value + 1)` (`PreDefinition/Basic.lean#L186-L190`).
   - **Five Critical Paths in `type_checker::is_def_eq_core` (`type_checker.cpp#L1171-L1246`):**
     1. `quick_is_def_eq` (`#L835-L859`): $O(1)$ structural equality and positive cache `succeeded_before(t, s)` (`#L960-L977`).
     2. Closed `Bool.true` reflection (`#L1181-L1185`): `if ((!has_fvar(t) || m_eager_reduce) && is_constant(s, *g_bool_true))` calls `whnf(t)`. Any open `FVar` (`has_fvar(t)`) disables this fast path unless `eagerReduce` is active (`#L169-L184`).
     3. `whnf_core(e, false, true)` (`#L468-L551, #L1194-L1195`): beta, zeta, projection (`cheap_proj = true`), and iota reduction without delta-unfolding.
     4. `is_def_eq_proof_irrel` (`#L932-L939`): equates any two `Prop` proof terms whose types are `is_def_eq` without inspecting either proof body.
     5. `lazy_delta_reduction` (`#L1088-L1114`): line `#L1093` gates GMP `reduce_nat` (`#L702-L733`) behind `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`. Then `lazy_delta_reduction_step` (`#L999-L1056`) fast-paths matching regular heads (`is_eqp(*d_t, *d_s) && d_t->get_hints().is_regular()`, `#L1032`) by comparing arguments first (`#L1039`), **but unfolds `@[irreducible] def` on argument mismatch or unequal head heights (`#L1016, #L1028`)**!

| Firewall Candidate | Pass-1 `TrustedBoundary` Admitted? | `MetaM` Opaque (`simp`/`rw`/`whnf`)? | C++ Kernel (`is_delta`) Opaque? | Eliminable Without `opaque`? |
| :--- | :---: | :---: | :---: | :--- |
| **`abbrev`** | Yes | No (`abbrev`) | No (unfolds before `regular`) | Trivial. |
| **Plain `def`** | Yes | No (`semireducible`) | No (`regular`; unfolds on mismatch) | Trivial. |
| **`@[irreducible] def`** | **Yes** (`#L595`) | **Yes** (`<50ms` LSP) | **Partial** (`#L1032` short-circuits matches; `#L1016` unfolds mismatches) | `unfold` lemma. |
| **`opaque`** | **NO** (banned outside `Trusted`, `#L1142-L1143`) | Yes | Yes (`declaration_kind::Opaque`, `has_value() = false`) | Disallowed in `theory/`. |
| **`Prop` `structure CutBox` + `@[irreducible]` wrapper** | **Yes** (`Parser.Command.structure`, `#L462`) | **Yes** (`@[irreducible] def cutPoint`) | **100% Yes** (`declaration_kind::Inductive`, `has_value() = false`, `is_delta == none` `#L555-L563`) | **Yes — `.mk p` and `h.val`**, zero axioms, proof-irrelevant (`#L932-L939`). |

---

### 4. Unified Pass-1 Architecture: `CutBox` + Canonical `PTree` + Lithium Framing

`Basis: derived`

Building directly on `Anneal.CanonicalTrie` (§1.2), pairing `CutBox` + `@[irreducible]` cutpoints with `evalLiGoal : LiGoal Atom → PTree Atom → Prop` delivers both `MetaM` interactivity and unconditional C++ kernel isolation across basic blocks:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
-- Assumes `Pos`, `PTree`, `PTree.get`, `PTree.set`, `PTree.remove` from Section 1.2 (`Anneal.CanonicalTrie`).

namespace Anneal.ScaledTheory

open Anneal.CanonicalTrie

/-- Unconditional C++ kernel firewall (`declaration_kind::Inductive`, `has_value() == false`,
    `type_checker::is_delta == none`) plus `is_def_eq_proof_irrel` isolation.
    `spanTag` binds failed cutpoints directly to Rust spans. -/
structure CutBox (spanTag : Nat) (P : Prop) : Prop where
  val : P

/-- `MetaM`-opaque cut-point predicate (`@[irreducible]` blocks `simp`/`rw`/`whnf` < 50ms LSP). -/
@[irreducible]
def cutPoint {σ : Type} (spanTag : Nat) (P : σ → Prop) (s : σ) : Prop :=
  CutBox spanTag (P s)

theorem enterCut {σ : Type} (tag : Nat) (P : σ → Prop) (s : σ) (h : P s) :
    cutPoint tag P s := by
  unfold cutPoint; exact ⟨h⟩

theorem exitCut {σ : Type} (tag : Nat) (P : σ → Prop) (s : σ) (h : cutPoint tag P s) :
    P s := by
  unfold cutPoint at h; exact h.val

theorem composeCut {σ : Type} {t₁ t₂ t₃ : Nat} {P₁ P₂ P₃ : σ → Prop}
    (h12 : ∀ s, cutPoint t₁ P₁ s → cutPoint t₂ P₂ s)
    (h23 : ∀ s, cutPoint t₂ P₂ s → cutPoint t₃ P₃ s) :
    ∀ s, cutPoint t₁ P₁ s → cutPoint t₃ P₃ s :=
  fun s h => h23 s (h12 s h)

/-- Lithium asymmetric goal AST (`H * G` consumes keyed atoms, `H -* G` inserts disjoint atoms). -/
inductive LiGoal (Atom : Type) where
  | true_
  | pureReq (cond : Prop) (cont : LiGoal Atom)
  | atomReq (k : Pos) (subsume : Atom → Prop) (cont : LiGoal Atom)
  | addAtom (k : Pos) (a : Atom) (cont : LiGoal Atom)
  | conj (g₁ g₂ : LiGoal Atom)

/-- Total `@LiGoal.rec` deterministic Lithium evaluator over canonical `PTree Atom`. -/
def evalLiGoal {Atom : Type} (g : LiGoal Atom) (Δ : PTree Atom) : Prop :=
  @LiGoal.rec Atom (fun _ => PTree Atom → Prop)
    (fun _ => True)
    (fun c _ ih d => c ∧ ih d)
    (fun k sub _ ih d =>
      match PTree.get k d with
      | none   => False
      | some a => sub a ∧ ih (PTree.remove k d))
    (fun k a _ ih d =>
      match PTree.get k d with
      | some _ => False
      | none   => ih (PTree.set k a d))
    (fun _ _ ih₁ ih₂ d => ih₁ d ∧ ih₂ d)
    g Δ

end Anneal.ScaledTheory
```

---

### 5. Evaluation Against the Anneal Theory Rubric `(T1, P1–P5, C1–C2)`

`Basis: source + derived`

| Rubric Dimension | Grade | Assessment |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **S** | `Pos`, `PTree`, `evalLiGoal`, and `CutBox` compile in Pass-1 `theory/` (`prelude` + `Init.*`), requiring **zero `Trusted.*` edits** and **zero extra axioms** (`PTree.ext` needs `0` axioms). Statement-Origin Separation holds identically because all framing/cutpoint machinery lives inside `ConstantInfo.value?`. *(Pointer-backed Lithium heaps await non-empty `CallerMemory` support beyond `callerMem = ⟨[]⟩` on `c131b320...`.)* |
| **(P1) Human Spec Auditability** | **S** | Invisible at the Rust spec boundary; maintainers audit pure Rust contracts without seeing `PTree`, `LiGoal`, `CutBox`, or `Node001..Node111`. |
| **(P2) Authoring & Day-2 Locality** | **S** | `PTree` canonicalization gives `rfl` across diamond joins, `LiGoal` eliminates manual list-permutation proofs, and `CutBox` isolates Rust block edits from sibling blocks' proof goals and kernel checks. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **S** | `@[irreducible]` bounds `MetaM` elaboration (`<50ms` LSP); `CutBox` (`declaration_kind::Inductive`, `is_delta == none`) blocks C++ kernel delta-reduction; `is_def_eq_proof_irrel` decouples proof terms; `Pos` bypasses `has_fvar` `Nat` stalls and `._unsafe_rec`. |
| **(P4) Heterogeneous Composability** | **S** | Parametric `PTree Atom` unifies stack `LocalSlot`s, `PermTree` sub-places, `UnsafeCell`/PCM pointer cells, and ghost tokens under one framing engine. |
| **(P5) Failure Legibility** | **S** | `CutBox spanTag` binds cut failures to Rust spans; `evalLiGoal` surfaces the exact missing `Pos` key `k` or failing `subsume` predicate instead of giant list states. |
| **(C1–C2) Conceptual Minimality** | **S** | Collapses `List` maps, ad-hoc frame shufflers, `Hold` wrappers, and bespoke `SepLogic` lists into three orthogonal primitives (`PTree`, `LiGoal`, `CutBox`). |

## Boundaries

1. **`opaque` Cut-Point Declarations in `theory/` (`unsupported`):** `TrustedBoundary.validateRepoConstant` (`#L1142-L1143`) rejects `.opaqueInfo` outside `Trusted`; cutpoints in `theory/` must use `structure CutBox` + `@[irreducible]`.
2. **Disjunctive Spatial Left-Goals and Ambiguous Existential Keys (`known not to apply`):** Lithium's non-backtracking completeness (`10.1145/3453483.3454036`) does not cover unguarded disjunctive left-goals $(A_1 \vee A_2) \ast G$ or unkeyed spatial atoms without functional key determination; both require explicit case splitting or witness hints before `evalLiGoal`.
3. **Pure `rfl` Canonicalization with Uninstantiated Symbolic `Pos` Keys (`known not to apply`):** Symbolic keys `k₁ ≠ k₂ : Pos` (`FVar`s) cannot reduce `PTree.set`/`PTree.remove` by `whnf_core` and require `PTree.ext` + `gss`/`gso` lemmas (`Canonical.v#L208-L252`).
4. **Native Compiled Runtime Speed vs. `Std.DTreeMap` (`not examined`):** Pass 1 excludes `Std.*`, `Lean.*`, `#eval`, and `native_decide`; only kernel `whnf_core` reduction and axiom-free extensionality govern `theory/`.
5. **Exact Empirical Frame-Size Crossover $N^*$ (`unknown`):** The exact local/atom count $N^*$ where 7-constructor `PTree` kernel iota-steps overtake linear `List.foldr` lookup (`mirListGet?`) in Lean `v4.34.1` C++ instruction counts was not benchmarked (`unknown`).

## Evidence

| Subject | Immutable Identity / DOI | Inspected Path & Exact Symbols / Line Ranges |
| :--- | :--- | :--- |
| **Anneal `TrustedBoundary`, `MirSemantics`, `PureLift`** | `joshlf/anneal` `@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`) | `trusted/audit/TrustedBoundary.lean#L442-L596, #L1108-L1153, #L1548-L1550`; `trusted/lean/Trusted/MirAst.lean#L75-L92`; `trusted/lean/Trusted/MirSemantics.lean#L633`; `theory/Anneal/PureLift/Lens.lean#L41-L79`; `theory/Anneal/PureLift/PermTree.lean#L51-L100`; `theory/Anneal/PureLift/MirBridge.lean#L106-L120` |
| **Lean `v4.34.1` Kernel & `MetaM`** | `leanprover/lean4` `@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `src/kernel/declaration.h#L15-L55, #L99-L237`; `src/kernel/type_checker.cpp#L168-L184, #L393-L602, #L702-L733, #L835-L859, #L932-L1253` (`has_fvar` at `#L1093, #L1181`; kernel reducibility comment `#L1119-L1120`); `src/Lean/ReducibilityAttrs.lean#L12-L193`; `src/Lean/Elab/PreDefinition/Basic.lean#L186-L216`; `src/Lean/Meta/WHNF.lean#L89-L116` |
| **Appel & Leroy Paper** | DOI `10.1007/s10817-022-09655-x`, `arXiv:2110.05063v4` | Andrew W. Appel and Xavier Leroy, *Efficient Extensional Binary Tries*, Journal of Automated Reasoning 67:8 (2023) |
| **Canonical Binary Tries Coq Suite** | `xavierleroy/canonical-binary-tries` `@0dffeda1846d4bad47c39aa72611ab523bb8bfd5` | `README.md`; `Canonical.v#L25-L192, #L254-L470, #L524-L757`; `Original.v`, `Node01.v`, `Sigma.v`, `GADT.v`, `Patricia.v` |
| **CompCert `Maps.v`** | `AbsInt/CompCert` `@2685140bf72c959446981fb99b5e44a8975021bc` | `lib/Maps.v#L47-L140, #L189-L320` |
| **RefinedC / Lithium** | DOI `10.1145/3453483.3454036` | Michael Sammler et al., *RefinedC: Automating the Foundational Verification of C Code with Refined Ownership Types*, PLDI 2021 |

## Revalidation

1. **Verify Kernel Opacity & `has_fvar` Behavior Across Lean Upgrades:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/leanprover/lean4/<LEAN_SHA>/src/kernel/type_checker.cpp | grep -n -C 3 "has_fvar\|does not have access to reducibility"
   curl --http1.1 -fsSL https://raw.githubusercontent.com/leanprover/lean4/<LEAN_SHA>/src/kernel/declaration.h | grep -n -A 6 "bool has_value()"
   ```
   Confirm `is_delta` ignores `declaration_kind::Inductive` and check whether `reduce_nat` still gates on `!has_fvar`.
2. **Verify Pass-1 Compilation, Zero `._unsafe_rec`, and Zero-Axiom Purity:**
   Combine §1.2 and §4 into `/tmp/ptree_lithium_probe.lean` and run `anneal-lean-run lean /tmp/ptree_lithium_probe.lean` plus `TrustedBoundary` preflight/audit. Verify `demo_comm_writes` reduces by `rfl`, zero `._unsafe_rec` helpers appear, and `#print axioms demo_comm_writes` emits no axioms. Passing confirms Pass-1 admissibility; end-to-end scaling requires benchmarking multi-block MIR crates under `cargo anneal verify`.
