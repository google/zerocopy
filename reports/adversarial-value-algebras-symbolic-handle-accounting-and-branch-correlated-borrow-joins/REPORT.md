# Algebraic Value-Carrier Laws, Symbolic Borrow-Handle Conservation, and Branch-Correlated Permission Joins in Functional Rust MIR Lifters

## Summary

Functional verification of Rust via ownership-guided lifting eliminates explicit heap reasoning on safe code by translating borrows into pure value flows, backward updates, or prophecy variables. Across four major verification architectures—Aeneas (`AeneasVerif/aeneas` at `2e3d4488280bb8a95411db81019a7854a784861f`, `10.1145/3547647`, `10.1145/3674640`), Creusot (`creusot-rs/creusot` at `faeb61f5b5a8ffda94fde1f100ef96a1d798088b`, `10.1145/3519939.3523704`), Verus (`verus-lang/verus` at `d749566d31400c9d1ab437f0853ee16d769d1b04`, `10.1145/3586037`), and carrier-parametric lens-based MIR lifters in Lean 4 (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)—soundness of nested `&mut` manipulation, conditional borrow joins, and `core::mem::swap` hinges on algebraic invariants omitted from both classical lens laws and concrete ADT interpreters:

1. **Classical very-well-behaved lens laws (`get_put`, `put_get`, `put_put`, `10.1145/1232420.1232424`) are unsoundly weak for borrow-handle carriers.** An adversarial carrier satisfying all three base lens laws can still break Rust ownership by (a) aliasing distinct field indices (`f != g`), (b) exposing fields or branch splits inside decoded handles (`decodeRef_getField`, `decodeRef_branchSplit`), (c) placing handles beyond fixed scan cutoffs (`sizeBound`, `getField_lt_sizeBound`), (d) dropping aggregate tags across field-wise joins (`sameAggregateShape_ext`), (e) mutating scalar leaves during loan-ID relabeling (`remapRefInVal_leaf`), or (f) collapsing distinct symbolic conditions or provenance-bearing handles (`sameCond_eq`, `sameRefVal_eq`). Closing all six failure modes requires 18+ supplementary carrier laws.
2. **Symbolic borrow-handle accounting is polarity-asymmetric and requires branch correlation.** Under symbolic `zipVal cond vt vf` merges, newly written values (`news`) require a pointwise multiset least upper bound (`maxUnionHandleRef`), whereas overwritten values (`olds`) require a greatest lower bound (`minInterHandleRef`). Unresolved guards `cond` must be handle-free (`collectHandleRefs cond = some []`) to stop capability smuggling, while correlated joins (`if c { h1 } else { h2 }`) require truth-table enumeration over `identifiableConds` when branch-agnostic bounds fail.
3. **Whole-writeback multiset conservation admits `mem::swap(&mut r1, &mut r2)` while defeating handle forgery.** Independent per-place conservation rejects `core::mem::swap` on `&mut &mut T` handles, whereas global multiset conservation (`replaceableVals loans olds news`) permits permuting unique handles across disjoint updated targets while blocking duplication, fabrication, sub-path retargeting, shared-to-mutable flavor forging, and resurrection of `.ended` or spatially exported loans.
4. **Sub-place permission tries require dual-flavor join cells, contradiction checks, and inherited-loan provenance guards.** Merging divergent branch borrows at the same path requires retaining both mutable and shared loan IDs (`.mutJoined mutLoans sharedLoans`), paired with writeback flavor checks (`hasMutLoanAtPath && !hasSharedLoanAtPath`), exact `List LoanId` shared-loan accounting, and ancestor-provenance checks in `setChildPerm`.

## Applicability

This report examines primary implementations and formal foundations across five repositories and five peer-reviewed publications as observed on `2026-11-20`:

- **Aeneas & Charon (`AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f`, `AeneasVerif/charon@b23c297f57c0b2072de7967c7f17088db0278a8c`):** Inspected for LLBC values (`src/llbc/Values.ml`), region abstractions (`src/interp/InterpAbs.ml`), borrow-join projection markers (`src/interp/InterpJoin.ml`, `src/interp/InterpMatchCtxs.ml`, `10.1145/3674640`), and reference types (`charon/src/ast/type_level/types.rs`).
- **Creusot (`creusot-rs/creusot@faeb61f5b5a8ffda94fde1f100ef96a1d798088b`) & Verus (`verus-lang/verus@d749566d31400c9d1ab437f0853ee16d769d1b04`):** Inspected for `core::mem::swap` specs (`creusot-std/src/std/mem.rs`, `source/vstd/std_specs/core.rs`) and `Guarded` vs. unguarded mutable permissions (`creusot-std/src/std/ptr.rs`, `creusot-std/src/cell/pcell.rs`, `creusot-std/src/invariant/guarded.rs`).
- **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Applies to constructive `prelude` formalizations (`Init.Core`, `Init.Data.List.Basic`, `Init.Data.Nat.Basic`, zero `Classical.choice`/`Quot.sound`/`sorryAx`) encoding borrow graphs with `List.foldr` and `@Nat.recCompiled`.

General overviews of Aeneas, prophetic translation, and bidirectional lenses appear in corpus packages `aeneas-borrows-symbolic-ownership-and-resource-semantics`, `rust-verification-lifetimes-prophecies-and-functional-translation`, `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, `bidirectional-lenses-resugaring-and-non-malleable-format-compilers`, and `rustc-postcleanup-mir-place-path-lens-and-borrow-semantics`. This report adds the adversarial value-algebra laws, two-sided multiset handle equations, whole-writeback conservation rules, and permission-trie join invariants.

## Findings

### 1. Value-Carrier Representations Across Aeneas, Creusot, Verus, and Lens-Parameterized Lifters

Basis: source + normative + derived

Pure functional Rust verifiers differ sharply in how references, nested borrows, and branch merges are modeled:

| System | `&'a mut T` Encoding | Nested `&mut &mut T` & `mem::swap` | Symbolic Branch Merge | Carrier-Tag Hazard |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** (`AeneasVerif/aeneas`) | Fixed ADT `tvalue` (`Values.ml:93–159`): `VLoan` / `VBorrow` (`VMutBorrow (bid, tv)`) | `convert_value_to_abstractions` (`InterpAbs.ml:25, 104, 164–166, 209–212`) aborts on nested borrows (`"Nested borrows are not supported yet"`) | Projection markers `PNone \| PLeft \| PRight` (`Values.ml:224`, `10.1145/3674640` §5) | Closed OCaml ADT blocks integer/handle punning but couples interpreter to AST |
| **Creusot** (`creusot-rs/creusot`) | Prophetic pair `{ cur: T, fin: T }` (`*x`, `^x`), closed by `Resolve` (`resolve.rs:9–64`) | `core::mem::swap` (`mem.rs:28–31`): `^x == *y && ^y == *x` | SMT `ite`; `Guarded` protects `Perm<*const T>` (`ptr.rs:599–608`) | `PCell::from_mut` (`pcell.rs:196–207`) returns unguarded `&mut Perm`, risking swap theft |
| **Verus** (`verus-lang/verus`) | `old(x)`/`final(x)` + linear `Tracked<T>` | `core::mem::swap` (`core.rs:177–183`): `*final(a) == *old(b) && *final(b) == *old(a)` | SMT conditionals; `Tracked` mode linearity | Linearity enforced on `Tracked`, not raw byte buffers |
| **Lens-Parametric Lifter** (`ValAlgebra Val`) | Opaque handle `encodeRef lid path` (mut) / `encodeSharedRef lid path` (shared) | `BackTarget` + `PermTree` + `replaceableVals` across target vector | `zipVal cond vt vf`, `branchSplit`, `projectBranchVal`, `sameCond` | Raw-byte handle punning collides with integers unless separated by tagged `SymVal` or `ValAlgebra` axioms |

In `AeneasVerif/aeneas` (`2e3d4488280bb8a95411db81019a7854a784861f`), `Values.ml:93–159` hardcodes `VLiteral | VAdt | VBottom | VBorrow | VLoan | VSymbolic`, separating `VSharedBorrow`, `VMutBorrow`, and deferred-activation `VReservedMutBorrow` (`AeneasVerif/charon` `types.rs:35, 179–182` records `RefKind::Mut | Shared`). Decoupling the borrow engine via a parameter `alg : ValAlgebra Val` enables swapping concrete MIR representations (scalars, tagged sums, or raw bytes) without rewriting the loan graph, provided `ValAlgebra` excludes adversarial carrier implementations that satisfy basic lens axioms while breaking Rust aliasing soundness (e.g., Tree Borrows uniqueness, `10.1145/3735592`).

---

### 2. Adversarial "Lawful-but-Weird" Carrier Counterexamples and the Complete `ValAlgebra` Law Suite

Basis: normative + derived

Foster et al. (`10.1145/1232420.1232424`) define a very well-behaved partial lens `Lens S A := { get : S → Option A, put : S → A → Option S }` by three axioms: **GetPut** (`get s = some a → put s a = some s`), **PutGet** (`put s a = some s' → get s' = some a`), and **PutPut** (`put s a1 = some s1 → put s1 a2 = put s a2`). Even when `fieldLens alg f` satisfies all three laws for every field `f`, **six adversarial carriers violate borrow soundness**:

1. **Aliasing field indices:** If `getField f (x, _) := some x` and `setField f (_, y) a := some (a, y)` for all `f`, each individual field satisfies `GetPut`/`PutGet`/`PutPut`, yet borrowing `&mut s.0` and `&mut s.1` aliases the same storage. Even with `getField_setField_other` (`f ≠ g → getField g s' = getField g s`), hidden counters updated differently by `setField 0` and `setField 1` break order-independence unless whole-value commutation `setField_setField_comm` holds.
2. **Handle-inside-leaf smuggling & flavor forgery:** If `decodeRef v = some (lid, path)` simultaneously exposes `getField 0 v = some secretMut` or `branchSplit v = some (c, vt, vf)`, handle scanners stop at `decodeRef` while `getPath [0] v` later extracts `secretMut`. Similarly, if `decodeRef (encodeRef l p)` returns `(l+1, p)` or `decodeRefIsShared` returns `true` on `encodeRef` when `encodeSharedRef ≠ encodeRef`, mutable handles masquerade as copyable shared handles.
3. **Traversal-cutoff evasion:** Hardcoded width (`< 8`) or depth bounds let a 33-field struct hide an untracked `&mut` at index `32` where `getPath [32]` still reaches it. Structure-derived `sizeBound : Val → Nat` with `getField_lt_sizeBound` eliminates fixed bounds while keeping `natFold` over `sizeBound v + 1` complete.
4. **Non-extensional aggregate shapes:** If `mkTagA x` and `mkTagB x` expose identical `getField 0 _ = some x`, field-by-field branch joins silently lose enum discriminants unless `sameAggregateShape_ext` guarantees equality when all fields match (`sameAggregateShape_setField` preserves relation across writes).
5. **Scalar-corrupting handle remapping:** An adversarial `remapRefInVal oldLid newLid` can obey `decodeRef_remapRefInVal` while adding `1000` to every `.nat` scalar leaf or mutating branch arms during explicit CFG joins unless constrained on fields, branch splits, and leaves (`remapRefInVal_leaf`).
6. **Unsound condition/handle equality:** If `sameCond` equates distinct conditions (`c1 ≠ c2`) or `sameRefVal` collapses handles with distinct provenance/generation tags, branch joins lose handles or metadata (`sameCond_eq`, `sameRefVal_eq`).

#### Complete Lean 4 `ValAlgebra` Axiomatization (`prelude`, `propext`-Only)

```lean
abbrev LoanId := Nat
abbrev FieldIdx := Nat
abbrev SubPath := List FieldIdx

structure ValAlgebra (Val : Type) where
  defaultVal : Val
  asBool : Val → Option Bool
  zipVal : Val → Val → Val → Val
  projectBranchVal : Val → Bool → Val → Val := fun _ _ v => v
  -- (A) Branch projection coherence
  projectBranchVal_concrete :
    ∀ cond b branch v, asBool cond = some b → projectBranchVal cond branch v = v
  projectBranchVal_zip_true :
    ∀ cond vt vf, asBool cond = none →
      projectBranchVal cond true (zipVal cond vt vf) = projectBranchVal cond true vt
  projectBranchVal_zip_false :
    ∀ cond vt vf, asBool cond = none →
      projectBranchVal cond false (zipVal cond vt vf) = projectBranchVal cond false vf
  getField : FieldIdx → Val → Option Val
  getField_projectBranchVal :
    ∀ cond branch f s a, getField f s = some a →
      getField f (projectBranchVal cond branch s) = some (projectBranchVal cond branch a) :=
    fun _ _ _ _ _ h => h
  setField : FieldIdx → Val → Val → Option Val
  -- (B) Field lens + disjoint separation & whole-value commutation
  getField_setField : ∀ f s a, getField f s = some a → setField f s a = some s
  setField_getField : ∀ f s a s', setField f s a = some s' → getField f s' = some a
  setField_setField : ∀ f s a1 a2 s1, setField f s a1 = some s1 → setField f s1 a2 = setField f s a2
  getField_setField_other : ∀ f g s a s', f ≠ g → setField f s a = some s' → getField g s' = getField g s
  setField_setField_comm :
    ∀ f g s a b s1 s2, f ≠ g → setField f s a = some s1 → setField g s1 b = some s2 →
      Exists fun s1' => setField g s b = some s1' ∧ setField f s1' a = some s2
  -- (C) Handle-as-leaf & shared/mutable flavor round-trip
  encodeRef : LoanId → SubPath → Val
  encodeSharedRef : LoanId → SubPath → Val := encodeRef
  decodeRef : Val → Option (LoanId × SubPath)
  decodeRefIsShared : Val → Bool := fun _ => true
  decodeRef_encodeRef : ∀ lid path, decodeRef (encodeRef lid path) = some (lid, path)
  decodeRef_encodeSharedRef : ∀ lid path, decodeRef (encodeSharedRef lid path) = some (lid, path)
  decodeRefIsShared_encodeSharedRef : ∀ lid path, decodeRefIsShared (encodeSharedRef lid path) = true :=
    fun _ _ => rfl
  decodeRefIsShared_encodeRef :
    ∀ lid path, encodeSharedRef lid path = encodeRef lid path ∨ decodeRefIsShared (encodeRef lid path) = false :=
    fun _ _ => Or.inl rfl
  decodeRef_getField : ∀ f v r, decodeRef v = some r → getField f v = none
  branchSplit : Val → Option (Val × Val × Val)
  decodeRef_branchSplit : ∀ v r, decodeRef v = some r → branchSplit v = none
  branchSplit_zipVal : ∀ cond vt vf, asBool cond = none → branchSplit (zipVal cond vt vf) = some (cond, vt, vf)
  -- (D) Conservative equality & 4-law loan remapping
  sameCond : Val → Val → Bool
  sameCond_eq : ∀ c1 c2, sameCond c1 c2 = true → c1 = c2
  sameRefVal : Val → Val → Bool := fun _ _ => false
  sameRefVal_eq : ∀ r1 r2, sameRefVal r1 r2 = true → r1 = r2 := fun _ _ h => nomatch h
  remapRefInVal : LoanId → LoanId → Val → Val
  decodeRef_remapRefInVal :
    ∀ oldLid newLid v, decodeRef (remapRefInVal oldLid newLid v) =
      (decodeRef v).map (fun r => (if r.1 == oldLid then newLid else r.1, r.2))
  getField_remapRefInVal :
    ∀ oldLid newLid f v, getField f (remapRefInVal oldLid newLid v) =
      (getField f v).map (remapRefInVal oldLid newLid)
  branchSplit_remapRefInVal :
    ∀ oldLid newLid v, branchSplit (remapRefInVal oldLid newLid v) =
      (branchSplit v).map (fun s =>
        (remapRefInVal oldLid newLid s.1, remapRefInVal oldLid newLid s.2.1, remapRefInVal oldLid newLid s.2.2))
  remapRefInVal_leaf :
    ∀ oldLid newLid v, decodeRef v = none → (∀ f, getField f v = none) →
      branchSplit v = none → remapRefInVal oldLid newLid v = v
  -- (E) Traversal budget & aggregate extensionality
  sizeBound : Val → Nat
  getField_lt_sizeBound : ∀ f v c, getField f v = some c → f < sizeBound v ∧ sizeBound c < sizeBound v
  sameAggregateShape : Val → Val → Bool
  sameAggregateShape_ext : ∀ v1 v2, sameAggregateShape v1 v2 = true → (∀ f, getField f v1 = getField f v2) → v1 = v2
  sameAggregateShape_setField :
    ∀ f s a s' t, sameAggregateShape s t = true → setField f s a = some s' → sameAggregateShape s' t = true
```

Family B mechanically induces `getPath_putPath_diverging` and `putPath_putPath_diverging_comm` for arbitrary diverging `SubPath` pairs, while conservative fallbacks (`sameCond := fun _ _ => false`, `sameRefVal := fun _ _ => false`, `sameAggregateShape := fun _ _ => false`) remain sound whenever a carrier omits extensional tags. Any tagged symbolic carrier (such as a `SymVal` replacing raw-byte handle encoding to avoid integer/provenance collisions) must prove all 22 laws above; omitting `remapRefInVal_leaf` or `sameAggregateShape_ext` re-opens silent scalar/tag corruption.

---

### 3. Two-Sided Branch-Correlated Symbolic Handle Accounting (`maxUnion` vs. `minInter` and Choice-Guard Handle-Freedom)

Basis: source + derived

When writing `news : List Val` over `olds : List Val`, handle accounting operates over finite multisets of `HandleRef := LoanId × SubPath × Bool` (where the boolean flags shared encoding via `decodeRefIsShared`):

- **Multiset Join (`maxUnionHandleRef`):** $\operatorname{count}(h, X \sqcup_{\max} Y) = \max(\operatorname{count}(h, X), \operatorname{count}(h, Y))$, computed by removing one copy of each `x ∈ X` from `Y` before appending (`xs ++ xs.foldr removeOneHandleRef ys`).
- **Multiset Meet (`minInterHandleRef`):** $\operatorname{count}(h, X \sqcap_{\min} Y) = \min(\operatorname{count}(h, X), \operatorname{count}(h, Y))$.

`collectHandleRefsIn alg lower ctx v` traverses `v` with budget `alg.sizeBound v + 1`:
1. Leaf handles (`decodeRef w = some (lid, path)`) yield `some [(lid, path, decodeRefIsShared w)]`.
2. Struct/tuple fields `0 ≤ idx < sizeBound w` combine via multiset **sum (`++`)**, because sibling fields coexist in every branch.
3. Symbolic merges `branchSplit w = some (cond, vt, vf)` obey **three rules**:
   - **Choice-guard handle-freedom:** Require `collectHandleRefsIn ... cond = some []`; any handle hidden inside `cond` fails closed (`none`), preventing capability smuggling inside a guard discarded by `projectBranchVal`.
   - **Context lookup:** If `lt == lf`, return `some lt`; if `lookupCond alg ctx cond = some b` (matched via `alg.sameCond`), return the selected arm.
   - **Polarity-asymmetric unresolved bounds:** When `cond` is unfixed by `ctx`, **`news` (`lower = false`, upper bound) takes `maxUnionHandleRef lt lf`**—so `zipVal c h h` counts multiplicity `1`, not `2` as `++` would—whereas **`olds` (`lower = true`, lower bound) takes `minInterHandleRef lt lf`**, crediting only handles unconditionally present in *both* arms (`fromFields` and `fromArms` combine with `maxUnionHandleRef` when `lower = true` to avoid double-crediting overlapping structure).

**Correlated Truth-Table Fallback:** For `olds = [zipVal c h1 h2, zipVal c h2 h1]` overwritten by `news = [zipVal c h2 h1, zipVal c h1 h2]`, branch-agnostic `fitsIn []` sees `minInter [h1] [h2] = []` and returns `false`. `replaceableVals` then extracts `identifiableConds` (`sameCond c c = true`, deduplicated by `sameCond`) and verifies `(condAssignments ...).all fitsIn`: both `(c, true)` (`[h1, h2] → [h2, h1]`) and `(c, false)` (`[h2, h1] → [h1, h2]`) pass, justified by `sameCond_eq`.

---

### 4. Whole-Writeback Multiset Conservation (`mem::swap` of `&mut`) and Spatial Reabsorption Boundaries

Basis: source + derived

Creusot (`creusot-std/src/std/mem.rs:28–31`, `faeb61f5b5a8ffda94fde1f100ef96a1d798088b`) and Verus (`source/vstd/std_specs/core.rs:177–183`, `d749566d31400c9d1ab437f0853ee16d769d1b04`) verify `core::mem::swap(&mut r1, &mut r2)` by equating output/final values across exclusive borrows (`^x == *y && ^y == *x`). In a first-order handle lifter, checking `replaceableVal old_i new_i` *per place* rejects `mem::swap` on `&mut &mut U`, because `old_0 = [h1]` lacks `h2` while `new_0 = [h2]`.

**Whole-writeback multiset conservation** (`replaceableVals alg loans olds news` across pairwise-disjoint `ownerPathsDisjoint` targets) checks across the concatenated target lists `olds` and `news` that in every branch `ctx`, each `r ∈ newRefs` satisfies:

$$\mathsf{handleRefCopyable}(\mathsf{loans}, r) \;\lor\; \Big(\mathsf{handleFlavorMatchesLoan}(\mathsf{alg}, \mathsf{loans}, r) \;\land\; \operatorname{count}(r, \mathsf{newRefs}) \le \operatorname{count}(r, \mathsf{oldRefs})\Big)$$

where `handleRefCopyable` requires `r.2.1 = []`, `r.2.2 = true`, and a unique `.activeShared` loan, while `handleFlavorMatchesLoan` enforces exact flavor match (`.activeShared ↦ r.2.2 = true`; `.activeMut ↦ r.2.2 = decodeRefIsShared (encodeRef r.1 r.2.1)`) and rejects `.ended` and `.spatialExported`. Together with `setLocalChecked` (gating local writes by `copyableVal` and `canWritePath []`), this closes **five laundering exploits**: (1) duplicating `&mut` handles (`[h1] → [h1, h1]`), (2) fabricating handles from scalars (`[0] → [h1]`), (3) sub-path retargeting (`(lid, [0], false) → (lid, [1], false)`) or shared sub-path forging (`(lid, [0], true)`), (4) elevating shared-form handles to mutable-form encodings, and (5) reviving `.ended` or spatially exported loans across cell/raw-pointer writebacks. Note the contrast with Creusot's `PCell::from_mut` (`creusot-std/src/cell/pcell.rs:196–207`), which omits the `Guarded` anti-swap wrapper applied to `Perm<*const T>::from_mut` (`creusot-std/src/std/ptr.rs:599–608`), permitting `mem::swap` on two `Ghost<&mut Perm<PCell<T>>>` arguments to exchange permissions across distinct `&mut T` prophecies.

---

### 5. Sub-Place Permission Tries (`PermTree`): `.mutJoined` Dual-Flavor Joins and Inherited-Loan Provenance

Basis: source + derived

Where Aeneas tags joined region abstractions with `proj_marker = PNone | PLeft | PRight` (`Values.ml:224`, `InterpJoin.ml`, `10.1145/3674640` §5), a cell-indexed permission trie `PermTree` (`unborrowed | shared (List LoanId) | mutLocked LoanId | mutJoined (List LoanId) (List LoanId) | split (List (SubPath × SubPerm))`) enforces four invariants at branch joins and writebacks:

1. **Exact `List LoanId` shared tracking:** Replacing anonymous integer refcounts with deduplicated `List LoanId` lists ensures `releaseLoanPerm lid` is path-free and never prematurely unlocks sibling shared borrows (`&x.0` vs `&x`).
2. **Dual-flavor `.mutJoined mutLoans sharedLoans` joins:** When branch 1 mutably borrows `x.0` (`lid 1`) and branch 2 shared- or mutably borrows `x.0` (`lid 2`), merging retains both active lists rather than overwriting either lock, normalizing via `mkSubPermOpt` back to `.shared`, `.mutLocked`, or `.unborrowed` as loans retire.
3. **Writeback contradiction rejection:** Before mutating `(owner, path)` on behalf of `lockLid`, writeback requires `hasMutLoanAtPath lockLid path perm = true` and `hasSharedLoanAtPath lockLid path perm = false`, rejecting contradictory `.mutJoined [lockLid] [lockLid]` cells and checking every retired sibling against its pre-retirement `LoanStatus` (`releasedPermFlavorsMatch`, then `noResidualLoanListPerm`).
4. **Inherited-ancestor provenance guard (`setChildPerm`):** Because `getChildPerm 0 (.shared [1])` inherits root loan `1` (`[]` is a prefix of `[0]`), writing back a mutated child such as `renameLoanPerm 1 2 (.shared [1]) = .shared [2]` via `setChildPerm` would leave `[]` locked by `1` while inventing a phantom child lock `2` at `[0]`. `setChildPerm` computes `solelyInheritedRootOpt` (root loans not already present at `[f]`) and returns `none` whenever `subPermContainsLoans inhSp childRootSp` fails.

---

### 6. Branch-Correlated Live-Loan Writeback Overlap (`leafBranchContexts`) and Untaken-Arm Well-Formedness

Basis: derived

When two conditional borrows share leaves in opposite branches (`if sym_c { (&mut a, &mut b) } else { (&mut b, &mut a) }`), `l1` targets `choice sym_c (direct a) (direct b)` and `l2` targets `choice sym_c (direct b) (direct a)`. Leaf-set intersection reports `{a, b} ∩ {b, a} ≠ ∅`, falsely blocking retirement of `l1` while `l2` is live.

Pre-order serialization of `BackTarget` (`BackTargetStep`: `.rootParam | .direct | .choiceJoin cond | .lensCall | .regionOut`) enables three structural checks via `List.foldr`:

1. **Unconditional `targetWellFormed` before concrete pruning:** First counts stack depth unconditionally across all `.choiceJoin` steps (must yield `some 1`), rejecting truncated subtrees even inside untaken concrete (`false`) arms before branch pruning runs.
2. **Writer branch-context extraction (`leafBranchContexts`):** Collects the symbolic condition assignments `List (Val × Bool)` reaching `(owner, path)` (collapsing concrete `asBool cond = some b` choices and defaulting to `[[]]` on malformed or empty matches).
3. **Context-sensitive observer hit test (`targetMayHitIn`):** Checks every live non-exempt loan (`!e.status.isEnded`) and active region group against each `ctx ∈ writerCtxs`, looking up `cond` via `lookupCond` (`alg.sameCond`) and short-circuiting whenever both arms agree (`bTrue == bFalse`). Whenever `sameCond` returns `false` on opaque guards, `targetMayHitIn` conservatively assumes both arms may execute. Note that if `l1` targets outer `(x, [])` on `!sym_c` while `l2` targets inner `(x, [0])` on `sym_c`, `l2` must retire before `l1`'s writeback turns `x` into a `zipVal` wrapper opaque to `getPath [0]`.

---

## Boundaries

- **Dynamic Miri / Tree Borrows runtime and Why3/Z3 solver latency (`not examined`):** All findings derive from static inspection of pinned upstream sources, peer-reviewed semantics, and Lean 4 (`v4.34.1`) proofs; dynamic Why3/Z3 trigger latency and Miri execution throughput were `not examined`.
- **Complexity of linear-arithmetic branch correlation beyond syntactic `sameCond` (`unknown`):** Generalizing `identifiableConds`/`condAssignments` from syntactic `sameCond_eq` identity to arithmetic implication (`x < 5` vs `x >= 5`) without SMT solvers or exponential explosion has `unknown` minimal complexity.
- **Sufficiency of classical 3-law lenses, per-place conservation, and `PCell::from_mut` swap protection (`known not to apply`):** Foster et al.'s three basic lens laws (`10.1145/1232420.1232424`) are `known not to apply` as sufficient borrow-carrier soundness laws due to Finding 2's six counterexamples; per-place `replaceableVal` is `known not to apply` to `core::mem::swap(&mut r1, &mut r2)`; and Creusot's `Guarded` anti-swap wrapper on `Perm<*const T>::from_mut` (`creusot-std/src/std/ptr.rs:599–608`) is `known not to apply` to `PCell::from_mut` (`creusot-std/src/cell/pcell.rs:196–207`).
- **Nested borrows in Aeneas abstractions and cyclic non-spatial borrow graphs (`unsupported`):** Nested mutable borrows inside region abstractions (`&'a mut &'b mut T`) are explicitly `unsupported` in `AeneasVerif/aeneas@2e3d4488280bb8a95411db81019a7854a784861f` (`src/interp/InterpAbs.ml:25, 30–31, 94–95, 104, 164–166, 209–212`: `"Nested borrows are not supported yet"`), and cyclic self-referential borrows without spatial export (`UnsafeCell`/`Pin`) are `unsupported` by acyclic DAG writeback.

## Evidence

- **Primary Upstream Repositories (inspected `2026-11-20`):**
  - `AeneasVerif/aeneas` at `2e3d4488280bb8a95411db81019a7854a784861f`: `src/llbc/Values.ml:77–159, 222–260`; `src/interp/InterpAbs.ml:14–252`; `src/interp/InterpJoin.ml:18–235`; `src/interp/InterpMatchCtxs.ml:22–180`.
  - `AeneasVerif/charon` at `b23c297f57c0b2072de7967c7f17088db0278a8c`: `charon/src/ast/type_level/types.rs:14–84, 179–182`; `charon/src/ast/type_level/regions.rs:10–22`.
  - `creusot-rs/creusot` at `faeb61f5b5a8ffda94fde1f100ef96a1d798088b`: `creusot-std/src/std/mem.rs:19–37`; `creusot-std/src/resolve.rs:9–64`; `creusot-std/src/invariant/guarded.rs:22–112`; `creusot-std/src/std/ptr.rs:599–608`; `creusot-std/src/cell/pcell.rs:196–207`.
  - `verus-lang/verus` at `d749566d31400c9d1ab437f0853ee16d769d1b04`: `source/vstd/std_specs/core.rs:177–183`.
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `src/Init/Data/Nat/Basic.lean:20–30`; `src/Init/Data/List/Basic.lean:544–549`.
- **Peer-Reviewed Publications:**
  - Son Ho and Jonathan Protzenko, *"Aeneas: Rust Verification by Functional Translation"*, ICFP 2022, DOI `10.1145/3547647`.
  - Son Ho, Aymeric Fromherz, and Jonathan Protzenko, *"Sound Borrow-Checking for Rust via Symbolic Semantics"*, ICFP 2024, DOI `10.1145/3674640`.
  - J. Nathan Foster et al., *"Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem"*, TOPLAS 29(3), 2007, DOI `10.1145/1232420.1232424`.
  - Yusuke Matsushita et al., *"RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code"*, PLDI 2022, DOI `10.1145/3519939.3523704`.
  - Neven Villani et al., *"Tree Borrows"*, PLDI 2025, DOI `10.1145/3735592`.
- **Executable Lean 4 (`v4.34.1`) `prelude` Probe (`/tmp/valalgebra_probe.lean`):**
  Run `lean -j1 -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/valalgebra_probe.lean`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.SimpLemmas

abbrev HandleRef := Nat × List Nat × Bool
def handleEq (a b : HandleRef) : Bool := a.1 == b.1 && a.2.1 == b.2.1 && a.2.2 == b.2.2
def removeOne (r : HandleRef) (rs : List HandleRef) : List HandleRef :=
  (rs.foldr (fun x (acc : List HandleRef × List HandleRef) =>
    match acc with | (rest, out) => (x :: rest, if handleEq x r then rest else x :: out)) ([], [])).2
def maxUnion (xs ys : List HandleRef) : List HandleRef := xs ++ xs.foldr (fun x acc => removeOne x acc) ys
def countH (r : HandleRef) (rs : List HandleRef) : Nat := rs.foldr (fun y n => if handleEq y r then n + 1 else n) 0

theorem maxUnion_idempotent_rfl : countH (1, [], false) (maxUnion [(1, [], false)] [(1, [], false)]) = 1 := rfl
theorem swap_whole_writeback_conserves_rfl :
    let olds := [(1, [], false), (2, [], false)]
    let news := [(2, [], false), (1, [], false)]
    countH (1, [], false) news ≤ countH (1, [], false) olds ∧ countH (2, [], false) news ≤ countH (2, [], false) olds :=
  ⟨Nat.le_refl 1, Nat.le_refl 1⟩
theorem alias_lens_violates_separation :
    let getF (_f : Nat) (s : Nat × Nat) : Option Nat := some s.1
    let setF (_f : Nat) (s : Nat × Nat) (a : Nat) : Option (Nat × Nat) := some (a, s.2)
    (getF 1 (match setF 0 (10, 20) 99 with | some s' => s' | none => (0, 0))) ≠ getF 1 (10, 20) := by
  intro h; injection h with hEq; contradiction

#print axioms maxUnion_idempotent_rfl
#print axioms swap_whole_writeback_conserves_rfl
```

## Revalidation

1. **Aeneas nested borrows (`AeneasVerif/aeneas`):** Check `git diff 2e3d4488280bb8a95411db81019a7854a784861f..HEAD -- src/interp/InterpAbs.ml src/llbc/Values.ml` for removal of `"Nested borrows are not supported yet"`.
2. **Creusot & Verus `mem::swap` (`creusot-rs/creusot`, `verus-lang/verus`):** Diff `creusot-std/src/std/mem.rs`, `creusot-std/src/cell/pcell.rs` (`PCell::from_mut`), and `source/vstd/std_specs/core.rs` against `faeb61f5b5a8ffda94fde1f100ef96a1d798088b` / `d749566d31400c9d1ab437f0853ee16d769d1b04`.
3. **Lean 4 kernel probe (`leanprover/lean4`):** Run `lean -j1 -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/valalgebra_probe.lean` and verify `rc = 0` plus `does not depend on any axioms` (`[]`).
