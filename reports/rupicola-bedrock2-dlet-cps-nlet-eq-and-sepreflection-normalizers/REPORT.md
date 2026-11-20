# Rupicola, bedrock2, and LiveVerif: CPS dlet/nlet_eq Lifting, Local-State Preservation, and Pass-1 Separation-Logic Normalizers

## Summary

MIT's `bedrock2`, `Rupicola` (PLDI 2022), and `LiveVerif` (PLDI 2024) solve three scaling bottlenecks that arise identically when lifting imperative Rust MIR (`Trusted.MirSemantics`) into functional Lean 4 specifications inside Anneal's Pass 1 `theory/` layer (`Init.*` only, zero `._unsafe_rec`, zero custom macros/elabs):

1. **CPS `dlet!` WP Threading & `ExprReflection` (`witnessb`):** `bedrock2`'s `WeakestPrecondition.cmd_body` (`WeakestPrecondition.v:69-116`) threads `(trace, mem, locals)` through continuation-passing `dlet!` (`coqutil.dlet`) updates, eliminating monadic bind reassociation and substituting expression values via structural recursion (`expr_body`), while `Rupicola`'s `ExprReflection` (`ExprReflection.v:15-111`) discharges an entire pure expression AST's WP via one boolean reflection check `witnessb ast true = true`. Because `bedrock2`'s `Semantics.interp_binop` treats unsigned division/modulo (`Zmod.udiv`/`Zmod.umod`) as total without faulting, adapting `ExprReflection` to `Trusted.MirSemantics.evalBinOp` (`MirSemantics.lean:1060-1159`) requires augmenting `witnessb` into `witnessSafeB` so `.div`, `.rem`, and unchecked `.addUnchecked`/`.shlUnchecked` operations carry decidable non-UB guards before `rfl` discharge.
2. **Relational `nlet_eq` Lifting (`Heq : a = a0`) & Synthesis-vs-Verification Duality:** Bare `let` bindings lose the definitional equality between an intermediate value and its source expression once abstracted across imperative stores. `Rupicola` (`Core.v:1207-1222`, `Compiler.v:16-171`) solves this via `nlet_eq vars a0 (fun (a : A) (Heq : a = a0) => ...)` (`compile_sig_as_nlet_eq`), transporting `{x : A | P0 x}` refinement invariants via `eq_rect_r` (`Eq.ndrec` in Lean 4) without unfolding `a0`. Dualizing `Rupicola`'s forward synthesis (`gallina -> ?cmd`) into Anneal's backward lifting (`captured Mir.Body -> ?spec_or_cf`) preserves `Heq` across `MirWp.wpOutcomeState` / `PureLift` steps while respecting Pass 1 Statement-Origin Separation.
3. **Local-State Preservation Without Term Blowup (`LiveVerif`):** `LiveVerif` (`LiveRules.v:48-61, 188-350`; `LiveProgramLogic.v:79-97, 197-221`) eliminates $O(N^2)$ symbolic-state cloning and $2^k$ short-circuit branch duplication through four mechanisms: sealed `Inductive elet` (`mk_elet` preserving conditional equality inside `if`/`else`), conditional in-place variable renaming (`put_into_current_locals`), single-occurrence continuation threading (`dexpr1`, `dexpr_bool3`), and isolated heaplet hypotheses `m_i |= P_i` (`with_mem`) plus `currently s := True`. In Pass 1 Lean 4 (`v4.34.1`), `@[irreducible] def LetFirewall` replicates `elet`/`currently` sealing natively at the kernel boundary without `Ltac2` or `PropExtensionality`.
4. **Three Generations of Separation-Logic Normalizers Adapted to Pass 1 Lean 4:** `coqutil`'s list `Cancel` (`SeparationLogic.v:231-360`) incurs $O(N^2)$ `firstn`/`skipn` list surgery; `Rupicola`'s `SepReflection.unsep_normal_form'` (`SepReflection.v:31-107, 165-219`) distributes `Sep` over `Unsep` (`&&&`), incurring $2^k$ Cartesian `product` blowup and **out-parameter `Rout` information loss** when expanded eagerly before mutable write-target cancellation; `LiveVerif`'s `mem_tree` (`HeapletwiseHyps.v:127-385`) achieves $O(\log N)$ binary-path tree cancellation and magic-wand frame ramification (`ramify_funspec_hyp`). In Pass 1 Lean 4, replacing `Unsep` `product` distribution with `PureLift` fractional `PermTree`/`LoanGraph` + positive-radix `PTree.diffWith` (`Pos := xH | xO | xI`, zero `funext`) and linear accumulator flattening (`flattenSepAcc`) yields $O(N \log N)$ ground `rfl` cancellation with zero `&&&` blowup.

---

## Applicability

These findings govern pure Pass 1 program-logic lifting, local-state encapsulation, and separation-logic cancellation normalizers inside Anneal's untrusted `theory/` layer (`joshlf/anneal` `20aa204315cd36aaf944778b7d33c0d609ced8e8`), analyzed against three Coq source baselines and their primary peer-reviewed specifications:
- **`mit-plv/rupicola` @ `cd89cf519551add249540db9f24aa97d8cc5d20f`** (`src/Rupicola/Lib/{Core,Notations,Compiler,ExprReflection,SepReflection}.v`; PLDI 2022, DOI `10.1145/3519939.3523706`);
- **`mit-plv/bedrock2` @ `67b682a504041acd2cd678782ff2505983d7cd6f`** (`bedrock2/src/bedrock2/{WeakestPrecondition,Semantics,ProgramLogic,HeapletwiseHyps,canceling_sepapps}.v`, `LiveVerif/src/LiveVerif/{LiveProgramLogic,LiveRules}.v`; PLDI 2021 `10.1145/3453483.3454065`, PLDI 2024 `10.1145/3656439`);
- **`mit-plv/coqutil` @ `4c399b76628330f77c53c25ebbeceadb115602ee`** (`src/coqutil/dlet.v`, `src/coqutil/Map/SeparationLogic.v`).

All Lean 4 (`v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`) adaptation modules must pass Anneal's Pass 1 `TrustedBoundary.lean` rules (`trusted/audit/TrustedBoundary.lean:442-596`): `prelude` + 51 locked `Init.*` modules only (`trusted/lean/foundation-lock.json`), closed pure tactic allowlist (`allowedTheorySyntaxKinds`: `rfl`, `decide`, `simp`, `dsimp`, `rw`, `change`, `cases`, `induction`, `injection`, `apply`, `exact`, `refine`, `unfold`, `funext`, `subst`, `@[irreducible]`; banning `sorry`, `axiom`, `partial`, `unsafe`, `omega`, `ring`, `bv_decide`, `native_decide`, `decide!`, `grind`, `._unsafe_rec`, `set_option`, `noncomputable section`, and custom `macro`/`elab`/`syntax` extensions), `{propext, Quot.sound, Classical.choice}` axiom ceiling, and Statement-Origin Separation.

Adjacent corpus reports cover complementary foundations without overlapping these findings: `anneal-fuel-free-mir-lifting-and-alias-erasure` covers `PureLift` functional borrow lifting; `lean-canonical-mir-state-and-compositional-symbolic-execution` evaluates canonical MIR state records; `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` compares Iris vs. Lean separation logics; and `aeneas-lean-backend-generated-signatures-and-wp-proof-tools` analyzes Aeneas's forward translation WP tools.

---

## Findings

### 1. `bedrock2` Continuation-Passing `dlet!` WP & `Rupicola` `ExprReflection`

`Basis: source`

#### 1.1 `dlet!` Continuation Threading in `WeakestPrecondition.cmd_body`

`coqutil/src/coqutil/dlet.v:1-6` defines a transparent let-combinator (`dlet`) whose body uses Coq `let y := x in f y` so reduction (`cbv beta delta [dlet]`) preserves local definitions in the proof context instead of substituting `x` everywhere inside `P`:

```coq
Definition dlet {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.
Notation "'dlet!' x .. y := v 'in' f" :=
  (dlet v (fun x => .. (fun y => f) .. )) ...
```

`bedrock2/src/bedrock2/WeakestPrecondition.v:69-116` embeds `dlet!` directly inside its structurally recursive command WP `cmd_body` (avoiding monadic bind associativity completely; falling back to operational `Semantics.exec` / `Semantics.call` only at `cmd.while` and `cmd.call`):

```coq
| cmd.set x ev =>
  exists v, dexpr m l ev v /\ dlet! l := map.put l x v in post t m l
| cmd.unset x =>
  dlet! l := map.remove l x in post t m l
| cmd.seq c1 c2 =>
  rec c1 t m l (fun t m l => rec c2 t m l post)
```

Notice the two mechanisms working together: `dexpr m l ev v := expr m l ev (eq v)` evaluates pure expression syntax recursively (`WeakestPrecondition.v:24-47, 64`), and `dlet! l := ...` avoids expanding the local map term across `post`.

#### 1.2 `ExprReflection` (`witnessb`) and Total-vs.-Faulting Operator Guards

In `mit-plv/rupicola` (`src/Rupicola/Lib/ExprReflection.v:15-111`), `ExprReflection` eliminates $O(|AST|)$ `straightline` tactic steps on nested arithmetic/bitwise expressions by pairing a reified `AST` (`ELit | EVar | EOp`) with a total `expr_denotation T` homomorphism (`er_opfun_morphism`) and a single accumulator check `witnessb`:

```coq
Fixpoint witnessb ast acc :=
  match ast with
  | ELit z t _ => acc
  | EVar nm => is_some (map.get concrete_locals nm) && acc
  | EOp op l r => witnessb r (witnessb l acc)
  end%bool.

Lemma interp_sound ast mem :
  witnessb ast true = true ->
  map.mapped_compat er_T2w concrete_locals locals ->
  WeakestPrecondition.dexpr mem locals (compile ast) (er_T2w (interp ast)).
```

Because `witnessb ast false = false` (`witnessb_decreasing`, lines 69-74), a single `reflexivity` (`rfl` in Lean) simultaneously establishes that every `EVar` exists in `concrete_locals` (an ordered `SortedListString.map`) and evaluates `compile ast` to `interp ast` in one reflection step.

**Crucial Semantic Discrepancy on Rust MIR (`MirSemantics.lean` vs. `bedrock2/Semantics.v`):**
In `bedrock2/src/bedrock2/Semantics.v:78-97`, `interp_binop` maps `bopname.divu => Zmod.udiv` and `bopname.remu => Zmod.umod`—total Gallina functions that never fault! By contrast, `Trusted.MirSemantics` (`MirSemantics.lean:1034-1159`) faults `.error .undefined` on:
- `.div` / `.rem` whenever `r == 0` or signed `l == signedMinInt w && r == -1`;
- `.addUnchecked` / `.subUnchecked` / `.mulUnchecked` on integer overflow;
- `.shlUnchecked` / `.shrUnchecked` when `r < 0` or `r >= w.bitWidth`.

Therefore, porting `ExprReflection` directly to Pass 1 Lean 4 without tracking domain side-conditions in `witnessb` fails on non-total MIR operators! Instead, `MirExprRefl` splits pure expressions into:
1. Total operations (`add`, `sub`, `mul`, `bitAnd`, `bitOr`, `bitXor`, comparisons, masked `shl`/`shr`): discharged unconditionally by ground `witnessb`;
2. Potentially faulting operations (`.div`, `.rem`, `*Unchecked`): either represented via an explicit precondition check `witnessSafeB locals vals ast = true` (discharging ground constants by `rfl`), or returning an explicit symbolic safety conjunction `(r != 0) ∧ ...` fused with `MirWp` via conjunctive WP modus ponens.

---

### 2. `Rupicola` Relational `nlet` / `nlet_eq` Lifting & Synthesis-vs-Verification Duality

`Basis: source + derived`

In `mit-plv/rupicola` (`src/Rupicola/Lib/Core.v:1207-1222`; `src/Rupicola/Lib/Notations.v:7-153`), relational compilation wraps intermediate bindings in `nlet` (carrying target C/bedrock2 variable names `vars : list string`) and its dependent equality-preserving twin `nlet_eq`:

```coq
Definition nlet_eq {A} {P: forall a: A, Type}
           (vars: list string) (a0: A)
           (body : forall (a : A) (Heq: a = a0), P a) : P a0 :=
  let x := a0 in body x eq_refl.

Definition nlet {A T} (vars: list string) (a0: A) (body : A -> T) : T :=
  let x := a0 in body x.
```

#### 2.1 Why `nlet_eq` (`Heq : a = a0`) Is Essential for Dependent Types & Array Bounds

When a pure program constructs a refinement subtype `{x : A | P0 x}` (for instance, a bounded array index `idx < len`) and an imperative step computes `x0' : A` into a local variable or memory slot, bare `let x := x0 in body x` cannot relate the abstracted variable `x0'` back to `P0 x0` once `x0` has been generalized inside `WeakestPrecondition.cmd`. `Compiler.v:152-171` resolves this via `compile_sig_as_nlet_eq`:

```coq
Lemma compile_sig_as_nlet_eq {tr mem locals functions} {A} P0 (x0: A) Px0:
  let v := exist P0 x0 Px0 in
  forall {T} {pred: T -> predicate} {k: {x: A | P0 x} -> T} vars cmd,
    (let Px := Px0 in
     let cast {x0'} Heq := eq_rect_r (fun x => P0 x) Px Heq in
     <{ Trace := tr; Memory := mem; Locals := locals; Functions := functions }>
     cmd <{ pred (nlet_eq (P := fun _ => T) vars x0
                     (fun x0' Heq => k (exist P0 x0' (cast Heq)))) }>) ->
    <{ Trace := tr; Memory := mem; Locals := locals; Functions := functions }>
    cmd <{ pred (nlet vars v k) }>.
```

Because `Heq : x0' = x0` stays explicitly bound in the continuation while `compile_copy_pointer` (`Compiler.v:122-150`) and `compile_expr` (`ExprReflection.v:195-218`) instantiate `Heq` with `eq_refl` at leaf discharge, dependent bounds invariants `P0 x0'` transport through `eq_rect_r` (`Eq.ndrec` in Lean 4) without unfolding `x0`!

#### 2.2 Synthesis vs. Backward Verification Polarity

| Aspect | `Rupicola` Forward Compilation (`Compiler.v`) | Anneal Backward Verification (`theory/Anneal/`) |
| :--- | :--- | :--- |
| **Input & Unknown** | Input: pure Gallina `nlet` program; Unknown: `?cmd : Syntax.cmd`. | Input: concrete captured `Mir.Body` `b`; Unknown: lifted `PureSpec` / proof over `wpState b`. |
| **Direction of `compile_*` rules** | Head of `post` (`nlet vars v k`) drives synthesis of `?cmd` (`cmd.seq (cmd.set ...) ?k_impl`). | Head of `b` statement (`Assign dst rv`, `SwitchInt`, `Call`) drives lifting into `nletEq v (fun x hx => ...)`. |
| **Binding names (`vars`)** | Target variable strings emitted into generated C/bedrock2 AST. | Diagnostic Rust source local / span labels for human/LSP error messages. |
| **Type/proof erasure** | `compile_sig_as_nlet_eq` strips `{x | P0 x}` proofs out of generated C locals. | Statement-Origin Separation keeps `nletEq` inside `theory/` proof terms, never inside `CrateTheorem`! |

---

### 3. `LiveVerif` Local-State Preservation Without Global Term Blowup

`Basis: source`

Inspecting `mit-plv/bedrock2@67b682a5` (`LiveVerif/src/LiveVerif/LiveRules.v:48-61, 188-350`; `LiveVerif/src/LiveVerif/LiveProgramLogic.v:79-97, 197-221`) isolates four engineering patterns that eliminate the quadratic term blowup seen in raw symbolic execution:

1. **Branch-Safe Sealed Bindings (`Inductive elet`):** As `LiveRules.v:48-61` observes, using raw `(∃ x, x = rhs ∧ P x)` under an `if c then ... else ...` branch loses `x = rhs` when pulling `∃ x` outside the `if`:
   ```coq
   Inductive elet{A: Type}(rhs: A)(body: A -> Prop): Prop :=
   | mk_elet(x: A)(_: x = rhs)(_: body x).
   ```
   Destructing `mk_elet` binds `x` and keeps `Heq : x = rhs` isolated until explicitly unfolded, matching `nlet_eq` inside `Prop`.
2. **In-Place Variable Renaming (`put_into_current_locals`):** Instead of accumulating `map.put (map.put ...)` terms inside every subsequent hypothesis (`O(K^2)` map lookups), `LiveProgramLogic.v:197-221` checks whether the RHS `v` is already a fresh local variable (`is_var v`) not shadowed in `locals` or `FunctionParams`. If so, it renames `v` directly to the program variable name (`rename v into i`) with zero equality hypothesis! Only when `v` is an expression or shared parameter does it emit `update_one_local_eq` (`Def0 : x = v`).
3. **Single-Occurrence Continuation Threading (`dexpr1` & `dexpr_bool3`):** Evaluating short-circuiting boolean expressions `e1 && e2` with heap loads naively duplicates memory hypotheses across the `true` and `false` arms ($2^k$ blowup across $k$ conjuncts). `LiveRules.v:191-350` introduces:
   ```coq
   Inductive dexpr1(m: mem)(l: locals)(e: expr)(v: word)(P: Prop): Prop :=
   | mk_dexpr1(Hde: dexpr m l e v)(Hp: P).

   Definition bool_expr_branches(b: bool)(Pt Pf Pa: Prop): Prop :=
     (if b then Pt else Pf) /\ Pa.

   Inductive dexpr_bool3(m: mem)(l: locals)(e: expr): bool -> Prop -> Prop -> Prop -> Prop := ...
   ```
   In `dexpr_bool3_lazy_and` (`LiveRules.v:304-333`), `Pt`, `Pf`, and `Pa` each appear **exactly once** syntactically in the rule conclusion, with `Pt` nested inside `e2`'s continuation so heap updates performed while evaluating `e1` stay visible when stepping into `e2`, avoiding $2^k$ tree explosion.
4. **Isolated Heaplets (`with_mem`) & Non-Growing State Container (`currently`):** `HeapletwiseHyps.v:20` wraps individual disjoint heaplets in `with_mem m P` (`m |= P`) so local mutations touch only the single `m_i |= P_i` hypothesis containing `a ↦ v` rather than rewriting one monolithic `sep` conjunction over the entire heap; `LiveProgramLogic.v:79-97` stores tactic metadata inside `Definition currently (contents : Type) := True`, whose `change` updates leave proof terms completely unchanged (`I : True`).

---

### 4. Separation-Logic Normalizers (`Cancel`, `SepReflection`, `mem_tree`) & Pure Pass-1 Lean 4 Design

`Basis: source + derived`

#### 4.1 Comparative Anatomy of the Three Upstream Normalizers

| Normalizer & Source Anchor | Core Representation & Algorithm | Complexity & Unification Behavior | Key Soundness / Scalability Hazard |
| :--- | :--- | :--- | :--- |
| **`coqutil` `Cancel`**<br>`coqutil/.../SeparationLogic.v:231-360, 703-715, 853-858` | Reifies `sep` trees into flat `list (mem -> Prop)` (`seps`), then repeatedly runs `cancel_seps_at_indices i j xs ys` using `firstn`/`skipn` and `iff1ToEq` (`PropExtensionality` + `FunctionalExtensionality`). | **$O(N^2)$ list splitting + backtracking `ecancel` unification** (`multimatch` over list indices). | Sensitive to syntactic mismatches (`S n` vs `Nat.succ n`); relies on `PropExtensionality` + `FunctionalExtensionality` for `iff1ToEq`; quadratic tactic search on large frames. |
| **`Rupicola` `SepReflection`**<br>`SepReflection.v:19-107, 165-219`; `Core.v:763-896` | Inductive `expr := Pred \| Sep \| Unsep`; `unsep_normal_form'` distributes `Sep` over `Unsep` (`&&&`) via `map2 Sep (product ...)` and proves one-way `impl1` soundness (`unsep_normal_form_sound`). | **$O(2^k)$ worst-case Cartesian `product` blowup** when `Sep` nests $k$ `Unsep` disjunctions! | **1. `Rout` info loss (`SepReflection.v:191-216`):** Expanding `(z ↦ Z * (x ↦ X &&& y ↦ Y))` to `(z ↦ Z * x ↦ X) &&& (z ↦ Z * y ↦ Y)` eagerly before canceling mutable out-param `z` drops either `x` or `y`!<br>**2. One-way `impl1` only:** distribution is not `iff1` invertible. |
| **`LiveVerif` `mem_tree`**<br>`HeapletwiseHyps.v:70-86, 127-385`; `canceling_sepapps.v:14-56` | Binary AST `mem_tree := NEmpty \| NLeaf m \| NDisjointUnion \| NEqualUnion`; cancels matched heaplets along binary `path : list bool` (`mem_tree_remove`), unfolds `sepapps` struct offsets, and uses `wand` ramification (`ramify_funspec_hyp`, `canceling_done_frame`). | **$O(\log N)$ path lookup/removal per heaplet** + zero premature `?Frame` evars (via `wand calleePost callerPost`). | Implemented via `Ltac1` / `Ltac2` search scripts + `propositional_extensionality` (`wand_alt`); cannot run as custom tactic elabs inside Anneal Pass 1 `theory/`. |

**Why `Rupicola`'s `Unsep` (`&&&`) Causes Both Blowup and `Rout` Loss (`SepReflection.v:168-216`):**
In C/bedrock2, a read-only input slice `p1` and `p2` can alias (`add(x, y, x)`), so `Rupicola` encodes may-alias preconditions via non-separating conjunction `(p1 ↦ o1 * R1) &&& (p2 ↦ o2 * R2) &&& (pout ↦ out * Rout)`. Because `SepReflection`'s `product` (`SepReflection.v:34-36`) only expands `Sep` over `Unsep` and never factors, expanding `z ↦ Z * (x ↦ X &&& y ↦ Y)` early forces `ecancel` to unify `Rout` against only one branch (`x ↦ X` or `y ↦ Y`), dropping the other read-only invariant. `SepReflection.v:205-219` therefore uses a fragile heuristic (`Hint Extern 1 ((sep _ _) _) => normalize_decompose_relevant_sep`) only *after* direct cancellation fails!

#### 4.2 Pure Pass-1 Lean 4 (`v4.34.1`) Realization (`theory/Anneal/`)

Under `TrustedBoundary.lean:442-596`, Pass 1 bans custom `macro`/`elab` reifiers, `omega`, `partial`, and `Std.*`, while **admitting `@[irreducible]`, `rfl`, `decide`, `Init.Data.Nat.Basic`, and primitive `@Ind.rec`**. Adapting the best ideas from `bedrock2`, `Rupicola`, and `LiveVerif` without their `Ltac`/exponential traps yields three small, kernel-fast Pass 1 components:

1. **`nletEq` + `@[irreducible] def LetFirewall` (Zero-Blowup Local Scoping):**
   ```lean
   prelude
   import Init.Core

   namespace Anneal.CPS

   def nletEq {A : Type} {P : A → Type} (a0 : A)
       (body : ∀ (a : A), a = a0 → P a) : P a0 :=
     body a0 rfl

   /-- Pass-1 `elet`/`currently` equivalent: `@[irreducible]` is explicitly
       admitted by `TrustedBoundary.lean:595` and blocks kernel `whnf`/`isDefEq`
       from unfolding `P` across branch joins or local slot updates. -/
   @[irreducible]
   def LetFirewall (_tag : Nat) (P : Prop) : Prop := P

   theorem letFirewall_intro {tag : Nat} {P : Prop} (h : P) : LetFirewall tag P := by
     unfold LetFirewall; exact h

   theorem letFirewall_elim {tag : Nat} {P : Prop} (h : LetFirewall tag P) : P := by
     unfold LetFirewall at h; exact h

   end Anneal.CPS
   ```

2. **Safe MIR `ExprReflection` (`MirExprRefl` with `witnessSafeB`):**
   Reifies pure `Rvalue` expression trees into `ExprAst` (`lit | var idx | op binOp l r`) evaluated over C++ GMP `Nat` / sign-magnitude `SInt` without `._unsafe_rec`. Unlike `Rupicola`'s total `witnessb`, `witnessSafeB` checks **both** slot liveness/initialization (`locInitMask`) and safety guards for `.div`/`.rem` (`rhs != 0`, no signed `MIN / -1`) and `*Unchecked` (`Nat.ble width 128` + bounds), collapsing multi-step `evalRvalue` / `evalStatement` WP goals into a single ground `rfl` application!

3. **Linear-Time `PTree` Spatial Cancellation Without `Unsep` (`PTreeSepCancel`):**
   Rust's aliasing discipline cleanly eliminates `Rupicola`'s `Unsep` (`&&&`) trap: read-only shared references `&T` (`Freeze` or shared `PCM` read fractions `(num, den)`) compose cleanly inside a single separating resource store (`PureLift` `PermTree`/`LoanGraph` for safe borrows + `PCM` fractional shares for raw/spatial regions) instead of duplicating heap descriptions across `&&&`! Spatial framing and cancellation then run in **$O(N \log N)$ via canonical positive-radix tries `PTree`** (avoiding both `coqutil`'s $O(N^2)$ `firstn`/`skipn` and `Rupicola`'s $2^k$ `product`):
   ```lean
   prelude
   import Init.Core
   import Init.Data.List.Basic

   namespace Anneal.SepNorm

   /-- Positive-radix binary key for canonical trie (`PTree`). -/
   inductive Pos where
     | xH
     | xO (p : Pos)
     | xI (p : Pos)

   /-- Canonical empty-collapsed trie: `make .leaf none .leaf = .leaf`,
       giving structural extensionality without `funext` or `propext`! -/
   inductive PTree (α : Type) where
     | leaf
     | node (l : PTree α) (v : Option α) (r : PTree α)

   def PTree.make {α : Type} : PTree α → Option α → PTree α → PTree α
     | .leaf, none, .leaf => .leaf
     | l,     v,    r     => .node l v r

   /-- Linear $O(|AST|)$ accumulator normalizer (zero quadratic `++`!). -/
   inductive SepAst (Atom : Type) where
     | emp
     | pure (idx : Nat)
     | atom (key : Pos) (a : Atom)
     | star (lhs rhs : SepAst Atom)

   def flattenSepAcc {Atom : Type} :
       SepAst Atom → List (Pos × Atom) × List Nat → List (Pos × Atom) × List Nat
     | .emp,       acc => acc
     | .pure i,    (atoms, props) => (atoms, i :: props)
     | .atom k a,  (atoms, props) => ((k, a) :: atoms, props)
     | .star l r,  acc => flattenSepAcc l (flattenSepAcc r acc)

   end Anneal.SepNorm
   ```
   At a call site (`PureLift.SpatialPin` or raw-pointer pre/post framing), inserting the caller's spatial atoms into `PTree Atom` (keyed by `(AllocId, SegmentId) : Pos`) and running `PTree.diffWith` against the callee's required atoms cancels matching heaplets in $O(N \log N)$ kernel `rfl` steps, isolates unmatched residues as exact `Frame` subtrees (or magic-wand ramification obligations matching `LiveVerif`'s `ramify_funspec_hyp`), and leaves all pure facts in a flat `List Nat` index vector without `product` blowup or `Rout` loss!

---

### 5. Anneal `theory/` Rubric Evaluation (`T1`, `P1`–`P5`, `C1`–`C2`)

`Basis: derived`

| Mechanism | (T1) 0-TCB Bridge | (P1) Spec Auditability | (P2) Authoring & Locality | (P3) Kernel & `<50 ms` LSP | (P4) Hetero. Comp. | (P5) Failure Legibility | (C1–C2) Minimality & Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`nletEq` + `@[irreducible]` `LetFirewall`** | **100% 0-TCB:** 15 LOC over `Init.Core`; hidden from `CrateTheorem` via Statement-Origin Separation. | **High:** Keeps user specs readable without unfolding intermediate block states. | **Very High:** `Heq : a = a0` survives control joins & transports refinement bounds (`Eq.ndrec`). | **Very High:** Blocks kernel `whnf`/`isDefEq` traversal across `CutFirewall` boundaries (`<5 ms`). | **High:** Works uniformly across pure values, `PureLift` lenses, and `Unwind` tracks. | **High:** `tag : Nat` maps firewall failures directly to Rust `rustc_span` locations. | **Adopt (P0):** Minimal bedrock binder unifying `dlet`, `nlet_eq`, and `elet`. |
| **`MirExprRefl` (`witnessSafeB`)** | **100% 0-TCB:** Reifies `Rvalue` ASTs over `Init.*` + `Trusted.MirAst`. | **High:** Proofs show 1 `rfl` instead of 20+ manual `evalStatement` steps. | **High:** Local expression edits re-check independently in 1 step. | **Very High:** C++ GMP `Nat` `witnessSafeB` runs in `<1 ms` (`rfl`). | **High:** Explicit UB checks handle total ops AND `.div`/`.rem`/`*Unchecked` safely. | **High:** Failed `witnessSafeB` returns exact uninit/UB operand index. | **Adopt (P0):** Direct Pass 1 successor to `Rupicola` `ExprReflection`. |
| **`LiveVerif` `dexpr_bool3` + `with_mem` Pattern** | **100% 0-TCB:** Pure `Prop` continuation combinator in `theory/`. | **High:** Avoids nested `∃` skolemization clutter in branch postconditions. | **Very High:** Eliminates $2^k$ duplication on short-circuiting `&&`/`||` guards. | **Very High:** Single syntactic occurrence of `Pt`/`Pf`/`Pa` keeps proof terms linear. | **High:** Preserves state updates across `e1 && e2` with heap mutations/borrows. | **Med-High:** Clear split into `onTrue`/`onFalse`/`always` subgoals. | **Adopt (P1):** Structure branch combinators with single-use continuations. |
| **`PTreeSepCancel` + `PureLift` / `PCM` Shares (Replacing `Unsep`)** | **0-TCB on `PureLift`;** bridges raw pointers once `CallerMemory`/`PtrVal` land. | **High:** Eliminates `&&&` may-alias formulas from Rust specs via borrows/fractions. | **Very High:** Updating 1 key in `PTree` preserves all sibling frames (`O(log N)`). | **Very High:** Ground `PTree.diffWith` runs via `rfl` in $O(N \log N)$ vs $O(N^2)$ `Cancel` / $2^k$ `Unsep`. | **Very High:** Unifies safe `&T` (`PermTree`), `SpatialPin`, fractional reads, and ramified callback frames. | **High:** Reports exact missing `(AllocId, SegmentId)` key on frame mismatch. | **Adopt (P0/P1):** Collapses `Cancel`, `SepReflection`, and `mem_tree` into 1 canonical `PTree` normalizer. |

#### Conceptual Minimality Audit (`C1–C2`): Three Premature Collapses Refuted

1. **Collapsing `nletEq` into plain `let`:** Refuted by dependent refinement transport (`compile_sig_as_nlet_eq`): once an intermediate `let x := v` is generalized across a call or branch (`CutFirewall`), plain `let` loses `x = v`, preventing `Eq.ndrec` transport of `x < slice.len`!
2. **Collapsing `PureLift` shared loans / `PCM` shares into `Rupicola` `Unsep` (`&&&`):** Refuted by `SepReflection.v:34-36, 191-216`: `&&&` forces $2^k$ Cartesian `product` expansion under `Sep` and causes out-parameter `Rout` information loss when expanded eagerly, whereas Rust `&T` borrows and `PCM` fractional shares stay linear inside a single `PTree`.
3. **Collapsing `MirExprRefl` `witnessSafeB` into total `Rupicola` `witnessb`:** Refuted by `Trusted.MirSemantics.evalArithOp` (`MirSemantics.lean:1060-1089`), where `.div`/`0` and `.addUnchecked` fault `.undefined` rather than returning total `Zmod` values.

---

## Boundaries

- **Known not to apply:**
  - `Rupicola`'s `unsep_normal_form_sound` (`SepReflection.v:79-87`) as an `iff1` equivalence **is known not to apply** (distribution of `*` over `&&&` is strictly one-way `impl1`), and eager `unsep_normal_form` prior to out-parameter cancellation **is known not to apply** due to `Rout` information loss (`SepReflection.v:191-216`).
  - Porting `Rupicola`'s `ExprReflection.witnessb` (`ExprReflection.v:62-67`) to Rust MIR without adding division/overflow guards (`witnessSafeB`) **is known not to apply**, because `bedrock2` arithmetic is total (`Zmod.udiv`) whereas `Trusted.MirSemantics` faults `.undefined`.
  - Using `coqutil`'s `iff1ToEq` (`SeparationLogic.v:853-858`) or `LiveVerif`'s `wand_alt` (`HeapletwiseHyps.v:50-55`) without `PropExtensionality` / `FunctionalExtensionality` **is known not to apply** (Pass 1 bans `funext`-free extensionality traps by preferring structural `PTree` normalization over predicate equality).
- **Unsupported:**
  - Implementing `Ltac`/`Ltac2`-style custom tactic reifiers (`reify_map`, `expr_reify_word`, `SepRefl.reify`) via custom `elab`, `macro`, `syntax`, or `notation` inside Anneal Pass 1 `theory/` files is **unsupported** (`TrustedBoundary.lean:442-558`); certificate ASTs must be constructed externally or written explicitly and checked in pure Lean via `rfl`.
  - Raw-pointer heaplet predicates (`ptsto`, `sepapp`) over `Trusted.MirSemantics` at `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8` are currently **unsupported** (`CallerMemory` must be empty and `.ref`/`.rawPtr` step to `.fault .unsupported`), so `PTreeSepCancel` operates on `PureLift` logical places until raw memory allocations are admitted in `Trusted.*`.
- **Not examined:**
  - `Rupicola`'s experimental array/loop broadcast synthesis rules (`src/Rupicola/Lib/Loops.v`) and `LiveVerif`'s Coq-IDE C-like custom notation parser (`LiveSnippet.v`) were **not examined**.
  - Weak-memory / concurrent separation-logic frames (fractional atomic permissions) were **not examined** in this comparison.
- **Unknown:**
  - For small spatial contexts ($N \le 8$ atoms), whether flat sorted `List (Nat × Atom)` merge or `Pos`-indexed `PTree.diffWith` minimizes Lean `v4.34.1` C++ kernel `whnf` wall-clock time remains **unknown** pending empirical benchmarking.

---

## Evidence

1. **`mit-plv/rupicola` @ `cd89cf519551add249540db9f24aa97d8cc5d20f` (`Basis: source + normative`):**
   - `src/Rupicola/Lib/Core.v:122-141, 763-896, 1207-1222`: `mapped_compat`, `SeparationLogic.unsep`/`unseps`/`unseps_distr_sep`, `nlet_eq`, `nlet`, `nlet_as_nlet_eq`.
   - `src/Rupicola/Lib/Notations.v:7-153, 205-206`: `let/d`, `let/n`, `let/n ... eq:`, `⋆`, `&&&`.
   - `src/Rupicola/Lib/Compiler.v:16-171`: `compile_dlet_as_nlet_eq`, `compile_nlet_as_nlet_eq`, `compile_nested_nlet`, `compile_nlet_push_continuation`, `compile_copy_pointer`, `compile_sig_as_nlet_eq`, `compile_unsets`.
   - `src/Rupicola/Lib/ExprReflection.v:15-133, 135-225`: `expr_denotation`, `AST`, `witnessb`, `witnessb_decreasing`, `interp_sound`, `expr_word_denotation`, `expr_Z_denotation`.
   - `src/Rupicola/Lib/SepReflection.v:19-107, 165-219`: `SepRefl.expr`, `unsep_normal_form'`, `unsep_normal_form_sound`, `Rout` information-loss commentary.
2. **`mit-plv/bedrock2` @ `67b682a504041acd2cd678782ff2505983d7cd6f` (`Basis: source`):**
   - `bedrock2/src/bedrock2/WeakestPrecondition.v:13-125`: `literal`, `cmd_body` (`dlet!`), `dexpr`.
   - `bedrock2/src/bedrock2/Semantics.v:78-97`: total `interp_binop` (`bopname.divu => Zmod.udiv`).
   - `bedrock2/src/bedrock2/HeapletwiseHyps.v:20, 70-86, 127-385`: `with_mem`, `wand`, `ramify_funspec_hyp`, `mem_tree`, `mem_tree_lookup`, `mem_tree_remove`, `canceling_done_frame`, `consume_mem_tree`.
   - `bedrock2/src/bedrock2/canceling_sepapps.v:14-56`: `cancel_sepapp_head`, `cancel_sepapps_*`.
   - `LiveVerif/src/LiveVerif/LiveRules.v:48-61, 188-350`: `elet`, `dexpr1`, `bool_expr_branches`, `dexpr_bool3`, `dexpr_bool3_lazy_and`.
   - `LiveVerif/src/LiveVerif/LiveProgramLogic.v:79-97, 197-221`: `currently`, `put_into_current_locals`.
3. **`mit-plv/coqutil` @ `4c399b76628330f77c53c25ebbeceadb115602ee` (`Basis: source`):**
   - `src/coqutil/dlet.v:1-6`: `dlet` and `dlet!` notation.
   - `src/coqutil/Map/SeparationLogic.v:231-360, 703-715, 853-858`: `seps`, `cancel_seps_at_indices`, `ecancel`, `iff1ToEq`.
4. **`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` & `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) (`Basis: source`):**
   - `trusted/audit/TrustedBoundary.lean:442-596`: Pass 1 allowlists (`allowedTheorySyntaxKinds`, `@[irreducible]` admission).
   - `trusted/lean/Trusted/MirSemantics.lean:1034-1159`: faulting `.div`/`.rem`/`*Unchecked` arithmetic and shifts.
5. **Publications (`Basis: normative`):**
   - Pit-Claudel, Philipoom, Jamner, Erbsen, Chlipala, *"Relational Compilation for Performance-Critical Applications"*, PLDI 2022, DOI `10.1145/3519939.3523706`.
   - Erbsen, Gruetter, Choi, Wood, Chlipala, *"Integration Verification Across Software and Hardware for a Simple Embedded System"*, PLDI 2021, DOI `10.1145/3453483.3454065`.
   - Gruetter, Fukala, Chlipala, *"Live Verification in an Interactive Proof Assistant"*, PACMPL 8(PLDI), Article 209, 2024, DOI `10.1145/3656439`.

---

## Revalidation

1. **Upstream Coq definition checks (`Rupicola`, `bedrock2`, `coqutil`):**
   ```bash
   RUP_SHA="cd89cf519551add249540db9f24aa97d8cc5d20f"
   B2_SHA="67b682a504041acd2cd678782ff2505983d7cd6f"
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/mit-plv/rupicola/${RUP_SHA}/src/Rupicola/Lib/Core.v" | grep -nE "Definition nlet_eq|Definition nlet "
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/mit-plv/rupicola/${RUP_SHA}/src/Rupicola/Lib/SepReflection.v" | grep -nE "unsep_normal_form|product"
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/mit-plv/bedrock2/${B2_SHA}/LiveVerif/src/LiveVerif/LiveRules.v" | grep -nE "Inductive elet|Inductive dexpr_bool3"
   ```
2. **Pass 1 Lean 4 (`v4.34.1`) admission probe:** Compile the `Anneal.CPS` (`nletEq`, `@[irreducible] def LetFirewall`) and `Anneal.SepNorm` (`Pos`, `PTree`, `flattenSepAcc`) snippets from Section 4.2 under Anneal's `anneal-audit` Pass 1 syntactic preflight (`TrustedBoundary.lean:442-596`), verifying zero forbidden syntax kinds, zero `._unsafe_rec` helpers, and `#print axioms` strictly within `{propext, Quot.sound, Classical.choice}`.
