# Backward-Sound MIR Move-Deinitialization, Freeze-Gated GVN/CSE, and Guarded-Preheader LICM

## Summary

Backward-sound MIR proof-compression preprocessors run outside Anneal's Trusted Computing Base (`theory/`) by transforming `Runtime(PostCleanup)` `Trusted.MirAst.Body` terms `b` into simplified bodies `b'` (demoting `Operand.move` to `Operand.copy`, erasing redundant storage markers, deduplicating dominated expressions, or hoisting loop invariants) and transporting weakest preconditions `wpState b' Q -> wpState b Q` backward without modifying `Trusted.*`. Because **verification polarity inverts compiler-optimization polarity**, four invariants govern soundness and completeness under Anneal's MIR semantics ($M_{\text{anneal}}$, anchored in Pass 2 to `proofs-rs/lean-miri` with `deinitMovedPlace = true`):

1. **Polarity Inversion & the `SsaLocals` / `deinitMovedPlace = true` Trap:** Forward passes (`rustc` `SsaLocals`/`GVN`, `CompCert` `CSEdomain.v`) enforce $\mathsf{Fault}(b') \subseteq \mathsf{Fault}(b)$, allowing Undefined Behavior (`Val.lessdef` or double-move faults) to be eliminated. Backward WP transport requires $\mathsf{Fault}(b) \subseteq \mathsf{Fault}(b')$ and agreement on non-faulting traces. Upstream `rustc` (`ssa.rs`, `gvn.rs`) ignores `Operand::Move` deinitialization, whereas `Trusted.MirSemantics.evalOperandToSlot` and `lean-miri`'s `OperandMachine.evalOperand` (`deinitMovedPlace = true`) set non-ZST moved slots to uninitialized. Adapting `SsaLocals` / `StorageRemover` unmodified turns double-move UB into valid `copy` instructions. Certified `MoveToCopy` requires an intra-statement operand-sequential bitmask check (`checkNoSubsequentReadBeforeReinit`) proving no non-ZST `move` reaches a subsequent read before re-assignment or `StorageLive`/`StorageDead`, while accepting RHS moves (`D7a`), self-moves (`D8`), and inhabited ZSTs (`D9`/`D12`).
2. **Safe Storage Erasure (`checkStorageSafe`) & Loop Resets:** `Trusted.MirSemantics.evalStatement` faults `.unsupported` on `StorageDead 0` and `.undefined` on accessing `.dead` locals, while `StorageLive k` resets non-ZST `locals[k]` to `.live none` on each iteration. `RemoveStorageMarkers` is unsound if `_0` hits `StorageDead`, a dead local is accessed, a local is address-taken (`&`/`*`), or a loop uses `StorageLive` to re-uninitialize `locals[k]`.
3. **Blazy–Demange–Pichardie `[pre, post]` Dominance & `Freeze` GVN/CSE:** Validating a dominator tree in Pass 1 Lean 4 (`Init.*` only, zero `._unsafe_rec`, zero `omega`) reduces to an $O(|V| + |E|)$ RPO/`idom`/`[pre, post]` check supporting $O(1)$ dominance (`pre[u] <= pre[v] && post[v] <= post[u]`). Sound MIR CSE requires `strict = true` equality (no `Val.lessdef`), kill-free paths, fault equivalence on trapping/checked ops, and `gvn.rs:831-864`'s triple shared-deref gate: `Mutability::Not`, `Ty::is_freeze`, and `!ty_may_have_ref`.
4. **Two-Tier 1-Trip Guarded-Preheader LICM:** Unguarded hoisting of trapping or checked ops (`div`, `rem`, `*Unchecked`, `Assert`) is backward-*sound* ($\mathsf{Fault}(b) \subseteq \mathsf{Fault}(b')$) yet *incomplete* on zero-trip loops (e.g., empty slices with `d == 0`). Hoisting total pure rvalues unconditionally while rotating fallible ops into a 1-trip guarded preheader (`if loopCond { hoisted; loop { ... } }`) preserves bidirectional WP equivalence ($\mathsf{wpState}\;b'\;Q \iff \mathsf{wpState}\;b\;Q$).

---

## Applicability

These findings govern certified MIR proof-compression modules in Anneal's `theory/` layer targeting `Trusted.MirAst` and `Trusted.MirSemantics` at `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, anchored in Pass 2 via `Trusted.Correspondence` to `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (pinning `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` and `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`). Compiler rules derive from `rust-lang/rust@8144389c` (`ssa.rs`, `gvn.rs`, `remove_storage_markers.rs`, `ty/util.rs`), `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc` (`CSEdomain.v`, `CSE.v`), Blazy–Demange–Pichardie (ITP 2015), and Monniaux–Six (LCTES 2021). All Lean 4 checkers target `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) under Pass 1 audit constraints (`trusted/audit/TrustedBoundary.lean:442-596`): `prelude` + the locked 51-module `Init.*` foundation (`Std.*`/`Lean.*`/`Init.Omega` banned), pure tactics plus `@[irreducible]` (`sorry`, `omega`, `bv_decide`, `native_decide`, `partial`, `._unsafe_rec`, `set_option` banned), and strict statement-origin separation (obligations mention only `Init.*`, `Trusted.*`, and `Mir.*`).

Adjacent corpus reports cover complementary seams: `lean-miri-interpreter-hooks-move-deinit-and-provenance-fragments` (`InitSubsumes` forward simulation), `bidirectional-mir-minissa-refinement-and-anneal-vc-transport` (`HybridTrace` `MiniSSA`), `rustc-mir-optimization-passes-semantics-soundness-and-value` (`inner_optimized_mir` catalog), and `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses` (partial SROA over `UnsafeCell`).

---

## Findings

### 1. Backward Verification Polarity vs. Forward Compiler Refinement

`Basis: source + derived`

In `Trusted.MirSemantics` (`trusted/lean/Trusted/MirSemantics.lean:332-340, 1646-1676`), `evalStep` returns `StepResult State TerminalOut := .step next | .done out | .fault k` with `FaultKind := .undefined | .unsupported`. Both fault kinds falsify `WellFormed`:

```lean
noncomputable def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))
```

In `theory/Anneal/MirWp.lean:69-92`, `wpState` instantiates `wpOutcomeState` with `onFault := fun _ => False`, and `wellFormed_and_spec_of_wp` (`WpSoundnessClaim`) bridges `wpProg` to `SatisfiesPost`. For an untrusted preprocessor rewriting `b` to `b'` certified by `checkPreproc b b' cert = true`, backward transport `wpState (replaceBody p defId b') fuel' s₀ post -> wpState p (liftFuel cert fuel') s₀ post` reverses compiler polarity:

| Property | Forward Compilation (`b -> b'`) | Backward Verification (`wp(b') -> wp(b)`) | Effect on Fault-Erasing Transforms |
| :--- | :--- | :--- | :--- |
| **Observable traces** | $\mathsf{Beh}_{\neg\text{ub}}(b') \subseteq \mathsf{Beh}(b)$ | $\mathsf{Beh}(b) \subseteq \mathsf{Beh}(b')$ | `b'` must admit every terminating outcome of `b`. |
| **Fault inclusion** | $\mathsf{Fault}(b') \subseteq \mathsf{Fault}(b)$ | $\mathsf{Fault}(b) \subseteq \mathsf{Fault}(b')$ | `b'` may fault *more* than `b`, never *less*. |
| **`CompCert` `Val.lessdef`** (`CSEdomain.v:35, 173-176`) | `Eq l false r` (`Vundef <= v`): substitutes `v` for `Vundef`. | **Unsound unless `strict = true`:** hides `.undefined` on `.live none`. | CSE must enforce strict value and fault equality. |
| **Unused trapping op (`1 / 0`)** | Elidable (source UB licenses any target). | **Unsound unless non-UB proved:** dropping `.div`/`.rem` hides UB. | Dead trapping ops need non-UB witnesses before erasure. |

In `AbsInt/CompCert@2685140b` (`backend/CSEdomain.v:34-35, 167-176`; `backend/CSE.v:119-125, 165-169`), `Eq l strict r` mixes strict equations (`strict = true`) with `Val.lessdef` (`strict = false`) via `find_valnum_rhs'`. That suffices for forward compilation, but under backward transport `strict = false` lets `b'` verify even when `b` dereferenced uninitialized state.

---

### 2. The `deinitMovedPlace = true` Soundness Trap in `SsaLocals`, `MaybeUninitializedLocals`, and `GVN`

`Basis: source + derived`

#### 2.1 Upstream `rustc` vs. $M_{\text{anneal}}$ / `lean-miri`

At `rust-lang/rust@8144389c`, `compiler/rustc_middle/src/mir/syntax.rs` notes `Operand::Move(place)` *may* overwrite `place` with `uninit` bytes (`UCG#188`), while `eval_operand` skips move invalidation outside `Call` arguments. Four components of `rustc`'s SSA/GVN pipeline ignore move deinitialization:
1. `SsaVisitor::visit_local` (`ssa.rs:228-253`) lumps `NonMutatingUseContext::Move` under `PlaceContext::NonMutatingUse(_)`, keeping moved locals in `Set1::One(_)`.
2. `compute_copy_classes` (`ssa.rs:300-347`) merges `Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)` identically (`copies[local] = copies[rhs]`).
3. `MaybeUninitializedLocals::apply_primary_statement_effect` (`ssa.rs:421-440`) updates uninitialization on `Assign`, `StorageLive`, and `StorageDead`, omitting `Operand::Move`.
4. `StorageRemover::visit_operand` (`gvn.rs:2159-2166`) rewrites `Operand::Move(place)` to `Operand::Copy(place)` across `reused_locals`.

By contrast, `Trusted.MirSemantics.evalOperandToSlot` (`MirSemantics.lean:949-977`)—anchored to `vendor/lean-miri/Miri/Interpreter/OperandMachine.lean:20, 92-135` (`deinitMovedPlace = true`)—deinitializes non-ZST local slots immediately upon evaluating `.move`:

```lean
noncomputable def liveUninitSlot (ty : MirTy) : LocalSlot :=
  match ty with
  | .unit => .live (some .unit)
  | .enum ety => if isZstEnumTy ety then .live (some (.enumVal ety 0)) else .live none
  | _ => .live none

-- Inside evalOperandToSlot (MirSemantics.lean:961-972):
| .move place =>
  if !place.projection.isEmpty then .error .unsupported
  else match getElem? bodyLocals place.localId, getElem? locals place.localId with
  | some ty, some (.live optVal) =>
    match setElem? locals place.localId (liveUninitSlot ty) with
    | some locals' => .ok (ty, optVal, locals')
    | none => .error .unsupported
  | some _, some .dead => .error .undefined
  | _, _ => .error .unsupported
```

`evalRvalue` (`MirSemantics.lean:1252-1261`) threads `locals` left-to-right from `lhs` into `rhs` inside `.binaryOp`, and `evalStatement` (`MirSemantics.lean:1413-1418`) evaluates the full RHS *before* `writePlace` updates `dst`. Seven Pass 2 correspondence canaries in `Trusted/Correspondence.lean:2802-3029` pin this exact semantics:

| Canary (`Trusted.Correspondence`) | Program Shape | Outcome ($M_{\text{anneal}}$ & $M_{\text{ref}}$) | Effect of Unguarded `SsaLocals` / `Move -> Copy` |
| :--- | :--- | :--- | :--- |
| **`D6`** (`progUseAfterMoveD6`) | `_2 = move _1; _0 = copy _1` (`u32`) | `.fault .undefined` (`.ub`) | Rewrites UB to `.returned 42` (**UNSOUND**). |
| **`D7a`** (`progBinOpCopyThenMoveD7a`) | `_0 = Add(copy _1, move _1)` (`u32`) | **`.returned 84`** (`WellFormed`) | Valid to rewrite `move _1 -> copy _1`. |
| **`D7b`** (`progBinOpMoveThenCopyD7b`) | `_0 = Add(move _1, copy _1)` (`u32`) | **`.fault .undefined`** (`.ub`) | Rewrites intra-statement UB to `.returned 84` (**UNSOUND**). |
| **`D7c`** (`progBinOpMoveThenMoveD7c`) | `_0 = Add(move _1, move _1)` (`u32`) | **`.fault .undefined`** (`.ub`) | Rewrites intra-statement UB to `.returned 84` (**UNSOUND**). |
| **`D8`** (`progSelfMoveD8`) | `_1 = move _1; _0 = copy _1` (`u32`) | **`.returned 42`** (`WellFormed`) | `writePlace` reinitializes `_1` after RHS eval (valid!). |
| **`D9`** (`progMoveUnitZstD9`) | `_2 = move _1; _0 = copy _1` (`()`) | **`.returned .unit`** (`WellFormed`) | `liveUninitSlot .unit` stays `.live (some .unit)`. |
| **`D12`** (`progZstSingleEnumMoveAndDiscr`) | `_2 = move _1; _0 = discr(_1)` (1-var ZST) | **`.returned 42`** (`WellFormed`) | `Variants::Single { index: 0 }` stays initialized after `move`. |

#### 2.2 Counterexamples Breaking Naive `SsaLocals` + `GVN`

1. **Cross-statement move + GVN reuse:** Given `_2 = Add(copy _1, 1); _3 = Mul(move _2, 4); _4 = Add(copy _1, 1); _5 = copy _2`, `rustc` marks `_2` SSA (`1` assignment) and rewrites `_4 = copy _2` while `StorageRemover` turns `move _2 -> copy _2`. `b'` verifies cleanly, masking the `.undefined` fault at `_5 = copy _2` in `b`.
2. **Intra-statement ordering (`D7b`) vs. self-move (`D8`):** Coarse per-statement liveness either accepts `_0 = Add(move _1, copy _1)` (missing `lhs` deinit before `rhs` read) or rejects `_1 = move _1; _0 = copy _1` (missing that `writePlace` runs after RHS evaluation).

#### 2.3 Pass-1 Certificate Checker: `checkNoSubsequentReadBeforeReinit`

To make `MoveToCopy` (`Operand.move -> Operand.copy`) exact bisimulation in Pass 1 Lean 4 (`Init.*` only, zero `._unsafe_rec`, shift guard `k <= 512`), an untrusted pass emits `movedOutIn : List Nat` (bit `k = 1` iff local `k` may hold a post-move hole at block entry). The Lean checker threads `movedOut` strictly in `evalStatement` order:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Trusted.MirAst

namespace Anneal.MirPreproc.MoveCheck

open Trusted.MirAst

def isInhabitedZstTy : MirTy → Bool
  | .unit => true
  | .enum ety => match ety.tagRepr, ety.discriminants with
    | .zeroSized, [_] => true
    | _, _ => false
  | _ => false

def maskBit (k : Nat) : Nat := if Nat.ble k 512 then Nat.shiftLeft 1 k else 0
def setBit (m k : Nat) : Nat := Nat.lor m (maskBit k)
def clearBit (m k : Nat) : Nat := Nat.land m (Nat.xor m (Nat.land m (maskBit k)))
def maskSubset (sub sup : Nat) : Bool := Nat.beq (Nat.land sub sup) sub

def stepOperand (locals : List MirTy) (movedOut : Nat) : Operand → Option Nat
  | .constant _ => some movedOut
  | .copy p =>
    if !p.projection.isEmpty || Nat.testBit movedOut p.localId then none else some movedOut
  | .move p =>
    if !p.projection.isEmpty || Nat.testBit movedOut p.localId then none
    else match locals[p.localId]? with
      | none => none
      | some ty =>
        if !Nat.ble p.localId 512 then none
        else if isInhabitedZstTy ty then some movedOut else some (setBit movedOut p.localId)

def stepRvalue (locals : List MirTy) (movedOut : Nat) : Rvalue → Option Nat
  | .use op | .unaryOp _ op => stepOperand locals movedOut op
  | .binaryOp _ lhs rhs =>
    match stepOperand locals movedOut lhs with
    | none => none | some m1 => stepOperand locals m1 rhs
  | .discriminant p =>
    if !p.projection.isEmpty || Nat.testBit movedOut p.localId then none else some movedOut
  | .aggregateTuple ops =>
    ops.foldl (fun acc? op => match acc? with
      | none => none | some m => stepOperand locals m op) (some movedOut)
  | _ => none

def stepStmt (locals : List MirTy) (movedOut : Nat) : StatementKind → Option Nat
  | .nop => some movedOut
  | .storageLive k | .storageDead k =>
    if !Nat.ble k 512 then none else some (clearBit movedOut k)
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else match stepRvalue locals movedOut rv with
      | none => none | some m1 => some (clearBit m1 dst.localId)
  | .unsupported => none

end Anneal.MirPreproc.MoveCheck
```

At terminators, `stepTerminator` steps `.switchInt discr`, rejects `.return_` when `Nat.testBit movedOut 0 = true`, and checks `maskSubset outMask cert[succ] = true` (starting from `cert[0] = 0`). When `checkNoSubsequentReadBeforeReinit b cert = true`, any reachable state reading local `k` in `b` either reads a non-moved local or faults identically in `b` and `b'` (from entry/`.storageLive` uninit or `.dead`), yielding **exact bisimulation** (`moveToCopy_bisim`) across `D6`–`D12`.

---

### 3. Safe `StorageLive` / `StorageDead` Erasure (`checkStorageSafe`)

`Basis: source + derived`

`Trusted.MirSemantics.evalStatement` (`MirSemantics.lean:1376-1405`) enforces three storage rules: (1) `.storageDead 0` faults `.unsupported` (`CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim`, lines 2245-2268); (2) `.storageDead k` (`k != 0`) sets `locals[k] := .dead`, making subsequent accesses fault `.undefined` (`CanaryNegativeUbStorageDeadReadAnnealClaim`, lines 2221-2242); (3) `.storageLive k` resets non-ZST `locals[k]` to `.live none`.

Removing markers unconditionally (`remove_storage_markers.rs:16-25`) or when `MaybeUninitialized` holds at reuse (`gvn.rs:166-179, 2181-2220`) fails backward verification along **four vectors**:
- **S1 (Dead-local access):** Accessing `_k` after `StorageDead _k` faults `.undefined` in `b` but succeeds in `b'`.
- **S2 (`StorageDead 0`):** Erasing `StorageDead 0` suppresses an `.unsupported` fault.
- **S3 (Loop-carried uninit wipe):** In `bb1: StorageLive(_2); if c { ... } else { _3 = copy _2; } _2 = 1; goto bb1`, iteration `0` sets `_2 := 1`, then iteration `1` resets `_2 := .live none` via `StorageLive(_2)` so the `else` branch faults `.undefined`. Because `StorageLive(_2)` appears once syntactically, `StorageLiveLocals::has_single_storage` (`ssa.rs:391`) returns `true` and leaks iteration `0`'s value!
- **S4 (Address-taken locals):** If `ref`/`addressOf` takes `&k`, `StorageDead(k)` invalidates dangling pointers (`make_local_dead`).

**Certified Erasure (`checkStorageSafe`):** To erase `StorageLive`/`StorageDead` for local set `S`, a Pass-1 verifier checks per-block bitmasks `(deadMaskIn, uninitMaskIn)`: (1) `0 ∉ S`, no `k ∈ S` is address-taken, and no read/write touches `k ∈ S` with `deadMask[k] == 1`; (2) `bb0` initializes non-arg, non-return locals as `.dead` (or uninit), `StorageLive(k)` sets `deadMask[k] := 0, uninitMask[k] := 1` (if non-ZST), `Assign` clears `uninitMask[dst] := 0`, and `StorageDead(k)` sets `deadMask[k] := 1`; (3) for **S3**, rejecting any read of `k ∈ S` while `uninitMask[k] == 1` guarantees erasing `StorageLive(k)` suppresses zero loop-reset faults, while `liftFuel` adds `+1` per erased marker.

---

### 4. Blazy–Demange–Pichardie `[pre, post]` Dominance & `Ty::is_freeze` GVN/CSE

`Basis: source + derived`

#### 4.1 $O(1)$ Dominance Validation via `[pre, post]` Intervals (ITP 2015)

To validate dominance in Pass 1 without implementing Lengauer–Tarjan in Lean, the preprocessor emits `(rpo, idom, pre, post : List Nat)` plus DFS euler-tour `dfsTrace : List (Nat × Bool)` over reachable blocks (`entry = 0`), following Blazy, Demange, and Pichardie (ITP 2015, DOI `10.1007/978-3-319-22102-1_6`):
1. **Acyclic `0`-rooted tree (`wfDomTree`):** Verify `rpo[0] == 0`, `idom[0] == 0`, and `rpo[idom[b]] < rpo[b]` for reachable `b ≠ 0`.
2. **DFS interval nesting (`wfPrePost`):** Replay `dfsTrace` via `List.foldl` tracking `(parentBb, enterTime)` stack and `clock`: `(b, true)` checks `pre[b] == clock` and `idom[b] == parentBb`; `(b, false)` checks `post[b] == clock` and pops `b`. This $O(|V|)$ pass proves `Nat.ble pre[u] pre[v] && Nat.ble post[v] post[u]` iff `u` is an `idom`-ancestor of `v`.
3. **Edge-dominance check (`checkEdgeDom`):** For each reachable edge `u -> v` (`v ≠ 0`), verify `dom (idom[v]) u == true` and either `rpo[u] < rpo[v]` or back-edge `dom v u == true`. By path induction, `dom u v = true` proves `u` dominates `v` in $O(1)$ GMP `Nat.ble`.

#### 4.2 Four Soundness Conditions for Backward GVN/CSE (`checkFreezeCse`)

Rewriting `bb2[i2]: _b = expr` to `_b = Operand.copy _a` from dominating `bb1[i1]: _a = expr` preserves backward WP (`wpState b' Q -> wpState b Q`) iff:
1. **Strict Dominance:** `(bb1 == bb2 ∧ i1 < i2)` or `(bb1 ≠ bb2 ∧ dom bb1 bb2 == true)`.
2. **Kill-Free Dominated Subgraph:** Along all blocks `w` reachable from `bb1` to `bb2` (all dominated by `bb1`), neither `_a` nor operands of `expr` are assigned, non-ZST moved (`MoveToCopy` active), or hit by `StorageLive`/`StorageDead`.
3. **Triple Shared-Deref Gate (`gvn.rs:831-864`, `ty/util.rs:1183-1195`):** Deduplicating `*_r` across statements/calls requires all three `VnState::project` guards:
   - *(a) Shared mutability:* `_r` is `&T` (`Mutability::Not` / `.shared`), never `&mut T` or `*const`/`*mut`.
   - *(b) `Ty::is_freeze` (`UnsafeCell` hazard):* `pointeeTy.is_freeze` (`ty_util.rs:1183-1185`) holds, blocking `&Cell<u32>` mutation across shared calls (`let a = r.get(); mutate(r); let b = r.get()`). At `joshlf/anneal@20aa2043`, modeled non-`.unsupported` `MirTy` constructors are trivially `Freeze` (`ty_util.rs:1191-1206`); future `MirTy.adt` nodes must carry an audited `isFreeze : Bool` flag failing closed on `UnsafeCell`.
   - *(c) `!ty_may_have_ref` (`gvn.rs:840-856, 1710-1761`):* When `pointeeTy` contains references (`a : &&T`), two derefs produce distinct borrows and Tree Borrows retag provenances; merging them illegally extends the first tag's lifetime.
4. **Fault Preservation on Trapping & Checked Ops:** Since `bb1` dominates `bb2`, reaching `(bb2, i2)` ensures `(bb1, i1)` succeeded without faulting (`y != 0`, no signed `MIN / -1`, no overflow). Replacing dominated `Div`/`Rem`/`*Unchecked` with `copy _a` preserves both values and faults; replacing a dominated checked `Assert(!_t2.1)` with `Goto` is sound once `_t1.1 == false` dominates `bb2`.

---

### 5. 1-Trip Guarded-Preheader LICM & Zero-Trip Loop Completeness

`Basis: derived + source`

In forward verified compilation (Monniaux & Six, LCTES 2021, DOI `10.1145/3461648.3463850`), unguarded hoisting requires non-trapping `can_speculate` ops so zero-trip paths do not crash. Under Anneal's backward WP (`wpState b' Q -> wpState b Q`), unguarded hoisting of trapping ops is **sound** ($\mathsf{Fault}(b) \subseteq \mathsf{Fault}(b')$) **yet incomplete** on guarded zero-trip loops:

```rust
pub fn scale_chunks(xs: &[u32], k: u32, d: u32) -> u32 {
    let mut acc = 0;
    for c in xs.chunks_exact(4) { acc = acc.wrapping_add(c[0].wrapping_mul(k / d)); }
    acc
}
```

When `xs.len() < 4` and `d == 0`, original MIR `b` executes `0` trips and returns `0`; unguarded hoisting of `k / d` makes `b'` fault `.undefined`, rejecting safe code.

**Two-Tier Guarded-Preheader LICM (`checkGuardedLicm`):**
1. **Unconditional Preheader (`isTotalPureRvalue = true`):** Hoist ops guaranteed not to fault on live initialized operands—constants, copies of live pre-loop locals, wrapping `.binaryOp` (`.add`, `.sub`, `.mul`, bitwise ops, comparisons, masked `.shl`/`.shr` per `MirSemantics.lean:1034-1090`), and `.unaryOp .not`/signed `.neg`—into `bb_pre`.
2. **1-Trip Guarded Preheader (Loop Rotation):** Hoist loop-invariant `.div`, `.rem`, `*Unchecked`, checked `*WithOverflow + Assert`, and `&Freeze` derefs guarded by loop entry into a cloned entry branch (`bb_entry: switchInt loopCond -> [true: bb_guard_preheader, false: bb_exit]`; `bb_guard_preheader` runs the hoisted op once and jumps to `bb_loop_body`, which merges back to `bb_loop_hdr`). Each hoisted evaluation in `b'` corresponds 1-to-1 with trip `0` in `b`, preserving exact equivalence ($\mathsf{wpState}\;b'\;Q \iff \mathsf{wpState}\;b\;Q$). Removing $O(N)$ per-trip steps requires scaling `liftFuel` by loop trip bound or using fuel-independent `LoopInv` cutpoints.

---

### 6. Anneal `theory/` Rubric Evaluation (`T1`, `P1`–`P5`, `C1`–`C2`)

`Basis: derived`

| Mechanism | (T1) 0-TCB Bridge | (P1) Spec Audit | (P2) Locality | (P3) Kernel / `<50 ms` LSP | (P4) Hetero. Comp. | (P5) Failure Legibility | (C1–C2) Minimality & Verdict |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`MoveToCopy`** (`checkNoSubsequentReadBeforeReinit`) | **0-TCB:** Pure `Init.Data.Nat.Bitwise.Basic` checker in `theory/`. | **High:** Zero change to `Specs`; preserves `D6`–`D12`. | **High:** Block-local bitmask checks isolate temp edits. | **Very High:** GMP `Nat.land`/`testBit` evaluates `<1 ms` by `rfl`. | **High:** Exact on ZSTs (`D9`/`D12`) & self-moves (`D8`); fails closed on projections. | **High:** Pinpoints `(bb, stmtIdx, localId)` of illegal post-move read. | **Adopt (P0):** Mandatory gate before SSA/GVN under `deinitMovedPlace = true`. |
| **`StorageSafe`** (`checkStorageSafe`) | **0-TCB:** Dual bitmask checker in `theory/`. | **High:** Strips `~50%` of dead/live boilerplate in lifted traces. | **High:** Single-local marker changes stay local. | **Very High:** Cuts `evalStatement` steps & `List` slot updates. | **Med-High:** Rejects `&`/`*`-taken locals and catches loop reset Vector S3. | **High:** Distinguishes `StorageDead 0` vs. dead access vs. loop reset. | **Adopt (P0):** Merge into unified `LivePass` bitmask check with `MoveToCopy`. |
| **`FreezeCSE` + `[pre, post]` Dom** | **0-TCB now; minimal later:** 0-TCB for `20aa2043`; needs audited `MirTy.isFreeze` on future ADTs. | **High:** Eliminates redundant subexpressions & duplicate `Assert`s. | **High:** `[pre, post]` tree updates only on CFG shape edits. | **Very High:** $O(1)$ `Nat.ble` dom tests; sub-ms kernel checks. | **High:** Protects `UnsafeCell` (`isFreeze`) and Tree Borrows `&&T` (`!tyMayHaveRef`). | **High:** Names exact clobbering stmt or `!Freeze` pointee type. | **Adopt (P1):** Share Blazy `[pre, post]` certificate with Stackifier CFG structuring. |
| **`GuardedLICM`** (`if cond { pre; ... }`) | **0-TCB:** Loop-rotation theorem proved in `theory/`. | **High:** Simplifies loop invariants by lifting pure defs. | **High:** Separates loop-invariant side conditions from induction step. | **High:** Evaluates hoisted `div`/bitvec terms once instead of per trip. | **High:** Preserves 0-trip slice/iterator completeness; respects `!Freeze`/calls. | **High:** Distinguishes entry-guard failures from loop-body failures. | **Adopt (P1):** Use for loops with invariant checked/div arithmetic. |

#### Conceptual Minimality Audit (`C1–C2`): Refuting Four Premature Collapses

1. **Collapsing `MoveToCopy` into `SsaLocals` without `checkNoSubsequentReadBeforeReinit`:** Refuted by `D6` (`_2 = move _1; _0 = copy _1`) and `D7b` (`_0 = Add(move _1, copy _1)`), where unguarded conversion erases `.undefined`.
2. **Collapsing `&T` CSE without BOTH `isFreeze` and `!tyMayHaveRef`:** Refuted by `&Cell<u32>` (interior mutability) and `a : &&T` (`gvn.rs:840-856`, lifetime and Tree Borrows retag extension).
3. **Collapsing `StorageLive` safety into syntactic single-occurrence (`StorageLiveLocals::has_single_storage`, `ssa.rs:391`):** Refuted by Vector S3 inside a loop header, where one syntactic `StorageLive` resets `locals[k]` dynamically on iteration `1`.
4. **Collapsing `GuardedLICM` into unguarded preheaders:** Refuted by `scale_chunks(&[], 10, 0)` losing completeness on zero-trip loops.

---

## Boundaries

- **Known not to apply:**
  - Applying `rustc`'s `SsaLocals` (`ssa.rs:228-253`), `MaybeUninitializedLocals` (`ssa.rs:400-454`), or `StorageRemover` (`gvn.rs:2159-2166`) unmodified for backward verification under `deinitMovedPlace = true` **is known not to apply**, because it turns double-move UB into defined execution.
  - Using `CompCert` `CSEdomain.v` `strict = false` (`Val.lessdef`) equations in backward WP transport **is known not to apply**, because refining `Vundef` masks source UB.
  - Applying shared-borrow GVN/CSE when `!pointeeTy.is_freeze` (`UnsafeCell`) or `tyMayHaveRef pointeeTy == true` (`&&T`) **is known not to apply**.
  - Hoisting trapping or checked operations into an unguarded preheader **is known not to apply** when zero-trip completeness is required.
  - Transporting finite-fuel `wpState` across LICM with constant additive fuel slack alone **is known not to apply** without a loop-bound fuel multiplier or fuel-independent `WellFormed` / `LoopInv` cutpoints.
- **Unsupported:**
  - Inside `Trusted.MirAst` and `Trusted.MirSemantics` at `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, non-empty `Place.projection` (`.deref`, `.field`), `Rvalue.ref`, `Rvalue.addressOf`, `TerminatorKind.assert`, `TerminatorKind.call`, and general `MirTy.adt` structs/`UnsafeCell` are **unsupported** (`evalStatement`/`evalRvalue`/`evalTerminator` step to `.fault .unsupported`), so the `&Freeze` deref and ADT rules characterize the contract required once those constructs are admitted in `Trusted.*`.
  - Using `omega`, `bv_decide`, `native_decide`, `partial` (`._unsafe_rec`), `Std.*`, or `Lean.*` in Pass 1 `theory/` checkers is **unsupported** (`trusted/audit/TrustedBoundary.lean:442-596`).
- **Not examined:**
  - Cross-thread `Atomic*` ordering, volatile MMIO accesses, and IEEE-754 floating-point NaN-payload / `-0.0` CSE normalization were **not examined**.
  - Runtime benchmark measurements of `MoveToCopy` + `FreezeCSE` on multi-hundred-block crates inside `anneal-audit` were **not examined**.
- **Unknown:**
  - Whether upstream `rust-lang/rust` resolution of `UCG#188` will standardize rvalue `Operand::Move` deinitialization for scalars or confine it to in-place `Call` arguments remains **unknown**.

---

## Evidence

1. **`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` (`Basis: source`):**
   - `trusted/lean/Trusted/MirAst.lean:177-315, 448-625`: `Mutability`, `EnumTagRepr`, `MirTy`, `ProjectionElem`, `Operand`, `Rvalue`.
   - `trusted/lean/Trusted/MirSemantics.lean:61-149, 332-340, 916-1091, 1240-1427, 1646-1676, 2219-2269`: `liveUninitSlot`, `evalOperandToSlot`, `evalRvalue`, `writePlace`, `evalStatement`, `WellFormed`, `SatisfiesPost`, `CanaryNegativeUbStorageDeadReadAnnealClaim`, `CanaryNegativeUbStorageDeadReturnPlaceAnnealClaim`.
   - `trusted/correspondence/Trusted/Correspondence.lean:60-76, 2794-3029`: `M_anneal` ↔ `M_ref` correspondence and canaries `D6`–`D12`.
   - `theory/Anneal/MirWp.lean:69-92` and `trusted/audit/TrustedBoundary.lean:442-596`: `wpOutcomeState`, `wpState`, Pass 1 syntax/tactic allowlists.
2. **`proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Basis: source`):**
   - `Miri/Interpreter/OperandMachine.lean:10-21, 92-135`: `Hooks.deinitMovedPlace : Bool` and `evalOperand`.
3. **`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd` (`Basis: source + documentation`):**
   - `compiler/rustc_mir_transform/src/ssa.rs:20-101, 228-253, 300-347, 363-455`: `SsaLocals`, `SsaVisitor::visit_local`, `compute_copy_classes`, `StorageLiveLocals`, `MaybeUninitializedLocals`.
   - `compiler/rustc_mir_transform/src/gvn.rs:129-188, 823-865, 1710-1761, 2077-2221`: `GVN::run_pass`, `VnState::project`, `ty_may_have_ref`, `StorageRemover`, `StorageChecker`.
   - `compiler/rustc_mir_transform/src/remove_storage_markers.rs:1-27` and `compiler/rustc_middle/src/ty/util.rs:1176-1221` (`Ty::is_freeze`).
   - `compiler/rustc_const_eval/src/interpret/operand.rs` & `compiler/rustc_middle/src/mir/syntax.rs`: `Operand::Move` `FIXME` and `UCG#188`.
4. **`AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` (`Basis: source`):** `backend/CSEdomain.v:29-36, 157-186` (`Eq`, `Val.lessdef`), `backend/CSE.v:108-126, 165-170, 524-580` (`find_valnum_rhs'`, `transfer`).
5. **Publications (`Basis: normative + source`):** Blazy–Demange–Pichardie, ITP 2015, DOI `10.1007/978-3-319-22102-1_6`; Monniaux–Six, LCTES 2021, DOI `10.1145/3461648.3463850` (arXiv `2105.01344`).

---

## Revalidation

1. **Upstream `rustc` `SsaLocals` / `GVN` / `is_freeze` drift check:**
   ```bash
   BASE="https://raw.githubusercontent.com/rust-lang/rust/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_mir_transform/src"
   curl --http1.1 -fsSL "${BASE}/ssa.rs" | grep -nE "NonMutatingUse|Move|MaybeUninitializedLocals"
   curl --http1.1 -fsSL "${BASE}/gvn.rs" | grep -nE "is_freeze|ty_may_have_ref|reused_locals"
   ```
2. **Anneal `MirSemantics` move-deinit & `MirTy` check:**
   ```bash
   curl --http1.1 -fsSL "https://raw.githubusercontent.com/joshlf/anneal/20aa204315cd36aaf944778b7d33c0d609ced8e8/trusted/lean/Trusted/MirSemantics.lean" | grep -nE "evalOperandToSlot|liveUninitSlot|storageLive|storageDead"
   ```
   Confirm `evalOperandToSlot` still deinitializes non-ZST moves and check if `MirAst.MirTy` adds `.adt` (needing `isFreeze : Bool` before `&T` CSE).
3. **Pass-1 `MoveCheck` canary probe:** Evaluate `stepStmt` / `stepRvalue` (Section 2.3) in Lean `v4.34.1` on `progUseAfterMoveD6`, `progBinOpCopyThenMoveD7a`, `progBinOpMoveThenCopyD7b`, `progSelfMoveD8`, and `progMoveUnitZstD9` (`Trusted/Correspondence.lean:2806-2970`), checking by `rfl` that `D6`/`D7b` return `none` and `D7a`/`D8`/`D9` return `some _`.
