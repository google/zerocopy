# Call-by-Name WHNF Pathology, CPS Midpoint Forcing, and Stack-Bounded Kernel Reduction in Proof Assistants

## Summary

In dependent-type proof assistants whose conversion checker reduces terms to weak head normal form (WHNF)—including Lean 4's C++ kernel (`lean::type_checker::whnf_core`), Lean 4's elaborator (`Lean.Meta.whnfImp`), and `Lean4Lean`—constructor applications $C\,e_1 \dots e_m$ are already WHNF values whose fields $e_i$ remain unreduced, and head $\beta$-reduction substitutes arguments call-by-name. When binary exponentiation (`runPow2 d s := runPow2 (d - 1) (runPow2 (d - 1) s)`) iterates a state transition $2^d$ times over a multi-field record and radix-2 binary trie (`PTree`), constructor laziness converts an intended $O(d)$ recursion into an $\Omega(2^d)$ active call-stack chain that trips Lean 4's default `maxRecDepth = 512` at $d = 6$ ($64$ steps).

Three common strictness idioms fail even earlier (`d = 4` or `d = 5`): wrapping projections inside constructors (`MachState.mk (strictNat s.f) ...`), matching the outer record in direct style (`matchStrict (runPow2 d (matchStrict (runPow2 d s)))`), and threading full-tree Continuation-Passing Style (`forcePTree : PTree → (PTree → α) → α`) directly around the continuation `k` (which holds $\Theta(d \cdot |T|)$ frames on the stack during `k`).

Restoring $O(d + m + \operatorname{height}(T))$ stack depth without `set_option maxRecDepth` or trusted native evaluation (`Lean.ofReduceBool`) requires **two-tier shallow CPS midpoint forcing**:
1. **Bottom-up value-returning state normalization (`strictMachState : MachState → MachState` and `forcePTree : PTree → PTree`):** Force each `Nat` field via `forceNatVal n k := match n with | 0 => k 0 | m + 1 => k (m + 1)` (severing prior AST pointers into a 2-node literal constructor) and rebuild each trie subtree via shallow `withForcedPTree`, returning a value so all field and trie stack frames pop on return.
2. **Single-eliminator CPS midpoint sequencing (`withForcedState (runPow2Forced d s) (fun sMid => runPow2Forced d sMid)`):** Pattern-match `strictMachState (runPow2Forced d s)` once as a recursor major premise so `whnf` completes the first $2^d$ steps and pops their frames before head $\beta$-reduction enters the second half.

On `leanprover/lean4` `v4.34.1` (`-Ddebug.skipKernelTC=false`, default `maxRecDepth = 512`), this pattern discharges $2^8 = 256$ coupled state-and-`PTree` steps by `rfl` at `193.5 MiB` RSS (`< 200 MiB`), scales linearly through $2^{10} = 1,024$ steps (`31.0 s`), and proves `runPow2Forced d s = runPow2Spec d s` with zero axioms (`[]`).

## Applicability

This report applies to computational reflection, operational-semantics stepping, and `rfl` conversion checking across five pinned upstream subjects:

1. **Lean 4 C++ kernel and Meta WHNF implementation** (`leanprover/lean4` at `badf11f93b505238d48439a6538dc2b395009453`): `src/kernel/type_checker.{h,cpp}`, `src/kernel/inductive.{h,cpp}`, `src/runtime/interrupt.{h,cpp}`, `src/runtime/stackinfo.cpp`, `src/Lean/Util/RecDepth.lean`, and `src/Lean/Meta/WHNF.lean`.
2. **Lean 4 `v4.34.1` release toolchain** (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), used for execution and `ru_maxrss` measurements via `lean -j1 -Ddebug.skipKernelTC=false -DwarningAsError=true` over `prelude` + `Init.Core`.
3. **Lean4Lean verified kernel typechecker** (`digama0/lean4lean` at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`): `Lean4Lean/TypeChecker.lean`, `Lean4Lean/Inductive/Reduce.lean`, and `Lean4Lean/FuelConfig.lean`.
4. **Rocq Prover kernel reduction engines** (`rocq-prover/rocq` at `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`): `kernel/reduction.ml`, `kernel/cClosure.ml`, `pretyping/cbv.ml`, `kernel/vconv.ml`, and `kernel/nativeconv.ml`.
5. **CompCert radix-2 binary trie finite maps** (`AbsInt/CompCert` at `2685140bf72c959446981fb99b5e44a8975021bc`, `lib/Maps.v`).

The inspected Lean 4 WHNF and recursor rules are identical across `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) and `badf11f93b505238d48439a6538dc2b395009453`, and match `Lean4Lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`) up to deterministic `FuelConfig` counters vs C++ stack guards. Baseline RSS figures (`~140 MiB` empty import) reflect `prelude` + `Init.Core` on `x86_64` Linux; importing full `Init` adds a fixed `~350 MiB` `.olean` image offset without changing asymptotic stack depth.

## Findings

### 1. Dual Stack Guards, Lazy Constructor WHNF, and $O(1)$ Numeral Unpacking in Lean 4

`Basis: source + execution`

Lean 4 checks definitional equality through two WHNF implementations with distinct recursion ceilings:

1. **Elaborator WHNF (`Lean.Meta.whnfImp`):** `src/Lean/Meta/WHNF.lean:1101–1125` wraps non-trivial calls in `withIncRecDepth` against `maxRecDepth` (`src/Lean/Util/RecDepth.lean:15–18`, default `512`), aborting with `maximum recursion depth has been reached` at depth `513`.
2. **C++ Kernel WHNF (`lean::type_checker::whnf` / `whnf_core`):** Every entry to `infer_type_core` (`src/kernel/type_checker.cpp:321–322`) and `whnf_core` (`L456–458`) enforces:
   - `scope_rec_depth guard;` (`src/runtime/interrupt.cpp:59–88`), bounding `g_rec_depth` by `g_kernel_rec_depth_factor * maxRecDepth = 16 * 512 = 8,192` (`L68`) and throwing `stack_space_exception("type checker")`;
   - `check_system("type checker: whnf", true)` (`L114–121`), calling `check_stack` (`src/runtime/stackinfo.cpp:115–121`) to compare `__builtin_frame_address(0)` against `RLIMIT_STACK` (`L62–70`).
   - `Lean4Lean` (`Lean4Lean/FuelConfig.lean:18–31`, `TypeChecker.lean:531–541`) replaces OS stack checks with explicit fuel (`whnf := 100000`, `recDepth := 50000`).

Three kernel reduction properties govern iterated state machines:
- **Constructors halt WHNF without evaluating fields:** In `type_checker::whnf_core` (`src/kernel/type_checker.cpp:499–529`), $e = C\,a_1 \dots a_m$ has constant head $f_0 = C$ with `!rec_info->is_recursor()` (`src/kernel/inductive.h:96`), so `reduce_recursor` returns `none_expr()`. In `type_checker::whnf` (`L718–730`), neither `reduce_nat` nor `unfold_definition` applies (`!info->has_value()` at `L547`), returning $C\,a_1 \dots a_m$ with every $a_i$ unevaluated.
- **Head $\beta$-reduction is call-by-name:** `whnf_core` (`L503–512`) substitutes raw argument ASTs $u_i$ into $\lambda$-bodies via `instantiate` without prior reduction.
- **Recursor $\iota$-reduction forces its major premise, and GMP `Nat` unpacking is $O(1)$:** `inductive_reduce_rec` (`src/kernel/inductive.h:90–135`; `Lean4Lean/Inductive/Reduce.lean:80–108`) evaluates `major = whnf(major)` (`L107`) *before* selecting a constructor rule (`L114`). When `major` is a GMP literal `Lit(natVal(v))` produced by `reduce_nat` (`type_checker.cpp:660–691`), `nat_lit_to_constructor` (`src/kernel/inductive.cpp:1357–1364`) constructs `mk_app(*g_nat_succ, mk_lit(literal(v - nat(1))))` for $v > 0$—a single `Nat.succ` node in $O(1)$ time and space rather than unary $O(v)$ allocation.

---

### 2. Asymptotic Collapse of Four Standard Iterated-Step Encodings (`runPow2`)

`Basis: source + derived + execution`

Let `stepMach : MachState → MachState` update $m$ scalar `Nat` fields and a radix-2 `PTree` (`empty | node (l : PTree) (o : Option Nat) (r : PTree)`), iterated $2^d$ times via `runPow2 d s`. Four natural encodings hit `maxRecDepth = 512` at small $d$:

1. **Encoding A — Unforced doubling (`runPow2 d s := runPow2 (d - 1) (runPow2 (d - 1) s)`):**
   Unfolding the outer spine $d$ times builds $2^d$ nested `stepMach` calls. When step $2^d$ tests `Nat.ble s.stepNo 1000000` (`reduce_bin_nat_pred`, `type_checker.cpp:650–658`), `reduce_proj` (`L432–442`) demands `whnf` of step $2^d - 1$, which demands step $2^d - 2$, pushing $\Theta(2^d)$ nested `whnfImp`/`whnf_core` frames simultaneously. On `v4.34.1`, `d = 5` ($32$ steps) passes (`0.597 s`), while `d = 6` ($64$ steps) fails with `maximum recursion depth has been reached`.
2. **Encoding B — Constructor-field wrapper (`wrapStrict s := MachState.mk (strictNat s.stepNo) ...`):**
   Because `wrapStrict t` unfolds directly to constructor head `MachState.mk`, `whnf` never enters `strictNat` until a downstream projection demands the field, adding extra `reduce_proj` + `strictNat` frames per step along the $\Theta(2^d)$ chain and failing earlier at `d = 5` (`0.609 s`).
3. **Encoding C — Direct-style outer match (`matchStrict (runPow2 d (matchStrict (runPow2 d s)))`):**
   Head $\beta$-reduction passes the midpoint `s_mid := matchStrict (runPow2 d s)` **by name** into the outer `runPow2 d`, which unfolds down $d$ levels to step $2^d$ before demanding `s_mid`, keeping outer frames live while chaining all $2^d$ steps (`d = 5` fails in `0.720 s`).
4. **Encoding D — Deep full-tree CPS (`forcePTreeDeep : PTree → (PTree → α) → α` around `k`):**
   ```lean
   def forcePTreeDeep {α : Type} : PTree → (PTree → α) → α
     | .empty, k => k .empty
     | .node l o r, k =>
       forcePTreeDeep l (fun fl =>
         forceOptNat o (fun fo =>
           forcePTreeDeep r (fun fr => k (.node fl fo fr))))
   ```
   Although this evaluates the midpoint before entering `k`, a 16-leaf binary trie ($|T| = 31$ nodes) chains $31$ continuations sequentially and invokes `k` (`runPow2 d sMid`) from the innermost leaf while all $\Theta(|T|)$ frames remain on the host C++/`MetaM` stack (which lacks tail-call elimination across RAII `scope_rec_depth` / `withIncRecDepth` guards). Stack depth grows as $\Theta(d \cdot (m + |T|))$, failing at `d = 4` ($16$ steps).

| Iterated-Step Encoding (`2^d` steps, 4 scalars + 16-slot `PTree`) | Peak Active WHNF Stack Depth | `d = 4` (`16`) | `d = 5` (`32`) | `d = 6` (`64`) | `d = 8` (`256`) |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **A. Unforced `runPow2`** | $\Theta(2^d)$ | PASS (`0.81 s`) | PASS (`0.60 s`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) |
| **B. Constructor-wrapped `wrapStrict`** | $\Theta(2^d)$ (larger constant) | PASS (`0.62 s`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) |
| **C. Direct-style `matchStrict`** | $\Theta(2^d)$ | PASS (`0.71 s`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) |
| **D. Deep full-tree CPS `forcePTreeDeep`** | $\Theta(d \cdot (m + \lvert T \rvert))$ | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) | FAIL (`maxRecDepth`) |
| **E. Two-tier shallow CPS midpoint forcing** | $\Theta(d + m + \operatorname{height}(T))$ | PASS (`1.33 s`, `147.3 MiB`) | PASS (`1.77 s`, `160.9 MiB`) | PASS (`2.19 s`, `173.2 MiB`) | PASS (`8.09 s`, `193.5 MiB`) |

---

### 3. Two-Tier Shallow CPS Midpoint Forcing and Exact Stack Recurrence

`Basis: source + derived + execution`

Bounding both stack depth and heap retention requires separating **intra-state normalization** (returning a concrete value so its frames pop) from **inter-step midpoint sequencing** (a single shallow recursor elimination):

```lean
inductive PTree where
  | empty : PTree
  | node  : PTree → Option Nat → PTree → PTree

def forceNatVal {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

def forceOptNat {α : Type} (o : Option Nat) (k : Option Nat → α) : α :=
  match o with
  | none => k none
  | some v => forceNatVal v (fun fv => k (some fv))

def withForcedPTree {α : Type} (t : PTree) (k : PTree → α) : α :=
  match t with
  | .empty => k .empty
  | .node l o r => k (.node l o r)

def forcePTree : PTree → PTree
  | .empty => .empty
  | .node l o r =>
    withForcedPTree (forcePTree l) (fun fl =>
    forceOptNat o (fun fo =>
    withForcedPTree (forcePTree r) (fun fr =>
      .node fl fo fr)))

structure MachState where
  stepNo : Nat
  accA   : Nat
  accB   : Nat
  tag    : Nat
  mem    : PTree

def strictMachState (s : MachState) : MachState :=
  match s with
  | MachState.mk stp a b t m =>
    forceNatVal stp (fun fstp =>
    forceNatVal a (fun fa =>
    forceNatVal b (fun fb =>
    forceNatVal t (fun ft =>
    withForcedPTree (forcePTree m) (fun fm =>
      MachState.mk fstp fa fb ft fm)))))

def withForcedState {α : Type} (s : MachState) (k : MachState → α) : α :=
  match strictMachState s with
  | MachState.mk stp a b t m => k (MachState.mk stp a b t m)

def runPow2Forced (step : MachState → MachState) : Nat → MachState → MachState
  | 0, s => strictMachState (step s)
  | d + 1, s =>
    withForcedState (runPow2Forced step d s) (fun sMid =>
      runPow2Forced step d sMid)
```

Three exact invariants hold during kernel reduction:
1. **Syntactic AST severance (`forceNatVal` vs boolean guards):** Forcing via `if Nat.ble 0 n then k n else k n` caches `n ↦ Lit(v)` in `m_st->m_whnf` (`type_checker.cpp:653`) but passes the *unreduced syntactic AST* `n` into `k`, retaining an $O(2^d)$-deep expression DAG across steps. Conversely, `forceNatVal n k` invokes `inductive_reduce_rec` (`inductive.h:107–128`) and `nat_lit_to_constructor` (`inductive.cpp:1363`), substituting only the fresh 2-node closed term `Nat.succ (Lit(v - 1))` (or `0`) into `k` and severing all references to prior state ASTs.
2. **Sibling stack reclamation (`forcePTree : PTree → PTree`):** Evaluating `withForcedPTree (forcePTree l)` reduces the left child as a major premise and **pops all left-subtree frames** upon returning `.node`/`.empty` before `forceOptNat o` or `forcePTree r` runs. Thus normalizing a trie of size $|T|$ and height $h$ uses peak stack $\Theta(h)$ instead of $\Theta(|T|)$, and leaves zero trie frames on the stack once `strictMachState` returns.
3. **$O(1)$ midpoint transition (`withForcedState`):** In `runPow2Forced (d + 1) s`, `inductive_reduce_rec` reduces `strictMachState (runPow2Forced d s)` to `MachState.mk fstp fa fb ft fm`, popping **all** first-half and normalizer stack frames before `whnf_core` (`type_checker.cpp:506–512`) collapses the 5-argument $\beta$-redex to `runPow2Forced d (.mk fstp fa fb ft fm)`. Peak stack depth therefore satisfies $D(d + 1) = c_{\text{mid}} + D(d)$, yielding:
   $$D(d) = c_{\text{mid}} \cdot d + D_{\text{step}} + c_m m + c_h h = \Theta(d + m + h)$$

| Doubling `d` | Steps (`2^d`) | Exit (`-Ddebug.skipKernelTC=false`) | Wall Time (`s`) | Peak RSS (`MiB`) | `#print axioms` |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `4` | `16` | `0` | `1.327` | `147.3` | `[]` |
| `5` | `32` | `0` | `1.766` | `160.9` | `[]` |
| `6` | `64` | `0` | `2.191` | `173.2` | `[]` |
| `7` | `128` | `0` | `3.655` | `171.7` | `[]` |
| `8` | `256` | `0` | `8.090` | `193.5` | `[]` |
| `9` | `512` | `0` | `15.752` | `240.4` | `[]` |
| `10` | `1,024` | `0` | `31.027` | `341.6` | `[]` |

Wall time scales strictly as $O(2^d)$ (`~2x` per increment of $d$). Above $256$ monolithic steps, per-declaration `m_st->m_whnf` and `m_st->m_whnf_core` hash tables (`src/kernel/type_checker.h:31–32`) retain $O(2^d)$ distinct normalized intermediate states, raising RSS from `193.5 MiB` ($d = 8$) to `341.6 MiB` ($d = 10$). Splitting long $N = k \cdot 2^d$ traces across separate top-level checkpoint theorems (`st_0_to_64`, `st_64_to_128`, ...) discards `type_checker::state` between declarations and keeps RSS flat below `200 MiB`.

---

### 4. Zero-Axiom (`[]`) Equivalence Proofs and Path-Forced GMP `PTree` Updates

`Basis: source + derived + execution`

Equivalence between `runPow2Forced` and the textbook unforced specification closes in 35 lines without `propext`, `Quot.sound`, `Classical.choice`, or `Lean.ofReduceBool`:

```lean
def runPow2Spec (step : MachState → MachState) : Nat → MachState → MachState
  | 0, s => step s
  | d + 1, s => runPow2Spec step d (runPow2Spec step d s)

theorem forceNatVal_eq {α : Type} (n : Nat) (k : Nat → α) : forceNatVal n k = k n := by
  cases n <;> rfl

theorem forceOptNat_eq {α : Type} (o : Option Nat) (k : Option Nat → α) :
    forceOptNat o k = k o := by
  cases o with
  | none => rfl
  | some v => exact forceNatVal_eq v (fun fv => k (some fv))

theorem withForcedPTree_eq {α : Type} (t : PTree) (k : PTree → α) :
    withForcedPTree t k = k t := by
  cases t <;> rfl

theorem forcePTree_eq (t : PTree) : forcePTree t = t := by
  induction t with
  | empty => rfl
  | node l o r ihl ihr =>
    dsimp [forcePTree]
    rw [withForcedPTree_eq, forceOptNat_eq, withForcedPTree_eq, ihl, ihr]

theorem strictMachState_eq (s : MachState) : strictMachState s = s := by
  cases s with
  | mk stp a b t m =>
    dsimp [strictMachState]
    rw [forceNatVal_eq, forceNatVal_eq, forceNatVal_eq, forceNatVal_eq,
        withForcedPTree_eq, forcePTree_eq]

theorem withForcedState_eq {α : Type} (s : MachState) (k : MachState → α) :
    withForcedState s k = k s := by
  dsimp [withForcedState]
  rw [strictMachState_eq]

theorem runPow2Forced_eq_spec (step : MachState → MachState) (d : Nat) (s : MachState) :
    runPow2Forced step d s = runPow2Spec step d s := by
  induction d generalizing s with
  | zero => exact strictMachState_eq (step s)
  | succ d ih =>
    dsimp [runPow2Forced, runPow2Spec]
    rw [withForcedState_eq, ih, ih]
```

Two details keep axiom dependencies empty (`[]`) and trie updates fast:
1. **Structural $\eta$-conversion on `MachState`:** In `withForcedState_eq`, once `rw [strictMachState_eq]` rewrites the scrutinee to `s`, `to_cnstr_when_structure` (`src/kernel/inductive.h:60–87`; `WHNF.lean:185–227`) $\eta$-expands single-constructor non-recursive structures (`inductive.cpp:28–33`), closing `MachState.casesOn s (fun ... => k (.mk ...)) = k s` definitionally without casing on `s`.
2. **Bit-fuel `@Nat.rec` over GMP `Nat.div`/`Nat.mod`:** CompCert's `PTree` (`AbsInt/CompCert`, `lib/Maps.v:189–307`) indexes tries by inductive `positive`. In Lean 4, indexing by `Nat` with explicit bit-width fuel (`fuel = 16` for 16-bit keys) uses kernel-accelerated `Nat.div idx 2` and `Nat.mod idx 2` via `@Nat.rec`, avoiding `WellFounded.fix` (which introduces `propext`). Forcing updated leaf values eagerly inside `incSlot` via `forceNatVal (v + 1) (fun fv => some fv)` prevents linear `+ 1` thunk chains inside frequently updated leaves; moreover, if `ptreeModify` wraps only the $O(\text{fuel})$ modified spine nodes in `withForcedPTree`, `strictMachState` need only invoke `withForcedPTree m` ($O(1)$) instead of walking untouched subtrees.

---

### 5. Cross-Assistant Contrast: Rocq (`CClosure`, `cbv`, `vm_compute`, `native_compute`) vs Lean 4

`Basis: source + documentation + derived`

Inspecting `rocq-prover/rocq` (`ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`) explains how alternative kernel architectures trade off stack usage, heap closures, and trusted computing base (TCB) size:

| Reduction Engine | Stack & Control Representation | Argument & Constructor Discipline | TCB Impact | Behavior on Unforced `runPow2 d s` |
| :--- | :--- | :--- | :--- | :--- |
| **Lean 4 Kernel WHNF**<br>(`type_checker.cpp:456–731`) | Host C++ call stack; `scope_rec_depth` (`8,192`) + `check_stack` | Call-by-name $\beta$; lazy constructors; `m_whnf` closed-term cache | Core C++ kernel (mirrored by `Lean4Lean`) | Trips `maxRecDepth` (`512` in `Meta`, `8,192` in kernel) via $\Theta(2^d)$ stack chain |
| **Rocq `CClosure` Kernel**<br>(`kernel/cClosure.ml:78–125, 1531–1640`) | Tail-recursive OCaml loop (`knh`/`knht`) with **heap zipper `stack`** (`Zapp`, `ZcaseT`, `Zproj`, `Zupdate`) | **Call-by-need** (`Zupdate` mutates `fconstr.term` in place; `FLOCKED` guard); lazy `FConstruct` | Core OCaml kernel | Avoids C stack overflow (zipper on heap), but allocates $\Theta(2^d)$ heap `Zproj`/`ZcaseT` frames and unforced `FConstruct` closures |
| **Rocq `cbv` Tactic**<br>(`pretyping/cbv.ml:45–81, 511–594`) | OCaml recursion (`norm_head`) | **Call-by-value** (`App` normalizes arguments eagerly via `Array.fold_right` at `L517–522`) | Untrusted tactic layer (`Qed` re-runs kernel conversion) | Normalizes in $O(d)$ tactic depth, but `Qed` still hits `CClosure` unless paired with `vm_compute` |
| **Rocq `vm_compute`**<br>(`kernel/vconv.ml:72–280`) | C ZAM bytecode interpreter + value stack | Strict **call-by-value** (`Vblock` constructor arrays) | Adds bytecode compiler + C VM to kernel TCB | Evaluates in $O(d)$ VM stack depth without source CPS |
| **Rocq `native_compute` / Lean `native_decide`**<br>(`nativeconv.ml`; `Lean.ofReduceBool`) | Compiles to native code via `ocamlopt` or `leanc` | Strict native call-by-value | Trusts full compiler, linker, and runtime (`Lean4Lean` rejects `reduceBool`/`reduceNat` at `TypeChecker.lean:453–460`) | Fast native execution, but violates zero-axiom (`[]`) minimal-TCB policies |

Notably, Lean 4's internal `eagerReduce` wrapper (`src/kernel/type_checker.cpp:168–184`; `Lean4Lean/TypeChecker.lean:299–301`) only overrides heuristic delta-unfolding deferral in `is_def_eq`; it does **not** evaluate constructor fields or switch `whnf_core` to call-by-value. Two-tier shallow CPS midpoint forcing relies solely on standard eliminator $\iota$-reduction and therefore works portably across Lean 4, `Lean4Lean`, and Rocq `CClosure` with zero TCB expansion.

## Boundaries

- **`not examined` — Coinductive state machines and infinite stream unfolding:** Only finite inductive records and finite radix-2 tries over bounded step horizons were studied; coinductive `CoFix` reduction (`rocq-prover/rocq`, `kernel/cClosure.ml:92`) was `not examined`.
- **`not examined` — Multi-threaded parallel `.olean` replay memory superposition:** Measurements used single-threaded invocation (`-j1`); aggregate peak RSS under concurrent multi-worker module replay was `not examined`.
- **`unknown` — Optimal checkpoint granularity across non-`x86_64` cache hierarchies:** Checkpointing every $64$–$256$ steps keeps `Init.Core` RSS under `200 MiB` on `x86_64` Linux, whereas monolithic $512$–$1,024$-step proofs trade `240–342 MiB` `m_whnf` cache retention for fewer declarations; the exact wall-time optimum on `aarch64` hosts remains `unknown`.
- **`known not to apply` — `eagerReduce` and `@[inline]` as replacements for CPS midpoint forcing:** `@[inline]` targets only untrusted IR/C codegen, and `eagerReduce` leaves constructor arguments lazy inside `whnf_core`; both are `known not to apply` as fixes for `maxRecDepth` exhaustion on `runPow2`.
- **`known not to apply` — Deep full-tree CPS (`forcePTree : PTree → (PTree → α) → α`) around step continuations:** Nesting $O(|T|)$ container continuations around `k` keeps all container frames on the stack during `k` and is `known not to apply`.
- **`unsupported` — `Lean.ofReduceBool` / `Lean.ofReduceNat` (`native_decide`) in `Lean4Lean` and zero-axiom (`[]`) verification:** `Lean4Lean` (`Lean4Lean/TypeChecker.lean:453–460`) explicitly rejects both primitives as `unsupported`, and `#print axioms` records `Lean.ofReduceBool`.

## Evidence

### Primary Upstream Source Coordinates

1. **`leanprover/lean4` (`badf11f93b505238d48439a6538dc2b395009453` and `v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`):**
   - `src/kernel/type_checker.cpp:168–186` (`is_eager_reduce`), `L318–350` (`infer_type_core` stack guards), `L456–539` (`whnf_core` constructor return, call-by-name `instantiate`, `m_whnf_core`), `L602–731` (`reduce_nat` and `whnf`).
   - `src/kernel/inductive.h:60–135` (`to_cnstr_when_structure`, `inductive_reduce_rec` `major = whnf(major)` at `L107`) and `src/kernel/inductive.cpp:1357–1364` (`nat_lit_to_constructor`).
   - `src/runtime/interrupt.{h,cpp}:59–121` (`g_kernel_rec_depth_factor = 16`, `scope_rec_depth`, `check_system`) and `src/runtime/stackinfo.cpp:62–121` (`check_stack`).
   - `src/Lean/Util/RecDepth.lean:15–18` (`maxRecDepth := 512`) and `src/Lean/Meta/WHNF.lean:261–293, 1101–1125` (`reduceRec`, `whnfImp`).
2. **`digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`):**
   - `Lean4Lean/TypeChecker.lean:364–415, 453–460, 519–544`, `Lean4Lean/Inductive/Reduce.lean:80–108`, `Lean4Lean/FuelConfig.lean:12–31`.
3. **`rocq-prover/rocq` (`ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`):**
   - `kernel/reduction.ml:23–50`, `kernel/cClosure.ml:78–125, 882–914, 1531–1640, 2384–2403`, `pretyping/cbv.ml:45–81, 511–594`, `kernel/vconv.ml:72–124, 242–280`, `kernel/nativeconv.ml:45–91`.
4. **`AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`):**
   - `lib/Maps.v:189–307` (`Module PTree`).

### Literature

- G. D. Plotkin, "Call-by-name, call-by-value and the $\lambda$-calculus," *Theoretical Computer Science*, 1(2):125–159, 1975. DOI: `10.1016/0304-3975(75)90017-1`.
- O. Danvy and A. Filinski, "Representing Control: a Study of the CPS Transformation," *Mathematical Structures in Computer Science*, 2(4):361–391, 1992. DOI: `10.1017/S0960129500001535`.
- B. Grégoire and X. Leroy, "A compiled implementation of strong reduction," *ICFP '02*, pp. 235–246, 2002. DOI: `10.1145/581478.581501`.
- X. Leroy, "Formal verification of a realistic compiler," *Communications of the ACM*, 52(7):107–115, 2009. DOI: `10.1145/1538788.1538814`.
- M. Boespflug, M. Dénès, and B. Grégoire, "Full reduction at full throttle," *CPP 2011*, LNCS 7086, pp. 362–377, 2011. DOI: `10.1007/978-3-642-25379-9_26`.
- M. Sozeau et al., "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq," *POPL 2020*, PACMPL 4(POPL):8:1–8:28, 2020. DOI: `10.1145/3371076`.
- L. de Moura and S. Ullrich, "The Lean 4 Theorem Prover and Programming Language," *CADE 28*, LNCS 12699, pp. 625–635, 2021. DOI: `10.1007/978-3-030-79876-5_37`.
- M. Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean," *TYPES 2025*, LIPIcs 384, pp. 2:1–2:23, 2025. DOI: `10.4230/LIPIcs.TYPES.2025.2` (`arXiv:2403.14064`).

### Execution Telemetry (`2026-11-20`, revalidated `2026-11-21`)

Measured on `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` with `lean -j1 -Ddebug.skipKernelTC=false -DwarningAsError=true` and `os.wait4` `ru_maxrss`:
- Unforced `runPow2`: `d = 5` passes (`0.597 s`, `140.5 MiB`); `d = 6` fails (`maximum recursion depth has been reached`).
- `wrapStrict` and `matchStrict`: `d = 4` passes; `d = 5` fails (`maximum recursion depth has been reached`).
- `forcePTreeDeep`: `d = 4` fails (`maximum recursion depth has been reached`).
- `runPow2Forced`: `d = 4..10` (`16..1,024` steps) all exit `0` with `[]` axioms (`d = 8`: `8.090 s`, `193.5 MiB`; `d = 10`: `31.027 s`, `341.6 MiB`).

## Revalidation

1. **Source check:** Inspect `src/kernel/type_checker.cpp` (`whnf_core` `App` branch), `src/kernel/inductive.h` (`inductive_reduce_rec`), `src/kernel/inductive.cpp` (`nat_lit_to_constructor`), and `src/runtime/interrupt.cpp` (`g_kernel_rec_depth_factor`) in the target `leanprover/lean4` commit.
2. **Executable discriminator (`< 10 s`):** Concatenate `prelude` + `import Init.Core`, the declarations in **Findings §3–§4**, and the step harness below into `repro_cps_midpoint.lean`:
   ```lean
   def ptreeModify : Nat → Nat → (Option Nat → Option Nat) → PTree → PTree
     | 0, _, f, .empty => match f none with | none => .empty | some v => .node .empty (some v) .empty
     | 0, _, f, .node l o r => .node l (f o) r
     | fuel + 1, idx, f, .empty =>
       match Nat.beq (Nat.mod idx 2) 0 with
       | true => .node (ptreeModify fuel (Nat.div idx 2) f .empty) none .empty
       | false => .node .empty none (ptreeModify fuel (Nat.div idx 2) f .empty)
     | fuel + 1, idx, f, .node l o r =>
       match Nat.beq (Nat.mod idx 2) 0 with
       | true => .node (ptreeModify fuel (Nat.div idx 2) f l) o r
       | false => .node l o (ptreeModify fuel (Nat.div idx 2) f r)

   def ptreeGet : Nat → Nat → PTree → Nat
     | 0, _, .empty => 0 | 0, _, .node _ none _ => 0 | 0, _, .node _ (some v) _ => v
     | _ + 1, _, .empty => 0
     | fuel + 1, idx, .node l _ r =>
       match Nat.beq (Nat.mod idx 2) 0 with
       | true => ptreeGet fuel (Nat.div idx 2) l | false => ptreeGet fuel (Nat.div idx 2) r

   def incSlot (o : Option Nat) : Option Nat :=
     match o with | none => some 1 | some v => forceNatVal (v + 1) (fun fv => some fv)

   def stepMach (s : MachState) : MachState :=
     match Nat.ble s.stepNo 1000000 with
     | true =>
       { stepNo := s.stepNo + 1, accA := s.accA + (Nat.mod s.stepNo 7) + 1,
         accB := s.accB + s.accA, tag := Nat.mod (s.tag * 3 + s.stepNo + 1) 65536,
         mem := ptreeModify 4 (Nat.mod s.stepNo 16) incSlot s.mem }
     | false => s

   def initMach : MachState := { stepNo := 0, accA := 0, accB := 0, tag := 0, mem := .empty }

   theorem test_step_256 : (runPow2Forced stepMach 8 initMach).stepNo = 256 := rfl
   theorem test_mem_256  : ptreeGet 4 0 (runPow2Forced stepMach 8 initMach).mem = 16 := rfl
   #print axioms runPow2Forced_eq_spec
   #print axioms test_step_256
   ```
   Run `lean -j1 -Ddebug.skipKernelTC=false -DwarningAsError=true repro_cps_midpoint.lean` and verify exit `0`, peak RSS `< 200 MiB` (on `Init.Core`), and `does not depend on any axioms`; then substitute `runPow2Spec stepMach 6` to verify the negative `maxRecDepth` failure still fires.
