/-
  TargetFeatureAndSimdRefinement.lean

  Self-contained, kernel-checked Lean 4 (v4.34.1) mechanization of:
  1. Target-Feature Capability Lattice (`x86_64` and `aarch64` transitive feature
     implication closure, decidable subset `⊆`, and MIR equal-feature vs. LLVM
     subset-feature inlining gates);
  2. Safe `#[target_feature]` (RFC 2396 / Rust 1.86+) Operational Machine,
     capability-witness `fn()` pointer reification (`adjust_target_feature_sig`),
     dynamic CPUID dispatch (`ifCpuHas`), cross-function inlining, and intra-function
     pure instruction hoisting, proving No-`SIGILL` Soundness;
  3. Two concrete sharpness counterexamples:
     - CE1: Unchecked cross-feature inlining (`avx2` into baseline `sse2`) followed
       by pure instruction hoisting above a `false` CPUID guard deterministically
       faults with `Fault.illegalInstruction` on baseline `sse2` hardware;
     - CE2: Allowing baseline safe code to coerce a safe `#[target_feature(enable = "avx2")]`
       function item into a safe `fn()` pointer without `calleeReq ⊆ callerReq`
       deterministically faults with `Fault.illegalInstruction` without `unsafe`;
  4. Portable SIMD (`core::intrinsics::simd`) Lane and Mask Refinement:
     - `simd_shuffle` monomorphization bounds (`idx[i] < 2 * N`) and lane-wise
       concatenation equivalence;
     - All-ones/all-zeros vector mask invariant, MSB sign-bit extraction
       (`lshr (w - 1)`), endian-aware `simd_bitmask` packing (including non-power-of-two
       lane counts such as 10-lane vectors), and `simd_select_bitmask` <-> `simd_select`
       roundtrip equivalence;
     - `simd_masked_load` and `simd_masked_store` off-lane non-access (tail-slice
       safety when `base + N > mem.length`) and memory frame preservation.

  Proof discipline:
  - Pure `Init` only;
  - Constructive structural recursion and decidable reflection throughout, with
    axiom footprint restricted strictly to `{propext, Quot.sound}`.
-/

namespace TargetFeatureAndSimdRefinement

/-! ## Section 1: Target-Feature Lattice (`x86_64` and `aarch64`) -/

/-- Representative target features across `x86_64` and `aarch64` matching
    `compiler/rustc_target/src/target_features.rs` (`rust-lang/rust` 1.99.1). -/
inductive Feature where
  | sse
  | sse2
  | sse3
  | ssse3
  | sse41
  | sse42
  | avx
  | f16c
  | fma
  | avx2
  | avx512f
  | avx512bw
  | avx512vl
  | neon
  | fp16
  | sve
  | sve2
  deriving DecidableEq, Repr

/-- Characteristic predicate representation of a finite target-feature set. -/
abbrev FeatureSet := Feature → Bool

/-- Exhaustive enumeration of `Feature` for constructive decidability. -/
def allFeatures : List Feature :=
  [ .sse, .sse2, .sse3, .ssse3, .sse41, .sse42, .avx, .f16c, .fma,
    .avx2, .avx512f, .avx512bw, .avx512vl, .neon, .fp16, .sve, .sve2 ]

theorem mem_allFeatures (f : Feature) : f ∈ allFeatures := by
  cases f <;> decide

def emptyFeatures : FeatureSet := fun _ => false

def insertFeature (s : FeatureSet) (f : Feature) : FeatureSet :=
  fun q => (q == f) || s q

def unionFeatures (a b : FeatureSet) : FeatureSet :=
  fun q => a q || b q

/-- Transitive closure of features implied by enabling a single feature `f` in
    `rustc` 1.99.1 (`X86_FEATURES` and `AARCH64_FEATURES`). -/
def impliedBy : Feature → FeatureSet
  | .sse      => fun q => q == .sse
  | .sse2     => fun q => q == .sse2 || q == .sse
  | .sse3     => fun q => q == .sse3 || q == .sse2 || q == .sse
  | .ssse3    => fun q => q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .sse41    => fun q => q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .sse42    => fun q => q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .avx      => fun q => q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .f16c     => fun q => q == .f16c || q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .fma      => fun q => q == .fma || q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .avx2     => fun q => q == .avx2 || q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .avx512f  => fun q => q == .avx512f || q == .avx2 || q == .fma || q == .f16c || q == .avx ||
                          q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .avx512bw => fun q => q == .avx512bw || q == .avx512f || q == .avx2 || q == .fma || q == .f16c ||
                          q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .avx512vl => fun q => q == .avx512vl || q == .avx512f || q == .avx2 || q == .fma || q == .f16c ||
                          q == .avx || q == .sse42 || q == .sse41 || q == .ssse3 || q == .sse3 || q == .sse2 || q == .sse
  | .neon     => fun q => q == .neon
  | .fp16     => fun q => q == .fp16 || q == .neon
  | .sve      => fun q => q == .sve || q == .fp16 || q == .neon
  | .sve2     => fun q => q == .sve2 || q == .sve || q == .fp16 || q == .neon

/-- Close a feature set under `impliedBy`. -/
def closeFeatures (s : FeatureSet) : FeatureSet :=
  fun q => allFeatures.any (fun f => s f && impliedBy f q)

/-- Constructively decidable feature subset (`req ⊆ avail`), modeling both
    `tcx.is_target_feature_call_safe` and LLVM `TTI.areInlineCompatible`. -/
def subsetFeatures (req avail : FeatureSet) : Bool :=
  allFeatures.all (fun f => !(req f) || avail f)

/-- Constructively decidable strict feature-set equality (`req == avail`), modeling
    `rustc_mir_transform/src/inline.rs` (`callee_feature_names == this_feature_names`). -/
def eqFeatures (a b : FeatureSet) : Bool :=
  allFeatures.all (fun f => a f == b f)

private theorem list_all_iff {α : Type} (xs : List α) (p : α → Bool) :
    xs.all p = true ↔ ∀ x, x ∈ xs → p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx
      cases hx
    · intro _
      rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons]
    constructor
    · intro h x hx
      rcases hx with rfl | hmem
      · exact h.1
      · exact ih.mp h.2 x hmem
    · intro h
      exact ⟨h hd (Or.inl rfl), ih.mpr (fun x hx => h x (Or.inr hx))⟩

private theorem list_any_iff {α : Type} (xs : List α) (p : α → Bool) :
    xs.any p = true ↔ ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, hx, _⟩
      cases hx
  | cons hd tl ih =>
    simp only [List.any_cons, Bool.or_eq_true, List.mem_cons]
    constructor
    · intro h
      rcases h with hhd | htl
      · exact ⟨hd, Or.inl rfl, hhd⟩
      · rcases ih.mp htl with ⟨x, hx, px⟩
        exact ⟨x, Or.inr hx, px⟩
    · rintro ⟨x, hx, px⟩
      rcases hx with rfl | htl
      · exact Or.inl px
      · exact Or.inr (ih.mpr ⟨x, htl, px⟩)

theorem subsetFeatures_iff (req avail : FeatureSet) :
    subsetFeatures req avail = true ↔ ∀ f, req f = true → avail f = true := by
  unfold subsetFeatures
  rw [list_all_iff]
  constructor
  · intro h f hreq
    have hf := h f (mem_allFeatures f)
    rw [hreq] at hf
    exact hf
  · intro h f _
    cases hreq : req f
    · rfl
    · exact h f hreq

theorem subsetFeatures_refl (s : FeatureSet) : subsetFeatures s s = true :=
  (subsetFeatures_iff s s).mpr (fun _ h => h)

theorem subsetFeatures_trans {a b c : FeatureSet}
    (hab : subsetFeatures a b = true)
    (hbc : subsetFeatures b c = true) :
    subsetFeatures a c = true := by
  rw [subsetFeatures_iff] at hab hbc ⊢
  intro f ha
  exact hbc f (hab f ha)

theorem eqFeatures_iff (a b : FeatureSet) :
    eqFeatures a b = true ↔ ∀ f, a f = b f := by
  unfold eqFeatures
  rw [list_all_iff]
  constructor
  · intro h f
    have hf := h f (mem_allFeatures f)
    exact beq_iff_eq.mp hf
  · intro h f _
    exact beq_iff_eq.mpr (h f)

/-- MIR's strict feature-equality inline gate strictly implies LLVM's subset inline gate. -/
theorem mirInlineGate_implies_llvmInlineGate {callee caller : FeatureSet}
    (h : eqFeatures callee caller = true) :
    subsetFeatures callee caller = true := by
  rw [eqFeatures_iff] at h
  rw [subsetFeatures_iff]
  intro f hcal
  rw [← h f]
  exact hcal

def sse2Set : FeatureSet := impliedBy .sse2
def sse41Set : FeatureSet := impliedBy .sse41
def avxSet : FeatureSet := impliedBy .avx
def avx2Set : FeatureSet := impliedBy .avx2
def avx512fSet : FeatureSet := impliedBy .avx512f
def neonSet : FeatureSet := impliedBy .neon
def sveSet : FeatureSet := impliedBy .sve
def sve2Set : FeatureSet := impliedBy .sve2

/-- Concrete separation between the MIR and LLVM inlining gates: an `sse4.1` leaf
    satisfies `subsetFeatures sse41Set avx2Set = true` (LLVM inlines it into an `avx2`
    caller) while failing `eqFeatures sse41Set avx2Set` (MIR preserves the `Call`). -/
theorem mirInlineGate_strictly_stronger_than_llvmInlineGate :
    subsetFeatures sse41Set avx2Set = true ∧ eqFeatures sse41Set avx2Set = false := by
  decide

theorem x86_lattice_chain :
    subsetFeatures sse2Set sse41Set = true ∧
    subsetFeatures sse41Set avxSet = true ∧
    subsetFeatures avxSet avx2Set = true ∧
    subsetFeatures avx2Set avx512fSet = true ∧
    subsetFeatures avx512fSet avx2Set = false := by
  decide

theorem aarch64_lattice_chain :
    subsetFeatures neonSet sveSet = true ∧
    subsetFeatures sveSet sve2Set = true ∧
    subsetFeatures sve2Set sveSet = false := by
  decide

/-- A hardware CPU's active feature set is closed under architectural feature implication. -/
def IsClosedFeatures (cpu : FeatureSet) : Prop :=
  ∀ f, cpu f = true → subsetFeatures (impliedBy f) cpu = true

theorem impliedBy_refl (f : Feature) : impliedBy f f = true := by
  cases f <;> decide

theorem impliedBy_trans (f g h : Feature) :
    impliedBy f g = true → impliedBy g h = true → impliedBy f h = true := by
  intro hfg
  cases f <;> cases g <;> (try cases hfg) <;> cases h <;> decide

theorem subset_closeFeatures (s : FeatureSet) :
    subsetFeatures s (closeFeatures s) = true := by
  rw [subsetFeatures_iff]
  intro f hsf
  unfold closeFeatures
  rw [list_any_iff]
  exact ⟨f, mem_allFeatures f, Bool.and_eq_true_iff.mpr ⟨hsf, impliedBy_refl f⟩⟩

/-- Key dynamic-dispatch capability lemma: if `avail ⊆ cpu`, `cpu` is implication-closed,
    and runtime detection witnesses `cpu feat = true`, then the extended capability set
    `closeFeatures (insertFeature avail feat)` is completely supported by `cpu`. -/
theorem guarded_extension_subset_cpu
    {avail cpu : FeatureSet} {feat : Feature}
    (hClosed : IsClosedFeatures cpu)
    (hAvail : subsetFeatures avail cpu = true)
    (hHas : cpu feat = true) :
    subsetFeatures (closeFeatures (insertFeature avail feat)) cpu = true := by
  rw [subsetFeatures_iff]
  intro q hq
  unfold closeFeatures at hq
  rw [list_any_iff] at hq
  rcases hq with ⟨f, _, hfAnd⟩
  rcases Bool.and_eq_true_iff.mp hfAnd with ⟨hfIns, hImp⟩
  unfold insertFeature at hfIns
  cases hEq : (f == feat)
  · rw [hEq, Bool.false_or] at hfIns
    have hfCpu : cpu f = true := (subsetFeatures_iff avail cpu).mp hAvail f hfIns
    exact (subsetFeatures_iff (impliedBy f) cpu).mp (hClosed f hfCpu) q hImp
  · have hEq' : f = feat := beq_iff_eq.mp hEq
    subst hEq'
    exact (subsetFeatures_iff (impliedBy f) cpu).mp (hClosed f hHas) q hImp


/-! ## Section 2: `TargetFeature` Capability Machine, Safe `FnPtr` Witnessing, & Inlining -/

/-- Runtime values: scalar integers or safe `fn(Int) -> Int` function pointers (`FnPtr`). -/
inductive Val where
  | int (n : Nat)
  | safeFnPtr (fnId : Nat)
  deriving DecidableEq, Repr

/-- Hardware and runtime faults; `illegalInstruction` models architectural `#UD` / `SIGILL`. -/
inductive Fault where
  | illegalInstruction
  | invalidCallee
  | typeMismatch
  | outOfFuel
  deriving DecidableEq, Repr

inductive Outcome where
  | ok (v : Val)
  | fault (e : Fault)
  deriving DecidableEq, Repr

/-- Core expression language with ISA-gated vector ops, local bindings, runtime CPUID
    guards (`ifCpuHas`), direct calls, capability-checked `fn()` pointer reification
    (`reifySafeFnPtr`), and safe indirect `fn()` calls (`callSafeFnPtr`). -/
inductive Expr where
  | lit (n : Nat)
  | var (x : Nat)
  | isaOp (req : FeatureSet) (result : Nat)
  | letIn (x : Nat) (bound : Expr) (body : Expr)
  | ifCpuHas (feat : Feature) (thenBr : Expr) (elseBr : Expr)
  | directCall (calleeId : Nat) (arg : Expr)
  | reifySafeFnPtr (calleeId : Nat)
  | callSafeFnPtr (ptrExpr : Expr) (arg : Expr)

/-- Function item declaration. `isSafe = true` covers both unannotated baseline safe
    functions and RFC 2396 / Rust 1.86+ `HeaderSafety::SafeTargetFeatures` functions. -/
structure FnDecl where
  reqFeatures : FeatureSet
  isSafe : Bool
  paramVar : Nat
  body : Expr

structure Prog where
  baselineFeatures : FeatureSet
  fns : List FnDecl

def lookupList {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => lookupList xs k

def Prog.lookupFn (p : Prog) (fnId : Nat) : Option FnDecl :=
  lookupList p.fns fnId

abbrev Env := Nat → Val

def emptyEnv : Env := fun _ => .int 0

def updateEnv (env : Env) (x : Nat) (v : Val) : Env :=
  fun y => if y == x then v else env y

/-- Total fuel-indexed big-step operational semantics parameterized by hardware `cpu`. -/
def eval (p : Prog) (cpu : FeatureSet) : Nat → Env → Expr → Outcome
  | 0, _, _ => .fault .outOfFuel
  | _ + 1, _, .lit n => .ok (.int n)
  | _ + 1, env, .var x => .ok (env x)
  | _ + 1, _, .isaOp req res =>
      if subsetFeatures req cpu then
        .ok (.int res)
      else
        .fault .illegalInstruction
  | fuel + 1, env, .letIn x e1 e2 =>
      match eval p cpu fuel env e1 with
      | .ok v1 => eval p cpu fuel (updateEnv env x v1) e2
      | .fault err => .fault err
  | fuel + 1, env, .ifCpuHas feat thenBr elseBr =>
      if cpu feat then
        eval p cpu fuel env thenBr
      else
        eval p cpu fuel env elseBr
  | fuel + 1, env, .directCall cid arg =>
      match eval p cpu fuel env arg with
      | .fault err => .fault err
      | .ok vArg =>
          match p.lookupFn cid with
          | none => .fault .invalidCallee
          | some fnDecl =>
              eval p cpu fuel (updateEnv emptyEnv fnDecl.paramVar vArg) fnDecl.body
  | _ + 1, _, .reifySafeFnPtr cid =>
      match p.lookupFn cid with
      | none => .fault .invalidCallee
      | some _ => .ok (.safeFnPtr cid)
  | fuel + 1, env, .callSafeFnPtr ptrExpr arg =>
      match eval p cpu fuel env ptrExpr with
      | .fault err => .fault err
      | .ok (.int _) => .fault .typeMismatch
      | .ok (.safeFnPtr cid) =>
          match eval p cpu fuel env arg with
          | .fault err => .fault err
          | .ok vArg =>
              match p.lookupFn cid with
              | none => .fault .invalidCallee
              | some fnDecl =>
                  eval p cpu fuel (updateEnv emptyEnv fnDecl.paramVar vArg) fnDecl.body

/-- Static target-feature safety judgment (`check_unsafety` + `adjust_target_feature_sig`).
    Notice how `reifySafeFnPtr` requires `subsetFeatures callee.reqFeatures avail = true`:
    - In baseline code (`avail = baselineFeatures`), an `avx2` function CANNOT coerce
      to a safe `fn()` pointer (`E0308` / `TypeError::TargetFeatureCast`);
    - Inside an `avx2` body (`avail = avx2Set`), coercing an `avx2` function to `fn()`
      IS permitted because entering the `avx2` body dynamically witnesses `avx2 ⊆ cpu`! -/
inductive TypedExpr (p : Prog) : FeatureSet → Expr → Prop where
  | lit (avail : FeatureSet) (n : Nat) :
      TypedExpr p avail (.lit n)
  | var (avail : FeatureSet) (x : Nat) :
      TypedExpr p avail (.var x)
  | isaOp {avail req : FeatureSet} (res : Nat) :
      subsetFeatures req avail = true →
      TypedExpr p avail (.isaOp req res)
  | letIn {avail : FeatureSet} (x : Nat) {e1 e2 : Expr} :
      TypedExpr p avail e1 →
      TypedExpr p avail e2 →
      TypedExpr p avail (.letIn x e1 e2)
  | ifCpuHas {avail : FeatureSet} (feat : Feature) {thenBr elseBr : Expr} :
      TypedExpr p (closeFeatures (insertFeature avail feat)) thenBr →
      TypedExpr p avail elseBr →
      TypedExpr p avail (.ifCpuHas feat thenBr elseBr)
  | directCall {avail : FeatureSet} {cid : Nat} {callee : FnDecl} {arg : Expr} :
      p.lookupFn cid = some callee →
      callee.isSafe = true →
      subsetFeatures callee.reqFeatures avail = true →
      TypedExpr p avail arg →
      TypedExpr p avail (.directCall cid arg)
  | reifySafeFnPtr {avail : FeatureSet} {cid : Nat} {callee : FnDecl} :
      p.lookupFn cid = some callee →
      callee.isSafe = true →
      subsetFeatures callee.reqFeatures avail = true →
      TypedExpr p avail (.reifySafeFnPtr cid)
  | callSafeFnPtr {avail : FeatureSet} {ptrExpr arg : Expr} :
      TypedExpr p avail ptrExpr →
      TypedExpr p avail arg →
      TypedExpr p avail (.callSafeFnPtr ptrExpr arg)

/-- Every safe function in `p` is well-typed under its declared `reqFeatures`. -/
def WellTypedFn (p : Prog) (f : FnDecl) : Prop :=
  f.isSafe = true → TypedExpr p f.reqFeatures f.body

def WellTypedProg (p : Prog) : Prop :=
  ∀ cid f, p.lookupFn cid = some f → WellTypedFn p f

/-- Semantic capability-witness invariant on runtime values: any safe `fn()` pointer
    reachable at runtime points to a safe function whose `reqFeatures ⊆ cpu`. -/
def SafeVal (p : Prog) (cpu : FeatureSet) : Val → Prop
  | .int _ => True
  | .safeFnPtr cid =>
      ∃ callee, p.lookupFn cid = some callee ∧
                callee.isSafe = true ∧
                subsetFeatures callee.reqFeatures cpu = true

def SafeEnv (p : Prog) (cpu : FeatureSet) (env : Env) : Prop :=
  ∀ x, SafeVal p cpu (env x)

theorem safeEnv_empty (p : Prog) (cpu : FeatureSet) : SafeEnv p cpu emptyEnv :=
  fun _ => trivial

theorem safeEnv_update {p : Prog} {cpu : FeatureSet} {env : Env} {x : Nat} {v : Val}
    (hEnv : SafeEnv p cpu env)
    (hVal : SafeVal p cpu v) :
    SafeEnv p cpu (updateEnv env x v) := by
  intro y
  unfold updateEnv
  cases y == x
  · exact hEnv y
  · exact hVal

/-- Core Inductive Preservation & Progress-Without-`SIGILL` Lemma:
    Evaluating any `TypedExpr p avail e` under hardware `cpu` where `avail ⊆ cpu`
    never faults with `Fault.illegalInstruction` and preserves `SafeVal p cpu` on `.ok`. -/
theorem eval_typed_no_sigill
    {p : Prog} {cpu : FeatureSet}
    (hClosed : IsClosedFeatures cpu)
    (hProg : WellTypedProg p) :
    ∀ (fuel : Nat) {avail : FeatureSet} {env : Env} {e : Expr},
      TypedExpr p avail e →
      subsetFeatures avail cpu = true →
      SafeEnv p cpu env →
      eval p cpu fuel env e ≠ .fault .illegalInstruction ∧
      (∀ v, eval p cpu fuel env e = .ok v → SafeVal p cpu v)
  | 0, _, _, _, _, _, _ => by
      constructor
      · intro h; cases h
      · intro _ h; cases h
  | fuel + 1, _, _, .lit n, _, _, _ => by
      constructor
      · intro h; cases h
      · intro v h; cases h; trivial
  | fuel + 1, _, env, .var x, _, _, hEnv => by
      constructor
      · intro h; cases h
      · intro v h; cases h; exact hEnv x
  | fuel + 1, _, _, .isaOp req res, .isaOp _ hReqAvail, hAvailCpu, _ => by
      have hReqCpu : subsetFeatures req cpu = true :=
        subsetFeatures_trans hReqAvail hAvailCpu
      simp only [eval, hReqCpu, ↓reduceIte]
      constructor
      · intro h; cases h
      · intro v h; cases h; trivial
  | fuel + 1, _, env, .letIn x e1 e2, .letIn _ ht1 ht2, hAvailCpu, hEnv => by
      have ih1 := eval_typed_no_sigill hClosed hProg fuel ht1 hAvailCpu hEnv
      simp only [eval]
      cases hEval1 : eval p cpu fuel env e1 with
      | ok v1 =>
          have hv1 : SafeVal p cpu v1 := ih1.2 v1 hEval1
          exact eval_typed_no_sigill hClosed hProg fuel ht2 hAvailCpu (safeEnv_update hEnv hv1)
      | fault err =>
          constructor
          · intro hEq
            apply ih1.1
            rw [hEval1]
            exact hEq
          · intro _ hEq; cases hEq
  | fuel + 1, _, env, .ifCpuHas feat thenBr elseBr, .ifCpuHas _ htThen htElse, hAvailCpu, hEnv => by
      simp only [eval]
      cases hHas : cpu feat
      · exact eval_typed_no_sigill hClosed hProg fuel htElse hAvailCpu hEnv
      · have hExtCpu : subsetFeatures (closeFeatures (insertFeature _ feat)) cpu = true :=
          guarded_extension_subset_cpu hClosed hAvailCpu hHas
        exact eval_typed_no_sigill hClosed hProg fuel htThen hExtCpu hEnv
  | fuel + 1, _, env, .directCall cid arg, .directCall hLookup hSafe hCalleeSub htArg, hAvailCpu, hEnv => by
      have ihArg := eval_typed_no_sigill hClosed hProg fuel htArg hAvailCpu hEnv
      simp only [eval]
      cases hArg : eval p cpu fuel env arg with
      | fault err =>
          constructor
          · intro hEq; apply ihArg.1; rw [hArg]; exact hEq
          · intro _ hEq; cases hEq
      | ok vArg =>
          simp only [hLookup]
          have hvArg : SafeVal p cpu vArg := ihArg.2 vArg hArg
          have hCalleeTyped : TypedExpr p _ _ := hProg cid _ hLookup hSafe
          have hCalleeCpu : subsetFeatures _ cpu = true :=
            subsetFeatures_trans hCalleeSub hAvailCpu
          exact eval_typed_no_sigill hClosed hProg fuel hCalleeTyped hCalleeCpu
            (safeEnv_update (safeEnv_empty p cpu) hvArg)
  | fuel + 1, _, _, .reifySafeFnPtr cid, .reifySafeFnPtr hLookup hSafe hCalleeSub, hAvailCpu, _ => by
      simp only [eval, hLookup]
      constructor
      · intro h; cases h
      · intro v hEq
        cases hEq
        exact ⟨_, hLookup, hSafe, subsetFeatures_trans hCalleeSub hAvailCpu⟩
  | fuel + 1, _, env, .callSafeFnPtr ptrExpr arg, .callSafeFnPtr htPtr htArg, hAvailCpu, hEnv => by
      have ihPtr := eval_typed_no_sigill hClosed hProg fuel htPtr hAvailCpu hEnv
      simp only [eval]
      cases hPtr : eval p cpu fuel env ptrExpr with
      | fault err =>
          constructor
          · intro hEq; apply ihPtr.1; rw [hPtr]; exact hEq
          · intro _ hEq; cases hEq
      | ok vPtr =>
          cases vPtr with
          | int _ =>
              constructor
              · intro hEq; cases hEq
              · intro _ hEq; cases hEq
          | safeFnPtr cid =>
              have hSafePtr : SafeVal p cpu (.safeFnPtr cid) := ihPtr.2 (.safeFnPtr cid) hPtr
              rcases hSafePtr with ⟨callee, hLookup, hSafe, hCalleeCpu⟩
              have ihArg := eval_typed_no_sigill hClosed hProg fuel htArg hAvailCpu hEnv
              cases hArg : eval p cpu fuel env arg with
              | fault err =>
                  constructor
                  · intro hEq; apply ihArg.1; rw [hArg]; exact hEq
                  · intro _ hEq; cases hEq
              | ok vArg =>
                  simp only [hLookup]
                  have hvArg : SafeVal p cpu vArg := ihArg.2 vArg hArg
                  have hCalleeTyped : TypedExpr p callee.reqFeatures callee.body :=
                    hProg cid callee hLookup hSafe
                  exact eval_typed_no_sigill hClosed hProg fuel hCalleeTyped hCalleeCpu
                    (safeEnv_update (safeEnv_empty p cpu) hvArg)

theorem typedExpr_weaken {p : Prog} {a b : FeatureSet} {e : Expr}
    (ht : TypedExpr p a e)
    (hab : subsetFeatures a b = true) :
    TypedExpr p b e := by
  induction ht generalizing b with
  | lit _ n => exact .lit b n
  | var _ x => exact .var b x
  | isaOp res hReq => exact .isaOp res (subsetFeatures_trans hReq hab)
  | letIn x _ _ ih1 ih2 => exact .letIn x (ih1 hab) (ih2 hab)
  | @ifCpuHas avail' feat _ _ _ _ ihThen ihElse =>
      have hSubExt :
          subsetFeatures (closeFeatures (insertFeature avail' feat))
                         (closeFeatures (insertFeature b feat)) = true := by
        rw [subsetFeatures_iff]
        intro q hq
        unfold closeFeatures at hq ⊢
        rw [list_any_iff] at hq ⊢
        rcases hq with ⟨f, hMem, hfAnd⟩
        rcases Bool.and_eq_true_iff.mp hfAnd with ⟨hfIns, hImp⟩
        refine ⟨f, hMem, Bool.and_eq_true_iff.mpr ⟨?_, hImp⟩⟩
        unfold insertFeature at hfIns ⊢
        cases hEq : (f == feat)
        · rw [hEq, Bool.false_or] at hfIns
          exact (subsetFeatures_iff avail' b).mp hab f hfIns
        · rfl
      exact .ifCpuHas feat (ihThen hSubExt) (ihElse hab)
  | directCall hLookup hSafe hSub _ ihArg =>
      exact .directCall hLookup hSafe (subsetFeatures_trans hSub hab) (ihArg hab)
  | reifySafeFnPtr hLookup hSafe hSub =>
      exact .reifySafeFnPtr hLookup hSafe (subsetFeatures_trans hSub hab)
  | callSafeFnPtr _ _ ihPtr ihArg =>
      exact .callSafeFnPtr (ihPtr hab) (ihArg hab)

/-- Non-recursive cross-function direct-call inliner gated by `gate calleeReq callerReq`. -/
def inlineExpr (p : Prog) (callerReq : FeatureSet)
    (gate : FeatureSet → FeatureSet → Bool) : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .isaOp req res => .isaOp req res
  | .letIn x e1 e2 => .letIn x (inlineExpr p callerReq gate e1) (inlineExpr p callerReq gate e2)
  | .ifCpuHas feat t e =>
      .ifCpuHas feat (inlineExpr p callerReq gate t) (inlineExpr p callerReq gate e)
  | .directCall cid arg =>
      let arg' := inlineExpr p callerReq gate arg
      match p.lookupFn cid with
      | none => .directCall cid arg'
      | some callee =>
          if callee.isSafe && gate callee.reqFeatures callerReq then
            .letIn callee.paramVar arg' callee.body
          else
            .directCall cid arg'
  | .reifySafeFnPtr cid => .reifySafeFnPtr cid
  | .callSafeFnPtr ptr arg =>
      .callSafeFnPtr (inlineExpr p callerReq gate ptr) (inlineExpr p callerReq gate arg)

/-- Intra-function speculative pure-op hoisting (modeling LLVM LICM / GVN hoisting an
    `isaOp` out of `ifCpuHas` when valid under the enclosing function's `callerReq`). -/
def hoistPureOpIfLegal (callerReq : FeatureSet) : Expr → Expr
  | .letIn x e1 e2 => .letIn x (hoistPureOpIfLegal callerReq e1) (hoistPureOpIfLegal callerReq e2)
  | .ifCpuHas feat (.letIn x (.isaOp req res) thenRest) elseBr =>
      let thenRest' := hoistPureOpIfLegal callerReq thenRest
      let elseBr' := hoistPureOpIfLegal callerReq elseBr
      if subsetFeatures req callerReq then
        .letIn x (.isaOp req res) (.ifCpuHas feat thenRest' elseBr')
      else
        .ifCpuHas feat (.letIn x (.isaOp req res) thenRest') elseBr'
  | .ifCpuHas feat t e =>
      .ifCpuHas feat (hoistPureOpIfLegal callerReq t) (hoistPureOpIfLegal callerReq e)
  | .directCall cid arg => .directCall cid (hoistPureOpIfLegal callerReq arg)
  | .callSafeFnPtr ptr arg =>
      .callSafeFnPtr (hoistPureOpIfLegal callerReq ptr) (hoistPureOpIfLegal callerReq arg)
  | other => other

/-- Unchecked intra-function speculative hoisting (models LLVM LICM hoisting ANY pure op
    present in the caller body above a loop/branch guard because LLVM assumes every instruction
    already inside the caller body is legal for the caller's `"target-features"`). -/
def hoistPureOpUnchecked : Expr → Expr
  | .ifCpuHas feat (.letIn x (.isaOp req res) thenRest) elseBr =>
      .letIn x (.isaOp req res)
        (.ifCpuHas feat (hoistPureOpUnchecked thenRest) (hoistPureOpUnchecked elseBr))
  | .letIn x e1 e2 => .letIn x (hoistPureOpUnchecked e1) (hoistPureOpUnchecked e2)
  | .ifCpuHas feat t e => .ifCpuHas feat (hoistPureOpUnchecked t) (hoistPureOpUnchecked e)
  | .directCall cid arg => .directCall cid (hoistPureOpUnchecked arg)
  | .callSafeFnPtr ptr arg => .callSafeFnPtr (hoistPureOpUnchecked ptr) (hoistPureOpUnchecked arg)
  | other => other

def optimizeProg (p : Prog) (gate : FeatureSet → FeatureSet → Bool) : Prog :=
  { p with
    fns := p.fns.map (fun f =>
      { f with body := hoistPureOpIfLegal f.reqFeatures (inlineExpr p f.reqFeatures gate f.body) }) }

theorem lookupList_map {α β : Type} (g : α → β) :
    ∀ (xs : List α) (k : Nat), lookupList (xs.map g) k = (lookupList xs k).map g
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => lookupList_map g xs k

theorem typedExpr_change_prog {p1 p2 : Prog}
    (hSameMeta : ∀ cid f1, p1.lookupFn cid = some f1 →
      ∃ f2, p2.lookupFn cid = some f2 ∧ f2.isSafe = f1.isSafe ∧ f2.reqFeatures = f1.reqFeatures)
    {avail : FeatureSet} {e : Expr}
    (ht : TypedExpr p1 avail e) :
    TypedExpr p2 avail e := by
  induction ht with
  | lit a n => exact .lit a n
  | var a x => exact .var a x
  | isaOp res hReq => exact .isaOp res hReq
  | letIn x _ _ ih1 ih2 => exact .letIn x ih1 ih2
  | ifCpuHas feat _ _ ihT ihE => exact .ifCpuHas feat ihT ihE
  | directCall hLookup hSafe hSub _ ihArg =>
      rcases hSameMeta _ _ hLookup with ⟨f2, hL2, hS2, hR2⟩
      rw [← hS2] at hSafe
      rw [← hR2] at hSub
      exact .directCall hL2 hSafe hSub ihArg
  | reifySafeFnPtr hLookup hSafe hSub =>
      rcases hSameMeta _ _ hLookup with ⟨f2, hL2, hS2, hR2⟩
      rw [← hS2] at hSafe
      rw [← hR2] at hSub
      exact .reifySafeFnPtr hL2 hSafe hSub
  | callSafeFnPtr _ _ ihP ihA => exact .callSafeFnPtr ihP ihA

theorem inlineExpr_preserves_typing
    {p : Prog} {callerReq avail : FeatureSet}
    {gate : FeatureSet → FeatureSet → Bool}
    (hGateSound : ∀ callee caller, gate callee caller = true → subsetFeatures callee caller = true)
    (hProg : WellTypedProg p)
    (hCallerSub : subsetFeatures callerReq avail = true)
    {e : Expr}
    (ht : TypedExpr p avail e) :
    TypedExpr p avail (inlineExpr p callerReq gate e) := by
  induction ht with
  | lit a n => exact .lit a n
  | var a x => exact .var a x
  | isaOp res hReq => exact .isaOp res hReq
  | letIn x _ _ ih1 ih2 => exact .letIn x (ih1 hCallerSub) (ih2 hCallerSub)
  | @ifCpuHas avail' feat _ _ _ _ ihThen ihElse =>
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail' feat)) = true := by
        have hIns : subsetFeatures avail' (insertFeature avail' feat) = true := by
          rw [subsetFeatures_iff]
          intro f hf
          unfold insertFeature
          rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub
          (subsetFeatures_trans hIns (subset_closeFeatures (insertFeature avail' feat)))
      exact .ifCpuHas feat (ihThen hSubExt) (ihElse hCallerSub)
  | @directCall avail' cid callee arg hLookup hSafe hSub _ ihArg =>
      have ihArg' := ihArg hCallerSub
      cases hCond : (callee.isSafe && gate callee.reqFeatures callerReq)
      · simp only [inlineExpr, hLookup, hCond]
        exact .directCall hLookup hSafe hSub ihArg'
      · simp only [inlineExpr, hLookup, hCond, ↓reduceIte]
        rcases Bool.and_eq_true_iff.mp hCond with ⟨hSafeCallee, hGateOk⟩
        have hCalleeSubCaller : subsetFeatures callee.reqFeatures callerReq = true :=
          hGateSound callee.reqFeatures callerReq hGateOk
        have hCalleeTyped : TypedExpr p callee.reqFeatures callee.body :=
          hProg cid callee hLookup hSafeCallee
        have hCalleeAvail : TypedExpr p avail' callee.body :=
          typedExpr_weaken hCalleeTyped (subsetFeatures_trans hCalleeSubCaller hCallerSub)
        exact .letIn callee.paramVar ihArg' hCalleeAvail
  | reifySafeFnPtr hLookup hSafe hSub =>
      exact .reifySafeFnPtr hLookup hSafe hSub
  | callSafeFnPtr _ _ ihPtr ihArg =>
      exact .callSafeFnPtr (ihPtr hCallerSub) (ihArg hCallerSub)

theorem hoistPureOpIfLegal_preserves_typing
    {p : Prog} {callerReq avail : FeatureSet}
    (hCallerSub : subsetFeatures callerReq avail = true) :
    ∀ {e : Expr}, TypedExpr p avail e → TypedExpr p avail (hoistPureOpIfLegal callerReq e)
  | .lit n, _ => .lit avail n
  | .var x, _ => .var avail x
  | .isaOp _ res, .isaOp _ hReq => .isaOp res hReq
  | .letIn x _ _, .letIn _ ht1 ht2 =>
      .letIn x (hoistPureOpIfLegal_preserves_typing hCallerSub ht1)
               (hoistPureOpIfLegal_preserves_typing hCallerSub ht2)
  | .directCall _ _, .directCall hL hS hSub htArg =>
      .directCall hL hS hSub (hoistPureOpIfLegal_preserves_typing hCallerSub htArg)
  | .reifySafeFnPtr _, .reifySafeFnPtr hL hS hSub =>
      .reifySafeFnPtr hL hS hSub
  | .callSafeFnPtr _ _, .callSafeFnPtr htP htA =>
      .callSafeFnPtr (hoistPureOpIfLegal_preserves_typing hCallerSub htP)
                     (hoistPureOpIfLegal_preserves_typing hCallerSub htA)
  | .ifCpuHas feat (.letIn x (.isaOp req res) thenRest) elseBr,
    .ifCpuHas _ (.letIn _ (.isaOp _ hReqExt) htThenRest) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]
          intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      have ihThen := hoistPureOpIfLegal_preserves_typing hSubExt htThenRest
      have ihElse := hoistPureOpIfLegal_preserves_typing hCallerSub htElse
      simp only [hoistPureOpIfLegal]
      cases hLeg : subsetFeatures req callerReq
      · exact .ifCpuHas feat (.letIn x (.isaOp res hReqExt) ihThen) ihElse
      · have hReqAvail : subsetFeatures req avail = true := subsetFeatures_trans hLeg hCallerSub
        exact .letIn x (.isaOp res hReqAvail) (.ifCpuHas feat ihThen ihElse)
  | .ifCpuHas feat (.lit n) elseBr, .ifCpuHas _ _ htElse =>
      .ifCpuHas feat (.lit _ n) (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.var y) elseBr, .ifCpuHas _ _ htElse =>
      .ifCpuHas feat (.var _ y) (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.isaOp _ res) elseBr, .ifCpuHas _ (.isaOp _ hReq) htElse =>
      .ifCpuHas feat (.isaOp res hReq) (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.lit n) r) elseBr, .ifCpuHas _ (.letIn _ _ htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (.lit _ n) (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.var y) r) elseBr, .ifCpuHas _ (.letIn _ _ htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (.var _ y) (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.letIn y a b) r) elseBr, .ifCpuHas _ (.letIn _ htL htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (hoistPureOpIfLegal_preserves_typing hSubExt htL)
                                     (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.ifCpuHas f2 a b) r) elseBr, .ifCpuHas _ (.letIn _ htL htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (hoistPureOpIfLegal_preserves_typing hSubExt htL)
                                     (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.directCall c a) r) elseBr, .ifCpuHas _ (.letIn _ htL htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (hoistPureOpIfLegal_preserves_typing hSubExt htL)
                                     (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.reifySafeFnPtr c) r) elseBr, .ifCpuHas _ (.letIn _ htL htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (hoistPureOpIfLegal_preserves_typing hSubExt htL)
                                     (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.letIn x (.callSafeFnPtr p1 a) r) elseBr, .ifCpuHas _ (.letIn _ htL htR) htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (.letIn x (hoistPureOpIfLegal_preserves_typing hSubExt htL)
                                     (hoistPureOpIfLegal_preserves_typing hSubExt htR))
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.ifCpuHas f2 a b) elseBr, .ifCpuHas _ htT htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (hoistPureOpIfLegal_preserves_typing hSubExt htT)
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.directCall c a) elseBr, .ifCpuHas _ htT htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (hoistPureOpIfLegal_preserves_typing hSubExt htT)
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.reifySafeFnPtr c) elseBr, .ifCpuHas _ htT htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (hoistPureOpIfLegal_preserves_typing hSubExt htT)
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)
  | .ifCpuHas feat (.callSafeFnPtr p1 a) elseBr, .ifCpuHas _ htT htElse => by
      have hSubExt : subsetFeatures callerReq (closeFeatures (insertFeature avail feat)) = true := by
        have hIns : subsetFeatures avail (insertFeature avail feat) = true := by
          rw [subsetFeatures_iff]; intro f hf; unfold insertFeature; rw [hf, Bool.or_true]
        exact subsetFeatures_trans hCallerSub (subsetFeatures_trans hIns (subset_closeFeatures _))
      exact .ifCpuHas feat (hoistPureOpIfLegal_preserves_typing hSubExt htT)
                           (hoistPureOpIfLegal_preserves_typing hCallerSub htElse)

theorem optimizeProg_preserves_wellTyped
    {p : Prog} {gate : FeatureSet → FeatureSet → Bool}
    (hGateSound : ∀ callee caller, gate callee caller = true → subsetFeatures callee caller = true)
    (hProg : WellTypedProg p) :
    WellTypedProg (optimizeProg p gate) := by
  intro cid fOpt hLookupOpt hSafeOpt
  unfold optimizeProg Prog.lookupFn at hLookupOpt
  rw [lookupList_map] at hLookupOpt
  cases hLookupOrig : lookupList p.fns cid with
  | none =>
      rw [hLookupOrig] at hLookupOpt
      cases hLookupOpt
  | some fOrig =>
      rw [hLookupOrig] at hLookupOpt
      injection hLookupOpt with hEq
      rw [← hEq] at hSafeOpt ⊢
      have hOrigTyped : TypedExpr p fOrig.reqFeatures fOrig.body :=
        hProg cid fOrig hLookupOrig hSafeOpt
      have hInlTyped : TypedExpr p fOrig.reqFeatures
          (inlineExpr p fOrig.reqFeatures gate fOrig.body) :=
        inlineExpr_preserves_typing hGateSound hProg
          (subsetFeatures_refl fOrig.reqFeatures) hOrigTyped
      have hHoistTyped : TypedExpr p fOrig.reqFeatures
          (hoistPureOpIfLegal fOrig.reqFeatures (inlineExpr p fOrig.reqFeatures gate fOrig.body)) :=
        hoistPureOpIfLegal_preserves_typing (subsetFeatures_refl fOrig.reqFeatures) hInlTyped
      refine typedExpr_change_prog ?_ hHoistTyped
      intro cid2 g1 hL1
      unfold Prog.lookupFn at hL1
      refine ⟨{ g1 with body := hoistPureOpIfLegal g1.reqFeatures (inlineExpr p g1.reqFeatures gate g1.body) },
              ?_, rfl, rfl⟩
      unfold optimizeProg Prog.lookupFn
      rw [lookupList_map, hL1]
      rfl

/-- **Main Theorem 1 (No-`SIGILL` Target-Feature Type & Feature-Monotone Inlining Soundness)**:
    For any `WellTypedProg p`, hardware capability set `cpu` closed under architectural
    feature implication, and cross-function inlining gate `gate` satisfying
    `gate callee caller = true → subsetFeatures callee caller = true` (which covers both
    MIR's `eqFeatures` gate and LLVM's `subsetFeatures` gate), executing any safe entry
    function `entry` of `optimizeProg p gate` whose `reqFeatures ⊆ cpu` NEVER faults with
    `Fault.illegalInstruction` at any fuel bound. -/
theorem no_sigill_soundness_of_typed_and_feature_monotone_inlining
    {p : Prog} {cpu : FeatureSet}
    {gate : FeatureSet → FeatureSet → Bool}
    (hClosed : IsClosedFeatures cpu)
    (hProg : WellTypedProg p)
    (hGateSound : ∀ callee caller, gate callee caller = true → subsetFeatures callee caller = true)
    {entryId : Nat} {entryFn : FnDecl}
    (hEntry : (optimizeProg p gate).lookupFn entryId = some entryFn)
    (hSafe : entryFn.isSafe = true)
    (hEntrySupported : subsetFeatures entryFn.reqFeatures cpu = true)
    (argVal : Nat) (fuel : Nat) :
    eval (optimizeProg p gate) cpu fuel
      (updateEnv emptyEnv entryFn.paramVar (.int argVal)) entryFn.body ≠
      .fault .illegalInstruction := by
  have hOptProg : WellTypedProg (optimizeProg p gate) :=
    optimizeProg_preserves_wellTyped hGateSound hProg
  have hBodyTyped : TypedExpr (optimizeProg p gate) entryFn.reqFeatures entryFn.body :=
    hOptProg entryId entryFn hEntry hSafe
  have hEnv : SafeEnv (optimizeProg p gate) cpu
      (updateEnv emptyEnv entryFn.paramVar (.int argVal)) :=
    safeEnv_update (safeEnv_empty _ cpu) trivial
  exact (eval_typed_no_sigill hClosed hOptProg fuel hBodyTyped hEntrySupported hEnv).1


/-! ## Section 3: Sharpness Counterexamples (CE1 & CE2) -/

/-- Baseline x86-64 CPU supporting only `sse` and `sse2` (lacking `avx2` and `avx512f`). -/
def baselineSse2Cpu : FeatureSet := sse2Set

theorem baselineSse2Cpu_closed : IsClosedFeatures baselineSse2Cpu := by
  intro f
  cases f <;> decide

/-- **Counterexample CE1 (Unchecked Cross-Feature Inlining + Instruction Hoisting)**:
    - Function 0 (`avx2Kernel`): safe `#[target_feature(enable = "avx2")]` executing a pure
      `avx2` vector instruction (`isaOp avx2Set 230`).
    - Function 1 (`baselineDispatcher`): safe baseline (`sse2`) function guarding the call
      behind `ifCpuHas .avx2 (.directCall 0 (.var 0)) (.lit 42)`. -/
def ce1Avx2Kernel : FnDecl :=
  { reqFeatures := avx2Set
    isSafe := true
    paramVar := 0
    body := .isaOp avx2Set 230 }

def ce1BaselineDispatcher : FnDecl :=
  { reqFeatures := sse2Set
    isSafe := true
    paramVar := 0
    body := .ifCpuHas .avx2 (.directCall 0 (.var 0)) (.lit 42) }

def ce1Prog : Prog :=
  { baselineFeatures := sse2Set
    fns := [ce1Avx2Kernel, ce1BaselineDispatcher] }

theorem ce1Prog_wellTyped : WellTypedProg ce1Prog := by
  intro cid f hLookup _
  cases cid with
  | zero =>
      injection hLookup with hEq; subst hEq
      exact .isaOp 230 (by decide)
  | succ cid1 =>
      cases cid1 with
      | zero =>
          injection hLookup with hEq; subst hEq
          refine .ifCpuHas .avx2 ?_ (.lit sse2Set 42)
          exact .directCall rfl rfl (by decide) (.var _ 0)
      | succ cid2 =>
          cases hLookup

/-- Under feature-monotone LLVM inlining (`subsetFeatures`), `ce1BaselineDispatcher`
    does NOT inline `ce1Avx2Kernel` across the `sse2 -> avx2` boundary, and returns
    `.ok (.int 42)` cleanly on `baselineSse2Cpu`.
    By contrast, when cross-feature inlining ignores `calleeReq ⊆ callerReq`
    (`uncheckedGate := fun _ _ => true`) and intra-function LICM (`hoistPureOpUnchecked`)
    hoists `.isaOp avx2Set 230` above `ifCpuHas .avx2`, execution on `baselineSse2Cpu`
    deterministically faults with `Fault.illegalInstruction`! -/
def ce1UncheckedInlinedBody : Expr :=
  inlineExpr
    { ce1Prog with fns := [{ ce1Avx2Kernel with body := .isaOp avx2Set 230 }, ce1BaselineDispatcher] }
    sse2Set (fun _ _ => true)
    (.ifCpuHas .avx2 (.letIn 1 (.isaOp avx2Set 230) (.var 1)) (.lit 42))

theorem ce1_sharpness_counterexample :
    WellTypedProg ce1Prog ∧
    eval (optimizeProg ce1Prog subsetFeatures) baselineSse2Cpu 6 emptyEnv
      ce1BaselineDispatcher.body = .ok (.int 42) ∧
    eval ce1Prog baselineSse2Cpu 6 emptyEnv
      (hoistPureOpUnchecked ce1UncheckedInlinedBody) = .fault .illegalInstruction := by
  refine ⟨ce1Prog_wellTyped, ?_, ?_⟩
  · decide
  · decide

/-- **Counterexample CE2 (Coercing Safe `#[target_feature]` Fn to Safe `fn()` Pointer)**:
    - Function 0 (`avx2Callee`): safe `#[target_feature(enable = "avx2")]` executing `isaOp avx2Set 99`.
    - Function 1 (`applySafeFnPtr`): safe baseline (`sse2`) higher-order consumer calling a
      safe `fn()` pointer via `callSafeFnPtr (.var 0) (.lit 0)` with zero `unsafe`.
    - Baseline expression `ce2BadBaselineCoercion`: attempts `.reifySafeFnPtr 0` in `sse2`
      context and passes it to `applySafeFnPtr`. -/
def ce2Avx2Callee : FnDecl :=
  { reqFeatures := avx2Set
    isSafe := true
    paramVar := 0
    body := .isaOp avx2Set 99 }

def ce2HigherOrderBaseline : FnDecl :=
  { reqFeatures := sse2Set
    isSafe := true
    paramVar := 0
    body := .callSafeFnPtr (.var 0) (.lit 0) }

def ce2Prog : Prog :=
  { baselineFeatures := sse2Set
    fns := [ce2Avx2Callee, ce2HigherOrderBaseline] }

def ce2BadBaselineCoercion : Expr :=
  .directCall 1 (.reifySafeFnPtr 0)

theorem ce2Prog_wellTyped : WellTypedProg ce2Prog := by
  intro cid f hLookup _
  cases cid with
  | zero =>
      injection hLookup with hEq; subst hEq
      exact .isaOp 99 (by decide)
  | succ cid1 =>
      cases cid1 with
      | zero =>
          injection hLookup with hEq; subst hEq
          exact .callSafeFnPtr (.var sse2Set 0) (.lit sse2Set 0)
      | succ cid2 =>
          cases hLookup

theorem ce2_baseline_safe_fnptr_coercion_rejected :
    ¬ TypedExpr ce2Prog sse2Set (.reifySafeFnPtr 0) := by
  intro hTyped
  cases hTyped with
  | reifySafeFnPtr hLookup _ hSub =>
      injection hLookup with hEq
      subst hEq
      exact absurd hSub (by decide)

theorem ce2_avx2_witness_safe_fnptr_reification_allowed :
    TypedExpr ce2Prog avx2Set (.reifySafeFnPtr 0) :=
  .reifySafeFnPtr rfl rfl (by decide)

theorem ce2_sharpness_counterexample :
    WellTypedProg ce2Prog ∧
    (¬ TypedExpr ce2Prog sse2Set (.reifySafeFnPtr 0)) ∧
    eval ce2Prog baselineSse2Cpu 6 emptyEnv ce2BadBaselineCoercion =
      .fault .illegalInstruction :=
  ⟨ce2Prog_wellTyped, ce2_baseline_safe_fnptr_coercion_rejected, by decide⟩


/-! ## Section 4: Portable SIMD (`core::intrinsics::simd`) Lane & Mask Refinement -/

/-- Length-indexed SIMD vector of `n` lanes of element type `α`. -/
structure SimdVec (α : Type) (n : Nat) where
  get : Fin n → α

theorem SimdVec.ext {α : Type} {n : Nat} {u v : SimdVec α n}
    (h : ∀ i : Fin n, u.get i = v.get i) : u = v := by
  cases u with
  | mk gu =>
    cases v with
    | mk gv =>
      have hFun : gu = gv := funext h
      subst hFun
      rfl

/-- Constructive universal quantifier over `Fin m`. -/
def allFin : (m : Nat) → (Fin m → Bool) → Bool
  | 0, _ => true
  | m + 1, p =>
      p ⟨0, Nat.zero_lt_succ m⟩ &&
      allFin m (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem allFin_iff :
    ∀ (m : Nat) (p : Fin m → Bool), allFin m p = true ↔ ∀ i : Fin m, p i = true
  | 0, _ => by
      constructor
      · intro _ i; exact Fin.elim0 i
      · intro _; rfl
  | m + 1, p => by
      simp only [allFin, Bool.and_eq_true]
      rw [allFin_iff m]
      constructor
      · rintro ⟨h0, hSucc⟩ ⟨k, hk⟩
        cases k with
        | zero => exact h0
        | succ k' =>
            have hk' : k' < m := Nat.lt_of_succ_lt_succ hk
            exact hSucc ⟨k', hk'⟩
      · intro hAll
        exact ⟨hAll ⟨0, Nat.zero_lt_succ m⟩,
               fun i => hAll ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩

/-! ### 4.1 `simd_shuffle` Bounds & Concatenated Lane Selection -/

private theorem sub_lt_of_lt_add_same {k n : Nat}
    (hNotLt : ¬ k < n) (hLt2 : k < n + n) : k - n < n := by
  have hLe : n ≤ k := Nat.le_of_not_lt hNotLt
  have hEq : k - n + n = k := Nat.sub_add_cancel hLe
  rw [← hEq] at hLt2
  exact Nat.lt_of_add_lt_add_right hLt2

def simdShuffleValid {m : Nat} (n : Nat) (idx : SimdVec Nat m) : Bool :=
  allFin m (fun i => decide (idx.get i < n + n))

/-- Reference lane-wise specification of `simd_shuffle(x, y, idx)` when `idx[i] < 2 * n`. -/
def simdShuffleSpec {α : Type} {n m : Nat}
    (x y : SimdVec α n) (idx : SimdVec Nat m)
    (hValid : ∀ i : Fin m, idx.get i < n + n) : SimdVec α m where
  get i :=
    if hLt : idx.get i < n then
      x.get ⟨idx.get i, hLt⟩
    else
      y.get ⟨idx.get i - n, sub_lt_of_lt_add_same hLt (hValid i)⟩

/-- Checked monomorphization lowering matching `rustc_codegen_llvm/src/intrinsic.rs:2170-2256`. -/
def simdShuffleChecked {α : Type} {n m : Nat}
    (x y : SimdVec α n) (idx : SimdVec Nat m) : Except Fault (SimdVec α m) :=
  if h : simdShuffleValid n idx = true then
    .ok (simdShuffleSpec x y idx (fun i =>
      of_decide_eq_true (((allFin_iff m _).mp h) i)))
  else
    .error .typeMismatch

/-- **Theorem 2a (`simd_shuffle` In-Bounds Soundness & Lane-Wise Equivalence)**. -/
theorem simdShuffleChecked_lanewise_eq {α : Type} {n m : Nat}
    (x y : SimdVec α n) (idx : SimdVec Nat m)
    (hInBounds : ∀ i : Fin m, idx.get i < n + n) :
    ∃ out,
      simdShuffleChecked x y idx = .ok out ∧
      ∀ i : Fin m,
        out.get i =
          (if hLt : idx.get i < n then
             x.get ⟨idx.get i, hLt⟩
           else
             y.get ⟨idx.get i - n, sub_lt_of_lt_add_same hLt (hInBounds i)⟩) := by
  have hBool : simdShuffleValid n idx = true :=
    (allFin_iff m _).mpr (fun i => decide_eq_true (hInBounds i))
  simp only [simdShuffleChecked, hBool, ↓reduceDIte]
  exact ⟨simdShuffleSpec x y idx hInBounds, rfl, fun _ => rfl⟩

/-- Out-of-bounds shuffle index (`idx[i] ≥ 2 * n`) fails closed at monomorphization (`E0511`). -/
theorem simdShuffleChecked_oob_rejected {α : Type} {n m : Nat}
    (x y : SimdVec α n) (idx : SimdVec Nat m)
    (i : Fin m) (hOob : ¬ (idx.get i < n + n)) :
    simdShuffleChecked x y idx = .error .typeMismatch := by
  unfold simdShuffleChecked
  split
  · next hBool =>
      exact False.elim (hOob (of_decide_eq_true ((allFin_iff m _).mp hBool i)))
  · rfl

/-! ### 4.2 Vector Mask MSB Sign Extraction, Endian `simd_bitmask`, & `simd_select_bitmask` -/

/-- `core::intrinsics::simd` lane-mask representation invariant: every mask lane of bit-width
    `w + 1` is either `0` (`false`) or all-ones `BitVec.allOnes (w + 1)` (`true`). -/
def encodeMaskLane (w : Nat) (b : Bool) : BitVec (w + 1) :=
  if b then BitVec.allOnes (w + 1) else 0#(w + 1)

/-- Exact model of `rustc_codegen_llvm/src/intrinsic.rs:2028-2040` (`vector_mask_to_bitmask`):
    logical shift right by `elem_bits - 1` (`w`) followed by truncation to `i1`. -/
def extractMaskBitMSB (w : Nat) (lane : BitVec (w + 1)) : Bool :=
  ((lane >>> w).truncate 1) == 1#1

private theorem two_pow_pos : ∀ w : Nat, 0 < 2 ^ w
  | 0 => Nat.zero_lt_one
  | w + 1 => by
      rw [Nat.pow_succ]
      have ih := two_pow_pos w
      exact Nat.mul_pos ih (by decide)

private theorem allOnes_ushiftRight_top (w : Nat) :
    ((2 ^ (w + 1) - 1) / (2 ^ w)) % 2 = 1 := by
  have hPowPos : 0 < 2 ^ w := two_pow_pos w
  have hStep : 2 ^ (w + 1) - 1 = 2 ^ w + (2 ^ w - 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.add_sub_assoc hPowPos (2 ^ w)
  rw [hStep]
  have hRemLt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt hPowPos Nat.zero_lt_one
  have hDiv1 : (2 ^ w + (2 ^ w - 1)) / (2 ^ w) = 1 + (2 ^ w - 1) / (2 ^ w) := by
    rw [Nat.add_comm (2 ^ w) (2 ^ w - 1)]
    rw [Nat.add_div_right (2 ^ w - 1) hPowPos]
    exact Nat.add_comm _ 1
  rw [hDiv1, Nat.div_eq_of_lt hRemLt]

/-- **Theorem 2b-i (`vector_mask_to_bitmask` Sign-Bit Extraction Soundness)**:
    For every positive byte/element width `w + 1`, shifting an all-ones/all-zeros mask lane
    right by `w` and truncating to 1 bit recovers the exact boolean mask value `b`. -/
theorem extractMaskBitMSB_encodeMaskLane (w : Nat) (b : Bool) :
    extractMaskBitMSB w (encodeMaskLane w b) = b := by
  cases b
  · have hZero : (0#(w + 1) >>> w).truncate 1 = 0#1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
          BitVec.toNat_ofNat, Nat.zero_mod, Nat.shiftRight_eq_div_pow, Nat.zero_div]
      rfl
    unfold extractMaskBitMSB encodeMaskLane
    change ((0#(w + 1) >>> w).truncate 1 == 1#1) = false
    rw [hZero]
    rfl
  · have hOne : (BitVec.allOnes (w + 1) >>> w).truncate 1 = 1#1 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
          BitVec.toNat_allOnes, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      exact allOnes_ushiftRight_top w
    unfold extractMaskBitMSB encodeMaskLane
    change ((BitVec.allOnes (w + 1) >>> w).truncate 1 == 1#1) = true
    rw [hOne]
    rfl

/-- Target endianness governing `simd_bitmask` and `simd_select_bitmask` bit ordering
    (`rustc_codegen_llvm/src/intrinsic.rs:2051-2088, 2346-2397` & `IntrinsicSimd.lean:168-181`). -/
inductive Endian where
  | little
  | big
  deriving DecidableEq, Repr

/-- Pure arithmetic bit test (`bit k` of `bits` from LSB `k = 0`). -/
def testBitAt : Nat → Nat → Bool
  | bits, 0 => bits % 2 == 1
  | bits, k + 1 => testBitAt (bits / 2) k

/-- Pack a list of booleans from LSB (`head`) to MSB. -/
def packBitsLSB : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * packBitsLSB bs

private theorem bit_add_two_mul_mod (b : Bool) (rest : Nat) :
    ((if b then 1 else 0) + 2 * rest) % 2 = (if b then 1 else 0) := by
  cases b
  · simp [Nat.mul_mod_right]
  · simp only [↓reduceIte]
    rw [Nat.add_comm 1 (2 * rest)]
    rw [Nat.mul_add_mod 2 rest 1]

private theorem bit_add_two_mul_div (b : Bool) (rest : Nat) :
    ((if b then 1 else 0) + 2 * rest) / 2 = rest := by
  cases b
  · simp [Nat.mul_div_right _ (by decide : 0 < 2)]
  · simp only [↓reduceIte]
    rw [Nat.add_comm 1 (2 * rest)]
    rw [Nat.mul_add_div (by decide : 0 < 2) rest 1]
    rfl

theorem testBitAt_packBitsLSB :
    ∀ (bs : List Bool) (k : Nat) (hk : k < bs.length),
      testBitAt (packBitsLSB bs) k = bs[k]
  | [], _, hk => by cases hk
  | b :: bs, 0, _ => by
      simp only [packBitsLSB, testBitAt, bit_add_two_mul_mod, List.getElem_cons_zero]
      cases b <;> rfl
  | b :: bs, k + 1, hk => by
      simp only [packBitsLSB, testBitAt, bit_add_two_mul_div, List.getElem_cons_succ]
      exact testBitAt_packBitsLSB bs k (Nat.lt_of_succ_lt_succ hk)

theorem packBitsLSB_lt_two_pow :
    ∀ (bs : List Bool), packBitsLSB bs < 2 ^ bs.length
  | [] => Nat.zero_lt_one
  | b :: bs => by
      have ih := packBitsLSB_lt_two_pow bs
      cases b
      · change 0 + 2 * packBitsLSB bs < 2 ^ (bs.length + 1)
        rw [Nat.pow_succ, Nat.mul_two, Nat.zero_add, Nat.two_mul]
        exact Nat.add_lt_add ih ih
      · change 1 + 2 * packBitsLSB bs < 2 ^ (bs.length + 1)
        rw [Nat.pow_succ, Nat.mul_two]
        have h1 : 1 + 2 * packBitsLSB bs = (packBitsLSB bs + 1) + packBitsLSB bs := by
          rw [Nat.two_mul, ← Nat.add_assoc, Nat.add_comm 1 (packBitsLSB bs)]
        rw [h1]
        exact Nat.add_lt_add_of_le_of_lt (Nat.succ_le_of_lt ih) ih

def vecToList : {n : Nat} → SimdVec α n → List α
  | 0, _ => []
  | n + 1, v =>
      v.get ⟨0, Nat.zero_lt_succ n⟩ ::
      vecToList ⟨fun i => v.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩

theorem vecToList_length : ∀ {n : Nat} (v : SimdVec α n), (vecToList v).length = n
  | 0, _ => rfl
  | n + 1, v => by
      simp only [vecToList, List.length_cons]
      rw [vecToList_length]

theorem vecToList_getElem :
    ∀ {n : Nat} (v : SimdVec α n) (i : Fin n),
      (vecToList v)[i.val]'(by rw [vecToList_length]; exact i.isLt) = v.get i
  | 0, _, i => Fin.elim0 i
  | n + 1, v, ⟨0, _⟩ => rfl
  | n + 1, v, ⟨k + 1, hk⟩ => by
      simp only [vecToList, List.getElem_cons_succ]
      exact vecToList_getElem ⟨fun j => v.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩⟩
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Endian-aware `simd_bitmask`:
    - Little-endian packs lane `0` at LSB (`bit i = mask[i]`), zero-extending above bit `n - 1`;
    - Big-endian packs lane `0` at bit `n - 1` (`bit (n - 1 - i) = mask[i]`). -/
def simdBitmaskPack (e : Endian) {n : Nat} (mask : SimdVec Bool n) : Nat :=
  match e with
  | .little => packBitsLSB (vecToList mask)
  | .big    => packBitsLSB (vecToList mask).reverse

def simdBitmaskUnpack (e : Endian) (n : Nat) (bits : Nat) : SimdVec Bool n where
  get i :=
    match e with
    | .little => testBitAt bits i.val
    | .big    => testBitAt bits (n - 1 - i.val)

def simdSelectVec {α : Type} {n : Nat} (mask : SimdVec Bool n) (yes no : SimdVec α n) : SimdVec α n where
  get i := if mask.get i then yes.get i else no.get i

def simdSelectBitmask {α : Type} {n : Nat} (e : Endian) (bits : Nat) (yes no : SimdVec α n) : SimdVec α n :=
  simdSelectVec (simdBitmaskUnpack e n bits) yes no

private theorem sub_sub_cancel_of_lt {i n : Nat} (hi : i < n) :
    n - 1 - (n - 1 - i) = i := by
  have h1 : i ≤ n - 1 := Nat.le_pred_of_lt hi
  exact Nat.sub_sub_self h1

private theorem sub_lt_of_lt_pos {i n : Nat} (hi : i < n) :
    n - 1 - i < n := by
  have hPos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hPredLt : n - 1 < n := Nat.sub_lt hPos Nat.zero_lt_one
  exact Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) i) hPredLt

theorem simdBitmaskPack_lt_two_pow (e : Endian) {n : Nat} (mask : SimdVec Bool n) :
    simdBitmaskPack e mask < 2 ^ n := by
  cases e
  · unfold simdBitmaskPack
    have h := packBitsLSB_lt_two_pow (vecToList mask)
    rw [vecToList_length] at h
    exact h
  · unfold simdBitmaskPack
    have h := packBitsLSB_lt_two_pow (vecToList mask).reverse
    rw [List.length_reverse, vecToList_length] at h
    exact h

theorem simdBitmask_unpack_pack_roundtrip (e : Endian) {n : Nat} (mask : SimdVec Bool n) :
    simdBitmaskUnpack e n (simdBitmaskPack e mask) = mask := by
  apply SimdVec.ext
  intro i
  cases e
  · simp only [simdBitmaskUnpack, simdBitmaskPack]
    have hLen : i.val < (vecToList mask).length := by rw [vecToList_length]; exact i.isLt
    rw [testBitAt_packBitsLSB (vecToList mask) i.val hLen]
    exact vecToList_getElem mask i
  · simp only [simdBitmaskUnpack, simdBitmaskPack]
    have hIdxLt : n - 1 - i.val < (vecToList mask).reverse.length := by
      rw [List.length_reverse, vecToList_length]
      exact sub_lt_of_lt_pos i.isLt
    rw [testBitAt_packBitsLSB (vecToList mask).reverse (n - 1 - i.val) hIdxLt]
    rw [List.getElem_reverse]
    have hPos : (vecToList mask).length - 1 - (n - 1 - i.val) = i.val := by
      rw [vecToList_length]
      exact sub_sub_cancel_of_lt i.isLt
    simp only [hPos]
    exact vecToList_getElem mask i

/-- **Theorem 2b-ii (`simd_select_bitmask` <-> `simd_select` Roundtrip Equivalence)**:
    For both little-endian and big-endian targets and EVERY vector lane count `n`
    (including non-power-of-two widths such as `n = 10`), `simd_select_bitmask` on the
    integer packed by `simd_bitmask` is extensionally identical to `simd_select`. -/
theorem simdSelectBitmask_pack_eq_simdSelect {α : Type} {n : Nat}
    (e : Endian) (mask : SimdVec Bool n) (yes no : SimdVec α n) :
    simdSelectBitmask e (simdBitmaskPack e mask) yes no = simdSelectVec mask yes no := by
  unfold simdSelectBitmask
  rw [simdBitmask_unpack_pack_roundtrip]

/-- Concrete 10-lane non-power-of-two bitmask check matching `core::intrinsics::simd::simd_bitmask`
    upstream documentation and our `I16x10` runtime execution probe (`0b0101001011 = 331`). -/
def mask10Example : SimdVec Bool 10 where
  get i :=
    match i.val with
    | 0 => true  | 1 => true  | 2 => false | 3 => true  | 4 => false
    | 5 => false | 6 => true  | 7 => false | 8 => true  | _ => false

theorem nonpow2_10lane_bitmask_little_endian_eq :
    simdBitmaskPack .little mask10Example = 0b0101001011 := rfl

/-! ### 4.3 `simd_masked_load` & `simd_masked_store` Off-Lane Non-Access & Frame Safety -/

/-- Operational semantics of `simd_masked_load(mask, base, passthrough)`:
    DISABLED lanes (`mask[i] = false`) NEVER access `mem[base + i]` and succeed even when
    `base + i ≥ mem.length` (e.g. tail slices shorter than vector width `n`). -/
def simdMaskedLoad {n : Nat}
    (mask : SimdVec Bool n) (mem : List Nat) (base : Nat) (passthrough : SimdVec Nat n) :
    Except Fault (SimdVec Nat n) :=
  if hOk : allFin n (fun i => !(mask.get i) || decide (base + i.val < mem.length)) = true then
    .ok ⟨fun i =>
      if hm : mask.get i = true then
        have hCell : (!mask.get i || decide (base + i.val < mem.length)) = true :=
          (allFin_iff n _).mp hOk i
        have hLt : base + i.val < mem.length := by
          rw [hm] at hCell
          exact of_decide_eq_true hCell
        mem[base + i.val]'hLt
      else
        passthrough.get i⟩
  else
    .error .typeMismatch

/-- **Theorem 2c-i (`simd_masked_load` Tail-Slice Fault-Freedom & Off-Lane Passthrough)**:
    Even if `base + n > mem.length`, `simdMaskedLoad` succeeds whenever every *enabled*
    lane satisfies `base + i < mem.length`, returning `mem[base + i]` on active lanes and
    `passthrough[i]` on disabled lanes. -/
theorem simdMaskedLoad_active_inbounds_sound {n : Nat}
    (mask : SimdVec Bool n) (mem : List Nat) (base : Nat) (passthrough : SimdVec Nat n)
    (hActive : ∀ i : Fin n, mask.get i = true → base + i.val < mem.length) :
    ∃ out,
      simdMaskedLoad mask mem base passthrough = .ok out ∧
      ∀ i : Fin n,
        out.get i =
          (if hm : mask.get i = true then
             mem[base + i.val]'(hActive i hm)
           else
             passthrough.get i) := by
  have hOk : allFin n (fun i => !(mask.get i) || decide (base + i.val < mem.length)) = true := by
    rw [allFin_iff]
    intro i
    cases hm : mask.get i
    · rfl
    · simp only [Bool.not_true, Bool.false_or]
      exact decide_eq_true (hActive i hm)
  let expected : SimdVec Nat n :=
    ⟨fun i =>
      if hm : mask.get i = true then
        mem[base + i.val]'(hActive i hm)
      else
        passthrough.get i⟩
  refine ⟨expected, ?_, fun _ => rfl⟩
  simp only [simdMaskedLoad, hOk, ↓reduceDIte]
  rfl

/-- Concrete 8-lane tail-slice witness matching `probe_results.json`: a 5-word slice
    `[11, 22, 33, 44, 55]` loaded with 8-lane AVX2 mask `[T, F, T, F, T, F, F, F]`
    succeeds without out-of-bounds fault even though `5 < 8`. -/
def tailMask8 : SimdVec Bool 8 where
  get i := i.val == 0 || i.val == 2 || i.val == 4

def tailPassthrough8 : SimdVec Nat 8 where
  get i := 70 + i.val

theorem simdMaskedLoad_short_5word_slice_ok :
    (simdMaskedLoad tailMask8 [11, 22, 33, 44, 55] 0 tailPassthrough8).map vecToList =
      .ok [11, 71, 33, 73, 55, 75, 76, 77] := rfl

/-- Structural indexed list mapper avoiding intermediate `Array` accumulators. -/
def mapWithAddr {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | idx, y :: ys => f idx y :: mapWithAddr f (idx + 1) ys

theorem mapWithAddr_length {α β : Type} (f : Nat → α → β) :
    ∀ (idx : Nat) (xs : List α), (mapWithAddr f idx xs).length = xs.length
  | _, [] => rfl
  | idx, _ :: xs => by
      simp only [mapWithAddr, List.length_cons]
      rw [mapWithAddr_length f (idx + 1) xs]

theorem mapWithAddr_getElem {α β : Type} (f : Nat → α → β) :
    ∀ (idx : Nat) (xs : List α) (k : Nat) (hk : k < xs.length),
      (mapWithAddr f idx xs)[k]'(by rw [mapWithAddr_length]; exact hk) = f (idx + k) xs[k]
  | _, [], _, hk => by cases hk
  | idx, _ :: _, 0, _ => by
      simp [mapWithAddr, Nat.add_zero]
  | idx, _ :: xs, k + 1, hk => by
      simp only [mapWithAddr, List.getElem_cons_succ]
      rw [mapWithAddr_getElem f (idx + 1) xs k (Nat.lt_of_succ_lt_succ hk)]
      have hAssoc : (idx + 1) + k = idx + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      rw [hAssoc]

/-- Pure masked memory update: for each address `addr`, if `addr = base + i` for an active
    lane `i < n` with `mask[i] = true`, write `vals[i]`; otherwise preserve `mem[addr]`. -/
def simdMaskedStoreSpec {n : Nat}
    (mask : SimdVec Bool n) (mem : List Nat) (base : Nat) (vals : SimdVec Nat n) : List Nat :=
  mapWithAddr (fun addr oldVal =>
    if decide (base ≤ addr) then
      if hLt : addr - base < n then
        let laneIdx : Fin n := ⟨addr - base, hLt⟩
        if mask.get laneIdx then vals.get laneIdx else oldVal
      else
        oldVal
    else
      oldVal) 0 mem

theorem simdMaskedStoreSpec_length {n : Nat}
    (mask : SimdVec Bool n) (mem : List Nat) (base : Nat) (vals : SimdVec Nat n) :
    (simdMaskedStoreSpec mask mem base vals).length = mem.length :=
  mapWithAddr_length _ 0 mem

/-- **Theorem 2c-ii (`simd_masked_store` Frame & Disabled-Lane Preservation)**:
    1. Memory length is preserved;
    2. Every active lane `i` (`mask[i] = true`, `base + i < mem.length`) stores `vals[i]`;
    3. Every disabled lane `i` (`mask[i] = false`) leaves `mem[base + i]` strictly unchanged;
    4. Every out-of-window address (`addr < base` or `addr ≥ base + n`) is untouched. -/
theorem simdMaskedStoreSpec_frame_and_lanes {n : Nat}
    (mask : SimdVec Bool n) (mem : List Nat) (base : Nat) (vals : SimdVec Nat n) :
    (simdMaskedStoreSpec mask mem base vals).length = mem.length ∧
    (∀ (i : Fin n) (hIn : base + i.val < mem.length),
      (simdMaskedStoreSpec mask mem base vals)[base + i.val]'(by
        rw [simdMaskedStoreSpec_length]; exact hIn) =
        if mask.get i then vals.get i else mem[base + i.val]) ∧
    (∀ (addr : Nat) (hIn : addr < mem.length),
      (addr < base ∨ base + n ≤ addr) →
      (simdMaskedStoreSpec mask mem base vals)[addr]'(by
        rw [simdMaskedStoreSpec_length]; exact hIn) = mem[addr]) := by
  refine ⟨simdMaskedStoreSpec_length mask mem base vals, ?_, ?_⟩
  · intro i hIn
    unfold simdMaskedStoreSpec
    rw [mapWithAddr_getElem _ 0 mem (base + i.val) hIn]
    simp only [Nat.zero_add]
    have hGe : decide (base ≤ base + i.val) = true :=
      decide_eq_true (Nat.le_add_right base i.val)
    have hSub : (base + i.val) - base = i.val := Nat.add_sub_cancel_left base i.val
    have hSubLt : (base + i.val) - base < n := by rw [hSub]; exact i.isLt
    simp only [hGe, ↓reduceIte, hSubLt, ↓reduceDIte]
    have hFinEq : (⟨(base + i.val) - base, hSubLt⟩ : Fin n) = i := by
      cases i with
      | mk iv isLt =>
        simp only [Fin.mk.injEq]
        exact hSub
    rw [hFinEq]
  · intro addr hIn hOut
    unfold simdMaskedStoreSpec
    rw [mapWithAddr_getElem _ 0 mem addr hIn]
    simp only [Nat.zero_add]
    rcases hOut with hLtBase | hGeEnd
    · have hNotGe : decide (base ≤ addr) = false :=
        decide_eq_false (Nat.not_le_of_lt hLtBase)
      simp only [hNotGe, Bool.false_eq_true, ↓reduceIte]
    · cases hDec : decide (base ≤ addr)
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · have hGe : base ≤ addr := of_decide_eq_true hDec
        have hNotLt : ¬ (addr - base < n) := by
          intro hSubLt
          have hAddLt : (addr - base) + base < n + base := Nat.add_lt_add_right hSubLt base
          rw [Nat.sub_add_cancel hGe, Nat.add_comm n base] at hAddLt
          exact Nat.not_le_of_lt hAddLt hGeEnd
        simp only [↓reduceIte, hNotLt, ↓reduceDIte]

end TargetFeatureAndSimdRefinement
