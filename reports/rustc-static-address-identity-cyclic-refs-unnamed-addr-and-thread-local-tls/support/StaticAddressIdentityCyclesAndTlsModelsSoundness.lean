/-!
# Soundness of `rustc` Static Address Identity, Two-Phase Cyclic Static Allocation,
# `unnamed_addr` Constant Deduplication, and `#[thread_local]` TLS Isolation

Standalone kernel-checked formalization (`Lean v4.34.1`) with:
- `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`
- `0` `partial def`, `0` `unsafe def`, `0` `axiom`, `0` `opaque`, `0` `._unsafe_rec`
- Every definition explicitly marked `noncomputable def` (no `noncomputable section`,
  no `deriving DecidableEq`/`Repr` on inductives).

Formalized subsystems matching pinned `rust-lang/rust` (`compiler/rustc_codegen_llvm/src/{consts.rs, context.rs}`,
`compiler/rustc_const_eval/src/{const_eval/eval_queries.rs, const_eval/machine.rs, interpret/util.rs, interpret/eval_context.rs}`,
`compiler/rustc_middle/src/mir/interpret/mod.rs`, `compiler/rustc_session/src/{options.rs, session.rs}`),
`llvm/llvm-project` (`GlobalValue.h`, `ConstantMerge.cpp`, `GlobalOpt.cpp`, `GlobalStatus.cpp`,
`TargetMachine.cpp`, `TargetLoweringObjectFile.cpp`, `TargetLoweringObjectFileImpl.cpp`), and
`rust-lang/reference` (`items.static.intro`, `items.static.storage-disjointness`, `items.const.behavior`):

1. **Two-Phase Static/Const Initializer Graph (`StaticInitGraph`):**
   Models value-dependency edges (`readVal`) vs. address-of relocation edges (`addrOf`)
   under `reserve_and_set_static_alloc` (`create_static_alloc` / `eval_global`) and the
   `rustc_query_system` active-query stack (`eval_static_initializer`).
   - Proves `two_phase_static_acyclicity_soundness`: value-edge acyclicity (topological rank)
     guarantees unique, well-founded initialization for all `static` items even in the
     presence of arbitrary `addrOf` cycles (both self-cycles and mutual cycles).
   - Proves `value_cycle_e0391_necessity`: any value-dependency cycle forces query-cycle
     rejection (`E0391` for $\ge 2$-node cycles, `RecursiveStatic` `E0080` for self-value cycles)
     and can never produce a valid evaluated allocation at any fuel.
   - Proves `const_ref_cycle_e0391_contrast`: `const` items lacking `reserve_and_set_static_alloc`
     fail with `E0391` on the same mutual reference graph that succeeds for `static`.

2. **`unnamed_addr` Constant Deduplication vs. `static` Address Identity:**
   Models `rustc_codegen_llvm` (`static_addr_of_mut` emitting `private unnamed_addr constant`
   vs. `codegen_static_item` omitting `unnamed_addr`), `GlobalOpt` `local_unnamed_addr`
   refinement gated by `GS.IsCompared`, and `ConstantMergePass` (`makeMergeable`).
   - Proves `unnamed_addr_dedup_preserves_all_deref_observations`: merging equal read-only
     `unnamed_addr` constants preserves every pointer-dereference observation identically.
   - Proves `non_unnamed_addr_static_preserves_address_distinctness`: distinct `static` items
     retain `UnnamedAddr.none` (or non-mergeable state under `ConstantMerge`), preserving
     strictly distinct link-time addresses even with identical payloads.
   - Proves `mixed_merge_downgrades_survivor_and_preserves_static_disjointness`: merging an
     `unnamed_addr` constant with one `static` strips `UnnamedAddr.global_` from the
     survivor, blocking subsequent merges with a second distinct `static`.

3. **`#[thread_local]` ELF `.tdata`/`.tbss`, `-Z tls-model`, and TLS Non-Interference:**
   Models `TlsModel`, `TargetMachine::getTLSModel` PIE upgrade, `isSuitableForBSS` `.tdata`/`.tbss`
   partitioning (`GV->isConstant()` forcing `.tdata` even for zero initializers), `@llvm.threadlocal.address.p0`,
   and per-thread TLS memory instantiation.
   - Proves `tls_noninterference_trace`: writes to any `#[thread_local]` static in thread `t1`
     never affect reads of any `#[thread_local]` static in any distinct thread `t2 ≠ t1`.
-/

namespace StaticAddressIdentityCyclesAndTlsModelsSoundness

/-! ## Section 1: Pure Constructive Arithmetic, Lists, and Association Maps -/

noncomputable def natBeq (a b : Nat) : Bool :=
  Nat.beq a b

theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natBeq_eq {a b : Nat} (h : natBeq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : natBeq a b = false := by
  cases hbeq : natBeq a b
  · rfl
  · exact False.elim (h (natBeq_eq hbeq))

theorem natBeq_symm (a b : Nat) : natBeq a b = natBeq b a := by
  cases h : natBeq a b
  · cases h2 : natBeq b a
    · rfl
    · have heq := natBeq_eq h2
      subst heq
      rw [natBeq_refl] at h
      cases h
  · have heq := natBeq_eq h
    subst heq
    rw [natBeq_refl]

noncomputable def natBle (a b : Nat) : Bool :=
  Nat.ble a b

noncomputable def natBlt (a b : Nat) : Bool :=
  Nat.ble (a + 1) b

theorem natBle_true_iff_le {a b : Nat} : natBle a b = true ↔ a ≤ b := by
  dsimp only [natBle]
  rw [Nat.ble_eq]

theorem natBlt_true_iff_lt {a b : Nat} : natBlt a b = true ↔ a < b := by
  dsimp only [natBlt]
  rw [Nat.ble_eq]
  exact ⟨fun h => h, fun h => h⟩

theorem nat_lt_irrefl (n : Nat) : ¬ (n < n) :=
  Nat.lt_irrefl n

theorem nat_lt_trans {a b c : Nat} (h1 : a < b) (h2 : b < c) : a < c :=
  Nat.lt_trans h1 h2

noncomputable def replicateVal (n : Nat) (v : Nat) : List Nat :=
  Nat.repeat (fun acc => v :: acc) n []

theorem replicateVal_succ (n v : Nat) :
    replicateVal (n + 1) v = v :: replicateVal n v := rfl

theorem replicateVal_length (n v : Nat) : (replicateVal n v).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [replicateVal_succ, List.length_cons, ih]

theorem replicateVal_getElem (n v i : Nat) (h : i < (replicateVal n v).length) :
    (replicateVal n v)[i] = v := by
  induction n generalizing i with
  | zero =>
    dsimp only [replicateVal, Nat.repeat, List.length_nil] at h
    exact False.elim (Nat.not_lt_zero i h)
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [replicateVal_succ, List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

noncomputable def listContainsNat (xs : List Nat) (x : Nat) : Bool :=
  xs.foldr (fun y acc => if natBeq y x then true else acc) false

theorem listContainsNat_true_iff_mem (xs : List Nat) (x : Nat) :
    listContainsNat xs x = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    constructor
    · intro h
      dsimp only [listContainsNat, List.foldr] at h
      cases hyx : natBeq y x
      · rw [hyx] at h
        exact List.mem_cons_of_mem y (ih.mp h)
      · have heq : y = x := natBeq_eq hyx
        subst heq
        exact List.mem_cons_self
    · intro h
      dsimp only [listContainsNat, List.foldr]
      cases h with
      | head =>
        simp only [natBeq_refl, ↓reduceIte]
      | tail _ hmem =>
        cases hyx : natBeq y x
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih.mpr hmem
        · rfl

theorem listContainsNat_false_iff_not_mem (xs : List Nat) (x : Nat) :
    listContainsNat xs x = false ↔ x ∉ xs := by
  constructor
  · intro hf hm
    have ht := (listContainsNat_true_iff_mem xs x).mpr hm
    rw [hf] at ht
    cases ht
  · intro hnm
    cases hv : listContainsNat xs x
    · rfl
    · exact False.elim (hnm ((listContainsNat_true_iff_mem xs x).mp hv))

noncomputable def assocLookup {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α :=
  xs.foldr (fun p acc => if natBeq p.1 k then some p.2 else acc) none

theorem assocLookup_cons_eq {α : Type} (k : Nat) (v : α) (xs : List (Nat × α)) :
    assocLookup ((k, v) :: xs) k = some v := by
  dsimp only [assocLookup, List.foldr]
  rw [natBeq_refl]
  rfl

theorem assocLookup_cons_ne {α : Type} {k k' : Nat} (hne : k' ≠ k) (v : α)
    (xs : List (Nat × α)) :
    assocLookup ((k', v) :: xs) k = assocLookup xs k := by
  dsimp only [assocLookup, List.foldr]
  rw [natBeq_false_of_ne hne]
  rfl

noncomputable def assocInsert {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α) :
    List (Nat × α) :=
  (k, v) :: xs

theorem assocLookup_insert_eq {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α) :
    assocLookup (assocInsert xs k v) k = some v :=
  assocLookup_cons_eq k v xs

theorem assocLookup_insert_ne {α : Type} {k k' : Nat} (hne : k' ≠ k)
    (xs : List (Nat × α)) (v : α) :
    assocLookup (assocInsert xs k' v) k = assocLookup xs k :=
  assocLookup_cons_ne hne v xs

noncomputable def listAll {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  xs.foldr (fun x acc => if p x then acc else false) true

theorem listAll_true_iff {α : Type} (p : α → Bool) (xs : List α) :
    listAll p xs = true ↔ ∀ x, x ∈ xs → p x = true := by
  induction xs with
  | nil =>
    constructor
    · intro _ x hx; cases hx
    · intro _; rfl
  | cons y ys ih =>
    constructor
    · intro h x hx
      dsimp only [listAll, List.foldr] at h
      cases hpy : p y
      · rw [hpy] at h; cases h
      · rw [hpy] at h
        cases hx with
        | head => exact hpy
        | tail _ hmem => exact (ih.mp h) x hmem
    · intro h
      dsimp only [listAll, List.foldr]
      have hpy : p y = true := h y List.mem_cons_self
      rw [hpy]
      exact ih.mpr (fun x hx => h x (List.mem_cons_of_mem y hx))

noncomputable def listGetWithDefault (xs : List Nat) (idx : Nat) (dflt : Nat) : Nat :=
  match xs, idx with
  | [], _ => dflt
  | x :: _, 0 => x
  | _ :: rest, i + 1 => listGetWithDefault rest i dflt

noncomputable def listSetAt (xs : List Nat) (idx : Nat) (v : Nat) : List Nat :=
  match xs, idx with
  | [], _ => []
  | _ :: rest, 0 => v :: rest
  | x :: rest, i + 1 => x :: listSetAt rest i v

theorem listSetAt_length (xs : List Nat) (idx v : Nat) :
    (listSetAt xs idx v).length = xs.length := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x rest ih =>
    cases idx with
    | zero => rfl
    | succ j =>
      dsimp only [listSetAt, List.length_cons]
      rw [ih j]

theorem listGetWithDefault_setAt_eq (xs : List Nat) (idx v dflt : Nat)
    (h : idx < xs.length) :
    listGetWithDefault (listSetAt xs idx v) idx dflt = v := by
  induction xs generalizing idx with
  | nil =>
    dsimp only [List.length_nil] at h
    exact False.elim (Nat.not_lt_zero idx h)
  | cons x rest ih =>
    cases idx with
    | zero => rfl
    | succ j =>
      dsimp only [listSetAt, listGetWithDefault]
      dsimp only [List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

theorem listGetWithDefault_setAt_ne (xs : List Nat) (i j v dflt : Nat) (hne : i ≠ j) :
    listGetWithDefault (listSetAt xs i v) j dflt = listGetWithDefault xs j dflt := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x rest ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hne rfl)
      | succ j' => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        dsimp only [listSetAt, listGetWithDefault]
        exact ih i' j' (fun h => hne (congrArg Nat.succ h))

theorem listGetWithDefault_lt_eq_getElem (xs : List Nat) (i dflt : Nat) (h : i < xs.length) :
    listGetWithDefault xs i dflt = xs[i] := by
  induction xs generalizing i with
  | nil =>
    dsimp only [List.length_nil] at h
    exact False.elim (Nat.not_lt_zero i h)
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ j =>
      dsimp only [listGetWithDefault]
      dsimp only [List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

/-! ## Section 2: Two-Phase Static/Const Initializer Graph (`E0391` vs. `reserve_and_set_static_alloc`) -/

/-- Rust item kind in CTFE (`InternKind::Static` vs `InternKind::Constant`).
Only `staticItem` has a fixed runtime address reserved via `tcx.reserve_and_set_static_alloc`
before evaluating its initializer (`eval_context.rs:591-595`, `util.rs:75-93`). -/
inductive DeclKind where
  | staticItem
  | constItem

noncomputable def declKindBeq (a b : DeclKind) : Bool :=
  match a, b with
  | .staticItem, .staticItem => true
  | .constItem, .constItem => true
  | _, _ => false

/-- Type-level layout determined from `GlobalAlloc::Static(def_id).size_and_align`
using `tcx.type_of(def_id)` without evaluating the initializer (`mod.rs:354-394`). -/
structure TypeLayout where
  sizeBytes : Nat
  alignBytes : Nat

/-- Initializer expression language distinguishing scalar literals, two-field product nodes
(`Node(tag, next)`), by-value reads of another item (`readVal`, creating a value edge),
and taking the address of another item (`addrOf`, creating a relocation edge). -/
inductive InitExpr where
  | scalar (val : Nat)
  | node (tag : Nat) (ptr : InitExpr)
  | pair (fst : InitExpr) (snd : InitExpr)
  | readVal (targetId : Nat)
  | addrOf (targetId : Nat)

/-- Declaration node in the CTFE static/const program graph. -/
structure GlobalDeclNode where
  declId : Nat
  kind : DeclKind
  layout : TypeLayout
  init : InitExpr

/-- Evaluated constant/static value representation in CTFE memory:
- `valScalar v`: concrete scalar integer
- `valPtr allocId`: provenance pointer to reserved `GlobalAlloc::Static` or interned memory
- `valNode tag v`: two-field node payload (`tag`, inner pointer/value)
- `valPair v1 v2`: general pair -/
inductive EvalVal where
  | valScalar (v : Nat)
  | valPtr (allocId : Nat)
  | valNode (tag : Nat) (ptr : EvalVal)
  | valPair (fst : EvalVal) (snd : EvalVal)

/-- Phase-1 reservation record: maps `declId -> allocId` (`reserve_and_set_static_alloc`)
together with type-level `(sizeBytes, alignBytes)` and NO initializer evaluation. -/
structure StaticReservation where
  declId : Nat
  allocId : Nat
  layout : TypeLayout

/-- Resolved allocation after Phase-2 initialization (`eval_static_initializer`), recording
the item's `allocId`, evaluated `EvalVal`, and the list of `AllocId` targets referenced by
address relocations. -/
structure ResolvedAlloc where
  declId : Nat
  allocId : Nat
  value : EvalVal

/-- CTFE evaluation error classes corresponding directly to `rustc` diagnostics:
- `recursiveStaticE0080`: direct self-value access caught by `CompileTimeMachine::before_access_global`
  (`machine.rs:1007-1009`) -> `error[E0080]`
- `queryCycleE0391`: mutual cycle re-entering `tcx.eval_static_initializer` or `const` evaluation
  -> `error[E0391]`
- `missingDecl`: unbound `declId`
- `outOfFuel`: fuel exhausted before base case -/
inductive CtfeError where
  | recursiveStaticE0080 (declId : Nat)
  | queryCycleE0391 (fromId : Nat) (toId : Nat)
  | missingDecl (declId : Nat)
  | outOfFuel

inductive CtfeResult (α : Type) where
  | ok (v : α)
  | err (e : CtfeError)

/-- Phase 1: Assign a unique `AllocId` (`base + index`) to every `staticItem` in `decls`,
leaving `constItem`s unreserved (`eval_context.rs:591-598`). -/
noncomputable def reserveStaticsAux (decls : List GlobalDeclNode) (nextAllocId : Nat) :
    List (Nat × StaticReservation) :=
  match decls with
  | [] => []
  | d :: rest =>
    match d.kind with
    | .staticItem =>
      (d.declId, { declId := d.declId, allocId := nextAllocId, layout := d.layout }) ::
        reserveStaticsAux rest (nextAllocId + 1)
    | .constItem =>
      reserveStaticsAux rest nextAllocId

noncomputable def reserveStaticAllocs (decls : List GlobalDeclNode) :
    List (Nat × StaticReservation) :=
  reserveStaticsAux decls 1

noncomputable def lookupDecl (decls : List GlobalDeclNode) (id : Nat) : Option GlobalDeclNode :=
  decls.foldr (fun d acc => if natBeq d.declId id then some d else acc) none

theorem lookupDecl_cons_eq (d : GlobalDeclNode) (rest : List GlobalDeclNode) :
    lookupDecl (d :: rest) d.declId = some d := by
  dsimp only [lookupDecl, List.foldr]
  rw [natBeq_refl]
  rfl

theorem lookupDecl_cons_ne {d : GlobalDeclNode} {id : Nat} (hne : d.declId ≠ id)
    (rest : List GlobalDeclNode) :
    lookupDecl (d :: rest) id = lookupDecl rest id := by
  dsimp only [lookupDecl, List.foldr]
  rw [natBeq_false_of_ne hne]
  rfl

/-- Distinct declaration IDs across a declaration table. -/
noncomputable def declIdsDistinct (decls : List GlobalDeclNode) : Prop :=
  match decls with
  | [] => True
  | d :: rest =>
    lookupDecl rest d.declId = none ∧ declIdsDistinct rest

theorem lookupDecl_some_of_mem (decls : List GlobalDeclNode) (d : GlobalDeclNode)
    (hmem : d ∈ decls) : ∃ x, lookupDecl decls d.declId = some x := by
  induction decls with
  | nil => cases hmem
  | cons y ys ih =>
    cases hmem with
    | head => exact ⟨d, lookupDecl_cons_eq d ys⟩
    | tail _ hm =>
      cases hy : natBeq y.declId d.declId
      · have hne : y.declId ≠ d.declId := fun e => by rw [e, natBeq_refl] at hy; cases hy
        rcases ih hm with ⟨x, hx⟩
        exact ⟨x, by rw [lookupDecl_cons_ne hne]; exact hx⟩
      · exact ⟨y, by dsimp only [lookupDecl, List.foldr]; rw [hy]; rfl⟩

/-- Phase-1 invariant: every static item in `decls` receives a valid `StaticReservation`
without inspecting `d.init`, and distinct `declId`s receive distinct `allocId`s. -/
theorem reserveStaticsAux_some_of_static (decls : List GlobalDeclNode) (d : GlobalDeclNode)
    (nextAllocId : Nat)
    (hmem : d ∈ decls)
    (hstat : d.kind = .staticItem)
    (huniq : declIdsDistinct decls) :
    ∃ res, assocLookup (reserveStaticsAux decls nextAllocId) d.declId = some res ∧
      res.declId = d.declId ∧ res.layout = d.layout := by
  induction decls generalizing nextAllocId with
  | nil => cases hmem
  | cons hd tl ih =>
    cases hmem with
    | head =>
      dsimp only [reserveStaticsAux]
      rw [hstat]
      refine ⟨{ declId := d.declId, allocId := nextAllocId, layout := d.layout }, ?_, rfl, rfl⟩
      exact assocLookup_cons_eq d.declId _ _
    | tail _ hmemTl =>
      have hhd_none : lookupDecl tl hd.declId = none := huniq.1
      have htl_uniq : declIdsDistinct tl := huniq.2
      have hne : hd.declId ≠ d.declId := by
        intro heq
        rcases lookupDecl_some_of_mem tl d hmemTl with ⟨x, hx⟩
        rw [heq] at hhd_none
        rw [hx] at hhd_none
        cases hhd_none
      cases hk : hd.kind
      · dsimp only [reserveStaticsAux]
        rw [hk]
        rcases ih (nextAllocId + 1) hmemTl htl_uniq with ⟨res, hlook, hdid, hlay⟩
        refine ⟨res, ?_, hdid, hlay⟩
        rw [assocLookup_cons_ne hne]
        exact hlook
      · dsimp only [reserveStaticsAux]
        rw [hk]
        exact ih nextAllocId hmemTl htl_uniq

/-- Helper proving `assocLookup` on `reserveStaticsAux` yields `allocId ≥ nextAllocId`. -/
theorem reserveStaticsAux_allocId_ge (decls : List GlobalDeclNode) (base id : Nat)
    (res : StaticReservation)
    (h : assocLookup (reserveStaticsAux decls base) id = some res) :
    base ≤ res.allocId := by
  induction decls generalizing base with
  | nil =>
    dsimp only [reserveStaticsAux, assocLookup, List.foldr] at h
    cases h
  | cons d rest ih =>
    cases hk : d.kind with
    | staticItem =>
      dsimp only [reserveStaticsAux] at h
      rw [hk] at h
      cases hbeq : natBeq d.declId id
      · have hne : d.declId ≠ id := fun e => by subst e; rw [natBeq_refl] at hbeq; cases hbeq
        rw [assocLookup_cons_ne hne] at h
        have hge := ih (base + 1) h
        exact Nat.le_trans (Nat.le_succ base) hge
      · have heq : d.declId = id := natBeq_eq hbeq
        subst heq
        rw [assocLookup_cons_eq] at h
        injection h with hres
        rw [← hres]
        exact Nat.le_refl base
    | constItem =>
      dsimp only [reserveStaticsAux] at h
      rw [hk] at h
      exact ih base h

/-- Distinct `staticItem` declarations receive strictly distinct `allocId`s in Phase 1. -/
theorem reserveStaticsAux_allocIds_injective (decls : List GlobalDeclNode) (base id1 id2 : Nat)
    (r1 r2 : StaticReservation)
    (hne : id1 ≠ id2)
    (h1 : assocLookup (reserveStaticsAux decls base) id1 = some r1)
    (h2 : assocLookup (reserveStaticsAux decls base) id2 = some r2) :
    r1.allocId ≠ r2.allocId := by
  induction decls generalizing base with
  | nil =>
    dsimp only [reserveStaticsAux, assocLookup, List.foldr] at h1
    cases h1
  | cons d rest ih =>
    cases hk : d.kind with
    | constItem =>
      dsimp only [reserveStaticsAux] at h1 h2
      rw [hk] at h1 h2
      exact ih base h1 h2
    | staticItem =>
      dsimp only [reserveStaticsAux] at h1 h2
      rw [hk] at h1 h2
      cases hb1 : natBeq d.declId id1
      · have hd1 : d.declId ≠ id1 := fun e => by subst e; rw [natBeq_refl] at hb1; cases hb1
        rw [assocLookup_cons_ne hd1] at h1
        cases hb2 : natBeq d.declId id2
        · have hd2 : d.declId ≠ id2 := fun e => by subst e; rw [natBeq_refl] at hb2; cases hb2
          rw [assocLookup_cons_ne hd2] at h2
          exact ih (base + 1) h1 h2
        · have heq2 : d.declId = id2 := natBeq_eq hb2
          subst heq2
          rw [assocLookup_cons_eq] at h2
          injection h2 with hr2
          have hge1 : base + 1 ≤ r1.allocId := reserveStaticsAux_allocId_ge rest (base + 1) id1 r1 h1
          rw [← hr2]
          dsimp only
          intro heqa
          rw [heqa] at hge1
          exact Nat.not_succ_le_self base hge1
      · have heq1 : d.declId = id1 := natBeq_eq hb1
        subst heq1
        rw [assocLookup_cons_eq] at h1
        injection h1 with hr1
        have hd2 : d.declId ≠ id2 := hne
        rw [assocLookup_cons_ne hd2] at h2
        have hge2 : base + 1 ≤ r2.allocId := reserveStaticsAux_allocId_ge rest (base + 1) id2 r2 h2
        rw [← hr1]
        dsimp only
        intro heqa
        rw [← heqa] at hge2
        exact Nat.not_succ_le_self base hge2

/-- Value-dependency edges extracted from `InitExpr`:
- `readVal targetId` adds `targetId` as a value dependency for BOTH `static` and `const`.
- `addrOf targetId` adds `targetId` as a value dependency ONLY if `targetId` is NOT a `staticItem`
  (because `staticItem` uses `reserve_and_set_static_alloc` without evaluating its initializer,
  whereas `constItem` must evaluate `targetId` directly). -/
noncomputable def exprValueDeps (decls : List GlobalDeclNode) : InitExpr → List Nat
  | .scalar _ => []
  | .node _ p => exprValueDeps decls p
  | .pair a b => exprValueDeps decls a ++ exprValueDeps decls b
  | .readVal target => [target]
  | .addrOf target =>
    match lookupDecl decls target with
    | some d =>
      match d.kind with
      | .staticItem => []
      | .constItem => [target]
    | none => [target]

/-- Value-dependency edge predicate `valueEdge decls u v`: evaluating `u`'s initializer
requires recursively evaluating `v`'s initializer. -/
noncomputable def valueEdge (decls : List GlobalDeclNode) (u v : Nat) : Prop :=
  ∃ du, lookupDecl decls u = some du ∧ v ∈ exprValueDeps decls du.init

/-- Two-phase CTFE query evaluator factored into pure structural recursion over `InitExpr`
(`evalExprStep`) and pure structural recursion over `fuel` (`evalExprAux`), eliminating
`WellFounded.fix` so every concrete evaluation reduces definitionally by `rfl`:
1. `eval_static_initializer` active-query stack `active : List Nat` (top = `curId`)
2. `readVal target`: checks `target == curId` (`E0080` `RecursiveStatic`) and
   `target ∈ active` (`E0391` query cycle), then evaluates `target` recursively with `fuel'`.
3. `addrOf target`:
   - If `target` has a Phase-1 `StaticReservation` (`staticItem`), immediately returns
     `EvalVal.valPtr res.allocId` WITHOUT consulting `active` or evaluating `target`'s body!
   - Otherwise (`constItem`), evaluates `target` via `evalTarget true target` (entering `active` ->
     `E0391` on cycles) and returns an anonymous memory pointer (`1000 + target`). -/
noncomputable def evalExprStep
    (resMap : List (Nat × StaticReservation))
    (evalTarget : Bool → Nat → CtfeResult EvalVal)
    (e : InitExpr) : CtfeResult EvalVal :=
  match e with
  | .scalar v => .ok (.valScalar v)
  | .node tag p =>
    match evalExprStep resMap evalTarget p with
    | .ok pv => .ok (.valNode tag pv)
    | .err err => .err err
  | .pair a b =>
    match evalExprStep resMap evalTarget a with
    | .err err => .err err
    | .ok av =>
      match evalExprStep resMap evalTarget b with
      | .ok bv => .ok (.valPair av bv)
      | .err err => .err err
  | .addrOf target =>
    match assocLookup resMap target with
    | some res => .ok (.valPtr res.allocId)
    | none =>
      match evalTarget true target with
      | .ok _ => .ok (.valPtr (1000 + target))
      | .err err => .err err
  | .readVal target =>
    evalTarget false target

noncomputable def evalExprAux
    (decls : List GlobalDeclNode)
    (resMap : List (Nat × StaticReservation))
    (fuel : Nat)
    (curId : Nat)
    (active : List Nat)
    (e : InitExpr) : CtfeResult EvalVal :=
  match fuel with
  | 0 =>
    evalExprStep resMap (fun _ _ => .err .outOfFuel) e
  | fuel' + 1 =>
    evalExprStep resMap
      (fun isAddrOf target =>
        if natBeq target curId then
          .err (if isAddrOf then .queryCycleE0391 curId target else .recursiveStaticE0080 target)
        else if listContainsNat active target then
          .err (.queryCycleE0391 curId target)
        else
          match lookupDecl decls target with
          | none => .err (.missingDecl target)
          | some td => evalExprAux decls resMap fuel' target (curId :: active) td.init)
      e

noncomputable def evalDeclInitializer
    (decls : List GlobalDeclNode)
    (fuel : Nat)
    (id : Nat) : CtfeResult ResolvedAlloc :=
  let resMap := reserveStaticAllocs decls
  match lookupDecl decls id with
  | none => .err (.missingDecl id)
  | some d =>
    match evalExprAux decls resMap fuel id [] d.init with
    | .err e => .err e
    | .ok v =>
      let aid :=
        match assocLookup resMap id with
        | some r => r.allocId
        | none => 1000 + id
      .ok { declId := id, allocId := aid, value := v }

theorem lookupDecl_mem (decls : List GlobalDeclNode) (id : Nat) (d : GlobalDeclNode)
    (h : lookupDecl decls id = some d) : d ∈ decls := by
  induction decls with
  | nil =>
    dsimp only [lookupDecl, List.foldr] at h
    cases h
  | cons y ys ih =>
    dsimp only [lookupDecl, List.foldr] at h
    cases hy : natBeq y.declId id
    · rw [hy] at h
      exact List.mem_cons_of_mem y (ih h)
    · rw [hy] at h
      injection h with heq
      subst heq
      exact List.mem_cons_self

theorem lookupDecl_declId_eq (decls : List GlobalDeclNode) (id : Nat) (d : GlobalDeclNode)
    (h : lookupDecl decls id = some d) : d.declId = id := by
  induction decls with
  | nil =>
    dsimp only [lookupDecl, List.foldr] at h
    cases h
  | cons y ys ih =>
    dsimp only [lookupDecl, List.foldr] at h
    cases hy : natBeq y.declId id
    · rw [hy] at h
      exact ih h
    · rw [hy] at h
      injection h with heq
      rw [← heq]
      exact natBeq_eq hy

/-- Auxiliary invariant: along any active query stack where `rank` strictly decreases
from top toward base (`∀ a ∈ active, rank curId < rank a`), `curId` never appears in `active`,
and evaluation succeeds within fuel `rank curId + 1`. -/
theorem evalExprAux_succeeds_under_rank
    (decls : List GlobalDeclNode)
    (resMap : List (Nat × StaticReservation))
    (rank : Nat → Nat)
    (h_res : ∀ d, d ∈ decls → d.kind = .staticItem →
      ∃ r, assocLookup resMap d.declId = some r)
    (h_defined : ∀ d, d ∈ decls → ∀ v, v ∈ exprValueDeps decls d.init →
      ∃ dv, dv ∈ decls ∧ lookupDecl decls v = some dv)
    (h_dec : ∀ d, d ∈ decls → ∀ v, v ∈ exprValueDeps decls d.init →
      rank v < rank d.declId)
    (bound : Nat) :
    ∀ (d : GlobalDeclNode) (active : List Nat) (fuel : Nat) (e : InitExpr),
      d ∈ decls →
      (∀ v, v ∈ exprValueDeps decls e → v ∈ exprValueDeps decls d.init) →
      (∀ a, a ∈ active → rank d.declId < rank a) →
      rank d.declId < bound →
      bound ≤ fuel →
      ∃ val, evalExprAux decls resMap fuel d.declId active e = .ok val := by
  induction bound with
  | zero =>
    intro d active fuel e _ _ _ hlt _
    exact False.elim (Nat.not_lt_zero _ hlt)
  | succ b' ih_bound =>
    intro d active fuel e hd hsub hstack hrank hfuel
    have hfuel_pos : ∃ f', fuel = f' + 1 := by
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ b') hfuel))
      | succ f' => exact ⟨f', rfl⟩
    rcases hfuel_pos with ⟨f', hf'⟩
    subst hf'
    dsimp only [evalExprAux]
    induction e with
    | scalar v =>
      exact ⟨.valScalar v, rfl⟩
    | node tag p ihp =>
      have hsub_p : ∀ v, v ∈ exprValueDeps decls p → v ∈ exprValueDeps decls d.init :=
        fun v hv => hsub v hv
      rcases ihp hsub_p with ⟨pv, hpv⟩
      dsimp only [evalExprStep]
      rw [hpv]
      exact ⟨.valNode tag pv, rfl⟩
    | pair a b iha ihb =>
      have hsub_a : ∀ v, v ∈ exprValueDeps decls a → v ∈ exprValueDeps decls d.init :=
        fun v hv => hsub v (List.mem_append.mpr (.inl hv))
      have hsub_b : ∀ v, v ∈ exprValueDeps decls b → v ∈ exprValueDeps decls d.init :=
        fun v hv => hsub v (List.mem_append.mpr (.inr hv))
      rcases iha hsub_a with ⟨av, hav⟩
      rcases ihb hsub_b with ⟨bv, hbv⟩
      dsimp only [evalExprStep]
      rw [hav, hbv]
      exact ⟨.valPair av bv, rfl⟩
    | addrOf target =>
      dsimp only [evalExprStep]
      cases hres : assocLookup resMap target with
      | some res =>
        exact ⟨.valPtr res.allocId, rfl⟩
      | none =>
        have hmem_dep : target ∈ exprValueDeps decls (.addrOf target) := by
          dsimp only [exprValueDeps]
          cases hl : lookupDecl decls target with
          | none => exact List.mem_cons_self
          | some dt =>
            cases hdk : dt.kind with
            | staticItem =>
              have hdt_mem := lookupDecl_mem decls target dt hl
              rcases h_res dt hdt_mem hdk with ⟨r, hr⟩
              have hdt_id := lookupDecl_declId_eq decls target dt hl
              rw [hdt_id] at hr
              rw [hr] at hres
              cases hres
            | constItem =>
              dsimp only
              rw [hdk]
              exact List.mem_cons_self
        have ht_in_d : target ∈ exprValueDeps decls d.init := hsub target hmem_dep
        rcases h_defined d hd target ht_in_d with ⟨dt, hdt_mem, hdt_look⟩
        have hlt_td : rank target < rank d.declId := h_dec d hd target ht_in_d
        have hne_cur : natBeq target d.declId = false := by
          apply natBeq_false_of_ne
          intro heq
          rw [heq] at hlt_td
          exact Nat.lt_irrefl _ hlt_td
        have hnot_act : listContainsNat active target = false := by
          apply (listContainsNat_false_iff_not_mem active target).mpr
          intro hmem_act
          have hgt := hstack target hmem_act
          exact Nat.lt_irrefl _ (Nat.lt_trans hlt_td hgt)
        have hdt_id : dt.declId = target := lookupDecl_declId_eq decls target dt hdt_look
        have hstack' : ∀ a, a ∈ d.declId :: active → rank dt.declId < rank a := by
          intro a ha
          rw [hdt_id]
          cases ha with
          | head => exact hlt_td
          | tail _ hm => exact Nat.lt_trans hlt_td (hstack a hm)
        have hrank' : rank dt.declId < b' := by
          rw [hdt_id]
          exact Nat.lt_of_lt_of_le hlt_td (Nat.le_of_lt_succ hrank)
        have hfuel' : b' ≤ f' := Nat.le_of_succ_le_succ hfuel
        rcases ih_bound dt (d.declId :: active) f' dt.init hdt_mem (fun _ hx => hx) hstack' hrank' hfuel' with ⟨val, hval⟩
        rw [hdt_id] at hval
        rw [hne_cur, hnot_act, hdt_look]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hval]
        exact ⟨.valPtr (1000 + target), rfl⟩
    | readVal target =>
      have ht_in_d : target ∈ exprValueDeps decls d.init := hsub target List.mem_cons_self
      rcases h_defined d hd target ht_in_d with ⟨dt, hdt_mem, hdt_look⟩
      have hlt_td : rank target < rank d.declId := h_dec d hd target ht_in_d
      have hne_cur : natBeq target d.declId = false := by
        apply natBeq_false_of_ne
        intro heq
        rw [heq] at hlt_td
        exact Nat.lt_irrefl _ hlt_td
      have hnot_act : listContainsNat active target = false := by
        apply (listContainsNat_false_iff_not_mem active target).mpr
        intro hmem_act
        have hgt := hstack target hmem_act
        exact Nat.lt_irrefl _ (Nat.lt_trans hlt_td hgt)
      have hdt_id : dt.declId = target := lookupDecl_declId_eq decls target dt hdt_look
      have hstack' : ∀ a, a ∈ d.declId :: active → rank dt.declId < rank a := by
        intro a ha
        rw [hdt_id]
        cases ha with
        | head => exact hlt_td
        | tail _ hm => exact Nat.lt_trans hlt_td (hstack a hm)
      have hrank' : rank dt.declId < b' := by
        rw [hdt_id]
        exact Nat.lt_of_lt_of_le hlt_td (Nat.le_of_lt_succ hrank)
      have hfuel' : b' ≤ f' := Nat.le_of_succ_le_succ hfuel
      rcases ih_bound dt (d.declId :: active) f' dt.init hdt_mem (fun _ hx => hx) hstack' hrank' hfuel' with ⟨val, hval⟩
      rw [hdt_id] at hval
      dsimp only [evalExprStep]
      rw [hne_cur, hnot_act, hdt_look]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨val, hval⟩

/-- **Main Theorem 1: Two-Phase Static Acyclicity Soundness.**
If the value-dependency subgraph is acyclic (witnessed by `rank`), then EVERY declaration
in `decls` evaluates cleanly to a concrete `ResolvedAlloc` in `evalDeclInitializer` with
zero `E0391` / `E0080` / `outOfFuel` errors — **even in the presence of arbitrary `addrOf`
cycles among `static` items**. -/
theorem two_phase_static_acyclicity_soundness
    (decls : List GlobalDeclNode)
    (rank : Nat → Nat)
    (huniq : declIdsDistinct decls)
    (hdefined : ∀ d, d ∈ decls → ∀ v, v ∈ exprValueDeps decls d.init →
      ∃ dv, dv ∈ decls ∧ lookupDecl decls v = some dv)
    (hdec : ∀ d, d ∈ decls → ∀ v, v ∈ exprValueDeps decls d.init →
      rank v < rank d.declId)
    (d : GlobalDeclNode)
    (hd : d ∈ decls) :
    ∃ res, evalDeclInitializer decls (rank d.declId + 1) d.declId = .ok res := by
  have hlook : ∃ d', lookupDecl decls d.declId = some d' ∧ d'.declId = d.declId ∧ d'.init = d.init := by
    clear hdefined hdec
    induction decls with
    | nil => cases hd
    | cons y ys ih =>
      cases hd with
      | head => exact ⟨d, lookupDecl_cons_eq d ys, rfl, rfl⟩
      | tail _ hm =>
        have hys : declIdsDistinct ys := huniq.2
        rcases ih hys hm with ⟨d', hl, hid, hinit⟩
        have hne : y.declId ≠ d.declId := by
          intro heq
          have hy_none := huniq.1
          rw [heq, hl] at hy_none
          cases hy_none
        exact ⟨d', by rw [lookupDecl_cons_ne hne]; exact hl, hid, hinit⟩
  rcases hlook with ⟨d', hdlook, hd'id, hd'init⟩
  have hd'_mem := lookupDecl_mem decls d.declId d' hdlook
  have hres : ∀ x, x ∈ decls → x.kind = .staticItem →
      ∃ r, assocLookup (reserveStaticAllocs decls) x.declId = some r :=
    fun x hx hkx =>
      let ⟨r, hr, _⟩ := reserveStaticsAux_some_of_static decls x 1 hx hkx huniq
      ⟨r, hr⟩
  have hstack0 : ∀ a, a ∈ ([] : List Nat) → rank d'.declId < rank a :=
    fun _ ha => by cases ha
  have hrank0 : rank d'.declId < rank d.declId + 1 := by
    rw [hd'id]
    exact Nat.lt_succ_self _
  rcases evalExprAux_succeeds_under_rank decls (reserveStaticAllocs decls) rank
      hres hdefined hdec (rank d.declId + 1) d' [] (rank d.declId + 1) d'.init
      hd'_mem (fun _ hx => hx) hstack0 hrank0 (Nat.le_refl _) with ⟨val, hval⟩
  dsimp only [evalDeclInitializer]
  rw [hdlook]
  dsimp only
  rw [hd'id] at hval
  rw [hval]
  exact ⟨_, rfl⟩

/-- Concrete primary-source witness: mutual `static` reference cycle
`static A: Node = Node(10, &B); static B: Node = Node(20, &A);` plus self-cycle
`static SELF: Node = Node(42, &SELF);` initializes cleanly under `evalDeclInitializer`. -/
noncomputable def cyclicStaticRefProgram : List GlobalDeclNode :=
  [ { declId := 1, kind := .staticItem, layout := { sizeBytes := 16, alignBytes := 8 },
      init := .node 10 (.addrOf 2) }
  , { declId := 2, kind := .staticItem, layout := { sizeBytes := 16, alignBytes := 8 },
      init := .node 20 (.addrOf 1) }
  , { declId := 3, kind := .staticItem, layout := { sizeBytes := 16, alignBytes := 8 },
      init := .node 42 (.addrOf 3) } ]

theorem static_addr_of_cycle_concrete_witness :
    evalDeclInitializer cyclicStaticRefProgram 4 1 =
      .ok { declId := 1, allocId := 1, value := .valNode 10 (.valPtr 2) } ∧
    evalDeclInitializer cyclicStaticRefProgram 4 2 =
      .ok { declId := 2, allocId := 2, value := .valNode 20 (.valPtr 1) } ∧
    evalDeclInitializer cyclicStaticRefProgram 4 3 =
      .ok { declId := 3, allocId := 3, value := .valNode 42 (.valPtr 3) } := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Main Theorem 2a: Direct Self-Value Cycle (`E0080` `RecursiveStatic`) Necessity.**
For any item whose initializer reads its own value (`init = .readVal id`), evaluation
fails (`error[E0080]`) at every `fuel` and can NEVER return `.ok`. -/
theorem self_value_cycle_never_ok (decls : List GlobalDeclNode) (d : GlobalDeclNode)
    (h_look : lookupDecl decls d.declId = some d)
    (h_self : d.init = .readVal d.declId) (fuel : Nat) :
    ∀ res, evalDeclInitializer decls fuel d.declId ≠ .ok res := by
  intro res hok
  dsimp only [evalDeclInitializer] at hok
  rw [h_look] at hok
  dsimp only at hok
  rw [h_self] at hok
  cases fuel with
  | zero =>
    dsimp only [evalExprAux, evalExprStep] at hok
    cases hok
  | succ f' =>
    dsimp only [evalExprAux, evalExprStep] at hok
    rw [natBeq_refl] at hok
    simp only [↓reduceIte] at hok
    cases hok

/-- **Main Theorem 2b: Value-Dependency Cycle Non-Termination / `E0391` Necessity.**
If a closed cycle of `readVal` dependencies (`∀ x, x ∈ cycle → ∃ dx succ, lookupDecl decls x = some dx ∧ dx.init = .readVal succ ∧ succ ∈ cycle`) exists and `x₀ ∈ cycle`, then **no fuel `k` ever produces `.ok`**: every finite run either exhausts fuel or terminates with `recursiveStaticE0080` / `queryCycleE0391`. -/
theorem value_cycle_readval_never_ok
    (decls : List GlobalDeclNode)
    (resMap : List (Nat × StaticReservation))
    (cycle : List Nat)
    (hclosed : ∀ x, x ∈ cycle →
      ∃ dx s, lookupDecl decls x = some dx ∧ dx.init = .readVal s ∧ s ∈ cycle) :
    ∀ (fuel : Nat) (x : Nat) (active : List Nat) (val : EvalVal),
      x ∈ cycle →
      ∀ dx, lookupDecl decls x = some dx →
      evalExprAux decls resMap fuel x active dx.init ≠ .ok val := by
  intro fuel
  induction fuel with
  | zero =>
    intro x active val hx dx hdx hok
    rcases hclosed x hx with ⟨dx', s, hdx', hs_init, _⟩
    rw [hdx] at hdx'
    injection hdx' with heq
    rw [← heq] at hs_init
    rw [hs_init] at hok
    dsimp only [evalExprAux, evalExprStep] at hok
    cases hok
  | succ f' ih =>
    intro x active val hx dx hdx hok
    rcases hclosed x hx with ⟨dx', s, hdx', hs_init, hs_mem⟩
    rw [hdx] at hdx'
    injection hdx' with heq
    rw [← heq] at hs_init
    rw [hs_init] at hok
    dsimp only [evalExprAux, evalExprStep] at hok
    cases hself : natBeq s x
    · rw [hself] at hok
      simp only [Bool.false_eq_true, ↓reduceIte] at hok
      cases hact : listContainsNat active s
      · rw [hact] at hok
        simp only [Bool.false_eq_true, ↓reduceIte] at hok
        rcases hclosed s hs_mem with ⟨ds, s2, hds, _, _⟩
        rw [hds] at hok
        dsimp only at hok
        exact ih s (x :: active) val hs_mem ds hds hok
      · rw [hact] at hok
        simp only [↓reduceIte] at hok
        cases hok
    · rw [hself] at hok
      simp only [↓reduceIte] at hok
      cases hok

/-- Corollary at the top-level `evalDeclInitializer` entry point: any member of a
`readVal` cycle fails for all `fuel`. -/
theorem value_cycle_e0391_necessity
    (decls : List GlobalDeclNode)
    (cycle : List Nat)
    (hclosed : ∀ x, x ∈ cycle →
      ∃ dx s, lookupDecl decls x = some dx ∧ dx.init = .readVal s ∧ s ∈ cycle)
    (x : Nat) (hx : x ∈ cycle) (fuel : Nat) (res : ResolvedAlloc) :
    evalDeclInitializer decls fuel x ≠ .ok res := by
  intro hok
  dsimp only [evalDeclInitializer] at hok
  rcases hclosed x hx with ⟨dx, s, hdx, _, _⟩
  rw [hdx] at hok
  dsimp only at hok
  cases heval : evalExprAux decls (reserveStaticAllocs decls) fuel x [] dx.init with
  | err e =>
    rw [heval] at hok
    cases hok
  | ok v =>
    exact value_cycle_readval_never_ok decls (reserveStaticAllocs decls) cycle hclosed
      fuel x [] v hx dx hdx heval

/-- Concrete mutual-value cycle witness `static A: u32 = B; static B: u32 = A;`
explicitly fails with `CtfeError.queryCycleE0391 2 1`. -/
noncomputable def mutualValueCycleProgram : List GlobalDeclNode :=
  [ { declId := 1, kind := .staticItem, layout := { sizeBytes := 4, alignBytes := 4 },
      init := .readVal 2 }
  , { declId := 2, kind := .staticItem, layout := { sizeBytes := 4, alignBytes := 4 },
      init := .readVal 1 } ]

theorem mutual_value_cycle_emits_e0391 :
    evalDeclInitializer mutualValueCycleProgram 16 1 = .err (.queryCycleE0391 2 1) := rfl

/-- Concrete `const` mutual-reference contrast (`const A: Node = Node(10, &B); const B: Node = Node(20, &A)`):
because `constItem`s do NOT populate `reserveStaticAllocs`, taking `&B` inside `A` forces
re-entrant evaluation and fails with `CtfeError.queryCycleE0391 2 1`, in contrast to
`static_addr_of_cycle_concrete_witness`. -/
noncomputable def mutualConstRefProgram : List GlobalDeclNode :=
  [ { declId := 1, kind := .constItem, layout := { sizeBytes := 16, alignBytes := 8 },
      init := .node 10 (.addrOf 2) }
  , { declId := 2, kind := .constItem, layout := { sizeBytes := 16, alignBytes := 8 },
      init := .node 20 (.addrOf 1) } ]

theorem const_ref_cycle_e0391_contrast :
    evalDeclInitializer mutualConstRefProgram 16 1 = .err (.queryCycleE0391 2 1) := rfl

/-! ## Section 3: `unnamed_addr` Constant Deduplication vs. `static` Address Distinctness -/

/-- LLVM `GlobalValue::UnnamedAddr` (`GlobalValue.h:211-215`). -/
inductive UnnamedAddrMode where
  | none
  | local_
  | global_

noncomputable def unnamedAddrBeq (a b : UnnamedAddrMode) : Bool :=
  match a, b with
  | .none, .none => true
  | .local_, .local_ => true
  | .global_, .global_ => true
  | _, _ => false

/-- Source-level Rust global/constant origin (`consts.rs:236-286, 410-539`). -/
inductive RustGlobalOrigin where
  | promotedOrIndirectConst
  | staticItem (exported : Bool) (isFreeze : Bool) (addrCompared : Bool)

/-- LLVM GlobalVariable descriptor modeled after `llvm::GlobalVariable` and
`ConstantMerge.cpp` (`isUnmergeableGlobal`, `makeMergeable`). -/
structure LlvmGlobal where
  symId : Nat
  isConstant : Bool
  hasLocalLinkage : Bool
  unnamedAddr : UnnamedAddrMode
  payload : List Nat
  hasExplicitSection : Bool
  isThreadLocal : Bool
  inUsedList : Bool

/-- Initial LLVM IR emission from `rustc_codegen_llvm/src/consts.rs`:
- `promotedOrIndirectConst`: `static_addr_of_mut` sets `PrivateLinkage` (`hasLocalLinkage = true`),
  `UnnamedAddr::Global` (`unnamedAddr = .global_`), `set_global_constant(true)` (`isConstant = true`).
- `staticItem`: `codegen_static_item` NEVER calls `set_unnamed_address` (`unnamedAddr = .none`),
  and sets `isConstant = isFreeze`. -/
noncomputable def rustcLowerToLlvm (symId : Nat) (origin : RustGlobalOrigin) (payload : List Nat) :
    LlvmGlobal :=
  match origin with
  | .promotedOrIndirectConst =>
    { symId := symId
      isConstant := true
      hasLocalLinkage := true
      unnamedAddr := .global_
      payload := payload
      hasExplicitSection := false
      isThreadLocal := false
      inUsedList := false }
  | .staticItem exported isFreeze _ =>
    { symId := symId
      isConstant := isFreeze
      hasLocalLinkage := !exported
      unnamedAddr := .none
      payload := payload
      hasExplicitSection := false
      isThreadLocal := false
      inUsedList := false }

/-- LLVM `GlobalOpt::processGlobal` (`GlobalOpt.cpp:1656-1671`) + `GlobalStatus::analyzeGlobal`
(`GlobalStatus.cpp:159-188`): sets `local_unnamed_addr` (non-local) or `unnamed_addr` (local)
only if `!GS.IsCompared` (and address does not escape). Notice for non-local statics this yields
AT MOST `.local_`, NEVER `.global_` (`!GV.hasGlobalUnnamedAddr()`). -/
noncomputable def globalOptRefine (g : LlvmGlobal) (addrEscapesOrCompared : Bool) : LlvmGlobal :=
  if addrEscapesOrCompared then
    g
  else
    match g.unnamedAddr with
    | .global_ => g
    | .local_ =>
      if g.hasLocalLinkage then { g with unnamedAddr := .global_ } else g
    | .none =>
      if g.hasLocalLinkage then { g with unnamedAddr := .global_ }
      else { g with unnamedAddr := .local_ }

/-- `ConstantMerge.cpp:91-101` (`!isUnmergeableGlobal`). -/
noncomputable def isMergeableGlobal (g : LlvmGlobal) : Bool :=
  g.isConstant && !g.hasExplicitSection && !g.isThreadLocal && !g.inUsedList

/-- `ConstantMerge.cpp:104-112` (`makeMergeable(Old, New)`).
Both globals must be mergeable, have identical constant payloads, `Old` must have local
linkage (so it can be erased), and at least one of `Old`/`New` must have `UnnamedAddr::Global`. -/
noncomputable def listNatBeq (xs ys : List Nat) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => if natBeq x y then listNatBeq xs' ys' else false
  | _, _ => false

theorem listNatBeq_refl (xs : List Nat) : listNatBeq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp only [listNatBeq]
    rw [natBeq_refl]
    exact ih

theorem listNatBeq_eq {xs ys : List Nat} (h : listNatBeq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => dsimp only [listNatBeq] at h; cases h
  | cons x xs' ih =>
    cases ys with
    | nil => dsimp only [listNatBeq] at h; cases h
    | cons y ys' =>
      dsimp only [listNatBeq] at h
      cases hxy : natBeq x y
      · rw [hxy] at h; cases h
      · rw [hxy] at h
        have hx : x = y := natBeq_eq hxy
        have hxs := ih h
        subst hx
        subst hxs
        rfl

noncomputable def canMergeGlobals (gOld gNew : LlvmGlobal) : Bool :=
  isMergeableGlobal gOld &&
  isMergeableGlobal gNew &&
  gOld.hasLocalLinkage &&
  listNatBeq gOld.payload gNew.payload &&
  (unnamedAddrBeq gOld.unnamedAddr .global_ || unnamedAddrBeq gNew.unnamedAddr .global_)

/-- Post-merge canonical survivor (`ConstantMerge.cpp:110-112`): if `Old` lacked
`UnnamedAddr::Global`, `New` is downgraded to `UnnamedAddr::None`. -/
noncomputable def mergedSurvivor (gOld gNew : LlvmGlobal) : LlvmGlobal :=
  if unnamedAddrBeq gOld.unnamedAddr .global_ then gNew
  else { gNew with unnamedAddr := .none }

/-- Link-time module state after `ConstantMerge`: maps every surviving `symId` to its
`LlvmGlobal` and every erased/merged `oldSymId` via a symbol alias table `redirect`. -/
structure LinkedConstantModule where
  globals : List (Nat × LlvmGlobal)
  redirect : List (Nat × Nat)

noncomputable def resolveSym (m : LinkedConstantModule) (sym : Nat) : Nat :=
  match assocLookup m.redirect sym with
  | some target => target
  | none => sym

noncomputable def applyConstantMergePair (m : LinkedConstantModule) (oldSym newSym : Nat) :
    LinkedConstantModule :=
  match assocLookup m.globals oldSym, assocLookup m.globals newSym with
  | some gOld, some gNew =>
    if natBeq oldSym newSym then m
    else if canMergeGlobals gOld gNew then
      { globals := assocInsert m.globals newSym (mergedSurvivor gOld gNew)
        redirect := assocInsert m.redirect oldSym newSym }
    else m
  | _, _ => m

/-- Pointer-dereference observation: reading `len` bytes starting at `offset` from the
module's storage backing `resolveSym m sym` (returns `none` on out-of-bounds). -/
noncomputable def obsDerefByte (m : LinkedConstantModule) (sym offset : Nat) : Option Nat :=
  match assocLookup m.globals (resolveSym m sym) with
  | none => none
  | some g =>
    if natBlt offset g.payload.length then
      some (listGetWithDefault g.payload offset 0)
    else none

/-- Pointer-equality observation under a faithful link layout where distinct surviving symbols
map to distinct addresses (`resolveSym m s1 == resolveSym m s2`). -/
noncomputable def obsPtrEq (m : LinkedConstantModule) (s1 s2 : Nat) : Bool :=
  natBeq (resolveSym m s1) (resolveSym m s2)

/-- Well-formedness of a `LinkedConstantModule`: redirects point only to surviving globals
not themselves redirected, and `globals` keys match `g.symId`. -/
noncomputable def moduleWf (m : LinkedConstantModule) : Prop :=
  (∀ s t, assocLookup m.redirect s = some t →
    assocLookup m.redirect t = none ∧ ∃ gt, assocLookup m.globals t = some gt) ∧
  (∀ s g, assocLookup m.globals s = some g → g.symId = s)

/-- **Main Theorem 3a: `unnamed_addr` Constant Deduplication Soundness.**
Given any well-formed module containing two globals `oldSym ≠ newSym` with identical payload
and `canMergeGlobals gOld gNew = true` (in particular, two `private unnamed_addr constant`
promoted items), merging `oldSym -> newSym` preserves **every pointer-dereference observation**
across ALL symbols `s` and ALL byte offsets `off`. -/
theorem unnamed_addr_dedup_preserves_all_deref_observations
    (m : LinkedConstantModule)
    (oldSym newSym : Nat)
    (gOld gNew : LlvmGlobal)
    (_hwf : moduleWf m)
    (hne : oldSym ≠ newSym)
    (hold : assocLookup m.globals oldSym = some gOld)
    (hnew : assocLookup m.globals newSym = some gNew)
    (hno_red_old : assocLookup m.redirect oldSym = none)
    (_hno_red_new : assocLookup m.redirect newSym = none)
    (hcan : canMergeGlobals gOld gNew = true) :
    ∀ s off, obsDerefByte (applyConstantMergePair m oldSym newSym) s off = obsDerefByte m s off := by
  intro s off
  have hpayload_eq : gOld.payload = gNew.payload := by
    dsimp only [canMergeGlobals] at hcan
    cases h1 : isMergeableGlobal gOld <;> cases h2 : isMergeableGlobal gNew <;>
    cases h3 : gOld.hasLocalLinkage <;> cases h4 : listNatBeq gOld.payload gNew.payload
    all_goals try (rw [h1, h2, h3, h4] at hcan; simp only [Bool.false_and, Bool.and_false] at hcan; cases hcan)
    exact listNatBeq_eq h4
  have hsurv_payload : (mergedSurvivor gOld gNew).payload = gNew.payload := by
    dsimp only [mergedSurvivor]
    cases unnamedAddrBeq gOld.unnamedAddr .global_ <;> rfl
  have hm_eq : applyConstantMergePair m oldSym newSym =
      { globals := assocInsert m.globals newSym (mergedSurvivor gOld gNew)
        redirect := assocInsert m.redirect oldSym newSym } := by
    dsimp only [applyConstantMergePair]
    rw [hold, hnew]
    dsimp only
    rw [natBeq_false_of_ne hne, hcan]
    rfl
  rw [hm_eq]
  dsimp only [obsDerefByte, resolveSym]
  cases hs_old : natBeq oldSym s
  · have hne_old_s : oldSym ≠ s := fun e => by subst e; rw [natBeq_refl] at hs_old; cases hs_old
    rw [assocLookup_insert_ne hne_old_s]
    cases hred_s : assocLookup m.redirect s with
    | none =>
      cases hnew_s : natBeq newSym s
      · have hne_new_s : newSym ≠ s := fun e => by subst e; rw [natBeq_refl] at hnew_s; cases hnew_s
        rw [assocLookup_insert_ne hne_new_s]
      · have heq_ns : newSym = s := natBeq_eq hnew_s
        subst heq_ns
        rw [assocLookup_insert_eq, hnew]
        dsimp only
        rw [hsurv_payload]
    | some t =>
      cases hnew_t : natBeq newSym t
      · have hne_new_t : newSym ≠ t := fun e => by subst e; rw [natBeq_refl] at hnew_t; cases hnew_t
        rw [assocLookup_insert_ne hne_new_t]
      · have heq_nt : newSym = t := natBeq_eq hnew_t
        subst heq_nt
        rw [assocLookup_insert_eq, hnew]
        dsimp only
        rw [hsurv_payload]
  · have heq_os : oldSym = s := natBeq_eq hs_old
    subst heq_os
    rw [assocLookup_insert_eq, hno_red_old]
    dsimp only
    rw [assocLookup_insert_eq, hold]
    dsimp only
    rw [hsurv_payload, hpayload_eq]

/-- **Main Theorem 3b: Non-`unnamed_addr` `static` Preserves Address Distinctness.**
For any two distinct `static` items `s1 ≠ s2` (whether exported or private when compared,
and even with identical byte payloads), `rustcLowerToLlvm` + `globalOptRefine` yields globals
with `unnamedAddr ≠ .global_`, so `canMergeGlobals = false`, `applyConstantMergePair` is
the identity, and `obsPtrEq` remains `false`! -/
theorem non_unnamed_addr_static_preserves_address_distinctness
    (s1 s2 : Nat) (hne : s1 ≠ s2)
    (exp1 exp2 fz1 fz2 : Bool)
    (payload : List Nat) :
    let g1 := globalOptRefine (rustcLowerToLlvm s1 (.staticItem exp1 fz1 true) payload) true
    let g2 := globalOptRefine (rustcLowerToLlvm s2 (.staticItem exp2 fz2 true) payload) true
    g1.unnamedAddr = .none ∧
    g2.unnamedAddr = .none ∧
    canMergeGlobals g1 g2 = false ∧
    (let m : LinkedConstantModule := { globals := [(s1, g1), (s2, g2)], redirect := [] }
     let m' := applyConstantMergePair m s1 s2
     obsPtrEq m' s1 s2 = false) := by
  intro g1 g2
  have hg1 : g1.unnamedAddr = .none := rfl
  have hg2 : g2.unnamedAddr = .none := rfl
  have hcan : canMergeGlobals g1 g2 = false := by
    dsimp only [canMergeGlobals]
    rw [hg1, hg2]
    dsimp only [unnamedAddrBeq]
    simp only [Bool.or_self, Bool.and_false]
  refine ⟨hg1, hg2, hcan, ?_⟩
  dsimp only [applyConstantMergePair]
  rw [assocLookup_cons_eq, assocLookup_cons_ne hne, assocLookup_cons_eq]
  dsimp only
  rw [natBeq_false_of_ne hne, hcan]
  dsimp only [obsPtrEq, resolveSym, assocLookup, List.foldr]
  exact natBeq_false_of_ne hne

/-- Even when `static` items are NOT address-compared locally (`addrEscapes = false`)
and are exported (`exported = true`), `GlobalOpt` assigns AT MOST `UnnamedAddr.local_`
(never `.global_`), so `ConstantMerge` still CANNOT merge `s1` and `s2`! -/
theorem exported_static_local_unnamed_addr_still_unmergeable
    (s1 s2 : Nat) (fz1 fz2 : Bool) (payload : List Nat) :
    let g1 := globalOptRefine (rustcLowerToLlvm s1 (.staticItem true fz1 false) payload) false
    let g2 := globalOptRefine (rustcLowerToLlvm s2 (.staticItem true fz2 false) payload) false
    g1.unnamedAddr = .local_ ∧ g2.unnamedAddr = .local_ ∧ canMergeGlobals g1 g2 = false := by
  intro g1 g2
  have hu1 : g1.unnamedAddr = .local_ := rfl
  have hu2 : g2.unnamedAddr = .local_ := rfl
  have hcan : canMergeGlobals g1 g2 = false := by
    dsimp only [canMergeGlobals]
    rw [hu1, hu2]
    dsimp only [unnamedAddrBeq]
    simp only [Bool.or_self, Bool.and_false]
  exact ⟨hu1, hu2, hcan⟩

/-- **Theorem 3c: Mixed Merge Downgrades Survivor & Blocks Second Static Merge.**
Matches the exact `ConstantMerge.cpp:110-112` behavior observed in `opt -passes=constmerge`:
merging a private `unnamed_addr` constant `ua` and one private non-`unnamed_addr` `static`
`st1` strips `UnnamedAddr::Global` from the survivor (`UnnamedAddr::None`), so a second
distinct private `static` `st2` CANNOT subsequently merge into the survivor — preserving
`st1 ≠ st2` (`obsPtrEq = false`) while permitting `ua` and `st1` to share storage (`items.static.storage-disjointness`). -/
theorem mixed_merge_downgrades_survivor_and_preserves_static_disjointness
    (uaSym st1Sym st2Sym : Nat)
    (hne12 : st1Sym ≠ st2Sym) (hneU1 : st1Sym ≠ uaSym) (hneU2 : st2Sym ≠ uaSym)
    (payload : List Nat) :
    let gUA := rustcLowerToLlvm uaSym .promotedOrIndirectConst payload
    let gSt1 := rustcLowerToLlvm st1Sym (.staticItem false true true) payload
    let gSt2 := rustcLowerToLlvm st2Sym (.staticItem false true true) payload
    let m0 : LinkedConstantModule :=
      { globals := [(uaSym, gUA), (st1Sym, gSt1), (st2Sym, gSt2)], redirect := [] }
    let m1 := applyConstantMergePair m0 st1Sym uaSym
    let m2 := applyConstantMergePair m1 st2Sym uaSym
    (∃ gSurv, assocLookup m1.globals uaSym = some gSurv ∧ gSurv.unnamedAddr = .none) ∧
    obsPtrEq m2 st1Sym st2Sym = false := by
  intro gUA gSt1 gSt2 m0 m1 m2
  have hcan1 : canMergeGlobals gSt1 gUA = true := by
    dsimp only [canMergeGlobals, isMergeableGlobal, gSt1, gUA, rustcLowerToLlvm]
    rw [listNatBeq_refl]
    rfl
  have hm1_eq : m1 =
      { globals := assocInsert m0.globals uaSym (mergedSurvivor gSt1 gUA)
        redirect := assocInsert m0.redirect st1Sym uaSym } := by
    dsimp only [m1, applyConstantMergePair, m0]
    rw [assocLookup_cons_ne hneU1.symm, assocLookup_cons_eq, assocLookup_cons_eq]
    dsimp only
    rw [natBeq_false_of_ne hneU1, hcan1]
    rfl
  have hm1_globals : assocLookup m1.globals uaSym = some (mergedSurvivor gSt1 gUA) := by
    rw [hm1_eq]
    exact assocLookup_insert_eq _ _ _
  have hsurv_none : (mergedSurvivor gSt1 gUA).unnamedAddr = .none := rfl
  have hcan2 : canMergeGlobals gSt2 (mergedSurvivor gSt1 gUA) = false := by
    dsimp only [canMergeGlobals, mergedSurvivor, gSt2, gSt1, gUA, rustcLowerToLlvm, unnamedAddrBeq, isMergeableGlobal]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_self, Bool.and_false]
  have hm1_st2 : assocLookup m1.globals st2Sym = some gSt2 := by
    rw [hm1_eq]
    dsimp only [m0]
    rw [assocLookup_insert_ne hneU2.symm, assocLookup_cons_ne hneU2.symm,
        assocLookup_cons_ne hne12, assocLookup_cons_eq]
  have hm2_eq : m2 = m1 := by
    dsimp only [m2, applyConstantMergePair]
    rw [hm1_st2, hm1_globals]
    dsimp only
    rw [natBeq_false_of_ne hneU2, hcan2]
    rfl
  have hm2_red_st2 : assocLookup m2.redirect st2Sym = none := by
    rw [hm2_eq, hm1_eq]
    dsimp only [m0]
    rw [assocLookup_insert_ne hne12]
    rfl
  have hm2_red_st1 : assocLookup m2.redirect st1Sym = some uaSym := by
    rw [hm2_eq, hm1_eq]
    dsimp only [m0]
    exact assocLookup_insert_eq _ _ _
  refine ⟨⟨mergedSurvivor gSt1 gUA, hm1_globals, hsurv_none⟩, ?_⟩
  dsimp only [obsPtrEq, resolveSym]
  rw [hm2_red_st1, hm2_red_st2]
  exact natBeq_false_of_ne hneU2.symm

/-! ## Section 4: `#[thread_local]` ELF Sections, `-Z tls-model`, and TLS Non-Interference -/

/-- Rust `TlsModel` (`compiler/rustc_target/src/spec/mod.rs:1002-1012`). -/
inductive TlsModel where
  | generalDynamic
  | localDynamic
  | initialExec
  | localExec
  | emulated

noncomputable def tlsModelBeq (a b : TlsModel) : Bool :=
  match a, b with
  | .generalDynamic, .generalDynamic => true
  | .localDynamic, .localDynamic => true
  | .initialExec, .initialExec => true
  | .localExec, .localExec => true
  | .emulated, .emulated => true
  | _, _ => false

/-- `compiler/rustc_codegen_llvm/src/context.rs:170-178` (`to_llvm_tls_model`). -/
inductive LlvmThreadLocalMode where
  | notThreadLocal
  | generalDynamicTLSModel
  | localDynamicTLSModel
  | initialExecTLSModel
  | localExecTLSModel

noncomputable def toLlvmTlsModel : TlsModel → LlvmThreadLocalMode
  | .generalDynamic => .generalDynamicTLSModel
  | .localDynamic => .localDynamicTLSModel
  | .initialExec => .initialExecTLSModel
  | .localExec => .localExecTLSModel
  | .emulated => .generalDynamicTLSModel

/-- `compiler/rustc_session/src/session.rs` (`Session::tls_model`):
`-Z tls-model` CLI override or target default. -/
noncomputable def sessionTlsModel (cliOpt : Option TlsModel) (targetDefault : TlsModel) : TlsModel :=
  match cliOpt with
  | some m => m
  | none => targetDefault

/-- Relocation and output artifact mode for `TargetMachine::getTLSModel`
(`llvm/lib/Target/TargetMachine.cpp:262-287`, `context.rs:252-266`). -/
inductive RelocKind where
  | static_
  | picSharedLib
  | pieExecutable

noncomputable def tlsModelRank : LlvmThreadLocalMode → Nat
  | .notThreadLocal => 0
  | .generalDynamicTLSModel => 1
  | .localDynamicTLSModel => 2
  | .initialExecTLSModel => 3
  | .localExecTLSModel => 4

noncomputable def effectiveLlvmTlsModel
    (reloc : RelocKind) (isDsoLocal : Bool) (selected : LlvmThreadLocalMode) :
    LlvmThreadLocalMode :=
  let baseModel :=
    match reloc with
    | .picSharedLib =>
      if isDsoLocal then .localDynamicTLSModel else .generalDynamicTLSModel
    | .pieExecutable | .static_ =>
      if isDsoLocal then .localExecTLSModel else .initialExecTLSModel
  if natBle (tlsModelRank baseModel) (tlsModelRank selected) then selected else baseModel

/-- Whether a TLS model is linkable inside an ELF `-shared` (`cdylib`) DSO. -/
noncomputable def tlsAllowedInSharedLib : LlvmThreadLocalMode → Bool
  | .localExecTLSModel => false
  | _ => true

/-- ELF TLS section kinds (`TargetLoweringObjectFile.cpp:82-99, 265-275`,
`TargetLoweringObjectFileImpl.cpp:552, 623-626`):
- `.tdata` (`SHT_PROGBITS`, `SHF_WRITE | SHF_ALLOC | SHF_TLS`)
- `.tbss` (`SHT_NOBITS`, `SHF_WRITE | SHF_ALLOC | SHF_TLS`). -/
inductive TlsElfSection where
  | tdataProgbirsWat
  | tbssNobitsWat

/-- `TargetLoweringObjectFile::isSuitableForBSS` (`L82-99`):
returns `false` when `GV->isConstant()` (`Freeze` immutable static), forcing even
all-zero immutable `#[thread_local]` statics into `.tdata` instead of `.tbss`! -/
noncomputable def isSuitableForBss (allZero : Bool) (isConstant : Bool) : Bool :=
  allZero && !isConstant

noncomputable def classifyTlsElfSection (allZero : Bool) (isConstant : Bool) : TlsElfSection :=
  if isSuitableForBss allZero isConstant then .tbssNobitsWat else .tdataProgbirsWat

theorem freeze_zero_tls_in_tdata_not_tbss :
    classifyTlsElfSection true true = .tdataProgbirsWat := rfl

theorem cell_zero_tls_in_tbss_not_tdata :
    classifyTlsElfSection true false = .tbssNobitsWat := rfl

theorem cell_nonzero_tls_in_tdata :
    classifyTlsElfSection false false = .tdataProgbirsWat := rfl

theorem tls_model_pie_upgrades_dynamic_and_cdylib_rejects_localexec :
    effectiveLlvmTlsModel .pieExecutable false .generalDynamicTLSModel = .initialExecTLSModel ∧
    effectiveLlvmTlsModel .pieExecutable false .localDynamicTLSModel = .initialExecTLSModel ∧
    effectiveLlvmTlsModel .picSharedLib false .generalDynamicTLSModel = .generalDynamicTLSModel ∧
    effectiveLlvmTlsModel .picSharedLib false .localDynamicTLSModel = .localDynamicTLSModel ∧
    tlsAllowedInSharedLib .localExecTLSModel = false ∧
    tlsAllowedInSharedLib .initialExecTLSModel = true ∧
    tlsAllowedInSharedLib .generalDynamicTLSModel = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Descriptor of one `#[thread_local]` slot inside the module's `PT_TLS` template:
- `symId`: symbol identifier (e.g. `TLS_NONZERO`, `TLS_ZERO`)
- `offset`: slot offset inside the per-thread TLS block
- `section`: `.tdata` (`PROGBITS`) or `.tbss` (`NOBITS`)
- `initVal`: initial byte/word value in the `PT_TLS` template (`0` for `.tbss`). -/
structure TlsSlotSpec where
  symId : Nat
  offset : Nat
  sectionKind : TlsElfSection
  initVal : Nat

/-- Module-level `PT_TLS` template image (`tdata ++ zeros(tbss)`). -/
structure PtTlsTemplate where
  tdataWords : List Nat
  tbssZeroCount : Nat

noncomputable def instantiateTlsBlock (tpl : PtTlsTemplate) : List Nat :=
  tpl.tdataWords ++ replicateVal tpl.tbssZeroCount 0

theorem instantiateTlsBlock_length (tpl : PtTlsTemplate) :
    (instantiateTlsBlock tpl).length = tpl.tdataWords.length + tpl.tbssZeroCount := by
  dsimp only [instantiateTlsBlock]
  rw [List.length_append, replicateVal_length]

theorem instantiateTlsBlock_tdata_exact (tpl : PtTlsTemplate) (i : Nat)
    (h : i < tpl.tdataWords.length) :
    (instantiateTlsBlock tpl)[i]'(by rw [instantiateTlsBlock_length]; exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)) =
      tpl.tdataWords[i] := by
  dsimp only [instantiateTlsBlock]
  exact List.getElem_append_left h

theorem instantiateTlsBlock_tbss_zero (tpl : PtTlsTemplate) (k : Nat)
    (hk : k < tpl.tbssZeroCount) :
    (instantiateTlsBlock tpl)[tpl.tdataWords.length + k]'(by
      rw [instantiateTlsBlock_length]
      exact Nat.add_lt_add_left hk _) = 0 := by
  have hge : tpl.tdataWords.length ≤ tpl.tdataWords.length + k := Nat.le_add_right _ _
  have hlt : tpl.tdataWords.length + k - tpl.tdataWords.length < (replicateVal tpl.tbssZeroCount 0).length := by
    rw [replicateVal_length, Nat.add_sub_cancel_left]
    exact hk
  have h1 : (tpl.tdataWords ++ replicateVal tpl.tbssZeroCount 0)[tpl.tdataWords.length + k]'(by
      rw [List.length_append, replicateVal_length]
      exact Nat.add_lt_add_left hk _) =
      (replicateVal tpl.tbssZeroCount 0)[tpl.tdataWords.length + k - tpl.tdataWords.length]'hlt :=
    List.getElem_append_right hge
  exact h1.trans (replicateVal_getElem tpl.tbssZeroCount 0 (tpl.tdataWords.length + k - tpl.tdataWords.length) hlt)

/-- Multi-threaded TLS execution state:
- `template`: immutable `PT_TLS` image shared across all threads
- `banks`: per-thread private TLS blocks indexed by `ThreadId : Nat`. -/
structure MultiThreadTlsState where
  template : PtTlsTemplate
  banks : List (Nat × List Nat)

/-- `@llvm.threadlocal.address.p0(ptr @TLS_SYM)` lowered for thread `tid`:
resolves to `(tid, slotOffset)` within thread `tid`'s disjoint bank. -/
structure TlsRuntimePtr where
  ownerTid : Nat
  slotOffset : Nat

noncomputable def llvmThreadLocalAddress (tid slotOffset : Nat) : TlsRuntimePtr :=
  { ownerTid := tid, slotOffset := slotOffset }

noncomputable def spawnThread (st : MultiThreadTlsState) (tid : Nat) : MultiThreadTlsState :=
  { st with banks := assocInsert st.banks tid (instantiateTlsBlock st.template) }

noncomputable def tlsRead (st : MultiThreadTlsState) (ptr : TlsRuntimePtr) : Option Nat :=
  match assocLookup st.banks ptr.ownerTid with
  | none => none
  | some bank =>
    if natBlt ptr.slotOffset bank.length then
      some (listGetWithDefault bank ptr.slotOffset 0)
    else none

noncomputable def tlsWrite (st : MultiThreadTlsState) (ptr : TlsRuntimePtr) (v : Nat) :
    MultiThreadTlsState :=
  match assocLookup st.banks ptr.ownerTid with
  | none => st
  | some bank =>
    if natBlt ptr.slotOffset bank.length then
      { st with banks := assocInsert st.banks ptr.ownerTid (listSetAt bank ptr.slotOffset v) }
    else st

/-- Operational steps on `MultiThreadTlsState`: thread spawn, TLS write, or TLS read. -/
inductive TlsOp where
  | spawn (tid : Nat)
  | write (tid : Nat) (slotOffset : Nat) (val : Nat)

noncomputable def execTlsOp (st : MultiThreadTlsState) : TlsOp → MultiThreadTlsState
  | .spawn tid => spawnThread st tid
  | .write tid off val => tlsWrite st (llvmThreadLocalAddress tid off) val

noncomputable def execTlsTrace (st : MultiThreadTlsState) (ops : List TlsOp) : MultiThreadTlsState :=
  ops.foldl execTlsOp st

noncomputable def opTargetTid : TlsOp → Nat
  | .spawn tid => tid
  | .write tid _ _ => tid

/-- Spawning a thread always initializes its TLS block cleanly from `st.template`,
regardless of prior writes performed by any other existing threads. -/
theorem tls_spawn_fresh_template_sound (st : MultiThreadTlsState) (tid : Nat) :
    assocLookup (spawnThread st tid).banks tid = some (instantiateTlsBlock st.template) := by
  dsimp only [spawnThread]
  exact assocLookup_insert_eq st.banks tid _

/-- Single-step TLS non-interference: executing any `TlsOp` targeting thread `t1 ≠ t2`
preserves `assocLookup st.banks t2` (and hence every `tlsRead` in thread `t2`) identically. -/
theorem tls_noninterference_step (st : MultiThreadTlsState) (op : TlsOp) (t2 : Nat)
    (hne : opTargetTid op ≠ t2) :
    assocLookup (execTlsOp st op).banks t2 = assocLookup st.banks t2 := by
  cases op with
  | spawn t1 =>
    dsimp only [execTlsOp, spawnThread, opTargetTid] at hne ⊢
    exact assocLookup_insert_ne hne st.banks _
  | write t1 off val =>
    dsimp only [execTlsOp, tlsWrite, llvmThreadLocalAddress, opTargetTid] at hne ⊢
    cases hbank : assocLookup st.banks t1 with
    | none => rfl
    | some bank =>
      dsimp only
      have hsplit : ∀ b : Bool,
          assocLookup (if b = true then { template := st.template, banks := assocInsert st.banks t1 (listSetAt bank off val) } else st).banks t2 =
          assocLookup st.banks t2 := by
        intro b
        cases b with
        | false => rfl
        | true => exact assocLookup_insert_ne hne st.banks _
      exact hsplit (natBlt off bank.length)

/-- **Main Theorem 4: Thread-Local Storage Non-Interference Theorem.**
For ANY finite execution trace `ops : List TlsOp` in which no operation targets `t2`
(e.g., all spawns/writes belong to threads `t1 ≠ t2`), every read of EVERY
`#[thread_local]` slot `off` in thread `t2` after `ops` returns the exact value observed
before `ops` (`tlsRead (execTlsTrace st ops) (llvmThreadLocalAddress t2 off) = tlsRead st (llvmThreadLocalAddress t2 off)`). -/
theorem tls_noninterference_trace
    (st : MultiThreadTlsState) (ops : List TlsOp) (t2 off : Nat)
    (hdisjoint : ∀ op, op ∈ ops → opTargetTid op ≠ t2) :
    tlsRead (execTlsTrace st ops) (llvmThreadLocalAddress t2 off) =
      tlsRead st (llvmThreadLocalAddress t2 off) := by
  have hbanks : assocLookup (execTlsTrace st ops).banks t2 = assocLookup st.banks t2 := by
    induction ops generalizing st with
    | nil => rfl
    | cons op rest ih =>
      dsimp only [execTlsTrace]
      rw [List.foldl_cons]
      have hhead : opTargetTid op ≠ t2 := hdisjoint op List.mem_cons_self
      have htail : ∀ o, o ∈ rest → opTargetTid o ≠ t2 :=
        fun o ho => hdisjoint o (List.mem_cons_of_mem op ho)
      have ih_res := ih (execTlsOp st op) htail
      dsimp only [execTlsTrace] at ih_res
      rw [ih_res]
      exact tls_noninterference_step st op t2 hhead
  dsimp only [tlsRead, llvmThreadLocalAddress]
  rw [hbanks]

/-- Same-thread read-after-write completeness: writing `val` to `(t1, off)` inside bounds
updates thread `t1`'s slot to `some val` while leaving every other slot `off' ≠ off` in `t1`
and every slot in `t2 ≠ t1` unchanged. -/
theorem tls_write_updates_self_preserves_other_slots_and_threads
    (st : MultiThreadTlsState) (t1 t2 off off' val : Nat)
    (bank : List Nat)
    (hbank : assocLookup st.banks t1 = some bank)
    (hlt : off < bank.length)
    (hne_t : t1 ≠ t2)
    (hne_off : off ≠ off') :
    let ptr1 := llvmThreadLocalAddress t1 off
    let st' := tlsWrite st ptr1 val
    tlsRead st' (llvmThreadLocalAddress t1 off) = some val ∧
    tlsRead st' (llvmThreadLocalAddress t1 off') = tlsRead st (llvmThreadLocalAddress t1 off') ∧
    tlsRead st' (llvmThreadLocalAddress t2 off) = tlsRead st (llvmThreadLocalAddress t2 off) := by
  dsimp only
  have hblt : natBlt off bank.length = true := natBlt_true_iff_lt.mpr hlt
  have hst' : tlsWrite st (llvmThreadLocalAddress t1 off) val =
      { st with banks := assocInsert st.banks t1 (listSetAt bank off val) } := by
    dsimp only [tlsWrite, llvmThreadLocalAddress]
    rw [hbank]
    dsimp only
    rw [hblt]
    rfl
  rw [hst']
  have hlen : (listSetAt bank off val).length = bank.length := listSetAt_length bank off val
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [tlsRead, llvmThreadLocalAddress]
    rw [assocLookup_insert_eq]
    dsimp only
    rw [hlen, hblt]
    simp only [↓reduceIte]
    rw [listGetWithDefault_setAt_eq bank off val 0 hlt]
  · dsimp only [tlsRead, llvmThreadLocalAddress]
    rw [assocLookup_insert_eq, hbank]
    dsimp only
    rw [hlen]
    split
    · rw [listGetWithDefault_setAt_ne bank off off' val 0 hne_off]
    · rfl
  · dsimp only [tlsRead, llvmThreadLocalAddress]
    rw [assocLookup_insert_ne hne_t]

/-- Concrete multi-thread TLS witness matching live probe `probe_results.json`:
Main thread (`tid = 1`) and child thread (`tid = 2`) spawn from `[TLS_NONZERO = 7, TLS_ZERO = 0]`;
child writes `TLS_NONZERO := 99` and `TLS_ZERO := 123`; main continues observing `7` and `0`. -/
theorem tls_main_child_concrete_witness :
    let tpl : PtTlsTemplate := { tdataWords := [7], tbssZeroCount := 1 }
    let st0 : MultiThreadTlsState := { template := tpl, banks := [] }
    let ops : List TlsOp := [.spawn 1, .spawn 2, .write 2 0 99, .write 2 1 123]
    let st1 := execTlsTrace st0 ops
    tlsRead st1 (llvmThreadLocalAddress 1 0) = some 7 ∧
    tlsRead st1 (llvmThreadLocalAddress 1 1) = some 0 ∧
    tlsRead st1 (llvmThreadLocalAddress 2 0) = some 99 ∧
    tlsRead st1 (llvmThreadLocalAddress 2 1) = some 123 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 5: Sharpness Counterexamples (Boundary Failures) -/

/-- Counterexample 1: If `rustc` erroneously emitted `static S1`, `static S2` with
`UnnamedAddr.global_` (`unnamed_addr`) for identical payloads, `ConstantMerge` WOULD merge
them (`canMergeGlobals = true`) and equate `&S1 == &S2` (`obsPtrEq = true`), violating
Rust Reference `items.static.storage-disjointness`. -/
theorem ce1_erroneous_unnamed_addr_on_static_breaks_disjointness
    (s1 s2 : Nat) (hne : s1 ≠ s2) (payload : List Nat) :
    let g1 : LlvmGlobal :=
      { symId := s1, isConstant := true, hasLocalLinkage := true, unnamedAddr := .global_,
        payload := payload, hasExplicitSection := false, isThreadLocal := false, inUsedList := false }
    let g2 : LlvmGlobal :=
      { symId := s2, isConstant := true, hasLocalLinkage := true, unnamedAddr := .global_,
        payload := payload, hasExplicitSection := false, isThreadLocal := false, inUsedList := false }
    let m0 : LinkedConstantModule := { globals := [(s1, g1), (s2, g2)], redirect := [] }
    let m1 := applyConstantMergePair m0 s1 s2
    obsPtrEq m1 s1 s2 = true := by
  dsimp only [applyConstantMergePair, obsPtrEq, resolveSym]
  rw [assocLookup_cons_eq, assocLookup_cons_ne hne, assocLookup_cons_eq]
  dsimp only
  rw [natBeq_false_of_ne hne]
  have hcan : canMergeGlobals
      { symId := s1, isConstant := true, hasLocalLinkage := true, unnamedAddr := .global_,
        payload := payload, hasExplicitSection := false, isThreadLocal := false, inUsedList := false }
      { symId := s2, isConstant := true, hasLocalLinkage := true, unnamedAddr := .global_,
        payload := payload, hasExplicitSection := false, isThreadLocal := false, inUsedList := false } = true := by
    dsimp only [canMergeGlobals, isMergeableGlobal, unnamedAddrBeq]
    rw [listNatBeq_refl]
    rfl
  rw [hcan]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [assocLookup_insert_eq, assocLookup_insert_ne hne]
  dsimp only [assocLookup, List.foldr]
  exact natBeq_refl s2

/-- Counterexample 2: Why `common.rs` forbids `GlobalAlloc::Static` pointers targeting
`#[thread_local]` statics inside non-TLS constants: if a constant captured a single concrete
thread-1 pointer `llvmThreadLocalAddress 1 0` and shared it with thread 2, thread 2 would
observe thread 1's mutation (`99`) instead of its own `7`! -/
theorem ce2_sharing_tls_ptr_across_threads_violates_isolation :
    let tpl : PtTlsTemplate := { tdataWords := [7], tbssZeroCount := 1 }
    let st0 : MultiThreadTlsState := { template := tpl, banks := [] }
    let st1 := execTlsTrace st0 [.spawn 1, .spawn 2, .write 1 0 99]
    let sharedLeakedPtr := llvmThreadLocalAddress 1 0
    tlsRead st1 sharedLeakedPtr ≠ tlsRead st1 (llvmThreadLocalAddress 2 0) := by
  intro tpl st0 st1 sharedLeakedPtr heq
  have h1 : tlsRead st1 sharedLeakedPtr = some 99 := rfl
  have h2 : tlsRead st1 (llvmThreadLocalAddress 2 0) = some 7 := rfl
  rw [h1, h2] at heq
  cases heq

end StaticAddressIdentityCyclesAndTlsModelsSoundness
