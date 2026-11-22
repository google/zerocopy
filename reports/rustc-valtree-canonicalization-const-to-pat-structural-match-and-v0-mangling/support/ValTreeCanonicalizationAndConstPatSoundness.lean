/-
  Formal model of `rustc` `ValTree` canonicalization (`const_to_valtree_inner`,
  `valtree_to_const_value`, `valtree_into_mplace`), active-variant `const_to_pat`
  `StructuralPartialEq` pattern lowering, `v0` const-generic symbol mangling with
  `self.consts` backref deduplication, and `VALTREE_MAX_NODES` vs. DAG `settled`
  memoization.

  Scope note: This standalone Lean 4 module formalizes the abstract semantics of
  the `rustc` algorithms audited in the accompanying reference report. It does
  not import external crates or compiler runtime libraries.

  Verification profile:
    - Total structural recursion throughout; no admitted goals.
    - Purely constructive decidable equality; kernel-verified axiom audit below.
-/

namespace ValTreeFormal

/-! ## 1. Byte-Level Memory, Provenance, IEEE-754 Float Classes, and Types -/

/-- A single byte in CTFE/Miri memory: either initialized with a byte value or uninitialized. -/
inductive MemByte where
  | init (val : Nat)
  | uninit
  deriving DecidableEq

/-- Pointer provenance: `none` denotes an integer-in-disguise (provenance-free) address;
`some allocId` denotes provenance tied to a concrete allocation. -/
abbrev Provenance := Option Nat

/-- Abstract IEEE-754 float classes sufficient for pattern-matching semantics
(`-0.0 == +0.0`, distinct finite bit patterns, and NaN payloads unequal to everything). -/
inductive FloatVal where
  | posZero
  | negZero
  | finite (bits : Nat)
  | nan (payload : Nat)
  deriving DecidableEq

/-- IEEE-754 `BinOp::Eq` semantics used by MIR `TestKind::ScalarEq` on floats. -/
noncomputable def floatIeeeEq : FloatVal → FloatVal → Bool
  | .posZero, .posZero => true
  | .posZero, .negZero => true
  | .negZero, .posZero => true
  | .negZero, .negZero => true
  | .finite a, .finite b => a == b
  | _, _ => false

/-- Predicate identifying IEEE-754 NaN values rejected by `const_to_pat` (RFC 3535). -/
noncomputable def floatIsNaN : FloatVal → Bool
  | .nan _ => true
  | _ => false

mutual
  /-- Simplified `rustc` type language capturing `ValTree`, `const_to_pat`, and `v0` distinctions. -/
  inductive Ty where
    | int
    | bool
    | float
    | thinRawPtr
    | wideRawPtr
    | fnPtr
    | fnDef (sym : Nat)
    | ref (inner : Ty)
    | array (elem : Ty) (len : Nat)
    | structTy (name : String) (structural : Bool) (padLen : Nat) (fields : TyFields)
    | enumTy (name : String) (structural : Bool) (variants : VariantDecls)
    | unionTy (name : String)

  /-- Named field list of a struct or enum variant. -/
  inductive TyFields where
    | nil
    | cons (fieldName : String) (ty : Ty) (rest : TyFields)

  /-- Variant declarations of an enum, including per-variant padding length and field schema. -/
  inductive VariantDecls where
    | nil
    | cons (variantName : String) (padLen : Nat) (fields : TyFields) (rest : VariantDecls)
end

/-- Look up the `idx`-th variant declaration of an enum. -/
noncomputable def getVariant : VariantDecls → Nat → Option (String × Nat × TyFields)
  | .nil, _ => none
  | .cons vName padLen fields _, 0 => some (vName, padLen, fields)
  | .cons _ _ _ rest, n + 1 => getVariant rest n

/-- Shallow `StructuralPartialEq` check matching `Ty::is_structural_eq_shallow`. -/
noncomputable def isStructuralShallow : Ty → Bool
  | .int | .bool | .thinRawPtr | .fnPtr | .ref _ | .array _ _ => true
  | .structTy _ structural _ _ => structural
  | .enumTy _ structural _ => structural
  | .float | .wideRawPtr | .fnDef _ | .unionTy _ => false

/-- Construct a list of `n` uninitialized padding bytes. -/
noncomputable def uninitPad : Nat → List MemByte
  | 0 => []
  | n + 1 => .uninit :: uninitPad n

/-- Check that every byte in a padding byte list is `MemByte.uninit`. -/
noncomputable def allBytesUninit : List MemByte → Bool
  | [] => true
  | .uninit :: rest => allBytesUninit rest
  | .init _ :: _ => false

theorem allBytesUninit_uninitPad : ∀ n : Nat, allBytesUninit (uninitPad n) = true
  | 0 => rfl
  | n + 1 => allBytesUninit_uninitPad n

/-! ## 2. Concrete Allocation Values (`AllocVal`) and Canonical `ValTree` -/

mutual
  /-- Typed byte-level CTFE/runtime value carrying explicit padding bytes, reference addresses,
  and raw-pointer provenance. -/
  inductive AllocVal where
    | intVal (v : Int)
    | boolVal (b : Bool)
    | floatVal (f : FloatVal)
    | thinRawPtr (addr : Nat) (prov : Provenance)
    | wideRawPtr (addr : Nat) (metaLen : Nat) (prov : Provenance)
    | fnPtr (sym : Nat)
    | fnDef (sym : Nat)
    | refVal (allocAddr : Nat) (pointee : AllocVal)
    | structVal (name : String) (pad : List MemByte) (fields : AllocFields)
    | enumVal (name : String) (variantIdx : Nat) (pad : List MemByte) (fields : AllocFields)
    | arrayVal (elems : AllocFields)
    | unionVal (name : String) (rawBytes : List MemByte)

  /-- Ordered list of concrete field/element values. -/
  inductive AllocFields where
    | nil
    | cons (head : AllocVal) (tail : AllocFields)
end

/-- Rejection errors produced during `ValTree` construction or reconstruction. -/
inductive ValTreeErr where
  | provenanceRawPtr
  | wideRawPtr
  | fnPtr
  | unionType
  | cyclicConst
  | nodesOverflow
  | layoutMismatch
  deriving DecidableEq

mutual
  /-- Canonical, padding-free, address-free `ValTree` representation mirroring `ty::ValTreeKind`. -/
  inductive ValTree where
    | leafInt (v : Int)
    | leafBool (b : Bool)
    | leafFloat (f : FloatVal)
    | leafPtrAddr (addr : Nat)
    | branch (elems : ValTreeList)

  /-- Ordered child list of a `ValTree.branch`. -/
  inductive ValTreeList where
    | nil
    | cons (head : ValTree) (tail : ValTreeList)
end

/-- `ValTree::zst`: empty branch slice. -/
noncomputable def ValTree.zst : ValTree := .branch .nil

mutual
  /-- Structural boolean equality on canonical `ValTree`s (used by `v0` `self.consts` cache). -/
  noncomputable def valTreeEq : ValTree → ValTree → Bool
    | .leafInt a, .leafInt b => if a = b then true else false
    | .leafBool a, .leafBool b => if a = b then true else false
    | .leafFloat a, .leafFloat b => if a = b then true else false
    | .leafPtrAddr a, .leafPtrAddr b => if a = b then true else false
    | .branch a, .branch b => valTreeListEq a b
    | _, _ => false
  termination_by structural a => a

  noncomputable def valTreeListEq : ValTreeList → ValTreeList → Bool
    | .nil, .nil => true
    | .cons h1 t1, .cons h2 t2 => valTreeEq h1 h2 && valTreeListEq t1 t2
    | _, _ => false
  termination_by structural a => a
end

mutual
  theorem valTreeEq_refl : ∀ v : ValTree, valTreeEq v v = true
    | .leafInt a => by simp only [valTreeEq, ↓reduceIte]
    | .leafBool a => by simp only [valTreeEq, ↓reduceIte]
    | .leafFloat a => by simp only [valTreeEq, ↓reduceIte]
    | .leafPtrAddr a => by simp only [valTreeEq, ↓reduceIte]
    | .branch ts => valTreeListEq_refl ts

  theorem valTreeListEq_refl : ∀ ts : ValTreeList, valTreeListEq ts ts = true
    | .nil => rfl
    | .cons h t => by
        simp only [valTreeListEq, valTreeEq_refl h, valTreeListEq_refl t, Bool.and_self]
end

mutual
  /-- Quotient map `const_to_valtree_inner`: strips padding bytes and reference addresses,
  accepts provenance-free thin raw pointers and `FnDef` ZSTs, and rejects provenance raw
  pointers, wide raw pointers, function pointers, and unions. -/
  noncomputable def toValTree : AllocVal → Except ValTreeErr ValTree
    | .intVal v => .ok (.leafInt v)
    | .boolVal b => .ok (.leafBool b)
    | .floatVal f => .ok (.leafFloat f)
    | .thinRawPtr addr none => .ok (.leafPtrAddr addr)
    | .thinRawPtr _ (some _) => .error .provenanceRawPtr
    | .wideRawPtr _ _ _ => .error .wideRawPtr
    | .fnPtr _ => .error .fnPtr
    | .fnDef _ => .ok ValTree.zst
    | .refVal _ pointee => toValTree pointee
    | .structVal _ _ fields =>
        match toValTreeFields fields with
        | .ok ts => .ok (.branch ts)
        | .error e => .error e
    | .enumVal _ vIdx _ fields =>
        match toValTreeFields fields with
        | .ok ts => .ok (.branch (.cons (.leafInt (Int.ofNat vIdx)) ts))
        | .error e => .error e
    | .arrayVal elems =>
        match toValTreeFields elems with
        | .ok ts => .ok (.branch ts)
        | .error e => .error e
    | .unionVal _ _ => .error .unionType
  termination_by structural a => a

  /-- Field-wise helper for `toValTree`. -/
  noncomputable def toValTreeFields : AllocFields → Except ValTreeErr ValTreeList
    | .nil => .ok .nil
    | .cons h t =>
        match toValTree h with
        | .error e => .error e
        | .ok vh =>
            match toValTreeFields t with
            | .error e => .error e
            | .ok vt => .ok (.cons vh vt)
  termination_by structural fs => fs
end

mutual
  /-- Equivalence relation identifying concrete `AllocVal`s that agree on all logical fields,
  discriminants, and values while possibly differing in padding bytes and reference addresses. -/
  inductive SameFieldsModPadAndRef : AllocVal → AllocVal → Prop where
    | intVal (v : Int) : SameFieldsModPadAndRef (.intVal v) (.intVal v)
    | boolVal (b : Bool) : SameFieldsModPadAndRef (.boolVal b) (.boolVal b)
    | floatVal (f : FloatVal) : SameFieldsModPadAndRef (.floatVal f) (.floatVal f)
    | thinRawPtr (addr : Nat) (prov : Provenance) :
        SameFieldsModPadAndRef (.thinRawPtr addr prov) (.thinRawPtr addr prov)
    | wideRawPtr (addr metaLen : Nat) (prov : Provenance) :
        SameFieldsModPadAndRef (.wideRawPtr addr metaLen prov) (.wideRawPtr addr metaLen prov)
    | fnPtr (sym : Nat) : SameFieldsModPadAndRef (.fnPtr sym) (.fnPtr sym)
    | fnDef (sym : Nat) : SameFieldsModPadAndRef (.fnDef sym) (.fnDef sym)
    | refVal (a1 a2 : Nat) {p1 p2 : AllocVal} :
        SameFieldsModPadAndRef p1 p2 →
        SameFieldsModPadAndRef (.refVal a1 p1) (.refVal a2 p2)
    | structVal (name : String) (pad1 pad2 : List MemByte) {f1 f2 : AllocFields} :
        SameFieldsListModPadAndRef f1 f2 →
        SameFieldsModPadAndRef (.structVal name pad1 f1) (.structVal name pad2 f2)
    | enumVal (name : String) (vIdx : Nat) (pad1 pad2 : List MemByte) {f1 f2 : AllocFields} :
        SameFieldsListModPadAndRef f1 f2 →
        SameFieldsModPadAndRef (.enumVal name vIdx pad1 f1) (.enumVal name vIdx pad2 f2)
    | arrayVal {e1 e2 : AllocFields} :
        SameFieldsListModPadAndRef e1 e2 →
        SameFieldsModPadAndRef (.arrayVal e1) (.arrayVal e2)
    | unionVal (name : String) (b1 b2 : List MemByte) :
        SameFieldsModPadAndRef (.unionVal name b1) (.unionVal name b2)

  /-- List lift of `SameFieldsModPadAndRef`. -/
  inductive SameFieldsListModPadAndRef : AllocFields → AllocFields → Prop where
    | nil : SameFieldsListModPadAndRef .nil .nil
    | cons {h1 h2 : AllocVal} {t1 t2 : AllocFields} :
        SameFieldsModPadAndRef h1 h2 →
        SameFieldsListModPadAndRef t1 t2 →
        SameFieldsListModPadAndRef (.cons h1 t1) (.cons h2 t2)
end

mutual
  /-- Theorem 1 (Padding & Reference-Identity Quotient Invariance):
  Two `AllocVal`s differing only in padding bytes or reference addresses yield the exact same
  `toValTree` result. -/
  theorem toValTree_ignores_padding_and_ref_addr :
      ∀ {a1 a2 : AllocVal}, SameFieldsModPadAndRef a1 a2 → toValTree a1 = toValTree a2
    | _, _, .intVal _ => rfl
    | _, _, .boolVal _ => rfl
    | _, _, .floatVal _ => rfl
    | _, _, .thinRawPtr _ _ => rfl
    | _, _, .wideRawPtr _ _ _ => rfl
    | _, _, .fnPtr _ => rfl
    | _, _, .fnDef _ => rfl
    | _, _, .refVal _ _ hp => by
        simp only [toValTree]
        exact toValTree_ignores_padding_and_ref_addr hp
    | _, _, .structVal _ _ _ hf => by
        simp only [toValTree, toValTreeFields_ignores_padding_and_ref_addr hf]
    | _, _, .enumVal _ _ _ _ hf => by
        simp only [toValTree, toValTreeFields_ignores_padding_and_ref_addr hf]
    | _, _, .arrayVal hf => by
        simp only [toValTree, toValTreeFields_ignores_padding_and_ref_addr hf]
    | _, _, .unionVal _ _ _ => rfl

  /-- Mutual field-list lemma for Theorem 1. -/
  theorem toValTreeFields_ignores_padding_and_ref_addr :
      ∀ {f1 f2 : AllocFields}, SameFieldsListModPadAndRef f1 f2 →
        toValTreeFields f1 = toValTreeFields f2
    | _, _, .nil => rfl
    | _, _, .cons hh ht => by
        simp only [toValTreeFields,
          toValTree_ignores_padding_and_ref_addr hh,
          toValTreeFields_ignores_padding_and_ref_addr ht]
end

/-! ## 3. Typing, Reconstruction (`fromValTree`), and Padding Uninitialization -/

mutual
  /-- Typing judgement relating a concrete `AllocVal` to its `Ty`. -/
  inductive HasTy : AllocVal → Ty → Prop where
    | intVal (v : Int) : HasTy (.intVal v) .int
    | boolVal (b : Bool) : HasTy (.boolVal b) .bool
    | floatVal (f : FloatVal) : HasTy (.floatVal f) .float
    | thinRawPtr (addr : Nat) (prov : Provenance) : HasTy (.thinRawPtr addr prov) .thinRawPtr
    | wideRawPtr (addr metaLen : Nat) (prov : Provenance) :
        HasTy (.wideRawPtr addr metaLen prov) .wideRawPtr
    | fnPtr (sym : Nat) : HasTy (.fnPtr sym) .fnPtr
    | fnDef (sym : Nat) : HasTy (.fnDef sym) (.fnDef sym)
    | refVal (addr : Nat) {p : AllocVal} {inner : Ty} :
        HasTy p inner → HasTy (.refVal addr p) (.ref inner)
    | structVal (name : String) (structural : Bool) (padLen : Nat)
        (pad : List MemByte) {fields : AllocFields} {ftys : TyFields} :
        HasTyFields fields ftys →
        HasTy (.structVal name pad fields) (.structTy name structural padLen ftys)
    | enumVal (name : String) (structural : Bool) (vIdx : Nat) (vName : String)
        (padLen : Nat) (pad : List MemByte)
        {fields : AllocFields} {ftys : TyFields} {variants : VariantDecls} :
        getVariant variants vIdx = some (vName, padLen, ftys) →
        HasTyFields fields ftys →
        HasTy (.enumVal name vIdx pad fields) (.enumTy name structural variants)
    | arrayVal {elems : AllocFields} {elemTy : Ty} {len : Nat} :
        HasTyArray elems elemTy len →
        HasTy (.arrayVal elems) (.array elemTy len)
    | unionVal (name : String) (raw : List MemByte) :
        HasTy (.unionVal name raw) (.unionTy name)

  /-- Field-wise typing judgement for struct and enum variant fields. -/
  inductive HasTyFields : AllocFields → TyFields → Prop where
    | nil : HasTyFields .nil .nil
    | cons (fName : String) {h : AllocVal} {ty : Ty} {t : AllocFields} {rest : TyFields} :
        HasTy h ty → HasTyFields t rest →
        HasTyFields (.cons h t) (.cons fName ty rest)

  /-- Element-wise typing judgement for fixed-length arrays. -/
  inductive HasTyArray : AllocFields → Ty → Nat → Prop where
    | nil (elemTy : Ty) : HasTyArray .nil elemTy 0
    | cons {h : AllocVal} {t : AllocFields} {elemTy : Ty} {n : Nat} :
        HasTy h elemTy → HasTyArray t elemTy n →
        HasTyArray (.cons h t) elemTy (n + 1)
end

mutual
  /-- Predicate asserting that every padding byte in every nested struct/enum is `MemByte.uninit`. -/
  noncomputable def allPaddingUninit : AllocVal → Bool
    | .intVal _ | .boolVal _ | .floatVal _ | .thinRawPtr _ _
    | .wideRawPtr _ _ _ | .fnPtr _ | .fnDef _ | .unionVal _ _ => true
    | .refVal _ p => allPaddingUninit p
    | .structVal _ pad fields => allBytesUninit pad && allPaddingUninitFields fields
    | .enumVal _ _ pad fields => allBytesUninit pad && allPaddingUninitFields fields
    | .arrayVal elems => allPaddingUninitFields elems
  termination_by structural a => a

  /-- Field-list helper for `allPaddingUninit`. -/
  noncomputable def allPaddingUninitFields : AllocFields → Bool
    | .nil => true
    | .cons h t => allPaddingUninit h && allPaddingUninitFields t
  termination_by structural fs => fs
end

/-- Generic fixed-length array mapper over `ValTreeList` (keeps `fromValTree` structurally recursive on `Ty`). -/
noncomputable def mapValTreeArray {α : Type} (f : ValTree → Except ValTreeErr α)
    (combine : α → List α → List α) : Nat → ValTreeList → Except ValTreeErr (List α)
  | 0, .nil => .ok []
  | n + 1, .cons vh vt =>
      match f vh with
      | .error e => .error e
      | .ok ah =>
          match mapValTreeArray f combine n vt with
          | .error e => .error e
          | .ok atail => .ok (combine ah atail)
  | _, _ => .error .layoutMismatch

/-- Helper lifting a `ValTree` decoder over a fixed-length array into `AllocFields`. -/
noncomputable def decodeArrayFields (f : ValTree → Except ValTreeErr AllocVal) :
    Nat → ValTreeList → Except ValTreeErr AllocFields
  | 0, .nil => .ok .nil
  | n + 1, .cons vh vt =>
      match f vh with
      | .error e => .error e
      | .ok ah =>
          match decodeArrayFields f n vt with
          | .error e => .error e
          | .ok atail => .ok (.cons ah atail)
  | _, _ => .error .layoutMismatch

mutual
  /-- Reconstruction `valtree_to_const_value` / `valtree_into_mplace`: allocates fresh
  uninitialized padding (`uninitPad padLen`) and writes only canonical fields. -/
  noncomputable def fromValTree : Ty → ValTree → Except ValTreeErr AllocVal
    | .int, .leafInt v => .ok (.intVal v)
    | .bool, .leafBool b => .ok (.boolVal b)
    | .float, .leafFloat f => .ok (.floatVal f)
    | .thinRawPtr, .leafPtrAddr addr => .ok (.thinRawPtr addr none)
    | .fnDef sym, .branch .nil => .ok (.fnDef sym)
    | .ref inner, vt =>
        match fromValTree inner vt with
        | .ok p => .ok (.refVal 0 p)
        | .error e => .error e
    | .structTy name _ padLen ftys, .branch ts =>
        match fromValTreeFields ftys ts with
        | .ok fs => .ok (.structVal name (uninitPad padLen) fs)
        | .error e => .error e
    | .enumTy name _ variants, .branch (.cons (.leafInt (.ofNat vIdx)) ts) =>
        fromValTreeVariants name variants vIdx ts
    | .array elemTy len, .branch ts =>
        match decodeArrayFields (fromValTree elemTy) len ts with
        | .ok es => .ok (.arrayVal es)
        | .error e => .error e
    | .wideRawPtr, _ => .error .wideRawPtr
    | .fnPtr, _ => .error .fnPtr
    | .unionTy _, _ => .error .unionType
    | _, _ => .error .layoutMismatch
  termination_by structural ty => ty

  /-- Variant lookup + reconstruction (structurally recursive on `VariantDecls`). -/
  noncomputable def fromValTreeVariants (name : String) :
      VariantDecls → Nat → ValTreeList → Except ValTreeErr AllocVal
    | .nil, _, _ => .error .layoutMismatch
    | .cons _ padLen ftys _, 0, ts =>
        match fromValTreeFields ftys ts with
        | .ok fs => .ok (.enumVal name 0 (uninitPad padLen) fs)
        | .error e => .error e
    | .cons _ _ _ rest, n + 1, ts =>
        match fromValTreeVariants name rest n ts with
        | .ok (.enumVal nm idx pad fs) => .ok (.enumVal nm (idx + 1) pad fs)
        | .ok other => .ok other
        | .error e => .error e
  termination_by structural vs => vs

  /-- Field-wise reconstruction helper. -/
  noncomputable def fromValTreeFields : TyFields → ValTreeList → Except ValTreeErr AllocFields
    | .nil, .nil => .ok .nil
    | .cons _ ty rest, .cons vh vt =>
        match fromValTree ty vh with
        | .error e => .error e
        | .ok ah =>
            match fromValTreeFields rest vt with
            | .error e => .error e
            | .ok atail => .ok (.cons ah atail)
    | _, _ => .error .layoutMismatch
  termination_by structural ftys => ftys
end

theorem fromValTreeVariants_eq_getVariant (name : String) :
    ∀ (vs : VariantDecls) (vIdx : Nat) (vName : String) (padLen : Nat) (ftys : TyFields)
      (ts : ValTreeList) (fs : AllocFields),
      getVariant vs vIdx = some (vName, padLen, ftys) →
      fromValTreeFields ftys ts = .ok fs →
      fromValTreeVariants name vs vIdx ts = .ok (.enumVal name vIdx (uninitPad padLen) fs)
  | .nil, _, _, _, _, _, _, hget, _ => by cases hget
  | .cons _ _ _ _, 0, _, _, _, _, _, hget, hfs => by
      cases hget
      simp only [fromValTreeVariants, hfs]
  | .cons _ _ _ rest, n + 1, vName, padLen, ftys, ts, fs, hget, hfs => by
      have ih := fromValTreeVariants_eq_getVariant name rest n vName padLen ftys ts fs hget hfs
      simp only [fromValTreeVariants, ih]

mutual
  /-- Theorem 2 (Round-Trip Field Preservation & Padding Uninitialization):
  If a well-typed `AllocVal` canonicalizes to `vt`, then `fromValTree ty vt` succeeds,
  preserves all logical fields/discriminants (`SameFieldsModPadAndRef`), leaves every padding
  byte strictly `MemByte.uninit`, and re-canonicalizes to the exact same `ValTree`. -/
  theorem fromValTree_preserves_fields_and_uninit_padding :
      ∀ {a : AllocVal} {ty : Ty} {vt : ValTree},
        HasTy a ty → toValTree a = .ok vt →
        ∃ a', fromValTree ty vt = .ok a' ∧
              SameFieldsModPadAndRef a a' ∧
              allPaddingUninit a' = true ∧
              toValTree a' = .ok vt
    | _, _, _, .intVal v, h => by
        cases h
        exact ⟨.intVal v, rfl, .intVal v, rfl, rfl⟩
    | _, _, _, .boolVal b, h => by
        cases h
        exact ⟨.boolVal b, rfl, .boolVal b, rfl, rfl⟩
    | _, _, _, .floatVal f, h => by
        cases h
        exact ⟨.floatVal f, rfl, .floatVal f, rfl, rfl⟩
    | _, _, _, .thinRawPtr addr prov, h => by
        cases prov with
        | none =>
            cases h
            exact ⟨.thinRawPtr addr none, rfl, .thinRawPtr addr none, rfl, rfl⟩
        | some _ => cases h
    | _, _, _, .wideRawPtr _ _ _, h => by cases h
    | _, _, _, .fnPtr _, h => by cases h
    | _, _, _, .fnDef sym, h => by
        cases h
        exact ⟨.fnDef sym, rfl, .fnDef sym, rfl, rfl⟩
    | _, _, _, .refVal addr hp, h => by
        have ⟨p', hfrom, hsame, huninit, hrt⟩ :=
          fromValTree_preserves_fields_and_uninit_padding hp h
        refine ⟨.refVal 0 p', ?_, .refVal addr 0 hsame, huninit, hrt⟩
        simp only [fromValTree, hfrom]
    | _, _, _, .structVal name structural padLen pad hfields, h => by
        simp only [toValTree] at h
        cases hf : toValTreeFields _ with
        | error e => rw [hf] at h; cases h
        | ok ts =>
            rw [hf] at h; cases h
            have ⟨fs', hfrom, hsame, huninit, hrt⟩ :=
              fromValTreeFields_preserves hfields hf
            refine ⟨.structVal name (uninitPad padLen) fs', ?_, .structVal name pad _ hsame, ?_, ?_⟩
            · simp only [fromValTree, hfrom]
            · simp only [allPaddingUninit, allBytesUninit_uninitPad, huninit, Bool.and_self]
            · simp only [toValTree, hrt]
    | _, _, _, .enumVal name structural vIdx vName padLen pad hget hfields, h => by
        simp only [toValTree] at h
        cases hf : toValTreeFields _ with
        | error e => rw [hf] at h; cases h
        | ok ts =>
            rw [hf] at h; cases h
            have ⟨fs', hfrom, hsame, huninit, hrt⟩ :=
              fromValTreeFields_preserves hfields hf
            have hvar := fromValTreeVariants_eq_getVariant name _ vIdx vName padLen _ ts fs' hget hfrom
            refine ⟨.enumVal name vIdx (uninitPad padLen) fs', ?_,
                    .enumVal name vIdx pad _ hsame, ?_, ?_⟩
            · simp only [fromValTree, hvar]
            · simp only [allPaddingUninit, allBytesUninit_uninitPad, huninit, Bool.and_self]
            · simp only [toValTree, hrt]
    | _, _, _, .arrayVal harray, h => by
        simp only [toValTree] at h
        cases hf : toValTreeFields _ with
        | error e => rw [hf] at h; cases h
        | ok ts =>
            rw [hf] at h; cases h
            have ⟨es', hfrom, hsame, huninit, hrt⟩ :=
              fromValTreeArray_preserves harray hf
            refine ⟨.arrayVal es', ?_, .arrayVal hsame, huninit, ?_⟩
            · simp only [fromValTree, hfrom]
            · simp only [toValTree, hrt]
    | _, _, _, .unionVal _ _, h => by cases h

  /-- Field-list round-trip lemma for Theorem 2. -/
  theorem fromValTreeFields_preserves :
      ∀ {fs : AllocFields} {ftys : TyFields} {ts : ValTreeList},
        HasTyFields fs ftys → toValTreeFields fs = .ok ts →
        ∃ fs', fromValTreeFields ftys ts = .ok fs' ∧
               SameFieldsListModPadAndRef fs fs' ∧
               allPaddingUninitFields fs' = true ∧
               toValTreeFields fs' = .ok ts
    | _, _, _, .nil, h => by
        cases h
        exact ⟨.nil, rfl, .nil, rfl, rfl⟩
    | _, _, _, .cons fName hh ht, h => by
        simp only [toValTreeFields] at h
        cases h1 : toValTree _ with
        | error e => rw [h1] at h; cases h
        | ok vh =>
            rw [h1] at h
            cases h2 : toValTreeFields _ with
            | error e => rw [h2] at h; cases h
            | ok vt =>
                rw [h2] at h; cases h
                have ⟨ah', hfromH, hsameH, huninitH, hrtH⟩ :=
                  fromValTree_preserves_fields_and_uninit_padding hh h1
                have ⟨at', hfromT, hsameT, huninitT, hrtT⟩ :=
                  fromValTreeFields_preserves ht h2
                refine ⟨.cons ah' at', ?_, .cons hsameH hsameT, ?_, ?_⟩
                · simp only [fromValTreeFields, hfromH, hfromT]
                · simp only [allPaddingUninitFields, huninitH, huninitT, Bool.and_self]
                · simp only [toValTreeFields, hrtH, hrtT]

  /-- Array element round-trip lemma for Theorem 2. -/
  theorem fromValTreeArray_preserves :
      ∀ {es : AllocFields} {elemTy : Ty} {n : Nat} {ts : ValTreeList},
        HasTyArray es elemTy n → toValTreeFields es = .ok ts →
        ∃ es', decodeArrayFields (fromValTree elemTy) n ts = .ok es' ∧
               SameFieldsListModPadAndRef es es' ∧
               allPaddingUninitFields es' = true ∧
               toValTreeFields es' = .ok ts
    | _, _, _, _, .nil _, h => by
        cases h
        exact ⟨.nil, rfl, .nil, rfl, rfl⟩
    | _, _, _, _, .cons hh ht, h => by
        simp only [toValTreeFields] at h
        cases h1 : toValTree _ with
        | error e => rw [h1] at h; cases h
        | ok vh =>
            rw [h1] at h
            cases h2 : toValTreeFields _ with
            | error e => rw [h2] at h; cases h
            | ok vt =>
                rw [h2] at h; cases h
                have ⟨ah', hfromH, hsameH, huninitH, hrtH⟩ :=
                  fromValTree_preserves_fields_and_uninit_padding hh h1
                have ⟨at', hfromT, hsameT, huninitT, hrtT⟩ :=
                  fromValTreeArray_preserves ht h2
                refine ⟨.cons ah' at', ?_, .cons hsameH hsameT, ?_, ?_⟩
                · simp only [decodeArrayFields, hfromH, hfromT]
                · simp only [allPaddingUninitFields, huninitH, huninitT, Bool.and_self]
                · simp only [toValTreeFields, hrtH, hrtT]
end

/-! ## 4. Active-Variant `StructuralPartialEq` Pattern Lowering (`valTreeToPat`) -/

/-- Pattern lowering errors matching `rustc_mir_build/src/thir/pattern/const_to_pat.rs`. -/
inductive PatErr where
  | nonStructural (name : String)
  | nanPattern
  | unsupportedType (kind : String)
  | badValTree
  deriving DecidableEq

mutual
  /-- Lowered THIR-level pattern produced from a canonical `ValTree`. -/
  inductive Pat where
    | constInt (v : Int)
    | constBool (b : Bool)
    | constFloat (f : FloatVal)
    | constPtrAddr (addr : Nat)
    | deref (sub : Pat)
    | structPat (name : String) (fields : PatFields)
    | variantPat (name : String) (variantIdx : Nat) (fields : PatFields)
    | arrayPat (elems : PatFields)

  /-- Ordered subpatterns for struct fields, enum active-variant fields, or array elements. -/
  inductive PatFields where
    | nil
    | cons (head : Pat) (tail : PatFields)
end

/-- Array-element helper lifting a `Pat` lowerer over a fixed-length `ValTreeList`. -/
noncomputable def lowerArrayPat (f : ValTree → Except PatErr Pat) :
    Nat → ValTreeList → Except PatErr PatFields
  | 0, .nil => .ok .nil
  | n + 1, .cons vh vt =>
      match f vh with
      | .error e => .error e
      | .ok ph =>
          match lowerArrayPat f n vt with
          | .error e => .error e
          | .ok pt => .ok (.cons ph pt)
  | _, _ => .error .badValTree

mutual
  /-- `ConstToPat::valtree_to_pat`:
  - Checks `isStructuralShallow` (`structural == true`) on ADTs;
  - For enums, projects ONLY the active variant index and recurses ONLY into its fields
    (never checking inactive variants' field types);
  - Rejects `NaN` floats (RFC 3535) and accepts finite floats (including `-0.0` / `+0.0`);
  - Rejects `FnDef` even though `toValTree` succeeded with `ValTree.zst`. -/
  noncomputable def valTreeToPat : Ty → ValTree → Except PatErr Pat
    | .int, .leafInt v => .ok (.constInt v)
    | .bool, .leafBool b => .ok (.constBool b)
    | .float, .leafFloat f =>
        if floatIsNaN f then .error .nanPattern else .ok (.constFloat f)
    | .thinRawPtr, .leafPtrAddr addr => .ok (.constPtrAddr addr)
    | .ref inner, vt =>
        match valTreeToPat inner vt with
        | .ok sub => .ok (.deref sub)
        | .error e => .error e
    | .structTy name structural _ ftys, .branch ts =>
        if !structural then
          .error (.nonStructural name)
        else
          match valTreeFieldsToPat ftys ts with
          | .ok ps => .ok (.structPat name ps)
          | .error e => .error e
    | .enumTy name structural variants, .branch (.cons (.leafInt (.ofNat vIdx)) ts) =>
        if !structural then
          .error (.nonStructural name)
        else
          valTreeVariantsToPat name variants vIdx ts
    | .array elemTy len, .branch ts =>
        match lowerArrayPat (valTreeToPat elemTy) len ts with
        | .ok ps => .ok (.arrayPat ps)
        | .error e => .error e
    | .fnDef _, _ => .error (.unsupportedType "fnDef")
    | .wideRawPtr, _ => .error (.unsupportedType "wideRawPtr")
    | .fnPtr, _ => .error (.unsupportedType "fnPtr")
    | .unionTy _, _ => .error (.unsupportedType "union")
    | _, _ => .error .badValTree
  termination_by structural ty => ty

  /-- Active-variant lookup + lowering (never inspects inactive variants). -/
  noncomputable def valTreeVariantsToPat (name : String) :
      VariantDecls → Nat → ValTreeList → Except PatErr Pat
    | .nil, _, _ => .error .badValTree
    | .cons _ _ ftys _, 0, ts =>
        match valTreeFieldsToPat ftys ts with
        | .ok ps => .ok (.variantPat name 0 ps)
        | .error e => .error e
    | .cons _ _ _ rest, n + 1, ts =>
        match valTreeVariantsToPat name rest n ts with
        | .ok (.variantPat nm idx ps) => .ok (.variantPat nm (idx + 1) ps)
        | .ok other => .ok other
        | .error e => .error e
  termination_by structural vs => vs

  /-- Field-list helper for `valTreeToPat`. -/
  noncomputable def valTreeFieldsToPat : TyFields → ValTreeList → Except PatErr PatFields
    | .nil, .nil => .ok .nil
    | .cons _ ty rest, .cons vh vt =>
        match valTreeToPat ty vh with
        | .error e => .error e
        | .ok ph =>
            match valTreeFieldsToPat rest vt with
            | .error e => .error e
            | .ok pt => .ok (.cons ph pt)
    | _, _ => .error .badValTree
  termination_by structural ftys => ftys
end

theorem valTreeVariantsToPat_inv (name : String) :
    ∀ (vs : VariantDecls) (vIdx : Nat) (vName : String) (padLen : Nat) (ftys : TyFields)
      (ts : ValTreeList) (p : Pat),
      getVariant vs vIdx = some (vName, padLen, ftys) →
      valTreeVariantsToPat name vs vIdx ts = .ok p →
      ∃ ps, valTreeFieldsToPat ftys ts = .ok ps ∧ p = .variantPat name vIdx ps
  | .nil, _, _, _, _, _, _, hget, _ => by cases hget
  | .cons _ _ _ _, 0, _, _, _, _, _, hget, hp => by
      cases hget
      simp only [valTreeVariantsToPat] at hp
      cases hps : valTreeFieldsToPat _ _ with
      | error e => rw [hps] at hp; cases hp
      | ok ps => rw [hps] at hp; cases hp; exact ⟨ps, rfl, rfl⟩
  | .cons _ _ _ rest, n + 1, vName, padLen, ftys, ts, p, hget, hp => by
      simp only [valTreeVariantsToPat] at hp
      cases hrec : valTreeVariantsToPat name rest n ts with
      | error e => rw [hrec] at hp; cases hp
      | ok p' =>
          have ⟨ps, hps, hp'⟩ := valTreeVariantsToPat_inv name rest n vName padLen ftys ts p' hget hrec
          subst hp'
          rw [hrec] at hp
          cases hp
          exact ⟨ps, hps, rfl⟩

mutual
  /-- Operational match semantics of a lowered THIR/MIR pattern against a runtime `AllocVal`.
  Note: padding bytes and reference addresses are never consulted; floats use `floatIeeeEq`. -/
  noncomputable def patMatches : Pat → AllocVal → Bool
    | .constInt v1, .intVal v2 => v1 == v2
    | .constBool b1, .boolVal b2 => b1 == b2
    | .constFloat f1, .floatVal f2 => floatIeeeEq f1 f2
    | .constPtrAddr a1, .thinRawPtr a2 _ => a1 == a2
    | .deref sub, .refVal _ p => patMatches sub p
    | .structPat n1 ps, .structVal n2 _ fs => (n1 == n2) && patMatchesFields ps fs
    | .variantPat n1 i1 ps, .enumVal n2 i2 _ fs =>
        (n1 == n2) && (i1 == i2) && patMatchesFields ps fs
    | .arrayPat ps, .arrayVal es => patMatchesFields ps es
    | _, _ => false
  termination_by structural p => p

  /-- Field-list helper for `patMatches`. -/
  noncomputable def patMatchesFields : PatFields → AllocFields → Bool
    | .nil, .nil => true
    | .cons ph pt, .cons fh ft => patMatches ph fh && patMatchesFields pt ft
    | _, _ => false
  termination_by structural ps => ps
end

mutual
  /-- Direct structural equality between two runtime/CTFE `AllocVal`s (ignoring padding bytes
  and reference addresses, comparing floats with IEEE `Eq`, and comparing only active enum
  variant payloads when discriminants agree). -/
  noncomputable def structuralEq : AllocVal → AllocVal → Bool
    | .intVal v1, .intVal v2 => v1 == v2
    | .boolVal b1, .boolVal b2 => b1 == b2
    | .floatVal f1, .floatVal f2 => floatIeeeEq f1 f2
    | .thinRawPtr a1 _, .thinRawPtr a2 _ => a1 == a2
    | .refVal _ p1, .refVal _ p2 => structuralEq p1 p2
    | .structVal n1 _ f1, .structVal n2 _ f2 => (n1 == n2) && structuralEqFields f1 f2
    | .enumVal n1 i1 _ f1, .enumVal n2 i2 _ f2 =>
        (n1 == n2) && (i1 == i2) && structuralEqFields f1 f2
    | .arrayVal e1, .arrayVal e2 => structuralEqFields e1 e2
    | _, _ => false
  termination_by structural a => a

  /-- Field-list helper for `structuralEq`. -/
  noncomputable def structuralEqFields : AllocFields → AllocFields → Bool
    | .nil, .nil => true
    | .cons h1 t1, .cons h2 t2 => structuralEq h1 h2 && structuralEqFields t1 t2
    | _, _ => false
  termination_by structural fs => fs
end

mutual
  /-- Theorem 3 (Active-Variant Structural Pattern Soundness):
  For any well-typed constant `c` of type `ty` whose `ValTree` lowers via `valTreeToPat` to `p`,
  and any well-typed scrutinee `x` of the same type `ty`, matching `x` against `p` returns `true`
  if and only if `c` and `x` are structurally equal on their active variant and non-padding fields
  (including IEEE `-0.0 == +0.0` float equality and padding/ref-address erasure). -/
  theorem activeVariant_pat_matches_iff_structural_eq :
      ∀ {c x : AllocVal} {ty : Ty} {vt : ValTree} {p : Pat},
        HasTy c ty → HasTy x ty →
        toValTree c = .ok vt →
        valTreeToPat ty vt = .ok p →
        patMatches p x = structuralEq c x
    | _, _, _, _, _, .intVal v1, .intVal v2, hvt, hpat => by
        cases hvt; cases hpat; rfl
    | _, _, _, _, _, .boolVal b1, .boolVal b2, hvt, hpat => by
        cases hvt; cases hpat; rfl
    | _, _, _, _, _, .floatVal f1, .floatVal f2, hvt, hpat => by
        cases hvt
        simp only [valTreeToPat] at hpat
        cases hnan : floatIsNaN f1 with
        | true => rw [hnan] at hpat; cases hpat
        | false => rw [hnan] at hpat; cases hpat; rfl
    | _, _, _, _, _, .thinRawPtr a1 prov1, .thinRawPtr a2 prov2, hvt, hpat => by
        cases prov1 with
        | some _ => cases hvt
        | none => cases hvt; cases hpat; rfl
    | _, _, _, _, _, .wideRawPtr _ _ _, _, hvt, _ => by cases hvt
    | _, _, _, _, _, .fnPtr _, _, hvt, _ => by cases hvt
    | _, _, _, _, _, .fnDef _, _, hvt, hpat => by
        cases hvt; cases hpat
    | _, _, _, vt, _, .refVal _ hc, .refVal _ hx, hvt, hpat => by
        simp only [toValTree] at hvt
        simp only [valTreeToPat] at hpat
        cases hsub : valTreeToPat _ vt with
        | error e => rw [hsub] at hpat; cases hpat
        | ok sub =>
            rw [hsub] at hpat; cases hpat
            simp only [patMatches, structuralEq]
            exact activeVariant_pat_matches_iff_structural_eq hc hx hvt hsub
    | _, _, _, _, _, .structVal name structural padLen pad1 hcf,
                     .structVal _ _ _ pad2 hxf, hvt, hpat => by
        simp only [toValTree] at hvt
        cases hts : toValTreeFields _ with
        | error e => rw [hts] at hvt; cases hvt
        | ok ts =>
            rw [hts] at hvt; cases hvt
            simp only [valTreeToPat] at hpat
            cases structural with
            | false => cases hpat
            | true =>
                simp only [Bool.not_true] at hpat
                cases hps : valTreeFieldsToPat _ ts with
                | error e => rw [hps] at hpat; cases hpat
                | ok ps =>
                    rw [hps] at hpat; cases hpat
                    simp only [patMatches, structuralEq]
                    rw [activeVariant_pat_matches_fields hcf hxf hts hps]
    | _, _, _, _, p, .enumVal name structural vIdx1 vName1 padLen1 pad1 hget1 hcf,
                     .enumVal _ _ vIdx2 vName2 padLen2 pad2 hget2 hxf, hvt, hpat => by
        simp only [toValTree] at hvt
        cases hts : toValTreeFields _ with
        | error e => rw [hts] at hvt; cases hvt
        | ok ts =>
            rw [hts] at hvt; cases hvt
            simp only [valTreeToPat] at hpat
            cases structural with
            | false => cases hpat
            | true =>
                simp only [Bool.not_true] at hpat
                have ⟨ps, hps, hpEq⟩ :=
                  valTreeVariantsToPat_inv name _ vIdx1 vName1 padLen1 _ ts p hget1 hpat
                subst hpEq
                simp only [patMatches, structuralEq]
                cases heq : (vIdx1 == vIdx2) with
                | false =>
                    simp only [Bool.and_false, Bool.false_and]
                | true =>
                    have hidx : vIdx1 = vIdx2 := eq_of_beq heq
                    subst hidx
                    rw [hget1] at hget2
                    injection hget2 with htuple
                    injection htuple with _ hrest
                    injection hrest with _ hftys
                    subst hftys
                    rw [activeVariant_pat_matches_fields hcf hxf hts hps]
    | _, _, _, _, _, .arrayVal hca, .arrayVal hxa, hvt, hpat => by
        simp only [toValTree] at hvt
        cases hts : toValTreeFields _ with
        | error e => rw [hts] at hvt; cases hvt
        | ok ts =>
            rw [hts] at hvt; cases hvt
            simp only [valTreeToPat] at hpat
            cases hps : lowerArrayPat (valTreeToPat _) _ ts with
            | error e => rw [hps] at hpat; cases hpat
            | ok ps =>
                rw [hps] at hpat; cases hpat
                exact activeVariant_pat_matches_array hca hxa hts hps
    | _, _, _, _, _, .unionVal _ _, _, hvt, _ => by cases hvt

  /-- Mutual field-list lemma for Theorem 3. -/
  theorem activeVariant_pat_matches_fields :
      ∀ {cf xf : AllocFields} {ftys : TyFields} {ts : ValTreeList} {ps : PatFields},
        HasTyFields cf ftys → HasTyFields xf ftys →
        toValTreeFields cf = .ok ts →
        valTreeFieldsToPat ftys ts = .ok ps →
        patMatchesFields ps xf = structuralEqFields cf xf
    | _, _, _, _, _, .nil, .nil, hts, hps => by
        cases hts; cases hps; rfl
    | _, _, _, _, _, .cons _ hch hct, .cons _ hxh hxt, hts, hps => by
        simp only [toValTreeFields] at hts
        cases h1 : toValTree _ with
        | error e => rw [h1] at hts; cases hts
        | ok vh =>
            rw [h1] at hts
            cases h2 : toValTreeFields _ with
            | error e => rw [h2] at hts; cases hts
            | ok vt =>
                rw [h2] at hts; cases hts
                simp only [valTreeFieldsToPat] at hps
                cases hp1 : valTreeToPat _ vh with
                | error e => rw [hp1] at hps; cases hps
                | ok ph =>
                    rw [hp1] at hps
                    cases hp2 : valTreeFieldsToPat _ vt with
                    | error e => rw [hp2] at hps; cases hps
                    | ok pt =>
                        rw [hp2] at hps; cases hps
                        simp only [patMatchesFields, structuralEqFields]
                        rw [activeVariant_pat_matches_iff_structural_eq hch hxh h1 hp1,
                            activeVariant_pat_matches_fields hct hxt h2 hp2]

  /-- Mutual array-list lemma for Theorem 3. -/
  theorem activeVariant_pat_matches_array :
      ∀ {ce xe : AllocFields} {elemTy : Ty} {n : Nat} {ts : ValTreeList} {ps : PatFields},
        HasTyArray ce elemTy n → HasTyArray xe elemTy n →
        toValTreeFields ce = .ok ts →
        lowerArrayPat (valTreeToPat elemTy) n ts = .ok ps →
        patMatchesFields ps xe = structuralEqFields ce xe
    | _, _, _, _, _, _, .nil _, .nil _, hts, hps => by
        cases hts; cases hps; rfl
    | _, _, _, _, _, _, .cons hch hct, .cons hxh hxt, hts, hps => by
        simp only [toValTreeFields] at hts
        cases h1 : toValTree _ with
        | error e => rw [h1] at hts; cases hts
        | ok vh =>
            rw [h1] at hts
            cases h2 : toValTreeFields _ with
            | error e => rw [h2] at hts; cases hts
            | ok vt =>
                rw [h2] at hts; cases hts
                simp only [lowerArrayPat] at hps
                cases hp1 : valTreeToPat _ vh with
                | error e => rw [hp1] at hps; cases hps
                | ok ph =>
                    rw [hp1] at hps
                    cases hp2 : lowerArrayPat (valTreeToPat _) _ vt with
                    | error e => rw [hp2] at hps; cases hps
                    | ok pt =>
                        rw [hp2] at hps; cases hps
                        simp only [patMatchesFields, structuralEqFields]
                        rw [activeVariant_pat_matches_iff_structural_eq hch hxh h1 hp1,
                            activeVariant_pat_matches_array hct hxt h2 hp2]
end

/-! ## 5. Theorem 4 Family: Provenance, Wide-Ptr, FnPtr, Union, NaN & FnDef Fail-Closed Rejections -/

theorem provenance_raw_ptr_rejected (addr allocId : Nat) :
    toValTree (.thinRawPtr addr (some allocId)) = .error .provenanceRawPtr := rfl

theorem wide_raw_ptr_rejected (addr metaLen : Nat) (prov : Provenance) :
    toValTree (.wideRawPtr addr metaLen prov) = .error .wideRawPtr := rfl

theorem fn_ptr_rejected (sym : Nat) :
    toValTree (.fnPtr sym) = .error .fnPtr := rfl

theorem union_rejected (name : String) (raw : List MemByte) :
    toValTree (.unionVal name raw) = .error .unionType := rfl

theorem nan_pattern_rejected (payload : Nat) :
    valTreeToPat .float (.leafFloat (.nan payload)) = .error .nanPattern := rfl

theorem float_neg_zero_matches_pos_zero :
    patMatches (.constFloat .posZero) (.floatVal .negZero) = true ∧
    patMatches (.constFloat .negZero) (.floatVal .posZero) = true ∧
    ∀ p, patMatches (.constFloat .posZero) (.floatVal (.nan p)) = false :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem fndef_valtree_ok_but_pat_rejected (sym : Nat) :
    toValTree (.fnDef sym) = .ok ValTree.zst ∧
    valTreeToPat (.fnDef sym) ValTree.zst = .error (.unsupportedType "fnDef") :=
  ⟨rfl, rfl⟩

/-! ## 6. Injective `v0` Symbol Mangling Over Canonical `ValTree`s & Backref Deduplication -/

/-- Token grammar modeling `compiler/rustc_symbol_mangling/src/v0.rs:808-946`. -/
inductive V0Tok where
  | intLit (isNeg : Bool) (mag : Nat)                              -- `Kl[n]<hex>_`
  | boolLit (b : Bool)                                             -- `Kb0_` / `Kb1_`
  | refPrefix                                                      -- `KR`
  | arrStart                                                       -- `KA`
  | structStart (name : String)                                    -- `KVNt...<name>S`
  | fieldTag (fieldName : String)                                  -- `<len><fieldName>`
  | variantStart (enumName : String) (vIdx : Nat) (vName : String) -- `KVNtNt...<enum><var>S`
  | endTok                                                         -- `E`
  | backref (slot : Nat)                                           -- `KB<base62>_`
  deriving DecidableEq

/-- Encode signed `Int` as `(isNeg, unsignedMagnitude)` matching `v0.rs:819-829`. -/
noncomputable def encodeSignedInt : Int → Bool × Nat
  | .ofNat n => (false, n)
  | .negSucc k => (true, k + 1)

/-- Decode `(isNeg, unsignedMagnitude)` back to `Int`. -/
noncomputable def decodeSignedInt : Bool → Nat → Option Int
  | false, n => some (.ofNat n)
  | true, 0 => none
  | true, k + 1 => some (.negSucc k)

theorem decode_encodeSignedInt (v : Int) :
    let p := encodeSignedInt v
    decodeSignedInt p.1 p.2 = some v := by
  cases v with
  | ofNat n => rfl
  | negSucc k => rfl

/-- Array-element helper lifting a `v0` mangler over a fixed-length `ValTreeList`. -/
noncomputable def mangleArrayToks (f : ValTree → Except ValTreeErr (List V0Tok)) :
    Nat → ValTreeList → Except ValTreeErr (List V0Tok)
  | 0, .nil => .ok []
  | n + 1, .cons vh vt =>
      match f vh with
      | .error e => .error e
      | .ok th =>
          match mangleArrayToks f n vt with
          | .error e => .error e
          | .ok tt => .ok (th ++ tt)
  | _, _ => .error .layoutMismatch

/-- Array-element helper lifting a `v0` parser over a fixed-length token stream. -/
noncomputable def parseArrayToks (f : List V0Tok → Option (ValTree × List V0Tok)) :
    Nat → List V0Tok → Option (ValTreeList × List V0Tok)
  | 0, rest => some (.nil, rest)
  | n + 1, rest =>
      match f rest with
      | some (vh, rest1) =>
          match parseArrayToks f n rest1 with
          | some (vt, rest2) => some (.cons vh vt, rest2)
          | none => none
      | none => none

mutual
  /-- Type-directed `v0` symbol mangler (`V0SymbolMangler::print_const`) over `ConstParamTy`
  canonical `ValTree`s. -/
  noncomputable def mangleValTree : Ty → ValTree → Except ValTreeErr (List V0Tok)
    | .int, .leafInt v =>
        let p := encodeSignedInt v
        .ok [.intLit p.1 p.2]
    | .bool, .leafBool b => .ok [.boolLit b]
    | .ref inner, vt =>
        match mangleValTree inner vt with
        | .ok toks => .ok (.refPrefix :: toks)
        | .error e => .error e
    | .array elemTy len, .branch ts =>
        match mangleArrayToks (mangleValTree elemTy) len ts with
        | .ok toks => .ok (.arrStart :: (toks ++ [.endTok]))
        | .error e => .error e
    | .structTy name _ _ ftys, .branch ts =>
        match mangleValTreeFields ftys ts with
        | .ok toks => .ok (.structStart name :: (toks ++ [.endTok]))
        | .error e => .error e
    | .enumTy name _ variants, .branch (.cons (.leafInt (.ofNat vIdx)) ts) =>
        mangleValTreeVariants name variants vIdx ts
    | _, _ => .error .layoutMismatch
  termination_by structural ty => ty

  /-- Variant lookup + mangling (structurally recursive on `VariantDecls`). -/
  noncomputable def mangleValTreeVariants (name : String) :
      VariantDecls → Nat → ValTreeList → Except ValTreeErr (List V0Tok)
    | .nil, _, _ => .error .layoutMismatch
    | .cons vName _ ftys _, 0, ts =>
        match mangleValTreeFields ftys ts with
        | .ok toks => .ok (.variantStart name 0 vName :: (toks ++ [.endTok]))
        | .error e => .error e
    | .cons _ _ _ rest, n + 1, ts =>
        match mangleValTreeVariants name rest n ts with
        | .ok (.variantStart nm idx vn :: tail) => .ok (.variantStart nm (idx + 1) vn :: tail)
        | .ok other => .ok other
        | .error e => .error e
  termination_by structural vs => vs

  /-- Field-list mangler emitting disambiguated field identifiers before each child `ValTree`. -/
  noncomputable def mangleValTreeFields : TyFields → ValTreeList → Except ValTreeErr (List V0Tok)
    | .nil, .nil => .ok []
    | .cons fName ty rest, .cons vh vt =>
        match mangleValTree ty vh with
        | .error e => .error e
        | .ok th =>
            match mangleValTreeFields rest vt with
            | .error e => .error e
            | .ok tt => .ok (.fieldTag fName :: (th ++ tt))
    | _, _ => .error .layoutMismatch
  termination_by structural ftys => ftys
end

mutual
  /-- Prefix-free recursive-descent inverse parser for `mangleValTree`. -/
  noncomputable def parseValTree : Ty → List V0Tok → Option (ValTree × List V0Tok)
    | .int, .intLit neg mag :: rest =>
        match decodeSignedInt neg mag with
        | some v => some (.leafInt v, rest)
        | none => none
    | .bool, .boolLit b :: rest => some (.leafBool b, rest)
    | .ref inner, .refPrefix :: rest => parseValTree inner rest
    | .array elemTy len, .arrStart :: rest =>
        match parseArrayToks (parseValTree elemTy) len rest with
        | some (ts, .endTok :: tail) => some (.branch ts, tail)
        | _ => none
    | .structTy name _ _ ftys, .structStart n :: rest =>
        if n = name then
          match parseValTreeFields ftys rest with
          | some (ts, .endTok :: tail) => some (.branch ts, tail)
          | _ => none
        else
          none
    | .enumTy name _ variants, .variantStart n vIdx vName :: rest =>
        if n = name then
          parseValTreeVariants variants vIdx vName rest
        else
          none
    | _, _ => none
  termination_by structural ty => ty

  /-- Variant lookup + inverse parser. -/
  noncomputable def parseValTreeVariants :
      VariantDecls → Nat → String → List V0Tok → Option (ValTree × List V0Tok)
    | .nil, _, _, _ => none
    | .cons expName _ ftys _, 0, vName, rest =>
        if vName = expName then
          match parseValTreeFields ftys rest with
          | some (ts, .endTok :: tail) => some (.branch (.cons (.leafInt (.ofNat 0)) ts), tail)
          | _ => none
        else
          none
    | .cons _ _ _ restV, n + 1, vName, rest =>
        match parseValTreeVariants restV n vName rest with
        | some (.branch (.cons (.leafInt (.ofNat idx)) ts), tail) =>
            some (.branch (.cons (.leafInt (.ofNat (idx + 1))) ts), tail)
        | _ => none
  termination_by structural vs => vs

  /-- Field-list inverse parser. -/
  noncomputable def parseValTreeFields : TyFields → List V0Tok → Option (ValTreeList × List V0Tok)
    | .nil, rest => some (.nil, rest)
    | .cons fName ty restF, .fieldTag tag :: rest =>
        if tag = fName then
          match parseValTree ty rest with
          | some (vh, rest1) =>
              match parseValTreeFields restF rest1 with
              | some (vt, rest2) => some (.cons vh vt, rest2)
              | none => none
          | none => none
        else
          none
    | _, _ => none
  termination_by structural ftys => ftys
end

theorem parseArrayToks_mangleArrayToks
    {m : ValTree → Except ValTreeErr (List V0Tok)}
    {p : List V0Tok → Option (ValTree × List V0Tok)}
    (helem : ∀ vt toks rest, m vt = .ok toks → p (toks ++ rest) = some (vt, rest)) :
    ∀ (len : Nat) (ts : ValTreeList) (toks rest : List V0Tok),
      mangleArrayToks m len ts = .ok toks →
      parseArrayToks p len (toks ++ rest) = some (ts, rest)
  | 0, .nil, toks, rest, h => by cases h; rfl
  | n + 1, .cons vh vt, toks, rest, h => by
      simp only [mangleArrayToks] at h
      cases h1 : m vh with
      | error e => rw [h1] at h; cases h
      | ok th =>
          rw [h1] at h
          cases h2 : mangleArrayToks m n vt with
          | error e => rw [h2] at h; cases h
          | ok tt =>
              rw [h2] at h; cases h
              simp only [List.append_assoc, parseArrayToks,
                         helem vh th (tt ++ rest) h1,
                         parseArrayToks_mangleArrayToks helem n vt tt rest h2]
  | 0, .cons _ _, _, _, h => by cases h
  | _ + 1, .nil, _, _, h => by cases h

mutual
  /-- Prefix-free left-inverse law: `parseValTree` recovers `vt` and the unconsumed suffix `rest`. -/
  theorem parseValTree_mangleValTree :
      ∀ (ty : Ty) (vt : ValTree) (toks rest : List V0Tok),
        mangleValTree ty vt = .ok toks →
        parseValTree ty (toks ++ rest) = some (vt, rest)
    | .int, vt, toks, rest, h => by
        cases vt with
        | leafInt v =>
            cases h
            simp only [List.cons_append, List.nil_append, parseValTree, decode_encodeSignedInt]
        | leafBool _ | leafFloat _ | leafPtrAddr _ | branch _ => cases h
    | .bool, vt, toks, rest, h => by
        cases vt with
        | leafBool b => cases h; rfl
        | leafInt _ | leafFloat _ | leafPtrAddr _ | branch _ => cases h
    | .ref inner, vt, toks, rest, h => by
        simp only [mangleValTree] at h
        cases hm : mangleValTree inner vt with
        | error e => rw [hm] at h; cases h
        | ok innerToks =>
            rw [hm] at h; cases h
            simp only [List.cons_append, parseValTree]
            exact parseValTree_mangleValTree inner vt innerToks rest hm
    | .array elemTy len, vt, toks, rest, h => by
        cases vt with
        | branch ts =>
            simp only [mangleValTree] at h
            cases hm : mangleArrayToks (mangleValTree elemTy) len ts with
            | error e => rw [hm] at h; cases h
            | ok elemToks =>
                rw [hm] at h; cases h
                simp only [List.cons_append, List.append_assoc, List.nil_append, parseValTree]
                rw [parseArrayToks_mangleArrayToks
                      (fun v t r h' => parseValTree_mangleValTree elemTy v t r h')
                      len ts elemToks (.endTok :: rest) hm]
        | leafInt _ | leafBool _ | leafFloat _ | leafPtrAddr _ => cases h
    | .structTy name s p ftys, vt, toks, rest, h => by
        cases vt with
        | branch ts =>
            simp only [mangleValTree] at h
            cases hm : mangleValTreeFields ftys ts with
            | error e => rw [hm] at h; cases h
            | ok fieldToks =>
                rw [hm] at h; cases h
                simp only [List.cons_append, List.append_assoc, List.nil_append, parseValTree,
                           ↓reduceIte]
                rw [parseValTreeFields_mangleValTreeFields ftys ts fieldToks (.endTok :: rest) hm]
        | leafInt _ | leafBool _ | leafFloat _ | leafPtrAddr _ => cases h
    | .enumTy name s variants, vt, toks, rest, h => by
        cases vt with
        | branch bs =>
            cases bs with
            | nil => cases h
            | cons hd ts =>
                cases hd with
                | leafInt iv =>
                    cases iv with
                    | negSucc _ => cases h
                    | ofNat vIdx =>
                        simp only [mangleValTree] at h
                        have ⟨vName, body, htok, hparse⟩ :=
                          parseValTreeVariants_mangleValTreeVariants name variants vIdx ts toks rest h
                        subst htok
                        simp only [List.cons_append, parseValTree, ↓reduceIte]
                        exact hparse
                | leafBool _ | leafFloat _ | leafPtrAddr _ | branch _ => cases h
        | leafInt _ | leafBool _ | leafFloat _ | leafPtrAddr _ => cases h
    | .float, _, _, _, h => by cases h
    | .thinRawPtr, _, _, _, h => by cases h
    | .wideRawPtr, _, _, _, h => by cases h
    | .fnPtr, _, _, _, h => by cases h
    | .fnDef _, _, _, _, h => by cases h
    | .unionTy _, _, _, _, h => by cases h
  termination_by structural ty => ty

  /-- Variant-list prefix-free round-trip lemma. -/
  theorem parseValTreeVariants_mangleValTreeVariants (name : String) :
      ∀ (vs : VariantDecls) (vIdx : Nat) (ts : ValTreeList) (toks rest : List V0Tok),
        mangleValTreeVariants name vs vIdx ts = .ok toks →
        ∃ vName body,
          toks = .variantStart name vIdx vName :: body ∧
          parseValTreeVariants vs vIdx vName (body ++ rest) =
            some (.branch (.cons (.leafInt (.ofNat vIdx)) ts), rest)
    | .nil, _, _, _, _, h => by cases h
    | .cons vName _ ftys _, 0, ts, toks, rest, h => by
        simp only [mangleValTreeVariants] at h
        cases hm : mangleValTreeFields ftys ts with
        | error e => rw [hm] at h; cases h
        | ok fieldToks =>
            rw [hm] at h; cases h
            refine ⟨vName, fieldToks ++ [.endTok], rfl, ?_⟩
            simp only [List.append_assoc, List.cons_append, List.nil_append,
                       parseValTreeVariants, ↓reduceIte,
                       parseValTreeFields_mangleValTreeFields ftys ts fieldToks (.endTok :: rest) hm]
    | .cons _ _ _ restV, n + 1, ts, toks, rest, h => by
        simp only [mangleValTreeVariants] at h
        cases hrec : mangleValTreeVariants name restV n ts with
        | error e => rw [hrec] at h; cases h
        | ok innerToks =>
            have ⟨vName, body, htok, hparse⟩ :=
              parseValTreeVariants_mangleValTreeVariants name restV n ts innerToks rest hrec
            subst htok
            rw [hrec] at h
            cases h
            refine ⟨vName, body, rfl, ?_⟩
            simp only [parseValTreeVariants, hparse]
  termination_by structural vs => vs

  /-- Field-list prefix-free round-trip lemma. -/
  theorem parseValTreeFields_mangleValTreeFields :
      ∀ (ftys : TyFields) (ts : ValTreeList) (toks rest : List V0Tok),
        mangleValTreeFields ftys ts = .ok toks →
        parseValTreeFields ftys (toks ++ rest) = some (ts, rest)
    | .nil, .nil, toks, rest, h => by cases h; rfl
    | .cons fName ty restF, .cons vh vt, toks, rest, h => by
        simp only [mangleValTreeFields] at h
        cases h1 : mangleValTree ty vh with
        | error e => rw [h1] at h; cases h
        | ok th =>
            rw [h1] at h
            cases h2 : mangleValTreeFields restF vt with
            | error e => rw [h2] at h; cases h
            | ok tt =>
                rw [h2] at h; cases h
                simp only [List.cons_append, List.append_assoc, parseValTreeFields,
                           ↓reduceIte,
                           parseValTree_mangleValTree ty vh th (tt ++ rest) h1,
                           parseValTreeFields_mangleValTreeFields restF vt tt rest h2]
    | .nil, .cons _ _, _, _, h => by cases h
    | .cons _ _ _, .nil, _, _, h => by cases h
  termination_by structural ftys => ftys
end

/-- Injectivity of `v0` symbol mangling over canonical `ValTree`s for a fixed type `ty`. -/
theorem mangleValTree_injective {ty : Ty} {vt1 vt2 : ValTree} {toks : List V0Tok}
    (h1 : mangleValTree ty vt1 = .ok toks) (h2 : mangleValTree ty vt2 = .ok toks) :
    vt1 = vt2 := by
  have p1 := parseValTree_mangleValTree ty vt1 toks [] h1
  have p2 := parseValTree_mangleValTree ty vt2 toks [] h2
  rw [p1] at p2
  injection p2 with hpair
  injection hpair

/-- Two-argument `v0` mangling with `self.consts` backref cache (`v0.rs:803-806, 943-945`). -/
noncomputable def manglePairWithBackref (ty : Ty) (a1 a2 : AllocVal) : Except ValTreeErr (List V0Tok × List V0Tok) :=
  match toValTree a1, toValTree a2 with
  | .ok vt1, .ok vt2 =>
      match mangleValTree ty vt1 with
      | .error e => .error e
      | .ok t1 =>
          if valTreeEq vt1 vt2 then
            .ok (t1, [.backref 0])
          else
            match mangleValTree ty vt2 with
            | .error e => .error e
            | .ok t2 => .ok (t1, t2)
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Quotient symbol merging: two `AllocVal`s differing only in padding or reference addresses
collapse to the same `ValTree` and trigger `v0` `KB` backref deduplication. -/
theorem manglePairWithBackref_dedups_mod_pad_and_ref {ty : Ty} {a1 a2 : AllocVal} {vt : ValTree}
    {toks : List V0Tok}
    (hsame : SameFieldsModPadAndRef a1 a2)
    (hvt : toValTree a1 = .ok vt)
    (hm : mangleValTree ty vt = .ok toks) :
    manglePairWithBackref ty a1 a2 = .ok (toks, [.backref 0]) := by
  have hvt2 : toValTree a2 = .ok vt := by
    rw [← toValTree_ignores_padding_and_ref_addr hsame, hvt]
  simp only [manglePairWithBackref, hvt, hvt2, hm, valTreeEq_refl, ↓reduceIte]

/-! ## 7. `VALTREE_MAX_NODES` vs. DAG `settled` Memoization -/

/-- Exact upstream constant `compiler/rustc_const_eval/src/const_eval/mod.rs:29`. -/
noncomputable def VALTREE_MAX_NODES : Nat := 100000

/-- Logical leaf count of a binary sharing DAG of depth `d` (`2^d`). -/
noncomputable def dagLogicalLeaves : Nat → Nat
  | 0 => 1
  | d + 1 => dagLogicalLeaves d + dagLogicalLeaves d

/-- Total visits without `settled` memoization (pre-cycle-detection `valtrees.rs`: `2^(d+1) - 1`). -/
noncomputable def dagUnmemoizedVisits : Nat → Nat
  | 0 => 1
  | d + 1 => 1 + dagUnmemoizedVisits d + dagUnmemoizedVisits d

/-- Lookup in an association list modeling `settled : FxHashMap<MPlaceTy, ValTree>`. -/
noncomputable def settledLookup (settled : List (Nat × Nat)) (nodeId : Nat) : Option Nat :=
  match settled with
  | [] => none
  | (k, v) :: rest => if k = nodeId then some v else settledLookup rest nodeId

/-- Executable simulation of `const_to_valtree_inner` with `settled` DAG memoization over a
binary sharing DAG where node `0` is `Leaf(1)` and node `k + 1` is `Pair(&N_k, &N_k)`.
A cache hit in `settled` returns immediately without incrementing `numNodes` (`valtrees.rs:94-96`). -/
noncomputable def evalBinaryDagMemo (nodeId : Nat) (numNodes : Nat) (settled : List (Nat × Nat)) :
    Nat × List (Nat × Nat) :=
  match settledLookup settled nodeId with
  | some _ => (numNodes, settled)
  | none =>
      match nodeId with
      | 0 => (numNodes + 1, (0, 1) :: settled)
      | k + 1 =>
          let (n1, s1) := evalBinaryDagMemo k numNodes settled
          let (n2, s2) := evalBinaryDagMemo k n1 s1
          (n2 + 1, (k + 1, 1) :: s2)

/-- Distinct nodes charged by `evalBinaryDagMemo` starting from an empty `settled` cache. -/
noncomputable def settledNodeCount (d : Nat) : Nat :=
  (evalBinaryDagMemo d 0 []).1

theorem settledLookup_ne_none_of_mem :
    ∀ (s : List (Nat × Nat)) (a b : Nat),
      (a, b) ∈ s → settledLookup s a ≠ none
  | [], _, _, hp => nomatch hp
  | (k, v) :: rest, a, b, hp => by
      cases hp with
      | head =>
          simp only [settledLookup, ↓reduceIte]
          intro hc; cases hc
      | tail _ htl =>
          simp only [settledLookup]
          cases decEq k a with
          | isTrue hk => simp only [hk, ↓reduceIte]; intro hc; cases hc
          | isFalse hk => simp only [hk, ↓reduceIte]; exact settledLookup_ne_none_of_mem rest a b htl

theorem evalBinaryDagMemo_spec :
    ∀ (d numNodes : Nat) (s : List (Nat × Nat)),
      (∀ p ∈ s, p.1 < d + 1) →
      (∀ j, j ≤ d → settledLookup s j = none) →
      let res := evalBinaryDagMemo d numNodes s
      res.1 = numNodes + (d + 1) ∧
      settledLookup res.2 d = some 1 ∧
      (∀ p ∈ res.2, p.1 < d + 1)
  | 0, numNodes, s, hlt, hnone => by
      have h0 : settledLookup s 0 = none := hnone 0 (Nat.le_refl 0)
      simp only [evalBinaryDagMemo, h0]
      refine ⟨trivial, ?_, ?_⟩
      · simp only [settledLookup, ↓reduceIte]
      · intro p hp
        cases hp with
        | head => exact Nat.zero_lt_succ 0
        | tail _ hp' =>
            cases p with
            | mk a b =>
                have ha0 : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hlt (a, b) hp'))
                subst ha0
                exact False.elim (settledLookup_ne_none_of_mem s 0 b hp' h0)
  | k + 1, numNodes, s, hlt, hnone => by
      have hk1 : settledLookup s (k + 1) = none := hnone (k + 1) (Nat.le_refl _)
      have hlt_k : ∀ p ∈ s, p.1 < k + 1 := by
        intro p hp
        cases p with
        | mk a b =>
            have hle : a ≤ k + 1 := Nat.le_of_lt_succ (hlt (a, b) hp)
            cases Nat.eq_or_lt_of_le hle with
            | inl heq =>
                subst heq
                exact False.elim (settledLookup_ne_none_of_mem s (k + 1) b hp hk1)
            | inr hlt' => exact hlt'
      have ih := evalBinaryDagMemo_spec k numNodes s hlt_k
        (fun j hj => hnone j (Nat.le_succ_of_le hj))
      simp only [evalBinaryDagMemo, hk1]
      rcases ih with ⟨hcnt, hfound, hbound⟩
      have hsecond : evalBinaryDagMemo k (evalBinaryDagMemo k numNodes s).1
          (evalBinaryDagMemo k numNodes s).2 =
          ((evalBinaryDagMemo k numNodes s).1, (evalBinaryDagMemo k numNodes s).2) := by
        rw [evalBinaryDagMemo.eq_def, hfound]
      rw [hsecond]
      refine ⟨?_, ?_, ?_⟩
      · rw [hcnt, Nat.add_assoc]
      · simp only [settledLookup, ↓reduceIte]
      · intro p hp
        cases hp with
        | head => exact Nat.lt_succ_self (k + 1)
        | tail _ htl => exact Nat.lt_succ_of_lt (hbound p htl)

/-- Closed-form node count under `settled` memoization: exactly `d + 1` distinct nodes visited. -/
theorem settledNodeCount_eq (d : Nat) : settledNodeCount d = d + 1 := by
  have h := evalBinaryDagMemo_spec d 0 []
    (fun _ hp => nomatch hp)
    (fun _ _ => rfl)
  simp only [settledNodeCount, h.1, Nat.zero_add]

/-! ## 8. Constructive Counterexamples (`ce1`, `ce2`, `ce3`) -/

/-- Type of `#[repr(C)] #[derive(PartialEq, Eq, ConstParamTy)] struct Padded { a: u8, b: u32 }`
with 3 bytes of internal padding after `a`. -/
noncomputable def paddedStructTy : Ty :=
  .structTy "Padded" true 3 (.cons "a" .int (.cons "b" .int .nil))

/-- `PAD_ZERO`: `Padded { a: 1, b: 2 }` with `[0, 0, 0]` padding bytes. -/
noncomputable def padZeroVal : AllocVal :=
  .structVal "Padded" [.init 0, .init 0, .init 0]
    (.cons (.intVal 1) (.cons (.intVal 2) .nil))

/-- `PAD_DEAD`: `Padded { a: 1, b: 2 }` with `[0xDE, 0xAD, 0xBE]` padding bytes. -/
noncomputable def padDeadVal : AllocVal :=
  .structVal "Padded" [.init 0xDE, .init 0xAD, .init 0xBE]
    (.cons (.intVal 1) (.cons (.intVal 2) .nil))

/-- Counterexample 1: Distinct concrete padding byte sequences unify to the exact same `ValTree`,
collapse to the exact same `v0` mangled symbol (deduplicating via `KB` backref), and reconstruct
with all 3 padding bytes strictly uninitialized (`MemByte.uninit`). -/
theorem ce1_distinct_padding_bytes_unify_to_same_valtree :
    padZeroVal ≠ padDeadVal ∧
    toValTree padZeroVal = toValTree padDeadVal ∧
    (∃ vt toks,
      toValTree padZeroVal = .ok vt ∧
      manglePairWithBackref paddedStructTy padZeroVal padDeadVal = .ok (toks, [.backref 0]) ∧
      fromValTree paddedStructTy vt = .ok
        (.structVal "Padded" [.uninit, .uninit, .uninit]
          (.cons (.intVal 1) (.cons (.intVal 2) .nil)))) := by
  refine ⟨?_, rfl, ?_⟩
  · intro h; cases h
  · refine ⟨.branch (.cons (.leafInt 1) (.cons (.leafInt 2) .nil)),
            [.structStart "Padded", .fieldTag "a", .intLit false 1,
             .fieldTag "b", .intLit false 2, .endTok],
            rfl, rfl, rfl⟩

/-- `struct Manual(u8)` with a manual (non-structural) `impl PartialEq`. -/
noncomputable def manualTy : Ty :=
  .structTy "Manual" false 0 (.cons "0" .int .nil)

/-- `#[derive(PartialEq)] enum Wrap<Manual> { Empty, Full(Manual) }`.
Variant 0 (`Empty`) has no fields; variant 1 (`Full`) contains non-structural `Manual`. -/
noncomputable def wrapManualTy : Ty :=
  .enumTy "Wrap" true
    (.cons "Empty" 0 .nil
      (.cons "Full" 0 (.cons "0" manualTy .nil) .nil))

/-- `const C_EMPTY: Wrap<Manual> = Wrap::Empty`. -/
noncomputable def wrapEmptyVal : AllocVal :=
  .enumVal "Wrap" 0 [] .nil

/-- `const C_FULL: Wrap<Manual> = Wrap::Full(Manual(1))`. -/
noncomputable def wrapFullVal : AllocVal :=
  .enumVal "Wrap" 1 [] (.cons (.structVal "Manual" [] (.cons (.intVal 1) .nil)) .nil)

/-- Counterexample 2: Active-variant-only recursion in `valTreeToPat` admits `Wrap::Empty`
even though `Wrap<Manual>`'s inactive `Full` variant holds non-structural `Manual`, while
rejecting `Wrap::Full(Manual(1))` with `.nonStructural "Manual"`. -/
theorem ce2_inactive_nonstructural_variant_payload_admitted :
    (∃ vtEmpty,
      toValTree wrapEmptyVal = .ok vtEmpty ∧
      valTreeToPat wrapManualTy vtEmpty = .ok (.variantPat "Wrap" 0 .nil)) ∧
    (∃ vtFull,
      toValTree wrapFullVal = .ok vtFull ∧
      valTreeToPat wrapManualTy vtFull = .error (.nonStructural "Manual")) := by
  exact ⟨⟨.branch (.cons (.leafInt 0) .nil), rfl, rfl⟩,
         ⟨.branch (.cons (.leafInt 1) (.cons (.branch (.cons (.leafInt 1) .nil)) .nil)), rfl, rfl⟩⟩

/-- Counterexample 3: At binary DAG depth `d = 18`, `settled` memoization charges only `19`
distinct nodes (`< VALTREE_MAX_NODES = 100_000`), admitting a DAG whose logical tree expansion
contains `2^18 = 262,144` leaves (`> VALTREE_MAX_NODES`) and `524,287` unmemoized visits. -/
theorem ce3_dag_memoized_node_count_exponentially_below_tree_leaves :
    settledNodeCount 18 = 19 ∧
    settledNodeCount 18 < VALTREE_MAX_NODES ∧
    dagLogicalLeaves 18 = 262144 ∧
    VALTREE_MAX_NODES < dagLogicalLeaves 18 ∧
    dagUnmemoizedVisits 18 = 524287 ∧
    VALTREE_MAX_NODES < dagUnmemoizedVisits 18 := by
  refine ⟨settledNodeCount_eq 18, ?_, rfl, ?_, rfl, ?_⟩
  · rw [settledNodeCount_eq 18]
    exact of_decide_eq_true (rfl : decide (19 < 100000) = true)
  · exact of_decide_eq_true (rfl : decide (100000 < 262144) = true)
  · exact of_decide_eq_true (rfl : decide (100000 < 524287) = true)

end ValTreeFormal

/-! ## 9. Kernel Axiom Audit -/

#print axioms ValTreeFormal.toValTree_ignores_padding_and_ref_addr
#print axioms ValTreeFormal.fromValTree_preserves_fields_and_uninit_padding
#print axioms ValTreeFormal.activeVariant_pat_matches_iff_structural_eq
#print axioms ValTreeFormal.provenance_raw_ptr_rejected
#print axioms ValTreeFormal.wide_raw_ptr_rejected
#print axioms ValTreeFormal.fn_ptr_rejected
#print axioms ValTreeFormal.union_rejected
#print axioms ValTreeFormal.nan_pattern_rejected
#print axioms ValTreeFormal.fndef_valtree_ok_but_pat_rejected
#print axioms ValTreeFormal.mangleValTree_injective
#print axioms ValTreeFormal.manglePairWithBackref_dedups_mod_pad_and_ref
#print axioms ValTreeFormal.settledNodeCount_eq
#print axioms ValTreeFormal.ce1_distinct_padding_bytes_unify_to_same_valtree
#print axioms ValTreeFormal.ce2_inactive_nonstructural_variant_payload_admitted
#print axioms ValTreeFormal.ce3_dag_memoized_node_count_exponentially_below_tree_leaves
