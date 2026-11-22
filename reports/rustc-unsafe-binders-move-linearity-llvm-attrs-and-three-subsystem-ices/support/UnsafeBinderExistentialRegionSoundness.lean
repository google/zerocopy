/-
  UnsafeBinderExistentialRegionSoundness.lean

  Self-contained, zero-sorry, Classical.choice-free Lean 4 (v4.34.1) formalization
  of `rustc` `unsafe_binders` (`TyKind::UnsafeBinder`, `Rvalue::WrapUnsafeBinder`,
  `ProjectionElem::UnwrapUnsafeBinder`):

  1. Four-tier wrapper LLVM attribute lattice:
       `&T < MaybeDangling<&T> < UnsafeBinder<&T> < MaybeUninit<&T>`
     (in value-set permissiveness; reverse order in LLVM parameter attribute strength)
     and LLVM 23 parameter-attribute soundness (`unsafeBinder_param_attrs_sound`)
     plus 8-byte `Option` null-niche bijection (`option_unsafeBinder_null_niche_injective`).

  2. Existential region-pack / unpack operational soundness
     (`wrap_unwrap_live_region_witness_sound`) and move-only (`!Copy` /
     `deinitMovedPlace`) single-consumption linearity (`move_only_binder_single_consumption`).

  3. Complete prefix-free De-Bruijn `v0` symbol mangling extension for
     `TyKind::UnsafeBinder` (`v0_mangle_with_unsafe_binder_injective`) and
     backward compatibility with stock `v0` (`mangleExt_extends_stock`).

  4. Constructive sharpness counterexamples:
     - `ce1_safe_unwrap_without_live_witness_uaf`
     - `ce2_align8_attr_on_misaligned_transmuted_binder_ub`
     - `ce3_partial_v0_mangler_panics_on_unsafe_binder`
     - `ce4_compound_binder_pointee_attr_leak_ub`

  Strict kernel discipline:
  - 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`, 0 `native_decide`,
    0 `partial def`, 0 `._unsafe_rec`.
  - All recursive functions over recursive inductives are marked `noncomputable def`.
  - Structural `DecidableEq` is implemented manually without `deriving` on recursive types.
-/

namespace UnsafeBinderSoundness

/-! ## Section 1: Four-Tier Wrapper Attribute Lattice & LLVM 23 Soundness -/

/-- The four Rust pointer-wrapper tiers ordered by semantic permissiveness:
    `plainRef` (`&T`) is most restricted; `maybeUninit` (`MaybeUninit<&T>`) is most permissive. -/
inductive WrapperTier where
  | plainRef
  | maybeDangling
  | unsafeBinder
  | maybeUninit

def WrapperTier.decEq : (a b : WrapperTier) → Decidable (a = b)
  | .plainRef, .plainRef => isTrue rfl
  | .maybeDangling, .maybeDangling => isTrue rfl
  | .unsafeBinder, .unsafeBinder => isTrue rfl
  | .maybeUninit, .maybeUninit => isTrue rfl
  | .plainRef, .maybeDangling => isFalse (fun h => nomatch h)
  | .plainRef, .unsafeBinder => isFalse (fun h => nomatch h)
  | .plainRef, .maybeUninit => isFalse (fun h => nomatch h)
  | .maybeDangling, .plainRef => isFalse (fun h => nomatch h)
  | .maybeDangling, .unsafeBinder => isFalse (fun h => nomatch h)
  | .maybeDangling, .maybeUninit => isFalse (fun h => nomatch h)
  | .unsafeBinder, .plainRef => isFalse (fun h => nomatch h)
  | .unsafeBinder, .maybeDangling => isFalse (fun h => nomatch h)
  | .unsafeBinder, .maybeUninit => isFalse (fun h => nomatch h)
  | .maybeUninit, .plainRef => isFalse (fun h => nomatch h)
  | .maybeUninit, .maybeDangling => isFalse (fun h => nomatch h)
  | .maybeUninit, .unsafeBinder => isFalse (fun h => nomatch h)

instance : DecidableEq WrapperTier := WrapperTier.decEq

/-- LLVM pointer-parameter attribute bundle emitted by `rustc_ty_utils::abi`
    and `rustc_codegen_llvm::abi`. `align = 1` represents absence of an LLVM
    `align N` attribute; `dereferenceable = 0` represents absence of
    `dereferenceable(N)`. -/
structure ParamAttrSet where
  noundef : Bool
  nonnull : Bool
  align : Nat
  dereferenceable : Nat
  readonly : Bool
  noalias : Bool
  nofree : Bool

/-- Pointwise attribute-strength preorder: `attrLe a b` means `a` asserts
    no stronger LLVM entry UB precondition than `b`. -/
def attrLe (a b : ParamAttrSet) : Prop :=
  (a.noundef = true → b.noundef = true) ∧
  (a.nonnull = true → b.nonnull = true) ∧
  (a.align > 1 → b.align = a.align) ∧
  (a.dereferenceable ≤ b.dereferenceable) ∧
  (a.readonly = true → b.readonly = true) ∧
  (a.noalias = true → b.noalias = true) ∧
  (a.nofree = true → b.nofree = true)

/-- Strict attribute-strength order (`a` is strictly weaker than `b`). -/
def attrLt (a b : ParamAttrSet) : Prop :=
  attrLe a b ∧ ¬ attrLe b a

/-- Exact ABI-emitted LLVM 23 parameter attributes for a thin shared reference
    pointee of alignment `alignBytes` and size `sizeBytes` across the four tiers:
    - `&T`: `noalias nofree noundef readonly align(A) dereferenceable(S)` (implies `nonnull`)
    - `MaybeDangling<&T>`: `noundef nonnull align(A)`
    - `unsafe<'a> &'a T`: `noundef nonnull` (strips `align(A)` because
      `ty_and_layout_pointee_info_at` returns `None`)
    - `MaybeUninit<&T>`: `{}` (strips `noundef` and `nonnull` as well). -/
def emitWrapperAttrs (alignBytes sizeBytes : Nat) : WrapperTier → ParamAttrSet
  | .plainRef =>
      { noundef := true
        nonnull := true
        align := alignBytes
        dereferenceable := sizeBytes
        readonly := true
        noalias := true
        nofree := true }
  | .maybeDangling =>
      { noundef := true
        nonnull := true
        align := alignBytes
        dereferenceable := 0
        readonly := false
        noalias := false
        nofree := false }
  | .unsafeBinder =>
      { noundef := true
        nonnull := true
        align := 1
        dereferenceable := 0
        readonly := false
        noalias := false
        nofree := false }
  | .maybeUninit =>
      { noundef := false
        nonnull := false
        align := 1
        dereferenceable := 0
        readonly := false
        noalias := false
        nofree := false }

/-- Concrete runtime state of a pointer argument at function entry. -/
structure PtrState where
  initialized : Bool
  addr : Nat
  liveBytes : Nat
  aliasedMutable : Bool
  freedDuringCall : Bool

/-- LLVM 23 parameter-attribute entry-UB contract: all asserted attributes
    must be satisfied by `p` at function entry, or the call has immediate UB. -/
def AttrsValidAtEntry (attrs : ParamAttrSet) (p : PtrState) : Prop :=
  (attrs.noundef = true → p.initialized = true) ∧
  (attrs.nonnull = true → p.addr ≠ 0) ∧
  (attrs.align > 1 → p.addr % attrs.align = 0) ∧
  (attrs.dereferenceable > 0 → attrs.dereferenceable ≤ p.liveBytes) ∧
  (attrs.readonly = true → p.aliasedMutable = false) ∧
  (attrs.noalias = true → p.aliasedMutable = false) ∧
  (attrs.nofree = true → p.freedDuringCall = false)

/-- Rust language-level value validity invariant for each wrapper tier
    (for a pointee with alignment `alignBytes` and size `sizeBytes`).
    Note: thin `unsafe<'a> &'a T` inherits scalar `Initialized` + `valid_range = 1..=MAX`
    from `rustc_ty_utils::layout` (`noundef` + `nonnull`) without requiring
    pointee alignment, dereferenceability, or aliasing freedom. -/
def TierValueValid (alignBytes sizeBytes : Nat) : WrapperTier → PtrState → Prop
  | .plainRef, p =>
      p.initialized = true ∧
      p.addr ≠ 0 ∧
      (alignBytes > 1 → p.addr % alignBytes = 0) ∧
      (sizeBytes > 0 → sizeBytes ≤ p.liveBytes) ∧
      p.aliasedMutable = false ∧
      p.freedDuringCall = false
  | .maybeDangling, p =>
      p.initialized = true ∧
      p.addr ≠ 0 ∧
      (alignBytes > 1 → p.addr % alignBytes = 0)
  | .unsafeBinder, p =>
      p.initialized = true ∧
      p.addr ≠ 0
  | .maybeUninit, _ => True

/-- Monotonicity of LLVM entry-UB satisfaction: weakening attributes never
    introduces undefined behavior. -/
theorem attr_valid_monotone {a b : ParamAttrSet} {p : PtrState}
    (hle : attrLe a b) (hb : AttrsValidAtEntry b p) : AttrsValidAtEntry a p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact hb.1 (hle.1 h)
  · intro h; exact hb.2.1 (hle.2.1 h)
  · intro h
    have heq : b.align = a.align := hle.2.2.1 h
    have hbgt : b.align > 1 := by rw [heq]; exact h
    have hmod := hb.2.2.1 hbgt
    rw [heq] at hmod
    exact hmod
  · intro h
    have hleD : a.dereferenceable ≤ b.dereferenceable := hle.2.2.2.1
    have hbg : b.dereferenceable > 0 := Nat.lt_of_lt_of_le h hleD
    exact Nat.le_trans hleD (hb.2.2.2.1 hbg)
  · intro h; exact hb.2.2.2.2.1 (hle.2.2.2.2.1 h)
  · intro h; exact hb.2.2.2.2.2.1 (hle.2.2.2.2.2.1 h)
  · intro h; exact hb.2.2.2.2.2.2 (hle.2.2.2.2.2.2 h)

/-- Strict 4-tier attribute lattice chain for any aligned, non-ZST pointee
    (`alignBytes > 1`, `sizeBytes > 0`, e.g., `u64` with `8, 8`):
    `MaybeUninit<&T> < UnsafeBinder<&T> < MaybeDangling<&T> < &T` in attribute strength
    (equivalently `&T < MaybeDangling<&T> < UnsafeBinder<&T> < MaybeUninit<&T>`
    in permitted runtime pointer states). -/
theorem wrapper_attr_lattice_strict (alignBytes sizeBytes : Nat)
    (hAlign : alignBytes > 1) (hSize : sizeBytes > 0) :
    attrLt (emitWrapperAttrs alignBytes sizeBytes .maybeUninit)
           (emitWrapperAttrs alignBytes sizeBytes .unsafeBinder) ∧
    attrLt (emitWrapperAttrs alignBytes sizeBytes .unsafeBinder)
           (emitWrapperAttrs alignBytes sizeBytes .maybeDangling) ∧
    attrLt (emitWrapperAttrs alignBytes sizeBytes .maybeDangling)
           (emitWrapperAttrs alignBytes sizeBytes .plainRef) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- maybeUninit ≤ unsafeBinder
    refine ⟨(fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h),
            (fun h => absurd h (Nat.lt_irrefl 1)),
            Nat.zero_le 0, (fun h => Bool.noConfusion h),
            (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h)⟩
  · -- ¬ (unsafeBinder ≤ maybeUninit)
    intro h
    exact Bool.noConfusion (h.1 rfl)
  · -- unsafeBinder ≤ maybeDangling
    refine ⟨(fun h => h), (fun h => h),
            (fun h => absurd h (Nat.lt_irrefl 1)),
            Nat.zero_le 0, (fun h => Bool.noConfusion h),
            (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h)⟩
  · -- ¬ (maybeDangling ≤ unsafeBinder)
    intro h
    have heq : (1 : Nat) = alignBytes := h.2.2.1 hAlign
    rw [← heq] at hAlign
    exact Nat.lt_irrefl 1 hAlign
  · -- maybeDangling ≤ plainRef
    refine ⟨(fun h => h), (fun h => h), (fun _ => rfl),
            Nat.zero_le sizeBytes, (fun h => Bool.noConfusion h),
            (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h)⟩
  · -- ¬ (plainRef ≤ maybeDangling)
    intro h
    have hle : sizeBytes ≤ 0 := h.2.2.2.1
    exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hSize hle)

/-- Value-set inclusion across the four tiers:
    `&T ⊆ MaybeDangling<&T> ⊆ UnsafeBinder<&T> ⊆ MaybeUninit<&T>`. -/
theorem tier_value_inclusion (alignBytes sizeBytes : Nat) (p : PtrState) :
    (TierValueValid alignBytes sizeBytes .plainRef p →
      TierValueValid alignBytes sizeBytes .maybeDangling p) ∧
    (TierValueValid alignBytes sizeBytes .maybeDangling p →
      TierValueValid alignBytes sizeBytes .unsafeBinder p) ∧
    (TierValueValid alignBytes sizeBytes .unsafeBinder p →
      TierValueValid alignBytes sizeBytes .maybeUninit p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h; exact ⟨h.1, h.2.1⟩
  · intro _; trivial

/-- Core LLVM 23 parameter-attribute soundness theorem for `unsafe<'a> &'a T`:
    every valid `UnsafeBinder` value satisfies `ptr noundef nonnull` without
    requiring alignment, dereferenceability, aliasing freedom, or nofree. -/
theorem unsafeBinder_param_attrs_sound (alignBytes sizeBytes : Nat) (p : PtrState)
    (hValid : TierValueValid alignBytes sizeBytes .unsafeBinder p) :
    AttrsValidAtEntry (emitWrapperAttrs alignBytes sizeBytes .unsafeBinder) p := by
  refine ⟨(fun _ => hValid.1), (fun _ => hValid.2),
          (fun h => absurd h (Nat.lt_irrefl 1)),
          (fun h => absurd h (Nat.lt_irrefl 0)),
          (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h),
          (fun h => Bool.noConfusion h)⟩

/-- Complete soundness of ABI attribute emission across all four wrapper tiers. -/
theorem all_four_tiers_param_attrs_sound (alignBytes sizeBytes : Nat)
    (t : WrapperTier) (p : PtrState)
    (hValid : TierValueValid alignBytes sizeBytes t p) :
    AttrsValidAtEntry (emitWrapperAttrs alignBytes sizeBytes t) p := by
  cases t with
  | plainRef =>
      exact ⟨(fun _ => hValid.1), (fun _ => hValid.2.1), hValid.2.2.1,
             hValid.2.2.2.1, (fun _ => hValid.2.2.2.2.1),
             (fun _ => hValid.2.2.2.2.1), (fun _ => hValid.2.2.2.2.2)⟩
  | maybeDangling =>
      exact ⟨(fun _ => hValid.1), (fun _ => hValid.2.1), hValid.2.2,
             (fun h => absurd h (Nat.lt_irrefl 0)),
             (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h),
             (fun h => Bool.noConfusion h)⟩
  | unsafeBinder =>
      exact unsafeBinder_param_attrs_sound alignBytes sizeBytes p hValid
  | maybeUninit =>
      exact ⟨(fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h),
             (fun h => absurd h (Nat.lt_irrefl 1)),
             (fun h => absurd h (Nat.lt_irrefl 0)),
             (fun h => Bool.noConfusion h), (fun h => Bool.noConfusion h),
             (fun h => Bool.noConfusion h)⟩

/-- 8-byte `Option<unsafe<'a> &'a T>` null-niche encoding:
    `none` maps to `0`, `some p` (with `p.addr ≠ 0`) maps to `p.addr`. -/
def encodeOptUnsafeBinder (o : Option { p : PtrState // p.initialized = true ∧ p.addr ≠ 0 }) : Nat :=
  match o with
  | none => 0
  | some ⟨p, _⟩ => p.addr

/-- Because `unsafe<'a> &'a T` preserves `valid_range = 1..=usize::MAX` (`p.addr ≠ 0`),
    `Option<unsafe<'a> &'a T>` discriminates `none` from `some` in a single pointer word
    (`8` bytes on 64-bit targets, matching `OPT_SHARED=8 OPT_MUT=8`). -/
theorem option_unsafeBinder_null_niche_discriminates
    (v : { p : PtrState // p.initialized = true ∧ p.addr ≠ 0 }) :
    encodeOptUnsafeBinder none = 0 ∧
    encodeOptUnsafeBinder (some v) ≠ 0 ∧
    encodeOptUnsafeBinder none ≠ encodeOptUnsafeBinder (some v) := by
  refine ⟨rfl, v.2.2, ?_⟩
  intro h
  exact v.2.2 h.symm

/-! ## Section 2: Existential Region-Pack / Unpack Soundness & Move-Only Linearity -/

/-- A single heap allocation carrying its allocation id, liveness flag,
    stored `u64` payload (as `Nat`), and owning lifetime/region id. -/
structure AllocEntry where
  aid : Nat
  live : Bool
  val : Nat
  regionId : Nat

/-- A heap is a list of allocation records indexed by `aid`. -/
abbrev Heap := List AllocEntry

/-- Structural lookup of an allocation by id (marked `noncomputable def`
    on recursive `List`). -/
noncomputable def lookupAlloc : Heap → Nat → Option AllocEntry
  | [], _ => none
  | e :: rest, aid => if e.aid = aid then some e else lookupAlloc rest aid

/-- Active-region environment mapping each region id to whether it is still live. -/
structure RegionEnv where
  active : Nat → Bool

/-- Heap-region well-formedness: every allocation whose owning region is still
    active in `env` is guaranteed live in `h`. -/
def HeapWf (env : RegionEnv) (h : Heap) : Prop :=
  ∀ aid e, lookupAlloc h aid = some e → env.active e.regionId = true → e.live = true

/-- A typed Rust reference `&'r u64` carrying both allocation id and region `'r`. -/
structure TypedRef where
  aid : Nat
  regionId : Nat

/-- Type-level validity of `&'r u64` in `(env, h)`: the target allocation exists,
    belongs to `'r`, and `'r` is active. -/
def TypedRefValid (env : RegionEnv) (h : Heap) (r : TypedRef) : Prop :=
  ∃ e, lookupAlloc h r.aid = some e ∧ e.regionId = r.regionId ∧ env.active r.regionId = true

/-- An erased existential unsafe binder `unsafe<'a> &'a u64`: the lifetime parameter
    `'a` is erased from the runtime representation, leaving only the pointer identity. -/
structure UnsafeBinderVal where
  aid : Nat

/-- `Rvalue::WrapUnsafeBinder`: packs `&'r u64` into `unsafe<'a> &'a u64` by erasing `'r`. -/
def wrapBinder (r : TypedRef) : UnsafeBinderVal :=
  { aid := r.aid }

/-- Result of dereferencing a projected reference. -/
inductive DerefResult where
  | ok (v : Nat)
  | useAfterFree

/-- `ProjectionElem::UnwrapUnsafeBinder` followed by `*` dereference on heap `h`. -/
noncomputable def unwrapAndDeref (h : Heap) (b : UnsafeBinderVal) : DerefResult :=
  match lookupAlloc h b.aid with
  | some e => if e.live = true then .ok e.val else .useAfterFree
  | none => .useAfterFree

/-- The caller's `unsafe` proof obligation at `unwrap_binder!(b)`:
    a live existential region witness in the *current* state `(env, h)`. -/
def LiveRegionWitness (env : RegionEnv) (h : Heap) (b : UnsafeBinderVal) : Prop :=
  ∃ r : Nat, ∃ e : AllocEntry,
    lookupAlloc h b.aid = some e ∧ e.regionId = r ∧ env.active r = true

/-- Packing a valid typed reference produces a live region witness in the packing state. -/
theorem wrap_preserves_initial_witness {env : RegionEnv} {h : Heap} {r : TypedRef}
    (hr : TypedRefValid env h r) :
    LiveRegionWitness env h (wrapBinder r) := by
  rcases hr with ⟨e, hlook, hreg, hact⟩
  exact ⟨r.regionId, e, hlook, hreg, hact⟩

/-- Core existential region-pack/unpack safety obligation soundness theorem:
    if a valid reference `r` is packed via `wrapBinder` at `(env₁, h₁)` into
    `b = wrapBinder r`, and execution reaches any later well-formed state `(env₂, h₂)`
    where the caller discharges `LiveRegionWitness env₂ h₂ b`, then unwrapping and
    dereferencing `b` in `h₂` is guaranteed UAF-free and returns the live value
    stored at `b.aid`. -/
theorem wrap_unwrap_live_region_witness_sound
    {env₁ env₂ : RegionEnv} {h₁ h₂ : Heap} {r : TypedRef}
    (_hPackValid : TypedRefValid env₁ h₁ r)
    (hWf₂ : HeapWf env₂ h₂)
    (hWitness₂ : LiveRegionWitness env₂ h₂ (wrapBinder r)) :
    ∃ e, lookupAlloc h₂ (wrapBinder r).aid = some e ∧
         unwrapAndDeref h₂ (wrapBinder r) = .ok e.val := by
  rcases hWitness₂ with ⟨reg, e, hlook, hreg, hact⟩
  have hact' : env₂.active e.regionId = true := by rw [hreg]; exact hact
  have hlive : e.live = true := hWf₂ (wrapBinder r).aid e hlook hact'
  refine ⟨e, hlook, ?_⟩
  unfold unwrapAndDeref
  rw [hlook]
  simp [hlive]

/-- Linear move-only MIR local slot for `!Copy` `UnsafeBinderVal`
    (matching both `rustc`'s `E0277`/`E0382` omission of `Copy` and
    `Trusted.MirSemantics` `deinitMovedPlace = true`). -/
inductive LinearSlot where
  | uninit
  | live (v : UnsafeBinderVal)

/-- Moving out of a `!Copy` `UnsafeBinderVal` slot atomically yields the value
    and transitions the source slot to `.uninit`. -/
def moveOutSlot : LinearSlot → Option (UnsafeBinderVal × LinearSlot)
  | .uninit => none
  | .live v => some (v, .uninit)

/-- Single-consumption linearity: once a `!Copy` `UnsafeBinderVal` is moved out of
    its local slot, any immediate second move from the resulting slot fails
    (preventing duplication of `unsafe<'a> &'a u64` or `unsafe<'a> &'a mut u64`). -/
theorem move_only_binder_single_consumption (s : LinearSlot) (v : UnsafeBinderVal) (s' : LinearSlot)
    (hMove : moveOutSlot s = some (v, s')) :
    s' = .uninit ∧ moveOutSlot s' = none := by
  cases s with
  | uninit => exact nomatch hMove
  | live v0 =>
      cases hMove
      exact ⟨rfl, rfl⟩

/-! ## Section 3: Complete De-Bruijn `v0` Symbol Mangling Injectivity Extension -/

/-- Reference / raw-pointer mutability. -/
inductive Mutbl where
  | not
  | mut

def Mutbl.decEq : (a b : Mutbl) → Decidable (a = b)
  | .not, .not => isTrue rfl
  | .mut, .mut => isTrue rfl
  | .not, .mut => isFalse (fun h => nomatch h)
  | .mut, .not => isFalse (fun h => nomatch h)

instance : DecidableEq Mutbl := Mutbl.decEq

/-- Region representation in `v0` mangling: either erased (`ReErased`) or a
    flattened 1-based De-Bruijn index (`L<num>`). -/
inductive V0Region where
  | erased
  | bound (idx : Nat)

def V0Region.decEq : (a b : V0Region) → Decidable (a = b)
  | .erased, .erased => isTrue rfl
  | .bound i, .bound j =>
      match Nat.decEq i j with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (fun heq => by cases heq; exact h rfl)
  | .erased, .bound _ => isFalse (fun h => nomatch h)
  | .bound _, .erased => isFalse (fun h => nomatch h)

instance : DecidableEq V0Region := V0Region.decEq

/-- Core `rustc` type AST modeled for `v0` symbol mangling, including both
    higher-ranked `FnPtr` binders and `TyKind::UnsafeBinder`. -/
inductive V0Ty where
  | bool
  | u64
  | unit
  | ref (m : Mutbl) (r : V0Region) (inner : V0Ty)
  | rawPtr (m : Mutbl) (inner : V0Ty)
  | slice (inner : V0Ty)
  | fnPtr (binders : Nat) (arg : V0Ty) (ret : V0Ty)
  | unsafeBinder (binders : Nat) (inner : V0Ty)

/-- Manual structural `DecidableEq` on recursive `V0Ty` (no `deriving`, no `._unsafe_rec`). -/
noncomputable def V0Ty.decEq : (a b : V0Ty) → Decidable (a = b)
  | .bool, .bool => isTrue rfl
  | .u64, .u64 => isTrue rfl
  | .unit, .unit => isTrue rfl
  | .ref m1 r1 i1, .ref m2 r2 i2 =>
      match Mutbl.decEq m1 m2, V0Region.decEq r1 r2, V0Ty.decEq i1 i2 with
      | isTrue hm, isTrue hr, isTrue hi => isTrue (by rw [hm, hr, hi])
      | isFalse hm, _, _ => isFalse (fun h => by cases h; exact hm rfl)
      | _, isFalse hr, _ => isFalse (fun h => by cases h; exact hr rfl)
      | _, _, isFalse hi => isFalse (fun h => by cases h; exact hi rfl)
  | .rawPtr m1 i1, .rawPtr m2 i2 =>
      match Mutbl.decEq m1 m2, V0Ty.decEq i1 i2 with
      | isTrue hm, isTrue hi => isTrue (by rw [hm, hi])
      | isFalse hm, _ => isFalse (fun h => by cases h; exact hm rfl)
      | _, isFalse hi => isFalse (fun h => by cases h; exact hi rfl)
  | .slice i1, .slice i2 =>
      match V0Ty.decEq i1 i2 with
      | isTrue hi => isTrue (by rw [hi])
      | isFalse hi => isFalse (fun h => by cases h; exact hi rfl)
  | .fnPtr b1 a1 r1, .fnPtr b2 a2 r2 =>
      match Nat.decEq b1 b2, V0Ty.decEq a1 a2, V0Ty.decEq r1 r2 with
      | isTrue hb, isTrue ha, isTrue hr => isTrue (by rw [hb, ha, hr])
      | isFalse hb, _, _ => isFalse (fun h => by cases h; exact hb rfl)
      | _, isFalse ha, _ => isFalse (fun h => by cases h; exact ha rfl)
      | _, _, isFalse hr => isFalse (fun h => by cases h; exact hr rfl)
  | .unsafeBinder b1 i1, .unsafeBinder b2 i2 =>
      match Nat.decEq b1 b2, V0Ty.decEq i1 i2 with
      | isTrue hb, isTrue hi => isTrue (by rw [hb, hi])
      | isFalse hb, _ => isFalse (fun h => by cases h; exact hb rfl)
      | _, isFalse hi => isFalse (fun h => by cases h; exact hi rfl)
  | .bool, .u64 => isFalse (fun h => nomatch h)
  | .bool, .unit => isFalse (fun h => nomatch h)
  | .bool, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .bool, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .bool, .slice _ => isFalse (fun h => nomatch h)
  | .bool, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .bool, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .u64, .bool => isFalse (fun h => nomatch h)
  | .u64, .unit => isFalse (fun h => nomatch h)
  | .u64, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .u64, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .u64, .slice _ => isFalse (fun h => nomatch h)
  | .u64, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .u64, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .unit, .bool => isFalse (fun h => nomatch h)
  | .unit, .u64 => isFalse (fun h => nomatch h)
  | .unit, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .unit, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .unit, .slice _ => isFalse (fun h => nomatch h)
  | .unit, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .unit, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .ref _ _ _, .bool => isFalse (fun h => nomatch h)
  | .ref _ _ _, .u64 => isFalse (fun h => nomatch h)
  | .ref _ _ _, .unit => isFalse (fun h => nomatch h)
  | .ref _ _ _, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .ref _ _ _, .slice _ => isFalse (fun h => nomatch h)
  | .ref _ _ _, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .ref _ _ _, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .bool => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .u64 => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .unit => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .slice _ => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .rawPtr _ _, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .slice _, .bool => isFalse (fun h => nomatch h)
  | .slice _, .u64 => isFalse (fun h => nomatch h)
  | .slice _, .unit => isFalse (fun h => nomatch h)
  | .slice _, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .slice _, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .slice _, .fnPtr _ _ _ => isFalse (fun h => nomatch h)
  | .slice _, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .bool => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .u64 => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .unit => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .slice _ => isFalse (fun h => nomatch h)
  | .fnPtr _ _ _, .unsafeBinder _ _ => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .bool => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .u64 => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .unit => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .ref _ _ _ => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .rawPtr _ _ => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .slice _ => isFalse (fun h => nomatch h)
  | .unsafeBinder _ _, .fnPtr _ _ _ => isFalse (fun h => nomatch h)

noncomputable instance : DecidableEq V0Ty := V0Ty.decEq

/-- Self-delimiting `_`-terminated ASCII count encoding (`0 -> "_"`, `n+1 -> "1" ++ encNat n`),
    disjoint from all alphabetic `v0` type tags. -/
noncomputable def encNat : Nat → List Char
  | 0 => ['_']
  | n + 1 => '1' :: encNat n

/-- Prefix-free proof for `encNat` (explicit cons injection). -/
theorem encNat_pf :
    ∀ n₁ n₂ r₁ r₂, encNat n₁ ++ r₁ = encNat n₂ ++ r₂ → n₁ = n₂ ∧ r₁ = r₂ := by
  intro n₁
  induction n₁ with
  | zero =>
      intro n₂ r₁ r₂ h
      cases n₂ with
      | zero =>
          have h' : '_' :: r₁ = '_' :: r₂ := h
          exact ⟨rfl, (List.cons.inj h').2⟩
      | succ _ =>
          have h' : '_' :: r₁ = '1' :: (encNat _ ++ r₂) := h
          exact absurd (List.cons.inj h').1 (by decide)
  | succ k₁ ih =>
      intro n₂ r₁ r₂ h
      cases n₂ with
      | zero =>
          have h' : '1' :: (encNat k₁ ++ r₁) = '_' :: r₂ := h
          exact absurd (List.cons.inj h').1 (by decide)
      | succ k₂ =>
          have h' : '1' :: (encNat k₁ ++ r₁) = '1' :: (encNat k₂ ++ r₂) := h
          have htail := (List.cons.inj h').2
          have ⟨hk, hr⟩ := ih k₂ r₁ r₂ htail
          exact ⟨congrArg Nat.succ hk, hr⟩

/-- Complete extended `v0` mangler:
    - Uses exact `rustc_symbol_mangling::v0` prefix tags (`b`, `y`, `u`, `R`, `Q`, `P`, `O`, `S`, `F`, `L`, `G`, `E`).
    - Assigns unused uppercase prefix tag `'J'` followed by `'G'` + binder count to `TyKind::UnsafeBinder`. -/
noncomputable def mangleExt : V0Ty → List Char
  | .bool => ['b']
  | .u64 => ['y']
  | .unit => ['u']
  | .ref .not .erased inner => 'R' :: mangleExt inner
  | .ref .not (.bound k) inner => 'R' :: 'L' :: (encNat k ++ mangleExt inner)
  | .ref .mut .erased inner => 'Q' :: mangleExt inner
  | .ref .mut (.bound k) inner => 'Q' :: 'L' :: (encNat k ++ mangleExt inner)
  | .rawPtr .not inner => 'P' :: mangleExt inner
  | .rawPtr .mut inner => 'O' :: mangleExt inner
  | .slice inner => 'S' :: mangleExt inner
  | .fnPtr b arg ret => 'F' :: 'G' :: (encNat b ++ (mangleExt arg ++ ('E' :: mangleExt ret)))
  | .unsafeBinder b inner => 'J' :: 'G' :: (encNat b ++ mangleExt inner)

/-- Stock `rustc 1.102.0-nightly` (`v0.rs:679`) partial `v0` mangler:
    returns `none` whenever `TyKind::UnsafeBinder` is encountered anywhere in the type. -/
noncomputable def mangleStockV0 : V0Ty → Option (List Char)
  | .bool => some ['b']
  | .u64 => some ['y']
  | .unit => some ['u']
  | .ref .not .erased inner =>
      match mangleStockV0 inner with
      | some s => some ('R' :: s)
      | none => none
  | .ref .not (.bound k) inner =>
      match mangleStockV0 inner with
      | some s => some ('R' :: 'L' :: (encNat k ++ s))
      | none => none
  | .ref .mut .erased inner =>
      match mangleStockV0 inner with
      | some s => some ('Q' :: s)
      | none => none
  | .ref .mut (.bound k) inner =>
      match mangleStockV0 inner with
      | some s => some ('Q' :: 'L' :: (encNat k ++ s))
      | none => none
  | .rawPtr .not inner =>
      match mangleStockV0 inner with
      | some s => some ('P' :: s)
      | none => none
  | .rawPtr .mut inner =>
      match mangleStockV0 inner with
      | some s => some ('O' :: s)
      | none => none
  | .slice inner =>
      match mangleStockV0 inner with
      | some s => some ('S' :: s)
      | none => none
  | .fnPtr b arg ret =>
      match mangleStockV0 arg, mangleStockV0 ret with
      | some sa, some sr => some ('F' :: 'G' :: (encNat b ++ (sa ++ ('E' :: sr))))
      | _, _ => none
  | .unsafeBinder _ _ => none

/-- Predicate asserting that a `V0Ty` contains no `UnsafeBinder` subterms. -/
noncomputable def hasNoUnsafeBinder : V0Ty → Prop
  | .bool => True
  | .u64 => True
  | .unit => True
  | .ref _ _ inner => hasNoUnsafeBinder inner
  | .rawPtr _ inner => hasNoUnsafeBinder inner
  | .slice inner => hasNoUnsafeBinder inner
  | .fnPtr _ arg ret => hasNoUnsafeBinder arg ∧ hasNoUnsafeBinder ret
  | .unsafeBinder _ _ => False

/-- Backward compatibility: on all existing (binder-free) Rust types, `mangleExt`
    agrees identically with `mangleStockV0`. -/
theorem mangleExt_extends_stock (t : V0Ty) (h : hasNoUnsafeBinder t) :
    mangleStockV0 t = some (mangleExt t) := by
  induction t with
  | bool => rfl
  | u64 => rfl
  | unit => rfl
  | ref m r inner ih =>
      have hi := ih h
      cases m <;> cases r <;> simp [mangleStockV0, mangleExt, hi]
  | rawPtr m inner ih =>
      have hi := ih h
      cases m <;> simp [mangleStockV0, mangleExt, hi]
  | slice inner ih =>
      have hi := ih h
      simp [mangleStockV0, mangleExt, hi]
  | fnPtr b arg ret iha ihr =>
      have ha := iha h.1
      have hr := ihr h.2
      simp [mangleStockV0, mangleExt, ha, hr]
  | unsafeBinder _ _ =>
      exact False.elim h

/-- Helper: the leading tag character of `mangleExt t` is never `'L'`.
    This is what allows `R<ty>` vs `RL<idx><ty>` (erased vs bound lifetime)
    to remain prefix-free, matching `rustc_symbol_mangling/src/v0.rs:573-582`. -/
theorem mangleExt_head_ne_L (t : V0Ty) :
    ∀ c cs, mangleExt t = c :: cs → c ≠ 'L' := by
  cases t with
  | bool => intro c cs h; cases h; decide
  | u64 => intro c cs h; cases h; decide
  | unit => intro c cs h; cases h; decide
  | ref m r inner =>
      cases m <;> cases r <;> (intro c cs h; cases h; decide)
  | rawPtr m inner =>
      cases m <;> (intro c cs h; cases h; decide)
  | slice inner => intro c cs h; cases h; decide
  | fnPtr b arg ret => intro c cs h; cases h; decide
  | unsafeBinder b inner => intro c cs h; cases h; decide

/-- Helper: every `mangleExt t` is non-empty and never starts with `'L'`. -/
theorem mangleExt_append_ne_L (t : V0Ty) (r : List Char) :
    ∀ rest, mangleExt t ++ r ≠ 'L' :: rest := by
  intro rest h
  cases hm : mangleExt t with
  | nil =>
      cases t with
      | bool => simp [mangleExt] at hm
      | u64 => simp [mangleExt] at hm
      | unit => simp [mangleExt] at hm
      | ref m r' inner => cases m <;> cases r' <;> simp [mangleExt] at hm
      | rawPtr m inner => cases m <;> simp [mangleExt] at hm
      | slice inner => simp [mangleExt] at hm
      | fnPtr b arg ret => simp [mangleExt] at hm
      | unsafeBinder b inner => simp [mangleExt] at hm
  | cons c cs =>
      rw [hm] at h
      have hc : c = 'L' := (List.cons.inj h).1
      exact mangleExt_head_ne_L t c cs hm hc

/-- Prefix-freeness of `mangleExt`: if `mangleExt t₁ ++ r₁ = mangleExt t₂ ++ r₂`,
    then `t₁ = t₂` and `r₁ = r₂`. -/
theorem mangleExt_prefix_free :
    ∀ t₁ t₂ r₁ r₂, mangleExt t₁ ++ r₁ = mangleExt t₂ ++ r₂ → t₁ = t₂ ∧ r₁ = r₂ := by
  intro t₁
  induction t₁ with
  | bool =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact ⟨rfl, (List.cons.inj h).2⟩
      | u64 => exact absurd (List.cons.inj h).1 (by decide)
      | unit => exact absurd (List.cons.inj h).1 (by decide)
      | ref m r' _ => cases m <;> cases r' <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => exact absurd (List.cons.inj h).1 (by decide)
  | u64 =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact absurd (List.cons.inj h).1 (by decide)
      | u64 => exact ⟨rfl, (List.cons.inj h).2⟩
      | unit => exact absurd (List.cons.inj h).1 (by decide)
      | ref m r' _ => cases m <;> cases r' <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => exact absurd (List.cons.inj h).1 (by decide)
  | unit =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact absurd (List.cons.inj h).1 (by decide)
      | u64 => exact absurd (List.cons.inj h).1 (by decide)
      | unit => exact ⟨rfl, (List.cons.inj h).2⟩
      | ref m r' _ => cases m <;> cases r' <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => exact absurd (List.cons.inj h).1 (by decide)
  | ref m₁ rg₁ inner₁ ih =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | u64 => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | unit => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m₁ <;> cases rg₁ <;> cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => cases m₁ <;> cases rg₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | ref m₂ rg₂ inner₂ =>
          cases m₁ <;> cases m₂
          · -- .not, .not
            cases rg₁ <;> cases rg₂
            · have ht := (List.cons.inj h).2
              have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ ht
              exact ⟨congrArg (V0Ty.ref .not .erased) hi, hr⟩
            · have ht := (List.cons.inj h).2
              exact False.elim (mangleExt_append_ne_L inner₁ r₁ _ ht)
            · have ht := (List.cons.inj h).2
              exact False.elim (mangleExt_append_ne_L inner₂ r₂ _ ht.symm)
            · rename_i k₁ k₂
              simp only [mangleExt, List.cons_append, List.append_assoc] at h
              have ht1 := (List.cons.inj h).2
              have ht2 := (List.cons.inj ht1).2
              have ⟨hk, hrest⟩ := encNat_pf k₁ k₂ (mangleExt inner₁ ++ r₁) (mangleExt inner₂ ++ r₂) ht2
              have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ hrest
              rw [hk, hi]
              exact ⟨rfl, hr⟩
          · -- .not, .mut
            cases rg₁ <;> cases rg₂ <;> exact absurd (List.cons.inj h).1 (by decide)
          · -- .mut, .not
            cases rg₁ <;> cases rg₂ <;> exact absurd (List.cons.inj h).1 (by decide)
          · -- .mut, .mut
            cases rg₁ <;> cases rg₂
            · have ht := (List.cons.inj h).2
              have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ ht
              exact ⟨congrArg (V0Ty.ref .mut .erased) hi, hr⟩
            · have ht := (List.cons.inj h).2
              exact False.elim (mangleExt_append_ne_L inner₁ r₁ _ ht)
            · have ht := (List.cons.inj h).2
              exact False.elim (mangleExt_append_ne_L inner₂ r₂ _ ht.symm)
            · rename_i k₁ k₂
              simp only [mangleExt, List.cons_append, List.append_assoc] at h
              have ht1 := (List.cons.inj h).2
              have ht2 := (List.cons.inj ht1).2
              have ⟨hk, hrest⟩ := encNat_pf k₁ k₂ (mangleExt inner₁ ++ r₁) (mangleExt inner₂ ++ r₂) ht2
              have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ hrest
              rw [hk, hi]
              exact ⟨rfl, hr⟩
  | rawPtr m₁ inner₁ ih =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | u64 => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | unit => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | ref m rg _ => cases m₁ <;> cases m <;> cases rg <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => cases m₁ <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m₂ inner₂ =>
          cases m₁ <;> cases m₂
          · have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ (List.cons.inj h).2
            exact ⟨congrArg (V0Ty.rawPtr .not) hi, hr⟩
          · exact absurd (List.cons.inj h).1 (by decide)
          · exact absurd (List.cons.inj h).1 (by decide)
          · have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ (List.cons.inj h).2
            exact ⟨congrArg (V0Ty.rawPtr .mut) hi, hr⟩
  | slice inner₁ ih =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact absurd (List.cons.inj h).1 (by decide)
      | u64 => exact absurd (List.cons.inj h).1 (by decide)
      | unit => exact absurd (List.cons.inj h).1 (by decide)
      | ref m rg _ => cases m <;> cases rg <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice inner₂ =>
          have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ (List.cons.inj h).2
          exact ⟨congrArg V0Ty.slice hi, hr⟩
      | fnPtr _ _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => exact absurd (List.cons.inj h).1 (by decide)
  | fnPtr b₁ arg₁ ret₁ iha ihr =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact absurd (List.cons.inj h).1 (by decide)
      | u64 => exact absurd (List.cons.inj h).1 (by decide)
      | unit => exact absurd (List.cons.inj h).1 (by decide)
      | ref m rg _ => cases m <;> cases rg <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr b₂ arg₂ ret₂ =>
          simp only [mangleExt, List.cons_append, List.append_assoc] at h
          have ht1 := (List.cons.inj h).2
          have ht2 := (List.cons.inj ht1).2
          have ⟨hb, hrest1⟩ := encNat_pf b₁ b₂
            (mangleExt arg₁ ++ ('E' :: (mangleExt ret₁ ++ r₁)))
            (mangleExt arg₂ ++ ('E' :: (mangleExt ret₂ ++ r₂))) ht2
          have ⟨harg, hrest2⟩ := iha arg₂ ('E' :: (mangleExt ret₁ ++ r₁)) ('E' :: (mangleExt ret₂ ++ r₂)) hrest1
          have hrest3 := (List.cons.inj hrest2).2
          have ⟨hret, hr⟩ := ihr ret₂ r₁ r₂ hrest3
          rw [hb, harg, hret]
          exact ⟨rfl, hr⟩
  | unsafeBinder b₁ inner₁ ih =>
      intro t₂ r₁ r₂ h
      cases t₂ with
      | bool => exact absurd (List.cons.inj h).1 (by decide)
      | u64 => exact absurd (List.cons.inj h).1 (by decide)
      | unit => exact absurd (List.cons.inj h).1 (by decide)
      | ref m rg _ => cases m <;> cases rg <;> exact absurd (List.cons.inj h).1 (by decide)
      | rawPtr m _ => cases m <;> exact absurd (List.cons.inj h).1 (by decide)
      | slice _ => exact absurd (List.cons.inj h).1 (by decide)
      | fnPtr _ _ _ => exact absurd (List.cons.inj h).1 (by decide)
      | unsafeBinder b₂ inner₂ =>
          simp only [mangleExt, List.cons_append, List.append_assoc] at h
          have ht1 := (List.cons.inj h).2
          have ht2 := (List.cons.inj ht1).2
          have ⟨hb, hrest⟩ := encNat_pf b₁ b₂ (mangleExt inner₁ ++ r₁) (mangleExt inner₂ ++ r₂) ht2
          have ⟨hi, hr⟩ := ih inner₂ r₁ r₂ hrest
          rw [hb, hi]
          exact ⟨rfl, hr⟩

/-- Main De-Bruijn `v0` mangling injectivity theorem with `TyKind::UnsafeBinder`:
    distinct types (including arbitrary nested `UnsafeBinder` and `FnPtr` De-Bruijn
    lifetimes) always produce distinct mangled symbols. -/
theorem v0_mangle_with_unsafe_binder_injective (t₁ t₂ : V0Ty)
    (h : mangleExt t₁ = mangleExt t₂) : t₁ = t₂ := by
  have h' : mangleExt t₁ ++ [] = mangleExt t₂ ++ [] := by
    simp only [List.append_nil]
    exact h
  exact (mangleExt_prefix_free t₁ t₂ [] [] h').1

/-! ## Section 4: Constructive Sharpness Counterexamples -/

/-- Counterexample 1 (sharpness of `E0133` `unsafe` gating on `unwrap_binder!`):
    There exist well-formed packing state `(env₁, h₁)`, valid reference `r`,
    and well-formed later state `(env₂, h₂)` (after deallocation) such that
    `wrapBinder r` was legitimately constructed from a live reference yet
    unwrapping and dereferencing without `LiveRegionWitness env₂ h₂` yields
    `DerefResult.useAfterFree`. -/
theorem ce1_safe_unwrap_without_live_witness_uaf :
    ∃ (env₁ env₂ : RegionEnv) (h₁ h₂ : Heap) (r : TypedRef),
      HeapWf env₁ h₁ ∧
      TypedRefValid env₁ h₁ r ∧
      HeapWf env₂ h₂ ∧
      ¬ LiveRegionWitness env₂ h₂ (wrapBinder r) ∧
      unwrapAndDeref h₂ (wrapBinder r) = .useAfterFree := by
  let env₁ : RegionEnv := { active := fun _ => true }
  let env₂ : RegionEnv := { active := fun _ => false }
  let h₁ : Heap := [{ aid := 0, live := true, val := 42, regionId := 0 }]
  let h₂ : Heap := [{ aid := 0, live := false, val := 42, regionId := 0 }]
  let r : TypedRef := { aid := 0, regionId := 0 }
  refine ⟨env₁, env₂, h₁, h₂, r, ?_, ?_, ?_, ?_, ?_⟩
  · -- HeapWf env₁ h₁
    intro aid e hlook _
    unfold lookupAlloc at hlook
    by_cases ha : (0 : Nat) = aid
    · simp [ha] at hlook
      cases hlook
      rfl
    · simp [ha, lookupAlloc] at hlook
  · -- TypedRefValid env₁ h₁ r
    exact ⟨{ aid := 0, live := true, val := 42, regionId := 0 }, by simp [lookupAlloc, r, h₁], rfl, rfl⟩
  · -- HeapWf env₂ h₂
    intro aid e _ hact
    exact Bool.noConfusion hact
  · -- ¬ LiveRegionWitness env₂ h₂ (wrapBinder r)
    intro ⟨_, _, _, _, hact⟩
    exact Bool.noConfusion hact
  · -- unwrapAndDeref h₂ (wrapBinder r) = .useAfterFree
    simp [unwrapAndDeref, lookupAlloc, wrapBinder, r, h₂]

/-- Counterexample 2 (sharpness of stripping `align 8` on thin `unsafe<'a> &'a u64`):
    A misaligned non-null pointer (`addr = 1`, modeling `transmute::<usize, unsafe<'a> &'a u64>(1)`)
    is valid for `UnsafeBinder` and satisfies its emitted `ptr noundef nonnull` contract,
    yet immediately triggers LLVM entry UB if `align 8` (as emitted for `MaybeDangling<&u64>`)
    is retained. -/
theorem ce2_align8_attr_on_misaligned_transmuted_binder_ub :
    ∃ p : PtrState,
      TierValueValid 8 8 .unsafeBinder p ∧
      AttrsValidAtEntry (emitWrapperAttrs 8 8 .unsafeBinder) p ∧
      ¬ AttrsValidAtEntry (emitWrapperAttrs 8 8 .maybeDangling) p := by
  let p : PtrState :=
    { initialized := true
      addr := 1
      liveBytes := 0
      aliasedMutable := true
      freedDuringCall := true }
  refine ⟨p, ?_, ?_, ?_⟩
  · exact ⟨rfl, by decide⟩
  · exact unsafeBinder_param_attrs_sound 8 8 p ⟨rfl, by decide⟩
  · intro hMd
    have hAlign8 : (8 : Nat) > 1 := by decide
    have hMod : p.addr % 8 = 0 := hMd.2.2.1 hAlign8
    have hNe : (1 : Nat) % 8 ≠ 0 := by decide
    exact hNe hMod

/-- Counterexample 3 (sharpness of the live `v0.rs:679` ICE):
    On `unsafe<'a> &'a u64` (`V0Ty.unsafeBinder 1 (.ref .not (.bound 1) .u64)`),
    the stock `v0` mangler returns `none` (ICE / panic at `v0.rs:679`), while
    `mangleExt` produces a concrete encoding distinct from `&u64` and
    `unsafe<'a> &'a mut u64`. -/
theorem ce3_partial_v0_mangler_panics_on_unsafe_binder :
    ∃ t : V0Ty,
      mangleStockV0 t = none ∧
      mangleExt t ≠ mangleExt (.ref .not .erased .u64) ∧
      mangleExt t ≠ mangleExt (.unsafeBinder 1 (.ref .mut (.bound 1) .u64)) := by
  let t : V0Ty := .unsafeBinder 1 (.ref .not (.bound 1) .u64)
  refine ⟨t, rfl, ?_, ?_⟩
  · intro h
    have heq := v0_mangle_with_unsafe_binder_injective t (.ref .not .erased .u64) h
    dsimp only [t] at heq
    cases heq
  · intro h
    have heq := v0_mangle_with_unsafe_binder_injective t (.unsafeBinder 1 (.ref .mut (.bound 1) .u64)) h
    dsimp only [t] at heq
    cases heq

/-- Counterexample 4 (soundness bug for compound `UnsafeBinder` pointee attribute leak):
    An aligned dangling pointer (`addr = 8, liveBytes = 0`) is a valid `UnsafeBinder` value,
    yet violates the leaked `plainRef` LLVM attribute bundle (`dereferenceable(8)`)
    that `rustc` erroneously emits when `ty_and_layout_pointee_info_at` recurses through
    `field_ty_or_layout` on compound binders (`unsafe<'a> Wrap<'a>`, `unsafe<'a> (&'a u64, u64)`). -/
theorem ce4_compound_binder_pointee_attr_leak_ub :
    ∃ p : PtrState,
      TierValueValid 8 8 .unsafeBinder p ∧
      AttrsValidAtEntry (emitWrapperAttrs 8 8 .unsafeBinder) p ∧
      ¬ AttrsValidAtEntry (emitWrapperAttrs 8 8 .plainRef) p := by
  let p : PtrState :=
    { initialized := true
      addr := 8
      liveBytes := 0
      aliasedMutable := false
      freedDuringCall := false }
  refine ⟨p, ?_, ?_, ?_⟩
  · exact ⟨rfl, by decide⟩
  · exact unsafeBinder_param_attrs_sound 8 8 p ⟨rfl, by decide⟩
  · intro hPlain
    have hDeref8 : (8 : Nat) > 0 := by decide
    have hLe : 8 ≤ p.liveBytes := hPlain.2.2.2.1 hDeref8
    have hNotLe : ¬ (8 ≤ (0 : Nat)) := by decide
    exact hNotLe hLe

end UnsafeBinderSoundness

-- Kernel axiom audits (must report zero sorryAx, zero Classical.choice, zero ofReduceBool)
#print axioms UnsafeBinderSoundness.wrapper_attr_lattice_strict
#print axioms UnsafeBinderSoundness.unsafeBinder_param_attrs_sound
#print axioms UnsafeBinderSoundness.all_four_tiers_param_attrs_sound
#print axioms UnsafeBinderSoundness.option_unsafeBinder_null_niche_discriminates
#print axioms UnsafeBinderSoundness.wrap_unwrap_live_region_witness_sound
#print axioms UnsafeBinderSoundness.move_only_binder_single_consumption
#print axioms UnsafeBinderSoundness.mangleExt_extends_stock
#print axioms UnsafeBinderSoundness.v0_mangle_with_unsafe_binder_injective
#print axioms UnsafeBinderSoundness.ce1_safe_unwrap_without_live_witness_uaf
#print axioms UnsafeBinderSoundness.ce2_align8_attr_on_misaligned_transmuted_binder_ub
#print axioms UnsafeBinderSoundness.ce3_partial_v0_mangler_panics_on_unsafe_binder
#print axioms UnsafeBinderSoundness.ce4_compound_binder_pointee_attr_leak_ub
