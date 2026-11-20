# MiniRust Galois Byte Layouts, Stateful Lifetime Continuations, and Unsafe Raw-Pointer Interop

## Summary

Bridging pure functional Rust borrow-erasure and unsafe byte-level raw-pointer verification requires solving four orthogonal problems: padding-aware byte serialization, layout opaqueness, lifetime-preserving backward continuations across safe-to-raw conversions, and ergonomic separation-logic contract surfaces. Examining `minirust/minirust@063d7841`, `AeneasVerif/aeneas` PRs `#1447` (`2a1dd755`), `#1537` (`5c28fe8d`), and `#1497` (`d17ca83f`), `google/zerocopy@1962a9c0`, `joshlf/anneal@20aa2043`, Fulminate/CN (`10.1145/3704879`, `10.1145/3571194`), and `rust-lang/compiler-team#942` establishes four reusable invariants:

1. **MiniRust's 4-law Galois connection over `AbstractByte` models padding and `zerocopy` traits cleanly:** Decoupling high-level values (`MVal`), machine layouts (`Layout : MType → Type 0`), and `AbstractByte := uninit | init Byte` (`Aeneas#1447`) proves `DecodeValid`, `DecodeMono`, `DecodeEncode`, and `EncodeDecodeLeDefined` (`encode l v hv ≤_def bs` when `decode l bs = some v`) for every valid struct, enum, packed, or aligned layout. Under these laws, `zerocopy`'s `IntoBytes` strengthens `EncodeDecodeLeDefined` from `≤_def` to exact byte equality (`encode` emits zero `.uninit` bytes), whereas `SpatialPin`'s `hasUninitCell` check in `joshlf/anneal@20aa2043` (`SpatialPin.lean:220, 276`) rejects valid padded structs until upgraded to a Galois `LayoutCodec`. When pointer provenance lanes are present (`Byte.pointer` in `#1497`), scalar `encode` must remain strictly narrower than `decode⁻¹` to block integer-to-pointer provenance forgery.
2. **Layout opaqueness distinguishes `Classical.choice` blocking from universal layout quantification:** Wrapping a constructive `example_layout` witness in `Classical.choice` (`HasLayout.the_layout`, `#1447` `HasLayout.lean:48`) blocks Lean definitional unfolding for `#[repr(Rust)]` structs, while `#[repr(C)]` permits exact offset reduction via `IsReprCTuple`. Universal quantification (`∀ l : Layout ty, l.Valid → ...`) eliminates `Classical.choice` entirely inside `Init.*`-only Lean while additionally preventing cross-monomorphization layout peeking.
3. **Effectful backward continuations, 3-tier lifetime scheduling, and `ClosedViews` close the safe↔raw gap:** Pure functional borrow-erasure collapses zero-output borrows too early and omits writeback thunks on raw re-materialization. PR `#1537` introduces monadic `Result` backward continuations (`is_effectful`), NLL-approximating backward local-liveness retirement for `short` borrows (`as_mut`/`as_shr`), two-pass join deferral for `long` borrows (`from_mut`/`from_shr`), and CSE suppression (`simplify_duplicate_calls_visitor` skips `is_result_ty`). Composing nested raw scopes further requires separating view activity (`active`) from allocation liveness (`alive`) and proving transitive `ClosedViews` preservation of `RootReturn` (`#1497` `ScopedView.lean`).
4. **Effectful `owned<T>(p)` / `alloc_block` contracts desugar into first-order `IProp` triples:** Following Fulminate (`10.1145/3704879`) and `rust-lang/compiler-team#942`, imperative contract statements (`let v = owned(p)`) sequence points-to consumption and restoration while using `owned::<MaybeUninit<T>>` for write-only targets and `ManuallyDrop<T>` to suppress runtime destructors.

*(Scope boundary: `zerocopy` FFI/intrinsic inventories and `Ptr` alignment/aliasing lattices appear in `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`; baseline LLBC symbolic borrow-checking appears in `aeneas-borrows-symbolic-ownership-and-resource-semantics`; two-zone borrow/heap adapters appear in `hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4`; forward-compatible `rustc` capture isolation appears in `anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement`; and meta-free `IProp` / `SepAC` kernels appear in `meta-free-reflective-separation-logic-framing-view-pcms-and-step-index-free-adequacy`.)*

---

## Applicability

These findings apply to the pinned repositories, PR branches, and papers below:

| Subject / System | Pinned Identity / Citation | Examined Scope |
|---|---|---|
| **`minirust/minirust`** | `063d784186d3252bee242217f218223205c0b568` | `spec/lang/representation.md`: `AbstractByte`, `le_defined`, `encode`/`decode`, 4 Galois laws, `transmute` |
| **Aeneas PR `#1447`** | `JoJoDeveloping/aeneas` `layouts` @ `2a1dd75567517e078f90b1df746af7373fe24cbc` (base `673f9e30e1e2a81b355df9a9550168e672a10d4e`) | `backends/lean/Aeneas/Data/Layout/{Bytes,MTypes,Defs,EncodeDecode,ReprC,Properties,Valid,GaloisConnection,Reasonable,RichMTypes,HasLayout}.lean` |
| **Aeneas PR `#1537`** | `JoJoDeveloping/aeneas` `alive-hint` @ `5c28fe8def8db99041d22503175591ba1fa47915` (base `0d21a9ec7bbbb110110cacc14464a47fd71c8705`) | `InterpLiveness.ml`, `InterpStatements.ml`, `SymbolicToPure*.ml`, `PureMicroPassesGeneral.ml`, `tests/{src,lean}/stateful-lifetime*` |
| **Aeneas PR `#1497`** | `AeneasVerif/aeneas` `fournet/wip-memory-model` @ `d17ca83fc07d712d1785f650840cb2073c259e69` (base `de16f3cf877976e966906dc890f63dcb418884fa`) | `Heap/{Repr,Model,ExclusiveReturn,ScopedView}.lean`, `Heap/{README,TRANSMUTE}.md`, PR review comments on `Repr.lean`/`Model.lean` |
| **`google/zerocopy`** | `1962a9c0e3eda8a3a58387f61c70ddd2c396b118` | `zerocopy/src/lib.rs`: `KnownLayout`, `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes` |
| **`joshlf/anneal`** | `20aa204315cd36aaf944778b7d33c0d609ced8e8` | `theory/Anneal/PureLift/{LoanGraph,SpatialPin}.lean`, `trusted/audit/TrustedBoundary.lean` |
| **Lean `v4.34.1`** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | Kernel checking constraints (`Init.*`-only, no `Vector.ofFn` WHNF cast pollution) |
| **CN / Fulminate / Contracts** | `rems-project/cerberus` @ `e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`; DOIs `10.1145/3704879`, `10.1145/3571194`; `rust-lang/compiler-team#942` | Surface `owned<T>` / `alloc_block` primitives, Miri runtime checks, and first-order `IProp` desugaring |

---

## Findings

### 1. Three-Level Serialization and the Four-Law MiniRust Galois Connection

**Basis: normative (`minirust@063d7841` `spec/lang/representation.md`) + source (`JoJoDeveloping/aeneas@2a1dd755` `Data/Layout/*`, `AeneasVerif/aeneas@d17ca83f` `Heap/Repr.lean`, `joshlf/anneal@20aa2043` `SpatialPin.lean`) + derived.**

#### 1.1 MiniRust's Byte/Value Definedness Order and Galois Adjoint

In `minirust/minirust@063d7841` (`spec/lang/representation.md:32–142, 623–778`), typed loads and stores mediate between `List<AbstractByte<Provenance>>` and `Value<M>`. MiniRust orders bytes and values by **definedness** (`le_defined`, `representation.md:641–747`):

- On `AbstractByte`: `Uninit ≤_def _`, `Init(b₁, None) ≤_def Init(b₂, _) ↔ b₁ = b₂`, and `Init(b₁, Some p₁) ≤_def Init(b₂, Some p₂) ↔ b₁ = b₂ ∧ p₁ = p₂` (`lines 652–669`). Initializing an uninitialized byte or adding provenance makes memory strictly more defined.
- On `Option<Value>`: `None ≤_def _`, and `Some v₁ ≤_def Some v₂ ↔ v₁ ≤_def v₂` (`lines 738–746`).

MiniRust requires four generic consistency laws linking `encode`, `decode`, and `check_value` (`representation.md:753–766`):
1. **`EncodeMono` / `DecodeMono`:** Increasing definedness of values preserves `encode` order; increasing definedness of bytes preserves `decode` order (`bs₁ ≤_def bs₂ → decode(bs₁) ≤_def decode(bs₂)`).
2. **`DecodeEncode`:** For well-formed values `v`, `decode(encode(v)) = Some(v)` (lossless round-trip).
3. **`EncodeDecodeLeDefined`:** Whenever `decode(bs) = Some(v)`, `encode(v) ≤_def bs`. Because `encode` deterministically writes `Uninit` into padding slots whereas `bs` may hold arbitrary initialized or uninitialized padding bytes, re-encoding after decoding drops padding back to `Uninit` while preserving every value-bearing byte (`lines 768–778`). This justifies eliminating self-assignments (`tmp = x; x = tmp`): omitting the write leaves `bs` in place instead of `encode(v)`, keeping memory more defined so all later decodes yield identical results by `DecodeMono`.

#### 1.2 Aeneas PR `#1447`'s Three-Level Layout Mechanization

Aeneas PR `#1447` (`2a1dd755`, 12 Lean modules under `backends/lean/Aeneas/Data/Layout/`, plus `ExtractTypes.ml`) implements MiniRust's representation model in Lean 4 without pointer provenance:

1. **Bytes layer (`Bytes.lean:10–65, 216–245`):** Defines `AbstractByte := uninit | init (data : Byte)` and `Bytes n := Vector AbstractByte n` with bytewise `le_defined`, `subslice_with_length`, `write_subslice_at_index`, and `foldl_write_subslice_overlay_le_defined` (`lines 235–244`, proved via a per-index overwrite dichotomy).
2. **Machine-type and Layout layer (`MTypes.lean`, `Defs.lean`, `EncodeDecode.lean`, `Valid.lean`, `GaloisConnection.lean`):**
   - `MType` (`.int | .tuple fields TupleFlags | .enum variants EnumFlags`, `MTypes.lean:87–91`) intentionally omits concrete field offsets so one `MType` admits multiple valid layouts.
   - `Layout : MType → Type 0` (`Defs.lean:42–60`) stores `SizeAndAlign` (`wf_align : align.isPowerOfTwo`, `wf_size : align ∣ size`), field offset functions `field_offs`, recursive `field_layouts`, and for enums a decision tree `Discriminator` (`.known | .invalid | .read offset ty matcher`) paired with `variant_tags : List TagToWrite`.
   - `Layout.Valid` (`Valid.lean:34–87`) enforces structural soundness: `TupleValid` (pairwise disjoint field ranges `disj_range`, all `field_offs + size ≤ sa.size`), `EnumValid` (`tags_preserve_payload`, `discr_complete`, and `discr_tags_le_defined`), and `Layout.satisfies` (`Properties.lean:113–126`: `ReasonablyAligned`, `Packed n` with existential field bijection `Fin n → Fin n`, `Aligned n`, `Transparent`, `IsReprCTuple`, `IsReprCEnum`, `IsReprPrimEnum`).
   - `GaloisConnection.lean:101–256` proves all four laws for every `hl : l.Valid`: `valid_decodeValid`, `valid_decodeMono`, `valid_decodeEncode`, and `valid_encodeDecodeLeDefined`.
3. **Surface typeclass layer (`HasLayout.lean:31–43, 141–187`):** `HasLayout α` pairs `rty : RichMType` with a **partial bijection** (`embed : α → { v // v.valid_for rty.1 }`, `retract : { v // v.valid_for rty.1 } → Option α`, laws `retract_embed` and `embed_retract`). Partiality in `retract` allows refined Lean types (e.g. non-null/bounded wrappers) to forbid machine values that are structurally valid in `MVal`.

#### 1.3 Provenance Asymmetry (`#1497` `Repr.lean`) and `SpatialPin` Integration (`joshlf/anneal`)

Two critical design contrasts emerge when comparing PR `#1447` with PR `#1497` (`d17ca83f`) and `joshlf/anneal@20aa2043`:

- **Why relational `encode` diverges from `decode⁻¹` under pointer provenance:** In PR `#1497` (`Aeneas/Std/Heap/Repr.lean:33–48, 97–128, 209–318`), `Byte` carries symbolic pointer lanes (`uninit | data (value : U8) | pointer (value : RawPtr Unit) (lane : Nat)`), and `Repr ty` uses functional `decode` alongside relational `encode : ty → Vector Byte size → Prop` (`Repr.lean:100–101`). When pointer provenance is absent (`#1447`) or on exact pointer descriptors (`pointer_decode_iff` at `Repr.lean:277–292`), `decode bytes = some v ↔ encode v bytes` makes relational `encode` redundant. When scalar `decode` can read address bytes numerically from pointer lanes (`Byte.numeric`, `Repr.lean:42–48, 213`), however, scalar `encode` **must** emit only provenance-free `.data` (`Repr.lean:214`) to prohibit forging pointer provenance from integer writes—making `encode` strictly narrower than `decode⁻¹`. Pointer payload tracking (`Repr.Carries`, `Repr.lean:125–128`) derives pointer containment directly from `encode` rather than duplicating a ghost pointer table, and storing `lane : Fin pointerWidth` directly in `Byte.pointer` avoids the external `encode_valid` obligation (`Repr.lean:114–117`).
- **Upgrading `SpatialPin` without `Vector` WHNF overhead:** In `joshlf/anneal@20aa2043`, `LoanGraph.lean:519–542` and `SpatialPin.lean:219–220, 276` define `SpatialCodec` with only `decode (encode v) = some v` and unconditionally reject any block with `.uninit` cells (`if hasUninitCell cells then .fail`), blocking padded structs and `MaybeUninit<T>`. Replacing `hasUninitCell` rejection with Galois-law `LayoutCodec` over `List AbstractByte` (and replacing `#1447`'s `Vector.ofFn` dependent-length casts `h ▸ bytes` at `EncodeDecode.lean:67, 98` with length-indexed `List` operations) avoids dependent cast friction in Lean's `Init.*`-only kernel while validating padding-tolerant reabsorption.

---

### 2. Layout Opaqueness (`Classical.choice` vs. Universal Quantification) and `zerocopy` Traits

**Basis: source (`JoJoDeveloping/aeneas@2a1dd755` `HasLayout.lean`, `ReprC.lean`; `google/zerocopy@1962a9c0` `zerocopy/src/lib.rs`; `AeneasVerif/aeneas@d17ca83f` `TRANSMUTE.md`) + derived.**

#### 2.1 `Classical.choice` Opaqueness vs. Universal Layout Quantification

In `Aeneas/Data/Layout/RichMTypes.lean:74–96`, `RichMType.example_layout` constructively builds a valid layout for any `Reasonable` type (laying out `reprRust` fields in list order via `ReprC.mkTuple`). Exposing `example_layout` directly would allow proofs over `#[repr(Rust)]` structs to inspect and depend on unstable compiler-unspecified field offsets. PR `#1447` (`HasLayout.lean:48`) defeats definitional unfolding with a single axiom application:

```lean
-- JoJoDeveloping/aeneas@2a1dd755: Aeneas/Data/Layout/HasLayout.lean:48
noncomputable def the_layout (α : Type u) [h : HasLayout α] :
    { l : Layout (ty α) // h.valid_layout l } :=
  Classical.choice (Nonempty.intro h.valid_layout_inhab)
```

Because `Classical.choice` is opaque in Lean's kernel, client proofs can observe only `h.valid_layout l` (guaranteeing `ReasonablyAligned`, disjoint field ranges, and the 4 Galois laws for `#[repr(Rust)]`, while still exposing exact `tupleFieldOffset` equations under `IsReprCTuple` for `#[repr(C)]`).

However, comparing `Classical.choice` blocking against **universal layout quantification** (`∀ l : Layout (ty α), h.valid_layout l → P l`) reveals two structural advantages of universal quantification:
1. **Zero `Classical.choice` in the axiom cone:** Universal quantification remains 100% constructive (`[propext, Quot.sound]`), avoiding `noncomputable` wrappers inside `Init.*`-only proof layers.
2. **Cross-monomorphization / version stability:** `the_layout α` picks a single fixed unknown layout `l₀` for `α` across a proof, whereas quantifying universally over all `l` satisfying `h.valid_layout l` guarantees that correctness holds even if distinct compilation units or compiler versions select different valid `#[repr(Rust)]` permutations.

#### 2.2 Exact Galois Characterizations of `google/zerocopy` Traits

On `google/zerocopy@1962a9c0e3eda8a3a58387f61c70ddd2c396b118` (`zerocopy/src/lib.rs`), the six core marker and reinterpretation traits (`KnownLayout` `line 746`, `Immutable` `line 1729`, `TryFromBytes` `line 1965`, `FromZeros` `line 3768`, `FromBytes` `line 4358`, `IntoBytes` `line 6005`) admit crisp algebraic characterizations relative to any valid Galois layout `(l : Layout (ty α), hl : l.Valid)` and partial bijection `(embed, retract)`:

| `zerocopy` Trait (`zerocopy/src/lib.rs`) | Galois / Layout Characterization over `(l : Layout (ty α), embed, retract)` | Padding & Partial-Init Interaction |
|---|---|---|
| **`IntoBytes`** (`line 6005`; paired with `Immutable` `line 1729`) | `∀ x : α, ∀ i < l.size, ((encode l (embed x).1 (embed x).2)[i]).data.isSome = true` (plus interior-mutability exclusion from `Immutable`) | **Tightens `EncodeDecodeLeDefined` from `≤_def` to `=`:** on any `bs` where `decode l bs = some v`, `encode l v hv = bs` holds identically because zero padding `.uninit` positions exist. A padded struct `#[repr(C)] (u8, u16)` (`size = 4`, offset `1 = .uninit`) satisfies `DecodeEncode` and `EncodeDecodeLeDefined` yet refutes `IntoBytes` at index `1`. |
| **`FromBytes`** (`line 4358`) | `∀ bs : Bytes l.size, (∀ i < l.size, (bs[i]).data.isSome) → ∃ x : α, (decode l bs).bind retract = some x` | Every fully initialized byte slice decodes to a valid `α` (not merely `MVal`, requiring `retract` totality on `valid_for`), while padding bytes may also be `.uninit` or arbitrary `.init` bytes by `DecodeMono`. |
| **`FromZeros`** (`line 3768`) | `∃ x₀ : α, (decode l (Vector.replicate l.size (.init 0))).bind retract = some x₀` | All-zero initialized bytes form a valid `α` (e.g., `Option<NonZeroU8>` via niche `0`, whereas `NonZeroU8` refutes it). |
| **`TryFromBytes`** (`line 1965`, `is_safe` / `is_bit_valid`) | Soundness contract: `∀ bs : Bytes l.size, (∀ i ∈ inspected, (bs[i]).data.isSome) → is_bit_valid bs = true → ∃ x : α, (decode l bs).bind retract = some x` | Must inspect every byte read by `decode_discriminant` and non-padding fields (`Discriminator.read`), ignoring `.uninit` padding offsets. |
| **By-value `transmute<Src, Dst>`** | `l_src.size = l_dst.size ∧ ∀ x : Src, ∃ y : Dst, (decode l_dst (encode l_src (embed x).1 (embed x).2)).bind retract = some y` | **Automatic UB protection:** if `Src` leaves `.uninit` padding at an index where `Dst` expects a scalar or tag byte, `decode l_dst` returns `none` (`retract` fails). Contrast with PR `#1497` `TRANSMUTE.md:71–85`, where `ExactAt(S, T, x, expected)` universally quantifies over **every** `bs` decoding to `x` (`S.decode bs = Some x → T.decode bs = Some expected`) rather than choosing one canonical encoding. |

---

### 3. Stateful Lifetime Continuations, Three-Tier Scheduling, and `ClosedViews`

**Basis: source (`JoJoDeveloping/aeneas@5c28fe8d` `InterpLiveness.ml`, `InterpStatements.ml`, `SymbolicToPure*.ml`, `PureMicroPassesGeneral.ml`, `tests/{src,lean}/stateful-lifetime*`; `AeneasVerif/aeneas@d17ca83f` `Heap/{Model,ExclusiveReturn,ScopedView}.lean`; `joshlf/anneal@20aa2043` `PureLift/{LoanGraph,SpatialPin}.lean`) + derived.**

#### 3.1 Why Pure Functional Borrow-Erasure Breaks Safe↔Raw Bridges

In pure Aeneas functional translation (`10.1145/3547647`) and `PureLift`, backward functions are pure (`T → T`), and any borrow abstraction returning no reference in its outputs is immediately retired at the call site. Applying that discipline to safe-to-raw pointer interop (`tests/src/stateful-lifetime.rs:27–72`) fails doubly:
1. **`Ptr::from_mut<'a>(r: &'a mut T) -> Ptr<T>`** returns no safe reference (`Ptr<T>` is `Copy` raw wrapper). Standard borrow-erasure immediately ends `'a` and yields `T → Result (Ptr T × T)`, reclaiming `x : T` before `ptr` is ever dereferenced!
2. **`Ptr::as_mut<'a>(self: Ptr<T>) -> &'a mut T`** takes a raw `Ptr<T>` (no safe `&mut` input) and yields a pure backward function `T → Unit` that cannot write mutations back into the spatial heap, while lacking a safe borrow conflict to terminate the first `as_mut()` before a second `ptr.as_mut()` call.

#### 3.2 Effectful Continuations, NLL-Style `short`/`default`/`long` Scheduling, and CSE Disabling (`PR #1537`)

Aeneas PR `#1537` (`5c28fe8d`) resolves both obstructions via three coupled mechanisms:

1. **Effectful `Result`-returning backward thunks (`SymbolicToPureCore.ml:162`, `SymbolicToPureAbs.ml:232–246, 1075–1098`, `SymbolicToPureTypes.ml:932–978`):** Replacing `can_fail` with `is_effectful : bool` keeps `Option.is_some abs.stateful_lifetime` abstractions from collapsing into pure functions (even when `inputs = [] && outputs = []`), emitting monadic `Result` backward continuations (`tests/lean/StatefulLifetime.lean:60–75`):
   ```lean
   axiom Ptr.as_shr {T : Type _} : Ptr T → Result (T × (Result Unit))
   axiom Ptr.as_mut {T : Type _} : Ptr T → Result (T × (T → Result Unit))
   axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))
   axiom Ptr.from_shr {T : Type _} : T → Result ((Ptr T) × (Result Unit))
   ```
2. **Three-tier lifetime scheduling (`InterpLiveness.ml:17–189`, `InterpStatements.ml:665–675, 1114–1275`):**
   - **`short` (`as_mut`, `as_shr`):** Runs a 624-line backward local-variable liveness fixpoint over LLBC (`compute_liveness`, approximating Rust NLL; `apply_place_write` at `InterpLiveness.ml:36–47` treats projected writes `*r = ...` / `x.f = ...` as reads rather than kills so root locals remain live). Immediately before statements or block exits where no live local carries a borrow from a `short` abstraction (`InterpStatements.ml:665–675`), Aeneas retires the abstraction early—allowing `ptr.as_mut()` → mutate → `as_mut_back` → `ptr.as_shr()` → `as_shr_back` → `ptr.as_mut()` sequentially (`StatefulLifetime.lean:119–130`).
   - **`long` (`from_mut`, `from_shr`):** Survives `if`/`match` control-flow joins via two-pass join retry (`InterpStatements.ml:1114–1275`, retrying joins without ending `long` abstractions first) and stays open across loops until the underlying safe place is re-accessed or the function returns (`StatefulLifetime.lean:135–171`).
   - **`default`:** Uses standard region expiration rules without inlining into a pure pair (`from_mut_regular`).
3. **Mandatory CSE disabling (`PureMicroPassesGeneral.ml:686–722`, `tests/src/stateful-lifetime.rs`):** `simplify_duplicate_calls_visitor` (`line 702`) restricts deduplication to `(not monadic) && not (is_result_ty bound.ty)`. Deduplicating two identical calls to an effectful backward thunk would be **unsound** because each invocation reads/writes mutable heap state! Negative borrow-check tests (`tests/src/stateful-lifetime-negative.rs:44–115`) enforce that dependent outlives (`'a: 'b` with stateful `'b`), ambiguous `'static` unattached abstractions across multiple stateful lifetimes, or returning stateful borrows into non-stateful output lifetimes fail closed.

#### 3.3 Nested Scope Composition via `RootReturn` + `ClosedViews` (`PR #1497`) and `PureLift` Implications

Ending a `from_mut_back` continuation safely when nested raw sub-views or shared exposures occurred in between requires proving that no active alias remains. In PR `#1497`:
- `Model.lean:23–24, 48–59, 318–345` separates **`block.active`** (whether this view can still be accessed) from **`block.alive`** (physical allocation lifetime). Retiring a child view sets `active := false` while preserving `alive := true` and allocation bounds for pointer `offset`/`distance` arithmetic.
- `ExclusiveReturn.lean:135–141` proves `endBorrowRange_exclusive.spec` under explicit `RootReturn s p.provenance` authority (`s.noAliases` confirming zero other active views share `blk.root`): **owning `.borrowed` cells alone is insufficient** if an active child view still aliases `root` (`README.md:50–58`).
- `ScopedView.lean:48–178` introduces `ClosedViews s₀ s₁`, requiring `s₀.next ≤ s₁.next`, identical `returnShape := (blk.bptr, blk.root, blk.repr.length, blk.active)` on all pre-existing IDs `< s₀.next`, and `blk.active = false` on all newly issued IDs `≥ s₀.next`—with **unrestricted byte updates**. `RootReturn.after_closed_views` (`lines 111–157`) proves by induction over `ClosedViews.trans` (`lines 59–75`) that outer `RootReturn` authority survives arbitrarily many nested scoped borrows and disjoint byte mutations.

**Mapping onto `joshlf/anneal@20aa2043` `PureLift`:** In `SpatialPin.lean:206–293`, `freezeToSpatialInState` and `reabsorbFromSpatialInState` already implement `long` pinning (`LoanPhase.spatialPinned` preserving `BackTarget`). Adding dual `checkoutFromSpatial` / `writebackToSpatial` plan steps (creating a temporary pure `LoanEntry` whose `BackTarget` updates `SpatialBlock`, paired with `ClosedSpatialScopes` tracking `activeSubSplits == 0`) reproduces PR `#1537`'s `short`/`long` schedule inside untrusted proof plans while keeping `InterpLiveness.ml` completely out of the TCB.

---

### 4. Surface Resource-Contract Desugaring (`owned(p)` in Fulminate/CN and `compiler-team#942`)

**Basis: normative + documentation (`10.1145/3704879`, `10.1145/3571194`, `rust-lang/compiler-team#942`) + derived.**

CN (`10.1145/3571194`) and Fulminate (`10.1145/3704879`, `rems-project/cerberus@e29a8ec9`) restrict separation logic to a mode-checked first-order fragment whose ownership predicates (`RW` / `Owned`) possess an executable ghost-state interpretation for runtime checking. Adopted for Rust contracts in `rust-lang/compiler-team#942` (accepted `2025-11-22`, followed at `rust-lang/rust#149213`), this surface exposes five core primitives:

```rust
// rust-lang/compiler-team#942: core::contracts::ownership primitives & convenience API
pub const fn owned_unaligned<T>(ptr: *const T) -> ManuallyDrop<T>;
pub fn alloc_block_layout<T>(ptr: *const T, layout: Layout);
pub const fn owned<T>(ptr: *const T) -> ManuallyDrop<T>;        // aligned + owned_unaligned
pub fn alloc_block<T>(ptr: *const T);
pub fn alloc_block_array<T>(ptr: *const T, count: usize);
```

1. **Imperative effect sequencing as `IProp` triples:** Rather than writing explicit `∗` formulas or existentials, `;`-separated statements inside `#[requires(...)]` and `#[ensures(...)]` thread ownership linearly:
   ```rust
   #[requires(let r1 = owned(p); owned(r1); true)]
   #[ensures(move |_| { let r2 = owned(p); let v2 = owned(r2); r2 == r1 && v2 == 0 })]
   ```
   desugars into the first-order `IProp` Hoare triple `{ ∃ r1 v0, p ↦ r1 ∗ r1 ↦ v0 } f(p) { ∃ r2, p ↦ r2 ∗ r2 ↦ 0 ∗ ⌜r2 = r1⌝ }`, while `alloc_block(ptr)` desugars directly to `Resource.cleanup base size bptr true` (`Aeneas#1551` `Resource.lean:21`, distinct from stack `owned(p)` which carries no `free` authority).
2. **`MaybeUninit<T>` and `ManuallyDrop<T>` runtime invariants:** Specifying `core::ptr::write<T>(dst, src)` uses `owned::<MaybeUninit<T>>(dst)` in `#[requires]` because `owned::<T>` checks type validity and would trigger UB in Miri if `dst` held uninitialized bytes; `owned` returns `ManuallyDrop<T>` so evaluating a contract never invokes `Drop::drop` on ghost-observed values. Under `#[cfg(not(miri))]`, `owned` returns `Err(Error::CheckUnsupported)` so concrete tests without Miri ownership tracking skip rather than cause UB.
3. **TCB statement-origin boundary in `joshlf/anneal`:** Because `TrustedBoundary.lean:183–206` forbids `Trusted` theorem statements from mentioning `Anneal.*` (`theory/`) definitions, surface `owned(p)`/`alloc_block` contracts on `unsafe fn` cannot expose `Anneal.SepLogic.IProp` directly in theorem types; they must either live as pure `Trusted` memory-ownership predicates or desugar inside `theory/` proofs discharging `Trusted.MirSemantics.WellFormed` / `CrateTheorem`.

---

## Boundaries

- **Exact byte equality round-tripping (`encode (decode bs) = bs`) and CSE on effectful backward thunks — known not to apply:** For padded `#[repr(C)]` layouts such as `(u8, u16)` (`EncodeDecode.lean`, `Valid.lean`), `encode` emits `.uninit` at padding offsets, so equality `encode (decode bs) = bs` fails when `bs` contains initialized padding (only `≤_def` holds unless `IntoBytes` guarantees zero padding). Likewise, `PureMicroPassesGeneral.ml:702` establishes that pure common-subexpression elimination (`simplify_duplicate_calls_visitor`) does not extend to `Result`-returning backward thunks (`is_result_ty bound.ty`), where deduplicating calls alters mutable heap state.
- **Dynamic shared/read-only contracts and reference-returning contracts in `compiler-team#942` — unsupported:** `rust-lang/compiler-team#942` explicitly marks read-only / shared points-to permissions (needed for `ptr::read` without exclusive ownership) and functions returning reborrowed `&'a mut T` (where ownership returns at lifetime expiration rather than function return) as out of scope.
- **Unsized DSTs (`[T]`, `dyn Trait`) and unions in Aeneas PR `#1447` — unsupported:** PR `#1447` (`MTypes.lean`, `Defs.lean`) models sized integers, tuples/structs, and enums only; slice DST layouts (`KnownLayout::LAYOUT` / `SizeInfo::SliceDst` in `google/zerocopy@1962a9c0`) and `union` definedness (which requires per-byte union chunk tracking rather than equality `le_defined` on `MVal`, noted at `Valid.lean:61`) are unmodeled in `#1447`.
- **Single ZST accesses and mutable `u8` loans over pointer lanes in PR `#1497` — unsupported:** As documented in `Aeneas/Std/Heap/README.md:21, 45–48`, PR `#1497` enforces `0 < repr.size` on `read`/`write`/`borrow` (`Repr.lean:168–206`) and rejects mutably loaning a single byte inside an 8-lane symbolic pointer via `&mut u8`, even though both are valid Rust patterns.
- **Direct compilation of PRs `#1447`, `#1537`, `#1497` and `rustc` layout cross-fuzzing — not examined:** Code definitions, Galois proofs, and `InterpLiveness.ml` rules were verified by primary-source inspection, whereas running `lake build` on those WIP PRs or fuzzing `ReprC.mkTuple` against `rustc` `layout_of` across target triples was not executed.
- **Runtime behavior of Miri's experimental Fulminate ownership prototype — unknown:** `compiler-team#942` references an external Miri ownership-tracking prototype and notes pending execution-model design shifts toward `rust-lang/rust#149213`; final stabilized `rustc` / Miri behavior remains unknown until upstream implementation merges.

---

## Evidence

All claims rest on primary specifications, pinned public commits, and peer-reviewed DOIs (observed `2026-11-20`):

- **`minirust/minirust@063d784186d3252bee242217f218223205c0b568`:** `spec/lang/representation.md:32–142` (`Type::decode`, `Type::encode`, `decode_ptr`, `encode_ptr`), `520–621` (`check_ptr`, `check_value`, `typed_store`, `typed_load`), `641–806` (`DefinedRelation`, `AbstractByte`, `le_defined`, 4 Galois laws, `transmute`).
- **`JoJoDeveloping/aeneas@2a1dd75567517e078f90b1df746af7373fe24cbc` (PR `#1447`):**
  - `backends/lean/Aeneas/Data/Layout/Bytes.lean:10–65, 216–245` (`AbstractByte`, `Bytes`, `le_defined`, `foldl_write_subslice_overlay_le_defined`)
  - `MTypes.lean:87–118`, `Defs.lean:13–60`, `EncodeDecode.lean:38–146`, `ReprC.lean:37–116`, `Properties.lean:12–126`, `Valid.lean:34–87, 236–454`
  - `GaloisConnection.lean:101–256` (`valid_decodeValid`, `valid_decodeMono`, `valid_decodeEncode`, `valid_encodeDecodeLeDefined`)
  - `Reasonable.lean:11–34`, `RichMTypes.lean:9–96`, `HasLayout.lean:31–52, 118–187` (`HasLayout.the_layout`)
- **`JoJoDeveloping/aeneas@5c28fe8def8db99041d22503175591ba1fa47915` (PR `#1537`):**
  - `src/interp/InterpLiveness.ml:17–189` (`apply_place_write`, `compute_liveness`), `InterpStatements.ml:665–675, 1114–1275`
  - `src/symbolic/SymbolicToPureCore.ml:162`, `SymbolicToPureAbs.ml:232–246, 1075–1098`, `SymbolicToPureTypes.ml:932–978`
  - `src/pure/PureMicroPassesGeneral.ml:686–722` (`simplify_duplicate_calls_visitor`)
  - `tests/src/stateful-lifetime.rs:27–99`, `tests/src/stateful-lifetime-negative.rs:44–115`, `tests/lean/StatefulLifetime.lean:57–131`
- **`AeneasVerif/aeneas@d17ca83fc07d712d1785f650840cb2073c259e69` (PR `#1497`):**
  - `backends/lean/Aeneas/Std/Heap/Repr.lean:33–128, 209–318`, `Model.lean:18–126, 318–364`, `ExclusiveReturn.lean:135–216`, `ScopedView.lean:48–178`, `README.md:16–97`, `TRANSMUTE.md:48–95`, and PR `#1497` review comments on `Repr.lean` and `Model.lean`.
- **`google/zerocopy@1962a9c0e3eda8a3a58387f61c70ddd2c396b118`:** `zerocopy/src/lib.rs:746, 1729, 1965, 3768, 4358, 6005`.
- **`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`:** `theory/Anneal/PureLift/{LoanGraph.lean:519–623, SpatialPin.lean:44–61, 206–354}`, `trusted/audit/TrustedBoundary.lean:183–206, 442–596`.
- **Contracts & Literature:** `rems-project/cerberus@e29a8ec9f247ef7e0fbc3a19141dfc8f0f9b902e`, `rust-lang/compiler-team#942`, Fulminate (`10.1145/3704879`), CN (`10.1145/3571194`), Aeneas (`10.1145/3547647`, `10.1145/3674640`), RefinedRust (`10.1145/3656423`).

---

## Revalidation

1. **Galois law & `zerocopy` trait boundary probe:** Fetch `GaloisConnection.lean` (`2a1dd755`) and `zerocopy/src/lib.rs` (`1962a9c0`) via `curl --http1.1 -fsSL` and verify that the four theorem signatures (`valid_decodeValid`, `valid_decodeMono`, `valid_decodeEncode`, `valid_encodeDecodeLeDefined`) hold without `sorry`. In an `Init.*`-only Lean `4.34.1` probe (`/tmp/galois_zerocopy_probe.lean`), encode a 4-byte padded `repr(C)` tuple `(u8, u16)` (`[init a, uninit, init b0, init b1]`) vs. an unpadded 4-byte tuple `(u16, u16)`, verifying by `rfl` / `decide` that both satisfy all 4 Galois laws (`EncodeDecodeLeDefined`) while only `(u16, u16)` satisfies the `IntoBytes` all-`isSome` predicate.
2. **Stateful-lifetime regression check:** Inspect `PureMicroPassesGeneral.ml` (`5c28fe8d`) around `simplify_duplicate_calls_visitor` to verify `is_result_ty bound.ty` still disables CSE on effectful backward continuations, and check `StatefulLifetime.lean` (`example_two_derefs`) to confirm `from_mut` (`long`) encloses sequential `as_mut`/`as_shr`/`as_mut` (`short`) calls.
3. **Contracts surface sync check:** Check `rust-lang/rust#149213` for updates to `core::contracts::ownership::{owned, owned_unaligned, alloc_block*}` signatures before finalizing any front-end `owned(p)` desugaring into `IProp`.
