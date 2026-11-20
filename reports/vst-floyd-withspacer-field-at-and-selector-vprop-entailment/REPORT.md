# Canonical PROP/LOCAL/SEP State, withspacer Struct-Padding Decomposition, and Self-Framing Selector Entailment across VST-Floyd, Steel/Pulse, and Anneal

## Summary

Two complementary separation-logic breakthroughs resolve the sharpest ergonomic and kernel-scaling bottlenecks in low-level systems verification:

1. **VST `floyd` (`PrincetonUniversity/VST` at `d50ac1969f9f6586621895eb043ccf08a165f731`)** stratifies symbolic assertions into canonical **`PROPx P (LOCALx Q (SEPx R))`** zones (`floyd/canon.v:L9–161`) and decomposes composite C aggregates through **`field_at`** and **`withspacer`** (`floyd/field_at.v:L124–217`, `floyd/mapsto_memory_block.v:L342–466`). `withspacer sh be ed P p` checks `ed - be == 0` directly: on zero-gap structs (`zerocopy::IntoBytes`), `withspacer` reduces by **definitional equality (`rfl`)** to `P p` with zero `* emp` clutter; on padded structs (`#[repr(C)] struct Padded { a: u8, b: u16 }`), `withspacer` isolates `[be, ed)` as an explicit byte spacer so typed moves clobber padding to `.uninit` while preserving total allocation conservation (`sizeof`).
2. **Project Everest `Steel` and `Pulse` (`FStarLang/steel` at `ff1acec21b5e7ab864aec9901231a5be06116cdd`, `FStarLang/FStar` at `fc1776afe592ed8eef352c6610614a70d77b3b66`)** eliminate existential quantifier skolemization across control-flow joins via **self-framing footprint-local value selectors** (`sel_depends_only_on` and `sel_depends_only_on_core` in `Steel.Effect.Common.fsti:L59–144`), while `Pulse` replaces `Steel`'s tactic-in-type `rmem` projections with **`[@@@mkey]` syntactic matching keys** (`Pulse.Lib.Core.fsti:L26–47`).

Transferring both into **Anneal** (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, Lean `v4.34.1`) outside the TCB shows how a **canonical positive-radix trie (`PTree`) + total footprint-local `SpatialVProp` + `withSpacer`** unifies VST's stratification, Steel's quantifier-free selectors, and Pulse's structural keys within the 51-module `Init.*` foundation ceiling (`TrustedBoundary.lean:L442–596`).

## Applicability

This report examines and connects seven durable upstream software subjects, five peer-reviewed primary sources, and one finite execution environment:

1. **VST-Floyd** (`PrincetonUniversity/VST@d50ac1969f9f6586621895eb043ccf08a165f731`): `floyd/{canon,field_at,mapsto_memory_block,aggregate_pred,data_at_rec_lemmas,entailer}.v`, paired with Appel et al. (*Program Logics for Certified Compilers*, CUP 2014, DOI `10.1017/CBO9781107256552`) and Cao et al. (*VST-Floyd*, JAR 2018, DOI `10.1007/s10817-018-9457-5`).
2. **Project Everest `Steel` & `Pulse`** (`FStarLang/steel@ff1acec21b5e7ab864aec9901231a5be06116cdd`, `FStarLang/FStar@fc1776afe592ed8eef352c6610614a70d77b3b66`, and `FStarLang/pulse@c35460e00483be17a38397b1594c29a9bf29df15` whose `README.md:L1–10` records Pulse's migration into `FStarLang/FStar` under `pulse/lib/`): `Steel.Memory.fsti`, `Steel.Effect.Common.fsti`, `Steel.Reference.fsti`, `PulseCore.InstantiatedSemantics.fsti`, `PulseCore.Semantics.fst`, and `Pulse.Lib.Core.fsti`, paired with Swamy et al. (`SteelCore`, ICFP 2020, DOI `10.1145/3409003`), Fromherz et al. (`Steel`, ICFP 2021, DOI `10.1145/3473590`), and Ebner et al. (`PulseCore`, PLDI 2025, DOI `10.1145/3729311`).
3. **`zerocopy` & Anneal / Lean 4** (`google/zerocopy@ec133ce4d7993775413d852f91c9e3eb2a2a0897`; `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`): `zerocopy/src/lib.rs`, `trusted/audit/TrustedBoundary.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `theory/Anneal/PureLift/{Lens,SpatialPin,MirBridge}.lean`. Non-TCB `theory/` modules must open with `prelude`, import only the 51 locked `Init.*` modules plus `Trusted.*` and `Anneal.*`, forbid `._unsafe_rec` and banned tactics (`omega`, `ring`, `bv_decide`, `native_decide`, `grind`, `sorry`), use only `{propext, Quot.sound, Classical.choice}`, and satisfy Statement-Origin Separation.

**Corpus relationship:** Existing packages `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses`, `hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4`, `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, and `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures` cover high-level separation-logic tooling and partial SROA. This report extracts the exact Coq/F\* definitions of VST `PROP/LOCAL/SEP`, `field_at`, `withspacer`, `Steel` `sel` (`rmem`), `Pulse` `[@@@mkey]`, and their pure 3-axiom Lean 4 mechanization for `zerocopy` and Anneal.

## Findings

### 1. VST-Floyd Canonical `PROPx / LOCALx / SEPx` Stratification and `entailer` Normalization

Basis: normative (Cao et al., JAR 2018 `10.1007/s10817-018-9457-5`) + source (`PrincetonUniversity/VST@d50ac196...`, `floyd/canon.v:L9–260`, `floyd/entailer.v:L97–349`)

Unstratified verification conditions embed pure propositions, local variable bindings, and spatial points-to atoms inside a single nested record or separation conjunction, forcing rewrite tactics (`rw`, `simp`) to traverse the entire heap spine on every step. `floyd/canon.v` fixes every assertion into three orthogonal zones (`L52–101`):

1. **`PROPx (P : list Prop)` (`L52–53`)**: Pure propositional facts `andp (prop (fold_right and True P))`.
2. **`LOCALx (Q : list localdef)` (`L9–30, L63–64`)**: Finite-map bindings for temporaries (`temp i v`), addressable stack variables (`lvar i t v`), and globals (`gvars gv`).
3. **`SEPx (R : list mpred)` (`L99–101`)**: Spatial separation-logic atoms `fold_right_sepcon R`, sealed against accidental unfolding by **`Arguments SEPx A R _ : simpl never`** (`L101`; similarly `Arguments GLOBALSx gs _ : simpl never`, `L81`).

Order-independence holds via three permutation lemmas (`PROPx_Permutation`, `LOCALx_Permutation`, `SEPx_Permutation`, `L115–161`), while `SEPx_super_non_expansive` (`L236–260`) propagates step-indexed contractive invariants (`approx`) cleanly across list elements. During proof normalization, `pull_out_props` and `ent_iter` (`floyd/entailer.v:L312–349`) extract pure `!!P` facts from `SEPx` atoms into Coq hypotheses once, substitute equalities, simplify CompCert typechecking (`simpl_denote_tc`, `L97–142`), and confine arithmetic rewriting strictly to `PROP`.

**Transfer to Anneal:** In `joshlf/anneal@c131b320`, `Trusted.MirSemantics.State` stores locals and allocations in unstratified `List`s (`MirBridge.lean`), while `SpatialPin` stores spatial blocks in `List (SpatialBlock Val)` (`SpatialPin.lean:L63–248`). Replacing raw list spines inside `theory/` with canonical `PROP / LOCAL / SEP` stratification where `LOCAL` and `SEP` use balanced `PTree`s (and `@[irreducible]` firewalls replace `simpl never`) prevents `rw`/`simp` from walking unrelated locals and allocations.

---

### 2. VST `field_at`, `data_at_rec`, and `withspacer`: Zero-Gap `rfl` Collapse vs. Padding Soundness

Basis: source (`VST@d50ac196...`: `floyd/mapsto_memory_block.v:L284–466`, `floyd/field_at.v:L124–217, L999–1198`, `floyd/data_at_rec_lemmas.v:L50–97`, `floyd/aggregate_pred.v:L138–160, L579–595, L1342–1503`; `zerocopy@ec133ce4...`: `zerocopy/src/lib.rs`; `joshlf/anneal@c131b320`: `Trusted/MirSemantics.lean`) + execution (`Probe 2`) + derived

To unify field-level reasoning with byte-level `memory_block` predicates (necessary for `malloc`/`free`, `memset`/zeroing, and union punning), VST defines offset shifting, explicit spacers, and structural field predicates:

```coq
Definition at_offset (P: val -> mpred) (z: Z): val -> mpred := fun v => P (offset_val z v).
(* Arguments at_offset P z v : simpl never. *)

Definition spacer (sh: share) (be: Z) (ed: Z) : val -> mpred :=
  if Z.eq_dec (ed - be) 0 then fun _ => emp
  else at_offset (memory_block sh (ed - be)) be.

Definition withspacer sh (be: Z) (ed: Z) P (p: val): mpred :=
   if Z.eq_dec (ed - be) 0 then P p
   else P p * spacer sh be ed p.
```

Three crucial properties emerge from `floyd/mapsto_memory_block.v`, `floyd/field_at.v`, `floyd/data_at_rec_lemmas.v`, and `floyd/aggregate_pred.v`:

1. **Zero-Gap Elimination Without `* emp` Clutter (`mapsto_memory_block.v:L349–352`)**:
   `withspacer` tests `Z.eq_dec (ed - be) 0` directly to return **`P p` instead of `P p * emp`**, eliminating residual unit assertions on tightly packed structs while preserving `withspacer_ramif_Q` (`L364–375`) to frame spacers automatically when updating a field. Notice `L337–338` warns that `spacer` alone lacks `isptr` local facts when `ed = be` (because `emp` holds on `Vundef`), whereas `withspacer_preserve_local_facts` (`L422–429`) inherits `isptr p` from `P p`.
2. **Exact Byte-Block Conservation Across Structs and Unions**:
   `field_at sh t gfs v p` (`field_at.v:L124–126`) pairs `!! (field_compatible t gfs p)` with `at_offset (data_at_rec sh (nested_field_type t gfs) v) (nested_field_offset t gfs) p`. In `data_at_rec_eq` (`data_at_rec_lemmas.v:L60–97`) and `nested_sfieldlist_at` (`field_at.v:L197–207`), every struct member is wrapped in `withspacer sh (off_i + sizeof f_i) (field_offset_next ... sz)` using `struct_pred`, and unions wrap the active member up to `co_sizeof` using `union_pred` (`nested_ufieldlist_at`, `L209–217`). Because spacers explicitly account for all inter-field and trailing gaps, `memory_block_struct_pred` (`aggregate_pred.v:L1342–1414`), `mapsto_zeros_struct_pred` (`L1426–1503`), and `withspacer_field_at__Tunion` (`field_at.v:L1133–1198`) prove **exact equality** between `memory_block sh (sizeof t) p` and the separated field-plus-spacer tree!
3. **Direct Mapping onto Rust `zerocopy` and Anneal `deinitMovedPlace = true` (`Probe 2`)**:
   - **Zero-Gap `IntoBytes` (`#[repr(C)] struct Tight { a: u16, b: u16 }`)**: Field spans `[0, 2)` and `[2, 4)` inside size `4` yield `ed - be = 0` at every boundary (`2 - 2 = 0`, `4 - 4 = 0`). `withSpacer` reduces by **definitional equality (`rfl`)** to `sepConj P_a P_b` with **0 spacers**, giving a lossless bijection with `zerocopy::IntoBytes::as_bytes` (`zerocopy/src/lib.rs:L6005–6085`).
   - **Padded `FromBytes` (`#[repr(C)] struct Padded { a: u8, b: u16 }`)**: Field spans `[0, 1)` and `[2, 4)` inside size `4` force `withSpacer 1 2`, isolating offset `[1, 2)` as an explicit byte spacer. In Rust MIR under `Trusted.MirSemantics.evalOperandToSlot` (`MirSemantics.lean:L949–977`, matching `lean-miri`'s `deinitMovedPlace = true`), a typed move copies field spans `[0, 1)` and `[2, 4)`, deinitializes the source, and **clobbers the destination padding byte `[1, 2)` to `.uninit`** (`Probe 2`: `padded_dst = [0x11, None, 0x33, 0x44]`), so a subsequent `as_bytes` read fails cleanly (`FAULT_UNINIT_PADDING_READ`), while `mapsto_zeros_struct_pred` explains why `#[derive(FromZeros)]` (`zerocopy/src/lib.rs:L1574–1600`) remains sound for *all* structs (zeroing initializes fields and padding bytes alike).

---

### 3. `Steel` Self-Framing `vprop` Selectors vs. `Pulse` `[@@@mkey]` Predicate Indexing

Basis: normative (`SteelCore` ICFP 2020 `10.1145/3409003`; `Steel` ICFP 2021 `10.1145/3473590`; `PulseCore` PLDI 2025 `10.1145/3729311`) + source (`FStarLang/steel@ff1acec2...`: `Steel.{Memory,Effect.Common,Reference}.fsti`; `FStarLang/FStar@fc1776af...`: `pulse/lib/core/PulseCore.{InstantiatedSemantics,Semantics}.fsti`, `pulse/lib/common/Pulse.Lib.Core.fsti`)

Classical separation-logic assertions index heap ownership by value parameters (`pts_to r v`). Across $K$ basic-block joins or $M$ live mutable references, every update forces new existential witnesses `∃ v1 ... vM` (`192` existentials across $K=12, M=16$ in `Probe 2`). `Steel` eliminates these value indices from `slprop`s by equipping each assertion with a **self-framing ghost selector**:

```fstar
let selector' (a:Type0) (hp:slprop) = hmem hp -> GTot a
let sel_depends_only_on (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp) (m1:mem{disjoint m0 m1}). (interp_depends_only_on hp; sel m0 == sel (join m0 m1))
let sel_depends_only_on_core (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp). sel m0 == sel (core_mem m0)

noeq type vprop' = { hp: slprop u#1; t: Type0; sel: selector t hp }
type vprop = | VUnit : vprop' -> vprop | VStar : vprop -> vprop -> vprop
```

In `Steel.Effect.Common.fsti`:
- **`sel_depends_only_on_core` (`L69–70`)**: `core_mem m0` (`Steel.Memory.fsti:L29–39`) strips lock/invariant metadata from `mem`, forcing selectors to depend strictly on concrete heap cell ownership so selectors remain invariant across ghost invariant open/close steps.
- **Restricted Heap Views `rmem` & `focus_rmem` (`L274–360`)**: Specifications write `h (vptr r)` (`sel r h == x` in `Steel.Reference.fsti:L260–262, L294–304`) rather than `∃ v, pts_to r v`, while `frame_vc_norm` (`L414–461`) emits quantifier-free frame equalities `h0 frame == h1 frame`. Combinators `vrefine`, `vdep` (`dtuple2`), and `vrewrite` (`L543–641`) transform selector types compositionally; non-informative spatial resources (such as padding) use `to_vprop p` with selector `fun _ -> ()` (`L96–101`).

Primary-source inspection of `Steel` alongside `Pulse` (`FStarLang/FStar@fc1776afe592ed8eef352c6610614a70d77b3b66`) exposes **three architectural friction points** that motivated `Pulse`:
1. **Proof-in-Type `with_tactic` Coupling (`Steel.Reference.fsti:L260–262`)**: Every `sel r h` occurrence carries `FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)` inside its refinement type, coupling specification elaboration to AC-matching tactics.
2. **Normalizer & SMT Trigger Fragility (`Steel.Effect.Common.fsti:L563, L629`)**: Nested `dtuple2`/product selectors trigger documented `FIXME` SMT pattern failures (`vrefine_sel_eq` and `vrewrite_sel_eq`).
3. **Dual API Duplication (`Steel.Reference.fsti:L54–274`)**: Non-deterministic or relational resources (`ghost_pts_to`, concurrent PCM views) cannot expose a constructive `sel` function without `IndefiniteDescription`, forcing `Steel.Reference` to duplicate every operation (`pts_to`/`read_pt`/`write_pt` vs `vptr`/`read`/`write`, bridged via `intro_vptr`/`elim_vptr`, `L265–274`).

`Pulse` (`PulseCore.InstantiatedSemantics.fsti:L20–123`, `Pulse.Lib.Core.fsti:L26–47`) resolves these by returning to first-order `slprop` predicates annotated with **`[@@@mkey]` syntactic matching keys** (matching resources purely by key unification before checking value equalities, avoiding AC backtracking!) and lightweight `exists*` binders—while sacrificing `Steel`'s single-equation selector ergonomics across pure `if/else` joins.

---

### 4. Unifying VST `withspacer`, `Steel` Selectors, and Canonical `PTree`s in 3-Axiom Lean 4 `theory/`

Basis: source (`joshlf/anneal@c131b320...`: `TrustedBoundary.lean:L442–596`, `Trusted/MirSemantics.lean`, `PureLift/SpatialPin.lean`) + execution (`Probe 2`) + derived

Neither `Steel`'s `with_tactic` refinement types nor `Pulse`'s `[@@@mkey]` custom attribute is admissible inside Anneal's non-TCB `theory/` envelope (`TrustedBoundary.lean:L489–595` bans `byElab`/tactics in types and restricts attributes to `[simp, instance, reducible, semireducible, irreducible]`). Instead, a pure 3-axiom Lean 4 synthesis gets the strengths of all three:
1. **Canonical Positive-Radix `PTree` for `LOCAL` & `SEP`**: Normalizing empty nodes (`PTree.make .leaf none .leaf := .leaf`) guarantees structural extensionality without `funext` or `Classical.choice`, $O(\log_2 M)$ lookups (`5` steps vs `16` at $M=16$ in `Probe 2`), and **`rfl` commutativity** on disjoint updates (`ptree_set(ptree_set(t, 5, A), 12, B) == ptree_set(ptree_set(t, 12, B), 5, A)`).
2. **Total Footprint-Local Selectors (`SpatialVProp`) + `withSpacer`**: Making `sel : MemSeg → α` total over partial maps (returning `Option ByteCell`-derived values on initialized typed fields and `Unit` on `.spacer`/`.uninitRun`/relational locks) removes `hmem` proof obligations from specification terms, while **`join_comm` on disjoint heaplets proves `vpropStar` framing unconditionally** (zero compatibility side-conditions!):

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic

namespace Anneal.CanonSpatial

inductive ByteCell where
  | init (b : UInt8)
  | uninit

abbrev MemSeg := Nat → Option ByteCell

def disjoint (m1 m2 : MemSeg) : Prop :=
  ∀ a, m1 a = none ∨ m2 a = none

def join (m1 m2 : MemSeg) : MemSeg :=
  fun a =>
    match m1 a with
    | some c => some c
    | none   => m2 a

theorem disjoint_sym (m1 m2 : MemSeg) (h : disjoint m1 m2) : disjoint m2 m1 := by
  intro a
  cases h a with
  | inl h1 => exact Or.inr h1
  | inr h2 => exact Or.inl h2

theorem join_comm (m1 m2 : MemSeg) (h : disjoint m1 m2) : join m1 m2 = join m2 m1 := by
  funext a
  dsimp [join]
  cases h a with
  | inl h1 =>
    rw [h1]
    cases m2 a <;> rfl
  | inr h2 =>
    rw [h2]
    cases m1 a <;> rfl

abbrev SlProp := MemSeg → Prop

def sepConj (P Q : SlProp) : SlProp :=
  fun m => Exists fun m1 => Exists fun m2 =>
    m = join m1 m2 ∧ disjoint m1 m2 ∧ P m1 ∧ Q m2

def spacerBlock (be ed : Nat) : SlProp :=
  fun m =>
    ∀ a, (be ≤ a ∧ a < ed → Exists fun c => m a = some c) ∧
         (¬ (be ≤ a ∧ a < ed) → m a = none)

/-- VST `withspacer`: collapses by `rfl` on zero-gap `IntoBytes` layouts (`be = ed`). -/
def withSpacer (be ed : Nat) (P : SlProp) : SlProp :=
  match Nat.beq (ed - be) 0 with
  | true  => P
  | false => sepConj P (spacerBlock be ed)

theorem withSpacer_intoBytes_rfl (P0 P1 : SlProp) :
    sepConj (withSpacer 2 2 P0) (withSpacer 4 4 P1) = sepConj P0 P1 :=
  rfl

/-- Total footprint-local selector (`Steel` `vprop` distilled for 3-axiom Lean 4). -/
structure SpatialVProp (α : Type) where
  own       : SlProp
  sel       : MemSeg → α
  sel_frame : ∀ m1 m2, own m1 → disjoint m1 m2 → sel (join m1 m2) = sel m1

/-- Non-informative selector (`Steel.to_vprop`) for spacers, `.uninit`, and locks. -/
def unitVProp (P : SlProp) : SpatialVProp Unit where
  own := P
  sel _ := ()
  sel_frame _ _ _ _ := rfl

inductive Pos where
  | xH
  | xO (p : Pos)
  | xI (p : Pos)

inductive PTree (α : Type) where
  | leaf
  | node (l : PTree α) (v : Option α) (r : PTree α)

def PTree.make {α : Type} : PTree α → Option α → PTree α → PTree α
  | .leaf, none, .leaf => .leaf
  | l,     v,    r     => .node l v r

structure CanonState (LocalCell SpatialAtom : Type) where
  propHyps : Prop
  locals   : PTree LocalCell
  spatial  : PTree SpatialAtom

end Anneal.CanonSpatial
```

Note on `vpropStar`: because `join_comm` holds for any `disjoint mL mR`, `q.sel (join mL mR) = q.sel (join mR mL) = q.sel mR` and `q.sel (join (join mL mR) m2) = q.sel (join mR (join mL m2)) = q.sel mR`, yielding unconditional star-composition of `SpatialVProp` selectors in pure `Init.*` Lean 4.

Evaluating this unified architecture across Anneal's seven engineering criteria:
1. **Zero-TCB Bridge & `Trusted.*` Gap Analysis**: `CanonState`, `PTree`, `withSpacer`, and `SpatialVProp` reside completely in non-TCB `theory/Anneal/`. Over `joshlf/anneal@c131b320`, `PureLift.SpatialPin` handles only simulated `SpatialBlock` cells (`SpatialPin.lean`); admitting real Rust `&T`, `&mut T`, structs, unions, and raw pointers requires correspondence-verified `Trusted.MirAst` / `Trusted.MirSemantics` extensions (`CallerMemory` non-empty admission at `MirSemantics.lean:L803`, byte-level `AllocByte`/`PtrVal` dereference, `MirTy.struct_`/`.union_`, parametric `LayoutTable` capturing `#[repr(C)]` vs `repr(Rust)` spacing, and `MirTy.isFreeze`).
2. **Human Specification Auditability**: `Steel`-style `sel` equations keep multi-block postconditions quantifier-free (`sel dst m' = ...`), and `withSpacer` hides padding noise completely on `IntoBytes` structs (`rfl`) while making `.uninit` spacers explicit on padded structs under Statement-Origin Separation.
3. **Authoring & Day-2 Edit Locality**: `PROP / LOCAL / SEP` stratification confines arithmetic `rw` to `propHyps`, `PTree` isolates sibling variable edits, and `withspacer_ramif_Q` frames spacers locally across field mutations.
4. **Lean 4 (`v4.34.1`) Kernel & `<50 ms` LSP Scaling**: Replacing `List` scanning with $O(\log M)$ `PTree` lookups, eliminating AC-unification via canonical tries (`rfl` commutativity), and sealing frames with `@[irreducible]` (`TrustedBoundary.lean:L595`) eliminates the $O(N^2)$ spine traversals that stall Lean `whnf`.
5. **Heterogeneous Composability**: Keeps `CanonState.spatial = .leaf` for 100% safe `PureLift` code, populates `withSpacer` `SymSeg` regions on `freezeToSpatialInState`, attaches `unitVProp` (`sel _ := ()`) to `.spacer`, `MaybeUninit`, and `!Freeze` (`UnsafeCell`) invariant-locked regions, and preserves padding-byte conservation across `MirSemantics`'s `TerminalOut.unwound` panic paths.
6. **Failure Legibility**: Trie key lookup failure or uninitialized `[be, ed)` spacer reads report exact `(allocId, be, ed)` offsets rather than opaque unification failures.
7. **Conceptual Minimality & Refuted Premature Collapses**: Unifying `PROP/LOCAL/SEP` + `PTree` + `withSpacer` + `SpatialVProp` removes duplicate `List` frame solvers, ad-hoc `Hold` wrappers, and manual existential skolemization, while four over-collapses fail concrete counterexamples: (i) forcing safe `PureLift` locals into `SEP` spatial maps sacrifices $O(1)$ borrow lifting; (ii) omitting `withspacer` in `struct_pred` either breaks `sizeof` conservation (`memory_block_struct_pred`) or unsoundly preserves padding bytes across typed MIR moves (`Probe 2`); (iii) giving value selectors via `Classical.choice` to `.spacer`/`.uninit` or concurrent `!Freeze` cells fabricates deterministic values over indeterminate bytes; and (iv) C TBAA split-heaps fail soundness under `zerocopy` byte casts and Rust unions.

## Boundaries

- **not examined**: Sub-byte C bitfield packing rules across MSVC vs SysV ABIs inside VST `compspecs` and weak-memory relaxed atomic fences (`PulseCore` / Iris relaxed-memory extensions) were not examined.
- **unknown**: The concrete allocation count $M$ at which Lean 4.34.1 `PTree` path-equality proofs on symbolic keys benefit from `@[irreducible]` subtree sealing under a `<50 ms` LSP interactive budget was not benchmarked in Lean.
- **known not to apply**:
  - `repr(Rust)` structs without `#[repr(C)]` or `#[repr(transparent)]` do **not** have fixed cross-release spacer offsets (`be`, `ed`). As `zerocopy` observes (`zerocopy/src/lib.rs:L1574–1600`), `FromZeros` holds regardless of `repr(Rust)` padding layout (because zeroing initializes all bytes including spacers via `mapsto_zeros_struct_pred`), whereas `IntoBytes` requires zero padding.
  - Typed MIR struct copies/moves do **not** preserve initialized spacer bytes (`Probe 2`).
  - Deterministic value selectors (`sel`) do **not** apply to uninitialized `.spacer`/`.uninit` ranges or concurrently shared `!Freeze` (`UnsafeCell`) memory without invariant/PCM synchronization (`unitVProp`).
- **unsupported**: In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirSemantics` fails closed (`FaultKind.unsupported`) on non-empty `CallerMemory`, `&T`/`&mut T`/pointer entry parameters, `ProjectionElem.deref`, `MirTy` structs/unions, and `CastKind.transmute` (`MirSemantics.lean:L332, L803, L1686–1694`).

## Evidence

### Primary Repositories, Commits, Files, and Publications

| Subject | Exact Identity | Inspected Paths & Anchors |
| :--- | :--- | :--- |
| **VST-Floyd** | `PrincetonUniversity/VST` @ `d50ac1969f9f6586621895eb043ccf08a165f731` | `floyd/canon.v` (`L9–260`); `floyd/entailer.v` (`L97–142`, `L312–349`); `floyd/mapsto_memory_block.v` (`L284–466`); `floyd/field_at.v` (`L124–228`, `L999–1198`); `floyd/data_at_rec_lemmas.v` (`L50–98`); `floyd/aggregate_pred.v` (`L138–160`, `L579–595`, `L1342–1503`) |
| **Steel** | `FStarLang/steel` @ `ff1acec21b5e7ab864aec9901231a5be06116cdd` | `lib/steel/Steel.Memory.fsti` (`L26–111`); `Steel.Effect.Common.fsti` (`L59–144`, `L274–461`, `L543–642`); `Steel.Reference.fsti` (`L54–305`) |
| **Pulse / F\*** | `FStarLang/FStar` @ `fc1776afe592ed8eef352c6610614a70d77b3b66`; `FStarLang/pulse` @ `c35460e00483be17a38397b1594c29a9bf29df15` | `pulse/lib/core/PulseCore.InstantiatedSemantics.fsti` (`L20–123`); `pulse/lib/core/PulseCore.Semantics.fst` (`L33–60`); `pulse/lib/common/Pulse.Lib.Core.fsti` (`L26–47`); `pulse/README.md` (`L1–10`) |
| **zerocopy** | `google/zerocopy` @ `ec133ce4d7993775413d852f91c9e3eb2a2a0897` | `zerocopy/src/lib.rs` (`L1574–1600` `FromZeros`, `L4358–4430` `FromBytes`, `L6005–6085` `IntoBytes`) |
| **Anneal & Lean 4** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/Trusted/MirSemantics.lean` (`L332`, `L803`, `L949–977`, `L1646–1809`); `theory/Anneal/PureLift/{Lens,SpatialPin,MirBridge}.lean` |
| **Literature** | JAR 2018 (`10.1007/s10817-018-9457-5`); CUP 2014 (`10.1017/CBO9781107256552`, `ISBN 978-1-107-04801-0`); ICFP 2020 (`10.1145/3409003`); ICFP 2021 (`10.1145/3473590`); PLDI 2025 (`10.1145/3729311`) | Cao et al., Appel et al., Swamy et al., Fromherz et al., Ebner et al. |

### Executable Probe 2 (`CPython 3.13.15`, `x86_64`, `2026-11-19`)

```python
def typed_struct_move(src_bytes, field_ranges, total_size, deinit_moved=True):
    dst = [None] * total_size
    for lo, hi in field_ranges:
        for i in range(lo, hi):
            if src_bytes[i] is None:
                return ("FAULT_UNINIT_FIELD_READ", None, None)
            dst[i] = src_bytes[i]
    new_src = ([None] * total_size) if (deinit_moved and total_size > 0) else list(src_bytes)
    return ("OK", new_src, dst)

def as_bytes_read(buf):
    return "FAULT_UNINIT_PADDING_READ" if any(b is None for b in buf) else bytes(buf)

def withspacer_atoms(field_ranges, total_size):
    atoms = []
    for idx, (lo, hi) in enumerate(field_ranges):
        next_off = field_ranges[idx + 1][0] if idx + 1 < len(field_ranges) else total_size
        atoms.append(("field", lo, hi))
        if next_off - hi != 0:
            atoms.append(("spacer", hi, next_off))
    return atoms

tight_atoms = withspacer_atoms([(0, 2), (2, 4)], 4)
padded_atoms = withspacer_atoms([(0, 1), (2, 4)], 4)
assert [k for k, _, _ in tight_atoms] == ["field", "field"]
assert padded_atoms == [("field", 0, 1), ("spacer", 1, 2), ("field", 2, 4)]

_, _, tight_dst = typed_struct_move([0x11, 0x22, 0x33, 0x44], [(0, 2), (2, 4)], 4)
_, padded_src_after, padded_dst = typed_struct_move([0x11, 0xAA, 0x33, 0x44], [(0, 1), (2, 4)], 4)
assert as_bytes_read(tight_dst) == b"\x11\x22\x33\x44"
assert padded_dst == [0x11, None, 0x33, 0x44]
assert as_bytes_read(padded_dst) == "FAULT_UNINIT_PADDING_READ"
assert all(b is None for b in padded_src_after)

def ptree_make(l, v, r):
    return None if (l is None and v is None and r is None) else (l, v, r)

def ptree_set(t, pos_bits, val):
    l, v, r = t if t is not None else (None, None, None)
    if pos_bits == 1: return ptree_make(l, val, r)
    if (pos_bits & 1) == 0: return ptree_make(ptree_set(l, pos_bits >> 1, val), v, r)
    return ptree_make(l, v, ptree_set(r, pos_bits >> 1, val))

def ptree_get(t, pos_bits):
    steps = 0
    while t is not None:
        steps += 1
        l, v, r = t
        if pos_bits == 1: return v, steps
        t = l if (pos_bits & 1) == 0 else r
        pos_bits >>= 1
    return None, steps

t_ab = ptree_set(ptree_set(None, 5, "A"), 12, "B")
t_ba = ptree_set(ptree_set(None, 12, "B"), 5, "A")
assert t_ab == t_ba and ptree_set(ptree_set(t_ab, 5, None), 12, None) is None
t16 = None
for k in range(1, 17):
    t16 = ptree_set(t16, k, k * 10)
print("PROBE_2_OK", {
    "tight_spacers": sum(1 for k, _, _ in tight_atoms if k == "spacer"),
    "padded_spacers": sum(1 for k, _, _ in padded_atoms if k == "spacer"),
    "padded_move_as_bytes": as_bytes_read(padded_dst),
    "ptree_comm_rfl": t_ab == t_ba,
    "ptree_empty_collapse": ptree_set(ptree_set(t_ab, 5, None), 12, None) is None,
    "lookup_steps_m16_ptree_vs_list": (max(ptree_get(t16, k)[1] for k in range(1, 17)), 16),
    "join_existentials_k12_m16_indexed_vs_selector": (12 * 16, 0),
})
```

Observed output (`2026-11-19`, `CPython 3.13.15`): `PROBE_2_OK {'tight_spacers': 0, 'padded_spacers': 1, 'padded_move_as_bytes': 'FAULT_UNINIT_PADDING_READ', 'ptree_comm_rfl': True, 'ptree_empty_collapse': True, 'lookup_steps_m16_ptree_vs_list': (5, 16), 'join_existentials_k12_m16_indexed_vs_selector': (192, 0)}`.

## Revalidation

1. **VST-Floyd check:** Fetch `floyd/{canon,mapsto_memory_block,field_at,aggregate_pred}.v` from a newer `PrincetonUniversity/VST` commit and diff `withspacer`, `nested_sfieldlist_at`, and `memory_block_struct_pred` against `d50ac1969f9f6586621895eb043ccf08a165f731`.
2. **Steel / Pulse check:** Diff `Steel.Effect.Common.fsti` (`FStarLang/steel`) and `pulse/lib/common/Pulse.Lib.Core.fsti` (`FStarLang/FStar`) to verify whether `Steel` added tactic-free selector keys or `Pulse` added selector projections atop `[@@@mkey]`.
3. **Anneal & Lean kernel check:** Inspect `Trusted/MirSemantics.lean` for byte-level `CallerMemory` / ADT support and compile `Anneal.CanonSpatial` under `lean` (`v4.34.1`, `--trust=0`) plus Anneal's boundary auditor to confirm zero errors and `{propext, Quot.sound, Classical.choice}` closure.
4. **Executable probe:** Run the Python 3 script in **Evidence** (`python3` $\ge 3.10$) and verify `PROBE_2_OK` prints with exit code `0`.
