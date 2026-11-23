# Rustc HIR Method Resolution: Autoderef-Step-First Precedence, E0034 Ambiguity vs. Cross-Step Shadowing, Arbitrary Self Types (`Receiver`), and `zerocopy` Dispatch

## Summary

This report establishes primary-source, empirical (`rustc` + `Miri` + `--emit=mir`), and kernel-checked (`Lean v4.34.1`) ground truth for `rustc_hir_typeck` method resolution (`compiler/rustc_hir_typeck/src/method/{probe,confirm,suggest}.rs`), `Autoderef` / well-formedness checking (`compiler/rustc_hir_analysis/src/{autoderef,check/wfcheck}.rs`), `core::ops::Receiver` dispatch, and first-customer wrapper patterns in `google/zerocopy` (`Ptr`, `Unalign`, `ReadOnly`):

1. **Method probing is strictly lexicographic in `(step_index, adjustment_stage, candidate_bucket)` over stable candidates first, then unstable candidates — never depth-first per trait or inherent-first across steps.**
   `method_autoderef_steps` (`probe.rs:655-821`) materializes the `Deref` chain (plus, when `#![feature(arbitrary_self_types)]` or `#![feature(arbitrary_self_types_pointers)]` is enabled, the potentially longer `Receiver` chain tagged via `zip` with `reachable_via_deref = false` beyond the `Deref` prefix), tagging every step after a raw pointer with `from_unsafe_deref = true` and appending **at most one** trailing `unsize = true` step `[T; N] -> [T]` only when `autoderef_via_deref.final_ty()` is an array `ty::Array(elem_ty, _)`. `pick_core` (`probe.rs:1319-1344`) runs `pick_all_method` first filtering unstable candidates (`unstable_candidates: Some(Vec::new())`) and falls back to a second pass including unstable candidates only on `None`. Across filtered steps (`step.reachable_via_deref && !step.self_ty.value.references_error() && !step.from_unsafe_deref`), `pick_all_method` (`probe.rs:1351-1479`) returns on the **first** step producing any `Some(PickResult)`, probing stages in the invariant sequence `by_value` (skipped if `unsize`) -> `autoref(Not)` -> `autoref(Mut)` -> `const_ptr` (`*mut T -> *const T`, skipped if `unsize`) -> `reborrow_pin` (`Pin<&mut T> -> Pin<&T>`, `pin_ergonomics`), and checking `self.inherent_candidates` (`InherentImplCandidate`, `ObjectCandidate`, `WhereClauseCandidate`) strictly before `self.extension_candidates` (`TraitCandidate`) inside each `(step, stage)` slot. Consequently:
   - Step `0` `&self` **extension** beats step `0` `&mut self` **inherent**;
   - Step `0` `&self` or `&mut self` **extension** beats step `1` `self` or `&self` **inherent**;
   - Probe ignores expression place mutability: calling an `&mut self` inherent method at step `0` on an immutable binding wins probe and fails downstream borrow-checking with **`E0596`** rather than backtracking to a step-1 `&self` method;
   - Raw pointers `*mut T` / `*const T` include dereference steps in `self.steps` solely to assemble pointee inherent candidates, never as callable receivers (`E0599` for pointee methods); `*mut T` can coerce once to `*const T` via `ToConstPtr` at step `0` after `autoref(Mut)` misses, cannot chain `&*const T` (`E0599`), and `*mut [T; N]` cannot combine unsizing with `ToConstPtr` (`E0599`).

2. **`E0034` ambiguity is a strictly intra-slot collision, whereas cross-step shadowing and early-stage preference are silent by construction.**
   `consider_candidates` (`probe.rs:1783-1858`) raises `MethodError::Ambiguity` (`E0034`, `suggest.rs:334-357`) only when `> 1` candidates survive in the **exact same** `(step, adjustment_stage, bucket)` slot:
   - Before unstable-candidate filtering, `collapse_candidates_to_trait_pick` (`probe.rs:2391-2428`) collapses `>= 2` `TraitCandidate` picks that all share the same `trait_container` (e.g., `Wrap<?0>` with ambiguous blanket/concrete impls) directly into a single `TraitPick`, deferring obligation resolution.
   - After unstable filtering, if `> 1` candidates remain and `#![feature(supertrait_item_shadowing)]` is disabled, `E0034` fires immediately (short-circuiting both later `extension` candidates if ambiguity occurred in `inherent`, and all later `steps`). Enabling `supertrait_item_shadowing` activates `collapse_candidates_to_subtrait_pick` (`probe.rs:2439-2514`, RFC #3624), resolving subtrait-over-supertrait collisions with a lint while still rejecting unrelated traits with `E0034`.
   - Two overlapping generic inherent impls (`impl<T> Gen<T, u32>` vs `impl<U> Gen<u32, U>`) trigger `E0592` alongside `E0034` inside `inherent_candidates` without falling back to traits; `WhereClauseCandidate` (`T: T1 + T2`) and `ObjectCandidate` (`&dyn Combined`) trigger pure `E0034` inside `inherent_candidates` without `E0592`.
   - Conversely, candidates in strictly different `(step, adjustment_stage, bucket)` slots never collide under standard `Deref` rules — the lexicographically earlier slot silently shadows all later ones.

3. **`#![feature(arbitrary_self_types)]` decouples well-formed `self` chains (`Receiver::Target`) from deref reachability (`Deref`) and adds an asymmetric, niche-bypassable `E0034` anti-shadowing guard.**
   In `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1752-2021`, enabling `arbitrary_self_types` switches `receiver_is_valid` from `Deref + LegacyReceiver` to `Autoderef::use_receiver_trait()`, relying on the blanket `impl<P: ?Sized, T: ?Sized> Receiver for P where P: Deref<Target = T>` (`library/core/src/ops/deref.rs:379-385`). Custom smart pointers implementing only `Receiver<Target = Target>` allow `impl Target { fn m(self: SmartOnly<Self>) }` and `impl Target { fn m(self: &SmartOnly<Self>) }` to type-check and resolve on `SmartOnly<Target>` at step `0`, while calling `Target::m(&self)` fails with `E0599` because step `1` (`Target`) has `reachable_via_deref = false`. To prevent smart pointers from silently hijacking pointee methods, `pick_all_method` calls `check_for_shadowed_autorefd_method` (`probe.rs:1496-1581`) on `InherentImplPick` picks at `by_value` (checking `{Not, Mut}`) and `autoref(Not)` (checking `{Mut}`): if another inherent candidate at equal `autoderefs` has `candidate.receiver_steps > shadowed.receiver_steps`, `rustc` raises `E0034`. This check is provably **asymmetric** (`Target::m(self: SmartPtr<Self>)` silently shadows `SmartPtr::m(&self)` because `0 > 1` is false), bypassed in the documented **double-reference niche** (`SmartPtr::m(&self)` called on `&SmartPtr<Target>` increments `pick.autoderefs` to `1` while `step.autoderefs == 0`, silently shadowing `Target::m(self: &&SmartPtr<Self>)`), and **exempt on `const_ptr`** (`RawWrap::m(self: *mut Self)` silently shadows `Target::m(self: *const RawWrap<Self>)`).

4. **Real `zerocopy` wrappers (`Ptr`, `Unalign`, `ReadOnly`) exploit these exact method-probe invariants (`google/zerocopy@e8dcb7f0`).**
   `Ptr<'a, T, I>` (`zerocopy/src/pointer/ptr.rs:57-300`) omits `Deref` intentionally so referent methods are unreachable (`E0599`) while `Ptr::as_ref(self)` (step `0`, `by_value`, `inherent`) beats any `&self` trait extension without ambiguity. `Unalign<T>` (`zerocopy/src/wrappers.rs:118-421`) defines inherent `get(&self)` at step `0` (shadowing `[u8; 4]`/`ReferentGet::get(&self)`) alongside conditional `impl<T: Unaligned> Deref`, enabling `Unalign<[u8; 4]>::len()` to walk `Deref -> [u8; 4]` then unsize via `PointerCoercion::Unsize` to `[u8]::len` while failing closed (`E0599`) on `Unalign<[u32; 4]>`. `ReadOnly<T>` (`wrappers.rs:627-815`) omits `&self` inherent methods (`into_inner(r)` / `as_mut(r)` are associated functions!) precisely so inherent step-0 methods never shadow `<T as Deref>::Target` methods when `T: Immutable`, and exposes `AsRef<T>::as_ref(&self)` cleanly at step `0` `extension` without blocking slice unsizing.

5. **Full empirical and Lean `v4.34.1` verification plus fail-closed Anneal MIR boundary (`joshlf/anneal@c131b320e`).**
   All 26 `rustc 1.98.0-nightly (14210df0e)` compile/run/diagnostic probes, 3 `--emit=mir` lowerings, and 4 `Miri` Stacked Borrows / `-Zmiri-tree-borrows` executions pass cleanly (`support/probe_results.json`), confirming identical resolution across runtime models and capturing exact `Unsize`, `<T as Deref>::deref`, and `Ptr::reborrow` / `as_ref` MIR. The 2,758-line pure constructive Lean `v4.34.1` formalization (`support/HirMethodResolutionAutoderefSoundness.lean`: 46 `noncomputable def`s, 72 user theorems, 0 `sorry`, 0 `Classical.choice`, 0 `omega`/`bv_decide`/`native_decide`/`partial def`, and 0 `._unsafe_rec` constants verified via Lean MetaM) proves outcome trichotomy, step-lexicographic optimality and antisymmetric uniqueness, step-0 extension vs. step-1/`&mut` precedence, same-step `E0034` vs. cross-step shadowing, `Receiver`-chain isolation and asymmetric anti-shadowing/bypass theorems, `unsize` termination/uniqueness, `zerocopy` dispatch invariants, and fail-closed rejection across `joshlf/anneal`'s current `Trusted.MirAst` / `Trusted.MirSemantics` boundary.

---

## Applicability

This report documents five pinned, independently resolvable upstream subjects recorded in `REPORT.json`:

| Subject | Repository | Immutable Revision | Role in This Report |
| :--- | :--- | :--- | :--- |
| Upstream `rustc` and `core` source | `rust-lang/rust` | `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` (`main`) | Primary-source audit of method probing, confirmation, error diagnostics, `Autoderef`, `wfcheck`, and `core::ops::Receiver`. |
| Executed `rustc` nightly and `Miri` toolchain | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, LLVM `22.1.6`, `miri 0.1.0`) | Live native compilation, `--emit=mir` inspection, diagnostic capture (`E0034`/`E0596`/`E0599`/`E0592`), `Miri` SB/TB execution, and source diff vs. `0259d5e9`. |
| Upstream `zerocopy` crate source | `google/zerocopy` | `e8dcb7f08edbc19485c9e7980333607ebbff5f48` (`main`) | Primary-source inspection of `Ptr`, `Unalign`, and `ReadOnly` method signatures, `Deref` bounds, and `AsRef` impls (`zerocopy/src/{pointer/ptr.rs,wrappers.rs}`). |
| Anneal trusted MIR semantics and `rustc-capture` | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main`) | Primary-source audit of `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/rustc-capture/src/driver.rs`. |
| Lean 4 proof kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel type-checking and MetaM axiom / `_unsafe_rec` audit of `support/HirMethodResolutionAutoderefSoundness.lean`. |

### Relationship Among Subjects and Version Scope

- **Stable vs. nightly Rust applicability:** All core autoderef-step-first method resolution rules (`method_autoderef_steps` `Deref` walk + trailing `[T; N] -> [T]` unsize step, `by_value -> autoref(Not) -> autoref(Mut) -> const_ptr` per step, `inherent` before `extension` per `(step, stage)`, `collapse_candidates_to_trait_pick`, `E0034` same-slot collisions vs. cross-step shadowing, raw-pointer `from_unsafe_deref` filtering, two-phase mutable autoref confirmation, and `zerocopy` `Ptr`/`Unalign`/`ReadOnly` dispatch) apply identically on **stable Rust** (`--edition=2024`, zero crate `#![feature(...)]` flags required).
- **Unstable feature-gated mechanisms explicitly scoped in probes and Lean theorems:**
  - `#![feature(arbitrary_self_types)]`: enables custom non-`Deref` `Receiver<Target = T>` chains, `wfcheck` `Receiver` acceptance, and `check_for_shadowed_autorefd_method`;
  - `#![feature(arbitrary_self_types_pointers)]`: enables `*const Self` and `*mut Self` receivers without `Receiver`, and exercises the raw-pointer `*mut` anti-shadowing exemption (`RawWrap::*mut`);
  - `#![feature(pin_ergonomics)]`: enables `AutorefOrPtrAdjustment::ReborrowPin` (`pick_reborrow_pin_method` on `Pin<&mut T>` -> `Pin<&T>`);
  - `#![feature(supertrait_item_shadowing)]`: enables `collapse_candidates_to_subtrait_pick` (RFC #3624) with `#![warn(resolving_to_items_shadowing_supertrait_items)]`.
- **Cross-revision continuity between executed `rustc 1.98.0-nightly` (`14210df0e`) and `rust-lang/rust` `main` (`0259d5e9`):** Direct source diffing across all audited compiler and `core` files confirms exact semantic equivalence across every examined rule (Finding 7 details the structural deltas, primarily `ProbeScope::Single(DefId, Option<Ty>)` for `fn_delegation` and named fields on `TraitCandidate` / `TraitPick`, none of which alter method precedence or autoderef chains).
- **Standalone Lean model vs. `joshlf/anneal`:** `support/HirMethodResolutionAutoderefSoundness.lean` is a standalone pure-`Init` Lean 4 formalization of the extracted HIR method-probe state machine, `zerocopy` receiver examples, and Anneal fail-closed projection (`classifyPickInAnneal`), rather than importing `Trusted.MirSemantics` directly (which currently halts on `.deref`, `.cast(Unsize | MutToConstPointer)`, retags, and `.call`).

---

## Findings

### 1. Upstream Architecture: `method_autoderef_steps`, `ProbeContext`, and Two-Pass Lexicographic Probing

Basis: source + execution

In `rustc_hir_typeck`, method resolution runs in two decoupled phases: **(A)** cached query construction of the receiver conversion sequence (`method_autoderef_steps`), followed by **(B)** two-bucket candidate assembly (`inherent_candidates`, `extension_candidates`) and two-pass lexicographic search (`pick_core` -> `pick_all_method` -> `pick_method` -> `consider_candidates`).

#### 1.1 `Autoderef` Iterator Semantics (`autoderef.rs:33-108`)

`Autoderef<'a, 'tcx>` (`compiler/rustc_hir_analysis/src/autoderef.rs:33-47`) lazily yields `(Ty<'tcx>, usize)` pairs starting with `(base_ty, 0)` while `at_start` is true (`lines 56-60`). On each subsequent call to `next()`:
1. Enforces `tcx.recursion_limit().value_within_limit(self.state.steps.len())` (`lines 63-69`), setting `reached_recursion_limit = true` on overflow.
2. Stops immediately on non-opaque type inference variables (`ty::Infer(ty::TyVar(vid))` when `!infcx.has_opaques_with_sub_unified_hidden_type(vid)`, `lines 76-80`) so method lookup does not guess dereferences for unconstrained `{unknown}` variables.
3. Attempts a **built-in** dereference first via `cur_ty.builtin_deref(self.include_raw_pointers)` (`lines 88-90`, covering `&T`, `&mut T`, and when enabled `*const T`, `*mut T` — notably built-in derefs run *even when* `use_receiver_trait = true` so `&T`/`&mut T` avoid unnecessary overloaded trait projections, `lines 83-86`).
4. Otherwise calls `self.overloaded_deref_ty(cur_ty)` (`lines 91-93`), which projects `<cur_ty as Receiver>::Target` if `use_receiver_trait` is set, else `<cur_ty as Deref>::Target`, normalizing obligations in `infcx`.

#### 1.2 `method_autoderef_steps` and the Unique Trailing `Unsize` Step (`probe.rs:655-821`)

`method_autoderef_steps` (`compiler/rustc_hir_typeck/src/method/probe.rs:655-821`) builds the `steps: &'tcx [CandidateStep]` slice as follows:

- It always initializes `autoderef_via_deref = Autoderef::new(...).include_raw_pointers().silence_errors()` (`lines 706-709`). Notice `.include_raw_pointers()` is **always** passed to `Autoderef`, even on stable Rust.
- **Standard mode (`!arbitrary_self_types && !arbitrary_self_types_pointers`, `lines 748-771`):** It iterates `autoderef_via_deref`, emitting `CandidateStep { self_ty, autoderefs: d, from_unsafe_deref: reached_raw_pointer, unsize: false, reachable_via_deref: true }`, and sets `reached_raw_pointer = true` **after** emitting the raw pointer step itself whenever `ty.is_raw_ptr()` is true (`lines 763-766`). Thus `*const Pointee` / `*mut Pointee` appears at `d = 0` with `from_unsafe_deref = false`, while pointee `Pointee` appears at `d = 1` with `from_unsafe_deref = true`.
- **Arbitrary Self Types mode (`lines 714-747`):** It zips `autoderef_via_receiver` (constructed with `.include_raw_pointers().use_receiver_trait()`) against the boolean stream `autoderef_via_deref.by_ref().map(|_| true).chain(std::iter::repeat(false))`. Because `core::ops::Deref` implies `core::ops::Receiver` via the blanket impl (`core/src/ops/deref.rs:380-385`), the `Deref` chain forms an exact prefix with `reachable_via_deref = true`, while strictly `Receiver`-only hops receive `reachable_via_deref = false`.
- **Trailing array-to-slice unsize step (`lines 790-809`):** After exhausting `autoderef_via_deref`, it checks **`final_ty = autoderef_via_deref.final_ty()`**:

```rust
ty::Array(elem_ty, _) => {
    let autoderefs = steps.iter().filter(|s| s.reachable_via_deref).count() - 1;
    steps.push(CandidateStep {
        self_ty: infcx.make_query_response_ignoring_pending_obligations(
            inference_vars,
            Ty::new_slice(infcx.tcx, *elem_ty),
            prev_opaque_entries,
        ),
        self_ty_is_opaque: false,
        autoderefs,
        from_unsafe_deref: reached_raw_pointer,
        unsize: true,
        reachable_via_deref: true,
    });
    None
}
```

Four load-bearing consequences follow directly from lines `772-809`:
1. If `final_ty` is `[T; N]`, **at most one** `unsize: true` step (`[T]`) is ever appended at the very end, reusing the array step's `autoderefs` count (`reachable_via_deref.count() - 1`) and inheriting `reached_raw_pointer` (so a raw `*mut [T; N]` / `*const [T; N]` sets `from_unsafe_deref = true` on `[T]` and blocks slice method calls).
2. Unsizing uses `autoderef_via_deref.final_ty()`, **not** `autoderef_via_receiver.final_ty()`: a `SmartOnly<[u8; 4]>` implementing `Receiver` without `Deref` does not terminate `autoderef_via_deref` at `[u8; 4]` (it stops at `SmartOnly<[u8; 4]>`), so no `unsize: true` `[u8]` step is appended (`support/probe_results.json`).
3. If the receiver starts as `[u8; 4]`, step `0` is `[u8; 4]` (`unsize: false, autoderefs: 0`) and step `1` is `[u8]` (`unsize: true, autoderefs: 0`).
4. If the receiver is `OwnedArr` with `impl Deref for OwnedArr { type Target = [u8; 4]; }`, step `0` is `OwnedArr`, step `1` is `[u8; 4]`, and step `2` is `[u8]` (`unsize: true, autoderefs: 1`). Array trait methods on step `1` (`ArrayOverride::len`, `ArrayOverride::custom_arr`) therefore precede slice inherent/trait methods on step `2` (`<[u8]>::len`, `SliceFallback::custom_arr`), whereas `Box<[u8; 5]>` with no overriding `[u8; 5]` trait falls through step `0` to the trailing `unsize` slice step (`OA_OVR=ArrayOverride::[u8;4]`, `OA_SLICE=4`, `OA_TRAIT=404`, `BOX_LEN=5` in `a_matrix`).

#### 1.3 Candidate Assembly Across All Steps (`probe.rs:887-1215`)

`ProbeContext` partitions candidates into three vectors (`lines 887-895`):
- `inherent_candidates`: populated by `assemble_inherent_candidates` (`lines 898-1083`), which iterates **every** `step` in `self.steps` (including `reachable_via_deref = false` and `from_unsafe_deref = true` steps!) and collects:
  - `InherentImplCandidate { impl_def_id, receiver_steps: step.autoderefs }` for `Adt`, `Foreign`, `&dyn`, and primitive/incoherent types;
  - `ObjectCandidate(trait_ref)` for `&dyn Trait` supertraits (`lines 1027-1056`);
  - `WhereClauseCandidate(poly_trait_ref)` for type-parameter `ty::Param` bounds (`lines 1060-1083`).
- `extension_candidates`: populated by `assemble_extension_candidates_for_traits_in_scope` (`lines 1107-1215`) once from `tcx.in_scope_traits(scope_expr_id)` (`TraitCandidate { trait_ref, is_ambiguously_imported }`), including trait alias expansion (`expand_trait_aliases`, `lines 1163-1189`).
- `private_candidates`: collected whenever visibility fails so `E0624` private-method diagnostics only trigger if no public candidate matches (`lines 887-895, 1766-1779`).

#### 1.4 Two-Pass Search (`pick_core` -> `pick_all_method`, `probe.rs:1319-1479`)

`pick_core` (`lines 1319-1344`) performs up to two passes of `pick_all_method`:
- **Pass 1 (`unstable_candidates: Some(Vec::new())`):** Inside `consider_candidates` (`lines 1822-1832`), any candidate flagged `eval_stability == Deny` is recorded for unstable-collision diagnostics and **removed** (except note the `collapse_candidates_to_trait_pick` ordering quirk in Finding 3.2).
- **Pass 2 (`unstable_candidates: None`):** Executed `.or_else(|| ...)` **only if** Pass 1 returns `None` across every step, retrying with unstable candidates enabled.

Within `pick_all_method` (`lines 1346-1479`):
```rust
self.steps
    .iter()
    .filter(|step| step.reachable_via_deref)
    .filter(|step| !step.self_ty.value.references_error() && !step.from_unsafe_deref)
    .find_map(|step| { ... })
```
Because `.find_map` terminates on the **first** `Some(PickResult<'tcx>)` (whether `Ok(Pick)` or `Err(Ambiguity | BadReturnType)`), Rust's method lookup establishes a **strict lexicographic order**:
$$(\text{step\_index},\; \text{AdjustmentStage},\; \text{CandidateBucket})$$
where:
1. `step_index`: $0 < 1 < \dots < n-1$ among steps passing `reachable_via_deref && !from_unsafe_deref && !references_error`,
2. `AdjustmentStage`: $\text{ByVal}(0) < \text{Autoref}(\text{Not})(1) < \text{Autoref}(\text{Mut})(2) < \text{ConstPtr}(3) < \text{ReborrowPin}(4)$,
3. `CandidateBucket`: $\text{Inherent}(0) < \text{Extension}(1)$.

---

### 2. Per-Step Adjustment Order, Confirmation Adjustments, and Why Place Mutability Does Not Backtrack

Basis: source + execution

#### 2.1 Five Adjustment Stages Per Step (`probe.rs:1589-1739`, `confirm.rs:201-292`)

At a fixed eligible `step`, `pick_all_method` invokes up to five stage helpers:

| Rank | Stage (`probe.rs`) | Guard / Skip Condition | Pick `autoderefs` & `AutorefOrPtrAdjustment` | MIR / HIR Adjustment (`confirm.rs:201-292`) |
| :---: | :--- | :--- | :--- | :--- |
| `0` | `pick_by_value_method` (`1589-1631`) | Returns `None` immediately if `step.unsize == true`. | Normally `(step.autoderefs, None)`. **Special reborrow case:** if `*step.self_ty` is `ty::Ref(_, _, mutbl)`, increments **`pick.autoderefs += 1`** and sets `Autoref { mutbl, unsize }`! If `pin_ergonomics` + `Pin<&'a mut T>`, sets `ReborrowPin(mutbl)`. | `Adjust::Deref` (`autoderefs`) + optional `Adjust::Borrow(AutoBorrow::Ref(mutbl, AllowTwoPhase::Yes))` on `&T`/`&mut T` reborrow |
| `1` | `pick_autorefd_method(..., Not)` (`1633-1668`) | Always probed with `&self_ty`. | `(step.autoderefs, Some(Autoref { mutbl: Not, unsize: step.unsize }))` | `autoderef.nth(autoderefs)` + `Borrow(Ref(Not, TwoPhase))` + optional `PointerCoercion::Unsize` if `step.unsize` |
| `2` | `pick_autorefd_method(..., Mut)` (`1454-1461, 1633-1668`) | Always probed with `&mut self_ty`. | `(step.autoderefs, Some(Autoref { mutbl: Mut, unsize: step.unsize }))` | `autoderef.nth(autoderefs)` + `Borrow(Ref(Mut, TwoPhase))` + optional `PointerCoercion::Unsize` if `step.unsize` |
| `3` | `pick_const_ptr_method` (`1713-1739`) | Returns `None` if `step.unsize == true` OR `*step.self_ty` is not `RawPtr(ty, Mut)`. | `(step.autoderefs, Some(ToConstPtr))` | `autoderef.nth(autoderefs)` + `Adjust::Pointer(PointerCoercion::MutToConstPointer)` |
| `4` | `pick_reborrow_pin_method` (`1672-1708`) | Returns `None` unless `pin_ergonomics` is enabled AND `self_ty` is `Pin<&mut T>`. | `(step.autoderefs, Some(ReborrowPin(Not)))` | `Adjust::Deref(DerefAdjustKind::Pin)` + `Adjust::Borrow(AutoBorrow::Pin(Not))` |

Three subtle interaction rules documented in `AutorefOrPtrAdjustment` and `pick_by_value_method` (`probe.rs:139-143, 1596-1617, 1721`) are verified empirically by `support/probe_method_resolution_autoderef.py`:

1. **No chained `ToConstPtr` + `Autoref`, and `by_value` precedes `ToConstPtr`:** `probe.rs:139-143` explicitly notes that `rustc` never chains `T -> &T -> *const T` or `*mut T -> *const T -> &*const T`. In `a_raw_ptr_to_const_no_chained_autoref_e0599`, calling `p.on_const_ptr_ref()` (`impl ConstPtrTrait for *const Target { fn on_const_ptr_ref(&self) -> u32 }`) on `p: *mut Target` fails with **`E0599`**. Conversely, `p.only_const()` (`fn only_const(self: *const Self)`) succeeds via `ToConstPtr` (`TO_CONST_PTR=77`), and when `Target::prefer_mut(self: *mut Self)` (`inherent`, stage `0` `by_value`) competes against `FallbackConst::prefer_mut(self: *const Self)` (`extension`, stage `3` `const_ptr`), step-0 `by_value` `*mut Self` wins cleanly (`PREFER_MUT=mut_ptr_by_val` in `a_raw_ptr_to_const_positive`).
2. **`step.unsize` blocks `by_value` and `const_ptr`:** Both `pick_by_value_method` (`line 1596`) and `pick_const_ptr_method` (`line 1721`) begin with `if step.unsize { return None; }`. Thus on `p: *mut [u8; 4]`, although `ToConstPtr` exists (`*mut -> *const`), `p.slice_const_ptr()` (`fn slice_const_ptr(self: *const [u8])`) fails with **`E0599`** (`a_unsize_skips_by_value_and_const_ptr_e0599`), and unsized slice methods can only take `&[T]` or `&mut [T]` (`autoref(Not)` / `autoref(Mut)`).
3. **`pick_by_value_method` `ty::Ref` reborrowing preserves `&mut T` ownership while `&mut T -> &T` coercions wait until step `1` (`probe.rs:1599-1617`):** In `a_matrix`, `RefStep(u32)` derives `Clone, Copy`, implements inherent `by_val(self)` and `m_val_or_ref(self)`, and implements traits `RefStepRef` (`by_val(&self)`, `m_val_or_ref(&self)`, `reborrow_or_ref(&self)`) and `RefStepMut` (`reborrow_or_ref(&mut self)`):
   - **`V3`/`V3B` (`r_mut: &mut RefStep`, calling `r_mut.reborrow_or_ref()` twice):** At step `0` (`self_ty = &mut RefStep`), `pick_by_value_method` sees `*step.self_ty` is `ty::Ref(_, _, Mut)`. Because `RefStepMut::reborrow_or_ref(&mut self)` accepts `&mut RefStep` directly, `rustc` matches it at stage `0` (`by_value`), **increments `pick.autoderefs` from `0` to `1`**, and sets `Autoref { mutbl: Mut, unsize: false }` so the call reborrows `r_mut` rather than moving it (`V3=RefStepMut::&mut self`), beating `RefStepRef::reborrow_or_ref(&self)` at step `1`. Calling `r_mut.reborrow_or_ref()` immediately afterward (`V3B`) compiles cleanly, confirming ownership preservation.
   - **`V4` (`r_mut: &mut RefStep`, calling `r_mut.m_val_or_ref()`):** Neither `RefStep::m_val_or_ref(self)` nor `RefStepRef::m_val_or_ref(&self)` accepts `&mut RefStep` directly in `pick_by_value_method`, and `pick_autorefd_method(..., Not)` probes `&&mut RefStep` (not coerced `&RefStep`). Probe therefore advances to step `1` (`RefStep`), where stage `0` (`by_value`, copying the `Copy` struct) selects `RefStep::by_val(self)` (`V4=RefStep::by_val(self)`) ahead of `RefStepRef::&self` (`stage 1`).
   - **`V5` (`r_imm: &RefStep`, calling `r_imm.reborrow_or_ref()`):** Step `0` (`&RefStep`) matches `RefStepRef::reborrow_or_ref(&self)` directly inside `pick_by_value_method` (`autoderefs += 1`, `Autoref { mutbl: Not }`) without advancing to step `1` (`V5=RefStepRef::&self`).

#### 2.2 Complete 17-Cell Empirical Autoderef & Adjustment Matrix (`a_matrix`, `rustc 1.98.0-nightly` + `Miri`)

Execution (`support/probe_method_resolution_autoderef.py`, identical stdout under native `rustc`, Miri Stacked Borrows, and Miri `-Zmiri-tree-borrows`, `rc = 0`):

| Cell | Receiver Expr Type | Competing Candidates | Observed Winner (`stdout`) | Exact Winning `(step, stage, bucket)` |
| :--- | :--- | :--- | :--- | :--- |
| `A1` | `Outer(Inner)` | `OuterTrait::trait(&self)` vs `Inner::inherent(&self)` | `OuterTrait::trait(&self)` | `(0, autoref(Not), Ext)` beats `(1, autoref(Not), Inh)` |
| `A2` | `Outer(Inner)` (`o1`) | `Outer::val_vs_ref(&self)` vs `Inner::val_vs_ref(self)` | `Outer::inherent(&self)` | `(0, autoref(Not), Inh)` beats `(1, by_value, Inh)` |
| `A3` | `Outer` | `OuterByVal::trait(self)` vs `Outer::inherent(&self)` | `OuterByVal::trait(self)` | `(0, by_value, Ext)` beats `(0, autoref(Not), Inh)` |
| `A4` | `Outer` | `OuterTrait::trait(&self)` vs `Outer::ref_vs_mut(&mut self)` | `OuterTrait::trait(&self)` | `(0, autoref(Not), Ext)` beats `(0, autoref(Mut), Inh)` |
| `A5` | `mut Outer` | `Outer::only_mut(&mut self)` vs `InnerTrait::m(&self)` | `Outer::only_mut(&mut self)` | `(0, autoref(Mut), Inh)` beats `(1, autoref(Not), Ext)` |
| `A6` | `mut Outer` | `Inner::only_inner_mut(&mut self)` (`Inner` only) | `Inner::mut(&mut self)` | `(1, autoref(Mut), Inh)` |
| `V1`–`V5` | `RefStep` / `&RefStep` / `&mut RefStep` | `RefStep::by_val(self)` / `RefStepRef(&self)` / `RefStepMut(&mut self)` | `V1=by_val`, `V2=&self`, `V3=&mut`, `V3B=&mut`, `V4=by_val`, `V5=&self` | `V2`: step-0 `&self` beats `&mut self`; `V3`/`V3B`: step-0 `by_value` `&mut` reborrow; `V4`: step-1 `by_val(self)` beats `&self`; `V5`: step-0 `by_value` `&` copy/reborrow |
| `OA_*` | `OwnedArr` (`Deref<Target=[u8;4]>`) / `[u8;4]` / `Box<[u8;5]>` | Slice inherent `[u8]::len` vs `[u8;4]` `ArrayOverride` trait | `OA_SLICE=4`, `OA_TRAIT=404`, `OA_OVR=ArrayOverride::[u8;4]`, `BOX_LEN=5` | `step 0 (OwnedArr) < step 1 ([u8;4]) < step 2 ([u8], unsize=true)` |
| `W` | `T: WhereBound` + `BlanketExt` (`fn w(&self)` on both) | `WhereClauseCandidate(T: WhereBound)` vs `TraitCandidate(BlanketExt)` | `W=WhereBound::inherent_priority` | `WhereClauseCandidate` lives in `inherent_candidates` (`bucket 0 < bucket 1`)! |
| `PIN` | `Pin<&mut Pinned>` (`#![feature(pin_ergonomics)]`) | `Pinned` method taking `Pin<&Self>` | `PIN_REBORROW=110` | Stage 4 (`reborrow_pin`) at step `0` |

#### 2.3 Why Method Probing Ignores Place Mutability (`E0596`) and Uses Two-Phase Borrows (`confirm.rs:230`)

Because `pick_all_method` matches purely on **types** in `ProbeContext`, it never inspects whether the receiver place expression (`o`) is declared `mut`. In `a_probe_ignores_place_mutability_e0596`, `let o = Outer(Inner);` has immutable binding `o`, while `Outer` defines `fn m(&mut self)` (step `0`, stage `2`) and `Inner` defines `fn m(&self)` (step `1`, stage `1`). `rustc` commits to `Outer::m` at step `0` during HIR probe and later emits **`error[E0596]: cannot borrow o as mutable, as it is not declared as mutable`** (`support/probe_results.json`), never backtracking to `Inner::m(&self)`.

Furthermore, during confirmation (`confirm.rs:230`), **every** `Autoref` adjustment is constructed with `AutoBorrowMutability::new(mutbl, AllowTwoPhase::Yes)` (explicitly commented: *"Method call receivers are the primary use case for two-phase borrows"*), allowing `v.push(v.len())`-style nested argument borrows to evaluate after reserving the `&mut` receiver borrow before activating it at the call boundary.

---

### 3. Candidate Assembly, Same-Step `E0034` Ambiguity Collisions, Trait/Subtrait Collapsing, and Cross-Step Shadowing

Basis: source + execution

#### 3.1 When `consider_candidates` Raises `E0034` vs. Silent Shadowing (`probe.rs:1783-1858, suggest.rs:334-357`)

Whenever `consider_candidates` (`probe.rs:1783-1858`) collects `applicable_candidates` for a single `(step, stage, bucket)` triple:
1. If `applicable_candidates.len() > 1`, it first calls `collapse_candidates_to_trait_pick` (`lines 2391-2428`). If every candidate is a `TraitCandidate` whose `item.trait_container(tcx)` is identical (common when an inference variable `Wrap<?0>` matches multiple concrete impls of the same trait `SameTrait`), `consider_candidates` returns `Some(Ok(Pick { kind: TraitPick { is_ambiguously_imported }, .. }))` **immediately** — **even before filtering unstable candidates** (`lines 1814-1832`)! In `inference_deferred_same_trait_collapse`, `rustc` confirms this resolves `COLLAPSE_SAME_TRAIT=0` cleanly.
2. Otherwise, Pass 1 removes `eval_stability == Deny` candidates (`lines 1822-1832`).
3. If `applicable_candidates.len() > 1` remains:
   - If `tcx.features().supertrait_item_shadowing()` (`#![feature(supertrait_item_shadowing)]`, RFC #3624) is active, `collapse_candidates_to_subtrait_pick` (`lines 2439-2514`) checks via transitive `supertrait_def_ids` iteration whether one candidate's trait container is a strict subtrait of every other candidate's trait container (`SUPERTRAIT_SHADOW=2` + `#![warn(resolving_to_items_shadowing_supertrait_items)]`).
   - Otherwise `consider_candidates` returns **`Some(Err(MethodError::Ambiguity(sources)))`**, which `pick_method`, `pick_all_method`, and `pick_core` all propagate immediately (`?` / early `return`) without consulting the `extension` bucket or later `autoderef` steps, and `suggest.rs:334-357` emits **`E0034: multiple applicable items in scope`**.

#### 3.2 Complete Empirical Ambiguity & Shadowing Matrix (`probe_results.json`, `rustc 1.98.0-nightly`)

| Probe Case | Bucket / Relation | Feature Flags | Observed `rustc` Result | Why |
| :--- | :--- | :--- | :--- | :--- |
| `same_step_trait_ambiguity_e0034` | Two distinct traits `T1`, `T2` at `(0, Not, Ext)` | Stable | **`E0034`** | Neither shares a trait container; unrelated traits cannot collapse. |
| `same_step_inherent_ambiguity_e0034` | Overlapping generic impls `Gen<T, u32>` vs `Gen<u32, U>` at `(0, Not, Inh)` | Stable | **`E0592` + `E0034`** (`inherent` only, no `Ext` fallback) | Coherence emits `E0592` (`duplicate definitions`), and `inherent` `E0034` aborts before `ExtDup` trait fallback. |
| `same_step_where_clause_ambiguity_e0034` | Bounded `fn f<T: T1 + T2>(x: T)` | Stable | Pure **`E0034`** (`0` `E0592`) | Both bounds populate `WhereClauseCandidate` inside `inherent_candidates` at `(0, Not, Inh)`. |
| `same_step_object_candidate_ambiguity_e0034` | Trait object `x: &dyn Combined` (`Combined: T1 + T2`) | Stable | Pure **`E0034`** (`0` `E0592`) | Both supertraits populate `ObjectCandidate` inside `inherent_candidates` at `(0, Not, Inh)`. |
| `supertrait_collision_without_feature_e0034` | `impl<T: Sub> ...` calling `x.item()` with `Sub: Super` | Stable | **`E0034`** | RFC #3624 subtrait collapsing is gated behind `supertrait_item_shadowing`. |
| `supertrait_shadowing_with_feature` | Same code with `#![feature(supertrait_item_shadowing)]` | `supertrait_item_shadowing` | **Compiles & runs `SUPERTRAIT_SHADOW=2`** + shadow lint | `collapse_candidates_to_subtrait_pick` selects `Sub::item` and records `Super::item` in `shadowed_candidates`. |
| `inference_deferred_same_trait_collapse` | `Wrap<?0>` matching two impls of `SameTrait` | Stable | **`COLLAPSE_SAME_TRAIT=0`** | `collapse_candidates_to_trait_pick` succeeds before inference completes. |
| `cross_step_trait_shadows_inner_inherent` | Step-0 `&self` `TOuter` trait vs step-1 `&self` `Inner` inherent | Stable | **`CROSS_STEP=TOuter_step0`** (silent, `0` `E0034`) | `.find_map` returns on step `0` before inspecting step `1`. |

---

### 4. Arbitrary Self Types (`core::ops::Receiver` vs. `Deref`) and the Asymmetric `E0034` Anti-Shadowing Check

Basis: source + execution

#### 4.1 Receiver Validity (`wfcheck.rs:1752-2080`) and `core::ops::Receiver` (`deref.rs:368-406`)

In `library/core/src/ops/deref.rs:370-385` (`0259d5e9`):
```rust
#[lang = "receiver"]
#[unstable(feature = "arbitrary_self_types", issue = "44874")]
#[rustc_dyn_incompatible_trait]
pub trait Receiver: PointeeSized {
    #[rustc_diagnostic_item = "receiver_target"]
    #[lang = "receiver_target"]
    #[unstable(feature = "arbitrary_self_types", issue = "44874")]
    type Target: ?Sized;
}

impl<P: ?Sized, T: ?Sized> Receiver for P
where
    P: Deref<Target = T>,
{
    type Target = T;
}
```
Notice how `check_method_receiver` (`compiler/rustc_hir_analysis/src/check/wfcheck.rs:1752-1889`) and `receiver_is_valid` (`lines 1925-2021`) enforce method signature well-formedness:
- **Special case (`lines 1939-1949`):** `receiver_ty == self_ty` is always valid even without `Receiver`.
- **Method generic prohibition (`confirm_type_is_not_a_method_generic_param`, `lines 1904-1914`):** No step on the deref chain from `receiver_ty` to `self_ty` may be a generic parameter introduced by the method itself (`param.index >= method_generics.parent_count`).
- **Without `arbitrary_self_types` (`lines 1996-2016`):** Walks `Deref` only (`use_receiver_trait()` NOT called) and requires every intermediate type along the chain to implement `LegacyReceiver` (`&T`, `&mut T`, `Box`, `Rc`, `Arc`, `Pin`), rejecting `*const Self`/`*mut Self` (`arbitrary_self_types_pointers`) and custom `Deref` wrappers with `E0307` / `E0658`.
- **With `arbitrary_self_types` (or `_pointers`, `lines 1958-1965`):** Sets `autoderef = autoderef.use_receiver_trait()`, and if `ArbitrarySelfTypesLevel::WithPointers`, also `.include_raw_pointers()`.
- Notice the deliberate **asymmetry between assembly and dispatch** in `method_autoderef_steps`: `SmartOnly<Target>` (`impl Receiver<Target = Target>`, NO `Deref`) admits `impl Target { fn take_smart(self: &SmartOnly<Self>) }` cleanly (`SMART_REF=107`, `SMART_VAL=117`), while calling `Target`'s ordinary `fn needs_deref(&self)` on `SmartOnly<Target>` fails with **`E0599`** (`arbitrary_self_receiver_without_deref_e0599`) because step `1` (`Target`) has `reachable_via_deref = false`! When a wrapper *does* implement `Deref` (via blanket `impl<P: Deref> Receiver`), both target `&self` (`DEREF_FALLBACK=209`) and `Receiver`-parameterized methods resolve seamlessly.

#### 4.2 `check_for_shadowed_autorefd_method`: Scope, Asymmetry, Double-Ref Niche Bypass, and `*mut` Exemption

To uphold Rust's backwards-compatibility guarantee when smart pointers add inherent methods, `pick_all_method` (`probe.rs:1383-1453, 1496-1581`) guards `by_value` (checking `{Not, Mut}`) and `autoref(Not)` (checking `{Mut}`) whenever `possible_shadower.kind == PickKind::InherentImplPick` and `arbitrary_self_types || arbitrary_self_types_pointers`:

```rust
struct PickConstraintsForShadowed {
    autoderefs: usize,
    receiver_steps: Option<usize>,
    def_id: DefId,
}
impl PickConstraintsForShadowed {
    fn may_shadow_based_on_autoderefs(&self, autoderefs: usize) -> bool {
        autoderefs == self.autoderefs
    }
    fn candidate_may_shadow(&self, candidate: &Candidate<'_>) -> bool {
        candidate.item.def_id != self.def_id
            && match candidate.kind {
                CandidateKind::InherentImplCandidate { receiver_steps, .. } => match self.receiver_steps {
                    Some(shadowed_receiver_steps) => receiver_steps > shadowed_receiver_steps,
                    _ => false
                },
                _ => false
            }
    }
}
```

Four exact behaviors follow from `probe.rs:1383-1581` and are confirmed both by `rustc` execution (`support/probe_results.json`) and our Lean Theorem 6 (`antiShadow_*`):
1. **Positive protection (`E0034`):** On `p: SmartPtr<Target>`, `SmartPtr::collide(self)` (`receiver_steps = 0`) shadowing `Target::collide(self: &SmartPtr<Self>)` (`receiver_steps = 1`), and `SmartPtr::collide(&self)` (`0`) shadowing `Target::collide(self: &mut SmartPtr<Self>)` (`1`), **both** fail with **`E0034`** (`anti_shadowing_by_val_over_ref_e0034`, `anti_shadowing_shared_ref_over_mut_ref_e0034`).
2. **Asymmetry (`ASYM_POINTEE_WINS=Target::SmartPtr<Self>`):** If `Target` defines `fn asym(self: SmartPtr<Self>)` (`receiver_steps = 1`) and `SmartPtr` defines `fn asym(&self)` (`receiver_steps = 0`), `Target` wins `by_value` and `candidate_may_shadow` tests `0 > 1` -> `false`! No `E0034` is emitted (`anti_shadowing_asymmetry_pointee_shadows_smart`).
3. **Documented double-ref niche bypass (`DOUBLE_REF_NICHE=SmartPtr::&self`, `probe.rs:1534-1562`):** When `Target` defines `fn niche(self: &&SmartPtr<Self>)`, `SmartPtr` defines `fn niche(&self)`, and the caller invokes `(&s).niche()`, `pick_by_value_method` matches step `0` (`&SmartPtr<Target>`) and increments `possible_shadower.autoderefs` from `0` to `1` for reference reborrowing (`lines 1606-1612`), whereas `step.autoderefs == 0`. Thus `may_shadow_based_on_autoderefs(0)` evaluates `0 == 1` (`false`), bypassing `E0034` and resolving silently to `SmartPtr::&self` (`anti_shadowing_double_ref_niche_bypass`).
4. **Raw-pointer `*mut` exemption (`MUT_PTR_EXEMPT=RawWrap::*mut`, `probe.rs:1431-1451`):** Because `<*mut T>::cast` must shadow `<*const T>::cast` without `E0034`, `pick_const_ptr_method` is omitted from anti-shadowing searches. Therefore `RawWrap::ptr_shadow(self: *mut Self)` silently shadows `Target::ptr_shadow(self: *const RawWrap<Self>)` (`anti_shadowing_mut_ptr_exemption`).

---

### 5. Real-World First-Customer Receiver Patterns in `google/zerocopy` (`Ptr`, `Unalign`, and `ReadOnly`)

Basis: source + execution

Direct inspection of `google/zerocopy@e8dcb7f08edbc19485c9e7980333607ebbff5f48` combined with replica probes (`group_c_zerocopy_first_customer_patterns`) reveals how `zerocopy`'s public wrapper APIs are deliberately engineered around `rustc_hir_typeck`'s exact method resolution rules:

| Type (`google/zerocopy`) | Source Location | Receiver / Trait Design | Method Resolution Behavior (`rustc` & `Miri` SB/TB) | MIR Lowering Impact |
| :--- | :--- | :--- | :--- | :--- |
| **`Ptr<'a, T, I>`** | `zerocopy/src/pointer/ptr.rs:57-310` | **Zero `Deref` impl.** Inherent `pub fn as_ref(self) -> &'a T` (`L237`), `pub fn reborrow<'b>(&'b mut self) -> Ptr<'b, T, I>` (`L293`, `'a: 'b`). | **Step `0` only.** `as_ref(self)` matches `(0, by_value, Inh)` and beats any `&self` trait extension (no ambiguity); `reborrow(&mut self)` resolves at `(0, autoref(Mut), Inh)`; calling referent methods (`p.len()` on `Ptr<'_, [u8; 4]>`) fails **`E0599`** (preventing implicit deref of potentially unaligned/unsafe `Ptr`s). | `reborrow` takes `&mut _1`, returns reborrowed `Ptr`; `as_ref` consumes `move _4` to return `&[u8; 4]` (which then unsizes on `.len()`). |
| **`Unalign<T>`** | `zerocopy/src/wrappers.rs:118-421` | Inherent `pub fn get(&self) -> T` (`L401`, `Copy`), `pub fn try_deref(&self)` (`L202`); **`impl<T: Unaligned> Deref`** (`L407-414`) & `DerefMut` (`L416-421`). | On `Unalign<[u8; 4]>` (`[u8; 4]: Unaligned`), `u.get()` resolves to `Unalign::get(&self)` at `(0, autoref(Not), Inh)` cleanly shadowing referent `ReferentGet::get(&self)`; `u.len()` walks `step 0 (Unalign) -> step 1 ([u8; 4] via Deref) -> step 2 ([u8] via unsize=true)` (`UNALIGN_GET=[10, 20, 30, 40] UNALIGN_LEN=4`). When `T: !Unaligned` (`Unalign<[u32; 4]>`), `Deref` is unsatisfied, stopping at step `0` so `u.len()` fails **`E0599`** (preventing unaligned reference UB!). | `bb0: _3 = <UnalignLike as Deref>::deref(copy _1); bb1: _2 = copy _3 as &[u8] (PointerCoercion(Unsize, Implicit)); _0 = PtrMetadata(move _2);` |
| **`ReadOnly<T>`** | `zerocopy/src/wrappers.rs:627-815` | Associated-only `into_inner(r)` (`L644`) & `as_mut(r)` (`L651`) — **zero `&self` inherent methods!** Implements `Deref<Target = T>` + `AsRef<T>` + `Borrow<T>` gated on **`T: Immutable`** (`L761-790`), plus `AsMut<T>` (`L792`). | Omitting `&self` inherent methods ensures `ReadOnly<T>` **never shadows** `T`'s inherent or trait methods at step `0` when `T: Immutable`; `ro.as_ref()` resolves cleanly to `<ReadOnly<T> as AsRef<T>>::as_ref(&self)` at `(0, autoref(Not), Ext)` (`RO_AS_REF=[5, 6, 7, 8] RO_LEN=4 RO_INNER=[5, 6, 7, 8]`). On `ReadOnly<Cell<u8>>` (`!Immutable`), `Deref` is unsatisfied so `r.get()` fails **`E0599`** (`zerocopy_readonly_missing_immutable_e0599`). | Same `Deref::deref` + `PointerCoercion(Unsize, Implicit)` sequence for slice length. |

Notice the crucial `zerocopy` invariant at `wrappers.rs:644-655`: `ReadOnly::into_inner(r: ReadOnly<T>)` and `ReadOnly::as_mut(r: &mut ReadOnly<T>)` intentionally omit `self` receivers (associated functions only!) for the exact same reason documented for `Arc`/`Box`/`ManuallyDrop` in stdlib: adding *any* method taking `self`/`&self`/`&mut self` at step `0` would silently shadow every identically named inherent method of the wrapped `T` at step `1`! Similarly, `Ptr::as_inner(&self)` (`ptr.rs:105`) and `Ptr::as_ref(self)` (`ptr.rs:237`) carry `self` safely **precisely because** `Ptr` intentionally does not implement `Deref`.

---

### 6. Kernel-Checked `Lean v4.34.1` Mechanization and Purity Audit

Basis: derived (verified by `lean v4.34.1` kernel under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`)

`support/HirMethodResolutionAutoderefSoundness.lean` (2,758 lines, 140,520 bytes) mechanizes the complete 2-level `(step_index, adjustment_stage, candidate_bucket)` probe state machine, bounded `Autoderef`/`Receiver` chain builder with unique trailing `unsize` step, `collapse_candidates_to_trait_pick` / `collapse_candidates_to_subtrait_pick`, `check_for_shadowed_autorefd_method`, `zerocopy` first-customer dispatch invariants, and Anneal MIR fail-closed classification in pure constructive Lean 4 (`Init` only — zero `import` outside prelude).

**Strict constructive purity receipt (verified statically and dynamically via Lean MetaM):**
- `46` value-level definitions, **100% explicitly marked `noncomputable def`**, `0` `partial def`, `0` `deriving` clauses on recursive inductives, `0` `sorry` / `omega` / `bv_decide` / `native_decide` in code.
- MetaM `Environment` audit across all constants in `HirMethodResolutionAutoderefSoundness`: **`defs=242`, `thms=179`, `unsafe_recs=0` (`0` `._unsafe_rec`), `bad_axioms=0` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`)**. Every theorem depends exclusively on `[]`, `[propext]`, or `[propext, Quot.sound]`.

Key theorems and exact kernel axioms:

| Theorem (`HirMethodResolutionAutoderefSoundness.*`) | Line | Proven Invariant | Kernel Axioms |
| :--- | :---: | :--- | :--- |
| `probeKeyLe_trans` / `probeKeyLe_antisymm` | `L341, L368` | Weak `(stepIdx, stageRank, bucketRank)` ordering is transitive and antisymmetric. | `[]` / `[propext]` |
| `unsize_step_termination_and_uniqueness` | `L632` | `buildMethodAutoderefSteps` terminates in `<= limit + 2` steps, emits **at most 1** `unsize = true` slice step exclusively at `[T; N]` tail with `reachableViaDeref = true`, and never recurses unsizing. | `[propext, Quot.sound]` |
| `probeMethod_trichotomy` | `L1665` | Under compatible return types, `probeMethod` deterministically partitions into `picked \| ambiguity \| noMatch` (`≠ .badReturnType`). | `[propext]` |
| `probeMethod_lexicographic_optimality` | `L1766` | Whenever `probeMethod` returns `.picked p`, `p.step` is eligible and `ProbeKeyLe` holds between `p` and every eligible matching candidate (`isUnstable = false` in Pass 1; all candidates if Pass 1 missed). Together with `probeKeyLe_antisymm`, any optimal pick has a unique `(stepIdx, stage, bucket)` key. | `[propext, Quot.sound]` |
| `step0_pick_beats_step1_inherent` | `L1814` | Any eligible pick at step `0` (including `.extension`) terminates `probeMethod` at `p.stepIdx = 0` without inspecting step `1` inherent candidates. | `[propext, Quot.sound]` |
| `step_autoref_imm_beats_autoref_mut` | `L1834` | Step-0 `.autorefImm` strictly precedes `.autorefMut` whenever `.byValue` misses and no anti-shadowing error fires. | `[propext, Quot.sound]` |
| `step0_extension_imm_beats_step0_inherent_mut` | `L1992` | Specifically proves `(0, .autorefImm, .extension)` strictly beats `(0, .autorefMut, .inherent)`. | `[propext]` |
| `inherent_bucket_beats_extension_same_slot` / `inherent_ambiguity_short_circuits_extension` | `L1858, L1869` | Within any fixed `(step, stage)` slot, `.inherent` beats `.extension` and `.ambiguity` aborts before consulting `.extension`. | `[propext]` |
| `raw_ptr_never_autoderefed_and_unsize_blocks_val_const_ptr` | `L1882` | `fromUnsafeDeref = true` fails `stepEligible`; `unsize = true` blocks both `.byValue` and `.constPtr`. | `[propext]` |
| `ambiguity_propagates_across_steps` | `L1906` | Step-0 `.ambiguity` short-circuits immediately across remaining `rest` steps. | `[propext, Quot.sound]` |
| `same_step_two_distinct_traits_collide_e0034` / `same_step_two_trait_picks_distinct_traits_e0034` | `L1915, L1937` | Distinct traits matching the same `(step, stage, .extension)` slot yield `.ambiguity [c1.id, c2.id]` (`E0034`). | `[propext]` / `[propext, Quot.sound]` |
| `same_trait_candidates_collapse_without_e0034` | `L1958` | Two candidates sharing `traitId` (`tryCollapseSameTrait`) collapse to `.picked` without `E0034`. | `[propext, Quot.sound]` |
| `cross_step_shadowing_no_e0034` | `L1975` | Early-step match precludes `.ambiguity` (`≠ .ambiguity ids`) against later-step matches. | `[propext, Quot.sound]` |
| `subtrait_item_shadowing_collapses_when_enabled` | `L2015` | `[sub, sup]` yields `.ambiguity [sub.id, sup.id]` with `supertraitItemShadowing = false`, and `.picked ... sub` when `true`. | `[propext, Quot.sound]` |
| `const_ptr_coercion_and_pin_reborrow_precedence` | `L2057` | `.constPtr` yields `some .toConstPtr`; `.autorefImm` beats `.constPtr`; `Pin` reborrow requires `pinErgonomics = true`. | `[propext]` |
| `receiver_only_chain_soundness` | `L2104` | Non-`Deref` `Receiver` wrapper produces `[step0(reachable=true), step1(reachable=false)]`; target `&self` fails `.noMatch` (`E0599`) while target `self: &SmartReceiver<Target>` succeeds at step `0`. | `[propext]` |
| `antiShadow_*` + `arbitrary_self_anti_shadowing_asymmetry_soundness` | `L2304–L2501` | Proves all five `check_for_shadowed_autorefd_method` cases: `ByVal->Ref` `E0034`, `Imm->Mut` `E0034`, asymmetric `Target::SmartPtr<Self>` silent shadow, double-ref niche bypass (`autoderefs = 1 != 0`), and `*mut` raw-ptr exemption. | `[propext]` |
| `zerocopy_first_customer_dispatch_soundness` | `L2545` | Verifies `Ptr` (`as_ref`, `reborrow`, `len`=`E0599`), `Unalign` (`get` shadow, `Deref`+`Unsize` `len`, `!Unaligned`=`E0599`), and `ReadOnly` (`AsRef::as_ref` `extension`, `Deref`+`Unsize` `len`, `!Immutable`=`E0599`). | `[propext]` |
| `anneal_mir_boundary_soundness` | `L2696` | Proves every pick using `objectPick`, `autoderefs > 0`, `unsize = true`, `toConstPtr`, `reborrowPin`, or `autoref` classifies as `.unsupported` in `classifyPickInAnneal`. | `[propext]` |
| `hir_method_resolution_autoderef_master_soundness` | `L2734` | Master composition uniting trichotomy, lexicographic optimality, `unsize` termination/uniqueness, and Anneal fail-closed boundary. | `[propext, Quot.sound]` |

---

### 7. Fail-Closed Projection onto Anneal's Trusted MIR Semantics and Revision Deltas

Basis: source + derived

#### 7.1 Anneal Trusted MIR Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Inspection of `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirAst.lean`, and `trusted/lean/Trusted/MirSemantics.lean` establishes why HIR method adjustments outside direct scalar value calls currently fail closed in Anneal:
- **Projections (`MirAst.lean:472-475`):** `ProjectionElem` only models `.deref`, `.field`, and `.unsupported`, and `evalOperandToSlot` / place evaluation (`MirSemantics.lean`) rejects dereference chains when `callerMem` or compound place dereferences appear (`autoderefs > 0` for `Deref::deref` or `&mut`/reborrow chains classify `.unsupported`).
- **Coercions and Reborrows (`MirAst.lean:596-628`):** Every `Rvalue::Cast` (including `PointerCoercion::Unsize` from array-to-slice method calls such as `Unalign<[u8; 4]>::len()` and `PointerCoercion::MutToConstPointer` from `ToConstPtr`) lowers to `Rvalue.unsupported`. Likewise `Rvalue::Use(_, WithRetag::Yes)` on reference/box receivers lowers to `Rvalue.unsupported`.
- **Call Terminators (`MirAst.lean:780-795`, `MirSemantics.lean:1568, 1686-1693`):** Non-`FnDef` callees (including `ObjectPick` virtual `dyn` method calls) map to `.unsupported`, `callerMem` must be empty, and single-body `step` halts at `TerminatorKind.call` with `.fault .unsupported` pending interprocedural function-summary / `#[spec]` call lowering.

#### 7.2 Source Diff Between `rust-lang/rust` `14210df0e` (`1.98.0-nightly`) and `0259d5e9` (`main`)

Programmatic `difflib` comparison across all examined compiler files shows **zero change to method resolution precedence, autoderef chaining, or anti-shadowing logic** between the executed `1.98.0-nightly` toolchain and `main`:

| File | Delta (`14210df0e` -> `0259d5e9`) | Behavioral Impact on Findings 1–5 |
| :--- | :--- | :--- |
| `compiler/rustc_hir_typeck/src/method/probe.rs` | Adds `self_ty_override: Option<Ty<'tcx>>` on `ProbeScope::Single(DefId, Option<Ty>)` for `fn_delegation` (`probe.rs:100`); converts tuple variants `TraitCandidate(PolyTraitRef, bool)` and `TraitPick(bool)` to named fields `{ trait_ref, is_ambiguously_imported }` (`lines 121, 250-252`); updates diagnostic module paths. | **None.** `method_autoderef_steps`, `pick_core`, `pick_all_method`, `check_for_shadowed_autorefd_method`, and `collapse_candidates_*` are semantically identical. |
| `compiler/rustc_hir_typeck/src/method/confirm.rs` | Threads `call_args: Option<&'tcx [hir::Expr<'tcx>]>` for diagnostics and moves `UnresolvedDiagnostic` hints (`AllowTwoPhase::Yes`, `Unsize`, `MutToConstPointer`, `ReborrowPin` unchanged). | **None.** `create_ty_adjustments_from_pick` (`lines 201-292`) is semantically identical. |
| `compiler/rustc_hir_analysis/src/autoderef.rs` | Renames `body_id` -> `body_def_id` and `resolve_vars_if_possible` -> `deeply_resolve_ignoring_regions`; switches `Limit` import path (`62` diff lines total). | **None.** `Autoderef::next` iteration order and `use_receiver_trait` / `include_raw_pointers` flags are unchanged. |
| `compiler/rustc_hir_analysis/src/check/wfcheck.rs` | Updates `LangItem::NonNull` lookup, diagnostics/lint imports, and sibling view/default-field checks. | **None.** `check_method_receiver` and `receiver_is_valid` preserve identical `LegacyReceiver` vs. `ArbitrarySelfTypesLevel::{Basic, WithPointers}` logic. |

---

## Boundaries

### Negative-Space Classification

- **`not examined` — Execution on a binary compiled directly from `rust-lang/rust` `0259d5e9` (`main`):** All live `rustc`, `--emit=mir`, and `Miri` executions in `support/probe_results.json` ran on `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)`. Continuity with `0259d5e9` is established by source-level diffing rather than re-compiling upstream `rust-lang/rust`.
- **`not examined` — Next-generation trait solver (`-Znext-solver=globally`) and `ProbeScope::Single` delegation calls:** All empirical probes used the default trait solver and ordinary method calls (`ProbeScope::All` / `TraitsInScope`), not `fn_delegation`'s `self_ty_override` path or solver-specific opaque normalization corner cases (`overloaded_deref_ty` `predicate_may_hold_opaque_types_jank`).
- **`not examined` — Negative `E0034` interactions with macro-hygienic private items, specialization (`min_specialization`), and coherence orphan rules outside inherent overlap:** Only overlapping generic inherent impls (`Gen<T, u32>` vs `Gen<u32, U>` triggering `E0592` + `E0034`), distinct traits, supertrait/subtrait pairs, `WhereClauseCandidate` bounds, and `ObjectCandidate` trait objects were empirically executed.
- **`unknown` — Future stabilization shape of `arbitrary_self_types` / `arbitrary_self_types_pointers` / `pin_ergonomics` / `supertrait_item_shadowing`:** Upstream may tighten `check_for_shadowed_autorefd_method` (for instance, plugging the double-ref `autoderefs == self.autoderefs` niche bypass or extending guards to `*mut -> *const` outside primitive raw pointers) prior to stabilizing `#![feature(arbitrary_self_types)]`.
- **`known not to apply` — Backtracking on `E0596` mutability, borrow-checker errors, or lifetime/predicate errors after probe selection:** `pick_all_method` selects the winning `Pick` solely on step/stage/bucket order and HIR trait obligation satisfiability during probe; expression place immutability (`let o = ...; o.m()` calling `&mut self`) commits to step `0` and fails with `E0596` without reconsidering step `1` (`a_probe_ignores_place_mutability_e0596`).
- **`known not to apply` — Anti-shadowing `E0034` on extension traits, target-wins `ByVal` over smart-pointer `&self`, double-ref calls, or `*mut -> *const`:** As proven in Finding 4.2 and Lean Theorem 6, `check_for_shadowed_autorefd_method` skips `Extension` picks, fails `receiver_steps > shadowed_receiver_steps` symmetrically (`Target` `by_value` wins silently), short-circuits on `autoderefs != self.autoderefs` for `&SmartPtr<T>` calls, and omits `ConstPtr` / `ReborrowPin`.
- **`known not to apply` — Chained `*mut T -> *const T -> &*const T` or `*mut [T; N] -> *const [T]`:** `rustc` never chains `ToConstPtr` with `Autoref` and blocks `unsize = true` inside both `pick_by_value_method` and `pick_const_ptr_method` (`E0599`).
- **`unsupported` — Pointee inherent methods through `SmartOnly` (`Receiver`-only without `Deref`), raw pointers `*const T` / `*mut T` without `Receiver`, and MIR method adjustments in `joshlf/anneal@c131b320e`:** `rustc` rejects pointee `&self` calls through non-`Deref` `Receiver` types and through `*const`/`*mut` with `E0599`, and `joshlf/anneal` rejects `.deref`, `Rvalue::Cast` (`Unsize` / `MutToConstPointer`), retagging `Use`, and virtual/non-scalar `.call`s fail-closed.

### Attractive Stronger Conclusions Not Established

1. **"Type-checking `zerocopy`'s `Ptr` / `Unalign` / `ReadOnly` wrappers guarantees Anneal can verify their callers today":** False — `Unalign<T>::len()` and `ReadOnly<T>::len()` desugar to `<Wrapper as Deref>::deref` followed by `Rvalue::Cast(PointerCoercion(Unsize, Implicit))` (`support/probe_results.json`), which immediately hit `.unsupported` in `joshlf/anneal@c131b320e`'s current `MirAst` / `MirSemantics` (`anneal_mir_boundary_soundness`).
2. **"Adding an inherent `&self` method on a smart pointer implementing `Deref` is harmless because `rustc` will warn or report `E0034` ambiguity":** False across `autoderef` depths! Whenever `SmartPtr<T>` implements `Deref`, `SmartPtr::m(&self)` (`step 0`) **silently shadows** `T::m(&self)` (`step 1`) with **zero `E0034` and zero warning**, because `may_shadow_based_on_autoderefs` checks `autoderefs == self.autoderefs`! This is precisely why `zerocopy::ReadOnly<T>` omits `&self` inherent methods completely.
3. **"Lean `v4.34.1` theorems prove binary extraction fidelity of `rustc` itself":** False — `HirMethodResolutionAutoderefSoundness.lean` proves total mathematical properties of a faithful pure-Lean model of `rustc`'s documented `method_autoderef_steps` and `pick_all_method` algorithms, not machine-checked translation validation from `rustc`'s compiled x86-64 machine code.

---

## Evidence

### 1. Upstream Primary-Source Coordinates (Pinned 40-Hex Commits)

All repository revisions were resolved live via GitHub API on `2026-11-23`:

- **`rust-lang/rust` (`main` HEAD): `0259d5e9a81c6af08e40f8c204f2c0c41dca1647`**
  - `compiler/rustc_hir_typeck/src/method/probe.rs` — `CandidateKind` / `ProbeContext` (`L55-123`), `AutorefOrPtrAdjustment` (`L132-170`), `PickConstraintsForShadowed` (`L190-215`), `Pick` / `PickKind` (`L218-257`), `method_autoderef_steps` (`L655-821`), `assemble_inherent_candidates` / `_from_object` / `_from_param` (`L898-1083`), `assemble_extension_candidates_for_traits_in_scope` (`L1107-1215`), `pick_core` (`L1319-1344`), `pick_all_method` (`L1346-1479`), `check_for_shadowed_autorefd_method` (`L1496-1581`), `pick_by_value_method` (`L1589-1631`), `pick_autorefd_method` (`L1633-1668`), `pick_reborrow_pin_method` (`L1672-1708`), `pick_const_ptr_method` (`L1713-1739`), `pick_method` (`L1741-1781`), `consider_candidates` (`L1783-1858`), `collapse_candidates_to_trait_pick` (`L2391-2428`), `collapse_candidates_to_subtrait_pick` (`L2439-2514`).
  - `compiler/rustc_hir_typeck/src/method/confirm.rs` — `create_ty_adjustments_from_pick` (`L201-292`, `AllowTwoPhase::Yes` at `L230`, `Unsize` at `L246`, `MutToConstPointer` at `L261`, `ReborrowPin` at `L275-284`).
  - `compiler/rustc_hir_typeck/src/method/suggest.rs` — `MethodError::Ambiguity` -> `E0034` reporting (`L334-357`).
  - `compiler/rustc_hir_analysis/src/autoderef.rs` — `Autoderef` iterator, `builtin_deref` vs `overloaded_deref_ty`, recursion limit (`L33-108`).
  - `compiler/rustc_hir_analysis/src/check/wfcheck.rs` — `check_method_receiver` (`L1752-1889`), `confirm_type_is_not_a_method_generic_param` (`L1904-1914`), `receiver_is_valid` (`L1925-2021`), `legacy_receiver_is_implemented` (`L2059-2079`).
  - `library/core/src/ops/deref.rs` — `Receiver`, blanket `impl<P: ?Sized, T: ?Sized> Receiver for P where P: Deref<Target = T>`, `LegacyReceiver` (`L368-406`).
- **`rust-lang/rust` (executed toolchain): `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `LLVM 22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`).
  - Examined files in `compiler/` diffed programmatically against `0259d5e9` (`probe.rs`, `confirm.rs`, `autoderef.rs`, `wfcheck.rs`).
- **`google/zerocopy` (`main` HEAD): `e8dcb7f08edbc19485c9e7980333607ebbff5f48`**
  - `zerocopy/src/pointer/ptr.rs` — `Ptr<'a, T, I>` (`L57-109`), `Ptr::as_ref(self)` (`L222-278`), `Ptr::reborrow(&mut self)` (`L280-310`).
  - `zerocopy/src/wrappers.rs` — `Unalign<T>` (`L118-421`: `try_deref` at `L202`, `get(&self)` at `L401`, `impl<T: Unaligned> Deref` at `L407-414`); `ReadOnly<T>` (`L627-815`: `into_inner` at `L644`, `as_mut` at `L651`, `impl<T: ?Sized + Immutable> Deref` at `L761`, `AsRef<T>` at `L778`).
- **`joshlf/anneal` (`main` HEAD): `c131b320eeeb26ef692e5afd5ec8db49ee518613`**
  - `trusted/rustc-capture/src/driver.rs` (`L25-150`), `trusted/lean/Trusted/MirAst.lean` (`L472-475`, `L596-628`, `L780-795`), `trusted/lean/Trusted/MirSemantics.lean` (`L803`, `L953-976`, `L1568`, `L1686-1693`).
- **`leanprover/lean4` (`v4.34.1`): `5045d0056413266e57c625dcd7c365b10e377c52`**.

### 2. Preserved Package Support Artifacts and Integrity Hashes

All probes, machine outputs, and kernel-checked proofs are preserved inside `support/`:

| Artifact | Lines | Bytes | SHA-256 | Role |
| :--- | ---: | ---: | :--- | :--- |
| `support/probe_method_resolution_autoderef.py` | 1,333 | 43,585 | `29059f5c544f82486e215118a38bef0aea8060acf7a5895ecce2be8eea6ddf11` | Self-contained `rustc` + `--emit=mir` + `Miri` (Stacked Borrows & Tree Borrows) runner executing all 20 compile/run/error probes inside `tempfile.TemporaryDirectory()`. |
| `support/probe_results.json` | 274 | 35,156 | `6002eb529cf2761e7fc576ed46bde15c161d3186dc186f6cf0f8be42b4723b88` | Machine-captured stdout/stderr, return codes, Miri receipts, and MIR dumps captured `2026-11-23` under `rustc 1.98.0-nightly (14210df0e 2026-05-31)`. |
| `support/HirMethodResolutionAutoderefSoundness.lean` | 2,758 | 140,520 | `a3e2252b20e287bf6d6b077f6a6bcedeb4e44e6214efc46a542af75a659e601b` | Pure constructive `Lean v4.34.1` mechanization (`46` `noncomputable def`s, `72` user theorems, `0` `._unsafe_rec`, `0` forbidden axioms/tactics). |

### 3. Live Compiler, MIR, and `Miri` Execution Receipts

Command executed (`exit code 0`):
```bash
python3 support/probe_method_resolution_autoderef.py --out support/probe_results.json
```

Summary of observed results (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`):
- **`group_a_autoderef_and_adjustment_precedence` (7 probes):**
  - `a_matrix`: `rc = 0` (`A1=OuterTrait::trait(&self) | A2=Outer::inherent(&self) | A3=OuterByVal::trait(self) | A4=OuterTrait::trait(&self) | A5=Outer::only_mut(&mut self) | A6=Inner::mut(&mut self) | V1=RefStep::by_val(self) | V2=RefStepRef::&self | V3=RefStepMut::&mut self | V3B=RefStepMut::&mut self | V4=RefStep::by_val(self) | V5=RefStepRef::&self | OA_SLICE=4 | OA_TRAIT=404 | OA_OVR=ArrayOverride::[u8;4] | BOX_LEN=5 | W=WhereBound::inherent_priority`).
  - `a_pin_reborrow_positive`: `rc = 0` (`PIN_REBORROW=110`).
  - `a_raw_ptr_to_const_positive`: `rc = 0` (`TO_CONST_PTR=77 PREFER_MUT=mut_ptr_by_val`).
  - `a_probe_ignores_place_mutability_e0596`: `compile_returncode = 1` (`error[E0596]`).
  - `a_raw_ptr_no_autoderef_e0599`: `compile_returncode = 1` (`error[E0599]`).
  - `a_raw_ptr_to_const_no_chained_autoref_e0599`: `compile_returncode = 1` (`error[E0599]`).
  - `a_unsize_skips_by_value_and_const_ptr_e0599`: `compile_returncode = 1` (`error[E0599]`).
- **`group_b_ambiguity_shadowing_and_arbitrary_self_types` (15 probes):**
  - Positive runtime discriminators (`rc = 0`, 7 probes): `anti_shadowing_asymmetry_pointee_shadows_smart` (`ASYM_POINTEE_WINS=Target::SmartPtr<Self>`), `anti_shadowing_double_ref_niche_bypass` (`DOUBLE_REF_NICHE=SmartPtr::&self`), `anti_shadowing_mut_ptr_exemption` (`MUT_PTR_EXEMPT=RawWrap::*mut`), `arbitrary_self_receiver_vs_deref_positive` (`SMART_REF=107 SMART_VAL=117 DEREF_FALLBACK=209`), `cross_step_trait_shadows_inner_inherent` (`CROSS_STEP=TOuter_step0`), `inference_deferred_same_trait_collapse` (`COLLAPSE_SAME_TRAIT=0`), `supertrait_shadowing_with_feature` (`SUPERTRAIT_SHADOW=2` + warning).
  - Compile-failure discriminators (`compile_returncode = 1`, 8 probes): `anti_shadowing_by_val_over_ref_e0034` (`E0034`), `anti_shadowing_shared_ref_over_mut_ref_e0034` (`E0034`), `arbitrary_self_receiver_without_deref_e0599` (`E0599`), `same_step_inherent_ambiguity_e0034` (`E0592` + `E0034`), `same_step_object_candidate_ambiguity_e0034` (`E0034`), `same_step_trait_ambiguity_e0034` (`E0034`), `same_step_where_clause_ambiguity_e0034` (`E0034`), `supertrait_collision_without_feature_e0034` (`E0034`).
- **`group_c_zerocopy_first_customer_patterns` (4 probes + 3 `--emit=mir` dumps):**
  - `zerocopy_patterns_positive`: `rc = 0` (`PTR=[1, 2, 3, 4] RB=1 CONSUMED=[1, 2, 3, 4] UNALIGN_GET=[10, 20, 30, 40] UNALIGN_LEN=4 RO_AS_REF=[5, 6, 7, 8] RO_LEN=4 RO_INNER=[5, 6, 7, 8]`).
  - `zerocopy_ptr_no_deref_to_referent_e0599`, `zerocopy_unalign_missing_unaligned_e0599`, `zerocopy_readonly_missing_immutable_e0599`: all `compile_returncode = 1` with `E0599`.
  - `mir_lowering_excerpts` (`--crate-type=lib --emit=mir -C opt-level=0`, verbatim):
    ```text
    fn mir_array_unsize_len(_1: &[u8; 4]) -> usize {
        debug a => _1;
        let mut _0: usize;
        let mut _2: &[u8];
        bb0: {
            _2 = copy _1 as &[u8] (PointerCoercion(Unsize, Implicit));
            _0 = PtrMetadata(move _2);
            return;
        }
    }

    fn mir_deref_then_unsize_len(_1: &UnalignLike) -> usize {
        debug u => _1;
        let mut _0: usize;
        let mut _2: &[u8];
        let _3: &[u8; 4];
        bb0: {
            _3 = <UnalignLike as Deref>::deref(copy _1) -> [return: bb1, unwind continue];
        }
        bb1: {
            _2 = copy _3 as &[u8] (PointerCoercion(Unsize, Implicit));
            _0 = PtrMetadata(move _2);
            return;
        }
    }

    fn mir_ptr_reborrow_and_as_ref(_1: PtrLike<'_, [u8; 4]>) -> usize {
        debug p => _1;
        let mut _0: usize;
        let mut _2: &[u8];
        let _3: &[u8; 4];
        let mut _4: PtrLike<'_, [u8; 4]>;
        let mut _5: &mut PtrLike<'_, [u8; 4]>;
        bb0: {
            _5 = &mut _1;
            _4 = PtrLike::<'_, [u8; 4]>::reborrow(move _5) -> [return: bb1, unwind continue];
        }
        bb1: {
            _3 = PtrLike::<'_, [u8; 4]>::as_ref(move _4) -> [return: bb2, unwind continue];
        }
        bb2: {
            _2 = copy _3 as &[u8] (PointerCoercion(Unsize, Implicit));
            _0 = PtrMetadata(move _2);
            return;
        }
    }
    ```
- **`group_d_miri_execution` (4 Miri runs):**
  - `a_matrix_stacked`, `a_matrix_tree_borrows`, `c_zerocopy_stacked`, `c_zerocopy_tree_borrows`: all exit `0` with byte-identical stdout to native `rustc`.

### 4. Lean `v4.34.1` Kernel Verification and MetaM Axiom Audit Receipts

Command executed (`exit code 0`, empty stderr, zero warnings):
```bash
LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/HirMethodResolutionAutoderefSoundness.lean
```
MetaM `Environment` audit summary across all 179 kernel-checked theorem constants and 242 definitions: `unsafe_recs=0`, `bad_axioms=0`; every user theorem depends solely on `[]`, `[propext]`, or `[propext, Quot.sound]`.

---

## Revalidation

To verify whether these findings still hold on a newer `rustc` nightly, `Miri`, `google/zerocopy`, `joshlf/anneal`, or `leanprover/lean4` toolchain without repeating the full crawl:

1. **Re-run the empirical `rustc` + `--emit=mir` + `Miri` probe suite** (~10 seconds with cached Miri sysroot, writing to a scratch JSON output outside the corpus working tree):
   ```bash
   python3 support/probe_method_resolution_autoderef.py --out revalidate_method_res.json
   ```
   - Any divergence in `a_matrix`, `a_raw_ptr_*`, or `a_probe_ignores_place_mutability_e0596` flags a precedence or backtracking change in `probe.rs::pick_all_method`.
   - A change in `anti_shadowing_double_ref_niche_bypass` or `anti_shadowing_mut_ptr_exemption` indicates upstream closed one of the documented `check_for_shadowed_autorefd_method` exemptions (`probe.rs:1431-1451, 1534-1562`).
   - A change in `supertrait_collision_without_feature_e0034` signals stabilization of RFC #3624 (`supertrait_item_shadowing`).
2. **Diff the narrow upstream compiler and `zerocopy` regions** against `0259d5e9` (`rust-lang/rust`) and `e8dcb7f0` (`google/zerocopy`):
   - `compiler/rustc_hir_typeck/src/method/probe.rs` (`method_autoderef_steps`, `pick_core`, `pick_all_method`, `check_for_shadowed_autorefd_method`, `pick_method`, `consider_candidates`, `collapse_candidates_*`);
   - `compiler/rustc_hir_typeck/src/method/confirm.rs` (`create_ty_adjustments_from_pick`) and `compiler/rustc_hir_analysis/src/check/wfcheck.rs` (`check_method_receiver`, `receiver_is_valid`);
   - `zerocopy/src/pointer/ptr.rs` (`Ptr::as_ref`, `Ptr::reborrow`, checking whether `Deref` remains omitted) and `zerocopy/src/wrappers.rs` (`Unalign` and `ReadOnly`, checking whether `ReadOnly` adds any `&self` inherent methods).
3. **Re-check the Lean `v4.34.1` kernel proof** (~10 seconds):
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/HirMethodResolutionAutoderefSoundness.lean
   ```
   and confirm via MetaM / `#print axioms` that `hir_method_resolution_autoderef_master_soundness`, `unsize_step_termination_and_uniqueness`, and `zerocopy_first_customer_dispatch_soundness` still exclude `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, and `_unsafe_rec`.
4. **Re-audit Anneal's MIR support boundary** whenever `joshlf/anneal` modifies `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` or `trusted/rustc-capture/src/driver.rs`, checking whether `ProjectionElem::Deref`, `PointerCoercion::Unsize`, `MutToConstPointer`, reference retags, or `.call` terminators transition from `.unsupported` to modeled semantics.
