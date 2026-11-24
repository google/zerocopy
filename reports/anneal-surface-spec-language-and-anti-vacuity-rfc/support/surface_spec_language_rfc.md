# Anneal High-Level Surface Specification Language (`#[anneal::spec]` & `anneal::external_spec!`)

*Authored by an AI agent acting on joshlf's behalf.*

**Status:** Pre-Implementation Architectural Specification (Standalone RFC, `bounded stop` pending human sign-off on Partition 3 Policy Decisions `D1`–`D4`)
**Target Umbrella:** `google/zerocopy#4102` (`[anneal][specs]`), `#3697` (Zero-Lean Rust UX), `#3091` (Assumed Contract Realizability), `#3203` (Diverging & Panicking Specifications)
**Authoritative Baselines:**
- `google/zerocopy:main` @ `d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/trusted/cargo-anneal/src/{verify,target,stage}.rs`, `zerocopy/Cargo.toml` MSRV `1.56.0`, `zerocopy/POLICIES.md`, `zerocopy/build.rs`, `zerocopy/proofs/`) `[source inspection]`
- `google/zerocopy:reference` (`rust-contract-mir-core-speceval-assumed-effects-and-productive-unsafe-impls`, `rust-specification-and-contract-syntax-landscape-core-contracts-anodized-verifiers`, `rustc-native-contracts-requires-ensures-runtime-checks-and-ctfe-soundness`, `rustc-check-cfg-semilattice-builtin-coherence-and-diagnostic-attribute-algebra`, `ghost-code-erasure-and-specification-only-state`, `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux`, `cross-tool-source-spans-utf8-columns-and-diagnostic-normalization`, `specification-adequacy-vacuity-detection-and-anti-goodhart-verification`, `dual-polar-mutation-refutation-spec-strength-auditing-and-anti-vacuity-harnesses`) `[kernel-checked proof]` `[real measurement]` `[source inspection]`
- Companion Semantic Core RFC: `arch_spec_core_v2.md` (`FnContract` + `EffectMask` + `SpecEval`/`SpecEvalVal` + `InvariantEnv` + `TrapFreeHumanSpecAST`)

**Evidence Tag Legend:** `[kernel-checked proof]` = verified by the Lean `v4.34.1` kernel with `0` `sorryAx` and axioms $\subseteq \{\text{propext}, \text{Classical.choice}, \text{Quot.sound}\}$; `[real measurement]` = live execution against `rustc` (`1.56.0`, `1.100.0`, `1.98.0-nightly` `f8a08b688`) and `cargo-anneal verify` (`spec-preflight` + `target-audit`); `[source inspection]` = direct inspection of repository files; `[projected]` = engineering estimate for unbuilt Profile v2 components.

---

# Partition 1: Surface Specification Language & Zero-TCB Lowering Architecture

## 1. Purpose, Scope, Guarantees, and Non-Goals

Anneal's `PRINCIPLES.md` and `THREAT_MODEL.md` establish two simultaneous requirements on specifications:
1. **No-Lean-Required Ergonomics (`#3697`):** Rust engineers must be able to state caller safety preconditions, functional postconditions, memory framing, and effect bounds in idiomatic, typechecked Rust syntax—receiving `rustc`-style `file:line:col` diagnostics without learning Lean 4 syntax or `Trusted.MirAst` encodings.
2. **Bounded Human Review & Zero TCB Bloat (`THREAT_MODEL.md` §1):** A human reviewer auditing a verified crate inspects *only* the stated specifications and the TCB audit log—never proofs (`Proof.lean`) or proof automation (`Anneal.*`). Adding a high-level Rust surface specification language must introduce **zero lines of parser, proc-macro, or expression-evaluator code into `anneal/trusted/lean/`** (`0` Lean TCB bloat) and **zero runtime, compile-time, dependency, or MSRV cost on downstream crate consumers** (such as `zerocopy` at `rust-version = "1.56.0"`).

### 1.1 Governing Outcome Contract `(C+, C-)`

**Positive Guarantees (`C+`):**
- **`C+1` (Zero Downstream Cost on `zerocopy`):** Downstream Cargo and direct-`rustc` consumers of `zerocopy` incur `0` new crate dependencies in `zerocopy/Cargo.toml`, `0` MSRV increases beyond `1.56.0`, `0` proc-macro compilation overhead, `0` runtime instructions, and `0` `unexpected_cfgs` warnings under `--deny warnings`.
- **`C+2` (Zero Lean TCB Bloat & Existing `spec-preflight` Admission):** The Rust surface contract frontend lives strictly outside `anneal/trusted/lean/`. It lowers deterministically into declarative Lean 4 `TargetRole::Specification` modules (`Spec.lean`) that pass `TrustedBoundary.lean`'s existing `"spec-preflight"` gate and bind into Receipt v3 via `specification_manifest_sha256` (Profile v1 today, extending seamlessly to `Trusted.MirSemantics.Contract` `FnContract` + `SpecEval` in Profile v2).
- **`C+3` (Expressive Coverage Across Profile v1 & Profile v2):** A single orthogonal surface grammar covers `requires` (splitting `safetyPre` on `unsafe fn` from `behaviorPre` on safe `fn`), `ensures`, `cases(...)` disjoint/complete case partitions, `ensures_err` / `ensures_unwind` exceptional-exit guarantees, `after_expiry` / `reborrows` end-of-borrow contracts for `&mut`-returning APIs (`FromBytes::mut_from_bytes`, `SplitAt::split_at_mut`), `modifies` framing, `#[anneal::pure]` specification helpers, `old(...)` pre-state snapshots, effect qualifiers (`total`, `terminates`, `no_panic`, `no_unwind`, `no_abort`), and memory/layout shorthands (`valid_read`, `valid_write`, `aligned_to`, `in_bounds`, `disjoint`, `same_alloc`, `slice_len`, `is_init`) needed across `zerocopy`'s `546` callable `unsafe` blocks (`14` closure `unsafe` blocks, `63` `const` `unsafe` blocks).
- **`C+4` (Deterministic Byte-Identical Lowering & Trap Freedom):** Identical Rust contract inputs emit byte-identical `Spec.lean` outputs (`generated_spec_lean_sha256`). Silent formal-logic traps—eager bitwise `&` clause conjunction (`anodized#240`), side-effecting blocks (`rust-lang/rust#139548`), Lean `autoImplicit` typo quantification, saturating `Nat.sub` (`0 - 1 = 0`), and totalized `/ 0`—are rejected fail-closed at frontend compile time before Lean elaboration.
- **`C+5` (Exact UTF-8 Bidirectional Span Provenance):** Every generated Lean specification declaration records an out-of-key `spec_span_map.json` entry mapping `(lean_decl, lean_line_start..lean_line_end)` back to `(file, start_byte..end_byte, lo_line:lo_col..hi_line:hi_col)` in 1-based Unicode scalar coordinates, translating `spec-preflight` and proof failures into `rustc`-formatted diagnostics without polluting `MirItemKey` incremental proof caches.
- **`C+6` (Constructive Anti-Vacuity Integration, `#4102`):** Every lowered specification emits machine-checked non-vacuity obligations (`preInhabited` domain witness propositions, safe-callable `isUnsafe = false` unconditional UB-freedom, `AssumedContractRealizable` on `#[anneal::trusted]` / `extern` stubs, and byte-locked `Spec.lean` compatibility with Dual-Polar Mutation Refutation `Pole A ∧ Pole B`).

**Scope Exclusions & Non-Goals (`C-`):**
- **`C-1`:** No Lean parser, Rust macro expander, or SMT solver inside `anneal/trusted/lean/`.
- **`C-2`:** No runtime contract instrumentation (`-Zcontract-checks=yes`) during verification capture (which perturbs Tree Borrows aliasing and masks UB).
- **`C-3`:** No inline proof scripts, tactics, or solver hints inside Rust source files or `/// # Safety` comments.
- **`C-4`:** No claim that automated anti-vacuity checks replace human review of specification intent (`THREAT_MODEL.md` §2.2); out-of-band `.anneal/spec-lock.json` pinning protects reviewed contracts against unreviewed agent edits.
- **`C-5`:** OS/syscall/POSIX durability and concurrent protocol refinement (`[anneal][ffi-isa]`) remain outside Profile v1–v2 in-memory specifications, though `SpecClause` reserves an additive `assumes_world(...)` / `on_crash(...)` extension seam so external-world contracts compose later without grammar breakage.

---

## 2. Zero-MSRV, Zero-Dependency Architecture for `zerocopy`

A subtle interaction between Cargo packaging, `rustc 1.56.0` attribute parsing, and Rust `1.80+`'s `unexpected_cfgs` lint governs how specifications attach to `zerocopy` (`[real measurement]`):

1. **Out-of-Tree Companion Specifications (`zerocopy/proofs/<unit>/spec.rs` via `anneal::external_spec!`) — Zero Touch on `zerocopy/src/`:**
   - Companion `.rs` files live alongside `request.json` and `Proof.lean` inside `zerocopy/proofs/`, which `zerocopy/Cargo.toml` excludes from published crates (`exclude = [".*", "/proofs"]`).
   - Requires **zero edits** to `zerocopy/src/*.rs`, **zero lines** in `zerocopy/build.rs`, **zero crate dependencies**, and **zero MSRV exposure**. Downstream `cargo build` on `rustc 1.56.0` through `1.100.0+` never reads `zerocopy/proofs/`.
2. **Inline Inert Attributes (`#[cfg_attr(anneal, anneal::spec(...))]`) — Zero Dependency, Single `build.rs` Line:**
   - Empirically verified on `rustc 1.56.0`, `rustc 1.100.0`, and `rustc 1.98.0-nightly` (`[real measurement]`):
     - Under `rustc +1.56.0 --edition=2021 --crate-type=lib` with `#![deny(warnings)]`, `#[cfg_attr(anneal, anneal::spec(...))]` containing custom logical operators (`==>`, `<==>`) compiles with **exit `0` (`0` errors, `0` warnings)** and **zero `anneal` crate in `Cargo.toml`**, because `rustc` parses inactive `cfg_attr` payloads solely as balanced token trees (`TokenStream`) and strips them before name resolution and macro expansion.
     - Under `rustc +1.100.0` (`zerocopy`'s `pinned-stable`), `rustc` emits `error: unexpected cfg condition name: anneal` under `--deny warnings` *unless* `println!("cargo:rustc-check-cfg=cfg(anneal)");` is added to `zerocopy/build.rs` (matching line 92's existing `println!("cargo:rustc-check-cfg=cfg(kani)");`, guarded by `rustc_version >= 1.77.0`). With that single line, `rustc +1.100.0` and `nightly` compile with **exit `0` (`0` errors, `0` warnings)** and **zero dependencies**.

### Unified Dual-Attachment Architecture

Rather than forcing a fork between inline attributes and out-of-tree files, Anneal defines **one canonical surface AST (`SpecUnitAST`)** with two syntactic attachment forms that lower through the **exact same deterministic compiler** to byte-identical `Spec.lean`:

```text
  Form A: Out-of-Tree Companion (`zerocopy/proofs/<unit>/spec.rs`)
    anneal::external_spec! { impl PointerMetadata for usize { #[anneal::spec(...)] fn ...; } }
      • 0 edits to `zerocopy/src/` or `build.rs`; works on unowned 3P crates & `core`
                                     │
                                     ▼
                    ┌────────────────────────────────────┐
                    │  Anneal Surface Spec Frontend      │  (0 Lean TCB LOC; pure Rust)
                    │  1. Tokenize + parse `SpecUnitAST` │
                    │  2. Resolve target `DefId`s & sigs │
                    │  3. Enforce U1 & M7–M12 trap gates │
                    │  4. Emit `Spec.lean` + span map    │
                    └────────────────┬───────────────────┘
                                     ▲
  Form B: Inline Inert Attribute (`zerocopy/src/*.rs` + 1-line `check-cfg` in `build.rs`)
    #[cfg_attr(anneal, anneal::spec(...))] pub unsafe fn split_at_unchecked(...) { ... }
      • 0 Cargo.toml dependencies; MSRV 1.56.0 clean; co-locates spec with `// SAFETY:`
                                     │
                                     ▼
            ┌────────────────────────────────────────────────────────┐
            │  Generated `Spec.lean` (`TargetRole::Specification`)   │
            │  • Admitted unchanged by `TrustedBoundary.lean`        │
            │    `"spec-preflight"` (closed 14-command allowlist)    │
            │  • Bound in Receipt v3 `specification_manifest_sha256` │
            │  • Reviewed directly OR via `specification_manifest`   │
            └────────────────────────────────────────────────────────┘
```

*(Which attachment form `zerocopy` uses by default is a pure repository policy choice surfaced as Decision `D1` in Partition 3; both share 100% of the grammar, typechecker, lowering pipeline, and `spec_span_map.json` format.)*

---

## 3. Concrete Surface Grammar & Semantics

All surface specifications are valid Rust token trees (`syn`-compatible) so standard editors, brace matchers, and syntax highlighters never choke. Custom logical connectives (`==>`, `<==>`) are valid multi-punctuation sequences inside Rust attribute token trees (`#[cfg_attr(anneal, ...)]` and `external_spec! { ... }`).

### 3.1 EBNF Grammar

```ebnf
SpecFile        ::= InnerAttr* (ExternalSpecBlk | PureHelperItem | SpecFnItem)*

ExternalSpecBlk ::= ("anneal" "::")? "external_spec" "!" "{"
                      ("unit" ":" StringLit ";"?)?
                      ExternalEntry*
                    "}"
ExternalEntry   ::= PureHelperItem
                  | ("impl" TypeParams? Path "for" Type WhereClause? "{" SpecFnDecl* "}")
                  | ("mod" Path "{" SpecFnDecl* "}")
                  | SpecFnDecl

SpecAttr        ::= "#[" ("cfg_attr" "(" "anneal" "," SpecMeta ")" | SpecMeta) "]"
SpecMeta        ::= ("anneal" "::")? "spec" "(" SpecClause ("," SpecClause)* ","? ")"
                  | ("anneal" "::")? "pure"
                  | ("anneal" "::")? "trusted" "(" "reason" "=" StringLit ")"

SpecClause      ::= "requires" "(" SpecExpr ")"
                  | "ensures" "(" ("|" Pat "|")? SpecExpr ")"
                  | "ensures_err" "(" ("|" Pat "|")? SpecExpr ")"
                  | "after_expiry" "(" ("|" Pat "|")? SpecExpr ")"
                  | "cases" "(" (SpecExpr "=>" SpecExpr) ("," SpecExpr "=>" SpecExpr)* ","? ")"
                  | "modifies" "(" ("none" | PlaceExpr ("," PlaceExpr)*) ")"
                  | "unwinds_if" "(" SpecExpr ")"
                  | "ensures_unwind" "(" SpecExpr ")"
                  | "decreases" "(" SpecExpr ")"
                  | "witness" "(" SpecExpr "=>" SpecExpr ")"
                  | "must_reject" "(" SpecExpr "=>" SpecExpr ")"
                  | EffectQual
                  | "target" "=" StringLit

EffectQual      ::= "total"          (* terminates && no_unwind && no_abort *)
                  | "terminates"     (* EffectMask.terminates := true *)
                  | "no_panic"       (* no_unwind && no_abort *)
                  | "no_unwind"      (* EffectMask.noUnwind := true *)
                  | "no_abort"       (* EffectMask.noAbort := true *)

PureHelperItem  ::= SpecAttr /* pure */ Visibility? "const"? "fn" Ident
                    "(" ParamList? ")" ("->" Type)? "{" SpecExpr "}"

SpecExpr        ::= QuantExpr
                  | IffExpr
QuantExpr       ::= ("forall" | "exists") "(" "|" TypedBinders "|" SpecExpr ")"
IffExpr         ::= ImpliesExpr ("<==>" ImpliesExpr)*
ImpliesExpr     ::= OrExpr ("==>" ImpliesExpr)?              (* right-associative *)
OrExpr          ::= AndExpr ("||" AndExpr)*                  (* short-circuiting *)
AndExpr         ::= CmpExpr ("&&" CmpExpr)*                  (* short-circuiting; bare `&` banned! *)
CmpExpr         ::= BitOrExpr (("==" | "!=" | "<" | "<=" | ">" | ">=") BitOrExpr)?
BitOrExpr       ::= ShiftExpr ("|" ShiftExpr)*
ShiftExpr       ::= AddExpr (("<<" | ">>") AddExpr)*
AddExpr         ::= MulExpr (("+" | "-") MulExpr)*           (* gated by TrapFree arith rule §3.3 *)
MulExpr         ::= UnaryExpr (("*" | "/" | "%") UnaryExpr)* (* gated by TrapFree arith rule §3.3 *)
UnaryExpr       ::= ("!" | "*") UnaryExpr | PostfixExpr
PostfixExpr     ::= PrimaryExpr ("." Ident ("(" ArgList? ")")? | "[" SpecExpr "]")*
PrimaryExpr     ::= Lit | Path ("(" ArgList? ")")? | "old" "(" SpecExpr ")" | "(" SpecExpr? ")"
```

### 3.2 Core Clause Semantics & The Safe-Callable Law (`U1`)

1. **`requires(P)` — Automatic Safe vs. Unsafe Split (`U1`, `M4`):**
   - Multiple `requires(P_1), requires(P_2)` clauses conjoin sequentially via short-circuiting `&&` (`P_1 ∧ (P_1 → P_2)`).
   - **On `unsafe fn` (`body.isUnsafe = true`):** `requires(P)` defines **both** the caller safety obligation (`safetyPre`) and the behavioral domain (`behaviorPre`). Callers must prove `P` at every call site; the callee proves UB-freedom (`WellFormed`) and postconditions under `P`.
   - **On safe `fn` (`body.isUnsafe = false`):** By Rust's soundness contract (`Boundary.lean:238`), safe functions **cannot waive UB via preconditions**. On a safe function, `safetyPre` is unconditionally `True` (the function must prove `WellFormed` for *all* well-typed `FullValid` inputs!), while `requires(P)` populates `behaviorPre` (gating `ensures`, `modifies`, and `EffectMask` obligations—for example, stating that a safe function does not panic and returns `Some(...)` *when* `P` holds).
2. **`ensures(|ret| Q)`, `ensures_err(|err| Q_err)`, `cases(...)`, & End-of-Borrow `after_expiry(|ret| Q_end)`:**
   - `ensures(|ret| Q)` evaluates `Q` on normal return (`.returned out`), binding `ret` to `out.ret`. For `Result<T, E>` APIs (`TryFromBytes::try_read_from_prefix`), `ensures_err(|e| Q_err)` and `ensures_unwind(Q_unw)` bind explicit state-preservation guarantees on failure/unwind exits (preventing omitted error-branch frame conditions).
   - **`cases(G_1 => Q_1, ..., G_k => Q_k)` (Disjoint/Complete Partition):** Lowers to three pure `Prop` conjuncts in `Spec.lean`: completeness (`pre → G_1 ∨ ... ∨ G_k`), pairwise disjointness (`pre → ¬(G_i ∧ G_j)` for $i < j$), and per-branch implication (`G_i → Q_i`), matching SPARK `Contract_Cases` auditability with `0` TCB additions.
   - **`old(expr)` (Profile v2):** Evaluates `expr` purely in entry state `(q.args, q.callerMem)` (`SpecEvalVal` in `Contract.lean`), preventing `AllocId` collisions between entry and exit `&mut T` references. Forbidden inside `requires(...)` (`E_ANNEAL_OLD_IN_PRECONDITION`).
   - **`after_expiry(|ret| Q_end)` & `reborrows_subslice` (`&mut`-Returning Functions, Profile v2):** Two-state `(old(x), exit)` postconditions alone cannot specify `&mut`-returning functions such as `FromBytes::mut_from_bytes`, `SplitAt::split_at_mut`, or `Split<&mut T>::via_runtime_check` (`zerocopy/src/split_at.rs:263-355`, where dynamic trailing-padding overlap couples `cases(...)` with returned mutable borrows), because caller writes through `ret` occur *after* the function returns. Unlike SMT tools over erased functional views that require prophetic axioms (`^x`), Anneal's `MirSemantics` represents `&mut` as a concrete `(AllocId, Offset, TbTag)` in `out.callerMem`. Lowering `after_expiry` via `Anneal.PureLift.ByteSubLens` / `LoanGraph` expresses that `ret` is a valid mutable sub-projection of the input `AllocId` so any caller write preserving `FullValid` updates the parent slice view at lifetime expiry with **`0` prophetic axioms in `trusted/lean/`** (enforcing prophetic purity by rejecting `final(...)` inside `requires` and runtime code).
3. **`modifies(...)` — Explicit Memory Framing:**
   - `modifies(none)` asserts pure caller memory (`out.callerMem = q.callerMem`; in Profile v1 scalar/unit mode, `callerMem = ⟨[]⟩`).
   - `modifies(p1, p2, ...)` (Profile v2 Waves 2–3) asserts a spatial frame condition (`FramePreserved q.callerMem out.callerMem [footprint(p1), footprint(p2)]`): every caller allocation byte outside the listed mutable reference or raw-pointer slice footprints retains its exact entry `AbstractByte` (`init`/`uninit` + value + provenance).
   - **Default when omitted:** Safe functions default to mutating only reachable `&mut` parameters (enforced by Rust borrowck + Tree Borrows); `unsafe fn`s taking `*mut T` **must** declare `modifies(...)` explicitly (`E_ANNEAL_MISSING_UNSAFE_MODIFIES`), eliminating the classic ACSL/JML forgotten-`assigns` bug class.
4. **`#[anneal::pure]` Helpers:**
   - Pure, terminating, total specification functions usable across `requires`, `ensures`, and `invariant` clauses. Must have zero `unsafe`, zero mutation, and acyclic call graphs (or explicit `decreases(...)` termination measures), lowering directly to pure total `def`s in `Spec.lean`.
5. **Effect Qualifiers (`EffectMask`):**
   - Default (when no qualifier is written): partial correctness + UB-freedom (`terminates = false, noUnwind = false, noAbort = false`), allowing diverging (`-> !`) and panicking functions (`#3091`, `#3203`).
   - `terminates` forbids `Diverges`; `no_unwind` forbids `.unwound`; `no_abort` forbids `.aborted`; `no_panic` sets `noUnwind ∧ noAbort`; `total` sets all three (`terminates ∧ noUnwind ∧ noAbort`).

### 3.3 Built-In Memory, Slice, Pointer, & Alignment Shorthands (Profile v1 & Profile v2)

To express `zerocopy`'s safety comments (`src/{lib,layout,byte_slice,ref,util}.rs`) concisely without raw Lean boilerplate, `anneal::spec` provides built-in pure specification intrinsics (rejected fail-closed if ever called in runtime code `E_ANNEAL_GHOST_IN_RUNTIME`):

| Intrinsic / Shorthand | Profile | Signature in Spec Language | Exact Lowered Lean 4 Semantics (`Spec.lean`) | Primary `zerocopy` Unlock |
| :--- | :---: | :--- | :--- | :--- |
| `wrapping_add(a, b)`, `wrapping_sub(a, b)`, `wrapping_mul(a, b)` | **v1 & v2** | `(T, T) -> T` | Modular `BitVec W` `+`, `-`, `*` | Scalar/index wrap specs |
| `no_overflow_add(a, b)`, `no_overflow_mul(a, b)` | **v1 & v2** | `(usize, usize) -> bool` | `a.toNat + b.toNat < 2^64`, `a.toNat * b.toNat < 2^64` | `NumExt::unchecked_*`, `add_scaled_metadata` (Wave 1) |
| `math(x)` / `math { expr }` | **v1 & v2** | `(IntOrUInt) -> Int` | Explicit `Int.ofNat x.toNat` / `x.toInt` injection (never `↑` coercions); inside `math { a + b * c }`, `+`, `-`, `*` lower directly to unbounded `Int` without per-operand cast clutter | `TrailingSliceLayout`, `DstLayout` (`21` Kani-contracted `layout.rs`/`util` fns) |
| `is_power_of_two(n)` | **v1 & v2** | `(usize) -> bool` | `n.toNat > 0 ∧ (n &&& (n - 1#64)) = 0#64` | `RoundingAlignAndPhase::new` |
| `aligned_to(ptr_or_addr, align)` | **v2 (W2)** | `(*const T \| usize, usize) -> bool` | `isPowerOfTwo align ∧ (addrOf ptr).toNat % align.toNat = 0` | `validate_aligned_to`, `Ptr::try_into_aligned` |
| `valid_read(ptr, count)` / `valid_write(ptr, count)` | **v2 (W2–3)** | `(*const T, usize) -> bool` | Non-null, aligned for `T`, `count * size_of::<T>() <= isize::MAX`, live allocation in `callerMem` with Tree Borrows read/write permission | `PtrInner`, `HasField::project` (`351` blocks), `copy_unchecked` |
| `is_init(ptr, count)` | **v2 (W3)** | `(*const T, usize) -> bool` | Every byte in `[ptr .. ptr + count * size_of::<T>())` has `AbstractByte.init _` in `InitMask` (and `FullValid T` when typed) | `MaybeUninit::assume_init`, `TryFromBytes`, `FromBytes` |
| `same_alloc(p, q)` / `in_bounds(base, count)` | **v2 (W2–3)** | `(*const u8, *const u8) -> bool` | `p.allocId = q.allocId` and `[base.offset .. base.offset + count] ⊆ alloc.len` | `PtrInner::split_at_unchecked`, `slice_unchecked` |
| `disjoint(p, len_p, q, len_q)` | **v2 (W2–3)** | `(*const u8, usize, *const u8, usize) -> bool` | `p.allocId ≠ q.allocId ∨ p.end ≤ q.offset ∨ q.end ≤ p.offset` | `util::copy_unchecked`, `SplitByteSlice` `&mut [u8]` |
| `slice_len(s)` / `slice_ptr(s)` / `view(s)` | **v2 (W3)** | `(&[T] \| *const [T]) -> usize / *const T / List Byte` | Fat-pointer `PtrMeta.sliceLen`, base `PtrVal`, and mathematical `List (BitVec 8)` byte sequence | `<&[u8] \| &mut [u8] as SplitByteSlice>::split_at_unchecked` |

**Concrete Profile v2 Preview on `zerocopy/src/byte_slice.rs:214` (`<&[u8] as SplitByteSlice>::split_at_unchecked`):**
```rust
anneal::external_spec! {
    impl<'a> SplitByteSlice for &'a [u8] {
        #[anneal::spec(
            requires(mid <= slice_len(self)),
            modifies(none),
            total,
            ensures(|(left, right)|
                slice_len(left) == mid
                && slice_len(right) == wrapping_sub(slice_len(self), mid)
                && view(left) == view(self).take(mid)
                && view(right) == view(self).drop(mid)
            ),
        )]
        unsafe fn split_at_unchecked(self, mid: usize) -> (Self, Self);
    }
}
```

### 3.4 Arithmetic Trap Elimination (`TrapFreeHumanSpecAST`, `M12`)

A pervasive source of false verification confidence across Dafny, Verus, and Lean specifications is silent arithmetic mismatch: in Rust, `a + b` wraps or panics at $2^{64}$, whereas in Lean `Nat`, `0 - 1 = 0` saturates silently and `x / 0 = 0` totalizes silently. Moreover, in `zerocopy/src/`'s `21` Kani-contracted functions (`layout.rs` and `util/mod.rs`), multi-term offset formulas (`size_base + elems * elem_size + padding`) mix mathematical bounds with `usize` arithmetic (`[source inspection]`). The surface compiler enforces a strict, low-friction type-directed rule:
- **Unbounded mathematical `Int` (`math(a) + math(b)` or scoped `math { size_base + elems * elem_size }`):** Admits `+`, `-`, `*` directly, lowering every integer variable inside `math { ... }` via explicit `Int.ofNat` / `BitVec.toInt` (where subtraction never saturates at `0`). Division/modulo (`/` and `%`) emit explicit `Int.tdiv` / `Int.tmod` and require a `divisor != 0` guard (`E_ANNEAL_UNGUARDED_SPEC_DIV`).
- **Machine-width scalars (`usize`, `u8`..`u128`, `isize`, `i8`..`i128` outside `math { ... }`):** Bare `+`, `-`, `*`, `/`, `%` inside specification clauses fail closed (`E_ANNEAL_AMBIGUOUS_SPEC_ARITH`) with a targeted `help:` diagnostic prompting the author to wrap the expression in `math { ... }` (unbounded math) or `wrapping { ... }` / `wrapping_add(a, b)` / `no_overflow_add(a, b)` (exact `BitVec` modular arithmetic).

---

## 4. Deterministic Lowering to `Spec.lean` & `spec-preflight` Admission

### 4.1 Exact Mapping into `TrustedBoundary.lean` (`"spec-preflight"`)

`TrustedBoundary.lean` (`lines 1258–2089` on `google/zerocopy:main`) validates every `TargetRole::Specification` file *before* elaboration against a closed 14-command allowlist (`declaration`, `namespace`, `section`, `end`, `universe`, `variable`, `open`, `export`, `mutual`, `in`, `attribute`, `deriving`, `set_option`, `moduleDoc`), a 7-declaration allowlist (`def`, `abbrev`, `theorem`, `structure`, `inductive`, `classInductive`, `instance`), and `forbiddenSpecTermKinds` (banning `sorry`, `unsafe`, `partial`, `opaque`, `axiom`, `by_elab`, `include_str`, quotations, `autoParam`, and `panic*`).

The surface compiler emits **strictly tactic-free, quotation-free, coercion-free declarative Lean 4** inside `namespace Spec ... end Spec`—always spelling explicit constructors (`Int.ofNat`, `BitVec.ofNat 64`, `Int.tdiv`) rather than overloaded `↑` coercions (which Lean `v4.34.1`'s pretty-printer can elide even under `pp.coercions true`, silently re-elaborating `Int` equalities back to `Nat` `[real measurement]`):
1. `prelude` + `import Init.Data.BitVec.BasicAux` (when fixed-width words appear) + `import Trusted.MirSemantics` (and `Trusted.MirSemantics.Contract` once PR-S1 lands).
2. Canonical sorted declaration order:
   - `fnId_0 .. fnId_{k-1} : String` (`"rust-path-v1::<canonical_path>"`),
   - Topologically sorted `#[anneal::pure]` helpers (`def <helper> ...`),
   - `ReturnsTotal` / `FnContract` combinators,
   - `pre_i` and `post_i` pure `Prop` definitions (one per specified function, preserving 1-to-1 clause granularity for diagnostics and $(m+1)$ clause-independence checks),
   - `safetyPrecondition : String → List Val → Prop` (including `pre_i` **iff** `isUnsafe = true`, enforcing `U1` structurally),
   - `preInhabited : Prop` (`∃ args, pre_0 args ∧ ...`, constructively proved inside `Proof.lean`!),
   - `<unit>Spec : Program → Prop` and `specs : Specs := ⟨safetyPrecondition, <unit>Spec⟩`.
3. **Zero TCB trust in the surface compiler (`THREAT_MODEL.md` §1) & Raw `Spec.lean` Defense-in-Depth:**
   - `cargo-anneal verify` hashes both the Rust surface contract source (`surface_spec_sha256`) and the generated `Spec.lean` (`specification_manifest_sha256`).
   - Even if the surface compiler had a bug, `TrustedBoundary.lean`'s `"spec-preflight"` and `"target-audit"` (`TargetOrigin` + fresh kernel replay) reject any malformed, cyclic, `Proof`-referencing, or axiom-bearing `Spec.lean` fail-closed.
   - *Companion raw-`Spec.lean` hardening note (`#4102`):* While the Rust surface compiler rejects unbound typo identifiers, bare `Nat` subtraction/division, and panicking indexing before emitting `Spec.lean`, hand-written Tier-2 `Spec.lean` files on `main` (`d3362d9a65`) should additionally be hardened in `stage.rs` and `TrustedBoundary.lean` (`validateSpecSetOption` + `isForbiddenSpecTransitiveConst`) by passing `-DautoImplicit=false -DrelaxedAutoImplicit=false`, rejecting `set_option autoImplicit true`, and banning `Nat.{sub,div,mod}` and `!`-panicking accessors (`getElem!`, `head!`, `get!`).

### 4.2 Bidirectional Span Mapping (`spec_span_map.json`)

Following `unified-cargo-anneal-and-verified-rustc-diagnostic-mapping-and-ux` and `cross-tool-source-spans-utf8-columns-and-diagnostic-normalization` (`origin/reference`):
1. **Out-of-key sideband:** `Spec.lean` contains **zero** embedded Rust line/column comments, so reformatting comments or blank lines above a function in `zerocopy/src/` leaves `Spec.lean` (`specification_manifest_sha256`) and `MirItemKey` **100% unchanged** (`0` proof cache invalidations).
2. **Coordinate normalization:** `spec_span_map.json` records exact UTF-8 byte offsets (`start_byte`, `end_byte`) alongside 1-based lines and **1-based Unicode scalar columns** (matching `lean --json`'s 1-based line / 0-based Unicode scalar `Position` with `col_rust = col_lean + 1`, avoiding Charon's UTF-8 byte-vs-display-width mid-codepoint bug on multi-byte characters).
3. **Diagnostic translation:**
   - Frontend syntax/type/trap errors (`E_ANNEAL_EAGER_CLAUSE_JOIN`, `E_ANNEAL_IMPURE_SPEC_EXPR`, `E_ANNEAL_AMBIGUOUS_SPEC_ARITH`, `E_ANNEAL_SPEC_UNKNOWN_IDENT`) render directly against the Rust contract file with `rustc` caret underlines.
   - Downstream Lean `Spec.lean:L:C` or unsatisfied postcondition obligations map via `lean_line_start <= L <= lean_line_end` back to the exact `requires(...)` or `ensures(...)` span in Rust.

---

## 5. Constructive Anti-Vacuity Integration (`#4102`)

Surface contracts integrate directly with Anneal's Layer 2 anti-vacuity defenses (`arch_auditing_and_reward_hacking_defense.md` §3):
1. **Automatic `preInhabited` Obligation (`M4⊥` Closure):** Every generated `<unit>Spec` conjoins `preInhabited` (`∃ params, pre_i params` for each function in the unit). A contradictory precondition (`requires(x > 10 && x < 5)` or `requires(false)`) makes `preInhabited` mathematically unprovable (`Proof.verify` fails!). An intentional uninhabited-type test must opt in explicitly via `#[anneal::vacuous_ok(reason = "...")]`, which surfaces prominently in the human-reviewed manifest.
2. **Lightweight `witness(...)` / `must_reject(...)` Anchors Alongside `preInhabited`:** Because `preInhabited` catches empty preconditions (`M4⊥`) rather than weak (`ensures(|_| true)`) or over-constrained postconditions—and empirical usability studies (e.g., `Forge` OOPSLA'24) show heavy modal `is necessary / is sufficient` keywords see near-zero engineer adoption—optional `witness(in => ok_out)` and `must_reject(in => bad_out)` clauses lower directly to ground-term `post_i` theorems and negated `¬ post_i` checks in `Spec.lean`, giving human reviewers concrete positive/negative anchors with zero modal boilerplate.
3. **Safe-Callable UB Non-Waiver (`U1` / `M4`):** Because `safetyPrecondition` omits `pre_i` whenever `isUnsafe = false`, adding `requires(false)` to a safe function **never** exempts its body from proving UB-freedom (`BodyVerified`) across all `2^64` inputs.
4. **Byte-Locked Dual-Polar Mutation Refutation (`Pole A ∧ Pole B`):** Because `Spec.lean` is emitted deterministically from `spec.rs`, mutation testing mutates *only* the Rust implementation body while holding `sha256(Spec.lean)` fixed—verifying that `cargo-anneal verify` cleanly reports `status = "proof_failed"` (`Pole A`, demonstrated live in §6) and `⊢ ¬ UnitTheorem ⟨P_mut, Spec.specs⟩` (`Pole B`).
5. **Out-of-Band `.anneal/spec-lock.json` Protection:** In CI and agentic proof loops, `spec.rs` and its `generated_spec_lean_sha256` are locked in `.anneal/spec-lock.json` checked against the base branch / `--spec-lock-sha256`, preventing a proving agent from weakening a surface contract to make `Proof.lean` pass.

---

## 6. Empirical Prototype Verification Receipt (`[real measurement]`)

A working, dependency-free reference compiler and test suite (`lower_surface_spec.py` + `test_surface_spec.py` in the companion `h1_surface_spec` prototype package) was executed against **unmodified `zerocopy/src/`** (`google/zerocopy:main` @ `d3362d9a657e2f943d25a0812f7b13b93e60af4d`) using stock `cargo-anneal verify` (`spec-preflight` + `linux_bwrap` `ExecSeal` + `TrustedBoundary.lean` fresh kernel replay, **`0` TCB lines modified**):

| Unit (`zerocopy/src/` Target Items) | Surface Contract (`contracts/*.rs`) | Generated `Spec.lean` SHA-256 | `cargo-anneal verify` Verdict (`[real measurement]`) | Axioms & Taint |
| :--- | :--- | :---: | :--- | :--- |
| **`01_usize_pointer_metadata`** (`<usize as PointerMetadata>::{from,to}_elem_count`, 2 safe bodies + `#[anneal::pure]` helper) | `28` LOC Rust (`01_usize_pointer_metadata_spec.rs`) → `65` LOC `Spec.lean` | `06d5b878682f92cb...` | **`selected_unit_verified`** (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| **`02_unit_pointer_metadata`** (`<() as PointerMetadata>::{from,to}_elem_count`, 2 safe bodies + `#[anneal::pure]` helper) | `28` LOC Rust (`02_unit_pointer_metadata_spec.rs`) → `65` LOC `Spec.lean` | `f334bf31821b9a56...` | **`selected_unit_verified`** (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| **`03_macros_unsafe`** (`util::macros::__unsafe`, 1 `const unsafe fn` body) | `16` LOC Rust (`03_macros_unsafe_spec.rs`) → `46` LOC `Spec.lean` | `dcc50ebd52c70015...` | **`selected_unit_verified`** (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| **Negative Control (`Pole A`)** (`03_macros_unsafe` with `ensures(\|_ret\| false)`) | `Spec.lean` admitted by `spec-preflight`; proof cleanly rejected | — | **`proof_failed`** (`rc = 1`, `phase = "audit"`, `0` crashes) | Rejected fail-closed |

Unit tests (`9/9 PASS` in `0.009s` `[real measurement]`) additionally verify: deterministic lowering, `U1` safe-vs-unsafe `requires` split, byte-identical output between inline `#[cfg_attr(anneal, anneal::spec(...))]` and out-of-tree `anneal::external_spec!`, fail-closed rejection of eager `&` (`M9`), imperative statement blocks and assignments (`M7`/`M8`), bare ambiguous arithmetic (`M12`), unresolved typo identifiers (`M12`), and UTF-8 `Spec.lean` → Rust `file:line:col` diagnostic reverse mapping.

---

# Partition 2: Decision Rationale & Eliminated Alternatives

Every architectural alternative below was evaluated against `(C+1..C+6, C-1..C-4)` and `PROBED` compiler/corpus evidence:

| Design Axis | Eliminated Alternative | Elimination Basis (`PROBED` Evidence / Contract Violation) | Selected Architecture |
| :--- | :--- | :--- | :--- |
| **1. `zerocopy` Attachment & MSRV (`1.56.0`)** | **Mandatory `anneal-spec` proc-macro dependency in `zerocopy/Cargo.toml`** (even optional or dev-linked). | **Violates `C+1` (`[source inspection]` `zerocopy/Cargo.toml:30`, `POLICIES.md:96-106`):** Adds dependency/syn MSRV exposure, host-vs-target `RUSTFLAGS` proc-macro `cfg` friction (`joshlf/anneal:unstable`), and downstream compile-time weight. | **Zero-dependency dual attachment:** out-of-tree `zerocopy/proofs/*.rs` (`anneal::external_spec!`, `0` edits to `zerocopy/`) + optional inert `#[cfg_attr(anneal, anneal::spec(...))]` (`0` deps, 1 `check-cfg` line in `build.rs`, verified `rc=0` on `rustc 1.56.0` & `1.100.0` `[real measurement]`). |
| **2. Comment-Embedded DSL** | **Fenced doc-comment DSL (`/// ```anneal ...`) or `// SAFETY:` extraction** (Anneal Gen 0 / Gen 1 `#2777`, `#3062`, `#3086`). | **Disqualified (`C-3` + `PROBED` comment-drift studies in `origin/reference`):** Invisible to `rustc` token validation and IDE refactoring (`>50%` rename drift in `Fraco`), fragile indentation parsing (`#3086`), and conflated Lean internals with Rust source (`#3697`). | Real balanced Rust token trees (`#[cfg_attr(anneal, anneal::spec(...))]` / `external_spec!`) with full UTF-8 span provenance. |
| **3. Exclusive Upstream `core::contracts` (`#128044`)** | **Rely solely on nightly `#![feature(contracts)]` (`#[core::contracts::{requires, ensures}]`).** | **Falsified (`[real measurement]` on `1.98.0-nightly` & `1.102.0-nightly`, `C+1` + `C+3`):** Fails on stable `rustc` & MSRV `1.56.0`; `build_check_ensures` requires `Fn(&Ret) -> bool + Copy + 'static` (blocking `&T`/`&mut T` postconditions); permits at most 1 `requires`/`ensures`; allows dead-branch outer side effects (`#139548`); lacks `old()`, `modifies(...)`, `#[pure]`, and pointer/alignment predicates. | Ingest `core::contracts` as an L1 compatibility frontend in Profile v2, while providing `anneal::spec` / `external_spec!` for full MSRV-clean systems-Rust expressivity (`C+1`, `C+3`). |
| **4. Bespoke Full-Module Verifier DSL** | **Whole-module macro wrapper (`verus! { ... }`) or embedded logic string DSL (`pearlite!`, RefinedRust `#[rr::ensures("...")]`).** | **Violates `C+1` & `#3697` (`[source inspection]`):** `verus!{}` breaks `rustfmt`, `rust-analyzer`, and unmodified `zerocopy` builds (requiring a parallel AST stripper); string-literal Rocq/Lean embeddings lack Rust syntax structure and leak prover internals. | Attribute/companion-item grammar over standard Rust expressions + minimal explicit spec intrinsics (`old`, `math`, `wrapping_*`, `aligned_to`, `valid_read`, `disjoint`). |
| **5. TCB Placement of Surface Lowering** | **Parse Rust contracts inside `TrustedBoundary.lean` or add a Rust AST expression interpreter to `Trusted/MirSemantics/`.** | **Violates `C+2` & `C-1`:** Expands `anneal/trusted/lean/` by `>1,500` LOC of complex string/AST parsing and creates a second Rust operational semantics that can drift from `MirSemantics`. | **Pure pre-elaboration lowering outside `trusted/lean/` (`0` Lean TCB LOC):** emit declarative `Spec.lean` checked by existing `"spec-preflight"` (Profile v1/v2) + `SpecEval` over single `MirSemantics` (Profile v2). |
| **6. Arithmetic & Clause Conjunction Semantics** | **Silent Lean `Nat` lowering of `+`/`-`/`/` OR eager bitwise `&` clause conjunction (`anodized#240`).** | **Falsified (`[kernel-checked proof]` `M9`, `M12`):** `Nat.sub` silently turns `0 - 1` into `0` (accepting buggy underflows); eager `&` panics/UBs on guarded clauses `requires(i < s.len() & s[i] == 0)`. | Reject bare machine arithmetic (`E_ANNEAL_AMBIGUOUS_SPEC_ARITH` → explicit `math(...)` vs. `wrapping_*`) and reject boolean `&` (`E_ANNEAL_EAGER_CLAUSE_JOIN` → short-circuiting `&&`). |

---

# Partition 3: Open Human Decisions & Epistemic Calibration

## 1. Open Policy Decisions for `joshlf`

All four choices below are **strictly policy-invariant with respect to the core lowering architecture** (both attachment forms and policy thresholds share identical AST, typechecker, and `Spec.lean` codegen plumbing):

### Decision `D1` — Default Contract Placement Policy in `google/zerocopy`
- **Question:** For `zerocopy` itself (`zerocopy/src/` vs. `zerocopy/proofs/`), where should authored Rust-syntax contracts live by default?
- **Options:**
  - **Option A (Recommended — High Confidence, Default): Out-of-tree `zerocopy/proofs/<unit>/spec.rs` (`anneal::external_spec!`) for Phase 1, permitting opt-in inline `#[cfg_attr(anneal, anneal::spec(...))]` once `cfg(anneal)` is added to `zerocopy/build.rs`.** Keeps `zerocopy/src/` 100% untouched during rapid proof scale-up while allowing maintainers to co-locate stabilized contracts next to `// SAFETY:` comments later with zero rewrites.
  - **Option B: Inline `#[cfg_attr(anneal, anneal::spec(...))]` directly in `zerocopy/src/*.rs` from Day 1** (adding 1 `cargo:rustc-check-cfg=cfg(anneal)` line to `zerocopy/build.rs`). Co-locates contracts with `#[cfg_attr(kani, ...)]` immediately, at the cost of touching `zerocopy/src/` on spec-only PRs.
  - **Option C: Out-of-tree `zerocopy/proofs/` exclusively** (forbid `cfg_attr(anneal, ...)` in `zerocopy/src/`).
- **Blast radius:** Repository layout convention + 1 line in `zerocopy/build.rs`; `0` TCB or lowering changes.

### Decision `D2` — Human Review Surface in PRs: Rust Contract Alone vs. Committed `Spec.lean`
- **Question:** When a PR adds or modifies a surface contract (`spec.rs` or `#[cfg_attr(anneal, ...)]`), should `Spec.lean` also be committed into `zerocopy/proofs/<unit>/` for human diff review, or generated ephemerally during `cargo-anneal verify`?
- **Options:**
  - **Option A (Recommended — High Confidence, Default): Commit both `spec.rs` AND deterministic `Spec.lean` (emitted with explicit `Int.ofNat` / `BitVec.ofNat` constructors, zero `↑` coercions) during Stage 1 (`#4012`), transitioning to Rust-only review once the surface compiler is SHA-pinned in `cargo-anneal`'s release bundle.** Gives `THREAT_MODEL.md` reviewers 100% unambiguous visibility into the exact Lean `Prop` during alpha/Stage 1 (avoiding Lean delaborator coercion-elision drift) while eliminating hand-written Lean authoring immediately; CI checks `lower(spec.rs) == Spec.lean` fail-closed.
  - **Option B: Commit only `spec.rs`** and materialize `Spec.lean` ephemerally in `cargo-anneal` staging. Smaller PR diffs, **but** implicitly adds the surface-to-`Spec.lean` compiler (`~800` LOC Rust) to the specification-meaning TCB unless reviewers inspect build artifacts.
- **Blast radius:** `verify_zerocopy.py` / `cargo-anneal` staging check and `THREAT_MODEL.md` review-surface accounting.

### Decision `D3` — Machine Arithmetic Default in Spec Clauses (`E_ANNEAL_AMBIGUOUS_SPEC_ARITH`)
- **Question:** Should `a + b` / `a - b` on `usize`/`u32` inside `#[anneal::spec(...)]` require explicit disambiguation (`math(a) + math(b)` vs. `wrapping_add(a, b)`), or implicitly lift to unbounded mathematical `Int` (Verus/Pearlite style)?
- **Options:**
  - **Option A (Recommended — High Confidence, Default): Require explicit `math { ... }` / `math(...)` or `wrapping { ... }` / `wrapping_*` on `+`, `-`, `*`, `/`, `%` (`E_ANNEAL_AMBIGUOUS_SPEC_ARITH`).** Aligns with `zerocopy`'s `clippy::arithmetic_side_effects = "deny"` discipline, keeps multi-term `layout.rs` bounds readable via scoped `math { ... }` blocks, and eliminates silent wrap-vs-`Int` confusion with a 1-second compiler fix suggestion.
  - **Option B: Implicitly lift `+`, `-`, `*` in spec clauses to mathematical `Int`** (requiring `wrapping_*` only when modular wraparound is intended). More concise (`left.len() + right.len() == s.len()`), but diverges from executable Rust `#[cfg(test)]` / `SpecEval` checked arithmetic.
- **Blast radius:** Single typechecker rule in the surface spec compiler (`0` Lean TCB impact).

### Decision `D4` — Surface Syntax Dialect Alignment (`#[anneal::spec(...)]` vs. `anodized` `#[spec(...)]`)
- **Question:** Should Anneal's primary Rust surface syntax use functional call clauses (`requires(P), ensures(|r| Q), modifies(...)` — aligned with `core::contracts`, Kani, and `verify-rust-std`) or `anodized`'s struct-field syntax (`requires: P, maintains: ..., captures: ..., ensures: |r| Q`)?
- **Options:**
  - **Option A (Recommended — High Confidence, Default): Canonical `#[anneal::spec(requires(...), ensures(|r| ...), modifies(...), total)]` (matching `zerocopy`'s existing `29` `kani::ensures` / `11` `kani::requires` annotations), while accepting `anodized::spec` colon/array syntax as an L2 frontend alias.** Zero migration friction for `zerocopy`'s `63` Kani harnesses and `verify-rust-std`.
  - **Option B: Adopt `anodized` colon/struct-initializer syntax as the canonical Anneal surface.**
- **Blast radius:** Parser surface production in `anneal-spec-lower`; identical `SpecUnitAST` and `Spec.lean` output.

---

## 2. Epistemic Calibration & Verification Ledger

- **Stopping Status:** `bounded stop` — all discriminating technical premises (`rustc 1.56.0` / `1.100.0` `cfg_attr` zero-dep compilation, `spec-preflight` closed-allowlist compatibility, `U1` safe-vs-unsafe precondition split, deterministic `Spec.lean` emission, UTF-8 span reverse mapping, and end-to-end `linux_bwrap` `cargo-anneal verify` on real `zerocopy/src/` functions) are **`PROBED: confirmed`**. Stopped cleanly prior to production repository edits pending human sign-off on `D1`–`D4`.
- **Deliverability:** **Qualified Partial Spec (Standalone RFC)** + isolated verified companion prototype (`h1_surface_spec/`). Zero production files or tracked repository docs in `google/zerocopy` were modified.
- **Mandatory Stage 2 Pre-Delivery Read-Only Audit:** Passed (`6/6` checks: direct compliance with `C+1..C+6` and `C-1..C-4`; zero hardcoded policy defaults presented as structural necessities; explicit attribution of `build.rs` `check-cfg` and `Spec.lean` commit trade-offs; zero unfactored runtime knobs; zero unaccepted superset-taxed boundaries; zero falsified claims treated as viable).
- **Primary Evidence Summary:**
  1. `rustc +1.56.0`, `+1.100.0`, `+nightly-2026-05-31`, `+nightly-2026-09-30` live probes (`[real measurement]`): confirmed `rc = 0` (`0` warnings under `#![deny(warnings)]`) for `#[cfg_attr(anneal, anneal::spec(...))]` with `==>`, `<==>`, and zero `Cargo.toml` dependencies once `--check-cfg=cfg(anneal)` is set on `>= 1.77`.
  2. Live `cargo-anneal verify` (`[real measurement]`): verified 3 real `zerocopy/src/` proof packages (`<usize as PointerMetadata>::{from,to}_elem_count`, `<() as PointerMetadata>::{from,to}_elem_count`, and `util::macros::__unsafe` — 5 real `zerocopy/src/` functions across 3 units) lowered from `contracts/*.rs` → `Spec.lean` → `spec-preflight` → `linux_bwrap` elaboration → fresh kernel replay (`status = "selected_unit_verified"`, `axioms = ["propext"]`, `taint_reasons = []`), plus negative mutation control (`status = "proof_failed"`).
- **Explicit Boundaries Not Yet Exercised in Live `cargo-anneal` (`[projected]`):**
  - Profile v2 pointer/slice intrinsics (`aligned_to`, `valid_read`, `is_init`, `disjoint`, `slice_len`, `old(...)`, `modifies(p)`) are specified in §3.2–3.3 and align 1-to-1 with `arch_spec_core_v2.md` and Profile v2 Waves 2–4 (`profile_v2_zerocopy_master_plan.md`), but cannot execute through stock `main` `cargo-anneal` until `MirSemantics` Waves 2–3 (`callerMem` + fat slices + `Contract.lean`) merge onto `google/zerocopy:main`.
