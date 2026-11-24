# Anneal High-Level Surface Specification Language (`#[anneal::spec]` & `anneal::external_spec!`)

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

This report records the pre-implementation architectural specification (`google/zerocopy#4102`, `#3697`, `#3091`, `#3203`) for Anneal's high-level Rust surface specification language (`#[cfg_attr(anneal, anneal::spec(...))]` and `anneal::external_spec!`) and its zero-TCB deterministic compiler into Lean 4 `Spec.lean` (`TargetRole::Specification`):

1. **Zero-MSRV, Zero-Dependency Attachment (`[real measurement]`):** Out-of-tree companion specifications (`zerocopy/proofs/<unit>/spec.rs` via `anneal::external_spec!`) require `0` edits to `zerocopy/src/` or `zerocopy/build.rs` and `0` Cargo dependencies (`zerocopy/Cargo.toml` excludes `/proofs`, preserving MSRV `1.56.0`). Inline inert attributes (`#[cfg_attr(anneal, anneal::spec(...))]`) also compile with `0` dependencies (`rc = 0`, `0` warnings under `#![deny(warnings)]` on `rustc +1.56.0`, `+1.100.0`, and `nightly` once `println!("cargo:rustc-check-cfg=cfg(anneal)");` is added to `build.rs` for `rustc >= 1.77.0`).
2. **Zero Lean TCB Bloat & Existing `spec-preflight` Admission:** All parsing, name resolution, trap checking, and Lean codegen run outside `anneal/trusted/lean/` (`0` Lean TCB LOC). The compiler emits tactic-free, quotation-free, coercion-free declarative Lean 4 (`Int.ofNat`, `BitVec.ofNat`, `Int.tdiv`—never overloaded `↑` coercions) admitted unchanged by `TrustedBoundary.lean`'s 14-command `"spec-preflight"` gate (`lines 1258–2089`).
3. **Trap-Free Logic, Safe-Callable Law (`U1`), & Out-of-Key Span Map:** Enforces `safetyPre` (`isUnsafe = true` only) vs. `behaviorPre` (`isUnsafe = false` never waives UB), rejects eager bitwise `&` clause joins (`anodized#240`), requires explicit `math { ... }` vs. `wrapping_*` arithmetic (preventing silent `Nat.sub` saturation and `/ 0` totalization), emits `spec_span_map.json` outside `Spec.lean` (1-based lines, 1-based Unicode scalar columns matching `lean --json` without invalidating `MirItemKey` caches on whitespace edits), and integrates `preInhabited`, `witness`/`must_reject`, and `.anneal/spec-lock.json` anti-vacuity checks.
4. **Live End-to-End Prototype Verification (`[real measurement]`):** Stock `cargo-anneal verify` (`linux_bwrap` `ExecSeal`, `0` TCB lines modified) verified `5` unmodified `zerocopy/src/` functions across `3` units (`<usize as PointerMetadata>::{from,to}_elem_count`, `<() as PointerMetadata>::{from,to}_elem_count`, `util::macros::__unsafe`) with `axioms = ["propext"]`, `taint: []`, and rejected a `Pole A` negative mutation (`ensures(|_ret| false)` -> `proof_failed`).

Full specification grammar, semantics, and policy options (`D1`–`D4`) are preserved in [support/surface_spec_language_rfc.md](support/surface_spec_language_rfc.md).

## Applicability

- **Target Baseline:** `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/trusted/cargo-anneal/src/{verify,target,stage}.rs`, `zerocopy/Cargo.toml` MSRV `1.56.0`, `zerocopy/build.rs`, `zerocopy/proofs/`).
- **Compiler & Prover Coverage:** Live `rustc` attribute checks executed on `1.56.0`, `1.100.0` (`pinned-stable`), `nightly-2026-05-31` (`f8a08b688`), and `nightly-2026-09-30`; Lean verification executed under Lean `v4.34.1`.
- **Profile Split:** Scalar/pure clauses (`wrapping_*`, `no_overflow_*`, `math { ... }`, `is_power_of_two`, `requires`, `ensures`, `cases`, `total`, `terminates`, `no_panic`, `preInhabited`) target Profile v1 today; pointer/memory/borrow clauses (`aligned_to`, `valid_read`, `valid_write`, `is_init`, `same_alloc`, `in_bounds`, `disjoint`, `slice_len`, `view`, `old(...)`, `modifies(p)`, `after_expiry`) target Profile v2 Waves 2–4.

## Findings

### Zero-MSRV Dual-Attachment Architecture (`[real measurement]`)

Basis: `execution` (`rustc +1.56.0`, `+1.100.0`, `+nightly-2026-05-31`, `+nightly-2026-09-30`) + `source` (`zerocopy/Cargo.toml:30`, `zerocopy/build.rs:92`).

- **Out-of-tree `zerocopy/proofs/<unit>/spec.rs` (`anneal::external_spec!`):** Zero edits to `zerocopy/src/` or `build.rs`; `zerocopy/Cargo.toml` already excludes `proofs/`. Works identically on unowned third-party crates and `core`.
- **Inline `#[cfg_attr(anneal, anneal::spec(...))]`:** Inactive `cfg_attr` payloads containing `==>` / `<==>` compile on `rustc +1.56.0 --edition=2021` under `#![deny(warnings)]` with exit `0` and `0` dependencies (parsed solely as balanced `TokenStream`s). On `rustc >= 1.77.0` (`+1.100.0`), `unexpected_cfgs` requires `println!("cargo:rustc-check-cfg=cfg(anneal)");` in `zerocopy/build.rs` (matching `cfg(kani)` at line 92).
- **Single AST (`SpecUnitAST`):** Both forms lower through the same compiler to byte-identical `Spec.lean` (`9/9` prototype unit tests pass in `0.009 s` `[real measurement]`).

### Surface Grammar, Safe-Callable Law (`U1`), and Trap Elimination

Basis: `normative` (`Boundary.lean:238`, `TrustedBoundary.lean:1258-2089`) + `derived` + `[kernel-checked proof]`.

- **Clause Set (`SpecClause`):** `requires`, `ensures`, `ensures_err`, `after_expiry`, `cases(G_i => Q_i)` (emitting completeness, pairwise disjointness, and per-branch implication), `modifies(none | p1, ...)` (mandatory on `unsafe fn` taking `*mut T`), `unwinds_if`, `ensures_unwind`, `decreases`, `witness`, `must_reject`, effect qualifiers (`total | terminates | no_panic | no_unwind | no_abort`), and `#[anneal::pure]`.
- **Safe-Callable Law (`U1`):** `safetyPrecondition` includes `pre_i` **iff** `body.isUnsafe = true`. Safe functions (`isUnsafe = false`) have `safetyPre = True` (must prove `WellFormed` on all `FullValid` inputs), while `requires(P)` populates `behaviorPre` gating `ensures`/`modifies`/`EffectMask`.
- **`after_expiry` Without Prophetic Axioms:** Because `MirSemantics` represents `&mut` concretely as `(AllocId, Offset, TbTag)` in `out.callerMem`, `after_expiry(|ret| Q_end)` lowers via `Anneal.PureLift.ByteSubLens` / `LoanGraph` with `0` prophetic axioms in `trusted/lean/` (`final(...)` rejected in `requires` and runtime code).
- **Trap-Free Logic (`TrapFreeHumanSpecAST`):** Bare `+`, `-`, `*`, `/`, `%` on machine-width types outside `math { ... }` / `wrapping { ... }` fail with `E_ANNEAL_AMBIGUOUS_SPEC_ARITH`; bare `&` fails with `E_ANNEAL_EAGER_CLAUSE_JOIN`; unguarded `/` or `%` inside `math { ... }` fails with `E_ANNEAL_UNGUARDED_SPEC_DIV`; `old(...)` inside `requires` fails with `E_ANNEAL_OLD_IN_PRECONDITION`; ghost intrinsics in runtime code fail with `E_ANNEAL_GHOST_IN_RUNTIME`.
- **Explicit Constructors Over Coercions:** Lean `v4.34.1` pretty-printing can elide `↑` even with `pp.coercions true`; the emitter writes explicit `Int.ofNat`, `BitVec.ofNat 64`, `Int.tdiv`, `Int.tmod`. Raw `Spec.lean` hardening additionally recommends `-DautoImplicit=false -DrelaxedAutoImplicit=false` and banning `Nat.{sub,div,mod}`, `getElem!`, `head!`, `get!`.

### Deterministic Lowering, Out-of-Key Span Map, Anti-Vacuity, and Prototype Receipt

Basis: `execution` (`cargo-anneal verify`, `[real measurement]`) + `source` (`TrustedBoundary.lean:1258-2089`).

- **`spec_span_map.json`:** Stored outside `Spec.lean` (so comment/whitespace edits in Rust never mutate `specification_manifest_sha256` or `MirItemKey`), recording `(file, start_byte..end_byte, lo_line:lo_col..hi_line:hi_col)` in 1-based Unicode scalar columns (`col_rust = col_lean + 1` matching `lean --json`).
- **Constructive Anti-Vacuity (`#4102`):** Every `<unit>Spec` conjoins `preInhabited` (`∃ args, pre_i args` unless `#[anneal::vacuous_ok(reason = "...")]` is declared), optional `witness`/`must_reject` ground checks, byte-locked `sha256(Spec.lean)` for Dual-Polar Mutation Refutation (`Pole A ∧ Pole B`), and `.anneal/spec-lock.json` verification.
- **Prototype Execution Against Unmodified `zerocopy/src/` (`[real measurement]`):**

| Unit (`zerocopy/src/` Target Items) | Contract -> `Spec.lean` | `Spec.lean` SHA-256 prefix | `cargo-anneal verify` Verdict | Axioms & Taint |
| :--- | :--- | :--- | :--- | :--- |
| `01_usize_pointer_metadata` (`<usize as PointerMetadata>::{from,to}_elem_count`) | `28` LOC -> `65` LOC | `06d5b878682f92cb...` | `selected_unit_verified` (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| `02_unit_pointer_metadata` (`<() as PointerMetadata>::{from,to}_elem_count`) | `28` LOC -> `65` LOC | `f334bf31821b9a56...` | `selected_unit_verified` (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| `03_macros_unsafe` (`util::macros::__unsafe`) | `16` LOC -> `46` LOC | `dcc50ebd52c70015...` | `selected_unit_verified` (`exactType: true`, `linux_bwrap`) | `["propext"]`, `taint: []` |
| Negative Control (`Pole A`, `03_macros_unsafe` with `ensures(\|_ret\| false)`) | `Spec.lean` admitted by `spec-preflight` | — | `proof_failed` (`rc = 1`, `phase = "audit"`) | Rejected fail-closed |

- **Eliminated Alternatives:** Mandatory proc-macro dep in `zerocopy/Cargo.toml`, fenced doc-comment DSLs, relying solely on nightly `core::contracts` (`E0597` `C: 'static`, no `old()`, no `modifies`), whole-module `verus!{}` wrappers, parsing Rust inside `TrustedBoundary.lean`, and silent Lean `Nat` / eager `&` semantics.

## Boundaries

- **Profile v2 clauses (`not examined` in live `cargo-anneal`):** Pointer/slice intrinsics (`aligned_to`, `valid_read`, `is_init`, `disjoint`, `slice_len`, `old(...)`, `modifies(p)`, `after_expiry`) cannot execute through stock `main` `cargo-anneal` until `MirSemantics` Waves 2–3 (`callerMem`, fat slices, `Contract.lean`) merge onto `google/zerocopy:main`.
- **Pre-implementation specification (`not yet implemented` in `google/zerocopy`):** Production `cargo-anneal` does not yet ship the Rust surface spec compiler (`lower_surface_spec.py` prototype was used to verify lowered `Spec.lean` outputs).
- **Pending policy choices (`unknown`):** Four policy choices (`D1`: default out-of-tree vs. inline placement; `D2`: committing generated `Spec.lean` alongside `spec.rs`; `D3`: mandatory explicit `math`/`wrapping` vs. implicit `Int` lifting; `D4`: functional `#[anneal::spec(...)]` vs. `anodized` colon syntax) await maintainer decision.
- **Non-goals (`known not to apply`):** Automated anti-vacuity checks do not replace human specification review (`THREAT_MODEL.md` §2.2); OS durability/concurrent protocol specs (`assumes_world`/`on_crash` seam) remain outside Profile v1–v2.

## Evidence

- **Primary archived RFC:** [support/surface_spec_language_rfc.md](support/surface_spec_language_rfc.md) (`339` lines, observed `2026-11-23`).
- **Source baselines:** `google/zerocopy@d3362d9a657e2f943d25a0812f7b13b93e60af4d` (`anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean:238`, `anneal/trusted/audit/TrustedBoundary.lean:1258-2089`, `anneal/trusted/cargo-anneal/src/{verify,target,stage}.rs`, `zerocopy/Cargo.toml:30`, `zerocopy/build.rs:92`).
- **Live compiler & verifier runs (`[real measurement]`):** `rustc +1.56.0`, `+1.100.0`, `+nightly-2026-05-31`, `+nightly-2026-09-30` (`rc = 0`, `0` warnings with `--check-cfg=cfg(anneal)` on `>= 1.77`), `9/9` prototype compiler tests (`0.009 s`), and `cargo-anneal verify` (`linux_bwrap` `ExecSeal`) over `5` unmodified `zerocopy/src/` functions + `Pole A` negative mutant.

## Revalidation

1. Re-run `rustc +1.56.0 --edition=2021 --crate-type=lib` (`#![deny(warnings)]`) and `rustc +1.100.0 --check-cfg=cfg(anneal)` on a sample `#[cfg_attr(anneal, anneal::spec(requires(a ==> b), ensures(|r| r <==> true)))]` item if `zerocopy`'s MSRV or `pinned-stable` toolchain changes.
2. Inspect `TrustedBoundary.lean`'s `"spec-preflight"` command/declaration allowlists (`lines 1258–2089` at `d3362d9a657e`) and `Boundary.lean` / `Contract.lean` when Profile v2 merges onto `google/zerocopy:main`.
