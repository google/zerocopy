# Proof Kernels, Opaque Interfaces, and Adversarial Specification Hardening

## Summary

Scaling formal verification from isolated mathematical proofs to compiler-scale, multi-module, and agent-authored artifacts exposes three coupled failure modes across proof kernels, serialized module formats, and formal specifications:

1. **Dependent-type kernel reduction cliffs**: Call-by-name weak-head normal form (WHNF) kernels hit discontinuous asymptotic cliffs on compiler-scale derivations. Source inspection of `leanprover/lean4` (`v4.14.0` and HEAD `8009d0a64d2860606c6a5ac5ff6702622b24921e`) pinpoints four mechanisms: (a) recursive C++ WHNF (`whnf_core`) and reference-count cache bypasses (`is_likely_unshared` in `replace_fn.h` / `expr.h`) that trigger stack exhaustion or quadratic suffix cloning; (b) free-variable guards around GMP `Nat` reduction—inside `reduce_nat` in `v4.14.0` (`type_checker.cpp:621`) and still inside `lazy_delta_reduction` at HEAD (`type_checker.cpp:1067`, `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`)—that silently degrade $O(1)$ arithmetic into unary Peano `Nat.rec` whenever a `let`-bound local appears during conversion without `eagerReduce`; (c) missing native kernel reducers for `String` and `ByteArray`, forcing `string_lit_to_constructor` (`inductive.cpp:1358-1370`) to expand literals into `String.ofList (List.cons (Char.ofNat ...) ...)`; and (d) kernel unfoldability of `.thmInfo` proof bodies (`declaration.h:447-449`, `type_checker.cpp:547,723`) alongside Meta-only `@[irreducible]` annotations, contrasting with kernel-enforced opacity in Rocq (`OpaqueDef`, `cClosure.ml:468,2088`) and Agda (`OpaqueBlock`, `Reduce.hs:750-763`).
2. **Memory-unsafe binary object loaders and conflated proof archives**: Lean 4's `lean_compacted_region_read` (`module.cpp:424-613`, `compact.cpp:474-688`) dereferences an unchecked `data_size` field before validating file bounds, patches raw closure pointers via unchecked `closure_offsets`, skips validation on the zero-relocation fast path, and bundles multi-megabyte proof terms with consumer signatures. Rocq `.vo` (`lib/objFile.ml:105-114`) and Lambdapi `.lpo` (`src/core/sign.ml:268-294`) invoke OCaml's memory-unsafe `Marshal.from_channel` (in Rocq, *before* verifying a 16-byte MD5 digest). Conversely, Metamath Zero (`digama0/mm0`, `mm0-c/verifier.c`: 819 LOC C, 85 `ENSURE` bounds/tag checks) strictly separates compact `.mm0` interfaces from bounds-checked `.mmb` proof streams, and `nanoda_lib` (v0.4.32, zero `unsafe` blocks, `overflow-checks = true`) eliminates deserialization UB via structured NDJSON (`lean4export`)—though Lean 4 conversion compatibility forces it to inherit the same `has_fvar`, string-expansion, and `.thmInfo`-unfolding semantics.
3. **Adversarial Goodhart resistance in formal specifications**: Under automated or LLM-driven synthesis, optimization pressure systematically exploits six algebraic specification loopholes: (1) miracle target compilers (`Beh_tgt = ∅`), (2) domain collapse (`dom = False`), (3) observation codec erasure (`Obs = Unit`), (4) lying byte emitters and circular parser oracles, (5) circular reference-correspondence adapter hooks (postmortem in `joshlf/anneal@6b09691a2820d0608034e1468b8685a0dccddb77`), and (6) positive-only TCB rot via guard-weakened operational semantics. Hardening contracts with productivity preservation, pinned witness domains, injective codecs, end-to-end byte decoding over hash-pinned ISAs, hash-locked unmodified reference oracles, and automated semantic mutation testing killed by negative refutation canaries blocks 100% of these exploits while admitting sound compilers and conservative static analyzers. The preserved probe `support/verify_goodhart_spec_defenses.py` mechanically confirms naive refinement accepts 7/7 exploits (and 5/5 guard-weakened semantics mutants pass 100% of positive proofs), while hardened contracts reject 7/7 exploits, kill 5/5 mutants, and admit 4/4 honest tools.

## Applicability

This package applies to engineers and researchers designing or auditing dependent-type proof kernels, external proof verifiers, cross-module binary proof interfaces, and formal compiler or verifier harnesses—especially under untrusted or agent-generated proofs.

### Examined Subjects and Version Scope

- **Lean 4 version split**: Directly compares `leanprover/lean4` `v4.14.0` (`410fab7284703f41660ca2454218dcca9b2ec896`) against HEAD (`8009d0a64d2860606c6a5ac5ff6702622b24921e`), plus tags `v4.20.0`, `v4.25.0`, `v4.27.0`, `v4.28.0`, `v4.30.0`, `v4.34.1`, `v4.35.0` and commits `6e18afac8c`, `85e209a57b`, `44a3664c18`, `2a7175c74b`, and `ff3982f0c8`. Findings separate removed `v4.14.0` behavior (`reduce_nat`'s top-level `has_fvar` bailout and `reduce_native`) from persistent HEAD behavior (`lazy_delta_reduction`'s `has_fvar` guard, `string_lit_to_constructor`, `.thmInfo` unfolding in `whnf`, and unsafe `.olean` loading).
- **Cross-prover architecture comparison**: Directly inspects `rocq-prover/rocq` (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`), `agda/agda` (`9691cf2331ed3d5f9aba04380cc1cc8f415d192e`), `digama0/mm0` (`0d414c0bfdaaeb7fea571895127abc1fa5a3d956`), `ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, v0.4.32), and `Deducteam/lambdapi` (`b7e9e0a0ae09b16a8841bbce1c7bfceb013ff3e3`).
- **Trust-boundary and correspondence case study**: Directly inspects `joshlf/anneal` public `main` (`08f1184dce262d8d3ab610d4becedc3a0ae4486c`) and correspondence-hardening commit `6b09691a2820d0608034e1468b8685a0dccddb77`.
- **Literature and executable probe**: Grounded in Pollack (1998), Leroy (2009), Fonseca et al. (2017), Carneiro (2020), Wang et al. (2020), and Amaral et al. (2026), plus the standalone Python 3.10+ finite-state probe `support/verify_goodhart_spec_defenses.py`.

### Cross-References to Adjacent Corpus Packages

This report avoids duplicating Rust- and Lean-specific benchmark tables preserved in five adjacent packages:

- `lean-kernel-derivation-scale-checking-and-reflection-throughput`: Empirical Lean 4 step-count cliffs and CPS spine-forcing benchmarks (`N = 10^3` to `10^6`).
- `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`: Lean 4 RSS memory ceilings, auto-synthesized eliminator overhead, and `.thmInfo -> .axiomInfo` stripping economics.
- `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`: OS sandboxing (`seccomp-bpf`, Landlock, bubblewrap), elaborator effect isolation, and multi-kernel replay toolchains (`SafeVerify`, `Comparator`, `lean4checker`).
- `anneal-universal-algebra-institutions-and-incompleteness-bounds`: Meta-theoretic Gödel–Tarski–Löb impossibility bounds on object-level axiom hygiene.
- `anneal-vacuity-mutation-oracles-and-verification-scaling`: Rust/Anneal-specific vacuity detection and mutation-oracle scaling pipelines.

## Findings

### 1. Dependent-Type Kernel Reduction Cliffs at Compiler Scale

Basis: source + documentation + derived

When dependent-type kernels check compiler-scale reflective derivations, four concrete implementation choices create discontinuous performance and stack cliffs.

| System & Pinned Revision | Reduction Engine & Stack | Native `Nat` / Bignum Fast Path | Native `String` / `ByteArray` Reducer | Kernel Theorem Opacity | Compiled In-Kernel Evaluator |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Lean 4 `v4.14.0`** (`410fab72...`) | Recursive C++ `whnf_core` (call-by-name) | GMP `reduce_nat`, gated by `if (has_fvar(e))` in `reduce_nat` (`:621`) and `lazy_delta_reduction` (`:989`) | None (`string_lit_to_constructor` -> `List Char`) | **No** (`has_value(false)` true for `.thmInfo`); `@[irreducible]` Meta-only | Deprecated `reduce_native` (`Lean.reduceBool`/`reduceNat`) |
| **Lean 4 HEAD** (`8009d0a6...`) | Recursive C++ `whnf_core` with `maxRecDepth` (`85e209a57b`) | GMP `reduce_nat` (15 ops, 128 MB `LEAN_NAT_MAX_SIZE`); **still gated** by `(!has_fvar(t_n) && !has_fvar(s_n)) \|\| m_eager_reduce` in `lazy_delta_reduction` (`:1067`) | None (`string_lit_to_constructor` -> `String.ofList (List.cons ...)` at `inductive.cpp:1358-1370`) | **No** in `whnf` (`declaration.h:447-449`, `type_checker.cpp:547,723`); proof-irrel moved earlier in `is_def_eq_core` (`:1155`, PR `#15103`) | Removed in `2a7175c74b` (PR `#14953`); `eagerReduce` hint (`6e18afac8c`) |
| **Rocq** (`25f5b18a...`) | Explicit heap-allocated Krivine/zipper stack (`cClosure.ml:199-230`: `Zapp`, `ZcaseT`, `Zproj`, `Zfix`, `Zupdate`) | Primitive `Uint63` / `Sint63` / `Float64` / `PArray` via `Zprimitive` | Native persistent arrays (`PArray`) & primitive strings via `Zprimitive` | **Yes**: `OpaqueDef` (`Qed`) raises `NotEvaluableConst Opaque` (`cClosure.ml:468`), neutral at `:2088` | `vm_compute` (`vconv.ml`) & `native_compute` (`nativeconv.ml`) |
| **Agda** (`9691cf23...`) | Haskell lazy `ReduceM` (`Reduce.hs`) | Builtin `Nat` / `Integer` / `Word64` (`Primitive`, `Reduce.hs:771-776`) | Builtin `String` / `Char` via `primFunImplementation` (`Reduce.hs:798-814`) | **Yes**: `unfoldDefinitionStep` blocks `prp == Right True`, `isIrrelevant`, and `OpaqueBlock` (`Base.hs:5061`, `Reduce.hs:750-763`) | GHC/JS backends (outside kernel conversion) |
| **`nanoda_lib` v0.4.32** (`0da9f98f...`) | Safe Rust recursive `whnf` (`src/tc.rs:797-874`) | `num_bigint::BigUint` (`do_nat_bin`), mirroring `(!has_fvars(x) && !has_fvars(y)) \|\| eager_mode` (`tc.rs:1296`) | None (`str_lit_to_ctor_reducing`, `tc.rs:342-364, 463, 1121`) | **No** (`get_declar_val` exposes `Declar::Theorem` at `env.rs:324`) | None (pure replay) |
| **MM0 (`mm0-c`)** (`0d414c0b...`) | Non-recursive explicit C stacks (`g_stack`, `g_ustack`), explicit `CONV`/`UNFOLD` steps | N/A (logic-agnostic first-order checker) | N/A (explicit bytecode stream) | **Yes**: `LocalThm`/`LocalDef` private to `.mmb`; proofs never unfolded | None (near-linear bytecode verification) |

#### 1.1 Unforced Call-by-Name WHNF Spines, Stack Exhaustion, and `is_likely_unshared` Cache Bypasses

In Lean 4 (`src/kernel/type_checker.cpp:456-538`), `whnf_core` recurses directly on the C++ call stack under `scope_rec_depth` (bounded by `maxRecDepth` since commit `85e209a57b`, PR `#13956`, 2026-07-07). Under call-by-name reduction, linear state-update chains (`let s1 := step s0; let s2 := step s1; ...`) construct unforced spines whose evaluation recurses linearly in chain depth, hitting stack limits unless rewritten with strictness-forcing CPS combinators (see `lean-kernel-derivation-scale-checking-and-reflection-throughput` for empirical step thresholds up to $10^6$).

A second quadratic cliff arises from the interaction of `infer_lambda` (`src/kernel/type_checker.cpp:125-142`) with `replace_rec_fn` (`src/kernel/replace_fn.h:113-121`) and `is_likely_unshared` (`src/kernel/expr.h:373-375`):

```cpp
// leanprover/lean4 @ 8009d0a6..., src/kernel/expr.h:373-375
inline bool is_likely_unshared(expr const & e) {
    return lean_internal_get_rc(e.raw()) == 1 || lean_internal_get_rc(e.raw()) == -1;
}

// src/kernel/replace_fn.h:117-121
if (m_use_cache && !is_likely_unshared(e)) {
    if (lean_object * r = m_cache.find(e.raw(), offset))
        return expr(r, true);
    shared = true;
}
```

Contiguous lambda chains (`fun x1 ... xn => body`) are batched by `infer_lambda`'s `while (is_lambda(e))` loop into one `instantiate_rev` pass. Alternating `App` and `Lambda` layers break batching on every step; freshly allocated suffix nodes have reference count `1`, causing `is_likely_unshared(e)` to bypass `m_cache` and turning linear DAG instantiations into $\Theta(N^2)$ suffix cloning.

Rocq avoids native stack overflow by representing reduction contexts on an explicit heap-allocated zipper stack (`kernel/cClosure.ml:199-230`: `Zapp`, `ZcaseT`, `Zproj`, `Zfix`, `Zupdate`, `Zshift`, `Zprimitive`) and accelerates closed reflection via bytecode (`kernel/vconv.ml`, Grégoire & Leroy, ICFP 2002, DOI `10.1145/581478.581501`) and native OCaml compilation (`kernel/nativeconv.ml`, Boespflug, Dénès, & Grégoire, CPP 2011, DOI `10.1007/978-3-642-25379-9_26`), accepting a larger evaluator TCB. Lean 4 took the inverse TCB path: commit `2a7175c74b` (PR `#14953`, 2026-08-28) removed deprecated in-kernel `reduce_native` (`Lean.reduceBool`/`Lean.reduceNat`/`Lean.ofReduceBool`/`Lean.ofReduceNat`), isolating native evaluation outside kernel reduction.

#### 1.2 The `has_fvar` GMP Bypass Cliff Across Lean 4 Revisions

Lean 4's `type_checker::reduce_nat` (`src/kernel/type_checker.cpp:660-691`) accelerates 15 `Nat` operations (`succ`, `add`, `sub`, `mul`, `pow`, `gcd`, `mod`, `div`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`) via GMP bignum routines. Cross-version inspection distinguishes two distinct regimes:

- **`v4.14.0` (`410fab72...`)**: `reduce_nat` opened with `if (has_fvar(e)) return none_expr();` (`type_checker.cpp:621`). Any free variable anywhere inside `e`—even a `let`-bound local holding a ground numeral—disabled GMP inside `whnf` itself, falling through to `unfold_definition` and unary Peano `Nat.rec`.
- **`v4.20.0` through HEAD (`8009d0a6...`)**: The guard inside `reduce_nat` was removed, allowing direct `whnf` calls to zeta-reduce closed `let`-bound arguments into numerals. **However, `lazy_delta_reduction` and `is_def_eq_core` retain the guard at HEAD**:
  ```cpp
  // leanprover/lean4 @ 8009d0a6..., src/kernel/type_checker.cpp:1062-1075
  lbool type_checker::lazy_delta_reduction(expr & t_n, expr & s_n) {
      while (true) {
          lbool r = is_def_eq_offset(t_n, s_n);
          if (r != l_undef) return r;

          if ((!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce) {
              if (auto t_v = reduce_nat(t_n)) {
                  return to_lbool(is_def_eq_core(*t_v, s_n));
              } else if (auto s_v = reduce_nat(s_n)) {
                  return to_lbool(is_def_eq_core(t_n, *s_v));
              }
          }
          switch (lazy_delta_reduction_step(t_n, s_n)) { ... }
      }
  }
  ```
  Similarly, `is_def_eq_core` (`lines 1149-1153`) gates the `Bool.true` reflection fast path on `(!has_fvar(t) || m_eager_reduce)`. During conversion checking without `eagerReduce` (PR `#9865`, commit `6e18afac8c`, 2025-08-12, setting `m_eager_reduce = true` in `infer_app:178-183`), *any* free variable on *either* side of `t_n =?= s_n` bypasses `reduce_nat` and drops into `lazy_delta_reduction_step`, unfolding `Nat.add`/`Nat.mul`/`Nat.pow` into Peano `Nat.rec`. `nanoda_lib` (`0da9f98f...`, `src/tc.rs:1001, 1296`) mirrors both `has_fvars` guards verbatim for compatibility.

HEAD Lean 4 also bounds bignum resource exhaustion via `LEAN_NAT_MAX_SIZE` (default 128 MB, commit `44a3664c18`, PR `#14849`, 2026-08-20) enforced by `check_nat_size` and `get_count_arg` (`type_checker.cpp:35-36, 291-314, 613-648`).

#### 1.3 Missing Native Kernel Reducers for `String` and `ByteArray`

Lean 4 has no native kernel reducers for `String` or `ByteArray`. Whenever a string literal meets a structure projection (`reduce_proj_core`, `type_checker.cpp:408-410`) or definitional check against `String.ofList` (`try_string_lit_expansion_core`, `lines 1113-1124`, updated from `String.mk` in PR `#11048`, `cf871a892c`), the kernel expands it via `string_lit_to_constructor` (`src/kernel/inductive.cpp:1358-1370`):

```cpp
// leanprover/lean4 @ 8009d0a6..., src/kernel/inductive.cpp:1358-1370
expr string_lit_to_constructor(expr const & e) {
    lean_assert(is_string_lit(e));
    string_ref const & s = lit_value(e).get_string();
    std::vector<unsigned> cs;
    utf8_decode(s.to_std_string(), cs);
    expr r = *g_list_nil_char;
    size_t i = cs.size();
    while (i > 0) {
        i--;
        r = mk_app(*g_list_cons_char, mk_app(*g_char_of_nat, mk_lit(literal(cs[i]))), r);
    }
    return mk_app(*g_string_mk, r); // String.ofList
}
```

String equality and name-keyed IR lookups thus construct $O(|s|)$ right-nested `List.cons (Char.ofNat <lit>)` ASTs inside the kernel (mirrored by `nanoda_lib` `str_lit_to_ctor_reducing`, `src/tc.rs:342-364, 463, 1121`), exhausting `maxRecDepth` and dominating checking time. By contrast, Agda dispatches closed `Primitive` string ops directly to Haskell `primFunImplementation` (`Reduce.hs:771-814`), and Rocq provides native `PArray` and `Uint63` via `Zprimitive`. For compiler IRs verified in Lean-like kernels, all symbol names and block labels must be interned to dense `Nat` or fixed-width integer IDs before crossing the kernel boundary.

#### 1.4 Theorem-Body Unfolding and Opacity Mismatch: Lean 4 vs. Rocq vs. Agda

Kernel-enforced opacity cleanly separates Lean 4 from Rocq and Agda:

- **Lean 4 (`declaration.h:447-449`, `type_checker.cpp:543-551, 718-730, 1087-1088`)**:
  ```cpp
  // src/kernel/declaration.h:447-449
  bool has_value(bool allow_opaque = false) const {
      return is_theorem() || is_definition() || (allow_opaque && is_opaque());
  }
  ```
  Because `is_delta` (`type_checker.cpp:543-551`) checks `info->has_value()`, `whnf` (`lines 719-729`) unconditionally unfolds `.thmInfo` proof terms whenever a theorem appears in reduction head position (e.g., accessibility proofs in `Acc.rec`), even after commit `ff3982f0c8` (PR `#15103`, 2026-10-20) moved `is_def_eq_proof_irrel` ahead of `whnf_core` in `is_def_eq_core` (`line 1155`). Meanwhile, `@[irreducible]` lives solely in the Meta extension `reducibilityCoreExt` (`src/Lean/ReducibilityAttrs.lean:52`)—invisible to the C++ kernel (`type_checker.cpp:1087-1088`)—while kernel `reducibility_hints` (`declaration.h:34-46`, `declaration.cpp:19-44`) only orders unfolding priority (*"Remark: the hint only affects performance"*). `nanoda_lib` (`src/env.rs:322-324`, `src/tc.rs:1175-1176`) reproduces `.thmInfo` unfoldability with `ReducibilityHint::Opaque`. (For Lean 4 RSS ceilings and `.thmInfo -> .axiomInfo` stripping gains, see `lean-kernel-memory-ceilings-whnf-scaling-and-validator-architectures`.)
- **Rocq (`kernel/declarations.mli:53-56, 121-137`, `kernel/opaqueproof.mli`, `kernel/cClosure.ml:466-468, 2088`)**: `constant_def` statically splits `Def of Constr.t` (`Defined`) from `OpaqueDef of Opaqueproof.opaque` (`Qed`). Inside `cClosure.ml`, `constant_value_in` raises `NotEvaluableConst Opaque` (`line 468`) and WHNF marks `OpaqueDef _` neutral identically to `Undef _` (`line 2088`). Opaque bodies sit out-of-band behind integer handles (`type opaque_handle = int`, `opaqueproof.ml:56`) in a lazy per-module `opaquetab` segment.
- **Agda (`Monad/Base.hs:5061-5073`, `Reduce.hs:749-763`)**: `unfoldDefinitionStep` computes `dontUnfold = ... || (prp == Right True) || (isIrrelevant info) || (not defOk)`, directly enforcing both `Prop`/irrelevance non-unfolding and transitively closed `OpaqueBlock` (`opaqueUnfolding :: HashSet QName`) scoping inside the reducer.

---

### 2. Safe Wire Formats vs. Memory-Unsafe Object Loaders and Conflated Proof Archives

Basis: normative + source + documentation + derived

Distributing pre-checked proof modules across CI caches or trust boundaries turns module deserializers into an adversarial attack surface.

| Format & System | Serialization Mechanism | Memory-Safe on Untrusted Input? | Integrity Check | Interface vs. Proof Split |
| :--- | :--- | :--- | :--- | :--- |
| **Lean 4 `.olean`** (`lean4@8009d0a6...`) | `mmap` COW compacted region + raw pointer/closure fixups (`module.cpp:429-613`, `compact.cpp:520-688`) | **No** (unchecked `data_size` OOB read, unchecked `closure_offsets` write, zero-validation fast path, unchecked `ctor`/`array`/`mpz` bounds, untyped root cast `α`) | None in loader (magic, version, flags, optional `githash` only) | **No** (definitions, `.thmInfo` proof terms, and optional extensions share one region) |
| **Rocq `.vo`** (`rocq@25f5b18a...`) | Indexed segment container (`"Coq!"`) decoded via OCaml `Marshal.from_channel` (`lib/objFile.ml:105-114`) | **No** (`Marshal.from_channel` builds untyped OCaml heap blocks *before* digest check) | 16-byte **MD5** per segment (non-collision-resistant; verified *after* `marshal_in` at `objFile.ml:111-112`) | **Partial** (`opaquetab` isolates `Qed` bodies in a lazy segment inside `.vo`; `.vos`/`.vok` splits compilation) |
| **Lambdapi `.lpo`** (`lambdapi@b7e9e0a0...`) | `Marshal.to_channel oc sign [Marshal.Closures]` / `Marshal.from_channel` (`src/core/sign.ml:268-294`) | **No** (untyped OCaml `Marshal` with serialized closures; requires identical executable binary) | Binary closure digest only | **Partial** (compiled signature + rewrite rules; proof scripts stay in `.lp`, but `.lpo` is an unsafe heap dump) |
| **Agda `.agdai`** (`agda@9691cf23...`) | Zstd-compressed hash-consed binary stream into Haskell ADTs (`Serialise.hs`) | **Higher** (no raw C pointer fixups or `Obj.magic` grafting; DoS/bomb resilience unexamined) | Internal source/interface hashes (`deserializeHashes`) | **No** (monolithic compiler interface per module) |
| **MM0 `.mm0` + `.mmb`** (`mm0@0d414c0b...`) | Human-readable `.mm0` spec + 40-byte-header `.mmb` table & bytecode stream (`mm0-c/mmb.md`, `verifier.c`) | **Designed for hostile `.mmb`** (819 LOC C, **85 `ENSURE`** bounds/tag/sort/stack/heap checks; zero pointer fixups) | Lockstep spec verification (`parse_until`) against `.mm0`; externally hashable | **Yes** (`.mm0` holds only public sorts/terms/defs/axioms/theorems; `LocalDef`/`LocalThm` & proofs live only in `.mmb`) |
| **`lean4export` NDJSON + `nanoda_lib`** (`0da9f98f...`) | Line-delimited JSON parsed by `serde_json` into safe Rust arenas (`src/parser.rs`) | **Yes** (0 `unsafe` blocks crate-wide, `overflow-checks = true` in release, `#![deny(clippy::cast_possible_truncation)]`) | External (stream must be hash-pinned or sandbox-generated) | **No** (full declaration stream including `.thmInfo` proof terms for replay) |

#### 2.1 Hostile-Input Failures in `.olean`, `.vo`, and `.lpo`

Lean 4's `lean_compacted_region_read` (`src/library/module.cpp:424-613`, invoking `region_reader::read()` in `src/runtime/compact.cpp:617-688`) explicitly disclaims type safety (*"the C side does no type checking and the caller is responsible for using a type compatible with what was saved"*, `module.cpp:427-428`). Direct inspection at HEAD (`8009d0a6...`) confirms five concrete memory-corruption primitives on untrusted `.olean` inputs:

1. **Unchecked `data_size` OOB dereference (`module.cpp:578-585`)**: Reads `size_t data_size` from the mapped buffer and immediately dereferences `buffer + data_section_off + data_size` without checking bounds against file size `size`.
2. **Arbitrary pointer write via `closure_offsets` (`compact.cpp:629-643`)**: Adds relocation deltas to `*(void **)(begin + off)` for every untrusted `off` without verifying `off < m_size` or closure-header validity.
3. **Zero-validation fast path (`compact.cpp:645-659`)**: When `m_begin == m_base_addr` and `!needs_dep_reloc`, skips both dependency overlap checks and the object walk, returning raw `object * root` directly.
4. **Unchecked slow-path walk (`compact.cpp:520-686`)**: `fix_constructor`, `fix_array`, and `fix_mpz` trust untrusted object counts and limb sizes without verifying `end <= m_end`, pointer alignment, or valid object tags (calling `lean_unreachable()` on out-of-range pointers).
5. **Extension/initializer conflation**: Loading without `loadExts := false`, `plugins := #[]`, and `trustLevel := 0` deserializes arbitrary `PersistentEnvExtension` state and can trigger `[init]` hooks.

Rocq's `.vo` loader (`lib/objFile.ml:105-114`) similarly executes untyped `Marshal.from_channel` (`marshal_in`) *before* checking its non-cryptographic 16-byte MD5 digest, and Lambdapi (`src/core/sign.ml:276, 294`) marshals raw OCaml closures (`[Marshal.Closures]`). Auditors must therefore never load untrusted `.olean`, `.vo`, or `.lpo` files in-process; untrusted code requires sandboxed source re-elaboration (`untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`) or safe interchange formats.

#### 2.2 Separating Small Checked Interfaces (`.sig`) from Offline-Auditable Proof Archives (`.prf`)

Pollack (*How to Believe a Machine-Checked Proof*, OUP 1998, DOI `10.1093/oso/9780198501275.003.0013` / BRICS RS-97-18) separates proof trust into **independent derivability checking** (a small, surveyable checker) and **semantic fidelity** (human inspection of definitions and theorem statements). Bundling proof terms into binary interfaces defeats both goals by inflating consumer RSS, inviting accidental WHNF unfolding, and burying statements inside unsafe heap dumps.

Two inspected architectures provide the required building blocks:

- **MM0 `.mm0` + `.mmb`** (Carneiro, CICM 2020, DOI `10.1007/978-3-030-53518-6_5`, `arXiv:1910.10703`; `digama0/mm0@0d414c0b...`): Keeps the human-surveyable public interface (`.mm0`) strictly separate from the binary proof stream (`.mmb`). In `mm0-c/verifier.c` (819 LOC C), `verify()` bounds-checks the 40-byte `"MM0B"` header and sort/term/theorem/proof offsets against `len` (`lines 674-684`), `cmd_unpack` enforces 5-byte EOF read-ahead (`line 152`), `load_args` checks `args[num_args] <= g_end` and binder dependency bitmasks (`lines 178-197`), forward references are banned by monotonic counters (`g_num_terms`, `g_num_thms`), and 85 `ENSURE(...)` checks guard every stack, heap, and unification step. Private helpers (`CMD_STMT_LOCAL_DEF`, `CMD_STMT_LOCAL_THM`) never pollute `.mm0`, while public items lockstep-match `.mm0` via `parse_until`.
- **Safe-Rust replay (`nanoda_lib`) + Statement-Origin Separation (`joshlf/anneal`)**: `nanoda_lib` (`0da9f98f...`, v0.4.32) checks full Lean 4 environments in 100% safe Rust (0 `unsafe` blocks, `overflow-checks = true`) over `serde_json` NDJSON exports. Complementarily, `joshlf/anneal` (`08f1184d...`, `docs/trust-model.md:106-251`, `trusted/audit/TrustedBoundary.lean`) enforces **Statement-Origin Separation**: every constant in `ConstantInfo.type` must originate in `Trusted.*` (split into `vetted` and `candidate:<feature>` tiers with strict one-way dependencies) or hash-pinned `Init.*`, while untrusted `theory/` appears only inside `ConstantInfo.value?` and is replayed from scratch via `base.toKernelEnv.replay locals` with `loadExts := false` and `trustLevel := 0`.

Combining these designs defines a clean-slate **two-artifact module boundary**:
1. **Checked Interface (`.sig`)**: A compact, canonical, memory-safe, bounds-checked, content-addressed format carrying exported types, *transparent* computational definitions (`Defined`), proof-stripped **kernel-opaque** theorem signatures (`ConstantInfo.type` + universe params + transitive axiom manifest), and SHA-256 hashes of upstream `.sig` inputs and its companion `.prf` archive.
2. **Offline-Auditable Proof Archive (`.prf`)**: A replayable proof stream (MM0 bytecode or NDJSON derivation log) checked independently by a memory-safe verifier and never mapped into downstream consumer memory or WHNF tables.

---

### 3. Adversarial Goodhart Resistance in Formal Specifications

Basis: normative + source + documentation + execution + derived

Traditional interactive theorem proving assumes benevolent human authors. Under automated, RL, or LLM-driven proof and compiler synthesis, **Goodhart's Law** dominates: *the formal checker—not informal human intent—defines the optimization reward*. Empirical audits confirm that even human-verified systems fail primarily at specification and TCB boundaries:

- **Fonseca, Zhang, Wang, and Krishnamurthy (EuroSys 2017, DOI `10.1145/3064176.3064183`)** audited IronFleet (Dafny), Verdi (Coq), and Chapar (Coq) and found **16 bugs** causing crashes, wrong outputs, or violated verification guarantees—all residing in specs, unverified shims, or environment assumptions (their `PK` boundary toolkit caught 13/16).
- **Amaral, Mendes, and Campos (ICSE 2026, `arXiv:2511.15403`, MutDafny)** applied 40 mutation operators to 794 real-world Dafny programs, showing mutated buggy implementations frequently verify against weak specifications and uncovering five weak production specifications (1 per 241 LOC in the manually audited subset).
- **Meta-theoretic limit (`anneal-universal-algebra-institutions-and-incompleteness-bounds`)**: Gödel II, Tarski undefinability, and Löb's theorem prove that axiom hygiene (`NoSorry`) cannot be enforced purely inside the object logic; defenses must span object-level algebraic constraints, meta-level external auditors, and minimal human-audited TCB surfaces.

#### 3.1 Unified Refinement Preorder `(Behavior, ≤)`

Model source, target, and abstract semantics uniformly over partial behavior sets:
$$\text{Behavior} \;:=\; \text{Query} \to \text{Partial}(\mathcal{P}(\text{Obs})), \qquad \text{Partial}(X) \;:=\; \{ \top_{\text{UB}} \} \cup X$$
ordered pointwise by $b_1 \le b_2$:
$$b_1 \le b_2 \iff \forall q \in \text{dom},\quad b_2(q) = \top_{\text{UB}} \;\lor\; \big(b_1(q) \neq \top_{\text{UB}} \;\land\; b_1(q) \subseteq b_2(q)\big)$$
Here $\top_{\text{UB}}$ denotes undefined behavior (arbitrary target refinement permitted) and $\emptyset = \bot$ denotes uninhabited/stuck behavior. Compilers refine downward ($L_{\text{tgt}}.\text{sem}(t) \le \pi_c(L_{\text{src}}.\text{sem}(s))$) while static analyzers/verifiers over-approximate upward ($L_{\text{src}}.\text{sem}(s) \le \pi_v(L_{\text{abs}}.\text{sem}(a))$).

#### 3.2 Six Canonical Specification-Exploit Classes and Algebraic Defenses

| # | Exploit Class | Rogue Synthesizer Construction | Why Naive Refinement Passes | Required Algebraic & Meta-Level Defense |
| :--- | :--- | :--- | :--- | :--- |
| **1** | **Miracle target compiler** | Map programs to uninhabited target behavior (`Beh_tgt(q) := ∅ = ⊥`). | `∅ ⊆ S` holds vacuously for every `S`, so `⊥ ≤ Beh_src`. | **Productivity preservation**: `∀ q ∈ dom, Defined(src(q)) ∧ NonEmpty(src(q)) → Defined(tgt(q)) ∧ NonEmpty(tgt(q))` (cf. Leroy 2009 backward simulation + target progress). |
| **2** | **Contradictory precondition / domain collapse** | Shrink safe domain to `dom := ∅` (contradictory `requires P ∧ ¬P`, or degenerate `requires x == 0`). | Universal quantifier `∀ q ∈ ∅, ...` holds trivially for arbitrary broken outputs. | **Pinned signature / witness domain**: Caller pins required domain `Q_spec` or mandatory witness set `W_req ⊆ dom`; pair with vacuity/proof-dependency checks (e.g., Dafny `--warn-contradictory-assumptions`). |
| **3** | **Observation codec erasure** | Choose `Obs := Unit` or constant/1-bit projection `π(v) := 0`, collapsing `42` and miscompiled `99`. | `π({99}) = {0} ⊆ {0} = π({42})`. | **Observation codec injectivity**: `∀ x y ∈ Obs_src, π(x) = π(y) → x = y`. Export both source contracts and target proofs whenever cross-crate lowering codecs are non-invertible. |
| **4** | **Lying byte emitters & circular parser oracles** | **(4a)** Prove refinement on an AST while writing unrelated bytes (`xor eax, eax; ret`); **(4b)** supply a spoofed byte parser claiming wrong bytes compute `q + 3`. | Theorem binds only internal AST or untrusted decoder, never real emitted bytes under a fixed ISA. | **End-to-end byte-array emission + hash-pinned immutable ISA decoder**: Quantify over `raw_bytes` executed by pinned ISA semantics (cf. CompCertELF, Wang et al. OOPSLA 2020, DOI `10.1145/3428265`; CakeML, Kumar et al. POPL 2014 / Tan et al. JFP 2019). |
| **5** | **Circular reference-correspondence adapter hooks** | Override hooks in an external reference oracle (`S_ref`) so it imitates the candidate (`S_cand`). | Lockstep proof silently reduces to `S_cand ≈ S_cand`. | **Hash-locked unmodified reference oracle + non-interference witnesses**: Pin upstream blob/tree cryptographic hashes and prove hooks preserve upstream behavior on diverging features (`joshlf/anneal@6b09691a...`). |
| **6** | **Positive-only TCB rot (guard-weakened semantics)** | Drop or weaken UB guards (`x / 0 = 0`, Lean `Nat.sub` saturating `0 - 1 = 0`, missing PC/opcode checks). | Positive safety proofs quantify over UB-free paths where guards never fire, catching **0%** of guard removals. | **Automated semantic mutation testing + negative refutation canaries + differential conformance**: Mutate every UB guard systematically, require mechanized `Refuted` canaries to kill 100% of mutants, and differentially test against hardware/emulators/ISA specs. |

#### 3.3 Key Design Nuances and Real-World Postmortem

- **Productivity without blocking optimization (Leroy 2009)**: In CompCert (*A Formally Verified Compiler Back-End*, JAR 2009, DOI `10.1007/s10817-009-9155-4`, `arXiv:0902.2137`), backward simulation on safe source programs (`Safe(S)`) requires target receptiveness/determinism or explicit productivity preservation so empty target relations cannot cheat. Resolving benign source nondeterminism `{q+3, q+4}` downward to deterministic `{q+3}` still preserves non-emptiness.
- **Separating tool refusal from domain collapse**: Demanding `dom = AllPrograms` would wrongly reject sound, incomplete static analyzers. Hardened contracts permit a verifier to refuse out-of-fragment programs (`UNKNOWN`, emitting no false certificate) while requiring every *emitted certificate* to cover the caller-pinned witness domain `W_req`.
- **Real-world circular adapter postmortem (`joshlf/anneal@6b09691a2820d0608034e1468b8685a0dccddb77`, 2026-11-06)**: While proving lockstep correspondence between Anneal's MIR semantics and vendored `proofs-rs/lean-miri`, adapter hooks (`annealEvalOperand` and custom `StorageLive`/`StorageDead`) injected Anneal's move-invalidation and storage rules into `lean-miri`:
  > *"The A0 hooks made lean-miri imitate Anneal instead of running lean-miri's own semantics, so parts of the lockstep proofs related Anneal to itself."*
  Upstream `lean-miri` evaluates `Move` identically to `Copy` and rejects `StorageDead(_0)` with `cannotMakeReturnPlaceDead`. Commit `6b09691a28...` closed the loophole by (a) verifying upstream Git blob/tree SHA-1 digests across all 608 vendored files (`scripts/audit_lean_miri_cleanroom.sh`, `miri_tree_sha1 = ef473f04...`, `manifest_sha256 = 081747a3...`) and (b) pinning headline theorem statements, standard axioms, non-vacuity execution witnesses (`Witness.bisim_applies`, `Witness.divByZero_ub_agrees`, `Witness.div_returns_agree`), and hook non-interference proofs (`annealEvalOperand_move_eq_copy`, `annealStepHooks_storageDead_returnPlace`) in `lean-miri/lean/LeanMiriSpec/Audit.lean`.
- **Mutation canaries and 2-safety boundary**: Weakening operational-semantics guards never breaks positive proofs over UB-free inputs; systematic mutation testing paired with negative refutation canaries closes this silent TCB rot (see also `anneal-vacuity-mutation-oracles-and-verification-scaling`). Orthogonally, single-trace refinement remains blind to **2-safety hyperproperties** (constant-time secret-independent execution, preventing dead-store elimination of `zeroize()`), which require relational leakage traces.

---

### 4. Mechanized Finite-State Verification Results (`support/verify_goodhart_spec_defenses.py`)

Basis: execution + derived

`support/verify_goodhart_spec_defenses.py` models a finite-state source IR (`LOAD_ARG`, `LOAD_IMM`, `ADD_IMM`, `SUB_IMM`, `DIV_ARG`, `CHOICE_01`, `RET` over `Query = 0..7`), a 2-byte target mini-ISA with an immutable byte decoder (`pinned_isa_exec`), five toggleable UB guards (`SrcGuardConfig`), an interval abstract interpreter (`conservative_verifier_checks_safe`), and a reference-correspondence checker.

Running `python3 -B support/verify_goodhart_spec_defenses.py` (Python 3.10+, exit code `0`, `all_assertions_passed: true`) yields:

| Artifact / Exploit Case | Naive Contract | Hardened + Canaries | Hardened Diagnostic |
| :--- | :---: | :---: | :--- |
| `exploit_1_miracle_target` (`Beh_tgt = ∅`) | **Accepted** | **Rejected** | `REJECTED[miracle-target]: claimed target uninhabited/UB on productive source input q=0` |
| `exploit_2_domain_collapse` (`dom = ∅`) | **Accepted** | **Rejected** | `REJECTED[domain-collapse]: missing required witness inputs [0, 1, 2, 3, 4, 5, 6, 7]` |
| `exploit_3_observation_erasure` (`Obs := Unit`, returns `99`) | **Accepted** | **Rejected** | `REJECTED[obs-erasure]: non-injective codec maps 0 and 1 both to 0` |
| `exploit_4a_lying_byte_emitter` (honest AST, writes `ret 0`) | **Accepted** | **Rejected** | `REJECTED[lying-emitter]: pinned ISA bytes at q=0 produce {0}, violating {3, 4}` |
| `exploit_4b_circular_parser_oracle` (`ret 7`, spoofed decoder) | **Accepted** | **Rejected** | `REJECTED[lying-emitter]: pinned ISA bytes at q=0 produce {7}, violating {3, 4}` |
| `exploit_5_circular_adapter_hook` (hook imitates candidate) | **Accepted** | **Rejected** | `REJECTED[circular-adapter]: reference oracle digest 2b27813ba92b != pinned 21764a9d64d5` |
| `exploit_6_guard_weakened_mutants` (5 single-guard mutants) | **Accepted** (`5/5`) | **Rejected** (`5/5` killed) | `REJECTED[mutation-canaries]: 5/5 mutants killed (vs 0/5 by positive proofs)` |
| `honest_optimizing_compiler` (resolves `CHOICE_01` to bytes) | Accepted | **Accepted** | `ACCEPTED (hardened compiler contract)` |
| `honest_conservative_analyzer_in_fragment` (interval abstract) | N/A | **Accepted** | `ACCEPTED (sound conservative verifier proved non-UB upward refinement)` |
| `honest_conservative_analyzer_out_of_fragment_refusal` | N/A | **Accepted** | `ADMITTED (honest conservative refusal on out-of-fragment program)` |
| `honest_unmodified_oracle_correspondence` (pinned hash) | Accepted | **Accepted** | `ACCEPTED (hardened unmodified-oracle correspondence)` |

| Guard-Weakened Semantics Mutant | Passes Positive Proof Suite (`3` progs)? | Killed by Negative Canary? |
| :--- | :---: | :--- |
| `mutant_drop_div_zero_guard` (`acc / 0 -> 0`) | **Yes** | **Killed** (`canary_div_by_zero`) |
| `mutant_drop_underflow_guard` (`0 - 1 -> 0` saturating) | **Yes** | **Killed** (`canary_unsigned_underflow`) |
| `mutant_drop_overflow_guard` (`250 + 10 -> 4` wrapping) | **Yes** | **Killed** (`canary_u8_overflow`) |
| `mutant_drop_pc_oob_guard` (fall off end -> `acc`) | **Yes** | **Killed** (`canary_pc_oob`) |
| `mutant_drop_invalid_op_guard` (`BOGUS_OP` -> `acc`) | **Yes** | **Killed** (`canary_invalid_opcode`) |

All 7 exploits (spanning all 6 classes) pass naive refinement yet are 100% rejected by the hardened contract; 5/5 guard mutants survive positive proofs (`0%` caught) yet are 100% killed by negative canaries; and 4/4 honest tools (including a genuinely incomplete interval abstract interpreter) are admitted.

---

### 5. Clean-Slate Architectural Synthesis for Next-Generation Proof Kernels

Basis: derived

1. **Heap-allocated abstract machine + explicit strictness**: Replace C++ recursion in WHNF with an explicit zipper stack (Rocq `cClosure`) plus strict evaluation combinators, and avoid `rc == 1` cache-bypass cliffs across alternating `App`/`Lambda` spines.
2. **Free-variable-aware primitive reducers**: Never gate GMP/bitvector/byte-slice reduction on whole-term `!has_fvar(e)` during conversion (`lazy_delta_reduction`); zeta-reduce closed locals, bound bignum growth (`LEAN_NAT_MAX_SIZE`), and provide native reducers for packed byte slices/bitvectors (or mandate interned integer IR IDs).
3. **Kernel-enforced opacity**: Make theorem opacity a first-class kernel AST invariant (`OpaqueDef` / `OpaqueBlock`), decoupled from elaborator heuristics (`@[irreducible]`), so proof bodies never enter WHNF or consumer RSS.
4. **Memory-safe, content-addressed `.sig` / `.prf` split**: Replace raw `mmap` pointer fixups (`.olean`) and untyped `Marshal` (`.vo`, `.lpo`) with bounds-checked `.sig` interfaces (carrying stripped opaque theorem signatures and SHA-256 content hashes) separated from offline-auditable `.prf` proof archives (`mm0-c` / `nanoda_lib` model).
5. **Statement-origin separation + independent safe-language replay**: Constrain `ConstantInfo.type` to human-audited `Trusted.*` modules and replay `.prf` archives in an independent memory-safe external checker decoupled from interactive elaboration.
6. **Goodhart-hardened specifications + continuous semantic mutation CI**: Embed productivity preservation, caller-pinned domains, injective codecs, byte-level pinned ISA decoding, hash-locked reference oracles, and 100%-killed UB-guard mutation suites directly into CI contracts.

## Boundaries

- **not examined**: Isabelle/HOL, HOL4, CakeML's Candle kernel, F*, Rocq's `rocqchk` internals, `Lean4Lean` throughput benchmarks (covered in `lean-kernel-derivation-scale-checking-and-reflection-throughput` and `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification`), live hardware/QEMU/Sail differential fuzzing harnesses, and decompression-bomb fuzzing of Agda's Zstd `.agdai` decoder.
- **unknown**: Whether future `leanprover/lean4` releases will remove `lazy_delta_reduction`'s `has_fvar` guard (`type_checker.cpp:1067`), make `.thmInfo` opaque in `whnf`, or replace `.olean` compaction with a bounds-checked format; and the practical CI cost curve for 100%-kill semantic mutation suites on full x86-64/AArch64 Sail ISA models.
- **known not to apply**:
  - The top-level `if (has_fvar(e)) return none_expr();` inside `reduce_nat` (`lean4` `v4.14.0`, `type_checker.cpp:621`) is **known not to apply** to `v4.20.0` through HEAD (`8009d0a6...`); however, the residual `lazy_delta_reduction` (`:1067`) and `is_def_eq_core` (`:1149`) `has_fvar` guards *do* apply at HEAD without `eagerReduce`.
  - In-kernel `reduce_native` (`Lean.reduceBool`/`reduceNat`) is **known not to apply** to `leanprover/lean4` HEAD (`8009d0a6...`), removed in PR `#14953` (`2a7175c74b`).
  - The single-trace defenses in `support/verify_goodhart_spec_defenses.py` are **known not to apply** to relational 2-safety / side-channel hyperproperties (timing leaks, dead-store elimination of `zeroize()`).
- **unsupported**: Enforcing axiom hygiene (`NoSorry`) or full informal intent purely inside the object logic is **unsupported** in principle (Gödel II, Tarski, Löb; see `anneal-universal-algebra-institutions-and-incompleteness-bounds`). Kernel enforcement of `@[irreducible]` is explicitly **unsupported** in Lean 4 (`type_checker.cpp:1087-1088`).
- **Limits on stronger conclusions**: Hardened algebraic defenses and 100%-killed mutation suites narrow, but cannot eliminate, Pollack's informal-to-formal semantic-fidelity gap; finite-state probe validation does not establish mutation completeness for unbounded languages.

## Evidence

All primary-source inspections and probe executions were performed on `2026-11-19`.

### Primary Source Coordinates

1. **`leanprover/lean4` @ `8009d0a64d2860606c6a5ac5ff6702622b24921e` (HEAD)**:
   - `src/kernel/type_checker.cpp`: `:35-36, 291-314, 613-648` (`LEAN_NAT_MAX_SIZE`, `check_nat_size`, `get_count_arg`, PR `#14849` `44a3664c18`); `:125-142` (`infer_lambda`); `:169-186` (`m_eager_reduce`, PR `#9865` `6e18afac8c`); `:408-410, 1113-1124, 1276` (`string_lit_to_constructor`, `String.ofList`, PR `#11048` `cf871a892c`); `:456-538` (`whnf_core`, `scope_rec_depth`, PR `#13956` `85e209a57b`); `:543-551, 718-730` (`is_delta`, `whnf`); `:660-691` (`reduce_nat`); `:1062-1082` (`lazy_delta_reduction` `has_fvar`); `:1087-1088` (Meta reducibility comment); `:1149-1156` (`is_def_eq_core` `has_fvar` & `is_def_eq_proof_irrel`, PR `#15103` `ff3982f0c8`); `reduce_native` removal verified in `2a7175c74b` (PR `#14953`).
   - `src/kernel/declaration.h`: `:34-46` (`reducibility_hints`), `:398-408` (`ConstantInfo`), `:447-449` (`has_value`). `src/kernel/declaration.cpp`: `:19-44` (`compare`).
   - `src/kernel/inductive.cpp`: `:1349-1370` (`nat_lit_to_constructor`, `string_lit_to_constructor`).
   - `src/kernel/expr.h`: `:373-375` (`is_likely_unshared`). `src/kernel/replace_fn.h`: `:113-121` (`replace_rec_fn::apply`).
   - `src/Lean/ReducibilityAttrs.lean`: `:1-60` (`reducibilityCoreExt`).
   - `src/library/module.cpp`: `:424-613` (`lean_compacted_region_read`, unchecked `data_size` at `:578-585`).
   - `src/runtime/compact.cpp`: `:474-688` (`region_reader`, unchecked `closure_offsets` at `:629-643`, zero-validation fast path at `:645-659`, unchecked `fix_*` walks).
2. **`leanprover/lean4` @ `410fab7284703f41660ca2454218dcca9b2ec896` (`v4.14.0`)**: `src/kernel/type_checker.cpp:621` (`if (has_fvar(e))` in `reduce_nat`), `:558` (`reduce_native`), `:989`, `:1077`. Tags `v4.20.0`, `v4.25.0`, `v4.27.0`, `v4.28.0`, `v4.30.0`, `v4.34.1`, `v4.35.0` confirmed guard removal inside `reduce_nat` by `v4.20.0` and persistence in `lazy_delta_reduction`/`is_def_eq_core`.
3. **`rocq-prover/rocq` @ `25f5b18a320e4796f181f938d3b74bebe7db4dc4`**: `kernel/declarations.mli:53-56, 121-137` (`Def` vs `OpaqueDef`); `kernel/opaqueproof.{mli,ml}` (`opaquetab`, `opaque_handle`); `kernel/cClosure.ml:199-230, 468, 2088`; `kernel/vconv.ml`; `kernel/nativeconv.ml`; `lib/objFile.ml:14-56, 105-114` (`marshal_in` before MD5 check).
4. **`agda/agda` @ `9691cf2331ed3d5f9aba04380cc1cc8f415d192e`**: `src/full/Agda/TypeChecking/Monad/Base.hs:5061-5073` (`OpaqueBlock`); `src/full/Agda/TypeChecking/Reduce.hs:742-845` (`unfoldDefinitionStep`, `dontUnfold`, `Primitive`); `src/full/Agda/TypeChecking/Serialise.hs:1-80` (Zstd hash-consed `.agdai`).
5. **`digama0/mm0` @ `0d414c0bfdaaeb7fea571895127abc1fa5a3d956`**: `mm0-c/mmb.md:1-180`; `mm0-c/verifier.c` (819 LOC, 85 `ENSURE` checks, `:151-197, 670-819`).
6. **`ammkrn/nanoda_lib` @ `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929` (v0.4.32)**: `Cargo.toml` (`overflow-checks = true`), `src/lib.rs`, crate-wide scan confirming 0 `unsafe` blocks, `src/parser.rs`, `src/env.rs:320-324`, `src/tc.rs:342-364, 463, 1001, 1121, 1175-1176, 1296`.
7. **`Deducteam/lambdapi` @ `b7e9e0a0ae09b16a8841bbce1c7bfceb013ff3e3`**: `src/core/sign.ml:267-294` (`Marshal.Closures`, `Marshal.from_channel`).
8. **`joshlf/anneal` @ `08f1184dce262d8d3ab610d4becedc3a0ae4486c` & `6b09691a2820d0608034e1468b8685a0dccddb77`**: `docs/trust-model.md:42-255`; commit `6b09691a28...` message, `scripts/audit_lean_miri_cleanroom.sh` (608 files, `miri_tree_sha1 = ef473f04...`, `manifest_sha256 = 081747a3...`), and `lean-miri/lean/LeanMiriSpec/Audit.lean`.

### Published Literature

- Carneiro (2020), *Metamath Zero: Designing a Theorem Prover Prover*, CICM 2020, LNCS 12236, pp. 71–88, DOI `10.1007/978-3-030-53518-6_5` (`arXiv:1910.10703`).
- Pollack (1998), *How to Believe a Machine-Checked Proof*, *Twenty-Five Years of Constructive Type Theory*, OUP, pp. 205–220, DOI `10.1093/oso/9780198501275.003.0013` (BRICS RS-97-18, DOI `10.7146/brics.v4i18.18945`).
- Fonseca, Zhang, Wang, & Krishnamurthy (2017), *An Empirical Study on the Correctness of Formally Verified Distributed Systems*, EuroSys 2017, DOI `10.1145/3064176.3064183`.
- Leroy (2009), *A Formally Verified Compiler Back-End*, JAR 43(4):363–446, DOI `10.1007/s10817-009-9155-4` (`arXiv:0902.2137`).
- Wang, Xu, Wilke, & Shao (2020), *CompCertELF: Verified Separate Compilation of C Programs into ELF Object Files*, PACMPL 4 (OOPSLA 2020), DOI `10.1145/3428265`.
- Amaral, Mendes, & Campos (2026), *MutDafny: A Mutation-Based Approach to Assess Dafny Specifications*, ICSE 2026, `arXiv:2511.15403`, DOI `10.48550/arXiv.2511.15403`.
- Contextual citations: Grégoire & Leroy (ICFP 2002, DOI `10.1145/581478.581501`); Boespflug, Dénès, & Grégoire (CPP 2011, DOI `10.1007/978-3-642-25379-9_26`); Kumar et al. (POPL 2014, DOI `10.1145/2535838.2535841`); Tan et al. (JFP 2019, DOI `10.1017/S0956796818000229`).

### Preserved Executable Support Material

- `support/verify_goodhart_spec_defenses.py`: Executed `2026-11-19` via `python3 -B support/verify_goodhart_spec_defenses.py` (Python 3.10+, exit `0`): `exploits_tested: 7`, `naive_exploits_accepted: 7`, `hardened_exploits_rejected: 7`, `semantic_mutants_total: 5`, `semantic_mutants_passing_positive_suite: 5`, `semantic_mutants_killed_by_negative_canaries: 5`, `honest_tools_admitted: 4`, `all_assertions_passed: true`.

## Revalidation

1. **Re-run the mechanized probe**:
   ```console
   python3 -B reports/proof-kernels-opaque-interfaces-and-adversarial-spec-hardening/support/verify_goodhart_spec_defenses.py
   ```
   Expect exit `0` and `"all_assertions_passed": true` (`7/7` naive accepts, `7/7` hardened rejects, `5/5` mutants killed, `4/4` honest tools admitted).
2. **Check Lean 4 kernel cliffs and `.olean` safety on newer commits**: Inspect `src/kernel/type_checker.cpp` (`lazy_delta_reduction` `has_fvar`, native `String`/`ByteArray` reducers, `is_delta`/`whnf`), `src/kernel/declaration.h` (`has_value` checking `is_theorem()`), and `src/library/module.cpp` / `src/runtime/compact.cpp` (`data_size` and `closure_offsets` bounds checks, fast-path object validation).
3. **Check Rocq, Lambdapi, MM0, and `nanoda_lib`**: Verify whether `rocq-prover/rocq` `lib/objFile.ml` or `Deducteam/lambdapi` `src/core/sign.ml` replaced OCaml `Marshal`/MD5; verify `mm0-c/verifier.c` retains `ENSURE` bounds checks and `.mm0`/`.mmb` separation; verify `ammkrn/nanoda_lib` retains zero `unsafe` blocks and check `src/tc.rs` (`has_fvars`, `str_lit_to_ctor_reducing`) and `src/env.rs` (`get_declar_val`).
4. **Check correspondence oracle locking**: In cross-semantics bridges (e.g., `joshlf/anneal` `scripts/audit_lean_miri_cleanroom.sh`), confirm upstream blob/tree SHA-1 verification remains enforced in CI alongside hook non-interference lemmas.
