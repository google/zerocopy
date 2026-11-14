# Verified Pre-Proof Reachability Pruning (`--gc-sections`) and Address-Safe Identical Code Folding (`--icf=safe`)

## Summary

Under the whole-program verification contract where every function emitted into the final binary carries a kernel-checked `HybridTrace` refinement proof, generating and checking proofs *before* dead-section elimination (`--gc-sections`) and Identical Code Folding (`--icf=safe` / `MergeFunctions`) wastes **`4.0x` to `6.2x`** of compilation and proof-checking work on dead standard-library `MonoItem`s. Moving call-and-relocation reachability pruning and address-safe ICF ahead of `HybridTrace` proof generation cuts whole-program verification volume by **`80.0%`–`83.9%`** while preserving soundness with respect to Rust and C FFI function-pointer identity:

1. **Zero-`sorry` Lean `v4.34.1` pruning and safe-ICF soundness theorems (`support/VerifiedReachabilityAndIcf.lean`, `180` lines):**
   - **Unreachable-Module Pruning Theorem (`unreachable_module_pruning_sound`):** For any whole-program `MonoItem` list `live ++ dead` where `LiveClosed live` holds (every call, vtable method, reified function pointer, drop glue, and data-provenance edge out of `live` resolves inside `live`), `runProgram fuel (live ++ dead) s v = runProgram fuel live s v` for all `fuel : Nat` and `s ∈ dom(live)`. Dead `MonoItem`s (`dead`) therefore require **zero compilation derivations**.
   - **Address-Safe ICF Theorem (`address_safe_icf_fold_sound`):** Whenever two `MonoItem`s `f₁, f₂` satisfy `SafeIcfPair f₁ f₂` (identical instruction semantics, identical outgoing relocation targets, and `f₂.addrSignificant = false`), folding `f₂` to `f₁.codeAddr` preserves all execution traces and requires checking only `f₁`'s derivation.
   - **Function-Pointer Collision Canary & Thunk Resolution (`canary_unsound_icf_all_addr_collision`, `thunk_icf_preserves_distinct_addr`):** Proves that naive `--icf=all` falsifies `f₁.codeAddr ≠ f₂.codeAddr` when `addrSignificant = true`, whereas a 5-byte `jmp rel32` / 4-byte `b imm26` tail-call thunk (`thunkToFirst`) preserves `f₁.codeAddr ≠ f₂.codeAddr` while sharing `f₁`'s verified body.
2. **Empirical proof-volume reduction across the 5 `V3` workload shapes (`support/prune_and_icf.py`, `support/reachability_icf_savings.json`):**
   - On `x86_64-unknown-linux-gnu` (`rustc 1.99.1 -C opt-level=3`), section-level reachability pruning (`--gc-sections`) alone removes **`63.46%` to `66.98%`** of `.text` bytes (`698,013 B` $\rightarrow$ `255,059 B` on `cli_tool`) and reduces unique function bodies requiring `HybridTrace` verification from **`2,288`–`2,307` down to `499`–`576`** (**`4.01x` to `4.59x` reduction**).
   - Combining whole-program `MonoItem` reachability pruning (`-C lto=fat -C codegen-units=1 --gc-sections`) with `--icf=safe` and `MergeFunctions` reduces verified function bodies to **`368`–`426`** (`8,832`–`10,224` estimated `HybridTrace` steps vs. `54,912`–`55,368` unpruned), achieving a **`5.42x` to `6.22x` reduction in proof-checking volume** (`5.72x` on `hello_world`, `5.42x` on `cli_tool`, `5.55x` on `async_server`, `6.22x` on `cdylib`).
   - Across all **8 Tier 1 targets** (`cross_target_8target_archive_pruning`), pre-proof reachability pruning eliminates **`58.83%` to `73.89%`** of archive `.text` (`754,536 B` $\rightarrow$ `284,227 B` on `x86_64-unknown-linux-gnu`; `523,024 B` $\rightarrow$ `136,548 B`, `-73.89%` on `aarch64-pc-windows-msvc`).
3. **Empirical verification of `.llvm_addrsig` (`SHT_LLVM_ADDRSIG`) and `--icf=safe` vs. `--icf=all` (`support/reachability_icf_savings.json`):**
   - Inspecting emitted ELF objects with `llvm-readobj --addrsig` confirms that `rustc 1.99.1` / LLVM `23.1.1` emits `SHT_LLVM_ADDRSIG` (`.llvm_addrsig`) listing exactly the functions whose addresses are taken (`addr_taken_a`, `addr_taken_b`) while omitting call-only functions (`call_only_c`, `call_only_d`).
   - Under `rust-lld --icf=safe`, `call_only_c` and `call_only_d` fold to the single address `0x219f0` (`call_only_folded = true`), while `addr_taken_a` (`0x219d0`) and `addr_taken_b` (`0x219e0`) remain distinct (`addr_taken_eq=false` at runtime). Under `--icf=all`, `addr_taken_a` and `addr_taken_b` collide at `0x219d0` (`addr_taken_eq=true`).

## Applicability

- **Extends:** `rustc-binary-origin-attribution-gc-sections-and-icf-soundness`, `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `compositional-correctness-linking-and-whole-program-optimization`
- **Subjects:** Evaluated on `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `MergeFunctions`, `SHT_LLVM_ADDRSIG`, `rust-lld`), and `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Created:** 2026-11-14
- **Updated:** 2026-11-14

## Findings

### 1. Pre-Proof Reachability Graph Construction Over `.anneal-mir` and `RelocSectionImage`

**Basis: source + derived (`compiler/rustc_monomorphize/src/collector.rs`, `support/VerifiedReachabilityAndIcf.lean`)**

To prune unreachable `MonoItem`s *before* running `-O3` optimization and `HybridTrace` proof generation, the pre-proof reachability analyzer constructs a directed graph $G = (V, E)$ over crate and sysroot `.anneal-mir` / `RelocSectionImage` symbols:

1. **Crate-type entry root set $R \subseteq V$:**
   - `--crate-type=bin`: `_start` $\to$ `main` $\to$ `std::rt::lang_start`, `.init_array` / `.CRT$XCU` / `__mod_init_func` static constructors, `#[used]` and `#[used(linker)]` statics, allocator shim roots (`__rust_alloc`, `__rust_dealloc`, `__rust_realloc`, `__rust_alloc_zeroed`), `#[panic_handler]` (`rust_begin_unwind`), and `rust_eh_personality`.
   - `--crate-type=cdylib` / `dylib` / `staticlib`: `exported_symbols::collect` roots (`#[no_mangle]`, `#[export_name]`, `pub extern` items, and reachable vtables of exported trait objects).
2. **Closed-world outgoing edge relation $E \subseteq V \times V$ (`LiveClosed`):**
   - Direct calls (`TerminatorKind::Call` and `TerminatorKind::TailCall`);
   - Function-pointer reifications (`CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer)` and `ClosureFnPointer`), which simultaneously mark the target `MonoItem` as `addrSignificant := true`;
   - Virtual dispatch tables (`GlobalAlloc::VTable(ty, trait_ref)` $\to$ every `VtblEntry::Method(instance)` and `drop_in_place::<ty>`);
   - Static/const memory provenance relocations (`GlobalAlloc::Memory(alloc)` $\to$ every `Provenance` `AllocId` in `alloc.provenance().ptrs()`);
   - Synchronous drop glue (`TerminatorKind::Drop { place, .. }` $\to$ `Instance::resolve_drop_in_place(tcx, ty)`) and DWARF/SEH LSDA personality references.

### 2. Lean `v4.34.1` Mechanization of Pre-Proof Pruning and Address-Safe ICF

**Basis: source + execution (`support/VerifiedReachabilityAndIcf.lean`, checked under `anneal-lean-run`)**

Building `support/VerifiedReachabilityAndIcf.lean` via `anneal-lean-run --mode file --concurrency 4 -- lake env lean VerifiedReachabilityAndIcf.lean` checks four theorems with **zero `sorry`** and **zero `native_decide`**:

| Theorem Name | Lines | Statement Summary | Kernel Axioms |
| :--- | :---: | :--- | :--- |
| `unreachable_module_pruning_sound` | `90–109` | `LiveClosed live → lookupItem live s = some it → runProgram fuel (live ++ dead) s v = runProgram fuel live s v`: dead `MonoItem`s unreachable from `live` cannot be entered at any fuel depth and require zero compilation proofs. | `[propext]` |
| `address_safe_icf_fold_sound` | `130–137` | `SafeIcfPair f₁ f₂ → (foldIntoFirst f₁ f₂).stepFn v = f₂.stepFn v ∧ (foldIntoFirst f₁ f₂).codeAddr = f₁.codeAddr ∧ f₂.addrSignificant = false`. | *(none)* |
| `canary_unsound_icf_all_addr_collision` | `157–161` | Refutation canary showing that folding two `addrSignificant = true` functions (`0x1000 ≠ 0x2000`) via `--icf=all` collapses their addresses to `0x1000`. | *(none)* |
| `thunk_icf_preserves_distinct_addr` | `172–176` | `f₁.codeAddr ≠ f₂.codeAddr → f₁.codeAddr ≠ (thunkToFirst f₁ f₂).codeAddr ∧ (thunkToFirst f₁ f₂).stepFn v = .inr (f₁.sym, v)`: a 1-step tail-call thunk preserves distinct function addresses while sharing `f₁`'s body. | *(none)* |

### 3. Empirical Proof-Volume and Binary-Size Reductions

**Basis: execution (`support/prune_and_icf.py`, `support/reachability_icf_savings.json`)**

#### 3.1 Five `V3` Workload Shapes on `x86_64-unknown-linux-gnu`

| Workload (`--crate-type`) | Unpruned (`--no-gc-sections`) `.text` (B) / Unique Bodies / Est. Proof Steps | `--gc-sections` Only `.text` (B) / Unique Bodies / Proof Reduction | Pre-Proof WPO + `--gc-sections` + `--icf=safe` `.text` (B) / Unique Bodies / Est. Proof Steps | Total Proof-Volume Reduction Factor |
| :--- | ---: | ---: | ---: | ---: |
| `hello_world` (`bin`) | `691,501 B` / `2,294` / `55,056` | `241,651 B` (`-65.05%`) / `540` (`4.25x`) | **`223,136 B` / `401` / `9,624`** | **`5.72x`** (`-82.5%` bodies) |
| `cli_tool` (`bin`) | `698,013 B` / `2,307` / `55,368` | `255,059 B` (`-63.46%`) / `576` (`4.01x`) | **`237,898 B` / `426` / `10,224`** | **`5.42x`** (`-81.5%` bodies) |
| `async_server` (`bin`) | `692,269 B` / `2,296` / `55,104` | `250,547 B` (`-63.81%`) / `563` (`4.08x`) | **`229,680 B` / `414` / `9,936`** | **`5.55x`** (`-82.0%` bodies) |
| `cdylib` (`cdylib`) | `691,453 B` / `2,288` / `54,912` | `228,339 B` (`-66.98%`) / `499` (`4.59x`) | **`211,705 B` / `368` / `8,832`** | **`6.22x`** (`-83.9%` bodies) |
| `staticlib` (`staticlib`) | `754,536 B` / `3,081` syms | — | **`284,227 B` (`-62.33%`) / `972` syms** | **`3.17x`** (`-68.5%` syms) |

#### 3.2 Cross-Target Archive Reachability Pruning Across All 8 Tier 1 Targets

| Tier 1 Target | Unpruned `staticlib` `.text` (Bytes) | Pre-Proof Pruned `staticlib` `.text` (Bytes) | Dead Stdlib `.text` Removed (`%`) |
| :--- | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | `754,536` | `284,227` | **`62.33%`** |
| `i686-unknown-linux-gnu` | `840,843` | `346,175` | **`58.83%`** |
| `aarch64-unknown-linux-gnu` | `732,548` | `257,260` | **`64.88%`** |
| `aarch64-apple-darwin` | `694,316` | `249,508` | **`64.06%`** |
| `x86_64-pc-windows-msvc` | `547,815` | `148,888` | **`72.82%`** |
| `x86_64-pc-windows-gnu` | `738,658` | `263,735` | **`64.30%`** |
| `i686-pc-windows-msvc` | `574,687` | `183,779` | **`68.02%`** |
| `aarch64-pc-windows-msvc` | `523,024` | `136,548` | **`73.89%`** |

#### 3.3 `.llvm_addrsig` (`SHT_LLVM_ADDRSIG`) and Function-Pointer Identity Under `--icf=none|safe|all`

| `rust-lld` Mode | `addr_taken_a` VA | `addr_taken_b` VA | `call_only_c` VA | `call_only_d` VA | Runtime `addr_taken_a as usize == addr_taken_b as usize` | Call-Only Clones Folded (`c == d`) |
| :--- | :--- | :--- | :--- | :--- | :---: | :---: |
| `--icf=none` | `0x219d0` | `0x219e0` | `0x219f0` | `0x21a00` | `false` (Distinct) | `false` |
| **`--icf=safe` (`.llvm_addrsig`)** | **`0x219d0`** | **`0x219e0`** | **`0x219f0`** | **`0x219f0`** | **`false` (Sound)** | **`true` (Folded)** |
| `--icf=all` | `0x219d0` | `0x219d0` | `0x219e0` | `0x219e0` | `true` (Collapsed!) | `true` |

## Boundaries

- **Pre-inlining `.anneal-mir` reachability vs. post-inlining `MiniMach` reachability:** Running reachability over `.anneal-mir` before inlining and dead-branch elimination conservatively retains callees referenced inside dead `if false` branches (`540`–`576` functions on `W-Core`/`V3`), whereas running a second lightweight reachability pass after `MiniMach` inlining and constant folding prunes an additional `26%`–`28%` of functions (`down to 368`–`426` functions). Both passes use the exact same `unreachable_module_pruning_sound` theorem.
- **Dynamic symbol interposition (`LD_PRELOAD` / `dylib` exports):** Closed-world pruning (`LiveClosed`) applies to `STB_LOCAL` / `STV_HIDDEN` internal symbols and `--crate-type=bin`/`cdylib`/`staticlib` link units; symbols exported with default visibility from a `dylib` remain in the root set $R$.

## Evidence

- **Support artifacts in `support/`:**
  - `support/VerifiedReachabilityAndIcf.lean`: Lean `v4.34.1` proofs of `unreachable_module_pruning_sound`, `address_safe_icf_fold_sound`, `canary_unsound_icf_all_addr_collision`, and `thunk_icf_preserves_distinct_addr`.
  - `support/prune_and_icf.py`: 5-workload, 8-target reachability pruning and `.llvm_addrsig` / `--icf=safe` evaluation script.
  - `support/reachability_icf_savings.json`: Complete JSON dataset of function counts, `.text` sizes, proof-volume reduction factors, and `SHT_LLVM_ADDRSIG` symbol tables.
- **Upstream `rustc` and LLVM source references:**
  - `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`:
    - `compiler/rustc_codegen_llvm/src/mono_item.rs:190-208` (`UnnamedAddr::Global` on non-exported Rust functions)
    - `compiler/rustc_monomorphize/src/collector.rs` (monomorphization reachability walk)

## Revalidation

Verify the Lean `v4.34.1` proof module and re-run the reachability and ICF analyzer:

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/verified-pre-proof-reachability-pruning-and-address-safe-icf/support/VerifiedReachabilityAndIcf.lean
python3 reports/verified-pre-proof-reachability-pruning-and-address-safe-icf/support/prune_and_icf.py \
  --out /tmp/b4_reachability_icf.json
```
