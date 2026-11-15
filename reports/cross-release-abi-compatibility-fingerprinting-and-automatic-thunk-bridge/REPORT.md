# Cross-Release `AbiCompatHash` Fingerprinting and Verified Caller/Callee ABI Marshaling Thunk Synthesis (`AbiBridgeThunk`)

## Summary

In Wave 5 (`rustc-multi-release-mir-abi-drift-and-version-isolated-adapter` and
`compiler-upgrade-soundness-quarantine-and-proof-invalidation-bounds`), upgrading
`rustc` from `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) to `1.100.0`
(`0ef1bc386059596dada8fb65b50425aab2ea637a`) exposed a cross-release binary
linking boundary: when upstream `rustc` modifies an internal `CanonAbi::Rust`
calling convention—specifically `1.100.0` PR `#161583` on `i686` (`x86_32`),
which moved up to three `f32`/`f64`/SIMD parameters from `[esp + disp]` stack
slots into `XMM0..XMM2`, and `1.100.0`'s representation change from
`PassMode::Cast { pad_i32: bool }` to `PassMode::Cast { pad_i32_count: u8 }`—the
Wave 5 adapter invalidated and rebuilt `100.0%` of pre-compiled `.rlib` crates
for the affected target.

Mechanizing **`PhysicalFnAbi`**, **`abiCompatEq` (`AbiCompatHash`)**, and
**`synthesizeBridgeThunk` (`AbiBridgeThunk`)** in Lean `v4.34.1`
([`support/AbiBridge.lean`](support/AbiBridge.lean)) and evaluating cross-release
linking across the 12-crate benchmark corpus (`13,683` post-`-O3` functions)
between `rustc 1.99.1` and `rustc 1.100.0`
([`support/run_abi_bridge_probe.py`](support/run_abi_bridge_probe.py),
[`support/abi_bridge_metrics.json`](support/abi_bridge_metrics.json)) establishes
three architectural results:

1. **Per-Signature Physical `AbiCompatHash` Eliminates False-Positive Rebuild
   Cascades Across `1.99.1 -> 1.100.0` (`100.0%` Reuse on `x86_64`/`aarch64`,
   `97.81%` Direct Reuse on `i686`):**
   - Computing `AbiCompatHash(sig)` over the lowered physical argument/return
     locations (`PhysicalFnAbi`: `convId`, `args : List PhysicalArgLoc`,
     `ret : PhysicalArgLoc`, `calleePopBytes`, `canUnwind`) rather than internal
     `rustc_target::callconv` AST variants normalizes `PassMode::Cast { pad_i32: true }`
     (`1.99.1`) and `PassMode::Cast { pad_i32_count: 1 }` (`1.100.0`) to the
     exact same SHA-256 digest (`cc097ee6db2546f2...`).
   - Consequently, **`100.0%` (`13,683 / 13,683`)** of cached `.rlib` functions
     and Tier 3 `CompiledArtifactKey` proofs link directly across `1.99.1 ->
     1.100.0` on `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and
     `x86_64-pc-windows-msvc` (`direct_link_sound_of_abi_eq`,
     [`support/AbiBridge.lean:183-200`](support/AbiBridge.lean#L183-L200)).
   - On `i686-unknown-linux-gnu`, **`97.81%` (`13,383 / 13,683`)** of post-`-O3`
     functions pass only integer, pointer, reference, slice, or non-float
     aggregate arguments, retaining an identical `AbiCompatHash`
     (`98b4a9d45c3efc53...`) and linking directly with zero overhead.
2. **Kernel-Checked Caller/Callee Marshaling Thunk Synthesis (`bridge_thunk_sound`
   and `i686_1100_to_1991_float_thunk_sound`):**
   - For the remaining `2.19%` (`300 / 13,683`) of `i686` functions whose
     signatures pass or return `f32`/`f64`/SIMD values under `CanonAbi::Rust`,
     `285 / 300` (`2.08%` of corpus functions) are invoked exclusively via
     direct symbol calls.
   - Instead of invalidating the upstream `.rlib` object section or re-running
     `HybridTrace` verification on the callee, the linker adapter synthesizes a
     deterministic 7-instruction (`26`-byte) marshaling trampoline
     `__anneal_abi_thunk_v2_to_v1_<sym>` (`synthesizeBridgeThunk`) that moves
     `XMM0..XMM2` into the callee's expected `[esp + disp]` stack slots, calls
     the unmodified `1.99.1` callee, and loads the return value into `XMM0`.
   - Theorem `bridge_thunk_sound`
     ([`support/AbiBridge.lean:250-285`](support/AbiBridge.lean#L250-L285)) and
     its concrete `i686` `#161583` instantiation
     `i686_1100_to_1991_float_thunk_sound`
     ([`support/AbiBridge.lean:316-327`](support/AbiBridge.lean#L316-L327),
     checked with `[propext, Quot.sound]` only) prove that a `callerAbi` caller
     composed with `AbiBridgeThunk` and a cached `calleeAbi` callee produces the
     exact mathematical return value `sem argVals` in `callerAbi.ret` while
     preserving `calleeSaved` registers and `spOffset`.
3. **Selective `FnPtrAbiHash` Tracking for Indirect `fn(f32) -> f32` Pointers
   (`0.11%` of Corpus Functions):**
   - Only `15 / 13,683` (`0.11%`) functions on `i686` both pass float/SIMD
     values under `CanonAbi::Rust` and have their address taken as an indirect
     `fn` pointer or trait vtable slot across crate boundaries. Embedding
     `AbiCompatHash` into `.anneal-mir` function-pointer type metadata isolates
     selective recompilation to those `15` functions (`0.11%`), avoiding `99.89%`
     of cross-release `.rlib` proof rebuilds on `i686`.

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc 1.100.0`
(`0ef1bc386059596dada8fb65b50425aab2ea637a`), `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), and Anneal
(`joshlf/anneal@7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) when linking
cached `.rlib` artifacts and Tier 3 `CompiledArtifactKey` proofs across
compiler point releases.

It extends three corpus reports:
- `rustc-multi-release-mir-abi-drift-and-version-isolated-adapter`
- `lean-fnabi-marshaling-refinement-sysv64-win64-aapcs64-i686`
- `automated-toolchain-table-regeneration-and-mir-minissa-upgrade-validator`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Lean `v4.34.1` Mechanization of `AbiCompatHash` and `AbiBridgeThunk`

Basis: source + execution

In [`support/AbiBridge.lean`](support/AbiBridge.lean), `PhysicalArgLoc` models
physical argument and return locations (`.gpr r`, `.xmm x`, `.stack s`), and
`CallFrameState` models register files, stack slots, `calleeSaved` registers,
and `spOffset`. All four primary theorems verify with zero `sorryAx` and zero
`Lean.ofReduceBool`:

| Theorem Name | Lines | Axiom Footprint | Verified Contract |
| :--- | :---: | :---: | :--- |
| `direct_link_sound_of_abi_eq` | `183-200` | `[propext, Quot.sound]` | When `abiCompatEq callerAbi calleeAbi = true`, `execDirectCall` yields `sem argVals` in `callerAbi.ret` and preserves `calleeSaved` and `spOffset` without a bridge thunk. |
| `bridge_thunk_sound` | `250-285` | `[propext, Quot.sound]` | For any `thunk` satisfying `checkBridgeThunk callerAbi calleeAbi thunk = true`, `execBridgedCall` marshals `callerAbi.args -> calleeAbi.args` and `calleeAbi.ret -> callerAbi.ret`, yielding `sem argVals` and preserving `calleeSaved` and `spOffset`. |
| `i686_1100_to_1991_float_thunk_sound` | `316-327` | `[propext, Quot.sound]` | Concrete proof that `i686FloatThunk_1100_to_1991` soundly bridges a `rustc 1.100.0` `i686` caller (`[.gpr 0, .xmm 0, .xmm 1] -> .xmm 0`) to a cached `rustc 1.99.1` callee (`[.gpr 0, .stack 1, .stack 2] -> .stack 0`). |
| `canary_unbridged_i686_1100_to_1991_corrupts_float_args` | `339-344` | `[propext]` | Negative canary proving that linking a `1.100.0` `XMM0..XMM1` caller directly to a `1.99.1` stack-float callee without `AbiBridgeThunk` reads zeroed stack slots instead of the float arguments `0x3f800000` (`1.0f`) and `0x40000000` (`2.0f`). |

### 2. Cross-Release `1.99.1 -> 1.100.0` `AbiCompatHash` Census Across Tier 1 Targets

Basis: execution + derived

Table 1 summarizes the cross-release `AbiCompatHash` compatibility census across
the 12-crate benchmark corpus (`13,683` post-`-O3` functions) produced by
[`support/run_abi_bridge_probe.py`](support/run_abi_bridge_probe.py)
([`support/abi_bridge_metrics.json`](support/abi_bridge_metrics.json)):

| Target Triple | Total Post-`-O3` Functions | Direct `AbiCompatHash` Match (`0` Thunks) | Bridged via Synthesized `AbiBridgeThunk` | Indirect `fn`-Ptr Float Functions Recompiled | Upstream `.rlib` Callee Proofs Rebuilt (Monolithic `X8`/`X10` vs. `K6_`) |
| :--- | :---: | :---: | :---: | :---: | :---: |
| `x86_64-unknown-linux-gnu` | `13,683` | **`13,683` (`100.0%`)** | `0` (`0.0%`) | `0` (`0.0%`) | `100.0%` $\to$ **`0.0%`** |
| `aarch64-unknown-linux-gnu` | `13,683` | **`13,683` (`100.0%`)** | `0` (`0.0%`) | `0` (`0.0%`) | `100.0%` $\to$ **`0.0%`** |
| `x86_64-pc-windows-msvc` | `13,683` | **`13,683` (`100.0%`)** | `0` (`0.0%`) | `0` (`0.0%`) | `100.0%` $\to$ **`0.0%`** |
| `i686-unknown-linux-gnu` | `13,683` | **`13,383` (`97.81%`)** | **`285` (`2.08%`)** | **`15` (`0.11%`)** | `100.0%` $\to$ **`0.0%` direct / `0.11%` total** |

In the live binary execution harness inside
[`support/run_abi_bridge_probe.py`](support/run_abi_bridge_probe.py), the
7-instruction (`26`-byte) `__anneal_abi_thunk_v2_to_v1` bridge executes
`1,000,000` mixed-ABI calls `(7u, 1.5f, 4.0) -> 13.0f` (`0x41500000` bit-exact
IEEE-754 match) at **`2.67 ns`/call** (`~8–9` CPU cycles on `x86_64`), while
eliminating multi-second upstream `.rlib` recompilation and kernel proof
re-checking.

## Boundaries

1. **Struct Layout Drift (`ReprOptions::niche_versions` or Field Reordering Under `repr(Rust)`):**
   - `AbiBridgeThunk` bridges calling-convention register/stack placement shifts
     (`PhysicalArgLoc`) when argument and return *memory layouts* (`size`,
     `align`, field offsets) agree. If an upstream compiler upgrade changes the
     internal byte offsets of a non-`#[repr(C)]` `repr(Rust)` struct passed
     across crates, `TypeLayoutHash` inside `.anneal-mir` changes and triggers a
     standard Tier 1/Tier 2 rebuild for functions touching that struct type.
2. **C-Variadic (`extern "C" fn(..., ...)`) Signatures:**
   - `synthesizeBridgeThunk` requires fixed arity (`callerAbi.args.length ==
     calleeAbi.args.length`); C-variadic functions already use the stable target
     platform C ABI (`CanonAbi::C`), whose `AbiCompatHash` never changes across
     `rustc` releases.

## Evidence

1. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/AbiBridge.lean`](support/AbiBridge.lean): `PhysicalFnAbi`,
     `direct_link_sound_of_abi_eq`, `bridge_thunk_sound`,
     `i686_1100_to_1991_float_thunk_sound`, and
     `canary_unbridged_i686_1100_to_1991_corrupts_float_args` (zero `sorryAx`,
     zero `Lean.ofReduceBool`).
2. **12-Crate `1.99.1 -> 1.100.0` `AbiCompatHash` Census & Live Thunk Execution Probe:**
   - [`support/run_abi_bridge_probe.py`](support/run_abi_bridge_probe.py)
   - [`support/abi_bridge_metrics.json`](support/abi_bridge_metrics.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lean \
  reports/cross-release-abi-compatibility-fingerprinting-and-automatic-thunk-bridge/support/AbiBridge.lean
python3 reports/cross-release-abi-compatibility-fingerprinting-and-automatic-thunk-bridge/support/run_abi_bridge_probe.py \
  --out /tmp/abi_bridge_metrics.json
```
