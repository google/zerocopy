# Lean 4 Scalar MIR Semantics Transfer Barriers (`Trusted.MirSemantics`), `LCNF.floatLetIn` Clock-Sinking, and Perceus/`leanc` Native Performance Hazards

## Summary

Proving bitvector equivalence, structural well-founded recursion, and fast
native performance in Lean `v4.34.1` and `v4.35.0-rc2` exposes five compiler,
elaborator, and runtime mechanisms:

1. **Symbolic `whnf` barriers in `Trusted.MirSemantics` (`joshlf/anneal@31b91b61b84e`):**
   - *`signExtendBits` timeout:* Calling `rfl` on `decodeScalar` of a symbolic
     32-bit `i32` triggers a `(deterministic) timeout at whnf` (`~16.3 s` at
     `200,000` heartbeats; `78,661` `Nat.rec` and `19,330` `Nat.pow` unfoldings
     per `20,000` heartbeats) because `IntWidth.byteSize` and `Nat.pow 2 128`
     are unfolded structurally instead of rewriting through `BitVec.toInt`.
   - *Stuck `Bool.and` / `BEq` flags in `checkVal` and `evalArithOp`:* Testing
     `ScalarVal.wf` (`truncateBits v.width v.bits == v.bits`) or overflow flags
     `(hostOverflow || lossy) && op.isUnchecked` on symbolic operands leaves
     `Bool.and` and `BEq (BitVec 128)` stuck on the left operand even when the
     value came from `truncateBits` or `op.isUnchecked = false`, yielding an
     immediate `rfl` mismatch (`~0.8 s`); signed `evalBinOp .shl` adds `whnf`
     `Nat.pow` blowup (`~19.1–22.0 s`).
   - *Immediate mutant rejection (`>> 16 -> >> 15`):* Running `evalBinOp .shr`
     or symbolic `fastRun` on an off-by-one shift mutant against the unmutated
     specification fails via an **immediate definitional mismatch** (`~0.6–1.3 s`),
     *not* a heartbeat exhaustion timeout, and fails constructively on concrete
     witness `0x18000#32` (`3 ≠ 1`).
   - *Zero-TCB untrusted cures:* Proving `signExtendBits_eq_fast`, `truncateBits_idem`
     (`checkVal_eq_fast_of_wf`), and `evalBinOp_eq_fast` once in untrusted
     lemmas (or using spec-mirroring `gt_mirror_rfl`) reduces all symbolic scalar
     proofs to `< 25 ms` without editing `trusted/`.
2. **Well-founded recursion (`WF.Fix`) `whnf` blowup on bit-shifted match scrutinees:**
   Translating recursive functions over packed `UInt32` tokens where `match`
   scrutinizes `findLengthCode (((w >>> 16) &&& 0x7FFF).toNat)` inline under
   dependent array-size proofs forces `WellFounded.Nat.fix` to unroll 29
   table steps symbolically across `UInt32.toBitVec -> Nat.div.go`, timing out
   at `15,000` heartbeats. Outlining the table lookup and bounds proofs into
   non-recursive `@[inline]` helpers with `{a : Array Nat // a.size = N}`
   (`Subtype`) reduces elaboration to `~35 ms`.
3. **Silent `LCNF.floatLetIn` benchmark clock-sinking in `v4.34.1` vs. `v4.35.0-rc2`:**
   In Lean `v4.34.1`, writing `let r := pureFn x` between `t0 <- IO.monoNanosNow`
   and `t1 <- IO.monoNanosNow` with `if r == 0 then ...` after `t1` causes
   `LCNF.floatLetIn` to sink `l_pureFn` *after* the second `lean_io_mono_nanos_now()`
   call (`2,271 ns` / `100` reps vs. `11,678,809 ns` true cost). Wrapping the
   computation inside `@[noinline] def wrapper : IO ...` preserves execution
   strictly inside `[t0, t1]` (`v4.35.0-rc2` retains `[t0, pure, t1]` ordering on
   `pure_let` directly, though `LCNF.elimDeadVars` still deletes unused `_dead`
   calls in `2,035 ns` across both releases).
4. **Perceus `@&` borrow-alias self-copy quadratic trap:**
   Passing the same `ByteArray` simultaneously to a borrowed `@&` and an owned
   parameter forces `ExplicitRC` to emit `lean_inc_ref` before the call, raising
   `m_rc` from `1` to `2`. Every `lean_is_exclusive(dst)` check returns `false`,
   causing a full buffer copy per append (`210.5x–233.4x` slower over `4,000`
   steps than a single-owned `@[extern]` `ByteArray` primitive).
5. **Freestanding `leanc -nostdinc`, `-O0` `optnone` LTO blocking, and `lean.h` C ABI evolution:**
   Lake's `buildLeanO` (`leanc`) runs Clang with `-nostdinc` (rejecting
   `<string.h>`, requiring `__builtin_memcpy` and explicit `extern
   lean_sarray_ensure_capacity`) and defaults to `-O0` (tagging bitcode with
   `noinline optnone`, which blocks `ld.lld` LTO inlining even under `-O3` link
   flags unless `-O2 -DNDEBUG` is supplied explicitly).

---

## Applicability

These findings govern:

- **Formal MIR verifiers targeting `Lean.Meta.WHNF`:** Applicable to
  `Trusted.MirAst` and `Trusted.MirSemantics` in
  `joshlf/anneal@31b91b61b84e0058db44cacbd6d189a90433c2d1` and untrusted proof
  drivers running under Lean `v4.34.1` (`5045d0056413`). Canonical `List Slot`
  memory state `!e.hasFVar()` scaling is covered separately in
  [`lean-canonical-mir-state-and-compositional-symbolic-execution`](../lean-canonical-mir-state-and-compositional-symbolic-execution/REPORT.md).
- **Lean 4 native C compilation (`leanc` / `EmitC` / `ExplicitRC` / `LCNF`):**
  Applies to Lean `v4.34.1` (`5045d0056413`) and `v4.35.0-rc2` (`11acb17ec6b0`),
  as well as high-throughput FFI projects (`kim-em/lean-zip@2f7a63f38195`). Note
  two concrete cross-version changes:
  1. In `v4.34.1`, `LCNF.floatLetIn` sinks `pureLet` past `t1 <- IO.monoNanosNow`,
     whereas in `v4.35.0-rc2` `l_pureChecksum` remains between the two clock
     reads (while `LCNF.elimDeadVars` still deletes dead `let _` bindings in both).
  2. `<lean/lean.h>` in `v4.35.0-rc2` removes `lean_copy_byte_array` and exposes
     `lean_sarray_ensure_exclusive(a)` inline (`v4.34.1` exported
     `lean_copy_byte_array` while keeping `ensure_exclusive` internal).

---

## Findings

### 1. Scalar `Trusted.MirSemantics` Symbolic `whnf` Barriers and Zero-TCB Cures

`Basis: source + execution`

All measurements in this section execute against the verbatim scalar fragment
from `joshlf/anneal@31b91b61b84e` (`MirAst.lean:124-144, 279-286, 370-403` and
`MirSemantics.lean:130-351, 636-639, 942-1067`) preserved standalone in
[`support/ScalarMirFastStepProbe.lean`](support/ScalarMirFastStepProbe.lean).

#### 1.1 Anatomy of Barriers `W1`–`W3` and the `>> 15` Mutant

| Goal Class | Trusted Expression Attempted via `rfl` | Exact Failure Mechanism | Standalone Outcome (`4000` HB Guard) | Zero-TCB Cure (`< 25 ms` Proved in Probe) |
| :--- | :--- | :--- | :--- | :--- |
| **`W1` Signed decode** | `decodeScalar (i32Sym x) = x.toInt` | `IntWidth.bitWidth` + `bvOfInt 128` structurally unfold `Nat.pow 2 128` through `Nat.rec` | `(deterministic) timeout at whnf` (`~16 s` at default `200,000` HB) | Prove `signExtendBits_eq_fast` (`(v.setWidth w.bitWidth).toInt`) via `bvToInt_bvOfInt_128_of_range`; `rw [signExtendBits_eq_fast]` (`decode_i32Sym_eq_toInt`) |
| **`W2` Well-formedness** | `checkVal (.scalar ⟨.i32, false, truncateBits .i32 x⟩) (.int .i32 false) = true` | `ScalarVal.wf` reduces `truncateBits v.width v.bits == v.bits`; symbolic `BEq (BitVec 128)` blocks | Immediate `Tactic rfl failed` (`~0.7–1.2 s`) | Prove `truncateBits_idem` $\implies$ `scalarWf_truncateBits` and fast `checkValFast` (`checkVal_eq_fast_of_wf`) |
| **`W3` Unsigned arith** | `evalBinOp .add (u32 a) (u32 b) = .ok (.scalar (binAdd a b))` | `Bool.and`/`Bool.or` case-split first arg `(hostOverflow || lossy) && op.isUnchecked` on symbolic `hostOverflow` | Immediate `Tactic rfl failed` | Prove `truncateScalar_total` and `evalBinOp_eq_fast` (`evalBinOpFast`), then `rw [evalBinOp_eq_fast]; rfl` |
| **`W3` Signed shift** | `evalBinOp .shl (.scalar (i32Sym l)) (const 1) = .ok (.scalar (binShlConst ... 1))` | Enters `signExtendBits` inside `truncateScalar` (`Nat.rec`/`Nat.pow` blowup) | `(deterministic) timeout at whnf` (`~19–22 s` at `200,000` HB) | Same `evalBinOp_eq_fast` rewrite (`shl_i32_fast`, `kraft_step_i32_fast`) |
| **Spec mirroring** | `evalBinOp .gt (i32Sym x) 0` against `decide (decodeScalar (i32Sym x) > 0)` | Direct comparison reduces `signExtendBits` -> `whnf` timeout | `(deterministic) timeout at whnf` | Restate spec with trusted comparison term and close via `cases ... <;> rfl` (`gt_mirror_rfl`) without reducing `signExtendBits` |
| **Shift mutant (`>> 15`)** | `evalBinOp .shr (u32 e) (const 15)` vs. `binShrConst ... 16` | Differing shift constants diverge immediately after reduction | **Immediate `Tactic rfl failed`** (not a timeout) | Quantified universal refutation via concrete witness `0x18000#32`: `3 ≠ 1` (`huffEntryLen_mutation_refuted`) |

All `4,000`-heartbeat `#guard_msgs` timeout receipts, mismatch receipts, and
`#print axioms` receipts pass cleanly inside
[`support/ScalarMirFastStepProbe.lean`](support/ScalarMirFastStepProbe.lean)
with standard Lean axioms only (`[propext, Classical.choice, Quot.sound]`).

---

### 2. Well-Founded Recursion (`WF.Fix`) `whnf` Blowup on Shifted Bitfields

`Basis: execution`

When a `termination_by` loop nests a `match` over a table lookup whose argument
contains a stuck bit-shift on a loop variable—such as `match hflc : findLengthCode
(((w >>> 16) &&& 0x7FFF).toNat)` with `w = tokens[i]` and explicit `hlit :
litLenFreqs.size = 286`, `hdist : distFreqs.size = 30` proof parameters—`Lean.Meta.WHNF`
must abstract all recursive calls inside `Lean.Elab.PreDefinition.WF.Fix`. Because
`findLengthCode` calls `findTableCode.go` with concrete fuel `lengthBase.size = 29`,
`WF.Fix` eagerly unrolls `Nat.rec` across all `29` indices, reducing `baseTable[i+1]`
into `Array.toList` and comparing against stuck `UInt32.toBitVec -> Nat.div.go` (`w >>> 16`).
As verified by `[PASS 5]` (`verify_lean_semantics_and_codegen.py`), `tokenFreqsP_Slow`
reliably hits `(deterministic) timeout at whnf` at `15,000` heartbeats.

**Structural cure (`tokenFreqsP_Fast` in `LeanCodegenAndWfProbe.lean`):**
1. Extract every branch's `match` and `omega` index-preservation proof into
   standalone non-recursive `@[inline]` definitions (`bumpLitFreqP`,
   `bumpRefLitFreqP`, `bumpRefDistFreqP`), elaborated outside `WF.Fix`.
2. Bundle array capacity invariants into `{a : Array Nat // a.size = N}` (`Subtype`),
   removing dependent `Prop` parameters from `go`'s recursion signature so
   `WF.Fix` sees non-recursive helper applications and erases `Subtype` at runtime
   (`tokenFreqsP_Fast` elaborates cleanly alongside the rest of the file in
   `~1.16 s` total).

---

### 3. `LCNF.floatLetIn` Clock-Sinking and `LCNF.elimDeadVars` Benchmark Hoisting

`Basis: source + execution`

Microbenchmarking pure Lean functions inside an `IO` loop triggers three LCNF
transformations in `v4.34.1` and `v4.35.0-rc2` (`LeanCodegenAndWfProbe.lean` §1):

| Pattern Under `for _ in [:100] do` | `v4.34.1` Emitted C Placement & Timing | `v4.35.0-rc2` Emitted C Placement & Timing | Underlying Pass |
| :--- | :--- | :--- | :--- |
| `let _dead := pureChecksum data salt` | Deleted (`2,032 ns` total, **`20 ns/rep`**) | Deleted (`2,035 ns` total, **`20 ns/rep`**) | `LCNF.elimDeadVars` drops unused pure `let` |
| `4x` calls summed (`pureChecksum4x`) | `1` call to `l_pureChecksum` (`shl`/fold) | `1` call to `l_pureChecksum` | `LCNF.cse` deduplicates identical pure terms |
| `let r := pureChecksum ...` before `t1`, used in `if r == 0` after `t1` (`benchPureLetSunk`) | **Sunk after `t1`** (`2,271 ns` total, **`23 ns/rep`**) | **Remains inside `[t0, t1]`** (`11,639,590 ns`) | `LCNF.floatLetIn` in `v4.34.1` floats pure `let` across `RealWorld`-erased `IO` bind into the post-`t1` `if` |
| `@[inline] doChecksumInlineIO` | **Sunk after `t1`** (`2,282 ns` total, **`23 ns/rep`**) | **Inside `[t0, t1]`** (`11,637,153 ns`) | `LCNF.simp` inlines `@[inline] IO` pure return back to `benchPureLetSunk` |
| `@[noinline] doChecksumBarrier` (`IO UInt64`) | **Inside `[t0, t1]`** (`11,678,809 ns`, `~117 us/rep`) | **Inside `[t0, t1]`** (`11,626,464 ns`, `~116 us/rep`) | `IO` return value forces `EStateM` tag case-split before second `lean_io_mono_nanos_now()` |

Because `@[noinline]` in Lean only marks the LCNF pass and omits Clang's
`__attribute__((noinline))` in C, enclosing timed pure workloads inside an
`@[noinline] ... IO` wrapper whose scalar/size result is consumed *after* `t1`
is mandatory across versions—especially on `v4.34.1` where `floatLetIn` silently
sinks pure computations past `t1` while the outer loop still consumes full CPU
wall time.

---

### 4. Perceus `@&` Borrow-Alias Quadratic Copy Cascade & `leanc` Freestanding Rules

`Basis: source + execution`

#### 4.1 Perceus `@&` Aliasing (`m_rc == 2`) vs. Single-Owned Mutation (`m_rc == 1`)

In `Lean.Compiler.LCNF.ExplicitRC`, passing the same `ByteArray` argument `a` as
both a borrowed parameter (`src : @& ByteArray`, C ABI `b_lean_obj_arg`) and an
owned destination (`dst : ByteArray`, `lean_obj_arg`)—as happens whenever
`ByteArray.copySlice a srcOff a a.size len false` or `a ++ a` runs—forces
`ExplicitRC` to emit `lean_inc_ref(a)` immediately before the call (`l_stepAliased`).
That increments `m_rc` from `1` to `2`, so `lean_is_exclusive(dst)` evaluates to
`false` (`2 != 1`) inside `lean_byte_array_copy_slice`, allocating and copying
the full buffer on every append ($\Theta(N^2)$). Defining a single-owned wrapper
`@[extern "probe_byte_array_copy_within"] (a : ByteArray) (srcOff len : @& Nat)`
eliminates `lean_inc_ref`, preserves `m_rc == 1`, and speeds up `4,000`
`64`-byte appends by **`210.5x`** on `v4.34.1` (`233.4x` on `v4.35.0-rc2`).

#### 4.2 Boxing Tax in `ByteArray` Reductions (`data.data.foldl` vs. `do` vs. Tail `USize`)

As measured in `LeanCodegenAndWfProbe.lean` over `2 MiB`:
- `data.data.foldl` materializes `lean_byte_array_data(data)` (an `8 * N` =
  `16 MiB` boxed `Array UInt8` copy for `2 MiB`) and allocates a boxed `Nat × Nat`
  pair per byte (`~111–121 MB/s`);
- `Id.run do` with `let mut a, b : UInt32` (`for h : i in [0:n] do`) avoids
  copying the array, yet `forIn'` boxes `a, b` into a heap `MProd` with boxed `Nat`
  counter (`~189–197 MB/s`);
- Explicit tail recursion taking `(data : @& ByteArray) (i n : USize) (a b : UInt32)`
  erases `n.toNat ≤ data.size` and runs unboxed in `size_t`/`uint32_t` registers
  (`~332–341 MB/s`).

#### 4.3 `leanc -nostdinc`, `-O0` `optnone`, and `-plugin-opt=O3`

1. **`-nostdinc` freestanding C:** `leanc` invokes Clang with `-nostdinc -isystem
   <toolchain>/include/clang -I<toolchain>/include`, rejecting `#include <string.h>`
   with `fatal error: 'string.h' file not found`. C FFI shims compiled for Lean LTO
   must use `__builtin_memcpy`/`__builtin_memset` and declare `extern lean_object
   *lean_sarray_ensure_capacity(lean_object *a, size_t min_cap, int exact);`
   directly.
2. **`-O0` `optnone` traps:** Custom Lake C compilation rules calling `leanc -c`
   without `-O2 -DNDEBUG` compile FFI shims at `-O0`, emitting LLVM bitcode
   marked `attributes #0 = { noinline nounwind optnone ... }`. Even when linked
   with `-flto -O3`, `ld.lld` strictly honors `optnone` and keeps every FFI byte
   load out-of-line. Passing `-O2 -DNDEBUG -flto -fno-semantic-interposition`
   strips `noinline optnone` and enables `local_unnamed_addr` bitcode inlining,
   while `-O3` in link arguments selects `ld.lld` `-plugin-opt=O3` (verified by
   `leanc -###`).

---

## Boundaries

- **Scalar `Trusted.MirSemantics` scope:** [`ScalarMirFastStepProbe.lean`](support/ScalarMirFastStepProbe.lean)
  copies verbatim scalar definitions from `joshlf/anneal@31b91b61b84e` so it
  runs standalone without Lake/MirWp; pointer/memory effects live in
  `M.Memory` (`proofs-rs/lean-miri`) and [`lean-canonical-mir-state-and-compositional-symbolic-execution`](../lean-canonical-mir-state-and-compositional-symbolic-execution/REPORT.md).
- **Lean toolchain matrix:** Verified specifically on Lean `v4.34.1` and
  `v4.35.0-rc2` (`x86_64-unknown-linux-gnu`); `WF.Fix` heartbeat thresholds
  depend on `maxHeartbeats` (`15,000` for timeout, default `200,000` for full).

---

## Evidence

### 1. Primary Upstream Sources Examined

- **`joshlf/anneal` (`31b91b61b84e0058db44cacbd6d189a90433c2d1`):**
  - `trusted/lean/Trusted/MirAst.lean:124-144, 279-286, 370-403`.
  - `trusted/lean/Trusted/MirSemantics.lean:130-351, 636-639, 942-1067, 1213-1224`.
- **`leanprover/lean4` (`v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52` and `v4.35.0-rc2` `11acb17ec6b07a8f9e9173e6845197929540936b`):**
  - Observed `lean --c` / `leanc -###` / `leanc -S -emit-llvm` outputs produced
    across both toolchains by `verify_lean_semantics_and_codegen.py`.

### 2. Preserved Package Support Artifacts

- [`support/ScalarMirFastStepProbe.lean`](support/ScalarMirFastStepProbe.lean):
  Standalone Lean `v4.34.1` probe reproducing `W1`–`W3` timeouts/mismatches,
  `>> 15` immediate rejection, zero-TCB fast-step lemmas, and `#print axioms`
  `#guard_msgs` receipts (`3.82 s`).
- [`support/LeanCodegenAndWfProbe.lean`](support/LeanCodegenAndWfProbe.lean) and
  [`support/copy_within_ffi.c`](support/copy_within_ffi.c): Standalone Lean +
  C FFI probe reproducing `elimDeadVars`, `CSE`, `floatLetIn` (`v4.34.1` vs.
  `v4.35.0-rc2`), Perceus `@&` `lean_inc_ref` cascading vs. single-owned FFI,
  `WF.Fix` timeout on `w >>> 16` vs. `Subtype`, and `ByteArray` boxing gaps.
- [`support/verify_lean_semantics_and_codegen.py`](support/verify_lean_semantics_and_codegen.py):
  Automated verification harness checking both Lean toolchains (`v4.34.1`,
  `v4.35.0-rc2`), LLVM IR `optnone` vs. `-O2`, `-nostdinc`, `-plugin-opt=O3`,
  and runtime speedups.

---

## Revalidation

Run the self-contained verification suite (wrapping `lean`/`leanc` invocations in
`anneal-lean-run` when available):

```console
python3 reports/lean-mir-semantics-scalar-truncation-idempotence-and-fast-step-transfer/support/verify_lean_semantics_and_codegen.py
```

The command must exit `0` with `"status": "PASS"`, reporting `"sunk_past_t1"` for
`v4.34.1`, `"ordered_inside_t0_t1"` for `v4.35.0-rc2`, `> 20x` (observed `~210x–233x`)
Perceus single-owned speedup, `"wf_slow_whnf_timeout": true`, and
`"leanc_nostdinc_and_optnone_verified": true`.
