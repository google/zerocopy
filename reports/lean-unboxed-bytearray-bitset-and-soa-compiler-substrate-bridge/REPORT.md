# Closing the Lean 4.34.1 Bitset and Buffer Substrate Gap via Unboxed Scalar Arrays, `BitSet64` Bridges, and Struct-of-Arrays Loops

## Summary

Diagnosing the LCNF compiler and C runtime (`include/lean/lean.h`) root causes of the `4.51x`–`28.34x` Lean `v4.34.1` slowdown reported in `compiler-substrate-benchmarks-lean-rust-and-ocaml` and refactoring all six canonical compiler kernels (`support/x3_substrate/`, `support/run_x3_bench.py`, `support/metrics.json`) compresses the Compiled Lean `v4.34.1` vs. Rust `1.99.1` performance ratio from **`4.51x`–`28.34x`** down to **`0.49x`–`4.65x`** (`1.17x` on instruction encoding, `1.23x` on SSA IR parsing, `1.56x` on dominator trees, `3.06x` on union-find, `4.65x` on linear-scan register allocation, and `0.49x` on packed flat symbol tables):

1. **Four Concrete C-Codegen Root Causes in `include/lean/lean.h` and LCNF Lowering:**
   - **Heap Allocation on Every `UInt64` Box (`lean_box_uint64`, `lean.h:3001–3005`):** Because 64-bit Lean pointers reserve bit 0 as the scalar tag (`lean_is_scalar`), `lean_box_uint32` tags 32-bit integers in-pointer (`0` heap allocations), whereas `lean_box_uint64` calls `lean_alloc_ctor(0, 0, sizeof(uint64_t))` on **every** insertion into `Array UInt64`, `Std.HashMap UInt64 UInt64`, or a polymorphic tuple (`Prod` / `MProd`). Only `ByteArray` (`elem_size = 1`) and `FloatArray` (`elem_size = 8`, `lean_sarray_object` at `lean.h:204–209`) store unboxed 64-bit C primitives contiguously.
   - **GMP `Nat` Loop Counters vs. `UInt32` / `USize` (`lean_nat_add` / `lean_nat_dec_le`):** Writing `for i in [0:n]` or recursing over `i : Nat` passes boxed `lean_object*` GMP integers across iterations. Switching loop indices to `UInt32` or `USize` lowers to raw C `uint32_t` / `size_t` registers.
   - **`MProd` Tuple Boxing in Multi-Variable `for`/`while` Loops:** Updating $>1$ `let mut` variable inside a `for`/`while` block lowers to `Std.Range.forIn.loop` over nested `MProd` constructor cells (`134` `lean_alloc_ctor` sites in `K4Bench.c`). Replacing multi-variable `for`/`while` loops with tail-recursive functions taking scalar parameters—and packing small multi-scalar returns into a single `UInt64` bitfield `(a <<< 48) ||| (b <<< 32) ||| c`—compiles to register-only C `goto` loops (`lean_alloc_ctor` sites drop by **`82.1%`**, from `134` to `24`).
   - **Cross-DSO `lean_byte_array_push` Calls vs. Inlined `lean_byte_array_uset` (`lean.h:1220–1246`):** `ByteArray.push` is an exported `libleanshared.so` symbol (`LEAN_EXPORT`), whereas `ByteArray.set!` (`lean_byte_array_uset` / `lean_byte_array_fset`) is a `static inline` header write (`*it = v`).
2. **Verified `BitSet64` Refinement Bridge in Lean `v4.34.1` (`support/x3_substrate/BitSet64.lean`):**
   - A zero-`sorry`, zero-`native_decide` Lean `v4.34.1` library formalizes unboxed 64-bit word bitsets (`Word64`) and multi-word bitsets (`MultiBitSet`) and proves exact bitwise equivalence (`mem_empty`, `mem_union`, `mem_inter`, `mem_diff`, `mem_symDiff`, `zipUnion_memBit`) against pure mathematical bit predicates.

## Applicability

- **Extends:** `compiler-substrate-benchmarks-lean-rust-and-ocaml`, `lean-native-compilation-pipeline-runtime-and-trust-surface`
- **Metadata:** Created: 2026-11-14 · Updated: 2026-11-14
- **Subjects:**
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `include/lean/lean.h` lines `196`–`209`, `1188`–`1280`, `2979`–`3025`, and `leanc -O3`).
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, `--release -C opt-level=3 -C lto=thin`).

## Findings

### 1. Six-Kernel Head-to-Head Re-Benchmark: Baseline `K4` Lean vs. Unboxed/SoA Lean `v4.34.1` vs. Rust `1.99.1`

**Basis: execution + source (`support/x3_substrate/X3Bench.lean`, `support/run_x3_bench.py`, `support/metrics.json`)**

All six refactored Lean `v4.34.1` kernels verify the exact same 64-bit deterministic output checksums as `compiler-substrate-benchmarks-lean-rust-and-ocaml` across 7 timed iterations:

| Kernel ID | Rust `1.99.1` Median (`ms`) | Baseline `K4` Lean Median (`ms`) | Refactored Unboxed/SoA Lean Median / P95 (`ms`) | Speedup Over `K4` Lean | New Lean / Rust Ratio (was `K4`) | Shared 64-Bit Checksum | Key Unboxed / SoA Transformation |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| **`dom_ssa`** ($V = 20{,}000$) | `0.259` | `1.261` | **`0.403`** / `0.677` | **`3.13x`** | **`1.56x`** *(was `4.87x`)* | `2621001246` | `UInt32` block indices (`lean_box_uint32` tag) + tail-recursive `goto` loops |
| **`hashmap_intern`** ($5 \times 10^5$ ops) | `27.014` | `141.192` | **`13.230`** / `17.959` | **`10.67x`** | **`0.49x`** *(was `5.23x`)* | `3874992250000` | Single-array open-addressed `FloatArray` (`lean_sarray_object`) packing `(kTag28 <<< 28) \|\|\| val28` |
| **`egraph_uf`** ($2 \times 10^5$ classes) | `5.170` | `44.105` | **`15.822`** / `16.493` | **`2.79x`** | **`3.06x`** *(was `8.53x`)* | `25239800000` | Bit-packed `(rank8 <<< 24) \|\|\| parent24` in single `Array UInt32`; decoupled root find from halving |
| **`regalloc`** ($10^5$ vregs, 16 pregs) | `0.377` | `10.685` | **`1.751`** / `1.775` | **`6.10x`** | **`4.65x`** *(was `28.34x`)* | `7813181233` | Unboxed `UInt32` loop counters + 64-bit packed `(allocated <<< 48) \|\|\| (maxReg <<< 32) \|\|\| maxVal` return |
| **`inst_encode`** ($2 \times 10^6$ insts) | `6.390` | `28.792` | **`7.445`** / `9.331` | **`3.87x`** | **`1.17x`** *(was `4.51x`)* | `17000000` | Pre-sized `8 MB` `ByteArray` (`mkZeroByteArray`) + inlined `ByteArray.set!` (`lean_byte_array_fset`) |
| **`ir_parser`** ($5 \times 10^5$ SSA lines) | `9.198` | `76.809` | **`11.292`** / `11.345` | **`6.80x`** | **`1.23x`** *(was `8.35x`)* | `2147484415133360` | Tail-recursive `parseDigits` returning `(nextPos <<< 32) \|\|\| val` in a single `uint64_t` register |

---

### 2. C Runtime Boxing Audit (`include/lean/lean.h`) and Generated C Telemetry (`K4Bench.c` vs. `X3Bench.c`)

**Basis: source + execution (`include/lean/lean.h`, `support/metrics.json`)**

Inspecting `include/lean/lean.h` in `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` explains why polymorphic containers (`Array α`, `Prod α β`, `MProd α β`, `Std.HashMap`) incur heavy allocation overhead on 64-bit integers:

```c
// include/lean/lean.h:2979-3005
static inline lean_obj_res lean_box_uint32(uint32_t v) {
    if (sizeof(void*) == 4) {
        lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(uint32_t));
        lean_ctor_set_uint32(r, 0, v);
        return r;
    } else {
        return lean_box(v); // ((lean_object*)(((size_t)(v) << 1) | 1)) — ZERO heap allocation!
    }
}

static inline lean_obj_res lean_box_uint64(uint64_t v) {
    lean_obj_res r = lean_alloc_ctor(0, 0, sizeof(uint64_t)); // Heap-allocates 16B on EVERY box!
    lean_ctor_set_uint64(r, 0, v);
    return r;
}
```

1. **Why `Array UInt32` is Free of Element Heap Allocations While `Array UInt64` Heap-Allocates:**
   - Because `lean_array_object` (`lean.h:196–201`) stores `lean_object* m_data[]`, storing a `UInt32` on x86-64 invokes `lean_box_uint32`, which shifts the 32-bit integer into a tagged pointer (`(v << 1) | 1`) with zero heap traffic. Storing a `UInt64` into `Array UInt64` invokes `lean_box_uint64`, allocating a 16-byte heap object per write.
   - Conversely, `lean_sarray_object` (`lean.h:204–209`) stores raw unboxed bytes (`ByteArray`, `elem_size = 1`) or 8-byte IEEE-754 `double` words (`FloatArray`, `elem_size = 8`, `lean.h:1248–1279`). Packing a 56-bit non-NaN payload `(kTag28 <<< 28) ||| val28` (where bits `56..63` are `0`, guaranteeing a subnormal IEEE-754 float that is never canonicalized as `NaN`) into `FloatArray` via `Float.ofBits` and reading via `Float.toBits` provides a pure, safe, unboxed 64-bit word array (`uint64_t[]`) in standard Lean 4 without `@[extern]` C shims.
2. **Generated C Code Telemetry (`K4Bench.c` vs. `X3Bench.c`):**

| C Codegen Metric (`.lake/build/ir/*.c`) | `K4Bench.c` (Idiomatic `for`/`while` + `Std.HashMap`) | `X3Bench.c` (Unboxed Tail-Rec + `sarray` + Bit-Packing) | Reduction / Improvement |
| :--- | ---: | ---: | :--- |
| **Generated C Lines / Bytes** | `9,598` lines (`385,112 B`) | **`4,250` lines (`172,665 B`)** | **`2.26x` smaller C code (`-55.7%`)** |
| **`lean_alloc_ctor` Call Sites** | `134` | **`24`** | **`5.58x` fewer constructor allocations (`-82.1%`)** |
| **`lean_inc` Ref-Count Sites** | `261` | **`54`** | **`4.83x` fewer `lean_inc` sites (`-79.3%`)** |
| **`lean_dec` Ref-Count Sites** | `846` | **`282`** | **`3.00x` fewer `lean_dec` sites (`-66.7%`)** |
| **Peak Runtime Memory (RSS)** | `49.10 MB` | **`44.30 MB`** | **`-9.8%` lower peak RSS** |

---

### 3. Verified `BitSet64` Refinement Bridge (`support/x3_substrate/BitSet64.lean`)

**Basis: source + execution (`support/x3_substrate/BitSet64.lean`)**

To support verified liveness, dominator-frontier, and register-interference checkers over unboxed 64-bit words, `BitSet64.lean` (`128` lines, zero `sorry`, zero `native_decide`) proves the correspondence between bitwise word operations (`Word64` and `MultiBitSet.zipUnion`) and logical bit membership (`mem w i := w.bits.getLsbD i`):

```lean
theorem mem_empty (i : Nat) : mem empty i = false
theorem mem_union (a b : Word64) (i : Nat) : mem (union a b) i = (mem a i || mem b i)
theorem mem_inter (a b : Word64) (i : Nat) : mem (inter a b) i = (mem a i && mem b i)
theorem mem_diff  (a b : Word64) (i : Nat) (hi : i < 64) : mem (diff a b) i = (mem a i && !mem b i)
theorem zipUnion_memBit (xs ys : List Word64) (wIdx bIdx : Nat) (hlen : xs.length = ys.length) :
    (MultiBitSet.mk (MultiBitSet.zipUnion xs ys)).memBit wIdx bIdx =
      ((MultiBitSet.mk xs).memBit wIdx bIdx || (MultiBitSet.mk ys).memBit wIdx bIdx)
```

## Boundaries

- **Packing arbitrary 64-bit `UInt64` bit patterns into `FloatArray` when bits `52..62` are all `1` (`0x7FF0000000000000`) — known not to apply without NaN-Payload Masking:** In IEEE-754 double precision, values with exponent `0x7FF` and non-zero mantissa are `NaN`. While `Float.ofBits` / `Float.toBits` in `lean.h` performs a raw `memcpy` bit-cast on x86-64, keeping bits `56..62` non-all-ones (for example, packing $\le 56$ payload bits per `FloatArray` element or using `ByteArray` for full 64-bit arbitrary masks) avoids any target-dependent FPU NaN canonicalization.
- **Remaining `3.06x` (`egraph_uf`) and `4.65x` (`regalloc`) gap vs. Rust `1.99.1`:** Even after eliminating `MProd` tuple allocations, `Array.set!` on `Array UInt32` checks `lean_is_exclusive(a)` (`m_rc == 1`) and shifts tagged pointers `lean_unbox_uint32` (`v >> 1`) on every read/write, whereas Rust mutates `[u32; 16]` on the stack and `Vec<u32>` via raw pointers.

## Evidence

- **Lean `v4.34.1` C Runtime Header (`include/lean/lean.h` in `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
  - `lean_array_object` and `lean_sarray_object` (`lines 196–209`)
  - `lean_byte_array_push` vs. `lean_byte_array_uset` / `lean_float_array_uget` (`lines 1220–1279`)
  - `lean_box_uint32` vs. `lean_box_uint64` (`lines 2979–3005`)
- **Verified `BitSet64` Bridge and Refactored Benchmark Suite (`support/x3_substrate/`):**
  - `support/x3_substrate/BitSet64.lean` (`lines 1–128`)
  - `support/x3_substrate/X3Bench.lean` (`lines 1–312`)
  - `support/run_x3_bench.py` and `support/metrics.json`

## Revalidation

Run the benchmark and C-telemetry verification script from the package directory:

```bash
python3 support/run_x3_bench.py
```

The script compiles `BitSet64` and `x3_bench` under `anneal-lean-run --mode build --concurrency 4 -- lake build`, inspects `.lake/build/ir/X3Bench.c` for constructor/RC counts, executes all 6 benchmarks, asserts exact 64-bit checksum equality against the `K4` Rust `1.99.1` baselines, and writes `support/metrics.json`.
