# Greedy Zero-Ward `Niche::reserve` Multi-Level Niche Stacking, `#[repr(...)]` Discriminant Layouts, and `zerocopy::TryFromBytes` Tag-First Validation

## Summary

Rust's enum layout engine in `compiler/rustc_abi` does not assign niche tags monotonically upward for nested `Option` types. Instead, `Niche::reserve` selects extension directions greedily toward signed zero over wrapping scalar intervals (`WrappingRange`), combined with an explicit special case excluding `bool`'s initial `0..=1` range. Across all three audited `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, and `20fe935d50367c0ff8872c2ebfa050c5c99d9201`), single-niche extension (`count == 1`) skips the naive `[0, 1, 2, 3]` progression on nested `Option`s:

- **`Option<bool>` -> `[0, 1, 2]` (`1` byte):** `bool` (`valid_range = 0..=1`) triggers the `bool` guard (`is_bool` / `v != WrappingRange { start: 0, end: 1 }`), bypassing the signed zero-ward branch and falling into `move_end`, encoding `Some(false) = 0`, `Some(true) = 1`, `None = 2`.
- **`Option<Option<bool>>` -> `[0, 1, 2, 255]` (`1` byte, `0x03` is UB):** At depth 2 (`valid_range = 0..=2`), the initial-`bool` guard no longer matches. With `count == 1`, `next_down = |0 - 1|_i8 = 1 <= next_up = |2 + 1|_i8 = 3`, so `Niche::reserve` selects `move_start` and wraps below zero to `255` (`0xff`). Byte `0x03` lies strictly outside the resulting `255..=2` range; Miri aborts `transmute::<u8, Option<Option<bool>>>(3)` with Undefined Behavior (`at .<enum-tag>, encountered 0x03`).
- **`Option<Option<Option<bool>>>` -> `[0, 1, 2, 255, 254]` (`1` byte, `0x03` is UB):** At depth 3, `next_down = |-2_i8| = 2 <= next_up = 3`, extending downward again to `254` (`0xfe`). By contrast, a 3-variant single-level enum `enum BoolPlusTwo { Payload(bool), X, Y }` requests `count = 2` in a single reservation, bypasses the `count == 1` zero-ward branch, and produces contiguous `[0, 1, 2, 3]`.
- **`Option<Option<Option<char>>>` -> `[0x41, 0xffffffff, 0xfffffffe, 0xfffffffd]` (`4` bytes):** `rustc_ty_utils/src/layout.rs` summarizes `char` with a single convex `WrappingRange` of `0..=0x10ffff`. Wrapping below zero yields outer `None` tags `0xffffffff`, `0xfffffffe`, `0xfffffffd`. Crucially, UTF-16 surrogates (`0xD800..=0xDFFF`) remain inside the `WrappingRange`, producing a two-stage validity split observed under Miri: `0x00110000` fails at `.enum-tag`, whereas `0x0000D800` passes tag validation and fails deep payload validity at `.enum-variant(Some).0`.
- **Niche Capacity Exhaustion (`available = 0`) Spills to `TagEncoding::Direct`:** `NonNull<u8>` (`valid_range = 1..=u64::MAX`, `available = 1`) and `NonZero<u8>` (`valid_range = 1..=255`, `available = 1`) exhaust their sole niche (`0`) at depth 1. Depth 2 (`Option<Option<NonNull<u8>>>` and `Option<Option<NonZero<u8>>>`) receives `None` from `Niche::reserve` and spills to `TagEncoding::Direct` with explicit discriminant tags `[tag=1, tag=1, tag=0]` (`16 bytes, align 8` and `2 bytes, align 1`, respectively).
- **Explicit `#[repr(...)]` Layout & `E0732` Divergence:** `inhibit_enum_layout_opt()` suppresses niche optimization for `#[repr(C)]`, `#[repr(u8)]`, and `#[repr(C, u8)]`. On `x86_64-unknown-linux-gnu`, `#[repr(C)]` promotes discriminant size to `4` bytes (`size = 8, align = 4`, payload offset `4`), whereas `#[repr(C, u8)]` sets `prefix_align = max(tag_align, max_field_align)` (`2` when variants contain `(u16)` and `(u8)`), forcing 1 padding byte before `B(u8)` (offset `2`). Plain `#[repr(u8)]` keeps `prefix_align = 1`, placing `B(u8)` directly at offset `1` while padding `A(u16)` to offset `2` (`offset_of!` & Miri `(1, 2)`). Any explicit discriminant on a `#[repr(Rust)]` or `#[repr(C)]` enum with non-unit variants triggers compile-time error `E0732`.
- **`google/zerocopy` (`TryFromBytes`) Tag-First Validation:** Across `6f262351a9b652425d13867717966668f3dd7cb0`, `907b9175fee081872ec883ca4709e6ad922f8ed0`, and `e86eb0281380bdc278f4b4b3788dc9525ef59035`, `zerocopy-derive/src/derive/try_from_bytes.rs` (byte-identical SHA-256 `c5ef4996afd692800ba99a5d544ac554f5b80282b0aa532eceb55b4febce038a`) rejects `#[repr(Rust)]` and `#[repr(C, u8)]` enums (`this conflicts with another representation hint`) and accepts `#[repr(C)]` and `#[repr(Int)]` enums. Derived `TryFromBytes::is_bit_valid` reads `___ZerocopyTagPrimitive` via `.cast(...).recall_validity().read()`, dispatches on valid discriminants first, rejects unknown tags immediately, and only projects/validates variant fields inside `___ZerocopyVariantStruct` / `___ZerocopyRawEnum` for the matched variant.
- **Verification Status & Gap in `joshlf/anneal`:** Live `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) evaluates pre-computed `WrappingRange` and `TagEncoding::Niche` discriminants in `vendor/lean-miri`, while `trusted/lean/Trusted/MirAst.lean` models only fieldless `TagEncoding.Direct` enums. To mechanize the missing layer independently, this report supplies a standalone `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked formalization (`support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean`, `2,045` LOC, `134` theorems, `0` `sorry`, `0` `._unsafe_rec`, axioms `⊆ {propext, Quot.sound}`) proving `NicheChain` injectivity/disjointness, `[0, 1, 2, 255, 254]` / `0x03`-invalidity, capacity exhaustion spilling, `[u8]` vs `[C, u8]` vs `[C]` offsets/`E0732`, and tag-first `TryFromBytes` decoder soundness.

## Applicability

This report documents primary-source compiler rules, runtime/Miri measurements, `zerocopy` derive expansion semantics, and standalone Lean 4 mechanization across four repository ecosystems at eight pinned immutable commits observed on `2026-11-23`:

| Component / Repository | Pinned Commit / Version | Scope of Examination | Role in This Report |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`) | `rustc_abi`, `rustc_ty_utils`, `rustc_middle`, `rustc_const_eval`, `rustc_hir_analysis`, `core::ptr::NonNull`, plus live `rustc` & `cargo miri` execution on `x86_64-unknown-linux-gnu` | Primary source + live compiler/Miri execution (`support/probe_niche_stacking_and_try_from_bytes.py`) |
| `rust-lang/rust` | `49d734536222bf28bb6d07d885b3a81d145981da` | `compiler/rustc_abi/src/lib.rs`, `compiler/rustc_ty_utils/src/layout.rs` | Primary source comparison (inlined `!is_bool` form prior to `Primitive::Bool`) |
| `rust-lang/rust` | `20fe935d50367c0ff8872c2ebfa050c5c99d9201` (`main` on `2026-11-23`) | `compiler/rustc_abi/src/lib.rs`, `compiler/rustc_ty_utils/src/layout.rs` | Primary source comparison (introduces `Primitive::Bool` + conditional widening to `I8`, preserving `v != 0..=1` guard) |
| `google/zerocopy` | `6f262351a9b652425d13867717966668f3dd7cb0` | `zerocopy-derive/src/derive/try_from_bytes.rs`, `zerocopy-derive/src/repr.rs`, `zerocopy/src/lib.rs`, `zerocopy/src/impls.rs` | Primary source baseline |
| `google/zerocopy` | `907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`) | Full crate compiled offline natively and under Miri | Primary source + live native & Miri execution (`zerocopy::TryFromBytes`) |
| `google/zerocopy` | `e86eb0281380bdc278f4b4b3788dc9525ef59035` (`main` on `2026-11-23`) | `zerocopy-derive/src/derive/try_from_bytes.rs`, `zerocopy/src/lib.rs`, `zerocopy/src/impls.rs` | Primary source currency verification (`try_from_bytes.rs` SHA-256 identical across all 3 pins) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`main` on `2026-11-23`) | `vendor/lean-miri/Miri/{ABI/WrappingRange.lean, Interpreter/Discriminant.lean}`, `trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}`, `trusted/correspondence/Trusted/Correspondence.lean` | Audit of existing verification representation & gap characterization |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | `support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean` (`Init` stdlib only) | Kernel-checked standalone formalization (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) |

### Shared vs. Version-Specific Behavior Across Revisions

1. **Cross-Revision Invariance of `rustc` Greedy Niche Stacking (`14210df0e` vs. `49d734536` vs. `20fe935d5`):**
   - **Shared:** `WrappingRange::contains`, `WrappingRange::is_full_for`, `Niche::available`, zero-ward `next_down <= next_up` heuristic on `count == 1`, explicit exclusion of initial `bool` range `0..=1`, `char` `WrappingRange { start: 0, end: 0x10FFFF }`, `NonNull` / `NonZero<u8>` capacity exhaustion spill, `#[repr(C)]` `c_enum_min_size = 4` on `x86_64-unknown-linux-gnu`, `#[repr(C, u8)]` `prefix_align` rule vs. `#[repr(u8)]` `prefix_align = tag_align`, and `E0732` diagnostics.
   - **Differs by revision:**
     - `14210df0e` binds `let is_bool = size.bytes() == 1 && v == WrappingRange { start: 0, end: 1 };` (`compiler/rustc_abi/src/lib.rs:2024`) with an inline `FIXME` comment noting that allowing zero-ward wrapping for initial `bool` hit a miscompilation, so `!is_bool` prevents wrapping `Option<bool>` to `255`. `rustc_ty_utils/src/layout.rs:384-390` still represents `bool` as `Primitive::Int(Integer::I8, false)`.
     - `49d734536` keeps `bool` as `Primitive::Int(I8, false)` and inlines the condition directly into `if count == 1 && v != (WrappingRange { start: 0, end: 1 })` (no `size.bytes() == 1` check needed since callers reserve scalar niches matched to field size).
     - `20fe935d5` introduces `Primitive::Bool` at `rustc_ty_utils/src/layout.rs:411-417`. Inside `Niche::reserve`, `move_start` and `move_end` inspect `&mut Scalar` and promote `Primitive::Bool` to `Primitive::Int(Integer::I8, false)` whenever `scalar.valid_range().end.wrapping_sub(scalar.valid_range().start) >= 2`. Because `if count == 1 && v != (WrappingRange { start: 0, end: 1 })` remains verbatim in `20fe935d5`, `Option^k(bool)` produces identical discriminants `[0, 1, 2, 255, 254]` across all three commits.

2. **Target Architecture Qualification (`x86_64-unknown-linux-gnu`, LP64, Little-Endian):**
   - Pointer width (`64` bits) governs `NonNull<u8>` (`8` bytes -> `16` bytes at `Option<Option<NonNull<u8>>>`), and `TargetDataLayout.c_enum_min_size` (`I32`, `4` bytes) governs `#[repr(C)]` direct discriminants on `x86_64-unknown-linux-gnu`. Targets where C enums can be narrower (such as `-Z repr-c-short-enum` / C ABI configurations with smaller `c_enum_min_size`) are excluded by target scope; see Boundaries.
   - Byte-order decoding and unaligned reference checks (`char::try_ref_from_bytes` requiring 4-byte pointer alignment) were empirically verified on `x86_64-unknown-linux-gnu` little-endian buffers (`#[repr(align(4))]`).

3. **Standalone Status of Lean 4 Mechanization:**
   - The Lean 4 proof artifact (`support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean`) is an executable, kernel-checked **standalone** model written strictly on Lean `v4.34.1` `Init`. It does **not** import or refine `joshlf/anneal`'s `Trusted.MirSemantics` or `vendor/lean-miri` Miri AST; rather, it formalizes the primary-source algorithms extracted from `rust-lang/rust` and `google/zerocopy` directly, serving as a verified blueprint for extending `joshlf/anneal`.

---

## Findings

### 1. `WrappingRange` Algebra and Exact Greedy Zero-Ward `Niche::reserve` Stacking

Basis: `source` + `derived` + `execution` + `normative`.

#### 1.1 `WrappingRange` and Niche Capacity

In `compiler/rustc_abi/src/lib.rs` (`14210df0e` lines `195-240`, `1430-1560`), valid bit patterns of scalar primitives are represented modulo $2^w$ ($w = 8 \cdot \text{size\_bytes}$) as an inclusive interval `WrappingRange { start: u128, end: u128 }`:

- **Non-wrapping (`start <= end`):** valid bit patterns are $\{ x \in [0, 2^w) \mid \text{start} \le x \le \text{end} \}$.
- **Wrapping (`end < start`):** valid bit patterns wrap through $2^w - 1 \to 0$: $\{ x \in [0, 2^w) \mid \text{start} \le x \lor x \le \text{end} \}$.

From primary-source inspection and mechanized proof (`WrappingRange.contains_iff_shift` in Lean), shifting both `x` and `end` modulo $2^w$ by `-start` maps both wrapping and non-wrapping cases uniformly onto a linear prefix $[0, (\text{end} - \text{start}) \bmod 2^w]$:

$$x \in \text{WrappingRange}(\text{start}, \text{end}) \iff (x - \text{start}) \bmod 2^w \le (\text{end} - \text{start}) \bmod 2^w$$

Using `max_value = size.unsigned_int_max()` ($= 2^w - 1$), `compiler/rustc_abi/src/lib.rs` (`14210df0e:2005-2025`) defines remaining niche capacity as:

```rust
let available = v.start.wrapping_sub(v.end).wrapping_sub(1) & max_value;
```

Algebraically, modulo $2^w$, `available` equals the exact complement of the normalized valid range length:

$$\text{available} = (2^w - 1) - \bigl((\text{end} - \text{start}) \bmod 2^w\bigr)$$

Therefore, `available == 0` holds if and only if $(\text{end} - \text{start}) \bmod 2^w = 2^w - 1$, i.e., `WrappingRange::is_full_for(size)` (`start == (end + 1) mod 2^w`), as kernel-proved in `WrappingRange.available_zero_iff_isFull`.

#### 1.2 Exact 4-Branch Heuristic in `Niche::reserve`

When laying out an enum with `count` niche-tagged variants around a payload scalar whose current range is `v = WrappingRange { start, end }` (starting at `rustc_abi/src/lib.rs:2020-2096` at `14210df0e`; corresponding regions at `49d734536:2130-2175` and `20fe935d5:2169-2240`), `Niche::reserve(&self, scalar: &mut Scalar, count: u128) -> Option<u128>` returns `None` immediately if `count == 0` or `count > available`. Otherwise, it computes:

```rust
let max_value = size.unsigned_int_max();
let distance_end_zero = max_value - v.end;
// On 14210df0e:
let is_bool = size.bytes() == 1 && v == WrappingRange { start: 0, end: 1 };
// On 49d734536 and 20fe935d5: inlined `v != WrappingRange { start: 0, end: 1 }`
```

And executes four mutually exclusive branches using helpers `move_start(count)` (allocates `niche_start = v.start.wrapping_sub(count) & max_value`, updates `v.start = niche_start`) and `move_end(count)` (allocates `niche_start = v.end.wrapping_add(1) & max_value`, updates `v.end = v.end.wrapping_add(count) & max_value`):

1. **Branch 1 (`count == 1 && !is_bool`) — Zero-Ward Signed Tie-Breaker:**
   Computes signed magnitudes toward zero for both candidates:
   - `next_up = size.sign_extend(v.end.wrapping_add(1) & max_value).cast_signed().unsigned_abs()`
   - `next_down = size.sign_extend(v.start.wrapping_sub(1) & max_value).cast_signed().unsigned_abs()`
   If `next_down <= next_up`, it picks `move_start`; otherwise it picks `move_end`. Crucially, because `v.start = 0` gives `(0 - 1) mod 2^w = 2^w - 1 = -1` signed, `next_down = 1` dominates any `v.end >= 0` (`next_up >= 1` holds on ties via `<=`), driving single-niche `Option` tags negatively from `-1` downward (`255, 254, ...` for 8-bit, `0xffffffff, 0xfffffffe, ...` for 32-bit)!
2. **Branch 2 (`v.start > v.end`) — Already-Wrapped Multi-Niche Fallback (`count >= 2` or unreachable `count == 1`):**
   If the range already wraps across zero (`end < start`), only contiguous extension upward from `v.end` (`move_end`) avoids crossing zero into `v.start`.
3. **Branch 3 (`v.start <= distance_end_zero`) — Closer-to-Zero Heuristic:**
   If `v.start` is closer to `0` than `v.end` is to `2^w - 1`, `Niche::reserve` prefers extending downward (`move_start`) *only* if `count <= v.start` (i.e., enough room exists below `v.start` without wrapping past `0`); otherwise it calls `move_end`.
   - **Why `Option<bool>` yields `[0, 1, 2]`:** `bool` has `v = 0..=1`, `is_bool == true`, `count = 1`. Branch 1 is skipped! Branch 2 is false (`0 <= 1`). Branch 3 holds (`0 <= 254`), but `count <= v.start` (`1 <= 0`) is **false**, forcing `move_end` -> `niche_start = 2`, new `v = 0..=2`.
   - **Why `BoolPlusTwo { Payload(bool), X, Y }` yields `[0, 1, 2, 3]`:** `count = 2 != 1`, skipping Branch 1 regardless of `is_bool`. Branch 3 sees `2 <= 0` is false and picks `move_end` -> `niche_start = 2`, occupying `[2, 3]`, leaving `v = 0..=3`.
4. **Branch 4 (Symmetric `distance_end_zero < v.start`) — Upper-Room Check:**
   Checks whether adding `count` to `v.end` wraps into `[1..=v.end]`; if so, falls back to `move_start`, else `move_end`.

On `20fe935d5`, `rustc_ty_utils/src/layout.rs:411-417` lowers `ty::Bool` using `Primitive::Bool` (whereas `14210df0e:384-390` lowered `ty::Bool` as `Primitive::Int(Integer::I8, false)`). Consequently, `20fe935d5`'s `move_start` / `move_end` checks:

```rust
if let Primitive::Bool = value
    && valid_range.end.wrapping_sub(valid_range.start) >= 2
{
    value = Primitive::Int(Integer::I8, false);
}
```

Wait-free widening happens after `v` reaches `[0, 1, 2]` at depth 1 (`end - start == 2 >= 2`), turning `Option<bool>`'s tag scalar into `Int(I8, false)` while leaving the `v != 0..=1` skip intact.

#### 1.3 Worked Trace and Empirical Bit Patterns (`rustc 1.98.0-nightly 14210df0e`)

Table 1 summarizes the exact reservation trace confirmed both algebraically and by executing compiled binaries (`support/probe_results.json`, `parsed_execution_values` and `print_type_sizes`):

| Type | Inner Range | Branch Triggered | Assigned Outer Tag | Output `valid_range` | Observed Size / Align | Observed Payload Bit Patterns |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `Option<bool>` | `0..=1` (`bool`) | Branch 1 skipped (`is_bool`); Branch 3 (`1 <= 0` false) -> `move_end` | `2` (`0x02`) | `0..=2` | `1 B / 1 B` | `[0, 1, 2]` (`Some(false), Some(true), None`) |
| `Option<Option<bool>>` | `0..=2` | Branch 1 (`!is_bool`); `next_down = 1 <= next_up = 3` -> `move_start` | `255` (`0xff`) | `255..=2` | `1 B / 1 B` | `[0, 1, 2, 255]` (`0x03` invalid!) |
| `Option<Option<Option<bool>>>` | `255..=2` | Branch 1; `next_down = |-2_i8| = 2 <= next_up = 3` -> `move_start` | `254` (`0xfe`) | `254..=2` | `1 B / 1 B` | `[0, 1, 2, 255, 254]` (`0x03` invalid!) |
| `BoolPlusTwo { Payload(bool), X, Y }` | `0..=1` (`count = 2`) | Branch 1 skipped (`count != 1`); Branch 3 (`2 <= 0` false) -> `move_end` | `2, 3` (`0x02, 0x03`) | `0..=3` | `1 B / 1 B` | `[0, 1, 2, 3]` |

**Miri Enforcement on the `0x03` Hole (`b_miri_enum_validity`):** Running `cargo miri run --offline` on `transmute::<u8, Option<Option<bool>>>` succeeds for `[0, 1, 2, 255]` (`returncode: 0`, stdout `MIRI_NICHE_VALID=[Some(Some(false)), Some(Some(true)), Some(None), None]`), and aborts with `returncode: 1` for `transmute(3u8)` on **both** `Option<Option<bool>>` and `Option<Option<Option<bool>>>`:

```text
error: Undefined Behavior: constructing invalid value of type std::option::Option<std::option::Option<bool>>: at .<enum-tag>, encountered 0x03, but expected a valid enum tag
```

This confirms empirically why any FFI consumer or custom `TryFromBytes` checker assuming sequential `[0, 1, 2, 3]` discriminants for `Option<Option<bool>>` induces immediate Undefined Behavior on `0x03` while rejecting legitimate outer `None` `0xff`.

---

### 2. Multi-Level `char` Niche Stacking vs. Deep Unicode Surrogate Validity

Basis: `source` + `derived` + `execution` + `normative`.

In `compiler/rustc_ty_utils/src/layout.rs:391-397` (`14210df0e`; matching logic in `49d734536` and `20fe935d5`), `ty::Char` maps to:

```rust
Primitive::Int(I32, false) // valid_range = WrappingRange { start: 0, end: 0x10FFFF }
```

Because `WrappingRange` tracks only a single contiguous interval `[start, end]` modulo $2^{32}$, the UTF-16 surrogate hole `0xD800..=0xDFFF` is **not excluded** from `valid_range`. Only values `0x00110000..=0xFFFFFFFF` (`4,293,853,184` values) count toward `available`.

When nesting `Option<char>` three levels deep (`count = 1` at each level):
- Level 1 (`Option<char>`): `next_down = |(0 - 1)_i32| = 1 <= next_up = 0x00110000 = 1,114,112` -> `move_start`, outer `None = 0xffffffff`, new `valid_range = 0xffffffff..=0x10ffff`.
- Level 2 (`Option<Option<char>>`): `next_down = |-2_i32| = 2 <= 1,114,112` -> `move_start`, outer `None = 0xfffffffe`, new `valid_range = 0xfffffffe..=0x10ffff`.
- Level 3 (`Option<Option<Option<char>>>`): `next_down = |-3_i32| = 3 <= 1,114,112` -> `move_start`, outer `None = 0xfffffffd`, new `valid_range = 0xfffffffd..=0x10ffff`.

**Live Probe & Miri Validation Results:**
- Native execution + `-Zprint-type-sizes` confirms `size = 4 bytes, alignment = 4 bytes` across `Option<char>`, `Option<Option<char>>`, and `Option<Option<Option<char>>>`, with bit patterns `opt3_char_hex = ["0x41", "0xffffffff", "0xfffffffe", "0xfffffffd"]`.
- **Two-Stage Validity Gap Caught by Miri:** Under `cargo miri run --offline`, `compiler/rustc_const_eval/src/interpret/validity.rs` evaluates the `WrappingRange` enum tag *before* checking inner variant primitive validity:
  - `transmute::<u32, Option<char>>(0x110000)` fails at tag decoding: `at .<enum-tag>, encountered 0x00110000, but expected a valid enum tag`.
  - `transmute::<u32, Option<char>>(0xD800)` **passes `.enum-tag`** (since `0xD800` lies inside `0xffffffff..=0x10ffff`) and fails during deep variant payload checking: `at .<enum-variant(Some)>.0, encountered 0x0000d800, but expected a valid unicode scalar value (in 0..=0x10FFFF but not in 0xD800..=0xDFFF)`.

Sound unsafe decoders (including `zerocopy::TryFromBytes` on `char` in `zerocopy/src/impls.rs:141-147`) therefore cannot stop at `WrappingRange` containment; after confirming a non-niche `Some` variant, they must also check `char::from_u32(c).is_some()` (i.e., `c <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&c)`).

---

### 3. Capacity Exhaustion Spill to `TagEncoding::Direct`

Basis: `source` + `execution` + `derived`.

Both `core::ptr::NonNull<u8>` (`library/core/src/ptr/non_null.rs:71-76`, backed by `rustc_layout_scalar_valid_range_start(1)` / `pattern_type!` -> `valid_range = 1..=u64::MAX`, `available = 1`) and `core::num::NonZero<u8>` (`valid_range = 1..=255`, `available = 1`) possess exactly **one** invalid bit pattern (`0`).

- **Level 1 (`Option<NonNull<u8>>` / `Option<NonZero<u8>>`):** Consumes `0` via `move_start`, updating `valid_range` to `0..=2^w-1`, where `start == end.wrapping_add(1)` (`is_full_for = true`, `available = 0`). Both remain `8` bytes and `1` byte respectively (`nonnull_none = 0`, `nonzero_u8_none = 0`).
- **Level 2 (`Option<Option<NonNull<u8>>>` / `Option<Option<NonZero<u8>>>`):** `Niche::reserve` checks `count > available` (`1 > 0`) and returns `None`. `calculate_niche_filling_layout` fails over to `calculate_direct_layout` (`TagEncoding::Direct`), allocating an explicit tag field padded/aligned to the payload:
  - `Option<Option<NonNull<u8>>>`: `16 bytes, alignment: 8 bytes`, `-Zprint-type-sizes` reports `discriminant: 8 bytes`, `variant Some: 8 bytes`, `variant None: 0 bytes`. Probed leading tag words across `[Some(Some(nn)), Some(None), None]` yield `[1, 1, 0]` (`TagEncoding::Direct`: `Some` has discriminant `1`, `None` has `0`, distinguishing outer `Some(None)` whose inner payload bytes are `0` from outer `None` via the external discriminant byte `1` vs `0`).
  - `Option<Option<NonZero<u8>>>`: `2 bytes, alignment: 1 byte`, `-Zprint-type-sizes` reports `discriminant: 1 bytes`, `variant Some: 1 bytes`, `variant None: 0 bytes`, and probed leading tag bytes yield `[1, 1, 0]`.

---

### 4. `#[repr(u8)]` vs. `#[repr(C, u8)]` vs. `#[repr(C)]` Layouts and `E0732` Rules

Basis: `normative` + `source` + `execution` + `derived`.

#### 4.1 Compiler `inhibit_enum_layout_opt`, `discr_range_of_repr`, and `prefix_align`

Three independent mechanisms in `rustc` (`14210df0e`, matching `49d734536`/`20fe935d5`) govern explicit-`#[repr]` field-carrying enums:

1. **Niche Optimization Suppression (`rustc_middle/src/ty/layout.rs:77-120`):**
   `inhibit_enum_layout_opt()` disables niche filling whenever `repr.c()` or `repr.int.is_some()`. Hence `#[repr(C)]`, `#[repr(u8)]`, and `#[repr(C, u8)]` all use `TagEncoding::Direct` (explicit tag primitive at offset `0` via `Variants::Multiple { tag_encoding: Direct, ... }`).
2. **Minimum Discriminant Size (`rustc_middle/src/ty/layout.rs` -> `discr_range_of_repr`):**
   When `repr.int.is_none()` and `repr.c()` is set (plain `#[repr(C)]`), `rustc` initializes the discriminant integer range with `at_least = dl.c_enum_min_size`, which is `Integer::I32` (`4` bytes) on `x86_64-unknown-linux-gnu`. Even a 2-variant fieldless `#[repr(C)] enum CLikeC { X = 1, Y = 2 }` occupies `4 bytes, align 4`, whereas `#[repr(u8)] enum CLikeU8 { X = 1, Y = 2 }` occupies `1 byte, align 1`.
3. **Critical `#[repr(u8)]` vs. `#[repr(C, u8)]` Field-Offset Divergence (`compiler/rustc_abi/src/layout.rs:822-829, 1257-1307`):**
   When laying out variants with `StructKind::Prefixed(prefix_size, prefix_align)`:
   - For `#[repr(C, u8)]` (`repr.c() == true` and `repr.int.is_some()`), `enum` layout computes `prefix_align = max(tag_align, max_align_across_all_variants_and_fields)`. The unified `prefix_align` forces `offset = prefix_size.align_to(prefix_align)` **before** placing ANY field of ANY variant. For `ReprCU8Data { A(u16) = 5, B(u8) = 9 }`, `prefix_align = max(1, 2, 1) = 2`, so variant `B(u8)` begins at `1.align_to(2) = 2` (1 internal padding byte after the `u8` tag!).
   - For plain `#[repr(u8)]` (`repr.c() == false`), `prefix_align` equals `tag_align` (`1`). `StructKind::Prefixed(1, 1)` starts each variant independently at offset `1`: variant `A(u16)` aligns `.0` up to offset `2` (`padding: 1 byte` in `variant A`), whereas variant `B(u8)` packs `.0` immediately at **offset `1`** (`0` padding inside `variant B`).
   - Note subtle `offset_of!` vs. ABI size detail: even though both `ReprU8Data` and `ReprCU8Data` have total size `4 bytes` and alignment `2 bytes`, reading byte `1` of a `B(u8)` buffer reads payload `.0` for `ReprU8Data`, whereas byte `1` is uninitialized padding in `ReprCU8Data`!

Live `-Zprint-type-sizes`, `core::mem::offset_of!`, and Miri confirm exact byte offsets (`support/probe_results.json`):

| Type & Repr | Variants | Discriminant Size | Total Size / Align | `A.0` Byte Offset | `B.0` Byte Offset | Variant `B` Tag | Notes |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `ReprU8Data` (`#[repr(u8)]`) | `A(u16) = 5, B(u8) = 9` | `1 B` | `4 B / 2 B` | `2` | **`1`** | `9` | Zero padding before `B.0`; `Miri` prints `MIRI_OFFSETS=(1, 2)` |
| `ReprCU8Data` (`#[repr(C, u8)]`) | `A(u16) = 5, B(u8) = 9` | `1 B` | `4 B / 2 B` | `2` | **`2`** | `9` | `1 B` padding after tag in `variant B`; rejected by `zerocopy-derive` |
| `ReprCData` (`#[repr(C)]`) | `A(u16), B(u8)` | `4 B` | `8 B / 4 B` | `4` | `4` | `1` | `c_enum_min_size = 4B`; `2 B` end padding |
| `CLikeC` (`#[repr(C)]`) | `X = 1, Y = 2` | `4 B` | `4 B / 4 B` | `—` | `—` | `—` | Fieldless C enum |
| `CLikeU8` (`#[repr(u8)]`) | `X = 1, Y = 2` | `1 B` | `1 B / 1 B` | `—` | `—` | `—` | Compact fieldless enum |

Under Miri, initializing a 4-byte buffer `[7, 0, 0, 0]` and transmuting to `ReprU8Data` catches UB at the discriminant check before accessing any payload byte (`at .<enum-tag>, encountered 0x07, but expected a valid enum tag`).

#### 4.2 Exact `E0732` Explicit Discriminant Gate

In `compiler/rustc_hir_analysis/src/check/check.rs:1888-1925`, explicit discriminant expressions `= expr` require an integer `#[repr(u8/i8/...)]` (whether `#[repr(u8)]` or `#[repr(C, u8)]`) whenever:

```rust
repr.int.is_none() && (disr_non_unit.is_some() || (disr_unit.is_some() && non_unit.is_some()))
```

Notice the second disjunct: placing an explicit discriminant **even on a unit variant** inside an enum that has *any* non-unit payload variant violates `E0732` unless an explicit integer repr (`u8`, `i32`, etc.) is present (`#[repr(C)]` alone does NOT satisfy `repr.int.is_some()`!). Both failure modes (`e0732_non_unit_explicit_discr` and `e0732_unit_explicit_discr_with_non_unit_variant`) are verified empirically (`rustc` `returncode: 1`, `error[E0732]: #[repr(inttype)] must be specified for enums with explicit discriminants and non-unit variants`).

---

### 5. `google/zerocopy::TryFromBytes` Tag-First Semantics and Representation Rules

Basis: `source` + `execution` + `normative` + `derived`.

#### 5.1 Repr Gatekeeping in `zerocopy-derive`

Auditing `zerocopy/zerocopy-derive/src/{repr.rs, derive/try_from_bytes.rs, derive/project.rs}` across `6f262351a9b652425d13867717966668f3dd7cb0`, `907b9175fee081872ec883ca4709e6ad922f8ed0`, and `e86eb0281380bdc278f4b4b3788dc9525ef59035` (`try_from_bytes.rs` SHA-256 `c5ef4996afd692800ba99a5d544ac554f5b80282b0aa532eceb55b4febce038a` across all three pins) establishes:

1. **Rejected Representation Hints (`repr.rs:450, 487`):** `zerocopy-derive` rejects `#[repr(C, u8)]` and any combined `#[repr(C, Int)]` on enums, emitting `error: this conflicts with another representation hint` (`reject_repr_c_u8`, `cargo check` exit `101`). Default `#[repr(Rust)]` enums are likewise rejected by `#[derive(TryFromBytes)]` because Rust offers no stable ABI guarantee for `#[repr(Rust)]` discriminants.
2. **Accepted Enum Representations (`derive_try_from_bytes_enum`, `try_from_bytes.rs:315-346`):**
   - **Shortcut `FromBytes`-like fieldless path (`could_be_from_bytes`):** If an enum is fieldless (`all_variants_unit`), has `#[repr(u8|i8|u16|i16)]`, and defines $2^N$ variants (`8`/`16` bits exhausted), every bit pattern of the underlying tag integer is a valid variant discriminant (`is_bit_valid` returns `true` after size/alignment checks).
   - **General Tag-First `derive_is_safe` path (`try_from_bytes.rs:121-227`):** For any `#[repr(C)]` or `#[repr(u8|i8|...)]` enum not taking the exhaustive shortcut, `derive_is_safe` synthesizes a tag primitive `___ZerocopyTagPrimitive` and generates tag constants per variant discriminant.

#### 5.2 Tag-First Short-Circuiting Projection and Alignment Preconditions

Inside `zerocopy::TryFromBytes` (`zerocopy/src/lib.rs:1967-2000` trait definition and `is_safe`; `2100-2119` `try_ref_from_bytes`):

1. **Prefix Size & Pointer Alignment Guard First:** `try_ref_from_bytes(source: &[u8])` first validates slice length and pointer alignment before calling `unsafe fn is_bit_valid(candidate: Maybe<'_, Self>) -> bool`. Empirically, passing an unaligned 4-byte slice (`&0x41u32.to_le_bytes()` at alignment `1`) returns `Err` on native `x86_64-unknown-linux-gnu` while `&Aligned4(0x41u32.to_le_bytes()).0` succeeds (`Some('A')`).
2. **Tag-First Load & Recall Validity:** Inside derived `is_bit_valid` (`try_from_bytes.rs:121-227`):
   - **For `#[repr(C)]`:** Synthesizes `#[repr(C)] struct ___ZerocopyRawEnum { tag: ___ZerocopyTag, variants: ___ZerocopyVariants }`, projects to `.tag`, invokes `.cast::<___ZerocopyTagPrimitive>().recall_validity().read()`, and switches inside `match tag { ... }`. Notice `.recall_validity()` is sound specifically because every bit pattern of `___ZerocopyTagPrimitive` (`i8/u8/i16/u16/i32/u32/...`) is valid `FromBytes`. Unknown tags immediately hit `_ => false` **without projecting or reading any payload bytes**.
   - **For `#[repr(Int)]` (e.g., `#[repr(u8)]`):** Because each variant starts independently at offset `tag_size` with its own field alignment (Section 4.1), the derive generates a per-variant `#[repr(C)] struct ___ZerocopyVariantStruct(MaybeUninit<___ZerocopyInnerTag>, ...)` (`project.rs:260-376`), guaranteeing field `0` aligns with `#[repr(u8)]`'s offset rule (`offset 1` for `u8`/`bool` in `PacketU8::B(u8)` / `PacketU8::C(bool)` and `offset 2` for `u16` in `PacketU8::A(u16)`!).
   - **Per-Variant Field Validation (`derive_variant_is_safe:33-71`):** Only inside the matched discriminant arm does `is_bit_valid` validate each payload field via `<FieldTy as TryFromBytes>::is_bit_valid(...)`.
3. **Standard Library Primitive & Special Niche `impl`s (`zerocopy/src/impls.rs:113-295`):**
   - `bool` (`impls.rs:113-116`): checks `*byte < 2` (`Some(false)`, `Some(true)`, rejects `2` and `255`).
   - `char` (`impls.rs:141-147`): calls `char::from_u32(c).is_some()`, rejecting both out-of-range `0xFFFFFFFF` and surrogates `0xD800` (closing the `WrappingRange` gap of Section 2).
   - `Option<NonZero<T>>` (`impls.rs:182-295`): hand-implemented `TryFromBytes` (specifically `0 -> Ok(None)`, `n != 0 -> Ok(Some(n))`), validated in probe on `Option<NonZeroU8>` (`[0] -> Some(None)`, `[7] -> Some(7)`).

All assertions in `ZEROCOPY_PROBE_MAIN` compiled and passed identically both natively (`returncode: 0`) and under `cargo miri run --offline` (`returncode: 0`):
`ZC_RESULTS bool=(Some(false),Some(true),true,true) char=(Some('A'),true,true) onz=(Some(None),Some(7)) pkt_u8=(true,true,true,true,true) pkt_c=(true,true,true)`.

---

### 6. Alignment Gap Audit Against `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

Basis: `source` + `derived`.

Comparing `rustc_abi` / `zerocopy` semantics against live `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` identifies two precise verification boundaries:

1. **`vendor/lean-miri` (`Miri/ABI/WrappingRange.lean:1-150`, `Miri/Interpreter/Discriminant.lean:1-170`):**
   - Models `WrappingRange` bitvector membership and evaluates both `TagEncoding.Direct` and `TagEncoding.Niche` *assuming a pre-computed `Variants.Multiple` layout descriptor* has already been provided.
   - Does **not** compute `Niche::reserve` (`rustc_abi/src/lib.rs:2020-2096`) or verify multi-level `Option` stacking injectivity/disjointness.
2. **`trusted/lean/Trusted/` (`MirAst.lean:222-271`, `MirSemantics.lean:453-547`, `Correspondence.lean:835-847`):**
   - Models only **fieldless** enumerations via `EnumTagRepr` (`.zeroSized` or `.scalar width signed`) and `TagEncoding.Direct` scalar discriminant reads/writes.
   - Field-carrying `#[repr(u8)]` / `#[repr(C)]` variant projections, `StructKind::Prefixed` offset rules, `TagEncoding.Niche`, and stacked `Option^k` validity predicates lie outside Anneal's current `Trusted.MirAst` and `Trusted.MirSemantics`.

---

### 7. Kernel-Checked `Lean v4.34.1` Formalization

Basis: `source` + `execution` + `derived`.

`support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean` (`2,045` LOC, `91,142` bytes, `299` `noncomputable def`s, `134` local theorems) mechanizes the full pipeline cleanly on `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) with `Init` only.

#### 7.1 Purity & Trusted Kernel Hygiene Receipts

Checked strictly under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`) and audited over all `607` local environment constants via `Lean.collectAxioms`:
- `sorry` tokens: **`0`**
- Forbidden tactics (`omega`, `bv_decide`, `native_decide`): **`0`**
- `partial def`, `let rec`, `noncomputable section`, `deriving`: **`0`**
- Generated `._unsafe_rec` constants (`(env.getModuleIdxFor? n).isNone`): **`0`**
- Disallowed axioms (`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`): **`0`** (every theorem relies solely on `{propext, Quot.sound}` or zero axioms `[]`).

#### 7.2 Core Mechanized Theorems & Verified Witnesses

| Theorem / Witness (`AbiNicheStacking.*`) | Formal Statement Summary | Axiom Footprint | Role |
| :--- | :--- | :--- | :--- |
| `WrappingRange.contains_iff_shift` | Modular containment `r.contains x = true ↔ (x - r.start).toNat ≤ (r.finish - r.start).toNat` | `[propext]` | Unified linear-prefix coordinate transform |
| `WrappingRange.available_zero_iff_isFull` | `r.available = 0 ↔ r.isFull = true` | `[propext, Quot.sound]` | Links `wrapping_sub` complement to full-range exhaustion |
| `moveStart_sound` & `moveEnd_sound` | `ReservePost r count nicheStart r'` (exact containment union, base exclusion, intra-step tag injectivity, capacity conservation `r'.available = r.available - count`) | `[propext, Quot.sound]` / `[propext]` | Exact contracts for both extension directions |
| `nicheReserve_sound` & `nicheReserve_none_iff` | Universal 4-branch soundness of `nicheReserve`, plus `nicheReserve = none ↔ count = 0 ∨ r.available < count` | `[propext, Quot.sound]` / `[propext]` | Covers `isBool`, zero-ward `next_down <= next_up`, wrap, and exhaustion |
| **`NicheChain.tags_sound`** (Theorem 1) | Across any inductive `NicheChain`, all reserved `(level, slot)` tags are disjoint from `base`, contained in `top`, and pairwise distinct (`ChainTagsValid base steps`) | `[propext, Quot.sound]` | **Iterated `Niche::reserve` Injectivity & Disjointness** |
| `NicheChain.available_conservation` | `top.available + totalReserved steps = base.available` | `[propext, Quot.sound]` | Exact capacity accounting across arbitrary depth |
| `optBool_exact`, `optOptBool_exact`, `opt3Bool_exact`, `boolPlusTwo_exact`, **`optOptBool_valid_and_0x03_invalid`** (Theorem 2) | Proves `Option^3(bool)` tags `[0, 1, 2, 255, 254]`, `BoolPlusTwo` `[0, 1, 2, 3]`, and `contains 3#8 = false` for both `Option^2(bool)` and `Option^3(bool)` | `[]` (definitional `rfl`) | **Exact Wrap-Below-Zero & `0x03`-Invalidity Theorem** |
| `optChar_exact`, `optOptChar_exact`, `opt3Char_exact`, `opt3Char_tags_and_surrogate_gap` | Proves `[0x41, 0xffffffff, 0xfffffffe, 0xfffffffd]`, `contains 0x110000 = false`, and `contains 0xD800 = true` inside `WrappingRange 32` | `[]` | Formalizes `Option^3(char)` stacking & surrogate tag gap |
| **`nonNull64_spill_theorem`**, **`nonZero8_spill_theorem`**, `nonNull64_opt_opt_spills_to_16B`, `nonZero8_opt_opt_spills_to_2B` (Theorem 3) | Proves depth 1 reaches `isFull = true`, depth 2 hits `nicheReserve = none`, and `layoutOptionScalar` spills to `.directSpill 8 16` / `.directSpill 1 2` | `[]` | **Capacity Exhaustion Spill Theorem** |
| **`repr_u8_cu8_c_field_offset_divergence`** & `e0732_witnesses` & `zerocopyDerive_rejects_cInt_and_rust` (Theorem 4) | Proves `#[repr(u8)]` `[2],[1]` vs `#[repr(C, u8)]` `[2],[2]` vs `#[repr(C)]` `8B,[4],[4]`, all `E0732` gates, and `zerocopy` rejection of `#[repr(C, u8)]` / `#[repr(Rust)]` | `[]` | **Field-Offset Divergence & Repr Rejection Theorem** |
| **`isBitValidDirect_iff_decode_some`** & `isBitValidDirect_rejects_unknown_tag` (Theorem 5) | Total equivalence `isBitValidDirect m bytes = true ↔ ∃ val, decodeDirect m bytes = some val` with tag-first unknown-tag short-circuiting | `[propext, Quot.sound]` / `[propext]` | **Tag-First Direct-Enum `TryFromBytes` Soundness** |
| **`isBitValidNicheStack_iff_decode_some`** (Theorem 6) | Whenever `8 * baseCodec.size = w`, `isBitValidNicheStackClean w baseCodec outerSteps bytes = true ↔ ∃ val, decodeNicheStackClean w baseCodec outerSteps bytes = some val` | `[propext, Quot.sound]` | **Stacked-Niche `Option^k(T)` Zero-UB Soundness** |
| `opt2Bool_witness_decode`, `opt3Bool_witness_decode`, `opt3Char_witness_decode`, `packetU8_and_packetC_witnesses`, `opt3Bool_niche_chain`, `opt3Char_niche_chain` | End-to-end concrete decoding/rejection proofs for `PacketU8`, `PacketC`, `Option^2(bool)`, `Option^3(bool)`, and `Option^3(char)` (`0x110000` & `0xD800` both rejected by `decodeNicheStackClean`!) | `[propext]` / `[]` / `[propext, Quot.sound]` | Concrete model-to-probe conformance witnesses |

---

## Boundaries

To prevent future readers from over-generalizing beyond directly audited evidence, the following boundaries govern all claims in this report:

- **not examined:**
  - Multi-field payload structs containing non-scalar aggregates where `Niche::from_scalar` or `Variants::Multiple` picks a niche inside a nested struct field offset `offset > 0` across multi-byte structures (only single-scalar nested `Option^k` stacks and direct-tagged field-carrying `#[repr(...)]` enums were probed and formalized).
  - Non-`x86_64` / big-endian architectures and 32-bit pointer targets (`i686`, `aarch64`, `thumbv7m`), or `-Z randomize-layout` / packed struct (`#[repr(packed)]`) combinations.
  - Exhaustive audit of every standard-library `TryFromBytes` implementation beyond `bool`, `char`, `u8`, `u16`, `Option<NonZeroU8>`, and derived `#[repr(u8)]` / `#[repr(C)]` enums, or macro expansions using `#[zerocopy(crate = ...)]` with unaligned/ZST enum fields.
- **unknown:**
  - Whether future `rust-lang/rust` versions after `20fe935d50367c0ff8872c2ebfa050c5c99d9201` will resolve the inline `FIXME` for initial `bool` (`v == 0..=1`), which would flip `Option<bool>` from `[0, 1, 2]` to `[0, 1, 255]` and cascade to every nested `Option^k(bool)`.
  - What exact codegen/LLVM bug would recur if the `v != WrappingRange { start: 0, end: 1 }` guard in `Niche::reserve` were removed on `20fe935d50367c0ff8872c2ebfa050c5c99d9201` (not triggered without rebuilding `rustc`).
- **known not to apply:**
  - The assumption that nested `Option^k(bool)` uses contiguous tags `0, 1, 2, 3, ...` is **known not to apply** on all three audited `rustc` revisions (`14210df0e`, `49d734536`, `20fe935d5`): `0x03` is invalid (Miri UB) for `Option<Option<bool>>` and `Option<Option<Option<bool>>>`, whereas `255` and `254` are valid.
  - The assumption that passing `char`'s `WrappingRange` check suffices for bit-validity is **known not to apply**: surrogate `0xD800` passes `.enum-tag` under Miri and causes UB at `.enum-variant(Some).0`.
  - The assumption that `#[repr(u8)]` and `#[repr(C, u8)]` yield identical field offsets for mixed-alignment variants is **known not to apply**: `B(u8)` sits at offset `1` under `#[repr(u8)]` vs. offset `2` under `#[repr(C, u8)]`.
  - Integration between `support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean` and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) `Trusted.MirAst` / `Trusted.MirSemantics`: the Lean proof is self-contained and is **not** connected via machine-checked refinement to Anneal's internal AST (`Trusted.MirAst` currently supports only fieldless `Direct` enums).
- **unsupported:**
  - `#[derive(zerocopy::TryFromBytes)]` on **`#[repr(C, u8)]`** (and `#[repr(C, Int)]` generally) and on **`#[repr(Rust)]`** enums is explicitly unsupported by `zerocopy-derive` across `6f262351a`, `907b9175f`, and `e86eb0281`, failing macro expansion with `this conflicts with another representation hint` (verified `cargo check` exit `101`).
  - Explicit discriminants on `#[repr(C)]` or `#[repr(Rust)]` enums with non-unit variants (whether placed on unit or non-unit variants) are explicitly unsupported by `rustc` and rejected with `E0732`.
  - Direct multi-level `#[repr(C)]` enum layout optimization (`Variants::Multiple` with `TagEncoding::Niche`) is disabled (`inhibit_enum_layout_opt()`).

---

## Evidence

### 1. Primary Upstream Source Ledger

| Repository & Commit | Path & Symbol / Line Range | Inspected Fact | Basis |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_abi/src/lib.rs:195-240, 1425-1560, 2005-2096` (`WrappingRange`, `Niche::available`, `Niche::reserve`) | Defines `is_bool = size.bytes() == 1 && v == WrappingRange { start: 0, end: 1 }`, zero-ward `next_down <= next_up` when `count == 1 && !is_bool`, `move_start`, `move_end` | `source` |
| `rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da` | `compiler/rustc_abi/src/lib.rs:2130-2175` (`Niche::reserve`) | Inlines `count == 1 && v != (WrappingRange { start: 0, end: 1 })` | `source` |
| `rust-lang/rust` @ `20fe935d50367c0ff8872c2ebfa050c5c99d9201` | `compiler/rustc_abi/src/lib.rs:2169-2240`, `compiler/rustc_ty_utils/src/layout.rs:411-417` (`Primitive::Bool`) | Lowers `bool` as `Primitive::Bool`, widens `Bool -> Int(I8, false)` when `end.wrapping_sub(start) >= 2`, preserves `v != 0..=1` guard | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_ty_utils/src/layout.rs:268-285, 391-397` | Assigns `char` `WrappingRange { start: 0, end: 0x10FFFF }` (surrogates included) and `NonNull` `1..=2^w-1` (`available = 1`) | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_abi/src/layout.rs:597-1091, 1257-1307`, `compiler/rustc_middle/src/ty/layout.rs:77-120` | `inhibit_enum_layout_opt()`, `discr_range_of_repr` (`c_enum_min_size = 4B`), `#[repr(C, u8)]` `prefix_align` maxing variant field aligns vs `#[repr(u8)]` | `source` |
| `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_analysis/src/check/check.rs:1888-1925`, `compiler/rustc_const_eval/src/interpret/{discriminant.rs:45-327, validity.rs:1255-1330}` | `E0732` rule for non-int enums with explicit discriminants; runtime/CTFE `TagEncoding::Niche` tag decode + deep variant validity | `source` |
| `google/zerocopy` @ `6f262351a9b652425d13867717966668f3dd7cb0`, `907b9175fee081872ec883ca4709e6ad922f8ed0`, `e86eb0281380bdc278f4b4b3788dc9525ef59035` | `zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:33-71, 121-227, 315-346`, `zerocopy-derive/src/derive/project.rs:260-376`, `zerocopy-derive/src/repr.rs:450, 487` | SHA-256 `c5ef4996afd692800ba99a5d544ac554f5b80282b0aa532eceb55b4febce038a` identical across all 3 commits; `___ZerocopyTagPrimitive`, `___ZerocopyRawEnum`, `___ZerocopyVariantStruct`, rejection of `#[repr(C, Int)]` | `source` |
| `google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0` (identical in `6f262351a`, `e86eb0281`) | `zerocopy/src/lib.rs:1967-2000, 2100-2119`, `zerocopy/src/impls.rs:113-116, 141-147, 182-295` | `TryFromBytes::is_bit_valid`, `try_ref_from_bytes` align/size prefix guard, `bool` (`< 2`), `char::from_u32`, `Option<NonZero<T>>` | `source` |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `vendor/lean-miri/Miri/{ABI/WrappingRange.lean:1-150, Interpreter/Discriminant.lean:1-170}`, `trusted/lean/Trusted/{MirAst.lean:222-271, MirSemantics.lean:453-547}` | `lean-miri` lacks `Niche::reserve` generation; `Trusted.MirAst` models only fieldless `Direct` enums | `source` |

### 2. Preserved Execution Artifacts (`support/`)

All empirical claims are preserved as reproducible JSON transcripts in `support/probe_results.json` (`184` lines), generated on `2026-11-23` by running `support/probe_niche_stacking_and_try_from_bytes.py` (`638` LOC) with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` against `zerocopy 0.8.64` (`907b9175fee081872ec883ca4709e6ad922f8ed0`):

- **`probe_results.json -> a_type_sizes_and_niche_bit_patterns`:**
  - `print_type_sizes`: `-Zprint-type-sizes` output confirming exact variant padding/discriminant byte allocations (`ReprU8Data` `A` padding 1B / `B` 0B vs `ReprCU8Data` `B` padding 1B; `OptNonNull2` `discriminant: 8 bytes`, total `16 bytes`; `OptNonZeroU8_2` `discriminant: 1 bytes`, total `2 bytes`; `OptChar3` `4 bytes`).
  - `parsed_execution_values`: `opt_bool=[0, 1, 2]`, `opt_opt_bool=[0, 1, 2, 255]`, `opt3_bool=[0, 1, 2, 255, 254]`, `bool_plus_two=[0, 1, 2, 3]`, `opt3_char_hex=["0x41", "0xffffffff", "0xfffffffe", "0xfffffffd"]`, `field_offsets={"ReprU8Data_A": 2, "ReprU8Data_B": 1, "ReprCU8Data_B": 2, "ReprCData_B": 4}`, `tags={"ReprU8Data_B": 9, "ReprCU8Data_B": 9, "ReprCData_B": 1}`.
  - `e0732_non_unit_explicit_discr` & `e0732_unit_explicit_discr_with_non_unit_variant`: both exit `1` with `error[E0732]`.
- **`probe_results.json -> b_miri_enum_validity`:**
  - `miri_valid_option_option_bool_0_1_2_255_ok`: `returncode=0`, stdout `MIRI_NICHE_VALID=[Some(Some(false)), Some(Some(true)), Some(None), None]`.
  - `miri_invalid_niche_tag_3_ub_caught`: `returncode=1`, stderr `at .<enum-tag>, encountered 0x03, but expected a valid enum tag`.
  - `miri_invalid_niche_tag_3_opt3_ub_caught`: `returncode=1`, stderr `at .<enum-tag>, encountered 0x03, but expected a valid enum tag`.
  - `miri_invalid_char_niche_0x110000_ub_caught`: `returncode=1`, stderr `at .<enum-tag>, encountered 0x00110000, but expected a valid enum tag`.
  - `miri_invalid_char_surrogate_0xd800_ub_caught`: `returncode=1`, stderr `at .<enum-variant(Some)>.0, encountered 0x0000d800, but expected a valid unicode scalar value`.
  - `miri_repr_u8_vs_cu8_offsets_ok`: `returncode=0`, stdout `MIRI_OFFSETS=(1, 2)`.
  - `miri_invalid_repr_u8_tag_ub_caught`: `returncode=1`, stderr `at .<enum-tag>, encountered 0x07, but expected a valid enum tag`.
- **`probe_results.json -> c_zerocopy_try_from_bytes`:**
  - `native_run` (`cargo run --offline`, `returncode=0`) and `miri_run` (`cargo miri run --offline`, `returncode=0`): identical stdout `ZC_RESULTS bool=(Some(false),Some(true),true,true) char=(Some('A'),true,true) onz=(Some(None),Some(7)) pkt_u8=(true,true,true,true,true) pkt_c=(true,true,true)`.
  - `reject_repr_c_u8` (`cargo check --offline`, `returncode=101`): `error: this conflicts with another representation hint` pointing at `#[repr(C, u8)]`.

### 3. Preserved Lean 4 Kernel Proof (`support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean`)

- **Toolchain:** `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
- **Statistics:** `2,045` lines (`91,142` bytes), `607` local constants (`0` `._unsafe_rec`), `299` `noncomputable def`s, `134` local theorems, `0` warnings or errors with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` axioms outside `{propext, Quot.sound}`.

---

## Revalidation

Each major claim can be revalidated independently with low-cost checks:

1. **Re-run Live `rustc`, Miri, and `zerocopy::TryFromBytes` Probes:**
   Requires `rustc`, `cargo miri`, and a local `zerocopy` checkout (`--zerocopy-dir <path>` if outside standard relative workspace paths). Runs inside an isolated temporary directory without modifying the corpus:
   ```bash
   python3 support/probe_niche_stacking_and_try_from_bytes.py \
     --zerocopy-dir /path/to/zerocopy/zerocopy \
     --out /tmp/revalidated_probe_results.json
   ```
   Verify `parsed_execution_values` matches `[0, 1, 2]`, `[0, 1, 2, 255]`, `[0, 1, 2, 255, 254]`, `["0x41", "0xffffffff", "0xfffffffe", "0xfffffffd"]`, `field_offsets` (`1` vs `2` vs `4`), both `E0732` failures, all 7 Miri tests (`0x03`, `0x110000`, `0xD800`, `0x07`), and `zerocopy` native/Miri/rejection results.

2. **Re-check Upstream Source Shifts on a Newer `rust-lang/rust` or `google/zerocopy` Commit:**
   - **In `rust-lang/rust`:** Inspect `Niche::reserve` in `compiler/rustc_abi/src/lib.rs` to check whether the `v != WrappingRange { start: 0, end: 1 }` guard has been removed or altered, and check `prefix_align` in `compiler/rustc_abi/src/layout.rs` plus `inhibit_enum_layout_opt` in `compiler/rustc_middle/src/ty/layout.rs`.
   - **In `google/zerocopy`:** Check `zerocopy-derive/src/derive/try_from_bytes.rs` and `zerocopy-derive/src/repr.rs` to see whether `#[repr(C, Int)]` support or `___ZerocopyTagPrimitive` projection has changed.
   - **In `joshlf/anneal`:** Inspect `trusted/lean/Trusted/MirAst.lean` (`EnumTagRepr` / `TagEncoding`) to determine whether field-carrying enums or `Niche` tags have been added to `Trusted`.

3. **Kernel Re-check the Standalone `Lean v4.34.1` Formalization:**
   Verify zero errors, zero warnings, and clean elaboration with async elaboration disabled and full kernel typechecking enabled:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/AbiGreedyNicheStackingAndTryFromBytesSoundness.lean
   ```
