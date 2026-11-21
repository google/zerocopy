# `rustc` `TagEncoding::Niche` Wrapping Modular Tag Arithmetic, Variant-Order Size Non-Monotonicity, `SetDiscriminant` Write-Order UB, and Branchless x86-64 Niche Decoding

## Summary

In `rustc`, niche-optimized multi-variant enums (`TagEncoding::Niche`) encode all inhabited variants other than one chosen `untagged_variant` inside a single contiguous `RangeInclusive<VariantIdx>` span (`niche_variants`) mapped by wrapping unsigned modular arithmetic modulo $2^w$ (`tag = ((variant_index - niche_variants.start) + niche_start) mod 2^w`) over a single `WrappingRange` scalar validity hole in the largest variant. Direct inspection of upstream `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), live execution across `rustc`/`Miri` (`1.98.0-nightly`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) with cross-revision verification against `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`), and a constructive kernel-checked Lean 4 (`v4.34.1`) mechanization (`support/EnumNicheWrappingAndSetDiscriminant.lean`, 25 theorems, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`) establish five load-bearing invariants for compiler verification and MIR semantics:

1. **Variant-Declaration-Order Size Non-Monotonicity (`1 B` vs. `2 B`) and Dead Middle Slots.** Because `calculate_niche_filling_layout` computes `niche_variants` as the minimal inclusive span `[first_needing_disc, last_needing_disc]` and reserves `count = (last - start) + 1` contiguous niche values (`compiler/rustc_abi/src/layout/enum_layout.rs:604-615`), declaring the `untagged_variant` strictly between two niched variants forces `rustc` to allocate an extra unused niche slot to skip `untagged_variant`. For an inner payload `Inner1To254` with `valid_range = 1..=254` (`available = 2` wrapping niches `{255, 0}` mod 256), `enum OuterThreeEdge { UntaggedPayload(Inner1To254), FirstNiche, SecondNiche }` and `OuterThreeEdgeTail` have `size_of == 1` byte (`FirstNiche = 255`, `SecondNiche = 0`, `UntaggedPayload = 1..=254`), whereas merely reordering the declaration to `enum OuterThreeMiddle { FirstNiche, UntaggedPayload(Inner1To254), SecondNiche }` requires `count = 3 > 2` niches, causing `Niche::reserve` to return `None` and **doubling `size_of` to `2` bytes** (`TagEncoding::Direct`). When `3` niches are available (`Inner1To253`, valid on `1..=253`), `OuterThreeMiddle3Niches` fits in `1` byte (`FirstNiche = 254`, `SecondNiche = 0`, full `tagValidRange = 1..=0`), turning byte `255` (`0xff`) into an impossible dead middle slot inside `tagValidRange` that `rustc_codegen_ssa` rules out with an explicit `call void @llvm.assume(i1 (icmp ne i8 %x, -1))` (`compiler/rustc_codegen_ssa/src/mir/operand.rs:606-615`) and `Miri` rejects with `InvalidTag(0xff)` (`compiler/rustc_const_eval/src/interpret/discriminant.rs:188-193`).
2. **Signed-Closest-to-Zero Wrapping Niche Reservation (`Option<Option<bool>>`).** `Niche::reserve` (`compiler/rustc_abi/src/lib.rs:2139-2205`) prefers `count == 1` extensions closest to signed zero (`move_start` vs. `move_end`), except for an explicit `bool` guard (`v != WrappingRange { start: 0, end: 1 }`). Consequently, `Option<bool>::None` encodes as `2` (`valid_range = 0..=2`), while `Option<Option<bool>>::None` wraps downward via `move_start` to **`255` (`-1`, `valid_range = 255..=2` -> LLVM `range(i8 -1, 3)`)** and `Option<Option<Option<bool>>>::None` wraps to **`254` (`-2`)**—all in `1` byte—whereas `Option<Option<NonZero<u8>>>` and `Option<Option<&u32>>` double to `2` bytes and `16` bytes respectively because `WrappingRange` niches exhaust at `available == 0` (pointer alignment bits are never mined as niches).
3. **`StatementKind::SetDiscriminant` Write-Order UB Invisible to Native Codegen.** In `compiler/rustc_const_eval/src/interpret/discriminant.rs:20-46`, `InterpCx::write_discriminant` receives `Ok(None)` from `tag_for_variant` for `untagged_variant` and performs a mandatory **validation read** (`self.read_discriminant`), throwing `InvalidNichedEnumVariantWritten` if the existing bytes encode a different variant (e.g., `None = 0x00`) or uninitialized-memory UB if the slot is uninitialized. By contrast, `PlaceRef::codegen_set_discr` (`compiler/rustc_codegen_ssa/src/mir/place.rs:262-279`) emits **zero instructions** on `Ok(None)`. Reordering `SetDiscriminant(RET, 1)` before `place!(Field(Variant(RET, 1), 0)) = v` on `Option<NonZero<u8>>` compiles under `rustc -C opt-level=2` to the **exact same 2-instruction x86-64 function** (`movl %edi, %eax; retq`, `native_opt2_rc = 0`) as the valid payload-first order, yet faults immediate UB in `Miri` (`miri_opt0_rc = 1`) both over a `None`-initialized destination (`InvalidNichedEnumVariantWritten`) and over an uninitialized destination (`using uninitialized data`).
4. **Branchless x86-64 Niche Decoding and LLVM `!range` / `assume` Metadata.** `rustc_codegen_llvm` attaches half-open `!range` metadata (`[start, end.wrapping_add(1))`) on scalar loads (`compiler/rustc_codegen_llvm/src/builder.rs:755-790, 862-874`) and `range(...)` parameter/return attributes (`compiler/rustc_codegen_llvm/src/abi.rs:683-698`) whenever `!scalar.is_bool() && !scalar.is_always_valid(cx)`. Combined with `codegen_get_discr`'s unsigned/signed non-wrapping and wrapping-subtraction lowering (`operand.rs:540-715`), LLVM lowers wrapping niche matches into branchless x86-64 sequences: bit-packed right-shift tables (`incb %dil; shll $3, %ecx; movl $50462980, %eax; shrl %cl, %eax` for `Option<Option<bool>>` on LLVM `22.1.6`; `leal 2(%rdi), %eax; ...; movl $1968660, %eax; shrl %cl, %eax` for `OuterThreeEdge` on LLVM `23.1.5`) or branchless `leal`/`cmpb`/`cmovbl` arithmetic (`classify_outer_edge` and `classify_middle_3niches` on LLVM `22.1.6`).
5. **MIR Operation Distribution in `zerocopy` and Trusted Boundary Alignment in Anneal.** Across `zerocopy v0.8.64` (`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`), `StatementKind::SetDiscriminant` occurs **`0` times** in both `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR (`4,840 -> 4,590` bodies with `std+alloc+simd`, `4,715 -> 4,478` with default `no_std`, corroborating `4,663 -> 4,302` bodies on `rustc 1.102.0-nightly`) while `Rvalue::Discriminant` grows **2.48x–2.72x** after `Inline` (`664 -> 1,649` on `1.98.0-nightly`; `589 -> 1,601` on `1.102.0-nightly`). Normal enum construction stays `Rvalue::Aggregate(AggregateKind::Adt, ...)` through MIR optimization, whereas `StateTransform` on `async fn` coroutines (`compiler/rustc_mir_transform/src/coroutine/mod.rs:359-364`) directly emits `SetDiscriminant` (`3` statements in a two-step `async fn` probe). In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` currently admits only fieldless `Direct`/`Single` enums and lowers `SetDiscriminant` and `AggregateKind::Adt` fail-closed to `.unsupported`, while vendored `vendor/lean-miri/Miri/Interpreter/Discriminant.lean` already implements the full `TagEncoding::Niche` and `writeDiscriminant` validation-read contract.

## Applicability

This report characterizes the exact relationship across six durable upstream subjects recorded in `REPORT.json`:

1. **Primary compiler source (`rust-lang/rust`, `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`):** Governs every cited line range for `compiler/rustc_abi/src/{wrapping_range.rs,lib.rs,layout/enum_layout.rs}`, `compiler/rustc_ty_utils/src/layout/invariant.rs`, `compiler/rustc_const_eval/src/interpret/discriminant.rs`, `compiler/rustc_middle/src/mir/interpret/error.rs`, `compiler/rustc_codegen_ssa/src/mir/{place.rs,operand.rs,rvalue.rs,statement.rs}`, `compiler/rustc_codegen_llvm/src/{builder.rs,abi.rs}`, and `compiler/rustc_mir_transform/src/{coroutine/mod.rs,validate.rs}`.
2. **Cross-revision `rustc` equivalence (`14210df0e` vs. `3ef0c22cd` vs. `c7d5ba59d`):**
   - `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, LLVM `23.1.5`) and `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` are **byte-for-byte identical** in `compiler/rustc_abi/src/layout/enum_layout.rs`, `compiler/rustc_const_eval/src/interpret/discriminant.rs`, and `compiler/rustc_codegen_ssa/src/mir/place.rs` (verified by `diff -u` returning 0 bytes).
   - `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, LLVM `22.1.6`), on which the live execution suite (`support/probe_niche_layout_and_set_discriminant.py` -> `support/probe_results.json`) ran on `x86_64-unknown-linux-gnu`, predates the refactoring of `compiler/rustc_abi/src/layout.rs:574-743` into `compiler/rustc_abi/src/layout/enum_layout.rs:558-664` and uses `layout.for_variant(self, index).is_uninhabited()` rather than `layout.is_variant_uninhabited(index)` in `discriminant.rs`. Its `Niche::reserve` (`lib.rs:2029-2090`) and `calculate_niche_filling_layout` (`layout.rs:592-743`) implement the exact same wrapping range math, contiguous `niche_variants` span, `bool`-guarded `count == 1` closest-to-zero rule, validation read in `write_discriminant`, and no-op `codegen_set_discr` for `untagged_variant`.
   - **Codegen difference observed between LLVM `22.1.6` and LLVM `23.1.5`:** Both lower niche switches branchlessly on `x86_64-unknown-linux-gnu` at `-C opt-level=2`, but LLVM `23.1.5` lowered `classify_outer_edge` (`10`/`20`/`30`) to a bit-packed shift lookup (`movl $1968660, %eax; shrl %cl, %eax`), whereas LLVM `22.1.6` lowered `classify_outer_edge` to linear wrapping arithmetic plus `cmovbl` (`leal 1(%rdi), %eax; ...; cmpb $2, %al; cmovbl %ecx, %eax`) and lowered `classify_opt2_bool` (`1`/`2`/`3`/`4`) to the bit-packed shift lookup (`movl $50462980, %eax; shrl %cl, %eax`).
3. **Target and repr scope:**
   - Layout calculations apply to default `#[repr(Rust)]` enums whose `ReprOptions::inhibit_enum_layout_opt()` is false (i.e., no `#[repr(C)]`, no `#[repr(int)]`, and no explicit non-sequential discriminants—`layout_sanity_check` requires `discriminant_for_variant == idx` for all variants under `TagEncoding::Niche`).
   - Empirical execution (`Part A` and `Part B`) applies to `x86_64-unknown-linux-gnu` (`64`-bit little-endian pointers, `usize = 8` bytes). The `Part B` custom-MIR probes use `#![feature(custom_mir, core_intrinsics)]` targeting `dialect = "runtime", phase = "post-cleanup"`, matching the MIR phase where `StatementKind::SetDiscriminant` is permitted (`validate.rs:312-315`).
   - The `zerocopy` MIR census (`Part C`) applies to `zerocopy v0.8.64` (`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`) compiled as `--crate-type lib -O` under both `std+alloc+simd` and default `no_std`, contrasted with a cross-revision `rustc 1.102.0-nightly` build.
4. **Relationship to Anneal and Lean mechanization:**
   - The Anneal audit applies specifically to `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean` and `vendor/lean-miri/Miri/Interpreter/Discriminant.lean`).
   - The Lean 4 formalization (`support/EnumNicheWrappingAndSetDiscriminant.lean`, verified under `leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) is parametric over arbitrary bit width `w : Nat` (`modulus w = 2^w`) for integer scalar niches; concrete counterexamples specialize to `w = 8`. It complements abstract enum-prism validity theory by mechanizing `rustc`'s exact modular wrapping arithmetic, `move_end`/`move_start` reservation, `decodeNicheTag` dead-slot rejection, and `evalSetDiscriminant` vs. `evalCodegenSetDiscr` refinement.

## Findings

### 1. `WrappingRange` and `Niche::reserve` Wrapping Modular Arithmetic

Basis: source + execution + derived (Lean 4 proof)

`rustc_abi` represents every scalar's valid bit-pattern set as a single inclusive circular arc on $[0, 2^w)$:

```rust
// compiler/rustc_abi/src/wrapping_range.rs:19-22, 57-63, 112-116
pub struct WrappingRange { pub start: u128, pub end: u128 }

pub fn contains(&self, v: u128) -> bool {
    if self.start <= self.end {
        self.start <= v && v <= self.end
    } else {
        self.start <= v || v <= self.end
    }
}

pub fn is_full_for(&self, size: Size) -> bool {
    let max_value = size.unsigned_int_max();
    self.start == (self.end.wrapping_add(1) & max_value)
}
```

A scalar has a usable niche whenever `Niche::available` (`compiler/rustc_abi/src/lib.rs:2128-2137`) is strictly positive:

```rust
let niche = v.end.wrapping_add(1)..v.start;
niche.end.wrapping_sub(niche.start) & max_value
```

Algebraically, letting $M = 2^w$ and writing $(a - b) \bmod M$ for `wrapSub w a b`, the valid-value cardinality is $\text{validCount}(r) = ((r.\text{end} - r.\text{start}) \bmod M) + 1 \in [1, M]$, and the available niche count is $\text{availableNiches}(r) = (r.\text{start} - (r.\text{end} + 1)) \bmod M \in [0, M-1]$. As proved in `WrappingRange.validCount_add_availableNiches` (`support/EnumNicheWrappingAndSetDiscriminant.lean`), these satisfy the exact conservation law:

$$\text{validCount}(r) + \text{availableNiches}(r) = 2^w$$

Because every `WrappingRange` is non-empty ($\text{validCount}(r) \ge 1$), $\text{availableNiches}(r) < 2^w$ always holds, and a type can have **at most one contiguous circular gap** represented as a niche. Disjoint invalid values—such as pointer alignment low bits on `&u32` (whose valid range is simply `1..=u64::MAX`, with `available == 1`)—cannot be represented inside `WrappingRange` and are never consumed as enum niches.

When `calculate_niche_filling_layout` requests `count` niches (`count > 0`), `Niche::reserve` (`compiler/rustc_abi/src/lib.rs:2139-2205`) checks `count <= available` (returning `None` otherwise) and extends the valid range by moving either `v.start` downward (`move_start`: `niche_start = (v.start - count) & max_value`, `new_valid = { start: niche_start, end: v.end }`) or `v.end` upward (`move_end`: `niche_start = (v.end + 1) & max_value`, `new_valid = { start: v.start, end: (v.end + count) & max_value }`). The branch selection policy (`lib.rs:2174-2204`) follows four ordered rules:

1. **Single-niche signed-closest-to-zero rule (`count == 1` and `v != 0..=1`):** Compares `next_down = |sign_extend(v.start - 1)|` against `next_up = |sign_extend(v.end + 1)|`, choosing `move_start` if `next_down <= next_up` else `move_end`. Crucially, `bool` (`v = 0..=1`) is explicitly excluded from this branch (`lib.rs:2175-2177`), forcing `Option<bool>::None` onto `2` (`move_end`) rather than `255` (`-1`).
2. **Already-wrapping range (`v.start > v.end`):** Zero is already occupied by the payload, so `move_end` is selected.
3. **Start closer to zero than end (`v.start <= max_value - v.end`):** Chooses `move_start` if `count <= v.start`, otherwise (`count > v.start`, which would step past `0`) chooses `move_end`.
4. **End closer to zero (`v.start > max_value - v.end`):** Chooses `move_end` unless `(v.end + count) & max_value` overshoots into `1..=v.end`, in which case it chooses `move_start`.

Tracing this exact decision tree explains three subtle live observations in `support/probe_results.json`:

| Type | Inner `valid_range` | `available` | `count` | `Niche::reserve` Branch | Resulting `niche_start` & Outer `valid_range` | Live `size_of` / Raw Niche Bytes |
| :--- | :--- | ---: | ---: | :--- | :--- | :--- |
| `Option<bool>` | `0..=1` | `254` | `1` | Excluded from Rule 1; Rule 3 (`0 <= 254`, `1 > 0`) -> `move_end` | `niche_start = 2`, `valid_range = 0..=2` | `1 B`, `None = 2` |
| `Option<Option<bool>>` | `0..=2` | `253` | `1` | Rule 1 (`next_down = |-1| = 1 <= next_up = 3`) -> **`move_start`** | **`niche_start = 255`**, **`valid_range = 255..=2`** (wrapping!) | `1 B`, **`None = 255`** |
| `Option<Option<Option<bool>>>` | `255..=2` | `252` | `1` | Rule 1 (`next_down = |-2| = 2 <= next_up = 3`) -> **`move_start`** | **`niche_start = 254`**, **`valid_range = 254..=2`** (wrapping!) | `1 B`, **`None = 254`** |
| `OuterThreeEdge` (`Inner1To254`) | `1..=254` | `2` | `2` | Rule 3 (`v.start=1 <= dist_end=1`, `count=2 > 1`) -> **`move_end`** | **`niche_start = 255`**, `valid_range = 1..=0` (full, wrapping!) | `1 B`, `FirstNiche = 255`, `SecondNiche = 0` |
| `OuterThreeMiddle` (`Inner1To254`) | `1..=254` | `2` | `3` | Capacity check `3 > 2` -> **`None`** (`TagEncoding::Direct`) | Direct 1-byte tag + 1-byte payload | **`2 B`** |
| `OuterThreeMiddle3Niches` (`Inner1To253`) | `1..=253` | `3` | `3` | Rule 3 (`v.start=1 <= dist_end=2`, `count=3 > 1`) -> **`move_end`** | **`niche_start = 254`**, `valid_range = 1..=0` (full, wrapping!) | `1 B`, `FirstNiche = 254`, **dead `255`**, `SecondNiche = 0` |
| `Option<NonZero<u8>>` | `1..=255` | `1` | `1` | Rule 1 (`next_down = 0 <= next_up = 0`) -> `move_start` | `niche_start = 0`, `valid_range = 0..=255` (full) | `1 B`, `None = 0` |
| `Option<Option<NonZero<u8>>>` | `0..=255` | `0` | `1` | `largest_niche == None` -> `TagEncoding::Direct` | Direct 1-byte tag + 1-byte payload | **`2 B`** |
| `Option<&u32>` / `Result<&u32, ()>` | `1..=u64::MAX` | `1` | `1` | Rule 1 (`next_down = 0`) -> `move_start` | `niche_start = 0`, `valid_range = 0..=u64::MAX` (full) | `8 B`, `None/Err = 0usize` |
| `Option<Option<&u32>>` | `0..=u64::MAX` | `0` | `1` | `largest_niche == None` (align bits unused) -> `TagEncoding::Direct` | 8-byte aligned tag + 8-byte payload | **`16 B`** |
| `Option<&[u32]>` | `(ptr: 1..=MAX, len: full)` | `1` | `1` | `largest_niche` at offset `0` (`ScalarPair` `b.to_union()`) | `niche_start = 0` in data pointer field | `16 B` |
| `Option<UnsafeCell<bool>>` | `NicheOptimizations::Disabled` | `0` | `1` | `largest_niche == None` (`lib.rs:2210-2218`) | Direct 1-byte tag + 1-byte payload | **`2 B`** |
| `#[repr(u8)] OuterExplicitReprU8` | `1..=254` | `2` | — | `repr.inhibit_enum_layout_opt() == true` (`enum_layout.rs:569`) | Direct 1-byte tag + 1-byte payload | **`2 B`** |

Notice the unexpected empirical behavior on nested `Option<Option<bool>>`: because `Option<bool>` yields `valid_range = 0..=2` (which no longer triggers the `v == 0..=1` `bool` special-case guard), the second wrapping `Option` chooses `255` (`-1`) instead of `3`, turning `Option<Option<bool>>`'s tag range into a **wrapping range** `255..=2` (`range(i8 -1, 3)` in LLVM IR).

### 2. Variant-Declaration-Order Size Non-Monotonicity and Contiguous `niche_variants`

Basis: source + execution + derived (Lean 4 proof)

In `compiler/rustc_abi/src/layout/enum_layout.rs:558-664`, `calculate_niche_filling_layout` constructs a niche-encoded layout in six deterministic steps:

1. **Inhibition & variant count check (lines `569-575`):** Bails with `None` if `repr.inhibit_enum_layout_opt()` (true for `#[repr(C)]`, `#[repr(int)]`, or explicit discriminants that break `discriminant == variant_index`) or `variants.len() < 2`.
2. **Untagged variant selection (lines `599-602`):** Computes univariant layouts for all variants and picks `largest_variant_index = variant_layouts.iter_enumerated().max_by_key(|(_, l)| l.size.bytes())` (ties go to the **last** maximum-size variant under `Iterator::max_by_key`).
3. **Contiguous `niche_variants` span (lines `604-611`):**
   ```rust
   let needs_disc = |index: VariantIdx| index != largest_variant_index && !absent(&variants[index]);
   let niche_variants = RangeInclusive {
       start: variants.indices().find(|v| needs_disc(*v)).unwrap(),
       last: variants.indices().rev().find(|v| needs_disc(*v)).unwrap(),
   };
   let count = (niche_variants.last.index() as u128 - niche_variants.start.index() as u128) + 1;
   ```
4. **Largest-niche reservation (lines `614-615`):** Extracts `variant_layouts[largest_variant_index].largest_niche?` and calls `niche.reserve(dl, count)?`. **If `count > niche.available(dl)`, this immediately returns `None`**, falling back to `calculate_tagged_layout` (`TagEncoding::Direct`, lines `35-40`).
5. **Non-overlapping payload placement (lines `480-520`, `618-625`):** `try_fit_variants_around_niche_tag` verifies every other variant fits either before `niche.offset` (`layout.size <= niche_offset`) or aligned after `niche.offset + niche_size` within `size`.
6. **Layout tie-breaker (`layout_of_enum`, lines `42-55`):** Compares `tagged_layout` and `nl` by `(tagged_layout.size.cmp(&nl.size), niche_size(&tagged_layout).cmp(&niche_size(&nl)))`, picking `nl` only when `nl` is strictly smaller or equal-sized with a strictly larger remaining niche.

Step 3 is the exact root cause of **variant-declaration-order size non-monotonicity**. Because `TagEncoding::Niche` stores only a single inclusive interval `niche_variants = start..=last` (so decoding can compute `variant_index = start + ((tag - niche_start) mod 2^w)` with a single affine expression rather than a lookup table), any variant index lying strictly between `start` and `last`—including `untagged_variant` itself and any uninhabited variants—consumes a slot in `count`:

- For an $n$-variant enum ($n \ge 3$) with all variants inhabited (proved in `NicheLayout.edge_vs_interior_required_niches`):
  - If `untagged_variant == 0` (first variant): `niche_variants = 1..=(n - 1)`, so **`count = n - 1`**.
  - If `untagged_variant == n - 1` (last variant): `niche_variants = 0..=(n - 2)`, so **`count = n - 1`**.
  - If `0 < untagged_variant < n - 1` (interior variant): `niche_variants = 0..=(n - 1)`, so **`count = n`**—requiring **1 extra niche slot** that is permanently dead (`variant_index == untagged_variant`).
- For `Inner1To254` (`available = 2`):
  - `OuterThreeEdge` (`untagged = 0`, `niche_variants = 1..=2`, `count = 2 <= 2`): **`size_of == 1` B**, raw bytes `FirstNiche = 255`, `UntaggedPayload(1..=254) = 1..=254`, `SecondNiche = 0`.
  - `OuterThreeEdgeTail` (`untagged = 2`, `niche_variants = 0..=1`, `count = 2 <= 2`): **`size_of == 1` B**, raw bytes `FirstNiche = 255`, `SecondNiche = 0`, `UntaggedPayload(1..=254) = 1..=254`.
  - `OuterThreeMiddle` (`untagged = 1`, `niche_variants = 0..=2`, `count = 3 > 2`): `Niche::reserve` returns `None`, falling back to `TagEncoding::Direct` -> **`size_of == 2` B** (`-Zprint-type-sizes` confirms `discriminant: 1 bytes`, `variant UntaggedPayload: 1 bytes`).
- Furthermore, `compiler/rustc_ty_utils/src/layout/invariant.rs:300-318` (`layout_sanity_check`) enforces two additional structural invariants on every `TagEncoding::Niche` layout: (a) `niche_start <= niche_size.unsigned_int_max()`, and (b) for every variant `idx`, `layout.ty.discriminant_for_variant(tcx, idx).unwrap().val == u128::from(idx.as_u32())`. Thus `TagEncoding::Niche` never requires a tag-to-discriminant remapping table because variant index and discriminant value coincide identically.

### 3. `InterpCx::read_discriminant` and `write_discriminant` Operational Semantics and Write-Order UB

Basis: source + execution + derived (Lean 4 proof)

`compiler/rustc_const_eval/src/interpret/discriminant.rs` defines the authoritative operational semantics used by both CTFE and Miri:

#### 3.1 `read_discriminant` (`discriminant.rs:142-218`)

For `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`, after loading `tag_val` from `tag_field`:

1. **CTFE abstract-pointer path (lines `148-161`):** If `tag_val.try_to_scalar_int()` fails (an abstract pointer with provenance during CTFE), `read_discriminant` accepts it **only** when `niche_start == 0 && variants_start == variants_last && !self.scalar_may_be_null(tag_val)?` (e.g., `Option<&T>` with non-null provenance), returning `untagged_variant`; all other pointer-niche configurations throw `InvalidTag`.
2. **Integer/bit-pattern path (lines `162-204`):** Computes machine wrapping subtraction at `tag_layout` bit width:
   ```rust
   let variant_index_relative_val = self.binary_op(mir::BinOp::Sub, &tag_val, &niche_start_val)?;
   let variant_index_relative = variant_index_relative_val.to_scalar().to_bits(tag_val.layout.size)?;
   if variant_index_relative <= u128::from(variants_last - variants_start) {
       let variant_index = VariantIdx::from_u32(variants_start.checked_add(variant_index_relative as u32).unwrap());
       assert!(tag_scalar_layout.valid_range(self).contains(tag_bits));
       if variant_index == untagged_variant {
           throw_ub!(InvalidTag(Scalar::from_uint(tag_bits, tag_layout.size)))
       }
       variant_index
   } else {
       if !tag_scalar_layout.valid_range(self).contains(tag_bits) {
           throw_ub!(InvalidTag(Scalar::from_uint(tag_bits, tag_layout.size)))
       }
       untagged_variant
   }
   ```
3. **Uninhabited check (lines `214-216`):** If `op.layout().is_variant_uninhabited(index)`, throws `UninhabitedEnumVariantRead(Some(index))`.

Crucially, there are **two distinct `InvalidTag` UB paths** in `read_discriminant`:
- **Out-of-`valid_range` niche hole (`discriminant.rs:198-200`):** Demonstrated live by `option_bool_byte3_niche_hole_ub` (`support/probe_results.json`): reading raw byte `0x03` through `*const Option<bool>` (`valid_range = 0..=2`, `niche_start = 2`, `relative = (3 - 2) mod 256 = 1 > 0`) hits the `else` branch, fails `valid_range.contains(3)`, and aborts Miri (`miri_opt0_rc = 1`) with `error: Undefined Behavior: enum value has invalid tag: 0x03`, while native `-C opt-level=2` executes with `rc = 0` and prints `TAG:1`.
- **Dead middle niche slot *inside* `valid_range` (`discriminant.rs:188-193`):** Demonstrated live by `middle_3niches_dead_slot_invalid_tag_ub` (`support/probe_results.json`): for `OuterThreeMiddle3Niches` (`valid_range = 1..=0` [full!], `untagged_variant = 1`, `niche_variants = 0..=2`, `niche_start = 254`), raw byte `0xff` (`255`) satisfies `valid_range.contains(255) == true` and yields `relative = (255 - 254) mod 256 = 1 <= 2`, computing `variant_index = 0 + 1 = 1 == untagged_variant`. Miri immediately hits line `192` (`miri_opt0_rc = 1`) with `error: Undefined Behavior: enum value has invalid tag: 0xff`, while native `-C opt-level=2` executes with `rc = 0` and prints `TAG:20`.

#### 3.2 `write_discriminant` (`discriminant.rs:20-46`) vs. `codegen_set_discr` (`place.rs:262-279`)

For `StatementKind::SetDiscriminant { place, variant_index }`, `InterpCx::write_discriminant` dispatches on `tag_for_variant` (`discriminant.rs:247-327`):

- If `variant_index` is uninhabited: throws `UninhabitedEnumVariantWritten(variant_index)`.
- If `variant_index != untagged_variant` (`TagEncoding::Niche`): computes `tag = ((variant_index - variants_start) + niche_start) mod 2^w` via `mir::BinOp::Add` (`discriminant.rs:321-323`) and writes `tag` into `tag_field` without inspecting prior contents.
- If `variant_index == untagged_variant` (or `Variants::Single`): `tag_for_variant` returns `Ok(None)`, and `write_discriminant` executes the mandatory **validation read** (`discriminant.rs:39-43`):
  ```rust
  let actual_variant = self.read_discriminant(&dest.to_op(self)?)?;
  if actual_variant != variant_index {
      throw_ub!(InvalidNichedEnumVariantWritten { enum_ty: dest.layout().ty });
  }
  interp_ok(())
  ```

By stark contrast, `compiler/rustc_codegen_ssa/src/mir/place.rs:262-279` (`codegen_set_discr`) handles `Ok(None)` with an **empty match arm (`Ok(None) => {}`)**—emitting **zero LLVM IR instructions and zero machine instructions**.

This semantic-vs.-codegen asymmetry creates a razor-sharp **MIR write-order UB hazard** for any compiler pass or MIR emitter (such as deaggregation, destination propagation, or coroutine lowering):

| Custom-MIR Probe (`Option<NonZero<u8>>`, `untagged = 1 [Some]`) | Statement Order in `Runtime(PostCleanup)` MIR | Native `-C opt-level=2` x86-64 Asm | Native `-O2` Exit / Output | Miri `-O0` Exit | Exact Miri Diagnostic |
| :--- | :--- | :--- | :--- | ---: | :--- |
| **B1 (Valid order)** | `place!(Field(Variant(RET, 1), 0)) = v; SetDiscriminant(RET, 1);` | `movl %edi, %eax; retq` | `0` / `OK:7` | **`0`** | *(none — UB-free)* |
| **B2a (Reordered over `None`)** | `RET = Option::None; SetDiscriminant(RET, 1); place!(Field(Variant(RET, 1), 0)) = v;` | `movl %edi, %eax; retq` | `0` / `OK:7` | **`1`** | `Undefined Behavior: trying to set discriminant of a core::option::Option<core::num::NonZero<u8>> to the niched variant, but the value does not match` (`InvalidNichedEnumVariantWritten`) |
| **B2b (Reordered over uninit)** | `SetDiscriminant(RET, 1); place!(Field(Variant(RET, 1), 0)) = v;` | `movl %edi, %eax; retq` | `0` / `OK:7` | **`1`** | `Undefined Behavior: using uninitialized data, but this operation requires initialized memory` |

All three functions compile under `rustc 1.98.0-nightly -C opt-level=2` to the **identical 2-instruction x86-64 body** (`native_opt2_machine_code_identical_b1_b2a_b2b = true`), confirming that native testing cannot detect `SetDiscriminant`-before-payload reordering bugs on niched untagged variants. Notice also the two distinct Miri failure modes in B2a vs. B2b: when the destination already holds the niche byte `0x00` (`None`), `read_discriminant` succeeds with `actual_variant = 0 != 1` and trips `InvalidNichedEnumVariantWritten` at `discriminant.rs:41`; when the destination is uninitialized (`StorageLive` with no prior write), `read_discriminant` trips `InvalidUninitBytes` inside `read_immediate` at `discriminant.rs:100` before reaching line `40`.

### 4. LLVM `!range` / `assume` Metadata and Branchless x86-64 Niche Decoding

Basis: source + execution

`rustc_codegen_ssa` and `rustc_codegen_llvm` propagate `WrappingRange` invariants to LLVM through three channels (all gated on `OptLevel != OptLevel::No`):

1. **Scalar load `!range` metadata (`compiler/rustc_codegen_llvm/src/builder.rs:755-790, 862-874`):** `scalar_load_metadata` emits `!noundef` for initialized scalars, `!nonnull` for pointers excluding `0`, and `!range !{iN start, iN end.wrapping_add(1)}` for integers where `!scalar.is_always_valid(bx)`. Live `--emit=llvm-ir -C opt-level=2` verifies both wrapping and non-wrapping half-open ranges:
   - `load_inner254_from_ref`: `%_2 = load i8, ptr %x, align 1, !range !10, !noundef !6` with `!10 = !{i8 1, i8 -1}` (representing $[1, 255)$ mod 256, i.e., `1..=254`).
   - `load_opt_bool_from_ref`: `%0 = load i8, ptr %x, align 1, !range !11, !noundef !6` with `!11 = !{i8 0, i8 3}` (representing $[0, 3)$, i.e., `0..=2`).
2. **Function parameter and return `range(...)` attributes (`compiler/rustc_codegen_llvm/src/abi.rs:683-698`):** Attached whenever `!scalar.is_bool() && !scalar.is_always_valid(cx)`. Live IR confirms `define ... noundef range(i8 1, 5) i8 @classify_opt2_bool(i8 noundef zeroext range(i8 -1, 3) %0)` (carrying the wrapping `Option<Option<bool>>` range `[-1, 3) = {255, 0, 1, 2}` across the ABI boundary!), whereas `classify_outer_edge` and `classify_middle_3niches` carry **no** input `range(...)` attribute because their outer `tagValidRange = 1..=0` is full (`is_always_valid == true`).
3. **Explicit `llvm.assume` for interior dead niche slots (`compiler/rustc_codegen_ssa/src/mir/operand.rs:606-615`):** When `relative_max > 0` and `niche_variants.contains(&untagged_variant)`, `codegen_get_discr` computes `impossible = (niche_start + untagged_variant - niche_variants.start) mod 2^w` and emits `bx.assume(bx.icmp(IntNE, tag, impossible))`. Live IR for `classify_middle_3niches` confirms this exact instruction at the entry of the function:
   ```llvm
   define dso_local noundef range(i8 10, 31) i8 @classify_middle_3niches(i8 noundef zeroext %x) unnamed_addr #3 {
   start:
     %0 = icmp ne i8 %x, -1
     tail call void @llvm.assume(i1 %0)
     %1 = add i8 %x, 2
     %2 = icmp ult i8 %1, 3
     %3 = mul nsw i8 %1, 10
     %4 = add nsw i8 %3, 10
     %switch.offset = select i1 %2, i8 %4, i8 20
     ret i8 %switch.offset
   }
   ```
   Here `niche_start = 254` (`-2`), so subtracting `254` mod 256 simplifies to `%1 = add i8 %x, 2`; `%2 = icmp ult i8 %1, 3` tests `rel <= 2` (`FirstNiche=254 -> 0`, dead `255 -> 1`, `SecondNiche=0 -> 2`); and `%0 = icmp ne i8 %x, -1; tail call void @llvm.assume(i1 %0)` communicates the Miri `InvalidTag(0xff)` UB rule directly to LLVM's optimizer.

For multi-niche tag decoding (`operand.rs:664-707`), `codegen_get_discr` chooses among three test forms:
- Unsigned range comparison (`ULE`/`UGE`) when `tag_range.no_unsigned_wraparound(tag_size) == Ok(true)`;
- Signed range comparison (`SLE`/`SGE`) when `tag_range.no_signed_wraparound(tag_size) == Ok(true)`;
- General wrapping modular test `icmp ule (sub tag, niche_start), relative_max` when the range is full or wraps in both signed and unsigned views (as in `OuterThreeEdge` and `OuterThreeMiddle3Niches`, where `tag_range = 1..=0` returns `Err(..)` from both `no_*_wraparound` methods).

On `x86_64-unknown-linux-gnu` at `-C opt-level=2`, LLVM lowers all three niche classifiers completely **branchlessly** (zero conditional jump instructions):

- **`classify_opt2_bool` (`rustc 1.98.0-nightly`, LLVM `22.1.6`, 6 instructions — bit-packed shift LUT):**
  ```asm
  classify_opt2_bool:
      incb    %dil             # wrapping +1: 255->0, 0->1, 1->2, 2->3
      movzbl  %dil, %ecx
      shll    $3, %ecx         # bit offset in {0, 8, 16, 24}
      movl    $50462980, %eax  # 0x03020104 = (3<<24)|(2<<16)|(1<<8)|4
      shrl    %cl, %eax        # extracts byte: 255->4, 0->1, 1->2, 2->3
      retq
  ```
- **`classify_outer_edge` (`rustc 1.102.0-nightly`, LLVM `23.1.5`, 9 instructions — bit-packed shift LUT):**
  ```asm
  classify_outer:
      leal    2(%rdi), %eax    # wraps 255->1, 0->2, 1..254->3..256
      xorl    %edx, %edx
      testb   %dil, %dil       # sets ZF/SF on signed byte
      movzbl  %al, %ecx
      cmovgl  %edx, %ecx       # collapses positive signed payloads to index 0
      shll    $3, %ecx         # bit offset in {0, 8, 16}
      movl    $1968660, %eax   # 0x001e140a = (30<<16)|(20<<8)|10
      shrl    %cl, %eax        # extracts 10 (Untagged), 20 (FirstNiche), 30 (SecondNiche)
      retq
  ```
- **`classify_outer_edge` (`rustc 1.98.0-nightly`, LLVM `22.1.6`, 9 instructions — linear wrapping arithmetic + `cmovb`):**
  ```asm
  classify_outer_edge:
      leal    1(%rdi), %eax    # wrapping +1: 255->0, 0->1, 1..254->2..255
      addl    %edi, %edi       # 2*x
      leal    (%rdi,%rdi,4), %ecx  # 10*x (mod 256: 255->246, 0->0)
      addb    $30, %cl         # 255->20, 0->30
      cmpb    $2, %al          # CF=1 iff (x + 1) mod 256 < 2 (i.e. x in {255, 0})
      movzbl  %cl, %ecx
      movl    $10, %eax
      cmovbl  %ecx, %eax       # select 20/30 if niche, else 10
      retq
  ```

Both LLVM `22.1.6` and `23.1.5` exploit the full modular wraparound identity (`(x - 255) mod 256 == (x + 1) mod 256`) to decode wrapping niches in constant time with zero branches.

### 5. `zerocopy` MIR Enum-Operation Census and Anneal Trusted Boundary Alignment

Basis: source + execution

Inspecting real `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR dumps across `zerocopy` (`google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`, crate `v0.8.64`, live on `rustc 1.98.0-nightly`, alongside the cross-revision `rustc 1.102.0-nightly` build) reveals an asymmetric operational profile:

| Crate / Configuration | Toolchain | MIR Dialect / Pass | MIR Bodies | `SetDiscriminant` Stmts | `Rvalue::Discriminant` | `Downcast` Projections | `AggregateKind::Adt` |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| `zerocopy v0.8.64` (`std+alloc+simd`) | `rustc 1.98.0-nightly` (`14210df0e`) | `Runtime(PostCleanup)` | `4,840` | **`0`** | `664` | `1,080` | `417` |
| `zerocopy v0.8.64` (`std+alloc+simd`) | `rustc 1.98.0-nightly` (`14210df0e`) | `Runtime(Optimized)` | `4,590` | **`0`** | **`1,649`** (`2.48x`) | `880` | `1,532` |
| `zerocopy v0.8.64` (default `no_std`) | `rustc 1.98.0-nightly` (`14210df0e`) | `Runtime(PostCleanup)` | `4,715` | **`0`** | `657` | `1,074` | `410` |
| `zerocopy v0.8.64` (default `no_std`) | `rustc 1.98.0-nightly` (`14210df0e`) | `Runtime(Optimized)` | `4,478` | **`0`** | **`1,642`** (`2.50x`) | `873` | `1,513` |
| `zerocopy` (cross-revision comparison) | `rustc 1.102.0-nightly` (`3ef0c22cd`) | `Runtime(PostCleanup)` | `4,663` | **`0`** | `589` | `943` | `637` |
| `zerocopy` (cross-revision comparison) | `rustc 1.102.0-nightly` (`3ef0c22cd`) | `Runtime(Optimized)` | `4,302` | **`0`** | **`1,601`** (`2.72x`) | `793` | `1,806` |
| Two-step `async fn` probe | `rustc 1.98.0-nightly` (`14210df0e`) | `Runtime(PostCleanup)` | `2` | **`3`** | `2` | `1` | `2` |

*(Note: Differences in `AggregateKind::Adt` totals between the two toolchains partly reflect crate revision drift and counting unit-variant `AggregateKind::Adt` forms vs. parenthesis/brace ADT constructors in MIR pretty-prints; `SetDiscriminant` is identically `0` in every non-coroutine `zerocopy` build even with nested-parenthesis matching `^\s*discriminant\(.+\)\s*=`.)*

Two compiler facts explain these counts directly from `rustc` primary source:
1. **Why `SetDiscriminant` is `0` in `zerocopy`:** Standard enum construction (`Option::Some(v)`, `Result::Ok(x)`, `CastError::Alignment(...)`) lowers to `Rvalue::Aggregate(AggregateKind::Adt, ...)` and stays in aggregate form through `Runtime(Optimized)` MIR. `StatementKind::SetDiscriminant` is forbidden before `MirPhase::Runtime(RuntimePhase::Initial)` (`compiler/rustc_mir_transform/src/validate.rs:312-315, 1568-1584`) and in practice is emitted primarily by coroutine lowering `StateTransform` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:359-364`), verified by our two-step `async fn` probe emitting `discriminant((*_27)) = 3;`, `discriminant((*_27)) = 1;`, and `discriminant((*_27)) = 2;`. Because `zerocopy` contains no `async`/coroutine bodies, `SetDiscriminant` count is `0`.
2. **Why `Rvalue::Discriminant` grows 2.48x–2.72x after optimization:** MIR `Inline` duplicates `Option`/`Result` combinator bodies (`unwrap`, `map`, `ok_or`, `?` desugaring) into callers (`664 -> 1,649` / `589 -> 1,601`) while `SimplifyCfg` and `ScalarReplacementOfAggregates` slightly reduce surviving `Downcast` projections (`1,080 -> 880` / `943 -> 793`).

**Implication for Anneal's Trusted Boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
- `trusted/lean/Trusted/MirAst.lean:189-271, 620-662` currently represents only **fieldless** enums via `EnumTagRepr::{zeroSized, scalar}` (corresponding strictly to `Variants::Single` and `TagEncoding::Direct`), and lowers both `Rvalue::Aggregate(AggregateKind::Adt, _)` and `StatementKind::SetDiscriminant` fail-closed to `.unsupported`.
- Consequently, to verify real `zerocopy` bodies containing `Option`/`Result`/`CastError` without losing fail-closed soundness, the primary priority is adding payload-bearing ADT enums (`TagEncoding::{Direct, Niche}`, `Rvalue::Aggregate(AggregateKind::Adt, _)`, `ProjectionElem::Downcast`, and `Rvalue::Discriminant` over `Niche`), with `StatementKind::SetDiscriminant` required once coroutine/`async` bodies or MIR deaggregation passes enter scope.
- Encouragingly, `vendor/lean-miri/Miri/Interpreter/Discriminant.lean:63-168` in the same `joshlf/anneal` commit **already models** `tagForVariant`, `readDiscriminant`, and `writeDiscriminant` for `TagEncoding::Niche`—including wrapping `BitVec` subtraction `bits - nicheStart` (line `141`), dead-middle-slot rejection `if index == untagged then ub "InvalidTag(untagged variant encoded in niche)"` (line `149`), `validRange.contains` checks (lines `148, 153`), the CTFE pointer-nullability check (lines `132-137`), and `writeDiscriminant`'s validation read throwing `InvalidNichedEnumVariantWritten` (lines `164-167`).

### 6. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization

Basis: derived (Lean 4 kernel verification)

`support/EnumNicheWrappingAndSetDiscriminant.lean` (1,261 lines) constructively formalizes the full wrapping-niche ABI and operational/codegen discriminant semantics for arbitrary bit width `w : Nat` (`modulus w = 2^w`) using only Lean 4 `Init` (zero external dependencies) and passing:

```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/EnumNicheWrappingAndSetDiscriminant.lean
```

with exit code `0`, zero warnings, zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, and zero `._unsafe_rec`.

#### Core Mechanized Definitions
- **Modular arithmetic (`Section 1`):** `modulus w := 2 ^ w`, `wrapAdd w a b := (a + b) % modulus w`, `wrapSub w a b := (a % modulus w + (modulus w - b % modulus w)) % modulus w`, with proved bijective cancellation laws `wrapSub_wrapAdd_cancel`, `wrapAdd_wrapSub_cancel`, `wrapSub_eq_zero_iff`, `wrapAdd_injective`, `wrapAdd_assoc`, and `wrapSub_arc`.
- **`WrappingRange w` (`Section 2`):** Mirrors `wrapping_range.rs` (`contains`, `isFull`, `validCount`, `availableNiches`), proves modular-distance containment (`contains_iff_wrapSub_le`) and the exact conservation law (`validCount_add_availableNiches : r.validCount + r.availableNiches = modulus w`), and implements both `Niche::reserve` directions (`reserveFromEnd` and `reserveFromStart`) with complete geometric soundness specs (`reserveFromEnd_spec`, `reserveFromStart_spec`).
- **`NicheLayout w` & Operations (`Section 3`):** Carries `numVariants`, `validPayloadRange`, `untaggedVariant`, `nicheVariantsStart`, `nicheVariantsEnd`, `nicheStart`, and `tagValidRange`, together with `WellFormed` (constructively produced by `mkFromReserveEnd` / `mkFromReserveStart`), `encodeVariantTag`, `decodeNicheTag`, `evalSetDiscriminant` (Miri operational semantics with validation read), and `evalCodegenSetDiscr` (codegen no-op for `untaggedVariant`).

#### Proved Theorems and Kernel Axiom Audit

| Theorem Name | Mathematical / Semantic Guarantee | `#print axioms` |
| :--- | :--- | :--- |
| `WrappingRange.validCount_add_availableNiches` | `r.validCount + r.availableNiches = 2^w` for every in-bounds `WrappingRange w`. | `[propext]` |
| `NicheLayout.encode_decode_niched_roundtrip` | Every niched variant `v` encodes to `some tag` (`tag < 2^w`) with `decodeNicheTag tag = .ok v`. | `[propext]` |
| `NicheLayout.decode_untagged_payload_roundtrip` | Every valid payload bit-pattern `p` (`validPayloadRange.contains p = true`) decodes to `.ok untaggedVariant`. | `[propext]` |
| `NicheLayout.decode_ok_iff_encoded_or_payload` | Exact bijection: `decodeNicheTag tag = .ok v ↔ (v = untagged ∧ payloadValid tag) ∨ (isNiched v ∧ encodeVariantTag v = some tag)`. | `[propext]` |
| `NicheLayout.encodeVariantTag_injective` | Distinct niched variants never collide modulo `2^w`. | `[propext]` |
| `NicheLayout.dead_middle_slot_triggers_invalid_tag` | Whenever `nicheVariantsStart ≤ untagged ≤ nicheVariantsEnd`, the skipped slot `wrapAdd w nicheStart (untagged - nicheVariantsStart)` satisfies `tagValidRange.contains = true` yet ALWAYS yields `.ubInvalidTag`. | `[propext]` |
| `NicheLayout.niche_capacity_iff` / `niche_capacity_start_iff` | Necessary-and-sufficient capacity: `reserveFromEnd`/`reserveFromStart` succeeds iff `vEnd - vStart + 1 ≤ availableNiches`. | `[propext]` |
| `NicheLayout.edge_vs_interior_required_niches` | For any `n ≥ 3`: edge untagged (`0` or `n - 1`) requires `n - 1` niches; interior untagged (`0 < u < n - 1`) requires `n` niches. | `[propext]` |
| `NicheLayout.three_variant_two_niche_dichotomy` | When `availableNiches = 2` and `numVariants = 3`, niche filling succeeds iff `untagged = 0 ∨ untagged = 2` (explaining `1 B` edge vs. `2 B` middle). | `[propext]` |
| `NicheLayout.payload_write_before_set_discriminant_sound` | Writing a valid payload `p` before `evalSetDiscriminant untagged` always succeeds with `.ok (.init p)` and matches `evalCodegenSetDiscr`. | `[propext]` |
| `NicheLayout.niched_set_discriminant_sound` | `evalSetDiscriminant` on any niched variant succeeds from ANY `TagSlot` (including `.uninit`) and matches `evalCodegenSetDiscr`. | `[propext]` |
| `NicheLayout.codegen_set_discr_refines_miri` | Refinement: whenever `evalSetDiscriminant L v slot = .ok nextSlot`, `evalCodegenSetDiscr L v slot = nextSlot`. | `[propext, Quot.sound]` |
| `ce1_middle_untagged_variant_exceeds_two_niche_capacity` | Sharpness witness on `Inner1To254` (`w = 8`): edge fits (`FirstNiche = 255`, `SecondNiche = 0`), middle fails (`reserveFromEnd 3 = none`, `reserveFromStart 3 = none`). | `[]` (no axioms) |
| `ce2_set_discriminant_before_payload_triggers_niched_ub` | Sharpness witness on `Option<NonZero<u8>>`: `SetDiscriminant(1)` before payload faults `.ubInvalidNichedEnumVariantWritten 1 0` (over `None`) and `.ubUninitRead` (over `.uninit`) while `evalCodegenSetDiscr` is a no-op and payload-first returns `.ok (.init 7)`. | `[]` (no axioms) |
| `ce3_unassigned_niche_hole_triggers_invalid_tag_ub` | Sharpness witness for BOTH `InvalidTag` paths: `Option<bool>` byte `3` (outside `tagValidRange`) AND `OuterThreeMiddle3Niches` byte `255` (inside full `tagValidRange` yet colliding with `untagged = 1`). | `[]` (no axioms) |

## Boundaries

- **Pointer provenance and CTFE non-integer niche reads (`not examined` in Lean model; `source`-audited in `rustc` and `lean-miri`):** `support/EnumNicheWrappingAndSetDiscriminant.lean` models integer bit-pattern tags on $[0, 2^w)$ and does not formalize Miri's abstract provenance (`AllocId`) or `scalar_may_be_null` pointer-niche branch (`discriminant.rs:149-161`, `vendor/lean-miri/Miri/Interpreter/Discriminant.lean:132-137`). Empirical pointer-niche layout checks (`Option<&u32>`, `Result<&u32, ()>`, `Option<Option<&u32>>`, `Option<&[u32]>`) were executed on `x86_64-unknown-linux-gnu`.
- **Multi-field payload packing around a niche (`try_fit_variants_around_niche_tag`, `not examined` empirically):** When non-untagged variants carry non-ZST fields, `enum_layout.rs:480-520` attempts to place those fields before `niche.offset` or aligned after `niche.offset + niche_size` inside `largest_variant.size` and degrades their `backend_repr` to `BackendRepr::Memory`. The live probe tested ZST non-untagged variants (`FirstNiche`, `SecondNiche`, `None`, `Err(())`); non-ZST payload shifting around an interior niche offset was audited in source (`enum_layout.rs:480-520`) but not probed empirically or mechanized in Lean.
- **Uninhabited variants inside `niche_variants` (`not examined` empirically):** By `enum_layout.rs:604-605`, uninhabited variants (`absent(&variants[index])`) do not extend `niche_variants` at the ends, though an uninhabited variant declared strictly between two inhabited niched variants still consumes a slot inside `niche_variants` and triggers `UninhabitedEnumVariantRead` (`discriminant.rs:214-216`) / `UninhabitedEnumVariantWritten` (`discriminant.rs:256-258`). This case is documented from primary source, not probed in `support/probe_niche_layout_and_set_discriminant.py`.
- **`#[repr(C)]`, `#[repr(int)]`, and explicit non-sequential discriminants (`known not to apply` to `TagEncoding::Niche`):** As established by `enum_layout.rs:569` (`repr.inhibit_enum_layout_opt()`) and `invariant.rs:313-316`, these enums cannot use `TagEncoding::Niche` and always use `TagEncoding::Direct` (empirically confirmed by `OuterExplicitReprU8` having `size_of == 2` B).
- **Non-`x86_64` architectures and big-endian targets (`not examined` empirically):** All disassembly and live `rustc`/`Miri` measurements targeted `x86_64-unknown-linux-gnu`. While `rustc_abi`'s `WrappingRange` and `NicheLayout` arithmetic is endianness-independent at the scalar-value level, byte-offset layout of multi-byte tags and ARM64/RISC-V branchless lowering were not measured.
- **`Trusted.MirAst` support for niched enums (`unsupported` in `joshlf/anneal@c131b320e`):** `Trusted.MirAst` intentionally rejects payload-bearing enums, `AggregateKind::Adt`, and `SetDiscriminant` as `.unsupported`. Nothing in this report implies that `joshlf/anneal` currently verifies niched enums end-to-end; rather, this report supplies the exact specification and Lean mechanization needed to extend `Trusted.MirSemantics` safely.
- **Generalizability of `zerocopy`'s `0` `SetDiscriminant` count (`known not to apply` to `async`/coroutine crates):** The `0` `SetDiscriminant` measurement holds for `zerocopy` because `zerocopy` contains no coroutines/`async fn` bodies. As proved by the `async fn two_step` probe (`3` `SetDiscriminant` statements), crates using `async`/generators DO emit `StatementKind::SetDiscriminant` in `Runtime(PostCleanup)` MIR.
- **Stronger conclusion NOT established (`unknown` / `known not to apply`):** Passing native `-C opt-level=2` tests—even with identical emitted assembly—never establishes absence of `SetDiscriminant` write-order UB or `InvalidTag` UB; conversely, `codegen_set_discr_refines_miri` proves only forward refinement on Miri-valid executions, not that LLVM will preserve arbitrary UB executions.

## Evidence

### Primary Upstream Source Citations

All commits below were resolved and inspected directly on GitHub:

1. **`rust-lang/rust` @ `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (2026-11-20; byte-for-byte identical in `enum_layout.rs`, `discriminant.rs`, and `place.rs` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, 2026-11-11):**
   - `compiler/rustc_abi/src/wrapping_range.rs:19-63, 112-145, 169-211` — `WrappingRange`, `contains`, `is_full_for`, `no_unsigned_wraparound`, `no_signed_wraparound`, `smallest_range_containing`.
   - `compiler/rustc_abi/src/lib.rs:2074-2218` — `TagEncoding::{Direct, Niche}`, `Niche::{from_scalar, available, reserve}`, `NicheOptimizations` (`UnsafeCell` / `UnsafePinned` suppression).
   - `compiler/rustc_abi/src/layout/enum_layout.rs:15-58, 480-556, 558-664` — `layout_of_enum` size/niche tie-breaker, `try_fit_variants_around_niche_tag`, `calculate_niche_abi`, `calculate_niche_filling_layout` (`largest_variant_index`, contiguous `niche_variants`, `count`, `niche.reserve`).
   - `compiler/rustc_ty_utils/src/layout/invariant.rs:300-318` — `layout_sanity_check` enforcing `niche_start <= unsigned_int_max`, inhabited-variant coverage, and `discriminant == variant_index`.
   - `compiler/rustc_const_eval/src/interpret/discriminant.rs:20-46, 53-218, 247-327` — `write_discriminant` (validation read throwing `InvalidNichedEnumVariantWritten`), `read_discriminant` (`TagEncoding::Niche` pointer path, wrapping `BinOp::Sub`, `variant_index == untagged_variant` -> `InvalidTag`, `valid_range.contains` -> `InvalidTag`), `tag_for_variant` (wrapping `BinOp::Add`).
   - `compiler/rustc_middle/src/mir/interpret/error.rs:393, 418, 590, 625-630` — `InvalidTag` and `InvalidNichedEnumVariantWritten` error definitions and diagnostic text.
   - `compiler/rustc_codegen_ssa/src/mir/statement.rs:70-72` — `StatementKind::SetDiscriminant` dispatch to `codegen_set_discr`.
   - `compiler/rustc_codegen_ssa/src/mir/place.rs:262-279, 482-538` — `codegen_set_discr` (`Ok(None) => {}` no-op for `untagged_variant`) and `codegen_tag_value` (u128 wrapping add + bitmask).
   - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:743-752` & `compiler/rustc_codegen_ssa/src/mir/operand.rs:470-718` — `codegen_get_discr`, interior-untagged `bx.assume(ne)` (lines `606-615`), and unsigned/signed/wrapping tag comparisons (lines `664-707`).
   - `compiler/rustc_codegen_llvm/src/builder.rs:738-790, 862-874` — `scalar_load_metadata` and `range_metadata` emitting `[start, end.wrapping_add(1))`.
   - `compiler/rustc_codegen_llvm/src/abi.rs:683-698` — `apply_range_attr` emitting LLVM parameter/return `range(...)` attributes.
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs:359-364` & `compiler/rustc_mir_transform/src/validate.rs:312-315, 1568-1584` — coroutine `StateTransform` emission of `SetDiscriminant` and MIR phase gate (`MirPhase::Runtime(RuntimePhase::Initial)`).
2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, 2026-05-31):**
   - `compiler/rustc_abi/src/layout.rs:574-743` — pre-split `calculate_niche_filling_layout` closure (semantically identical to `enum_layout.rs:558-664`).
   - `compiler/rustc_abi/src/lib.rs:2011-2090` — `impl Niche` (`available`, `reserve`).
3. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (2026-11-19):**
   - `trusted/lean/Trusted/MirAst.lean:189-271, 620-662` — fieldless `EnumTagRepr` / `EnumTy`; `SetDiscriminant` and `AggregateKind::Adt` fail-closed to `.unsupported`.
   - `vendor/lean-miri/Miri/Interpreter/Discriminant.lean:63-168` — `tagForVariant`, `readDiscriminant`, `writeDiscriminant` matching `rustc_const_eval/src/interpret/discriminant.rs`.
4. **`google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0` (`zerocopy v0.8.64`, 2026-11-21):**
   - Live MIR dump census (`-Zdump-mir="runtime-post-cleanup | runtime-optimized"`) over `zerocopy/src/lib.rs`.
5. **`leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
   - Standalone kernel verification of `support/EnumNicheWrappingAndSetDiscriminant.lean`.

### Preserved Support Artifacts

All evidence artifacts live in `support/` within this package (paths scrubbed of any local filesystem details):

1. **`support/probe_niche_layout_and_set_discriminant.py`:** Standalone Python 3.10+ probe that invokes real `rustc`, builds an offline `no_std` core-only Miri sysroot directly from `rust-src` (`-Zalways-encode-mir`), runs native `-C opt-level=2` and Miri `-C opt-level=0` differential checks for Parts A and B, extracts `-Zprint-type-sizes`, LLVM IR (`!range`, `range(...)`, `llvm.assume`), and x86-64 disassembly, verifies instruction-for-instruction parity across valid and reordered `SetDiscriminant` binaries, runs the `async fn` `SetDiscriminant` MIR probe, and optionally scans a `zerocopy` crate checkout (`--zerocopy-src`).
2. **`support/probe_results.json`:** Complete sanitized execution record acquired on `2026-11-21` using `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `LLVM 22.1.6` / `Miri` on `x86_64-unknown-linux-gnu` against `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`, recording exact sizes, raw byte encodings, `-Zprint-type-sizes` outputs, LLVM IR functions and metadata nodes, x86-64 assembly, Miri UB diagnostics, `async fn` `SetDiscriminant` lines, and `zerocopy` MIR census tables.
3. **`support/EnumNicheWrappingAndSetDiscriminant.lean`:** 1,261-line self-contained Lean 4 (`v4.34.1`) formalization proving all modular arithmetic laws, `WrappingRange` conservation and `move_end`/`move_start` reservation specs, bijective encode/decode round-trip, dead-middle-slot `InvalidTag` theorem, general edge-vs.-interior capacity dichotomy, payload-before-`SetDiscriminant` operational soundness, `codegen_set_discr` refinement, and 3 constructive sharpness counterexamples (`ce1`, `ce2`, `ce3`) with zero `Classical.choice`, zero `sorryAx`, and zero `Lean.ofReduceBool`.

### Key Excerpts from Live Execution (`support/probe_results.json`, 2026-11-21)

- **Layout & raw bytes (`OuterThreeEdge` vs. `OuterThreeMiddle` vs. `OuterThreeMiddle3Niches`):**
  - `OuterThreeEdge`: `size = 1 B`, `align = 1 B`, `FirstNiche = 255`, `UntaggedPayload(V1) = 1`, `UntaggedPayload(V254) = 254`, `SecondNiche = 0`, `classifications = [10, 20, 30]`.
  - `OuterThreeMiddle`: `size = 2 B`, `align = 1 B`, `print-type-size`: `discriminant: 1 bytes`, `variant UntaggedPayload: 1 bytes`.
  - `OuterThreeMiddle3Niches`: `size = 1 B`, `FirstNiche = 254`, `UntaggedPayload(V1..=V253) = 1..=253`, `SecondNiche = 0`, `dead_middle_niche_byte = 255` (`0xff`).
  - `Option<Option<bool>>`: `size = 1 B`, `Some(Some(false)) = 0`, `Some(Some(true)) = 1`, `Some(None) = 2`, `None = 255` (`range(i8 -1, 3)`).
  - `Option<&u32>` and `Result<&u32, ()>`: `size = 8 B`, `align = 8 B`, `None = 0usize`, `Err(()) = 0usize`; `Option<Option<&u32>> = 16 B`; `Option<UnsafeCell<bool>> = 2 B`.
- **Differential `Miri` vs. Native `-O2` UB matrix:**
  - `valid_payload_before_set_discriminant`: `native_opt2_rc = 0` (`OK:7`), `miri_opt0_rc = 0`, `asm = ["movl %edi, %eax", "retq"]`.
  - `reordered_set_discriminant_before_payload_over_none_ub`: `native_opt2_rc = 0` (`OK:7`), `miri_opt0_rc = 1` (`InvalidNichedEnumVariantWritten`), `asm = ["movl %edi, %eax", "retq"]`.
  - `reordered_set_discriminant_before_payload_over_uninit_ub`: `native_opt2_rc = 0` (`OK:7`), `miri_opt0_rc = 1` (`using uninitialized data`), `asm = ["movl %edi, %eax", "retq"]`.
  - `option_bool_byte3_niche_hole_ub`: `native_opt2_rc = 0` (`TAG:1`), `miri_opt0_rc = 1` (`enum value has invalid tag: 0x03`).
  - `middle_3niches_dead_slot_invalid_tag_ub`: `native_opt2_rc = 0` (`TAG:20`), `miri_opt0_rc = 1` (`enum value has invalid tag: 0xff`).
- **Cross-revision LLVM `23.1.5` comparison (`rustc 1.102.0-nightly`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):**
  - Reproduced `SZ_INNER=1 SZ_EDGE=1 SZ_MIDDLE=2 SZ_OPT2_BOOL=1 EDGE_BYTES=(255, 1..254, 0) CLASS=(10, 20, 30)` with `miri_rc = 0`, branchless `shrl %cl, %eax` lookup (`$1968660 = 0x1e140a`), `InvalidNichedEnumVariantWritten` on reordered `SetDiscriminant`, `InvalidTag(0x03)` on `Option<bool>` byte `3`, and `zerocopy` counts `4,663 -> 4,302` bodies (`0` `SetDiscriminant`, `589 -> 1,601` `Rvalue::Discriminant`).

## Revalidation

Each claim class admits a fast, self-contained discriminating check:

1. **Re-run the complete `rustc` + `Miri` + LLVM IR + x86-64 disassembly probe (~15–25 s, zero network access required when `rust-src` and `miri` components are installed):**
   ```console
   python3 support/probe_niche_layout_and_set_discriminant.py --out /tmp/reval_probe.json
   ```
   To include a fresh `zerocopy` MIR enum-op census, pass `--zerocopy-src <path-to-zerocopy-crate>`:
   ```console
   python3 support/probe_niche_layout_and_set_discriminant.py \
     --zerocopy-src /path/to/zerocopy/zerocopy \
     --out /tmp/reval_probe.json
   ```
   Check in `/tmp/reval_probe.json` that:
   - `part_a_wrapping_niche_and_layout.runtime.sizes_bytes.OuterThreeEdge == 1` and `OuterThreeMiddle == 2`;
   - `part_a_wrapping_niche_and_layout.llvm_ir.classify_middle_3niches` contains `@llvm.assume`;
   - `part_b_set_discriminant_and_invalid_tag_ub.native_opt2_machine_code_identical_b1_b2a_b2b == true`, while both reordered `SetDiscriminant` cases and both `InvalidTag` cases return `miri_opt0_rc == 1` and `native_opt2_rc == 0`;
   - `part_c_mir_enum_ops.async_coroutine_probe.counts.post_cleanup.set_discriminant_stmts > 0` while `zerocopy` has `set_discriminant_stmts == 0`.
2. **Re-verify the Lean 4 (`v4.34.1`) mechanization and axioms (~3 s):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/EnumNicheWrappingAndSetDiscriminant.lean
   ```
   Confirm exit code `0` with empty output. To audit axioms across all theorems, append `#print axioms` lines to a temporary copy in `/tmp` and confirm no theorem depends on `Classical.choice`, `sorryAx`, or `Lean.ofReduceBool`.
3. **Check upstream `rustc` drift on a newer `rust-lang/rust` commit:** Diff only the four governing source regions against `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:
   - `compiler/rustc_abi/src/layout/enum_layout.rs` (`calculate_niche_filling_layout` — watch for non-contiguous niche variant tables or multi-niche support that would eliminate the `OuterThreeMiddle` size doubling);
   - `compiler/rustc_abi/src/lib.rs` (`Niche::reserve` — watch for removal of the `bool` `0..=1` guard or changes to the `count == 1` closest-to-zero policy);
   - `compiler/rustc_const_eval/src/interpret/discriminant.rs` (`write_discriminant` validation read and `read_discriminant` `InvalidTag` branches);
   - `compiler/rustc_codegen_ssa/src/mir/{place.rs,operand.rs}` (`codegen_set_discr` and `codegen_get_discr` `bx.assume`).
4. **Check Anneal TCB adoption (`joshlf/anneal`):** Inspect `trusted/lean/Trusted/MirAst.lean` (`EnumTagRepr`, `Rvalue`, `StatementKind`) against `c131b320eeeb26ef692e5afd5ec8db49ee518613` to determine whether `TagEncoding::Niche`, `AggregateKind::Adt`, `ProjectionElem::Downcast`, or `StatementKind::SetDiscriminant` have been admitted into the trusted MIR subset.
