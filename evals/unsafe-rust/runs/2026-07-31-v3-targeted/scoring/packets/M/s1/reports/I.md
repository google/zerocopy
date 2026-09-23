# Multi-release source-only unsafe Rust audit

## Claim, snapshot, and boundary

Artifact: the submitted `lib.rs`, `SUPPORT.md`, `EVIDENCE.md`, and `TCB.md`; audit cutoff 2026-07-31. For each exported unsafe function independently, the claim is: for every listed Rust release, every target on which the item exists, every ordinary debug/release profile, and every call satisfying its documented safety contract, evaluating the exact body is free of Rust undefined behavior and establishes each stated postcondition, relative only to the accepted TCB below.

The complete reachable surface is four stateless exported unsafe functions: `acknowledge`, `store_word`, `copy_byte`, and `load_word`. There are no exported safe wrappers, fields, constructors, traits/impls, macros, generated artifacts, `cfg` branches, dependencies, callbacks, or invariant-bearing state in the submitted source. Thus target and profile are parametric axes: the source operation does not vary, and each proof below covers every such case to which its cited premise applies. This is a Rust source-semantics result, not a compiler-backend or binary theorem.

`SUPPORT.md` directly defines explicit finite sets, so no interval normalization is used:

- `V_ack = V_copy = V_load = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`.
- `V_store = {1.80.0, 1.81.0}`.

For each claim, `Required = V_api × targets-where-item-exists × {ordinary-debug, ordinary-release}`. No release may be inferred between submitted evidence points.

## Verdict summary

| API | Soundness | Documented postconditions, separately | Aggregate `Covered` | Strongest combined verdict |
|---|---|---|---|---|
| `acknowledge` | **PROVED** on `V_ack` | returns `()`: **PROVED** on `V_ack` (there is no additional prose postcondition) | `Required_ack` | **PROVED**, relative to `SEM-EMPTY-BLOCK-180-182` |
| `store_word` | **PROVED** on `V_store` | stores `value` at `dst`: **PROVED**; does not read the old `u16`: **PROVED**; does not drop the old `u16`: **PROVED**, each on `V_store` | `Required_store` | **PROVED** |
| `copy_byte` | **PROVED** on `V_copy` | copies exactly the source byte to `dst`: **PROVED**; leaves the source byte unchanged: **PROVED**, each on `V_copy` | `Required_copy` | **PROVED**, relative to `COMPAT-COPY-180-182` |
| `load_word` | **PROVED** on `{1.80.0,1.82.0}`; **UNPROVED** on `{1.80.1,1.81.0}` | returns the initialized source `u32`: same regional result; leaves source unchanged: same regional result | `{1.80.0,1.82.0} × targets × profiles` | **UNPROVED** over `Required_load` |

The combined mandatory result for all four APIs is **UNPROVED**, solely because `Required_load ⊄ Covered_load`. No submitted fact proves an in-scope UB execution or a UB-free postcondition counterexample, so neither `UNSOUND` nor `CONTRACT-BROKEN` is certified.

## Obligation proofs

**`acknowledge`.** Its contract imposes no additional caller condition; inspection establishes a zero-parameter, unit-returning function with body exactly `{}`. Accepted `SEM-EMPTY-BLOCK-180-182` states parametrically over every `v ∈ V_ack`, relevant target, and ordinary profile that such a well-typed call has defined callee evaluation and returns `()`, and that `unsafe` changes only the static caller obligation. These facts prove both obligations and `Required_ack ⊆ Covered_ack`.

**`store_word`.** At each member of `V_store`, the applicable [`ptr::write` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and [`ptr::write` 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) contracts require `dst` to be valid for writes and aligned and say that the given value overwrites the location without reading or dropping the old value. The API contract supplies validity for one `u16` and alignment; `value: u16` is supplied by value; the body performs exactly `write(dst, value)`. Therefore soundness and all three postconditions hold in each release case. The two singleton cases exhaust `V_store`, hence their union is `Covered_store = Required_store`.

**`copy_byte`.** The body instantiates `copy_nonoverlapping` with `T=u8,count=1`. The contract supplies readable initialized source, writable destination, both alignments, and non-overlap of the one-byte regions. The accepted compatibility entry imports, for every case in `V_copy`, the exact relevant propositions from [`copy_nonoverlapping` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html), [primitive layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout), [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8), and [`Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html): these conditions satisfy the operation contract, one byte is copied to `dst`, and the source is unchanged. Thus every obligation has `Covered = Required_copy`.

**`load_word`.** For 1.80.0, [`ptr::read`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html), [`u32: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html) apply. The corresponding [1.82.0 `read`](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html), [`u32: Copy`](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` semantics](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) apply at 1.82.0. At each endpoint, the caller supplies readable, aligned, initialized `u32` storage; `read(src)` therefore is defined, returns its value, and leaves the source unchanged, with copying rather than ownership-moving semantics. No authority or accepted compatibility premise applies those propositions to 1.80.1 or 1.81.0. Endpoint agreement cannot cover the interior. The smallest missing propositions are the same `ptr::read`, `u32: Copy`, and Copy-semantic guarantees for both middle releases.

## TCB, findings, and maintenance

TCB identity: submitted `TCB.md`. Both entries are human-accepted and narrowly consumed:

- `SEM-EMPTY-BLOCK-180-182`: only the empty-body evaluation and unit return used by `acknowledge`.
- `COMPAT-COPY-180-182`: only the enumerated one-byte `copy_nonoverlapping` safety and postcondition propositions used by `copy_byte`.

They are not transferred to `store_word` or `load_word`. There is no tool-derived or test evidence and no other admitted premise.

**Finding F-LOAD-COVERAGE (UNPROVED; evidence/domain closure).** Affects soundness and both postconditions of `load_word` on 1.80.1 and 1.81.0. This is not an established implementation defect: the packet lacks the applicability bridge required for those releases. Resolution requires exact applicable authorities for both releases or an accepted proposition-preserving compatibility entry covering precisely the missing operations and release region. Re-audit on any source/contract/support-set change, either TCB disposition change, or material change to a consumed versioned authority.

Residual scope: compiler implementation, code generation, binaries, nonordinary profiles, targets where an item does not exist, and Rust releases outside the explicit finite sets are excluded.
