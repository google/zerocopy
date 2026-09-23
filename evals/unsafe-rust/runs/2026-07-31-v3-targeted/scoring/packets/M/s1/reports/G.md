# Multi-release unsafe Rust source review

## Claim, snapshot, and verdicts

This review covers exactly the four exported `unsafe` free functions in the submitted `lib.rs`, with `SUPPORT.md` (cutoff 2026-07-31), `EVIDENCE.md`, and `TCB.md` controlling. A valid call is a well-typed call satisfying the function's documented `# Safety` obligations. For each API and each required release/target/profile, the soundness claim is that every valid call has defined Rust-abstract-semantics evaluation. Each stated result/post-state guarantee is a separate mandatory postcondition. This is source-level only; no compiler-binary, deployment, security, or extra robustness claim is made.

Let:

- `A = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`;
- `S = {1.80.0, 1.81.0}`;
- `C = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`;
- `L = {1.80.0, 1.80.1, 1.81.0, 1.82.0}`, `E = {1.80.0, 1.82.0}`, and `M = {1.80.1, 1.81.0}`.

Every set also quantifies over every target on which the item exists and every ordinary debug or release profile.

| API / independent claim | `Required` | Exact `Covered` | Regional and strongest verdict |
|---|---:|---:|---|
| `acknowledge` soundness | `A` | `A` | `PROVED` |
| `acknowledge` returns `()` | `A` | `A` | `PROVED` |
| `store_word` soundness | `S` | `S` | `PROVED` |
| destination receives `value` | `S` | `S` | `PROVED` |
| old `u16` is not read | `S` | `S` | `PROVED` |
| old `u16` is not dropped | `S` | `S` | `PROVED` |
| `copy_byte` soundness | `C` | `C` | `PROVED` |
| destination receives the pre-call source byte | `C` | `C` | `PROVED` |
| source byte remains unchanged | `C` | `C` | `PROVED` |
| `load_word` soundness | `L` | `E` | `PROVED` on `E`; `UNPROVED` on `M`; whole-`L` `UNPROVED` |
| returned `u32` equals the pre-call source value | `L` | `E` | `PROVED` on `E`; `UNPROVED` on `M`; whole-`L` `UNPROVED` |
| source `u32` remains unchanged | `L` | `E` | `PROVED` on `E`; `UNPROVED` on `M`; whole-`L` `UNPROVED` |

Thus the strongest combined mandatory verdict is `PROVED` independently for `acknowledge`, `store_word`, and `copy_byte`, and `UNPROVED` for `load_word`. No `UNSOUND` execution or UB-free `CONTRACT-BROKEN` witness is established.

## Derivations and obligation coverage

**`acknowledge`.** The inspected signature has no parameters and returns unit; its body is exactly `{}`. Accepted TCB entry `SEM-EMPTY-BLOCK-180-182`, restricted to this consumer, says exactly that across `A` such a body has defined evaluation and returns `()`, and that `unsafe` changes only the caller obligation. The published contract imposes no additional obligation. These facts entail both rows over all of `A`.

**`store_word`.** For each member of `S`, the corresponding versioned [`ptr::write` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) or [`ptr::write` 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) authority requires `dst` to be write-valid and properly aligned. The API's caller contract supplies both for one `u16`; the source fixes `T = u16` and calls `write(dst, value)` once. The same authorities state that `write` overwrites with the given value “without reading or dropping the old value.” Therefore the call is permitted and establishes each of the three postconditions. The two exact authority regions exhaust `S`.

**`copy_byte`.** The source fixes `T = u8`, `count = 1`. Its caller contract supplies initialized one-byte source readability, destination writability, alignment of both pointers, and non-overlap. The submitted [`copy_nonoverlapping` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html), [primitive layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout), [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8), and [`Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html) authorities establish permission, one-byte extent, copying rather than moving, destination equality, and source preservation at 1.80.0. Accepted consumer-specific `COMPAT-COPY-180-182` preserves exactly those propositions, without added preconditions, throughout `C` and all required targets/profiles. Hence all three rows are proved on `C`.

**`load_word`.** At each endpoint in `E`, the matching [`ptr::read` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) or [`ptr::read` 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) authority requires a non-ZST source to be read-valid, aligned, and initialized; the caller contract supplies those facts for the source-fixed `T = u32`. The matching endpoint [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32) and [`Copy` semantics 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), or [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32) and [`Copy` semantics 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html), combine with `read`'s “without moving” and source-unchanged guarantees to prove both postconditions.

For `M`, no submitted authority applies and no accepted TCB entry transfers either endpoint's `ptr::read`, `u32: Copy`, or `Copy` propositions. Similar source and endpoint documentation cannot propagate guarantees forward or backward. The smallest missing premise is the same safety and behavior contract, including applicable `u32` copy semantics, for each release in `M`, or an accepted compatibility proposition covering precisely those releases. All three `load_word` claims therefore remain `UNPROVED` there.

## Boundary, configuration, and evidence closure

The complete submitted source has four public unsafe free-function surfaces and no public safe functions, fields, constructors, traits/impls, macros, hidden/reexported APIs, invariant-bearing state, dependencies, generated artifacts, conditional compilation, callbacks, FFI, assembly, allocation, or concurrency. Each call is its own unsafe boundary; there are no cross-call invariants or transitions.

Configuration coverage is parametric over target and ordinary profile because the source has no configuration branch and every consumed authority/TCB proposition carries the stated target/profile applicability. Release coverage is the explicit finite partition above, not a numeric interval. No builds or tool-derived evidence were used. Regions outside each API's `Required`, nonordinary profiles/flags, binaries/backends, and releases after the cutoff are excluded rather than inferred unsupported by the project.

## TCB audit log and findings

TCB identity is the exact submitted `TCB.md`. Trust policy admits only versioned Rust authorities listed in `EVIDENCE.md` and the two human-accepted `OUT-OF-BAND` entries. `SEM-EMPTY-BLOCK-180-182` is consumed only by `acknowledge`; `COMPAT-COPY-180-182` only by `copy_byte`. Their quantification, exclusions, consumers, and source/support-change re-audit triggers were checked. No entry is transferred to `store_word` or `load_word`; no new premise is admitted.

`F-LOAD-MIDDLE` (`UNPROVED`) is the only verdict-affecting finding: it affects soundness and both postconditions for `load_word` on `M`; there is no admissible release-applicable semantic bridge. Resolution requires the missing versioned authorities or authorized narrowly scoped compatibility entry, followed by re-review.

`F-PROOF-DOC` is non-verdict documentation debt: the three pointer-operation `SAFETY` comments assert “exactly”/“every” precondition but omit the versioned contract clauses and resulting postconditions reconstructed above. A replacement should name the concrete type/count, enumerate the locally inherited caller facts, cite the applicable authority/TCB entry, and state the established post-state. No wording can close `load_word` on `M` without new evidence.

Re-audit on any source/signature/contract change, support-set or cutoff change, material authority change, or change to either TCB entry/disposition. Final attestation: every in-scope surface, soundness obligation, documented postcondition, release region, and consumed premise has a status; `PROVED` is asserted only on the exact covered regions relative to the stated TCB.
