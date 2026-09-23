# Source-only audit of four exported unsafe APIs

## Claim, snapshot, and domain

Snapshot: the submitted `lib.rs`, `SUPPORT.md`, `EVIDENCE.md`, and `TCB.md`, audited at the support cutoff 2026-07-31. Scope is source-level Rust abstract-semantics soundness plus every documented postcondition of `acknowledge`, `store_word`, `copy_byte`, and `load_word`. A valid use satisfies the API's documented safety clauses. No backend/binary claim is made. No build, execution, expansion, generated artifact, dependency, or prior result is used.

Let `D={ordinary-debug, ordinary-release}` and `C_A(V)={(v,t,p) | v in V, A exists on target t, p in D}`. `SUPPORT.md` explicitly defines finite sets, so no interval inference is involved:

- `Required_ack=C_ack({1.80.0,1.80.1,1.81.0,1.82.0})`.
- `Required_store=C_store({1.80.0,1.81.0})`.
- `Required_copy=C_copy({1.80.0,1.80.1,1.81.0,1.82.0})`.
- `Required_load=C_load({1.80.0,1.80.1,1.81.0,1.82.0})`.

This is an exact normalization of each controlling expression: membership is listed explicitly and `SUPPORT.md` excludes every other release. The source has no `cfg`, feature, profile branch, macro, FFI, concurrency, allocator, or generated code. Thus target/profile coverage is parametric wherever the cited source-level contract or accepted TCB entry covers a release; only release applicability partitions the claims.

## Results

| API | Soundness | Documented postconditions, separately | Aggregate `Covered` | Strongest combined verdict |
|---|---|---|---|---|
| `acknowledge` | **PROVED** on `Required_ack` | returns `()`: **PROVED** on `Required_ack` | `Required_ack` | **PROVED** relative to `SEM-EMPTY-BLOCK-180-182` |
| `store_word` | **PROVED** on `Required_store` | (1) stores `value` at `dst`; (2) does not read the old `u16`; (3) does not drop it: each **PROVED** on `Required_store` | `Required_store` | **PROVED** |
| `copy_byte` | **PROVED** on `Required_copy` | (1) destination receives the pre-call source byte; (2) source byte remains unchanged: each **PROVED** on `Required_copy` | `Required_copy` | **PROVED** relative to `COMPAT-COPY-180-182` |
| `load_word` | **PROVED** on `C_load({1.80.0,1.82.0})`; **UNPROVED** on `C_load({1.80.1,1.81.0})` | (1) returns the pre-call initialized `u32`; (2) source remains unchanged: each has the same regional split | `C_load({1.80.0,1.82.0})` | **UNPROVED** over `Required_load` |

The strongest combined packet verdict is **UNPROVED** because `Required_load` is not contained in its aggregate `Covered`. No existential UB or UB-free postcondition counterexample is established, so neither `UNSOUND` nor `CONTRACT-BROKEN` applies.

## Obligation ledger and derivations

**ACK-S/P.** The body is syntactically exactly `{}` and the signature has no parameters and unit return. Accepted entry `SEM-EMPTY-BLOCK-180-182` states, for every required release/target/profile case, that such a body has defined evaluation and returns `()`, and that `unsafe` changes only the caller obligation. The documentation imposes no additional caller requirement. This proves soundness and the unit result; full-set closure is immediate.

**STORE-S.** At both required releases the call is exactly `ptr::write::<u16>(dst,value)`. The caller contract supplies `dst` valid for writes of one `u16` and properly aligned, exactly the two safety clauses on the [1.80.0 contract](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and independently on the [1.81.0 contract](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html): “valid for writes” and “properly aligned.” Therefore each executed unsafe operation meets its applicable contract. **STORE-P1/P2/P3.** Each page says the operation overwrites with the given value “without reading or dropping the old value.” This directly entails all three postconditions. The exhaustive release partition `{1.80.0} union {1.81.0}` equals `V_store`.

**COPY-S.** The local facts are `T=u8`, `count=1`, and exactly the documented source/destination alignment, access, initialization, and non-overlap obligations. The [1.80.0 operation contract](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html) requires read/write validity, alignment, and non-overlap for `count*size_of::<T>()`; [primitive layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout) gives `size_of::<u8>()=1`. The stronger initialized-source clause is sufficient. This closes 1.80.0. Accepted `COMPAT-COPY-180-182` preserves these exact premises and the operation's satisfaction for every required release/target/profile case. **COPY-P1/P2.** The operation copies the one byte. [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8) and the [Copy contract](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html)—“always a simple bit-wise copy”—permit both resulting values; the accepted entry explicitly preserves destination equality and unchanged source throughout `V_copy`. Hence each obligation covers all `Required_copy`.

**LOAD-S.** For release 1.80.0, the exact `ptr::read::<u32>` call receives the three facts required by the [1.80.0 contract](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html): readable, aligned, and properly initialized. The same derivation independently uses the [1.82.0 contract](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) at 1.82.0. **LOAD-P1/P2.** Both pages state that `read` reads without moving and leaves source memory unchanged. The endpoint [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), [Copy 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [Copy 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) establish safe coexistence and value preservation at those endpoints. No authority or accepted TCB proposition covers 1.80.1 or 1.81.0. Endpoint samples do not cover the intervening members, and `COMPAT-COPY-180-182` expressly excludes `ptr::read`. The smallest missing proposition is preservation, at 1.80.1 and 1.81.0, of the cited `ptr::read` safety and return/source guarantees plus `u32: Copy` semantics.

## Boundary, TCB, findings, and maintenance

The complete public surface in `lib.rs` is the four unsafe free functions; there are no safe wrappers, public fields, traits/impls, callbacks, hidden items, reexports, macros, representation invariants, or later unsafe consumers. Each caller-facing safety contract is sufficient for the covered regions. The short local `SAFETY` comments correctly identify the callee-contract handoff; release applicability is supplied by this evidence packet.

TCB revision is the submitted `TCB.md`: `SEM-EMPTY-BLOCK-180-182` (accepted OUT-OF-BAND semantics; consumer only ACK-S/P) and `COMPAT-COPY-180-182` (accepted OUT-OF-BAND compatibility; consumers only COPY-S/P). Their exact identities, scope, exclusions, disposition, and triggers were checked; neither is transferred to another operation. All other consumed premises are the exact versioned official pages cited above. No tool-derived evidence or dependency trust is consumed.

**Finding LOAD-COVERAGE (UNPROVED):** affects soundness and both postconditions only for `load_word` on releases 1.80.1 and 1.81.0, across every required target/profile. Resolution requires exact applicable authorities for those releases or a newly authorized, narrowly scoped compatibility premise proving the missing propositions. Re-audit all four claims if source/contracts or support sets change; re-audit consumers if either accepted entry or cited authority changes. Overall closure remains unavailable until `Required_load subseteq Covered_load` is established.

All in-scope obligations have a disposition; every affirmative result above is relative only to the stated authorities and accepted TCB entries.
