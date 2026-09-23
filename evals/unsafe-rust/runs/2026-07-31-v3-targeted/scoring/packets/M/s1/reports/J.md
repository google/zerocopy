# Unsafe Rust source audit: four exported APIs

## Claim, snapshot, and result

This review covers exactly the submitted `lib.rs`, its four exported unsafe functions, the contracts in that file, the finite policies in `SUPPORT.md`, and the submitted evidence/TCB packet. Audit cutoff: 2026-07-31. There is no generated code, conditional compilation, dependency, safe wrapper, trait, field, macro, FFI, concurrency, allocator, or other API surface in the submitted source. No binary/backend claim is made.

For API `f`, let `D(V) = V × {every target on which f exists} × {ordinary debug, ordinary release}`. The theorem is: every call satisfying `f`'s documented caller obligations has defined callee evaluation under documented Rust abstract semantics and establishes each listed postcondition. The exact target/profile quantifiers come directly from `SUPPORT.md`; copying each explicitly declared finite release set into `D` is an equality, not interval inference.

**Strongest four-API result: UNPROVED.** `acknowledge`, `store_word`, and `copy_byte` are fully **PROVED** relative to the accepted submitted TCB. `load_word` is regionally proved but its full required claim is **UNPROVED**. No `UNSOUND` or `CONTRACT-BROKEN` witness is established.

| API | Required releases | Soundness | Documented postconditions (separate results) | Strongest combined verdict |
|---|---|---|---|---|
| `acknowledge` | `A={1.80.0,1.80.1,1.81.0,1.82.0}` | **PROVED**, `Covered=A` | No prose postcondition; its signature-level `()` return is **PROVED**, `Covered=A` | **PROVED** over `D(A)` |
| `store_word` | `S={1.80.0,1.81.0}` | **PROVED**, `Covered=S` | destination stores `value`: **PROVED**, `Covered=S`; old `u16` is not read: **PROVED**, `Covered=S`; old `u16` is not dropped: **PROVED**, `Covered=S` | **PROVED** over `D(S)` |
| `copy_byte` | `C={1.80.0,1.80.1,1.81.0,1.82.0}` | **PROVED**, `Covered=C` | destination receives the pre-call source byte: **PROVED**, `Covered=C`; source byte is preserved: **PROVED**, `Covered=C` | **PROVED** over `D(C)` |
| `load_word` | `L={1.80.0,1.80.1,1.81.0,1.82.0}` | **PROVED** on `E={1.80.0,1.82.0}`; **UNPROVED** on `M={1.80.1,1.81.0}`; aggregate `Covered=E` | returned value equals the initialized source `u32`: same regional results; source is unchanged: same regional results | **UNPROVED** over `D(L)` |

For each proved claim, all required obligations have the displayed same release coverage, so their pointwise intersection is that `Covered`; equality with the relevant required set proves `Required ⊆ Covered`. For `load_word`, `E ⊂ L`, so closure fails.

## Obligation proofs

**ACK-SOUND/RET.** The inspected body is exactly `{}`, has no operation or state transition, and matches the signature covered by accepted `SEM-EMPTY-BLOCK-180-182`. That entry parametrically guarantees defined evaluation and return of `()` for every case in `D(A)`. There are no caller safety preconditions or other postconditions.

**STORE-SOUND/VALUE/NOREAD/NODROP.** The caller contract supplies an aligned `dst` valid to write one `u16`; these are exactly the safety clauses of [`ptr::write` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html) and [`ptr::write` 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html), independently verified for their respective singleton cases. The call uses that `dst` and passed `value`. Each page says the operation overwrites the location with the value without reading or dropping the old value. The exhaustive union of the two singleton lemmas is `S`.

**COPY-SOUND/DEST/SOURCE.** The call fixes `T=u8,count=1`. The caller contract supplies source/destination validity, initialization, alignment, and non-overlap. The verified 1.80 authorities establish the matching [`copy_nonoverlapping`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html) clauses, [`size_of::<u8>()=1`](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout), [`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8), and [bitwise `Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html). Accepted `COMPAT-COPY-180-182` preserves exactly the defined-call, one-byte destination-copy, source-preservation, size, and `Copy` propositions over every case in `D(C)`. Its consumer restriction is obeyed.

**LOAD-SOUND/RETURN/SOURCE.** At 1.80.0 and 1.82.0, the caller's aligned/readable/initialized `src` exactly discharges the independently verified [`ptr::read` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html) and [`ptr::read` 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) safety clauses. Those pages establish return of the read value and unchanged source. The corresponding [`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32), [`Copy` semantics 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html), [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32), and [`Copy` semantics 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html) establish that retaining and returning the duplicate `u32` preserves ownership validity. These are endpoint lemmas only.

## Finding LOAD-GAP — missing interior-release applicability

- **Status:** `UNPROVED`; implementation and both postconditions on `D(M)`.
- **Smallest missing premise:** for each `v∈M`, under the documented pointer conditions, this exact `ptr::read::<u32>` call is defined, returns the source value, leaves the source unchanged, and `u32` has the required `Copy` semantics.
- **Why unresolved:** the submitted pages apply only to 1.80.0 and 1.82.0. An audit cutoff and endpoint agreement do not establish semantic continuity. `TCB.md` supplies no `load_word` compatibility entry, and operation-specific evidence may not be transferred.
- **Certificate check:** no valid in-scope execution with a proved false safety proposition or UB consequence exists in the packet; no UB-free falsifying execution exists. Therefore neither `UNSOUND` nor `CONTRACT-BROKEN` applies.
- **Resolution:** provide applicable authorities for both interior releases or accept an exact proposition-preserving compatibility premise covering them, then re-audit all three obligations.

## TCB, proof artifacts, and residual scope

TCB identity is the exact submitted `TCB.md`. Its only non-authoritative entries are accepted `SEM-EMPTY-BLOCK-180-182` (consumed only by ACK-SOUND/RET) and accepted `COMPAT-COPY-180-182` (consumed only by COPY-SOUND/DEST/SOURCE). Their identities, scopes, limitations, consumers, and triggers were checked. All eleven submitted official pages were opened at their exact versioned URLs and their stated propositions verified. No tool-derived theorem or additional premise is consumed.

**Proof-documentation finding:** implementation proofs above reconstruct facts absent from the adjacent comments. `acknowledge` should place its no-requirements contract under `# Safety`. The three pointer comments identify caller-side preconditions but omit resulting facts and version applicability; `copy_byte` especially omits the `u8/count/size/Copy` bridge, and `load_word` omits the `u32: Copy` bridge. This does not weaken proved implementation regions, but the proof artifacts are deficient. Add the corresponding compact derivations above; no wording change can repair `LOAD-GAP` without new evidence.

Excluded: releases outside the explicit sets, nonordinary profiles, targets where an item does not exist, backend/binary correctness, and properties not documented or requested. Re-audit on any source/signature/contract change, support-set or configuration change, authoritative-page change, or change/disposition change to either consumed TCB entry.
