# Multi-release unsafe API source audit

## Claim, snapshot, and result

This review covers exactly the four exported `unsafe fn`s in `lib.rs`, at the
2026-07-31 cutoff. For each API independently, the soundness claim is: every
call satisfying its documented caller obligations has defined source-level Rust
evaluation. The postcondition claim is each behavioral promise stated in that
API's documentation. `Required` is the API-specific finite release set in
`SUPPORT.md`; it is not an interval. In every listed release the target domain
is every target on which the item exists and every ordinary debug or release
profile. There are no dependencies, generated artifacts, conditional source,
or additional configuration axes in the submitted snapshot. Compiler/backend
correctness and binary behavior are excluded.

| API | Required | Covered by admissible evidence | Soundness | Documented postconditions | Strongest combined verdict over Required |
|---|---|---|---|---|---|
| `acknowledge` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | same as Required | **PROVED** throughout | No behavioral postcondition is documented; the signature-level return of `()` is also **PROVED** throughout | **PROVED** |
| `store_word` | `{1.80.0, 1.81.0}` | same as Required | **PROVED** throughout | Stores `value` at `dst`: **PROVED**; does not read the old `u16`: **PROVED**; does not drop the old `u16`: **PROVED**, all throughout | **PROVED** |
| `copy_byte` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | same as Required | **PROVED** throughout | Destination becomes the source byte: **PROVED**; source byte is preserved: **PROVED**, all throughout | **PROVED** |
| `load_word` | `{1.80.0, 1.80.1, 1.81.0, 1.82.0}` | `{1.80.0, 1.82.0}` | **PROVED** on Covered; **UNPROVED** on `{1.80.1, 1.81.0}` | Returned `u32` equals the initialized source value: **PROVED** on Covered and **UNPROVED** on the remainder; source is unchanged: the same regional result | **UNPROVED** |

No valid UB witness or UB-free postcondition refutation is established. Thus no
regional result is `UNSOUND` or `CONTRACT-BROKEN`.

## Obligation derivations

### `acknowledge`

The local body is exactly `{}`, with zero parameters and unit return, and the
documentation imposes no additional safety requirement. Accepted
`SEM-EMPTY-BLOCK-180-182` states, for every release, target, and profile in
Required, that this exact form has defined evaluation and returns `()`; making
the function unsafe changes only the static call obligation. The body/signature
facts therefore instantiate that entry over all of Required. The TCB entry is
not used by any other API.

### `store_word`

The only unsafe operation is `ptr::write(dst, value)`. For both required
releases, the submitted version-matched [`write` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html)
and [`write` 1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html)
contracts require `dst` to be properly aligned and valid for writes; these are
exactly the public caller obligations. The well-typed `value: u16` supplies the
value being written. The same version-matched descriptions establish overwrite
without reading or dropping the old value. Hence soundness and every listed
effect are covered in both required releases without a compatibility premise.

### `copy_byte`

The source fixes `T = u8` and `count = 1`. Its caller contract supplies a
readable initialized source `u8`, a writable destination `u8`, alignment of
both, and nonoverlap of the one-byte regions. The submitted 1.80.0
[`copy_nonoverlapping`](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html),
[primitive layout](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout),
[`u8: Copy`](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8),
and [`Copy` semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html)
establish the base safety requirements, one-byte size, copying effect, and
non-moving source preservation. Accepted `COMPAT-COPY-180-182` preserves those
exact propositions across every release, target, and profile in Required.
Together with the local fixed type/count and caller clauses, this proves both
soundness and both postconditions throughout Required. The entry expressly
cannot support `ptr::read`, `ptr::write`, or another API.

### `load_word`

At 1.80.0 and 1.82.0, the version-matched [`read` 1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html)
and [`read` 1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html)
contracts require a readable, aligned, properly initialized non-ZST source;
the public caller contract supplies those facts for one `u32`. The respective
[`u32: Copy` 1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32)
and [`Copy` semantics 1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html),
and the corresponding [`u32: Copy` 1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32)
and [`Copy` semantics 1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html),
combine with each `read` description to establish the returned value and
unchanged source at those endpoints.

For 1.80.1 and 1.81.0, the packet supplies neither version-applicable `read` and
`Copy` authorities nor an accepted compatibility proposition. Later 1.82.0
text cannot establish earlier semantics, and 1.80.0 text cannot be propagated
forward without an admitted compatibility premise. `COMPAT-COPY-180-182` is
operation-specific and explicitly excludes `ptr::read`. The smallest missing
implication is that, in each uncovered release and full target/profile domain,
the documented caller facts satisfy `ptr::read`'s safety contract and the call
returns the source `u32` while leaving the source unchanged. Absence of that
premise makes both regional claims `UNPROVED`; it is not evidence of UB.

## TCB, proof artifacts, and maintenance

The complete non-authoritative TCB is the two accepted entries in `TCB.md`:
`SEM-EMPTY-BLOCK-180-182`, consumed only by `acknowledge`, and
`COMPAT-COPY-180-182`, consumed only by `copy_byte`. All `write`, `read`, layout,
and `Copy` facts above are claim- and release-specific submitted Rust authority;
none is transferred to a different operation or release.

The API safety contracts are sufficient for the proved regions. The terse
`SAFETY` comments do not themselves record the material release-applicability
derivations reconstructed above, especially the `copy_byte` compatibility
bridge and the endpoint-only `load_word` proof. This is proof-documentation
debt, not a contrary implementation verdict. A replacement comment should cite
the exact local type/count and caller clauses plus the applicable authority/TCB
entry; no comment can close `load_word`'s two missing release premises.

Re-audit is required upon any source/signature/contract change, change to a
Required set or target/profile policy, change or withdrawal of either accepted
TCB entry, or material change to a consumed versioned authority. To obtain a
full `load_word` verdict, submit applicable authority for 1.80.1 and 1.81.0 or
an accepted narrowly scoped compatibility premise covering the exact missing
propositions.
