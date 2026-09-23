# Unsafe Rust source review

## Claim, snapshot, and boundary

This review covers exactly the four unconditional `pub unsafe fn` items in
`lib.rs`, with `SUPPORT.md`, `EVIDENCE.md`, and accepted TCB revision `TCB.md`,
at cutoff 2026-07-31. For each item the claim is: every call satisfying its
literal `# Safety` contract has UB-free callee evaluation and establishes every
documented postcondition, for every required release, every target on which the
item exists, and every ordinary debug or release profile, relative only to the
TCB below.

The four functions are the complete exported surface. There are no safe
functions, fields, traits, macros, generated artifacts, dependencies, FFI,
stateful invariants, or conditional bodies in the submitted source. This is a
source-level Rust-semantics result, not a compiler/backend or binary theorem.

## Results

Sets below are finite sets, not intervals.

| API | `Required` | Exact `Covered` by evidence | Soundness | Documented postconditions | Strongest combined verdict over `Required` |
|---|---|---|---|---|---|
| `acknowledge` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | all `Required` | **PROVED** | No prose postcondition; signature/body return `()` is **PROVED** | **PROVED** |
| `store_word` | `{1.80.0,1.81.0}` | all `Required` | **PROVED** | stores `value`: **PROVED**; does not read old contents: **PROVED**; does not drop old contents: **PROVED** | **PROVED** |
| `copy_byte` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | all `Required` | **PROVED** | destination receives source byte: **PROVED**; source byte is preserved: **PROVED** | **PROVED** |
| `load_word` | `{1.80.0,1.80.1,1.81.0,1.82.0}` | `{1.80.0,1.82.0}` | **PROVED** on `Covered`; **UNPROVED** on `{1.80.1,1.81.0}` | returned value equals source `u32`: same regional result; source is unchanged: same regional result | **UNPROVED** |

No UB witness or UB-free postcondition refutation is established. Thus no
`UNSOUND` or `CONTRACT-BROKEN` result applies.

## Obligation ledger and derivations

### `acknowledge`

Its caller contract imposes no additional condition, and the inspected body is
exactly `{}`. Accepted `SEM-EMPTY-BLOCK-180-182` applies to precisely this
signature/body and all `Required` target/profile cases: evaluation is defined
and returns `()`. Those facts discharge soundness and the signature result
without transferring the entry to another API.

### `store_word`

For each required release, the caller supplies write-validity and alignment for
one `u16`. The exact [1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.write.html)
and [1.81.0](https://doc.rust-lang.org/1.81.0/std/ptr/fn.write.html) contracts
require exactly write-validity and alignment. Substitution of `T=u16` therefore
discharges the sole `ptr::write(dst, value)` call. Each page also states that
`write` overwrites with the supplied value without reading or dropping the old
contents, proving all three postconditions. No compatibility premise is used.

### `copy_byte`

The caller provides read-valid, initialized `src`, write-valid `dst`, alignment
of both, and nonoverlap of the one-byte regions. The
[1.80.0 operation contract](https://doc.rust-lang.org/1.80.0/std/ptr/fn.copy_nonoverlapping.html)
requires those region properties for `count * size_of::<T>()`; the
[layout axiom](https://doc.rust-lang.org/1.80.0/reference/type-layout.html#primitive-data-layout)
gives `size_of::<u8>()=1`. The [implementation fact](https://doc.rust-lang.org/1.80.0/std/primitive.u8.html#impl-Copy-for-u8)
and [Copy semantics](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html)
establish ordinary bitwise duplication rather than ownership transfer.
Accepted `COMPAT-COPY-180-182` preserves exactly these safety and result
propositions over every `Required` release/target/profile. With source
`T=u8,count=1`, the call is defined, writes the source byte to `dst`, and leaves
the source byte unchanged.

### `load_word`

At each covered endpoint, the caller's read-validity, alignment, and initialized
`u32` facts exactly discharge the [1.80.0](https://doc.rust-lang.org/1.80.0/std/ptr/fn.read.html)
or [1.82.0](https://doc.rust-lang.org/1.82.0/std/ptr/fn.read.html) `ptr::read`
contract. Those pages say the value is read without moving and source memory is
unchanged. Endpoint-specific `u32: Copy` evidence
([1.80.0](https://doc.rust-lang.org/1.80.0/std/primitive.u32.html#impl-Copy-for-u32),
[1.82.0](https://doc.rust-lang.org/1.82.0/std/primitive.u32.html#impl-Copy-for-u32))
and Copy semantics
([1.80.0](https://doc.rust-lang.org/1.80.0/std/marker/trait.Copy.html),
[1.82.0](https://doc.rust-lang.org/1.82.0/std/marker/trait.Copy.html)) permit the
returned duplicate and original source value to remain usable.

For 1.80.1 and 1.81.0, the smallest missing implication is: the endpoint
`ptr::read` safety/effect propositions and `u32: Copy` semantics apply without
weaker guarantees or added preconditions. No submitted authority or accepted
TCB entry supplies it; later evidence cannot propagate backward and 1.80.0
evidence cannot propagate forward unaided. Soundness and both postconditions
therefore remain `UNPROVED`.

## Configuration closure and TCB log

Release is the only evidence-sensitive axis. Target/profile coverage is
parametric because each consumed authority or TCB proposition has the stated
all-targets-where-present and ordinary-profile applicability, and source
selection does not vary. The table exhaustively partitions every required
finite release set. No builds or tool-derived evidence were used.

| Entry | Disposition and exact consumers |
|---|---|
| Versioned Rust/std pages listed above | authoritative, claim-specific axioms only in their stated release regions |
| `SEM-EMPTY-BLOCK-180-182` | accepted OUT-OF-BAND proposition; only `acknowledge` |
| `COMPAT-COPY-180-182` | accepted OUT-OF-BAND compatibility proposition; only `copy_byte` |

There are no other admitted premises. The TCB entries do not assume an in-scope
conclusion: local source facts connect each narrow proposition to its consumer.

## Proof-artifact findings and residual scope

The caller-facing safety clauses are sufficient where evidence covers them.
The three pointer-operation `SAFETY` comments state call-precondition transfer
but omit the material result derivations and release applicability reconstructed
above; `acknowledge` states its contract outside a conventional `# Safety`
section. These are documentation deficiencies, not implementation defects in
proved regions. Suitable adjacent result text is, respectively: `write`
overwrites without reading/dropping; the one-`u8` copy copies one byte and,
because `u8: Copy`, preserves source ownership; `read` returns a `u32` copy and
leaves source unchanged. No comment can close `load_word`'s middle releases
without new admissible evidence.

Residual scope is exactly `load_word` on 1.80.1 and 1.81.0, plus all binary,
backend, nonordinary-profile, and unlisted-release claims. Re-audit on any
source/contract change, support-set expansion, changed cited documentation,
TCB disposition/scope change, or addition of configuration-dependent code.
