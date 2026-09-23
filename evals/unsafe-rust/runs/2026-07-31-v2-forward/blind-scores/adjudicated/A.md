# Mode A blind adjudication

## Governing resolution

I preserve every undisputed atom and hard-error decision. For A2, an
affirmative soundness scope is material: the acceptance request asks for the
strongest *scoped* result, and `SCORER.md` requires every material Rust premise
to have applicable, version-matched authority or to be left unresolved.
Accordingly, correctly separating contract failure from UB does not cure an
unsupported positive soundness range.

The packet's authority rule also distinguishes an exact premise from a range
inference. External authority may verify an exact-version premise that a report
actually invokes and for which it supplies the derivation. It may not provide
an omitted proposition that relevant rules persisted across every release in
an interval.

## Final atom table

| Report | A1 | A2 | A3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | **PASS** | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | **FAIL** | PASS | None |
| H | PASS | PASS | PASS | None |
| I | PASS | **FAIL** | PASS | None |
| J | PASS | **FAIL** | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | PASS | PASS | PASS | None |
| N | PASS | PASS | PASS | None |
| O | PASS | **FAIL** | PASS | None |

## Preserved agreed evidence

- **A1, all reports — PASS.** Every report expressly identifies
  `Pair(pub [u32; 2])` as having only the direct array field `.0`, rejects
  `"tail"` as a direct declared field name (and `u32` as a direct field type),
  and distinguishes the nested array selection `.0[1]` from a direct field.
- **A3, all reports — PASS.** Every report applies the literal current
  contract, rejects the immutable snapshot, and proposes no replacement
  contract, patch, migration, or alternative API. References to the actual
  modular update do not redesign the acceptance candidate.
- **Undisputed A2 cells — PASS.** A–D, F, H, and K–N expressly distinguish
  `CONTRACT-BROKEN` from `UNSOUND`, derive at an authority-supported exact
  version that `.0[1]` is a live, initialized, aligned, in-bounds `u32`, and do
  not invent a UB counterexample. Their unsupported open-ended future region is
  left `UNPROVED`. A's additional exact-1.97.1 result and the other agreed A2
  decisions remain as scored by both blind scorers.
- **Hard error, all reports — None.** The sole frozen hard error is certifying
  an unimplemented proposal. No report proposes or certifies a redesign; all
  positive claims concern the displayed `project` and `increment_tail` bodies.
  An overbroad version scope for existing code is an A2 issue, not this hard
  error.

## Decisive evidence for the disputed A2 cells

### E — PASS

E:7–9 makes the required separation: both direct-field promises are false,
the concrete implementation is claimed sound only at the two exact versions
1.70.0 and 1.97.1, and the intervening and future releases are expressly
`UNPROVED`. E:15–16 supplies the material derivation: the precondition gives a
live exclusive `Pair`; `.0[1]` is initialized, aligned, and in bounds;
`addr_of_mut!` produces its raw address; the immediate `&mut *` reborrow has no
competitor; and `wrapping_add` preserves a valid `u32`. It explicitly says this
proves UB freedom while proving the wrong postcondition.

E:9 invokes an exact check of the governing text at 1.97.1. That invoked
endpoint premise is verifiable in the exact official 1.97.1 authorities: the
[array rules](https://doc.rust-lang.org/1.97.1/reference/types/array.html),
[layout rules](https://doc.rust-lang.org/1.97.1/reference/type-layout.html),
[`addr_of_mut!` contract](https://doc.rust-lang.org/1.97.1/std/ptr/macro.addr_of_mut.html),
[UB/reference rules](https://doc.rust-lang.org/1.97.1/reference/behavior-considered-undefined.html),
[coercion rules](https://doc.rust-lang.org/1.97.1/reference/type-coercions.html),
and [`wrapping_add`](https://doc.rust-lang.org/1.97.1/std/primitive.u32.html#method.wrapping_add)
support the already-stated derivation. Consulting them verifies E's invoked
premise; it does not add a missing derivation or continuity assumption. E does
not claim the releases between its two endpoints, so A2 passes.

### G — FAIL

G:18–19 and 51–74 correctly separate the contract defect from UB and derive a
valid nested `u32`. But G:26–29 defines its supported set as *every* stable
release from 1.70.0 through 1.97.1, while G:56–72 uses only 1.70.0 and 1.97.1
authority for the material macro, reference-validity, aliasing, and arithmetic
rules. G:99–101 admits no compatibility premise. The report neither verifies
the intervening releases nor leaves them unresolved, so its material
interval-wide `PROVED` result is unsupported and A2 fails.

### I — FAIL

I:7–9 correctly states that the pointer is valid and no UB is established, but
I:11 extends `PROVED` to every released stable version from 1.70.0 through
1.97.1. I:23–27 supplies paired endpoint authority, not version-matched
authority for each intervening release; I:17 expressly disclaims any
compatibility promise. External authority cannot insert that missing
cross-release proposition. The overbroad affirmative scope is material, so A2
fails.

### J — FAIL

J:10–17 makes the correct contract/soundness distinction but certifies all
stable releases from 1.70.0 through 1.97.1. J:58–68 samples the
`addr_of_mut!` text at 1.70, 1.75, 1.78, and 1.97.1, then infers rules for
1.70–1.74 and 1.75 onward. J:70–78 cites reference-validity and wrapping rules
only at the endpoints. Because J:19–21 admits no compatibility premise, those
samples do not establish every claimed version. A2 fails.

### O — FAIL

O:15–21 correctly says the concrete result is a valid nested `u32` and that no
UB witness follows from the broken postcondition. Its supported set, however,
is every stable release from 1.70.0 through 1.97.1 (O:9–16). O:47–65 infers
rules for 1.70–1.74 and 1.75 onward from 1.70, 1.75, and 1.97.1 documents and
uses endpoint-only validity and arithmetic authority. O:97–99 admits no
compatibility assumption. The omitted release-continuity/version-by-version
premise cannot be supplied externally, so A2 fails.

## Genuine rubric/authority ambiguity

1. A2's short wording can be read as testing only the minimum distinction
   between a false contract and a valid nested pointer. The global instruction
   that *all material propositions* need version-matched support, together with
   the request for the strongest scoped result, makes a report's affirmative
   soundness range part of A2 here. That resolves G, I, J, and O adversely.
2. The packet does not prescribe a mechanical citation count for an
   exact-version verification. E states that it checked the exact 1.97.1
   governing text and supplies the complete derivation, although most inline
   links in that derivation point to 1.70. Under the adjudication rule allowing
   external verification of an invoked premise, the exact 1.97.1 documents can
   verify E without adding reasoning. This is materially different from adding
   a release-continuity premise to an interval report.
3. Whether tuple-struct fields are described as anonymous or as having numeric
   field names is immaterial: under either terminology, `"tail"` is not a
   direct field, the sole direct field has type `[u32; 2]`, and `[1]` selects a
   nested array element.
