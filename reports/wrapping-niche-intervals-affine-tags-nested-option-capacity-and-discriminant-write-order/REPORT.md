# Wrapping niche intervals, affine tags, nested `Option` capacity, and discriminant write order (`Toy.WrapNiche`)

Lean `leanprover/lean4:v4.34.1`, core Lean and `Std`, no Mathlib. Lake project in `lean/` (one library, `Toy`; namespace `Toy.WrapNiche`). Every Lean statement below is quoted verbatim from the sources with a `file:line` citation; proofs are elided. All 22 results, their auxiliary lemmas, definition examples, counterexamples, non-vacuity witnesses and positive controls are proved and kernel-checked; there is no `sorry`, and concrete instances are checked by `decide` or `decide +kernel` (no `Lean.ofReduceBool`).

## Summary

This package is a toy model of niche-encoded enums: a niche field `Fin M`, wrapping intervals of field values, the affine tag formula and its one-subtraction decoder, interval hulls and contiguous tag capacity, adjacent reservation for nested `Option`, and a byte-level operational semantics of `SetDiscriminant`. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's enum layout computation, its generated code, its interpreter, MiniRust or LLVM.

One sentence per result, each with its hypotheses (identifiers are defined under Findings, Definitions; truncated `Nat` subtraction and floor modulo are named where a result relies on them):

- **R1.1** `mem_iff_offset_le_offset` (characterization, T0): For every M, every wrapping interval [s, e] of Fin M (membership `WrapInterval.Mem` defined by cases: s..=e if s <= e, else s..=M-1 followed by 0..=e) and every value x, x is a member iff (x - s) mod M <= (e - s) mod M, where each wrapping difference is computed in Nat as (x + (M - s)) % M (floor modulo; M - s does not truncate since s < M); there is no hypothesis (for M = 0, Fin 0 is empty and the statement is vacuous).
- **R1.2** `compl_mem_iff_not_mem_of_size_lt` (theorem, T0): For a wrapping interval [s, e] of Fin M that is not full (hypothesis: its size ((e - s) mod M) + 1 is less than M), the wrapping interval [e + 1, s - 1] (both ends computed with wrapping arithmetic) contains exactly the non-members of [s, e].
- **R1.3** `originTest_exactFor_iff_offset_le` (characterization, T0): For every origin o and wrapping interval [s, e] of Fin M, the conjunctive comparison test `originTest o` ('offset(o, s) <= offset(o, x) <= offset(o, e)', offsets being wrapping distances from o) agrees with membership for every x iff (s - o) mod M <= (e - o) mod M, i.e. iff the interval does not wrap past o. Origin 0 is the unsigned test s <= x <= e (`unsignedTest_iff_originTest_zero`, every M); for M = 256, origin 128 is the signed test on i8 readings (`signedTestI8_iff_originTest_128`, proved for M = 256; other widths are not stated).
- **R1.4** `not_exactFor_originTest_wrapSub_one_of_two_le` (impossibility, T0): For M >= 2 and every origin o of Fin M, the conjunctive fixed-origin comparison test `originTest o` ('offset(o, s) <= offset(o, x) <= offset(o, e)') is not exact for the two-element wrapping interval [o - 1, o] (o - 1 computed with wrapping arithmetic); hence for M >= 2 no single fixed origin makes this conjunctive test exact for every interval.
- **R2.1** `affineLayout_eq_nicheLayoutK_affineTags` (theorem, T1): For every payload validity set V on n-byte patterns and every affine encoding A (relative index r <= span gets tag (nicheStart + r) mod 256^n), the layout `affineLayout V A`, whose decoder performs one wrapping subtraction rel = (x - nicheStart) mod 256^n and returns relative index rel if rel <= span (else the payload if valid), is equal, as a layout, to the imported lookup layout `nicheLayoutK V (affineTags A)`; there is no hypothesis (when tags collide, both decoders return the least matching relative index).
- **R2.2** `affineLayout_lawful_iff_span_lt_and_tagsDisjoint` (characterization, T1): For every payload validity set V on n-byte patterns and every affine encoding A, the dead-slot-free single-subtraction layout `affineLayout V A` satisfies both round-trip laws (`DecEnc` and `Canonical`) iff span < 256^n and each of the span + 1 tags (nicheStart + r) mod 256^n, r <= span, is invalid for V.
- **R2.3** `classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint` (theorem, T1): For an enum shape E, an affine encoding A over Fin M with span < M, every tag of the niche range invalid for V (hypotheses), and every field value x (`classify` puts x into one of four classes: `liveTag` or `deadTag` if x lies in the tag interval, according to whether the variant index first + offset(nicheStart, x) of its slot is live, and otherwise `valid` or `unusedNiche` according to whether V x holds): x is classified `valid` iff V x holds; the single-subtraction decoder `decodeIdx` returns the untagged variant u on `valid` and on `unusedNiche` values; on the tag of relative index r <= span it returns first + r (whether that index is live, u, or uninhabited), the tag lying in the tag interval; and every value classified `liveTag` or `deadTag` is the tag of some relative index r <= span, on which `decodeIdx` returns first + r.
- **R2.4** `genLayout_dec_isSome_iff_classify_of_span_lt` (characterization, T1): For an enum shape E, an affine encoding A on n-byte patterns with span < 256^n (hypothesis), a payload validity set V and every field value x (`classify` puts x into one of four classes: `liveTag` or `deadTag` if x lies in the tag interval, according to whether the variant index first + offset(nicheStart, x) of its slot is live, and otherwise `valid` or `unusedNiche` according to whether V x holds), the checked decoder of `genLayout E A V` accepts x iff x is classified `valid` or `liveTag`; values at dead slots and unused niches are rejected.
- **R2.5** `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange` (theorem, T1): For an enum shape E (k variants, untagged variant u, inhabitedness flags; every variant other than u is dataless), an affine encoding A on n-byte patterns and a payload validity set V: if span < 256^n, every tag of the niche range is invalid for V, and every live variant (inhabited, other than u, index < k) lies in [first, first + span], then `genLayout E A V` satisfies both round-trip laws, even when the niche range contains u or uninhabited variants (dead slots).
- **R3.1** `exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull` (characterization, T1): For a validity set V on Fin M with at least one valid value and an interval hull H of V (a smallest wrapping interval containing every valid value), and every span: some placement of span + 1 contiguous tags ns, ..., ns + span (wrapping) avoids every valid value iff span + 1 <= M - H.size (H.size <= M, so this subtraction does not truncate).
- **R3.2** `sub_size_le_nichesCount_and_eq_iff_of_covers` (theorem, T0): For a validity set V on Fin M and every wrapping interval H that covers V (every valid value is a member of H; H need not be smallest), the number M - H.size of values outside H (H.size <= M, so no truncation) is at most the number of invalid values of V (for M = 256^n this count is the imported `numInvalid`, the unconstrained capacity, by `nichesCount_eq_numInvalid`), with equality iff every member of H is valid.
- **R3.3** `nichesCount_intervalV` (theorem, T0): For every wrapping interval I of Fin M, the validity set `intervalV I` whose valid values are exactly the members of I has M - I.size invalid values (I.size <= M, so no truncation).
- **R4.1** `exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq` (characterization, T1): For a validity set V on Fin M with at least one valid value, an interval hull H of V, k >= 2, and exactly k - 1 values outside H (M - H.size = k - 1; under k >= 2 the truncated subtraction k - 1 does not truncate), and for every natural number u: some start ns makes the naturalSpan k u + 1 contiguous tags ns, ..., ns + naturalSpan k u (wrapping) all invalid for V iff u = 0 or u = k - 1. Here naturalSpan k u = naturalLast k u - naturalFirst u; for u < k it is the span of the smallest index range containing every index of 0..k-1 other than u (`naturalFirst_naturalLast_spec`), i.e. of the niche range when the k - 1 variants other than u all need a tag.
- **R4.2** `rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid` (theorem, T1): For the rotated encoding (variant i gets tag ns + `rotIdx k u i`, where `rotIdx k u i` = (i - (u + 1)) mod k is computed in Nat as (i + k - (u + 1) % k) % k with floor modulo, the subtraction not truncating since (u + 1) % k < k, so the variants after u come first), with u < k, k <= M + 1, and V invalid at the rotated tag ns + r (wrapping addition) for each of the exactly k - 1 indices r with r + 1 < k (`RotTagsInvalid V k ns`; for k = 1 there is no such index and this hypothesis holds trivially): the rotated decoder `rotDecodeIdx` (one wrapping subtraction rel = (x - ns) mod M, then, if rel + 1 < k, the extra modular step (rel + u + 1) mod k, else u) recovers every variant i < k, i != u, from its rotated tag, and decodes every valid value to u.
- **R5.1** `extend_spec_of_size_lt` (theorem, T0): For a non-full wrapping interval I of Fin M (hypothesis: size < M) and either side, the adjacent value (e + 1 or s - 1, wrapping) is not a member of I, the extended interval contains exactly the members of I and that value, and its size is I.size + 1; this holds at the wrap point (for example [250, 255] extends upward to [250, 0], `ex_extend`).
- **R5.2** `nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt` (theorem, T1): For a non-full valid interval I of n-byte patterns (hypothesis: size < 256^n) and either side d, the one-level niche-filled Option layout that puts None on the adjacent value is lawful, and the patterns it accepts are exactly the members of `extend I d` (again a wrapping interval).
- **R5.3** `levelsReserveNiches_iff_length_le_and_nest_size` (characterization, T1): For every innermost valid interval R0 of Fin M and every list of side choices, adjacent reservation reserves an invalid value at every one of the sides.length levels iff sides.length <= M - R0.size (truncation-free since R0.size <= M), whatever sides are chosen; in that case the final valid interval has size R0.size + sides.length.
- **R5.4** `exists_lawful_extEnum_intervalV_iff_le_sub_size` (characterization, T0): For every valid interval R0 of n-byte patterns and every j, an enum with j dataless variants over the payload whose valid values are R0 has some lawful layout in the payload's n bytes (any layout, adjacent reservation or not) iff j <= 256^n - R0.size.
- **R6.1** `setDisc_operational_untagged_isSome_iff_of_tagsDisjoint` (characterization, T1): For a toy operational layout whose tags are all invalid for the niche-field validity (hypothesis): operational `SetDiscriminant u`, which reads the discriminant with the checked reader `OpLayout.readDisc` (the checked decoder of `genLayout`; for span < 256^nw it rejects dead slots and unused niches, `genLayout_dec_isSome_iff_classify_of_span_lt`) and is undefined behaviour unless the result is u, is free of undefined behaviour on a place iff the place's niche field lies inside the place (for nw >= 1; for nw = 0 there is no byte to check), is initialized, and holds a valid value; in particular, after writing a value x into a niche field that lies inside the place, it is free of undefined behaviour iff x is valid.
- **R6.2** `run_erased_eq_some_of_run_operational_eq_some` (theorem, T1): For every toy operational layout, every program of field writes, SetDiscriminant and discriminant reads, and every start state: if the program runs without undefined behaviour under the operational semantics, it produces the same place and the same read results under the erased semantics (`SetDiscriminant u` as a no-op); there is no hypothesis (in both semantics a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour).
- **R6.3** `run_write_setDisc_comm_of_disjointFromNiche` (theorem, T1): For every toy operational layout, both semantics, every variant v (including the untagged one) and every state: if the byte range of a `write` operation does not overlap the niche field (hypothesis), the programs 'write; SetDiscriminant v' and 'SetDiscriminant v; write' give the same result, undefined behaviour included (a write that does not fit in the place is undefined behaviour in both orders).
- **R6.4** `run_fields_then_setDisc_readDisc_of_disjoint` (theorem, T1): For a toy operational layout and a place, if the niche field lies inside the place, span < 256^nw, every tag is invalid for the niche-field validity, and the field writes ws lie inside the place, are pairwise disjoint and do not overlap the niche field (hypotheses), then under both semantics: for every encodable variant v other than u (`Encodable`: live and in the niche range), 'field writes; SetDiscriminant v; read discriminant' is defined, reads v, leaves v's tag in the niche field and every field write in ws readable as written; and for every valid niche value x, 'field writes; write x to the niche field; SetDiscriminant u; read discriminant' is defined, reads u, leaves x in the niche field and every field write in ws readable as written.

Non-claims: every result has non-claims (what it does not show), listed with the result under Findings and collected under Boundaries, together with the escape hatches of the impossibility result R1.4. Tightness of a hypothesis means a counterexample in a recorded witness class, not necessity in general.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

**Model fidelity.**

This package is a toy model of niche-encoded enums: a niche field `Fin M` (for a `w`-bit integer field `M = 2 ^ w`; no result needs a power of two), wrapping intervals of field values, the affine tag formula and its one-subtraction decoder, interval hulls, adjacent reservation for nested `Option`, and a byte-level operational semantics of `SetDiscriminant`. rustc, its interpreter (Miri) and MiniRust enter as `derived (modeling bridge)` prose citing documented behaviour.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's enum layout computation, its generated code, its interpreter, or MiniRust.

Rust guarantees no niche layout for enums in the default `Rust` representation. rust-lang/reference@956d1bd03d2a8934fc5041ecb04b33e55159c655 `src/type-layout.md:174-178`: "The only data layout guarantees made by this representation are those required for soundness. These are: 1. The offset of a field is divisible by that field's alignment. 2. The alignment of the type is at least the maximum alignment of its fields." (line breaks and list markup collapsed); and `src/type-layout.md:226-227`: "There are no other guarantees of data layout made by this representation." Niche-encoded layouts are therefore rustc implementation behaviour. The same section does guarantee zero size for default-representation enums with no variants (`src/type-layout.md:188-189`) and with a single variant whose fields are all zero-sized (`src/type-layout.md:194-195`); these cases lie outside the model. Layout guarantees that the standard library documents for particular `Option` types are not used or examined here.

Known model–system gaps (each a `derived (modeling bridge)` observation, not a proved relation):

- Validity is a set `V` of niche-field values; rustc describes the niche scalar's validity by a single wrapping range. The two coincide when `V` is an interval (`intervalV`).
- One niche field is modelled. Payloads with several fields (where another field's niches could be used), validity sets that are not one interval, and wrappers that hide niches are not modelled.
- `genLayout` makes every variant other than the untagged variant `u` dataless; rustc's niche-filling layout also places fields of such variants before or after the niche field (rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe `compiler/rustc_abi/src/layout.rs:652-680`). The operational model of group 6 does not tie field bytes to variants.
- Discriminants are variant indices, as rustc's layout sanity check requires for niche-encoded enums (`compiler/rustc_ty_utils/src/layout/invariant.rs:300-323` at the same commit); explicit discriminants are not modelled.
- `EnumSpec` does not require `u < k`; with `u ≥ k` every index below `k` is a candidate dataless variant (`ex_live_u_ge_k`).
- The niche field is read and written little-endian from provenance-free bytes; big-endian targets and pointer-valued niches (accepted by the interpreter in a special case, `compiler/rustc_const_eval/src/interpret/discriminant.rs:147-160`) are not modelled.
- Out-of-bounds accesses are undefined behaviour in the operational semantics (`stepOp`, `setDisc`, `OpLayout.readNiche`; for the niche-field read this holds for nw >= 1, while for nw = 0 there is no byte to check, see `OpLayout`); the byte helpers `writeBytes` and `OpLayout.writeNiche` are total, and the semantics calls them on in-bounds ranges.
- `Sem.erased` performs no check and no write for `SetDiscriminant u`, like the code generator's no-write case and like MiniRust's `SetDiscriminant` with an empty tagger; it does not model the abort that the code generator emits for an uninhabited variant (see R6.1, R6.2).

Truncating operations used in statements: `Nat` truncated subtraction (`M - H.size`, `M - I.size`, `k - 1`, `i - first`, `naturalLast k u - naturalFirst u`) and floor modulo (`%`) in `offset`, `wrapAdd`, `wrapSub`, `rotIdx`, `rotDecodeIdx`. Where a result relies on them its card names them. Degenerate edges: `M = 0` makes `Fin M` empty (statements quantifying over its values are vacuous); every wrapping interval is non-empty; the empty validity set is excluded by an explicit hypothesis where it matters; `span ≥ M` collapses the tag interval (`ex_tagInterval_collapses`); `extend` of a full interval collapses (`ex_extend_full`); `nw = 0` is a degenerate niche field (see `OpLayout`).

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std`, no Mathlib; the Lake project in `lean/` has no dependencies.

**Subjects and how they relate.** The Lean toolchain is the system that checks every proof (Basis: execution (Lean kernel check)). The rustc sources (rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe), the Rust Reference (rust-lang/reference@956d1bd03d2a8934fc5041ecb04b33e55159c655), the MiniRust specification (minirust/minirust@063d784186d3252bee242217f218223205c0b568), LLVM (llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1, tag `llvmorg-21.1.0`) and Gange et al. (2015) are the sources the toy definitions are compared with in prior-art citations and in `derived (modeling bridge)` prose. They are interpreted through the toy; no claim is made that they satisfy the theorems, and their behaviour was read from the quoted text, not executed.

**Imported declarations.** The four files `lean/Toy/WrapNiche/Imported/{Defs,Lemmas,Counting,Results}.lean` are copied, with proofs, from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants`; the 16 definitions and 6 theorems of these files that this report uses are quoted under Findings, Imported declarations, and the provenance hashes of the files are recorded under Evidence. They are cited, not counted as results of this package.

## Findings

Basis for every result below: execution (Lean kernel check). Each connection to a real system is a separate `derived (modeling bridge)` line with its reasoning.

### Imported declarations (not results of this package)

Copied with proofs from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants` (`google/zerocopy`, branch `reference`, published at commit `00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; Lean sources unchanged at the latest correction commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), directory `reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/`, namespace renamed from `Toy.Niche` to `Toy.WrapNiche.Imported`. Statements and proofs of the kept declarations are verbatim; they are cited, not counted as results here. Provenance hashes (SHA-256) are recorded under Evidence.


```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:39
abbrev Pat (n : Nat) : Type := Fin (256 ^ n)
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:41
theorem pat_card_pos (n : Nat) : 0 < 256 ^ n := …
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:59
abbrev Validity (n : Nat) : Type := Pat n → Bool
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:62
abbrev Val {n : Nat} (V : Validity n) : Type := {p : Pat n // V p = true}
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:73
def IsNiche {n : Nat} (V : Validity n) (p : Pat n) : Prop := V p = false
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:97
def numInvalid {n : Nat} (V : Validity n) : Nat := (invalidPats V).length
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:104-108
@[ext] structure Layout (α : Type) (m : Nat) where
  /-- The chosen representation of each value. -/
  enc : α → Pat m
  /-- The validity check and interpretation of a pattern. -/
  dec : Pat m → Option α
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:114
def DecEnc (L : Layout α m) : Prop := ∀ x, L.dec (L.enc x) = some x
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:118
def Canonical (L : Layout α m) : Prop := ∀ p x, L.dec p = some x → L.enc x = p
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:121
def Lawful (L : Layout α m) : Prop := DecEnc L ∧ Canonical L
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:134
abbrev ExtEnum (k : Nat) {n : Nat} (V : Validity n) : Type := Fin k ⊕ Val V
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:130
abbrev Opt {n : Nat} (V : Validity n) : Type := Option (Val V)
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:170-174
def nicheLayout (V : Validity n) (q : Pat n) : Layout (Opt V) n where
  enc
    | none => q
    | some v => v.val
  dec p := if p = q then some none else if h : V p = true then some (some ⟨p, h⟩) else none
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:210-217
def nicheLayoutK {k : Nat} (V : Validity n) (t : Fin k → Pat n) : Layout (ExtEnum k V) n where
  enc
    | .inl i => t i
    | .inr v => v.val
  dec p :=
    match (List.finRange k).find? (fun i => t i == p) with
    | some i => some (.inl i)
    | none => if h : V p = true then some (.inr ⟨p, h⟩) else none
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:221-222
def firstNiches (V : Validity n) (k : Nat) : Fin k → Pat n :=
  fun i => (invalidPats V).getD i.val (zeroPat n)
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:81
def nonZeroV (n : Nat) : Validity n := fun p => p.val != 0
```

```lean
-- lean/Toy/WrapNiche/Imported/Defs.lean:90
def allV (n : Nat) : Validity n := fun _ => true
```

```lean
-- lean/Toy/WrapNiche/Imported/Results.lean:43-44
theorem nicheLayout_lawful_iff_isNiche (V : Validity n) (q : Pat n) :
    Lawful (nicheLayout V q) ↔ IsNiche V q := by …
```

```lean
-- lean/Toy/WrapNiche/Imported/Results.lean:56-58
theorem nicheLayoutK_lawful_iff_injective_and_isNiche {k : Nat} (V : Validity n)
    (t : Fin k → Pat n) :
    Lawful (nicheLayoutK V t) ↔ (Function.Injective t ∧ ∀ i, IsNiche V (t i)) := by …
```

```lean
-- lean/Toy/WrapNiche/Imported/Results.lean:109-110
theorem le_numInvalid_of_decEnc_of_size_le {k : Nat} (V : Validity n)
    (L : Layout (ExtEnum k V) m) (hsize : m ≤ n) (hde : DecEnc L) : k ≤ numInvalid V := by …
```

```lean
-- lean/Toy/WrapNiche/Imported/Results.lean:140-143
theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
    (V : Validity n) (k : Nat) :
    (k ≤ numInvalid V ↔ ∃ L : Layout (ExtEnum k V) n, Lawful L) ∧
      (k ≤ numInvalid V ↔ Lawful (nicheLayoutK V (firstNiches V k))) := by …
```

```lean
-- lean/Toy/WrapNiche/Imported/Results.lean:156-157
theorem opt_opt_nonZero_no_decEnc_layout_in_payload_size
    (L : Layout (Option (Opt (nonZeroV n))) n) : ¬ DecEnc L := by …
```

### Definitions


#### `wrapAdd`

Wrapping addition `(x + j) mod M` (floor modulo). Examples: `ex_wrapAdd`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:29-30
def wrapAdd {M : Nat} (x : Fin M) (j : Nat) : Fin M :=
  ⟨(x.val + j) % M, Nat.mod_lt _ (pos_of_fin x)⟩
```

#### `wrapSub`

Wrapping subtraction `(x - j) mod M`. Examples: `ex_wrapSub`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:34-35
def wrapSub {M : Nat} (x : Fin M) (j : Nat) : Fin M :=
  ⟨(x.val + (M - j % M)) % M, Nat.mod_lt _ (pos_of_fin x)⟩
```

#### `offset`

Wrapping distance `(x - s) mod M`, the decoder's single subtraction. Examples: `ex_offset`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:40
def offset {M : Nat} (s x : Fin M) : Nat := (x.val + (M - s.val)) % M
```

#### `WrapInterval`

A wrapping interval `[s, e]`; every interval is non-empty and the full field is represented by every `[s, s - 1]`. Examples: `ex_mem_pos`, `ex_mem_neg`, `ex_size`, `ex_compl`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:43-48
structure WrapInterval (M : Nat) where
  /-- First value. -/
  s : Fin M
  /-- Last value. -/
  e : Fin M
deriving DecidableEq, Repr
```

#### `WrapInterval.Mem`

Semantic membership by cases (the documented reading of `WrappingRange`). Examples: `ex_mem_pos`, `ex_mem_neg`, `ex_tagInterval_collapses`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:56-57
def Mem (I : WrapInterval M) (x : Fin M) : Prop :=
  if I.s ≤ I.e then I.s ≤ x ∧ x ≤ I.e else I.s ≤ x ∨ x ≤ I.e
```

#### `WrapInterval.size`

Number of members, in `[1, M]`. Examples: `ex_size`, `ex_extend_full`, `ex_nest_past_capacity`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:63
def size (I : WrapInterval M) : Nat := offset I.s I.e + 1
```

#### `WrapInterval.compl`

`[e + 1, s - 1]`; the complement for a non-full interval (R1.2). Examples: `ex_compl`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:66
def compl (I : WrapInterval M) : WrapInterval M := ⟨wrapAdd I.e 1, wrapSub I.s 1⟩
```

#### `subTest`

Single-subtraction test. Examples: `ex_tests`, `ex_exactFor_pos`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:73-74
def subTest {M : Nat} (I : WrapInterval M) (x : Fin M) : Prop :=
  offset I.s x ≤ offset I.s I.e
```

#### `originTest`

Conjunctive fixed-origin comparison test. Examples: `ex_tests`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:80-81
def originTest {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) : Prop :=
  offset o I.s ≤ offset o x ∧ offset o x ≤ offset o I.e
```

#### `twoBranchTest`

Two-branch fixed-origin test (the comparison test, or a disjunction when the interval wraps past the origin). Examples: `ex_twoBranchTest`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:87-89
def twoBranchTest {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) : Prop :=
  if offset o I.s ≤ offset o I.e then originTest o I x
  else offset o I.s ≤ offset o x ∨ offset o x ≤ offset o I.e
```

#### `unsignedTest`

Unsigned test `s ≤ x ≤ e`. Examples: `ex_tests`, `ex_exactFor_neg`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:92-93
def unsignedTest {M : Nat} (I : WrapInterval M) (x : Fin M) : Prop :=
  I.s ≤ x ∧ x ≤ I.e
```

#### `toI8`

Two's-complement reading of an 8-bit value. Examples: `ex_toI8`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:96
def toI8 (x : Fin 256) : Int := if x.val < 128 then (x.val : Int) else (x.val : Int) - 256
```

#### `signedTestI8`

Signed `i8` test. Examples: `ex_tests`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:99-100
def signedTestI8 (I : WrapInterval 256) (x : Fin 256) : Prop :=
  toI8 I.s ≤ toI8 x ∧ toI8 x ≤ toI8 I.e
```

#### `ExactFor`

A test agrees with membership on every value. Examples: `ex_exactFor_pos`, `ex_exactFor_neg`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:116-117
def ExactFor {M : Nat} (T : WrapInterval M → Fin M → Prop) (I : WrapInterval M) : Prop :=
  ∀ x, I.Mem x ↔ T I x
```

#### `Covers`

An interval contains every valid value. Examples: `ex_covers_pos`, `ex_covers_neg`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:122-123
def Covers {M : Nat} (I : WrapInterval M) (V : Fin M → Bool) : Prop :=
  ∀ x, V x = true → I.Mem x
```

#### `IsHull`

A smallest covering interval (hulls need not be unique; for the empty validity set every singleton is a hull). Examples: `ex_isHull_pos`, `ex_isHull_neg`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:128-129
def IsHull {M : Nat} (V : Fin M → Bool) (H : WrapInterval M) : Prop :=
  Covers H V ∧ ∀ J : WrapInterval M, Covers J V → H.size ≤ J.size
```

#### `IsWrapIntervalSet`

The valid set is exactly the member set of an interval (never the empty set). Examples: `ex_isWrapIntervalSet_pos`, `ex_isWrapIntervalSet_neg`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:133-134
def IsWrapIntervalSet {M : Nat} (V : Fin M → Bool) : Prop :=
  ∃ I : WrapInterval M, ∀ x, I.Mem x ↔ V x = true
```

#### `intervalV`

The validity set of an interval. Examples: `ex_isWrapIntervalSet_pos`, `ex_intervalV`, `ex_intervalV_nonZero`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:137
def intervalV {M : Nat} (I : WrapInterval M) : Fin M → Bool := fun x => decide (I.Mem x)
```

#### `nichesCount`

Number of invalid values (the imported `numInvalid` at `M = 256 ^ n`). Examples: `ex_nichesCount`.

```lean
-- lean/Toy/WrapNiche/Interval.lean:141-142
def nichesCount {M : Nat} (V : Fin M → Bool) : Nat :=
  ((List.finRange M).filter (fun p => !V p)).length
```

#### `AffineNiche`

Affine encoding parameters `(first, span, nicheStart)`; the niche range `[first, first + span]` is never empty. Examples: `ex_tagInterval_collapses`, `ex_liveInRange_neg`, `ex_genLayout_lawful_span_eq_card`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:36-43
structure AffineNiche (M : Nat) where
  /-- Index of the first variant of the niche variant range. -/
  first : Nat
  /-- `last - first`: the range is `[first, first + span]`, with `span + 1` slots. -/
  span : Nat
  /-- Tag of variant `first`. -/
  nicheStart : Fin M
deriving DecidableEq, Repr
```

#### `AffineNiche.last`

`first + span`. Examples: `ex_affine`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:50
def last (A : AffineNiche M) : Nat := A.first + A.span
```

#### `AffineNiche.tagOf`

Tag of relative index `r`. Examples: `ex_affine`, `ex_tagInterval_collapses`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:53
def tagOf (A : AffineNiche M) (r : Nat) : Fin M := wrapAdd A.nicheStart r
```

#### `AffineNiche.tagInterval`

The tag interval; it equals the set of tags when `span < M` and collapses when `span ≥ M`. Examples: `ex_affine`, `ex_tagInterval_collapses`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:59-60
def tagInterval (A : AffineNiche M) : WrapInterval M :=
  ⟨A.nicheStart, wrapAdd A.nicheStart A.span⟩
```

#### `decodeIdx`

Index-only one-subtraction decoder. Examples: `ex_decodeIdx`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:66-67
def decodeIdx {M : Nat} (u : Nat) (A : AffineNiche M) (x : Fin M) : Nat :=
  if offset A.nicheStart x ≤ A.span then A.first + offset A.nicheStart x else u
```

#### `TagsDisjoint`

Every tag of a span is invalid (tags need not be distinct). Examples: `ex_tagsDisjoint_pos`, `ex_tagsDisjoint_neg`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:70-71
def TagsDisjoint {M : Nat} (V : Fin M → Bool) (ns : Fin M) (span : Nat) : Prop :=
  ∀ r, r ≤ span → V (wrapAdd ns r) = false
```

#### `affineTags`

Affine tag map for the imported `nicheLayoutK`. Examples: `ex_affine`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:80-81
def affineTags {M : Nat} (A : AffineNiche M) : Fin (A.span + 1) → Fin M :=
  fun r => A.tagOf r.val
```

#### `affineLayout`

Dead-slot-free one-subtraction layout of `ExtEnum (span + 1) V` (does not use `first`). Examples: `ex_affineLayout_pos`, `ex_affineLayout_neg`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:87-95
def affineLayout {n : Nat} (V : Validity n) (A : AffineNiche (256 ^ n)) :
    Layout (ExtEnum (A.span + 1) V) n where
  enc
    | .inl r => A.tagOf r.val
    | .inr v => v.val
  dec x :=
    if h : offset A.nicheStart x ≤ A.span then
      some (.inl ⟨offset A.nicheStart x, Nat.lt_succ_of_le h⟩)
    else if hv : V x = true then some (.inr ⟨x, hv⟩) else none
```

#### `EnumSpec`

Enum shape `(k, u, inh)`; `u < k` is not required. Examples: `ex_live_u_ge_k`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:103-109
structure EnumSpec where
  /-- Number of variants. -/
  k : Nat
  /-- Index of the untagged variant. -/
  u : Nat
  /-- Whether variant `i` (for `i ≠ u`) is inhabited. -/
  inh : Nat → Bool
```

#### `EnumSpec.Live`

Live variant: an inhabited variant other than `u` with index below `k` (dataless in `genLayout`). Examples: `ex_live_pos`, `ex_live_neg`, `ex_live_u_ge_k`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:112
def EnumSpec.Live (E : EnumSpec) (i : Nat) : Prop := i < E.k ∧ i ≠ E.u ∧ E.inh i = true
```

#### `LiveInRange`

Every live variant lies in the niche range. Examples: `ex_liveInRange_pos`, `ex_liveInRange_neg`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:118-119
def LiveInRange {M : Nat} (E : EnumSpec) (A : AffineNiche M) : Prop :=
  ∀ i, i < E.k → i ≠ E.u → E.inh i = true → A.first ≤ i ∧ i ≤ A.first + A.span
```

#### `GenVal`

Values of the general enum (variants other than `u` are dataless).

```lean
-- lean/Toy/WrapNiche/Affine.lean:126-127
abbrev GenVal (E : EnumSpec) {n : Nat} (V : Validity n) : Type :=
  {i : Nat // E.Live i} ⊕ Val V
```

#### `genLayout`

General affine layout with the checked decoder (dead slots allowed). Examples: `ex_genLayout_pos`, `ex_genLayout_neg`, `ex_genLayout_lawful_span_eq_card`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:133-143
def genLayout (E : EnumSpec) {n : Nat} (A : AffineNiche (256 ^ n)) (V : Validity n) :
    Layout (GenVal E V) n where
  enc
    | .inl i => A.tagOf (i.val - A.first)
    | .inr v => v.val
  dec x :=
    if offset A.nicheStart x ≤ A.span then
      if h : E.Live (A.first + offset A.nicheStart x) then
        some (.inl ⟨A.first + offset A.nicheStart x, h⟩)
      else none
    else if hv : V x = true then some (.inr ⟨x, hv⟩) else none
```

#### `FieldClass`

Four classes of field values.

```lean
-- lean/Toy/WrapNiche/Affine.lean:146-156
inductive FieldClass
  /-- Outside the tag interval and valid for the payload. -/
  | valid
  /-- In the tag interval, at the slot of a live variant. -/
  | liveTag
  /-- In the tag interval, at a dead slot (the slot of `u`, of an uninhabited variant, or of
  an index `≥ k`). -/
  | deadTag
  /-- Outside the tag interval and invalid for the payload. -/
  | unusedNiche
deriving DecidableEq, Repr
```

#### `classify`

Classification by tag-interval membership, liveness and validity. Examples: `ex_classify`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:160-164
def classify {M : Nat} (E : EnumSpec) (A : AffineNiche M) (V : Fin M → Bool) (x : Fin M) :
    FieldClass :=
  if A.tagInterval.Mem x then
    (if E.Live (A.first + offset A.nicheStart x) then .liveTag else .deadTag)
  else if V x then .valid else .unusedNiche
```

#### `naturalFirst`

First variant needing a tag (all dataless variants inhabited). Examples: `ex_naturalSpan`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:170
def naturalFirst (u : Nat) : Nat := if u = 0 then 1 else 0
```

#### `naturalLast`

Last variant needing a tag (truncated subtraction; meaningful for `k ≥ 2`). Examples: `ex_naturalSpan`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:174
def naturalLast (k u : Nat) : Nat := if u = k - 1 then k - 2 else k - 1
```

#### `naturalSpan`

Span of the natural range. Examples: `ex_naturalSpan`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:177
def naturalSpan (k u : Nat) : Nat := naturalLast k u - naturalFirst u
```

#### `rotIdx`

Rotated index (floor modulo). Examples: `ex_rotated`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:181
def rotIdx (k u i : Nat) : Nat := (i + k - (u + 1) % k) % k
```

#### `rotTag`

Rotated tag. Examples: `ex_rotated`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:184
def rotTag {M : Nat} (k u : Nat) (ns : Fin M) (i : Nat) : Fin M := wrapAdd ns (rotIdx k u i)
```

#### `rotDecodeIdx`

Rotated decoder (one extra modular step; no truncated subtraction). Examples: `ex_rotated`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:189-190
def rotDecodeIdx {M : Nat} (k u : Nat) (ns : Fin M) (x : Fin M) : Nat :=
  if offset ns x + 1 < k then (offset ns x + u + 1) % k else u
```

#### `RotTagsInvalid`

The `k - 1` rotated tags are invalid (empty for `k ≤ 1`). Examples: `ex_rotTagsInvalid_pos`, `ex_rotTagsInvalid_neg`.

```lean
-- lean/Toy/WrapNiche/Affine.lean:195-196
def RotTagsInvalid {M : Nat} (V : Fin M → Bool) (k : Nat) (ns : Fin M) : Prop :=
  ∀ r, r + 1 < k → V (wrapAdd ns r) = false
```

#### `Side`

Which end a nesting level reserves.

```lean
-- lean/Toy/WrapNiche/Nest.lean:19-24
inductive Side
  /-- Reserve `s - 1` (wrapping). -/
  | low
  /-- Reserve `e + 1` (wrapping). -/
  | high
deriving DecidableEq, Repr
```

#### `adjNiche`

Adjacent value. Examples: `ex_extend`.

```lean
-- lean/Toy/WrapNiche/Nest.lean:27-29
def adjNiche {M : Nat} (I : WrapInterval M) : Side → Fin M
  | .low => wrapSub I.s 1
  | .high => wrapAdd I.e 1
```

#### `extend`

Interval extended by its adjacent value (collapses for a full interval). Examples: `ex_extend`, `ex_extend_full`.

```lean
-- lean/Toy/WrapNiche/Nest.lean:32-34
def extend {M : Nat} (I : WrapInterval M) : Side → WrapInterval M
  | .low => ⟨wrapSub I.s 1, I.e⟩
  | .high => ⟨I.s, wrapAdd I.e 1⟩
```

#### `nest`

Iterated adjacent reservation. Examples: `ex_extend`, `ex_nest_past_capacity`.

```lean
-- lean/Toy/WrapNiche/Nest.lean:37-39
def nest {M : Nat} (I : WrapInterval M) : List Side → WrapInterval M
  | [] => I
  | d :: ds => nest (extend I d) ds
```

#### `LevelsReserveNiches`

Every level reserves an invalid value. Examples: `ex_levelsReserveNiches_pos`, `ex_levelsReserveNiches_neg`, `ex_nest_past_capacity`.

```lean
-- lean/Toy/WrapNiche/Nest.lean:44-46
def LevelsReserveNiches {M : Nat} (R₀ : WrapInterval M) (sides : List Side) : Prop :=
  ∀ j (hj : j < sides.length),
    ¬ (nest R₀ (sides.take j)).Mem (adjNiche (nest R₀ (sides.take j)) sides[j])
```

#### `Bytes`

A place: bytes without provenance, each uninitialized or holding a value.

```lean
-- lean/Toy/WrapNiche/Op.lean:35
abbrev Bytes : Type := List (Option (Fin 256))
```

#### `writeBytes`

Total byte-write helper (length-preserving; bytes past the end dropped). The semantics calls it on in-bounds ranges (an out-of-bounds write is undefined behaviour). Examples: `ex_bytes`.

```lean
-- lean/Toy/WrapNiche/Op.lean:41-43
def writeBytes (p : Bytes) (off : Nat) (bs : List (Fin 256)) : Bytes :=
  (List.range p.length).map fun i =>
    if off ≤ i ∧ i < off + bs.length then some (bs.getD (i - off) 0) else p.getD i none
```

#### `readBytes`

Byte read (`none` on uninitialized or out-of-place bytes). Examples: `ex_bytes`.

```lean
-- lean/Toy/WrapNiche/Op.lean:47-48
def readBytes (p : Bytes) (off len : Nat) : Option (List (Fin 256)) :=
  ((List.range len).map fun j => p.getD (off + j) none).mapM id
```

#### `leVal`

Little-endian value. Examples: `ex_bytes`.

```lean
-- lean/Toy/WrapNiche/Op.lean:51
def leVal (bs : List (Fin 256)) : Nat := bs.foldr (fun b acc => b.val + 256 * acc) 0
```

#### `leBytes`

Little-endian encoding. Examples: `ex_bytes`.

```lean
-- lean/Toy/WrapNiche/Op.lean:54-55
def leBytes (w x : Nat) : List (Fin 256) :=
  (List.range w).map fun j => ⟨x / 256 ^ j % 256, Nat.mod_lt _ (by decide)⟩
```

#### `OpLayout`

Operational enum layout (little-endian niche field; `nw = 0` is degenerate). Examples: `ex_readDisc_unusedNiche`.

```lean
-- lean/Toy/WrapNiche/Op.lean:62-72
structure OpLayout where
  /-- Byte offset of the niche field. -/
  no : Nat
  /-- Width of the niche field in bytes. -/
  nw : Nat
  /-- Enum shape. -/
  E : EnumSpec
  /-- Affine niche encoding. -/
  A : AffineNiche (256 ^ nw)
  /-- Validity of the niche field for the untagged variant's payload. -/
  V : Validity nw
```

#### `OpLayout.readNiche`

Read the niche field. Examples: `ex_readNiche`, `ex_setDisc_untagged_uninhabited`.

```lean
-- lean/Toy/WrapNiche/Op.lean:78-79
def readNiche (L : OpLayout) (p : Bytes) : Option (Pat L.nw) :=
  (readBytes p L.no L.nw).map fun bs => ⟨leVal bs % 256 ^ L.nw, Nat.mod_lt _ (pat_card_pos _)⟩
```

#### `OpLayout.writeNiche`

Write the niche field (helper; no bounds check).

```lean
-- lean/Toy/WrapNiche/Op.lean:82-83
def writeNiche (L : OpLayout) (p : Bytes) (x : Pat L.nw) : Bytes :=
  writeBytes p L.no (leBytes L.nw x.val)
```

#### `OpLayout.readDisc`

Checked discriminant read. Examples: `ex_readDisc`, `ex_readDisc_unusedNiche`, `ex_run`.

```lean
-- lean/Toy/WrapNiche/Op.lean:87-93
def readDisc (L : OpLayout) (p : Bytes) : Option Nat :=
  match L.readNiche p with
  | none => none
  | some x =>
    ((genLayout L.E L.A L.V).dec x).map fun
      | .inl i => i.val
      | .inr _ => L.E.u
```

#### `OpLayout.Encodable`

Live and in the niche range. Examples: `ex_encodable`.

```lean
-- lean/Toy/WrapNiche/Op.lean:97-98
def Encodable (L : OpLayout) (v : Nat) : Prop :=
  L.E.Live v ∧ L.A.first ≤ v ∧ v ≤ L.A.first + L.A.span
```

#### `OpLayout.DisjointFromNiche`

Byte range does not overlap the niche field (conservative for empty ranges). Examples: `ex_disjointFromNiche`.

```lean
-- lean/Toy/WrapNiche/Op.lean:106-107
def DisjointFromNiche (L : OpLayout) (off len : Nat) : Prop :=
  off + len ≤ L.no ∨ L.no + L.nw ≤ off
```

#### `Sem`

Operational (checks) vs erased (no check, no write) `SetDiscriminant u`.

```lean
-- lean/Toy/WrapNiche/Op.lean:115-120
inductive Sem
  /-- Checks that the place already decodes to the untagged variant. -/
  | operational
  /-- Does nothing for the untagged variant: no check and no write. -/
  | erased
deriving DecidableEq, Repr
```

#### `setDisc`

`SetDiscriminant`; undefined behaviour (`none`) for unencodable variants and for a niche field outside the place. Examples: `ex_setDisc`, `ex_setDisc_oob`, `ex_run`, `ex_setDisc_untagged_uninhabited`.

```lean
-- lean/Toy/WrapNiche/Op.lean:123-130
def setDisc (sem : Sem) (L : OpLayout) (v : Nat) (p : Bytes) : Option Bytes :=
  if v = L.E.u then
    match sem with
    | .operational => if L.readDisc p = some L.E.u then some p else none
    | .erased => some p
  else if L.Encodable v then
    if L.no + L.nw ≤ p.length then some (L.writeNiche p (L.A.tagOf (v - L.A.first))) else none
  else none
```

#### `Op`

Operations.

```lean
-- lean/Toy/WrapNiche/Op.lean:133-139
inductive Op
  /-- Write bytes at an offset (a field write). -/
  | write (off : Nat) (bs : List (Fin 256))
  /-- `SetDiscriminant v`. -/
  | setDisc (v : Nat)
  /-- Read the discriminant and append it to the output. -/
  | readDisc
```

#### `stepOp`

One step; an out-of-bounds `write` is undefined behaviour.

```lean
-- lean/Toy/WrapNiche/Op.lean:143-147
def stepOp (sem : Sem) (L : OpLayout) : Op → Bytes × List Nat → Option (Bytes × List Nat)
  | .write off bs, (p, out) =>
    if off + bs.length ≤ p.length then some (writeBytes p off bs, out) else none
  | .setDisc v, (p, out) => (setDisc sem L v p).map fun p' => (p', out)
  | .readDisc, (p, out) => (L.readDisc p).map fun i => (p, out ++ [i])
```

#### `run`

Program run. Examples: `ex_run_write_oob`, `ex_run`.

```lean
-- lean/Toy/WrapNiche/Op.lean:150-152
def run (sem : Sem) (L : OpLayout) : List Op → Bytes × List Nat → Option (Bytes × List Nat)
  | [], s => some s
  | o :: os, s => (stepOp sem L o s).bind (run sem L os)
```

#### `writesOf`

Field writes as operations.

```lean
-- lean/Toy/WrapNiche/Op.lean:155
def writesOf (ws : List (Nat × List (Fin 256))) : List Op := ws.map fun w => .write w.1 w.2
```

### Main results

Results are numbered R<group>.<item>. Group 1 (R1.1-R1.4): wrapping intervals and membership tests. Group 2 (R2.1-R2.5): the affine tag formula, its decoders and lawfulness. Group 3 (R3.1-R3.3): interval hulls, contiguous tag capacity and the niche count. Group 4 (R4.1-R4.2): the position of the untagged variant and the rotated encoding. Group 5 (R5.1-R5.4): adjacent reservation and nested `Option` capacity. Group 6 (R6.1-R6.4): the operational semantics of `SetDiscriminant` and write order.

#### R1.1 `mem_iff_offset_le_offset` (characterization, T0)

**Plain claim.** For every M, every wrapping interval [s, e] of Fin M (membership `WrapInterval.Mem` defined by cases: s..=e if s <= e, else s..=M-1 followed by 0..=e) and every value x, x is a member iff (x - s) mod M <= (e - s) mod M, where each wrapping difference is computed in Nat as (x + (M - s)) % M (floor modulo; M - s does not truncate since s < M); there is no hypothesis (for M = 0, Fin 0 is empty and the statement is vacuous).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:27-28
theorem mem_iff_offset_le_offset {M : Nat} (I : WrapInterval M) (x : Fin M) :
    I.Mem x ↔ offset I.s x ≤ offset I.s I.e := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `offset`, `WrapInterval`, `WrapInterval.Mem`.

**Tier.** T0: re-derivation; the membership test of wrapped intervals is published (Gange et al. 2015, Section 3.2) and the single-subtraction range check is textbook (Warren 2012, Section 4-1).

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: a case split on s <= e and x < s, closed by linear arithmetic.

**Non-vacuity witness.** M = 256, [255, 0], x = 0 (a wrapping interval). (`nv_mem_iff_offset_le_offset`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Membership is the model's case-split definition (`WrapInterval.Mem`); the result does not show that any compiler implements its range checks with this subtraction.
- Every `WrapInterval` is non-empty (it contains s); the empty set is not representable, so nothing is claimed about empty validity ranges.
- `offset` is computed in Nat as (x + (M - s)) % M; nothing is claimed about fixed-width machine subtraction beyond this arithmetic.

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- Henry S. Warren, Jr., Hacker's Delight, 2nd edition, Addison-Wesley, 2012, Section 4-1 "Checking Bounds of Integers": the machine-integer range check a ≤ x ≤ b as one unsigned comparison of the wrapping differences x - a and b - a (the non-wrapping case of the single-subtraction test).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:55-63 and 147-195 (source): `WrappingRange::contains` (lines 55-63, documented "Returns `true` if `v` is contained in the range.", line 55) tests membership by cases, `if self.start <= self.end { self.start <= v && v <= self.end } else { self.start <= v || v <= self.end }` (lines 58-62, line breaks collapsed) — the case split of `WrapInterval.Mem` and the two branches of `twoBranchTest` at origin 0; `smallest_range_containing` (lines 147-195) "Returns a `WrappingRange` that contains all of the values from the iterator, when they're treated as values `size` wide." (lines 147-148) by choosing the narrowest of the non-wraparound range and the wraparound candidates between consecutive sorted values (lines 176-194) — a computation of an interval hull in the sense of `IsHull`, which the toy characterizes semantically instead.
- llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1 (tag llvmorg-21.1.0) llvm/docs/LangRef.rst:7334-7371 (normative for LLVM IR), `range` metadata: "The pair ``a,b`` represents the range ``[a,b)``." (line 7346), "The range is allowed to wrap." (line 7348), and "The range should not represent the full or empty set. That is, ``a!=b``." (lines 7349-7350). LLVM ranges are half-open and a list of pairs may describe a union of ranges; the toy's intervals are inclusive single ranges like rustc's WrappingRange.
- llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1 (tag llvmorg-21.1.0) llvm/lib/IR/ConstantRange.cpp:517-524 and 1939-1945 (source): `ConstantRange::contains(const APInt &V)` tests membership in a half-open wrapping range by cases ("return Lower.ule(V) && V.ult(Upper);" when the range does not wrap, line 522, and "return Lower.ule(V) || V.ult(Upper);" otherwise, line 523); `ConstantRange::inverse()` returns "ConstantRange(Upper, Lower)" for a range that is neither full nor empty (line 1944) — the half-open counterpart of `WrapInterval.compl`.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).

**Design question.** When is a niche decoder's single wrapping subtraction exact, including intervals that wrap at the unsigned or the signed boundary?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). `WrapInterval.Mem` is compared with rustc's `WrappingRange`, documented as an inclusive wrap-around range whose `contains` uses the same two-case split (`compiler/rustc_abi/src/wrapping_range.rs:8-9` and `58-62` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe), and with the half-open wrapping ranges of LLVM's `ConstantRange::contains` (`llvm/lib/IR/ConstantRange.cpp:522-523` at llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1). The comparison reads the quoted source lines against the Lean definitions quoted under Definitions. No model–system relation is proved, so the theorem neither establishes nor refutes a property of rustc's or LLVM's range checks.

#### R1.2 `compl_mem_iff_not_mem_of_size_lt` (theorem, T0)

**Plain claim.** For a wrapping interval [s, e] of Fin M that is not full (hypothesis: its size ((e - s) mod M) + 1 is less than M), the wrapping interval [e + 1, s - 1] (both ends computed with wrapping arithmetic) contains exactly the non-members of [s, e].

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:37-38
theorem compl_mem_iff_not_mem_of_size_lt {M : Nat} (I : WrapInterval M) (hI : I.size < M)
    (x : Fin M) : I.compl.Mem x ↔ ¬ I.Mem x := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.Mem`, `WrapInterval.size`, `WrapInterval.compl`.

**Tier.** T0: re-derivation; the complement [e + 1, s - 1] of a non-full wrapped interval is published (Gange et al. 2015, Section 3.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hI : I.size < M` | Excludes the full interval, whose complement is empty and not representable; [e + 1, s - 1] is then again the full interval. | tight: counterexample `cex_compl_mem_iff_not_mem_of_size_lt_hI` (witness class: an instance with M = 4 (the full interval [0, 3])) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: offset arithmetic after rewriting both memberships with R1.1.

**Non-vacuity witness.** M = 256, [255, 0] (size 2). (`nv_compl_mem_iff_not_mem_of_size_lt`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For M = 1 every interval is full, so the hypothesis excludes M = 1 entirely.
- Nothing is claimed about how a real layout engine represents a full range.

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1 (tag llvmorg-21.1.0) llvm/lib/IR/ConstantRange.cpp:517-524 and 1939-1945 (source): `ConstantRange::contains(const APInt &V)` tests membership in a half-open wrapping range by cases ("return Lower.ule(V) && V.ult(Upper);" when the range does not wrap, line 522, and "return Lower.ule(V) || V.ult(Upper);" otherwise, line 523); `ConstantRange::inverse()` returns "ConstantRange(Upper, Lower)" for a range that is neither full nor empty (line 1944) — the half-open counterpart of `WrapInterval.compl`.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2075-2087 (source comment in Niche::reserve): "Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound." (line 2075-2076).

**Design question.** When is a niche decoder's single wrapping subtraction exact, including intervals that wrap at the unsigned or the signed boundary?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). `WrapInterval.compl` is compared with Gange et al.'s complement [y + 1, x - 1] of a w-interval (Section 3.1) and with LLVM's half-open `ConstantRange::inverse()` (`ConstantRange.cpp:1944`), by reading the quoted text against the Lean definition. No model–system relation is proved.

#### R1.3 `originTest_exactFor_iff_offset_le` (characterization, T0)

**Plain claim.** For every origin o and wrapping interval [s, e] of Fin M, the conjunctive comparison test `originTest o` ('offset(o, s) <= offset(o, x) <= offset(o, e)', offsets being wrapping distances from o) agrees with membership for every x iff (s - o) mod M <= (e - o) mod M, i.e. iff the interval does not wrap past o. Origin 0 is the unsigned test s <= x <= e (`unsignedTest_iff_originTest_zero`, every M); for M = 256, origin 128 is the signed test on i8 readings (`signedTestI8_iff_originTest_128`, proved for M = 256; other widths are not stated).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:65-66
theorem originTest_exactFor_iff_offset_le {M : Nat} (o : Fin M) (I : WrapInterval M) :
    ExactFor (originTest o) I ↔ offset o I.s ≤ offset o I.e := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `offset`, `WrapInterval`, `originTest`, `ExactFor`.

**Tier.** T0: re-derivation; the origin-relative order and the disagreement of the unsigned and signed orders across hemispheres are published (Gange et al. 2015, Section 3.1); this card restates them for an arbitrary origin.

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: offset arithmetic via the change-of-origin identity for offsets.

**Non-vacuity witness.** M = 8, origin 0, [2, 5]. (`nv_originTest_exactFor_iff_offset_le`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The folklore refutations are concrete: the unsigned test fails on [255, 0] mod 256 (`cex_folklore_unsignedTest_255_0`) and the i8 signed test fails on [127, 128] mod 256 (`cex_folklore_signedTestI8_127_128`). Each fixed test is exact on other wrapping intervals (`pc_signed_and_unsigned_exact_elsewhere`).
- The classification is for the conjunctive test `originTest o`. A two-branch test at a fixed origin (`twoBranchTest`) is exact for every interval (`pc_twoBranchTest_exactFor`); table lookups are not examined.
- The signed reading is stated for 8-bit fields (`toI8`, `signedTestI8`); the corresponding equivalence for other widths 2^w with origin 2^(w-1) is not stated (not proved here).

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:55-63 and 147-195 (source): `WrappingRange::contains` (lines 55-63, documented "Returns `true` if `v` is contained in the range.", line 55) tests membership by cases, `if self.start <= self.end { self.start <= v && v <= self.end } else { self.start <= v || v <= self.end }` (lines 58-62, line breaks collapsed) — the case split of `WrapInterval.Mem` and the two branches of `twoBranchTest` at origin 0; `smallest_range_containing` (lines 147-195) "Returns a `WrappingRange` that contains all of the values from the iterator, when they're treated as values `size` wide." (lines 147-148) by choosing the narrowest of the non-wraparound range and the wraparound candidates between consecutive sorted values (lines 176-194) — a computation of an interval hull in the sense of `IsHull`, which the toy characterizes semantically instead.
- llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1 (tag llvmorg-21.1.0) llvm/docs/LangRef.rst:7334-7371 (normative for LLVM IR), `range` metadata: "The pair ``a,b`` represents the range ``[a,b)``." (line 7346), "The range is allowed to wrap." (line 7348), and "The range should not represent the full or empty set. That is, ``a!=b``." (lines 7349-7350). LLVM ranges are half-open and a list of pairs may describe a union of ranges; the toy's intervals are inclusive single ranges like rustc's WrappingRange.

**Design question.** When is a niche decoder's single wrapping subtraction exact, including intervals that wrap at the unsigned or the signed boundary?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). That origin 0 is the unsigned comparison and, for M = 256, origin 128 is the i8 signed comparison is proved in the toy (`unsignedTest_iff_originTest_zero`, `signedTestI8_iff_originTest_128`). Relating these toy tests to range checks that a compiler emits is reasoning from the quoted rustc and LLVM range documentation and from Gange et al. (Section 3.1), not a proved relation; nothing is claimed about which comparison any compiler emits.

#### R1.4 `not_exactFor_originTest_wrapSub_one_of_two_le` (impossibility, T0)

**Plain claim.** For M >= 2 and every origin o of Fin M, the conjunctive fixed-origin comparison test `originTest o` ('offset(o, s) <= offset(o, x) <= offset(o, e)') is not exact for the two-element wrapping interval [o - 1, o] (o - 1 computed with wrapping arithmetic); hence for M >= 2 no single fixed origin makes this conjunctive test exact for every interval.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:90-91
theorem not_exactFor_originTest_wrapSub_one_of_two_le {M : Nat} (hM : 2 ≤ M) (o : Fin M) :
    ¬ ExactFor (originTest o) ⟨wrapSub o 1, o⟩ := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `wrapSub`, `originTest`, `ExactFor`.

**Tier.** T0: re-derivation; an immediate consequence of R1.3, itself a restatement of published facts (Gange et al. 2015, Section 3.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hM : 2 ≤ M` | For M = 1 there is a single interval, [0, 0], and the test at origin 0 is exact for it. | tight: counterexample `cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM` (witness class: an instance with M = 1) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: R1.3 instantiated at the interval [o - 1, o].

**Non-vacuity witness.** M = 256 (any origin). (`nv_not_exactFor_originTest_wrapSub_one_of_two_le`).

**Positive controls.** `pc_twoBranchTest_exactFor`, `pc_complTest_exactFor_fin8`, `pc_subTest_exactFor_all_fin8`, `cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM`.

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The witness interval is exposed: [o - 1, o]. The result says nothing about intervals that do not wrap past o, for which the fixed test is exact (`originTest_exactFor_iff_offset_le`).
- Escape hatch (a second branch): the test at the same fixed origin that uses `originTest o` when the interval does not wrap past o and the disjunction offset(o, s) <= offset(o, x) or offset(o, x) <= offset(o, e) otherwise (`twoBranchTest`) is exact for every interval, every M and every origin (`pc_twoBranchTest_exactFor`). At origin 0 its branches are the two cases of `WrapInterval.Mem`, the shape of rustc's `WrappingRange::contains` (prior art).
- Escape hatch (a negated complement): the fixed-origin test applied to the interval when it does not wrap past o, and the negated fixed-origin test applied to [e + 1, s - 1] otherwise, is exact for every origin and every interval of Fin 8 (`pc_complTest_exactFor_fin8`, a bounded check); the statement for general M is not proved here.
- Escape hatch (an origin that depends on the interval): with the interval's own start as origin the test is the single-subtraction test (`subTest_iff_originTest_start`), exact for every interval (`mem_iff_offset_le_offset`; `pc_subTest_exactFor_all_fin8` checks M = 8).
- Escape hatch (dropping hM): for M = 1 the only interval [0, 0] is tested exactly (`cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM`).

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:55-63 and 147-195 (source): `WrappingRange::contains` (lines 55-63, documented "Returns `true` if `v` is contained in the range.", line 55) tests membership by cases, `if self.start <= self.end { self.start <= v && v <= self.end } else { self.start <= v || v <= self.end }` (lines 58-62, line breaks collapsed) — the case split of `WrapInterval.Mem` and the two branches of `twoBranchTest` at origin 0; `smallest_range_containing` (lines 147-195) "Returns a `WrappingRange` that contains all of the values from the iterator, when they're treated as values `size` wide." (lines 147-148) by choosing the narrowest of the non-wraparound range and the wraparound candidates between consecutive sorted values (lines 176-194) — a computation of an interval hull in the sense of `IsHull`, which the toy characterizes semantically instead.
- llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1 (tag llvmorg-21.1.0) llvm/docs/LangRef.rst:7334-7371 (normative for LLVM IR), `range` metadata: "The pair ``a,b`` represents the range ``[a,b)``." (line 7346), "The range is allowed to wrap." (line 7348), and "The range should not represent the full or empty set. That is, ``a!=b``." (lines 7349-7350). LLVM ranges are half-open and a list of pairs may describe a union of ranges; the toy's intervals are inclusive single ranges like rustc's WrappingRange.

**Design question.** When is a niche decoder's single wrapping subtraction exact, including intervals that wrap at the unsigned or the signed boundary?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The remark that `twoBranchTest` at origin 0 has the shape of rustc's `WrappingRange::contains` rests on comparing the quoted source (`compiler/rustc_abi/src/wrapping_range.rs:58-62`) with the Lean definition. No model–system relation is proved, and nothing is claimed about which test any compiler emits.

#### R2.1 `affineLayout_eq_nicheLayoutK_affineTags` (theorem, T1)

**Plain claim.** For every payload validity set V on n-byte patterns and every affine encoding A (relative index r <= span gets tag (nicheStart + r) mod 256^n), the layout `affineLayout V A`, whose decoder performs one wrapping subtraction rel = (x - nicheStart) mod 256^n and returns relative index rel if rel <= span (else the payload if valid), is equal, as a layout, to the imported lookup layout `nicheLayoutK V (affineTags A)`; there is no hypothesis (when tags collide, both decoders return the least matching relative index).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:99-100
theorem affineLayout_eq_nicheLayoutK_affineTags {n : Nat} (V : Validity n)
    (A : AffineNiche (256 ^ n)) : affineLayout V A = nicheLayoutK V (affineTags A) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `AffineNiche`, `affineTags`, `affineLayout`, `Validity`, `nicheLayoutK`.

**Tier.** T1: folklore made precise; the affine encoding and its decoder are documented engineering (prior art); no mechanized statement was found (novelty search).

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: pointwise decoder equality; `List.find?` on `List.finRange` returns the offset when it is at most span.

**Non-vacuity witness.** n = 1, V = 1..=253, A = (first 0, span 2, nicheStart 254) (tags 254, 255, 0); also span 300 (colliding tags), checked pointwise. (`nv_affineLayout_eq_nicheLayoutK_affineTags`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Equality of decoders is not lawfulness: lawfulness needs span < 256^n and invalid tags (`affineLayout_lawful_iff_span_lt_and_tagsDisjoint`).
- The value type is the imported `ExtEnum (span + 1) V`: every slot of the niche range is a live dataless variant; dead slots are covered by the `genLayout` results instead.
- Variants of `affineLayout` are named by their relative index r, so `A.first` is not used by this layout and variant-index offsetting is not exercised here; it is exercised by `decodeIdx` and `genLayout` (R2.3-R2.5).

**Prior art.**

- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:251-300: theorem nicheLayoutK_lawful_iff_injective_and_isNiche (k-variant niche filling is lawful iff the tag map is injective and every tag is a niche). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** When does the affine tag formula with the one-subtraction decoder give a lawful enum layout, and what happens to field values in the niche range that encode no variant?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The tag formula of `AffineNiche.tagOf` and the single-subtraction decoder of `affineLayout` are compared with the formulas quoted from rustc's `TagEncoding::Niche` documentation (`compiler/rustc_abi/src/lib.rs:2008-2015`), by reading the quoted text against the Lean definitions; the documentation states the formula for variant indices i, whose relative index in the toy is r = i - first. The two round-trip laws are the imported `Lawful`, not a property read from rustc. No model–system relation is proved.

#### R2.2 `affineLayout_lawful_iff_span_lt_and_tagsDisjoint` (characterization, T1)

**Plain claim.** For every payload validity set V on n-byte patterns and every affine encoding A, the dead-slot-free single-subtraction layout `affineLayout V A` satisfies both round-trip laws (`DecEnc` and `Canonical`) iff span < 256^n and each of the span + 1 tags (nicheStart + r) mod 256^n, r <= span, is invalid for V.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:135-137
theorem affineLayout_lawful_iff_span_lt_and_tagsDisjoint {n : Nat} (V : Validity n)
    (A : AffineNiche (256 ^ n)) :
    Lawful (affineLayout V A) ↔ (A.span < 256 ^ n ∧ TagsDisjoint V A.nicheStart A.span) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `AffineNiche`, `TagsDisjoint`, `affineLayout`, `Validity`, `Lawful`.

**Tier.** T1: folklore made precise (as R2.1).

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: R2.1 and the imported characterization of lawful lookup layouts; injectivity of the affine tags is span < 256^n.

**Non-vacuity witness.** n = 1, V = 1..=253, tags 254, 255, 0 (both sides hold). (`nv_affineLayout_lawful_iff_span_lt_and_tagsDisjoint`).

**Positive controls.** `cex_affineLayout_lawful_overlap`, `cex_affineLayout_lawful_span`.

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Each conjunct of the right side is needed for this shape: an overlap with the valid set makes a valid payload decode as a niche variant (`cex_affineLayout_lawful_overlap`), and span = 256 with no valid value makes two tags coincide (`cex_affineLayout_lawful_span`).
- The equivalence is for the dead-slot-free shape. With dead slots (`genLayout`), span < 256^n is no longer necessary for lawfulness (`ex_genLayout_lawful_span_eq_card`: span 256, n = 1).
- `A.first` is not used by `affineLayout` (see R2.1).
- Whether a disjoint placement exists for a given V and span is a separate question (`exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull`).

**Prior art.**

- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:251-300: theorem nicheLayoutK_lawful_iff_injective_and_isNiche (k-variant niche filling is lawful iff the tag map is injective and every tag is a niche). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** When does the affine tag formula with the one-subtraction decoder give a lawful enum layout, and what happens to field values in the niche range that encode no variant?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). As for R2.1: the affine encoding is compared with rustc's documented `TagEncoding::Niche` formulas (`compiler/rustc_abi/src/lib.rs:2008-2015`), and lawfulness is the imported `Lawful`. No model–system relation is proved.

#### R2.3 `classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint` (theorem, T1)

**Plain claim.** For an enum shape E, an affine encoding A over Fin M with span < M, every tag of the niche range invalid for V (hypotheses), and every field value x (`classify` puts x into one of four classes: `liveTag` or `deadTag` if x lies in the tag interval, according to whether the variant index first + offset(nicheStart, x) of its slot is live, and otherwise `valid` or `unusedNiche` according to whether V x holds): x is classified `valid` iff V x holds; the single-subtraction decoder `decodeIdx` returns the untagged variant u on `valid` and on `unusedNiche` values; on the tag of relative index r <= span it returns first + r (whether that index is live, u, or uninhabited), the tag lying in the tag interval; and every value classified `liveTag` or `deadTag` is the tag of some relative index r <= span, on which `decodeIdx` returns first + r.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:166-175
theorem classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint {M : Nat} (E : EnumSpec)
    (A : AffineNiche M) (V : Fin M → Bool) (hspan : A.span < M)
    (hdisj : TagsDisjoint V A.nicheStart A.span) (x : Fin M) :
    (classify E A V x = .valid ↔ V x = true) ∧
    (classify E A V x = .valid → decodeIdx E.u A x = E.u) ∧
    (classify E A V x = .unusedNiche → decodeIdx E.u A x = E.u) ∧
    (∀ r, r ≤ A.span → x = A.tagOf r →
      decodeIdx E.u A x = A.first + r ∧ A.tagInterval.Mem x) ∧
    (classify E A V x = .liveTag ∨ classify E A V x = .deadTag →
      ∃ r, r ≤ A.span ∧ x = A.tagOf r ∧ decodeIdx E.u A x = A.first + r) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval.Mem`, `AffineNiche`, `AffineNiche.tagOf`, `AffineNiche.tagInterval`, `decodeIdx`, `TagsDisjoint`, `EnumSpec`, `classify`.

**Tier.** T1: folklore made precise (as R2.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hspan : A.span < M` | Makes tags of distinct relative indices distinct and makes the tag interval the set of tags. | tight: counterexample `cex_classify_valid_iff_and_decodeIdx_hspan` (witness class: an instance with M = 2, span = 2) |
| `hdisj : TagsDisjoint V A.nicheStart A.span` | Used by the first conjunct: without it a valid value can lie in the tag interval and be classified liveTag. | tight: counterexample `cex_classify_valid_iff_and_decodeIdx_hdisj` (witness class: an instance with M = 8, every value valid) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: case analysis on membership in the tag interval after R1.1.

**Non-vacuity witness.** M = 8, A = (first 0, span 2, nicheStart 5), V = 0..=4. (`nv_classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- All four classes occur in one instance (`ex_classify`: valid 0..=249, tags 253, 254, 255 with 254 a dead slot, 251 an unused niche). A three-way partition (valid, live tag, dead slot) therefore misses the unused niches; the three classes cover the field when the tag interval and the valid set together cover it (not stated as a theorem here).
- `decodeIdx` is the index-only decoder; it never rejects. On a dead slot it returns first + r, which is u or an index that is uninhabited or >= k; whether that is undefined behaviour is a property of the checked decoder (`genLayout_dec_isSome_iff_classify_of_span_lt`), not of `decodeIdx`.
- The folklore 'every tag in the niche interval encodes a variant' is refuted by `cex_folklore_dead_slot`.
- The proof of the second to fifth conjuncts does not use hdisj (they hold without it; not stated as a separate theorem); the first conjunct uses it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).
- https://github.com/rust-lang/rust/pull/133681 (merged 2024-12-04, merge commit 6e87eb58ede97cce4bd1e392694f88a2a2936e84), "improve TagEncoding::Niche docs, sanity check, and UB checks": "Turns out the `niche_variants` range can actually contain the `untagged_variant`. We should report this as UB in Miri, so this PR implements that."
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** When does the affine tag formula with the one-subtraction decoder give a lawful enum layout, and what happens to field values in the niche range that encode no variant?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The four field-value classes are the toy's `classify`. Dead slots are compared with the "dead values" of rustc's `TagEncoding::Niche` documentation (`compiler/rustc_abi/src/lib.rs:2027-2028`), and `decodeIdx` with its documented inverse formula (`lib.rs:2008-2015`), by reading the quoted text against the Lean definitions. No model–system relation is proved.

#### R2.4 `genLayout_dec_isSome_iff_classify_of_span_lt` (characterization, T1)

**Plain claim.** For an enum shape E, an affine encoding A on n-byte patterns with span < 256^n (hypothesis), a payload validity set V and every field value x (`classify` puts x into one of four classes: `liveTag` or `deadTag` if x lies in the tag interval, according to whether the variant index first + offset(nicheStart, x) of its slot is live, and otherwise `valid` or `unusedNiche` according to whether V x holds), the checked decoder of `genLayout E A V` accepts x iff x is classified `valid` or `liveTag`; values at dead slots and unused niches are rejected.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:217-220
theorem genLayout_dec_isSome_iff_classify_of_span_lt {n : Nat} (E : EnumSpec)
    (A : AffineNiche (256 ^ n)) (V : Validity n) (hspan : A.span < 256 ^ n) (x : Pat n) :
    ((genLayout E A V).dec x).isSome = true ↔
      (classify E A V x = .valid ∨ classify E A V x = .liveTag) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `AffineNiche`, `EnumSpec`, `genLayout`, `classify`, `Pat`, `Validity`.

**Tier.** T1: folklore made precise; the checked decoder follows documented interpreter behaviour (prior art).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hspan : A.span < 256 ^ n` | Makes semantic membership in the tag interval coincide with the decoder's test rel <= span. | tight: counterexample `cex_genLayout_dec_isSome_iff_classify_hspan` (witness class: an instance with n = 1, span = 256) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: the decoder and `classify` have the same case tree once R1.1 identifies the two membership tests.

**Non-vacuity witness.** n = 1, A = (first 0, span 2, nicheStart 253). (`nv_genLayout_dec_isSome_iff_classify_of_span_lt`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Acceptance is not lawfulness. A sufficient condition for lawfulness is `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange`, which adds hdisj and hlive to hspan; each of its hypotheses is tight in the witness class recorded in its ledger, but necessity for lawfulness in general is not proved here, and span < 256^n is not necessary for lawfulness (`ex_genLayout_lawful_span_eq_card`).
- There is no tag condition here. Without one, a valid payload value inside the tag interval is classified `liveTag` or `deadTag`, not `valid`: the checked decoder then decodes it as a dataless variant or rejects it (`cex_genLayout_lawful_hdisj`, `cex_genLayout_lawful_hdisj_deadSlot`).
- The correspondence between the checked decoder and the interpreter behaviour described in the source comments cited below is a derived (modeling bridge) claim, not a proved relation; the toy's validity set V plays the role of the niche scalar's valid range, which in rustc is a single wrapping range.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:187-200 and 210-215 (source comments): "The untagged variant can be in the niche range, but even then it is not a valid encoding. Codegen inserts an `assume` here so we really have to make this UB." (lines 188-190); "Ensure the tag is in its layout range. Codegen adds range metadata on the discriminant load so we really have to make this UB." (lines 195-196); "Reading the discriminant of an uninhabited variant is UB." (line 210).
- https://github.com/rust-lang/rust/pull/133681 (merged 2024-12-04, merge commit 6e87eb58ede97cce4bd1e392694f88a2a2936e84), "improve TagEncoding::Niche docs, sanity check, and UB checks": "Turns out the `niche_variants` range can actually contain the `untagged_variant`. We should report this as UB in Miri, so this PR implements that."
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).

**Design question.** When does the affine tag formula with the one-subtraction decoder give a lawful enum layout, and what happens to field values in the niche range that encode no variant?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Under the hypothesis span < 256^n, the checked decoder of `genLayout` rejects dead slots and unused niches; the quoted interpreter source comments describe undefined behaviour for the untagged variant's slot inside the niche range, for a tag outside the layout range, and for reading the discriminant of an uninhabited variant (`compiler/rustc_const_eval/src/interpret/discriminant.rs:188-190`, `195-196` and `210` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe). The correspondence is reasoned from those comments; it is not a proved relation.

#### R2.5 `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange` (theorem, T1)

**Plain claim.** For an enum shape E (k variants, untagged variant u, inhabitedness flags; every variant other than u is dataless), an affine encoding A on n-byte patterns and a payload validity set V: if span < 256^n, every tag of the niche range is invalid for V, and every live variant (inhabited, other than u, index < k) lies in [first, first + span], then `genLayout E A V` satisfies both round-trip laws, even when the niche range contains u or uninhabited variants (dead slots).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:236-239
theorem genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange {n : Nat} (E : EnumSpec)
    (A : AffineNiche (256 ^ n)) (V : Validity n) (hspan : A.span < 256 ^ n)
    (hdisj : TagsDisjoint V A.nicheStart A.span) (hlive : LiveInRange E A) :
    Lawful (genLayout E A V) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `AffineNiche`, `TagsDisjoint`, `EnumSpec`, `LiveInRange`, `genLayout`, `Validity`, `Lawful`.

**Tier.** T1: folklore made precise; dead values in the niche range are documented (prior art).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hspan : A.span < 256 ^ n` | Distinct live variants get distinct tags. | tight: counterexample `cex_genLayout_lawful_hspan` (witness class: an instance with n = 1, span = 256) |
| `hdisj : TagsDisjoint V A.nicheStart A.span` | No valid payload value is a tag, at a live slot or at a dead slot. | tight: counterexample `cex_genLayout_lawful_hdisj` (witness class: an instance with n = 1, every value valid) |
| `hlive : LiveInRange E A` | Every live variant is encodable. | tight: counterexample `cex_genLayout_lawful_hlive` (witness class: an instance with n = 1, range [1, 2] missing live variant 0) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: `Canonical` holds for every `genLayout` (`genLayout_canonical`, a proof lemma); `DecEnc` is a direct case split.

**Non-vacuity witness.** n = 1, E = (k 3, u 1, all inhabited), A = (first 0, span 2, nicheStart 253) so tag 254 is the dead slot of u, V = 0..=252. (`nv_genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A sufficient condition. Each hypothesis is tight (it has a counterexample in which the others hold), but span < 256^n is not necessary for lawfulness: with no valid value and the slot at relative index 256 dead, span 256 is lawful for n = 1 (`ex_genLayout_lawful_span_eq_card`).
- Valid payload values may not occupy dead slots either: a valid value at the dead slot of u is rejected by the checked decoder and the layout is not lawful (`cex_genLayout_lawful_hdisj_deadSlot`).
- The dead slot wastes a tag value; the capacity consequences are stated in group 3 and group 4.
- Every variant other than u is dataless in `genLayout`; rustc's niche-filling layout also admits such variants with fields placed before or after the niche field (prior art, derived (modeling bridge)), which are not modelled here.
- Discriminants are the variant indices, as rustc's layout sanity check requires for niche-encoded enums (prior art, derived (modeling bridge)); explicit discriminants are not modelled.
- `EnumSpec` does not require u < k: for u >= k every index below k is a candidate dataless variant (`ex_live_u_ge_k`); the theorem holds for such shapes too.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).
- https://github.com/rust-lang/rust/pull/133681 (merged 2024-12-04, merge commit 6e87eb58ede97cce4bd1e392694f88a2a2936e84), "improve TagEncoding::Niche docs, sanity check, and UB checks": "Turns out the `niche_variants` range can actually contain the `untagged_variant`. We should report this as UB in Miri, so this PR implements that."
- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:251-300: theorem nicheLayoutK_lawful_iff_injective_and_isNiche (k-variant niche filling is lawful iff the tag map is injective and every tag is a niche). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/layout.rs:652-680 (source): in the niche-filling layout computation every variant other than the largest one is checked to fit either before the niche ("// This variant will fit before the niche.", line 660) or after it ("// Determine if it'll fit after the niche.", line 664), with its field offsets shifted (lines 673-675); such variants may therefore carry fields outside the niche field. `genLayout` models every variant other than `u` as dataless; the operational model (group 6) does not tie field bytes to variants.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_ty_utils/src/layout/invariant.rs:300-323 (source): `layout_sanity_check` for `TagEncoding::Niche` asserts that every inhabited variant is the untagged variant or lies in `niche_variants` (line 308) and reports a bug if a variant's discriminant differs from its index ("// Ensure that for niche encoded tags the discriminant coincides with the variant index.", line 311). The toy identifies discriminants with variant indices throughout.

**Design question.** When does the affine tag formula with the one-subtraction decoder give a lawful enum layout, and what happens to field values in the niche range that encode no variant?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Two modelling gaps are read from the rustc sources quoted under Prior art: rustc's niche-filling layout checks whether each variant other than the largest fits before or after the niche, so such variants may carry fields (`compiler/rustc_abi/src/layout.rs:652-680`), whereas `genLayout` makes them dataless; and discriminants are variant indices, as rustc's layout sanity check requires for niche-encoded enums (`compiler/rustc_ty_utils/src/layout/invariant.rs:300-323`). Neither is a proved relation.

#### R3.1 `exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull` (characterization, T1)

**Plain claim.** For a validity set V on Fin M with at least one valid value and an interval hull H of V (a smallest wrapping interval containing every valid value), and every span: some placement of span + 1 contiguous tags ns, ..., ns + span (wrapping) avoids every valid value iff span + 1 <= M - H.size (H.size <= M, so this subtraction does not truncate).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:263-266
theorem exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull {M : Nat}
    (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (span : Nat) :
    (∃ ns : Fin M, TagsDisjoint V ns span) ↔ span + 1 ≤ M - H.size := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `IsHull`, `TagsDisjoint`.

**Tier.** T1: folklore made precise; hulls of wrapped intervals are published (Gange et al. 2015) and computed by rustc (prior art), but the capacity statement was not found mechanized or stated.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hne : ∃ x, V x = true` | With no valid value the hull is a singleton yet every value can be a tag. | tight: counterexample `cex_exists_tagsDisjoint_iff_span_succ_le_hne` (witness class: an instance with M = 4, V empty, span = 3) |
| `hH : IsHull V H` | A covering interval that is not smallest understates the capacity. | tight: counterexample `cex_exists_tagsDisjoint_iff_span_succ_le_hH` (witness class: an instance with M = 4, V = {0}, H = [0, 1]) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** substantive: both directions construct intervals (the tag interval and its complement, or the complement of the hull) and use minimality of the hull.

**Non-vacuity witness.** M = 4, V = {0, 1}, H = [0, 1]. (`nv_exists_tagsDisjoint_iff_span_succ_le_sub_size_of_isHull`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Contiguity is a modeling choice that mirrors the affine encoding; layouts with non-contiguous tags (the imported lookup layout) can exceed this capacity (`cex_folklore_fragmented_capacity_lt_nichesCount`).
- `TagsDisjoint` does not require the tags to be distinct. Under hne the theorem itself forces span + 1 <= M - H.size <= M - 1, so the tags are distinct; for the empty validity set `TagsDisjoint` holds for every span, including span >= M where tags repeat (`cex_genLayout_lawful_hspan` contains `TagsDisjoint (fun _ => false) 0 256` for M = 256), so dropping hne does not give an unbounded lawful capacity (lawfulness is R2.2).
- The existence of an interval hull for every V on Fin M with M > 0 is not proved here; rustc computes one (`smallest_range_containing`, prior art).
- A single niche field is modelled: payloads with several fields (where another field's niches could be used), and wrappers that hide niches, are not modelled.
- Nothing is claimed about which placement a layout engine chooses; rustc reserves values adjacent to the valid range (source comment cited), which is one of the disjoint placements when V is an interval.

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:55-63 and 147-195 (source): `WrappingRange::contains` (lines 55-63, documented "Returns `true` if `v` is contained in the range.", line 55) tests membership by cases, `if self.start <= self.end { self.start <= v && v <= self.end } else { self.start <= v || v <= self.end }` (lines 58-62, line breaks collapsed) — the case split of `WrapInterval.Mem` and the two branches of `twoBranchTest` at origin 0; `smallest_range_containing` (lines 147-195) "Returns a `WrappingRange` that contains all of the values from the iterator, when they're treated as values `size` wide." (lines 147-148) by choosing the narrowest of the non-wraparound range and the wraparound candidates between consecutive sorted values (lines 176-194) — a computation of an interval hull in the sense of `IsHull`, which the toy characterizes semantically instead.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2075-2087 (source comment in Niche::reserve): "Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound." (line 2075-2076).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/layout.rs:636-643 (source, read for orientation; no claim of this package relies on it): niche_variants runs from the first to the last variant that needs a discriminant, and count = last - first + 1 values are reserved.
- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:335-346: theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches (k dataless variants fit in the payload's bytes under some lawful layout iff k <= numInvalid V). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** How much capacity do contiguity of the tag range (and a reserved slot for the untagged variant) cost compared with the unconstrained niche count? (When the untagged variant lies inside the niche range its slot is counted in the span; see group 4.)

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). That rustc computes a smallest covering range (`smallest_range_containing`, `compiler/rustc_abi/src/wrapping_range.rs:147-195`) and reserves values adjacent to the valid range (`Niche::reserve`, `compiler/rustc_abi/src/lib.rs:2075-2076`) is read from the quoted source. The toy characterizes hulls semantically (`IsHull`) and proves nothing about rustc's computation or placement.

#### R3.2 `sub_size_le_nichesCount_and_eq_iff_of_covers` (theorem, T0)

**Plain claim.** For a validity set V on Fin M and every wrapping interval H that covers V (every valid value is a member of H; H need not be smallest), the number M - H.size of values outside H (H.size <= M, so no truncation) is at most the number of invalid values of V (for M = 256^n this count is the imported `numInvalid`, the unconstrained capacity, by `nichesCount_eq_numInvalid`), with equality iff every member of H is valid.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:361-363
theorem sub_size_le_nichesCount_and_eq_iff_of_covers {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hcov : Covers H V) :
    M - H.size ≤ nichesCount V ∧ (M - H.size = nichesCount V ↔ ∀ x, H.Mem x → V x = true) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.Mem`, `WrapInterval.size`, `Covers`, `nichesCount`.

**Tier.** T0: re-derivation; a counting corollary of R3.3 (the cardinality of a wrapped interval, Gange et al. 2015, Section 3.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hcov : Covers H V` | An interval that misses a valid value can have more values outside it than V has niches. | tight: counterexample `cex_sub_size_le_nichesCount_and_eq_iff_of_covers_hcov` (witness class: an instance with M = 4, V = {0, 1}, H = [0, 0]) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: R3.3 and the imported duplicate-free list counting lemmas.

**Non-vacuity witness.** M = 4, V = {0, 2}, H = [0, 2] (a hull; 1 value outside, 2 niches) and H = [0, 3] (covering, not a hull). (`nv_sub_size_le_nichesCount_and_eq_iff_of_covers`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For an interval hull H of a V with at least one valid value, M - H.size is the contiguous capacity of R3.1 (span + 1 <= M - H.size); for the empty validity set it is not (`cex_exists_tagsDisjoint_iff_span_succ_le_hne`: M = 4, M - H.size = 3, yet four contiguous tags fit).
- For an interval hull H, equality holds iff V is itself the member set of a wrapping interval (`sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull`); there the minimality half of `IsHull` is tight, witnessed on M = 4, V = {0, 1}, H = [0, 2] by `cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH`; whether it is needed for other instances is not claimed (not proved here).
- Strictness for fragmented validity is `cex_folklore_fragmented_capacity_lt_nichesCount` (M = 4, V = {0, 2}); the cost of u's slot inside the range is `cex_folklore_fit_depends_on_untagged_position`.
- For the empty validity set both sides of the equivalence are false (H is non-empty).

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:335-346: theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches (k dataless variants fit in the payload's bytes under some lawful layout iff k <= numInvalid V). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.

**Design question.** How much capacity do contiguity of the tag range (and a reserved slot for the untagged variant) cost compared with the unconstrained niche count? (When the untagged variant lies inside the niche range its slot is counted in the span; see group 4.)

Basis: execution (Lean kernel check).

#### R3.3 `nichesCount_intervalV` (theorem, T0)

**Plain claim.** For every wrapping interval I of Fin M, the validity set `intervalV I` whose valid values are exactly the members of I has M - I.size invalid values (I.size <= M, so no truncation).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:336-337
theorem nichesCount_intervalV {M : Nat} (I : WrapInterval M) :
    nichesCount (intervalV I) = M - I.size := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `intervalV`, `nichesCount`.

**Tier.** T0: re-derivation; the cardinality of a wrapped interval is published (Gange et al. 2015, Section 3.1).

**Hypothesis ledger.**

No hypotheses.

**Depth.** substantive: a counting argument: the members of I are in bijection with the offsets 0..(e - s) mod M, counted with duplicate-free lists.

**Non-vacuity witness.** M = 4, I = [3, 1]. (`nv_nichesCount_intervalV`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A counting lemma; it says nothing about layouts by itself.

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).

**Design question.** How much capacity do contiguity of the tag range (and a reserved slot for the untagged variant) cost compared with the unconstrained niche count? (When the untagged variant lies inside the niche range its slot is counted in the span; see group 4.)

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). `intervalV` is a validity set described by one wrapping interval, like a validity described by rustc's `WrappingRange` (`compiler/rustc_abi/src/wrapping_range.rs:8-9`); this is a comparison of definitions, not a proved relation.

#### R4.1 `exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq` (characterization, T1)

**Plain claim.** For a validity set V on Fin M with at least one valid value, an interval hull H of V, k >= 2, and exactly k - 1 values outside H (M - H.size = k - 1; under k >= 2 the truncated subtraction k - 1 does not truncate), and for every natural number u: some start ns makes the naturalSpan k u + 1 contiguous tags ns, ..., ns + naturalSpan k u (wrapping) all invalid for V iff u = 0 or u = k - 1. Here naturalSpan k u = naturalLast k u - naturalFirst u; for u < k it is the span of the smallest index range containing every index of 0..k-1 other than u (`naturalFirst_naturalLast_spec`), i.e. of the niche range when the k - 1 variants other than u all need a tag.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:408-411
theorem exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq
    {M : Nat} (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (k u : Nat) (hk : 2 ≤ k) (hcap : M - H.size = k - 1) :
    (∃ ns : Fin M, TagsDisjoint V ns (naturalSpan k u)) ↔ (u = 0 ∨ u = k - 1) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `IsHull`, `TagsDisjoint`, `naturalSpan`.

**Tier.** T1: folklore made precise; the order dependence is reported publicly (prior art) but no mechanized statement was found.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hne : ∃ x, V x = true` | Without a valid value every placement fits. | tight: counterexample `cex_naturalSpan_hne` (witness class: an instance with M = 3, V empty, k = 3, u = 1) |
| `hH : IsHull V H` | A covering interval that is not smallest misstates the capacity. | tight: counterexample `cex_naturalSpan_hH` (witness class: an instance with M = 4, V = {0}, H = [0, 1], k = 3, u = 1) |
| `hk : 2 ≤ k` | For k = 1 the natural span is 0 by truncated subtraction yet still needs one niche. | tight: counterexample `cex_naturalSpan_hk` (witness class: an instance with M = 2, every value valid, k = 1, u = 0) |
| `hcap : M - H.size = k - 1` | The exact-capacity boundary; with one more value outside H the middle position also fits. | tight: counterexample `cex_naturalSpan_hcap` (witness class: an instance with M = 4, V = {0}, k = 3, u = 1, M - H.size = 3) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: R3.1 with `naturalSpan_eq`.

**Non-vacuity witness.** M = 4, V = {0, 1}, H = [0, 1], k = 3. (`nv_exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Off the boundary hcap the answer is different and does not single out the ends: for every capacity, the natural range fits iff M - H.size >= k - 1 when u = 0 or u = k - 1 and M - H.size >= k otherwise (`exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull`, k >= 2). So with M - H.size >= k every u fits, including middle positions (`cex_naturalSpan_hcap` is an instance), and with M - H.size < k - 1 no u fits, not even u = 0 or u = k - 1.
- u is unconstrained: for u >= k the right side is false (u = 0 and u = k - 1 both fail since k >= 2), so by this theorem the left side is false too. For k = 2 there is no middle index (0 < u < 1 is empty) and the theorem says that both u = 0 and u = 1 fit.
- The theorem is about contiguous tag placements (`TagsDisjoint`) of span `naturalSpan k u`; deriving from it that no affine encoding satisfying `LiveInRange` fits needs `naturalFirst_naturalLast_spec` and monotonicity of `TagsDisjoint` in the span, and is not stated as a theorem here (not proved here).
- Other encodings behave differently: the rotated encoding fits for every u under the same capacity condition k - 1 <= M - H.size (R4.2 and `exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull`), and an unconstrained lookup layout can fit where the natural range does not (`cex_folklore_fit_depends_on_untagged_position`, n = 1, valid 0..=253, k = 3; it also refutes 'niche fit depends only on the multiset of variant layouts' for the natural range).
- `naturalSpan` assumes every dataless variant is inhabited; uninhabited variants at the ends shrink the range and are not covered.
- The public issue cited below reports a size difference for a 255-variant enum; this card does not claim to explain rustc's behaviour on that example (derived (modeling bridge) at most).

**Prior art.**

- https://github.com/rust-lang/rust/issues/117238 (issue, open when checked on 2026-11-21), "Enum size depends on ordering of members": a 255-variant enum whose one bool-carrying variant is 7th has size 2, the same enum with that variant last has size 1 (rustc 1.73.0); "I expected these to have the same size.  The two enums differ only in the placement of the `(bool)`-carrying member." (two spaces after the first sentence in the source)
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/layout.rs:636-643 (source, read for orientation; no claim of this package relies on it): niche_variants runs from the first to the last variant that needs a discriminant, and count = last - first + 1 values are reserved.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2002-2033 (documentation): TagEncoding::Niche docs, quoted: "For a variant with variant index `i`, such that `i != untagged_variant`, the tag is set to `(i - niche_variants.start).wrapping_add(niche_start)` (this is wrapping arithmetic using the type of the niche field, cf. the [`tag_for_variant`](../rustc_const_eval/interpret/struct.InterpCx.html#method.tag_for_variant) query implementation). To recover the variant index `i` from a `tag`, the above formula has to be reversed, i.e. `i = tag.wrapping_sub(niche_start) + niche_variants.start`. If `i` ends up outside `niche_variants`, the tag must have encoded the `untagged_variant`." (lib.rs:2008-2015); "Other variants that are not `untagged_variant` and that are outside the `niche_variants` range cannot be represented; they must be uninhabited. Nonetheless, uninhabited variants can also fall into the range of `niche_variants`." (lib.rs:2022-2024); and "This range *may* contain `untagged_variant` or uninhabited variants; these are then just "dead values" and not used to encode anything." (lib.rs:2027-2028).
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** Does niche fit depend on declaration order, and does a cyclic renumbering starting after the untagged variant remove the dependence?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The public issue https://github.com/rust-lang/rust/issues/117238 is titled "Enum size depends on ordering of members"; this card proves a statement about contiguous tag placements in the toy and does not claim to explain rustc's behaviour on the issue's example. `naturalSpan` is compared with the `niche_variants` range of rustc's `TagEncoding::Niche` documentation (`compiler/rustc_abi/src/lib.rs:2002-2033`) by reading the quoted text. No model–system relation is proved.

#### R4.2 `rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid` (theorem, T1)

**Plain claim.** For the rotated encoding (variant i gets tag ns + `rotIdx k u i`, where `rotIdx k u i` = (i - (u + 1)) mod k is computed in Nat as (i + k - (u + 1) % k) % k with floor modulo, the subtraction not truncating since (u + 1) % k < k, so the variants after u come first), with u < k, k <= M + 1, and V invalid at the rotated tag ns + r (wrapping addition) for each of the exactly k - 1 indices r with r + 1 < k (`RotTagsInvalid V k ns`; for k = 1 there is no such index and this hypothesis holds trivially): the rotated decoder `rotDecodeIdx` (one wrapping subtraction rel = (x - ns) mod M, then, if rel + 1 < k, the extra modular step (rel + u + 1) mod k, else u) recovers every variant i < k, i != u, from its rotated tag, and decodes every valid value to u.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:419-422
theorem rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid {M : Nat} (V : Fin M → Bool)
    (k u : Nat) (ns : Fin M) (hu : u < k) (hkM : k ≤ M + 1) (hdisj : RotTagsInvalid V k ns) :
    (∀ i, i < k → i ≠ u → rotDecodeIdx k u ns (rotTag k u ns i) = i) ∧
    (∀ x, V x = true → rotDecodeIdx k u ns x = u) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `rotTag`, `rotDecodeIdx`, `RotTagsInvalid`.

**Tier.** T1: folklore made precise; the rotation was proposed publicly (prior art, unmerged) but no mechanized statement was found.

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hu : u < k` | With u >= k the rotation misplaces a variant. | tight: counterexample `cex_rotDecodeIdx_hu` (witness class: an instance with M = 2, k = 2, u = 2) |
| `hkM : k ≤ M + 1` | Otherwise two rotated tags coincide. | tight: counterexample `cex_rotDecodeIdx_hkM` (witness class: an instance with M = 2, k = 4, u = 3) |
| `hdisj : RotTagsInvalid V k ns` | Used by the second conjunct: a valid value equal to a rotated tag decodes as that variant. | tight: counterexample `cex_rotDecodeIdx_hdisj` (witness class: an instance with M = 4, k = 2, u = 0, every value valid) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: modular arithmetic on rotated indices.

**Non-vacuity witness.** M = 256, k = 3, u = 1, ns = 254, V = 0..=253; and M = 2, k = 1, u = 0, every value valid. (`nv_rotDecodeIdx_exact`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For k >= 2, `RotTagsInvalid V k ns` is `TagsDisjoint V ns (k - 2)` (`rotTagsInvalid_iff_tagsDisjoint_sub_two`): the rotated range has span k - 2 for every position of u. For a payload with a valid value and an interval hull H, a start making all rotated tags invalid exists iff k - 1 <= M - H.size, for every k (truncated subtraction k - 1; trivial for k <= 1) and independently of u (`exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull`).
- `rotDecodeIdx` is an unchecked, index-only decoder: no lawful `Layout` is constructed for the rotated encoding (unlike R2.2 and R2.5), unused niches decode to u, and uninhabited variants and dead slots are not modelled.
- The theorem assumes hdisj for both conjuncts. The proof of the first conjunct does not use hdisj (so that conjunct holds without it; it is not stated as a separate theorem); the second conjunct uses it.
- The cited pull request is a closed, unmerged proposal and is not normative; as described there it rotates when u lies inside the range, whereas this model rotates always. No claim is made about its code.
- The cost of the extra modular step in generated code is not examined.

**Prior art.**

- https://github.com/rust-lang/rust/pull/131684 (closed unmerged on 2024-12-10; an unmerged proposal, not normative), "make enum size not depend on the order of variants": "I fixed the off-by-one error by allocating discriminant starting from the variant after the untagged variant and wrapping around to the first variant when it reaches the last variant.", "This is only applied when the `untagged_variant` is contained in the `niche_variants` wasting one value from the niche range.", and "It adds one arithmetic instruction in the general case and no additional branch instruction."
- https://github.com/rust-lang/rust/issues/117238 (issue, open when checked on 2026-11-21), "Enum size depends on ordering of members": a 255-variant enum whose one bool-carrying variant is 7th has size 2, the same enum with that variant last has size 1 (rustc 1.73.0); "I expected these to have the same size.  The two enums differ only in the placement of the `(bool)`-carrying member." (two spaces after the first sentence in the source)
- Novelty search (2026-11-21, web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding): the wrapped-interval facts of groups 1, 3 and 5 are published (Gange et al. 2015, cited on those cards) but no mechanization of them, and no treatment of the affine niche decoder with dead slots, contiguous-capacity loss against the niche count, declaration-order dependence, adjacent-reservation nesting or SetDiscriminant write order, was found; the closest artifacts are the rustc sources cited here, the MiniRust specification (decision-tree encoding, not affine) and the imported package (extensional tag maps).

**Design question.** Does niche fit depend on declaration order, and does a cyclic renumbering starting after the untagged variant remove the dependence?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The rotated encoding is compared with the closed, unmerged proposal https://github.com/rust-lang/rust/pull/131684 as described in its text (it rotates when the untagged variant lies inside the range; the toy rotates always). The proposal is not normative, and nothing is claimed about its code or about rustc.

#### R5.1 `extend_spec_of_size_lt` (theorem, T0)

**Plain claim.** For a non-full wrapping interval I of Fin M (hypothesis: size < M) and either side, the adjacent value (e + 1 or s - 1, wrapping) is not a member of I, the extended interval contains exactly the members of I and that value, and its size is I.size + 1; this holds at the wrap point (for example [250, 255] extends upward to [250, 0], `ex_extend`).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:465-467
theorem extend_spec_of_size_lt {M : Nat} (I : WrapInterval M) (d : Side) (hI : I.size < M) :
    ¬ I.Mem (adjNiche I d) ∧ (∀ x, (extend I d).Mem x ↔ (I.Mem x ∨ x = adjNiche I d)) ∧
      (extend I d).size = I.size + 1 := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.Mem`, `WrapInterval.size`, `Side`, `adjNiche`, `extend`.

**Tier.** T0: re-derivation; membership and cardinality of wrapped intervals are published (Gange et al. 2015, Section 3.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hI : I.size < M` | For a full interval the adjacent value is already a member. | tight: counterexample `cex_extend_spec_hI` (witness class: an instance with M = 4 (the full interval [0, 3])) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: offset arithmetic after R1.1.

**Non-vacuity witness.** M = 4, I = [1, 1]. (`nv_extend_spec_of_size_lt`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For a full interval (I.size = M), `extend` wraps past the opposite end and collapses to a singleton (`ex_extend_full`: `extend [0, 3] .high = [0, 0]` in Fin 4, size 1).
- Which side a layout engine picks is not modelled; both sides are covered.

**Prior art.**

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360 (consulted in the authors' copy at https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf; formulas paraphrased): the wrapped-interval (w-interval) domain over w-bit integers. Section 3.1 defines the relative order b ≤_a c iff (b - a) mod 2^w ≤ (c - a) mod 2^w and notes that the unsigned order (a = 0) and the signed order (a = 2^(w-1)) disagree across hemispheres; the same section (Definition 3.1 and the definitions after it) gives the meaning of a delimited interval by the same case split as `WrapInterval.Mem`, its cardinality (y - x) mod 2^w + 1, and its complement [y + 1, x - 1]; Section 3.2 tests membership as e ≤_x y — the single-subtraction test — and shows that w-intervals ordered by inclusion are not a lattice (two incomparable minimal upper bounds of equal cardinality); Section 3.3 gives a minimal-upper-bound algorithm (Fig. 5) that returns the complement of the largest uncovered gap. Unlike the toy, w-intervals include an empty element and a single full element.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2075-2087 (source comment in Niche::reserve): "Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound." (line 2075-2076).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/wrapping_range.rs:8-16 (documentation): "Inclusive wrap-around range of valid values, that is, if start > end, it represents `start..=MAX`, followed by `0..=end`." (lines 8-9) and "This is intended specifically to mirror LLVM’s `!range` metadata semantics." (line 16).

**Design question.** How do nested Option levels compose when each reserves a value next to the current valid interval?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). `extend` is compared with the source comment of rustc's `Niche::reserve` ("Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound.", `compiler/rustc_abi/src/lib.rs:2075-2076`), by reading the comment against the Lean definition. No model–system relation is proved.

#### R5.2 `nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt` (theorem, T1)

**Plain claim.** For a non-full valid interval I of n-byte patterns (hypothesis: size < 256^n) and either side d, the one-level niche-filled Option layout that puts None on the adjacent value is lawful, and the patterns it accepts are exactly the members of `extend I d` (again a wrapping interval).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:522-525
theorem nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt {n : Nat}
    (I : WrapInterval (256 ^ n)) (d : Side) (hI : I.size < 256 ^ n) :
    Lawful (nicheLayout (intervalV I) (adjNiche I d)) ∧
      ∀ p, ((nicheLayout (intervalV I) (adjNiche I d)).dec p).isSome = intervalV (extend I d) p := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `intervalV`, `Side`, `adjNiche`, `extend`, `Lawful`, `nicheLayout`.

**Tier.** T1: folklore made precise; adjacent reservation is documented engineering (prior art).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hI : I.size < 256 ^ n` | For the full range the reserved value is valid and the layout is not lawful. | tight: counterexample `cex_nicheLayout_adjNiche_lawful_hI` (witness class: an instance with n = 1 (the full range [0, 255])) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: R5.1 and the imported characterization of lawful niche-filled layouts.

**Non-vacuity witness.** n = 1, I = [1, 255] (the NonZero range). (`nv_nicheLayout_adjNiche_lawful`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Lawfulness is via the imported `nicheLayout_lawful_iff_isNiche`; this card adds the intervalness of the accepted set.
- A single niche field whose valid set is a wrapping interval is modelled; other payload shapes are not.

**Prior art.**

- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:43-51: theorem nicheLayout_lawful_iff_isNiche (one-variant niche filling with None -> q is lawful iff q is a niche). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2075-2087 (source comment in Niche::reserve): "Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound." (line 2075-2076).

**Design question.** How do nested Option levels compose when each reserves a value next to the current valid interval?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). As for R5.1, adjacent reservation (`adjNiche`) is compared with the source comment of rustc's `Niche::reserve` (`compiler/rustc_abi/src/lib.rs:2075-2076`); the one-level layout is the imported niche-filled layout. No model–system relation is proved.

#### R5.3 `levelsReserveNiches_iff_length_le_and_nest_size` (characterization, T1)

**Plain claim.** For every innermost valid interval R0 of Fin M and every list of side choices, adjacent reservation reserves an invalid value at every one of the sides.length levels iff sides.length <= M - R0.size (truncation-free since R0.size <= M), whatever sides are chosen; in that case the final valid interval has size R0.size + sides.length.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:543-546
theorem levelsReserveNiches_iff_length_le_and_nest_size {M : Nat} (R₀ : WrapInterval M)
    (sides : List Side) :
    (LevelsReserveNiches R₀ sides ↔ sides.length ≤ M - R₀.size) ∧
      (sides.length ≤ M - R₀.size → (nest R₀ sides).size = R₀.size + sides.length) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `Side`, `nest`, `LevelsReserveNiches`.

**Tier.** T1: folklore made precise; adjacent reservation is documented engineering (prior art); the composition over levels was not found stated or mechanized.

**Hypothesis ledger.**

No hypotheses.

**Depth.** substantive: an induction on the list of sides carrying the size invariant through R5.1.

**Non-vacuity witness.** M = 4, R0 = [1, 1], three levels, all-low and all-high. (`nv_levelsReserveNiches_iff_length_le_and_nest_size`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The levels are modelled at the validity-set level; the per-level layout is the imported niche-filled layout (`nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt`).
- Adjacent reservation is one strategy; the bound for arbitrary layouts of the flattened enum is `exists_lawful_extEnum_intervalV_iff_le_sub_size`. A non-adjacent reservation can be lawful for one level yet fragment the valid set and lose contiguous capacity (`cex_folklore_nonadjacent_reservation_fragments`: over [0, 1] in Fin 8, reserving 4 gives {0, 1, 4}, which is not an interval set (`IsWrapIntervalSet`) and has hull [0, 4]; four contiguous tags then no longer fit, whereas after adjacent reservation five do; both sets have five niches).
- Past capacity the second conjunct says nothing; `nest` then wraps and collapses rather than saturating (`ex_nest_past_capacity`: over [1, 1] in Fin 4, four upward levels end at the singleton [1, 1], size 1, not 5).
- The innermost valid set is a non-empty wrapping interval R0 of a single niche field. Validity sets that are not one wrapping interval (with internal holes), the empty validity set (an uninhabited payload), payloads with several fields (where another field's niches could be used), and wrappers that hide niches are not modelled.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/lib.rs:2075-2087 (source comment in Niche::reserve): "Extend the range of valid values being reserved by moving either `v.start` or `v.end` bound." (line 2075-2076).
- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:351-372: theorem opt_opt_nonZero_no_decEnc_layout_in_payload_size (two-level Option over an n-byte NonZero payload has no decode-after-encode layout in n bytes). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.

**Design question.** How do nested Option levels compose when each reserves a value next to the current valid interval?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Nested `Option` levels are modelled as repeated adjacent reservation (`nest`), compared with the source comment of rustc's `Niche::reserve` (`compiler/rustc_abi/src/lib.rs:2075-2076`). Whether rustc nests `Option` levels this way is not claimed; no model–system relation is proved.

#### R5.4 `exists_lawful_extEnum_intervalV_iff_le_sub_size` (characterization, T0)

**Plain claim.** For every valid interval R0 of n-byte patterns and every j, an enum with j dataless variants over the payload whose valid values are R0 has some lawful layout in the payload's n bytes (any layout, adjacent reservation or not) iff j <= 256^n - R0.size.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:593-595
theorem exists_lawful_extEnum_intervalV_iff_le_sub_size {n : Nat} (R₀ : WrapInterval (256 ^ n))
    (j : Nat) :
    (∃ L : Layout (ExtEnum j (intervalV R₀)) n, Lawful L) ↔ j ≤ 256 ^ n - R₀.size := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `WrapInterval`, `WrapInterval.size`, `intervalV`, `Layout`, `Lawful`, `ExtEnum`.

**Tier.** T0: re-derivation; a corollary of the imported cardinality theorem and R3.3.

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: the imported cardinality theorem rewritten with R3.3.

**Non-vacuity witness.** n = 1, R0 = [1, 255], j = 1 (lawful layout exhibited via the imported cardinality theorem). (`nv_exists_lawful_extEnum_intervalV`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- `ExtEnum j V` flattens j levels of Option into j dataless variants; the bijection with nested Option is not stated here (the imported two-level impossibility `opt_opt_nonZero_no_decEnc_layout_in_payload_size` proves its j = 2 instance for NonZero; `ex_intervalV_nonZero` identifies the NonZero validity with `intervalV [1, 255]`).
- The statement is about `Lawful` layouts of exactly the payload size n. Layouts that satisfy `DecEnc` without being required to be `Canonical`, or have a size m <= n, are covered by the imported `le_numInvalid_of_decEnc_of_size_le` (not restated as a theorem of this package).
- A corollary of the imported cardinality theorem and `nichesCount_intervalV`.
- The same payload-shape limits as R5.3 apply (a single niche field whose valid set is a non-empty wrapping interval).

**Prior art.**

- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:335-346: theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches (k dataless variants fit in the payload's bytes under some lawful layout iff k <= numInvalid V). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.
- google/zerocopy branch reference, package enum-niche-layout-guarantees-and-validity-invariants, published at 00c8f874bf1e70c933b7a2ea2572a76c1baa7327 (Lean sources unchanged at the latest correction f9bee82a6d3f8bb6698b4c9e716138018db94d4d), lean/Toy/Niche/Results.lean:351-372: theorem opt_opt_nonZero_no_decEnc_layout_in_payload_size (two-level Option over an n-byte NonZero payload has no decode-after-encode layout in n bytes). Copied with its proof into lean/Toy/WrapNiche/Imported/Results.lean.

**Design question.** How do nested Option levels compose when each reserves a value next to the current valid interval?

Basis: execution (Lean kernel check).

#### R6.1 `setDisc_operational_untagged_isSome_iff_of_tagsDisjoint` (characterization, T1)

**Plain claim.** For a toy operational layout whose tags are all invalid for the niche-field validity (hypothesis): operational `SetDiscriminant u`, which reads the discriminant with the checked reader `OpLayout.readDisc` (the checked decoder of `genLayout`; for span < 256^nw it rejects dead slots and unused niches, `genLayout_dec_isSome_iff_classify_of_span_lt`) and is undefined behaviour unless the result is u, is free of undefined behaviour on a place iff the place's niche field lies inside the place (for nw >= 1; for nw = 0 there is no byte to check), is initialized, and holds a valid value; in particular, after writing a value x into a niche field that lies inside the place, it is free of undefined behaviour iff x is valid.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:604-609
theorem setDisc_operational_untagged_isSome_iff_of_tagsDisjoint (L : OpLayout)
    (hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span) :
    (∀ p, (setDisc .operational L L.E.u p).isSome = true ↔
      ∃ x, L.readNiche p = some x ∧ L.V x = true) ∧
    (∀ p (x : Pat L.nw), L.no + L.nw ≤ p.length →
      ((setDisc .operational L L.E.u (L.writeNiche p x)).isSome = true ↔ L.V x = true)) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `TagsDisjoint`, `OpLayout`, `OpLayout.readNiche`, `OpLayout.writeNiche`, `setDisc`, `Pat`.

**Tier.** T1: folklore made precise; the interpreter double-check is documented (prior art).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span` | A valid value that is also a tag reads as a niche variant. | tight: counterexample `cex_setDisc_operational_untagged_isSome_iff_hdisj` (witness class: an instance with a one-byte niche field, every value valid) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: unfolding the checked reader; the second conjunct uses the little-endian round trip of the niche field.

**Non-vacuity witness.** The layout Lop (1-byte niche at offset 1, tags 253/254/255, valid 0..=252). (`nv_setDisc_operational_untagged_isSome_iff`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Write order under `Sem.operational`: by the first conjunct, SetDiscriminant u is defined exactly when the niche field already holds a valid value; so from uninitialized niche bytes or from a niche tag (invalid under hdisj) 'SetDiscriminant u; write payload' is undefined behaviour while 'write payload; SetDiscriminant u' is defined (instance: `cex_folklore_payload_write_setDisc_noncommuting`), and if the niche field already holds a valid value SetDiscriminant u is defined before any write. Writes disjoint from the niche field commute with SetDiscriminant u (`run_write_setDisc_comm_of_disjointFromNiche`). Under `Sem.erased` SetDiscriminant u performs no check.
- The checked `readDisc` rejects unused niches and dead slots; under a lenient reader that returned u for every value outside the tag interval, the 'iff x is valid' form would fail for unused niches (not proved here).
- `L.V` is the validity of the niche field alone; it stands in for the niche scalar's valid range, which in rustc is a single wrapping range. Operational `SetDiscriminant u` reads the niche field alone, not the validity of other fields of the untagged variant's payload. The niche field is read little-endian from provenance-free bytes; big-endian targets and pointer-valued niches are not modelled.
- If the untagged variant is uninhabited (no niche value is valid), operational SetDiscriminant u is undefined behaviour on every place while erased SetDiscriminant u is a no-op (`ex_setDisc_untagged_uninhabited`); rustc rejects uninhabited variants before it treats the untagged variant (prior art, derived (modeling bridge)).
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:15-44 (documentation and source comments): "If the variant is uninhabited, this is UB." (line 17); for the untagged variant: "No need to write the tag here, because an untagged variant is implicitly encoded. For `Niche`-optimized enums, this works by simply by having a value that is outside the niche variants. But what if the data stored here does not actually encode this variant? That would be bad! So let's double-check..." (lines 33-37), followed by a read of the discriminant and InvalidNichedEnumVariantWritten if it differs (lines 38-41).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:187-200 and 210-215 (source comments): "The untagged variant can be in the niche range, but even then it is not a valid encoding. Codegen inserts an `assume` here so we really have to make this UB." (lines 188-190); "Ensure the tag is in its layout range. Codegen adds range metadata on the discriminant load so we really have to make this UB." (lines 195-196); "Reading the discriminant of an uninhabited variant is UB." (line 210).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/interpret/error.rs:426-427 (documentation): "Trying to set discriminant to the niched variant, but the value does not match." InvalidNichedEnumVariantWritten { enum_ty: Ty<'tcx> },
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:357-361 (documentation): "Write the discriminant for a variant to the enum Place." and "This does not necessarily write to the entire place; instead, it writes to the minimum set of bytes as required by the layout for the type."
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:246-257 and 290-297 (source): `tag_for_variant` raises `UninhabitedEnumVariantWritten` for an uninhabited variant (lines 255-257) before it returns no tag for the untagged variant (lines 290-297); and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_codegen_ssa/src/mir/place.rs:254-273 and 499-527 (source): `codegen_set_discr` emits `bx.abort()` for an uninhabited variant (lines 262-266), stores the tag for a tagged variant (lines 267-270) and does nothing for `Ok(None)` (line 271), which `codegen_tag_value` returns for the untagged variant of a niche encoding (lines 504 and 524-526). `Sem.erased` mirrors the no-write case (no check, no write) but not the uninhabited-variant abort: erased `SetDiscriminant u` is a no-op even when the untagged variant has no valid value (`ex_setDisc_untagged_uninhabited`). derived (modeling bridge).

**Design question.** How do payload writes interact with a SetDiscriminant that checks the untagged variant (as the interpreter does) versus one that writes nothing and checks nothing?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). Operational `SetDiscriminant u` is compared with the interpreter's documented behaviour: for the untagged variant it writes no tag and double-checks by reading the discriminant, reporting `InvalidNichedEnumVariantWritten` if it differs (`compiler/rustc_const_eval/src/interpret/discriminant.rs:33-41`; error text `compiler/rustc_middle/src/mir/interpret/error.rs:426-427`), and `tag_for_variant` rejects an uninhabited variant before it treats the untagged variant (`discriminant.rs:246-257`, `290-297`), all at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe. The comparison reads the quoted source against the Lean definitions of `setDisc` and `OpLayout.readDisc`; it is not a proved relation.

#### R6.2 `run_erased_eq_some_of_run_operational_eq_some` (theorem, T1)

**Plain claim.** For every toy operational layout, every program of field writes, SetDiscriminant and discriminant reads, and every start state: if the program runs without undefined behaviour under the operational semantics, it produces the same place and the same read results under the erased semantics (`SetDiscriminant u` as a no-op); there is no hypothesis (in both semantics a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:643-645
theorem run_erased_eq_some_of_run_operational_eq_some (L : OpLayout) (prog : List Op)
    (s r : Bytes × List Nat) :
    run .operational L prog s = some r → run .erased L prog s = some r := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `Bytes`, `OpLayout`, `Op`, `run`.

**Tier.** T1: folklore made precise (as R6.1).

**Hypothesis ledger.**

No hypotheses.

**Depth.** shallow: induction on the program; by definition the two semantics differ at SetDiscriminant u and nowhere else.

**Non-vacuity witness.** Lop, program [write payload 5; SetDiscriminant 1; read]. (`nv_run_erased_eq_some_of_run_operational_eq_some`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Not an equivalence: operational SetDiscriminant u on uninitialized bytes is undefined behaviour while the erased one is a no-op (`cex_folklore_erasure_not_equivalent`); with an uninhabited untagged variant the two differ on every place (`ex_setDisc_untagged_uninhabited`).
- The refinement is stated for this concrete pair of semantics; no general refinement framework is proved.
- Out-of-bounds writes and tag writes are undefined behaviour in both semantics alike, so they do not separate them. In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:15-44 (documentation and source comments): "If the variant is uninhabited, this is UB." (line 17); for the untagged variant: "No need to write the tag here, because an untagged variant is implicitly encoded. For `Niche`-optimized enums, this works by simply by having a value that is outside the niche variants. But what if the data stored here does not actually encode this variant? That would be bad! So let's double-check..." (lines 33-37), followed by a read of the discriminant and InvalidNichedEnumVariantWritten if it differs (lines 38-41).
- minirust/minirust@063d784186d3252bee242217f218223205c0b568 spec/lang/step/statements.md:61-85 (specification): `Statement::SetDiscriminant` looks up the variant's `tagger` (lines 69-73) and stores its entries through `encode_discriminant(accessor, tagger)` (line 82) at offsets checked by `ptr_offset_inbounds` (line 78); it reads nothing from the place. With an empty `tagger` it writes nothing and checks nothing, which corresponds to `Sem.erased` rather than to `Sem.operational`.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:246-257 and 290-297 (source): `tag_for_variant` raises `UninhabitedEnumVariantWritten` for an uninhabited variant (lines 255-257) before it returns no tag for the untagged variant (lines 290-297); and rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_codegen_ssa/src/mir/place.rs:254-273 and 499-527 (source): `codegen_set_discr` emits `bx.abort()` for an uninhabited variant (lines 262-266), stores the tag for a tagged variant (lines 267-270) and does nothing for `Ok(None)` (line 271), which `codegen_tag_value` returns for the untagged variant of a niche encoding (lines 504 and 524-526). `Sem.erased` mirrors the no-write case (no check, no write) but not the uninhabited-variant abort: erased `SetDiscriminant u` is a no-op even when the untagged variant has no valid value (`ex_setDisc_untagged_uninhabited`). derived (modeling bridge).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:357-361 (documentation): "Write the discriminant for a variant to the enum Place." and "This does not necessarily write to the entire place; instead, it writes to the minimum set of bytes as required by the layout for the type."

**Design question.** How do payload writes interact with a SetDiscriminant that checks the untagged variant (as the interpreter does) versus one that writes nothing and checks nothing?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). `Sem.erased` is compared with MiniRust's `Statement::SetDiscriminant`, which stores the entries of the variant's tagger and reads nothing from the place, so an empty tagger writes and checks nothing (minirust/minirust@063d784186d3252bee242217f218223205c0b568 `spec/lang/step/statements.md:61-85`), and with the code generator's no-write case for the untagged variant (`compiler/rustc_codegen_ssa/src/mir/place.rs:254-273`, `499-527` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe); `Sem.operational` is compared with the interpreter's double-check (`compiler/rustc_const_eval/src/interpret/discriminant.rs:33-41`). These comparisons read the quoted text against the Lean definitions; none is a proved relation.

#### R6.3 `run_write_setDisc_comm_of_disjointFromNiche` (theorem, T1)

**Plain claim.** For every toy operational layout, both semantics, every variant v (including the untagged one) and every state: if the byte range of a `write` operation does not overlap the niche field (hypothesis), the programs 'write; SetDiscriminant v' and 'SetDiscriminant v; write' give the same result, undefined behaviour included (a write that does not fit in the place is undefined behaviour in both orders).

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:674-676
theorem run_write_setDisc_comm_of_disjointFromNiche (sem : Sem) (L : OpLayout) (v off : Nat)
    (bs : List (Fin 256)) (hdis : L.DisjointFromNiche off bs.length) (s : Bytes × List Nat) :
    run sem L [.write off bs, .setDisc v] s = run sem L [.setDisc v, .write off bs] s := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `Bytes`, `OpLayout`, `OpLayout.DisjointFromNiche`, `Sem`, `run`.

**Tier.** T1: folklore made precise; the no-overlap discipline between tag and fields is specified in MiniRust (prior art).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hdis : L.DisjointFromNiche off bs.length` | A write over the niche byte after SetDiscriminant clobbers the tag (the value then reads as another variant). | tight: counterexample `cex_run_write_setDisc_comm_hdis` (witness class: an instance with a one-byte niche field and a one-byte write over it) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** shallow: frame lemmas for disjoint byte ranges; SetDiscriminant keeps the length of the place.

**Non-vacuity witness.** Lop, write [9] at byte 0. (`nv_run_write_setDisc_comm_of_disjointFromNiche`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The statement covers the untagged variant too: no restriction to dataless variants is needed.
- Writes that overlap the niche field do not commute in general: with a tag (`cex_run_write_setDisc_comm_hdis`) and with operational SetDiscriminant u (`cex_folklore_payload_write_setDisc_noncommuting`).
- `DisjointFromNiche` is conservative: an empty write strictly inside the niche field is rejected although it overlaps nothing.
- Aliasing, borrows and concurrency are not modelled; a place is a single byte list.
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**Prior art.**

- minirust/minirust@063d784186d3252bee242217f218223205c0b568 spec/lang/types.md:101-126 and spec/lang/step/statements.md:61-85 (specification): enums carry a per-variant `tagger` ("MUST NOT touch any bytes written by the actual type of the variant and vice versa.", types.md:105-106) and a `Discriminator` decision tree over ranges of tag values; SetDiscriminant writes the variant's tagger entries. An extensional decision-tree encoding, not the affine one modelled here.
- minirust/minirust@063d784186d3252bee242217f218223205c0b568 spec/lang/step/statements.md:61-85 (specification): `Statement::SetDiscriminant` looks up the variant's `tagger` (lines 69-73) and stores its entries through `encode_discriminant(accessor, tagger)` (line 82) at offsets checked by `ptr_offset_inbounds` (line 78); it reads nothing from the place. With an empty `tagger` it writes nothing and checks nothing, which corresponds to `Sem.erased` rather than to `Sem.operational`.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:357-361 (documentation): "Write the discriminant for a variant to the enum Place." and "This does not necessarily write to the entire place; instead, it writes to the minimum set of bytes as required by the layout for the type."

**Design question.** How do payload writes interact with a SetDiscriminant that checks the untagged variant (as the interpreter does) versus one that writes nothing and checks nothing?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). MiniRust requires a variant's tagger not to touch bytes written by the variant's fields (`spec/lang/types.md:105-106` at minirust/minirust@063d784186d3252bee242217f218223205c0b568), and rustc documents that `SetDiscriminant` writes the minimum set of bytes required by the layout (`compiler/rustc_middle/src/mir/syntax.rs:357-361`); `DisjointFromNiche` is the toy's counterpart of that separation. This is reasoning from the quoted text, not a proved relation.

#### R6.4 `run_fields_then_setDisc_readDisc_of_disjoint` (theorem, T1)

**Plain claim.** For a toy operational layout and a place, if the niche field lies inside the place, span < 256^nw, every tag is invalid for the niche-field validity, and the field writes ws lie inside the place, are pairwise disjoint and do not overlap the niche field (hypotheses), then under both semantics: for every encodable variant v other than u (`Encodable`: live and in the niche range), 'field writes; SetDiscriminant v; read discriminant' is defined, reads v, leaves v's tag in the niche field and every field write in ws readable as written; and for every valid niche value x, 'field writes; write x to the niche field; SetDiscriminant u; read discriminant' is defined, reads u, leaves x in the niche field and every field write in ws readable as written.

**Statement.**

```lean
-- lean/Toy/WrapNiche/Results.lean:705-719
theorem run_fields_then_setDisc_readDisc_of_disjoint (sem : Sem) (L : OpLayout) (p : Bytes)
    (ws : List (Nat × List (Fin 256))) (hfit : L.no + L.nw ≤ p.length)
    (hspan : L.A.span < 256 ^ L.nw) (hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span)
    (hin : ∀ w ∈ ws, w.1 + w.2.length ≤ p.length)
    (hpw : ws.Pairwise (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1))
    (hws : ∀ w ∈ ws, L.DisjointFromNiche w.1 w.2.length) :
    (∀ v, L.Encodable v → ∃ q,
      run sem L (writesOf ws ++ [.setDisc v, .readDisc]) (p, []) = some (q, [v]) ∧
        L.readNiche q = some (L.A.tagOf (v - L.A.first)) ∧
        ∀ w ∈ ws, readBytes q w.1 w.2.length = some w.2) ∧
    (∀ x : Pat L.nw, L.V x = true → ∃ q,
      run sem L (writesOf ws ++ [.write L.no (leBytes L.nw x.val), .setDisc L.E.u, .readDisc])
        (p, []) = some (q, [L.E.u]) ∧
        L.readNiche q = some x ∧
        ∀ w ∈ ws, readBytes q w.1 w.2.length = some w.2) := by …
```

**Key definitions** (each quoted under Definitions or Imported declarations): `AffineNiche.tagOf`, `TagsDisjoint`, `Bytes`, `readBytes`, `leBytes`, `OpLayout`, `OpLayout.readNiche`, `OpLayout.readDisc`, `OpLayout.Encodable`, `OpLayout.DisjointFromNiche`, `Sem`, `run`, `writesOf`, `Pat`.

**Tier.** T1: folklore made precise (as R6.1).

**Hypothesis ledger.**

| Hypothesis | Purpose | Tightness |
|---|---|---|
| `hfit : L.no + L.nw ≤ p.length` | Without it the tag write of SetDiscriminant v (and the niche write) is out of bounds, which is undefined behaviour. | tight: counterexample `cex_run_fields_then_setDisc_hfit` (witness class: an instance with a three-byte place and the niche byte at offset 5) |
| `hspan : L.A.span < 256 ^ L.nw` | Without it two variants can share a tag, so a tag reads back as another variant. | tight: counterexample `cex_run_fields_then_setDisc_hspan` (witness class: an instance with a one-byte niche field and 257 live variants) |
| `hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span` | Used by the second conjunct: without it a valid niche value can be a tag and does not read as u. | tight: counterexample `cex_run_fields_then_setDisc_hdisj` (witness class: an instance with a one-byte niche field, every value valid) |
| `hin : ∀ w ∈ ws, w.1 + w.2.length ≤ p.length` | Without it a field write is out of bounds, which is undefined behaviour. | tight: counterexample `cex_run_fields_then_setDisc_hin` (witness class: an instance with a two-byte write at offset 2 of a three-byte place) |
| `hpw : ws.Pairwise (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1)` | Without it a later overlapping write overwrites an earlier field. | tight: counterexample `cex_run_fields_then_setDisc_hpw` (witness class: an instance with two different one-byte writes to byte 0) |
| `hws : ∀ w ∈ ws, L.DisjointFromNiche w.1 w.2.length` | Without it the tag write overwrites a field that overlaps the niche field. | tight: counterexample `cex_run_fields_then_setDisc_hws` (witness class: an instance with a one-byte write to the niche byte) |

"tight" means: a counterexample satisfying all the other hypotheses in which the conclusion fails; each counterexample is a theorem stating exactly that (quoted under Witnesses), and the witness class records where it lies. Tightness is not necessity in general.

**Depth.** substantive: composition of the frame lemmas over a list of pairwise disjoint writes, with the little-endian round trip of the niche field.

**Non-vacuity witness.** Lop, three uninitialized bytes, field writes at bytes 0 and 2 (with Encodable 0 and a valid niche value 0). (`nv_run_fields_then_setDisc_readDisc_of_disjoint`).

**Non-claims.**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A sufficient condition. Each hypothesis is tight in the instance class recorded in its ledger entry; none is claimed necessary in general (for example identical overlapping writes, or empty writes, would not break the conclusion; not proved here).
- Write order: writes disjoint from the niche field commute with SetDiscriminant v for every v, including u (`run_write_setDisc_comm_of_disjointFromNiche`). Under `Sem.operational` and when every tag is invalid, SetDiscriminant u is defined exactly when the niche field already holds a valid value (R6.1, first conjunct): starting from uninitialized niche bytes or from a niche tag the valid value has to be written first (instance: `cex_folklore_payload_write_setDisc_noncommuting`), whereas a niche field that already holds a valid value needs no prior write. Under `Sem.erased` SetDiscriminant u performs no check.
- The operational model does not tie field bytes to variants: the writes ws may stand for fields of v placed outside the niche field (rustc's niche-filling layout admits such fields, prior art, derived (modeling bridge)) or for the payload fields of u; `genLayout` (group 2), by contrast, models the variants other than u as dataless.
- Field contents are bytes; no typed validity of the fields is modelled.
- `L.V` is the validity of the niche field alone; it stands in for the niche scalar's valid range, which in rustc is a single wrapping range. Operational `SetDiscriminant u` reads the niche field alone, not the validity of other fields of the untagged variant's payload. The niche field is read little-endian from provenance-free bytes; big-endian targets and pointer-valued niches are not modelled.
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_const_eval/src/interpret/discriminant.rs:15-44 (documentation and source comments): "If the variant is uninhabited, this is UB." (line 17); for the untagged variant: "No need to write the tag here, because an untagged variant is implicitly encoded. For `Niche`-optimized enums, this works by simply by having a value that is outside the niche variants. But what if the data stored here does not actually encode this variant? That would be bad! So let's double-check..." (lines 33-37), followed by a read of the discriminant and InvalidNichedEnumVariantWritten if it differs (lines 38-41).
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/mir/syntax.rs:357-361 (documentation): "Write the discriminant for a variant to the enum Place." and "This does not necessarily write to the entire place; instead, it writes to the minimum set of bytes as required by the layout for the type."
- minirust/minirust@063d784186d3252bee242217f218223205c0b568 spec/lang/types.md:101-126 and spec/lang/step/statements.md:61-85 (specification): enums carry a per-variant `tagger` ("MUST NOT touch any bytes written by the actual type of the variant and vice versa.", types.md:105-106) and a `Discriminator` decision tree over ranges of tag values; SetDiscriminant writes the variant's tagger entries. An extensional decision-tree encoding, not the affine one modelled here.
- minirust/minirust@063d784186d3252bee242217f218223205c0b568 spec/lang/step/statements.md:61-85 (specification): `Statement::SetDiscriminant` looks up the variant's `tagger` (lines 69-73) and stores its entries through `encode_discriminant(accessor, tagger)` (line 82) at offsets checked by `ptr_offset_inbounds` (line 78); it reads nothing from the place. With an empty `tagger` it writes nothing and checks nothing, which corresponds to `Sem.erased` rather than to `Sem.operational`.
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_abi/src/layout.rs:652-680 (source): in the niche-filling layout computation every variant other than the largest one is checked to fit either before the niche ("// This variant will fit before the niche.", line 660) or after it ("// Determine if it'll fit after the niche.", line 664), with its field offsets shifted (lines 673-675); such variants may therefore carry fields outside the niche field. `genLayout` models every variant other than `u` as dataless; the operational model (group 6) does not tie field bytes to variants.

**Design question.** How do payload writes interact with a SetDiscriminant that checks the untagged variant (as the interpreter does) versus one that writes nothing and checks nothing?

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). The operational model leaves the owner of the field bytes open; that rustc's niche-filling layout admits fields of tagged variants outside the niche field is read from `compiler/rustc_abi/src/layout.rs:652-680` at rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe, and the write-order statements are compared with the interpreter's documented double-check (`compiler/rustc_const_eval/src/interpret/discriminant.rs:33-41`) and with MiniRust's `SetDiscriminant` (`spec/lang/step/statements.md:61-85`). None of these is a proved relation.

### Auxiliary lemmas cited by name

Proved lemmas and corollaries quoted for reference: those that the cards cite by name, `pos_of_fin` (used in definitions and statements quoted in this report), and `offset_self` and `offset_zero` (basic facts about `offset`, cited by no card). The Role column of the Evidence table lists, for each, the cards whose text names it.

```lean
-- lean/Toy/WrapNiche/Interval.lean:25
theorem pos_of_fin {M : Nat} (x : Fin M) : 0 < M := …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:167-168
theorem nichesCount_eq_numInvalid {n : Nat} (V : Imported.Validity n) :
    nichesCount (M := 256 ^ n) V = Imported.numInvalid V := …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:171
theorem offset_self {M : Nat} (s : Fin M) : offset s s = 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:178-179
theorem subTest_iff_originTest_start {M : Nat} (I : WrapInterval M) (x : Fin M) :
    subTest I x ↔ originTest I.s I x := by …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:185-186
theorem offset_zero {M : Nat} (x : Fin M) :
    offset ⟨0, pos_of_fin x⟩ x = x.val := by …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:192-193
theorem unsignedTest_iff_originTest_zero {M : Nat} (I : WrapInterval M) (x : Fin M) :
    unsignedTest I x ↔ originTest ⟨0, pos_of_fin x⟩ I x := by …
```

```lean
-- lean/Toy/WrapNiche/Interval.lean:201-202
theorem signedTestI8_iff_originTest_128 (I : WrapInterval 256) (x : Fin 256) :
    signedTestI8 I x ↔ originTest 128 I x := by …
```

```lean
-- lean/Toy/WrapNiche/Affine.lean:207-209
theorem naturalFirst_naturalLast_spec (k u : Nat) (hk : 2 ≤ k) :
    naturalFirst u < k ∧ naturalFirst u ≠ u ∧ naturalLast k u < k ∧ naturalLast k u ≠ u ∧
      ∀ i, i < k → i ≠ u → naturalFirst u ≤ i ∧ i ≤ naturalLast k u := by …
```

```lean
-- lean/Toy/WrapNiche/Affine.lean:214-215
theorem naturalSpan_eq (k u : Nat) (hk : 2 ≤ k) :
    naturalSpan k u = if u = 0 ∨ u = k - 1 then k - 2 else k - 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Affine.lean:225-226
theorem rotTagsInvalid_iff_tagsDisjoint_sub_two {M : Nat} (V : Fin M → Bool) (k : Nat)
    (ns : Fin M) (hk : 2 ≤ k) : RotTagsInvalid V k ns ↔ TagsDisjoint V ns (k - 2) := …
```

```lean
-- lean/Toy/WrapNiche/ProofLemmas.lean:133-134
theorem genLayout_canonical {n : Nat} (E : EnumSpec) (A : AffineNiche (256 ^ n))
    (V : Validity n) : Canonical (genLayout E A V) := by …
```

```lean
-- lean/Toy/WrapNiche/Corollaries.lean:18-20
theorem sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hH : IsHull V H) :
    M - H.size = nichesCount V ↔ IsWrapIntervalSet V := by …
```

```lean
-- lean/Toy/WrapNiche/Corollaries.lean:36-39
theorem exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull {M : Nat}
    (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (k : Nat) :
    (∃ ns : Fin M, RotTagsInvalid V k ns) ↔ k - 1 ≤ M - H.size := by …
```

```lean
-- lean/Toy/WrapNiche/Corollaries.lean:57-60
theorem exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H) (k u : Nat) (hk : 2 ≤ k) :
    (∃ ns : Fin M, TagsDisjoint V ns (naturalSpan k u)) ↔
      (if u = 0 ∨ u = k - 1 then k - 1 else k) ≤ M - H.size := by …
```

### Examples

Concrete objects and definition examples: intended positive examples each definition admits and negative examples it rejects, including wrapping and degenerate cases.

```lean
-- lean/Toy/WrapNiche/Examples.lean:17
def V02 : Fin 4 → Bool := fun x => x.val == 0 || x.val == 2
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:20
def V01 : Fin 4 → Bool := fun x => decide (x.val < 2)
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:23
def V0 : Fin 4 → Bool := fun x => x.val == 0
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:26
def Vlow : Validity 1 := fun x => decide (x.val < 253)
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:29
def Vlt254 : Validity 1 := fun x => decide (x.val < 254)
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:32
def Vmid : Validity 1 := fun x => decide (1 ≤ x.val ∧ x.val ≤ 253)
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:35
def A0 : AffineNiche 256 := ⟨0, 2, 254⟩
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:38
def Ag : AffineNiche 256 := ⟨0, 2, 253⟩
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:41
def E1 : EnumSpec := ⟨3, 1, fun _ => true⟩
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:44
def E2 : EnumSpec := ⟨3, 0, fun i => i != 1⟩
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:48
def Lop : OpLayout := ⟨1, 1, E1, Ag, Vlow⟩
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:51
def uninit3 : Bytes := [none, none, none]
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:62
theorem ex_wrapAdd : wrapAdd (255 : Fin 256) 3 = 2 ∧ wrapAdd (5 : Fin 256) 3 = 8 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:64
theorem ex_wrapSub : wrapSub (1 : Fin 256) 3 = 254 ∧ wrapSub (5 : Fin 256) 3 = 2 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:66-67
theorem ex_offset : offset (250 : Fin 256) 3 = 9 ∧ offset (3 : Fin 256) 250 = 247 ∧
    offset (7 : Fin 256) 7 = 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:72-73
theorem ex_mem_pos : (⟨255, 0⟩ : WrapInterval 256).Mem 255 ∧
    (⟨255, 0⟩ : WrapInterval 256).Mem 0 ∧ (⟨2, 5⟩ : WrapInterval 8).Mem 3 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:76-77
theorem ex_mem_neg : ¬ (⟨255, 0⟩ : WrapInterval 256).Mem 1 ∧
    ¬ (⟨255, 0⟩ : WrapInterval 256).Mem 254 ∧ ¬ (⟨2, 5⟩ : WrapInterval 8).Mem 6 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:79-81
theorem ex_size : (⟨255, 0⟩ : WrapInterval 256).size = 2 ∧
    (⟨0, 255⟩ : WrapInterval 256).size = 256 ∧ (⟨1, 0⟩ : WrapInterval 256).size = 256 ∧
    (⟨7, 7⟩ : WrapInterval 256).size = 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:83-84
theorem ex_compl : (⟨255, 0⟩ : WrapInterval 256).compl = ⟨1, 254⟩ ∧
    (⟨0, 3⟩ : WrapInterval 4).compl = ⟨0, 3⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:88
theorem ex_toI8 : toI8 127 = 127 ∧ toI8 128 = -128 ∧ toI8 255 = -1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:90-94
theorem ex_tests : subTest (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    ¬ unsignedTest (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    signedTestI8 (⟨255, 0⟩ : WrapInterval 256) 0 ∧
    ¬ signedTestI8 (⟨127, 128⟩ : WrapInterval 256) 128 ∧
    originTest (128 : Fin 256) ⟨255, 0⟩ 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:97
theorem ex_exactFor_pos : ExactFor subTest (⟨255, 0⟩ : WrapInterval 256) := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:100-101
theorem ex_twoBranchTest : twoBranchTest (0 : Fin 256) ⟨255, 0⟩ 255 ∧
    ¬ twoBranchTest (0 : Fin 256) ⟨255, 0⟩ 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:104
theorem ex_exactFor_neg : ¬ ExactFor unsignedTest (⟨255, 0⟩ : WrapInterval 256) := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:109-110
theorem ex_covers_pos : Covers (⟨0, 2⟩ : WrapInterval 4) V02 ∧
    Covers (⟨2, 0⟩ : WrapInterval 4) V02 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:112
theorem ex_covers_neg : ¬ Covers (⟨0, 1⟩ : WrapInterval 4) V02 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:116-117
theorem ex_isHull_pos : IsHull V02 ⟨0, 2⟩ ∧ IsHull V02 ⟨2, 0⟩ ∧
    IsHull (fun x : Fin 4 => x.val == 3 || x.val == 0) ⟨3, 0⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:120
theorem ex_isHull_neg : ¬ IsHull V02 ⟨0, 3⟩ ∧ ¬ IsHull V02 ⟨0, 1⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:122-123
theorem ex_isWrapIntervalSet_pos : IsWrapIntervalSet (intervalV (⟨3, 1⟩ : WrapInterval 4)) ∧
    IsWrapIntervalSet V01 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:125
theorem ex_isWrapIntervalSet_neg : ¬ IsWrapIntervalSet V02 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:127-128
theorem ex_intervalV : intervalV (⟨3, 0⟩ : WrapInterval 4) 3 = true ∧
    intervalV (⟨3, 0⟩ : WrapInterval 4) 1 = false := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:130-131
theorem ex_nichesCount : nichesCount V02 = 2 ∧ nichesCount V01 = 2 ∧
    nichesCount (fun _ : Fin 4 => true) = 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:135-136
theorem ex_affine : A0.tagOf 0 = 254 ∧ A0.tagOf 2 = 0 ∧ A0.tagInterval = ⟨254, 0⟩ ∧
    A0.last = 2 ∧ affineTags A0 ⟨2, by decide⟩ = 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:140-142
theorem ex_tagInterval_collapses : (⟨0, 256, 0⟩ : AffineNiche 256).tagInterval = ⟨0, 0⟩ ∧
    (⟨0, 256, 0⟩ : AffineNiche 256).tagOf 1 = 1 ∧
    ¬ (⟨0, 256, 0⟩ : AffineNiche 256).tagInterval.Mem 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:146
theorem ex_decodeIdx : decodeIdx 5 A0 0 = 2 ∧ decodeIdx 5 A0 1 = 5 ∧ decodeIdx 5 A0 254 = 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:149
theorem ex_tagsDisjoint_pos : TagsDisjoint Vmid 254 2 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:151
theorem ex_tagsDisjoint_neg : ¬ TagsDisjoint Vmid 253 2 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:154
theorem ex_affineLayout_pos : Lawful (affineLayout Vmid A0) := …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:158
theorem ex_affineLayout_neg : ¬ Lawful (affineLayout (allV 1) A0) := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:164
theorem ex_live_pos : E1.Live 0 ∧ E1.Live 2 ∧ E2.Live 2 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:167
theorem ex_live_neg : ¬ E1.Live 1 ∧ ¬ E1.Live 3 ∧ ¬ E2.Live 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:171-172
theorem ex_live_u_ge_k : (⟨2, 5, fun _ => true⟩ : EnumSpec).Live 0 ∧
    (⟨2, 5, fun _ => true⟩ : EnumSpec).Live 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:174
theorem ex_liveInRange_pos : LiveInRange E1 Ag := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:176
theorem ex_liveInRange_neg : LiveInRange E1 (⟨1, 1, 253⟩ : AffineNiche 256) → False := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:180
theorem ex_genLayout_pos : Lawful (genLayout E1 Ag Vlow) := …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:183
theorem ex_genLayout_neg : ¬ Lawful (genLayout E1 Ag (allV 1)) := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:190-193
theorem ex_classify : classify E1 Ag (fun x => decide (x.val < 250)) 0 = .valid ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 253 = .liveTag ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 254 = .deadTag ∧
    classify E1 Ag (fun x => decide (x.val < 250)) 251 = .unusedNiche := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:197-198
theorem ex_naturalSpan : naturalSpan 3 0 = 1 ∧ naturalSpan 3 2 = 1 ∧ naturalSpan 3 1 = 2 ∧
    naturalFirst 0 = 1 ∧ naturalLast 3 2 = 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:202-204
theorem ex_rotated : rotIdx 3 1 2 = 0 ∧ rotIdx 3 1 0 = 1 ∧ rotIdx 3 1 1 = 2 ∧
    rotTag 3 1 (254 : Fin 256) 0 = 255 ∧ rotDecodeIdx 3 1 (254 : Fin 256) 254 = 2 ∧
    rotDecodeIdx 3 1 (254 : Fin 256) 255 = 0 ∧ rotDecodeIdx 3 1 (254 : Fin 256) 5 = 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:209-210
theorem ex_rotTagsInvalid_pos : RotTagsInvalid Vlt254 3 254 ∧
    RotTagsInvalid (fun _ : Fin 2 => true) 1 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:213
theorem ex_rotTagsInvalid_neg : ¬ RotTagsInvalid Vlt254 3 253 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:219-221
theorem ex_extend : extend (⟨250, 255⟩ : WrapInterval 256) .high = ⟨250, 0⟩ ∧
    adjNiche (⟨0, 5⟩ : WrapInterval 256) .low = 255 ∧
    nest (⟨1, 1⟩ : WrapInterval 8) [.low, .high] = ⟨0, 2⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:225-226
theorem ex_extend_full : extend (⟨0, 3⟩ : WrapInterval 4) .high = ⟨0, 0⟩ ∧
    (extend (⟨0, 3⟩ : WrapInterval 4) .high).size = 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:228-229
theorem ex_levelsReserveNiches_pos :
    LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .high, .high] := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:231-232
theorem ex_levelsReserveNiches_neg :
    ¬ LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .high, .high, .low] := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:238-242
theorem ex_bytes : writeBytes uninit3 1 [7] = [none, some 7, none] ∧
    writeBytes [none] 0 [1, 2] = [some 1] ∧
    readBytes [none, some 7, none] 1 1 = some [7] ∧
    readBytes [none, some 7, none] 0 2 = none ∧ readBytes [some 7] 0 2 = none ∧
    leVal [1, 2] = 513 ∧ leBytes 2 513 = [1, 2] := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:246-247
theorem ex_run_write_oob : run .operational Lop [.write 2 [7, 8]] (uninit3, []) = none ∧
    run .operational Lop [.write 1 [7]] (uninit3, []) = some ([none, some 7, none], []) := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:250-251
theorem ex_readNiche : Lop.readNiche [none, some 5, none] = some 5 ∧
    Lop.readNiche [some 5, none, none] = none := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:255-259
theorem ex_readDisc : Lop.readDisc [none, some 5, none] = some 1 ∧
    Lop.readDisc [none, some 253, none] = some 0 ∧
    Lop.readDisc [none, some 255, none] = some 2 ∧
    Lop.readDisc [none, some 254, none] = none ∧
    Lop.readDisc [none, some 252, none] = some 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:263-265
theorem ex_readDisc_unusedNiche :
    ({ Lop with V := fun x => decide (x.val < 250) } : OpLayout).readDisc [none, some 251, none] =
      none := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:267-268
theorem ex_encodable : Lop.Encodable 0 ∧ Lop.Encodable 2 ∧ ¬ Lop.Encodable 1 ∧
    ¬ Lop.Encodable 3 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:270-271
theorem ex_disjointFromNiche : Lop.DisjointFromNiche 0 1 ∧ Lop.DisjointFromNiche 2 1 ∧
    ¬ Lop.DisjointFromNiche 0 2 ∧ ¬ Lop.DisjointFromNiche 1 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:276-279
theorem ex_setDisc : setDisc .operational Lop 2 uninit3 = some [none, some 255, none] ∧
    setDisc .operational Lop 1 uninit3 = none ∧ setDisc .erased Lop 1 uninit3 = some uninit3 ∧
    setDisc .operational Lop 1 [none, some 5, none] = some [none, some 5, none] ∧
    setDisc .erased Lop 3 uninit3 = none := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:283-284
theorem ex_setDisc_oob : setDisc .operational Lop 0 [none] = none ∧
    setDisc .erased Lop 2 [none] = none := by …
```

```lean
-- lean/Toy/WrapNiche/Examples.lean:286-288
theorem ex_run : run .operational Lop [.write 0 [9], .setDisc 0, .readDisc] (uninit3, []) =
      some ([some 9, some 253, none], [0]) ∧
    run .operational Lop [.readDisc] (uninit3, []) = none := by …
```

### Witnesses

Naming: `nv_<result>` states that a concrete instance satisfies all hypotheses of a main result; `cex_<result>_<hyp>` states that a concrete instance satisfies every hypothesis except `<hyp>` and that the conclusion fails; `pc_<result>` is a positive control for an impossibility; `cex_folklore_<name>` refutes an informal claim; `ex_<name>` is an illustrative instance.

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:23-25
theorem nv_mem_iff_offset_le_offset :
    ((⟨255, 0⟩ : WrapInterval 256).Mem 0 ↔ offset (255 : Fin 256) 0 ≤ offset (255 : Fin 256) 0) ∧
      (⟨255, 0⟩ : WrapInterval 256).Mem 0 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:27
theorem nv_compl_mem_iff_not_mem_of_size_lt : (⟨255, 0⟩ : WrapInterval 256).size < 256 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:32-34
theorem cex_compl_mem_iff_not_mem_of_size_lt_hI :
    ¬ (⟨0, 3⟩ : WrapInterval 4).size < 4 ∧
      ¬ ((⟨0, 3⟩ : WrapInterval 4).compl.Mem 0 ↔ ¬ (⟨0, 3⟩ : WrapInterval 4).Mem 0) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:37-39
theorem nv_originTest_exactFor_iff_offset_le :
    (ExactFor (originTest (0 : Fin 8)) ⟨2, 5⟩ ↔ offset (0 : Fin 8) 2 ≤ offset (0 : Fin 8) 5) ∧
      ExactFor (originTest (0 : Fin 8)) ⟨2, 5⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:42-43
theorem cex_folklore_unsignedTest_255_0 :
    (⟨255, 0⟩ : WrapInterval 256).Mem 255 ∧ ¬ unsignedTest (⟨255, 0⟩ : WrapInterval 256) 255 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:47-48
theorem cex_folklore_signedTestI8_127_128 :
    (⟨127, 128⟩ : WrapInterval 256).Mem 127 ∧ ¬ signedTestI8 ⟨127, 128⟩ 127 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:52-53
theorem pc_signed_and_unsigned_exact_elsewhere :
    ExactFor signedTestI8 ⟨255, 0⟩ ∧ ExactFor unsignedTest (⟨127, 128⟩ : WrapInterval 256) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:56
theorem nv_not_exactFor_originTest_wrapSub_one_of_two_le : 2 ≤ 256 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:60-61
theorem cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM :
    ¬ 2 ≤ 1 ∧ ¬ ¬ ExactFor (originTest (0 : Fin 1)) ⟨wrapSub 0 1, 0⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:65-66
theorem pc_twoBranchTest_exactFor {M : Nat} (o : Fin M) (I : WrapInterval M) :
    ExactFor (twoBranchTest o) I := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:88-90
theorem pc_complTest_exactFor_fin8 : ∀ (o : Fin 8) (I : WrapInterval 8),
    ExactFor (fun J y => if offset o J.s ≤ offset o J.e then originTest o J y
      else ¬ originTest o J.compl y) I := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:94
theorem pc_subTest_exactFor_all_fin8 : ∀ I : WrapInterval 8, ExactFor subTest I := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:100-103
theorem nv_affineLayout_eq_nicheLayoutK_affineTags :
    (∀ p, (affineLayout Vmid A0).dec p = (nicheLayoutK Vmid (affineTags A0)).dec p) ∧
    (∀ p, (affineLayout Vmid ⟨0, 300, 7⟩).dec p =
      (nicheLayoutK Vmid (affineTags (⟨0, 300, 7⟩ : AffineNiche 256))).dec p) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:108-109
theorem nv_affineLayout_lawful_iff_span_lt_and_tagsDisjoint :
    A0.span < 256 ^ 1 ∧ TagsDisjoint Vmid A0.nicheStart A0.span := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:113-116
theorem cex_affineLayout_lawful_overlap :
    A0.span < 256 ^ 1 ∧ ¬ TagsDisjoint (allV 1) A0.nicheStart A0.span ∧
      (affineLayout (allV 1) A0).dec 254 = some (.inl ⟨0, by decide +kernel⟩) ∧
      ¬ Lawful (affineLayout (allV 1) A0) := …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:121-124
theorem cex_affineLayout_lawful_span :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      TagsDisjoint (fun _ : Pat 1 => false) 0 256 ∧
      ¬ Lawful (affineLayout (fun _ : Pat 1 => false) ⟨0, 256, 0⟩) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:133-135
theorem nv_classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint :
    (⟨0, 2, 5⟩ : AffineNiche 8).span < 8 ∧
      TagsDisjoint (fun x : Fin 8 => decide (x.val < 5)) 5 2 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:139-153
theorem cex_classify_valid_iff_and_decodeIdx_hdisj :
    (⟨0, 2, 5⟩ : AffineNiche 8).span < 8 ∧ ¬ TagsDisjoint (fun _ : Fin 8 => true) 5 2 ∧
      ¬ ((classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .valid ↔
        (fun _ : Fin 8 => true) 5 = true) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .valid →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = E1.u) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .unusedNiche →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = E1.u) ∧
      (∀ r, r ≤ 2 → (5 : Fin 8) = (⟨0, 2, 5⟩ : AffineNiche 8).tagOf r →
        decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = 0 + r ∧
          (⟨0, 2, 5⟩ : AffineNiche 8).tagInterval.Mem 5) ∧
      (classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .liveTag ∨
          classify E1 ⟨0, 2, 5⟩ (fun _ : Fin 8 => true) 5 = .deadTag →
        ∃ r, r ≤ 2 ∧ (5 : Fin 8) = (⟨0, 2, 5⟩ : AffineNiche 8).tagOf r ∧
          decodeIdx E1.u ⟨0, 2, 5⟩ (5 : Fin 8) = 0 + r)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:157-171
theorem cex_classify_valid_iff_and_decodeIdx_hspan :
    ¬ (⟨0, 2, 0⟩ : AffineNiche 2).span < 2 ∧ TagsDisjoint (fun _ : Fin 2 => false) 0 2 ∧
      ¬ ((classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .valid ↔
        (fun _ : Fin 2 => false) 0 = true) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .valid →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = E1.u) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .unusedNiche →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = E1.u) ∧
      (∀ r, r ≤ 2 → (0 : Fin 2) = (⟨0, 2, 0⟩ : AffineNiche 2).tagOf r →
        decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = 0 + r ∧
          (⟨0, 2, 0⟩ : AffineNiche 2).tagInterval.Mem 0) ∧
      (classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .liveTag ∨
          classify E1 ⟨0, 2, 0⟩ (fun _ : Fin 2 => false) 0 = .deadTag →
        ∃ r, r ≤ 2 ∧ (0 : Fin 2) = (⟨0, 2, 0⟩ : AffineNiche 2).tagOf r ∧
          decodeIdx E1.u ⟨0, 2, 0⟩ (0 : Fin 2) = 0 + r)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:173
theorem nv_genLayout_dec_isSome_iff_classify_of_span_lt : Ag.span < 256 ^ 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:177-183
theorem cex_genLayout_dec_isSome_iff_classify_hspan :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      ¬ (((genLayout ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)).dec 1).isSome
          = true ↔
        (classify ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false) 1 = .valid ∨
          classify ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false) 1 = .liveTag)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:185-186
theorem nv_genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange :
    Ag.span < 256 ^ 1 ∧ TagsDisjoint Vlow Ag.nicheStart Ag.span ∧ LiveInRange E1 Ag := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:190-194
theorem cex_genLayout_lawful_hspan :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      TagsDisjoint (fun _ : Pat 1 => false) 0 256 ∧
      LiveInRange ⟨258, 257, fun _ => true⟩ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)) ∧
      ¬ Lawful (genLayout ⟨258, 257, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:203-205
theorem cex_genLayout_lawful_hdisj :
    Ag.span < 256 ^ 1 ∧ ¬ TagsDisjoint (allV 1) Ag.nicheStart Ag.span ∧ LiveInRange E1 Ag ∧
      ¬ Lawful (genLayout E1 Ag (allV 1)) := …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:211-217
theorem cex_genLayout_lawful_hdisj_deadSlot :
    Ag.span < 256 ^ 1 ∧
      ¬ TagsDisjoint (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254)) Ag.nicheStart Ag.span ∧
      LiveInRange E1 Ag ∧
      classify E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254)) 254 = .deadTag ∧
      (genLayout E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254))).dec 254 = none ∧
      ¬ Lawful (genLayout E1 Ag (fun x : Pat 1 => decide (x.val < 253 ∨ x.val = 254))) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:227-230
theorem cex_genLayout_lawful_hlive :
    (⟨1, 1, 253⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧ TagsDisjoint Vlow 253 1 ∧
      ¬ LiveInRange E1 (⟨1, 1, 253⟩ : AffineNiche (256 ^ 1)) ∧
      ¬ Lawful (genLayout E1 ⟨1, 1, 253⟩ Vlow) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:239-241
theorem ex_genLayout_lawful_span_eq_card :
    ¬ (⟨0, 256, 0⟩ : AffineNiche (256 ^ 1)).span < 256 ^ 1 ∧
      Lawful (genLayout ⟨257, 256, fun _ => true⟩ ⟨0, 256, 0⟩ (fun _ : Pat 1 => false)) := …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:247-249
theorem cex_folklore_dead_slot :
    Ag.tagInterval.Mem 254 ∧ classify E1 Ag Vlow 254 = .deadTag ∧
      decodeIdx E1.u Ag 254 = E1.u ∧ (genLayout E1 Ag Vlow).dec 254 = none := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:253-254
theorem nv_exists_tagsDisjoint_iff_span_succ_le_sub_size_of_isHull :
    (∃ x, V01 x = true) ∧ IsHull V01 ⟨0, 1⟩ := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:258-261
theorem cex_exists_tagsDisjoint_iff_span_succ_le_hne :
    ¬ (∃ x, (fun _ : Fin 4 => false) x = true) ∧ IsHull (fun _ : Fin 4 => false) ⟨0, 0⟩ ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint (fun _ => false) ns 3) ↔
        3 + 1 ≤ 4 - (⟨0, 0⟩ : WrapInterval 4).size) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:264-266
theorem cex_exists_tagsDisjoint_iff_span_succ_le_hH :
    (∃ x, V0 x = true) ∧ ¬ IsHull V0 ⟨0, 1⟩ ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns 2) ↔ 2 + 1 ≤ 4 - (⟨0, 1⟩ : WrapInterval 4).size) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:271-273
theorem cex_folklore_fragmented_capacity_lt_nichesCount :
    IsHull V02 ⟨0, 2⟩ ∧ 4 - (⟨0, 2⟩ : WrapInterval 4).size < nichesCount V02 ∧
      ¬ (∃ ns : Fin 4, TagsDisjoint V02 ns 1) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:276-277
theorem nv_sub_size_le_nichesCount_and_eq_iff_of_covers :
    Covers (⟨0, 2⟩ : WrapInterval 4) V02 ∧ Covers (⟨0, 3⟩ : WrapInterval 4) V02 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:280-284
theorem cex_sub_size_le_nichesCount_and_eq_iff_of_covers_hcov :
    ¬ Covers (⟨0, 0⟩ : WrapInterval 4) V01 ∧
      ¬ (4 - (⟨0, 0⟩ : WrapInterval 4).size ≤ nichesCount V01 ∧
        (4 - (⟨0, 0⟩ : WrapInterval 4).size = nichesCount V01 ↔
          ∀ x, (⟨0, 0⟩ : WrapInterval 4).Mem x → V01 x = true)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:289-291
theorem cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH :
    Covers (⟨0, 2⟩ : WrapInterval 4) V01 ∧ ¬ IsHull V01 ⟨0, 2⟩ ∧
      ¬ (4 - (⟨0, 2⟩ : WrapInterval 4).size = nichesCount V01 ↔ IsWrapIntervalSet V01) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:295-296
theorem nv_nichesCount_intervalV :
    nichesCount (intervalV (⟨3, 1⟩ : WrapInterval 4)) = 4 - (⟨3, 1⟩ : WrapInterval 4).size := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:301-302
theorem nv_exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last :
    (∃ x, V01 x = true) ∧ IsHull V01 ⟨0, 1⟩ ∧ 2 ≤ 3 ∧ 4 - (⟨0, 1⟩ : WrapInterval 4).size = 3 - 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:307-311
theorem cex_naturalSpan_hne :
    ¬ (∃ x, (fun _ : Fin 3 => false) x = true) ∧ IsHull (fun _ : Fin 3 => false) ⟨0, 0⟩ ∧
      2 ≤ 3 ∧ 3 - (⟨0, 0⟩ : WrapInterval 3).size = 3 - 1 ∧
      ¬ ((∃ ns : Fin 3, TagsDisjoint (fun _ => false) ns (naturalSpan 3 1)) ↔
        (1 = 0 ∨ 1 = 3 - 1)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:315-318
theorem cex_naturalSpan_hH :
    (∃ x, V0 x = true) ∧ ¬ IsHull V0 ⟨0, 1⟩ ∧ 2 ≤ 3 ∧
      4 - (⟨0, 1⟩ : WrapInterval 4).size = 3 - 1 ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns (naturalSpan 3 1)) ↔ (1 = 0 ∨ 1 = 3 - 1)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:322-326
theorem cex_naturalSpan_hk :
    (∃ x, (fun _ : Fin 2 => true) x = true) ∧ IsHull (fun _ : Fin 2 => true) ⟨0, 1⟩ ∧
      ¬ 2 ≤ 1 ∧ 2 - (⟨0, 1⟩ : WrapInterval 2).size = 1 - 1 ∧
      ¬ ((∃ ns : Fin 2, TagsDisjoint (fun _ => true) ns (naturalSpan 1 0)) ↔
        (0 = 0 ∨ 0 = 1 - 1)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:330-333
theorem cex_naturalSpan_hcap :
    (∃ x, V0 x = true) ∧ IsHull V0 ⟨0, 0⟩ ∧ 2 ≤ 3 ∧
      4 - (⟨0, 0⟩ : WrapInterval 4).size ≠ 3 - 1 ∧
      ¬ ((∃ ns : Fin 4, TagsDisjoint V0 ns (naturalSpan 3 1)) ↔ (1 = 0 ∨ 1 = 3 - 1)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:339-343
theorem cex_folklore_fit_depends_on_untagged_position :
    (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 0)) ∧
      (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 2)) ∧
      ¬ (∃ ns : Fin 256, TagsDisjoint Vlt254 ns (naturalSpan 3 1)) ∧
      (∃ L : Layout (ExtEnum 2 Vlt254) 1, Lawful L) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:351-353
theorem nv_rotDecodeIdx_exact :
    (1 < 3 ∧ 3 ≤ 256 + 1 ∧ RotTagsInvalid Vlt254 3 254) ∧
      (0 < 1 ∧ 1 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => true) 1 0) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:357-360
theorem cex_rotDecodeIdx_hu :
    ¬ 2 < 2 ∧ 2 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => false) 2 0 ∧
      ¬ ((∀ i, i < 2 → i ≠ 2 → rotDecodeIdx 2 2 (0 : Fin 2) (rotTag 2 2 (0 : Fin 2) i) = i) ∧
        (∀ x, (fun _ : Fin 2 => false) x = true → rotDecodeIdx 2 2 (0 : Fin 2) x = 2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:365-368
theorem cex_rotDecodeIdx_hkM :
    3 < 4 ∧ ¬ 4 ≤ 2 + 1 ∧ RotTagsInvalid (fun _ : Fin 2 => false) 4 0 ∧
      ¬ ((∀ i, i < 4 → i ≠ 3 → rotDecodeIdx 4 3 (0 : Fin 2) (rotTag 4 3 (0 : Fin 2) i) = i) ∧
        (∀ x, (fun _ : Fin 2 => false) x = true → rotDecodeIdx 4 3 (0 : Fin 2) x = 3)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:373-376
theorem cex_rotDecodeIdx_hdisj :
    0 < 2 ∧ 2 ≤ 4 + 1 ∧ ¬ RotTagsInvalid (fun _ : Fin 4 => true) 2 0 ∧
      ¬ ((∀ i, i < 2 → i ≠ 0 → rotDecodeIdx 2 0 (0 : Fin 4) (rotTag 2 0 (0 : Fin 4) i) = i) ∧
        (∀ x, (fun _ : Fin 4 => true) x = true → rotDecodeIdx 2 0 (0 : Fin 4) x = 0)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:381
theorem nv_extend_spec_of_size_lt : (⟨1, 1⟩ : WrapInterval 4).size < 4 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:385-390
theorem cex_extend_spec_hI :
    ¬ (⟨0, 3⟩ : WrapInterval 4).size < 4 ∧
      ¬ (¬ (⟨0, 3⟩ : WrapInterval 4).Mem (adjNiche ⟨0, 3⟩ .high) ∧
        (∀ x, (extend (⟨0, 3⟩ : WrapInterval 4) .high).Mem x ↔
          ((⟨0, 3⟩ : WrapInterval 4).Mem x ∨ x = adjNiche ⟨0, 3⟩ .high)) ∧
        (extend (⟨0, 3⟩ : WrapInterval 4) .high).size = (⟨0, 3⟩ : WrapInterval 4).size + 1) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:394
theorem nv_nicheLayout_adjNiche_lawful : (⟨1, 255⟩ : WrapInterval (256 ^ 1)).size < 256 ^ 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:399-405
theorem cex_nicheLayout_adjNiche_lawful_hI :
    ¬ (⟨0, 255⟩ : WrapInterval (256 ^ 1)).size < 256 ^ 1 ∧
      ¬ (Lawful (nicheLayout (intervalV (⟨0, 255⟩ : WrapInterval (256 ^ 1)))
          (adjNiche ⟨0, 255⟩ .high)) ∧
        ∀ p, ((nicheLayout (intervalV (⟨0, 255⟩ : WrapInterval (256 ^ 1)))
          (adjNiche ⟨0, 255⟩ .high)).dec p).isSome =
            intervalV (extend (⟨0, 255⟩ : WrapInterval (256 ^ 1)) .high) p) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:416-417
theorem ex_intervalV_nonZero :
    ∀ p : Pat 1, intervalV (⟨1, 255⟩ : WrapInterval (256 ^ 1)) p = nonZeroV 1 p := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:421-425
theorem nv_levelsReserveNiches_iff_length_le_and_nest_size :
    (LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.low, .low, .low] ↔ 3 ≤ 4 - 1) ∧
      (LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high] ↔ 3 ≤ 4 - 1) ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.low, .low, .low]).size = 4 ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high]).size = 4 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:429-430
theorem nv_exists_lawful_extEnum_intervalV :
    ∃ L : Layout (ExtEnum 1 (intervalV (⟨1, 255⟩ : WrapInterval (256 ^ 1)))) 1, Lawful L := …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:437-441
theorem ex_nest_past_capacity :
    ¬ LevelsReserveNiches (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high] ∧
      nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high] = ⟨1, 0⟩ ∧
      nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high] = ⟨1, 1⟩ ∧
      (nest (⟨1, 1⟩ : WrapInterval 4) [.high, .high, .high, .high]).size = 1 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:447-454
theorem cex_folklore_nonadjacent_reservation_fragments :
    intervalV (⟨0, 1⟩ : WrapInterval 8) 4 = false ∧
      ¬ IsWrapIntervalSet (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) ∧
      IsHull (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) ⟨0, 4⟩ ∧
      ¬ (∃ ns : Fin 8, TagsDisjoint (fun x => intervalV ⟨0, 1⟩ x || x == 4) ns 3) ∧
      (∃ ns : Fin 8, TagsDisjoint (intervalV (extend (⟨0, 1⟩ : WrapInterval 8) .high)) ns 4) ∧
      nichesCount (fun x : Fin 8 => intervalV ⟨0, 1⟩ x || x == 4) = 5 ∧
      nichesCount (intervalV (extend (⟨0, 1⟩ : WrapInterval 8) .high)) = 5 := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:459
def LopAll : OpLayout := { Lop with V := allV 1 }
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:461-462
theorem nv_setDisc_operational_untagged_isSome_iff :
    TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:467-475
theorem cex_setDisc_operational_untagged_isSome_iff_hdisj :
    ¬ TagsDisjoint LopAll.V LopAll.A.nicheStart LopAll.A.span ∧
      LopAll.no + LopAll.nw ≤ uninit3.length ∧ LopAll.V 253 = true ∧
      (setDisc .operational LopAll LopAll.E.u (LopAll.writeNiche uninit3 253)).isSome = false ∧
      ¬ ((∀ p, (setDisc .operational LopAll LopAll.E.u p).isSome = true ↔
            ∃ x, LopAll.readNiche p = some x ∧ LopAll.V x = true) ∧
         (∀ p (x : Pat LopAll.nw), LopAll.no + LopAll.nw ≤ p.length →
            ((setDisc .operational LopAll LopAll.E.u (LopAll.writeNiche p x)).isSome = true ↔
              LopAll.V x = true))) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:484-490
theorem cex_folklore_payload_write_setDisc_noncommuting :
    run .operational Lop [.write 1 [5], .setDisc 1] (uninit3, []) =
        some ([none, some 5, none], []) ∧
      run .operational Lop [.setDisc 1, .write 1 [5]] (uninit3, []) = none ∧
      run .operational Lop [.write 1 [5], .setDisc 1] ([none, some 253, none], []) =
        some ([none, some 5, none], []) ∧
      run .operational Lop [.setDisc 1, .write 1 [5]] ([none, some 253, none], []) = none := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:495-499
theorem nv_run_erased_eq_some_of_run_operational_eq_some :
    run .operational Lop [.write 1 [5], .setDisc 1, .readDisc] (uninit3, []) =
        some ([none, some 5, none], [1]) ∧
      run .erased Lop [.write 1 [5], .setDisc 1, .readDisc] (uninit3, []) =
        some ([none, some 5, none], [1]) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:503-505
theorem cex_folklore_erasure_not_equivalent :
    run .operational Lop [.setDisc 1] (uninit3, []) = none ∧
      run .erased Lop [.setDisc 1] (uninit3, []) = some (uninit3, []) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:509-514
theorem nv_run_write_setDisc_comm_of_disjointFromNiche :
    Lop.DisjointFromNiche 0 ([9] : List (Fin 256)).length ∧
      run .operational Lop [.write 0 [9], .setDisc 0] (uninit3, []) =
        some ([some 9, some 253, none], []) ∧
      run .operational Lop [.setDisc 0, .write 0 [9]] (uninit3, []) =
        some ([some 9, some 253, none], []) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:519-526
theorem cex_run_write_setDisc_comm_hdis :
    ¬ Lop.DisjointFromNiche 1 ([255] : List (Fin 256)).length ∧
      ¬ (run .operational Lop [.write 1 [255], .setDisc 0] (uninit3, []) =
          run .operational Lop [.setDisc 0, .write 1 [255]] (uninit3, [])) ∧
      run .operational Lop [.write 1 [255], .setDisc 0] (uninit3, []) =
        some ([none, some 253, none], []) ∧
      run .operational Lop [.setDisc 0, .write 1 [255], .readDisc] (uninit3, []) =
        some ([none, some 255, none], [2]) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:529
def LopNone : OpLayout := { Lop with V := fun _ => false }
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:534-538
theorem ex_setDisc_untagged_uninhabited :
    setDisc .operational LopNone LopNone.E.u [none, some 5, none] = none ∧
      setDisc .erased LopNone LopNone.E.u [none, some 5, none] = some [none, some 5, none] ∧
      (∀ p, (setDisc .operational LopNone LopNone.E.u p).isSome = true ↔
        ∃ x, LopNone.readNiche p = some x ∧ LopNone.V x = true) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:544-551
theorem nv_run_fields_then_setDisc_readDisc_of_disjoint :
    Lop.no + Lop.nw ≤ uninit3.length ∧ Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (2, [7])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((0 : Nat), [(9 : Fin 256)]), (2, [7])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (2, [7])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      Lop.Encodable 0 ∧ Lop.V 0 = true := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:555
def LopFar : OpLayout := { Lop with no := 5 }
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:559-580
theorem cex_run_fields_then_setDisc_hfit :
    ¬ (LopFar.no + LopFar.nw ≤ uninit3.length) ∧
      LopFar.A.span < 256 ^ LopFar.nw ∧
      TagsDisjoint LopFar.V LopFar.A.nicheStart LopFar.A.span ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopFar.DisjointFromNiche w.1 w.2.length) ∧
      LopFar.Encodable 0 ∧
      run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 0, .readDisc]) (uninit3, []) =
        none ∧
      ¬ ((∀ v, LopFar.Encodable v → ∃ q,
          run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopFar.readNiche q = some (LopFar.A.tagOf (v - LopFar.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopFar.nw, LopFar.V x = true → ∃ q,
          run .operational LopFar (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopFar.no (leBytes LopFar.nw x.val), .setDisc LopFar.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopFar.E.u]) ∧
          LopFar.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:590
def LopWide : OpLayout := ⟨1, 1, ⟨258, 257, fun _ => true⟩, ⟨0, 256, 0⟩, fun _ => false⟩
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:593-614
theorem cex_run_fields_then_setDisc_hspan :
    LopWide.no + LopWide.nw ≤ uninit3.length ∧
      ¬ (LopWide.A.span < 256 ^ LopWide.nw) ∧
      TagsDisjoint LopWide.V LopWide.A.nicheStart LopWide.A.span ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopWide.DisjointFromNiche w.1 w.2.length) ∧
      LopWide.Encodable 256 ∧
      run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc 256, .readDisc]) (uninit3, []) =
        some ([none, some 0, none], [0]) ∧
      ¬ ((∀ v, LopWide.Encodable v → ∃ q,
          run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopWide.readNiche q = some (LopWide.A.tagOf (v - LopWide.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopWide.nw, LopWide.V x = true → ∃ q,
          run .operational LopWide (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopWide.no (leBytes LopWide.nw x.val), .setDisc LopWide.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopWide.E.u]) ∧
          LopWide.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:625-647
theorem cex_run_fields_then_setDisc_hdisj :
    LopAll.no + LopAll.nw ≤ uninit3.length ∧
      LopAll.A.span < 256 ^ LopAll.nw ∧
      ¬ (TagsDisjoint LopAll.V LopAll.A.nicheStart LopAll.A.span) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), w.1 + w.2.length ≤ uninit3.length) ∧
      ([] : List (Nat × List (Fin 256))).Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ ([] : List (Nat × List (Fin 256))), LopAll.DisjointFromNiche w.1 w.2.length) ∧
      LopAll.V 253 = true ∧
      run .operational LopAll
        (writesOf ([] : List (Nat × List (Fin 256))) ++ [.write LopAll.no (leBytes LopAll.nw 253), .setDisc LopAll.E.u, .readDisc])
        (uninit3, []) = none ∧
      ¬ ((∀ v, LopAll.Encodable v → ∃ q,
          run .operational LopAll (writesOf ([] : List (Nat × List (Fin 256))) ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          LopAll.readNiche q = some (LopAll.A.tagOf (v - LopAll.A.first)) ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat LopAll.nw, LopAll.V x = true → ∃ q,
          run .operational LopAll (writesOf ([] : List (Nat × List (Fin 256))) ++
            [.write LopAll.no (leBytes LopAll.nw x.val), .setDisc LopAll.E.u, .readDisc]) (uninit3, []) =
            some (q, [LopAll.E.u]) ∧
          LopAll.readNiche q = some x ∧
          ∀ w ∈ ([] : List (Nat × List (Fin 256))), readBytes q w.1 w.2.length = some w.2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:660-680
theorem cex_run_fields_then_setDisc_hin :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      ¬ (∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((2 : Nat), [(7 : Fin 256), 8])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++ [.setDisc 0, .readDisc])
        (uninit3, []) = none ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((2 : Nat), [(7 : Fin 256), 8])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((2 : Nat), [(7 : Fin 256), 8])], readBytes q w.1 w.2.length = some w.2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:689-710
theorem cex_run_fields_then_setDisc_hpw :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], w.1 + w.2.length ≤ uninit3.length) ∧
      ¬ [((0 : Nat), [(9 : Fin 256)]), (0, [8])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      (∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++
        [.setDisc 0, .readDisc]) (uninit3, []) = some ([some 8, some 253, none], [0]) ∧
      readBytes [some 8, some 253, none] 0 1 ≠ some [9] ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((0 : Nat), [(9 : Fin 256)]), (0, [8])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((0 : Nat), [(9 : Fin 256)]), (0, [8])], readBytes q w.1 w.2.length = some w.2)) := by …
```

```lean
-- lean/Toy/WrapNiche/Witnesses.lean:724-745
theorem cex_run_fields_then_setDisc_hws :
    Lop.no + Lop.nw ≤ uninit3.length ∧
      Lop.A.span < 256 ^ Lop.nw ∧
      TagsDisjoint Lop.V Lop.A.nicheStart Lop.A.span ∧
      (∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], w.1 + w.2.length ≤ uninit3.length) ∧
      [((1 : Nat), [(9 : Fin 256)])].Pairwise
        (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1) ∧
      ¬ (∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], Lop.DisjointFromNiche w.1 w.2.length) ∧
      run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++ [.setDisc 0, .readDisc])
        (uninit3, []) = some ([none, some 253, none], [0]) ∧
      readBytes [none, some 253, none] 1 1 ≠ some [9] ∧
      ¬ ((∀ v, Lop.Encodable v → ∃ q,
          run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++ [.setDisc v, .readDisc]) (uninit3, []) =
            some (q, [v]) ∧
          Lop.readNiche q = some (Lop.A.tagOf (v - Lop.A.first)) ∧
          ∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], readBytes q w.1 w.2.length = some w.2) ∧
        (∀ x : Pat Lop.nw, Lop.V x = true → ∃ q,
          run .operational Lop (writesOf [((1 : Nat), [(9 : Fin 256)])] ++
            [.write Lop.no (leBytes Lop.nw x.val), .setDisc Lop.E.u, .readDisc]) (uninit3, []) =
            some (q, [Lop.E.u]) ∧
          Lop.readNiche q = some x ∧
          ∀ w ∈ [((1 : Nat), [(9 : Fin 256)])], readBytes q w.1 w.2.length = some w.2)) := by …
```

## Boundaries

### Non-claims

These are statements about the toy model `Toy.WrapNiche`; they neither establish nor refute the corresponding claims about rustc's enum layout computation, its generated code, its interpreter, MiniRust or LLVM. Model–system relation: none proved.

**Attractive stronger conclusions that are not established** (each is a non-claim of the result named):

- That rustc, its interpreter, its code generator, MiniRust or LLVM implement the toy's definitions or satisfy its theorems (every result);
- That every tag in the niche interval encodes a variant (refuted in the toy by `cex_folklore_dead_slot`, R2.3);
- That the contiguous capacity M - H.size of R3.1 equals the niche count for every validity set (strictly smaller for fragmented validity, `cex_folklore_fragmented_capacity_lt_nichesCount`, R3.2);
- That, for a validity set with a valid value, an interval hull H, k >= 3 and M - H.size = k - 1, the natural niche range fits for every position u < k of the untagged variant (R4.1: it fits iff u = 0 or u = k - 1); and that the end positions are singled out at every capacity (for k >= 2, off the boundary every u fits or none does, `exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull`);
- That a hypothesis marked tight is necessary in general (tightness is a counterexample in the witness class recorded in the ledger; for example the minimality half of `IsHull` in R3.2's corollary, and the sufficient conditions of R2.5 and R6.4);
- That operational and erased `SetDiscriminant u` are equivalent (`cex_folklore_erasure_not_equivalent`, R6.2);
- That writes overlapping the niche field commute with `SetDiscriminant` (`cex_run_write_setDisc_comm_hdis`, `cex_folklore_payload_write_setDisc_noncommuting`, R6.3);
- That the toy's out-of-bounds undefined behaviour describes how Rust, Miri or MiniRust treat out-of-bounds accesses (R6.1-R6.4).

**Non-claims of each result** (the same text is listed with each result under Findings):

**R1.1 `mem_iff_offset_le_offset`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Membership is the model's case-split definition (`WrapInterval.Mem`); the result does not show that any compiler implements its range checks with this subtraction.
- Every `WrapInterval` is non-empty (it contains s); the empty set is not representable, so nothing is claimed about empty validity ranges.
- `offset` is computed in Nat as (x + (M - s)) % M; nothing is claimed about fixed-width machine subtraction beyond this arithmetic.

**R1.2 `compl_mem_iff_not_mem_of_size_lt`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For M = 1 every interval is full, so the hypothesis excludes M = 1 entirely.
- Nothing is claimed about how a real layout engine represents a full range.

**R1.3 `originTest_exactFor_iff_offset_le`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The folklore refutations are concrete: the unsigned test fails on [255, 0] mod 256 (`cex_folklore_unsignedTest_255_0`) and the i8 signed test fails on [127, 128] mod 256 (`cex_folklore_signedTestI8_127_128`). Each fixed test is exact on other wrapping intervals (`pc_signed_and_unsigned_exact_elsewhere`).
- The classification is for the conjunctive test `originTest o`. A two-branch test at a fixed origin (`twoBranchTest`) is exact for every interval (`pc_twoBranchTest_exactFor`); table lookups are not examined.
- The signed reading is stated for 8-bit fields (`toI8`, `signedTestI8`); the corresponding equivalence for other widths 2^w with origin 2^(w-1) is not stated (not proved here).

**R1.4 `not_exactFor_originTest_wrapSub_one_of_two_le`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The witness interval is exposed: [o - 1, o]. The result says nothing about intervals that do not wrap past o, for which the fixed test is exact (`originTest_exactFor_iff_offset_le`).
- Escape hatch (a second branch): the test at the same fixed origin that uses `originTest o` when the interval does not wrap past o and the disjunction offset(o, s) <= offset(o, x) or offset(o, x) <= offset(o, e) otherwise (`twoBranchTest`) is exact for every interval, every M and every origin (`pc_twoBranchTest_exactFor`). At origin 0 its branches are the two cases of `WrapInterval.Mem`, the shape of rustc's `WrappingRange::contains` (prior art).
- Escape hatch (a negated complement): the fixed-origin test applied to the interval when it does not wrap past o, and the negated fixed-origin test applied to [e + 1, s - 1] otherwise, is exact for every origin and every interval of Fin 8 (`pc_complTest_exactFor_fin8`, a bounded check); the statement for general M is not proved here.
- Escape hatch (an origin that depends on the interval): with the interval's own start as origin the test is the single-subtraction test (`subTest_iff_originTest_start`), exact for every interval (`mem_iff_offset_le_offset`; `pc_subTest_exactFor_all_fin8` checks M = 8).
- Escape hatch (dropping hM): for M = 1 the only interval [0, 0] is tested exactly (`cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM`).

**R2.1 `affineLayout_eq_nicheLayoutK_affineTags`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Equality of decoders is not lawfulness: lawfulness needs span < 256^n and invalid tags (`affineLayout_lawful_iff_span_lt_and_tagsDisjoint`).
- The value type is the imported `ExtEnum (span + 1) V`: every slot of the niche range is a live dataless variant; dead slots are covered by the `genLayout` results instead.
- Variants of `affineLayout` are named by their relative index r, so `A.first` is not used by this layout and variant-index offsetting is not exercised here; it is exercised by `decodeIdx` and `genLayout` (R2.3-R2.5).

**R2.2 `affineLayout_lawful_iff_span_lt_and_tagsDisjoint`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Each conjunct of the right side is needed for this shape: an overlap with the valid set makes a valid payload decode as a niche variant (`cex_affineLayout_lawful_overlap`), and span = 256 with no valid value makes two tags coincide (`cex_affineLayout_lawful_span`).
- The equivalence is for the dead-slot-free shape. With dead slots (`genLayout`), span < 256^n is no longer necessary for lawfulness (`ex_genLayout_lawful_span_eq_card`: span 256, n = 1).
- `A.first` is not used by `affineLayout` (see R2.1).
- Whether a disjoint placement exists for a given V and span is a separate question (`exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull`).

**R2.3 `classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- All four classes occur in one instance (`ex_classify`: valid 0..=249, tags 253, 254, 255 with 254 a dead slot, 251 an unused niche). A three-way partition (valid, live tag, dead slot) therefore misses the unused niches; the three classes cover the field when the tag interval and the valid set together cover it (not stated as a theorem here).
- `decodeIdx` is the index-only decoder; it never rejects. On a dead slot it returns first + r, which is u or an index that is uninhabited or >= k; whether that is undefined behaviour is a property of the checked decoder (`genLayout_dec_isSome_iff_classify_of_span_lt`), not of `decodeIdx`.
- The folklore 'every tag in the niche interval encodes a variant' is refuted by `cex_folklore_dead_slot`.
- The proof of the second to fifth conjuncts does not use hdisj (they hold without it; not stated as a separate theorem); the first conjunct uses it.

**R2.4 `genLayout_dec_isSome_iff_classify_of_span_lt`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Acceptance is not lawfulness. A sufficient condition for lawfulness is `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange`, which adds hdisj and hlive to hspan; each of its hypotheses is tight in the witness class recorded in its ledger, but necessity for lawfulness in general is not proved here, and span < 256^n is not necessary for lawfulness (`ex_genLayout_lawful_span_eq_card`).
- There is no tag condition here. Without one, a valid payload value inside the tag interval is classified `liveTag` or `deadTag`, not `valid`: the checked decoder then decodes it as a dataless variant or rejects it (`cex_genLayout_lawful_hdisj`, `cex_genLayout_lawful_hdisj_deadSlot`).
- The correspondence between the checked decoder and the interpreter behaviour described in the source comments cited below is a derived (modeling bridge) claim, not a proved relation; the toy's validity set V plays the role of the niche scalar's valid range, which in rustc is a single wrapping range.

**R2.5 `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A sufficient condition. Each hypothesis is tight (it has a counterexample in which the others hold), but span < 256^n is not necessary for lawfulness: with no valid value and the slot at relative index 256 dead, span 256 is lawful for n = 1 (`ex_genLayout_lawful_span_eq_card`).
- Valid payload values may not occupy dead slots either: a valid value at the dead slot of u is rejected by the checked decoder and the layout is not lawful (`cex_genLayout_lawful_hdisj_deadSlot`).
- The dead slot wastes a tag value; the capacity consequences are stated in group 3 and group 4.
- Every variant other than u is dataless in `genLayout`; rustc's niche-filling layout also admits such variants with fields placed before or after the niche field (prior art, derived (modeling bridge)), which are not modelled here.
- Discriminants are the variant indices, as rustc's layout sanity check requires for niche-encoded enums (prior art, derived (modeling bridge)); explicit discriminants are not modelled.
- `EnumSpec` does not require u < k: for u >= k every index below k is a candidate dataless variant (`ex_live_u_ge_k`); the theorem holds for such shapes too.

**R3.1 `exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Contiguity is a modeling choice that mirrors the affine encoding; layouts with non-contiguous tags (the imported lookup layout) can exceed this capacity (`cex_folklore_fragmented_capacity_lt_nichesCount`).
- `TagsDisjoint` does not require the tags to be distinct. Under hne the theorem itself forces span + 1 <= M - H.size <= M - 1, so the tags are distinct; for the empty validity set `TagsDisjoint` holds for every span, including span >= M where tags repeat (`cex_genLayout_lawful_hspan` contains `TagsDisjoint (fun _ => false) 0 256` for M = 256), so dropping hne does not give an unbounded lawful capacity (lawfulness is R2.2).
- The existence of an interval hull for every V on Fin M with M > 0 is not proved here; rustc computes one (`smallest_range_containing`, prior art).
- A single niche field is modelled: payloads with several fields (where another field's niches could be used), and wrappers that hide niches, are not modelled.
- Nothing is claimed about which placement a layout engine chooses; rustc reserves values adjacent to the valid range (source comment cited), which is one of the disjoint placements when V is an interval.

**R3.2 `sub_size_le_nichesCount_and_eq_iff_of_covers`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For an interval hull H of a V with at least one valid value, M - H.size is the contiguous capacity of R3.1 (span + 1 <= M - H.size); for the empty validity set it is not (`cex_exists_tagsDisjoint_iff_span_succ_le_hne`: M = 4, M - H.size = 3, yet four contiguous tags fit).
- For an interval hull H, equality holds iff V is itself the member set of a wrapping interval (`sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull`); there the minimality half of `IsHull` is tight, witnessed on M = 4, V = {0, 1}, H = [0, 2] by `cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH`; whether it is needed for other instances is not claimed (not proved here).
- Strictness for fragmented validity is `cex_folklore_fragmented_capacity_lt_nichesCount` (M = 4, V = {0, 2}); the cost of u's slot inside the range is `cex_folklore_fit_depends_on_untagged_position`.
- For the empty validity set both sides of the equivalence are false (H is non-empty).

**R3.3 `nichesCount_intervalV`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A counting lemma; it says nothing about layouts by itself.

**R4.1 `exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Off the boundary hcap the answer is different and does not single out the ends: for every capacity, the natural range fits iff M - H.size >= k - 1 when u = 0 or u = k - 1 and M - H.size >= k otherwise (`exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull`, k >= 2). So with M - H.size >= k every u fits, including middle positions (`cex_naturalSpan_hcap` is an instance), and with M - H.size < k - 1 no u fits, not even u = 0 or u = k - 1.
- u is unconstrained: for u >= k the right side is false (u = 0 and u = k - 1 both fail since k >= 2), so by this theorem the left side is false too. For k = 2 there is no middle index (0 < u < 1 is empty) and the theorem says that both u = 0 and u = 1 fit.
- The theorem is about contiguous tag placements (`TagsDisjoint`) of span `naturalSpan k u`; deriving from it that no affine encoding satisfying `LiveInRange` fits needs `naturalFirst_naturalLast_spec` and monotonicity of `TagsDisjoint` in the span, and is not stated as a theorem here (not proved here).
- Other encodings behave differently: the rotated encoding fits for every u under the same capacity condition k - 1 <= M - H.size (R4.2 and `exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull`), and an unconstrained lookup layout can fit where the natural range does not (`cex_folklore_fit_depends_on_untagged_position`, n = 1, valid 0..=253, k = 3; it also refutes 'niche fit depends only on the multiset of variant layouts' for the natural range).
- `naturalSpan` assumes every dataless variant is inhabited; uninhabited variants at the ends shrink the range and are not covered.
- The public issue cited below reports a size difference for a 255-variant enum; this card does not claim to explain rustc's behaviour on that example (derived (modeling bridge) at most).

**R4.2 `rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For k >= 2, `RotTagsInvalid V k ns` is `TagsDisjoint V ns (k - 2)` (`rotTagsInvalid_iff_tagsDisjoint_sub_two`): the rotated range has span k - 2 for every position of u. For a payload with a valid value and an interval hull H, a start making all rotated tags invalid exists iff k - 1 <= M - H.size, for every k (truncated subtraction k - 1; trivial for k <= 1) and independently of u (`exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull`).
- `rotDecodeIdx` is an unchecked, index-only decoder: no lawful `Layout` is constructed for the rotated encoding (unlike R2.2 and R2.5), unused niches decode to u, and uninhabited variants and dead slots are not modelled.
- The theorem assumes hdisj for both conjuncts. The proof of the first conjunct does not use hdisj (so that conjunct holds without it; it is not stated as a separate theorem); the second conjunct uses it.
- The cited pull request is a closed, unmerged proposal and is not normative; as described there it rotates when u lies inside the range, whereas this model rotates always. No claim is made about its code.
- The cost of the extra modular step in generated code is not examined.

**R5.1 `extend_spec_of_size_lt`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- For a full interval (I.size = M), `extend` wraps past the opposite end and collapses to a singleton (`ex_extend_full`: `extend [0, 3] .high = [0, 0]` in Fin 4, size 1).
- Which side a layout engine picks is not modelled; both sides are covered.

**R5.2 `nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Lawfulness is via the imported `nicheLayout_lawful_iff_isNiche`; this card adds the intervalness of the accepted set.
- A single niche field whose valid set is a wrapping interval is modelled; other payload shapes are not.

**R5.3 `levelsReserveNiches_iff_length_le_and_nest_size`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The levels are modelled at the validity-set level; the per-level layout is the imported niche-filled layout (`nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt`).
- Adjacent reservation is one strategy; the bound for arbitrary layouts of the flattened enum is `exists_lawful_extEnum_intervalV_iff_le_sub_size`. A non-adjacent reservation can be lawful for one level yet fragment the valid set and lose contiguous capacity (`cex_folklore_nonadjacent_reservation_fragments`: over [0, 1] in Fin 8, reserving 4 gives {0, 1, 4}, which is not an interval set (`IsWrapIntervalSet`) and has hull [0, 4]; four contiguous tags then no longer fit, whereas after adjacent reservation five do; both sets have five niches).
- Past capacity the second conjunct says nothing; `nest` then wraps and collapses rather than saturating (`ex_nest_past_capacity`: over [1, 1] in Fin 4, four upward levels end at the singleton [1, 1], size 1, not 5).
- The innermost valid set is a non-empty wrapping interval R0 of a single niche field. Validity sets that are not one wrapping interval (with internal holes), the empty validity set (an uninhabited payload), payloads with several fields (where another field's niches could be used), and wrappers that hide niches are not modelled.

**R5.4 `exists_lawful_extEnum_intervalV_iff_le_sub_size`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- `ExtEnum j V` flattens j levels of Option into j dataless variants; the bijection with nested Option is not stated here (the imported two-level impossibility `opt_opt_nonZero_no_decEnc_layout_in_payload_size` proves its j = 2 instance for NonZero; `ex_intervalV_nonZero` identifies the NonZero validity with `intervalV [1, 255]`).
- The statement is about `Lawful` layouts of exactly the payload size n. Layouts that satisfy `DecEnc` without being required to be `Canonical`, or have a size m <= n, are covered by the imported `le_numInvalid_of_decEnc_of_size_le` (not restated as a theorem of this package).
- A corollary of the imported cardinality theorem and `nichesCount_intervalV`.
- The same payload-shape limits as R5.3 apply (a single niche field whose valid set is a non-empty wrapping interval).

**R6.1 `setDisc_operational_untagged_isSome_iff_of_tagsDisjoint`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Write order under `Sem.operational`: by the first conjunct, SetDiscriminant u is defined exactly when the niche field already holds a valid value; so from uninitialized niche bytes or from a niche tag (invalid under hdisj) 'SetDiscriminant u; write payload' is undefined behaviour while 'write payload; SetDiscriminant u' is defined (instance: `cex_folklore_payload_write_setDisc_noncommuting`), and if the niche field already holds a valid value SetDiscriminant u is defined before any write. Writes disjoint from the niche field commute with SetDiscriminant u (`run_write_setDisc_comm_of_disjointFromNiche`). Under `Sem.erased` SetDiscriminant u performs no check.
- The checked `readDisc` rejects unused niches and dead slots; under a lenient reader that returned u for every value outside the tag interval, the 'iff x is valid' form would fail for unused niches (not proved here).
- `L.V` is the validity of the niche field alone; it stands in for the niche scalar's valid range, which in rustc is a single wrapping range. Operational `SetDiscriminant u` reads the niche field alone, not the validity of other fields of the untagged variant's payload. The niche field is read little-endian from provenance-free bytes; big-endian targets and pointer-valued niches are not modelled.
- If the untagged variant is uninhabited (no niche value is valid), operational SetDiscriminant u is undefined behaviour on every place while erased SetDiscriminant u is a no-op (`ex_setDisc_untagged_uninhabited`); rustc rejects uninhabited variants before it treats the untagged variant (prior art, derived (modeling bridge)).
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**R6.2 `run_erased_eq_some_of_run_operational_eq_some`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- Not an equivalence: operational SetDiscriminant u on uninitialized bytes is undefined behaviour while the erased one is a no-op (`cex_folklore_erasure_not_equivalent`); with an uninhabited untagged variant the two differ on every place (`ex_setDisc_untagged_uninhabited`).
- The refinement is stated for this concrete pair of semantics; no general refinement framework is proved.
- Out-of-bounds writes and tag writes are undefined behaviour in both semantics alike, so they do not separate them. In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**R6.3 `run_write_setDisc_comm_of_disjointFromNiche`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- The statement covers the untagged variant too: no restriction to dataless variants is needed.
- Writes that overlap the niche field do not commute in general: with a tag (`cex_run_write_setDisc_comm_hdis`) and with operational SetDiscriminant u (`cex_folklore_payload_write_setDisc_noncommuting`).
- `DisjointFromNiche` is conservative: an empty write strictly inside the niche field is rejected although it overlaps nothing.
- Aliasing, borrows and concurrency are not modelled; a place is a single byte list.
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

**R6.4 `run_fields_then_setDisc_readDisc_of_disjoint`**

- These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's layout code, its generated code or its interpreter. Model–system relation: none proved.
- A sufficient condition. Each hypothesis is tight in the instance class recorded in its ledger entry; none is claimed necessary in general (for example identical overlapping writes, or empty writes, would not break the conclusion; not proved here).
- Write order: writes disjoint from the niche field commute with SetDiscriminant v for every v, including u (`run_write_setDisc_comm_of_disjointFromNiche`). Under `Sem.operational` and when every tag is invalid, SetDiscriminant u is defined exactly when the niche field already holds a valid value (R6.1, first conjunct): starting from uninitialized niche bytes or from a niche tag the valid value has to be written first (instance: `cex_folklore_payload_write_setDisc_noncommuting`), whereas a niche field that already holds a valid value needs no prior write. Under `Sem.erased` SetDiscriminant u performs no check.
- The operational model does not tie field bytes to variants: the writes ws may stand for fields of v placed outside the niche field (rustc's niche-filling layout admits such fields, prior art, derived (modeling bridge)) or for the payload fields of u; `genLayout` (group 2), by contrast, models the variants other than u as dataless.
- Field contents are bytes; no typed validity of the fields is modelled.
- `L.V` is the validity of the niche field alone; it stands in for the niche scalar's valid range, which in rustc is a single wrapping range. Operational `SetDiscriminant u` reads the niche field alone, not the validity of other fields of the untagged variant's payload. The niche field is read little-endian from provenance-free bytes; big-endian targets and pointer-valued niches are not modelled.
- In this toy model a `write` that does not fit in the place, a tag write into a niche field that does not lie inside the place, and a discriminant read of a niche field that does not lie inside the place (for nw >= 1; for nw = 0 there is no byte to check) are undefined behaviour (`ex_run_write_oob`, `ex_setDisc_oob`); nothing is claimed about how Rust, Miri or MiniRust treat out-of-bounds accesses beyond the in-bounds requirement quoted in the prior art.

### Escape hatches

The package has one impossibility result, R1.4 `not_exactFor_originTest_wrapSub_one_of_two_le` (for M >= 2 no fixed origin makes the conjunctive test `originTest o` exact for every interval). Its escape hatches, from its non-claims:

- Escape hatch (a second branch): the test at the same fixed origin that uses `originTest o` when the interval does not wrap past o and the disjunction offset(o, s) <= offset(o, x) or offset(o, x) <= offset(o, e) otherwise (`twoBranchTest`) is exact for every interval, every M and every origin (`pc_twoBranchTest_exactFor`). At origin 0 its branches are the two cases of `WrapInterval.Mem`, the shape of rustc's `WrappingRange::contains` (prior art).
- Escape hatch (a negated complement): the fixed-origin test applied to the interval when it does not wrap past o, and the negated fixed-origin test applied to [e + 1, s - 1] otherwise, is exact for every origin and every interval of Fin 8 (`pc_complTest_exactFor_fin8`, a bounded check); the statement for general M is not proved here.
- Escape hatch (an origin that depends on the interval): with the interval's own start as origin the test is the single-subtraction test (`subTest_iff_originTest_start`), exact for every interval (`mem_iff_offset_le_offset`; `pc_subTest_exactFor_all_fin8` checks M = 8).
- Escape hatch (dropping hM): for M = 1 the only interval [0, 0] is tested exactly (`cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM`).

### Hypotheses whose tightness is unknown

None. Every hypothesis of every result is marked tight and has a counterexample theorem stating that all other hypotheses hold and the conclusion fails, in the witness class recorded in its ledger entry (quoted under Findings, Witnesses). Tightness is not necessity in general.

### Disproved or dropped statements

None. Every result stated in this report is proved as stated; no statement was found false or left unproved.

### Not examined

- Validity sets that are not one wrapping interval for rustc-style layouts, payloads with several fields (where another field's niches could be used), wrappers that hide niches, and explicit discriminants.
- Hull existence for every validity set (rustc computes a covering range by `smallest_range_containing`; the toy characterizes hulls semantically).
- Big-endian targets, pointer-valued niches, provenance, aliasing, borrows and concurrency.
- The code generator's abort for an uninhabited variant in `SetDiscriminant`, and the cost of any decoder in generated code.
- Layout guarantees that the standard library documents for particular `Option` types.

## Evidence

### Kernel-check record

Observed on 2026-11-21 with `leanprover/lean4:v4.34.1` (GitHub `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, resolved through the GitHub API on that date), core Lean and `Std`, no Mathlib. A fresh copy of `lean/` (without a `.lake` directory) was built with `lake build` with Lake's artifact cache disabled, so every proof was re-elaborated and checked by the kernel; the build reported no errors and no `sorry` warnings. A token scan of every Lean source found no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern`, `unsafe`, `debug.skipKernelTC` or `Lean.ofReduceBool`. Lean's `collectAxioms` was run on every one of the 588 declarations of the library `Toy`: each depends on at most `propext`, `Classical.choice` and `Quot.sound` (recorded per declaration in `audit/axioms.json`).

Statement and closure hashes (recorded in `audit/statements.json`; recomputed by `support/revalidate.py`): the statement hash is the SHA-256 of Lean's `repr` of the declaration's type; the closure hash is the SHA-256 of the newline-joined, sorted lines `name : repr(type)` (followed by ` := repr(value)` for every constant that is not a theorem) of every package-local constant reachable from the statement through types, definition values and inductive constructors (theorem bodies excluded). Every declaration that a card references or this report quotes is hashed (260 declarations). The Role column gives a declaration's role for a result (result, non-vacuity witness, counterexample for the named hypothesis, positive control) or otherwise its kind (definition, imported definition or theorem, auxiliary lemma, corollary, concrete fixture, definition example of the named definitions, folklore refutation, counterexample, positive control, illustrative instance), followed by the other cards whose text names it ("cited by"); for a declaration that no card names, it lists the quoted statements that use it ("used in"). In `results.json`, every hashed declaration is registered in the `lean_names` list of some card so that its hash is recorded; that registration is not a citation, and the Role column is the citation record.

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 | Closure size |
| :--- | :--- | :--- | :--- | :--- | ---: |
| `mem_iff_offset_le_offset` | R1.1 result; cited by R1.4 | `Classical.choice`, `Quot.sound`, `propext` | `d7e879f3eaa580f95d129b31af1e00fe5edfbb71c50cc5d65de7e00f4b0af63c` | `680ffe66833a0664498711c840f879fade004e25df88c985a1c9447b32369263` | 6 |
| `compl_mem_iff_not_mem_of_size_lt` | R1.2 result | `Classical.choice`, `Quot.sound`, `propext` | `171ff0f3c60846204cf4da01b09c34b4c2fdf34371e61705b1e600e17917cbea` | `ab36b9171b1f2cff651feac8734a5ff3030e62c31b05d699d564cee22d7335cf` | 12 |
| `originTest_exactFor_iff_offset_le` | R1.3 result; cited by R1.4 | `Classical.choice`, `Quot.sound`, `propext` | `4b3d821fa38a2eb5b871a220073271b9f636e93279c0e61b2d63c980943e9d28` | `c11702fad047745d462aae6050640f3e5621f46f067d9c921c9c08caa31fcca5` | 8 |
| `not_exactFor_originTest_wrapSub_one_of_two_le` | R1.4 result | `Classical.choice`, `Quot.sound`, `propext` | `d885e82fc9ffbdba2567ad8a632672c7fc92133e6735a15bacb3039784da3c6d` | `94b29893435ede73a56cf73018eb3cd70277459c882080f5aefa7d49559cc707` | 10 |
| `affineLayout_eq_nicheLayoutK_affineTags` | R2.1 result | `Classical.choice`, `Quot.sound`, `propext` | `242dcfbd35741941947e8252148a5a5d2f78f25a5b70bae7756e6abc0ef85feb` | `c6fb220208206a2bdc2e8378ddd6723c16a976bfbe2b956fc2e0de889102a536` | 21 |
| `affineLayout_lawful_iff_span_lt_and_tagsDisjoint` | R2.2 result; cited by R2.1 | `Classical.choice`, `Quot.sound`, `propext` | `3b0eae26ea918331da371a1b07253433114379ab697a50d51f16e2491ce546ee` | `96bd02611722dbef8090c10ee980ca9057a0ad9470f1e4444320e92cb7f7cbad` | 23 |
| `classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint` | R2.3 result | `Classical.choice`, `Quot.sound`, `propext` | `1d43f6961f0e999702c30417ec31b3c2a066d1f0cda64ec31c9035ad0cae2288` | `7e7e853bb5d00cabf3633d4da62d18e6b4830d13c6f081156c75dad443a5d5c6` | 31 |
| `genLayout_dec_isSome_iff_classify_of_span_lt` | R2.4 result; cited by R2.3, R6.1 | `Classical.choice`, `Quot.sound`, `propext` | `6818749eb4c437201799815865985bc0163850bab1066a40a59223cc1c0ec5a7` | `63f4544f57ea0332817e27a33e2badd73f54fd5eef1ffed5382e637d6423fd3d` | 38 |
| `genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange` | R2.5 result; cited by R2.4 | `Quot.sound`, `propext` | `37693899bce7891f40aa40c1f912ca2208b4accd5d63068bd275ec2081371eb1` | `e8216c550c78c1d4aaa2df1bfff6ea7b4b2f8ea34016c1a4a974edf9126bbe03` | 31 |
| `exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull` | R3.1 result; cited by R2.2 | `Classical.choice`, `Quot.sound`, `propext` | `5d4adc0ea61ada117870fe328b09c28ca9330d5f0c43806ac675c0db9ca9e9c8` | `ec66e79ddb187d423c2369aaf08cbbf699f5f8f267ae529e05e5754724f65cbe` | 12 |
| `sub_size_le_nichesCount_and_eq_iff_of_covers` | R3.2 result | `Classical.choice`, `Quot.sound`, `propext` | `5c9c272f5acec691eaa2a3952bd6c0f4c2efb7d1e484d73208e3e728e9dfc6be` | `3ccb148a9f07e161354497fcb3c4217916a4d9f886ec66fa15b5475a9ae416d7` | 9 |
| `nichesCount_intervalV` | R3.3 result; cited by R5.4 | `Classical.choice`, `Quot.sound`, `propext` | `5ab5ab478e9e1c0a4e2736dfd9d847f05f857f8dceb6b43b11c169eb8f3e306e` | `a1aca57df6b6bc039ff625bc41c1f58ee0b1796ab59c99b4481c3533b12e080a` | 10 |
| `exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq` | R4.1 result | `Classical.choice`, `Quot.sound`, `propext` | `1bd7b367aa142094982f5868d4efd82af65c4a758d04c6717cea0a0c2c5e062c` | `0244373441802379a6a5fc952ed6fdd414a356ee195514ce807ff9646026888b` | 15 |
| `rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid` | R4.2 result | `Quot.sound`, `propext` | `875d11f82279d87eff8a1ac3fca89a7a5cb0a4bf1f8f1a973a42e967b4d1cf8b` | `444cfa7385f85833c1eeadaebf6a903133526ac682d21c1eaa951c84c57f32ea` | 7 |
| `extend_spec_of_size_lt` | R5.1 result | `Classical.choice`, `Quot.sound`, `propext` | `ba1c388c224e441ba30e940dea91ab87d11e22f64621c607fe4f3506bf1f5964` | `f3fe1dbc473a9d2c28ebd0fe3f732f1e3b95a4858df0664602ae30f595fd3728` | 19 |
| `nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt` | R5.2 result; cited by R5.3 | `Classical.choice`, `Quot.sound`, `propext` | `0aeae647517340cbad7c8e8065fb39476dad42a0b28413c2ab94ea4f74996666` | `a0a7612f835eb07e9350e687ad83e7171ce11ffea73f3031c8a8de1b890eb09c` | 34 |
| `levelsReserveNiches_iff_length_le_and_nest_size` | R5.3 result | `Classical.choice`, `Quot.sound`, `propext` | `d5a6de97b5aa5cea2ee02a01fc7fb8f46d2be31c2dc634831c078eb47314fd76` | `5d799e2f98ec6180f7932bc6eaf71991108256b384d8a27c78d58172cf1e38b8` | 23 |
| `exists_lawful_extEnum_intervalV_iff_le_sub_size` | R5.4 result; cited by R5.3 | `Classical.choice`, `Quot.sound`, `propext` | `58bd6c5626b7937f3ba55faee24687f99998996328cd3220f93c6a94b32d2d27` | `24f8ba12f4b7e65eee61c8bb0e1e178974b17dd80b81bbcecb5ea2f2d77b52c3` | 20 |
| `setDisc_operational_untagged_isSome_iff_of_tagsDisjoint` | R6.1 result | `Classical.choice`, `Quot.sound`, `propext` | `958761e57fc11a803b5d490c90390df826f4e1dd328d01cc71ac9a188502e632` | `9ab120d285a37fa5d05e5527a574d181c7e78374da9a9712430621542224610b` | 55 |
| `run_erased_eq_some_of_run_operational_eq_some` | R6.2 result | `Quot.sound`, `propext` | `1958a83c1914a02aa2c17fb5564de5694898301993b27c0c21f7b189f6f6c48d` | `b5c720995b23612475d3ae5a866147cba873666536e1c6731a198ae2a967b30f` | 65 |
| `run_write_setDisc_comm_of_disjointFromNiche` | R6.3 result; cited by R6.1, R6.4 | `Quot.sound`, `propext` | `34790b1d2a340e315e354efcf6de7b9015de6a3c412ebbd71bbea4571770fb6a` | `1ae4ada6dcc86c7244ad1e2f6fb4f191a8bed7f33b1b642aba76879c78d079c2` | 66 |
| `run_fields_then_setDisc_readDisc_of_disjoint` | R6.4 result | `Classical.choice`, `Quot.sound`, `propext` | `5f29ee811dc95e24312a0d0bde9a1e435c27d50ea539af4c1bc573cb46b392aa` | `7845616117e4fa96eac73f99d4b1df013d2a13c2372b4db086584ae494018bff` | 68 |
| `A0` | concrete fixture; used in witness statements of R2.1, R2.2; used in `ex_affine`, `ex_decodeIdx`, `ex_affineLayout_pos` and 1 more | `propext` | `3b818ee387af5057e047ae43adc7c3ebf35c050931d2fad151e1f1a0ef6a14b0` | `938265be6bcd95c2440a2f061a22ae6eb3b1dd87a4a9b62ac5b689050ed22555` | 2 |
| `AffineNiche` | definition; cited by R2.1, R2.2, R2.3, R2.4, R2.5, R6.4 | none | `c7c35980b7ad3879fd092de3c6b98bda7cc6446cda2a156c66df91facc66718b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `AffineNiche.last` | definition; used in `ex_affine` | none | `ed576a0f7cd9ac275381e4c1f0c9d1a07e0d68363ecf8d682fb755b3d27b170e` | `938265be6bcd95c2440a2f061a22ae6eb3b1dd87a4a9b62ac5b689050ed22555` | 2 |
| `AffineNiche.tagInterval` | definition; cited by R2.3 | none | `1c89333d028ee6a8c53c7864dc0a1a26bd28d1af46d1500ab1fde07da0c61b90` | `82872349dfdd6545a1c90498e4e6f112cd2a8f6445b1fa06f7cac076aea7cdb6` | 4 |
| `AffineNiche.tagOf` | definition; cited by R2.1, R2.3, R6.4 | none | `faf5c6690a7ecaa8d414c609fb0eefc94f179a00275b52085348d93e54860c20` | `938265be6bcd95c2440a2f061a22ae6eb3b1dd87a4a9b62ac5b689050ed22555` | 2 |
| `Ag` | concrete fixture; used in witness statements of R2.4, R2.5; used in `Lop`, `ex_liveInRange_pos`, `ex_genLayout_pos` and 4 more | `propext` | `3b818ee387af5057e047ae43adc7c3ebf35c050931d2fad151e1f1a0ef6a14b0` | `938265be6bcd95c2440a2f061a22ae6eb3b1dd87a4a9b62ac5b689050ed22555` | 2 |
| `Bytes` | definition; cited by R6.2, R6.3, R6.4 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Covers` | definition; cited by R3.2 | none | `add7a1c36096f8b6dec63a53b709f628f68f972a914f7598a79572f33d8ea2dc` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `E1` | concrete fixture; used in witness statements of R2.3, R2.5; used in `Lop`, `ex_live_pos`, `ex_live_neg` and 7 more | none | `d6d7cc52f53c9f653a71bcb7acd6af4bef86ad6fb1ae1116e6dfb17352f83261` | `3a8c784645bc1948c2f63b6ace6d9ccfe64dc759069e12d08f1cb06fbbe1daa2` | 2 |
| `E2` | concrete fixture; used in `ex_live_pos`, `ex_live_neg` | none | `d6d7cc52f53c9f653a71bcb7acd6af4bef86ad6fb1ae1116e6dfb17352f83261` | `3a8c784645bc1948c2f63b6ace6d9ccfe64dc759069e12d08f1cb06fbbe1daa2` | 2 |
| `EnumSpec` | definition; cited by R2.3, R2.4, R2.5 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `EnumSpec.Live` | definition; used in `GenVal`, `genLayout`, `classify` and 4 more | none | `f6539660755b422088244bb90b687c3ce91f45f7368fe4f36dedcdfa75c97a10` | `3a8c784645bc1948c2f63b6ace6d9ccfe64dc759069e12d08f1cb06fbbe1daa2` | 2 |
| `ExactFor` | definition; cited by R1.3, R1.4 | none | `ffd5c84473ddc2f78f54da71e7ded4eb8df385f38bcddb9a059c4b805eab637a` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `FieldClass` | definition; used in `classify` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `GenVal` | definition; used in `genLayout` | none | `be96eae378bde6cda2b4bd04f7d58393797e1ad1ad324b0232910988ef616a0f` | `37ade3eaf867e425fb5aa1d3fa202329e538c248cace066ce2618cd5ee0f254f` | 4 |
| `Imported.Canonical` | imported definition; cited by R2.2, R2.5, R5.4 | none | `71bc16e8396157e58171ed974b25d352f89488aad51fcde9f651ba228c427d27` | `0da1261a47f97b9e5940668763fad7396e048e28e1dcecce151a2c0c16844afa` | 3 |
| `Imported.DecEnc` | imported definition; cited by R2.2, R2.5, R5.4 | none | `71bc16e8396157e58171ed974b25d352f89488aad51fcde9f651ba228c427d27` | `0da1261a47f97b9e5940668763fad7396e048e28e1dcecce151a2c0c16844afa` | 3 |
| `Imported.ExtEnum` | imported definition; cited by R2.1, R5.4 | none | `3398103b1dd67d5dc72de5cf3acb2dc9d2013f83dd815c681c8fcff4176b783e` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.IsNiche` | imported definition; used in `Imported.nicheLayout_lawful_iff_isNiche`, `Imported.nicheLayoutK_lawful_iff_injective_and_isNiche` | none | `1b191dec16b118c4c2f9ba4b5fecb84f58145fdf33a4daf3655c39ae8909e789` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.Lawful` | imported definition; cited by R2.1, R2.2, R2.5, R5.2, R5.4 | none | `71bc16e8396157e58171ed974b25d352f89488aad51fcde9f651ba228c427d27` | `0da1261a47f97b9e5940668763fad7396e048e28e1dcecce151a2c0c16844afa` | 3 |
| `Imported.Layout` | imported definition; cited by R4.2, R5.4 | none | `221f6f19f5ec8309d1455058adbe32ee1ba0f51a9b15136b2886657ba2b4f139` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Imported.Opt` | imported definition; used in `Imported.nicheLayout`, `Imported.opt_opt_nonZero_no_decEnc_layout_in_payload_size` | none | `92b37b0deb81a3b666095352cbb450c9e113339e0705ed49ca2445d3128d7d7b` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.Pat` | imported definition; cited by R2.4, R6.1, R6.4 | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Imported.Val` | imported definition; used in `Imported.ExtEnum`, `Imported.Opt`, `GenVal` | none | `92b37b0deb81a3b666095352cbb450c9e113339e0705ed49ca2445d3128d7d7b` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.Validity` | imported definition; cited by R2.1, R2.2, R2.4, R2.5 | none | `f6f89b1e202b0402af79d58f047c64c0c027411fd8a20194e7a83a70d5bb9d4f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Imported.allV` | imported definition; used in witness statements of R2.2, R2.5; used in `ex_affineLayout_neg`, `ex_genLayout_neg`, `LopAll` | none | `92064bd06f653685e8985d4de27c4278a7dced467bcf750184fd8a7e93128edb` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.firstNiches` | imported definition; used in `Imported.le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches` | `propext` | `2fca5cf2a95b60282237ea16a67da8cc3ebd65555ff9827c0d85005fddb7dd44` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches` | imported theorem; cited by R3.1, R3.2, R5.4 | `Classical.choice`, `Quot.sound`, `propext` | `6eec567f03ee3ce27de078bfc445867c1fa0de461b1807e05c63fb5e5aa23cb1` | `71c2ca795c901d48541414a73f0b3a218a7dfb91a004308759b7da0a384f8691` | 19 |
| `Imported.le_numInvalid_of_decEnc_of_size_le` | imported theorem; cited by R5.4 | `Classical.choice`, `Quot.sound`, `propext` | `e8245f3253074ea975bb83877e4d5a77b9f52fb57e0e881ecd7ea2e8e06ecce2` | `7dbe4b550c7da75ee21bf3cd869f36f6ef5a0fa7ceda349f89c40fd5704ee734` | 11 |
| `Imported.nicheLayout` | imported definition; cited by R5.2 | none | `22c896e66154a5a53743390bc4f1701f84fef785b84313a87000bb6fb2353b51` | `cdf1ae73f677f5b49ebd4c7654f9aa2758c5f60cad0cb339bf171a9a8812948c` | 6 |
| `Imported.nicheLayoutK` | imported definition; cited by R2.1 | none | `f2f092ea20cccb1fe6f7f7085ad3085baacd10958434e4f81c6279ea73858e82` | `c478b2256d4c159566cf1b9769b1cc8c43633b2debc7b599da33f71d388d4e75` | 6 |
| `Imported.nicheLayoutK_lawful_iff_injective_and_isNiche` | imported theorem; cited by R2.1, R2.2, R2.5 | `Classical.choice`, `Quot.sound`, `propext` | `b5f6e56e2ded6b76d3440049277c36e24dd36b72528a676b70a5655af73afc53` | `4cedf43126ff75b0d4ec0696a951d554175ad06c4bf830cdea54106ef741f708` | 15 |
| `Imported.nicheLayout_lawful_iff_isNiche` | imported theorem; cited by R5.2 | `propext` | `06f15c47bb2e98e4d805b5f1bd3a9efe705aa11c43a00f5d3c5fdd3e7cc66b7e` | `7826d822b885e7ef99bec79823bb890ad08d0dc4cdd4834d97885ff93660b2f7` | 14 |
| `Imported.nonZeroV` | imported definition; used in `Imported.opt_opt_nonZero_no_decEnc_layout_in_payload_size`, `ex_intervalV_nonZero` | none | `92064bd06f653685e8985d4de27c4278a7dced467bcf750184fd8a7e93128edb` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.numInvalid` | imported definition; cited by R3.1, R3.2, R5.4 | none | `fb7fa99b1a5e918785bc94dc84e511b0a072883a14974f2379afa169e847a5c2` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Imported.opt_opt_nonZero_no_decEnc_layout_in_payload_size` | imported theorem; cited by R5.3, R5.4 | `Classical.choice`, `Quot.sound`, `propext` | `b080caa6c14eb2e99636aadd5e075e6d0b2bec225d3525cfb583d217092dd8b3` | `8f84462779adff25d7d61b5c2793d622b10702d4d86c8ca8146f1ad50ff6bb2f` | 10 |
| `Imported.pat_card_pos` | imported theorem; used in `OpLayout.readNiche` | none | `e224f035bbbd72b58204059dc0db2f0ec7e7f4bdb93ced1fe9d4eba0837cbaef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `IsHull` | definition; cited by R1.1, R1.3, R1.4, R3.1, R3.2, R4.1 | none | `1d2ff508a387e105b1e4854f0a91ba0ea516e3014983495737f4bb39a756bd79` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `IsWrapIntervalSet` | definition; cited by R5.3 | none | `b70fbd734e2cc39374b318764606d9bafd16983bac9433d9deb5fd3870bf0a6a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `LevelsReserveNiches` | definition; cited by R5.3 | none | `ecbeb86f8d847c813b014892c485630316b768cd870e4be70613070ad7205c78` | `322ed90dd16be7405f9ad783bc9c989c81a8748e488b7a1e041290581425e991` | 5 |
| `LiveInRange` | definition; cited by R2.5, R4.1 | none | `b1b58d38df824474578f4f89737fdd8f1552fef15b50c3d922a6bede05350747` | `2a0ee2d8afa290cf14e78db2d3dc12c4c68652fdb7a667e70f7dc02f55002d00` | 4 |
| `Lop` | concrete fixture; used in witness statements of R6.1, R6.2, R6.3, R6.4; used in `ex_run_write_oob`, `ex_readNiche`, `ex_readDisc` and 11 more | `propext` | `b58dd1b51fcf16373c3ae879fcf0038ff8b361aa79075adb1822d71b335b9e93` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `LopAll` | concrete fixture; used in witness statements of R6.1, R6.4 | `propext` | `b58dd1b51fcf16373c3ae879fcf0038ff8b361aa79075adb1822d71b335b9e93` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `LopFar` | concrete fixture; used in witness statements of R6.4 | `propext` | `b58dd1b51fcf16373c3ae879fcf0038ff8b361aa79075adb1822d71b335b9e93` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `LopNone` | concrete fixture; used in `ex_setDisc_untagged_uninhabited` | `propext` | `b58dd1b51fcf16373c3ae879fcf0038ff8b361aa79075adb1822d71b335b9e93` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `LopWide` | concrete fixture; used in witness statements of R6.4 | none | `b58dd1b51fcf16373c3ae879fcf0038ff8b361aa79075adb1822d71b335b9e93` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `Op` | definition; cited by R6.2 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `OpLayout` | definition; cited by R6.1, R6.2, R6.3, R6.4 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `OpLayout.DisjointFromNiche` | definition; cited by R6.3, R6.4 | none | `2dcc08db27d13429e36f99d644aa3e8ec23cecc69c05c75ca1e34965ec592df0` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `OpLayout.Encodable` | definition; cited by R6.4 | none | `bc679a1c1fbf430a7a0dc3803e3c4c2794aad44ca756a28141148dad8a34747f` | `8ba393f5d4e9020660635801a9892fde32bd1b1d51c129f5c8086d290b419628` | 8 |
| `OpLayout.readDisc` | definition; cited by R6.1, R6.4 | `propext` | `d88d5569ea6284bddcab5284569ab56b037bdf4c2668db00701bd3cb5e52e524` | `98e9b768353b5377ca4da61ed50de1fc4d46f0c1787bcae84f3ddc07c788784a` | 9 |
| `OpLayout.readNiche` | definition; cited by R6.1, R6.4 | `propext` | `5d8f75c0a00e94df68607ce65699eea641966b17b51376248e7d4ada6333077d` | `e71687b996b278b482f20a958c87a6b8ee371c3fad1291f7ae4a881de2f2e54f` | 10 |
| `OpLayout.writeNiche` | definition; cited by R6.1 | `propext` | `d581f1b743c9b35f6aa4295715b6857702cb465bf5f9acad84f253e69c5c0ac2` | `e71687b996b278b482f20a958c87a6b8ee371c3fad1291f7ae4a881de2f2e54f` | 10 |
| `RotTagsInvalid` | definition; cited by R4.2 | none | `cfdf97f8ba8c701b889d6e2ac390d235358df52d44aa645f2c368529f11c258f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Sem` | definition; cited by R6.1, R6.2, R6.3, R6.4 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Side` | definition; cited by R5.1, R5.2, R5.3 | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `TagsDisjoint` | definition; cited by R2.2, R2.3, R2.5, R3.1, R4.1, R4.2, R6.1, R6.4 | none | `f3520a7886ea9107ee9f40401bbe048bb1aee034879506e6d10eab56252215be` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `V0` | concrete fixture; used in witness statements of R3.1, R4.1 | none | `3364c0ab7aeae735930b16d6adc0d62ddee2dc413f900badf8f352551c740731` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `V01` | concrete fixture; used in witness statements of R3.1, R3.2, R4.1; used in `ex_isWrapIntervalSet_pos`, `ex_nichesCount`, `cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH` | none | `3364c0ab7aeae735930b16d6adc0d62ddee2dc413f900badf8f352551c740731` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `V02` | concrete fixture; used in witness statements of R3.2; used in `ex_covers_pos`, `ex_covers_neg`, `ex_isHull_pos` and 4 more | none | `3364c0ab7aeae735930b16d6adc0d62ddee2dc413f900badf8f352551c740731` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `Vlow` | concrete fixture; used in witness statements of R2.5; used in `Lop`, `ex_genLayout_pos`, `cex_folklore_dead_slot` | none | `398e8dd38c38c205b9430139f99d2955a7bb97d3860d7bd179c74cf7bd521c1d` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Vlt254` | concrete fixture; used in witness statements of R4.2; used in `ex_rotTagsInvalid_pos`, `ex_rotTagsInvalid_neg`, `cex_folklore_fit_depends_on_untagged_position` | none | `398e8dd38c38c205b9430139f99d2955a7bb97d3860d7bd179c74cf7bd521c1d` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `Vmid` | concrete fixture; used in witness statements of R2.1, R2.2; used in `ex_tagsDisjoint_pos`, `ex_tagsDisjoint_neg`, `ex_affineLayout_pos` | none | `398e8dd38c38c205b9430139f99d2955a7bb97d3860d7bd179c74cf7bd521c1d` | `e664cbf2f2b2847dde71965a6ccaeb177deb39eec4676ea1201502b533b89392` | 2 |
| `WrapInterval` | definition; cited by R1.1, R1.2, R1.3, R1.4, R2.3, R3.1, R3.2, R3.3, R4.1, R5.1, R5.2, R5.3, R5.4 | none | `c7c35980b7ad3879fd092de3c6b98bda7cc6446cda2a156c66df91facc66718b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `WrapInterval.Mem` | definition; cited by R1.1, R1.2, R1.3, R1.4, R2.3, R3.1, R3.2, R3.3, R5.1 | none | `cd8a8b1e81bf98582e6f1ee49d84e61b88bdd1449114288dda0ce066e94c837b` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `WrapInterval.compl` | definition; cited by R1.1, R1.2 | none | `15a3f8f21d3509c863d78432af110212713605facb48dc7e43f575002e077de4` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `WrapInterval.size` | definition; cited by R1.2, R3.1, R3.2, R3.3, R4.1, R5.1, R5.2, R5.3, R5.4 | none | `b48f431d1fe6d53e88143de98a838773993754f193f662f1d384014467ab5460` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `adjNiche` | definition; cited by R5.1, R5.2 | none | `e21ca81a10186973fb379a282917a1aa79a75da37de368935c97f1798afcbd7b` | `322ed90dd16be7405f9ad783bc9c989c81a8748e488b7a1e041290581425e991` | 5 |
| `affineLayout` | definition; cited by R2.1, R2.2 | none | `b81a8754744c37acebf655355b7b365ccf74746523f0fed49f22e0dba12b1017` | `6deba0833ab19e8c2cfed26f9617c86cb07ba42484b1bfddaeab3c335206b9f0` | 9 |
| `affineTags` | definition; cited by R2.1 | none | `67df3049bf6521d152eabbfa0bf38868d56bdce8053dd40dea60a73362f3d428` | `29db5eaa170a14f39aa33a58edcbbd505291688ac44af1f32df22b3bfbd94855` | 3 |
| `cex_affineLayout_lawful_overlap` | R2.2 positive control | `propext` | `67512fa11d33cd38e5bc961c70845a773d124857e9cae303cb103604283f01b4` | `a770015379c7a4350b3b53726652fb84d18f5aa6e5394ea39d8697f89a14645e` | 28 |
| `cex_affineLayout_lawful_span` | R2.2 positive control | none | `011191f45b0ad28a8923b536ebf9653e6f42a5460295aaef6c7b2d8f4c89b8e5` | `59d9824a1ed27da3c8ce3a05baa3f9a61c6f19c1e1f9f4a057936be77e71247d` | 24 |
| `cex_classify_valid_iff_and_decodeIdx_hdisj` | R2.3 counterexample (hdisj) | `Quot.sound`, `propext` | `2fe4c16250b3942f0725fc9d1934311d529364a54da16c8d8fc91298ad461e06` | `2062331683ad323b4eeb3d0e6c8232233975ecf96602d29eac56015ae34d0746` | 32 |
| `cex_classify_valid_iff_and_decodeIdx_hspan` | R2.3 counterexample (hspan) | `Quot.sound`, `propext` | `5c36ecba3c0be137e14e00eb3e1bdc2e734389cb9d0c63abdbca4d59124a0ae4` | `2062331683ad323b4eeb3d0e6c8232233975ecf96602d29eac56015ae34d0746` | 32 |
| `cex_compl_mem_iff_not_mem_of_size_lt_hI` | R1.2 counterexample (hI) | `propext` | `3fef3fe44ede6290f925f1f79d7f0a71bc686de121bb2e1d84411b09d4654e71` | `ab36b9171b1f2cff651feac8734a5ff3030e62c31b05d699d564cee22d7335cf` | 12 |
| `cex_exists_tagsDisjoint_iff_span_succ_le_hH` | R3.1 counterexample (hH) | `Quot.sound`, `propext` | `24c3c02fda36327e242432b9402de2c0582d53a7250965a34e7d05e941ad8711` | `1ec89002c5b6134cdcadd108d74b291b17875d6bd34957b1efbdc15a376dc9c2` | 13 |
| `cex_exists_tagsDisjoint_iff_span_succ_le_hne` | R3.1 counterexample (hne); cited by R3.2 | `Quot.sound`, `propext` | `40dbe8a85e0ac211efbadb4eda24b12bc7ad02622c873c3cc69c791ae32c4ca4` | `ec66e79ddb187d423c2369aaf08cbbf699f5f8f267ae529e05e5754724f65cbe` | 12 |
| `cex_extend_spec_hI` | R5.1 counterexample (hI) | `propext` | `2293c3adb391f4757b8f99f8db6a72d38b6870bc61efee3405b6070b328a6275` | `f3fe1dbc473a9d2c28ebd0fe3f732f1e3b95a4858df0664602ae30f595fd3728` | 19 |
| `cex_folklore_dead_slot` | folklore refutation; cited by R2.3 | `propext` | `9e68308edc50affa1af862aab49496ad1d47fe1f9fa98d755ce0c0059293b05c` | `a8d084e898f0bf18e0981ed4f318d0e0a0ddbc921e9f3667cd1b7f28f0823c48` | 44 |
| `cex_folklore_erasure_not_equivalent` | folklore refutation; cited by R6.2 | `propext` | `d3e9de261d0c6cd0b9e50a09ed163e7e6455315aba165231290e371394a52233` | `f5e3af2fb60d09dcc95d7c26172be20d35a0afdb7947b68f9a454d0b35e33eb8` | 71 |
| `cex_folklore_fit_depends_on_untagged_position` | folklore refutation; cited by R3.2, R4.1 | `Classical.choice`, `Quot.sound`, `propext` | `c79eba148355794b0d9889feab0aaa05f29236306741c008869662e75e1edd8d` | `b9ab73e03c2f551b464d632853a3a6751553f7827a4fcbeed05df66a0260f9d8` | 18 |
| `cex_folklore_fragmented_capacity_lt_nichesCount` | folklore refutation; cited by R3.1, R3.2 | `Quot.sound`, `propext` | `feddf840efe1d2540901de4949c2a0b982eaae74ff3a7d9ba60a4be3ab257642` | `bc8c90fc479fd194f0334481e61a37acf1c519d62b900520ccba995226db55e5` | 14 |
| `cex_folklore_nonadjacent_reservation_fragments` | folklore refutation; cited by R5.3 | `Quot.sound`, `propext` | `bfb2d06ff1dfccf79a0028fc523a6cd8ff0eb5af6952a3e531dbf81810d07d63` | `0002e431a78623e160b76f27114283ebf738d4050ad6eae9e4ff0c8f6561e990` | 25 |
| `cex_folklore_payload_write_setDisc_noncommuting` | folklore refutation; cited by R6.1, R6.3, R6.4 | `propext` | `ae34bef4d872eaef519526236317927c20b18d79444f4a00bb11b8283d1ec4f7` | `f5e3af2fb60d09dcc95d7c26172be20d35a0afdb7947b68f9a454d0b35e33eb8` | 71 |
| `cex_folklore_signedTestI8_127_128` | folklore refutation; cited by R1.3 | `propext` | `0e923970230fe524ca91a5db970f75bf5694a42beaa45a70862c71a370c37ada` | `630759368266c6dcd730e554ff230838a2f3cf1055a1df3efb4489a523826b30` | 7 |
| `cex_folklore_unsignedTest_255_0` | folklore refutation; cited by R1.3 | `propext` | `f08f9b03aae629c433265ac9343af1bdb3174a62411e9aa10ca3037c720fdb11` | `6cd6273c51c2737daa45718c8325d4749b7896a76e9a20e5161165cfd133c473` | 6 |
| `cex_genLayout_dec_isSome_iff_classify_hspan` | R2.4 counterexample (hspan) | none | `1c18165f97d0a2d2cd79345f92d9ed456ce39e46d335383e11b1ce5a611a2514` | `294d3bc420694fdc3178ed2d36261f938e57d4e2c47074fd670a4898716733f3` | 39 |
| `cex_genLayout_lawful_hdisj` | R2.5 counterexample (hdisj); cited by R2.4 | `propext` | `5b341f43adf4b696f7c8f473dbe83d6cb69e80b3f1df6de5cad653f075e7588b` | `dd8a998d82751ccb1b54f4edd0a528c574f22295669def746ebc0f3acddb4cba` | 35 |
| `cex_genLayout_lawful_hdisj_deadSlot` | counterexample; cited by R2.4, R2.5 | `propext` | `03df0e08bbc6acb187682b647aea0237f1eea5e4292c73f5ae20d53c478fb22f` | `072e4475ef7830d648a061aa57d1e9c1a75c2152a286a37e134ba608840a7f35` | 48 |
| `cex_genLayout_lawful_hlive` | R2.5 counterexample (hlive) | none | `e456ee1ec92fd883e6c34808c2e4237f1610cce5a7e611912090f9b4e1c4fa89` | `c295ede080d25e98da5730e3879a2f809e90eb20afeffcca4e5cfcc4b3121914` | 34 |
| `cex_genLayout_lawful_hspan` | R2.5 counterexample (hspan); cited by R3.1 | none | `9fb5a76a0c586bec5951006a19c84edb487f1cc5ab2c5eb1f2bcd9764010b842` | `5d0e44bd07938f2a96b769f3a57ff23ea670b0d7e54e4585c0758fdf73af7ba7` | 32 |
| `cex_naturalSpan_hH` | R4.1 counterexample (hH) | `Quot.sound`, `propext` | `65578d0c90addb581c8afe960ba1b78dd83145db5187fbc9b94d18ad28aae9f6` | `f7d1854e44b64b58964d0253eb50ab4e9588ec3433ee7baf798806ab8a712d5b` | 16 |
| `cex_naturalSpan_hcap` | R4.1 counterexample (hcap) | `Quot.sound`, `propext` | `ce30ceada9aa97fe9d8c86779e32088fa2ce714b55d3709e023bba2235edc4ad` | `f7d1854e44b64b58964d0253eb50ab4e9588ec3433ee7baf798806ab8a712d5b` | 16 |
| `cex_naturalSpan_hk` | R4.1 counterexample (hk) | `Quot.sound`, `propext` | `2a574eb66b49c554e26be736c0ab1e58fc719cea9814c89aaebbeacae3034c47` | `0244373441802379a6a5fc952ed6fdd414a356ee195514ce807ff9646026888b` | 15 |
| `cex_naturalSpan_hne` | R4.1 counterexample (hne) | `Quot.sound`, `propext` | `ec64bab889c1d0b5f40d2d44113538dbe1b3ee3b844eda8354c4462afdcc06c3` | `0244373441802379a6a5fc952ed6fdd414a356ee195514ce807ff9646026888b` | 15 |
| `cex_nicheLayout_adjNiche_lawful_hI` | R5.2 counterexample (hI) | none | `f35786b79ed420364e9f1e0709e0532d21aa013db1e9a67355a61d00befa75eb` | `f6a6fca967e0ca52821674766719de8c99bc0aeba54e3835af76163f364ca263` | 35 |
| `cex_not_exactFor_originTest_wrapSub_one_of_two_le_hM` | R1.4 positive control; R1.4 counterexample (hM) | `propext` | `159b2f885c6a081ca4c12c9d506d5a9b95c064876e6b3b3721ed1a5cb3fcd734` | `94b29893435ede73a56cf73018eb3cd70277459c882080f5aefa7d49559cc707` | 10 |
| `cex_rotDecodeIdx_hdisj` | R4.2 counterexample (hdisj) | `propext` | `f00bb728d6426f6a043bffd972c2555d8178cfe292c24ba3b2e12223df712071` | `444cfa7385f85833c1eeadaebf6a903133526ac682d21c1eaa951c84c57f32ea` | 7 |
| `cex_rotDecodeIdx_hkM` | R4.2 counterexample (hkM) | `propext` | `d4fd36a49db79b7d8d00fffe722d8900f63c8e9db9ac04b76c7de41a40a52634` | `444cfa7385f85833c1eeadaebf6a903133526ac682d21c1eaa951c84c57f32ea` | 7 |
| `cex_rotDecodeIdx_hu` | R4.2 counterexample (hu) | `propext` | `e65b5fc8e9af7e606dda82e455f0e9899244aee8ae1f5414d25a4964a7966c70` | `444cfa7385f85833c1eeadaebf6a903133526ac682d21c1eaa951c84c57f32ea` | 7 |
| `cex_run_fields_then_setDisc_hdisj` | R6.4 counterexample (hdisj) | `propext` | `408a81367220073f6ad262b70b48e72cd51af657fa45c1a57a4c58afd3162a8f` | `50d641821da5ef49f80dc21c99b69d899c8dd881a785aaeeec4bdebc07b91fbe` | 77 |
| `cex_run_fields_then_setDisc_hfit` | R6.4 counterexample (hfit) | `propext` | `eb5cff4cb9d0174d258b6137fc4cdafb935fc9ccc3f17146ce0140dba9a253a2` | `514097d8ae83c4f39374905a1a653e21d7ac5d6648b7b11e384e387d1086fa51` | 75 |
| `cex_run_fields_then_setDisc_hin` | R6.4 counterexample (hin) | `propext` | `0c7ce75cde8f2229a4d6c9ee8e518f7c565260140f653a57183dde217b0984f2` | `4736abad7b983e2eb97d394148bbc07830cccd4ae8ddbf1e176d6bd621330e2d` | 74 |
| `cex_run_fields_then_setDisc_hpw` | R6.4 counterexample (hpw) | `propext` | `0931e7aecc7669ee09e70e26aed9aa2c60ec483fbf31d2f6ca820ac42677f366` | `4736abad7b983e2eb97d394148bbc07830cccd4ae8ddbf1e176d6bd621330e2d` | 74 |
| `cex_run_fields_then_setDisc_hspan` | R6.4 counterexample (hspan) | `propext` | `6204a762c5ee8e75ea03fd311f3c649d646e6addee73e711bb171cd42783d989` | `bf52ff71c414b5af4e34d91a6ce56a588ed66f3c557f59ca8c3c03ee68893ec0` | 71 |
| `cex_run_fields_then_setDisc_hws` | R6.4 counterexample (hws) | `propext` | `220b032c54d2b4d6ddd08a7d7525f0ab30f7e081c1f6ebe5dfb593025e0095cf` | `4736abad7b983e2eb97d394148bbc07830cccd4ae8ddbf1e176d6bd621330e2d` | 74 |
| `cex_run_write_setDisc_comm_hdis` | R6.3 counterexample (hdis) | `propext` | `ab60a72d8d389da083d6c2835a29625fc3b2f56591967565983436cd89aa1523` | `4ffbbc0e85ce70b15c5f1569bb764bf7e0ed796310d54096bbc067c1c6f3551a` | 72 |
| `cex_setDisc_operational_untagged_isSome_iff_hdisj` | R6.1 counterexample (hdisj) | `propext` | `1fbc8af3f519dbd4c8b0b5009520cabf8cfd7659cebf633b4ee12e37fe4205bb` | `abde0a19545734c169778b20a9a26aca232558fa2dae01b3be91350cc5ac8b30` | 64 |
| `cex_sub_size_eq_nichesCount_iff_isWrapIntervalSet_hH` | counterexample; cited by R3.2 | `Quot.sound`, `propext` | `006297ac6a449e2924d67f5e611fae3c42ffaff8a2e820060dfe26779b82794c` | `ceef5af5178f43be18c49b401aed13632d3e86275ba031ee2a21f67da808616f` | 12 |
| `cex_sub_size_le_nichesCount_and_eq_iff_of_covers_hcov` | R3.2 counterexample (hcov) | `propext` | `68b8154438f6853f328d4b7b50f2e911c063d78c84d8d37aec7e654c95a829cc` | `66d95d222e46f4d4f433bd5cd07aed2c913d172f18be530ec401de55706f57e7` | 10 |
| `classify` | definition; cited by R2.3, R2.4 | none | `70e8c0214c5c3bf0d1e825c3a8a6d88652bff597a135b9ade76e45bca8e2a732` | `b4898a5f3d82f5b8b86ce7956945cc3f12ce7c1f5f68a6fba4d1b282e63d11ee` | 9 |
| `decodeIdx` | definition; cited by R2.1, R2.3 | none | `6d279525eddff73f4d8f27f2b518ff6fbf6635d60a7470d1815d2c41943af73d` | `938265be6bcd95c2440a2f061a22ae6eb3b1dd87a4a9b62ac5b689050ed22555` | 2 |
| `ex_affine` | definition example (`AffineNiche.last`, `AffineNiche.tagOf`, `AffineNiche.tagInterval`, `affineTags`) | `propext` | `3c37caab5b6b1ece15a42635581c9842f66e413dcad3de6e00dc17331c13fc4d` | `72873fe1bf37272a1ee023eb2eae7c275b9212d17d32c80e906874742814afc3` | 15 |
| `ex_affineLayout_neg` | definition example (`affineLayout`) | `propext` | `b3e38b76e3e55856f205e0b7fe63c3aeaca49f3b7cc2a57b1d770aa667051dee` | `1169b79d784b15c349656d762b7480db671594780bc45b944123e3e99cbded84` | 25 |
| `ex_affineLayout_pos` | definition example (`affineLayout`) | `propext` | `2f063e413f97d313f32fa3271801aceab79d6c247d29d53ccc2306155b8ada94` | `d95f44c6118b31ea9d80ac101a4d8d1a8c73f7771939a594b432cd062e50019d` | 25 |
| `ex_bytes` | definition example (`writeBytes`, `readBytes`, `leVal`, `leBytes`) | `propext` | `96c2bd3d5b8e4929dd115f106c6a9f7ebbf8d551a23a8de05d538c67ca0d93b4` | `28d9374b342728947d766449ea2ca7d372a0bac67dc82a99fa457539d2b1ccb3` | 8 |
| `ex_classify` | definition example (`classify`); cited by R2.3 | `propext` | `a9f73221367d63eca15532128d24756f8ceaf29155649ed796802b6e667f6205` | `3ccd280cb445abe66407d9ac112607145a22a03c062bb4b6206ff1194332b9c2` | 31 |
| `ex_compl` | definition example (`WrapInterval`, `WrapInterval.compl`) | `propext` | `b7fe082ca741d2f5d7de1d5e3d02a8ab10968ddc4b43dd65539d3d293d67f5e4` | `b903a5e8ba7a43401df8da27f628bb96d0b33e124d8593d7453acd4986b13229` | 9 |
| `ex_covers_neg` | definition example (`Covers`) | `propext` | `73a69484c325a6d13475ac389050b32d0ba6adccfc11c2ddd338741efe9f36e9` | `00b25ccb12abbdb2ea1ee7aadecf2c3c44a06f548d0ba01301370f95aa646050` | 7 |
| `ex_covers_pos` | definition example (`Covers`) | `propext` | `c31db1f5db6a29e5bdde02a4a01d78c4b526b4b2d0aecf60507065bdb906be56` | `00b25ccb12abbdb2ea1ee7aadecf2c3c44a06f548d0ba01301370f95aa646050` | 7 |
| `ex_decodeIdx` | definition example (`decodeIdx`) | `propext` | `1229d805d72521eaaa14f36aab0ea0d0379cd642ebb5b25e60469d7fb54d7198` | `4f26249211093dda440efbbc62fe12f5a7cdc3d1bae95f72a34dbcc5025d7a4b` | 9 |
| `ex_disjointFromNiche` | definition example (`OpLayout.DisjointFromNiche`) | `propext` | `e53616f92e9ce03137e1fcf157db21e9782c2abfe91a6e8806ab4ef565bb5ee5` | `400b8de25eaba88bb20a04c181ee6b6177e7c8c8718a4e2d0660f28259d1bd6e` | 16 |
| `ex_encodable` | definition example (`OpLayout.Encodable`) | `propext` | `bad2daa80678b79f2ada4194c504249c3dac67101314d51375155df45999eeb2` | `efec07005db06ca0fb86badfb5fbfe7fb552fb433f00e5c07289354b752b4820` | 23 |
| `ex_exactFor_neg` | definition example (`unsignedTest`, `ExactFor`) | `propext` | `7a202a2c4a8e0e13c6a1b0f8fd4ae00cccfe6d4970fec2a8b8aa20a98c233d70` | `f6b295064eb3c4c5fccb8a07cc24f84467a88012fa29d03de2256cdef005627c` | 7 |
| `ex_exactFor_pos` | definition example (`subTest`, `ExactFor`) | `propext` | `141dfc1f95bab7acbcc1049123ac6266218c7f9148258289f04459866c8c4382` | `36fa9cac093c36f7162a5dda5b1dd93eeadaa3f0941edd039aebde13adfadc48` | 8 |
| `ex_extend` | definition example (`adjNiche`, `extend`, `nest`); cited by R5.1 | `propext` | `106170f9bf320e2642f20842e4613234a738e2fd968fcbe482b154e67bb1d250` | `c4c16e1d44d2fd0654d6ee7d9a946c61046b4f514bd9dc08c68fcf1e8c1e8260` | 19 |
| `ex_extend_full` | definition example (`WrapInterval.size`, `extend`); cited by R5.1 | `propext` | `85d42aac8602803a045ef74b0969c7824eb6cffd4ae065c0a883969d9392812a` | `693a10994e77a709805fdb4fc765508dc1d2d8d2c99b5815fd8cafa745d17e7a` | 17 |
| `ex_genLayout_lawful_span_eq_card` | definition example (`AffineNiche`, `genLayout`); cited by R2.2, R2.4, R2.5 | `propext` | `93d26ab1e1304a982dc706d2418661ad3ea00ec85382b3ea24fb261c21e4e5b8` | `3da45ab8b50ed70f6fa1bb129dc9d11922ca711f2b82e3ec660eea3cb24c21a1` | 30 |
| `ex_genLayout_neg` | definition example (`genLayout`) | `propext` | `55ddd1132d38c036f9e61fc3949c1f9ca3a1999507f7bd1fae65b23125262da6` | `9244405bdbab5d48576e8024564c1714097bbfb351cacce7ac86d7c3ef8824ea` | 33 |
| `ex_genLayout_pos` | definition example (`genLayout`) | `propext` | `fd7db5b9ed244f4234869858c1a014412ef7c30432b2c0426408ad8ccf09d7d5` | `7acda6232df71712c166a190bf9c983709c318bda03f716679cda3862ecb594a` | 33 |
| `ex_intervalV` | definition example (`intervalV`) | `propext` | `6f1ecdccdc98755b4fede797f8968de528a34c7371436d21c37747730dc09294` | `4227cc7ee47cea5e5d33d065b977a5243478e5c571a6d9b84dcccded119643af` | 7 |
| `ex_intervalV_nonZero` | definition example (`intervalV`); cited by R5.4 | none | `185b2dc9360f10e4e1da8a1e159acb35f2933b589529bbba6252c9eecf4ff813` | `41552b16338213a87d3e5eb55f528fab3ad1c67190d8935841079f4d9b49edc1` | 11 |
| `ex_isHull_neg` | definition example (`IsHull`) | `propext` | `2a7bb1e3ad3ba1f8abe211d2ecd1d6ed9f1e2fbeb582262adf35651cf249c4b1` | `c62ec57caa55be6238b929a95887154a00a9c0b564bd5bdd9142ee566d7d1651` | 10 |
| `ex_isHull_pos` | definition example (`IsHull`) | `propext` | `4719f9774a7769b02cf622d3264bf726c5a56ededb4acfcd0d7030925876f550` | `c62ec57caa55be6238b929a95887154a00a9c0b564bd5bdd9142ee566d7d1651` | 10 |
| `ex_isWrapIntervalSet_neg` | definition example (`IsWrapIntervalSet`) | `Quot.sound`, `propext` | `c2d5dd391cd925f09b05a68d275a2c0106b9374733183e01c79838b8e7b7f0a5` | `84fcd7382e36b9caa291628dc848da6956130ca82dce50ed8e4fbaa7d088c399` | 7 |
| `ex_isWrapIntervalSet_pos` | definition example (`IsWrapIntervalSet`, `intervalV`) | `Quot.sound`, `propext` | `587dad40915595ab635dcf80f44a39f4174d6a0946eec99c7fab88d9ca17dcd6` | `f988de8f17bd649c604757212f8b074fce578461aadc4f7da8f20ff63c6dd00b` | 9 |
| `ex_levelsReserveNiches_neg` | definition example (`LevelsReserveNiches`) | `propext` | `ca8dc7d9df64c01bf30d4aed698d8b9280fb1bb0b6f2733ae5946f19a54ad648` | `f8c316dcde4aaae1d4962a5b39768871d976ea0ec4109750c9a6537a5301c06f` | 21 |
| `ex_levelsReserveNiches_pos` | definition example (`LevelsReserveNiches`) | `propext` | `bbe08a55e72b5a95a8aabaa8e041bcecfe2a947fb85e0f704b2e7141b109e8bb` | `f8c316dcde4aaae1d4962a5b39768871d976ea0ec4109750c9a6537a5301c06f` | 21 |
| `ex_liveInRange_neg` | definition example (`AffineNiche`, `LiveInRange`) | `propext` | `508c297636f5fa74f6cdb05ccb777e617459005a822031465c3b0ca8d15cbad1` | `495520ee329070df7b93ce12f6ad21a9189d543d91e87d72e03f37342062cfea` | 11 |
| `ex_liveInRange_pos` | definition example (`LiveInRange`) | `propext` | `b1d1841c85bfc14cabc3f07b9cc56a27c6223e1c68990dd761ad22e5bd2990a9` | `7e886152707b3d875a3c191d98b19fe711c5244da953d80a83bdba4859c3ec12` | 13 |
| `ex_live_neg` | definition example (`EnumSpec.Live`) | none | `b6f317c867419aae29c077c6d86158101895fba8bb9807c6397e34eed37d1f1d` | `4ce87436f5db3df0c27bdf1996e703d469992979142066d2980932ada0175b9b` | 8 |
| `ex_live_pos` | definition example (`EnumSpec.Live`) | none | `3ac514330338a2e5633267bbc0891f9ae041ab49995c40e1c9c22c58cab4ad5a` | `4ce87436f5db3df0c27bdf1996e703d469992979142066d2980932ada0175b9b` | 8 |
| `ex_live_u_ge_k` | definition example (`EnumSpec`, `EnumSpec.Live`); cited by R2.5 | none | `f53b05260de8163928a5336e49eaca85a58412ccb7b2ad68bb21db3933689949` | `d993604ee82fb1b8d88f4d3eeaad1874ee33d49fd2c4a707d8452360f0177aaf` | 6 |
| `ex_mem_neg` | definition example (`WrapInterval`, `WrapInterval.Mem`) | `propext` | `29c5df70477e7166fe6ed1c17f62e2b36aab1cb2254306b5426fb725e6fe1611` | `849308372599a5aaa73a53af61d71fc1cc3978e853d173acedee98df4cace80f` | 5 |
| `ex_mem_pos` | definition example (`WrapInterval`, `WrapInterval.Mem`) | `propext` | `8bb8e218664a5e5edc454c0c1d832670b83e6f6f34bface177e4b46ff42e8f1c` | `849308372599a5aaa73a53af61d71fc1cc3978e853d173acedee98df4cace80f` | 5 |
| `ex_naturalSpan` | definition example (`naturalFirst`, `naturalLast`, `naturalSpan`) | none | `59aff851499e8a3db4e0ac2ee25aba7e35dce401d00149032f5832ff5524e423` | `1ea0dcba39d2acc5f4bb5694c0e59eb6abb1cd6d002084e402667af0f18a3db9` | 3 |
| `ex_nest_past_capacity` | definition example (`WrapInterval.size`, `nest`, `LevelsReserveNiches`); cited by R5.3 | `propext` | `9d5c5eb687a529de1cf55c3873b34044cd41c5f8ae2b260d356f739c60ff179b` | `5d799e2f98ec6180f7932bc6eaf71991108256b384d8a27c78d58172cf1e38b8` | 23 |
| `ex_nichesCount` | definition example (`nichesCount`) | none | `10ac8fb8c145689637d2a567d860d065722743a1581e89835e3ab68c7845cdc9` | `c417db01c4317dcc5c81b19072e52e0d1fca914ab4fa5b1950ea060762a43c2e` | 3 |
| `ex_offset` | definition example (`offset`) | `propext` | `7a125c1d5a2bd19173dd953c4acb918bbec173826c3f4178ba8250875f4f15de` | `8bb20c61830b55dc8aea6bf731e38e73eeca9f59f9e3f8f4905d71aaf636abf9` | 1 |
| `ex_readDisc` | definition example (`OpLayout.readDisc`) | `propext` | `ea26aef4dad30d6c25e4946b63d95b3eac27a1ce17fee96d748b49d8bf4fbbd3` | `c48fa587b207e54c02ff80b5120bdc31a4267bae189f6dce7ae73efc8672f330` | 45 |
| `ex_readDisc_unusedNiche` | definition example (`OpLayout`, `OpLayout.readDisc`) | `propext` | `388fef495da1b6c2bec1cf307875a1198e126b25b79c0a3ca3bac174719daefc` | `c48fa587b207e54c02ff80b5120bdc31a4267bae189f6dce7ae73efc8672f330` | 45 |
| `ex_readNiche` | definition example (`OpLayout.readNiche`) | `propext` | `3755ee2062775cd2be2c59339ee2282fa61e7feb6170238f8a6203db7cc8d467` | `e113801d0385b47cec590ec67edf340a0679943ae02232551f07ebb61f5b6ade` | 21 |
| `ex_rotTagsInvalid_neg` | definition example (`RotTagsInvalid`) | none | `02f14d0bd3e1dac0e03844f6252bc70a6544f55f2d7adbafa30ff8b1c094a805` | `84a7508a2177c1f4c8a95110a239c800efb59e4eacc390748689b210ba2d0843` | 7 |
| `ex_rotTagsInvalid_pos` | definition example (`RotTagsInvalid`) | `propext` | `e39e794a80a60b73013c20615427d405741d22a19fe88d82b2cfe7764cabf799` | `84a7508a2177c1f4c8a95110a239c800efb59e4eacc390748689b210ba2d0843` | 7 |
| `ex_rotated` | definition example (`rotIdx`, `rotTag`, `rotDecodeIdx`) | `propext` | `efbcad468f9f5d4925199cb98995a0bf4eab5af7304d013213229477298274d3` | `bf4bc36a51afebdbf98a5200c18287e004e028ac6a393c73d62a6cdc5999ba2c` | 6 |
| `ex_run` | definition example (`OpLayout.readDisc`, `setDisc`, `run`) | `propext` | `5472fb6fc6461271d542d9f4cecd9a2b1c8509b3f477e523ffa42f7e2778355b` | `f5e3af2fb60d09dcc95d7c26172be20d35a0afdb7947b68f9a454d0b35e33eb8` | 71 |
| `ex_run_write_oob` | definition example (`run`); cited by R6.1, R6.2, R6.3, R6.4 | `propext` | `c1f1d25b6c6ed792536f8c6fd4fa60b607b50a1c9ea2e019bdc10fa1501d2870` | `f5e3af2fb60d09dcc95d7c26172be20d35a0afdb7947b68f9a454d0b35e33eb8` | 71 |
| `ex_setDisc` | definition example (`setDisc`) | `propext` | `65b30de8c889ab35182415e5a9b3dbefebf1e07c028b7bc7a7f41ae0349eb24d` | `4db6778739215f750e0c30c4bb8b4699733ca9bf891a74085f28e43406e3003f` | 60 |
| `ex_setDisc_oob` | definition example (`setDisc`); cited by R6.1, R6.2, R6.3, R6.4 | `propext` | `d3c44f0fd02bc7666c655f1e5df981824abb766e31268ad71fc94fef2302eaf2` | `ed2dba2b62821bb4356476152a3087d914b1465a4de094564e574d0d816190ce` | 59 |
| `ex_setDisc_untagged_uninhabited` | definition example (`OpLayout.readNiche`, `setDisc`); cited by R6.1, R6.2 | `Classical.choice`, `Quot.sound`, `propext` | `2d85d070f10d0fe646d128ed1b68232ffc419ff4eb8a7004d733ee9aea7d1279` | `068ff4ea8a21d0490512e6837e65693898b944bca0fb15a3d7a963ba03d3340b` | 60 |
| `ex_size` | definition example (`WrapInterval`, `WrapInterval.size`) | `propext` | `6caf0d0ae49a6b0017cacc5ade5c547a6fe1773197cdc7c315eee9bbc95e57ca` | `742e6c7f64c3f4fea0e8eb84da4b9895341e2eb59656c09f31392abe8aa7db38` | 6 |
| `ex_tagInterval_collapses` | definition example (`WrapInterval.Mem`, `AffineNiche`, `AffineNiche.tagOf`, `AffineNiche.tagInterval`) | `propext` | `45f5ba0c6868e5deb1122352d312d96378324697484a8d2ff6c1e1c373f216d2` | `78a1555d308698217dcec9505d1e93fddf3710bb34df9ba2f89bb05c68c2dc49` | 13 |
| `ex_tagsDisjoint_neg` | definition example (`TagsDisjoint`) | none | `31a306fe3447ec4dd570afc6699c7d9c5e4fd97305669b71a254aa52780cb850` | `02ca9cb7a829243976f11161e5d9e18e1cc56c7ef79538aa8559bf3f02d50702` | 7 |
| `ex_tagsDisjoint_pos` | definition example (`TagsDisjoint`) | none | `96d4483e44e37f0760779c8baa4b95f6f3b801f2e7198300ccaeb9a98bf8707c` | `02ca9cb7a829243976f11161e5d9e18e1cc56c7ef79538aa8559bf3f02d50702` | 7 |
| `ex_tests` | definition example (`subTest`, `originTest`, `unsignedTest`, `signedTestI8`) | `propext` | `773e9bca5aeb152ce55d94577800037cfbf271af6d55bd35c4d5a4e4f11a0803` | `13158716b06e54352fc5a338a2430f24d226152ea463e8a032a0dae7c41ccdca` | 10 |
| `ex_toI8` | definition example (`toI8`) | `propext` | `5d93f52dc2fa3dccd85d1bbdee21089561764794da3705e46e34780720c97bc6` | `2c1982b7b0583cb74aa22a9ea61714635ea34c32e39570cb3d9acd2b4d407fae` | 1 |
| `ex_twoBranchTest` | definition example (`twoBranchTest`) | `propext` | `69cb7e8a6064576919e02d061fd4e1402e8b178d11005111f507bfcf1dbc43ac` | `a9900ef003276d879005a4a45c0f5678268b0671622ad9f1d40a7bd5ee3a21e9` | 7 |
| `ex_wrapAdd` | definition example (`wrapAdd`) | `propext` | `638040e8cf47e0660e646de102357ea37fbe07e42cad265d3a38b0e7ec9d6109` | `7ae0f04df296660da23a20b502535378c78758ad4f56d0ab668a494ce1aed810` | 2 |
| `ex_wrapSub` | definition example (`wrapSub`) | `propext` | `3d6ef25518915616051b7e4c9674d907b8efe4b6f9826a80131d5870bc6ebf1d` | `5a7a9d5e7870e5f4e642332f861d37f0f58600d8c6a7368410e42b1bb307b629` | 2 |
| `exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull` | corollary; cited by R4.1, R4.2 | `Classical.choice`, `Quot.sound`, `propext` | `9b495155b3fca4a8c0ca5bf83ad11b7dd4eb82287334302574c3aeb0897efe84` | `fdc7f6df9ca54a6046ca4af97df1b11bbd999f8ec4cca0b6a22e96c6c8243ec7` | 12 |
| `exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull` | corollary; cited by R4.1 | `Classical.choice`, `Quot.sound`, `propext` | `443a9eca5290a35c0612bce73894f7f476dca5ffd964580fc048a1f4bef0b5ab` | `0244373441802379a6a5fc952ed6fdd414a356ee195514ce807ff9646026888b` | 15 |
| `extend` | definition; cited by R5.1, R5.2 | none | `c9ff1df4140562df347595de055f1553347941f90b49b4c3eb261f145f15a26e` | `322ed90dd16be7405f9ad783bc9c989c81a8748e488b7a1e041290581425e991` | 5 |
| `genLayout` | definition; cited by R2.1, R2.2, R2.4, R2.5, R6.1, R6.4 | none | `efae388bd2fdc9ebc30beff480a69ecda15db13fd6e4f1b08ba2e6b5f04fd78a` | `3222e8735260de08ba3408682cae9d16f541ebdf9d1a100346389160279fddf9` | 14 |
| `genLayout_canonical` | auxiliary lemma; cited by R2.5 | `Quot.sound`, `propext` | `7bc90babf11d54030390e114b9bb0812ce6ec12e05611080d80ca01cc89b08d5` | `4b98fca76163c4e704b42a56f6ea58911dfb427060c68f236080a14f05b48b2c` | 27 |
| `intervalV` | definition; cited by R3.3, R5.2, R5.4 | none | `9834545a4c231163d37029fbecd98a654ae201127429ea2fca1e344b2de6768e` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `leBytes` | definition; cited by R6.4 | none | `8274820d1afb7580166a25906c9057967076137b1da86b6f3724acb1ee5c4494` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `leVal` | definition; used in `OpLayout.readNiche`, `ex_bytes` | none | `1ed9d83b70c5594cd9161939f47fcd4a75442177594ec7256e7c44f4d0cc3dc0` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `naturalFirst` | definition; cited by R4.1 | none | `f9923049a8c8e095b3ef05e0d9af6b14120dcbc7e961af851b322b86aa123242` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `naturalFirst_naturalLast_spec` | auxiliary lemma; cited by R4.1 | `Classical.choice`, `Quot.sound`, `propext` | `1f4071cbe99daaee47e7dbe148a242ae2b2fa81594e6650ea153449fbaa9e2b5` | `723c55298c66b4c59b041ff20e7a4a0c73b87309dd7e37b7f632fb18c632b5d2` | 2 |
| `naturalLast` | definition; cited by R4.1 | none | `a37cdbf166c65e28ae1e257f4fe2bd836828ae16b2febda3343bd8e60be8b43a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `naturalSpan` | definition; cited by R4.1 | none | `a37cdbf166c65e28ae1e257f4fe2bd836828ae16b2febda3343bd8e60be8b43a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `naturalSpan_eq` | auxiliary lemma; cited by R4.1 | `Quot.sound`, `propext` | `63fd46098c823ba49803b012151f7c43a82594b6a8da066ce89f4ff2f65f59c4` | `1ea0dcba39d2acc5f4bb5694c0e59eb6abb1cd6d002084e402667af0f18a3db9` | 3 |
| `nest` | definition; cited by R5.3 | none | `09e658262c3e4ebb07f3f5e0a24b4c9acce65205ebc1bcc2698ed36bc74bfc68` | `322ed90dd16be7405f9ad783bc9c989c81a8748e488b7a1e041290581425e991` | 5 |
| `nichesCount` | definition; cited by R3.2, R3.3 | none | `ae1ffe9600bfdf3405da4ffa9e60679a3ccbb252d775d529b3fc294781151a66` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `nichesCount_eq_numInvalid` | auxiliary lemma; cited by R3.2 | none | `8f4fa0c36343dd4e05f75789bdb36ace1ed4e2ccb73b5672285e018fbba4a6b7` | `052b47cb9b8df7478c893dfb22739dc763642e9054f824192757f18ad431331e` | 5 |
| `nv_affineLayout_eq_nicheLayoutK_affineTags` | R2.1 non-vacuity witness | `propext` | `bd1bfb10a1c1a93835d81ee1550867b5ac5437ef102b542998f28755b198f2d2` | `ba0e91e5d6defcd84141ba6a42f01ffd9fd04146cd124d6b862f1d3da9e03c87` | 26 |
| `nv_affineLayout_lawful_iff_span_lt_and_tagsDisjoint` | R2.2 non-vacuity witness | `propext` | `250c7741bc84511d3d90ae4924f1be5881f86c2cf87ceaf7034ad360cd7175b3` | `70b00ef4356e8f1c6ef7aa0a049bea855180576408e41756440c6fee5d1072e5` | 12 |
| `nv_classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint` | R2.3 non-vacuity witness | `propext` | `f5d027bdf05a16c8eeb7a7b2e04ccd8bb45d5213492f125ef8c94193c6c4a65b` | `91926b8351c55a5db4475a597fc00d541aef2a44ae407ffa6af1e28f830b6d6f` | 6 |
| `nv_compl_mem_iff_not_mem_of_size_lt` | R1.2 non-vacuity witness | `propext` | `d0bde7ee86e01b8f939d4a7826a3b6b58b29c4f8e4ab9d871896de4fed6f0236` | `742e6c7f64c3f4fea0e8eb84da4b9895341e2eb59656c09f31392abe8aa7db38` | 6 |
| `nv_exists_lawful_extEnum_intervalV` | R5.4 non-vacuity witness | `Classical.choice`, `Quot.sound`, `propext` | `7332921967d0f3e76bb728ccb417ab3702877a8bc3a76d41153c6969d77789b5` | `f1dc0e7270459c15bd5987883dcade3f39a5c3635786f462bd541cc1efc41738` | 19 |
| `nv_exists_tagsDisjoint_iff_span_succ_le_sub_size_of_isHull` | R3.1 non-vacuity witness | `Quot.sound`, `propext` | `81af399b18917bf4e8a962ae6a3bf4158327231402bf912cc951429e6667b4ab` | `fb742c39c52d89779d602af94cd69ff4e6577f74e5c93bab9ba7f97f369b0c20` | 10 |
| `nv_exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last` | R4.1 non-vacuity witness | `Quot.sound`, `propext` | `4a7da13cd7728a4d484542127d074dba5f153169c2da7dfbd49b9ccde75521f5` | `fb742c39c52d89779d602af94cd69ff4e6577f74e5c93bab9ba7f97f369b0c20` | 10 |
| `nv_extend_spec_of_size_lt` | R5.1 non-vacuity witness | `propext` | `cf75b1034c6e363550882420f415cebf2c622f440d99b0dc6abf86cacfbe49a2` | `742e6c7f64c3f4fea0e8eb84da4b9895341e2eb59656c09f31392abe8aa7db38` | 6 |
| `nv_genLayout_dec_isSome_iff_classify_of_span_lt` | R2.4 non-vacuity witness | `propext` | `f315e482d69db762ce65f5dad69819843af65c9fdef2c245dc8151320262becd` | `f9e1d8ca4870906a794f015461fc5591db74cf22cde55e6aaf457e8901395b02` | 5 |
| `nv_genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange` | R2.5 non-vacuity witness | `propext` | `3e5105777db1f77036a1a70acb1747a329724f4782547236660b7fab24d37267` | `005a9b0591988b79d583fc04de43d970945815146f9572adbea7a93a6f54e623` | 20 |
| `nv_levelsReserveNiches_iff_length_le_and_nest_size` | R5.3 non-vacuity witness | `propext` | `8f7533cbbf88a600f3f541ff6d410bb7e80ca6e158ec6ed6f20755166d32a520` | `5d799e2f98ec6180f7932bc6eaf71991108256b384d8a27c78d58172cf1e38b8` | 23 |
| `nv_mem_iff_offset_le_offset` | R1.1 non-vacuity witness | `propext` | `b0dbdceed53cbc6c9913a0c8262201ecea13b6b9c9b1385717c27902f5507986` | `680ffe66833a0664498711c840f879fade004e25df88c985a1c9447b32369263` | 6 |
| `nv_nicheLayout_adjNiche_lawful` | R5.2 non-vacuity witness | none | `ad02f5f99d0d8fbb96bc6e3eeb93c2c2ca3471d5d3fc6bf0dc45252eea1f2637` | `966b73c13ed4dbeaaa90d663a27c6edea97ba9f4541f5acde7d863ad1eb9da6a` | 7 |
| `nv_nichesCount_intervalV` | R3.3 non-vacuity witness | `propext` | `36f9b8e6042d1cd13f59a5a409b3a2d804b1dc4c3f37b7a8e5e1b405aa54ec68` | `a1aca57df6b6bc039ff625bc41c1f58ee0b1796ab59c99b4481c3533b12e080a` | 10 |
| `nv_not_exactFor_originTest_wrapSub_one_of_two_le` | R1.4 non-vacuity witness | none | `2df0ca1efac58552cd52e52d705cbad0e850420afa4c64d78a5a3502c08f8b25` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `nv_originTest_exactFor_iff_offset_le` | R1.3 non-vacuity witness | `propext` | `95064ca7d2814451bca50a815a8e254cfa69c9ad6e98f18cb9834983e89e5284` | `c11702fad047745d462aae6050640f3e5621f46f067d9c921c9c08caa31fcca5` | 8 |
| `nv_rotDecodeIdx_exact` | R4.2 non-vacuity witness | `propext` | `c09ae37c23924369c23774c67adc2c5c71db7cf56e01bc7a393ce579953f51fc` | `84a7508a2177c1f4c8a95110a239c800efb59e4eacc390748689b210ba2d0843` | 7 |
| `nv_run_erased_eq_some_of_run_operational_eq_some` | R6.2 non-vacuity witness | `propext` | `e8863a74b31543c7b29997854256f8793416c1017b06f3e0c5dcc6748d4114ee` | `f5e3af2fb60d09dcc95d7c26172be20d35a0afdb7947b68f9a454d0b35e33eb8` | 71 |
| `nv_run_fields_then_setDisc_readDisc_of_disjoint` | R6.4 non-vacuity witness | `propext` | `64bfe7fe18350557385d57bd42823a594c6f7337a7dbea9adc3cdda64c80cb5b` | `29253d77a66351340863b890e35ec6f52f427c2a9047a33dc96b327871dc2913` | 33 |
| `nv_run_write_setDisc_comm_of_disjointFromNiche` | R6.3 non-vacuity witness | `propext` | `23b84e9ebc60bc531979a738e7ad676f1feac018485ad90faf0c6cd988a10f58` | `4ffbbc0e85ce70b15c5f1569bb764bf7e0ed796310d54096bbc067c1c6f3551a` | 72 |
| `nv_setDisc_operational_untagged_isSome_iff` | R6.1 non-vacuity witness | `propext` | `95600aec32381d80810f727055ed13e967ea8120367c3a07c6010211f5c3f480` | `ed2dc8cf343cebd39980d8f1db0f9526b8dc349bc48d750bb2eb87350be55d60` | 21 |
| `nv_sub_size_le_nichesCount_and_eq_iff_of_covers` | R3.2 non-vacuity witness | `propext` | `5b73df47eb24c1b601cd4c3bb5aceb184e77eb21d885f7685ae92dc32958352d` | `00b25ccb12abbdb2ea1ee7aadecf2c3c44a06f548d0ba01301370f95aa646050` | 7 |
| `offset` | definition; cited by R1.1, R1.3 | none | `4d061938187e3ca2e5a7a16665a8b29c7741b562b0fc4028dfa389b428de2b8a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `offset_self` | auxiliary lemma | `Quot.sound`, `propext` | `5ed274b528a32ac437fec0a3c432f0c241eb95f9cc4bf5521a6cabf7680ea632` | `8bb20c61830b55dc8aea6bf731e38e73eeca9f59f9e3f8f4905d71aaf636abf9` | 1 |
| `offset_zero` | auxiliary lemma | `propext` | `717fb389ab5f35e058877b3122ae7b4af662f2ee5b4405db399f7a795f1174c1` | `fb6e2cc1a149caa5ff1ec393a0dbe9c9d722142cd71ac7cfabd320ce754c0fcf` | 2 |
| `originTest` | definition; cited by R1.3, R1.4 | none | `717e623321c1e06b7712995530c7716c577fdbaa11ba9d96b94ff5f25bc52eb7` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `pc_complTest_exactFor_fin8` | R1.4 positive control | none | `0d7fe8e72335623e4426269400c413729b47857f7aca4af14d39dfea0cd10691` | `08e295a49832cfddd38472e9135d921630cd6718bb6c20df022c3f99b389e404` | 13 |
| `pc_signed_and_unsigned_exact_elsewhere` | positive control; cited by R1.3 | `propext` | `1435d338d400bcac77d4f6f5ddab318eebfc3d26da1dc50841611a70f834a2bc` | `4e34e80e5484e19c05b99861fecf6bc25877b89ea0ff7a39c25f020c0336fed8` | 9 |
| `pc_subTest_exactFor_all_fin8` | R1.4 positive control | none | `333b63ba8b02e5b3a3054a1c897b055ae6c036c169bcdfd815ef4cb30fbafa82` | `36fa9cac093c36f7162a5dda5b1dd93eeadaa3f0941edd039aebde13adfadc48` | 8 |
| `pc_twoBranchTest_exactFor` | R1.4 positive control; cited by R1.3 | `Classical.choice`, `Quot.sound`, `propext` | `df91d160da72b1a8dbfec8ec9d7cbb04e33a7b9aecbdc8c461142304e312d355` | `e5c1eac0c78afb3e5fed625ceb8b861fa7410f632c1f8063c6378f4b41c3ec02` | 9 |
| `pos_of_fin` | auxiliary lemma; used in `wrapAdd`, `wrapSub`, `offset_zero` and 1 more | none | `2fd18aa5c91ffcb89441e215111ceb175221ac4fbe26794e7fe41a3fa08d558d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `readBytes` | definition; cited by R6.4 | `propext` | `ab66d4e8ed99213b936f7228e2f85b2eb9ae0462e89ec4c2e9f0cd7520f8dc45` | `4e4009f3018244abbd074c7f1ac53b9d93553e0ee198f3d5638915ffcfa1c197` | 1 |
| `rotDecodeIdx` | definition; cited by R4.2 | none | `2a1216e9f1d9dbe55b2e239ba23e2588c4ec6bd3d596f609edbd065d50df0e12` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `rotIdx` | definition; cited by R4.2 | none | `8a373c4799a9cd78fefaed91c0dce4a0fe1170aad36748a7d71c72c619c2a6a7` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `rotTag` | definition; cited by R4.2 | none | `fbee2c1ff3d477800e5e8627b0e8bfb6f7654f7b84c7f8b996e4c419e7baf685` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `rotTagsInvalid_iff_tagsDisjoint_sub_two` | auxiliary lemma; cited by R4.2 | `Quot.sound`, `propext` | `a72ce878d5ead3e30ae23ed826cbf2ae2fa0679116a4edf8113ece140ee74d08` | `1fec37b1f79f291d28bf532713e44bd2d2822c9199f124fd6c300a74c960fe7e` | 4 |
| `run` | definition; cited by R6.2, R6.3, R6.4 | `propext` | `766d9fdde366d66c8b50262146e0849d3175053e7f6e012e03f475a7b7d50df4` | `39a2c644a7cdb9abe01c694ec33575d7a4d2dc8ca0b2a5ed15f0e1cd2adb627e` | 16 |
| `setDisc` | definition; cited by R6.1 | `propext` | `174ff1ca4319f6b4dbf8ba1ee70d8c711617d51b6cc828e2c70edd12f250ac9c` | `3a8798fe6d2aec3ec4527c64c0531941097c824d324a27651fed096446960a2e` | 12 |
| `signedTestI8` | definition; cited by R1.3 | none | `640d7d800f2bdf5c90bfe424dd4f4bebe510cffa62719283a78c2ec85ad38006` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `signedTestI8_iff_originTest_128` | auxiliary lemma; cited by R1.3 | `Classical.choice`, `Quot.sound`, `propext` | `a41679a5725c96ca4f03d8de12db02739170a7529d661279776e740475656eb3` | `f329b567e78874e8708d14ce33cda9f60826fca9a861729f9ab8750dbbb78864` | 8 |
| `stepOp` | definition; used in `run` | `propext` | `416d0eabef28c90953c69747842cc204cdab8ea33c31624b0b50e7ee5740db40` | `39a2c644a7cdb9abe01c694ec33575d7a4d2dc8ca0b2a5ed15f0e1cd2adb627e` | 16 |
| `subTest` | definition; used in witness statements of R1.4; used in `subTest_iff_originTest_start`, `ex_tests`, `ex_exactFor_pos` | none | `cd8a8b1e81bf98582e6f1ee49d84e61b88bdd1449114288dda0ce066e94c837b` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `subTest_iff_originTest_start` | auxiliary lemma; cited by R1.4 | `Quot.sound`, `propext` | `fbff4d42418c7299bdb584009e870e0b51a293ac953f06248472f801b36cda5e` | `a6645205ed3af4bcfea40d18f6453b337dee5663f632b452984b755d8c323f35` | 7 |
| `sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull` | corollary; cited by R3.2 | `Classical.choice`, `Quot.sound`, `propext` | `2c784e4a3d45bde801e856d850606819b6601f1898fb3dd104a54ea1325d058f` | `668dea2e503f4b23d887d1ba4b339f280d7f8ee4c0b8b8fc4d0973843f4cd835` | 11 |
| `toI8` | definition; cited by R1.3 | none | `4568d097c34978f4de059cb52eb7ca147ba313a112bbf8d257cd8bc016e85c81` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `twoBranchTest` | definition; cited by R1.1, R1.3, R1.4, R3.1 | none | `717e623321c1e06b7712995530c7716c577fdbaa11ba9d96b94ff5f25bc52eb7` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `uninit3` | concrete fixture; used in witness statements of R6.1, R6.2, R6.3, R6.4; used in `ex_bytes`, `ex_run_write_oob`, `ex_setDisc` and 3 more | none | `180152f0f5278bc0edea720696e40f7976b12217b9da9d07b5ce95b41be22f7b` | `4e4009f3018244abbd074c7f1ac53b9d93553e0ee198f3d5638915ffcfa1c197` | 1 |
| `unsignedTest` | definition; used in `unsignedTest_iff_originTest_zero`, `ex_tests`, `ex_exactFor_neg` and 2 more | none | `cd8a8b1e81bf98582e6f1ee49d84e61b88bdd1449114288dda0ce066e94c837b` | `1fbd74cecc6b1e2beabf94be5fc9454b7bfe8cbf76eab0d62646c87bf4b89c73` | 2 |
| `unsignedTest_iff_originTest_zero` | auxiliary lemma; cited by R1.3 | `propext` | `9d91cadb50e34d1b9c4d073a1cb1a3edc1e7629e7ca2fe924c61ba7611d44282` | `2aaf91ffe93dd9ebd84b2f83a91e4351467658049d4221af683f955dd11f2d02` | 8 |
| `wrapAdd` | definition; used in `WrapInterval.compl`, `AffineNiche.tagOf`, `AffineNiche.tagInterval` and 6 more | none | `8d298e3a34dfe85d956ecd0ad0751b3c4d7dc7491cd2d5f6695fd1dea1361121` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `wrapSub` | definition; cited by R1.4 | none | `8d298e3a34dfe85d956ecd0ad0751b3c4d7dc7491cd2d5f6695fd1dea1361121` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 0 |
| `writeBytes` | definition; used in `OpLayout.writeNiche`, `stepOp`, `ex_bytes` | `propext` | `5062f51b9d09694442c27ee1f882a1667365058b821d791ad1becb98f8e137b3` | `4e4009f3018244abbd074c7f1ac53b9d93553e0ee198f3d5638915ffcfa1c197` | 1 |
| `writesOf` | definition; cited by R6.4 | none | `dc34c92224e2528e77cc54e5cce90027f9d7c38f6684dbe653a6e38026729154` | `8392120bb97cfbb953ad3c1101a4d062f2030d6d23799a9af79e0a9c20b937f1` | 4 |

Declaration names are relative to the namespace `Toy.WrapNiche`.

### Imported module provenance

`lean/Toy/WrapNiche/Imported/{Defs,Lemmas,Counting,Results}.lean` are copied from `google/zerocopy`, branch `reference`, directory `reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/`, published at commit `00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; the four upstream files are byte-identical at the later correction commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`. The namespace is renamed from `Toy.Niche` to `Toy.WrapNiche.Imported`; statements and proofs of the kept declarations are verbatim. SHA-256 of each file:

| File | Upstream file (both commits) | Local copy `lean/Toy/WrapNiche/Imported/` | Edits |
|---|---|---|---|
| `Defs.lean` | `91c672ae20c64317dd288cb83199123f3add4dc5818f8ed03a590a3eff94d886` | `22badca8b13ab4185d1e957699a2487e34a7c52a7c043c6f310f914b83fd17fa` | namespace; header comment |
| `Lemmas.lean` | `b3b977d1e5444ff7c72fc1bab2b4624eb93974f290c423a64bd6685357e751c0` | `3bde6245756ff241a37fa82161db15e7ad9fdf89ba1af9ea9b31fe6d4874cda5` | namespace; header comment |
| `Counting.lean` | `ef8273526a1df77512aca86f330684938898314d9d3d48a1fc1f3b935af2001f` | `104803b29205622ab72b9be415db978fb955c419d78ec03d9f74a3ee9a4a6f1d` | namespace; header comment |
| `Results.lean` | `1cc88a25e188cafaae35db8e9c8cf6c7399d5e6b4005d0465af9bf8032e182ab` | `4be15d18dcade42e5908943a80313e1c30742f2c0e90feb4e49e2569a7c7e72a` | namespace; header comment replacing the module docstring; only the cited theorems and their prerequisites kept |

### Primary sources

Observation date for every source: 2026-11-21. Quoted passages were compared with the fetched files at the pinned revisions on that date; each revision was resolved through the GitHub API.

- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard and Peter J. Stuckey, "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss", ACM Transactions on Programming Languages and Systems 37(1), Article 1, January 2015, DOI 10.1145/2651360; read in the authors' copy https://jorgenavas.github.io/papers/ACM-TOPLAS-wrapped.pdf (Section 3.1 with Definition 3.1, Section 3.2, and Section 3.3 with Fig. 5); formulas paraphrased. Cited by R1.1-R1.4, R3.1-R3.3, R5.1.
- Henry S. Warren, Jr., Hacker's Delight, 2nd edition, Addison-Wesley, 2012, Section 4-1 "Checking Bounds of Integers"; title, edition and section confirmed by search, not quoted. Cited by R1.1.
- rust-lang/rust, commit `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` (committed 2026-08-05): `compiler/rustc_abi/src/wrapping_range.rs:8-16`, `55-63`, `147-195`; `compiler/rustc_abi/src/lib.rs:2002-2033` (`TagEncoding::Niche` documentation), `2075-2087` (`Niche::reserve`); `compiler/rustc_abi/src/layout.rs:636-643` (read for orientation; no claim relies on it), `652-680`; `compiler/rustc_ty_utils/src/layout/invariant.rs:300-323`; `compiler/rustc_const_eval/src/interpret/discriminant.rs:15-44`, `147-160`, `187-200`, `210-215`, `246-257`, `290-297`; `compiler/rustc_codegen_ssa/src/mir/place.rs:254-273`, `499-527`; `compiler/rustc_middle/src/mir/interpret/error.rs:426-427`; `compiler/rustc_middle/src/mir/syntax.rs:357-361`. Quoted under the cards' Prior art and in Applicability.
- rust-lang/reference, commit `956d1bd03d2a8934fc5041ecb04b33e55159c655`: `src/type-layout.md:174-178`, `188-189`, `194-195`, `226-227` (quoted in Applicability).
- minirust/minirust, commit `063d784186d3252bee242217f218223205c0b568`: `spec/lang/step/statements.md:61-85`, `spec/lang/types.md:101-126`. Cited by R6.2-R6.4.
- llvm/llvm-project, tag `llvmorg-21.1.0`, commit `3623fe661ae35c6c80ac221f14d85be76aa870f1`: `llvm/docs/LangRef.rst:7334-7371`; `llvm/lib/IR/ConstantRange.cpp:517-524`, `1939-1945`. Cited by R1.1-R1.4.
- The imported corpus package (see Imported module provenance), whose theorems `nicheLayoutK_lawful_iff_injective_and_isNiche`, `le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches`, `nicheLayout_lawful_iff_isNiche` and `opt_opt_nonZero_no_decEnc_layout_in_payload_size` are quoted under Imported declarations. Cited by R2.1, R2.2, R2.5, R3.1, R3.2, R5.2-R5.4.

Public tracker items cited in card prose (not subjects, not normative): https://github.com/rust-lang/rust/pull/133681 (merged on 2024-12-04, merge commit `6e87eb58ede97cce4bd1e392694f88a2a2936e84`; R2.3-R2.5), https://github.com/rust-lang/rust/issues/117238 (an issue, open when checked on 2026-11-21; R4.1, R4.2) and https://github.com/rust-lang/rust/pull/131684 (closed without being merged on 2024-12-10, an unmerged proposal; R4.2).

Novelty search (2026-11-21): a web search for mechanized Coq, Lean or Isabelle treatments of Rust enum niche layouts, wrapped intervals and discriminant decoding; its scope and outcome are recorded verbatim in the Prior art of R2.1-R2.3, R3.1, R4.1 and R4.2.

## Revalidation

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. The Lean project has no dependencies (no Mathlib, no `[[require]]`).

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source of the package for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) runs a generated Lean program that calls `Lean.collectAxioms` on every declaration of the library `Toy` and fails if any axiom other than `propext`, `Classical.choice`, `Quot.sound` occurs; and (4) for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, recomputes the statement hash and the closure hash described under Evidence (the SHA-256 of `repr` of the type, and the SHA-256 of the sorted `name : repr(type)` lines, with ` := repr(value)` for non-theorems, of the package-local constants reachable from the statement) and compares them with `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 iff every check passes.

Manual build and axiom check, run from the package directory (the file `lean/AxiomAudit.lean` is not part of the library target; it contains one `#print axioms` command for each of the hashed declarations):

```sh
cd lean
lake build
lake env lean AxiomAudit.lean
```

Each reported axiom list must be a subset of `propext`, `Classical.choice` and `Quot.sound` (or empty).

Spot check of a quoted external source, for example the membership test compared with `WrapInterval.Mem` (the printed lines must match the quotation in R1.1):

```sh
python3 -c "import urllib.request as u; L = u.urlopen('https://raw.githubusercontent.com/rust-lang/rust/26bfbf28f5f79dff333ce5a232f131b496ec9cfe/compiler/rustc_abi/src/wrapping_range.rs').read().decode().splitlines(); print(chr(10).join(L[54:63]))"
```

A passing run establishes that the recorded statements still build and kernel-check with the recorded axioms under the pinned toolchain; it re-establishes nothing about rustc, its interpreter, MiniRust or LLVM. Under a different toolchain the statement hashes may change even when the mathematics does not (they hash Lean's `repr` of terms); in that case compare the statements in `lean/Toy/WrapNiche/` with the ones quoted under Findings by reading them. The modeling-bridge claims and the quoted external sources are not revalidated by these commands: to check them against a newer revision of a source, re-fetch the cited file at that revision and compare the cited line ranges with the quotations.
