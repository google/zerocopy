# Independent generated-output delta review

**PASS for the parent's next full raw repaired-model build gate.** Independent comparison found no unapproved runtime equation, string, import, configuration or file-path change. The previously reviewed termination change remains the only residual after a concrete capture-safe fresh-name bijection. This is a source/output review, not successful compilation or theorem checking.

No generator/compiler/prover, Docker, network, install, Git, cleanup or publication action ran. Ordinary source/hash/text inspection ran; only this review was written. Both generated trees remain unchanged. The compiler and later proof must consume the **raw** repaired files, never review-renamed copies.

## Independent comparison

Inputs are original `work/execution/sail-runtime/generated-project` and repaired `termination-generated-project`. Both have178 files and exactly the same relative path set. Independently checking actual file byte lengths and SHA256 values against each respective census gave178 matches and zero errors for each tree. The original census's `generated/Lean_RV64D/` prefix was stripped only to locate corresponding copied paths; repaired census entries already use project-relative paths.

I independently enumerated every concrete identifier token matching k_exNUMBER_ in corresponding files, in source order; token counts agreed per file. For every aligned occurrence I required one consistent original→repaired name and the inverse to be unique. This independently derived163-entry mapping across185 occurrences, with no inconsistent or noninjective assignment. Only after deriving it did I compare with parent's recorded mapping; the dictionaries are identical. There are no unmapped unchanged k_ex identifiers anywhere in either project that could collide with a mapped target.

I then substituted the **specific mapped identifier for each occurrence**, simultaneously in memory, and compared complete file bytes. This is not replacing all identifiers by a placeholder: distinct names remain distinct, repeated occurrences retain their individual identity, and injectivity is enforced globally. Of32 files differing in raw bytes,31 become byte-identical; only `LeanRV64D/PlatformConfig.lean` retains a difference. A second raw-byte comparison confirmed this result without text newline normalization. File content outside the specific mapped token spans is preserved exactly, including string contents, imports and all punctuation.

## Scope and capture audit

A separate source lexical scan tracked nested /- -/ comments, line comments and escaped strings. Of185 mapped occurrences,175 are in comments and10 are in code; **zero** are in runtime string literals or quoted names. The10 code occurrences are these function-parameter type dimensions:

| File/line | Function | Original dimension | Repaired dimension |
| --- | --- | --- | --- |
| Sign.lean:232 | float_is_positive | k_ex1829740_ | k_ex1829761_ |
| Sign.lean:236 | float_is_negative | k_ex1829742_ | k_ex1829763_ |
| Inf.lean:232 | float_is_inf | k_ex1829738_ | k_ex1829759_ |
| Classify.lean:267 | float_classify | k_ex1829830_ | k_ex1829851_ |
| Normal.lean:232 | float_is_normal | k_ex1829746_ | k_ex1829767_ |
| Normal.lean:237 | float_is_subnormal | k_ex1829748_ | k_ex1829769_ |
| Nan.lean:232 | float_is_nan | k_ex1829732_ | k_ex1829753_ |
| Nan.lean:237 | float_is_snan | k_ex1829734_ | k_ex1829755_ |
| Nan.lean:242 | float_is_qnan | k_ex1829736_ | k_ex1829757_ |
| Zero.lean:232 | float_is_zero | k_ex1829744_ | k_ex1829765_ |

These are independent auto-implicit Nat dimensions introduced by BitVec's type parameter, not public definition names or architecture register identities. Each function has one such code dimension occurrence and its body does not introduce/refer to another k_ex variable. No mapped target captures an existing binder/free variable in any of these scopes. Names may overlap other original global fresh-name spellings, which is harmless under simultaneous bijection and disjoint local scopes; sequential search-and-replace would not be a valid comparison method. The remaining175 occurrences are generated quantifier documentation, including multiline comments; line-based comment filtering would misclassify86 of them. The lexical classification above accounts for those explicitly.

## Only approved residual

Independent residual matches parent's `termination-generated-residual.diff` in content:

- currentlyEnabled_measure: Zfinx9→10, Zdinx10→11, Zhinx10→11, Zhinxmin11→12;
- check_stateen_bit termination7→8;
- get_mstateen new termination7;
- is_zfinx_enabled_by_stateen termination8→9;
- legalize_mstateen0 new termination5;
- read_mstateen0 new termination6.

No other token, equation or effect-order change remains. In particular, legalization retains hartSupports(Zfinx), not currentlyEnabled(Zfinx), and read_mstateen0 retains its two real register reads. The auxiliary numeric helper's four outputs change as already reviewed; do not call those outputs identical. Changed well-founded proof/unfolding strategy is still possible. The source-ranking audit and this byte delta are sufficient to approve the next full-model checking attempt, not substitutes for it.

Parent's generation result0/160.688861 seconds/maxRSS500848KiB and the original result are distinct preserved runs. This review independently validates the copied generated bytes, not process timing. Original strict 'only one raw file differs' gate correctly stopped before compilation; recognizing capture-safe fresh binder renaming explains the32-file delta rather than excusing an unknown semantic difference. A full Lean check may still reject and must be preserved if it does.

## Evidence identities

SHA256:

- generation-census.json: `210326a9318afd1952580fcdcdadd14bd0b4fe9ef27c2becd09b8c2bc0e108ea`
- termination-generation-census.json: `6c25554e3bbb85130ecc4c78a16238933dcfbce5e6023fa3f28d51b7a8153aec`
- termination-fresh-name-map.json: `306ab8ab0d2789b591cc9ef24f267785cae1eab24ac74392984e09bdef494940`
- termination-generated.diff: `cd209a58be2f51b2c7cadd48938bf967edbb274a21086b5723d71aad1911bfc6`
- termination-generated-residual.diff: `e2eeb1b35b55fed5f1f087bd311983bb3fe87c47c9ef23380f1cacaa348f6c35`

All five are under `work/execution/sail-runtime`. Exact source patch identity and full134-edge rank review are in adjacent scratch TERMINATION-PATCH-REVIEW.md. No compiler inputs were renamed or normalized during review.
