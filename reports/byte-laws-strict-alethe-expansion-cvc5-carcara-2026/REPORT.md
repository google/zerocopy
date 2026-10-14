# Strict certificates for four fixed guarded byte laws

## Summary

All four original finite byte-law roots now have complete certificates accepted
by the unchanged native Carcara checker: IntoBytes observation, byte writing,
Boolean validation and two-element array validation. The primary route is actual
cvc5 proof generation followed by an untrusted local expansion of five exported
rewrite names. Carcara checks every replacement inference against the unchanged
whole-law root; the input domains, assumptions and target conjunctions are not
weakened or projected.

This closes the earlier export compatibility boundary for these exact examples.
It does not make the raw cvc5 exports acceptable: three whole-law exports still
fail before translation. Ten rejection controls and five fresh SAT-to-Lean
refutations retain the initializedness, alias/frame, validity, stability,
array-coverage and full-domain distinctions.

## Applicability

The experiment uses cvc5 1.4.2 at
`282d5e0c84baf49c780704c532f87ba66d8b513d`, Carcara 1.1.0 at
`20bf49c5ce31089ac83118574c888669355aaae1`, and Lean 4.34.1 at
`5045d0056413266e57c625dcd7c365b10e377c52`, on Darwin arm64. Exact executable,
Lean shared-library and `Init.olean` hashes are in `tool-locks.json`. The Lean
launcher hash alone is not a version identity.

The fixed semantic fixture is the earlier owned `ByteLaws.lean`, unchanged at
SHA256 `275e5f09043bc8091f3b962aada7e6a1b2d24876d9aeca0b323d5e38ac983acc`.
Bytes range over all `Fin 256`; addresses are the two Boolean indices. Byte
values, initializedness, read authority and write authority are separate fields.
The corresponding SMT roots retain the original `QF_AUFLIA` integer/array
encoding and every original assertion. Arbitrary SMT array entries outside
indices 0 and 1 are unobserved by the quoted fixture.

The roots were checked against the independently recorded earlier predicate map
before copying. `root-locks.json` binds exact bytes; `predicate-map.json` states
the carrier and predicate mapping. All support is report-owned source or captured
execution evidence. No old Lean 4.31 or retired extraction runtime is needed.

## Findings

### F1. The independently fixed whole-law subjects are unchanged

Basis: source + execution.

| Original root | SHA256 | Required consequence |
| --- | --- | --- |
| `roots/into_bytes.smt2` | `3f775009794160d1c56006f39c8cf8fd687cd438723e799204b1a37922c784e9` | All four initialization/read flags required by observation hold. The existing `observe_success_iff` connects these flags to successful byte-pair observation. |
| `roots/byte_write.smt2` | `6046a6c9cd3101bd01b1ca67afa39ec57d5daaaaaa2c9f2aa826298827258e70` | At the write index, value becomes replacement and initialization becomes true; at the distinct frame index, both value and initializedness remain unchanged. Write authority and disjointness remain asserted. |
| `roots/bool_validate.smt2` | `e85da6710cea19f811a8e431b34bec7b1125f445d8ba5e26667f5b92b56292d2` | Under snapshot/current readiness, equality and snapshot validity, current readiness and `not(current[0] >= 2)` hold. |
| `roots/array_validate.smt2` | `746f9d38906c183189a7195f1248f3f97a387dc001cfc6edd207f9058766cdb2` | Under readiness, equality and validity at both indices, all current readiness flags and validity at both indices hold. |

Every root includes the original full byte domain `0 <= b < 256`, replacement
domain and two-address domains. A proof need not use every asserted premise;
unused premises are not removed from the consumer's root. The write certificate
refutes the negation of its complete four-conjunct target, including the outside
initialization frame. It is not the previously accepted byte-frame projection.

The Lean definitions additionally include the guarded `writeByte` result and
`observe` result. Their relation to pure SMT store/read terms remains the explicit
finite predicate map and the existing mapping lemmas, not an assertion that the
Alethe checker interprets Rust operations.

### F2. Five local rule expansions repair the actual cvc5 exports

Basis: source + execution + derived.

Fresh cvc5 executions use
`--proof-format-mode=alethe --proof-granularity=dsl-rewrite-strict` on the exact
roots. They return UNSAT and proof text. Raw exports pass Carcara for IntoBytes
and fail for the other three whole laws because named `rare_rewrite` rules are
not found. These diagnostic captures remain in `final-run/*.raw.check.stderr`.
This is a concrete export-rule compatibility result, not absence of the
underlying array, Boolean or arithmetic reasoning.

`translate.py` replaces only these observed rewrite steps:

| Exported name | Checked replacement | Precise reason |
| --- | --- | --- |
| `array-read-over-write` | `arrays_idx` | The original conclusion is exactly `select(store A i v, i) = v`. |
| `eq-refl` | `eq_simplify` | The original conclusion is `(t = t) = true`. |
| `eq-symm` | `eq_symmetric` | The original conclusion is `(t = u) = (u = t)`. |
| `bool-double-not-elim` | `not_simplify` | The original conclusion removes a double negation. |
| `arith-elim-lt` | Four helper steps using `comp_simplify`, `cong`, `symm`, then the original step using `trans` | `< a b` and `not(>= a b)` are each proved equal to `not(<= b a)`. |

The arithmetic expansion is deliberately explicit. Carcara's comparison
simplifier produces `not(<= b a)` from `< a b` and `<= b a` from `>= a b`;
congruence under `not`, symmetry and transitivity produce the original exact
conclusion. No arithmetic equality is asserted as a new assumption.

The translator preserves every original assumption line, every original step
identifier/conclusion and all non-rewrite lines in order. The textual diagnostic
`verify_preservation.py` checks those facts independently of the translator;
`translation-preservation.json` records all 15 final comparisons. Boolean and
array proofs each gain eight native helper steps; other original conclusions
remain intact. Unknown rewrite names or unexamined syntax/arity cause an explicit
producer error. `producer-boundary-control.json` records the unknown-name check.

The translator is untrusted. Its output is not admitted on its own evidence.
Actual native Carcara checks the resulting proof against the original SMT root,
including the proof's global assumptions and the final empty clause. Carcara is
not patched; no custom rules, ignored rules, allowed-rule lists or holes are used.

### F3. All four complete translated certificates pass strict acceptance

Basis: execution.

Here “strict acceptance” means successful native `carcara --no-color check
PROOF ROOT` with exit status zero and stdout bytes exactly `valid\n`. It does not
mean Carcara's separate elaborated-granularity mode was selected. The native
rules and ordinary checking mode are pinned and explicit.

| Whole-law root | Raw cvc5 certificate | Locally expanded cvc5 certificate | Final samples |
| --- | --- | --- | --- |
| IntoBytes | `valid`, exit 0 | `valid`, exit 0 | 3/3 |
| Byte writing, all four conjuncts | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |
| Boolean validation | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |
| Array validation, both indices | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |

The narrowed local-domain claim also has a complete expanded proof, accepted in
3/3 samples. It is kept as a negative consumer-binding control, not reported as
evidence for the full-domain false claim. An independent bounded reconstruction
of each of these five roots also passes once; this is diagnostic evidence for
the native rule interface. It is not substituted for the primary translated
cvc5 certificate route in the table.

`final-run/results.json` binds each accepted proof hash, root hash, verdict,
exit status, rewrite count and phase capture. Successful SMT certificates are
not replaced by Lean proofs in these results.

### F4. False laws, missing premises and misbound proofs remain rejected

Basis: execution.

The consumer also executes these ten negative checks:

| Offered proof or corruption | Consumer result |
| --- | --- |
| IntoBytes proof attached to root missing initialization at index 0 | `invalid`, exit 1 |
| Whole write proof attached to root allowing frame aliasing | `invalid`, exit 1 |
| Boolean proof attached to widened `< 3` guard, allowing byte 2 | `invalid`, exit 1 |
| Boolean proof attached to root lacking snapshot/current stability | `invalid`, exit 1 |
| Array proof attached to root lacking index-1 snapshot validity | `invalid`, exit 1 |
| Valid narrowed-domain proof attached to full-domain widened-guard root | `invalid`, exit 1 |
| A native array step replaced by `hole` | `holey`, exit 0; consumer rejects |
| Array step's conclusion corrupted to `false` | `invalid`, exit 1 |
| Unmatched global assumption `false` inserted | `invalid`, exit 1 |
| Old outside-byte-frame-only proof attached to whole write root | `invalid`, exit 1 |

The independent root-identity comparison also rejects the narrowed root's hash
as the expected full-domain root. These checks distinguish semantic root
identity from the fact that some other SMT problem has a valid proof.

Fresh cvc5 queries for the five incorrect laws return SAT. The owned finite
interpreter evaluates every exact assertion true under each returned scalar/
selected-array valuation: respectively 11, 9, 14, 13 and 19 assertions. It does
not fill missing model entries or accept unknown syntax. The same literal
valuations are emitted to `final-run/SolverWitnesses.lean`; Lean 4.34.1 checks
all five refutations. Each reports only `propext`; the shared fixture's mapping
helpers additionally use the recorded standard `Classical.choice`/`Quot.sound`
premises. No `sorryAx` is reported and both Lean processes exit zero with empty
stderr. These refutations confirm finite witnesses; they do not verify the
native Carcara implementation.

No unexpected panic/assertion, timeout or operational failure occurred. Explicit
raw-proof rejection is retained as rejection, not classified as a tool crash or
blanket semantic unsupportedness.

### F5. Small separated measurements establish feasibility, not a ranking

Basis: execution.

The final replay takes three samples per fixed root, sequentially, without
installing or building tools. Process-inclusive cvc5 proof generation,
in-process translation excluding output-file writing, and process-inclusive
Carcara checking are recorded separately. The complete expanded proofs have
834 bytes (IntoBytes), 4,280 bytes (write), 11,684 bytes (Boolean) and 11,953 bytes
(array). On this run, whole-law cvc5 generation ranges from 10.803 to 18.745 ms,
translation from 0.047 to 0.565 ms, and checking from 3.986 to 5.469 ms.

These tiny fixed workloads, process startup, filesystem caches and host
scheduling do not support a cross-tool performance ranking. New source-creation
cost is not measured here: independently fixed root files are reused. Earlier
direct/reflected Lean measurements remain separate evidence. This wave closes
certificate acceptance, not named Rust-verifier feature parity.

## Boundaries

- **Established for this configuration:** exact fixed roots, all four complete
  translated cvc5 certificates, the local narrowed-domain certificate, ten
  negative checks and five finite countermodels/refutations.
- **Known not to apply:** the raw unexpanded cvc5 exports for the three named
  laws are not strict-valid at the pinned checker. The narrowed claim and frame
  projection do not certify the full-domain/whole-law consumer roots.
- **Not examined:** general cvc5 export translation, other rewrite names,
  arbitrary SMT theories, large proof scalability, other host/tool pins, named
  Rust-verifier end-to-end integration or general padded/dynamically sized Rust
  representations. Producer errors outside the observed rewrite vocabulary are
  not evidence that native Carcara cannot prove those statements by another
  derivation.
- **Explicit trusted frontier:** root/predicate selection, the owned quotation
  and literal I/O, SMT integer/array meaning, native Carcara and its runtime,
  the selected Lean kernel/runtime for the separate finite checks, and the
  Rust-to-finite-model correspondence. Root SHA checks are cooperative filesystem
  checks, not a security boundary against malicious same-user replacement.
- **No broader Rust claim:** finite permission flags model resource premises;
  they do not establish physical provenance, lifetime, aliasing or atomicity.
  Actual zerocopy source, compiler/front-end correctness and arbitrary safe-client
  closure remain the existing independently stated semantic arrows.

The remaining work for this bounded R095 architecture case is review/integration,
not an unperformed four-law experiment. Generalizing the translator or attaching
these roots to actual library implementations is future engineering with new
semantic obligations; successful local expansion alone does not discharge them.

## Evidence

- Owned primary fixtures: `ByteLaws.lean`, `roots/*.smt2`, `root-locks.json`,
  `predicate-map.json`, `projection-only.alethe` and `tool-locks.json`.
- Owned untrusted producers: `translate.py`, `reconstruct.py`; the latter is a
  diagnostic alternate producer only. `countermodels.py` supports the separate
  finite witness check. `replay.py` pins tools and root identities and captures
  exact stdout/stderr/status. `verify_preservation.py` is a text-identity check.
- Final execution: `final-run/` contains raw/expanded proofs, complete phase
  logs, negative inputs/verdicts, solver valuations and Lean source/logs;
  `final-run/results.json` is the result index. `.olean` is excluded from
  publication selection; it is reproducible from the retained source.
- Carcara primary source at the exact revision: [array rules](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/arrays.rs),
  [comparison/Boolean simplification](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/simplification.rs),
  [symmetry and native extras](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/extras.rs),
  [congruence](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/congruence.rs)
  and [assumption checking](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/mod.rs).
  `upstream-source-identity.json` records examined paths, symbols and file hashes;
  upstream source is not mirrored in this package.

The authoritative earlier observations remain valid for their recorded raw
exports. This supplement adds successful checked local expansions rather than
erasing those failures or implying a newer upstream release fixed them.

## Revalidation

Select the exact recorded tools explicitly, choose a fresh output directory, and
run from this package:

```sh
python3 -B replay.py --cvc5 "$CVC5" --carcara "$CARCARA" --lean "$LEAN" --output "$OUT" --samples 3
```

All three tool arguments and the output argument are mandatory; there are no
personal absolute defaults or retired-runtime fallbacks. `--samples 1` provides
the same whole-law and control coverage with fewer timing samples. Hash mismatch
fails before subprocess consumption. Changing tool pins requires deliberate
review of identities, native rule definitions and acceptance behavior, not
silently relaxing the lock.

For a single proof, run the native checker against its exact locked root. For a
translation audit, run `verify_preservation.py --original RAW --translated
EXPANDED` and inspect the local rule replacements. Text preservation is
diagnostic; exact native `valid\n` plus exit zero remains mandatory. Keep raw
failures and holey/invalid controls. Do not admit a changed root or a selected
projection as if it were the original whole law.

*Authored by an AI agent acting on joshlf's behalf.*
