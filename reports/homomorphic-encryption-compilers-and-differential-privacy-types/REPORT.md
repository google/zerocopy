# Homomorphic encryption compilers and differential-privacy types: noise, levels, slots and sensitivity as static resources, and where finite arithmetic breaks them

## Summary

Fully homomorphic encryption (FHE) compilers and differential-privacy (DP)
type systems solve the same shape of problem: a *graded resource* that the
programmer cannot observe at run time must be bounded statically, and the
bound is spent at a *release boundary* (decryption; publication of a noisy
answer).

- **FHE.** Three resources are invisible in library APIs and are what a
  compiler manages: the *noise budget* (spent mostly per multiplicative
  level), the CKKS *scale* (which must match on additions), and the *slot
  layout* (only a small group of slot permutations is cheap). A toy BFV
  model run for this report spends 0.2 bits of budget on one addition, 8.4
  bits on 4096 additions, and 10–12 bits on every multiplicative level when
  ciphertexts are relinearized; the eleventh squaring exhausts a 116-bit
  budget and decryption then returns a well-formed, wrong plaintext without
  any error. The same model shows that of the 16! permutations of 16 slots
  exactly 16 are single ring automorphisms, and that applying one to a
  ciphertext changes the key under which it decrypts.
- **Compilers differ in who computes the bound and what they promise.** EVA
  tracks integer log-scales and levels and has no noise estimator at all.
  HEIR runs a dataflow noise analysis under a selectable model and states in
  its own documentation that there is "no guarantee that they are correct or
  secure". Concrete optimizes TFHE parameters for a *user-chosen failure
  probability* (default 1/100000 for the whole circuit) and infers integer
  bit-widths from sample inputs. Coyote searches for a vectorization that
  minimizes rotations and blends.
- **Decryption is a release.** SEAL's own documentation warns that the noise
  budget "depends on the secret key" and "must not be propagated across a
  trust boundary"; Concrete's parameters assume decrypted results are never
  shared (IND-CPA only); TFHE-rs sets failure probability ≤ 2⁻¹²⁸ by default
  specifically for the IND-CPA-D model; OpenFHE's CKKS mitigation adds
  Gaussian flooding noise at decryption, the kind of repair that Li,
  Micciancio, Schultz and Sorrell analyse as post-processing decryption with
  a differential-privacy mechanism.
- **DP type systems** (Fuzz, DFuzz, and their successors) make sensitivity a
  type: `!_r τ ⊸ σ` is an r-Lipschitz function and a 1-sensitive function
  into the probability monad *is* an ε-DP mechanism. Their soundness theorems
  are stated over real numbers and mathematical probability distributions.
- **Executed arithmetic is not that model.** For the textbook binary64
  Laplace mechanism, 60–67% of outputs produced for one database are
  *impossible* for a neighbouring database (20000 samples per configuration,
  with exact support-membership tests). Exact discrete samplers remove the
  defect but consume a data-dependent number of random draws (5 to 52 in the
  run reported here, increasing with the magnitude of the noise). A bounded
  sum of single-precision values realises a sensitivity of 1.25 where the
  idealised analysis says 1.

## Applicability

The subjects are examined as a comparison across two literatures that share
one structure; no claim is made about combining them in one system.

| Group | Subjects (identities in `REPORT.json`) | How examined |
|---|---|---|
| FHE compilers | `google/heir` @ `372c088c9c4456f56ade7151058bbb900394d21b`; `microsoft/EVA` @ `7ea9d34b0380c25c03fe529fe9a755a6477144ce`; `raghav198/coyote` @ `d0d6d43a39be0be91709168b86b9cee8c60b4946`; `zama-ai/concrete` @ `ecb729bb0a6d516c7742593b66e1db11122f0db9`; papers for EVA (PLDI 2020), Porcupine (PLDI 2021), Coyote (ASPLOS 2023), HEIR (arXiv 2508.11095v1) | source and documentation at the pinned revisions; paper text or abstract |
| FHE libraries | `microsoft/SEAL` @ `ce53aa40969364f79599009bc8882f71fce0c13d` (4.7.2); `zama-ai/tfhe-rs` @ `fbc8b20de2bbf2f0e1582451d6399dec1bc45685` (1.9.0); `openfheorg/openfhe-development` @ `b59e1f291965f14fbee5172cd83a20f5b856204f` | specific documentation files only |
| DP type systems | Fuzz (ICFP 2010); DFuzz (POPL 2013) and `ejgallego/dfuzz` @ `09b408e4f917cdd6945bdc20b7dd325ff80e5843`; contextual linear types (TOPLAS 2023) | paper text (Fuzz, DFuzz); type-checker repository; bibliographic record and abstract-level description only for the TOPLAS paper |
| DP numerics | Mironov (CCS 2012); Canonne–Kamath–Steinke (arXiv 2004.00010v6) and its reference sampler `IBM/discrete-gaussian-differential-privacy` @ `cb190d2a990a78eff6e21159203bc888e095f01b`; Casacuberta et al. (arXiv 2207.10635v2); `opendp/opendp` @ `9e5d8b039cd573ea5b8d80ce8a7dff975d5c32ad`; `google/differential-privacy` @ `29ffc2a414b199ff62c040cf60c0f55599c7da22`; `leanprover/SampCert` @ `a2c53bb5ff790e729e252958060699b7eff898b9` | paper text or abstract; source; execution of the pinned reference sampler |

Scope conditions:

- **No FHE library or compiler was built or run.** The FHE execution
  evidence is a deliberately tiny pure-Python BFV model (ring degree 16,
  plaintext modulus 257, ciphertext modulus 2¹²⁸, symmetric-key, schoolbook
  arithmetic). It demonstrates structure and orders of magnitude *for those
  parameters*; absolute bit counts do not transfer to production parameter
  sets, which use ring degrees of 2¹²–2¹⁶, RNS moduli and different
  relinearization.
- **Floating-point evidence is platform-specific in its digits.** The
  Laplace experiment depends on the platform's `log`; it was run with
  CPython 3.13.15 on Linux x86_64 with glibc 2.43. Percentages will differ
  slightly elsewhere; the existence of unreachable outputs does not depend
  on the platform.
- Compiler statements describe the pinned heads. HEIR and TFHE-rs are under
  active development (head commits dated 2026-11-18); EVA's head is from
  2021 and targets SEAL 3.6.
- **Venue disambiguation.** *Coyote: A Compiler for Vectorizing Encrypted
  Arithmetic Circuits* (Malik, Sheth, Kulkarni) appeared at ASPLOS 2023. The
  PLDI 2024 FHE tensor compiler with automatic data packing (Krastev,
  Samardzic, et al.) is a different system, Fhelipe, on which HEIR's layout
  optimizer is based; it is not examined here.

## Findings

### 1. The statically managed FHE resources

#### 1.1 Noise budget: definition and consumption

Basis: source (`microsoft/SEAL`, `native/src/seal/decryptor.h`, documentation of `invariant_noise_budget`).

> The invariant noise polynomial of a ciphertext is a rational coefficient
> polynomial, such that a ciphertext decrypts correctly as long as the
> coefficients of the invariant noise polynomial are of absolute value less
> than 1/2. [...] If v denotes the invariant noise, we define the invariant
> noise budget as -log2(2v).

Basis: execution (toy BFV; source and command under Evidence, `toy_bfv_noise_and_slots_probe.py`, default seed).

```text
== Part A: invariant noise budget (toy BFV, n=16, t=257, q=2^128) ==
fresh ciphertext:     budget =  116.2 bits, decrypts correctly: True
after    1 additions: budget =  116.0 bits (consumed  0.2), correct: True
after   64 additions: budget =  112.7 bits (consumed  3.5), correct: True
after 4096 additions: budget =  107.8 bits (consumed  8.4), correct: True
repeated squaring WITH relinearization (base 2^4, 32 digits):
  depth 1: budget =   105.5 bits (consumed  10.7), components =  2, correct: True , key-holder estimate = 105.5
  depth 2: budget =    94.1 bits (consumed  11.4), components =  2, correct: True , key-holder estimate =  94.1
  depth 3: budget =    82.5 bits (consumed  11.5), components =  2, correct: True , key-holder estimate =  82.5
  depth 4: budget =    71.2 bits (consumed  11.4), components =  2, correct: True , key-holder estimate =  71.2
  depth 5: budget =    60.5 bits (consumed  10.6), components =  2, correct: True , key-holder estimate =  60.5
  depth 6: budget =    50.2 bits (consumed  10.4), components =  2, correct: True , key-holder estimate =  50.2
  depth 7: budget =    38.5 bits (consumed  11.7), components =  2, correct: True , key-holder estimate =  38.5
  depth 8: budget =    26.7 bits (consumed  11.8), components =  2, correct: True , key-holder estimate =  26.7
  depth 9: budget =    16.7 bits (consumed  10.0), components =  2, correct: True , key-holder estimate =  16.7
  depth 10: budget =     5.3 bits (consumed  11.4), components =  2, correct: True , key-holder estimate =   5.3
  depth 11: budget =    -5.1 bits (consumed  10.5), components =  2, correct: False, key-holder estimate =   0.1
    -> decrypt returned normally; result is a well-formed plaintext: True; coefficients that differ from the true product: 15/16
repeated squaring WITHOUT relinearization:
  depth 1: budget =   105.4 bits (consumed  10.8), components =  3, correct: True , key-holder estimate = 105.4
  depth 2: budget =    92.1 bits (consumed  13.4), components =  5, correct: True , key-holder estimate =  92.1
  depth 3: budget =    74.7 bits (consumed  17.3), components =  9, correct: True , key-holder estimate =  74.7
  depth 4: budget =    46.1 bits (consumed  28.7), components = 17, correct: True , key-holder estimate =  46.1
  depth 5: budget =    -3.0 bits (consumed  49.1), components = 33, correct: False, key-holder estimate =   0.1
    -> decrypt returned normally; result is a well-formed plaintext: True; coefficients that differ from the true product: 15/16
== Part B: plaintext SIMD slots of Z_257[x]/(x^16+1) ==
primitive 32nd root of unity mod 257: zeta = 136; slot exponents row0=[1, 3, 9, 27, 17, 19, 25, 11] row1=[31, 29, 23, 5, 15, 13, 7, 21]
encode/decode round trip: True
ring product == slot-wise product: True
ring sum     == slot-wise sum:     True
slots            : [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
after x -> x^3   : [2, 3, 4, 5, 6, 7, 8, 1, 10, 11, 12, 13, 14, 15, 16, 9]
  equals 'each row of 8 rotated left by one': True
after x -> x^31  : [9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8]
  equals 'the two rows swapped': True
distinct slot permutations reachable by a single automorphism: 16 of 16! = 20922789888000
full 16-cycle (1,2,...,16)->(2,...,16,1) is a single automorphism: False
== Part C: automorphism on a ciphertext ==
budget before: 116.1 bits; after x->x^3 under key s(x^3): 116.1 bits
decrypts to rotated slots under s(x^3): True
decrypts to rotated slots under original s: False
```

Reading Part A:

- **Addition is nearly free.** One addition of an independent fresh
  ciphertext costs 0.2 bits, 64 cost 3.5 and 4096 cost 8.4 — still less than
  one multiplication. The growth is faster than the `½·log2(count)` (3 and 6
  bits) that independent errors alone would give. (Basis: derived, not
  separated in the probe. With the encoding `Δ = ⌊q/t⌋` used here the scaled
  phase of a sum is `Σm − ((q mod t)/q)·Σm − (t/q)·Σe`, so the invariant
  noise contains a plaintext-dependent term that accumulates linearly. With
  `q mod t = 1` and `Σm ≈ 2¹⁹` after 4096 additions this predicts a budget
  near 128 − 1 − 19.3 ≈ 107.7 bits, which is what was measured for every
  seed tried.)
- **Multiplication costs a level.** With relinearization after each product
  every squaring consumes 10.0–11.8 bits in this run (9.9–12.9 across seeds
  1–8), independent of depth, until the budget is gone at depth 11 (10 or 11
  across those seeds). A budget of `B` bits therefore buys about `B / c`
  multiplicative levels, and supporting one more level means roughly `c`
  more bits of ciphertext modulus — the reason parameter size grows linearly
  with circuit depth, and the reason compilers minimize depth rather than
  operation count. (Basis: derived from the transcript. `c` is specific to
  the toy parameters; its size is consistent with the textbook estimate in
  which a multiplication scales invariant noise by about `t` times a
  ring-dependent expansion factor, `log2 t` being 8 here, but the two
  factors were not measured separately.)
- **Skipping relinearization is not a saving.** Without it the ciphertext
  grows to 3, 5, 9, 17, 33 components and the per-level cost climbs
  (10.8, 13.4, 17.3, 28.7, 49.1 bits); decryption fails at depth 5 (5 or 6
  across seeds) instead of 11.
- **Exhaustion is silent.** At the first failing depth `decrypt` returns
  normally with a well-formed plaintext in which 15 of 16 coefficients are
  wrong.
- **The key holder cannot detect it either.** The estimate computable
  without knowing the plaintext (distance of the scaled phase to the nearest
  integer) agrees with the true budget while the latter is positive and
  reads 0.1 bits when the true value is −5.1: it is confined to be
  non-negative. This is the aliasing SEAL's documentation warns about: "past
  that point the modular reduction aliases the noise [...] A non-zero budget
  does not prove that `Decryptor::decrypt` would return the correct
  plaintext."

The evaluator, who has no key, cannot measure the budget at all. Budget
tracking is therefore necessarily static (a compile-time bound) or
out-of-band (a key-holder diagnostic).

#### 1.2 Scale and level (CKKS)

Basis: documentation (EVA paper, constraints (1)–(4)) + source (EVA checkers, 2.1).

Each CKKS ciphertext carries a coefficient modulus `q` (its level) and a
fixed-point scale. For a node `n` with ciphertext operands:

```text
(1) n.parm1.modulus = n.parm2.modulus            if n.op in {ADD, SUB, MULTIPLY}
(2) n.parm1.scale   = n.parm2.scale              if n.op in {ADD, SUB}
(3) every operand has exactly 2 polynomials      if n.op = MULTIPLY
(4) n.parm2.value <= s_f                         if n.op = RESCALE   (s_f: maximum rescale value)
```

Multiplication multiplies scales; `RESCALE` divides the scale and drops one
prime of `q`; `MODSWITCH` drops a prime without changing the scale. Without
rescaling, "the log2 of the coefficient modulus product Q required for the
input would grow exponentially" with depth; with it, linearly.

#### 1.3 Slots and rotations

Basis: execution (Parts B and C of the transcript above).

With plaintext modulus `t ≡ 1 (mod 2n)` the plaintext ring
`Z_t[x]/(x^n+1)` is isomorphic to `n` independent copies of `Z_t` (*slots*):
ring addition and multiplication act slot-wise. The slots form a `2 × n/2`
array. The automorphism `x → x^3` rotates each row by one position,
`x → x^(2n−1)` swaps the rows, and the `n` automorphisms `x → x^g` (`g` odd)
give exactly `n` slot permutations — 16 of 16! here. In particular the
full 16-cycle is *not* an automorphism.

Applied to a ciphertext, an automorphism leaves the noise budget unchanged
(116.1 → 116.1 bits) but the result decrypts under the automorphed key
`s(x^g)`, not under `s`. Returning to `s` needs a key-switching key for that
specific `g`.

Consequences (Basis: derived):

1. "Vectorizing" for FHE means expressing data movement as products of row
   rotations and a row swap, or paying a multiplication by a mask (a
   *blend*) and thus noise.
2. The set of rotation amounts a compiled program uses is part of its
   interface: the key owner must generate one evaluation key per amount
   before the program can run.
3. The packing layout chosen by the compiler must be known to the client
   that encodes inputs and decodes outputs.

### 2. Compilers

#### 2.1 EVA

Basis: source (`eva/ckks/*.h`, `README.md`) + documentation (paper).

Pass order in `CKKSCompiler::transform`: `TypeDeducer` → `ConstantFolder` →
(`ReductionCombiner`, `ReductionLogExpander` if `balance_reductions`) → one
rescaler (`MinimumRescaler` | `AlwaysRescaler` | `EagerWaterlineRescaler` |
`LazyWaterlineRescaler`) → `EncodeInserter` → `LazyRelinearizer` or
`EagerRelinearizer` → `ModSwitcher` (a backward pass) → `SEALLowering`.
`validate` then runs `LevelsChecker`, `ParameterChecker` and `ScalesChecker`;
finally `EncryptionParametersSelector` and `RotationKeysSelector` compute the
parameter set and the list of rotation steps for which keys are needed.

| Aspect | What the source does |
|---|---|
| Scale representation | an unsigned integer number of *bits* per term (`TermMapOptional<uint32_t>`); multiplication adds operand scales, rescale subtracts the divisor |
| Waterline rule | `minScale` = the largest input scale; after a multiplication, `while (multScale >= fixedRescale + minScale) insert RESCALE by fixedRescale`, with `fixedRescale = 60` |
| Additions with unequal scales | the lower-scale ciphertext operand is multiplied by a constant 1 encoded at the scale difference |
| Scale check | `ScalesChecker` throws `std::logic_error("Addition or subtraction in program has operands of non-equal scale")` and rejects any zero scale |
| Level check | `LevelsChecker` compares operand levels with `assert(operandLevel == operandLevel2)` |
| Parameter check | `ParameterChecker` throws `InconsistentParameters`; the compiler's messages state that the `minimum` policy "is not general" and `always` "is only guaranteed to work for programs that have equal scale for all inputs and constants" |
| Parameter selection | prime bit-counts = primes for the output (output scale + user-declared range, in chunks of at most 60 bits) + the rescale divisors along the longest chain + one "key prime" equal to the largest; the ring degree is the smallest whose SEAL maximum modulus bit-count for the requested security level covers the total |
| Defaults (`ckks_config.h`) | `balance_reductions = true`, `rescaler = lazy_waterline`, `lazy_relinearize = true`, `security_level = 128`, `quantum_safe = false`, `warn_vec_size = true` |
| User obligations | `set_input_scales(bits)`, `set_output_ranges(bits)` |

Three properties that are easy to miss:

- **EVA has no noise model.** The word "noise" occurs once in its C++,
  Python and Markdown sources, in a comment. Correctness rests on the
  user-declared input scales and output ranges being adequate; no compiler
  pass checks that the fixed-point precision surviving the computation is
  sufficient. (Basis: source, by search.)
- **The level check is an `assert`.** In a build with assertions disabled it
  checks nothing; the scale check, in contrast, always throws. (Basis:
  derived from the two checker sources; the build configuration actually
  shipped was not examined.)
- **Scales are tracked as if primes were powers of two.** The paper notes
  that SEAL's primes are only "close to a power-of-2" and that the executor
  adjusts the scale "as if it was divided by the power-of-2 instead"; the
  README additionally requires building SEAL with transparent-ciphertext
  checking off because "it is not possible in general to statically ensure a
  program will not produce a transparent ciphertext".

#### 2.2 HEIR

Basis: source and in-tree documentation (`docs/content/en/docs/{pipelines.md,Design/*.md}`, `lib/Transforms/**/*.td`, `lib/Analysis/NoiseAnalysis/`).

HEIR is an MLIR-based toolchain. Programs enter in standard MLIR dialects
with secret inputs marked `{secret.secret}`; a `secret<T>` type wraps any
MLIR type and `secret.generic` lifts a cleartext computation to secret data,
so upstream canonicalizations apply before any scheme is chosen.

| Stage | Pipeline / pass | Effect |
|---|---|---|
| Scheme-agnostic | `--mlir-to-secret-arithmetic` | data-oblivious transforms (remove secret-dependent control flow), layout optimization, client encrypt/decrypt helpers |
| Scheme choice | `--mlir-to-bgv`, `--mlir-to-bfv`, `--mlir-to-ckks`, `--mlir-to-cggi` (Boolean via Yosys, or integer) | insert management operations, generate parameters, lower `secret` to a scheme dialect |
| Management | `secret-insert-mgmt-bgv` / `-bfv` / `-ckks` | relinearize after every ciphertext–ciphertext multiplication; modulus-switch (CKKS: rescale) before multiplications; equalize levels for additions; annotate each value with `mgmt.mgmt` (level, dimension); CKKS bootstraps greedily "when all levels are consumed" |
| Parameters | `generate-param-bgv`, `generate-param-bfv` | choose moduli under a named noise model |
| Validation | `validate-noise` | recompute the bound per value; prints `Noise Bound`, `Budget`, `Total` under `--debug-only=ValidateNoise` |
| Back end | `--scheme-to-openfhe`, `--scheme-to-lattigo`, `--scheme-to-tfhe-rs`, `--scheme-to-jaxite`, `--scheme-to-fpt`; `heir-translate --emit-*` | lower to a library-API dialect and print C++, Go, Rust or Python source |

Noise models selectable by name (default `bgv-noise-kpz21` / `bfv-noise-kpz21`):

| Model option | Tracks | Pass documentation's own characterization |
|---|---|---|
| `*-noise-by-bound-coeff-worst-case` | bound on the coefficient embedding, multiplication expansion factor `N` | "taken from KPZ21" |
| `*-noise-by-bound-coeff-average-case` (= `*-kpz21`) | same, expansion factor `2√N` (`4√N` "in some special cases") | "taken from KPZ21" |
| `bgv-noise-by-variance-coeff` (= `bgv-noise-mp24`) | variance of the coefficient embedding | "a more accurate noise estimate, but it may give underestimates in some cases" |
| `bfv-noise-by-variance-coeff` (= `bfv-noise-bmcm23`) | variance of the coefficient embedding | "a much tighter noise estimate for independent ciphertext input, but may give underestimation for dependent ciphertext input" |
| `bgv-noise-mono` | canonical-embedding bound on the quantity that decides correct decryption | "taken from MMLGA22" |
| `bfv-noise-canon-emb` | same | "adapted from MMLGA22 with mixes from BMCM23 and KPZ21" |

What HEIR states about soundness, verbatim from `Design/noise.md`:

> Noise analyses and (especially) parameter generation in HEIR should be
> viewed as experimental. *There is no guarantee that they are correct or
> secure* and the HEIR authors do not take responsibility.
>
> Currently, worst-case methods are often too conservative, while
> average-case methods often give underestimation.

The HEIR paper adds that CKKS noise models "require explicit bounds on the
range of values of the underlying messages" and that "CKKS parameter
selection is not completely automated". Testing support named in the paper:
a plaintext back end that runs the lowered program without encryption, and a
pass that inserts a call after every homomorphic operation while threading
the secret key through, used "to compare actual ciphertext noise to noise
model bounds".

Packing is represented explicitly (`Design/layout.md`): a *layout* is a
partial function from ciphertext-slot indices to cleartext tensor indices,
restricted to those expressible as a Presburger (quasi-affine) relation,
with unmapped slots equal to zero; the optimizer is based on Fhelipe.

#### 2.3 Concrete (TFHE)

Basis: documentation and source at the pinned revision.

- **Pipeline.** A Python function is traced and lowered through MLIR
  dialects `FHELinalg` → `FHE` (types such as `!FHE.eint<4>`, operations such
  as `FHE.apply_lookup_table`) → `TFHE` → `Concrete` (`docs/explanations/dialects.md`).
- **Programmable bootstrapping.** Every non-linear univariate function is a
  table lookup evaluated during bootstrapping; table inputs are limited to
  16 bits ("only up to 16-bit table lookups are supported",
  `docs/compilation/common_errors.md`), and cost rises with input precision.
- **Bit-widths come from samples.** "An inputset is a collection
  representing the typical inputs of the function. It is used to determine
  the bit widths and shapes of the variables" and "Evaluating the circuit
  with input values under or over the bounds may result in undefined
  behavior" (`docs/get-started/quick_start.md`). The integer range of every
  intermediate value is thus *measured*, not proved.
- **Correctness is probabilistic by configuration.**
  `DEFAULT_P_ERROR = None`, `DEFAULT_GLOBAL_P_ERROR = 1 / 100_000`
  (`frontends/concrete-python/concrete/fhe/compilation/configuration.py`):
  by default the whole circuit may be wrong once in 100000 executions.
  `p_error` bounds each lookup, `global_p_error` the circuit. The
  documentation's own example shows estimated complexity falling from
  294,773,524 at `p_error = 10⁻⁶` to 184,144,972 at `10⁻²`.
- **Parameters are optimized, not typed.** `concrete-optimizer` searches the
  parameter space for the cheapest set meeting a security level and "a noise
  bound that guarantees a given error level (under the assumption that noise
  growth is correctly managed via bootstrapping)"; the critical quantity is
  "the 2-norm of any dot product" (`docs/explanations/optimizer.md`).
  Security levels come from curves fitted to the Lattice Estimator.
- **Threat model.** "The cryptographic parameters are chosen considering the
  IND-CPA security model [...] it is assumed that the results of decrypted
  computations are not shared by the secret key owner with any third
  parties, as such an action can lead to leakage of the secret encryption
  key" (`docs/explanations/security.md`).

#### 2.4 Porcupine and Coyote

Basis: documentation (Porcupine paper) + source (Coyote repository).

- *Porcupine* synthesizes vectorized BFV kernels from a DSL, Quill, that
  models instruction "noise, latency, behavior"; the search completes a
  *sketch*, including a "local rotate" sketch that treats rotations as inputs
  of arithmetic instructions. Its abstract reports speedups "of up to 51%
  (11% geometric mean) compared to heuristic-driven hand-optimized kernels".
  The paper states the noise rule assumed: "add and rotate additively
  increase noise, and multiplication multiplicatively increases noise".
- *Coyote* compiles arithmetic circuits written as decorated Python
  functions (`scalar()`, `vector(n)`, `matrix(r, c)` inputs) to a scalar IR,
  vectorizes them, and lowers to C++ against SEAL. Its vector IR has five
  instruction kinds — rotate, element-wise operation, load, constant, and
  `blend(v1@mask1, v2@mask2, ...)` — and assigns scalar values to *lanes*;
  the rotation amount between producer and consumer is the lane difference
  modulo the vector width. The repository's `ops.csv` records per benchmark
  the scalar operation counts against the vector add/sub/mul, rotate and
  blend counts (for example `matmul3x3`: 18 scalar additions and 27 scalar
  multiplications become 5 vector additions, 6 vector multiplications, 10
  rotations and 11 blends). The artifact uses `networkx` and `z3`.

#### 2.5 Who computes the bound, and with what claim

| System | Resource tracked | Mechanism | Soundness claim in the examined material |
|---|---|---|---|
| EVA | scale (bits), level, polynomial count, rotation steps | forward/backward rewriting passes plus three checkers | paper: generated programs are "correct and secure"; no noise analysis exists in the source |
| HEIR | level, dimension, scale, noise bound, layout | MLIR dataflow analyses; named noise models; ILP/greedy placement | explicitly none for noise and parameters ("experimental") |
| Concrete | integer bit-width, noise level (through the 2-norm of dot products), failure probability | sampled bounds + external parameter optimizer | correctness "up to a given failure probability" chosen by the user; security at IND-CPA |
| Porcupine | noise, latency, rotations | sketch-based program synthesis | abstract: "optimized, verified HE kernels" |
| Coyote | rotations, blends, vector width | search over lane assignments | not examined beyond the repository |

### 3. Decryption is a release

Basis: source/documentation at the pinned revisions.

| Library | Statement |
|---|---|
| SEAL 4.7.2, `invariant_noise_budget` | "The return value is a function of c_0 + c_1*s mod q and therefore depends on the secret key. Repeated evaluation on attacker-chosen ciphertexts leaks the secret key. [...] its return value must not be propagated across a trust boundary." |
| OpenFHE, `src/pke/examples/CKKS_NOISE_FLOODING.md` | CKKS decryption returns `m + e`, so "we should always think of the RLWE ciphertext error as part of the secret key"; mitigation: randomized decryption adding discrete Gaussian noise with `σ = √(12τ) · 2^(s/2) · ct.t` for `τ` expected adversarial queries, `s` bits of statistical security and a statically estimated ciphertext error `ct.t`, obtained by a separate `EXEC_NOISE_ESTIMATION` run on a fresh key |
| Concrete | parameters assume IND-CPA; sharing decryptions requires custom parameters "in consideration of the IND-CPA^D security model" |
| TFHE-rs 1.9.0 | "default parameters are selected with a bootstrapping failure probability [...] fixed at p_error ≤ 2⁻¹²⁸ [...] A failure probability below 2⁻¹²⁸ ensures that our implementation is resilient against attacks in the IND-CPA-D model"; 2⁻⁶⁴ parameters remain available "where only the IND-CPA model is considered" |

The paper cited by both Zama documents for IND-CPA-D (Li, Micciancio,
Schultz, Sorrell; ePrint 2022/816) states the repair for approximate schemes
in its abstract: "post-processing the output of the decryption function with
a mechanism satisfying an appropriate notion of differential privacy (DP),
adding an amount of noise tailored to the worst-case error growth of the
homomorphic computation". (Basis: documentation.)

Basis: derived from the statements above. Two different leaks meet at the
same boundary. In approximate schemes the decrypted value itself contains
the error (OpenFHE); for exact schemes the quantity the TFHE-rs
documentation ties to IND-CPA-D security is the decryption *failure*
probability. Either way, a failure
probability that is acceptable for functional correctness (Concrete's
default 10⁻⁵ per circuit) is far from one that is safe when results are
published (2⁻¹²⁸), and the repair for the approximate case is a
differential-privacy mechanism whose scale depends on a bound on error
growth — the quantity section 2 showed compilers to estimate heuristically.

### 4. Sensitivity as a type

#### 4.1 Fuzz

Basis: documentation (Reed and Pierce, ICFP 2010).

Types denote metric spaces; a function is *c-sensitive* if it magnifies
distances by at most `c`.

```text
types   τ ::= α | b | 1 | μα.τ | τ + τ | τ ⊗ τ | τ & τ | τ ⊸ τ | τ → τ | !_r τ
τ1 ⊸ τ2      1-sensitive functions          !_r τ      τ with distances scaled by r
!_c τ1 ⊸ τ2  c-sensitive functions          τ1 → τ2    unrestricted (∞-sensitive) functions
contexts bind  x :_r τ   (x may be used with sensitivity r)

Metric preservation (Theorem 2.4).  If Γ ⊢ e : τ, x_i :_{r_i} τ_i ∈ Γ and
d(v_i, v_i') = s_i, and [v/x]e evaluates to v, then [v'/x]e evaluates to some v'
with d_τ(v, v') ≤ Σ_i r_i · s_i.

Probability monad ○τ with metric
    d_○τ(δ1, δ2) = (1/ε) · max_x | ln(δ1(x) / δ2(x)) |
Lemma 4.2.  A 1-sensitive function τ → ○σ is the same thing as an
ε-differentially private random function τ → σ.

primitives      size : db ⊸ R        add_noise : R ⊸ ○R
example         λd. add_noise (filter over_40 d) : db ⊸ ○R
monad rules     return multiplies the context by ∞;  let ○x = e in e' adds contexts
```

The `return` rule is the type-level form of "releasing a value exactly is
infinitely sensitive"; privacy budget composes because sequencing adds
context sensitivities. The paper treats values of type `○τ` "as literally
being mathematical probability distributions" over values that include real
numbers `R`.

#### 4.2 DFuzz and later systems

Basis: documentation (DFuzz paper) + source (`ejgallego/dfuzz`, `examples/dfuzz/cdf.fz`); bibliographic record only for the TOPLAS paper.

DFuzz adds *size* terms (natural numbers describing data sizes) and
*sensitivity* terms (non-negative extended reals) at the type level, with
quantification and subtyping, so that a sensitivity may depend on a run-time
size. From the pinned repository:

```text
function cdf
  forall (e : sens, i : size)
  (eps : num[e])
  (buckets : list(num)[i])
  (db :[i * e] num bag)
  : fuzzy list(num)[i] { ... sample count = add_noise[e] eps (bagsize lt); ... }
```

(body abridged; the signature is verbatim).

The annotation `db :[i * e]` says the database is used with sensitivity
`i · e`: one `e`-private count per bucket, `i` buckets. The repository is a
type checker only ("Running the program is still not supported in dFuzz").

*Contextual Linear Types for Differential Privacy* (Toro, Darais, Abuah,
Near, Árquez, Olmedo, Tanter; ACM TOPLAS 45(2), article 8, 2023) introduces
the language Jazz, whose types carry *latent contextual effects* that delay
the payment of sensitivity and privacy effects across products, sums and
higher-order functions, with the aim of supporting (ε, δ)-style variants
together with higher-order programming. Only its bibliographic record and an
abstract-level description were verified (see Boundaries).

#### 4.3 What the type systems assume about arithmetic

Basis: derived from 4.1–4.2.

Every judgment above is about real-valued metrics and exact probability
distributions. Three assumptions are therefore outside the theorem:

1. `add_noise` samples the stated continuous distribution exactly;
2. primitive arithmetic (`+`, `size`, summation) has the sensitivity of its
   real-number counterpart;
3. nothing but the returned value is observable (no timing, no rounding
   artefacts).

Section 5 shows each of these failing for a straightforward implementation.

### 5. Finite arithmetic at the release boundary

Basis: execution (source and command under Evidence, `dp_floating_point_probe.py`).

```text
== Part 1: binary64 Laplace mechanism  y = mu + s*lam*ln(k/2^53) ==
  window [2.0, 2.0+2^-32), lam=1.0: 524288 binary64 values
    reachable when f(D)=0 :   283819 ( 54.1%)  from 283819 grid points
    reachable when f(D)=1 :   455022 ( 86.8%)  from 771499 grid points
    reachable under both  :   246243;  under neither: 31690
    P[output identifies f(D)=0 | f(D)=0, output in window] = 0.1324
    P[output identifies f(D)=1 | f(D)=1, output in window] = 0.4589
  window [3.0, 3.0+2^-32), lam=1.0: 524288 binary64 values
    reachable when f(D)=0 :   104412 ( 19.9%)  from 104412 grid points
    reachable when f(D)=1 :   283819 ( 54.1%)  from 283819 grid points
    reachable under both  :    56528;  under neither: 192585
    P[output identifies f(D)=0 | f(D)=0, output in window] = 0.4586
    P[output identifies f(D)=1 | f(D)=1, output in window] = 0.8008
  lam=1        n=20000: self-test (own outputs found in own support) 20000/20000 and 20000/20000
    outputs of f(D)=0 that are impossible under f(D)=1: 0.668
    outputs of f(D)=1 that are impossible under f(D)=0: 0.603
  lam=2        n=20000: self-test (own outputs found in own support) 20000/20000 and 20000/20000
    outputs of f(D)=0 that are impossible under f(D)=1: 0.639
    outputs of f(D)=1 that are impossible under f(D)=0: 0.615
  lam=3.33333  n=20000: self-test (own outputs found in own support) 20000/20000 and 20000/20000
    outputs of f(D)=0 that are impossible under f(D)=1: 0.648
    outputs of f(D)=1 that are impossible under f(D)=0: 0.636
  lam=1.0: f(D)=0 outputs in (0,1): 63275; integer multiples of 2^-53: 36269 (0.5732)
  lam=1.0: f(D)=1 outputs in (0,1): 63671; integer multiples of 2^-53: 63671 (1.0000)
== Part 2: exact discrete samplers (pinned reference implementation) ==
  file sha256 = 6a19497ab5d77c6910a2b85b7fcf19ba6f83226910388e84ac3ecd23090b6c04
  discrete Laplace(scale=2): 100000 samples, all Python ints; max |empirical - exact pmf| on [-12,12] = 0.0013 (binomial 3-sigma at x=0 = 0.0041)
  pmf formula ratio max over x in [-50,50] of P[x]/P[x-1] = 1.648721; e^(1/scale) = 1.648721; observed sample range = [-21, 22]
  uniform draws consumed per sample, grouped by |output| (6 means >= 6):
    |x|=0: count= 24409 mean=  7.71 min= 5 max= 47
    |x|=1: count= 29846 mean=  8.07 min= 5 max= 44
    |x|=2: count= 18026 mean= 10.94 min= 8 max= 49
    |x|=3: count= 10929 mean= 11.36 min= 8 max= 45
    |x|=4: count=  6562 mean= 14.14 min=11 max= 50
    |x|=5: count=  3958 mean= 14.46 min=11 max= 49
    |x|=6: count=  6270 mean= 19.35 min=14 max= 52
  discrete Gaussian(sigma^2=4): mean=-0.0046 var=4.0027 (module's variance(4) = 4.0000); uniform draws per sample: mean=17.91
== Part 3: realised vs idealised sensitivity of a bounded sum (records in [0, 1]) ==
  (a) binary64, n=1048577: sum(D)=1.0000000002328306 sum(D')=1.1641532182693484e-10
      realised difference sum(D) - sum(D') = 1 + 1.164e-10 (exact rational arithmetic on the two computed sums); idealised sensitivity = 1
      true real sum of D = 1 + 1.164e-10; computed sum(D) - 1 = 2.328e-10 (each tiny addend was rounded up to a full ulp)
      same records, other orders: ascending sum(D) - 1 = 1.164e-10, math.fsum(D) - 1 = 1.164e-10
  (b) binary32, n=4194305: sum(D)=1.5 sum(D')=0.2500000298023224 realised |difference|=1.2499999701976776 vs idealised 1  (excess +0.2500)
  (c) int64 wraparound, records in [0, 2^62]: sum(D)=-9223372036854775808 sum(D')=4611686018427387904 |difference| = 3 * 2^62 vs idealised 1 * 2^62
```

#### 5.1 The Laplace mechanism in binary64 is porous

The mechanism modelled is the textbook `y = f(D) + S·λ·ln(U)` with `S`
uniform in `{−1, +1}` and `U = k/2⁵³`, `k` uniform in `1..2⁵³` — the form
Mironov's paper analyses as `Y ← (2Z − 1)·λ ln(U)`.

- **Exhaustive window.** Of the 524288 binary64 values in
  `[2, 2 + 2⁻³²)`, 54.1% are reachable when `f(D) = 0`, 86.8% when
  `f(D) = 1`, 246243 under both and 31690 under neither. Conditioned on the
  output falling in the window, 45.9% of the outputs produced with
  `f(D) = 1` cannot occur with `f(D) = 0`. In `[3, 3 + 2⁻³²)` the figure is
  80.1%.
- **Whole distribution.** For λ ∈ {1, 2, 1/0.3}, between 60% and 67% of
  20000 sampled outputs of one database are outside the support of the
  mechanism on the neighbouring database, in both directions. The
  membership test is exact up to an assumption of local monotonicity of
  `log` (bisection plus a ±16 grid-point scan); as a control, every sampled
  output was found in its own mechanism's support (20000/20000 in all six
  cases).

One such output identifies the database with certainty; no value of ε
describes that. Mironov's paper reports the same phenomenon for
`f(D) = 0`, `f(D') = 1`: for small λ "the probability that a single sample
reveals the input is close to 100%" and for λ up to 3 it "never becomes less
than 35%".

Why. `ln(U)` takes values on an irregular grid whose spacing `2⁻⁵³/U` is
unrelated to the spacing of doubles near the result, and adding `f(D)`
moves the noise into a binade with a different unit in the last place. The
last two lines of Part 1 measure the simplest consequence: among 200000
outputs per database (λ = 1), every one of the 63671 outputs of the
`f(D) = 1` mechanism that fell in `(0, 1)` is an integer multiple of 2⁻⁵³,
against 57.3% of the 63275 such outputs of the `f(D) = 0` mechanism. A
single divisibility test on the low-order bits therefore rules out
`f(D) = 1` for 42.7% of the `f(D) = 0` outputs in that interval. (Basis:
execution. The reason is derived: a double in `[0.5, 1)` is always a
multiple of 2⁻⁵³, and an output in `(0, 0.5)` is `1 + x` with
`x ∈ (−1, −0.5)`, itself a multiple of 2⁻⁵³, a subtraction binary64
performs exactly; the `f(D) = 0` mechanism instead returns `±ln(U)`
directly, on the finer grids of the binades below 0.5.)

#### 5.2 Repairs and what each still trusts

| Repair | Definition | Residual assumptions | Basis |
|---|---|---|---|
| Snapping mechanism (Mironov) | `clamp_B(⌊clamp_B(f(D)) ⊕ S ⊗ λ ⊗ LN(U*)⌉_Λ)`, `Λ` the smallest power of two ≥ λ, `U*` uniform over doubles in (0,1) with probability proportional to ulp, `LN` an exactly rounded logarithm | exactly rounded `ln`; correct sampling of `U*`; guarantee is `(1/λ + 2⁻⁴⁹B/λ)`-DP for `λ < B < 2⁴⁶·λ` (Theorem 1), not `1/λ` | documentation |
| Discrete Laplace / discrete Gaussian (Canonne, Kamath, Steinke) | integer-valued noise sampled exactly using only uniform integers and rational arithmetic | integer-valued query; unbounded integers and rationals; uniform integer source | source + execution |
| Granularity rounding (`google/differential-privacy`, C++) | granularity = next power of two ≥ `(sensitivity/ε)/2⁴⁰`; result = `RoundToNearestMultiple(value, granularity) + granularity × (two-sided geometric sample)`; header comment: "uses a geometric distribution to generate its noise in order to avoid the attack from Mironov's 2012 paper" | geometric sampler and rounding implemented in binary64 | source |
| OpenDP `cks20` samplers | Rust port of the reference sampler over big rationals (`dashu`), functions marked `#[proven]`; file header cites the IBM file at commit `cb190d2a990a78eff6e21159203bc888e095f01b` | the written soundness proofs kept beside the code (one LaTeX Hoare-triple document per function; not machine-checked); entropy source | source |
| SampCert | Lean 4 / Mathlib development with a verified discrete Gaussian sampler; its README states it "is deployed and used in the AWS Clean Rooms Differential Privacy service" | the four `@[extern]` primitives of its probability language (`prob_Pure`, `prob_Bind`, `prob_UniformByte`, `prob_While`) implemented in `ffi.cpp`, which reads `/dev/urandom`; extraction; running time | source |

Execution of the pinned reference sampler (Part 2 of the transcript):
100000 discrete Laplace samples at scale 2 are all Python integers and match
the exact probability mass function within sampling error (maximum deviation
0.0013 against a 3σ band of 0.0041). Since that mass function is positive at
every integer, the mechanism's support is all of ℤ for every integer query
value, and neighbouring outputs have ratio exactly `e^(1/scale)`: there are
no distinguishing outputs. (Basis: derived from the closed form; the sample
confirms the implementation follows it.)

**The exact sampler is not constant-time.** The number of uniform draws per
sample ranged from 5 to 52 and its *minimum* is a step function of the
output magnitude: 5 for |x| ≤ 1, 8 for |x| ∈ {2, 3}, 11 for {4, 5}, 14 beyond;
the mean rises from 7.7 to 19.4. An observer of running time learns about
the magnitude of the noise, hence about the true answer. This is the channel
reported by Jin, McMurtry, Rubinstein and Ohrimenko (IEEE S&P 2022), whose
abstract states that "an observer that can measure the time to draw
(discrete) Laplace or Gaussian noise can predict the noise magnitude" and
reports success rates "up to 99.65% for end-to-end timing attacks on private
sum protected with discrete Laplace". Exactness and
constant time pull in opposite directions: exact sampling of a distribution
with irrational probabilities needs an unbounded number of random bits.

#### 5.3 Sums are more sensitive than their idealization

Records are clamped to `[0, 1]`; neighbouring datasets differ by removing
one record; the idealized sensitivity of the sum is 1.

| Case | Computed | Realised difference | Excess |
|---|---|---|---|
| binary64, left-to-right, `D = [1.0] + [v]·2²⁰`, `v` the double just above 2⁻⁵³ | `sum(D) = 1.0000000002328306`, `sum(D') = 1.1641532182693484e-10` | `1 + 1.164e-10` | `2⁻³³` |
| binary32 (each partial sum rounded to single precision), `D = [1.0] + [v]·2²²`, `v` the float just above 2⁻²⁴ | `sum(D) = 1.5`, `sum(D') = 0.2500000298…` | `1.2499999702` | 25% |
| 64-bit two's-complement, records in `[0, 2⁶²]`, `D = [2⁶², 2⁶²]` | `sum(D) = −2⁶³` | `3 · 2⁶²` | 200% |

Mechanism (Basis: derived, confirmed by the binary64 row): each addend is
slightly more than half a unit in the last place of the running sum 1.0, so
every addition rounds *up* by a full unit. The computed sum of `D` exceeds
1 by `2.328e-10`, twice the true `1.164e-10`; the same addends summed from
zero are accumulated accurately. The excess is `m · u` for `m` addends and
unit roundoff `u`, i.e. it grows linearly with the number of records, and
the summation order matters: sorted ascending, or with `math.fsum`, the
excess vanishes.

This is the class of vulnerability described by Casacuberta, Shoemate,
Vadhan and Wagaman (CCS 2022), whose abstract concludes that "essentially
all differential privacy libraries fail to introduce enough noise".
OpenDP's repair at the pinned revision is visible in source
(`rust/src/traits/sum.rs`, `rust/src/transformations/sum/float/mod.rs`):
summation is typed by strategy (`Sequential`, with depth `n − 1`, or
`Pairwise`, with depth `⌈log2 n⌉`), and the stability map returns
`d · sensitivity + relaxation` with

```text
relaxation = 2 · (h·u / (1 − h·u)) · n · M        h = depth, u = epsilon/2 (unit roundoff),
                                                  n = maximum size, M = maximum magnitude
```

refusing construction when `h·u ≥ 1` or when an intermediate overflow is
possible. For the binary64 row above (`n = 2²⁰ + 1`, sequential,
`M = 1`) the relaxation is about `2⁻¹²`, comfortably above the observed
excess `2⁻³³`. (Basis: derived arithmetic on the source formula.)

### 6. One structure, two literatures

| | FHE | Differential privacy |
|---|---|---|
| Graded resource | noise budget / levels; failure probability | sensitivity; privacy budget ε (and δ) |
| Cheap operation | addition: sub-additive in bits | post-processing: free |
| Expensive operation | multiplication: one level each | each release: adds ε |
| Composition law | budgets subtract along the deepest path | sensitivities multiply through `!_r`, budgets add through monadic bind |
| Reset | bootstrapping (cost; in TFHE also a table lookup) | none |
| Who can observe the resource | only the key holder, and only approximately | nobody (it is a property of pairs of runs) |
| Static mechanism | dataflow analysis or parameter optimizer | linear/graded types |
| Idealization in the soundness argument | worst- or average-case noise heuristics; sampled value ranges | real numbers; exact distributions |
| What breaks it | under-estimated noise → silent wrong result, or key leakage when results are released | porous floating-point output; under-estimated sensitivity; timing |
| Release boundary | decrypt (needs flooding or negligible failure probability if shared) | noisy answer (needs an exact discrete sampler and a sensitivity bound for the executed arithmetic) |

Boundary invariants for a toolchain that wants to state these as types
(Basis: derived from the findings):

1. A ciphertext type needs at least scheme, key identity, level, scale,
   polynomial count, layout and a noise bound; a library handle that hides
   them makes every cross-library call unchecked.
2. The rotation set and the layout belong to a compiled function's
   signature, because both must exist on the client before the call.
3. Integer ranges used to choose bit-widths must be proven or enforced by
   clamping at entry; a sampled range is a profile.
4. Decryption must be typed as producing a secret; publishing it is a
   separate, budgeted operation.
5. A DP release type must be discrete, and the sensitivity bound must be
   proven for the arithmetic that runs (order of summation, precision,
   overflow), not for its real-number reading.
6. An exact sampler is a variable-time primitive; its running time must be
   padded or treated as part of the output.

## Boundaries

- **Not examined — production FHE behaviour.** No SEAL, OpenFHE, Lattigo,
  TFHE-rs, HEIR, EVA or Concrete binary was run. Whether HEIR's noise models
  under- or over-estimate on any concrete circuit, and by how much, is
  *unknown* from this report; only the project's own statement is recorded.
- **Not examined — key-recovery attacks.** The IND-CPA-D attacks on
  approximate and exact schemes are referenced only through the libraries'
  documentation and the one abstract quoted in Findings 3; the attack papers
  were not read and nothing was reproduced.
- **Not examined — Porcupine's and Coyote's algorithms in detail**, CHET,
  HECO, Fhelipe, and CKKS bootstrapping. Coyote's paper text was not
  retrieved; statements about it come from its repository, and its
  bibliographic identity from a DOI search.
- **Not examined — the TOPLAS 2023 paper's rules and theorems.** Its text
  could not be retrieved; no arXiv identifier is cited for it because none
  could be confirmed. Duet (OOPSLA 2019) is likewise not examined.
- **Not examined — the Fuzz runtime and its timing defences.**
- **Not examined — the snapping mechanism in execution.** It is quoted from
  the paper; implementing it faithfully needs an exactly rounded logarithm.
- **Unknown — EVA's shipped build configuration.** Whether `assert` is
  active in distributed builds was not determined.
- **Unknown — correctness of the Google C++ secure-noise implementation.**
  Only its structure was read; its accompanying design note was not.
- **Known not to apply.** Toy BFV bit counts (116-bit fresh budget, 10–13
  bits per level, depth 10–11) are properties of `n = 16`, `t = 257`,
  `q = 2¹²⁸` and base-16 relinearization. Only the *shape* (sub-linear
  additions, constant per-level multiplicative cost, growth without
  relinearization, silent failure) is argued to generalize, and that
  argument is derived, not measured on real parameters.
- **Known not to apply.** The porosity percentages are for a uniform grid of
  2⁵³ values of `U` and for `f(D) ∈ {0, 1}`; other uniform samplers give
  other percentages (Mironov tabulates several).
- **Not examined — typical-case summation error.** The sum examples are
  constructions chosen to exhibit the excess; how closely ordinary data
  approaches them was not measured. They show only that the idealized bound
  is not a bound.
- **Unsupported.** EVA at the pinned revision supports CKKS only. The dfuzz
  repository type-checks but does not run programs. HEIR's CKKS parameter
  selection is not fully automated.
- **Stronger conclusions the evidence does not support.** (a) That an
  FHE program accepted by any of these compilers decrypts correctly: EVA
  does not model noise, HEIR disclaims its models, Concrete targets a
  non-zero failure probability. (b) That a program well-typed in Fuzz or
  DFuzz is differentially private *as executed*. (c) That an exact discrete
  sampler makes a mechanism safe: sensitivity and timing remain. (d) That a
  verified sampler removes all trust: its entropy source, foreign-function
  primitives and extraction are outside the proof.

## Evidence

Observation date for all material: 2026-11-19. Repository heads were resolved
with `git ls-remote https://github.com/<owner>/<repo>.git HEAD` and files were
read from tarballs of exactly those commits.

### Source locations

| Repository @ revision | Paths used |
|---|---|
| `google/heir` @ `372c088c9c4456f56ade7151058bbb900394d21b` | `docs/content/en/docs/pipelines.md`; `docs/content/en/docs/Design/noise.md`, `layout.md`, `secret.md`; `lib/Transforms/GenerateParam/GenerateParam.td`; `lib/Transforms/ValidateNoise/ValidateNoise.td`; `lib/Transforms/SecretInsertMgmt/Passes.td`; `lib/Analysis/NoiseAnalysis/{README.md,BGV,BFV}` |
| `microsoft/EVA` @ `7ea9d34b0380c25c03fe529fe9a755a6477144ce` | `eva/ckks/ckks_compiler.h` (lines 36–135: `transform`, `validate`); `scales_checker.h`; `levels_checker.h`; `eager_waterline_rescaler.h` (lines 13, 87–91); `lazy_waterline_rescaler.h`; `encryption_parameter_selector.h`; `ckks_config.h` (lines 31–38); `README.md` |
| `raghav198/coyote` @ `d0d6d43a39be0be91709168b86b9cee8c60b4946` | `README.md`; `ARTIFACT.md`; `coyote/codegen.py`; `ops.csv` |
| `zama-ai/concrete` @ `ecb729bb0a6d516c7742593b66e1db11122f0db9` | `docs/core-features/fhe_basics.md`; `docs/core-features/table_lookups_advanced.md`; `docs/get-started/quick_start.md`; `docs/explanations/{dialects,optimizer,security}.md`; `docs/optimization/optimize-cryptographic-parameters/p-error.md`; `docs/compilation/common_errors.md`; `frontends/concrete-python/concrete/fhe/compilation/configuration.py` (lines 26–27) |
| `zama-ai/tfhe-rs` @ `fbc8b20de2bbf2f0e1582451d6399dec1bc45685` | `tfhe/docs/getting-started/security-and-cryptography.md` (lines 116–121); `tfhe/Cargo.toml` (version 1.9.0) |
| `microsoft/SEAL` @ `ce53aa40969364f79599009bc8882f71fce0c13d` | `native/src/seal/decryptor.h` (lines 84–115); `CMakeLists.txt` (version 4.7.2) |
| `openfheorg/openfhe-development` @ `b59e1f291965f14fbee5172cd83a20f5b856204f` | `src/pke/examples/CKKS_NOISE_FLOODING.md` |
| `ejgallego/dfuzz` @ `09b408e4f917cdd6945bdc20b7dd325ff80e5843` | `README.md`; `examples/dfuzz/cdf.fz` |
| `IBM/discrete-gaussian-differential-privacy` @ `cb190d2a990a78eff6e21159203bc888e095f01b` | `discretegauss.py` (SHA-256 `6a19497ab5d77c6910a2b85b7fcf19ba6f83226910388e84ac3ecd23090b6c04`) |
| `opendp/opendp` @ `9e5d8b039cd573ea5b8d80ce8a7dff975d5c32ad` (0.16.0-dev) | `rust/src/traits/samplers/cks20/mod.rs`; `rust/src/traits/sum.rs` (lines 40–68); `rust/src/transformations/sum/float/mod.rs` |
| `google/differential-privacy` @ `29ffc2a414b199ff62c040cf60c0f55599c7da22` | `cc/algorithms/distributions.h` (lines 125–160); `cc/algorithms/distributions.cc` (lines 256–272, 341–352); `cc/algorithms/numerical-mechanisms.cc` (line 197) |
| `leanprover/SampCert` @ `a2c53bb5ff790e729e252958060699b7eff898b9` | `README.md`; `SampCert/SLang.lean` (lines 65–143); `ffi.cpp`; `SampCert/Extractor/`; `lean-toolchain` (Lean v4.34.1) |

### Publications

| Work | Identity | Used for |
|---|---|---|
| Dathathri, Kostova, Saarikivi, Dai, Laine, Musuvathi. *EVA: An Encrypted Vector Arithmetic Language and Compiler for Efficient Homomorphic Computation.* PLDI 2020 | DOI `10.1145/3385412.3386023`; arXiv 1912.11951v2 | constraints (1)–(4); power-of-two footnote |
| Cowan, Dangwal, Alaghi, Trippel, Lee, Reagen. *Porcupine: A Synthesizing Compiler for Vectorized Homomorphic Encryption.* PLDI 2021 | DOI `10.1145/3453483.3454050`; arXiv 2101.07841v1 | 2.4 |
| Malik, Sheth, Kulkarni. *Coyote: A Compiler for Vectorizing Encrypted Arithmetic Circuits.* ASPLOS 2023 | DOI `10.1145/3582016.3582057` | identity only |
| Ali, Choi, Gipson, Gorantala, Kun, Legiest, Lim, Viand, Demissie, Zheng. *HEIR: A Universal Compiler for Homomorphic Encryption.* | arXiv 2508.11095v1 (14 Aug 2025) | noise-model description; testing support |
| Reed, Pierce. *Distance Makes the Types Grow Stronger: A Calculus for Differential Privacy.* ICFP 2010 | DOI `10.1145/1863543.1863568` | 4.1 |
| Gaboardi, Haeberlen, Hsu, Narayan, Pierce. *Linear Dependent Types for Differential Privacy.* POPL 2013 | DOI `10.1145/2429069.2429113` | 4.2 |
| Toro, Darais, Abuah, Near, Árquez, Olmedo, Tanter. *Contextual Linear Types for Differential Privacy.* ACM TOPLAS 45(2), 8:1–8:69, 2023 | DOI `10.1145/3589207` | identity and abstract-level description |
| Mironov. *On Significance of the Least Significant Bits for Differential Privacy.* CCS 2012 | DOI `10.1145/2382196.2382264` | mechanism form; quoted probabilities; snapping mechanism and Theorem 1 |
| Li, Micciancio, Schultz, Sorrell. *Securing Approximate Homomorphic Encryption Using Differential Privacy.* | IACR ePrint 2022/816 | abstract: decryption post-processing as a DP mechanism |
| Canonne, Kamath, Steinke. *The Discrete Gaussian for Differential Privacy.* | arXiv 2004.00010v6 | sampler provenance |
| Casacuberta, Shoemate, Vadhan, Wagaman. *Widespread Underestimation of Sensitivity in Differentially Private Libraries and How to Fix It.* CCS 2022 | arXiv 2207.10635v2 | 5.3 |
| Jin, McMurtry, Rubinstein, Ohrimenko. *Are We There Yet? Timing and Floating-Point Attacks on Differential Privacy Systems.* IEEE S&P 2022 | arXiv 2112.05307v4 | timing channel on discrete samplers (abstract only) |

### Executable probes

Environment: CPython 3.13.15, Linux x86_64, glibc 2.43; standard library
only. The BFV probe takes about one second; the DP probe about forty.

```bash
mkdir -p /tmp/probe && cd /tmp/probe
# save the two listings below under the names shown, then:
python3 toy_bfv_noise_and_slots_probe.py            # default seed 20261119; output in Findings 1.1
python3 toy_bfv_noise_and_slots_probe.py 3          # any other seed
curl -sSLO https://raw.githubusercontent.com/IBM/discrete-gaussian-differential-privacy/cb190d2a990a78eff6e21159203bc888e095f01b/discretegauss.py
sha256sum discretegauss.py                          # 6a19497ab5d77c6910a2b85b7fcf19ba6f83226910388e84ac3ecd23090b6c04
python3 dp_floating_point_probe.py discretegauss.py # output in Findings 5
```

Both probes are deterministic for a fixed seed. The DP probe executes the
upstream sampler file unmodified up to (not including) its
`import matplotlib` line, i.e. the samplers and the two exact-moment helper
functions, because the remainder of that file is plotting and test code.
Cross-seed ranges quoted in 1.1 come from running the BFV probe with seeds
1 through 8: fresh budget 116.1–116.8 bits; after 4096 additions
107.7–107.9; per-level consumption with relinearization 9.9–12.9; first
failing depth 10 or 11 with relinearization and 5 or 6 without.

`toy_bfv_noise_and_slots_probe.py`:

```python
#!/usr/bin/env python3
"""Toy BFV noise-budget and SIMD-slot probe (pure Python 3, standard library only).

NOT a secure or optimized implementation: ring degree n = 16, schoolbook
negacyclic multiplication, no relinearization, symmetric-key encryption.
Purpose: make three structural facts executable with exact integer/rational
arithmetic and a fixed seed.

  Part A  additive vs multiplicative consumption of the invariant noise budget,
          silent decryption failure, and aliasing of a key-holder budget estimate
  Part B  plaintext SIMD slots of Z_t[x]/(x^n+1): slot-wise product, the
          2 x n/2 hypercube, and which slot permutations Galois automorphisms give
  Part C  an automorphism applied to a ciphertext decrypts under the automorphed
          key with unchanged noise (hence a per-rotation key-switching key)
"""
import math
import random
from fractions import Fraction

N = 16                    # ring degree (power of two)
T = 257                   # plaintext modulus, prime, T = 1 mod 2N
Q = 1 << 128              # ciphertext modulus (2^128 = 1 mod 257, so q mod t = 1)
DELTA = Q // T
import sys
SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20261119
rng = random.Random(SEED)

# ------------------------------------------------------------ ring helpers
def polymul(a, b, mod=None):
    """Negacyclic product in Z[x]/(x^N+1) (optionally reduced mod `mod`)."""
    res = [0] * N
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            k = i + j
            if k < N:
                res[k] += ai * bj
            else:
                res[k - N] -= ai * bj
    return [c % mod for c in res] if mod else res

def polyadd(a, b, mod): return [(x + y) % mod for x, y in zip(a, b)]
def center(a, mod): return [((c + mod // 2) % mod) - mod // 2 for c in a]
def small_error(): return [sum(rng.getrandbits(1) for _ in range(20)) - sum(rng.getrandbits(1) for _ in range(20)) for _ in range(N)]
def automorph(a, g, mod=None):
    """a(x) -> a(x^g) in Z[x]/(x^N+1), g odd."""
    res = [0] * N
    for i, c in enumerate(a):
        e = (i * g) % (2 * N)
        if e < N:
            res[e] += c
        else:
            res[e - N] -= c
    return [c % mod for c in res] if mod else res

# ------------------------------------------------------------ toy BFV
S = [rng.choice((-1, 0, 1)) for _ in range(N)]            # ternary secret key

def encrypt(m):
    a = [rng.randrange(Q) for _ in range(N)]
    e = small_error()
    c0 = [(DELTA * mi - (asi + ei)) % Q for mi, asi, ei in zip(m, polymul(a, S, Q), e)]
    return [c0, a]

def phase(ct, key=None):
    """c_0 + c_1 s + c_2 s^2 + ... mod Q, centered."""
    key = S if key is None else key
    acc = [0] * N
    spow = [1] + [0] * (N - 1)
    for comp in ct:
        acc = polyadd(acc, polymul(comp, spow, Q), Q)
        spow = polymul(spow, key, Q)
    return center(acc, Q)

def decrypt(ct, key=None):
    return [int(round(Fraction(T * w, Q))) % T for w in phase(ct, key)]

def add(c, d):
    size = max(len(c), len(d))
    pad = lambda x: x + [[0] * N] * (size - len(x))
    return [polyadd(x, y, Q) for x, y in zip(pad(c), pad(d))]

def mul(c, d):
    """BFV tensor product without relinearization: round(t/q * (c (x) d)) mod q."""
    cc = [center(x, Q) for x in c]
    dd = [center(x, Q) for x in d]
    out = []
    for j in range(len(c) + len(d) - 1):
        acc = [0] * N
        for i in range(len(c)):
            if 0 <= j - i < len(d):
                acc = [x + y for x, y in zip(acc, polymul(cc[i], dd[j - i]))]
        out.append([int(round(Fraction(T * x, Q))) % Q for x in acc])
    return out

def true_budget(ct, m_true, key=None):
    """SEAL-style invariant noise budget -log2(2*||v||_inf), v = t/q*phase - m (mod t),
    computed against the KNOWN plaintext so that it stays meaningful after failure."""
    worst = Fraction(0)
    for w, mi in zip(phase(ct, key), m_true):
        v = Fraction(T * w, Q) - mi
        v -= T * round(v / T)                       # centered representative mod t
        worst = max(worst, abs(v))
    return -math.log2(2 * worst) if worst else float("inf")

def blind_budget(ct, key=None):
    """What a key holder can compute WITHOUT knowing m: distance of t/q*phase to Z."""
    worst = Fraction(0)
    for w in phase(ct, key):
        x = Fraction(T * w, Q)
        worst = max(worst, abs(x - round(x)))
    return -math.log2(2 * worst) if worst else float("inf")

# base-w relinearization key for s^2 (BFV "version 1" key switching)
W_BITS = 4
ELL = -(-128 // W_BITS)
S2 = polymul(S, S, Q)
EVK = []
for _i in range(ELL):
    _a = [rng.randrange(Q) for _ in range(N)]
    _e = small_error()
    _b = [((1 << (W_BITS * _i)) * s2 - (as_ + e)) % Q for s2, as_, e in zip(S2, polymul(_a, S, Q), _e)]
    EVK.append((_b, _a))

def relinearize(ct):
    """3-component ciphertext -> 2 components; adds sum_i digit_i * e_i to the phase."""
    c0, c1, c2 = ct
    for i, (b, a) in enumerate(EVK):
        digit = [(x >> (W_BITS * i)) & ((1 << W_BITS) - 1) for x in c2]
        c0 = polyadd(c0, polymul(digit, b, Q), Q)
        c1 = polyadd(c1, polymul(digit, a, Q), Q)
    return [c0, c1]

def squaring_chain(ct, m, b0, relin, extra_after_failure=1):
    cur_ct, cur_m, prev, failed = ct, m, b0, 0
    for depth in range(1, 12):
        cur_ct = mul(cur_ct, cur_ct)
        if relin:
            cur_ct = relinearize(cur_ct)
        cur_m = polymul(cur_m, cur_m, T)
        tb, bb = true_budget(cur_ct, cur_m), blind_budget(cur_ct)
        got = decrypt(cur_ct)
        ok = got == cur_m
        print(f"  depth {depth}: budget = {tb:7.1f} bits (consumed {prev - tb:5.1f}), components = {len(cur_ct):2d}, "
              f"correct: {str(ok):5s}, key-holder estimate = {bb:5.1f}")
        prev = tb
        if not ok:
            wrong = sum(1 for x, y in zip(got, cur_m) if x != y)
            well_formed = len(got) == N and all(0 <= x < T for x in got)
            print(f"    -> decrypt returned normally; result is a well-formed plaintext: {well_formed}; "
                  f"coefficients that differ from the true product: {wrong}/{N}")
            failed += 1
            if failed > extra_after_failure:
                break

def part_a():
    print(f"== Part A: invariant noise budget (toy BFV, n={N}, t={T}, q=2^{Q.bit_length() - 1}) ==")
    m = [rng.randrange(T) for _ in range(N)]
    ct = encrypt(m)
    b0 = true_budget(ct, m)
    print(f"fresh ciphertext:     budget = {b0:6.1f} bits, decrypts correctly: {decrypt(ct) == m}")
    for count in (1, 64, 4096):
        acc_ct, acc_m = ct, m
        for _ in range(count):
            other = [rng.randrange(T) for _ in range(N)]
            acc_ct = add(acc_ct, encrypt(other))
            acc_m = [(x + y) % T for x, y in zip(acc_m, other)]
        b = true_budget(acc_ct, acc_m)
        print(f"after {count:4d} additions: budget = {b:6.1f} bits (consumed {b0 - b:4.1f}), "
              f"correct: {decrypt(acc_ct) == acc_m}")
    print(f"repeated squaring WITH relinearization (base 2^{W_BITS}, {ELL} digits):")
    squaring_chain(ct, m, b0, relin=True)
    print("repeated squaring WITHOUT relinearization:")
    squaring_chain(ct, m, b0, relin=False, extra_after_failure=0)

# ------------------------------------------------------------ SIMD slots
def find_zeta():
    for g in range(2, T):                           # primitive 2N-th root of unity mod T
        z = pow(g, (T - 1) // (2 * N), T)
        if pow(z, N, T) == T - 1:
            return z
ZETA = find_zeta()
ROW0 = [pow(3, i, 2 * N) for i in range(N // 2)]    # exponents 3^i
ROW1 = [(2 * N - e) % (2 * N) for e in ROW0]        # exponents -3^i
EXPS = ROW0 + ROW1

def decode(poly): return [sum(c * pow(ZETA, e * i, T) for i, c in enumerate(poly)) % T for e in EXPS]
def encode(slots):
    """Inverse of `decode` by solving the 16x16 Vandermonde system mod T."""
    rows = [[pow(ZETA, e * i, T) for i in range(N)] + [s % T] for e, s in zip(EXPS, slots)]
    for col in range(N):
        piv = next(r for r in range(col, N) if rows[r][col])
        rows[col], rows[piv] = rows[piv], rows[col]
        inv = pow(rows[col][col], -1, T)
        rows[col] = [(x * inv) % T for x in rows[col]]
        for r in range(N):
            if r != col and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(x - f * y) % T for x, y in zip(rows[r], rows[col])]
    return [rows[i][N] for i in range(N)]

def part_b():
    print("== Part B: plaintext SIMD slots of Z_257[x]/(x^16+1) ==")
    print(f"primitive 32nd root of unity mod 257: zeta = {ZETA}; slot exponents row0={ROW0} row1={ROW1}")
    a = list(range(1, 17))
    b = [3] * 8 + [5] * 8
    pa, pb = encode(a), encode(b)
    print(f"encode/decode round trip: {decode(pa) == a}")
    print(f"ring product == slot-wise product: {decode(polymul(pa, pb, T)) == [(x * y) % T for x, y in zip(a, b)]}")
    print(f"ring sum     == slot-wise sum:     {decode(polyadd(pa, pb, T)) == [(x + y) % T for x, y in zip(a, b)]}")
    print(f"slots            : {a}")
    r3, r31 = decode(automorph(pa, 3, T)), decode(automorph(pa, 31, T))
    print(f"after x -> x^3   : {r3}")
    print(f"  equals 'each row of 8 rotated left by one': {r3 == a[1:8] + a[0:1] + a[9:16] + a[8:9]}")
    print(f"after x -> x^31  : {r31}")
    print(f"  equals 'the two rows swapped': {r31 == a[8:] + a[:8]}")
    perms = set()
    for g in range(1, 2 * N, 2):
        perms.add(tuple(decode(automorph(pa, g, T))))
    print(f"distinct slot permutations reachable by a single automorphism: {len(perms)} "
          f"of 16! = {math.factorial(16)}")
    cyc = a[1:] + a[:1]
    print(f"full 16-cycle (1,2,...,16)->(2,...,16,1) is a single automorphism: {tuple(cyc) in perms}")
    return pa

def part_c(pa):
    print("== Part C: automorphism on a ciphertext ==")
    ct = encrypt(pa)
    g = 3
    rot = [automorph(comp, g, Q) for comp in ct]
    s_g = automorph(S, g)
    want = automorph(pa, g, T)
    print(f"budget before: {true_budget(ct, pa):.1f} bits; after x->x^3 under key s(x^3): "
          f"{true_budget(rot, want, key=s_g):.1f} bits")
    print(f"decrypts to rotated slots under s(x^3): {decode(decrypt(rot, key=s_g)) == decode(want)}")
    print(f"decrypts to rotated slots under original s: {decode(decrypt(rot)) == decode(want)}")

if __name__ == "__main__":
    part_a()
    part_c(part_b())
```

`dp_floating_point_probe.py`:

```python
#!/usr/bin/env python3
"""Differential-privacy numeric-soundness probe (pure Python 3, standard library only).

  Part 1  porosity of the textbook binary64 Laplace mechanism  mu + s*lam*ln(U),
          U uniform on the 2^-53 grid (the least-significant-bits attack surface)
  Part 2  exact rational-arithmetic discrete Laplace / discrete Gaussian samplers
          (reference implementation, loaded from a pinned upstream file given as argv[1])
  Part 3  realised sensitivity of naive finite-precision summation vs the idealised bound

Usage: python3 dp_floating_point_probe.py /path/to/discretegauss.py
"""
import hashlib
import types
import math
import random
import struct
import sys
from fractions import Fraction

# ---------------------------------------------------------------- Part 1
def naive_laplace(mu, lam, k, sign):
    """Textbook mechanism: U = k / 2^53 (exact in binary64), k in 1..2^53."""
    return mu + sign * lam * math.log(k * 2.0 ** -53)

def window_enumeration(lam, lo, width):
    """Enumerate EVERY grid point k whose output can land in [lo, lo+width) for
    mu = 0 and mu = 1 (sign = -1 branch, the only branch reaching y > mu)."""
    hi = lo + width
    reach = {}
    for mu in (0.0, 1.0):
        k_min = int(math.exp(-(hi - mu) / lam) * 2 ** 53) - 4096
        k_max = int(math.exp(-(lo - mu) / lam) * 2 ** 53) + 4096
        outs = {}
        for k in range(max(1, k_min), min(2 ** 53, k_max) + 1):
            y = naive_laplace(mu, lam, k, -1)
            if lo <= y < hi:
                outs[y] = outs.get(y, 0) + 1
        reach[mu] = outs
    ulp = math.ulp(lo)
    n_doubles = round(width / ulp)
    s0, s1 = set(reach[0.0]), set(reach[1.0])
    mass0 = sum(reach[0.0].values())
    mass1 = sum(reach[1.0].values())
    only0 = sum(c for y, c in reach[0.0].items() if y not in s1)
    only1 = sum(c for y, c in reach[1.0].items() if y not in s0)
    print(f"  window [{lo}, {lo}+2^{int(math.log2(width))}), lam={lam}: {n_doubles} binary64 values")
    print(f"    reachable when f(D)=0 : {len(s0):8d} ({len(s0) / n_doubles:6.1%})  from {mass0} grid points")
    print(f"    reachable when f(D)=1 : {len(s1):8d} ({len(s1) / n_doubles:6.1%})  from {mass1} grid points")
    print(f"    reachable under both  : {len(s0 & s1):8d};  under neither: {n_doubles - len(s0 | s1)}")
    print(f"    P[output identifies f(D)=0 | f(D)=0, output in window] = {only0 / mass0:.4f}")
    print(f"    P[output identifies f(D)=1 | f(D)=1, output in window] = {only1 / mass1:.4f}")

def in_support(y, mu, lam):
    """Is y = naive_laplace(mu, lam, k, sign) for some k in 1..2^53, sign in {+1,-1}?
    Bisection on k (output is monotone in k for fixed sign), then a +-16 neighbourhood scan."""
    for sign in (1, -1):
        lo, hi = 1, 2 ** 53
        while lo < hi:
            mid = (lo + hi) // 2
            v = naive_laplace(mu, lam, mid, sign)
            if (v < y) if sign == 1 else (v > y):
                lo = mid + 1
            else:
                hi = mid
        for k in range(max(1, lo - 16), min(2 ** 53, lo + 16) + 1):
            if naive_laplace(mu, lam, k, sign) == y:
                return True
    return False

def sampled_smoking_guns(lam, n, rng):
    stats = {}
    for mu, other in ((0.0, 1.0), (1.0, 0.0)):
        self_ok = guns = 0
        for _ in range(n):
            k = rng.getrandbits(53) + 1
            sign = 1 if rng.getrandbits(1) else -1
            y = naive_laplace(mu, lam, k, sign)
            self_ok += in_support(y, mu, lam)
            guns += not in_support(y, other, lam)
        stats[mu] = (self_ok, guns)
    print(f"  lam={lam:<8.6g} n={n}: self-test (own outputs found in own support) "
          f"{stats[0.0][0]}/{n} and {stats[1.0][0]}/{n}")
    print(f"    outputs of f(D)=0 that are impossible under f(D)=1: {stats[0.0][1] / n:.3f}")
    print(f"    outputs of f(D)=1 that are impossible under f(D)=0: {stats[1.0][1] / n:.3f}")

def low_bit_structure(lam, n, rng):
    """Among outputs landing in (0, 1): how many are integer multiples of 2^-53?"""
    for mu in (0.0, 1.0):
        inside = multiples = 0
        for _ in range(n):
            y = naive_laplace(mu, lam, rng.getrandbits(53) + 1, 1 if rng.getrandbits(1) else -1)
            if 0.0 < y < 1.0:
                inside += 1
                multiples += (y * 2.0 ** 53).is_integer()
        print(f"  lam={lam}: f(D)={int(mu)} outputs in (0,1): {inside}; "
              f"integer multiples of 2^-53: {multiples} ({multiples / inside:.4f})")

def part1():
    print("== Part 1: binary64 Laplace mechanism  y = mu + s*lam*ln(k/2^53) ==")
    window_enumeration(1.0, 2.0, 2.0 ** -32)
    window_enumeration(1.0, 3.0, 2.0 ** -32)
    rng = random.Random(20261119)
    for lam in (1.0, 2.0, 1.0 / 0.3):
        sampled_smoking_guns(lam, 20000, rng)
    low_bit_structure(1.0, 200000, random.Random(7))

# ---------------------------------------------------------------- Part 2
class CountingRng:
    def __init__(self, seed):
        self.rng, self.calls = random.Random(seed), 0
    def randrange(self, m):
        self.calls += 1
        return self.rng.randrange(m)

def part2(path):
    print("== Part 2: exact discrete samplers (pinned reference implementation) ==")
    print(f"  file sha256 = {hashlib.sha256(open(path, 'rb').read()).hexdigest()}")
    # The upstream file imports matplotlib for its plotting/test section; execute only the
    # unmodified prefix that precedes that import (samplers + normalizing_constant + variance).
    source = open(path).read()
    namespace = {"__name__": "discretegauss_prefix"}
    exec(compile(source[:source.index("import matplotlib")], path, "exec"), namespace)
    dg = types.SimpleNamespace(**namespace)
    n = 100000
    scale = Fraction(2)                      # eps = 1/2 for a sensitivity-1 integer query
    rng = CountingRng(1)
    hist, calls_by_mag = {}, {}
    for _ in range(n):
        before = rng.calls
        x = dg.sample_dlaplace(scale, rng=rng)
        assert type(x) is int
        hist[x] = hist.get(x, 0) + 1
        calls_by_mag.setdefault(min(abs(x), 6), []).append(rng.calls - before)
    s = float(scale)
    norm = (math.exp(1 / s) - 1) / (math.exp(1 / s) + 1)
    dev = max(abs(hist.get(x, 0) / n - norm * math.exp(-abs(x) / s)) for x in range(-12, 13))
    print(f"  discrete Laplace(scale=2): {n} samples, all Python ints; "
          f"max |empirical - exact pmf| on [-12,12] = {dev:.4f} (binomial 3-sigma at x=0 = "
          f"{3 * math.sqrt(norm * (1 - norm) / n):.4f})")
    ratio = max(math.exp(-abs(x) / s) / math.exp(-abs(x - 1) / s) for x in range(-50, 51))
    print(f"  pmf formula ratio max over x in [-50,50] of P[x]/P[x-1] = {ratio:.6f}; e^(1/scale) = {math.exp(1 / s):.6f}; "
          f"observed sample range = [{min(hist)}, {max(hist)}]")
    print("  uniform draws consumed per sample, grouped by |output| (6 means >= 6):")
    for mag in sorted(calls_by_mag):
        c = calls_by_mag[mag]
        print(f"    |x|={mag}: count={len(c):6d} mean={sum(c) / len(c):6.2f} min={min(c):2d} max={max(c):3d}")
    rng = CountingRng(2)
    xs = [dg.sample_dgauss(Fraction(4), rng=rng) for _ in range(n)]
    mean = sum(xs) / n
    var = sum(x * x for x in xs) / n - mean * mean
    print(f"  discrete Gaussian(sigma^2=4): mean={mean:+.4f} var={var:.4f} "
          f"(module's variance(4) = {dg.variance(Fraction(4)):.4f}); "
          f"uniform draws per sample: mean={rng.calls / n:.2f}")

# ---------------------------------------------------------------- Part 3
def f32(x): return struct.unpack("f", struct.pack("f", x))[0]

def seq_sum(xs, rnd=lambda z: z):
    acc = 0.0
    for x in xs:
        acc = rnd(acc + x)
    return acc

def part3():
    print("== Part 3: realised vs idealised sensitivity of a bounded sum (records in [0, 1]) ==")
    # (a) binary64, left-to-right summation
    m = 2 ** 20
    v = math.nextafter(2.0 ** -53, 1.0)          # just above half an ulp of 1.0
    d, d_removed = [1.0] + [v] * m, [v] * m       # neighbours: remove the record 1.0
    sd, sr = seq_sum(d), seq_sum(d_removed)
    print(f"  (a) binary64, n={m + 1}: sum(D)={sd!r} sum(D')={sr!r}")
    print(f"      realised difference sum(D) - sum(D') = 1 + {float(Fraction(sd) - Fraction(sr) - 1):.3e} "
          f"(exact rational arithmetic on the two computed sums); idealised sensitivity = 1")
    print(f"      true real sum of D = 1 + {float(Fraction(v) * m):.3e}; computed sum(D) - 1 = {sd - 1.0:.3e} "
          f"(each tiny addend was rounded up to a full ulp)")
    print(f"      same records, other orders: ascending sum(D) - 1 = {seq_sum(sorted(d)) - 1.0:.3e}, "
          f"math.fsum(D) - 1 = {math.fsum(d) - 1.0:.3e}")
    # (b) binary32 emulated by rounding every partial sum to single precision
    m = 2 ** 22
    v = f32(2.0 ** -24 * (1 + 2.0 ** -23))        # just above half an ulp of 1.0f
    d, d_removed = [1.0] + [v] * m, [v] * m
    sd, sr = seq_sum(d, f32), seq_sum(d_removed, f32)
    print(f"  (b) binary32, n={m + 1}: sum(D)={sd!r} sum(D')={sr!r} realised |difference|={sd - sr!r} "
          f"vs idealised 1  (excess {sd - sr - 1.0:+.4f})")
    # (c) 64-bit two's-complement wraparound, records in [0, 2^62]
    def wrap(z): return (z + 2 ** 63) % 2 ** 64 - 2 ** 63
    d, d_removed = [2 ** 62, 2 ** 62], [2 ** 62]
    sd, sr = wrap(sum(d)), wrap(sum(d_removed))
    print(f"  (c) int64 wraparound, records in [0, 2^62]: sum(D)={sd} sum(D')={sr} "
          f"|difference| = {abs(sd - sr) // 2 ** 62} * 2^62 vs idealised 1 * 2^62")

if __name__ == "__main__":
    part1()
    part2(sys.argv[1])
    part3()
```

## Revalidation

Cheapest discriminating checks, in order of cost:

1. **Library statements (seconds each).** `grep -n "IND-CPA" ` in
   `zama-ai/concrete` `docs/explanations/security.md` and in `zama-ai/tfhe-rs`
   `tfhe/docs/getting-started/security-and-cryptography.md`; read the
   `@par Warning` block of `invariant_noise_budget` in SEAL's `decryptor.h`.
   A changed default failure probability or threat model changes the table
   in Findings 3.
2. **Concrete defaults (seconds).** `grep -n "DEFAULT_.*P_ERROR"
   frontends/concrete-python/concrete/fhe/compilation/configuration.py`.
3. **HEIR's soundness statement and model list (seconds).** Re-read
   `docs/content/en/docs/Design/noise.md` and the `description` of
   `GenerateParamBGV` in `lib/Transforms/GenerateParam/GenerateParam.td`. If
   the "experimental / no guarantee" paragraph is removed, look for what
   replaced it (a proof, a validation suite) before updating 2.2 and 2.5.
4. **EVA (seconds).** `grep -rni noise eva/ python/ README.md | wc -l`
   (expected: 1) and re-read `levels_checker.h` for `assert` versus `throw`.
5. **BFV shape (one second).** Rerun `toy_bfv_noise_and_slots_probe.py` with
   several seeds; the discriminating facts are the roughly constant
   per-level cost with relinearization, the rising cost without it, the
   non-negative key-holder estimate at the failing depth, and "16 of 16!".
   To test transfer to real parameters, repeat the measurement with a
   production library's noise-budget diagnostic on a squaring chain.
6. **Laplace porosity (forty seconds).** Rerun the DP probe on the target
   platform. The control line must read `20000/20000` twice per λ; if it
   does not, the platform's `log` violates the monotonicity assumption of
   the membership test and the percentages are unreliable. To evaluate a
   particular library's sampler, replace `naive_laplace` with a call to it
   and keep the exhaustive-window enumeration.
7. **Sampler provenance (seconds).** Compare the SHA-256 above; check that
   OpenDP's `cks20/mod.rs` header still cites the same upstream commit.
8. **Sum sensitivity (seconds).** Part 3 of the DP probe; for another
   summation routine, substitute it for `seq_sum` and compare the realised
   difference with the library's declared sensitivity plus relaxation.

A passing probe establishes only what it checks: the toy model says nothing
about a production parameter set's margins, and a clean porosity result for
one sampler says nothing about sensitivity or timing.
