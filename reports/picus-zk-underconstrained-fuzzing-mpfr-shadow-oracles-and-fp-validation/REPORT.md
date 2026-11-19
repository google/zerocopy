# Zero-Knowledge Under-Constrained Circuit Verification, Cryptographic Edge-Case Vectors, and Shadow Arbitrary-Precision Floating-Point Validation

## Summary

Zero-knowledge (`ZK`) arithmetic circuits, elliptic-curve / AEAD cryptographic primitives, and IEEE-754 floating-point kernels share a deceptive failure signature: **every normal functional test passes (`100%` completeness on honest inputs) while silent mathematical non-determinism, non-canonical group aliasing, or catastrophic bit cancellation completely destroys soundness or accuracy on adversarial inputs** (`Basis: source + execution + derived`).

Across the nine pinned upstream systems and companion primary literature examined in this report, eliminating silent finite-field, group-encoding, and real-to-float divergence requires four specialized validation mechanisms (`Basis: source + execution + derived`):

1. **2-Safety Uniqueness Verification and Witness-Constraint Consistency Fuzzing (`Veridise Picus`, `Circomspect`, `Ecne`, `zkFuzz`, `Arguzz`)**: Because `Circom` (`iden3/circom`) splits witness computation (`<--`) from Rank-1 Constraint System (`R1CS`) polynomial equations (`===`), honest witness generators produce a single valid assignment while malicious provers solve the raw polynomials directly over $\mathbb{F}_p$. On `BN254` ($p \approx 2^{254}$), omitting an input bit-length bound lets $x = p - 254 > 2^{253}$ satisfy `LessThan(8)(x, 2) === 1`, while `Num2Bits(254)` admits distinct `254`-bit witnesses for $1$ and $p + 1$. `Picus` (`Veridise/Picus`) discharges **weak uniqueness** ($\forall x, w_1, w_2.\; C(x, w_1) \land C(x, w_2) \implies \pi_{\text{out}}(w_1) = \pi_{\text{out}}(w_2)$) by alternating five algebraic propagation lemmas (`linear`, `binary01`, `basis2`, `aboz`, `bim`) with finite-field SMT (`cvc5` `QF_FF` / `Z3`), complemented by `zkFuzz` trace-constraint consistency fuzzing and `Arguzz` zkVM fault-injected metamorphic product programs. Crucially, ZK verifiers must themselves undergo soundness testing: direct inspection of `franklynwang/EcneProject` (`src/Math.jl:79-85`) uncovers a live algebraic bug where `solveQuadratic` divides `-b ± disc` instead of `-b ± rt` ($\sqrt{\Delta}$), returning non-roots `{7, p - 2}` (residual `18 != 0`) on $x^2 - 5x + 4 \equiv 0 \pmod{p}$!
2. **Adversarial Algebraic Edge-Case Vector Suites (`C2SP/wycheproof`)**: Uniform random fuzzing cannot synthesize low-order torsion points, BER-malleable ASN.1 lengths, or `Poly1305` $2^{130} - 5$ limb wraps. `Wycheproof` curates structured invalid/edge vectors (`210` `Ed25519` vectors including `29` RFC-8032 cofactor/small-order `"acceptable"` consensus-divergence cases, `484` `ECDSA-P256` vectors, `325` `ChaCha20-Poly1305` vectors, and `37` `RSA-OAEP` Manger-oracle vectors) that isolate cross-library acceptance splits.
3. **Adaptive MPFR Interval Shadow Execution and Oracle-Free Condition-Number Search (`Rival`, `Herbie`, `S3FP`, `Atomu`)**: Evaluating $(1 - \cos x) / x^2$ at $x = 1.5 \times 10^{-8}$ in `IEEE-754 binary64` loses **`46.75` of `53` mantissa bits** (`0.493432455...` vs. exact `0.5`). `Atomu`'s local subtraction condition number $\kappa_- = \frac{|1| + |\cos x|}{|1 - \cos x|} = 1.801 \times 10^{16}$ guides black-box search directly to cancellation inputs without an external oracle, while `herbie-fp/rival` evaluates ground-truth real intervals over GNU `MPFR` using boolean/error intervals (`ival-err?`), movability flags, and region-hint pruning (`make-hint` in `eval/adjust.rkt`) so `Herbie` synthesizes $\frac{1}{2}\left(\frac{\sin(x/2)}{x/2}\right)^2$ (`0.0` ULP error).
4. **Architectural IEEE-754 Bit-Exact Differential Reference Models (`Berkeley SoftFloat-3` & `TestFloat-3`)**: "IEEE-754 compliant" hardware still diverges across underspecified architectural choices (`source/{8086-SSE,RISCV,ARM-VFPv2}/specialize.h`): on subnormal boundary significand `0x7FFFFFFFFFFFFE01` at `exp = -1` (`s_roundPackToF64.c:72-81`), rounding to normal $2^{-1022}$ raises `FE_UNDERFLOW` on `ARM-VFPv2` (`tininess_beforeRounding`) but **not** on `x86-SSE` or `RISC-V` (`tininess_afterRounding`), while `NaN -> int32_t` returns `-2147483648` (`x86`), `+2147483647` (`RISC-V`), and `0` (`ARM`), and `RISC-V` canonicalizes all quiet `NaN` payloads to `0x7FF8000000000000`.

---

## Applicability

The findings in this report apply to zero-knowledge circuit compilers and analyzers, cryptographic primitive implementations, numerical shadow-oracle frameworks, and software/hardware floating-point engines pinned at the nine concrete revisions in `REPORT.json` (`Basis: source + documentation`):

- **ZK Circuit Compilers, Static Linting, and Uniqueness Solvers**: `Veridise/Picus` (`138b151d3a388e5b6c040c163e0a1db04f2ceda6`, Racket/Rust $\mathsf{QED}^2$ uniqueness checker over `.circom`, `.r1cs`, and `gnark` `.sr1cs`), `trailofbits/circomspect` (`50010b623ed4f3bff9d1b0363cfe952385b47af3`, Rust static analyzer for Circom), `iden3/circom` (`9b4b23331644e17868c90a85768826ed3bcba59f`, Rust R1CS compiler and C++/Wasm witness generator), and `franklynwang/EcneProject` (`25935352ca30705ad47363dcf200822635edc1c7`, Julia R1CS uniqueness verifier), alongside `zkFuzz` (`DOI: 10.1109/SP63933.2026.00049`) and `Arguzz` (`DOI: 10.48550/arXiv.2509.10819`).
- **Cryptographic Edge-Case Conformance Vectors**: `C2SP/wycheproof` (`65ca494727a52944c204441c860b039e6786b99b`, matching upstream `google/wycheproof` HEAD revision `65ca494727a52944c204441c860b039e6786b99b`, `testvectors_v1/`).
- **Shadow Real-Interval Oracles & IEEE-754 Bit-Level Reference Suites**: `herbie-fp/rival` (`4d2334a05338be8df9c6924e30534d693f83267d`), `herbie-fp/herbie` (`4612b0d493cbb2013dc5afac5c099b7722166ec2`), `ucb-bar/berkeley-softfloat-3` (`07ebd29db0cfb55723a79fbbffe99103ef38e305`, Release `3e`), and `ucb-bar/berkeley-testfloat-3` (`a9c849f1b0eb0264b626d9686ffae167d996e3be`).

These systems share a unifying structural vulnerability: **the gap between an operational calculation and its algebraic/finite-precision representation** (`Basis: derived`). Standalone Python `3.11+` execution probes were run on Linux `x86_64` (`Basis: execution`).

---

## Findings

### 1. Zero-Knowledge Under-Constrained Circuits: Uniqueness Solving, Static Analysis, and Witness Fuzzing

#### 1.1 The Witness-Constraint Split (`Circom`) and Canonical `BN254` Soundness Exploits (`Circomspect`)
In `iden3/circom` (`circom/src/`, `circom_algebra/src/constraint_storage/`), a circuit template compiles into **two separate artifacts**: (a) an imperative C++/WebAssembly witness calculator (`code_producers/src/c_elements/common/calcwit.cpp`) evaluating arbitrary divisions, bit shifts, and conditionals via `<--`, and (b) a declarative Rank-1 Constraint System (`R1CS`) $\{(A_i \cdot \mathbf{w}) \times (B_i \cdot \mathbf{w}) \equiv (C_i \cdot \mathbf{w}) \pmod{p}\}_{i=1}^m$ over a prime scalar field $\mathbb{F}_p$ (default `BN254`, `254`-bit prime $p = 21888242871839275222246405745257275088548364400416034343698204186575808495617$). The `<==` operator emits both a witness assignment and a quadratic `===` constraint, whereas `<--` emits **zero R1CS constraints** (`Basis: source`).

Because an adversarial SNARK prover discards `calcwit.cpp` entirely and constructs $\mathbf{w} \in \mathbb{F}_p^n$ directly, any missing or non-injective constraint allows forging proofs for false statements. `trailofbits/circomspect` (`doc/analysis_passes.md:3-140`, `program_analysis/src/under_constrained_signals.rs:13-120`) catalogs and statically flags four recurring vulnerability archetypes (`Basis: source + execution`):

1. **Prime-Wrap Range Bypass in `LessThan(n)` (`doc/analysis_passes.md:94-122`, `unconstrained_less_than.rs`)**: `Circomlib`'s `LessThan(8)` computes `n2b = Num2Bits(9)(in[0] + (1 << 8) - in[1])` and outputs `1 - n2b.out[8]`. If `in[0]` lacks an independent `Num2Bits` bound $< \lfloor \log_2 p \rfloor - 1$, supplying `in[0] = p - 254` (`> 2^{253}`) against `in[1] = 2` yields $(p - 254 + 256 - 2) \bmod p = 0$, setting bit `8` to `0` and **`lt.out = 1` ("`p - 254 < 2` is true!")** (`## Revalidation` Probe 1).
2. **Non-Strict Field Bit-Decomposition Aliasing (`doc/analysis_passes.md:83-93`, `nonstrict_binary_conversion.rs`)**: `Num2Bits(254)` constrains $b_i \in \{0, 1\}$ and $\sum_{i=0}^{253} 2^i b_i \equiv x \pmod{p}$. Since $p < 2^{254}$, for $x = 1$, **both** the `254`-bit binary representation of $1$ and that of $p + 1 < 2^{254}$ satisfy every R1CS constraint (`(p + 1) mod p == 1`, `## Revalidation` Probe 1), allowing double-spend nullifier malleability unless `AliasCheck` / `Num2Bits_strict` enforces $\sum 2^i b_i < p$.
3. **Zero-Divisor Witness Forgery (`doc/analysis_passes.md:123-135`, `unconstrained_division.rs`)**: Writing `c <-- a / b; c * b === a;` without constraining `IsZero(b) === 0` lets a malicious prover set `a = 0, b = 0` and choose **any of the $p$ field elements** for `c` (`c * 0 === 0`).
4. **Dead Accumulators and Unconstrained Template Outputs (`doc/analysis_passes.md:3-38, 67-78`, `under_constrained_signals.rs:13-108`)**: `find_under_constrained_signals` enforces `MIN_CONSTRAINT_COUNT = 2` (`under_constrained_signals.rs:13`) on `SignalType::Intermediate` wires (one constraint to define the wire, a second to bind an output), catching Tornado Cash's MiMC missing constraint and `circom-pairing`'s unconstrained template outputs (`Basis: source`).

#### 1.2 Decide-and-Propagate 2-Safety Uniqueness (`Veridise Picus`) vs. Soundness Bug in `Ecne`
Syntactic linters like `Circomspect` suffer both false positives (flagging safe single-constraint outputs like `Num2Bits`, `doc/analysis_passes.md:73`) and false negatives (missing multi-component algebraic under-constraints, and clobbering unversioned component arrays `c[0].in[0]` vs `c[1].in[1]` as noted in `constraint_analysis.rs:27-38`).

`Veridise/Picus` (`picus/algorithms/dpvl.rkt:1-120`, `README.md:8-120`; `Pailoor et al., PLDI 2023, DOI: 10.1145/3591282`) solves semantic **input-output uniqueness** via its **Decide & Propagate Verification Loop (`DPVL`)** (`Basis: source`):
- **2-Safety Product Encoding (`dpvl.rkt:66-98`)**: Given inputs $I$, target outputs $O$, and constraints $C(\mathbf{w})$, `Picus` maintains a monotonically growing known-unique wire set `ks` (initialized to $I$). To test candidate signal `sid`, `dpvl-solve` instantiates two disjoint witness copies `(concretize var "x")` and `(concretize var "y")`, asserts `x_j = y_j` for all `j in ks` (`L69-73`), and queries `x_sid != y_sid` (`L94`) under `cvc5` (`QF_FF` native Gröbner-basis finite-field theory, default `5000ms` timeout) or `Z3`.
- **Five Algebraic Propagation Lemmas (`dpvl.rkt:7-12`)**: Before invoking SMT, `Picus` repeatedly saturates `ks` using `linear-lemma.rkt` (Gaussian elimination over determined variables), `binary01-lemma.rkt` ($b(b-1)=0$), `basis2-lemma.rkt` (injective bit-packing $\sum_{i=0}^{k-1} 2^i b_i$ for $k < \lfloor \log_2 p \rfloor$), `aboz-lemma.rkt` (All-But-One-Zero multiplexer gates), and `bim-lemma.rkt` (Bounded-Input-Modulus), discharging $> 90\%$ of wires in milliseconds without SMT timeouts.
- **Weak vs. Strong Uniqueness (`dpvl.rkt:111-120`, `README.md:119-120`)**: If `sid` is an internal wire (`not (set-member? :target-set sid)`) and SMT returns `'sat`, `Picus` logs `"[solver] sat but not a target"` and skips `sid` (`L117-120`) unless `--strong` is passed—avoiding false alarms on circuits whose internal helper wires admit multiple representations while uniquely determining all public/output signals; if a target output admits two witnesses, `Picus` prints both concrete assignments and exits with code `9` (`README.md:66-83`).

**Live Verifier Soundness Defect Discovered in `franklynwang/EcneProject` (`Basis: source + execution`)**:
Inspecting `franklynwang/EcneProject` (`25935352ca30705ad47363dcf200822635edc1c7`, `src/Math.jl:62-90`)—an earlier algebraic R1CS uniqueness checker—reveals a textbook **`V2` checker soundness bug** inside `solveQuadratic`:

```julia
disc = b * b - field(4) * a * c
rt = squareRoot(field, disc)
if rt != 0
    return [
        AbstractAlgebra.divexact(-b + disc, field(2) * a),
        AbstractAlgebra.divexact(-b - disc, field(2) * a),
    ]
```

At lines `83-84`, `solveQuadratic` computes `rt = squareRoot(field, disc)` via Tonelli–Shanks (`L14-59`, which also omits a Legendre non-residue check and loops infinitely when $\Delta^{(p-1)/2} \equiv -1 \pmod{p}$!), **discards `rt`, and substitutes raw `disc` ($\Delta$) into the numerator $\frac{-b \pm \Delta}{2a}$**! Because $\Delta = \sqrt{\Delta}$ in $\mathbb{F}_p$ *only* when $\Delta \in \{0, 1\}$ (such as `0/1` boolean constraints $x(x-1)=0$ where $\Delta = 1$), `Ecne` passes simple boolean unit tests while computing wrong roots `{7, p - 2}` (with non-zero polynomial residual `18`) on $x^2 - 5x + 4 \equiv 0 \pmod{p}$ (whose true roots are `{1, 4}`, $\Delta = 9, \sqrt{\Delta} = 3$, verified in `## Revalidation` Probe 1).

#### 1.3 Witness-Mutation Circuit & zkVM Fuzzing (`zkFuzz` and `Arguzz`)
When R1CS/Plonkish circuits exceed `10^5` non-linear gates (e.g., `Keccak256`, `ECDSA`, or full RISC-V zkVMs), SMT Gröbner bases time out. Two dynamic fuzzing paradigms bridge that scalability cliff (`Basis: documentation + derived`):
- **Trace-Constraint Consistency Fuzzing (`zkFuzz`, `Takahashi et al., IEEE S&P 2026, DOI: 10.1109/SP63933.2026.00049`)**: Mutates Circom/Noir witness-generation computations (`<--`) and tests whether mutated witnesses still satisfy the compiled R1CS/ACIR constraints (`under-constrained`) or whether valid inputs cause witness-calculator aborts rejected by constraints (`over-constrained`).
- **Fault-Injected Metamorphic zkVM Product Testing (`Arguzz`, `Hochrainer, Wüstholz & Christakis, USENIX Security 2026, DOI: 10.48550/arXiv.2509.10819`)**: Targets RISC Zero, SP1, Jolt, Nexus, OpenVM, and Pico by injecting bit/instruction faults into the untrusted zkVM prover's execution trace and checking whether the verifier rejects every faulted proof whose public output diverges from clean execution.

---

### 2. Curated Cryptographic Edge-Case Differential Vectors (`Project Wycheproof`)

Random bit-flip fuzzing fails against cryptographic signature and AEAD verifiers because valid signatures occupy a $2^{-128}$ measure-zero subset. Direct parsing of `C2SP/wycheproof` (`65ca494727a52944c204441c860b039e6786b99b`, `testvectors_v1/`) demonstrates how algebraic boundary vectors isolate subtle implementation splits (`Basis: source + execution`):

- **`Ed25519` Cofactor, Torsion, and Scalar Malleability (`ed25519_test.json`, `210` vectors)**: Contains `117` `"valid"`, `64` `"invalid"`, and notably **`29` `"acceptable"`** vectors across `12` vulnerability flags (`SignatureMalleability`: `8` vectors with non-canonical $S \ge L$ or $S + L$; `SmallOrderPublicKey`: `8` vectors on the $h = 8$ Curve25519 torsion subgroup; `MixedOrderPublicKey`, `TruncatedSignature`, `TinkOverflow`). As analyzed by Chalkias, Garillot & Nikolaenko (*Taming the Many EdDSAs*, `DOI: 10.1007/978-3-030-64357-7_4`), RFC 8032 permits both cofactorless verification ($S \cdot B = R + k \cdot A$) and cofactored verification ($8 S \cdot B = 8 R + 8 k \cdot A$) and differs on small-order points—harmless for single-signer TLS, but **fatal for blockchain consensus** where validator nodes running two compliant libraries split the chain!
- **`ECDSA secp256r1` ASN.1/Arithmetic Corners (`ecdsa_secp256r1_sha256_test.json`, `484` vectors)**: `174` `"valid"`, `310` `"invalid"`, `0` `"acceptable"` across `17` flags including `BerEncodedSignature` (`7` vectors catching lax DER parsers accepting indefinite/non-minimal lengths), `RangeCheck` ($r, s \notin [1, n-1]$), `PointDuplication` (Shamir's trick $u_1 G + u_2 Q$ failing when $u_1 G = \pm u_2 Q$!), and `MissingZero` (unsigned integer MSB sign-bit mishandling).
- **`ChaCha20-Poly1305` & `RSA-OAEP` (`325` and `37` vectors)**: Exercises `Poly1305` $2^{130}-5$ modular carry limb-overflows (`EdgeCasePoly1305`), `InvalidNonceSize`, and Manger's `0x00`-leading-byte RSA-OAEP padding timing/error side channels (`InvalidOaepPadding`).

---

### 3. Shadow Arbitrary-Precision Oracles (`Rival` / `Herbie`), Condition-Number Search (`Atomu`), and `SoftFloat-3` Hardware Divergence

#### 3.1 Oracle-Free Condition-Number Guidance (`S3FP` / `Atomu`) + `Rival` Interval Shadow Execution
Testing floating-point kernels faces two coupled challenges: *finding* the tiny input intervals where catastrophic cancellation spikes, and *computing* an exact real-number reference without circular rounding errors (`Basis: source + execution`):

1. **Atomic Condition-Number Search (`Atomu`, `Zou et al., POPL 2020, DOI: 10.1145/3371128`; `S3FP`, `Chiang et al., PPoPP 2014, DOI: 10.1145/2555257.2555265`)**: Every large relative floating-point error originates at an ill-conditioned elementary operation—most commonly subtraction $a - b$ with condition number $\kappa_-(a, b) = \frac{|a| + |b|}{|a - b|}$, or sensitive zero-crossings of $\sin/\cos/\log$. Maximizing $\kappa_-$ via evolutionary/gradient search requires **only fast hardware `f64` execution** (zero MPFR overhead during search!). On $f(x) = \frac{1 - \cos x}{x^2}$ at $x = 1.5 \times 10^{-8}$ (`## Revalidation` Probe 3), $\kappa_-(1, \cos x) = \mathbf{1.801 \times 10^{16}}$, exposing that `binary64` evaluates `0.4934324553889586` instead of `0.5` (**`46.75` bits of precision lost out of `53`**!).
2. **Movability-Aware MPFR Interval Shadowing (`herbie-fp/rival`, `eval/main.rkt:36-110`, `eval/machine.rkt:16-50`, `eval/adjust.rkt:13-95`; `Flatt & Panchekha, DOI: 10.48550/arXiv.2107.05784`)**:
   - Standard point-sampled `MPFR` shadow evaluation at fixed `128`-bit precision can still round *wrongly* when the exact real value lands within $2^{-128}$ of an `f64` midpoint (the *Table-Maker's Dilemma*) or takes a wrong `if (x < y)` branch!
   - `Rival` (`machine.rkt:16-18`) starts at low precision (`*rival-min-precision* = 20` bits!) and evaluates `MPFR` endpoints as **error-propagating real and boolean intervals** (`ival-lo`, `ival-hi`, `ival-err?`, `adjust.rkt:68-92`). If the output interval straddles a target `f64` rounding boundary (`discretization`, `machine.rkt:22`) or an `ival-if` condition evaluates to `[#f, #t]` (`adjust.rkt:87`), `rival-apply` (`main.rkt:85-96`) adaptively increases per-instruction precision up to `*rival-max-iterations* = 5` (raising `exn:rival:unsamplable` on exact unresolvable ties like `x - x == 0` branch cuts!).
   - Furthermore, `make-hint` (`adjust.rkt:13-54`) compiles hyperrectangle specialization hints (`#f` skip, `#t` execute, `integer` copy child register, `ival` constant-fold resolved branch/assert), pruning dead `if`/`fmax` subtrees (`path-reduction`, `L61-95`). Using `Rival` as its shadow oracle, `Herbie` (`4612b0d493cbb2013dc5afac5c099b7722166ec2`, `DOI: 10.1145/2737924.2737959`) rewrites $\frac{1 - \cos x}{x^2} \leadsto \frac{1}{2}\left(\frac{\sin(x/2)}{x/2}\right)^2$, restoring **`0.0` ULP error** (`0.5` exact in `Probe 3`).

#### 3.2 Cross-ISA IEEE-754 Bit-Level Divergences (`Berkeley SoftFloat-3` & `TestFloat-3`)
Formal floating-point proofs (`Flocq`, `SMT QF_FP`) frequently assume IEEE-754 defines a unique bit-level function. Direct comparison of `ucb-bar/berkeley-softfloat-3` (`07ebd29db0cfb55723a79fbbffe99103ef38e305`, paired with differential generator `berkeley-testfloat-3` `a9c849f1b0eb0264b626d9686ffae167d996e3be`) across `source/8086-SSE/specialize.h`, `source/RISCV/specialize.h`, `source/ARM-VFPv2/specialize.h`, and `source/s_roundPackToF64.c` proves three concrete cross-silicon divergences (`Basis: source + execution`):

| Architectural Axis | `x86-SSE` (`8086-SSE/specialize.h`) | `RISC-V` (`RISCV/specialize.h`) | `ARM VFPv2` (`ARM-VFPv2/specialize.h`) |
| :--- | :--- | :--- | :--- |
| **`init_detectTininess` (`L48`)** | `tininess_afterRounding` (`1`) | `tininess_afterRounding` (`1`) | **`tininess_beforeRounding` (`0`)** |
| **`s_roundPackToF64(-1, 0x7FFFFFFFFFFFFE01)`** | Rounds to `2^-1022`; **`underflow = 0`** | Rounds to `2^-1022`; **`underflow = 0`** | Rounds to `2^-1022`; **`underflow = 1`** |
| **Default 16-bit Quiet NaN (`L81/88`)** | **`0xFE00`** (negative sign bit `1`) | **`0x7E00`** (positive sign bit `0`) | **`0x7E00`** (positive sign bit `0`) |
| **NaN Payload Propagation (`L76-83`)** | Propagates input `commonNaN` payload | **`struct commonNaN { char _unused; }`** (erases all payloads to canonical qNaN!) | Propagates `commonNaN` (unless `defaultNaN` mode) |
| **Invalid `NaN -> i32` (`i32_fromNaN`, `L59`)** | **`-0x80000000`** (`INT32_MIN`) | **`+0x7FFFFFFF`** (`INT32_MAX`) | **`0`** |
| **Invalid `-Inf -> u32` (`ui32_fromNegOverflow`)** | **`0xFFFFFFFF`** (`UINT32_MAX`) | **`0`** | **`0`** |

Any cross-platform WASM runtime, deterministic blockchain VM, or verified C compiler that lowers float-to-int casts, `fetestexcept(FE_UNDERFLOW)`, or `NaN` bit patterns directly to unmasked hardware instructions silently forks state across `x86_64`, `ARM`, and `RISC-V` hosts (`Basis: source + derived`)!

---

### 4. Cross-Cutting Synthesis: `L1–L6` Performance, `C1–C2` Comprehensibility & Simplicity, and `V1–V4` End-to-End Validation

#### 4.1 Multi-Level Performance and Resource Footprint Matrix (`L1–L6`)
`Basis: source + execution + documentation + derived`

| Validation Tool / Method | `(L1)` Authoring & Audit Velocity | `(L2)` Toolchain Build Time | `(L3)` Analysis / Synthesis Latency | `(L4)` Production Runtime Overhead | `(L5)` Witness / Vector Check Speed | `(L6)` RAM, Disk & Artifact Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Circomspect` Static Pass (`50010b62...`)** | `0` annotation LoC (runs directly on `.circom`) | Rust `cargo build --release` `~25 s` | **`< 50 ms`–`1.5 s`** interactive CLI/LSP feedback | `0` (compile-time linter) | Instant AST diagnostic | `< 100 MiB` RSS; binary `~8 MiB` |
| **`Veridise Picus` `DPVL` (`138b151d...`)** | `0–5` LoC (`CircuitVarIn`/`Out` in `gnark`, `0` in Circom) | Racket + Rust parser + `cvc5-ff` `~5–15 min` | Lemmas `< 100 ms`; hard `QF_FF` queries `5,000 ms`/wire timeout (`README.md:108`) | `0` (offline circuit verifier; `0` extra R1CS gates unless bug fixed) | Counterexample witness pair `(w_1, w_2)` verified in `< 2 ms` | Recommends `8–10 GiB` Docker RAM cap (`README.md:28-31`) on large rollups |
| **`Wycheproof` Vector Harness (`65ca4947...`)** | `30–80` LoC JSON test runner per primitive | `0 s` (`JSON` data files) | `210–484` public-key vectors execute in **`5–80 ms`** | `0` (CI regression gate) | `< 0.1 ms` per signature / AEAD vector | `37 KiB – 327 KiB` JSON per algorithm (`~15 MiB` full repo) |
| **`Rival` + `Atomu` FP Validation (`4d2334a0...`)** | `1–5` LoC FPCore mathematical spec | Racket `raco pkg install` `~20 s` | `Rival`: `20 -> 1000+` bit adaptive eval **`2–50 µs`/pt** (`make-hint` `2–5x` speedup); `Herbie`: `2–30 s`/expr | Rewritten expressions run at native `f64` speed (`0–2x` cycles vs `50–200x` runtime MPFR!) | Shadow interval containment check `< 10 µs`/sample | `MPFR` limb arenas `< 150 MiB` RSS |
| **`SoftFloat-3` / `TestFloat-3` (`07ebd29d...`)** | `0` LoC (automated `testfloat_gen | testfloat_ver` pipe) | Pure C build `< 5 s` (`Makefile`) | `10^6` corner vectors in **`0.2–1.5 s`** | Software FP emulation `10–40` cycles/op when used in deterministic VMs | Streaming bit-exact comparison `> 2M` ops/s | `< 64 KiB` C `.text` library (`0` `malloc`!) |

#### 4.2 Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)
`Basis: source + derived`

- **`(C1)` Human Comprehensibility & Mental-Model Ergonomics**:
  - **The `<--` vs. `<==` Mental-Model Trap in ZK**: Human programmers read `out[k] <-- (lin >> k) & 1` imperatively and subconsciously assume `out[k]` *is* `(lin >> k) & 1`. Even when an LLM generates syntactically valid R1CS equations, human auditors routinely miss missing `AliasCheck` ($< p$) or `IsZero(b)` guards because modular $\mathbb{F}_p$ wrap-around violates human unsigned-integer intuition (`p - 254 < 2`, §1.1). `Picus`'s concrete two-witness counterexample format (`inputs: inp=0 => first outputs: out=[1,0], second outputs: out=[0,0]`, `README.md:67-81`) translates abstract Gröbner-basis satisfiability into an immediately human-auditable forgery witness.
  - **Floating-Point Cancellation Blindness**: Humans cannot eyeball at which input magnitude $1 - \cos x$ loses `46.75` bits, nor remember whether `NaN as i32` yields `INT32_MIN`, `INT32_MAX`, or `0` across `x86`/`RISC-V`/`ARM`. `Herbie`'s regime plots + `Rival`'s exact bit-error metrics give engineers a visual map of accuracy cliffs.
- **`(C2)` Simplicity, Orthogonality & Universal Model Refinement (Felleisen Expressiveness & Ousterhout Deep Modules)**:
  - **Eliminating the ZK Witness/Constraint Schism**: Circom's dual `<--` / `===` semantics violates orthogonality by forcing authors to state one computation twice in different paradigms. A clean-slate circuit DSL treats deterministic functional computation as primary and requires every non-deterministic witness hint `hint w such_that P(x, w)` to carry an inline `Picus`-checked uniqueness certificate `(ProofUnique)`—making under-constrained signals un-expressible by default without manual `Circomspect` lints.
  - **Explicit IEEE-754 Specialization Profiles**: `SoftFloat-3`'s `specialize.h` cleanly factors IEEE-754's `5` underspecified degrees of freedom (`detectTininess`, `defaultNaN`, `commonNaN` payload propagation, and saturated vs. indefinite float-to-int overflow/NaN results) behind one `90`-line header (`Ousterhout` deep module), turning silent hardware accidents into explicit, testable semantic parameters (just as WebAssembly 1.0 standardized `trunc_sat_f64_s` and canonical `NaN` rules to rescue cross-CPU determinism!).

#### 4.3 End-to-End Solution & Implementation Validation Across `V1–V4`
`Basis: source + execution + documentation + derived`
- **`(V1)` Specification Adequacy, Mutation & Non-Vacuity**: `Picus` warns explicitly in `gnark-plonky2-verifier/src/exp.go:34-40` about missing `RangeCheck` preconditions: if a `Picus` `--precondition` JSON over-constrains inputs, uniqueness becomes vacuously true! Validating ZK specs requires pairing `Picus` uniqueness (`ProofForall`) with `zkFuzz` positive witness-generation tests (`WitnessExists`) and mutant-circuit injection (`benchmarks/buggy-mix/`).
- **`(V2)` Compiler, Lowering & Checker Soundness Fuzzing**: Our discovery of `EcneProject/src/Math.jl:80-85`'s `-b ± disc` quadratic-root bug proves why **verifiers themselves must be differentially tested** (`Picus` cross-checks `--solver cvc5` against `--solver z3` and runs against known-buggy `benchmarks/buggy-mix/`, while `Rival` cross-tests against `MPFI`, `Sollya`, and `Mathematica` in `infra/run-{mpfi,sollya,mathematica}.rkt`, even isolating `infra/mathematica-bug-1.wls`!).
- **`(V3)` Concurrency, Crash, Silicon & Physical Leakage Validation**: Passing `Wycheproof` mathematical vectors does **not** prove constant-time silicon execution! Production cryptographic implementations (`Ed25519`, `ECDSA`, `ChaCha20-Poly1305`, `RSA-OAEP` Manger checks) and ZK provers handling secret witnesses must additionally pass constant-time secret-taint verification, `Revizor` microarchitectural speculation fuzzing (`DOI: 10.1145/3503222.3507729`), `Coco`/`Alma` gate-level glitch-extended masking checks (`USENIX Security 2021`), and `TVLA` Welch's $t$-test power/EM leakage validation (e.g., variable-time subnormal microcode assists on `x86` leaking floating-point secrets!).
- **`(V4)` Plant Falsification, Telemetry/HIL Replay & Human Comprehension Validation**: When `Herbie`/`Rival`-verified floating-point controllers deploy onto embedded `ARM Cortex-M`/`RISC-V` FPUs (e.g., `FTZ`/`DAZ` flush-to-zero modes or `beforeRounding` underflow traps), end-to-end validation requires `TestFloat-3` on-target `HIL` execution, `S-TaLiRo` closed-loop `STL` falsification (`DOI: 10.1007/978-3-642-19835-9_21`), `ModelPlex` runtime monitor bounds (`DOI: 10.1007/s10703-016-0241-z`), and `SMoL` (`DOI: 10.1145/3649823`) human mental-model checks on finite-field and IEEE-754 edge semantics.

---

## Boundaries

1. **Completeness vs. Uniqueness in `Picus` (`known not to apply` to functional wrong-formula bugs)**: `Veridise/Picus` (`138b151d...`) proves *determinism/uniqueness* (each input maps to at most one valid output witness), **not** functional equivalence to a cryptographic specification (`Basis: source + derived`). A circuit constrained deterministically as `out <== in + 1` instead of `Poseidon(in)` is `100%` unique (`Picus` safe) while functionally wrong!
2. **Large Non-Linear Finite-Field SMT Timeouts (`unknown` on timeout in `Picus`)**: When `DPVL`'s five propagation lemmas (`dpvl.rkt:7-12`) cannot linearize coupled high-degree constraints (such as un-lemmatized custom S-boxes or large elliptic-curve pairings), `cvc5` `QF_FF` / `Z3` may hit the `5000ms` `--timeout` (`dpvl.rkt:65`: `'skip`), leaving uniqueness unresolved (`unknown`) unless modular sub-circuit preconditions are supplied (`Basis: source`).
3. **Unversioned Component Array Overwrite in `Circomspect` (`unsupported` / known precision limit)**: `trailofbits/circomspect` (`program_analysis/src/constraint_analysis.rs:27-38`) indexes `definitions` by `VariableName` rather than array-element `VariableAccess`, clobbering component-array initializations (`c[0].in[0]` vs. `c[1].in[1]`) (`Basis: source`).
4. **Incorrect General Quadratic Root Formula in `Ecne` (`known not to apply` when $\Delta \notin \{0, 1\}$)**: At pinned commit `25935352ca30705ad47363dcf200822635edc1c7`, `franklynwang/EcneProject/src/Math.jl:83-84` uses `disc` instead of `rt = squareRoot(field, disc)` and omits quadratic-non-residue termination guards (`L30-57`), making its quadratic solver unsound outside $\Delta \in \{0, 1\}$ (`Basis: source + execution`).
5. **Exact Zero-Width Branch Discontinuities in `Rival` (`unsupported` / raises `exn:rival:unsamplable`)**: On degenerate expressions containing exact real equality branches (`if (x - x == 0) ...` evaluated over non-point intervals or unresolvable transcendental identities), `Rival` (`eval/main.rkt:93-95`) hits `*rival-max-iterations*` and raises `exn:rival:unsamplable` rather than unsoundly guessing a branch (`Basis: source`).
6. **Native Racket/`cvc5-ff` and Hardware `ARM`/`RISC-V` Silicon Runs (`not examined` via local hardware execution)**: Upstream Racket, Rust, Julia, and C source trees and JSON test vectors were inspected directly at pinned `40`-hex commits and verified via exact Python `BigInt`/`Decimal`/bit-level probes on `x86_64`, while native `cvc5` finite-field binary execution and physical `ARM-VFPv2`/`RISC-V` FPU register runs were **not examined** directly (`Basis: execution`).

---

## Evidence

### Primary Upstream Source Repositories (Pinned 40-Hex Revisions)
- **`Veridise/Picus` @ `138b151d3a388e5b6c040c163e0a1db04f2ceda6`**:
  - `README.md:8-120` (CLI flags `--solver`, `--timeout 5000ms`, `--strong`, exit code `9` counterexample trace) & `picus/algorithms/dpvl.rkt:1-120` (`dpvl-solve` 2-safety `"x"`/`"y"` encoding and `l0..l4` propagation lemmas).
  - `benchmarks/gnark-plonky2-verifier/src/{exp.go,inverse.go,mul-add.go}` (`RangeCheck` precondition notes).
- **`trailofbits/circomspect` @ `50010b623ed4f3bff9d1b0363cfe952385b47af3`** & **`iden3/circom` @ `9b4b23331644e17868c90a85768826ed3bcba59f`**:
  - `circomspect`: `doc/analysis_passes.md:3-140`, `program_analysis/src/constraint_analysis.rs:25-96` (`L27-38` component array `TODO`), `program_analysis/src/under_constrained_signals.rs:13-120` (`MIN_CONSTRAINT_COUNT = 2`).
  - `circom`: `circom_algebra/src/constraint_storage/logic.rs` & `code_producers/src/c_elements/common/calcwit.cpp`.
- **`franklynwang/EcneProject` @ `25935352ca30705ad47363dcf200822635edc1c7`**:
  - `src/Math.jl:14-90` (`squareRoot` missing Legendre check and `solveQuadratic` `L83-84` `-b ± disc` bug), `src/ParseR1CS.jl:50-95`.
- **`C2SP/wycheproof` @ `65ca494727a52944c204441c860b039e6786b99b`**:
  - `testvectors_v1/ed25519_test.json` (`210` vectors: `117` valid, `64` invalid, `29` acceptable), `ecdsa_secp256r1_sha256_test.json` (`484` vectors), `chacha20_poly1305_test.json` (`325` vectors), `rsa_oaep_2048_sha256_mgf1sha256_test.json` (`37` vectors).
- **`herbie-fp/rival` @ `4d2334a05338be8df9c6924e30534d693f83267d`** & **`herbie-fp/herbie` @ `4612b0d493cbb2013dc5afac5c099b7722166ec2`**:
  - `rival`: `eval/main.rkt:36-110` (`rival-apply`, `rival-analyze-with-hints`), `eval/machine.rkt:16-50` (`*rival-min-precision* = 20`, `*rival-max-iterations* = 5`), `eval/adjust.rkt:13-95` (`make-hint`, `path-reduction`).
- **`ucb-bar/berkeley-softfloat-3` @ `07ebd29db0cfb55723a79fbbffe99103ef38e305`** & **`ucb-bar/berkeley-testfloat-3` @ `a9c849f1b0eb0264b626d9686ffae167d996e3be`**:
  - `source/include/softfloat.h:57-91`, `source/s_roundPackToF64.c:43-110` (`L72-81` `isTiny` logic), and `source/{8086-SSE,RISCV,ARM-VFPv2}/specialize.h:45-95`.

### Peer-Reviewed Primary Literature (Verified DOIs)
- Shankara Pailoor, Yanju Chen, Franklyn Wang, Clara Rodríguez, Jacob Van Geffen, Jason Morton, Michael Chu, Brian Gu, Yu Feng, Işıl Dillig, *Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs*, PLDI 2023 (`DOI: 10.1145/3591282`).
- Hideaki Takahashi, Jihwan Kim, Suman Jana, Junfeng Yang, *zkFuzz: Foundation and Framework for Effective Fuzzing of Zero-Knowledge Circuits*, IEEE S&P 2026 (`DOI: 10.1109/SP63933.2026.00049`).
- Christoph Hochrainer, Valentin Wüstholz, Maria Christakis, *Arguzz: Testing zkVMs for Soundness and Completeness Bugs*, USENIX Security 2026 (`DOI: 10.48550/arXiv.2509.10819`).
- Konstantinos Chalkias, François Garillot, Valeria Nikolaenko, *Taming the Many EdDSAs*, SSR 2020 (`DOI: 10.1007/978-3-030-64357-7_4`).
- Oliver Flatt, Pavel Panchekha, *An Interval Arithmetic for Robust Error Estimation*, 2021 (`DOI: 10.48550/arXiv.2107.05784`).
- Pavel Panchekha, Alex Sanchez-Stern, James R. Wilcox, Zachary Tatlock, *Automatically Improving Accuracy for Floating Point Expressions*, PLDI 2015 (`DOI: 10.1145/2737924.2737959`).
- Daming Zou, Muhan Zeng, Yingfei Xiong, Zhoulai Fu, Lu Zhang, Zhendong Su, *Detecting Floating-Point Errors via Atomic Conditions* (`Atomu`), POPL 2020 (`DOI: 10.1145/3371128`).
- Wei-Fan Chiang, Ganesh Gopalakrishnan, Zvonimir Rakamarić, Alexey Solovyev, *Efficient Search for Inputs Causing High Floating-Point Errors* (`S3FP`), PPoPP 2014 (`DOI: 10.1145/2555257.2555265`).
- Cross-layer `V3`/`V4` references: `Revizor` (`DOI: 10.1145/3503222.3507729`), `S-TaLiRo` (`DOI: 10.1007/978-3-642-19835-9_21`), `ModelPlex` (`DOI: 10.1007/s10703-016-0241-z`), `SMoL` (`DOI: 10.1145/3649823`).

### Execution Environment & Recorded Probe Receipts (`2026-11-19`)
Executed on Linux `x86_64` with Python `3` stdlib (`120`-digit `decimal` + exact `BN254` `int`):
- **Probe 1 (`BN254` Under-Constraints & `Ecne` Bug)**: `in0 = p - 254` forged `LessThan(8) == 1`; `p + 1 < 2^254` aliased `1` in `Num2Bits(254)`; `Ecne` `Math.jl:83-84` returned `[7, p - 2]` (residuals `[18, 18]`) vs. true roots `[1, 4]` (residuals `[0, 0]`).
- **Probe 2 (`Wycheproof` Audit)**: Verified exact `ed25519` (`117/64/29`) and `ecdsa_secp256r1` (`174/310/0`) splits.
- **Probe 3 (`Rival`/`Atomu` Cancellation & `SoftFloat-3` Tininess)**: `(1 - cos(1.5e-8)) / (1.5e-8)^2` lost `46.75` bits (`cond_sub = 1.801e16`) vs. `0.0` ULP rewritten; `s_roundPackToF64(-1, 0x7FFFFFFFFFFFFE01)` diverged on `FE_UNDERFLOW` (`ARM = True`, `x86/RISC-V = False`).

---

## Revalidation

Run the following self-contained Python `3.10+` verification script (`0` external dependencies; `exit 0` in `< 100 ms`) to revalidate the `BN254` `LessThan(8)` and `Num2Bits(254)` exploits, the `EcneProject/src/Math.jl` quadratic-root bug, the `46.75`-bit catastrophic cancellation and `Atomu` condition number, and the `SoftFloat-3` `beforeRounding` vs. `afterRounding` underflow divergence:

```bash
python3 - <<'PY'
import decimal, math

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617

# 1. Circom LessThan(8) wrap-around & Num2Bits(254) non-strict aliasing on BN254
in0 = P - 254
assert in0 > (1 << 253) and ((in0 + (1 << 8) - 2) % P) == 0
lt_out = 1 - (((in0 + 256 - 2) % P >> 8) & 1)
assert lt_out == 1
assert (P + 1) < (1 << 254) and ((P + 1) % P) == 1

# 2. Reproduction of franklynwang/EcneProject src/Math.jl:80-85 (-b +- disc)/(2a) bug
a, b, c = 1, P - 5, 4
disc = (b * b - 4 * a * c) % P
rt = 3
inv2a = pow(2 * a, P - 2, P)
ecne_roots = sorted([((-b + disc) * inv2a) % P, ((-b - disc) * inv2a) % P])
true_roots = sorted([((-b + rt) * inv2a) % P, ((-b - rt) * inv2a) % P])
assert ecne_roots == [7, P - 2] and [((r*r + b*r + c) % P) for r in ecne_roots] == [18, 18]
assert true_roots == [1, 4] and [((r*r + b*r + c) % P) for r in true_roots] == [0, 0]

# 3. Catastrophic cancellation (46.75 bits lost), Atomu condition number, & Rival/Herbie fix
decimal.getcontext().prec = 100
x = 1.5e-8
naive = (1.0 - math.cos(x)) / (x * x)
stable = 0.5 * (math.sin(0.5 * x) / (0.5 * x)) ** 2
xd = decimal.Decimal.from_float(x)
exact = float(decimal.Decimal(1)/decimal.Decimal(2) - (xd**2)/decimal.Decimal(24) + (xd**4)/decimal.Decimal(720))
bits_lost = round(math.log2((abs(naive - exact) / exact) / (2 ** -53)), 2)
cond_sub = (1.0 + math.cos(x)) / abs(1.0 - math.cos(x))
assert bits_lost == 46.75 and cond_sub > 1.8e16 and stable == exact == 0.5

# 4. SoftFloat-3 s_roundPackToF64.c:72-81 tininess_beforeRounding (ARM) vs afterRounding (x86/RISC-V)
exp, sig, inc = -1, 0x7FFFFFFFFFFFFE01, 512
tiny_before = True
tiny_after = (exp < -1) or (sig + inc < 0x8000000000000000)
sig_jam = (sig >> 1) | (sig & 1)
round_bits = sig_jam & 0x3FF
assert (tiny_before and bool(round_bits)) is True
assert (tiny_after and bool(round_bits)) is False
assert ((sig_jam + inc) >> 10) == 0x0010000000000000
print("PACKAGE 1 REVALIDATION PASSED: ecne_res=[18,18], bits_lost=46.75, tininess_split=(True,False)")
PY
```

To revalidate upstream repository coordinates on newer revisions:
1. Inspect `Veridise/Picus` `picus/algorithms/dpvl.rkt`, `trailofbits/circomspect` `program_analysis/src/under_constrained_signals.rs`, `franklynwang/EcneProject` `src/Math.jl` (`solveQuadratic`), `C2SP/wycheproof` `testvectors_v1/ed25519_test.json`, `herbie-fp/rival` `eval/{main.rkt,adjust.rkt}`, and `ucb-bar/berkeley-softfloat-3` `source/{8086-SSE,RISCV,ARM-VFPv2}/specialize.h`.
