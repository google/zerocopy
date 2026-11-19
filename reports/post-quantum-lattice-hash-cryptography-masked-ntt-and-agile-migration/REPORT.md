# Verified Post-Quantum Lattice and Hash Cryptography, Masked NTT Engineering, and Agile Migration

## Summary

Deploying NIST post-quantum standards (`FIPS 203` ML-KEM, `FIPS 204` ML-DSA, `FIPS 205` SLH-DSA) and hash-based post-quantum proof receipts (`FRI`/`STARK`) inside formally verified systems software exposes five tightly coupled engineering boundaries that do not appear in classical elliptic-curve deployments:

1. **Mechanized Verification Scope Differs Sharply Across Production Stacks:** None of the three leading verified ML-KEM/ML-DSA stacks eliminates the entire Trusted Computing Base (TCB) alone. `celabshq/libcrux` (formerly `cryspen/libcrux`) verifies panic-freedom and functional correctness of pure Rust (plus Eurydice-extracted C) via `hax -> F*`, but explicitly documents that LLVM constant-time preservation relies on best-effort `core::hint::black_box` barriers (and `volatile` shims in extracted C) and that NEON and generic `ind_cpa` proof modules lag behind portable/AVX2 coverage. `formosa-crypto/formosa-libjade` (the active successor to `Formosa-Crypto/formosa-mlkem`) proves functional correctness, safety, constant-time (`ct`), and speculative constant-time (`sct`) directly on Jasmin-compiled AVX2 assembly in EasyCrypt alongside ROM IND-CCA/EUF-CMA specification theorems, but leaves C ABI headers in the TCB and covers x86-64 AVX2 only. `pq-code-package/mlkem-native` combines CBMC memory/type-safety proofs for C90 frontends with HOL-Light object-code functional correctness and constant-time proofs for AArch64 and x86-64 assembly, while explicitly scoping out power/EM side channels, speculative execution, and fault injection.
2. **Compiler-Introduced Division Timing Leaks (`KyberSlash`) Persist Under Size Optimization:** Writing C integer division by the public modulus `q = 3329` inside `poly_tomsg` (KyberSlash1) or `poly_compress`/`polyvec_compress` (KyberSlash2) remains hazardous even on modern x86-64 compilers: direct execution of `gcc 15.2.0 -Os` emits a variable-time hardware `divl %ecx` instruction for `(((t << 1) + 1664U) / 3329U) & 1U`, whereas `-O2` emits magic multiplication. Replacing `/` with explicit constant-time Barrett multiplication (`((x << d) + c) * M >> s`) removes `divl` across `-O0`, `-Os`, and `-O2`, but exact rounding constants (`+1664` vs. `+1665`) are mathematically brittle: perturbing a single rounding offset by 1 introduces silent 1-in-3,329 coefficient mismatches (`x = 3225` at `d = 4`, `x = 52` at `d = 5`, `x = 2079` at `d = 10`, `x = 625` at `d = 11`).
3. **High-Order Masking Breaks at Arithmetic/Boolean Domain Boundaries and Under SIFA:** Lattice operations mix arithmetic ring additions/NTTs over $\mathbb{Z}_q$ with non-linear Boolean operations (Keccak/SHAKE-256 $\chi$, CBD sampling, ML-KEM `Compress_1` / Fujisaki–Okamoto ciphertext comparison, and ML-DSA's four sequential rejection checks). Naive fault-detection countermeasures that suppress output on detected mismatch leak masked secrets under Statistical Ineffective Fault Analysis (`SIFA`): a stuck-at-0 fault on an unmasked check bit or Keccak $\chi$ input yields an exact posterior bias $P(s=0 \mid \text{ineffective}) = 2/3$ at fault probability $p_f = 0.5$. Protecting ML-DSA rejection loops without leaking secret-correlated abort counts requires high-order masked bound checks (Coron et al. TCHES 2023) or shuffle-and-unmask gadgets (`SUCRE`, TCHES 2026) paired with infective or redundant fault countermeasures.
4. **Embedded Stack and Wire-MTU Budgets Force Streaming Designs and Protocol Chunking:** Reference `pq-crystals/dilithium` allocates 50.2 KiB (ML-DSA-44) to 120.8 KiB (ML-DSA-87) of stack polynomials alone—exceeding a 2 KiB embedded Root-of-Trust (RoT) stack by up to 60x—requiring on-the-fly matrix-element streaming and incremental Keccak schedules (reducing ML-DSA verification below 3 KiB and signing below 7 KiB RAM, or splitting ML-KEM keys via incremental encapsulation). On hardware attestation buses (`DMTF/libspdm` SPDM 1.4), transporting `3.3–49.9 KB` post-quantum signatures across small `DataTransferSize` MTUs (42–256 bytes) requires `14–1,662` `CHUNK_SEND`/`CHUNK_GET` fragments, which drove SPDM 1.4 to widen `chunk_seq_no` from `uint16_t` to `uint32_t`.
5. **Post-Quantum Proof Receipts (`FRI`/`STARK`) Depend Heavily on Proximity-Gap Regime:** Migrating long-lived proof stores from discrete-log SNARKs to hash-based `FRI`/Circle-STARK IOPs eliminates Shor's-algorithm risk, but concrete soundness varies by nearly 2.5x–3x in query count between conjectured regimes (`ethSTARK` / random-words) and provable regimes (Unique Decoding / Johnson Bound), while wide opening batches over 31-bit base fields (`BabyBear`/`KoalaBear`) make batching-round Grinding Proof-of-Work (`batch_proof_of_work_bits`) rather than query count the binding provable-soundness constraint.

## Applicability

This report synthesizes evidence across four classes of durable subjects identified in `REPORT.json` and defines how they relate:

- **Normative Standards (`FIPS 203`, `FIPS 204`, `FIPS 205`, DMTF SPDM 1.2–1.4):** Define parameter sets, ring arithmetic, serialization, key-validation checks (`check_pk`/`check_sk`), Fujisaki–Okamoto implicit rejection, ML-DSA hedged/deterministic signing with domain-separation context prefixes, SLH-DSA stateless hypertrees, and SPDM 1.4 wire encodings.
- **Reference vs. Formally Verified Implementations (Comparison):** Contrasts unverified C reference implementations (`pq-crystals/kyber` @ `3edd5af5...`, `pq-crystals/dilithium` @ `d35ba3fe...`) against three verified production verification architectures: `celabshq/libcrux` @ `e882e13e...` (Rust -> `hax` -> `F*` + Eurydice C), `formosa-crypto/formosa-libjade` @ `90ba5dc4...` (Jasmin -> AVX2 assembly + EasyCrypt, succeeding `Formosa-Crypto/formosa-mlkem` @ `d1e64d5f...`), and `pq-code-package/mlkem-native` @ `c179cea8...` (C90 + CBMC + AArch64/x86-64 HOL-Light).
- **Compiler & Wire-Protocol Boundary Subjects:** `gcc 15.2.0` on `x86_64-linux-gnu` directly characterizes `-O0`/`-Os`/`-O2` codegen for division-vs-Barrett compression; `DMTF/libspdm` @ `3f1253df...` supplies concrete SPDM 1.4 PQC algorithm identifiers and `CHUNK_SEND`/`CHUNK_GET` framing mechanics.
- **Post-Quantum Proof-System Subject:** `Plonky3/Plonky3` @ `0d803737...` (`fri` and `security` crates) characterizes production FRI low-degree testing, multi-site Proof-of-Work grinding, and proven vs. conjectured Reed–Solomon proximity-gap bounds.

**Scope qualifications:** Code-level claims for `libcrux`, `formosa-libjade`, `mlkem-native`, `kyber`, `dilithium`, `libspdm`, and `Plonky3` apply exactly to the pinned revisions in `REPORT.json`. Because `libcrux`'s `proofs/verification_status.md` evolves rapidly and `mlkem-native`'s ARMv8.1-M Helium backend is marked experimental, proof-coverage percentages must not be extrapolated to newer or older commits without re-inspecting the verification manifests. High-order masking and SIFA findings synthesize peer-reviewed hardware-security literature (TCHES 2018–2026) together with standalone mathematical probes; none of the three formally verified software libraries above (`libcrux`, `formosa-libjade`, `mlkem-native`) implements physical power/EM masking or hardware fault countermeasures at the inspected revisions.

## Findings

### 1. NIST Post-Quantum Standards: Algebraic Parameters, Wire Sizes, and Validation Contracts

Basis: normative (`FIPS 203`, `FIPS 204`, `FIPS 205`) + source (`pq-crystals/kyber`, `pq-crystals/dilithium`, `celabshq/libcrux`, `formosa-crypto/formosa-libjade`)

NIST finalized `FIPS 203` (ML-KEM), `FIPS 204` (ML-DSA), and `FIPS 205` (SLH-DSA) on 2024-08-13. Both ML-KEM and ML-DSA operate over the negacyclic polynomial ring $R_q = \mathbb{Z}_q[X]/(X^{256}+1)$ with $n = 256$, enabling fast Number-Theoretic Transforms (NTT), while SLH-DSA relies exclusively on symmetric hash/XOF security (`SHA2` or `SHAKE256`) via hypertrees of WOTS+ one-time signatures and FORS few-time signatures.

| Standard / Parameter Set | NIST Cat. | Algebraic / Structural Params | Public Key (B) | Secret Key (B) | Ciphertext / Sig (B) | Core Primitives & Hashing |
| --- | --- | --- | ---: | ---: | ---: | --- |
| **ML-KEM-512** (FIPS 203) | 1 | $q=3329, k=2, \eta_1=3, \eta_2=2, d_u=10, d_v=4$ | 800 | 1,632 | 768 | Incomplete NTT (128 deg-2 factors, $\zeta=17$), SHA3-256/512, SHAKE128/256 |
| **ML-KEM-768** (FIPS 203) | 3 | $q=3329, k=3, \eta_1=2, \eta_2=2, d_u=10, d_v=4$ | 1,184 | 2,400 | 1,088 | Same ring $R_{3329}$; FO implicit rejection via SHAKE256($z \mathbin{\Vert} c$) |
| **ML-KEM-1024** (FIPS 203) | 5 | $q=3329, k=4, \eta_1=2, \eta_2=2, d_u=11, d_v=5$ | 1,568 | 3,168 | 1,568 | Same ring $R_{3329}$; higher $d_u, d_v$ compression precision |
| **ML-DSA-44** (FIPS 204) | 2 | $q=8380417, (k,\ell)=(4,4), \gamma_1=2^{17}, \gamma_2=(q-1)/88, \tau=39, \eta=2, \beta=78, \omega=80$ | 1,312 | 2,560 | 2,420 | Full 256-point NTT ($\zeta=1753$), SHAKE128/256, Fiat–Shamir w/ aborts |
| **ML-DSA-65** (FIPS 204) | 3 | $q=8380417, (k,\ell)=(6,5), \gamma_1=2^{19}, \gamma_2=(q-1)/32, \tau=49, \eta=4, \beta=196, \omega=55$ | 1,952 | 4,032 | 3,309 | Same ring $R_{8380417}$; 4 sequential signing rejection predicates |
| **ML-DSA-87** (FIPS 204) | 5 | $q=8380417, (k,\ell)=(8,7), \gamma_1=2^{19}, \gamma_2=(q-1)/32, \tau=60, \eta=2, \beta=120, \omega=75$ | 2,592 | 4,896 | 4,627 | Same ring $R_{8380417}$; `pre = (0x00, ctxlen, ctx)` domain prefix |
| **SLH-DSA-128s / 128f** (FIPS 205) | 1 | $n=16, h=63/66, d=7/22$ | 32 | 64 | 7,856 / 17,088 | Stateless hash hypertree (WOTS+ / XMSS / FORS); `s`=small, `f`=fast |
| **SLH-DSA-192s / 192f** (FIPS 205) | 3 | $n=24, h=63/66, d=7/22$ | 48 | 96 | 16,224 / 35,664 | Zero lattice assumptions; signing cost dominates `s` variants |
| **SLH-DSA-256s / 256f** (FIPS 205) | 5 | $n=32, h=64/68, d=8/17$ | 64 | 128 | 29,792 / 49,856 | Largest standardized signatures (~49.9 KB for `256f`) |

**Normative input-validation pitfalls between Round-3 drafts and final FIPS 203/204:**

- **ML-KEM Modulus Check (FIPS 203 Section 7.2) & Decapsulation Key Hash Check (Section 7.3):** Every 12-bit decoded coefficient of the encapsulation key `ek` MUST satisfy $0 \le \hat{t}_i < 3329$ before encapsulation; naive `poly_frombytes` in `pq-crystals/kyber` (`ref/poly.c:151-158`) only masks with `& 0xFFF`, accepting non-canonical values in $[3329, 4095]$. Similarly, `ML-KEM.Decaps` requires verifying `H(ek) == dk[768k+32 .. 768k+64]`. Both `libcrux` (`validate_public_key` / `validate_private_key`, `libcrux-ml-kem/README.md:19-20`) and `formosa-libjade` (`check_pk` / `check_sk`, returning `-1` and zeroing outputs on failure, `README.md:132-141`) expose these explicitly, whereas `pq-crystals/kyber` `ref/kem.c` expects callers to enforce FIPS 203 wrapper checks separately.
- **ML-KEM Fujisaki–Okamoto (FO) Implicit Rejection:** In `pq-crystals/kyber` (`ref/kem.c:152-167`), `crypto_kem_dec` decrypts $m'$, computes $(K', r') = G(m' \mathbin{\|} H(ek))$, re-encrypts $c' = \text{K-PKE.Enc}(ek, m', r')$, computes the rejection key $\bar{K} = J(z \mathbin{\|} c)$ via `rkprf`, compares $c \stackrel{?}{=} c'$ in constant time (`verify`), and conditionally selects $K'$ or $\bar{K}$ (`cmov`). Any timing, branch, or fault leak distinguishing `fail == 0` from `fail == 1` breaks IND-CCA2 security via a plaintext-checking (PC) oracle.
- **ML-DSA Domain Separation & Hedged Signing:** FIPS 204 wraps pure ML-DSA messages with `M' = 0x00 || len(ctx) || ctx || M` (`ctxlen <= 255`, `pq-crystals/dilithium` `ref/sign.c:218-225`) and hashes `tr = SHAKE256(pk, 64)` into `mu = SHAKE256(tr || M', 64)` before deriving `rhoprime = SHAKE256(K || rnd || mu, 64)`. Hedged signing (`rnd` freshly random rather than all-zero) mitigates fault-injection attacks that rely on re-signing the same message with an identical nonce $y$.

### 2. Mechanized Verification Architecture Comparison: Libcrux vs. Formosa-Libjade vs. mlkem-native

Basis: source (`celabshq/libcrux`, `formosa-crypto/formosa-libjade`, `Formosa-Crypto/formosa-mlkem`, `pq-code-package/mlkem-native`) + documentation (`ePrint 2024/843`, `ePrint 2025/142`, `ePrint 2025/980`, `TCHES 2023`)

Inspection of `Formosa-Crypto/formosa-mlkem` @ `d1e64d5fee2157b47e5030c4f0bdc07bb36a7bde` confirms that its `README.md` is now an archival stub redirecting all active Jasmin ML-KEM (and ML-DSA) code and EasyCrypt proofs to `formosa-crypto/formosa-libjade` (inspected at `90ba5dc4d9da2b6950589c58a52282caa1dbfdfd`). Similarly, `github.com/cryspen/libcrux` permanently redirects to `github.com/celabshq/libcrux` (inspected at `e882e13e3f6b6482ea7622d786b499f504a76e97`).

| Dimension | `celabshq/libcrux` (`hax` -> `F*` + Eurydice C) | `formosa-crypto/formosa-libjade` (Jasmin + EasyCrypt) | `pq-code-package/mlkem-native` (CBMC + HOL-Light) |
| --- | --- | --- | --- |
| **Source & Extraction** | Pure Rust (`no_std`); extracted to F* by `hax`, extracted to C via Eurydice/KaRaMeL (`cg/`) | Jasmin DSL compiled by certified Jasmin compiler to System V AMD64 ELF AVX2 assembly (`asm/*.s`) | Portable C90 frontend + hand-written/SLOTHY-superoptimized assembly backends (AArch64, x86-64, RVV, VSX, exp. Armv8.1-M) |
| **Algorithms Covered** | ML-KEM 512/768/1024 (`libcrux-ml-kem`) & ML-DSA 44/65/87 (`libcrux-ml-dsa`) | ML-KEM 512/768/1024 & ML-DSA 44/65/87 (`avx2/sct` profile) | ML-KEM 512/768/1024 (separate sibling repo `mldsa-native` for ML-DSA) |
| **Memory & Panic Safety** | F* SMT verification of bounds & integer non-overflow (`hax_lib::requires`/`ensures`/`loop_invariant!`) | Jasmin safety checker + EasyCrypt safety proofs | CBMC function contracts (`__contract__`) & loop invariants (`__loop__`) on C90; HOL-Light on AArch64/x86-64 asm |
| **Functional Correctness** | F* proofs against `Spec.MLKEM.fst` (portable 52/52 fns verified; AVX2 42/47; generic `ind_cpa` 0/21, `ind_cca` 26/27; NEON 1/40 per `verification_status.md`) | End-to-end EasyCrypt relational equivalence (`equiv [M.__crypto_kem_*_jazz ~ MLKEM.*]`) across ML-KEM 512/768/1024 (`correctness{512,768,1024}.ec`) and ML-DSA 44/65/87 | Object-code HOL-Light (`s2n-bignum`) equivalence for AArch64 & x86-64 assembly kernels; C frontend relies on CBMC bounds + ACVP/Wycheproof KATs |
| **Cryptographic Security** | Functional correctness to FIPS 203 spec (no mechanized IND-CCA game proof inside `libcrux` repo) | Machine-checked EasyCrypt ROM IND-CCA for ML-KEM (`MLKEMSecurity.ec`, CRYPTO 2024 / `ePrint 2024/843`) & ROM EUF-CMA hedged signing w/ leakage for ML-DSA (`MLDSA_Security.ec`); explicit `provsec` tiers (`functional`, `reduction`, `leakage-aware reduction`) | Relies on FIPS 203 spec security; no mechanized IND-CCA proof in repo |
| **Constant-Time & Speculative CT** | Compile-time `libcrux-secrets` types (`check-secret-independence`) + `#[inline(never)]` + `core::hint::black_box` (Rust) / `volatile` shim (C); **no LLVM codegen proof** | Static `jasmin-ct` **CT and Speculative CT (`sct`)** verification directly on Jasmin IR preserved by certified compiler to assembly (`mlkem768_avx2_sct.s`) | Object-code HOL-Light CT proof for AArch64 & x86-64 asm (no secret branches/memory/variable-latency insns); C code uses CT barriers + Valgrind; **no SCT / power / fault proofs** |
| **Key TCB Boundaries** | `rustc`/LLVM lowering (explicitly warned in `constant_time_ops.rs:3-19`), `hax` translator, Eurydice C backend (`black_box` becomes no-op!), `F*`/Z3 | Jasmin compiler (Coq-verified core + unverified extraction/printer), EasyCrypt/SMT solvers, unverified C headers in `src/include/` (`README.md:163-164`) | C compiler (for C90 frontend), CBMC, HOL-Light + `s2n-bignum` ISA models, constant-time 32x32 multiplier hardware assumption (`README.md:76-77`) |

**Concrete source-level verification nuances observed directly in the pinned trees:**

- **Libcrux Rust-to-LLVM-to-C Barrier Gap:** In `celabshq/libcrux` (`libcrux-ml-kem/src/constant_time_ops.rs:3-28,115-124`), `ct_barrier_u8` wraps `core::hint::black_box(value)` with `#[inline(never)]` and an F* postcondition `result == value` so F* can verify functional correctness of `compare_ciphertexts_in_constant_time` and `select_ct` while hiding the `{0,1}` range of `is_non_zero` from LLVM value-range propagation (which otherwise converts bitmask selection `(lhs[i] & mask) | (rhs[i] & !mask)` into a secret-dependent branch). Crucially, lines 15–19 note that Eurydice translates `core::hint::black_box` into a no-op during C extraction, forcing the C extraction to substitute a hand-written `volatile` round-trip in `intrinsics/libcrux_ct_barrier.h`.
- **Libcrux Documentation vs. Status-Table Drift:** `libcrux-ml-kem/README.md:169-172` summarizes that portable, AVX2, and generic high-level code are formally verified, while deferring to `proofs/verification_status.md`. Reading `proofs/verification_status.md:22-55` directly reveals concrete remaining gaps at revision `e882e13e...`: `generic/ind_cpa` (0/21), `generic/sampling` (0/5), `generic/matrix` (1/5 panic-free, 0/5 correct), `avx2/ntt` (5/7), `avx2/serialize` (19/22), and `neon/*` (1/40 total). Engineering audits MUST read the module-level proof manifest rather than top-level badges.
- **Formosa-Libjade `ProvSec` Stratification:** `formosa-crypto/formosa-libjade` (`README.md:88-118`) enforces machine-checked CI claims via `meta.toml` + `scripts/claims.py` and explicitly distinguishes `provsec = "functional"` (spec security and impl correctness proved separately) from `reduction` and `leakage-aware reduction` (an EasyCrypt theorem directly composes implementation leakage with the security reduction). In `proofs/mlkem/avx2/sct/correctness/768/correctness768.ec:116-171`, `keygen_correct`, `encaps_correct`, and `decaps_correct` prove byte-for-byte relational equivalence between the extracted AVX2 Jasmin procedures and `Spec768.MLKEM` including exact byte offsets (`1152`, `2304`, `2336`, `2368` in `sk`; `960` in `ct`).

### 3. Compiler Division Timing Leaks (`KyberSlash`) and Exact Barrett Compression Constants

Basis: source (`pq-crystals/kyber`, `celabshq/libcrux`, `pq-code-package/mlkem-native`) + execution (`gcc 15.2.0` probe & exhaustive Python verifier) + documentation (`kyberslash.cr.yp.to`)

`KyberSlash` (Bernstein, Bhargavan, Bhasin, Chattopadhyay, Chia, Kannwischer, Kiefer, Paiva, Ravi, Tamvada, 2023–2024) demonstrated full secret-key recovery against Kyber/ML-KEM implementations containing C division `/` by the public constant `KYBER_Q = 3329`:

- **KyberSlash1 (`poly_tomsg`):** Decryption computes `Compress_1(x)` on secret-dependent polynomial coefficients $u = v - s^T u$ inside `indcpa_dec`: originally `(((t << 1) + KYBER_Q/2) / KYBER_Q) & 1`.
- **KyberSlash2 (`poly_compress` / `polyvec_compress`):** Decapsulation re-encrypts $m'$ inside the FO transform, executing `Compress_{d_u}` and `Compress_{d_v}` on coefficients derived from the secret message $m'$ and coins $r'$—even when decapsulation fails—creating a timing plaintext-checking oracle.

**Direct Compiler Codegen Observation (`Basis: execution`, `gcc 15.2.0`, `x86_64-linux-gnu`):**
Compiling the original division expression `(((t << 1) + 1664U) / 3329U) & 1U` alongside the Barrett fix `((((t << 1) + 1665U) * 80635U) >> 28) & 1U` demonstrates why source-level `/` by a compile-time constant is fundamentally non-portable across optimization flags:

| Function | `gcc -O0` (x86-64) | `gcc -Os` (x86-64, firmware size opt) | `gcc -O2` (x86-64) |
| --- | --- | --- | --- |
| `poly_tomsg_div` (`/` by `3329U`) | `imulq $989558401` + `shrq $32` + `shrl $11` (magic mul) | **`divl %ecx` (VARIABLE-TIME HARDWARE DIVISION!)** | `imulq $989558401` + `shrq $32` + `shrl $11` (magic mul) |
| `poly_tomsg_barrett` (`* 80635U >> 28`) | `imull $80635` + `shrl $28` | **`imull $80635` + `shrl $28` (zero `divl`)** | `imull $80635` + `shrl $28` |

Even on x86-64 (not only 32-bit ARM/RISC-V!), `-Os` intentionally trades the multi-instruction magic-multiplier sequence for a compact 2-byte `divl %ecx`, reintroducing operand-dependent cycle latency (on Intel/AMD x86-64, `div` executes in variable cycles depending on quotient/dividend bit length). Furthermore, `mlkem-native` (`README.md:75-77`) highlights a second compiler hazard (`clangover`) and notes that even multiplication-only C code assumes hardware constant-time $32\times 32 \to 32/64$ multipliers—an assumption violated on older ARM Cortex-M3 / some RISC-V cores with early-terminating multipliers.

**Exact Constant-Time `Compress_d` Formulas & Rounding-Offset Fragility (`Basis: source + execution`):**
Normative FIPS 203 Eq. (4.7) defines $\text{Compress}_d(x) = \lfloor (2^{d+1} x + q)/(2q) \rfloor \bmod 2^d$ for $x \in [0, 3328]$. Both `pq-crystals/kyber` (`ref/poly.c:34-58,203-207`; `ref/polyvec.c:28-63`) and `celabshq/libcrux` (`libcrux-ml-kem/src/vector/portable/compress.rs:31-130`) replace division with bit-exact constant-time approximations. Exhaustive testing across all 3,329 canonical coefficients confirms **0 mismatches** for every deployed formula, AND reveals that changing `+1664` vs. `+1665` by 1 breaks exactness on **1 to 3 isolated coefficients out of 3,329**:

| $d$ | `pq-crystals/kyber` Constant-Time Formula | `celabshq/libcrux` Constant-Time Formula | Exhaustive Mismatches ($x \in [0, 3328]$) | Perturbed Offset Failure Witness (`+1664` $\leftrightarrow$ `+1665`) |
| --- | --- | --- | ---: | --- |
| $1$ (`poly_tomsg`) | `(((x << 1) + 1665) * 80635) >> 28` & `1` (u32) | Branchless fold: `s = 1664 - x; (((((s>>15) ^ s) - 832) >> 15) & 1)` (i16, zero mul) | `0` / `0` | Universal 64-bit `(((x<<1)+1664)*10321340)>>35` also achieves `0` mismatches |
| $4$ ($d_v$, 512/768) | `(((x << 4) + 1665) * 80635) >> 28` & `0xF` (u32) | `(((x << 4) + 1664) * 10321340) >> 35` & `0xF` (u64) | `0` / `0` | `kyber` w/ `+1664`: **1 mismatch** at $x = 3225$ |
| $5$ ($d_v$, 1024) | `(((x << 5) + 1664) * 40318) >> 27` & `0x1F` (u32) | `(((x << 5) + 1664) * 10321340) >> 35` & `0x1F` (u64) | `0` / `0` | `kyber` w/ `+1665`: **1 mismatch** at $x = 52$ |
| $10$ ($d_u$, 512/768) | `(((x << 10) + 1665) * 1290167) >> 32` & `0x3FF` (u64) | `(((x << 10) + 1664) * 10321340) >> 35` & `0x3FF` (u64) | `0` / `0` | `kyber` w/ `+1664`: **1 mismatch** at $x = 2079$ |
| $11$ ($d_u$, 1024) | `(((x << 11) + 1664) * 645084) >> 31` & `0x7FF` (u64) | `(((x << 11) + 1664) * 10321340) >> 35` & `0x7FF` (u64) | `0` / `0` | `kyber` w/ `+1665`: **3 mismatches** ($x \in \{625, 1875, 3125\}$); `libcrux` w/ `+1665`: **1 mismatch** ($x = 625$) |

Additionally, exhaustive verification of `pq-crystals/kyber` `barrett_reduce(a)` (`ref/reduce.c:35-42`, $v = \lfloor (2^{26} + 1664)/3329 \rfloor = 20159$, $r = a - \lfloor (v \cdot a + 2^{25})/2^{26} \rfloor \cdot 3329$) confirms exact modular congruence over all 65,536 `int16_t` inputs $[-32768, 32767]$ with tight centered output range $[-1664, 1664]$ (`0` congruence errors). Note that `poly_compress` must still map signed outputs from `[-1664, 1664]` to canonical `[0, 3328]` via `u += (u >> 15) & KYBER_Q` before compression—otherwise `mlkem-native` (`mlkem/src/compress.c:35-44`) enforces `array_bound(a->coeffs, 0, MLKEM_N, 0, MLKEM_Q)` directly as a CBMC precondition.

### 4. High-Order Masking (B2A/A2B, NTT, Keccak), ML-DSA Rejection Loops, and SIFA

Basis: documentation (`TCHES 2018`, `TCHES 2021`, `TCHES 2022`, `TCHES 2023`, `TCHES 2026`) + source (`pq-crystals/dilithium`) + execution (Probe 1B & Probe 1D)

Software constant-time verification (`ct`/`sct`) only prevents *timing* and *cache* leakage; physical embedded targets (smartcards, hardware RoTs, HSMs) face differential power/EM side-channel analysis (`SCA`) and laser/clock/voltage fault injection (`FI`). High-order $d$-probing security splits every sensitive variable $x$ into $n = d + 1$ shares—either **Arithmetic shares** $x \equiv \sum_{i=0}^{d} A_i \pmod{q}$ (or $\bmod 2^k$) or **Boolean shares** $x = \bigoplus_{i=0}^{d} B_i$—subject to Strong Non-Interference (`SNI`) / Probe-Isolating Non-Interference (`PINI`) composability under hardware glitches.

#### 4.1 Masking Domain Transitions Across ML-KEM and ML-DSA Pipelines

| Pipeline Stage | Natural Masking Domain | Conversion / Cost Bottleneck | Key Literature & Design Patterns |
| --- | --- | --- | --- |
| **NTT / InvNTT / Poly Add / Basemul** | Arithmetic $\bmod q$ | Strictly linear in secret shares! Apply NTT independently to each share $A_i$ ($O(n)$ overhead, zero fresh randomness) | Bos et al. (TCHES 2021, `10.46586/tches.v2021.i4.173-214`); zero inter-share mixing inside NTT butterflies |
| **SHAKE-128 / SHAKE-256 (Keccak-f[1600])** | Boolean ($\mathbb{F}_2$) | Linear layers ($\theta, \rho, \pi, \iota$) run per-share; non-linear $\chi$ (`a ^ (~b & c)`) requires $O(n^2)$ ISW/DOM masked ANDs + fresh randomness per 1600-bit round (24 rounds) | Dominates runtime in higher-order masked ML-KEM/ML-DSA because FO re-encryption and ML-DSA `y` sampling invoke Keccak extensively |
| **ML-KEM `CBD` Noise Sampling** | Boolean -> Arithmetic $\bmod q$ | `B2A_q` conversion of small $\eta \in \{2, 3\}$ centered binomial bits | Bitsliced `B2A`/`A2B` gadgets (Bronchain & Cassiers, TCHES 2022, `10.46586/tches.v2022.i4.553-588`) amortize conversion across 32/64 coefficients in parallel |
| **ML-KEM `Compress_1` & FO Ciphertext Compare** | Arithmetic $\bmod q$ -> Boolean | `A2B` modulus-to-bit extraction (`poly_tomsg`) + masked comparison of $c \stackrel{?}{=} c'$ without unmasking $c'$ | Naive unmasked $c \stackrel{?}{=} c'$ leaks $m'$ via chosen-ciphertext power templates; masked hash-based comparison computes masked $H(c')$ or zero-testing over Boolean shares before unmasking a single 1-bit decision (Bos et al., TCHES 2021) |
| **ML-DSA Signing Rejection Sampling** | Arithmetic $\bmod q$ -> Infinity-norm bound check | Four sequential checks on secret-dependent vectors ($z, r_0, c t_0, h$); converting 23-bit `q = 8380417` coefficients via `A2B` at order $d$ is expensive | Coron et al. (TCHES 2023, `10.46586/tches.v2023.i4.110-145`) modulus-independent high-order rejection gadgets; **SUCRE** (TCHES 2026) shuffle-and-unmask preserves $\Vert z \Vert_\infty$ while randomly permuting coefficients before bound testing |

#### 4.2 ML-DSA Rejection-Loop Anatomy and Side-Channel / Fault Hazards

In `pq-crystals/dilithium` (`ref/sign.c:132-184`), each signing iteration samples $y$ from `rhoprime` and `nonce++`, computes $w = A y$, decomposes $w = w_1 \cdot 2\gamma_2 + w_0$, hashes $c = H(\mu \mathbin{\|} w_1)$, and then evaluates **four sequential abort branches (`goto rej`)**:
1. Line 161: $\|z\|_\infty \ge \gamma_1 - \beta$ where $z = y + c s_1$.
2. Line 170: $\|r_0\|_\infty \ge \gamma_2 - \beta$ where $r_0 = \text{LowBits}(w - c s_2)$.
3. Line 177: $\|c t_0\|_\infty \ge \gamma_2$.
4. Line 182: $\text{wt}(h) > \omega$ where $h = \text{MakeHint}(-c t_0, w - c s_2 + c t_0)$.

Direct evaluation of the FIPS 204 acceptance bounds (`Probe 1B`, `Basis: execution + derived`) yields:

| Parameter Set | $P(\Vert z \Vert_\infty < \gamma_1 - \beta)$ | $P(\Vert r_0 \Vert_\infty < \gamma_2 - \beta)$ | Combined $P(z \land r_0)$ | Expected Iterations $E[\text{iters}] \ge 1/P$ |
| --- | ---: | ---: | ---: | ---: |
| **ML-DSA-44** | 0.5436 | 0.4321 | 0.2349 | $\ge 4.26$ |
| **ML-DSA-65** | 0.6196 | 0.3166 | 0.1962 | $\ge 5.10$ |
| **ML-DSA-87** | 0.6635 | 0.3912 | 0.2595 | $\ge 3.85$ |

Three physical attack classes exploit this exact loop structure:
- **Early-Abort & Rejected-Trial Leakage:** Short-circuiting after Check 1 vs. Check 2 vs. Check 3 reveals *which* norm bound failed (correlating directly with $\|c s_1\|_\infty$ vs. $\|c s_2\|_\infty$); furthermore, rejected trials still expose power/EM traces of $y$, $c s_1$, and $c s_2$ under non-profiled template attacks even though the rejected $z$ is never published. Hardened masked implementations must evaluate all bound checks unconditionally (or mask the abort decision) and protect rejected iterations identically to accepted ones.
- **Loop-Abort Fault Injection:** Glitching the `nonce` loop or skipping Check 1 (`polyvecl_chknorm(&z, ...)`) or Check 2 forces release of an out-of-bounds signature $z = y + c s_1$ whose distribution is no longer independent of $s_1$, or releases a partially computed $y$ with zeroed limbs, enabling lattice key recovery from a small number of faulted signatures.
- **Statistical Ineffective Fault Analysis (`SIFA`, Dobraunig et al., TCHES 2018, `10.13154/tches.v2018.i3.547-572`) Against Masked + Fault-Detected Designs:** A widespread engineering anti-pattern combines power masking with naive dual-modular redundancy (DMR) that *suppresses output whenever a fault alters the result*. Under a biased hardware fault (e.g., stuck-at-0 with probability $p_f = 0.5$), `Probe 1D` (`Basis: execution + derived`) shows:
  - For an **unmasked** sensitive bit $s \in \{0,1\}$ (such as an unmasked rejection flag or FO check bit), $\Pr[\text{ineffective} \mid s=0] = 1.0$ vs. $\Pr[\text{ineffective} \mid s=1] = 0.5$, yielding Bayes posterior $P(s=0 \mid \text{ineffective}) = 2/3$—leaking $s$ purely from *fault-free* accepted outputs!
  - For a **single linear share** $s_0$ in $s = s_0 \oplus s_1$, $\Pr[\text{ineffective} \mid s=0] = \Pr[\text{ineffective} \mid s=1] = 0.75$ ($P(s=0 \mid I) = 0.5000$, zero leak).
  - For an **unmasked or improperly combined non-linear Keccak $\chi$ gate** $y = x_0 \oplus (\neg x_1 \land x_2)$ with stuck-at-0 on $\neg x_1$, $\Pr[\text{ineffective} \mid x_2=0] = 1.0$ vs. $\Pr[\text{ineffective} \mid x_2=1] = 0.5$, again yielding $P(x_2=0 \mid \text{ineffective}) = 2/3$.
  - **Architectural invariant:** To prevent SIFA, fault countermeasures MUST operate at the **masked share / Toffoli-gate level** (e.g., error-correcting masked gadgets or infective computation that guarantees fault propagation independent of unmasked secrets), NEVER by unmasking a check and suppressing output on mismatch.

### 5. Streaming Stack-Bounded Verification (2 KiB RoTs) and SPDM/TLS Wire Fragmentation

Basis: source (`pq-crystals/dilithium`, `celabshq/libcrux`, `DMTF/libspdm`) + execution (Probe 1B) + documentation (`AFRICACRYPT 2019`, `AFRICACRYPT 2022`, `draft-ietf-tls-ecdhe-mlkem`, `DSP0274 v1.4`)

#### 5.1 Embedded SRAM / Stack Pressure vs. Streaming Schedules

In `pq-crystals/dilithium` (`ref/sign.c:98-99`), the signing function allocates the entire expanded matrix `mat[K]` (each entry a `polyvecl` of $L$ polynomials of 256 `int32_t` = 1,024 B) plus 8 polynomial vectors (`s1, y, z, t0, s2, w1, w0, h`) and `cp` directly on the stack (`Basis: source + execution`):

| Algorithm | Reference `sign.c` Polynomial Stack (B) | Expanded Matrix $A$ Alone (B) | Polynomial Vectors Alone (B) | Ratio vs. 2 KiB RoT Stack | Streaming / Constrained Embedded Floor |
| --- | ---: | ---: | ---: | ---: | --- |
| **ML-DSA-44** | 50,176 B (49.0 KiB) | 16,384 B | 33,792 B | **24.5x** | Bos, Renes, Sprenkels (AFRICACRYPT 2022): **< 3 KiB verify, < 7 KiB sign/keygen** via on-the-fly matrix-element streaming, packed storage, and schoolbook fallback |
| **ML-DSA-65** | 77,824 B (76.0 KiB) | 30,720 B | 47,104 B | **38.0x** | Same streaming discipline; never materialize `mat[K]` in SRAM |
| **ML-DSA-87** | 120,832 B (118.0 KiB) | 57,344 B | 63,488 B | **59.0x** | Same streaming discipline; requires re-expanding `y` or streaming `w1` incrementally into SHAKE-256 |

For ML-KEM, storing a single $256 \times \text{int16\_t}$ polynomial consumes 512 B; a 2 KiB embedded RoT stack can hold at most 2–3 active polynomials plus a 200-byte Keccak-f[1600] state (`uint64_t[25]`), forcing three mandatory implementation and verification patterns:
1. **On-the-Fly Matrix $A_{i,j}$ Generation & Accumulate:** Stream each $(i,j)$ polynomial from `SHAKE-128(rho || j || i)` into a single reusable 512 B (ML-KEM) or 1,024 B (ML-DSA) scratch buffer, immediately multiply-accumulate into the running output polynomial, and discard $A_{i,j}$ (Botros, Kannwischer, Schwabe, AFRICACRYPT 2019; Bos, Renes, Sprenkels, AFRICACRYPT 2022).
2. **Incremental Sponge Absorption/Squeezing:** Absorb serialized $w_1$ or ciphertext chunks incrementally into a single 200 B Keccak state rather than buffering full $K \times \text{POLYW1\_PACKEDBYTES}$ arrays.
3. **Incremental / Split-Key Encapsulation (`celabshq/libcrux`):** `libcrux-ml-kem/src/ind_cca/incremental/README.md:25-63` demonstrates splitting the public key into `pk1 = (rho, H(ek))` (64 B) and `pk2 = serialized t` (`384k` B) so a peer can generate ciphertext component $c_1$ immediately upon receiving the 64 B `pk1` while streaming `pk2` for $c_2$, paired with a mandatory `validate_pk` consistency check binding `pk1` and `pk2` before finalizing `c2`.

#### 5.2 SPDM 1.4 (`DSP0274`) & TLS 1.3 Wire-MTU Fragmentation

Direct inspection of `DMTF/libspdm` @ `3f1253df61ef1af917f1f18ce40db065e93ff82c` (`include/industry_standard/spdm.h:482-524,1398-1482`; `library/spdm_requester_lib/libspdm_req_send_receive.c:382-470`) establishes exact SPDM 1.4 PQC wire primitives:
- **PQC Algorithm Negotiation (SPDM 1.4):** `SPDM_NEGOTIATE_ALGORITHMS` adds `ALG_TYPE_REQ_PQC_ASYM_ALG = 6` (`ML_DSA_{44,65,87}` and all 12 `SLH_DSA_{SHA2,SHAKE}_{128,192,256}{S,F}` bitmasks) and `ALG_TYPE_KEM_ALG = 7` (`ML_KEM_{512,768,1024}` bitmasks `0x1`/`0x2`/`0x4`).
- **MTU Chunking & Sequence-Number Widening:** SPDM 1.2's minimum `DataTransferSize` (`SPDM_MIN_DATA_TRANSFER_SIZE_VERSION_12`) is **42 bytes** (common MCTP/SMBus/I2C baseline MTUs are 64–256 B; PCIe DOE MTUs are typically 256–4096 B). `spdm_chunk_send_request_t` has a 12-byte header (plus 4-byte `large_message_size` in chunk 0). In SPDM 1.2/1.3, `chunk_seq_no` is `uint16_t` (capping transfers at `65536 * (min_dts - 12) - 4` bytes, `libspdm_req_send_receive.c:389-391`); **SPDM 1.4 widens `chunk_seq_no` to `uint32_t`** (`spdm_chunk_send_request_14_t`, `spdm_chunk_get_request_14_t`, `spdm_chunk_response_response_14_t`) while keeping the 12-byte header footprint by consuming the 2-byte `reserved` field.

Computed exact chunk counts (`Probe 1B`, `Basis: source + execution`):

| Post-Quantum Payload | Wire Size (B) | `DTS = 42 B` (SPDM min) | `DTS = 64 B` (MCTP baseline) | `DTS = 256 B` (DOE small) | `DTS = 4096 B` (DOE large) |
| --- | ---: | ---: | ---: | ---: | ---: |
| **ML-KEM-768 ciphertext** | 1,088 | 37 chunks | 21 chunks | 5 chunks | 1 (no chunking) |
| **ML-KEM-1024 ciphertext** | 1,568 | 53 chunks | 31 chunks | 7 chunks | 1 (no chunking) |
| **ML-DSA-65 signature** | 3,309 | 111 chunks | 64 chunks | 14 chunks | 1 (no chunking) |
| **ML-DSA-87 signature** | 4,627 | 155 chunks | 90 chunks | 19 chunks | 2 chunks |
| **SLH-DSA-128s signature** | 7,856 | 262 chunks | 152 chunks | 33 chunks | 2 chunks |
| **SLH-DSA-128f signature** | 17,088 | 570 chunks | 329 chunks | 71 chunks | 5 chunks |
| **SLH-DSA-256f signature** | 49,856 | 1,662 chunks | 959 chunks | 205 chunks | 13 chunks |
| **ML-DSA-87 3-cert chain (~15 KB)** | 15,360 | 513 chunks | 296 chunks | 63 chunks | 4 chunks |

On internet transports, `draft-ietf-tls-ecdhe-mlkem` defines hybrid TLS 1.3 key shares (`X25519MLKEM768` = 1,216 B ClientHello key share + 1,120 B ServerHello ciphertext, `SecP256r1MLKEM768`, `SecP384r1MLKEM1024`), where `X25519MLKEM768` pushes typical TLS `ClientHello` frames over a single ~1,460 B TCP MSS, triggering TCP record fragmentation and middlebox tolerance constraints—whereas `ML-KEM-768` + `X25519` retains classical ECDH security even if ML-KEM were cryptanalyzed.

### 6. Agile Proof-System Migration: Hash-Based FRI / Circle-STARK Post-Quantum Proof Receipts

Basis: source (`Plonky3/Plonky3` `fri` & `security` crates) + execution (Probe 1C) + documentation (`JACM 2023`, `ePrint 2019/834`, `ePrint 2024/278`)

Classical elliptic-curve SNARKs (`Groth16`, `PLONK` over KZG/BN254/BLS12-381, `Bulletproofs`/IPA) rely on discrete-logarithm or pairing hardness and are completely broken in polynomial time by a cryptographically relevant quantum computer (enabling forged proofs—not merely lost zero-knowledge—in long-lived proof archives and transparent logs). Replacing them with **hash-based Interactive Oracle Proofs (IOPs)** compiled via the **BCS (Ben-Sasson–Chiesa–Spooner) Merkle-commitment + Fiat–Shamir transform** (`FRI` or `Circle STARKs`, Haböck–Levit–Papini `ePrint 2024/278`) anchors soundness solely in collision/preimage resistance of a cryptographic hash/sponge (e.g., SHA-256, SHA3, Blake3, Poseidon2) in the Quantum Random Oracle Model (`QROM`, Chiesa–Manohar–Spooner, TCC 2019 / `ePrint 2019/834`, `10.1007/978-3-030-36033-7_1`).

#### 6.1 Proven vs. Conjectured Soundness Regimes in `Plonky3` (`0d803737...`)

Direct inspection of `Plonky3/Plonky3` (`fri/src/config.rs:34-152`, `security/src/assumption.rs:1-110`, `security/src/fri.rs:1-140`) exposes four critical verification-engineering invariants that govern post-quantum FRI receipt sizing:

1. **Three Distinct Grinding Sites (`FriParameters`):** `Plonky3` separates `batch_proof_of_work_bits` (before sampling the opening-batching challenge $\alpha$), `commit_proof_of_work_bits` (before each FRI folding challenge), and `query_proof_of_work_bits` (before sampling Merkle query indices). As `fri/src/config.rs:42-53` explains, on wide instances over small 31-bit prime fields (`BabyBear`/`KoalaBear` with degree-4/5 extensions), the **batch-opening linear-combination error**—not query soundness—dominates *proven* soundness, so grinding `batch_proof_of_work_bits` is mandatory to keep query counts bounded.
2. **Multi-Height Curve-Degree Trap (`security/src/fri.rs:40-59`):** `Plonky3` explicitly warns that when shorter committed matrices join a later FRI folding round of arity $a$, they contribute a curve of degree $a$ rather than $a - 1$, causing naive single-height commit bounds to undercharge soundness by **1.0 bit at arity 2** and **0.42 bits at arity 4** per round.
3. **Zero-Blowup & Unauthenticated-Width Rejections (`fri/src/verifier.rs:99-215`):** `FriError` explicitly enforces `log_blowup > 0` (at rate $\rho = 1$, every word is a valid codeword and arbitrary false evaluations verify), `num_queries > 0`, `max_log_arity > 0`, exact `CommitPhaseOpeningsCountMismatch` / `CommitRoundCountMismatch` checks (preventing zip truncation over unabsorbed lists!), and rejects any committed matrix opened at zero points (`MatrixWithoutOpeningPoints`) because its width cannot be authenticated.
4. **Query Count Gap Across Proximity Regimes (`Probe 1C`, `Basis: source + execution`):** Comparing `Plonky3`'s exact formulas across blowups $2^1, 2^2, 2^3$ ($\rho = 1/2, 1/4, 1/8$) with 16-bit query PoW and a 124-bit extension field (`BabyBear^4`):

| Target Classical $\lambda$ (w/ 16-bit PoW) | Blowup $1/\rho$ | Unique Decoding ($\alpha = \frac{1+\rho}{2}$, proven) | Johnson Bound ($\delta = 1 - \sqrt{\rho} - \frac{\sqrt{\rho}}{20}$, proven) | Random-Words (`2025/2010`, conjectured) | Legacy `ethSTARK` (`2021/582`, conjectured) |
| --- | --- | ---: | ---: | ---: | ---: |
| **100 bits** (84 query bits) | $2\times$ ($\rho=1/2$) | **203 queries** (0.415 b/q) | **196 queries** (0.430 b/q) | **87 queries** (0.972 b/q) | **84 queries** (1.000 b/q) |
| **100 bits** (84 query bits) | $4\times$ ($\rho=1/4$) | **124 queries** (0.678 b/q) | **91 queries** (0.930 b/q) | **43 queries** (1.960 b/q) | **42 queries** (2.000 b/q) |
| **100 bits** (84 query bits) | $8\times$ ($\rho=1/8$) | **102 queries** (0.830 b/q) | **59 queries** (1.430 b/q) | **29 queries** (2.949 b/q) | **28 queries** (3.000 b/q) |
| **128 bits** (112 query bits) | $2\times$ ($\rho=1/2$) | **270 queries** (0.415 b/q) | **261 queries** (0.430 b/q) | **116 queries** (0.972 b/q) | **112 queries** (1.000 b/q) |
| **128 bits** (112 query bits) | $4\times$ ($\rho=1/4$) | **166 queries** (0.678 b/q) | **121 queries** (0.930 b/q) | **58 queries** (1.960 b/q) | **56 queries** (2.000 b/q) |
| **128 bits** (112 query bits) | $8\times$ ($\rho=1/8$) | **135 queries** (0.830 b/q) | **79 queries** (1.430 b/q) | **38 queries** (2.949 b/q) | **38 queries** (3.000 b/q) |

**Post-Quantum (`QROM`) Security Adjustment (`Basis: derived + documentation`):**
- Under Grover's algorithm, a quantum adversary with $Q$ oracle queries can find a hash preimage or grind a $w$-bit PoW nonce in $O(2^{w/2})$ quantum queries, and finds a BHT/CNS hash collision in $O(2^{h/3})$ (or $O(2^{h/2})$ memory-constrained) queries; therefore, **128-bit post-quantum receipt soundness requires at least 256-bit Merkle/Fiat–Shamir hash digests** (e.g., SHA3-256 / Blake3-256 / 256-bit sponge capacity) AND **halves the effective quantum security contribution of PoW grinding** (a 16-bit classical PoW adds at most ~8 bits against an unconstrained quantum grinder, requiring additional FRI queries or larger `query_proof_of_work_bits` for strict QROM targets).
- Even with high-arity folding and $8\times$ blowup, STARK proof receipts typically occupy **40–200 KiB** (vs. ~200 B for Groth16), making **agile receipt envelopes**—tagging every stored proof with explicit `(scheme_id, hash_id, proximity_regime, qrom_bits)` metadata and supporting dual/migrated commitment roots—essential for long-lived verification artifact stores.

## Boundaries

- **Physical silicon power/EM leakage of `libcrux`, `formosa-libjade`, and `mlkem-native`:** *known not to apply / unsupported*. None of these three formally verified software libraries implements Boolean/Arithmetic masking or hardware fault countermeasures at the pinned commits (`mlkem-native/README.md:82` explicitly marks power/EM, speculative execution, and fault injection out of scope; `libcrux` and `formosa-libjade` target timing/cache and, for `formosa-libjade`, speculative timing side channels only).
- **End-to-end LLVM constant-time preservation for Rust/C (`libcrux`, `mlkem-native` C90 frontend):** *unsupported* by existing proofs. Neither `hax/F*` nor `CBMC` models LLVM IR-to-machine-code lowering; `libcrux` explicitly relies on `black_box` / `volatile` barriers plus post-compilation assembly auditing, and `Probe 1E` confirms that compiler optimization flags (`-Os`) can reintroduce variable-time instructions (`divl`) for source-level `/` operations.
- **ARMv7-M / Cortex-M4 / RISC-V cycle-accurate hardware benchmarks and physical fault-injection experiments:** *not examined* directly on physical silicon; embedded RAM footprints (< 3 KiB verify, < 7 KiB sign for ML-DSA) are drawn from peer-reviewed literature (AFRICACRYPT 2019, AFRICACRYPT 2022) and analytical stack sizing against `pq-crystals/dilithium` `ref/sign.c`.
- **Conjectured Capacity-Bound FRI security (`Plonky3` `SecurityAssumption::CapacityBound`):** *unknown* mathematically. `Plonky3/security/src/fri.rs:19-20` explicitly marks `CapacityBound` unsupported for FRI's commit-phase analysis, and `conjectured_soundness_bits` (`fri/src/config.rs:97-104`) relies on unproved Reed–Solomon correlated-agreement conjectures beyond the Johnson bound.
- **Formally verified masked ML-KEM/ML-DSA machine code:** *not examined*. Composing high-order glitch-resistant `PINI`/`DOM` masking proofs (e.g., `maskVerif`/`Silver`) with end-to-end EasyCrypt/F*/HOL-Light functional correctness and SIFA-resistant fault-countermeasure proofs remains an active research frontier rather than a turnkey capability in the inspected repositories.
- **SLH-DSA (`FIPS 205`) mechanized assembly proofs:** *not examined* in this report; `libcrux`, `formosa-libjade`, and `mlkem-native` focus on lattice schemes (ML-KEM / ML-DSA) at the pinned revisions.

## Evidence

### Primary Repositories and Source Coordinates (Observed 2026-11-19)

1. **`pq-crystals/kyber`** @ `3edd5af5991927164edd4aacebfcbee00b8064e7`:
   - `ref/poly.c:19-71` (`poly_compress`, commented KyberSlash2 division lines 33 & 53 and Barrett fixes `80635 >> 28` w/ `+1665` for $d=4$ and `40318 >> 27` w/ `+1664` for $d=5$); `ref/poly.c:151-158` (`poly_frombytes` unvalidated `& 0xFFF` decode); `ref/poly.c:192-211` (`poly_tomsg`, commented KyberSlash1 division line 202 and Barrett fix `80635 >> 28` w/ `+1665`).
   - `ref/polyvec.c:15-77` (`polyvec_compress`, commented division lines 27 & 57 and Barrett fixes `645084 >> 31` w/ `+1664` for $d=11$ and `1290167 >> 32` w/ `+1665` for $d=10$).
   - `ref/reduce.c:16-42` (`montgomery_reduce` $R=2^{16}$, `barrett_reduce` $v=20159$).
   - `ref/kem.c:140-170` (`crypto_kem_dec` FO re-encryption, `verify`, `rkprf`, `cmov`).
2. **`pq-crystals/dilithium`** @ `d35ba3fe5449bee3e6d43e1f296c3ca818bd36be`:
   - `ref/sign.c:85-189` (`crypto_sign_signature_internal`: lines 98–100 stack allocations `mat[K], s1, y, z, t0, s2, w1, w0, h, cp`; lines 132–184 four sequential `goto rej` predicates at lines 161, 170, 177, 182); `ref/sign.c:218-235` (FIPS 204 `pre = (0, ctxlen, ctx)` prefix and hedged/deterministic `rnd`).
3. **`celabshq/libcrux`** (redirected from `cryspen/libcrux`) @ `e882e13e3f6b6482ea7622d786b499f504a76e97`:
   - `libcrux-ml-kem/README.md:15-175` (API, `validate_public_key`/`validate_private_key`, `check-secret-independence` via `libcrux-secrets`, `incremental`, `pqcp`).
   - `libcrux-ml-kem/proofs/verification_status.md:1-55` (exact per-module panic-free and correctness counts across Generic, Portable, AVX2, NEON).
   - `libcrux-ml-kem/src/constant_time_ops.rs:3-232` (`ct_barrier_u8`, Eurydice `black_box` no-op caveat and `intrinsics/libcrux_ct_barrier.h` `volatile` fallback, F* loop invariants for `compare` and `select_ct`).
   - `libcrux-ml-kem/src/vector/portable/compress.rs:31-130` (`compress_message_coefficient` branchless shift-XOR folding; `compress_ciphertext_coefficient` universal 64-bit `10_321_340 >> 35` w/ `+1664`).
   - `libcrux-ml-kem/src/ind_cca/incremental/README.md:1-63` (split `pk1`/`pk2` incremental encapsulation and `validate_pk`).
4. **`Formosa-Crypto/formosa-mlkem`** @ `d1e64d5fee2157b47e5030c4f0bdc07bb36a7bde` and **`formosa-crypto/formosa-libjade`** @ `90ba5dc4d9da2b6950589c58a52282caa1dbfdfd`:
   - `formosa-mlkem/README.md`: archival pointer to `formosa-crypto/formosa-libjade`.
   - `formosa-libjade/README.md:38-180` (ML-KEM 512/768/1024 & ML-DSA 44/65/87 `avx2/sct` implementations, `MLKEMSecurity.ec` IND-CCA & `MLDSA_Security.ec` EUF-CMA, `meta.toml` `claims`/`provsec`, `jasmin-ct` CT/SCT checks, C header TCB).
   - `formosa-libjade/proofs/mlkem/avx2/sct/correctness/768/correctness768.ec:116-171` (`keygen_correct`, `encaps_correct`, `decaps_correct` EasyCrypt equivalence lemmas).
5. **`pq-code-package/mlkem-native`** @ `c179cea863ac90024e11b03a3cfe4f2ccd2e9629`:
   - `README.md:13-105` (C90 + CBMC memory/type safety, HOL-Light/`s2n-bignum` object-code correctness & CT on AArch64/x86-64, SLOTHY superoptimization, explicit out-of-scope note for power/EM/speculative/fault attacks).
   - `mlkem/src/compress.c:33-149` (CBMC `__contract__` and `__loop__` annotations requiring canonical `array_bound(a->coeffs, 0, MLKEM_N, 0, MLKEM_Q)`).
6. **`Plonky3/Plonky3`** @ `0d803737b681774186cd283b1fd2d8e493655c82`:
   - `fri/src/config.rs:34-216` (`FriParameters`, 3 PoW grinding sites, `conjectured_soundness_bits`, `security_regime`, `grinding_sites`).
   - `fri/src/verifier.rs:30-215` (`FriError` structural/soundness guards including `ZeroBlowup`, `ZeroQueries`, `CommitPhaseOpeningsCountMismatch`, `MatrixWithoutOpeningPoints`).
   - `security/src/assumption.rs:1-110` (`SecurityAssumption::{UniqueDecoding, JohnsonBound, CapacityBound}` and references `[BCI+20]`, `[BCSS25]`, `[Hab25]`, `[BCGM26]`, `[DKT26]`).
   - `security/src/fri.rs:1-140` (`FriRegime`, multi-height curve-degree warning, `conjectured_error` random-words formula).
7. **`DMTF/libspdm`** @ `3f1253df61ef1af917f1f18ce40db065e93ff82c`:
   - `include/industry_standard/spdm.h:53-54,93-94,116-120,435-436,482-524,1398-1482` (SPDM 1.4 ML-DSA/SLH-DSA/ML-KEM algorithm IDs, `spdm_chunk_send_request_t` vs. 32-bit `chunk_seq_no` `spdm_chunk_send_request_14_t`).
   - `library/spdm_requester_lib/libspdm_req_send_receive.c:382-470` (`max_chunk_data_transfer_size` calculation and chunk framing).

### Normative Standards & Peer-Reviewed Literature

- NIST `FIPS 203` (`10.6028/NIST.FIPS.203`), `FIPS 204` (`10.6028/NIST.FIPS.204`), `FIPS 205` (`10.6028/NIST.FIPS.205`), published 2024-08-13.
- Almeida et al., *Formally Verifying Kyber Episode IV: Implementation Correctness*, TCHES 2023(3):164–193 (`10.46586/tches.v2023.i3.164-193`); Almeida et al., *Formally Verifying Kyber — Episode V: Machine-Checked IND-CCA Security and Correctness of ML-KEM in EasyCrypt*, CRYPTO 2024 (`10.1007/978-3-031-68391-6_12`, `ePrint 2024/843`).
- Bhargavan et al., *hax: Verifying Security-Critical Rust Software using Multiple Provers*, VSTTE / LNCS 2025 (`ePrint 2025/142`); Bhargavan et al., *Formal Security and Functional Verification of Cryptographic Protocol Implementations in Rust*, ACM CCS (`ePrint 2025/980`).
- Bernstein et al., *KyberSlash: Exploiting secret-dependent division timings in Kyber implementations* (`https://kyberslash.cr.yp.to/`).
- Dobraunig et al., *SIFA: Exploiting Ineffective Fault Inductions on Symmetric Cryptography*, TCHES 2018(3):547–572 (`10.13154/tches.v2018.i3.547-572`).
- Bos et al., *Masking Kyber: First- and Higher-Order Implementations*, TCHES 2021(4):173–214 (`10.46586/tches.v2021.i4.173-214`); Bronchain & Cassiers, *Bitslicing Arithmetic/Boolean Masking Conversions for Fun and Profit*, TCHES 2022(4):553–588 (`10.46586/tches.v2022.i4.553-588`); Coron, Gérard, Trannoy, Zeitoun, *Improved Gadgets for the High-Order Masking of Dilithium*, TCHES 2023(4):110–145 (`10.46586/tches.v2023.i4.110-145`); SUCRE, TCHES 2026.
- Botros, Kannwischer, Schwabe, *Memory-Efficient High-Speed Implementation of Kyber on Cortex-M4*, AFRICACRYPT 2019; Bos, Renes, Sprenkels, *Dilithium for Memory Constrained Devices*, AFRICACRYPT 2022.
- Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed-Solomon Codes*, FOCS 2020 / JACM 70(5):31 (2023, `10.1145/3614423`, `ePrint 2020/654`); Chiesa, Manohar, Spooner, *Succinct Arguments in the Quantum Random Oracle Model*, TCC 2019 (`10.1007/978-3-030-36033-7_1`, `ePrint 2019/834`); Haböck, Levit, Papini, *Circle STARKs*, `ePrint 2024/278`.

### Executable Micro-Probes (Observed 2026-11-19)

1. **Exhaustive `Compress_d` & `barrett_reduce` Verifier (Python 3.13.15):**
   - Verified `kyber_compress` and `libcrux_compress` against exact FIPS 203 Eq. (4.7) over all 3,329 inputs $x \in [0, 3328]$ for $d \in \{1, 4, 5, 10, 11\}$ (`0` mismatches), verified single-offset perturbation failures (`x = 3225` at $d=4$, `x = 52` at $d=5$, `x = 2079` at $d=10$, `x ∈ {625, 1875, 3125}` at $d=11$, `libcrux` `x = 625` at $d=11$), and verified `barrett_reduce` (`v = 20159`) across all 65,536 `int16_t` inputs -> `[-1664, 1664]` with `0` congruence errors.
2. **GCC 15.2.0 (`Debian 15.2.0-14`, x86-64) KyberSlash Codegen Probe:**
   - Command: `gcc -Os -S -o - /tmp/kyberslash_probe.c` emitted `divl %ecx` in `poly_tomsg_div` (`(((t << 1) + 1664U) / 3329U) & 1U`), whereas `gcc -O2` emitted `imulq $989558401` + shifts and `poly_tomsg_barrett` (`* 80635U >> 28`) emitted `imull $80635` + `shrl $28` with zero `divl` across `-O0`, `-Os`, and `-O2`.
3. **Stack Sizing, SPDM Chunking, FRI Query-Count, and SIFA Posterior Probes (Python 3.13.15):**
   - Produced the exact ML-DSA stack bytes (`50,176` / `77,824` / `120,832` B), ML-DSA rejection probabilities ($E[\text{iters}] \ge 4.26 / 5.10 / 3.85$), SPDM chunk counts (1 to 1,662 chunks), FRI query tables (28 to 270 queries across regimes), and exact SIFA ineffective-fault posterior probabilities ($2/3$ vs. $1/2$).

## Revalidation

1. **Re-verify Compiler Division Emission (`KyberSlash` Regression Gate, ~1 s):** Run the minimal C probe on any target compiler (`gcc`, `clang`, `rustc` via `cargo asm`) across `-O0`, `-Os`, `-Oz`, `-O2`, `-O3` and assert zero `div`/`idiv`/`udiv`/`sdiv`/`__aeabi_uidiv` instructions in the emitted assembly:
   ```bash
   cat <<'EOF' > /tmp/ks_check.c
   #include <stdint.h>
   uint32_t f_div(int16_t a) { uint32_t t=(uint32_t)a; t+=(uint32_t)((int16_t)t>>15)&3329U; return (((t<<1)+1664U)/3329U)&1U; }
   uint32_t f_bar(int16_t a) { uint32_t t=(uint32_t)a; t+=(uint32_t)((int16_t)t>>15)&3329U; return ((((t<<1)+1665U)*80635U)>>28)&1U; }
   EOF
   for opt in -O0 -Os -O2; do echo "=== $opt ==="; gcc $opt -S -o - /tmp/ks_check.c | grep -E '^(f_|[[:space:]]+(div|idiv|imul))'; done
   ```
2. **Re-verify Constant-Time `Compress_d` Bit-Exactness (~0.1 s):** Whenever adopting new Barrett multipliers or rounding constants for $q = 3329$, run an exhaustive 3,329-element Python check against `(((x << (d + 1)) + 3329) // 6658) & ((1 << d) - 1)` for every supported $d \in \{1, 4, 5, 10, 11\}$ rather than relying on randomized KATs, which easily miss 1-in-3,329 boundary errors.
3. **Re-check Upstream Verification Manifests (~5 s):**
   - `celabshq/libcrux`: inspect `libcrux-ml-kem/proofs/verification_status.md` and `libcrux-ml-kem/src/constant_time_ops.rs` at the target revision to check whether `ind_cpa` / `neon` proofs or Eurydice barrier handling changed.
   - `formosa-crypto/formosa-libjade`: inspect `src/{mlkem,mldsa}/<target>/<profile>/<param>/meta.toml` for `claims` and `provsec` (`functional` vs. `reduction` vs. `leakage-aware reduction`).
   - `pq-code-package/mlkem-native`: inspect `README.md`, `SOUNDNESS.md`, and `proofs/{cbmc,hol_light}` for supported backends and verified scopes.
   - `Plonky3/Plonky3`: inspect `security/src/assumption.rs` and `security/src/fri.rs` to verify whether `CapacityBound` or updated proximity-gap theorems alter query counts and grinding-site assignments for target QROM security levels.
4. **Full Re-investigation Needed:** Any claim regarding physical power/EM side-channel resistance (TVLA / probing order) or laser/EM fault injection (SIFA) requires dedicated gate-level or silicon lab evaluation on the exact target implementation and cannot be revalidated by the software probes above.
