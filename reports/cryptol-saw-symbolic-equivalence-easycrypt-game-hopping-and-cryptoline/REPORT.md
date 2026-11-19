# Symbolic Equivalence, Game-Hopping Reductions, Algebraic-SMT Entailment, and Protocol Information-Flow Types across Cryptol/SAW, EasyCrypt/Jasmin, CryptoLine, and Owl

## Summary

Verifying cryptographic software *after* or *alongside* hand-tuned optimization—and linking primitive arithmetic up to computational protocol security—splits into four complementary verification architectures that solve distinct scalability bottlenecks where pure SMT bit-blasting or single-language refinement breaks down:

1. **Cryptol + SAW (`GaloisInc/cryptol`, `GaloisInc/saw-script`, `aws/aws-lc`, `awslabs/aws-lc-verification`)**: Proves bit-precise functional equivalence and memory safety (no out-of-bounds, uninitialized-read, or C UB) between readable **Cryptol** specs and compiled **LLVM bitcode**, **x86-64/AArch64 machine code**, or **Rust MIR** (`mir-json` schema v14) using **Crucible** symbolic execution and compositional function overrides (`llvm_verify`, `llvm_verify_x86`, `llvm_verify_fixpoint_chc_x86'`). Continuous CI verification on `aws/aws-lc` reveals a concrete operational constraint: compositional overrides match callee symbols, so `aws-lc-verification` patches `aws-lc` with **`__attribute__((noinline))`** (`25` `noinline-*.patch` files, including `noinline-fiat_p384_sub.patch`) and **`__attribute__((optnone))`** (`cmovznz.patch`), enumerates explicit aliasing variants (`p384_field_mul_same_l_spec`), and falls back to **Coq** (`CryptolToCoq_equiv.v`) when elliptic-curve group proofs outgrow SMT bit-blasting.
2. **EasyCrypt + Jasmin / `libjade` (`EasyCrypt/easycrypt`, `jasmin-lang/jasmin`, `formosa-crypto/formosa-libjade`)**: Mechanizes **Probabilistic Relational Hoare Logic (`pRHL`)** game-hopping reductions (`IND-CCA`, `EUF-CMA`, `upto bad` failure-event bounds, adversarial complexity) and links them via `jasmin2ec` (`toEC.ml`) to assembly-level **Jasmin** programs compiled by a Rocq-verified compiler (`Compiler.v`) with `jasmin-ct` constant-time and speculative constant-time (`--doit` + selective SLH) type checking. `formosa-libjade` explicitly separates three `ProvSec` assurance tiers (`functional`, `reduction`, `leakage-aware reduction`) and leaves C wrapper headers (`src/include/`) and `jasmin2ec`/`eclib` semantic alignment inside the TCB.
3. **CryptoLine (`fmlab-iis/cryptoline`)**: Solves the exponential timeout of SMT bitvector solvers (`QF_BV`) on wide multi-limb and NTT multiplications by **splitting every verification query into two orthogonal passes**: (a) converting bitvector instructions (`split`, `join`, `mull`, `adcs`) into polynomial equations over $\mathbb{Z}$ (`verify/cas.ml`) discharged via Groebner-basis ideal membership in **Singular**, and (b) discharging modular wraparound / range preconditions (`verify/smt.ml`) in **Boolector/Z3** (`QF_BV`), stitched together across `cut` points. Neither engine is sufficient alone: algebraic ideal checks pass on silently overflowing `u16` arithmetic, while `QF_BV` range checks pass on incorrect prime-folding constants.
4. **Owl and OwlC (`secure-foundations/owl`)**: Replaces manual EasyCrypt game-hopping on large multi-message protocols (`HPKE`, `SSH`, `Kerberos`) with a **decidable dependent information-flow and refinement type system** (`LabelChecking.hs`, `Typing.hs`) grounded in computational PPT adversary indistinguishability (`adv` labels, `Name` key/nonce types, `corr_case` corruption splits) backed by **Z3** (`4.12.5`), paired with **OwlC** extraction to **Verus**-verified Rust.

## Applicability

This report covers the pinned upstream repositories, specifications, and empirical probes in `REPORT.json`:

- **Cryptol, SAW, and AWS-LC (`GaloisInc/cryptol` @ `13adfaad9287c4af98ee43c5c2b70d168c530872`, `GaloisInc/saw-script` @ `f290af7bda474779c8e5685ddd30612a7e6f0399`, `aws/aws-lc` @ `784feabf5fe33678bfbd4badcd6e795092a37b7e`, `awslabs/aws-lc-verification` @ `797302470c1703cbb1a3a6fa98daffef0bfd3d80`)**: Applies to SAW's LLVM bitcode frontend (`clang` LLVM `3.5–23.0`), x86-64/AArch64 machine-code symbolic simulation (`llvm_verify_x86`, `llvm_verify_fixpoint_chc_x86`), and Rust MIR frontend (`mir-json` schema `14`, per `saw-script/README.md:L128–175`). Per `aws/aws-lc` `tests/ci/run_formal_verification.sh:L13–22` and `.github/workflows/formal-verification.yml:L52–74`, SAW and `NSym` proof scripts reside in the companion `awslabs/aws-lc-verification` repository (`SAW/proof/`, `NSym/`, `Coq/`), not inside `aws/aws-lc` itself; CI clones `aws-lc-verification` and copies the candidate `aws-lc` tree into `./src` before running `saw-x86_64`, `saw-x86_64-aes-gcm`, `saw-aarch64`, and `nsym-aarch64`.
- **EasyCrypt, Jasmin, and Libjade (`EasyCrypt/easycrypt` @ `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`, `jasmin-lang/jasmin` @ `91ffd004fc1e84f29625c124383797ab91ddf3a9`, `formosa-crypto/formosa-libjade` @ `74098e710a5204e031651d808ff031b58db2c186`)**: Note two repository-hygiene facts observed directly in source: (1) `formosa-crypto/libjade` (`89c38602783d9c90dda11a9b8053295a8a088597`) is a 4-line archive pointer redirecting to `formosa-crypto/formosa-libjade` (`README.md:L3–4`), where ML-KEM (FIPS 203) and ML-DSA (FIPS 204) AVX2/SCT code and EasyCrypt proofs live; (2) inside `EasyCrypt/easycrypt`, `README.md:L106` still states `Why3 >= 1.8 and < 1.9`, whereas the actual build manifest `easycrypt.opam:L13` requires **`"why3" {>= "1.9.0" & < "1.10"}`** alongside `bitwuzla-cxx` and `zarith >= 1.10`.
- **CryptoLine (`fmlab-iis/cryptoline` @ `c992f0c41b5f34fb1a07bf3f84568c732a935272`)**: Covers the CryptoLine SSA IR (`ast/cryptoline.ml`), algebraic Singular reduction (`verify/cas.ml`), SMT `QF_BV` encoding (`verify/smt.ml`), and `to_zdsl.py` assembly translator; relies on OCaml `>= 5.4.0`, `Singular` (or SageMath/Magma/Maple), `Boolector`/`Z3`/`MathSAT`, and `abc` (`README.md:L20–43`).
- **Owl (`owl-lang/owl` @ `d511c31aa10a382c9386e34283707fd7476ac48d` vs. `secure-foundations/owl` @ `1b56f8cc70a067721917b9ccb60430417ada68f0`)**: Primary-source inspection establishes that `owl-lang/owl` holds only a 1-line `# owl` placeholder `README.md`, whereas active development of Owl and OwlC (targeting Z3 `4.12.5` and Verus `0.2026.09.06.8dea4a2` / Rust `1.98.0`) resides at **`secure-foundations/owl`**.

## Findings

### 1. Galois Cryptol & SAW: Compositional Symbolic Execution on `AWS-LC`

Basis: normative (Chudnov et al., CAV 2018 `10.1007/978-3-319-96142-2_26`; Boston et al., CAV 2021 `10.1007/978-3-030-81685-8_31`) + source (`GaloisInc/cryptol@13adfaad...`, `lib/Cryptol.cry`; `GaloisInc/saw-script@f290af7b...`, `README.md`, `saw-central/src/SAWCentral/Crucible/LLVM/{Builtins,X86,MethodSpecIR}.hs`; `aws/aws-lc@784feabf...`, `.github/workflows/formal-verification.yml`; `awslabs/aws-lc-verification@79730247...`, `SAW/README.md`, `SAW/patch/*.patch`, `SAW/proof/EC/EC_P384_primitives.saw`, `SAW/proof/AES/AESNI-GCM.saw`, `Coq/README.md`) + execution (`Probe 2B` witness)

1. **Cryptol Size-Polymorphic Specifications (`lib/Cryptol.cry:L26–68`)**: Cryptol embeds cryptographic specs over finite sequences `[n]a` and modular rings `Z n` (with kind `#` and constraints `fin n, n >= 1`), `Rational`, `Integer`, and carry-less polynomial multiplication (`pmult`/`pmod`) for `GHASH`. `SAWCore` compiles Cryptol expressions into a maximally shared term DAG exported either to `What4` SMT solvers (`Z3`, `Yices`, `ABC` bit-blasters) or to **Coq** (`Coq/EC/CryptolToCoq_equiv.v` in `aws-lc-verification`).
2. **Crucible Symbolic Execution & Compositional Overrides (`Builtins.hs:L23–63`, `X86.hs:L27–33`, `MethodSpecIR.hs:L26–105`)**:
   - **`llvm_verify` / `crucible_llvm_verify`**: Symbolically executes a function's LLVM CFG starting from symbolic heap allocations (`llvm_alloc`, `llvm_alloc_readonly`, `llvm_alloc_aligned`), disjointness (`llvm_points_to`), and Cryptol preconditions (`llvm_precond`), asserting absence of LLVM UB / out-of-bounds reads/writes (`SAW/README.md:L6–9`) and equivalence to Cryptol postconditions (`llvm_points_to`, `llvm_return`).
   - **`llvm_verify_x86` & CHC Loop Fixpoints (`X86.hs:L28–32`, `AESNI-GCM.saw:L13–96`)**: For hand-written assembly (such as OpenSSL/BoringSSL-derived Perlasm x86-64 `aesni_gcm_encrypt` and `sha512`), SAW simulates concrete ELF machine code against LLVM/Cryptol contracts (`llvm_verify_x86`), avoiding the LLVM-IR-vs-machine-code gap. Where message lengths are **symbolic and unbounded** (`len < 2 ^^ 36` matching NIST SP 800-38D 32-bit block-counter wrap limits at `AESNI-GCM.saw:L21`), `AESNI-GCM.saw:L81–95` invokes `llvm_verify_fixpoint_chc_x86'`, generating a loop-invariant Constrained Horn Clause (CHC) problem discharged by **Z3**, alongside `add_x86_preserved_reg "rax"` hints and explicit `.rodata` global relocation sizes (`("byte64_len_to_mask_table", 704)`).
3. **Production Engineering Realities on `aws/aws-lc` (`awslabs/aws-lc-verification`)**:
   - **Why `noinline` and `optnone` patches are mandatory (`SAW/patch/*.patch`)**: Crucible matches verified callee overrides by symbol name during symbolic execution. If Clang inlines `fiat_p384_sub`, `SHA384_Update`, or `ec_compute_wNAF`, the override never triggers, causing symbolic path explosion; conversely, aggressive LLVM optimization on `cmovznz` can transform branchless masks in ways that break bit-level proof scripts. Hence `aws-lc-verification` maintains `25` `noinline-*.patch` overlays (`noinline-fiat_p384_sub.patch`, `noinline-p384_felem_cmovznz.patch`, `noinline-constant_time_is_zero_w.patch`, etc.) plus `cmovznz.patch` adding `__attribute__((optnone))`.
   - **Strict Pointer-Aliasing Enumeration (`EC_P384_primitives.saw:L24–160`)**: Because each `crucible_alloc` / `ptr_to_fresh` declaration asserts pairwise disjoint allocations, `aws-lc-verification` must prove separate specs for every aliasing permutation (`p384_field_mul_spec`, `p384_field_mul_same_l_spec`, `p384_field_mul_same_r_spec`, `cmovznz_same_l_spec`, `cmovznz_same_r_spec`, `p384_field_add_same_all_spec`).
   - **Override Strength Hazard (`Probe 2B` witness) & `llvm_unsafe_assume_spec`**: Soundness of a caller proof depends completely on the *proven* postconditions of its callee overrides—or on unproved axioms introduced via `llvm_unsafe_assume_spec`. As **Probe 2B** demonstrates for a 2-limb 15-bit representation over $P = 2^{30}-3$, if a callee override asserts only modular congruence $(r_0 + 2^{15} r_1) \bmod P$ while omitting limb-range bounds ($r_i < 2^{15}$), a symbolic witness $(65533, 65535)$ satisfies the override yet silently wraps (`(65533 + 10) % 65536 = 7`) in the caller's 16-bit addition.
   - **Coq Bridge (`Coq/README.md`, `Coq/EC/EC_P384_Abstract_Model_equiv.v`)**: High-level algebraic identities (point-addition associativity, scalar-multiplication windowing `wNAF`) that defeat bit-blasting SMT solvers are verified in Coq over Cryptol terms exported by SAW (`CryptolToCoq_equiv.v`).

---

### 2. EasyCrypt, Jasmin, and Libjade: `pRHL` Game-Hopping Linked to Verified Assembly

Basis: normative (Barthe et al., CRYPTO 2011 `10.1007/978-3-642-22792-9_5`; Almeida et al., CCS 2017 `10.1145/3133956.3134078`; Barbosa et al., S&P 2021 `10.1109/SP40001.2021.00008` & CCS 2021 `10.1145/3460120.3484548`) + source (`EasyCrypt/easycrypt@ce19cb6c...`, `src/phl/ecPhlFel.ml`, `theories/crypto/ROM.eca`; `jasmin-lang/jasmin@91ffd004...`, `compiler/src/toEC.ml`; `formosa-crypto/formosa-libjade@74098e71...`, `README.md`, `docs/assurance.md`) + execution (`Probe 2B`)

EasyCrypt and Jasmin close the historical gulf between asymptotic game-playing proofs and cycle-accurate assembly:

1. **EasyCrypt's Four-Logic Stack + Complexity Extension**:
   - **Ambient Higher-Order Logic (HOL)**: Standard mathematical theories (finite maps, groups, polynomials, distributions `Distr`).
   - **Hoare Logic (`hoare`)**: Partial correctness (safety, memory bounds, functional determinism; does *not* prove termination, `formosa-libjade/docs/assurance.md:L106–109`).
   - **Probabilistic Hoare Logic (`phoare`)**: Quantitative single-program probability bounds ($\Pr[M.f(x) : E] \bowtie p$, including `islossless` termination).
   - **Probabilistic Relational Hoare Logic (`equiv`)**: Judgments $\models c_1 \sim c_2 : P \Longrightarrow Q$ lifting relational pre/postconditions over coupled distributions of program memories $(m_1, m_2)$, enabling `byequiv` program transformations, eager/lazy Random Oracle switching (`theories/crypto/ROM.eca:L42–120` proving `Lazy.LRO` equivalent to `FiniteEager.ERO`), and **adversarial complexity / cost bounds** (`Barbosa et al., CCS 2021`) tracking exact oracle-query counts and concrete execution time without asymptotic hand-waving.
2. **Failure Event Lemma (`upto bad`) & Coupling Discipline (`ecPhlFel.ml:L50–140`, `Probe 2B`)**:
   - The core workhorse of game-hopping (`upto` / `fel` tactic in `ecPhlFel.ml`) bounds distinguishing advantage $|\Pr[G_0 : \mathsf{Win}] - \Pr[G_1 : \mathsf{Win}]| \le \Pr[G_1 : \mathsf{bad}]$ by proving: (i) `bad` is monotone (`bad => bad`), (ii) `G_0` and `G_1` preserve relational equality of observable state and `Win` whenever `~bad` holds, and (iii) `Pr[G_1 : bad]` is bounded over $q$ oracle invocations using `callable_oracles_f` write-footprint isolation (`L50–89`, ensuring an abstract adversary module cannot directly overwrite `bad` or oracle private state!).
   - **Probe 2B** demonstrates on a finite $N = 4$ 2-query PRF-vs-PRP switching experiment that when `G_0` and `G_1` agree on all non-colliding draws (`~bad`), $|\Pr[G_0:\mathsf{Win}] - \Pr[G_1:\mathsf{Win}]| = |1/3 - 1/2| = 1/6 \le 1/4 = \Pr[G_1:\mathsf{bad}]$, whereas violating the `~bad` relational invariant immediately breaks the bound ($|1/3 - 3/4| = 5/12 > 1/4$).
3. **Jasmin Extraction (`toEC.ml`), CT/SCT Checking, and `libjade` `ProvSec` Tiers (`docs/assurance.md:L45–172`)**:
   - Jasmin programs are register/stack-explicit imperative procedures with arrays (`ArrayOld`, `WArray`, `BArray` extraction models in `jasmin/compiler/src/toEC.ml:L8–12`). Running `jasminc -ec` (`jasmin2ec`) extracts an EasyCrypt module directly from the Jasmin AST, while Rocq-verified compilation (`Compiler.v`) lowers Jasmin to x86-64/ARM/RISC-V assembly preserving functional semantics.
   - `jasmin-ct` checks **Constant Time (CT)** and **Speculative Constant Time (SCT)** using selective Speculative Load Hardening (masking transient loads via an initialized misspeculation flag) plus `--doit` (restricting secret/transient operands to Intel Data Operand Independent Timing instructions, `docs/assurance.md:L111–125`). Notice an important nuance explicitly documented in `formosa-libjade/docs/assurance.md:L100–102`: **preservation of CT across the current Jasmin compiler version is NOT machine-checked in Rocq** (only functional semantic preservation is Rocq-checked in mainline `libjade`'s compiler version, though research prototypes verify SCT preservation).
   - `formosa-libjade` classifies every algorithm's end-to-end claim (`meta.toml`, `scripts/claims.py`) into three **`ProvSec`** levels (`docs/assurance.md:L127–145`):
     - `functional`: implementation correctness + specification security proved separately, without a mechanized reduction linking the two;
     - `reduction`: an EasyCrypt theorem explicitly reduces implementation security to spec security;
     - `leakage-aware reduction`: reduction further supplies the adversary with the implementation's constant-time leakage trace (including explicitly declassified rejection-sampling outcomes in ML-DSA).
   - **Residual TCB (`docs/assurance.md:L148–172`)**: `jasmin2ec` translation fidelity, semantic equivalence between EasyCrypt's `eclib` and Jasmin's Rocq semantics, unverified parser/assembly printer/assembler/linker, and unverified C API headers (`src/include/*.h`) plus entry-point misspeculation-flag wrappers (`L92–94`).

---

### 3. CryptoLine: Splitting Groebner-Basis Algebra from `QF_BV` Bitvector Range Checking

Basis: normative (Tsai, Wang, Yang, ACM CCS 2017 `10.1145/3133956.3134076`; Fu et al., ACM CCS 2019 `10.1145/3319535.3354199`) + source (`fmlab-iis/cryptoline@c992f0c4...`, `README.md`, `examples/qhasm/fe25519_add.cl`, `verify/cas.ml`, `verify/smt.ml`) + execution (`Probe 2A`)

Low-level assembly kernels (Montgomery multiplication, `Curve25519`, Kyber/Dilithium NTT butterflies) break monolithic SMT solvers because 64×64-bit multipliers across dozens of limbs cause exponential SAT bit-blasting blowup. Conversely, pure Computer Algebra Systems (CAS) reason over infinite integers $\mathbb{Z}$ or rings $\mathbb{Z}[X]$ and ignore fixed-width $2^{64}$ modular overflow. **CryptoLine (`cv`) solves both simultaneously by decoupling algebraic equivalence from range safety**:

1. **Dual-Specification Language (`examples/qhasm/fe25519_add.cl:L2–82`)**:
   - Each `.cl` SSA program carries a precondition and postcondition combining an **algebraic clause** (`eqmod (limbs 51 [x0..x4] + limbs 51 [y0..y4]) (limbs 51 [r0..r4]) (2**255 - 19)`) and a **range safety clause** (`r0 < const 64 (2**53) /\ ...`), plus instruction-level safety (`isafety`: no unexpected carry/borrow/shift overflow).
   - Intermediate `cut` assertions partition massive routines (e.g., full field multiplications or multi-stage NTTs) into verified lemmas cleared sequentially.
2. **Algebraic Ideal Membership Encoding (`verify/cas.ml:L49–156`)**:
   - `verify/cas.ml` translates bit-level CryptoLine instructions into multivariate polynomial equations over $\mathbb{Z}$: bit-splits `split` introduce explicit high/low variables satisfying `a = l + h * 2^n` (`bv2z_join`, `L67`), truncated casts introduce explicit `discarded` or sign-extension `a_sign` variables (`bv2z_cast`, `L70–123`), and carry flags `c` emit quadratic bit constraints `c * (c - 1) = 0` (`bv2z_is_bit`, `L128–129`).
   - Crucially, **this algebraic encoding is sound only if no instruction overflows its register width**—an assumption discharged separately by the SMT range pass! Given range soundness, proving a postcondition `p ≡ q (mod m)` reduces to polynomial ideal membership (whether `p - q` reduces to `0` modulo the Groebner basis generated by the instruction polynomials and modulus `m` in **Singular**, SageMath, Magma, or Maple).
   - Typed CryptoLine (`CCS 2019`, `Tsuint`/`Tsint` in `cas.ml:L71–122`) tracks signed vs. unsigned two's-complement interpretations cleanly for signed NTT reductions (like Kyber/ML-KEM `q = 3329`).
3. **Bitvector Range Encoding (`verify/smt.ml:L27–159`)**:
   - `verify/smt.ml` generates `QF_BV` constraints (`ZeroExtend`, `SignExtend`, `Add`, `Mul`, `exp_sbb`, `Ult`, `Slt`) for **Boolector**, **Z3**, or **MathSAT**, proving that intermediate widths stay inside word boundaries so `verify/cas.ml`'s integer identities match machine bitvector execution. Because range predicates rarely require exact nonlinear cross-limb products (or can use `cut` bounds), `QF_BV` remains tractable while Singular handles nonlinear polynomial cancellations in milliseconds.
4. **Empirical Orthogonality (`Probe 2A`)**:
   - **Variant 1 (Algebraic pass / Range fail)**: Under loose 16-bit inputs `x0 = 40000`, computing `t0 = 2 * x0` in `u16` satisfies `t0 - 2*x0 == 0` identically in pure $\mathbb{Z}$ algebra (passes a naive CAS check missing overflow checks), yet wraps to `14464` in `u16` (`exec_u16_res = 1073676285 != 0` mod $2^{30}-3$), caught exclusively by the `QF_BV` range check.
   - **Variant 2 (Range pass / Algebraic fail)**: Folding a carry with the wrong prime tap (`+1*c` instead of `+3*c` for $p = 2^{30}-3$) keeps `0 <= r0 <= 65279 < 2^{16}` and `0 <= r1 <= 32510 < 2^{15}` across all sampled inputs (100% range-safe!), yet yields `8,192` modular congruence failures (`(lhs - rhs) % P != 0`), caught exclusively by the Singular Groebner-basis check.
   - Unless certified proof certificates (as in `CoqCryptoLine`, CAV 2023) are generated and checked in Rocq, **Singular and the SMT solver (`Boolector`/`Z3`) remain inside CryptoLine's TCB**, alongside `to_zdsl.py` assembly lifting fidelity.

---

### 4. Owl and OwlC: Computational Information-Flow Types for Security Protocols

Basis: normative (Gancher et al., IEEE S&P 2023 `10.1109/SP46215.2023.10179477`) + source (`secure-foundations/owl@1b56f8cc...`, `README.md`, `docs/encrypted_key_basic.owl`, `src/LabelChecking.hs`, `src/Typing.hs`)

While EasyCrypt handles single primitives (`ML-KEM`, `HMAC`) and small protocols effectively, composing multi-round stateful protocols (`HPKE`, `SSH`, `Kerberos`) with manual game hops scales superlinearly in proof effort. **Owl** encodes computational indistinguishability directly into an SMT-checked type system:

1. **Names, Labels, and Dynamic Corruption (`docs/encrypted_key_basic.owl:L11–43`, `src/LabelChecking.hs:L25–99`, `src/Typing.hs:L86–140`)**:
   - Secret keys, nonces, and DH exponents are declared as typed `name` values with cryptographic capability kinds (`nonce`, `enckey T`, `NT_KEM`, `NT_StAEAD`, `NT_PKE`, `NT_Sig`, `NT_MAC`, `NT_KDF`, `LabelChecking.hs:L50–89`) bound to protocol localities (`locality alice`, `locality bob`).
   - Types carry information-flow confidentiality labels (`TData l1 l2`, `advLbl` for adversary-public bytes, `zeroLbl`, `LGhost` erased prior to concrete cryptographic axioms in `removeGhost`, `L31–48`).
   - A key's payload type bounds its secrecy conditionally on dynamic compromise (`if sec(k_data) then Result else Data<adv>` in `encrypted_key_basic.owl:L24`), checked via explicit `corr_case` branching and SMT flow queries (`sFlows`, `LabelChecking.hs:L25–99`, `Typing.hs:L106–120`).
2. **Computational Soundness & OwlC Extraction to Verus (`README.md:L5–56`, `src/Extraction/`)**:
   - Owl's soundness theorem proves that any typechecked Owl protocol is computationally secure (indistinguishable from an idealized security game against any PPT Turing machine adversary), eliminating manual probabilistic `equiv` game hops for supported primitives (`AEAD`, `CCA-PKE`, `MAC`, `Sig`, `DH`, `HKDF`, `Nonces`).
   - **OwlC** (`--extract`, `src/Extraction/GenVerus.hs`) compiles typed Owl specifications into executable Rust (`owl_aead.rs`, `owl_dhke.rs`, `owl_hkdf.rs`, `owl_const_bytes.rs` in `hpke/owl-hpke/src/`) accompanied by **Verus** (`0.2026.09.06.8dea4a2`) functional-correctness and memory-safety proofs verifying that the Rust code faithfully refines the typed Owl spec (`run_verus.sh`), while leaving `execlib.rs` cryptographic primitive bindings (`owl_crypto_suite`) and Verus/Z3 in the TCB.

---

### 5. Cross-Toolchain Decision Matrix and Soundness Hazard Taxonomy

Basis: derived from primary sources across all pinned repositories

| Dimension | Cryptol + SAW (`AWS-LC`) | EasyCrypt + Jasmin (`libjade`) | CryptoLine (`cv`) | Owl + OwlC (`secure-foundations/owl`) |
|---|---|---|---|---|
| **Primary Verification Goal** | Bit-precise functional equivalence + memory/UB safety of C, x86-64, AArch64, Rust MIR | `pRHL` cryptographic reductions + assembly safety, correctness, CT/SCT | Algebraic modular equivalence + bitvector range/overflow safety for straight-line/cut kernels | Computational PPT protocol security (secrecy, authentication) + refined Rust extraction |
| **Target Input Artifact** | LLVM bitcode, compiled ELF (`.S`/`.o`), Rust `mir-json` (schema v14) | `.ec` specs + `.jazz` assembly-level routines | `.cl` SSA IR (or `to_zdsl.py` lifted assembly) | `.owl` protocol specification -> Verus-annotated Rust |
| **Core Proof Engine(s)** | Crucible symexec + `What4` (`Z3`/`Yices`/`ABC`) + Z3 CHC + optional Coq | `pRHL`/`hoare`/`phoare` + `Why3` (`Alt-Ergo`, `Z3`, `CVC5`) + Rocq compiler | **Singular** (Groebner-basis ideal check) + **Boolector/Z3** (`QF_BV`) | Dependent flow/refinement typechecker + **Z3** + **Verus** (on extracted Rust) |
| **Loop Handling** | Unrolled (bounded) or CHC fixpoint / manual loop cut overrides (`llvm_verify_fixpoint_chc_x86'`) | Loop invariants (`while` rules in `hoare`/`phoare`/`equiv`) | Unrolled straight-line or explicit `cut` invariants | Tailored protocol state machines / bounded sessions |
| **Side-Channel Assurance** | None built-in (`optnone` / manual inspection; `SAW` checks functional equivalence only) | `jasmin-ct` CT + SCT (`--doit` + SLH); compiler CT preservation unproved in Rocq for current version | None built-in (verifies arithmetic semantics/ranges only) | Constant-time Rust abstractions in `owl_const_bytes.rs` (downstream LLVM still in TCB) |
| **High-Risk Soundness / Operational Traps** | `llvm_unsafe_assume_spec` axioms; missed overrides if Clang inlines helpers (`noinline-*.patch`); weak override bounds; LLVM-vs-ELF drift if not using `x86_verify` | `upto bad` divergence prior to `bad`; `jasmin2ec` vs Rocq `eclib` gap; unverified C headers (`src/include/`); CT compiler-preservation gap | Missing range constraints invalidate $\mathbb{Z}$-polynomials; uncertified `Singular`/`Boolector` TCB without `CoqCryptoLine` | Supported-primitive boundary (`AEAD`/`PKE`/`DH`/`HKDF`); unverified `execlib.rs` crypto wrapper bindings |

## Boundaries

- **Unbounded loops in SAW without CHC or manual loop specs (`unsupported` / conditional)**: Standard `llvm_verify` unrolls symbolic branches and fails on data-dependent unbounded loops unless factored via explicit recursive overrides or `llvm_verify_fixpoint_chc_x86'` (as in `AESNI-GCM.saw:L81–95`).
- **Automated timing side-channel verification in SAW and CryptoLine (`known not to apply` / `unsupported`)**: Neither SAW's functional equivalence checks (`llvm_verify`) nor CryptoLine's algebraic/range engines (`verify/cas.ml`, `verify/smt.ml`) verify constant-time execution or speculative leakage freedom; `aws-lc-verification`'s `cmovznz.patch` (`__attribute__((optnone))`) prevents compiler optimization of `cmovznz` empirically rather than verifying machine-level non-interference in SAW.
- **Quantum Random Oracle Model (QROM) and post-quantum lattice assumptions inside Owl (`unsupported` at `1b56f8cc...`)**: `secure-foundations/owl` lists classic primitives (`AEAD`, `CCA-PKE`, `MAC`, `Sig`, `DH`, `HKDF`, `Nonces`, `README.md:L19–26`) and `NT_KEM` hooks (`LabelChecking.hs:L53`), targeting classical PPT security reductions rather than QROM reductions (which require `EasyCrypt` extensions or specialized quantum relational logics).
- **Local binary execution of `saw`, `easycrypt`, `cv`, `Singular`, `Boolector`, and `owl` (`not examined`)**: None of the upstream verification binaries (`saw`, `easycrypt`, `cv`, `owl`) were compiled or executed locally; all technical findings on tool internals come from direct inspection of the pinned source repositories and peer-reviewed specifications, corroborated by standalone Python micro-probes modeling the exact mathematical mechanisms (`Probe 2A`, `Probe 2B`).
- **AArch64 `NSym` verification inside `aws-lc-verification` (`not examined`)**: Detailed source inspection covered `SAW/proof/`, `SAW/patch/`, and `Coq/` inside `awslabs/aws-lc-verification`; the `NSym/` AArch64 symbolic verification engine referenced in `.github/workflows/formal-verification.yml:L70–74` was not examined.

## Evidence

- **Pinned Git repositories & primary source locations (inspected 2026-11-19)**:
  - `GaloisInc/cryptol` @ `13adfaad9287c4af98ee43c5c2b70d168c530872`: `lib/Cryptol.cry:L26–68` (`Bit`, `Integer`, `Z n`, `Rational`, `Word n`).
  - `GaloisInc/saw-script` @ `f290af7bda474779c8e5685ddd30612a7e6f0399`:
    - `README.md:L124–176` (LLVM `3.5–23.0` bitcode, Rust `mir-json` schema v14).
    - `saw-central/src/SAWCentral/Crucible/LLVM/Builtins.hs:L23–63` (`llvm_verify`, `llvm_unsafe_assume_spec`, `llvm_alloc*`, `llvm_points_to*`).
    - `saw-central/src/SAWCentral/Crucible/LLVM/X86.hs:L27–33` (`llvm_verify_x86`, `llvm_verify_fixpoint_chc_x86`).
    - `saw-central/src/SAWCentral/Crucible/LLVM/MethodSpecIR.hs:L26–105` (`LLVMAllocSpec`, `LLVMPointsTo`).
  - `aws/aws-lc` @ `784feabf5fe33678bfbd4badcd6e795092a37b7e`: `.github/workflows/formal-verification.yml:L50–100`, `tests/ci/run_formal_verification.sh:L5–24`.
  - `awslabs/aws-lc-verification` @ `797302470c1703cbb1a3a6fa98daffef0bfd3d80`:
    - `SAW/README.md:L1–9`, `Coq/README.md:L1–2`.
    - `SAW/patch/cmovznz.patch:L1–12` (`__attribute__((optnone))`), `SAW/patch/noinline-fiat_p384_sub.patch:L1–12` (`__attribute__((noinline))`).
    - `SAW/proof/EC/EC_P384_primitives.saw:L18–160` (explicit aliasing specs).
    - `SAW/proof/AES/AESNI-GCM.saw:L13–96` (`llvm_verify_fixpoint_chc_x86'`, `len < 2 ^^ 36`).
  - `EasyCrypt/easycrypt` @ `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`:
    - `README.md:L106–112` vs `easycrypt.opam:L13` (`why3 >= 1.9.0 & < 1.10`, `bitwuzla-cxx`).
    - `src/phl/ecPhlFel.ml:L17–140` (`t_failure_event_r`, `callable_oracles_f`).
    - `theories/crypto/ROM.eca:L42–120` (`Lazy.LRO`, `FiniteEager.ERO`).
  - `jasmin-lang/jasmin` @ `91ffd004fc1e84f29625c124383797ab91ddf3a9`: `compiler/src/toEC.ml:L8–120` (`ArrayOld`, `WArray`, `BArray`, `global_options`).
  - `formosa-crypto/libjade` @ `89c38602783d9c90dda11a9b8053295a8a088597` (`README.md:L1–4`) redirecting to `formosa-crypto/formosa-libjade` @ `74098e710a5204e031651d808ff031b58db2c186`: `README.md:L38–180`, `docs/assurance.md:L13–172`.
  - `fmlab-iis/cryptoline` @ `c992f0c41b5f34fb1a07bf3f84568c732a935272`:
    - `README.md:L20–43`, `examples/qhasm/fe25519_add.cl:L2–82`.
    - `verify/cas.ml:L49–156` (`bv2z_join`, `bv2z_split`, `bv2z_cast`, `bv2z_is_bit`).
    - `verify/smt.ml:L27–159` (`exp_rexp`, `bexp_rbexp`, `exp_sbb`).
  - `owl-lang/owl` @ `d511c31aa10a382c9386e34283707fd7476ac48d` (`README.md:L1`) vs `secure-foundations/owl` @ `1b56f8cc70a067721917b9ccb60430417ada68f0`: `README.md:L1–77`, `docs/encrypted_key_basic.owl:L1–45`, `src/LabelChecking.hs:L25–99`, `src/Typing.hs:L57–140`.
- **Reproducible Execution Probes (`CPython 3.13.15`, Linux `x86_64`, observed `2026-11-19`)**:
  - Command:
    ```bash
    python3 - <<'EOF'
    from fractions import Fraction

    # Probe 2A: CryptoLine Dual-Engine Orthogonality (P = 2^30 - 3, W = 2^16)
    P, W = (1 << 30) - 3, 1 << 16
    x0 = 40000
    alg_z = (2 * x0 - 2 * x0) % P
    exec_u16 = ((2 * x0) % W - 2 * x0) % P
    print(f"Variant 1 (x0={x0}): alg_Z={alg_z}, u16_exec={exec_u16}")
    assert alg_z == 0 and exec_u16 != 0

    max_r0 = max_r1 = mismatches = 0
    first = None
    for a0 in range(0, 1 << 15, 257):
        for a1 in range(0, 1 << 15, 257):
            s1 = 2 * a1
            c, r1, r0 = s1 >> 15, s1 & 0x7FFF, 2 * a0 + (s1 >> 15)
            assert 0 <= r0 < W and 0 <= r1 < W
            max_r0, max_r1 = max(max_r0, r0), max(max_r1, r1)
            if ((r0 + (r1 << 15)) - 2 * (a0 + (a1 << 15))) % P != 0:
                mismatches += 1
                if first is None:
                    first = (a0, a1, r0, r1, ((r0 + (r1 << 15)) - 2 * (a0 + (a1 << 15))) % P)
    print(f"Variant 2 (+1*c bug): max_r0={max_r0}, max_r1={max_r1}, alg_mismatches={mismatches}, first={first}")

    # Probe 2B: EasyCrypt upto-bad Coupling & SAW Weak-Override Witness
    N = 4
    pr_g0 = pr_g1 = pr_bad = pr_broken = Fraction(0)
    for y1 in range(N):
        for y2 in range(N):
            p = Fraction(1, N * N)
            if y2 == y1:
                pr_bad += p
                pr_g1 += p
                pr_broken += p
                for y2p in range(N):
                    if y2p != y1 and (y1 + y2p) % 2 == 0:
                        pr_g0 += p * Fraction(1, N - 1)
            else:
                if (y1 + y2) % 2 == 0:
                    pr_g0 += p
                    pr_g1 += p
                else:
                    pr_broken += p
    print(f"Valid upto-bad: |{pr_g0}-{pr_g1}|={abs(pr_g0-pr_g1)} <= {pr_bad}")
    print(f"Broken ~bad:    |{pr_g0}-{pr_broken}|={abs(pr_g0-pr_broken)} > {pr_bad}")
    r0_w, r1_w = 65533, 65535
    print(f"SAW weak-override witness: r=({r0_w},{r1_w}), mod_P={(r0_w + (r1_w << 15)) % P}, caller u16 add={(r0_w+10)%W}")
    EOF
    ```
  - Recorded stdout:
    ```text
    Variant 1 (x0=40000): alg_Z=0, u16_exec=1073676285
    Variant 2 (+1*c bug): max_r0=65279, max_r1=32510, alg_mismatches=8192, first=(0, 16448, 1, 128, 1073741819)
    Valid upto-bad: |1/3-1/2|=1/6 <= 1/4
    Broken ~bad:    |1/3-3/4|=5/12 > 1/4
    SAW weak-override witness: r=(65533,65535), mod_P=32771, caller u16 add=7
    ```

## Revalidation

1. **Check toolchain integration & schema drift cheaply**:
   - In `aws/aws-lc` and `awslabs/aws-lc-verification`, check `.github/workflows/formal-verification.yml`, `tests/ci/run_formal_verification.sh`, and `SAW/patch/` to determine whether newer Clang/LLVM versions require additional `noinline-*.patch` / `optnone` entries or whether `llvm_verify_x86` / `NSym` coverage expanded to ML-KEM.
   - In `GaloisInc/saw-script`, check `README.md` and `saw-central/src/SAWCentral/Crucible/MIR/` for `mir-json` schema bumps past version `14` or updated LLVM bitcode upper bounds (`> 23.0`).
   - In `EasyCrypt/easycrypt`, check `easycrypt.opam` (`why3` pin) vs `README.md` to verify whether documentation matches opam build constraints, and in `formosa-crypto/formosa-libjade`, inspect `docs/assurance.md` and `src/*/*/*/meta.toml` to verify whether Jasmin's Rocq compiler correctness proof now covers CT/SCT preservation and whether ML-KEM/ML-DSA `provsec` tiers advance from `functional` to `leakage-aware reduction`.
   - In `fmlab-iis/cryptoline`, inspect `verify/cas.ml` and `verify/smt.ml` for new instructions or certified proof export (`CoqCryptoLine`), and in `secure-foundations/owl`, inspect `README.md` and `src/LabelChecking.hs` for newly added post-quantum primitives (`NT_KEM`).
2. **Re-run the Python dual-engine & coupling probe** above whenever evaluating modified multi-limb range/algebraic split conditions or `upto bad` coupling invariants; all arithmetic assertions and exact `Fraction` probabilities execute in `< 50 ms` with zero external dependencies.
