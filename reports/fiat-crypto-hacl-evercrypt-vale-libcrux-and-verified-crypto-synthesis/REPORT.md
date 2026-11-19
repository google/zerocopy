# Constructive Cryptographic Synthesis and Multi-Target Verified Compilation across Fiat-Crypto, HACL*/EverCrypt, Vale, and libcrux

## Summary

Constructive cryptographic verification replaces post-hoc verification of hand-written assembly or C with **correct-by-construction synthesis** or **proof-carrying extraction** from machine-checked functional specifications. Across the four major production toolchains—MIT **Fiat-Crypto**, **HACL\*** + **EverCrypt**, **Vale**, and Cryspen **libcrux** (via **hax** and **Eurydice**)—two architectural choices dominate both performance and the residual Trusted Computing Base (TCB): (1) **where unrolling, limb splitting, and bounds inference occur** relative to target code generation, and (2) **whether the verification boundary terminates above or below an unverified C/Rust compiler (`clang`/`rustc`/LLVM)**.

1. **Fiat-Crypto (`mit-plv/fiat-crypto`)** embeds prime-field arithmetic as polymorphic Gallina templates over `Associational` and `Positional` limb representations inside Rocq (`Coq >= 9.0`), specializes them via **reflective Normalization-by-Evaluation (NbE) partial evaluation**, propagates exact integer interval bounds through a **verified `ZRange` abstract interpreter** (`BoundsPipeline.v`), and emits straight-line, branchless code (`C`, `Rust`, `Go`, `Zig`, or verified `bedrock2`). Because partial evaluation eliminates every loop, allocation, and dynamic dispatch *inside* Rocq, generated C/Rust avoids the `cmov` and constant-time fragility only up to `value_barrier` inline assembly (`__asm__("" : "+r"(a))`) unless lowered through `bedrock2` (`Field25519.v`).
2. **HACL\* and EverCrypt (`hacl-star/hacl-star`, `project-everest/vale`)** stratify verification into pure functional specs (`Spec.*`), a shallow C-like embedding in F\* (`Low*` with `HyperStack` regions and `Lib.IntTypes` `SEC`/`PUB` secrecy levels forbidding secret indexing, division, and branching), and procedural assembly verification (`Vale` with `quickCode` weakest-precondition normalization and a verified taint/leakage checker). EverCrypt multiplexes `Low*` C (`KaRaMeL`), portable `HACLxN` SIMD, and `Vale` assembly behind one agile state-machine contract (`EverCrypt.AEAD`, `EverCrypt.AutoConfig2`), verifying C-to-assembly ABI, callee-saved register, and `XMM` register framing in F\*.
3. **Cryspen `libcrux` + `hax` (`cryspen/libcrux`, `cryspen/hax`)** inverts the extraction direction for post-quantum standards (NIST **FIPS 203** ML-KEM and **FIPS 204** ML-DSA): engineers write idiomatic, SIMD-trait-parameterized Rust (`portable`, `AVX2`, `NEON`) annotated with `#[hax_lib::requires]` / `#[hax_lib::ensures]` contracts and loop invariants. `hax` hooks `rustc` (`driver-hax-frontend-exporter`), rewrites loops and mutable references into pure functional F\* (or Lean via Charon+Aeneas, Rocq, ProVerif, SSProve, EasyCrypt) for panic-freedom, integer range bounds, and functional equivalence, while `Eurydice` + `KaRaMeL` extract the same Rust source to standalone C—forcing hand-written C barriers (`libcrux_ct_barrier.h`) wherever `Eurydice` erases `core::hint::black_box` to a no-op.

Exhaustive Python execution probes over `GF(2^255 - 19)` 5x51 unsaturated Solinas carry chains and ML-KEM (`q = 3329`) `i16` Barrett/Montgomery arithmetic expose exact arithmetic cliffs—including why Fiat-Crypto sets `tight_upperbounds` to `v + 1 = 2^51` (absorbing ripple carries along `[0, 1, 2, 3, 4, 0, 1]`) and why `libcrux`'s `ntt_binomially_sampled_ring_element` carries `verification_status(lax)` at a `2,879`-unit contract gap (`28,296 < 31,175 <= 31,625`) beneath the real `i16` multiplication overflow cliff (`q_hat = 10`, `33,290 > 32,767` at `v = 31,626`).

## Applicability

This report characterizes the architectures, proof boundaries, and verified/unverified seams of the pinned subjects in `REPORT.json`:

- **Constructive synthesis (`mit-plv/fiat-crypto` @ `3d2880ef2803faa9385589a81a835d5828eb3d38`)**: Covers the `BoundsPipeline`, `UnsaturatedSolinas`, `WordByWordMontgomery`, C/Rust stringification, and `bedrock2` X25519 integration (`src/Bedrock/End2End/X25519/Field25519.v`). Applies to straight-line finite-field limb arithmetic (`unsaturated-solinas`, `saturated-solinas`, `word-by-word-montgomery`, `dettman-multiplication`, `solinas-reduction`, `base-conversion`); requires Coq `>= 9.0` with Rocq standard library `>= 9.1` (per `README.md:L34`).
- **Imperative F\*/Low\* & verified assembly (`hacl-star/hacl-star` @ `f557259007db9933442dde10aa995c1b00bd3446`, `project-everest/vale` @ `bbae0eb89143734363b14a77642dbf8dec36e288`, `FStarLang/karamel` @ `6bd5918c7c518adbb973f75f23cdd0900acb7526`)**: Per `hacl-star/README.md:L14–22`, HACL\* is in **maintenance mode** and builds against a **frozen F\* version prior to the removal of the Low\* toolchain** (using `nix develop`); findings apply to the maintained `dist/` C and `dist/vale/` assembly outputs as well as the `EverCrypt` provider (`providers/evercrypt/`) and `Vale` x64/PPC64LE verification framework (`fstar/code/arch/x64/`).
- **Rust-first verification and C extraction (`cryspen/libcrux` @ `4f3bc83d0dd5fda622bcba0f47009b51dd31403c`, `cryspen/hax` @ `0d2f66ed697c46d7c0f5038150b7c9679e4d954b`, `AeneasVerif/eurydice` @ `b4ce1a78f645f89f669091b3c322e9aaa30b77a4`)**: Covers `libcrux-ml-kem` (FIPS 203) and `libcrux-ml-dsa` (FIPS 204) extracted via `hax` (`cargo hax into fstar`) and compiled to C via Charon + `Eurydice` + `KaRaMeL` (`libcrux-ml-kem/C-CODE.md`). Notice that individual Rust functions in `libcrux` explicitly annotate proof completion (`verified` vs `#[cfg_attr(hax, hax_lib::fstar::verification_status(lax))]` in `ntt.rs` and `polynomial.rs`); assertions about "fully verified ML-KEM" must distinguish panic-freedom, range invariants, functional equivalence against F\* specs, and unproved/lax sub-functions at a given commit.
- **Relationship among subjects**: Rather than competing monoliths, these toolchains form an evolutionary and complementary spectrum: Fiat-Crypto eliminates hand-written multi-limb C arithmetic (used in BoringSSL, AWS-LC, Go, Rustls); HACL\*/EverCrypt provides full symmetric/elliptic primitives with an agile multiplexing C/assembly boundary; `libcrux` brings `KaRaMeL`-style C extraction and F\* proof discipline into safe/SIMD Rust for NIST post-quantum algorithms.

## Findings

### 1. MIT Fiat-Crypto: Associational/Positional Algebra and Reflective PHOAS Synthesis

Basis: normative (Erbsen et al., IEEE S&P 2019 `10.1109/SP.2019.00005`) + source (`mit-plv/fiat-crypto@3d2880ef...`, `src/Arithmetic/Core.v`, `src/BoundsPipeline.v`, `src/PushButtonSynthesis/UnsaturatedSolinas.v`, `src/UnsaturatedSolinasHeuristics.v`, `src/Stringification/C.v`) + execution (`Probe 1A`)

Fiat-Crypto synthesizes finite-field arithmetic without asking Rocq to reason directly about flat C syntax or concrete prime bitwidths during proof development. Instead, it factors arithmetic generation into **three decoupled layers** proved generically once for all prime shapes:

1. **Dual Mathematical Representation (`src/Arithmetic/Core.v:L29–160`)**:
   - **`Associational`**: Represents an arbitrary intermediate sum of products as `list (Z * Z)` pairs `(weight, coeff)` with semantic evaluation `eval p = fold_right Z.add 0 (map (fun t => fst t * snd t) p)`. Polynomial multiplication (`Associational.mul`, `eval_mul : eval (mul p q) = eval p * eval q`, `L53–59`), squaring (`Associational.square`, factoring $2 a_i a_j$ cross-terms, `L63–76`), and modular splitting (`split s p` + `reduce s c p`, `L114–157`) rely solely on the algebraic identity `(a + s * b) mod (s - c) = (a + c * b) mod (s - c)` (`reduction_rule`, `L135–137`).
   - **`Positional`**: Projects associative lists onto fixed limb positions governed by `weight : nat -> Z` (`weight n = ceil(n * limbwidth)` for fractional Solinas bitwidths like `51` or `25.5`, or uniform `uweight machine_wordsize` $= 2^{w \cdot i}$ for saturated **Word-by-Word Montgomery**, `src/PushButtonSynthesis/WordByWordMontgomery.v:L125–234`, which checks `(r * r') mod m = 1`, `(m * m') mod r = (-1) mod r`, and `m < r^n` upfront in `check_args` before synthesizing `mul`, `square`, `from_montgomery`, `to_montgomery`, and Bernstein–Yang `divstep` modular inversion). Carry propagation (`carry_chains`), borrowing, and canonical `freeze` operate as pure positional transformations proved congruent modulo $m = s - \mathrm{eval}(c)$.

2. **Reflective PHOAS Partial Evaluation & `ZRange` Abstract Interpretation (`src/BoundsPipeline.v:L112–160, L702–895`)**:
   - Generic Gallina algorithms (parameterized over prime `s`, taps `c`, limb count `n`, and machine wordsize `w`) are reified into a Parametric Higher-Order Abstract Syntax (`PHOAS`) IR (`Expr t`).
   - `PreBoundsPipeline` (`L702–732`) runs `PartialEvaluate` (Normalization by Evaluation using `Rewriter`), optional `RewriteUnfoldValueBarrier`, constant folding `RewriteArith 0` / `RewriteArith (2^8)`, and optional `RewriteToFancy` (lowering into two-output `addc`/`subb`/carry-flag intrinsics). Every recursion over limb lists is completely unrolled into straight-line SSA expressions.
   - `BoundsPipelineWithDebug` (`L757–845`) then runs **three passes** of `CheckedPartialEvaluateWithBounds`:
     1. Exact `ZRange` (`[lo ~> hi]`) abstract interpretation without bitwidth relaxation, computing tight interval bounds on every intermediate expression;
     2. `RewriteArithWithCasts` + `CheckedPartialEvaluateWithBounds` stripping pre-existing casts to verify that tight/loose preconditions propagate through carry chains (`L786`);
     3. Bound relaxation (`relax_zrange_gen only_signed possible_values`, `L132–140`) mapping each intermediate interval onto the smallest unsigned or signed hardware type (`[0 ~> 2^bw - 1]` before `[-2^(bw-1) ~> 2^(bw-1)-1]`), followed by `RewriteMulSplit` / `RewriteMultiRetSplit` (splitting 128-bit products on 64-bit targets into `mulx`/`lo+hi` pairs), `RewriteNoSelect` (eliminating non-hardware conditional selects), and `RewriteStripLiteralCasts`.
   - If computed bounds fail to fit `out_bounds` or target wordsize `possible_values`, synthesis fails explicitly with `Computed_bounds_are_not_tight_enough` (`L842`) rather than silently truncating or widening.

3. **Unsaturated Solinas Heuristics, Carry Chains, and Constant-Time Barriers**:
   - In `src/UnsaturatedSolinasHeuristics.v:L170–246`, Fiat-Crypto sets `tight_upperbounds` to `Qceiling(Qabs(1 * (v + 1)))` (`L190`), where `v` is the saturated `limbwidth`-bit partition (`2^51 - 1` for `GF(2^255 - 19)` on 64-bit, giving **`tight_upperbound = 2^51`**, NOT `2^51 - 1`). Loose bounds allow `headspace_add_count = 2` additions and `headspace_sub_count = 1` subtraction against `balance = 2 * encode(p)` (`L197–240`).
   - For two-term Solinas primes (`length p == 2`), `carry_chains` equals `List.seq 0 n ++ [0; 1]` (`L181`), i.e., `[0, 1, 2, 3, 4, 0, 1]` on 5 limbs. As verified in **Executable Micro-Probe 1A**, on a worst-case input `x_edge = [2^51 - 1, 2^51 - 1, 2^51 - 1, 2^51 - 1, 2^52]`:
     - A single carry pass `[0, 1, 2, 3, 4]` leaves limb 0 at `0x8000000000025` (`2^51 + 37 > 2^51`), violating `tight_bounds`;
     - Appending `[0, 1]` propagates the wrapped `19 * carry_4` ripple across limbs `0 -> 1 -> 2`, yielding `[0x25, 0x0, 0x8000000000000, 0x7ffffffffffff, 0x0]`. Notice that limb 2 reaches `2^51` (`0x8000000000000`), which passes precisely because `tight_upperbounds` uses `v + 1 = 2^51`!
   - To eliminate non-canonical tight representations in `[p, 2^255 - 1]`, `UnsaturatedSolinas.v:L125–150` constructs `m_enc` (`[(2^51 - 19), 2^51 - 1, ..., 2^51 - 1]` satisfying `eval m_enc = p` and `tight_upperbounds[i] - fw[i] <= m_enc[i]`) and performs a constant-time borrow-subtract + `cmovznz` selection.
   - At C stringification (`src/Stringification/C.v:L86–97`), Fiat-Crypto protects boolean masks against LLVM branch conversion using an inline-assembly optimization barrier:
     ```c
     static __inline__ uint64_t ...value_barrier_u64(uint64_t a) {
       __asm__("" : "+r"(a) : /* no inputs */);
       return a;
     }
     ```
     Unless compiled via Fiat-Crypto's `bedrock2` backend (`src/Bedrock/End2End/X25519/Field25519.v:L48–160`), which composes `unsaturated_solinas_ops` with `bedrock2`'s verified C-to-RISC-V compiler (`FE310CSemantics` / `BasicC32Semantics`), **all C/Rust/Go compilers downstream of `BoundsPipeline` remain in the TCB** for timing side channels and arithmetic miscompilation.

---

### 2. HACL\* and Low\*: Shallow Embedding, HyperStack Regions, and Secrecy Types

Basis: normative (Zinzindohoué et al., ACM CCS 2017 `10.1145/3133956.3134043`; Protzenko et al., ICFP 2017 `10.1145/3110261`) + source (`hacl-star/hacl-star@f5572590...`, `lib/Lib.IntTypes.fsti`)

HACL\* writes executable imperative cryptographic primitives inside **Low\***, a sequential, stack-and-region-managed subset of F\* extracted to readable C99 via **KaRaMeL** (`FStarLang/karamel`):

1. **Pure Spec vs. Imperative Low\* Separation**: Every algorithm begins with a short, unoptimized pure functional specification (`specs/Spec.*.fst`, e.g., `Spec.Curve25519`, `Spec.Agile.AEAD`) operating over mathematical `nat`, `FStar.Seq`, and finite-field definitions. `Low*` implementations (`code/`) operate over `LowStar.Buffer` pointers in the `Stack` or `ST` (`FStar.HyperStack`) memory model, proving functional equivalence (`B.as_seq h1 out == Spec.f ...`), spatial disjointness (`B.loc_disjoint`), and explicit frame modification (`B.modifies (B.loc_buffer out) h0 h1`) via SMT (`Z3`).
2. **Type-Enforced Constant-Time via `Lib.IntTypes` (`lib/Lib.IntTypes.fsti:L18–255, L344–420`)**:
   - Integer types are indexed by both width (`inttype = U1 | U8 | U16 | U32 | U64 | U128 | S8..S128`) and secrecy lattice level `secrecy_level = SEC | PUB` (`int_t t l`).
   - `SEC` types are **abstract** (`val sec_int_t: inttype -> Type0` at `L137`, no decidable equality `eqtype`!): callers cannot compare `SEC` values with `=`, branch on them in `if`, index buffers (`B.index`), divide/mod (`/` or `%`), or downcast from `SEC` to `PUB` (`cast` requires `PUB? l \/ SEC? l'` at `L348`).
   - Secret conditional moves (`conditional_swap`, masks) work over `SEC` masks (`U1` / `ones t SEC`), while `pub_int_t` (`U32`, `size_t`, `byte_t`) admits standard indexing and control flow.
3. **`HACLxN` Generic Vector Abstraction & KaRaMeL Erasure**: Multi-buffer SIMD implementations (`AVX2`, `AVX-512`, `NEON`) share generic vector interfaces (`Lib.Vec.Types`) whose lane widths (`128`, `256`, `512`) instantiate to platform intrinsics while sharing a single F\* proof against vectorized pure specs (`Polubelova et al., CCS 2020`). KaRaMeL then erases `Ghost`/`erased` proof terms, monomorphizes inline helpers (`inline_for_extraction`), and emits C99—meaning **KaRaMeL and the downstream C compiler (`gcc`/`clang`) remain inside the TCB**, and LLVM backend regressions (e.g., converting `SEC` bitmasks back into branches) are not excluded by F\* typechecking alone.

---

### 3. Vale and EverCrypt: Procedural Assembly Verification and Agile Multiplexing

Basis: normative (Bond et al., USENIX Security 2017; Protzenko et al., IEEE S&P 2020 `10.1109/SP40000.2020.00067`) + source (`project-everest/vale@bbae0eb8...`, `doc/types.txt`, `fstar/code/arch/x64/X64.Vale.Decls.fsti`, `X64.Vale.QuickCodes.fsti`; `hacl-star/hacl-star@f5572590...`, `providers/evercrypt/EverCrypt.AEAD.fsti`, `EverCrypt.TargetConfig.fsti`, `code/curve25519/Hacl.Impl.Curve25519.Field64.Vale.fst`)

While HACL\* relies on a C compiler, **Vale** verifies hand-tuned assembly (`x86_64`, `ARM64`, `PPC64LE`) directly against machine-level semantics in F\* (or Dafny):

1. **Trusted Machine Semantics & Procedural DSL (`X64.Vale.Decls.fsti`, `doc/types.txt`)**:
   - Vale separates an untrusted procedural assembly language (`.vaf` files supporting `inline`, `ghost`, `inout operand`, explicit `reads`/`modifies` register/flag/heap frames, `doc/types.txt:L69–91`) from a compact **trusted machine interpreter** (`eval_code`, `X64.Machine_s`) modeling 64-bit GPRs (`nat64`), 128-bit `XMM` registers (`quad32`), CPU flags (`cf`, `overflow`), and heap `memory`.
   - Crucially, **Vale checks constant-time leakage as part of verification**: the trusted semantics records an explicit leakage trace (branch outcomes and effective memory addresses) and runs a verified **taint analysis** proving no `Secret`-tainted register, flag, or operand ever flows into branch conditions, memory address calculations, or variable-time instructions.
2. **Eliminating Z3 VC Blowup via `quickCode` Normalization (`X64.Vale.QuickCodes.fsti:L51–120`)**:
   - Naive weakest-precondition generation over hundreds of assembly instructions produces massive nested SMT formulas that time out Z3. Vale compiles verified procedures into `quickCodes` ASTs (`QSeq`, `QBind`, `QPURE`, `QLemma`, `QAssertBy`) whose `wp` combinator (`L107`) computes weakest preconditions by F\* **reflection/normalization** (`norm [zeta; delta_only ...]`, `X64.Vale.Decls.fsti:L31`), stripping frame conditions (`va_update_reg`, `va_update_mem`, `mods_contains`) and dispatching arithmetic subgoals before Z3 ever runs.
3. **EverCrypt Interop & CPUID Multiplexing (`EverCrypt.AEAD.fsti`, `EverCrypt.TargetConfig.fsti`, `Hacl.Impl.Curve25519.Field64.Vale.fst`)**:
   - EverCrypt exposes a single **agile, stateful `HyperStack` API** (`EverCrypt.AEAD.state alg`, `invariant`, `footprint`, `frame_invariant`, `L44–123`) covering AES-GCM (`AES128_GCM`, `AES256_GCM`) and `CHACHA20_POLY1305`.
   - At the FFI boundary (`Hacl.Impl.Curve25519.Field64.Vale.fst:L32–158`), EverCrypt proves ABI equivalence between HACL\* `Low*` `lbuffer uint64 4ul` (`F64.as_nat`) and Vale's heap representation (`FA.as_nat`), proving caller/callee-saved register preservation (`Rsp` forbidden as destination in `X64.Vale.Decls.fsti:L121`), `XMM` restoration, and `HyperStack` disjointness before dispatching either inline assembly (`Vale.Inline.X64.*`) or external `.S` symbols (`Vale.Wrapper.X64.*`) guarded by `[@@ CIfDef ]` compile-time flags (`EverCrypt.TargetConfig.fsti:L32–43`) and runtime CPUID (`aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\ movbe_enabled /\ sse_enabled`, `EverCrypt.AEAD.fsti:L91–92`).
   - Even here, non-x64 CPUID bridges (`evercrypt_targetconfig.h`, `EverCrypt.TargetConfig.fsti:L6–10`), the small Vale assembly printer, and the external assembler (`as`) remain outside formal proofs.

---

### 4. Cryspen `libcrux` and `hax`: Rust-First Extraction and Post-Quantum Invariants

Basis: normative (Bhargavan et al., VSTTE 2024 `10.1007/978-3-031-86695-1_7`; Bhargavan et al., CCS 2025 `10.1145/3719027.3765213`; NIST FIPS 203 `10.6028/NIST.FIPS.203`; NIST FIPS 204 `10.6028/NIST.FIPS.204`) + source (`cryspen/hax@0d2f66ed...`, `README.md`, `docs/frontend/index.md`; `cryspen/libcrux@4f3bc83d...`, `libcrux-ml-kem/src/{ntt,polynomial,constant_time_ops,ind_cca}.rs`, `libcrux-ml-kem/src/vector/{traits,portable/arithmetic,avx2/arithmetic}.rs`, `libcrux-ml-kem/extracts/c/generated/intrinsics/libcrux_ct_barrier.h`) + execution (`Probe 1B`)

Rather than writing specifications and code in separate languages, `libcrux` develops production Rust implementations of **ML-KEM (FIPS 203)** and **ML-DSA (FIPS 204)** and extracts verification models directly from `rustc`:

1. **`hax` Architecture & Rust Subset Discipline (`cryspen/hax`, `docs/frontend/index.md:L25–125`, `README.md:L117–128, L216–220`)**:
   - `cargo hax` sets `RUSTC_WORKSPACE_WRAPPER` to `driver-hax-frontend-exporter`, intercepting `rustc` after type/borrow checking (THIR/MIR) to serialize `*.haxmeta` ASTs (`hax-frontend-exporter`), which the OCaml `hax-engine` transforms into functional code by eliminating `for` loops (with `hax_lib::loop_invariant!`) and rewriting `&mut T` mutations into state-passing return pairs (`${var}_future`).
   - Because mutation elimination relies on Rust's exclusivity guarantees, `hax` **explicitly rejects functions returning `&mut T` and aliasing mutable borrows** (`README.md:L218`).
   - Backends split by property: **F\*** (`cargo hax into fstar`, stable—used by `libcrux` for panic-freedom, integer range safety, and equivalence to `Spec.MLKEM`/`Spec.MLDSA`), **Lean** (via Charon + Aeneas, active default in `hax 0.4+`), **ProVerif** (Dolev-Yao protocol models), and experimental Rocq, SSProve, and EasyCrypt backends.
2. **SIMD Trait Abstraction and Lattice Arithmetic Overflow Cliffs (`libcrux-ml-kem`)**:
   - All polynomial/NTT routines in `libcrux-ml-kem` (`ntt.rs`, `polynomial.rs`) are polymorphic over `Vector: Operations` (`libcrux-ml-kem/src/vector/traits.rs:L42–160`), with separate implementations for `portable` (`i16` loops), `avx2` (`mm256_add_epi16`, `mm256_mullo_epi16`), and `neon`. Because `hax` verifies the generic algorithm once against the `Vector::Operations` trait preconditions (`add_pre`, `barrett_reduce`, `ntt_layer_{1,2,3}_step`) and verifies each backend satisfies those trait specs (`avx2/arithmetic.rs:L13–98`), SIMD vectorization stays outside the `Spec.MLKEM` equivalence proof burden.
   - **Exact Barrett and Montgomery Bounds**: In `libcrux-ml-kem/src/vector/portable/arithmetic.rs:L259–466` ($q = 3329$):
     - `barrett_reduce_element(value)` computes `t = value * 20159 + 2^25`, `quotient = (t >> 26) as i16`, `result = value - quotient * 3329`, requiring `|value| <= 28296` (`L260`, ensuring `|quotient| <= 8` so `|quotient * 3329| <= 26632`) and ensuring `|result| <= 3328` (`|result| <= 1664` empirically).
     - `montgomery_reduce_element(value)` uses $R = 2^{16}$, $q^{-1} \bmod 2^{16} = 62209 \equiv -3327$, and $2^{-16} \equiv 169 \pmod{3329}$, proving `|result| <= 3328 + 1665 = 4993` for `|value| <= 3328 * 2^16` and tightening to `|result| <= 3328` when `|value| <= 3328 * 2^15` (`L355–358`).
   - **Empirical Contract Gap Caught by Execution + Source Inspection (`Probe 1B` vs `ntt.rs:L29, L322–345`)**:
     - Exhaustively testing all `65,536` `i16` inputs in **Micro-Probe 1B** proves that `barrett_reduce_element` produces zero `i16` overflow and `|out| <= 1664` for all `|v| <= 31625`, breaking first at **`v = 31626`** where `quotient = 10` causes `10 * 3329 = 33290 > 32767 = i16::MAX`!
     - Comparing this physical cliff against `libcrux-ml-kem/src/ntt.rs` explains why `ntt_binomially_sampled_ring_element` carries `#[cfg_attr(hax, hax_lib::fstar::verification_status(lax))]` (`L322`) at this pinned commit: `ntt_at_layer_1` guarantees `ntt_re_range_1`, whose bound is **`11207 + 6 * 3328 = 31175`** (`L29`). Although `31175 <= 31625` is mathematically safe in `i16` execution, `31175 > 28296` violates `poly_barrett_reduce`'s overly conservative `28296` precondition (`polynomial.rs:L223`), blocking strict F\* discharge until tightened or adjusted!
3. **Constant-Time & Eurydice C-Extraction Seam (`constant_time_ops.rs:L13–156`, `ind_cca.rs:L350–469`, `libcrux_ct_barrier.h:L11–38`)**:
   - `libcrux` avoids `KyberSlash`-style division leaks and Fujisaki–Okamoto (FO) decapsulation timing side channels: `ind_cca::decapsulate` (`L350–469`) unconditionally computes both the candidate `shared_secret` (from `G(decrypted || H(pk))` + `ind_cpa::encrypt`) and the `implicit_rejection_shared_secret` (`PRF(z || c)`), then passes both with `ciphertext` vs `expected_ciphertext` into `compare_ciphertexts_select_shared_secret_in_constant_time` (`L463–468`), backed by `libcrux_secrets` secrecy types, branchless `inz` (`((!value).wrapping_add(1) >> 8) & 1`), `compare_ciphertexts_in_constant_time`, and `select_ct`.
   - Crucially, `constant_time_ops.rs:L15–27` and `libcrux_ct_barrier.h:L11–38` document a real compiler-extraction hazard: **`Eurydice` translates `core::hint::black_box` into a no-op**! Consequently, the `extract.yaml` pipeline skips extracting `constant_time_ops::barrier` and substitutes a hand-written C header (`libcrux_ct_barrier.h`) routing `uint8_t` through a `static KRML_NOINLINE` `volatile uint8_t opaque = value` round-trip—preventing Clang/GCC from proving `is_non_zero` returns `{0, 1}` and folding `select_ct` back into a branch. Even with that barrier, the downstream Rust/C compilers (`rustc`/LLVM, `clang`) remain in the TCB for constant-time preservation.

---

### 5. Cross-Toolchain Architectural Matrix and TCB/ABI Seams

Basis: derived from primary sources across all five pinned repositories

| Dimension | Fiat-Crypto (C / Rust) | Fiat-Crypto + Bedrock2 | HACL\* (`Low*` / `KaRaMeL`) | Vale (`ValeCrypt`) | Cryspen `libcrux` (`hax` + `Eurydice`) |
|---|---|---|---|---|---|
| **Source / Spec Language** | Rocq (Gallina PHOAS + `ZRange`) | Rocq + `bedrock2` AST | F\* (`Spec.*` + `Low*`) | F\* / Dafny + `.vaf` assembly DSL | Rust + `hax_lib` contracts (`#[requires]`/`#[ensures]`) |
| **Target Artifact** | Unrolled straight-line C, Rust, Go, Zig | Verified RISC-V / machine words via `bedrock2` | C99 (`.c`/`.h`), WebAssembly | x86-64 / ARM64 / PPC64LE `.S` assembly | Safe/SIMD Rust + C11/C++17 via `Eurydice` |
| **Loop / Dispatch Handling** | Completely unrolled at synthesis time via NbE | Unrolled field ops composed inside `bedrock2` | Explicit `HyperStack` loops + `[@@ CIfDef ]` / `AutoConfig2` | Explicit assembly loops + `quickCode` WP normalization | Functionalized loops via `hax` + runtime `multiplexing` |
| **Constant-Time Mechanism** | Straight-line code + `cmovznz` + `__asm__` `value_barrier` | Straight-line IR in verified machine model | Abstract `SEC` int types (`Lib.IntTypes`) forbid secret branches/indices | Verified taint/leakage trace over registers, flags, memory | `libcrux_secrets` + `core::hint::black_box` / `volatile` C barrier |
| **Residual Trusted Computing Base (TCB)** | Rocq kernel + `C`/`Rust` compiler (`clang`/`rustc`) | Rocq kernel + `bedrock2` RISC-V ISA model | F\* + Z3 + `KaRaMeL` + `C` compiler (`clang`/`gcc`) | F\* + Z3 + `Vale` ISA model + assembler (`as`) | `rustc` + `hax` exporter/engine + F\* + Z3 + (`Eurydice`/`KaRaMeL`) + LLVM/C compiler |
| **Primary Failure / Friction Surface** | Large primes blow up NbE/partial-eval stack (`ulimit -s`); non-canonical tight limbs require `freeze` | Limited to platforms with verified `bedrock2` backend (`FE310`/RISC-V) | Maintenance mode on frozen F\*/Low\* toolchain; `KaRaMeL` + C optimizer outside proof | High proof engineering effort per ISA; non-x64 CPUID glue stays hand-written | `lax` proofs on sub-functions (`ntt.rs:L322`); `Eurydice` drops `black_box`; `&mut`-returning functions unsupported |

## Boundaries

- **Hardware microarchitectural leakage (`known not to apply` / `unsupported`)**: None of Fiat-Crypto's C/Rust output, HACL\*, `Vale`'s architectural leakage model, or `libcrux` proves resistance against speculative execution (`Spectre` v1/v4), Data Memory-Dependent Prefetchers (`GoFetch`), power/EM side channels (boolean masking / `PINI`), or voltage/clock glitching. Their constant-time claims cover architectural control flow, memory address traces, and avoidance of variable-latency instructions (`DIV`/`IDIV`).
- **Compiler preservation below `KaRaMeL`, `Eurydice`, `fiat_crypto` C/Rust (`known not to apply`)**: Except when Fiat-Crypto targets `bedrock2` down to machine words or Vale verifies assembly directly, LLVM/`rustc`/`clang`/`gcc` optimizations (e.g., `CodeGenPrepare` select-to-branch lowering, `X86CmovConversion`, register spilling leaving secrets unzeroed) lie outside the machine-checked proofs; barriers (`value_barrier`, `black_box`, `volatile`) are pragmatic mitigations rather than theorem-backed guarantees.
- **Unverified `lax` regions inside `libcrux` (`source`-observed gap at `4f3bc83d0dd5fda622bcba0f47009b51dd31403c`)**: Specific functions in `libcrux-ml-kem` (notably `subtract_reduce` in `polynomial.rs:L246`, `ntt_at_layer_4_plus` in `ntt.rs:L237`, `ntt_at_layer_7` in `ntt.rs:L277`, `ntt_binomially_sampled_ring_element` in `ntt.rs:L322`, and `ntt_vector_u` in `ntt.rs:L349`) carry `hax_lib::fstar::verification_status(lax)` annotations, meaning their contracts are assumed rather than fully SMT-discharged at this pinned revision.
- **Unsupported Rust constructs in `hax` (`unsupported`)**: Per `cryspen/hax` `README.md:L218`, `hax` forbids functions returning `&mut T` and aliasing mutable borrows; concurrent `unsafe` multi-threading, arbitrary inline assembly, and `Eurydice` trait inheritance (`eurydice/issues/111`, worked around by duplicating `Repr` in `traits.rs:L10–20`) lie outside the clean extraction subset.
- **Full end-to-end Coq/F\* proof replay (`not examined`)**: This investigation did not execute full `coqc` builds of `mit-plv/fiat-crypto`, `nix develop` F\* verification of `hacl-star`, or `cargo hax into fstar` + `fstar.exe` on `cryspen/libcrux` locally; proof structures and bounds were inspected directly in primary source files and cross-checked with exact Python arithmetic probes.
- **ARM64/NEON Vale and `libcrux-ml-dsa` per-function `lax` counts (`not examined`)**: Detailed line-by-line inspection focused on `Vale` x64 (`X64.Vale.*`) and `libcrux-ml-kem`; ARM64 Vale (`vale` / `hacl-star`) and full `libcrux-ml-dsa` F\* proof coverage ratios were not exhaustively inventoried.

## Evidence

- **Pinned Git repositories & primary source locations (inspected 2026-11-19)**:
  - `mit-plv/fiat-crypto` @ `3d2880ef2803faa9385589a81a835d5828eb3d38`:
    - `README.md:L34–160` (Rocq `>= 9.0` requirement, synthesis commands, `bedrock2` target).
    - `src/Arithmetic/Core.v:L29–160` (`Associational.eval`, `mul`, `square`, `split`, `reduction_rule`, `reduce`).
    - `src/BoundsPipeline.v:L112–160, L687–895` (`relax_zrange_gen`, `PreBoundsPipeline`, `BoundsPipelineWithDebug`, `RewriteToFancy`, `RewriteMulSplit`, `RewriteNoSelect`).
    - `src/UnsaturatedSolinasHeuristics.v:L170–246` (`carry_chains`, `tight_upperbounds` via `v + 1`, `loose_upperbounds`, `distribute_balance`).
    - `src/PushButtonSynthesis/UnsaturatedSolinas.v:L105–290` (`m_enc` freeze encoding, `check_args`, `scarry_mul`).
    - `src/PushButtonSynthesis/WordByWordMontgomery.v:L125–299` (`uweight` saturated Montgomery bounds, `check_args` `(m * m') mod r = (-1) mod r`, `divstep`).
    - `src/Stringification/C.v:L86–97` (`value_barrier_func` emitting `__asm__("" : "+r"(a))`).
    - `src/Bedrock/End2End/X25519/Field25519.v:L24–160` (10×25.5-bit `fe25519_*` `bedrock2` derivations).
  - `hacl-star/hacl-star` @ `f557259007db9933442dde10aa995c1b00bd3446`:
    - `README.md:L14–127` (maintenance mode, frozen F\*/Low\* toolchain, citations).
    - `lib/Lib.IntTypes.fsti:L18–255, L344–420` (`inttype`, `secrecy_level = SEC | PUB`, abstract `sec_int_t`, `cast`).
    - `providers/evercrypt/EverCrypt.AEAD.fsti:L42–160` (`state_s`, `config_pre`, `invariant`, `frame_invariant`).
    - `providers/evercrypt/EverCrypt.TargetConfig.fsti:L6–43` (`[@@ CIfDef ]`, non-x64 CPUID bridge).
    - `code/curve25519/Hacl.Impl.Curve25519.Field64.Vale.fst:L32–158` (`buffer_is_buffer`, `as_nat_is_as_nat`, `Vale.Inline` vs `Vale.Wrapper` dispatch).
  - `project-everest/vale` @ `bbae0eb89143734363b14a77642dbf8dec36e288`:
    - `doc/types.txt:L69–459` (operand modes `ghost`/`inline`/`inout`, typing and framing judgments).
    - `fstar/code/arch/x64/X64.Vale.Decls.fsti:L16–160` (`va_reveal_opaque`, `va_is_dst_opr64` forbidding `Rsp`, `va_update_*`).
    - `fstar/code/arch/x64/X64.Vale.QuickCodes.fsti:L51–120` (`quickCodes`, reflective `wp` VC generator).
  - `cryspen/libcrux` @ `4f3bc83d0dd5fda622bcba0f47009b51dd31403c`:
    - `libcrux-ml-kem/C-CODE.md:L1–66` (Charon + Eurydice + KaRaMeL C extraction matrix).
    - `libcrux-ml-kem/src/vector/traits.rs:L1–160` (`MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS = 1353`, `INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 62209`, `Repr` workaround for `eurydice/issues/111`, `Operations` trait contracts).
    - `libcrux-ml-kem/src/vector/portable/arithmetic.rs:L259–490` (`BARRETT_MULTIPLIER = 20159`, `barrett_reduce_element` `28296` precondition, `montgomery_reduce_element` `3328 * pow2 16` precondition).
    - `libcrux-ml-kem/src/vector/avx2/arithmetic.rs:L13–98` (AVX2 `mm256_*` trait proof lemmas).
    - `libcrux-ml-kem/src/ntt.rs:L13–371` (`ntt_re_range_1` `11207 + 6*3328 = 31175`, `verification_status(lax)` on `L237, L277, L322, L349`).
    - `libcrux-ml-kem/src/ind_cca.rs:L350–469` (`decapsulate` constant-time FO implicit rejection and ciphertext comparison).
    - `libcrux-ml-kem/src/constant_time_ops.rs:L13–156` and `libcrux-ml-kem/extracts/c/generated/intrinsics/libcrux_ct_barrier.h:L11–38` (`black_box` no-op in Eurydice and `volatile` C barrier replacement).
  - `cryspen/hax` @ `0d2f66ed697c46d7c0f5038150b7c9679e4d954b`: `README.md:L117–220` and `docs/frontend/index.md:L23–125`.
- **Reproducible Execution Probes (`CPython 3.13.15`, Linux `x86_64`, observed `2026-11-19`)**:
  - Command:
    ```bash
    python3 - <<'EOF'
    P25519 = (1 << 255) - 19
    MASK51 = (1 << 51) - 1
    TIGHT_B = 1 << 51
    for mult in [1, 2, 3, 4, 8, 16]:
        b = mult * TIGHT_B
        acc_max_0 = 77 * (b * b)
        print(f"loose_mult={mult:2d}x: max_limb_in=0x{b:x} ({b.bit_length()}b), max_acc0={acc_max_0.bit_length()}b, fits_u128={acc_max_0 < (1 << 128)}")
    def step(limbs, idx):
        out = list(limbs)
        c = out[idx] >> 51
        out[idx] &= MASK51
        if idx < 4: out[idx + 1] += c
        else: out[0] += 19 * c
        return out
    x_edge = [MASK51, MASK51, MASK51, MASK51, 1 << 52]
    s1 = list(x_edge)
    for i in [0, 1, 2, 3, 4]: s1 = step(s1, i)
    s2 = list(x_edge)
    for i in [0, 1, 2, 3, 4, 0, 1]: s2 = step(s2, i)
    print("single_pass [0..4]:", [hex(v) for v in s1], "tight?", all(v <= TIGHT_B for v in s1))
    print("chained [0..4,0,1]:", [hex(v) for v in s2], "tight?", all(v <= TIGHT_B for v in s2))
    limbs_nc = [MASK51 - 9, MASK51, MASK51, MASK51, MASK51]
    m_enc = [(1 << 51) - 19, MASK51, MASK51, MASK51, MASK51]
    diff, borrow = [], 0
    for i in range(5):
        d = limbs_nc[i] - m_enc[i] - borrow
        borrow = 1 if d < 0 else 0
        diff.append(d & MASK51)
    mask = -borrow
    frozen = [(limbs_nc[i] & mask) | (diff[i] & ~mask) for i in range(5)]
    print("freeze(2^255-10):", sum(frozen[i] << (51 * i) for i in range(5)))

    Q, BMULT, BSHIFT, BHALF, MINV = 3329, 20159, 26, 1 << 25, 62209
    def barrett(v):
        q_hat = (v * BMULT + BHALF) >> BSHIFT
        q_i16 = ((q_hat + 32768) % 65536) - 32768
        prod = q_i16 * Q
        ov = not (-32768 <= prod <= 32767) or not (-32768 <= v - prod <= 32767)
        return v - prod, q_i16, ov
    max_safe, first_fail, max_28296 = None, None, 0
    for a in range(32768):
        rp, qp, op = barrett(a)
        rn, qn, on = barrett(-a)
        vp = not op and -3328 <= rp <= 3328 and (rp - a) % Q == 0
        vn = not on and -3328 <= rn <= 3328 and (rn + a) % Q == 0
        if a <= 28296:
            assert vp and vn
            max_28296 = max(max_28296, abs(rp), abs(rn))
        if not (vp and vn) and first_fail is None:
            first_fail = (a, rp, qp, op, rn, qn, on)
        if vp and vn and first_fail is None:
            max_safe = a
    print(f"Barrett |v|<=28296: {2*28296+1} valid, max|out|={max_28296}; max_safe={max_safe}, first_fail={first_fail}")
    EOF
    ```
  - Recorded stdout:
    ```text
    loose_mult= 1x: max_limb_in=0x8000000000000 (52b), max_acc0=109b, fits_u128=True
    loose_mult= 2x: max_limb_in=0x10000000000000 (53b), max_acc0=111b, fits_u128=True
    loose_mult= 3x: max_limb_in=0x18000000000000 (53b), max_acc0=112b, fits_u128=True
    loose_mult= 4x: max_limb_in=0x20000000000000 (54b), max_acc0=113b, fits_u128=True
    loose_mult= 8x: max_limb_in=0x40000000000000 (55b), max_acc0=115b, fits_u128=True
    loose_mult=16x: max_limb_in=0x80000000000000 (56b), max_acc0=117b, fits_u128=True
    single_pass [0..4]: ['0x8000000000025', '0x7ffffffffffff', '0x7ffffffffffff', '0x7ffffffffffff', '0x0'] tight? False
    chained [0..4,0,1]: ['0x25', '0x0', '0x8000000000000', '0x7ffffffffffff', '0x0'] tight? True
    freeze(2^255-10): 9
    Barrett |v|<=28296: 56593 valid, max|out|=1664; max_safe=31625, first_fail=(31626, -1664, 10, True, 1664, -10, True)
    ```

## Revalidation

1. **Check upstream status and TCB seams cheaply** (without rebuilding full Coq/F\* proofs):
   - In `mit-plv/fiat-crypto`, diff `src/BoundsPipeline.v`, `src/UnsaturatedSolinasHeuristics.v`, and `src/Stringification/C.v` (`value_barrier_func`) against `3d2880ef2803faa9385589a81a835d5828eb3d38` to see if `tight_upperbounds` (`v + 1`), `carry_chains`, or inline-assembly barriers changed, and check `src/Bedrock/` for expanded primitive coverage beyond X25519.
   - In `hacl-star/hacl-star`, verify whether `README.md` still pins a frozen Low\* F\* version and inspect `providers/evercrypt/EverCrypt.TargetConfig.fsti` for any new architecture flags.
   - In `cryspen/libcrux`, search `libcrux-ml-kem/src/` and `libcrux-ml-dsa/src/` for `verification_status(lax)` to measure whether the `28,296` vs `31,175` Barrett/NTT contract gap in `ntt.rs` (`ntt_binomially_sampled_ring_element`) has been discharged, and verify `extracts/c/generated/intrinsics/libcrux_ct_barrier.h` remains active in `extract.yaml`.
2. **Re-run the Python arithmetic probe** above against any updated ML-KEM Barrett constants (`BARRETT_MULTIPLIER`, `BARRETT_SHIFT`, or `is_i16b` bounds in `arithmetic.rs`) or Solinas limb partitions (`carry_chains`); any change to `BARRETT_MULTIPLIER` or NTT layer bounds immediately shifts the `31,626` `i16` overflow cliff.
