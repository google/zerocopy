# Zero-Knowledge Proof Circuit DSLs, Linear Resource-Metered VMs, and Quantum Linear Languages

## Summary

Three non-Von-Neumann programming paradigms—zero-knowledge proof (ZKP) circuit DSLs (`Circom`, `Halo2`, `Noir`, `Cairo`), linear resource-metered virtual machines (`Move` vs. `EVM`), and quantum/reversible linear languages (`Silq`, `Quipper`, `QWIRE`, `SQIR`/`VOQC`)—replace classical register-and-RAM semantics with explicit mathematical or physical conservation laws:

1. **Algebraic determinism in ZKP circuit DSLs**: One source program compiles into two distinct artifacts over a prime finite field $\mathbb{F}_p$: an untrusted imperative *witness generator* (`<--` in `Circom`, `synthesize` in `Halo2`, `Brillig` in `Noir`, `Hint` in `Cairo`) and a soundness-critical *polynomial constraint system* (`===` R1CS, PLONKish gates/lookups, ACIR `AssertZero`, Cairo AIR). Because non-quadratic operations (inversion, bit extraction, division) cannot be expressed directly as degree-2 R1CS constraints, unconstrained witness computation is structurally unavoidable. Omitting booleanity, inverse, range, or field-aliasing constraints leaves honest witness tests 100% green while allowing a malicious prover to forge $y' \neq f(x)$. Uniqueness verifiers (`Picus`/`QED^2`, `Ecne`) check relational output determinism ($C(x, w_1) \land C(x, w_2) \implies y_1 = y_2$) via finite-field propagation lemmas (`Linear`, `Binary01`, `Basis2` guarded by $k \le \lfloor \log_2 p \rfloor$) plus finite-field SMT (`cvc5`); refinement-type systems (`CODA`) certify functional equivalence in Coq.
2. **Value conservation in linear resource-metered VMs**: Representing assets as integers in mutable maps (`Solidity`/`EVM`) with dynamic dispatch callbacks breaks scarcity via double-spend, loss, and reentrancy. `Move` moves asset enforcement out of the compiler into an on-chain **Bytecode Verifier** enforcing four orthogonal abilities (`copy = 0x1`, `drop = 0x2`, `store = 0x4`, `key = 0x8`), a 3-point control-flow-sensitive local-availability lattice (`Unavailable`, `MaybeAvailable`, `Available`), borrow-graph reference safety, and acyclic module dependencies. Deterministic execution gas metering with atomic rollback on out-of-gas/abort prevents non-terminating or aborting code from trapping or destroying resources, while verifier-time metering prevents abstract-interpretation DoS.
3. **Unitary and information conservation in quantum/reversible languages**: No-Cloning ($|\psi\rangle \not\mapsto |\psi\rangle^{\otimes 2}$), No-Deleting, and unitarity ($U^\dagger U = I$) forbid copying or silently dropping qubits. Discarding an entangled ancilla acts as a partial trace $\rho_A = \operatorname{Tr}_B(|\psi\rangle\langle\psi|)$, destroying interference (collapsing Hadamard $P(0)$ from $1.0$ to $0.5$ and 2-qubit Grover $P(11)$ from $1.0$ to $0.625$). `Silq` uses `!`, `const`, `mfree`, `qfree`, and `lifted` annotations to synthesize provably physical automatic Bennett uncomputation ($U^\dagger$). At the IR optimization layer, Coq-embedded `SQIR`/`VOQC` enforces no-cloning via concrete register-index distinctness (`m <> n`) and certifies gate inversion and optimization passes over symbolic unitary matrices.

The standalone Python 3.10+ probe ([`support/verify_zk_move_and_uncomputation.py`](support/verify_zk_move_and_uncomputation.py)) reproduces all three paradigms end-to-end.

## Applicability

This report documents language semantics, IR boundaries, verification algorithms, and failure mechanisms across sixteen durable subjects pinned in `REPORT.json`:

- **ZKP circuit DSLs and verifiers (comparative analysis)**: `iden3/circom`, `iden3/circomlib`, `zcash/halo2`, `noir-lang/noir`, `starkware-libs/cairo`, `Veridise/Picus`, Pailoor et al. (PLDI '23, `10.1145/3591282`), `franklynwang/EcneProject`, and `0xPARC/zk-bug-tracker`. Applies to prime-field arithmetic constraint systems (R1CS, PLONKish, ACIR, AIR) separating witness computation from polynomial verification. Error codes and operator rules correspond to the pinned revisions (Circom 2.x, Halo2 `ConstraintSystem<F>`, Noir ACIR/Brillig, Cairo CASM).
- **Linear resource-metered VMs (evolution & dialect comparison)**: Blackshear et al. (`2020-05-26` Move whitepaper), `move-language/move` (Core/Diem/Aptos lineage with global storage opcodes and `Acquires` checks), and `MystenLabs/sui` (Sui Move lineage with object storage, deprecated global-storage opcodes, verifier metering, and optional regex reference safety). Differences between the 2020 binary-kind formulation (`resource`/`unrestricted`) and modern 4-bit abilities (`copy`/`drop`/`store`/`key`), as well as account-indexed vs. object-centric storage, are explicitly distinguished.
- **Quantum and reversible linear languages (design-space comparison)**: Bichsel et al. (PLDI '20, `10.1145/3385412.3386007`), `eth-sri/silq`, Hietala et al. (POPL '21, `10.1145/3434318`), and `inQWIRE/SQIR`, contextualized against `Quipper` (Green et al., PLDI '13), `QWIRE` (Paykin et al., POPL '17), Landauer (1961), Bennett (1973), and `Janus` (Yokoyama & Glück, PEPM '07). Applies to QRAM gate-based quantum languages and Coq-verified circuit IRs.

**Cross-references to adjacent corpus packages**: Rather than duplicating Rust-oriented survey tables already preserved in the corpus, this report complements three adjacent packages:
- `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` (Rust constant-time crypto, ZKP, and zkVM verification positioning).
- `anneal-law-defi-mechanism-design-voting-and-medical-survey` (DeFi/smart-contract verifiers including Certora, Halmos, KEVM, and Move Prover).
- `anneal-cps-robotics-aerospace-eda-and-quantum-survey` (quantum compilation, ZX-calculus, and QEC alongside CPS and EDA verification).

## Findings

### 1. Cross-Paradigm Synthesis: Conservation Laws as Language-Design Drivers

Basis: derived from primary-source compiler/verifier implementations and normative semantics across all three domains.

Mainstream languages assume Von-Neumann registers and RAM: values can be copied, overwritten, or discarded arbitrarily, branches may depend on runtime secrets, and execution produces one forward trace. When a mathematical or physical conservation law governs correctness, those assumptions fail and force a strict split between unrestricted classical metadata and conserved values:

| Dimension | ZK Circuit DSLs (`Circom`, `Halo2`, `Noir`, `Cairo`) | Linear Resource VMs (`Move` vs. `EVM`) | Quantum & Reversible Languages (`Silq`, `QWIRE`, `SQIR`, `Janus`) |
| :--- | :--- | :--- | :--- |
| **Conservation Law** | Algebraic determinism over $\mathbb{F}_p$: constraints $C(x, w)$ must uniquely fix outputs $y = f(x)$ | Value scarcity: assets cannot be forged (copied) or silently lost (dropped), even on abort/OOG | Unitarity ($U^\dagger U = I$), No-Cloning, No-Deleting, and Landauer reversibility ($k_B T \ln 2$) |
| **Why Von-Neumann Fails** | Polynomials lack imperative assignment, secret-conditioned control flow, and division/shifts | Integer balance maps + dynamic dispatch allow accounting drift and callback reentrancy | Cloning violates physics; dropping an entangled ancilla traces out coherence ($\operatorname{Tr}_B$) |
| **Primary Soundness Bug** | **Under-constrained circuits**: honest tests pass while prover forges $y' \neq f(x)$ | **Reentrancy / double-spend / asset lock**: forged balances, callback interleaving, trapped assets | **Missing/invalid uncomputation**: residual ancilla entanglement destroys interference amplitudes |
| **Split Representation** | Untrusted witness gen (`<--`, `synthesize`, `Brillig`, `Hint`) vs. constraints (`===`, gates, `AssertZero`, AIR) | Untrusted off-chain compiler vs. trusted on-chain Bytecode Verifier + metered VM runtime | Unrestricted classical host/control (`!`, `qfree`) vs. linear quantum state (`mfree`, `ucom`) |
| **Enforcement Boundary** | Uniqueness verifiers (`Picus`, `Ecne`) or refinement provers (`CODA`); compiler checks degree/topology only | On-chain abstract interpretation (`type`/`locals`/`reference_safety`, abilities) + dual metering + rollback | Static annotations (`Silq` `const`/`qfree`/`mfree`/`lifted`, `QWIRE` linearity) or `SQIR` `m <> n` + Coq (`VOQC`) |
| **Why Naive Testing Fails** | Honest witness execution checks *completeness* only, never soundness | Happy-path tests miss crafted bytecode, callback reentrancy, and OOG partial state | Basis-state tests ($|0\rangle, |1\rangle$) miss entanglement bugs visible only on superpositions |

Across all three paradigms, **soundness hinges on segregating classical metadata from conserved state at the IR/type boundary**: `Circom` separates compile-time `var` from `signal` wires (forbidding constraints in `BlockType::Unknown`); `Move` separates `copy + drop` scalars from linear resource structs; and `Silq` separates `!` classical data and `const` quantum borrows from linear consumed qubits.

---

### 2. Zero-Knowledge Proof Circuit DSLs and the Witness-Generation vs. Constraint-Soundness Chasm

#### 2.1 Dual-Artifact Compilation Across Arithmetizations (`Circom`, `Halo2`, `Noir`, `Cairo`)

Basis: source (`iden3/circom`, `zcash/halo2`, `noir-lang/noir`, `starkware-libs/cairo`) + documentation.

A zk-SNARK or zk-STARK proves knowledge of a witness $w \in \mathbb{F}_p^m$ satisfying a public algebraic relation $C(x, w) = 0$ over a large prime field (e.g., BN254 scalar field $p \approx 2^{253.6}$). Because the cryptographic verifier checks only $C(x, w) = 0$ and never runs witness-generation code, every ZK DSL produces two artifacts with asymmetric trust: an **untrusted witness generator** (which a malicious prover may replace with arbitrary field values) and a **soundness-critical constraint system**:

| System & Arithmetization | Imperative Witness Mechanism (Untrusted) | Declarative Constraint Mechanism (Soundness-Critical) | Compiler Guardrails Verified in Source |
| :--- | :--- | :--- | :--- |
| **`Circom` (R1CS: $A w \circ B w = C w$)** | `AssignOp::AssignSignal` (`<--`, `-->`); arbitrary division, bit-shifts, conditionals | `AssignOp::AssignConstraintSignal` (`<==`, `==>`) and `ConstraintEquality` (`===`) | Rejects degree $> 2$ (`NonQuadraticConstraint`) and signal-branched constraints (`ConstraintInUnknown`); `--inspect` warns only (`CanBeQuadraticConstraintSingle`/`Multiple`) on quadratic `<--` |
| **`Halo2` (PLONKish matrix + lookups)** | `Circuit::synthesize` populating `Advice` cells and enabling `Selector` rows | `Circuit::configure` defining `create_gate` (arbitrary-degree polynomials over `VirtualCells` + `Rotation`), `enable_equality` (`permutation::Argument`), and `lookup` (`TableColumn`) | `create_gate` panics on empty constraints; `lookup` panics if input contains a simple selector (`contains_simple_selector()`); `compress_selectors` packs selectors into `Fixed` columns without exceeding `max_degree` |
| **`Noir` (ACIR + Brillig VM)** | `unconstrained fn` compiled to `Brillig` bytecode invoked via `Opcode::BrilligCall { id, inputs, outputs, predicate }` | `Opcode::AssertZero(Expression<F>)` (degree-$\le 2$ polynomial), `BlackBoxFuncCall`, `MemoryInit`/`MemoryOp` | `brillig.rs` states explicitly: *"Executing Brillig does not generate any constraints"*; outputs are solver hints requiring explicit downstream `AssertZero`/`BlackBoxFuncCall` constraints |
| **`Cairo` (AIR / STARK + CASM)** | `Hint` (`Core`, `Starknet`, `External`) populating write-once memory cells | `InstructionBody` (`AssertEq`, `QM31AssertEq`, `AddAp`, `Call`, `Jump`, `Jnz`, `Ret`, `Blake2sCompress`) verified by CPU AIR | Hinted cells are untrusted until bound by `AssertEq` or range-check builtin constraints |

Direct inspection of `iden3/circom` (`9b4b2333...`, `constraint_generation/src/execute.rs` L425–L555) demonstrates why `<--` cannot be eliminated from R1CS DSLs:
- `AssignOp::AssignConstraintSignal` (`<==`, L461–L476) checks `value_right.is_nonquadratic()` and fails compilation with `ExecutionError::NonQuadraticConstraint` (`"Non quadratic constraints are not allowed!"`, L4286–L4289). Only expressions reducible to R1CS pass `transform_expression_to_constraint_form` and `node.add_constraint(ctr)`.
- Both `<==` (L429–L438) and `===` (L523–L532) reject `runtime.block_type == BlockType::Unknown` (`ExecutionError::ConstraintInUnknown`) because R1CS circuit topology cannot branch on runtime signals.
- `AssignOp::AssignSignal` (`<--`, L477–L515) emits zero constraints. Passing `--inspect` emits a non-fatal warning *only* if `!value_right.is_nonquadratic() && !node.is_custom_gate`. Inherently non-quadratic operations—field inversion (`1/in`) and bit shifting (`(in >> i) & 1`)—*must* use `<--`, forcing programmers to write separate `===` constraints manually.

In `zcash/halo2` (`7465edf9...`, `halo2_proofs/src/plonk/circuit.rs` L71–L85, L471–L490, L934–L1255), PLONKish custom gates and Plookup-style `lookup` tables remove the degree-2 ceiling, yet the same soundness chasm reappears between `Circuit::configure` and `Circuit::synthesize`: assigning an `Advice` cell without enabling its `Selector`, or assigning matching Rust values to two cells without `enable_equality` + `Assignment::copy`/`constrain_equal`, passes honest proving while leaving cells decoupled for a malicious prover. Likewise, `noir-lang/noir` (`af5d97aa...`, `acvm-repo/acir/src/circuit/opcodes.rs` L58–L156, `brillig.rs` L1–L4) isolates unconstrained `Brillig` hints behind `Opcode::BrilligCall`, leaving constraint completeness on returned witnesses to the programmer or compiler-inserted checks.

#### 2.2 Anatomy of Under-Constrained vs. Over-Constrained Bugs

Basis: source (`iden3/circomlib`, `0xPARC/zk-bug-tracker`) + execution (`support/verify_zk_move_and_uncomputation.py`) + derived.

For specification $f : D \subseteq \mathbb{F}_p^k \to \mathbb{F}_p^r$ and constraint relation $C(x, y, z)$ over inputs $x$, outputs $y$, and intermediates $z$:
- **Completeness**: $\forall x \in D,\ \exists z.\ C(x, f(x), z)$. Failure yields an **over-constrained** circuit (honest input rejected—liveness bug).
- **Soundness**: $\forall x \in D,\ \forall y, z.\ C(x, y, z) \implies y = f(x)$. Failure yields an **under-constrained** circuit (malicious prover forges $y \neq f(x)$—cryptographic break).
- **Weak (Output) Determinism**: $\forall x \in D,\ \forall y_1, z_1, y_2, z_2.\ C(x, y_1, z_1) \land C(x, y_2, z_2) \implies y_1 = y_2$. Given completeness for $f$, weak determinism is necessary and sufficient for soundness, whereas **strong determinism** (also forcing $z_1 = z_2$) is strictly stronger and false for sound idioms such as `IsZero`.

Three canonical circuits from `iden3/circomlib` (`8852c3bc...`) and `0xPARC/zk-bug-tracker` (`56a99667...`) expose the exact failure modes:

1. **`circomlib::IsZero` — Missing Inverse Guard & Weak Determinism** (`circuits/comparators.circom` L24–L34):
   ```circom
   template IsZero() {
       signal input in;
       signal output out;
       signal inv;
       inv <-- in!=0 ? 1/in : 0;
       out <== -in*inv + 1;
       in*out === 0;
   }
   ```
   Omitting `in*out === 0` leaves honest witness generation (`inv = 1/in` for `in != 0`, `out = 0`) passing all tests, yet for any `in != 0` a malicious prover chooses `inv = 0` to satisfy `out = -in*0 + 1 = 1` (probed over $\mathbb{F}_{17}$ at `in = 1`: `{inv: 0, out: 1}` and `{inv: 1, out: 0}` both satisfy). With `in*out === 0` present, `out` is uniquely determined for all $x \in \mathbb{F}_p$, yet at `in = 0` the intermediate `inv` can take *any* of the $p$ field values (`target_unique = true`, `strongly_unique = false`).

2. **`circomlib::Num2Bits` vs. `Num2Bits_strict` — Booleanity, Domain Boundary, and Field Aliasing** (`circuits/bitify.circom` L25–L53; `circuits/aliascheck.circom` L24–L33):
   ```circom
   template Num2Bits(n) {
       signal input in;
       signal output out[n];
       var lc1 = 0; var e2 = 1;
       for (var i = 0; i < n; i++) {
           out[i] <-- (in >> i) & 1;
           out[i] * (out[i] - 1) === 0;
           lc1 += out[i] * e2;
           e2 = e2 + e2;
       }
       lc1 === in;
   }
   ```
   - *Missing booleanity*: Dropping `out[0]*(out[0]-1)===0` allows non-binary witnesses satisfying $\sum 2^i b_i \equiv \text{in} \pmod p$ (over $\mathbb{F}_{17}$ at `in = 5`, both `(1,0,1,0)` and forged `(3,1,0,0)` satisfy).
   - *Domain / completeness boundary*: For $n \le \lfloor\log_2 p\rfloor$ (e.g., `Num2Bits(4)` over $\mathbb{F}_{17}$, $2^4 = 16 < 17$), bits are unique on $[0, 15]$ while `in = 16` has zero witnesses (desired for range checks, over-constrained if arbitrary field inputs are expected).
   - *Field aliasing ($2^n > p$)*: On BN254 ($2^{253} < p < 2^{254}$), `Num2Bits(254)` admits **two** valid binary decompositions for every $x < 2^{254} - p$: the bits of $x$ and the bits of $x + p$. `Num2Bits_strict()` pairs `Num2Bits(254)` with `AliasCheck()` (`CompConstant(-1)` -> `out === 0`), enforcing $\sum 2^i b_i \le p - 1$ over $\mathbb{Z}$. Our probe reproduces this on $\mathbb{F}_{17}$ with `Num2Bits(5)`: `in = 1` admits both `(1,0,0,0,0)` ($1$) and `(0,1,0,0,1)` ($18 \equiv 1 \pmod{17}$); adding `b4 * (b0 + b1 + b2 + b3) = 0` restores uniqueness and completeness across all 17 elements.

3. **Dark Forest v0.3 `LessThan(n)` Modular Wraparound** (`0xPARC/zk-bug-tracker` `README.md` L60–L140; `circomlib/circuits/comparators.circom` L89–L99):
   ```circom
   template LessThan(n) {
       assert(n <= 252);
       signal input in[2];
       signal output out;
       component n2b = Num2Bits(n+1);
       n2b.in <== in[0] + (1<<n) - in[1];
       out <== 1 - n2b.out[n];
   }
   ```
   `LessThan(n)` relies on callers to range-constrain `in[0], in[1] < 2^n` and does **not** enforce that precondition internally. In Dark Forest v0.3 (`RangeProof`), identified by Daira Hopwood, unconstrained inputs wrapped modulo $p$ into $[0, 2^n)$, forging `LessThan`. Over $\mathbb{F}_{257}$ with $n = 4$, `in0 = 250, in1 = 2` yields $(250 + 16 - 2) \bmod 257 = 7$, giving bit 4 = `0` and forged `out = 1` (`250 < 2`); adding `Num2Bits(4)` input checks blocks the exploit.

#### 2.3 Automated Uniqueness and Refinement Verification (`Picus`/`QED^2`, `Ecne`, `CODA`)

Basis: source (`Veridise/Picus`, `franklynwang/EcneProject`) + documentation (Pailoor et al. PLDI '23; Liu et al. IEEE S&P '24).

- **`Picus` / $\mathsf{QED}^2$ (Pailoor et al., PLDI '23; `Veridise/Picus` `138b151d...`)**: Implements the **DPVL** (*Decide & Propagate Verification Loop*, `picus/algorithms/dpvl.rkt`), tracking known-unique wires `ks`, unknown wires `us`, and possible-value sets `range-vec`:
  1. *Deterministic algebraic lemmas* (`dpvl.rkt` L7–L11): `linear-lemma.rkt` (solves single linear unknown with non-zero coefficient mod $p$), `binary01-lemma.rkt` (infers $\{0, 1\}$ range from $x(x-1)=0$), `basis2-lemma.rkt` (propagates uniqueness from $z = \sum_{i=0}^{k-1} 2^i x_i$ with binary $x_i$), `aboz-lemma.rkt` (all-but-one-zero selectors), and `bim-lemma.rkt`. Critically, `basis2-lemma.rkt` L139–L143 bounds `basis2-seqs` to `(range (floor (log config:p 2)))`, guaranteeing $2^k - 1 < p$ so the lemma is **sound against field aliasing** (refusing unguarded 254-bit BN254 decompositions).
  2. *Relational finite-field SMT* (`dpvl-solve`, `dpvl.rkt` L66–L115): Duplicates constraints into `"x"` and `"y"` copies, equates all $j \in \text{ks}$, asserts $x_{\text{sid}} \neq y_{\text{sid}}$, and queries `cvc5` (`FF` finite-field theory). `unsat` promotes `sid` into `ks`; `sat` on `:target-set` reports a concrete two-witness forgery; `sat` on non-target intermediates (such as `inv` in `IsZero`) is ignored to avoid false positives under weak determinism.
  3. *Results (Pailoor et al., PLDI '23 / ePrint 2023/512)*: Solved **70%** of **163** real-world Circom benchmarks (proving uniqueness or producing counterexamples) and uncovered **8 previously unknown vulnerabilities** in deployed ZK libraries.
- **`Ecne` (`franklynwang/EcneProject` `25935352...`)**: Julia-based R1CS uniqueness checker (`solveWithTrustedFunctions`) introducing modular verification via pre-verified trusted sub-circuit specifications and foundational binary/basis propagation rules.
- **`CODA` (Liu et al., IEEE S&P '24, `10.1109/SP54263.2024.00078`)**: Addresses functional correctness beyond uniqueness (which cannot catch a circuit that uniquely computes the *wrong* formula) by lowering refinement-typed ZK programs into Coq obligations discharged via custom finite-field tactics. (See `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` for Rust/zkVM context.)

---

### 3. Linear Resource-Metered Virtual Machines (`Move` Bytecode Verifier vs. `EVM`)

#### 3.1 Mutable-Map Accounting, Untyped Dynamic Dispatch, and Reentrancy (`EVM` vs. `Move`)

Basis: documentation (Blackshear et al., 2020-05-26 §2.3) + source (`move-language/move` `cyclic_dependencies.rs`).

Blackshear et al. (2020-05-26 §2.3) diagnose three structural causes of EVM/Solidity asset exploits:
1. **Indirect asset representation**: Custom tokens (e.g., ERC-20) are stored as plain `uint256` entries inside `mapping(address => uint256)`, so bytecode cannot distinguish assets from integers or enforce conservation across transfers and data structures.
2. **Non-extensible scarcity**: Native Ether has hardcoded scarcity in EVM semantics, whereas custom assets must re-implement conservation manually.
3. **Dynamic dispatch callbacks and reentrancy**: Calling or transferring Ether to an external address (`CALL`) performs dynamic dispatch into untrusted fallback code, which can re-enter the caller before balances are decremented (the DAO and Parity Wallet exploits; see `anneal-law-defi-mechanism-design-voting-and-medical-survey` for EVM formal verifier surveys).

`Move` structurally eliminates callback reentrancy and indirect accounting:
- **Static dispatch + acyclic module graph**: Bytecode `Call`/`CallGeneric` targets are statically resolved handles with no runtime fallback hooks, and `cyclic_dependencies.rs` (`move-language/move` `c453c909...` L22–L70) enforces via DFS that module dependency and friend graphs are strictly acyclic—so a callee cannot import or re-enter its caller.
- **Module-encapsulated linear resources**: Only a struct's defining module may `Pack`, `Unpack`, or borrow its fields; external modules treat it as an opaque value subject to bytecode-verified linearity.

#### 3.2 Move's Four-Bit Ability System, Field Requirements, and Dialect Divergence

Basis: source (`MystenLabs/sui` `file_format.rs`, `move-language/move` `ability_field_requirements.rs`) + documentation (Blackshear et al., 2020-05-26 §5.2).

The May 2020 whitepaper used a binary *kind* split (`resource` vs. `unrestricted`), whereas modern Move bytecode (`MystenLabs/sui` `6463a0de...`, `file_format.rs` L648–L660, L765–L799) uses a 4-bit `AbilitySet(u8)`:

| Bitmask | `Ability` | Permitted Bytecode Operations | `Ability::requires()` on Fields | Conservation Role |
| :--- | :--- | :--- | :--- | :--- |
| `0x1` | `Copy` | `CopyLoc`, `ReadRef` | `Copy` | Absent $\implies$ **non-duplicable** (blocks double-spend) |
| `0x2` | `Drop` | `Pop`, `WriteRef`, `StLoc` overwrite, `Eq`/`Neq`, `Ret` leftover | `Drop` | Absent $\implies$ **non-discardable** (blocks silent loss/burn) |
| `0x4` | `Store` | Nested persistence inside global/object structs | `Store` | Governs cross-transaction persistence |
| `0x8` | `Key` | Top-level storage key (`MoveTo`/`MoveFrom` or Sui object root) | `Store` | Top-level persistent resource/object |

**Field-ability smuggling check**: `ability_field_requirements.rs` (`move-language/move` L20–L52) computes `required_abilities` via `Ability::requires()` and enforces `required_abilities.is_subset(field_abilities)` for every declared field, rejecting violations with `StatusCode::FIELD_MISSING_TYPE_ABILITY`. Wrapping a linear `Coin` (`store` only) in `struct FakeCopy has copy { c: Coin }` is thus rejected statically.

**Zero-ability "hot potato" pattern**: A struct with `AbilitySet::EMPTY` (no `copy`, `drop`, `store`, `key`) cannot be duplicated, dropped, *or persisted in storage*. Returning `(Coin, FlashReceipt)` from a flash-loan function guarantees at the bytecode verifier level that even adversarial caller bytecode must pass `FlashReceipt` back to the defining module's `repay` function before `Ret`, or abort atomically.

**Dialect divergence (Core/Aptos Move vs. Sui Move)**:
- Core/Aptos Move (`move-language/move` `c453c909...`) uses address-indexed global storage (`MoveTo`, `MoveFrom`, `BorrowGlobal`, `Exists`) checked statically by `acquires_list_verifier.rs` and dynamically reference-counted by the interpreter (`Blackshear et al. 2020` §5.2 p. 19).
- Sui Move (`MystenLabs/sui` `6463a0de...`, `locals_safety/mod.rs` L150–L159) marks those global opcodes `Deprecated` (`MoveToDeprecated` et al.), replacing them with an object-centric model where `key` structs carry unique `UID`s and are passed directly by value or reference, enabling parallel execution over disjoint owned objects.

#### 3.3 Untrusted-Bytecode Verification Pipeline (`type_safety`, `locals_safety`, `reference_safety`)

Basis: source (`move-language/move` `verifier.rs`; `MystenLabs/sui` `code_unit_verifier.rs`, `type_safety.rs`, `locals_safety/mod.rs`, `reference_safety/abstract_state.rs`) + execution (`support/verify_zk_move_and_uncomputation.py`).

Because Move's source compiler is **outside the TCB**, every published `CompiledModule` undergoes a fixed-order static verification pipeline (`verifier.rs` L87–L119, wrapped in `catch_unwind` converting panics into `VERIFIER_INVARIANT_VIOLATION`):

1. **Module-level checks**: `BoundsChecker` (validates table indices first), `LimitsVerifier`, `DuplicationChecker`, `SignatureChecker`, `InstructionConsistency`, `constants`, `friends`, `ability_field_requirements`, `RecursiveStructDefChecker` / `RecursiveDataDefChecker`, and `InstantiationLoopChecker`.
2. **Per-function abstract interpretation (`CodeUnitVerifier::verify_common`, `MystenLabs/sui` `code_unit_verifier.rs` L169–L205)**:
   - `control_flow::verify_function`: Builds the CFG and enforces `max_basic_blocks` and `max_back_edges_per_function`/`module`.
   - `StackUsageVerifier`: Guarantees balanced stack heights across CFG joins and bounds `max_value_stack_size`.
   - `type_safety::verify` (`type_safety.rs` L608–L818): Enforces ability preconditions on operand-stack instructions:
     - `Pop`: requires `has_drop()` $\to$ `POP_WITHOUT_DROP_ABILITY` (L608–L614).
     - `CopyLoc`: requires `has_copy()` $\to$ `COPYLOC_WITHOUT_COPY_ABILITY` (L720–L726).
     - `ReadRef`: requires inner `has_copy()` $\to$ `READREF_WITHOUT_COPY_ABILITY` (L785–L798).
     - `WriteRef`: requires inner `has_drop()` $\to$ `WRITEREF_WITHOUT_DROP_ABILITY` (L800–L818), preventing silent destruction of the overwritten linear resource.
   - `locals_safety::verify` (`locals_safety/mod.rs` L38–L95): Forward dataflow analysis over the **3-point availability lattice** `{Unavailable, MaybeAvailable, Available}` where `join(Available, Unavailable) = MaybeAvailable`:
     - `MoveLoc(idx)`: requires `Available`, sets `Unavailable` (else `MOVELOC_UNAVAILABLE_ERROR`).
     - `StLoc(idx)`: rejects `Available | MaybeAvailable` if `!has_drop()` (`STLOC_UNSAFE_TO_DESTROY_ERROR`), catching conditional branch leaks on overwrite.
     - `Ret`: rejects any `Available | MaybeAvailable` local lacking `drop` (`UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`).
   - `reference_safety` (`reference_safety/abstract_state.rs` L307–L565, L711–L740): Maintains a directed `BorrowGraph` rooted at `frame_root()` with `Label::Local`, `Label::StructField`, and `Label::Global` edges:
     - `move_loc` rejects moving a borrowed non-reference local (`MOVELOC_EXISTS_BORROW_ERROR`, L443–L445); `st_loc` releases any previous reference in the slot and rejects overwriting a borrowed local (`STLOC_UNSAFE_TO_DESTROY_ERROR`, L457–L465).
     - `read_ref` requires `is_freezable(id)` on `&mut` (no consistent child mutable borrows, else `READREF_EXISTS_MUTABLE_BORROW_ERROR`, L330–L338, L511–L523).
     - `write_ref` requires `is_writable(id)` (no consistent child borrows, else `WRITEREF_EXISTS_BORROW_ERROR`, L307–L311, L525–L537).
     - `call` checks no `acquired_resource` is globally borrowed (`GLOBAL_REFERENCE_ERROR`, L720–L724) and every `&mut` argument is writable (`CALL_BORROWED_MUTABLE_REFERENCE_ERROR`, L729–L737).
     - Sui Move (`code_unit_verifier.rs` L191–L215) also provides `regex_reference_safety`, engineered to be strictly more permissive than the graph analysis while keeping verification cost bounded.

#### 3.4 Dual Metering: Execution Gas and Verifier-Time Metering as Conservation Requirements

Basis: normative/documentation (Blackshear et al., 2020-05-26 §5.1–§5.2) + source (`move-language/move` `gas.rs`, `MystenLabs/sui` `code_unit_verifier.rs`, `locals_safety/mod.rs`) + execution.

1. **Runtime gas metering + atomic rollback (`Blackshear et al. 2020` §5.2 p. 18; `move-vm-types/src/gas.rs` L12–L75)**: Non-termination would permanently trap resources held in local variables, while an unrolled-back mid-execution abort would destroy in-flight resources on the operand stack. Deterministic per-instruction `GasMeter` accounting guarantees termination, and atomic transaction rollback on `OUT_OF_GAS` or `Abort` discards all partial state updates so resources return intact to their pre-transaction locations (confirmed in our probe: total supply stays `125` on both commit and `OUT_OF_GAS` rollback).
2. **Static verifier metering (`MystenLabs/sui` `move_bytecode_verifier_meter::Meter`, `VerifierConfig`)**: Because untrusted bytecode triggers fixpoint abstract interpretation on every validator node, adversarial CFGs or borrow graphs could cause verifier DoS. Sui Move threads a `BoundMeter` across `Scope::Function`, `Scope::Module`, and `Scope::Package`, charging per-instruction (`STEP_BASE_COST`, `RET_COST`) and borrow-graph-size costs (`charge_graph_size`) against `max_per_fun_meter_units` and `max_per_mod_meter_units`.

---

### 4. Quantum and Reversible Linear Languages (`Silq`, `Quipper`, `QWIRE`, `SQIR`/`VOQC`, `Janus`)

#### 4.1 Physical Conservation Laws, Reversible Computing, and the Ancilla Entanglement Trap

Basis: normative theory (Landauer 1961; Bennett 1973; Wootters & Zurek 1982; Pati & Braunstein 2000; Yokoyama & Glück PEPM '07) + execution (`support/verify_zk_move_and_uncomputation.py`).

- **Thermodynamic reversibility**: By Landauer's Principle (1961), erasing 1 bit dissipates at least $k_B T \ln 2$ of heat. Bennett (1973) showed any classical computation can be executed logically reversibly via **compute–copy–uncompute**: compute forward keeping history, XOR-copy the output, then run backward to zero all temporary scratch bits. Reversible languages like `Janus` (Yokoyama & Glück, PEPM '07) enforce bijectivity via invertible updates (`x += e`, `x ^= e`), entry/exit branch assertions (`if e1 ... else ... fi e2`), reversible loops (`from e1 do ... loop ... until e2`), and explicit `uncall`; functional `Theseus` builds on type isomorphisms ($A \leftrightarrow B$).
- **Quantum unitarity, No-Cloning, and No-Deleting**: Closed quantum evolution applies unitary operators $U^\dagger U = I$ on $(\mathbb{C}^2)^{\otimes n}$. Wootters–Zurek (1982) forbids arbitrary cloning $|\psi\rangle|0\rangle \mapsto |\psi\rangle|\psi\rangle$; Pati–Braunstein (2000) forbids deleting an unknown copy.

**Why omitting ancilla uncomputation breaks interference**: Prepare $|+\rangle = \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle)$ on qubit $x$ and compute a temporary ancilla $a = x$ via $\text{CNOT}(x, a)$, producing Bell state $|\Phi^+\rangle = \frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)$.
- *Without uncomputation*: Discarding $a$ before $H(x)$ leaves $x$ in the reduced density matrix $\rho_x = \operatorname{Tr}_a\bigl((H \otimes I)|\Phi^+\rangle\langle\Phi^+|(H \otimes I)\bigr) = \frac{1}{2} I$: purity collapses to $\operatorname{Tr}(\rho_x^2) = 0.5$ and $P(x=0) = 0.5$ (interference destroyed).
- *With Bennett uncomputation*: Applying $\text{CNOT}^\dagger(x, a) = \text{CNOT}(x, a)$ restores the separable product state $|+\rangle \otimes |0\rangle_a$ (purity $1.0$), so $H(x)$ deterministically produces $|0\rangle$ with $P(x=0) = 1.0$.
- *2-qubit Grover search for $|11\rangle$*: Computing ancilla $t = x_0 \land x_1$ (`CCX(x0, x1, t)`), applying phase flip `Z(t)`, and running 1 Grover diffusion iteration yields **$P(11) = 1.0$ (purity $1.0$)** when `CCX` uncomputes $t$ before diffusion, but collapses to **$P(11) = 0.625$ (purity $0.625$)** when uncomputation of $t$ is omitted—a $37.5\%$ failure invisible to basis-state testing.

#### 4.2 `Silq`'s Annotation Hierarchy and Provably Physical Automatic Uncomputation

Basis: normative/source (Bichsel, Baader, Gehr & Vechev, PLDI '20 §4, §6–§8; `eth-sri/silq` `hqir.d`, `qsim.d`, `test/*.slq`) + execution (`support/verify_zk_move_and_uncomputation.py`).

`Silq` (Bichsel et al., PLDI '20, `10.1145/3385412.3386007`) synthesizes safe automatic Bennett uncomputation (`autoforget`) via five annotations backed by Theorems 7.1–7.5:

| Annotation | Formal Semantic Guarantee (PLDI '20 §7) | Linearity & Uncomputation Role | Examples |
| :--- | :--- | :--- | :--- |
| **`!`** (classical) | Basis states only (no superposition); `Thm 7.1 (Type Preservation)` | Unrestricted (copyable and droppable) | `0 : !B`, `n : !N`, `H : B !→_mfree B` |
| **`const`** | `Thm 7.2 (Const Semantics)`: $\sum \gamma_{v,w} |v\rangle_{\bar x}|w\rangle_{\bar y}\tilde\psi_{v,w} \mapsto \sum \gamma_{v,w} |v\rangle_{\bar x}\chi_{v,w}\tilde\psi_{v,w}$ | **Non-linear** (may be basis-duplicated via `CNOT` or ignored) because preserved original allows later uncomputation; non-`const` quantum variables are **strictly linear** | Oracle input `const x : uint[n]`, control qubit |
| **`mfree`** | `Thm 7.3 (Mfree Semantics)`: For fixed classical state $\sigma$, acts as a **linear isometry** ($\langle \psi_1|\psi_2\rangle = \langle \psi_1'|\psi_2'\rangle$) | Required by `reverse(f)` and quantum-controlled `if q { ... }` (isometric rather than square unitary when ancillae are allocated) | `H`, `X`, `phase` |
| **`qfree`** | `Thm 7.4 (Qfree Semantics)`: Ground-set map $\bar f$ mapping $\sum_\sigma \gamma_\sigma |\sigma\rangle\tilde\psi_\sigma \mapsto \sum_\sigma \gamma_\sigma |\bar f(\sigma)\rangle\tilde\psi_\sigma$ | Creates **no new superpositions** (`X` is `qfree`; `H` is `mfree`, not `qfree`) | `X`, `dup`, classical arithmetic/boolean oracles |
| **`lifted`** | `qfree` + all params `const` $\implies \bar f(v) = (v, \tilde f(v))$ | **Sufficient condition for safe automatic uncomputation**: reversing the `qfree` body from preserved `const` inputs resets ancilla to $|0\rangle$ | Grover oracle `f : uint[n] !→_lifted B` |

**Physical basis duplication vs. cloning (PLDI '20 §4.4 p. 7)**: Silq distinguishes unphysical cloning $\sum \gamma_v |v\rangle \mapsto (\sum \gamma_v |v\rangle)^{\otimes 2}$ from physical basis duplication $\sum \gamma_v |v\rangle \mapsto \sum \gamma_v |v\rangle|v\rangle$ via `CNOT` (`qfree_call[qbuiltin.dup]` / `qfree_call_rev[qbuiltin.dup]` in `hqir.d` L254–L255). Passing a `const` variable to a consuming parameter implicitly duplicates it and consumes only the duplicate.

**Five static physicality rejections (`Theorem 7.5 (Physicality)` — QRAM-realizable)** (PLDI '20 §4.4):
1. `useConsumed`: reusing a consumed non-`const` linear qubit.
2. `discard`: silently dropping a non-`const` quantum parameter.
3. `nonQfree`: automatically uncomputing a non-`qfree` temporary (e.g., `H(x)`).
4. `nonConst`: automatically uncomputing a temporary after consuming one of its dependencies (e.g., `X(c)` consumes `c`; Silq also infers *temporary `const`* lifetimes within statements such as `f(cand)`).
5. `condMeas`: executing non-`mfree` `measure` inside a quantum-conditioned branch `if q { ... }`.

**Compiler IR and empirical evaluation**: In `eth-sri/silq` (`5632173e...`), `hqir.d` (L199–L277, L8478–L8567, L9287–L9308) lowers calls to `qfree_call`/`mfree_call` and inverses `qfree_call_rev`/`mfree_call_rev`, scheduling `autoforget` uncomputations topologically (`places`, `uncomputedAfter`) before releasing `const` dependencies; explicit manual `forget(y = x)` statements verify equivalence at simulation time and raise `"bad forget"` on violations (`qsim.d` L596, L1072, L2338, L4086; `test/badControlUncomp.slq`, `test/badReverse.slq`). Across all 28 tasks of Microsoft's Q# S18/W19 coding contests (PLDI '20 Table 1, §8.1), Silq used **267 LOC** vs. **493 LOC** for Q# reference solutions (**-46%**, **-59%** vs. top-10 contestants), **10** vs. **22** quantum primitives, **3** vs. **6** annotations, and **37** vs. **87** low-level gates (and **-38%** LOC vs. Quipper).

#### 4.3 Circuit-Embedding and Verified Quantum IRs (`Quipper`, `QWIRE`, `SQIR`/`VOQC`)

Basis: source (`inQWIRE/SQIR` `SQIR/SQIR.v`, `UnitarySem.v`, `UnitaryOps.v`, `VOQC/Main.v`) + documentation (Green et al. PLDI '13; Paykin et al. POPL '17; Hietala et al. POPL '21).

| System | Formalism | No-Cloning Enforcement | Uncomputation / Inversion | Verification Status |
| :--- | :--- | :--- | :--- | :--- |
| **`Quipper`** (PLDI '13) | Haskell EDSL (`Circ` monad) | None statically (wire duplication fails only at circuit generation/runtime) | Manual `with_computed` / `reverse_generic` without static disentanglement proof | Unverified generator |
| **`QWIRE`** (POPL '17) | Linear circuit language in classical host | Linear context splitting ($\Gamma_1, \Gamma_2$) | Explicit linear wiring and boxing | Core soundness in Coq; context-splitting complicates optimizer proofs |
| **`SQIR` / `VOQC`** (POPL '21; `inQWIRE/SQIR` `134fb942...`) | Coq-embedded `ucom U dim` + non-unitary `com U dim` | Concrete global register indices (`nat`) + `uc_well_typed` distinctness (`m <> n`, `SQIR.v` L85–L90) | Verified `invert` with Coq proof `invert_correct : (uc_eval c)† = uc_eval (invert c)` (`UnitaryOps.v` L17–L51) | First fully verified quantum circuit optimizer extracted from Coq to OCaml |

Direct inspection of `inQWIRE/SQIR` (`134fb942...`) highlights three verification engineering decisions:
- **Concrete-index well-typedness (`SQIR/SQIR.v` L12–L175)**: `ucom U dim` applies 1-, 2-, and 3-qubit gates to `nat` indices over `base_Unitary` (`U_R θ ϕ λ`, `U_CNOT`); `uc_well_typed` enforces `n < dim` and pairwise distinct indices (`m <> n`), with decidable reflection `uc_well_typed_b_equiv`, avoiding linear context-permutation proof boilerplate. `com` adds `meas n c1 c2` (encoding `reset n := meas n (X n) skip`).
- **Symbolic unitary semantics & inversion (`UnitarySem.v` L15–L55; `UnitaryOps.v` L17–L51)**: `uc_eval` denotes circuits as symbolic $2^{\text{dim}} \times 2^{\text{dim}}$ complex matrices via padded Kronecker products (`pad_u`, `pad_ctrl`), quantifying proofs over arbitrary `dim`. `invert` reverses composition and maps `U_R θ ϕ λ -> U_R (-θ) (-λ) (-ϕ)` and `U_CNOT -> U_CNOT`, proved via `invert_correct` and confirmed numerically by our probe on a 5-gate 3-qubit circuit ($\max \| U(\text{invert}(C)) U(C) - I \|_\infty = 2.30 \times 10^{-16}$).
- **Verified optimization passes (`VOQC/Main.v` L1–L90)**: `NotPropagation`, `HadamardReduction`, `GateCancellation`, `Optimize1qGates`, `RotationMerging`, `SwapRoute`, `MappingValidation`, `convert_to_ibm`, and `convert_to_rzq` preserve exact unitary equivalence (`=l=`) or phase equivalence (`≅l≅`), well-typedness, and directed hardware coupling graphs (`convert_to_ibm_preserves_mapping`). (See `anneal-cps-robotics-aerospace-eda-and-quantum-survey` for ZX-calculus and QEC tooling.)

---

### 5. Executable Multi-Paradigm Verification Probe Summary

Basis: execution (`support/verify_zk_move_and_uncomputation.py`, Python 3.10+ stdlib-only, `python3 -B -W error`, `< 0.3s`).

| Domain | Verification Check | Observed Exact Result |
| :--- | :--- | :--- |
| **ZK / R1CS** | `IsZero` omitting `in * out === 0` over $\mathbb{F}_{17}$ | Forgery at `in = 1`: `{inv: 0, out: 1}` vs. `{inv: 1, out: 0}` |
| **ZK / R1CS** | Sound `circomlib::IsZero` over $\mathbb{F}_{17}$ | `target_unique = true`, `strongly_unique = false` (`inv` free at `in = 0`) |
| **ZK / R1CS** | `Num2Bits(4)` missing `b0 * (b0 - 1) === 0` over $\mathbb{F}_{17}$ | Forgery at `in = 5`: `(1,0,1,0)` vs. `(3,1,0,0)` |
| **ZK / R1CS** | Sound `Num2Bits(4)` over $\mathbb{F}_{17}$ ($2^4 < 17$) | `Basis2Lemma` proves unique; `in = 16` unsat (range boundary) |
| **ZK / R1CS** | `Num2Bits(5)` aliasing over $\mathbb{F}_{17}$ ($2^5 > 17$) | `Basis2Lemma` guarded ($5 > 4$); forgery at `in = 1`: `1` vs. `18`; `AliasCheck` restores uniqueness & completeness |
| **ZK / R1CS** | Dark Forest v0.3 `LessThan(4)` wraparound over $\mathbb{F}_{257}$ | `in0 = 250, in1 = 2` $\implies (250 + 16 - 2) \bmod 257 = 7 \implies$ forged `out = 1`; blocked by `Num2Bits(4)` |
| **Move VM** | `FakeCopy has copy { c: Coin }` field-ability smuggling | Rejected: `FIELD_MISSING_TYPE_ABILITY(FakeCopy.c)` |
| **Move VM** | `Coin` double-spend, ref-bypass, silent drop | Rejected: `COPYLOC_WITHOUT_COPY_ABILITY`, `READREF_WITHOUT_COPY_ABILITY`, `POP_WITHOUT_DROP_ABILITY`, `WRITEREF_WITHOUT_DROP_ABILITY` |
| **Move VM** | Branch join (`MaybeAvailable`) leak on `Ret` and `StLoc` | Rejected: `UNSAFE_RET_UNUSED_VALUES_WITHOUT_DROP`, `STLOC_UNSAFE_TO_DESTROY_ERROR` |
| **Move VM** | Borrow safety (`MoveLoc` borrowed; `WriteRef`/`ReadRef` parent `&mut` with live child `&mut`) | Rejected: `MOVELOC_EXISTS_BORROW_ERROR`, `WRITEREF_EXISTS_BORROW_ERROR`, `READREF_EXISTS_MUTABLE_BORROW_ERROR` |
| **Move VM** | Zero-ability `FlashReceipt` hot potato & OOG rollback | Sound flash loan passes; abandoned receipt rejected; `OUT_OF_GAS` rollback preserves supply `125` |
| **Quantum** | Silq static checks (`useConsumed`, `discard`, `nonQfree`, `nonConst`, `condMeas`, `lifted`) | All 5 unphysical patterns rejected; `lifted` oracle + `auto_forget` accepted (`OK`) |
| **Quantum** | Hadamard interference (`H(x)` after `a = dup(x)`) | Without uncomp: `P(0) = 0.5`, purity `0.5`; with `CNOT^\dagger`: `P(0) = 1.0`, purity `1.0` |
| **Quantum** | 2-qubit Grover (`|11>`, ancilla `t = x0 & x1`) | Without uncomp: `P(11) = 0.625`, purity `0.625`; with `CCX^\dagger`: `P(11) = 1.0`, purity `1.0` |
| **Quantum** | SQIR `invert` unitary identity on 5-gate 3-qubit circuit | $\max \| U(\text{invert}(C)) U(C) - I \|_\infty = 2.30 \times 10^{-16}$ |

## Boundaries

- **not examined**:
  - Live execution of upstream `circom`, `halo2`, `nargo`, `cairo-compile`, `picus`, `move-bytecode-verifier` Rust binaries, `silq` LDC binaries, or `coqc` (`SQIR`/`VOQC`) was not run; execution evidence comes from `support/verify_zk_move_and_uncomputation.py`, paired with direct source inspection of all pinned upstream revisions.
  - The `tgehr/ast` submodule referenced by `eth-sri/silq/.gitmodules` (`semantic_.d`, `type.d`, `reverse.d`) was not fetched after unauthenticated GitHub tree API calls hit rate limits; Silq's typing rules and theorems were verified directly from Bichsel et al. (PLDI '20) and `eth-sri/silq` (`hqir.d`, `qsim.d`, `test/*.slq`).
  - Cryptographic protocol layers outside circuit constraints (Fiat–Shamir "Frozen Heart" transcripts, trusted setups, KZG/IPA/FRI polynomial commitments, zkVM lookup tables) and fault-tolerant QEC/pulse compilation were not examined (see `anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey` and `anneal-cps-robotics-aerospace-eda-and-quantum-survey`).
- **unknown**:
  - Solve rates of `Veridise/Picus` (`138b151d...`) on the post-PLDI-23 `gnark` `.sr1cs` benchmarks remain unknown without executing the Racket/`cvc5` harness.
  - Mainnet default activation status of `MystenLabs/sui`'s `switch_to_regex_reference_safety` across protocol epochs beyond commit `6463a0de...` cannot be inferred from verifier source alone.
- **known not to apply**:
  - **Uniqueness $\neq$ functional correctness**: `Picus`/`Ecne` uniqueness proofs do not rule out deterministic logic errors (constraining the wrong formula) or over-constrained completeness failures; specification refinement requires tools such as `CODA`.
  - **Move linearity $\neq$ economic safety**: Bytecode abilities protect resource handle conservation, not minting authorization, oracle pricing, or multi-transaction DeFi invariants.
  - **Core/Aptos global-storage opcodes do not apply to Sui Move**: `MoveTo`/`MoveFrom`/`BorrowGlobal` and `acquires_list_verifier.rs` apply to Core/Aptos Move and are deprecated in Sui Move's object model.
  - **Silq automatic uncomputation does not cover non-`qfree` inverses**: Reversing superposing subprograms (e.g., QFT) requires explicit `reverse(...)` or manual `forget(...)`.
- **unsupported**:
  - `Circom` rejects non-quadratic `<==` (`NonQuadraticConstraint`) and signal-branched constraints (`ConstraintInUnknown`).
  - `zcash/halo2` panics if a simple selector appears inside `ConstraintSystem::lookup` (`circuit.rs` L1069–L1071).
  - `Move` rejects cyclic module dependencies (`cyclic_dependencies.rs`), recursive structs, and `WriteRef` on non-`drop` types.
  - `Silq` rejects reversing non-`mfree` functions, quantum-controlled measurements, dropping non-`const` qubits, and auto-uncomputing non-`qfree` or consumed-dependency values.
  - `SQIR`'s `uc_eval` (`UnitarySem.v` L24–L30) evaluates `uapp3` to `Zero` unless decomposed to 1-/2-qubit base gates first.

## Evidence

All evidence below was acquired and verified on `2026-11-19`.

### Primary Source Code Repositories (Pinned 40-Character Commits)

1. **`iden3/circom` @ `9b4b23331644e17868c90a85768826ed3bcba59f`** (`2026-10-20`): `constraint_generation/src/execute.rs` L148–L157 (`ExecutionError`), L425–L555 (`AssignConstraintSignal`, `AssignSignal` + `--inspect`, `ConstraintEquality`, `BlockType::Unknown`), L4285–L4294.
2. **`iden3/circomlib` @ `8852c3bc91e3ede890f2143f36457b25302abce2`** (`2026-11-18`): `circuits/comparators.circom` L24–L34 (`IsZero`), L89–L99 (`LessThan`); `circuits/bitify.circom` L25–L53 (`Num2Bits`, `Num2Bits_strict`); `circuits/aliascheck.circom` L24–L33 (`AliasCheck`).
3. **`zcash/halo2` @ `7465edf9110aace00b8c24b96270e1b820fd39fb`** (`2026-11-14`): `halo2_proofs/src/plonk/circuit.rs` L71–L85, L261–L300, L344–L490 (`Assignment::copy`, `Circuit::configure`/`synthesize`), L934–L1085 (`ConstraintSystem`, `enable_equality`, `lookup` L1069–L1071), L1200–L1255 (`create_gate`, `compress_selectors`).
4. **`noir-lang/noir` @ `af5d97aaa0f67fde5da9a7a790968b88cffff439`** (`2026-11-18`): `acvm-repo/acir/src/circuit/opcodes.rs` L58–L165 (`Opcode`); `acvm-repo/acir/src/circuit/brillig.rs` L1–L5.
5. **`starkware-libs/cairo` @ `98565f78d3bebb0e667607f549cb668edaf7bf9e`** (`2026-11-15`): `crates/cairo-lang-casm/src/instructions.rs` L14–L55 (`InstructionBody`); `crates/cairo-lang-casm/src/hints/mod.rs` L26–L34 (`Hint`).
6. **`Veridise/Picus` @ `138b151d3a388e5b6c040c163e0a1db04f2ceda6`** (`2024-03-13`): `README.md`; `picus/algorithms/dpvl.rkt` L1–L115; `picus/algorithms/lemmas/{linear,binary01,aboz,basis2}-lemma.rkt` (`basis2-lemma.rkt` L139–L143 aliasing bound).
7. **`franklynwang/EcneProject` @ `25935352ca30705ad47363dcf200822635edc1c7`** (`2022-05-22`): `README.md` (`solveWithTrustedFunctions`).
8. **`0xPARC/zk-bug-tracker` @ `56a996672fb50486279126c8e12530f2bf933d0b`** (`2024-12-19`): `README.md` L44–L140 (vulnerability taxonomy and Dark Forest v0.3 `LessThan` postmortem).
9. **`MystenLabs/sui` @ `6463a0de12c80520f1a6186a1109202ec4b73c7f`** (`2026-11-19`): `external-crates/move/crates/move-binary-format/src/file_format.rs` L648–L660, L765–L799 (`Ability`, `requires`); `move-bytecode-verifier/src/{verifier.rs,code_unit_verifier.rs,type_safety.rs,locals_safety/mod.rs,reference_safety/abstract_state.rs}`.
10. **`move-language/move` @ `c453c90994cba0af30314fe4134acee57fb20d0c`** (`2024-05-04`): `language/move-bytecode-verifier/src/{verifier.rs,ability_field_requirements.rs,cyclic_dependencies.rs}`; `language/move-vm/types/src/gas.rs` L12–L75.
11. **`eth-sri/silq` @ `5632173e9cbc4e4accf9532effcef7274fa242c0`** (`2026-11-18`): `hqir.d` L199–L277, L8478–L8567, L9042–L9332; `qsim.d` L585–L596, L1066–L1125, L2333–L2340, L2684–L2705, L4074–L4102; `test/{badControlUncomp,badReverse,classicalQfree1,classicalQfreeReverse1}.slq`.
12. **`inQWIRE/SQIR` @ `134fb942265091baa3e3972f78f72da41827351f`** (`2025-07-30`): `SQIR/{SQIR.v,UnitarySem.v,UnitaryOps.v}`; `VOQC/Main.v` L1–L90.

### Primary Papers and Specifications

- **Pailoor et al. (2023)**: *"Automated Detection of Under-Constrained Circuits in Zero-Knowledge Proofs"*, PACMPL Vol. 7 (PLDI '23), Art. 168, DOI `10.1145/3591282`, ePrint `2023/512`.
- **Liu et al. (2024)**: *"Certifying Zero-Knowledge Circuits with Refinement Types"*, IEEE S&P '24, DOI `10.1109/SP54263.2024.00078`, ePrint `2023/547` (`CODA`).
- **Blackshear et al. (2020)**: *"Move: A Language With Programmable Resources"*, `2020-05-26`, `https://diem-developers-components.netlify.app/papers/diem-move-a-language-with-programmable-resources/2020-05-26.pdf`.
- **Bichsel, Baader, Gehr & Vechev (2020)**: *"Silq: A High-Level Quantum Language with Safe Uncomputation and Intuitive Semantics"*, PLDI '20, DOI `10.1145/3385412.3386007`.
- **Hietala, Rand, Hung, Wu & Hicks (2021)**: *"A Verified Optimizer for Quantum Circuits"*, PACMPL Vol. 5 (POPL '21), DOI `10.1145/3434318`, `arXiv:1912.02250`.
- **Foundational context**: Landauer (1961, *IBM J. Res. Dev.* 5(3):183–191); Bennett (1973, *IBM J. Res. Dev.* 17(6):525–532); Wootters & Zurek (1982, *Nature* 299:802–803); Pati & Braunstein (2000, *Nature* 404:164–165); Yokoyama & Glück (PEPM '07, `Janus`); Green et al. (PLDI '13, `Quipper`); Paykin, Rand & Zdancewic (POPL '17, `QWIRE`).

### Preserved Executable Support Material

- [`support/verify_zk_move_and_uncomputation.py`](support/verify_zk_move_and_uncomputation.py): Python 3.10+ stdlib-only probe verified with `python3 -B -W error` (exit `0`, zero warnings, ~0.22s).

## Revalidation

1. **Re-run the preserved multi-paradigm probe** (`< 1s`, zero external dependencies):
   ```console
   python3 -B -W error reports/zk-circuit-dsls-resource-metered-vms-and-quantum-linear-languages/support/verify_zk_move_and_uncomputation.py
   ```
2. **Diff ZK compiler/verifier control points against newer revisions**: `iden3/circom` `constraint_generation/src/execute.rs` (`AssignSignal`/`AssignConstraintSignal`); `zcash/halo2` `halo2_proofs/src/plonk/circuit.rs` (`lookup`/`create_gate`); `noir-lang/noir` `acvm-repo/acir/src/circuit/opcodes.rs` (`BrilligCall`); `Veridise/Picus` `picus/algorithms/{dpvl.rkt,lemmas/basis2-lemma.rkt}`.
3. **Diff Move verifier rules**: `file_format.rs` (`Ability`, `requires`), `code_unit_verifier.rs` (`verify_common`, `switch_to_regex_reference_safety`), `locals_safety/mod.rs`, and `reference_safety/abstract_state.rs`.
4. **Diff Quantum IR / uncomputation passes**: `eth-sri/silq` `hqir.d` (`opForget`, `qfree_call_rev`) and `test/*.slq`; `inQWIRE/SQIR` `SQIR/{SQIR.v,UnitaryOps.v}` and `VOQC/Main.v` (or run `dune build` in an upstream Coq checkout).
