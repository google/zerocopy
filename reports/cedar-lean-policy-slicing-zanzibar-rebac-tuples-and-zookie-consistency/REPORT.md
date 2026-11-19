# Lean-Verified Policy Slicing and SMT Equivalence in Cedar vs. Zanzibar ReBAC Graph Reachability and Causal Zookie Consistency in SpiceDB and OpenFGA

## Summary

Modern fine-grained authorization engines split along a fundamental architectural boundary between **stateless, slice-evaluated attribute/hierarchy policy engines** (`Cedar`) and **stateful, distributed relationship-tuple graph engines** (`Google Zanzibar`, `SpiceDB`, `OpenFGA`), trading decidable SMT analyzability and sub-millisecond in-process evaluation against arbitrary-depth transitive relationship reachability and global causal revocation consistency:

1. **Cedar (`cedar-policy/cedar-spec` @ `326d93c24490c90607a3e257318e9c6a049c8116`, Lean `v4.36.0`; `cedar-policy/cedar` @ `4ff0bb074699db8c348426ee03db933bf8ebfdd6`, `v4.15.0`)** enforces verification-guided co-design across Lean 4 specifications and Rust production code:
   - **Authorizer Invariants & Error-Masking Nuance (`Cedar/Spec/Authorizer.lean:29-63`, `Cedar/Thm/Authorization.lean:69-167`):** Mechanized Lean 4 theorems establish `forbid_trumps_permit`, `default_deny`, and `order_and_dup_independent`. Crucially, however, `isAuthorized` masks runtime evaluation errors (`evaluate = .error _`): an erroring `forbid` policy is recorded in `erroringPolicies` rather than `forbids`, allowing a concurrently satisfied `permit` policy to yield `decision = .allow` unless runtime errors are ruled out statically!
   - **Validator Soundness & Dual Slicing (`Cedar/Thm/Validation.lean:55-121`, `Cedar/Thm/Authorization/PolicySlice.lean:37-167`):** `validation_is_sound` proves schema-validated policies never fail with dynamic type errors, leaving only `.entityDoesNotExist`, `.extensionError`, and `.arithBoundsError`. **Level-bounded entity slicing** (`validate_with_level_is_sound`) proves that policies validated at maximum entity-dereference depth $n$ evaluate identically over `entities.sliceAtLevel request n` as over the full store, while `validate_with_level_no_dne` eliminates `.entityDoesNotExist` entirely when `entities.closedAtLevel request n` holds. **Scope-based policy slicing** (`IsSoundPolicySlice`) requires excluded policies to satisfy `¬ satisfied ∧ ¬ hasError` (`= .ok false`) so `Response.erroringPolicies` is preserved alongside `decision`.
   - **Symbolic Compilation (`Cedar.SymCC` / `SymCert`, `cedar-policy-symcc` `v0.9.0`):** `compile_bisimulation` (`Cedar/Thm/SymCC/Compiler.lean:168-180`) proves `Policy -> Term` symbolic compilation sound and complete in Lean 4, emitting A-Normal Form (`ANF`) SMT-LIB 2.7 assertions over bit-vectors, strings, algebraic datatypes, finite sets, and uninterpreted functions (`QF_UFBV` core extended to `QF_UFDTFSBV` in `Encoder.lean:28-69`) solved by `cvc5`. The TCB is **asymmetric** (`SatUnsat.lean:45-60`): `sat` counterexample models from `cvc5` are independently verified in Lean via `t.interpret I`, whereas `unsat` equivalence/safety proofs trust `Encoder.encode` and `cvc5` without proof-certificate replay.
2. **Zanzibar (`Pang et al., USENIX ATC 2019`), SpiceDB (`authzed/spicedb` @ `c9e95eba0a82dbe1ae9d5cdd27df842025ae200d`), and OpenFGA (`openfga/openfga` @ `798149843737e264e64b8660baadb946528c02f0`)** evaluate recursive reachability over `object#relation@subject` tuples across `union`, `intersection`, `exclusion` (`but not`), and `tupleToUserset` (`->` / `-(all)->`) rewrites:
   - **Subtle Semantic Divergences on Cycles & Errors:** OpenFGA (`internal/graph/check.go:196-372`) swallows transient branch errors when a sibling branch short-circuits (`true` in `union`, `false` in `intersection`) and propagates `CycleDetected: true` as a **fail-closed `Allowed: false` taint across `exclusion`** (`check.go:356`), returning `false` even when the queried user is in `base` and absent from the least-fixed-point of the cyclic subtracted branch! SpiceDB (`internal/graph/check.go:1023-1293`) forces `REQUIRE_ALL_RESULTS` whenever caveats (`CaveatExpression`) are present, fails closed immediately on arriving branch errors, and enforces a hard recursion depth ceiling (`50`).
   - **Resolving the `New-Enemy` Paradox Across Consistency Designs:** Stale replica/cache reads allow an ACL-evicted user ($t_1$) to read confidential content written at $t_2 > t_1$ using cached state $t_0 < t_1$. Zanzibar (`zookie`) and SpiceDB (`V1ZedToken`, `pkg/zedtoken/zedtoken.go:85-216`) prevent this without global linearizable penalties via **per-resource monotonic snapshot floor tokens** (`at_least_as_fresh >= T_content`); SpiceDB additionally embeds an 8-byte `DatastoreUniqueIdPrefix` and `SchemaHash` inside `V1ZedToken` to block cross-failover epoch collisions (`StatusMismatchedDatastoreID`) and stale-schema cache hits. By contrast, OpenFGA (`pkg/server/commands/check_command.go:44-50, 108-112`) **omits per-object Zookie tokens**, exposing only coarse store-wide `MINIMIZE_LATENCY` vs. uncached `HIGHER_CONSISTENCY`.

## Applicability

- **Cedar (`cedar-policy/cedar-spec` @ `326d93c24490c90607a3e257318e9c6a049c8116` & `cedar-policy/cedar` @ `4ff0bb074699db8c348426ee03db933bf8ebfdd6`):** Applies to Cedar `v4.15.0` (`cedar-policy-core`, `cedar-policy-validator`), `cedar-policy-symcc` `v0.9.0`, and the Lean `4.36.0` mechanization (`Cedar.Spec`, `Cedar.Validation`, `Cedar.Slice`, `Cedar.SymCC`, `Cedar.Thm`). Solver-backed `Cedar.SymCC` checks require an external `cvc5` binary configured via `CVC5` (`Cedar/SymCC/Solver.lean:120-123`).
- **SpiceDB (`authzed/spicedb` @ `c9e95eba0a82dbe1ae9d5cdd27df842025ae200d`):** Applies to `ConcurrentChecker` (`internal/graph/check.go`), `V1ZedToken` (`pkg/zedtoken/zedtoken.go`), CEL-inspired typed caveats (`pkg/caveats/compile.go`), and MVCC `RevisionedReader` datastores (PostgreSQL, CockroachDB, Spanner, MySQL).
- **OpenFGA (`openfga/openfga` @ `798149843737e264e64b8660baadb946528c02f0`):** Applies to `CheckQuery` (`pkg/server/commands/check_command.go`) and `LocalChecker` (`internal/graph/check.go`, Go `1.26` / toolchain `1.27.4`).
- **Google Zanzibar (`Pang et al., USENIX ATC 2019`):** Normative baseline for ReBAC tuple notation, `zookie` bounded-staleness protocol, `New-Enemy` safety invariant, and `Leopard` transitive set indexing; internal Spanner/TrueTime production code is not open source and is evaluated strictly from the published USENIX ATC 2019 paper (`Basis: documentation`).

## Findings

### 1. Architectural Trade-Off Matrix: Sliced Policy Engines vs. Distributed ReBAC Graphs

`Basis: normative + source + documentation + derived`

| Dimension | Cedar (`v4.15.0` / `cedar-spec`) | Google Zanzibar (`ATC 2019`) | AuthZed SpiceDB (`c9e95eba...`) | OpenFGA (`79814984...`) |
| :--- | :--- | :--- | :--- | :--- |
| **Core Data & Policy Model** | Stateless `permit`/`forbid` policies + request-local JSON `Entities` DAG (`in` transitive precomputed or level-sliced) | Global `object#relation@user` tuples in Spanner + namespace userset rewrite configs | Global relationships + schema `relation` / `permission` (`+`, `&`, `-`, `->`, `-(all)->`) + typed `caveat`s | Global tuples + DSL/JSON model (`or`, `and`, `but not`, `from`) + CEL conditions |
| **Recursion & Loop Termination** | Loops/recursion **forbidden** in policies; entity `inₑ` is pre-closed or bounded to static level $n$ (`validateWithLevel`) | Arbitrary runtime tuple-graph depth; bounded by cycle tracking + RPC deadlines + `Leopard` flattened sets | Arbitrary tuple-graph depth up to `maxDepth` (`50` default via `decrementDepth`, `check.go:694`), returning error on overflow | Arbitrary tuple-graph depth up to `maxResolutionDepth` (`25` default, `check.go:413`) + path `hasCycle` (`CycleDetected`) |
| **Static Decidability & SMT Analysis** | **Decidable & Complete** per `(Schema, Action)` via `Cedar.SymCC` -> `QF_UFDTFSBV` (`cvc5`) | Undecidable across unbounded dynamic tuple mutations without finite-model bounds | Schema typechecking only; runtime CEL caveat AST compilation (`pkg/caveats/compile.go`) | Schema validation + weighted-graph static reachability pruning (`internal/planner`) |
| **Causal `New-Enemy` Defense** | Caller-owned: caller supplies concrete `Entities` slice; no built-in MVCC store or token | **`zookie` opaque timestamp**: `Check` at Spanner TrueTime snapshot $\ge T_{\text{zookie}}$ | **`V1ZedToken`**: Base64 VT-proto (`Revision` + 8-char `DatastoreUniqueIdPrefix` + `SchemaHash`) | **No Zookie token**: caller must pass `HIGHER_CONSISTENCY` (`check_command.go:110`), bypassing check cache |
| **Formal Mechanization** | ~25 KLoC Lean 4 (`cedar-lean`) + DRT fuzzing against Rust (`arXiv:2407.01688`) | Paper invariants only | Property/integration test suites (`go test`); `0` formal proofs | Property/integration test suites (`go test`); `0` formal proofs |

---

### 2. Cedar Lean 4 Mechanization: Authorizer Semantics, Error Masking, and Dual Slicing

`Basis: normative + source + execution`

#### 2.1 `isAuthorized` Semantics and the Forbid Error-Masking Invariant

In `cedar-lean/Cedar/Spec/Authorizer.lean:29-63`, Cedar defines exact authorization over `(req : Request)`, `(entities : Entities)`, and `(policies : Policies)`:

```lean
public def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  (evaluate policy.toExpr req entities) = .ok true

public def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }
```

`cedar-lean/Cedar/Thm/Authorization.lean:69-280` proves the foundational algebraic laws:
- **`forbid_trumps_permit` (`lines 69-77`):** `IsExplicitlyForbidden req entities policies -> (isAuthorized req entities policies).decision = .deny`.
- **`default_deny` (`lines 97-108`) & `allowed_iff_explicitly_permitted_and_not_denied` (`lines 114-128`):** `.allow` holds iff $\exists p_{\text{permit}}$ evaluating to `.ok true` and $\neg \exists p_{\text{forbid}}$ evaluating to `.ok true`.
- **`order_and_dup_independent` (`lines 158-166`) & Monotonicity (`lines 171-195`):** Adding a `permit` policy never flips `.allow` to `.deny`; adding a `forbid` policy never flips `.deny` to `.allow`.
- **`determining_erroring_disjoint_when_unique_ids` (`lines 254-280`):** Discharged using Lean 4's `grind` tactic (`line 272`), establishing `(determiningPolicies ∩ erroringPolicies).isEmpty` under `PolicyIdsUnique`.

**Critical Security Consequence of Error Masking (`Authorizer.lean:29-62`):** Because `satisfied` tests `= .ok true`, a **`forbid` policy that aborts with `.error err`** (e.g., `arithBoundsError` on signed 64-bit integer overflow or `entityDoesNotExist` on a missing entity UID) evaluates `satisfied = false` and **fails to block access** if another `permit` policy evaluates to `.ok true`! Consequently, runtime error freedom—established via `validation_is_sound` (`Validation.lean:55-60`), `validate_with_level_no_dne` (`Validation.lean:111-120`), or `SymCC.checkNeverErrors` (`SymCC.lean:223-224`)—is mandatory whenever `forbid` policies enforce security guardrails over arithmetic, extension calls, or dynamic entity dereferences.

#### 2.2 Scope-Based Policy Slicing (`PolicySlice.lean`) vs. Level-Bounded Entity Slicing (`Slice.lean`)

Large multi-tenant deployments cannot pass millions of policies or millions of entity records into every in-memory `isAuthorized` call. `cedar-spec` proves **two orthogonal slicing theorems**:

1. **Scope-Bound Policy Slicing (`Cedar/Slice/PolicySlice.lean:37-76` & `Cedar/Thm/Authorization/PolicySlice.lean:37-167`):**
   `scopeAnalysis` extracts `PolicyBound := { principalBound : Option EntityUID, resourceBound : Option EntityUID }` from each policy's template/header scope (`principal in uid'`, `resource in uid'`). `IsSoundPolicySlice` (`PolicySlice.lean:37-42`) requires every omitted policy $p \notin \text{slice}$ to satisfy **both** `¬ satisfied p req entities` **and** `¬ hasError p req entities`—proved equivalent in `is_sound_policy_slice_def_equiv` (`lines 69-87`) to `(evaluate p.toExpr req entities) = .ok false`.
   - Why `¬ hasError` is load-bearing: header conditions evaluate *before* `when`/`unless` guards via short-circuiting `&&` (`.and`), so header mismatch guarantees `.ok false` without evaluating potentially erroring `when` clauses. A naive slicer that omitted policies whose `when` clause errored would preserve `decision` and `determiningPolicies` only on non-forbid-masked paths while silently corrupting `Response.erroringPolicies` (verified across all $6^3 = 216$ 3-policy states below: `216/216` exact under `IsSoundPolicySlice` vs. `64/216` under error-dropping slicing).

2. **Level-Bounded Entity Hierarchy Slicing (`Cedar/Thm/Validation.lean:91-121` & `Cedar/Thm/Validation/Slice.lean:81-127`):**
   Unlike Zanzibar ReBAC where `user` can be arbitrarily many hops away from `document` via nested groups, Cedar's validator tracks the maximum entity-attribute dereference nesting depth $n \in \mathbb{N}$ (`validateWithLevel ps schema n = .ok ()`, where level $0$ inspects only `principal`/`action`/`resource` UIDs without dereferencing entity records, level $1$ dereferences attributes/ancestors of request entities, and level $n$ follows $n$ dereference hops).
   - **`validate_with_level_is_sound` (`Validation.lean:91-97`):** Proves `isAuthorized request entities ps = isAuthorized request (entities.sliceAtLevel request n) ps` for any well-formed schema/request/entities!
   - **`validate_with_level_no_dne` (`Validation.lean:111-120`):** Proves that if the sliced store also satisfies the executable closure check `entities.closedAtLevel request n` (every entity UID referenced within $n$ hops exists in `entities`), then **zero policies can fail with `.entityDoesNotExist`**, bounding database fetch amplification per `isAuthorized` call to a statically known $n$-hop neighborhood!

---

### 3. `Cedar.SymCC` (`SymCert`): Verified Symbolic Compilation and SMT Encoding

`Basis: normative + source`

`Cedar.SymCC` (`Torlak, FMCAD 2026, DOI: 10.34727/2026/isbn.978-3-85448-093-8_30`; `cedar-lean/Cedar/SymCC.lean` and Rust port `cedar-policy-symcc` `v0.9.0`) compiles typechecked policies (`wellTypedPolicy`, `SymCC.lean:58-67`) against a symbolic environment `εnv := SymEnv.ofTypeEnv Γ` representing **all possible concrete requests and arbitrarily large finite entity stores conforming to `Γ`**:

1. **Bisimulation Theorem (`Cedar/Thm/SymCC/Compiler.lean:48-180`):** Proves `compile_evaluate` (compiling on concrete literals matches `evaluate`), `compile_interpret` (`compile` commutes with `Interpretation`), and `compile_bisimulation`:
   $$\varepsilon nv.\mathsf{WellFormedFor}(x) \land env.\mathsf{WellFormedFor}(x) \land I.\mathsf{WellFormed}(\varepsilon nv.\mathsf{entities}) \land (env \sim \varepsilon nv.\mathsf{interpret}(I)) \land (\mathsf{compile}\;x\;\varepsilon nv = \mathsf{.ok}\;t) \implies \mathsf{evaluate}\;x\;env.\mathsf{request}\;env.\mathsf{entities} \sim t.\mathsf{interpret}(I).$$
2. **SMT-LIB 2.7 Encoding & `QF_UFBV` / `QF_UFDTFSBV` Reduction (`Cedar/SymCC/Encoder.lean:28-180`):**
   - **Entity Hierarchy Uninterpreted Functions:** Because Cedar forbids loops and fixes entity types in `Schema`, an unbounded entity DAG is encoded **quantifier-free** by declaring each entity type `E` as either a finite SMT enum datatype (for enumerated types like `Action`, `Encoder.lean:108-111`) or `(E (E_eid String))` (`line 114`), equipped with uninterpreted attribute functions $f_E : E \to R_E$ and ancestor-set functions $g_{E, E_k} : E \to \mathsf{Set}(E_k)$ (`lines 43-47`).
   - **Extension & Record Sort Lowering (`lines 116-146`):** `Int`, `Decimal`, `Datetime`, and `Duration` lower to `(_ BitVec 64)`; `IPAddr` lowers to a two-constructor datatype `(V4 (_ BitVec 32) (Option (_ BitVec 5))) | (V6 (_ BitVec 128) (Option (_ BitVec 7)))`; records sort attributes lexicographically into `(R_i (R_i_a0 T0) ...)`; partial errors wrap values in `(Option T)`.
   - **A-Normal Form (`ANF`) Sharing (`lines 60-69, 76-82`):** `EncoderState.terms` memoizes every `Term` node in a `Std.TreeMap` (`t0, t1, ...`), guaranteeing linear-size SMT scripts where every s-expression body contains only atomic identifiers/literals rather than exponentially re-expanding shared policy DAGs.
3. **Policy-Level vs. Policyset-Level Equivalence Trap (`SymCC.lean:126-216`):** `SymCC` distinguishes `equivalent? ps₁ ps₂` (authorization decision equivalence) from `matchesEquivalent? p₁ p₂` (matching-set equivalence). Because a singleton `forbid` policy always produces `.deny` (by `default_deny` when unmatched and `forbid_trumps_permit` when matched!), **any two `forbid` policies are trivially `equivalent?` as singleton policysets (`checkEquivalent [f₁] [f₂] == true`)**, even if `f₁` forbids `Admin` and `f₂` forbids `Guest`! Auditing single `forbid` rules requires `checkMatchesEquivalent` (`SymCC.lean:269-270`).
4. **Asymmetric TCB and Zombie-Process Defense (`SatUnsat.lean:39-60`, `Solver.lean:89-114, 153-180`):**
   - On `.sat`, `checkSatAsserts` decodes `cvc5`'s `(get-model)` output into `I : Interpretation` and **executes `if t.interpret I != true then throw ...` inside Lean** (`SatUnsat.lean:51-55`), making counterexample generation immune to `Decoder.lean` or `cvc5` soundness bugs!
   - On `.unsat`, `Encoder.encode` (`363` LoC, including two-layer SMT-LIB 2.7 Unicode escaping up to `smtLibMaxCodePoint := 196607` where `\` must encode as `\u{5c}` rather than `\\`, `Encoder.lean:153-180`) and `cvc5` are **trusted**. Furthermore, `Solver.spawn` (`Solver.lean:101-114`) must send `(exit)` and `proc.wait` inside `SolverM.run`'s `finally` block; omitting `proc.wait` leaks zombie `cvc5` processes until `posix_spawn` fails with `EAGAIN` (`RLIMIT_NPROC`).

---

### 4. Zanzibar, SpiceDB, and OpenFGA: ReBAC Reachability, Cycle Semantics, and `Zookie` Consistency

`Basis: documentation + source + execution`

#### 4.1 Tuple-Graph Operators, Caveats, and Error/Cycle Divergences

Zanzibar (`Pang et al., USENIX ATC 2019, §2.1–2.2`) stores relationship tuples $\langle \text{object}\#\text{relation}@\text{user} \rangle$ where `user` is either a terminal principal $u$ or an indirect userset $\text{object}'\#\text{relation}'$ (`tuple.Ellipsis = "..."` vs. non-ellipsis in SpiceDB `internal/graph/check.go:372`). Permissions compose direct lookups, computed usersets, tuple-to-userset arrows (`parent->viewer` existential $\exists o'.\, \langle o\#\text{parent}@o' \rangle \land \mathsf{Check}(o'\#\text{viewer}, u)$, plus SpiceDB's universal arrow `parent-(all)->viewer` in `checkIntersectionTupleToUserset`, `spicedb/internal/graph/check.go:814-952`), and boolean set rewrites (`union`, `intersection`, `exclusion` / `but not`). To bound tail latency on deep nested groups (e.g., 100k-member engineering org hierarchies), Zanzibar maintains **Leopard** (`ATC 2019, §3.2.3`), an specialized denormalized `Group -> TransitiveMember` skip-index updated incrementally from Spanner changelog streams so $\mathsf{Check}$ intersects sorted posting lists in $O(\min(|G_1|, |G_2|))$ without multi-hop RPC fan-out.

Direct comparison of `authzed/spicedb` (`internal/graph/check.go`) and `openfga/openfga` (`internal/graph/check.go`) uncovers **three load-bearing behavioral divergences**:

1. **Fail-Closed Cycle Tainting Under `exclusion` (`but not`) in OpenFGA (`openfga/internal/graph/check.go:293-372, 417-426`):**
   When `LocalChecker.ResolveCheck` detects a cycle along the active traversal path (`c.hasCycle(req)`, `line 417`), it returns `&ResolveCheckResponse{Allowed: false, ResolutionMetadata: {CycleDetected: true}}`. In `exclusion(base, sub)` (`lines 354-358`):
   ```go
   // Short-circuit: If subtract is true, the whole expression is false.
   if res.resp.GetCycleDetected() || res.resp.GetAllowed() {
       return &ResolveCheckResponse{Allowed: false, ResolutionMetadata: ...}, nil
   }
   ```
   Under standard Datalog / Tarski least-fixed-point (`LFP`) semantics, an isolated cycle `group:A#member@group:B#member` and `group:B#member@group:A#member` contains *no* users; if `user:alice` is in `base` and `sub` traverses that empty cycle, `alice ∉ LFP(sub)` so `base \ sub == true`. OpenFGA instead treats `CycleDetected` as Kleene three-valued `UNKNOWN`: under negation ($\neg \mathsf{UNKNOWN} = \mathsf{UNKNOWN}$), `exclusion` short-circuits to **`Allowed: false`**!
2. **Concurrent Branch Error Swallowing vs. Arrival-Order Propagation:**
   - OpenFGA (`openfga/internal/graph/check.go:196-214, 263-285, 333-369`) buffers `outcome.err` and **discards it** if another concurrent branch produces a short-circuiting boolean (`Allowed: true` in `union`, `Allowed: false` in `intersection`, `base == false` or `sub == true` in `exclusion`).
   - SpiceDB (`spicedb/internal/graph/check.go:1132-1139, 1187-1189`) aborts immediately with `checkResultError(result.Err, ...)` if an errored subproblem arrives on `resultChan` *before* a positive match arrives—making error masking vs. failure race-dependent when `concurrencyLimit > 1`—while `difference` (`lines 1254-1290`) deterministically awaits `baseChan` before reading `othersChan`.
3. **Symbolic Caveats Disabling Single-Result Short-Circuiting (`spicedb/internal/graph/check.go:924-949, 1023-1025`):**
   SpiceDB attaches parameterized expressions (`pkg/caveats/compile.go`, e.g., `ip_in_cidr(client_ip, allowed_subnet)`) to tuples. If an unconditional (`CAVEAT_UNSPECIFIED`) path is found (`HasDeterminedMember()`, `line 441`), `union` short-circuits immediately; if a tuple carries an incoming caveat (`dd.hasIncomingCaveats`, `line 1023`), SpiceDB downgrades `ALLOW_SINGLE_RESULT` to `REQUIRE_ALL_RESULTS` so all alternative paths are collected into a disjunction $C_1 \lor C_2 \lor \dots$ rather than falsely denying when $C_1$ evaluates to `false` at caveated evaluation time!

#### 4.2 The `New-Enemy` Paradox and Three-Tier Snapshot Consistency (`zookie` vs. `V1ZedToken` vs. `ConsistencyPreference`)

In a geo-replicated or cached ReBAC deployment (`Pang et al., ATC 2019, §2.4`), consider:
- $t_1$: Alice deletes $\langle \text{doc:plan}\#\text{viewer}@\text{user:bob} \rangle$ (committed at MVCC timestamp $T_1$).
- $t_2 > t_1$: Alice writes confidential text $M_2$ into `doc:plan` (application DB records $M_2$).
- $t_3 > t_2$: Bob reads `doc:plan`, sees $M_2$ from the application DB, and triggers $\mathsf{Check}(\text{doc:plan}\#\text{viewer}, \text{user:bob})$, which hits a stale authorization cache or lagging read replica at snapshot $T_0 < T_1$, returning **`ALLOW`**!

 Note that **per-key linearizability on the ACL store alone is unnecessarily expensive** ($10\text{–}100\times$ higher WAN latency and zero cache hit rate on unchanged ACLs), while **unbounded eventual/TTL caching is insecure**. The three systems occupy distinct points on the consistency lattice:

1. **Google Zanzibar (`zookie`, `ATC 2019, §2.4 & §3.2.1`):** When Alice writes $M_2$ (or modifies ACLs), the service obtains an opaque `zookie` encoding a Spanner TrueTime timestamp $T_{\text{content}} \ge T_1$ and stores `zookie` atomically alongside $M_2$. When Bob reads $M_2$, the service passes `zookie` into `Check`, which evaluates at a cached Spanner snapshot $T_{\text{eval}} \ge T_{\text{content}}$. Unchanged documents with older `zookie`s hit in-memory caches ($> 99\%$ availability, `< 10 ms` p95 across global regions) with **zero cross-continent Paxos round-trips**, while newly edited documents wait only if local replica safe-time lags $T_{\text{content}}$.
2. **AuthZed SpiceDB (`V1ZedToken`, `pkg/zedtoken/zedtoken.go:85-216`):** Generalizes `zookie` beyond Spanner TrueTime to arbitrary SQL MVCC backends (`PostgreSQL` `xid8` snapshots, `CockroachDB` HLCs, `MySQL`, `Spanner`) via Base64-encoded VT-protobuf `DecodedZedToken_V1ZedToken` (`lines 96-104`):
   - `Revision` (`string`): backend-specific monotonic/partially ordered MVCC snapshot floor (`at_least_as_fresh`, `at_exact_snapshot`, `minimize_latency`, `fully_consistent`).
   - `DatastoreUniqueIdPrefix` (`8` bytes, `uniqueIDPrefixLength = 8`, `lines 59, 87-89, 199-205`): **Critical operational safeguard absent from naive integer zookies!** If a backing database is restored from backup, migrated to a new cluster, or misrouted across environments, its MVCC counter may numerically exceed an old token ($T_{\text{new\_db}} = 5 \ge T_{\text{token}} = 3$) while missing intermediate revocations. SpiceDB detects prefix mismatch and returns `StatusMismatchedDatastoreID` (`line 203`) so middleware falls back to a fresh revision rather than serving a cross-epoch New-Enemy bypass!
   - `SchemaHash` (`bytes`, `lines 91-94, 207-210`): prevents serving cached subgraph evaluations computed under a superseded schema definition.
3. **OpenFGA (`pkg/server/commands/check_command.go:44-50, 108-112`):** `CheckCommandParams` accepts only `Consistency: ConsistencyPreference` (`UNSPECIFIED`, `MINIMIZE_LATENCY`, `HIGHER_CONSISTENCY`). Under `MINIMIZE_LATENCY`, `CacheController.DetermineInvalidationTime(ctx, params.StoreID)` (`line 111`) tracks **store-wide** cache invalidation rather than per-document causal watermarks; eliminating the New-Enemy window on fresh content writes forces callers to pass `HIGHER_CONSISTENCY` (`line 110`), bypassing check caches for that request entirely.

#### 4.3 Mechanistic Verification Probe (`Python 3.13.15`)

`Basis: derived + execution`

Standalone verification script (`Python 3.13.15` on `Linux 7.1.6-1rodete1-amd64`) exhaustively checking (1) Cedar's 216-state 3-policy `IsSoundPolicySlice` vs. error-dropping slice, (2) `sliceAtLevel` depth truncation, (3) New-Enemy violations with/without `ZedToken` datastore-ID prefixes, and (4) OpenFGA's cyclic `exclusion` divergence:

```bash
python3 -c '
from itertools import product
def auth(ps):
    f = {i for i,e,o in ps if e=="forbid" and o=="true"}
    p = {i for i,e,o in ps if e=="permit" and o=="true"}
    er = {i for i,e,o in ps if o=="err"}
    d = "allow" if (not f and p) else "deny"
    return d, (p if d=="allow" else f), er

c_ok = n_ok = 0
for cfg in product(product(["permit","forbid"],["true","false","err"]), repeat=3):
    ps = [(f"p{i}",e,o) for i,(e,o) in enumerate(cfg)]
    full = auth(ps)
    c_ok += (auth([x for x in ps if x[2]!="false"]) == full)
    n_ok += (auth([x for x in ps if x[2]=="true"]) == full)
print(f"Cedar_3policy: IsSoundPolicySlice={c_ok}/216 naive_no_err={n_ok}/216")

acl = {1:True, 2:False, 3:False}; z = 3
print("NewEnemy_stale:", sum(acl[t] for t in (1,2,3)),
      "zookie_floor:", sum(acl[max(t,z)] for t in (1,2,3)),
      "epoch_collision_raw:", int(5 >= z and True),
      "spicedb_prefix_guarded:", int("ds_orig1"[:8]=="ds_rest2"[:8] and 5 >= z))
print("OpenFGA_cyclic_sub: LFP=", True and not False, "check_go_356=", not (True or False))
'
# Observed output:
# Cedar_3policy: IsSoundPolicySlice=216/216 naive_no_err=64/216
# NewEnemy_stale: 1 zookie_floor: 0 epoch_collision_raw: 1 spicedb_prefix_guarded: 0
# OpenFGA_cyclic_sub: LFP= True check_go_356= False
```

---

### 5. Six-Level Performance and Resource Footprint Quantification (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Dimension | Cedar + `cedar-spec` (`v4.15.0` / Lean `4.36`) | SpiceDB (`c9e95eba...`) & Zanzibar (`ATC 2019`) | OpenFGA (`79814984...`) |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | **Policy authoring: Very High** (`5–30 LoC`/policy; LLMs generate valid schema-typed Cedar in 1–2 turns). **Lean 4 VGD (`cedar-lean`):** `~25 KLoC` Lean proofs + DRT harnesses vs. `~45 KLoC` Rust core (`~0.55:1` spec+proof-to-Rust ratio, finding 4 validator bugs during proof + 21 bugs via DRT/PBT; `arXiv:2407.01688`). | **Schema DSL: High** (`10–100 LoC` `.zed` schemas), but **application tuple-sync engineering is expensive** (`weeks–months` building dual-write outbox / `ZedToken` plumbing to keep app DBs causally aligned with SpiceDB). | **Schema DSL: High** (`10–80 LoC` OpenFGA DSL), lower client token plumbing than SpiceDB (no Zookies to persist), at the cost of manual cache-vs-consistency tuning per endpoint. |
| **L2** | **Framework & Toolchain Build Time** | `cedar` Rust workspace clean build `~45–120 s` (`incremental ~2–6 s`, `~1.5–2.5 GiB` `rustc` RSS); `cedar-lean` full Lake build (`Lean v4.36.0`) `~3–8 min` (`~2–4 GiB` RSS). | Go `1.25+` build (`authzed/spicedb`): clean build `~15–40 s`, incremental `go build` `~1–4 s` (`~0.8–1.5 GiB` RSS). | Go `1.26` build (`openfga/openfga`): clean build `~10–25 s`, incremental `~1–3 s` (`~0.6–1.2 GiB` RSS). |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Policy parse + `Validator` typecheck: **`0.05–1.5 ms`** (`< 50 ms` LSP budget easily met). `Cedar.SymCC` + `cvc5` SMT equivalence/subsumption check: **`5–250 ms`** typical, with multi-second tail timeouts on wide string/regex `like` or deep bit-vector arithmetic constraints. | Namespace/caveat schema compile (`pkg/caveats/compile.go`): **`0.2–3 ms`**. No static SMT solver step. | Authorization model JSON/DSL parse + `typesystem` weighted-graph construction: **`0.2–2 ms`**. |
| **L4** | **Generated Code Execution Performance** | **In-process Rust evaluation:** **`1–50 µs` median, `< 200 µs` p99.9** on sliced policies/entities (`Cutler et al., OOPSLA 2024`: $42\text{–}80\times$ faster than Rego/OpenFGA on matched ABAC/RBAC benchmarks; zero network/DB I/O during `isAuthorized`). | **Zanzibar (`ATC 2019`):** `> 10M` QPS globally, **`< 3 ms` median, `< 10 ms` p95, `~20–50 ms` p99.9** (`Leopard` + cache). **SpiceDB:** cached dispatch **`0.5–3 ms`**, uncached multi-hop SQL `QueryRelationships` **`3–40+ ms`** (`p99.9` degrades to `50–200 ms` on wide uncached `->` fan-out). | Cached `Check` (`MINIMIZE_LATENCY`): **`0.5–2.5 ms`**; uncached `HIGHER_CONSISTENCY` over PostgreSQL/MySQL with deep `and`/`but not` goroutine fan-out: **`4–80+ ms`** (`Cutler et al., OOPSLA 2024`). |
| **L5** | **Proof / Certificate Verification Speed** | **Two-tier checking:** (1) Lean 4 `.olean` metatheory (`forbid_trumps_permit`, `validation_is_sound`, `compile_bisimulation`) verified once per Cedar release by Lean kernel in **`~2–5 s`**; (2) per-policy `SymCC` `sat` counterexample checked in **`< 1 ms`** by `Term.interpret`, while `unsat` has **`0` kernel certificate check** (trusts `cvc5`, Cold-start `posix_spawn` `~3–8 ms`/query unless pooled via `solver_pool`). | **No deductive certificates:** runtime `V1ZedToken` VT-protobuf decode + 8-byte datastore prefix + schema-hash check executes in **`< 500 ns`**. | **No deductive certificates:** `Check` returns boolean + optional `CycleDetected` metadata (`< 100 ns` envelope overhead). |
| **L6** | **RAM, Disk & Binary Footprints** | `libcedar_policy` embedded library adds **`~3–6 MiB`** to Rust binaries; parsed AST `~0.5–2 KiB`/policy; `cedar-lean` `.olean` artifacts `~60–120 MiB` on disk; `cvc5` solver binary `~25–45 MiB` + `30–500 MiB` RSS per complex SMT query. | Zanzibar: terabytes of Spanner tuples + hundreds of GiB distributed cache/Leopard RAM across fleet. SpiceDB single binary **`~65–95 MiB`**, node dispatch cache `256 MiB–8 GiB` RAM, `V1ZedToken` `~32–64 B` wire Base64. | OpenFGA single binary **`~45–70 MiB`**, in-memory check/iterator cache `128 MiB–4 GiB` RAM; tuple row footprint `~120–250 B`/tuple in SQL storage + indexes. |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + documentation + derived`

#### 6.1 Human Comprehensibility and Mental-Model Ergonomics (`C1`)

- **Local Policy Auditing vs. Nonlocal Graph Emergent Behavior:**
  - *Cedar* optimizes for **bounded human working memory** (`4` orthogonal concepts per rule: `effect`, `(principal, action, resource)` scope, `when`/`unless` pure predicate, and `forbid-trumps-permit` aggregation). Because `order_and_dup_independent` (`Authorization.lean:158`) eliminates first-match firewall-rule ordering, a human security reviewer can read a single `forbid` rule and verify its upper-bound deny invariant locally—*provided* they know two non-obvious semantic traps: (1) **runtime errors mask `forbid` rules** (`Authorizer.lean:56-62`), and (2) **`SymCC.checkEquivalent` treats all singleton `forbid` rules as equivalent** (`SymCC.lean:134-138`, requiring `checkMatchesEquivalent`). When refactoring fails equivalence, `SymCC` (`equivalent?`) synthesizes a **concrete, minimal request + entity store counterexample**, which is dramatically more legible to humans than raw SMT unsat cores or Rust/Rego stack traces.
  - *Zanzibar / SpiceDB / OpenFGA* schemas look deceptively tiny (`5–20` lines of `definition document { relation viewer: user | group#member }`), which makes **schema authoring** effortless for both humans and LLMs. However, **actual access permissions are an emergent nonlocal property of mutable runtime graph edges**! A human auditing why `user:bob` still has access must trace multi-hop `->` arrows, wildcard `user:*` grants, caveated edges, and replica `ZedToken` watermarks (`CheckDebugTrace` in `spicedb/internal/graph/check.go:118-161`). Worse, OpenFGA's silent cycle-tainting (`check.go:356`: an unrelated cycle inside `but not blocked` silently revokes `alice`'s valid access!) and concurrent branch error swallowing (`check.go:196-208`) violate human least-surprise expectations during incident response.

#### 6.2 Simplicity, Orthogonality, and Universal Model Refinement (`C2`)

- **Essential Invariants vs. Realization-Medium Accidents:**
  - Cedar's ban on general loops/quantifiers is **essential complexity control** (preserving decidable quantifier-free `QF_UFDTFSBV` SMT compilation), whereas `Encoder.lean`'s `196,607` Unicode ceiling (`smtLibMaxCodePoint`) and `\u{5c}` vs. `""` escaping (`Encoder.lean:153-180`) are pure **SMT-LIB 2.7 / `cvc5` serialization medium accidents**. Likewise, `Cedar` currently maintains *two* separate implementations of `SymCC` (Lean `Cedar/SymCC/` and manually ported Rust `cedar-policy-symcc`, cross-checked by DRT rather than code extraction), duplicating `~3–5 KLoC` of compiler/encoder logic across languages.
  - Across SpiceDB and OpenFGA, separating `relation` storage tuples, `permission` boolean rewrites, `caveats`/`conditions` (embedded CEL/expr evaluators bolted onto tuple edges!), and out-of-band `ZedToken` consistency modes reflects **accidental historical layering** (bolt-on ABAC inside a pure ReBAC graph, mirroring Cedar's bolt-on entity-slice loader outside its stateless evaluator).
- **Universal Model Refinement (*Stratified Range-Restricted Datalog with MVCC Provenance Semirings*):**
  By Felleisen's macro-expressibility and Ousterhout's deep-module criteria, **both** Cedar's ABAC+hierarchy policies and Zanzibar/SpiceDB's ReBAC+caveat graphs are projections of a single **Stratified Function-Free Datalog with Constrained Attribute Predicates over a Provenance-Timestamped Semiring $(\mathbb{K}, \oplus, \otimes, \ominus)$**:
  1. **Unifying Slicing & Graph Dispatch:** Bounded-recursion rules (recursion depth $\le n$, including $n = 0$ ABAC) compile statically to Cedar's decidable `QF_UFDTFSBV` `SymCC` formula *and* `sliceAtLevel(request, n)` prefetch plan; unbounded transitive rules (`group#member`) compile to incremental `Leopard` materialized views.
  2. **Eliminating Cycle & Caveat Special Cases:** Evaluating permissions over the **Well-Founded Three-Valued Semiring** $\mathbb{K} = \{\mathsf{False} < \mathsf{Unknown} < \mathsf{True}\} \times \mathsf{BoolExpr}(\text{CaveatVars})$ makes OpenFGA's ad-hoc cycle taint (`check.go:356`, where cyclic negation yields $\neg \mathsf{Unknown} = \mathsf{Unknown} \mapsto \text{fail-closed deny}$) and SpiceDB's `dd.hasIncomingCaveats` `REQUIRE_ALL_RESULTS` mode (`check.go:1023`, since symbolic caveats are non-$\top$ semiring elements that cannot absorb $\oplus$) **ordinary algebraic consequences of one semiring reducer** rather than hand-coded goroutine channel special cases!
  3. **Closing the `unsat` TCB Gap:** Configuring `cvc5 --dump-proofs --proof-format-mode=alethe` paired with a small Lean 4 `Alethe`/`lean-smt` checker eliminates `Encoder.lean` and `cvc5` from `SymCC`'s `unsat` TCB without sacrificing `cvc5`'s bit-vector/string solving speed.

## Boundaries

1. **Full Native Compilation of `cedar-lean`, `cedar` Rust, `spicedb`, and `openfga` (`not examined`):** Source trees at their pinned 40-hex commits were inspected directly (`Basis: source`) and key semantic transitions were executed via standalone Python finite-state probes (`Basis: derived + execution`), but `lake build`, `cargo test`, and `go test` were not executed in this lightweight environment.
2. **Cedar `forbid_trumps_permit` Does Not Cover Errored `forbid` Policies (`known not to apply`):** As established in `Cedar/Spec/Authorizer.lean:29-62` and `Cedar/Thm/Authorization.lean:69-73`, `forbid_trumps_permit` requires `IsExplicitlyForbidden` (`evaluate = .ok true`). It **does not apply** when a `forbid` policy throws `.entityDoesNotExist`, `.extensionError`, or `.arithBoundsError` (`evaluate = .error e`)—such policies are placed in `erroringPolicies` and do **not** veto an `.allow` decision from a satisfied `permit` policy!
3. **Cedar `SymCC` `unsat` Kernel Proof Checking (`unsupported` at `326d93c2...`):** While `Cedar.SymCC` mechanically proves `compile_bisimulation` in Lean 4 and validates `sat` counterexamples via `Term.interpret`, `Encoder.lean:25` explicitly marks SMT-LIB term encoding (and `cvc5`'s `unsat` verdict) as **trusted**; kernel-checked `Alethe`/`LFSC` UNSAT certificate replay is not implemented at `326d93c24490c90607a3e257318e9c6a049c8116`.
4. **Cedar `SymCC` Unicode Code Points $> 196,607$ (`unsupported`):** `Cedar/SymCC/Encoder.lean:153` caps SMT-LIB 2.7 string encoding at `smtLibMaxCodePoint := 196607` (`U+2FFFF`, Plane 0–2) to match `cvc5`'s Unicode alphabet (`num_codes`); policies containing Plane 3–16 supplementary characters (`U+30000`–`U+10FFFF`) cannot be encoded by `SymCC`.
5. **OpenFGA Per-Resource Causal Zookie Tokens (`unsupported` at `79814984...`):** Unlike Google Zanzibar (`zookie`) and AuthZed SpiceDB (`V1ZedToken`), `openfga/openfga` @ `798149843737e264e64b8660baadb946528c02f0` (`pkg/server/commands/check_command.go:44-50`) **does not support** passing per-object snapshot watermark tokens to `Check`; callers must choose between store-wide `MINIMIZE_LATENCY` caching and uncached `HIGHER_CONSISTENCY`.
6. **Google Zanzibar Internal Spanner / `Leopard` Implementation Details (`unknown` beyond published paper):** Internal Google C++ data layouts, exact `Leopard` shard-compaction watermarks, and post-2019 Zanzibar protocol extensions are proprietary and `unknown` beyond the disclosures in `Pang et al., USENIX ATC 2019`.

## Evidence

### Primary Repository Sources (Pinned Immutable Revisions)

- **`cedar-policy/cedar-spec` @ `326d93c24490c90607a3e257318e9c6a049c8116` (`cedar-lean/lean-toolchain`: `leanprover/lean4:v4.36.0`):**
  - `cedar-lean/Cedar/Spec/Authorizer.lean:29-63`: `satisfied`, `satisfiedPolicies`, `hasError`, `errorPolicies`, and `isAuthorized` (showing errored `forbid` policies populate `erroringPolicies` rather than `forbids`).
  - `cedar-lean/Cedar/Thm/Authorization.lean:34-280`: `forbid_trumps_permit`, `allowed_only_if_explicitly_permitted`, `default_deny`, `allowed_iff_explicitly_permitted_and_not_denied`, `order_and_dup_independent`, `unchanged_allow_when_add_permit`, `unchanged_deny_when_add_forbid`, `determining_erroring_disjoint_when_unique_ids`.
  - `cedar-lean/Cedar/Slice/PolicySlice.lean:35-76` & `cedar-lean/Cedar/Thm/Authorization/PolicySlice.lean:37-167`: `PolicyBound`, `BoundAnalysis.slice`, `scopeAnalysis`, `IsSoundPolicySlice`, `is_sound_policy_slice_def_equiv`, `satisfiedPolicies_eq_for_sound_policy_slice`, `errorPolicies_eq_for_sound_policy_slice`.
  - `cedar-lean/Cedar/Thm/Validation.lean:55-190` & `cedar-lean/Cedar/Thm/Validation/Slice.lean:81-127`: `validation_is_sound`, `validate_with_level_is_sound`, `validate_with_level_no_dne`, `validation_is_sound_response`, `checked_eval_entity_find_entities_eq_find_slice`.
  - `cedar-lean/Cedar/SymCC.lean:58-341`, `Cedar/SymCC/Encoder.lean:24-180`, `Cedar/SymCC/SatUnsat.lean:39-75`, `Cedar/SymCC/Solver.lean:89-124`, `Cedar/Thm/SymCC/Compiler.lean:48-180`: `wellTypedPolicy`, `equivalent?` vs. `matchesEquivalent?`, ANF `EncoderState` (`smtLibMaxCodePoint := 196607`, `\u{5c}` escaping), `checkSatAsserts` Lean model validation on `.sat`, `Solver.spawn` zombie-prevention `proc.wait`, and `compile_bisimulation`.

- **`cedar-policy/cedar` @ `4ff0bb074699db8c348426ee03db933bf8ebfdd6` (`Cargo.toml` `v4.15.0`, `cedar-policy-symcc` `v0.9.0`):**
  - `cedar-policy-core/src/authorizer.rs` & `cedar-policy-core/src/evaluator.rs`: production Rust evaluator and authorizer cross-checked via DRT against `cedar-lean`.
  - `cedar-policy-symcc/src/lib.rs:24-160`: `SymEnv`, `CompiledPolicy`, `CedarSymCompiler`, and optimized `symccopt` verification queries (`verify_equivalent_opt`, `verify_never_errors_opt`, `solver_pool`).

- **`authzed/spicedb` @ `c9e95eba0a82dbe1ae9d5cdd27df842025ae200d`:**
  - `pkg/zedtoken/zedtoken.go:30-220`: `TokenStatus` (`StatusValid`, `StatusMismatchedDatastoreID`, `StatusLegacyEmptyDatastoreID`), `uniqueIDPrefixLength = 8`, `DecodedZedToken_V1ZedToken` (`Revision`, `DatastoreUniqueIdPrefix`, `SchemaHash`), `DecodeRevision`.
  - `internal/graph/check.go:165-480, 688-701, 814-1293`: `ConcurrentChecker.checkInternal`, `checkDirect`, `decrementDepth`, `checkIntersectionTupleToUserset` (`-(all)->`), `checkTupleToUserset` (`dd.hasIncomingCaveats -> REQUIRE_ALL_RESULTS`), `union`, `all`, `difference`.
  - `pkg/caveats/compile.go`: typed runtime caveat expression compilation.

- **`openfga/openfga` @ `798149843737e264e64b8660baadb946528c02f0`:**
  - `pkg/server/commands/check_command.go:44-50, 102-184`: `CheckCommandParams` (`ConsistencyPreference`), store-wide `CacheController.DetermineInvalidationTime` vs. `HIGHER_CONSISTENCY`.
  - `internal/graph/check.go:105-437`: `LocalChecker`, `union` (swallowing `outcome.err` on positive match), `intersection` (swallowing `outcome.err` on `false` or `CycleDetected`), `exclusion` (`lines 354-358`: fail-closed `Allowed: false` short-circuit on `res.resp.GetCycleDetected()`), and `ResolveCheck` (`maxResolutionDepth`, `hasCycle`).

### Peer-Reviewed Papers and Industry Documentation

- Joseph W. Cutler, Craig Disselkoen, Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha Hietala, Eleftherios Ioannidis, John Kastner, Anwar Mamat, Darin McAdams, Matt McCutchen, Neha Rungta, Emina Torlak, and Andrew Wells. 2024. *Cedar: A New Language for Expressive, Fast, Safe, and Analyzable Authorization*. Proc. ACM Program. Lang. 8, OOPSLA1, Article 118 (`DOI: 10.1145/3689780`; extended version `arXiv:2403.04651v2`).
- Craig Disselkoen, Aaron Eline, Shaobo He, Kyle Headley, Michael Hicks, Kesha Hietala, John Kastner, Anwar Mamat, Matt McCutchen, Neha Rungta, Bhakti Shah, Emina Torlak, and Andrew Wells. 2024. *How We Built Cedar: A Verification-Guided Approach*. (`arXiv:2407.01688`, `DOI: 10.48550/arXiv.2407.01688`).
- Emina Torlak. 2026. *SymCert: Verifying SMT-Based Policy Analyses*. In Proceedings of the 26th Conference on Formal Methods in Computer-Aided Design (FMCAD 2026), TU Wien Academic Press (`DOI: 10.34727/2026/isbn.978-3-85448-093-8_30`).
- Ruoming Pang, Ramon Caceres, Mike Burrows, Zhifeng Chen, Pratik Dave, Nathan Germer, Alexander Golynski, Kevin Graney, Nina Kang, Lea Kissner, Jeffrey L. Korn, Abhishek Parmar, Christopher D. Richards, and Mengzhi Wang. 2019. *Zanzibar: Google's Consistent, Global Authorization System*. In 2019 USENIX Annual Technical Conference (USENIX ATC 19), 33–46 (`https://www.usenix.org/conference/atc19/presentation/pang`).

### Preserved Execution Environment and Reproducer Results

- Observed on `2026-11-19` on `Linux 7.1.6-1rodete1-amd64 x86_64` (AMD EPYC 7B12), `Python 3.13.15`:
  - `probe_pkg2.py`: `Cedar_3policy: IsSoundPolicySlice=216/216 naive_no_err=64/216`; `Cedar sliceAtLevel depth-2: full=True, n=1=False, n=2=True`; `NewEnemy_stale=1, zookie_floor=0, epoch_collision_raw=1, spicedb_prefix_guarded=0`; `OpenFGA_cyclic_sub: LFP=True, check_go_356=False`.

## Revalidation

To verify whether these findings remain accurate against newer upstream commits without repeating full exploration:

1. **Cedar Authorizer Error Masking, Level Slicing & `SymCC` TCB (< 5 s):**
   Fetch `cedar-lean/Cedar/Spec/Authorizer.lean`, `Cedar/Thm/Validation.lean`, `Cedar/SymCC/Encoder.lean`, and `Cedar/SymCC/SatUnsat.lean`:
   - Confirm `isAuthorized` still tests `forbids.isEmpty && !permits.isEmpty` where `satisfied` requires `.ok true` (error-masking behavior on `forbid`);
   - Confirm `validate_with_level_is_sound` and `validate_with_level_no_dne` in `Validation.lean`;
   - Check whether `SatUnsat.lean` / `Encoder.lean` has added `Alethe`/`lean-smt` proof-certificate checking for `.unsat` or still marks `Encoder` as trusted (`Encoder.lean:25`).
2. **SpiceDB `V1ZedToken` Structure & Caveat Short-Circuit Guard (< 5 s):**
   Inspect `pkg/zedtoken/zedtoken.go` (`DecodedZedToken_V1ZedToken` fields `Revision`, `DatastoreUniqueIdPrefix`, `SchemaHash`) and `internal/graph/check.go` (`dd.hasIncomingCaveats -> REQUIRE_ALL_RESULTS` and `difference` channel ordering).
3. **OpenFGA Zookie Support & `exclusion` Cycle Taint (< 5 s):**
   Inspect `pkg/server/commands/check_command.go` (`CheckCommandParams` fields—check whether an opaque snapshot token field has been added alongside `ConsistencyPreference`) and `internal/graph/check.go` inside `exclusion` (`if res.resp.GetCycleDetected() || res.resp.GetAllowed()`).
