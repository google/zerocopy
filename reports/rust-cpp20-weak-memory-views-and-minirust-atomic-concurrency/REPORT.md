# Rust and C++20 Weak-Memory Message-Passing Contracts, MiniRust Concurrency Boundaries, and Operational Prefix Coverage in Lean 4.34.1

## Summary

Rust's `core::sync::atomic` module adopts the C++20 atomic memory model (linking the N4868 draft rendering of `intro.races`) while translating C++ object-level access rules to byte-span accesses and omitting `memory_order_consume`. At the same time, MiniRust at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` models `Atomicity::Atomic` vs. `Atomicity::None` for data-race filtering in `ConcurrentMemory` (`spec/mem/concurrent.md`) and delegates `load`/`store` to the underlying sequential memory without `Release`/`Acquire`/`Relaxed` ordering parameters (`spec/mem/interface.md:162-167`, `spec/lang/step/intrinsics.md:430-490`). This report documents a source audit of the pinned N4868 (`1f468a67c67143625d7946cdc4cfc7f7730d9160`), `core::sync::atomic` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), and MiniRust (`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) specifications, together with five machine-checked Lean 4.34.1 modules (`AtomicMessagePassing`, `AtomicMessagePassingControls`, `AtomicPrefixExecution`, `AtomicPrefixRules`, and `AtomicPrefixCoverage`, totaling 113 `#print axioms` audits across target modules) that formalize a six-event atomic message-passing fragment, its coupling with `MiniRustReference` raw storage validity checks, and its operational prefix semantics.

Key findings:

1. **Pinned N4868 and Rust `core::sync::atomic` message-passing rules:** Under N4868 `intro.races` (`basic.tex:5890-6229`) and `atomics.order` (`atomics.tex:388-562`), a release store $F$ (`flag.store(1, Release)`) observed by an acquire load $A$ (`flag.load(Acquire) == 1`) establishes $F \xrightarrow{\text{sw}} A$; combined with intra-thread sequencing $D \xrightarrow{\text{sb}} F$ and $A \xrightarrow{\text{sb}} B$, transitive happens-before ($D \xrightarrow{\text{hb}} B$) and write-read coherence (`intro.races` §18) force the relaxed payload load $B$ (`data.load(Relaxed)`) to observe $D$'s value `1` rather than initial `0`. When $F$ and $A$ are changed to `Relaxed`, no synchronizes-with edge arises, and the stale outcome `(1,0)` ($A \leftarrow F$, $B \leftarrow I_{\text{data}}$) satisfies the atomic read-source rule (§14), happens-before acyclicity (§10), per-location modification order (§4), and all four coherence rules (§§15–18). Both communication locations must be atomic so that the unordered relaxed payload accesses do not form a non-atomic data race (§21, `atomic.rs:25-58`).
2. **MiniRust `@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` atomic boundary:** `spec/mem/concurrent.md:14-21` defines `Atomicity::Atomic` (documented as sequentially consistent) and `Atomicity::None`, without `Release`, `Acquire`, or `Relaxed` variants. `ConcurrentMemory::store` and `load` (`concurrent.md:63-86`) record an `Access` and delegate to `self.memory.store`/`load` without an ordering or read-from supplier parameter; `spec/mem/interface.md:162-167` explicitly identifies `Option<Ordering>` and thread-ID parameters on `Memory` methods as future concurrency extensions, and `AtomicStore`/`AtomicLoad` (`spec/lang/step/intrinsics.md:430-490`) pass `Atomicity::Atomic` without reading an ordering operand. However, the header comment at `concurrent.md:3-4` ("Atomicity is currently ignored") requires qualification: `Access.races` (`concurrent.md:164-174`) actively exempts pairs of `Atomic` accesses, and `check_data_races` (`concurrent.md:134-149`) already accepts a current thread ID and prior synchronized-thread set.
3. **Candidate classifier, latest-value exclusion, and storage-validity independence (`AtomicMessagePassing`, `AtomicMessagePassingControls`):**
   - `ra_flag_one_data_one` and `ra_observed_values` prove that every Release/Acquire candidate satisfying `Shape` and `SelectedRules` with `flagValue rf = 1` returns `(1,1)` (`ra_no_observed_stale` excludes `(1,0)`), while `relaxed_stale_rules` and `actual_relaxed_stale` prove that `(1,0)` is admitted in Relaxed mode.
   - `latest_flag_one_data_one` and `stale_not_latest` prove that any total interleaving schedule where loads must read the latest preceding write (`LatestOnly`) forces $D < F < A < B$ when $A = 1$ and therefore excludes the relaxed `(1,0)` witness.
   - `actual_wrong_supplier` proves that read-from (RF) edges must track modifying-event identities rather than numeric values: assigning $D$ (`dataStore`, value `1`) as the supplier for $A$ (`flagLoad`) produces the same numeric pair `(1,1)` as `bothStores`, but fails `RFValid` and is rejected as `.inconsistent locations`.
   - `actual_no_provenance_result`, `actual_dead_result`, `actual_misaligned_result`, and `invalid_ordering_independent` prove that atomic ordering never repairs raw pointer/allocation UB (`.noProvenance`, `.dead`, `.misalignedLoad`).
4. **Operational prefix semantics vs. snapshot prefiltering (`AtomicPrefixExecution`, `AtomicPrefixRules`, `AtomicPrefixCoverage`):**
   - Because `runCandidate` filters `flagValue rf = 0` before checking raw gates (`zero_flag_bad_producer_outside`), a static candidate classifier can return `.outsideBranch 0` even when an earlier producer store `D` has raw UB (`.noProvenance`).
   - `AtomicPrefixExecution` declares an independent operational step relation (`Step`) that threads actual `MiniRustReference.store` memory updates (`store_step_threads_raw`, `healthyD_actual`), immediately transitions to terminal `.ub` on any reached raw fault without future-completion or RF premises (`ub_step_iff`, `badD_first`, `badD_not_noUB`), and enforces an already-issued-write `ReadGuard` (`PrefixRules` over present records).
   - `AtomicPrefixRules` and `AtomicPrefixCoverage` prove root-reachable structural and coherence invariants (`root_prefix_invariant`, `root_prefix_coherent`), exact bidirectional agreement between completed `A = 1` prefix graphs and `SelectedRules` (`completed_flag_one_bridge`), partial-projection soundness (`projected_sound`), constructive producer-first coverage (`old_observed_covered`, where raw memory holds `[1, 0]` at both locations even when relaxed `RF` selects `Idata` and binds atomic value `0`), and `root_flag_zero_no_B` (proving that any root-reachable `A = 0` configuration skips the consumer without ever attempting or recording `B`).

## Applicability

These findings apply to:

- Formalizing weak-memory extensions, read-from (RF) / modification-order (MO) / happens-before (HB) consistency predicates, or operational write-history buffers on top of MiniRust's `Memory` and `ConcurrentMemory` traits.
- Designing verification conditions for concurrent Rust code using `core::sync::atomic` (`Ordering::Release`, `Ordering::Acquire`, `Ordering::Relaxed`) that must simultaneously enforce pointer/provenance/alignment validity and weak-memory coherence.

Specific version and configuration anchors:

- **C++ working draft baseline:** `cplusplus/draft` tag `n4868` (commit `1f468a67c67143625d7946cdc4cfc7f7730d9160`), specifically `source/basic.tex` (blob `f078e90b7505cad0a51f896b16d12c059aca6330`, SHA-256 `61ed03143748efdcdad8c5da86d374c35f6ce2c3b17172b6615f311c9fdf2f2a`) and `source/atomics.tex` (blob `5891afba507bda95dad2fe6b2fbe3d3a7f7730d9160` / `5891afba507bda95dad2fe6b2fbe3d3a7f759891`, SHA-256 `72e815eb5db56ce779ac19aecb4bbdc09b4b7293c7663b0713640937a8fa0186`).
- **Rust standard library and Reference:** `rust-lang/rust` release `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `library/core/src/sync/atomic.rs` blob `71502f8d918e739c558710955e3fba31db2ad29e`, SHA-256 `cec944d1305f81be719caf639e8dce2f8aaba9a3d7751cb48f2bbf22096e4d2e`) and `rust-lang/reference` (`82da570bafd9efed421bdbae0f8603ede8dd308b`).
- **MiniRust specification:** `minirust/minirust` commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`.
- **Lean 4 kernel verification:** Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`).

## Findings

### 1. Normative and Documentation Audit: N4868 C++20 Draft and Rust `core::sync::atomic`

`Basis: normative | documentation | source`

Rust's `library/core/src/sync/atomic.rs:25-58` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) states that Rust atomics follow the same rules as C++20 atomics (`cpp-intro.races`), citing the N4868 draft URL (`https://timsong-cpp.github.io/cppwp/n4868/intro.multithread#intro.races`, generated from `cplusplus/draft` tag `n4868`, commit `1f468a67c67143625d7946cdc4cfc7f7730d9160`). Cross-checking the pinned LaTeX sources (`basic.tex` and `atomics.tex`) and Rust's adaptation (`atomic.rs`) isolates the exact clauses governing two-thread message passing:

| Source File and Passage | Clause / Role | Extracted Contract and Qualification |
| --- | --- | --- |
| `basic.tex:5715-5752` (`intro.execution`) | Sequenced-before (`sb`) | Full-expressions within a single thread are ordered by sequenced-before ($D \xrightarrow{\text{sb}} F$ in producer, $A \xrightarrow{\text{sb}} B$ in consumer). |
| `basic.tex:5908-5967` (`intro.races` §§3–6) | Modification order (`mo`) and release sequences | Every atomic object has a total modification order over all modifications to that object (§4). No global order across distinct atomic objects is required. With no RMW operations present, a release sequence headed by $F$ consists solely of $\{F\}$ (§5). |
| `atomics.tex:388-426` (`atomics.order` §§1–2) | Release/Acquire synchronization (`sw`) | An atomic store with `memory_order::release` is a release operation; an atomic load with `memory_order::acquire` is an acquire operation; `memory_order::relaxed` performs no synchronization (§1). An acquire operation $A$ on an atomic object $M$ synchronizes with ($F \xrightarrow{\text{sw}} A$) a release operation $F$ on $M$ if $A$ takes its value from a side effect in the release sequence headed by $F$ (§2). Equal observed bits alone do not establish synchronization; the supplying modification identity is required. |
| `basic.tex:6019-6085` (`intro.races` §§9–11) | Happens-before (`hb`) and acyclicity | Without `consume` operations (which Rust excludes), happens-before coincides with simply-happens-before: the transitive closure of sequenced-before and synchronizes-with. An execution is inconsistent if happens-before contains a cycle (§10). |
| `basic.tex:6138-6147` (`intro.races` §14) | Atomic read-source restriction | The value of an atomic read $R$ is the value stored by some modifying side effect $W$ on the same object, and $R$ cannot happen before $W$ ($\neg (R \xrightarrow{\text{hb}} W)$). |
| `basic.tex:6149-6197` (`intro.races` §§15–18) | Four coherence rules | **Write-write (§15):** if $W_1 \xrightarrow{\text{hb}} W_2$ on $M$, then $W_1 \xrightarrow{\text{mo}} W_2$. **Read-read (§16):** if $R_1 \xrightarrow{\text{hb}} R_2$ on $M$ and $R_1$ observes $W_1$, then $R_2$ observes $W_1$ or $W_2$ with $W_1 \xrightarrow{\text{mo}} W_2$. **Read-write (§17):** if $R \xrightarrow{\text{hb}} W$ on $M$ and $R$ observes $W_0$, then $W_0 \xrightarrow{\text{mo}} W$. **Write-read (§18):** if $W \xrightarrow{\text{hb}} R$ on $M$, then $R$ observes $W$ or $W'$ with $W \xrightarrow{\text{mo}} W'$. |
| `basic.tex:6217-6229` (`intro.races` §21), `atomics.tex:1654-1665` (`atomics.types.operations` §3) | Data races and non-atomic initialization | Two conflicting actions in different threads not ordered by HB cause a data race (UB) unless both are atomic (§21). Atomic constructor initialization (`AtomicUsize::new(0)`) is **not** an atomic operation (`atomics.types.operations` §3); initialization must happen-before worker accesses via thread creation or prior synchronization. |
| `library/core/src/sync/atomic.rs:25-58, 4489-4498` | Rust access-byte adaptation | Rust omits `Consume`, translates C++ object-value rules to accessed byte spans, permits concurrent atomic and non-atomic reads, requires unordered overlapping atomic accesses to have identical byte span and size (or be two reads), and panics at runtime on `fence(Ordering::Relaxed)` (`atomic.rs:4489-4498`). |

### 2. MiniRust `@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` Concurrency and Atomic Boundary

`Basis: source`

Inspecting the three concurrency and atomic files in MiniRust at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (`support/atomic-message-passing-sources.json`) establishes the exact boundary between MiniRust's built-in concurrency wrapper and weak-memory ordering:

1. **`spec/mem/concurrent.md` (5,864 bytes, SHA-256 `2b3f928517bed4da43739395656c7e24572dae37cb041fb7b77061c47a8e5816`):**
   - Lines 14–21 define `pub enum Atomicity { Atomic, None }`, documenting `Atomic` as a sequentially consistent atomic access and `None` as a non-atomic access. There are no `Release`, `Acquire`, or `Relaxed` variants.
   - Lines 63–86 (`ConcurrentMemory::store` and `ConcurrentMemory::load`) push an `Access { kind, atomicity, addr: ptr.addr, len }` into `self.accesses` and delegate directly to `self.memory.store(ptr, bytes, align)` or `self.memory.load(ptr, len, align)`. No ordering parameter or read-from supplier selection exists in these methods.
   - **Qualification on the file header (`concurrent.md:3-4`):** Although the prose header states that *"Atomicity is currently ignored"*, `Access.races` (lines 164–174) explicitly checks `if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }` after excluding two loads. Furthermore, `check_data_races` (lines 134–149) takes `cur_thread: ThreadId` and `sync_threads: Set<ThreadId>`, filtering out accesses from threads in `sync_threads` before checking `Access.races`. Thus `Atomicity` is actively used for data-race filtering, and thread IDs are present in the race detector.
2. **`spec/mem/interface.md` (7,541 bytes, SHA-256 `dfe4e0f504fc8892a520c555cb64b82774973b46f9adcaaaf915f4e5610f4708`):**
   - Lines 95–110 define `Memory::store` and `Memory::load` with ordinary `Result` return types (recording that only `allocate` is `NdResult`).
   - Lines 162–167 explicitly document that supporting concurrency in the `Memory` trait will require adding a thread-ID parameter to memory operations and an `Option<Ordering>` parameter to `load` and `store`.
3. **`spec/lang/step/intrinsics.md` (20,288 bytes, SHA-256 `261fe197e65556bae74cf209c64c5913fdd713f3a57d2bf56f0b1fb0e3a34be8`):**
   - `AtomicStore` (lines 430–463) and `AtomicLoad` (lines 465–490) validate argument counts, thin-pointer types, power-of-two size/alignment up to `Target::MAX_ATOMIC_SIZE`, and invoke `typed_store(..., Atomicity::Atomic)` / `typed_load(..., Atomicity::Atomic)`. Neither intrinsic takes a memory-ordering argument.

Consequently, modeling Release/Acquire vs. Relaxed message passing and read-from value supply on top of MiniRust requires an explicit weak-memory extension layer above `MiniRustReference`'s raw byte/allocation kernel.

### 3. Six-Event Message-Passing Classifier, Latest-Value Exclusion, and Storage Validity Controls (`AtomicMessagePassing.lean`, `AtomicMessagePassingControls.lean`)

`Basis: execution | derived`

`support/AtomicMessagePassing.lean` (SHA-256 `869ce51f5c4ca92a58015ea5ed1764052f37597e4e0ce6a8ad50e3485abddddd`, 28 `#print axioms` audits, 3 axiom-free) and `support/AtomicMessagePassingControls.lean` (SHA-256 `45c01ff675970c43cbd6d76f035ed8f4f7a62b676518d5152114378c24009f76`, 37 `#print axioms` audits, 2 axiom-free) formalize the six-event message-passing litmus over two 2-byte atomic locations (`data` at allocation `0`, base `16`; `flag` at allocation `1`, base `32`):

```text
Initial modifications: Idata (data := 0), Iflag (flag := 0)
Producer thread:       D: data.store(1, Relaxed);  F: flag.store(1, mode)
Consumer thread:       A: flag.load(mode);         if A == 1 { B: data.load(Relaxed) }
```

Key verified theorems and controls:

1. **Per-location MO and HB acyclicity (`mo_irreflexive`, `mo_transitive`, `mo_same_location`, `mo_total_per_location`, `hb_acyclic`, `no_read_hb_write`):**
   - `MO` orders `.initialData < .dataStore` and `.initialFlag < .flagStore` per location without imposing a cross-location total order.
   - `HB mode rf` is the inductive transitive closure of initialization edges (`IsInitial → IsRuntime`), producer sequencing (`.d → .f`), consumer sequencing (`.a → .b`), and conditional Release/Acquire synchronization (`mode = .releaseAcquire → rf.flag = .flagStore → HB mode rf .f .a`).
2. **Release/Acquire `(1,0)` exclusion vs. Relaxed `(1,0)` admissibility:**
   - `ra_flag_one_data_one`: for any `Locations` satisfying `Shape` and any `rf : RF` satisfying `SelectedRules locations .releaseAcquire rf` with `flagValue rf = 1`, `flag_one_supplier` forces `rf.flag = .flagStore`, `data_hb_read` derives `HB .releaseAcquire rf .d .b`, and `rules.writeRead` eliminates `.initialData`, proving `dataValue rf = 1`.
   - `both_stores_rules` proves `SelectedRules locations mode ⟨.flagStore, .dataStore⟩` (`returned = (1, 1)`) in both modes.
   - `relaxed_stale_rules` uses the monotone cut `relaxed_cut` (`producerCut .d = producerCut .f = 1`, `producerCut _ = 0`) to prove that `HB .relaxed staleData .d .b` cannot hold, establishing `SelectedRules locations .relaxed ⟨.flagStore, .initialData⟩` (`returned = (1, 0)`).
3. **Exclusion of `(1,0)` by latest-preceding-write interleavings (`latest_flag_one_data_one`, `stale_not_latest`, `sequential_both_stores_latest`):**
   - `Schedule` assigns injective natural-number positions to all 6 events respecting initialization, `position .d < position .f`, and `position .a < position .b`.
   - `LatestOnly` requires each read's supplier to precede the read and forbids any intervening same-location write $W$ with $\text{pos}(\text{source}(R)) < \text{pos}(W) < \text{pos}(R)$.
   - `latest_flag_one_data_one` proves that when `flagValue rf = 1`, `rf.flag = .flagStore` forces $\text{pos}(D) < \text{pos}(F) < \text{pos}(A) < \text{pos}(B)$, so $D$ intervenes between $I_{\text{data}}$ and $B$. Thus `stale_not_latest` refutes `LatestOnly locations staleData schedule` for every possible `Schedule`, while `sequential_both_stores_latest` witnesses `LatestOnly` for `bothStores` `(1,1)`.
4. **Coupling with `MiniRustReference` raw storage gates (`runCandidate`, `observed_sound`, `ra_observed_values`, `ra_no_observed_stale`):**
   - `gates` checks `writeGate` (`MiniRustReference.store ... oneBytes 2` + `checkedLocation`) on `D` and `F` and `readGate` (`MiniRustReference.load ... 2 2` + `checkedLocation`) on `A` and `B` against the `StateWF` initial snapshot `initial` (`initial_StateWF`, `initial_operand_admission`, `initial_initialized`).
   - `actual_raw_zero_loads`, `actual_ra`, and `actual_relaxed_stale` prove that while raw loads from `initial` return `[zeroByte, zeroByte]`, the mathematical classifier `runCandidate` returns `.observed locations (1, 1)` for Release/Acquire `bothStores` and `.observed locations (1, 0)` for Relaxed `staleData`.
5. **Supplier-identity, pointer-alias, and storage-failure discriminators:**
   - **Wrong supplier with equal numeric value (`wrong_supplier_same_values`, `actual_wrong_supplier`):** `wrongSupplier := ⟨.dataStore, .dataStore⟩` has `returned wrongSupplier = (1, 1) = returned bothStores`, but because `.dataStore` modifies `dataSpan` rather than `flagSpan`, `runCandidate initial handles mode wrongSupplier = .inconsistent locations`.
   - **Zero-offset pointer alias (`alias_pointer`, `alias_handle_distinct`, `alias_substitution`, `actual_alias_outcomes`):** `dataAlias := ⟨MiniRustReference.wrappingOffset dataPointer 0, 77⟩` has a distinct handle label (`77 ≠ 3`) but resolves to the identical `dataSpan`, preserving `gates`, `SelectedRules`, and `runCandidate` across all modes and `RF` inputs.
   - **Raw UB independence from atomic ordering (`actual_no_provenance_result`, `actual_dead_result`, `actual_misaligned_result`, `invalid_no_observation`, `invalid_ordering_independent`):** Removing provenance (`⟨16, none⟩`), deallocating allocation `0` (`deadData`), or misaligning the load pointer (`⟨17, some 0⟩`, where `actual_misalignment_before_bounds` shows `load` returns `.ub .misalignedLoad` before `checkPtr`'s `.ub .bounds`) yields `.ordinaryUB` identically in both `releaseAcquire` and `relaxed` modes.

### 4. Operational Execution Prefixes and Completed-Candidate Coverage (`AtomicPrefixExecution.lean`, `AtomicPrefixRules.lean`, `AtomicPrefixCoverage.lean`)

`Basis: execution | derived`

In `AtomicMessagePassingControls.lean`, `zero_flag_bad_producer_outside` exposes a key limitation of static candidate prefiltering: when `flagValue zeroFlag = 0`, `runCandidate initial badProducerHandles mode zeroFlag = .outsideBranch 0` even though `MiniRustReference.store initial noProvenancePointer oneBytes 2 = .ub .noProvenance`. To model actual prefix execution without prefiltering away earlier faults, three Lean 4.34.1 modules formalize a step-by-step operational semantics:

1. **Operational machine and immediate raw-UB reflection (`support/AtomicPrefixExecution.lean`, SHA-256 `6c612cbd6502fd0c0832b9897d703e7bfff63c79480dac38e294b76aa2f7e50c`, 13 audits, 1 axiom-free):**
   - `Machine` tracks `raw : MiniRustReference.State`, `producer : ProducerPC` (`d`, `f`, `done`), `consumer : ConsumerPC` (`a`, `b`, `skipped`, `done`), `trace : List Attempt`, `writes : List WriteRecord`, and `flagRead / dataRead : Option ReadRecord`.
   - `ActionStep.store` executes `MiniRustReference.store before.raw ... oneBytes 2 = .ok changed`, threads the exact updated memory `changed` into `commitStore` (`store_step_threads_raw`, `scheduled_store_success`), and requires no consistency or future-completion guard. `healthyD_actual` proves that executing `D` produces `afterDMemory ≠ initial` where `dataPointer` loads `oneBytes` and `flagPointer` loads `zeroBytes`.
   - `ActionStep.ub` immediately transitions to terminal `.ub instruction diagnostic` whenever a scheduled raw store or load returns `.ub diagnostic` (`ub_step_iff`, `fault_residual`, `terminal_no_step`). `badD_first` and `badD_not_noUB` prove that scheduling a no-provenance `D` store reaches `.ub .d .noProvenance` in 1 step and refutes `Execution.NoUB` in both modes before any consumer read occurs.
   - `ActionStep.read` requires a successful raw `MiniRustReference.load` (recording the actual `rawBytes`) together with `ReadGuard`, which checks that `record.supplier` is already present in `before.writes` at `spanOf checked` (**already-issued-write policy**) and that `PrefixRules` holds on the tentative prefix `commitRead before input op record`.
2. **Rooted prefix coherence and completed `A = 1` graph bridge (`support/AtomicPrefixRules.lean`, SHA-256 `121cfcd44d625e4164f80c98869298f6749a617d229f30472eeb4a839ba5dcb4`, 20 audits):**
   - `store_preserves_info` and `successful_span` prove from the raw kernel definitions that successful stores preserve allocation metadata (`RawLayout`) and that within the 81-input operand family (`healthy | noProvenance | misaligned` per instruction), only `.healthy` operands succeed and always resolve to their canonical `designated` span.
   - `pending_reads` proves that whenever `machine.producer ≠ .done`, `machine.dataRead = none` and any completed `A` read must have selected `.initialFlag`. Using `zeroRF := ⟨.initialFlag, .initialData⟩` as a proof-only full-graph extension (`rules_from_full`, `zero_rules`), `store_coherent` and `scheduled_store_coherent` prove that **every scheduled successful store preserves `PrefixRules` unconditionally**, without assuming incoming coherence or future completion.
   - `root_prefix_invariant` and `root_prefix_coherent` establish `Structure` and `PrefixRules` for every configuration reachable from `root` (including running, normal, `.ub`, and `.unsupported` residuals).
   - `completed_flag_one_bridge` proves that for any reachable `.normal machine` where `A` read `1`, both stores and both reads have completed (`Complete machine flag data`), all four operands are `.healthy`, `PrefixHB` and `PrefixMO` are bi-implicationally equivalent to full `AtomicMessagePassing.HB` and `MO` under `extractedRF flag data` (`complete_hb_iff`, `complete_mo_iff`), and `SelectedRules` holds (`complete_selected_rules`).
3. **Partial-projection soundness, producer-first coverage, and `A = 0` branch history (`support/AtomicPrefixCoverage.lean`, SHA-256 `25b051bab35d64da7c496b2f074be2a0afeb708888bb3d660eb2fc9063f4976a`, 15 audits):**
   - `project : Config → Option CandidateProjection` extracts `⟨locations, extractedRF flag data, (readValue flag, readValue data)⟩` only for `.normal` configurations with `readValue flag = 1`.
   - `projected_sound` and `completed_sound` prove that every defined projection of a root-reachable prefix is an accepted `.observed` result of `AtomicMessagePassing.runCandidate`.
   - Conversely, `old_observed_covered` and `producer_first_run` prove that every `.observed` equation of `runCandidate` in the input family is realized by an explicit 5-step operational execution (`D → F → A → B → finish`) ending in `.normal (producerAB input rf)` with `raw = afterDFMemory`. In `producer_first_observations`, both locations in `afterDFMemory` contain `oneBytes` (`[1, 0]`), and `B`'s `ReadRecord` records `rawBytes = oneBytes` even when Relaxed `rf` selects `.initialData` and binds `readValue = 0`.
   - `ra_completed_values` derives `(readValue flag, readValue data) = (1, 1)` for all Release/Acquire `A = 1` normal completions via the completed bridge.
   - `root_trace_history` and `root_flag_zero_no_B` prove an inductive trace invariant (`BHistory`): across all reachable configurations (running or terminal), if `A` read `0`, then `consumer = .skipped`, `dataRead = none`, and no attempt in `machine.trace` ever executed `.read .data` (even as a failed UB attempt).

## Boundaries

- **`not examined`:**
  - Read-modify-write (RMW) operations (`fetch_add`, `compare_exchange`, `compare_exchange_weak`), multi-step release sequences, fences (`atomic::fence`, `compiler_fence`), and `Ordering::SeqCst` total-order interactions.
  - Promising-semantics or speculative future-write execution prefixes (where a relaxed load observes a store from another thread before that store has been issued in global step order), as well as out-of-thin-air (`atomics.order` §8) value-computation cycles.
  - Concurrent composition of weak-memory read-from graphs with Tree Borrows alias/protector state transitions.
- **`unknown`:**
  - Exact formal specification of the complete Rust weak-memory model where `rust-lang/reference` (`src/memory-model.md:4-5`) marks the model as open/incomplete beyond the C++20 rules inherited by `core::sync::atomic`.
- **`known not to apply`:**
  - A non-atomic payload `data` cannot be used as the relaxed `(1,0)` stale-data control: without Release/Acquire synchronization on `flag`, the producer's `data` write and consumer's `data` read are unordered by HB and would form a data race (`intro.races` §21, `atomic.rs:25-58`).
  - A single global memory store where every load returns the latest preceding write (`LatestOnly`) cannot realize the C++20/Rust Relaxed `(1,0)` message-passing outcome (`stale_not_latest`).
  - Candidate prefiltering on `flag == 0` (`runCandidate` returning `.outsideBranch 0`) does **not** establish prefix safety (`NoUB`), because an earlier producer operation can fault before the consumer inspects `flag` (`zero_flag_bad_producer_outside`, `badD_first`).
- **`unsupported`:**
  - In MiniRust at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `Release`, `Acquire`, and `Relaxed` memory orderings are not supported by `Atomicity`, `Memory::load`/`store`, or `AtomicLoad`/`AtomicStore` (`spec/mem/concurrent.md:14-21`, `spec/mem/interface.md:162-167`, `spec/lang/step/intrinsics.md:430-490`).
  - In the atomic-prefix study (`atomic-prefix-coverage.md`), a fourth planned module (`AtomicPrefixControls`, SHA-256 `22428d161304e8c99df67e9001e01b56331854104d187975fb9f9181b1af4e57`) failed its check with two `rfl` type mismatches at the study's preset 4-failure cap and is wholly excluded from accepted evidence; its unaccepted mutant discriminators (`CompletionPrunedStep` and `DiscardSuccessfulStoreState`) are not claimed as checked results.

## Evidence

All primary evidence artifacts are archived in `support/`:

| File | Bytes | SHA-256 | Audits (Axiom-Free) | Role |
| --- | ---: | --- | ---: | --- |
| `support/atomic-message-passing-sources.json` | 3,107 | `54374238ec485df290b09384ce814cddfe45e6a0d6f4da4b58e7ce089b59094c` | — | Pinned commit, blob, size, and SHA-256 inventory for N4868 `basic.tex`/`atomics.tex`, Rust `atomic.rs`, and MiniRust `concurrent.md`/`interface.md`/`intrinsics.md`. |
| `support/AtomicMessagePassing.lean` | 24,409 | `869ce51f5c4ca92a58015ea5ed1764052f37597e4e0ce6a8ad50e3485abddddd` | 28 (3) | Six-event `SelectedRules` model, `ra_flag_one_data_one`, `relaxed_stale_rules`, `LatestOnly` exclusion (`stale_not_latest`), and `runCandidate`. |
| `support/AtomicMessagePassingControls.lean` | 17,301 | `45c01ff675970c43cbd6d76f035ed8f4f7a62b676518d5152114378c24009f76` | 37 (2) | Concrete 2-allocation `MiniRustReference` snapshot, `observed_sound`, `actual_ra`, `actual_relaxed_stale`, `actual_wrong_supplier`, `alias_substitution`, and raw UB controls. |
| `support/AtomicPrefixExecution.lean` | 28,255 | `6c612cbd6502fd0c0832b9897d703e7bfff63c79480dac38e294b76aa2f7e50c` | 13 (1) | Operational prefix machine (`Step`), state-threading stores (`store_step_threads_raw`, `healthyD_actual`), and immediate UB reflection (`ub_step_iff`, `badD_first`). |
| `support/AtomicPrefixRules.lean` | 45,011 | `121cfcd44d625e4164f80c98869298f6749a617d229f30472eeb4a839ba5dcb4` | 20 (0) | `RawLayout` and `Structure` preservation, unguarded store coherence (`store_coherent`), `root_prefix_coherent`, and `completed_flag_one_bridge`. |
| `support/AtomicPrefixCoverage.lean` | 38,195 | `25b051bab35d64da7c496b2f074be2a0afeb708888bb3d660eb2fc9063f4976a` | 15 (0) | Partial projection soundness (`projected_sound`), constructive producer-first coverage (`old_observed_covered`), `ra_completed_values`, and `root_flag_zero_no_B`. |
| `support/lean-check-results.json` | 40,958 | `cc6835ac5c651a5d575cd5768cb55fcf326a2498b92e80cce2beefa19ef1f330` | — | Complete Lean 4.34.1 verification ledger (`exit_code: 0`, `.olean` digests, and `#print axioms` audits for all 5 target modules and dependencies). |

## Revalidation

To revalidate all five Lean 4.34.1 modules in topological order (after compiling base modules `MiniRustReference` and `Execution` onto `LEAN_PATH`):

```bash
for mod in AtomicMessagePassing AtomicMessagePassingControls AtomicPrefixExecution AtomicPrefixRules AtomicPrefixCoverage; do
  lean -j1 -M2048 -o "/tmp/build/AnnealResearch/${mod}.olean" "support/${mod}.lean"
done
```

Every module compiles with exit code `0`, zero warnings, and `.olean` SHA-256 digests matching both the original canonical development records and `support/lean-check-results.json`.
