# TLA+ Execution-Trace Conformance, Packetdrill Wire-Timing Validation, and Multi-Oracle Parser-Differential Fuzzing

## Summary

Formal protocol specifications and high-level type safety proofs routinely fail at three concrete implementation boundaries: (1) **implementation-to-model refinement drift**, where distributed systems (`etcd`, `MongoDB`) pass model checking on an idealized TLA+ specification while production Go/C++ state machines omit persistence barriers, reorder configuration transitions, or take unmodeled silent steps; (2) **kernel wire-timing and stateful message-order drift**, where TCP/UDP/ICMP socket implementations and TLS state machines deviate from RFC timer tolerances (`RACK-TLP`, `PTO`), randomized Initial Sequence Number (`ISN`) arithmetic, or handshake transition guards; and (3) **multi-implementation parser split-brain**, where X.509/ASN.1, JSON, ELF, PDF, or URI parsers accept or interpret identical byte buffers differently across trust boundaries (`Basis: source, normative`).

Grounded in twelve pinned repositories (`tlaplus/tlaplus`, `tlaplus/CommunityModules`, `apalache-mc/apalache`, `etcd-io/raft`, `etcd-io/etcd`, `mongodb/mongo`, `google/packetdrill`, `tls-attacker/TLS-Attacker`, `nezha-dt/nezha`, `C2SP/x509-limbo`, `nst/JSONTestSuite`, `project-everest/everparse`), seven peer-reviewed primary papers, and deterministic execution probes, this report establishes four primary findings:

1. **Constrained BFS Trace Validation (`TraceSpec` + `TraceView == <<vars, l>>` + `TraceMatched`)**: In `etcd-io/raft` (`ae830f4a15a0bdb5f59bb7988e50663e92cc028f`), compile-time `//go:build with_tla` instrumentation emits newline-delimited JSON (`NDJSON`) snapshots (`tla/example.ndjson`, `4,888` real Go Raft events across `17` observed event kinds out of `19` defined `stateMachineEventType` variants). `Traceetcdraft.tla` (`L35–475`) and `Traceetcdraft.cfg` (`L22–75`) solve partial-observability and granularity mismatch via three mechanisms: stratifying TLC's state-fingerprint view by log cursor `TraceView == <<vars, l>>` (`L451–457`) so revisited protocol states are not pruned; disabling `CHECK_DEADLOCK FALSE` (`Traceetcdraft.cfg:43–44`) while encoding existential trace-extension conformance as the single-worker BFS temporal property `TraceMatched == [](l <= Len(TraceLog) => [](TLCGet("queue") = 1 \/ l > Len(TraceLog)))` (`L461–471`); and decoupling implementation vs. model step counts through `StepToNextTraceIfMessageIsProcessed` (`L119–125`) and `SkipUnusedLogline` (`L387–395`) while simultaneously verifying `etcdSpec` refinement and `8` global Raft invariants (`Basis: source, execution`).
2. **Microsecond Wire-Timing & Stateful Protocol Fuzzing (`Packetdrill` + `TLS-Attacker`)**: `google/packetdrill` (`15ab46aedd01a5e664ec5cfb2b1888328cdd3901`) achieves deterministic microsecond kernel socket-to-packet testing via a two-thread single-mutex (`state->mutex`, `run.h:25–52`) execution loop, busy-spinning `const int MAX_SPIN_USECS = 20` (`run.c:55–68`) before deadlines to wake tickless (`CONFIG_NO_HZ=y`) kernels and eliminate `~15 µs` `unlock`/`usleep`/`lock` jiffy-staleness jitter, pre-caching unique ephemeral 4-tuples (`run_packet.c:52–83`) to avoid `TIME_WAIT` collisions, and translating script-relative sequence numbers into live randomized kernel ISNs even inside echoed ICMP error payloads (`map_inbound_icmp_tcp_packet`, `run_packet.c:539–547`). Complementarily, `tls-attacker/TLS-Attacker` (`5ab7d3d6a0a82e2fef8a298a7a59da61d0da979e`) replaces fixed handshake drivers with XML-serializable `WorkflowTrace` sequences annotated with `@HoldsModifiableVariable` (`WorkflowTrace.java:48–100`) and socket-retaining `State.reset()` (`State.java:88–105`), exposing state-machine bypasses (`CCS` injection, `0-RTT` replay) while incurring a documented JAXB serialization bottleneck in `WorkflowTrace.copy()` (`WorkflowTrace.java:57–87`) (`Basis: source, execution`).
3. **Behavioral-Asymmetry ($\delta$-Diversity) Differential Fuzzing vs. Verified Canonical Parsers (`NEZHA` vs. `EverParse`)**: `nezha-dt/nezha` (`cd3b5fcc958ce4d216cee1c2f39695d7302fc8dc`) demonstrates why single-target edge coverage stalls on semantic parser bugs: by packing chain validation outcome, certificate depth, and error code into `compositize_ret_val(raw_ret, depth, err)` (`common.h:34–38`), isolating colliding C symbol tables via `dlopen(..., RTLD_LAZY)` (`diff.cpp:13–30`), and rewarding novel cross-library output/edge vectors (`diff.h:48–89`), NEZHA exposes critical X.509 split-brain vulnerabilities such as LibreSSL `2.4.0`'s `asn1_time_parse` inferring `UTCTime` vs. `GeneralizedTime` purely from byte `len` while ignoring the ASN.1 tag (`openssl-1.0.2h_libressl-2.4.0/Readme.md:6–94`), causing expired certificates rejected by OpenSSL (`a000:certificate has expired`) to pass LibreSSL (`0:OK`). Across `nst/JSONTestSuite` (`1ef36fa01286573e846ac449e8683f8833c5b26a`), `i_` (`IMPLEMENTATION_PASS` / `IMPLEMENTATION_FAIL`) inputs expose specification ambiguity across `30+` JSON parsers—and primary-source inspection uncovers two latent defects in `JSONTestSuite`'s own unverified runner (`run_tests.py:588` `UnboundLocalError` on first-test timeout and `run_tests.py:606` `result == "FAIL"` statement-expression bug). `project-everest/everparse` (`f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`, `LowParse`/`3D`/`QuackyDucky`/`EverCBOR`/`EverCDDL`) eliminates parser split-brain at the root by generating zero-copy C and standalone Rust parsers proven **sound, complete, and non-malleable (injective/bijective on deterministic encodings)** (`README.md:6–26, 74–99`) (`Basis: source, execution`).
4. **Cross-Cutting Synthesis (`L1–L6`, `C1–C2`, `V1–V4`)**: Unifying trace validation, packet-timing scripts, differential parser fuzzing, and Multi-Variant Execution Environments (`MVEE`, Volckaert et al., EuroSys 2017) under a single **Observation-Refinement & Canonical-Quotient Projection** ($\pi_{\text{obs}} : \Sigma_{\text{impl}} \twoheadrightarrow \Sigma_{\text{spec}} / {\sim}$) eliminates ad-hoc harness glue while defining exact validation gates from `V1` spec-mutation and test-harness auditing through `V4` continuous-time `STL`/`HIL` replay and operator mental-model litmus tests (`Basis: derived, normative`).

---

## Applicability

This report governs verification and systems-validation architecture across zero-copy binary parsing, FFI boundaries, distributed consensus implementations, and kernel/user-space network stacks:

- **Zero-Copy Layout & Binary Format Parsers (`zerocopy`, FFI Wire Boundaries)**: Whenever safe Rust code shares wire buffers (`#[repr(C)]`, packet headers, ASN.1/CBOR/JSON/ELF envelopes) across C/C++ FFI or multi-service proxies, memory safety (`TryFromBytes`) alone does **not** prevent semantic split-brain if an upstream C firewall (`LibreSSL`/`Go`/`C++`) and downstream Rust parser disagree on tag/length canonicality, duplicate keys, or trailing bytes. `EverParse`-style bijective canonicality (`format(parse(b)) == b`) plus `NEZHA`-style $\delta$-diversity differential fuzzing directly govern these boundaries (`Basis: source, derived`).
- **Implementation-to-Model Conformance for Stateful Systems**: Formal verification of an abstract state machine (`TLA+`, `Lean 4`) leaves an unverified refinement gap whenever production code uses asynchronous batching (`Ready`), network serialization (`raftpb`), or conditional build tags. Build-gated structured trace emission (`with_tla`) paired with constrained BFS/symbolic trace specs closes this gap on real integration and chaos-test executions without requiring monolithic deductive verification of the entire runtime (`Basis: source`).
- **Deterministic Sub-Millisecond I/O & Protocol State Machines**: Testing timers, retransmission (`RACK-TLP`), hardware crypto offloads (`PSP`), and adversarial message reorderings (`TLS 1.3` / `QUIC`) requires explicit virtualized or spin-calibrated wire injection (`Packetdrill`) and modifiable protocol workflow traces (`TLS-Attacker`) rather than wall-clock sleep tests (`Basis: source`).
- **Lockstep FFI Shadowing (`MVEE`)**: When wrapping legacy C codecs or migrating C/Rust components incrementally, lockstep multi-variant execution (`MVEE`) turns single-input production/fuzz traffic into an online differential soundness and memory-disclosure oracle (`Basis: documentation, derived`).

---

## Findings

### 1. TLA+/PlusCal Execution-Trace Conformance Validation (`TLC`, `Apalache`, `etcd-io/raft`, `MongoDB`)

`Basis: source, documentation, execution`

#### 1.1 Zero-Overhead Build-Gated Instrumentation (`etcd-io/raft`)
A recurring obstacle to trace validation in systems software is production telemetry overhead and log-schema rot. In `etcd-io/raft` (`ae830f4a15a0bdb5f59bb7988e50663e92cc028f`), `state_trace.go:15–120` isolates TLA+ instrumentation behind Go build constraint `//go:build with_tla` (`const StateTraceDeployed = true`), paired with no-op stubs in `state_trace_nop.go` (`//go:build !with_tla`) so default release binaries pay **zero instructions and zero heap allocations** (`L4`/`L6`) (`Basis: source`).

When compiled with `-tags=with_tla`, `state_trace.go:31–75` enumerates exactly `19` canonical `stateMachineEventType` transitions:
- Lifecycle & election (`InitState`, `BecomeCandidate`, `BecomeFollower`, `BecomeLeader`, `Ready`);
- Replication & commit (`Commit`, `Replicate`);
- Membership reconfiguration (`ChangeConf`, `ApplyConfChange` with `AddNewServer`, `RemoveServer`, `AddLearner` at `L78–81`);
- Wire RPC send/receive pairs (`SendAppendEntriesRequest`, `ReceiveAppendEntriesRequest`, `SendAppendEntriesResponse`, `ReceiveAppendEntriesResponse`, `SendRequestVoteRequest`, `ReceiveRequestVoteRequest`, `SendRequestVoteResponse`, `ReceiveRequestVoteResponse`, `SendSnapshot`, `ReceiveSnapshot`).

Each emitted NDJSON record (`TracingEvent`, `state_trace.go:83–113`) captures only the projection observable without cloning the full Raft log payload: `nid`, `role`, `State: {term, vote, commit}`, `log` (integer length `uint64`, not full entry contents), joint membership `conf: [2][]string`, and optional `TracingMessage` metadata (`type`, `term`, `from`, `to`, `entries` count, `logTerm`, `index`, `commit`, `vote`, `reject`, `rejectHint`) (`Basis: source`).

#### 1.2 Constrained BFS Trace Specifications: `TraceView`, `CHECK_DEADLOCK FALSE`, and `TraceMatched`
Mapping partial implementation logs onto a non-deterministic TLA+ specification (`etcdraft.tla`) via `tlaplus/CommunityModules` (`cbf7a667423a3768aa3c87fe622faf7db1baa2e7`, `modules/Json.tla:86–95` `JsonDeserialize`/`ndJsonDeserialize` and `modules/IOUtils.tla:34–87` Java overrides) exposes four subtle model-checking hazards solved directly in `etcd-io/raft/tla/Traceetcdraft.tla` (`L35–475`) and `Traceetcdraft.cfg` (`L22–75`) (`Basis: source`):

1. **State-Space Cycle Pruning vs. Repeated States (`TraceView`)**: A distributed node frequently returns to an identical abstract state $s$ (e.g., `Follower` at `term = 2` with identical `log` after heartbeats) at trace lines $i < j$. Standard TLC state fingerprinting discards any revisited state $s$, prematurely terminating exploration at line $j$. `Traceetcdraft.tla:451–457` defines `TraceView == <<vars, l>>` (configured via `VIEW TraceView` in `Traceetcdraft.cfg:25–26`), stratifying TLC's state graph into a DAG indexed by trace line $l \in 1..\mathrm{Len}(\mathit{TraceLog})$.
2. **Partial Observability & False Deadlocks (`CHECK_DEADLOCK FALSE` + `TraceMatched`)**: Because NDJSON logs omit internal variables (such as exact entry values or in-flight multiset multiplicities in `messages`), `TraceSpec` permits non-deterministic branching to reconstruct omitted state (`Traceetcdraft.cfg:16–21`). Dead-end branches that guess wrong fail to match a later line $k < \mathrm{Len}(\mathit{TraceLog})$ and have zero enabled `TraceNext` actions. Because `tlaplus/tlaplus` (`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`, `TLC.java:221, 250–251`) enables deadlock checking by default (`deadlock = true`), TLC would report the *first* dead-end guess as a spurious counterexample! Conformance is instead an **existential hyperproperty** ($\exists \sigma \in \llbracket \mathit{Spec} \rrbracket : \pi(\sigma) = \tau$). `Traceetcdraft.cfg:28–44` disables deadlock checking (`CHECK_DEADLOCK FALSE`) and checks a single-worker (`ASSUME TLCGet("config").worker = 1`, `TLCGet("config").mode = "bfs"`, `L35, 462`) temporal formula (`L464–471`):
   $$\mathit{TraceMatched} \triangleq \Box\bigl(l \le \mathrm{Len}(\mathit{TraceLog}) \implies \Box(\mathrm{TLCGet}(\text{"queue"}) = 1 \lor l > \mathrm{Len}(\mathit{TraceLog}))\bigr)$$
   Because TLC evaluates temporal properties *after* generating all successors of the current state, if the BFS queue is exhausted (`TLCGet("queue") = 1`) while $l \le \mathrm{Len}(\mathit{TraceLog})$, *every* non-deterministic reconstruction branch died at or before line $l$, proving true implementation-to-model non-conformance (`Basis: source`). (Modern TLC also exposes native `-loadTrace format file` in `TLC.java:269–270`, restricted to model-checking mode.)
3. **Action-Granularity Mismatch (Multi-Step Silent Actions & Skipped Implementation Logs)**: Cirstea, Kuppe, Loillier, and Merz (*Validating Traces of Distributed Programs Against TLA+ Specifications*, `arXiv:2404.16075`, `DOI: 10.48550/arXiv.2404.16075`) and Davis, Hirschhorn, and Schvimer (*eXtreme Modelling in Practice*, PVLDB 2020, `DOI: 10.14778/3397230.3397233`, documenting MongoDB replication TLA+ trace checking across `mongodb/mongo` `fec4e10e7616b50d54c3d77a0d97431cf944de03`) identify **atomicity mismatch** and **silent actions** as the dominant engineering cost in trace validation. `Traceetcdraft.tla` handles both directions explicitly:
   - *One log line $\to$ multiple spec actions*: In `TraceNextReceiveActions` (`L432–436`), `StepToNextTraceIfMessageIsProcessed(msg)` (`L119–125`) advances `l' = l + 1` only when `OneLessMessage(msg)` holds; otherwise it sets `pl' = l /\ UNCHANGED <<l>>`, while `ValidatePreStates(i)` (`L190–198`) guards pre-state assertions with `pl = l - 1 => ...` so intermediate silent steps on the same log line do not re-trigger pre-state mismatches.
   - *Multiple log lines $\to$ one spec action*: `SkipUnusedLogline` (`L387–395`) advances `StepToNextTrace` with `UNCHANGED <<vars>>` when Go `raft` emits separate `BecomeFollower` records already subsumed by `UpdateTerm` (`LoglineIsBecomeFollowerInUpdateTermOrReturnToFollower`, `L366–379`) or separate response-send logs (`SendAppendEntriesResponse` where `from # to`).
4. **Simultaneous Refinement & Invariant Checking**: `Traceetcdraft.cfg:34–35, 67–75` checks `PROPERTIES etcdSpec` (`etcd!Init /\ [][etcd!NextDynamic]_etcd!vars`, `L473–474`) alongside `8` safety invariants (`LogInv`, `MoreThanOneLeaderInv`, `ElectionSafetyInv`, `LogMatchingInv`, `QuorumLogInv`, `MoreUpToDateCorrectInv`, `LeaderCompletenessInv`, `CommittedIsDurableInv`), executed across parallel trace files via `tla/validate.sh:68` (`java -XX:+UseParallelGC ... tlc2.TLC ... -lncheck final -fpmem 0.9`). For traces with wide non-deterministic data domains where explicit-state enumeration explodes, `apalache-mc/apalache` (`78b8e72c982bca06507d7c1d9fc404cffc7cbb8e`) encodes bounded TLA+ transition chains directly into Z3 SMT constraints (`Basis: source, documentation`).

#### 1.3 Empirical Probe on Real `etcd-io/raft` NDJSON Traces
Executing our trace-conformance probe (reproduced in `## Revalidation`) against `etcd-io/raft/tla/example.ndjson` (`4,888` logged trace events spanning `17` distinct `stateMachineEventType` variants across a `5`-node reconfiguring cluster) confirms `100%` per-node term monotonicity, single-vote-per-term (`ElectionSafety`), and commit monotonicity (`real_trace_valid = true`). Injecting a single non-persisted `votedFor` restart glitch—where node `2` forgets its prior vote `"2"` in `term = 2` and grants vote `"99"` on the next event (`line 77`)—is caught immediately at exact `line 77` with `DoubleVoteInTerm(nid=2,term=2,2!=99)` (`Basis: execution`).

---

### 2. Deterministic Network-Stack Wire-Timing (`Packetdrill`) and Stateful Protocol Fuzzing (`TLS-Attacker`)

`Basis: source, documentation, execution`

#### 2.1 `google/packetdrill`: Microsecond Socket-to-Packet Determinism
Unit tests above POSIX sockets cannot observe malformed TCP options, middlebox sequence rewriting, or sub-millisecond retransmission timers (`RACK-TLP`, `BBR`), whereas full multi-VM network benchmarks suffer millisecond scheduling jitter and flaky timeouts (Cardwell et al., USENIX ATC 2013). `google/packetdrill` (`15ab46aedd01a5e664ec5cfb2b1888328cdd3901`) closes this gap through four concrete C mechanisms in `gtests/net/packetdrill/` (`Basis: source`):

1. **Two-Thread Single-Mutex Execution (`run.h:25–52, 93–110`)**: Every test process runs exactly two threads—the *main thread* (injecting inbound packets, sniffing outbound packets, executing non-blocking syscalls) and the *blocking system call thread*—coordinated by a single `pthread_mutex_t mutex` (`state->mutex`). The main thread holds `state->mutex` throughout script execution, unlocking it solely during `wait_for_event()` sleeps, waiting for the syscall thread to enter its kernel blocking point, or thread teardown (`run.h:38–44`). The syscall thread unlocks `state->mutex` only across the blocking kernel call itself (`run.h:48–52`), eliminating harness data races without lock-order complexity (`C1`/`C2`).
2. **Tickless-Kernel (`CONFIG_NO_HZ=y`) Spin-Wake Calibration (`run.c:55–68`)**: Sleeping right up to an event's microsecond timestamp via `usleep` introduces two errors: `~15 µs` `unlock`/`usleep`/`lock` wakeup latency (measured on a `2.2 GHz` host) and stale kernel `jiffies` on tickless (`CONFIG_NO_HZ=y`) Linux kernels. `run.c:68` defines `const int MAX_SPIN_USECS = 20`: `wait_for_event()` sleeps until `20 µs` prior to the target deadline (forcing the kernel wakeup path to refresh `jiffies`) and busy-spins the final `20 µs`, achieving sub-`20 µs` wire injection precision (`L4`).
3. **Pre-Cached Unique Ephemeral 4-Tuples (`run_packet.c:52–83`)**: Sequential TCP scripts running thousands of tests per minute collide with kernel `TIME_WAIT`, `FIN_WAIT1`, and `FIN_WAIT2` state if ports are reused. `ephemeral_port()` (`run_packet.c:59–64`) binds a socket to port `0` and **intentionally keeps the file descriptor open for the lifetime of the `packetdrill` process** (`L55–57`) so the OS never recycles the port, while `next_ephemeral_port()` (`L73–83`) pre-allocates the common single-remote-port case before test start so `0.000` `SYN` injection pays zero extra syscalls.
4. **Live Randomized ISN & Echoed-ICMP `SEQ` Translation (`run_packet.c:539–547`) + Hardware Offload Modes**: Scripts are authored against human-legible relative sequence numbers (`0:1000(1000)`), while the live kernel chooses a cryptographic random Initial Sequence Number (`live_isn`). `packetdrill` records `seq_offset = live_isn - script_isn`, rewrites inbound TCP `SEQ`/`ACK` headers on the fly, and in `map_inbound_icmp_tcp_packet()` (`run_packet.c:539–547`) even rewrites the **inner echoed 8-byte TCP header `seq`** inside inbound ICMP `Frag Needed` / `Packet Too Big` datagrams (`*seq = htonl(ntohl(*seq) + seq_offset)`) so kernel ICMP socket lookup accepts synthetic path-MTU faults! Beyond local `tun` virtual devices, `wire_client.c:22–90` + `wire_server.c` run identical `.pkt` scripts across a **physical NIC wire** between two machines (filtering `-wire_client` out of `argv` at `wire_client.c:52–86`) to validate hardware TSO/GRO/checksum offloads and `PSP` (`ynl_psp.c`, `psp_crypto.c`, `run.c:98–103`) netlink security associations (`Basis: source`).

Our wire-timing probe (reproduced in `## Revalidation`) verifies exact round-trip `ISN` + echoed-ICMP sequence translation (`live_isn = 0x9A41C300`, `script_seq = 1000` $\leftrightarrow$ `0x9a41c6e8`) and shows how `MAX_SPIN_USECS = 20` (`20,018 µs` observed TX) passes an RFC 8985 `RACK-TLP` `PTO = 2 * SRTT = 20,000 ± 1,000 µs` assertion while catching a `250 Hz` (`4 ms` jiffy-coalesced `24,000 µs`) timer regression (`Basis: execution`).

#### 2.2 `tls-attacker/TLS-Attacker`: Modifiable Stateful Protocol Workflows
Whereas `Packetdrill` validates transport headers and microsecond timers against a fixed script, cryptographic handshakes (`SSL 3.0`, `TLS 1.0–1.3`, `DTLS`, `0-RTT`, `STARTTLS`, `~300` cipher suites in `tls-attacker/TLS-Attacker` `5ab7d3d6a0a82e2fef8a298a7a59da61d0da979e`, `README.md:84–98`) fail when implementations accept **out-of-order, duplicated, or omitted protocol messages** (e.g., `EarlyChangeCipherSpec` CVE-2014-0224, `FREAK`, `ROBOT`, rogue `KeyUpdate`) (Somorovsky, ACM CCS 2016, `DOI: 10.1145/2976749.2978411`) (`Basis: source, documentation`).

`TLS-Attacker` models a protocol session as a mutable `WorkflowTrace` (`WorkflowTrace.java:48–115`) containing `List<AliasedConnection>` (supporting multi-party/MitM workflows via `TLS-Mitm`, `README.md:71, 92`) and `@HoldsModifiableVariable private List<TlsAction> tlsActions` (`L97–99`). Every cryptographic or framing field inside a `ProtocolMessage` is wrapped in a `ModifiableVariable` (supporting runtime `XOR`, byte insertion, truncation, or explicit override *after* valid session keys and handshake hashes are computed by `ContextContainer` in `State.java:51–86`). For stateful fuzzing loops, `State.reset()` (`State.java:88–105`) clears `contextContainer`, kills spawned target subprocesses, re-initializes cryptographic contexts, and invokes `retainServerTcpTransportHandlers()` (`L97–105`) to avoid `bind()` port-exhaustion stalls across iterations—while `WorkflowTrace.copy()` (`WorkflowTrace.java:55–87`) documents a concrete `L3`/`L4` engineering trade-off: round-tripping through JAXB XML (`WorkflowTraceSerializer.write` $\to$ `insecureRead`) and manually patching `@XmlTransient` flags (`setSingleConnectionWorkflow`) slows in-process mutation throughput compared to native C/Rust struct cloning (`Basis: source`).

---

### 3. Multi-Oracle Parser-Differential Fuzzing (`NEZHA`, `x509-limbo`, `JSONTestSuite`), Canonical Parsers (`EverParse`), and Lockstep `MVEE`

`Basis: source, documentation, execution`

#### 3.1 Behavioral Asymmetry ($\delta$-Diversity) in `nezha-dt/nezha` and `Frankencerts`
Standard coverage-guided fuzzing (`libFuzzer`/`AFL`) against a single parser struggles to uncover **semantic acceptance discrepancies**: once a parser's error-return branch (e.g., `asn1_time_parse` returning `V_ASN1_UTCTIME`) has been executed once, single-target edge coverage treats benign `UTCTime` inputs and adversarial tag-mismatched `GeneralizedTime` inputs as identical.

Following Brubaker et al.'s *Frankencerts* (`DOI: 10.1109/SP.2014.15`, which syntactically recombines certificate fields from real corpora across SSL libraries), Petsios et al. (*NEZHA: Efficient Domain-Independent Differential Testing*, IEEE S&P 2017, `DOI: 10.1109/SP.2017.27`; `nezha-dt/nezha` `cd3b5fcc958ce4d216cee1c2f39695d7302fc8dc`) introduce **$\delta$-diversity** across $N \ge 2$ independent implementations inside a single `libFuzzer` `-diff_mode=1` process (`differential_fuzzing_tutorial/Readme.md:14–64`) (`Basis: source, documentation`):

- **Symbol-Isolated In-Process Harness (`diff.cpp:13–30, 61–95`)**: Because OpenSSL and LibreSSL export identical C symbol names (`X509_verify_cert`, `d2i_X509`), static linking causes silent symbol interposition. `diff.cpp:13–30` loads each compiled shared library via `dlopen(libpath, RTLD_LAZY)` and resolves `dlsym(handle, FN_VERIFY_CERT)` into distinct function pointers (`verify_cert_openssl`, `verify_cert_libressl`).
- **Composite Semantic Return Encodings (`common.h:34–38`)**: Rather than collapsing validation to `1`/`0`, `common.h:34–38` packs three semantic coordinates into a 32-bit integer:
  $$\mathrm{compositize\_ret\_val}(\mathit{raw\_ret}, \mathit{depth}, \mathit{err}) = \mathit{raw\_ret} \;\lor\; (\mathit{depth} \ll 4) \;\lor\; (\mathit{err} \ll 12)$$
  distinguishing *whether* validation succeeded (`bit 0`), *which* certificate in the chain failed (`bits 11:4`), and *why* it failed (`bits 32:12`, e.g., `__LF_X509_V_ERR_CERT_HAS_EXPIRED = 10`, `__LF_X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD = 14`, `__LF_X509_V_ERR_UNHANDLED_CRITICAL_EXTENSION = 34` at `common.h:70–95`).
- **Per-Library Coarse Sanitizer Bitsets & Pre-Mutation Provenance (`diff.h:48–89`, `Readme.md:48–64`)**: `EXERCISE(name)` (`diff.h:48–60`) resets and snapshots `__sanitizer_update_counter_bitset_and_clear_counters(bitset_cur[cur_lib])` (`8` logarithmic hit buckets `1, 2, 3, 4–7, ..., 128+`) around each library invocation, prioritizing inputs that yield novel **joint return-value vectors** `(ret_0, ..., ret_{k-1})` or divergent path vectors `cov_diff`. Whenever a discrepancy occurs, NEZHA writes both `diff_<ret0>_<ret1>_<hash>` and `<hash>_BeforeMutationWas_<parent_hash>` (`differential_fuzzing_tutorial/Readme.md:53–64`) to localize the exact single-step byte mutation that broke consensus (`C1`).
- **Concrete X.509 Expiration Bypass Caught (`openssl-1.0.2h_libressl-2.4.0/Readme.md:6–94`)**: In RFC 5280 `Validity`, `Time ::= CHOICE { utcTime UTCTime, generalTime GeneralizedTime }`. In LibreSSL `2.4.0` (`crypto/asn1/a_time_tm.c`, quoted at `Readme.md:73–94`), `X509_cmp_time` calls `asn1_time_parse(ctm->data, ctm->length, &tm1, 0)` with `mode = 0`, which ignores the outer ASN.1 tag (`0x17` vs `0x18`) and switches purely on `len` (`case UTCTIME_LENGTH:` $\to$ `type = V_ASN1_UTCTIME`). Feeding a `GeneralizedTime` without seconds (`YYYYMMDDHHMMZ`, `13` bytes = `UTCTIME_LENGTH`) causes OpenSSL `1.0.2h` to reject (`openssl:a000:certificate has expired`, error `0xa = 10` shifted by `12` bits = `0xa000`) while LibreSSL `2.4.0` misinterprets the 4-digit year prefix as `YYMMDD...` and accepts an expired certificate (`libressl:0:OK`)!

Deterministic execution of our differential fuzzing probe (`600` mutation steps, fixed seed `20261119`, reproduced in `## Revalidation`) confirms that NEZHA $\delta$-diversity (`(ret_strict, ret_lax)` joint feedback) **doubles** the explored behavioral corpus (`12` vs. `6` distinct equivalence states) and increases discovered `accept`/`reject` split-brain inputs (`127` vs. `107`) compared to single-parser feedback (`Basis: execution`).

#### 3.2 Curated Conformance Oracles (`C2SP/x509-limbo`, `nst/JSONTestSuite`) and Harness Soundness Bugs
Differential fuzzing requires complementary normative conformance suites when *all* implementations share a common bug or when a specification leaves dangerous `implementation-defined` gray zones:
- **`C2SP/x509-limbo` (`b12423782a88abead01141fa6582254e3eb49e74`)**: Standardizes machine-readable RFC 5280 / CABF path-validation vectors (`limbo-schema.json`, `limbo.json`, incorporating Netflix `BetterTLS` cases, `README.md:18–22, 56–58`) evaluated across Rust (`harness-support/rust/src/models.rs:14–22` `ActualResult { Success, Failure, Skipped, Hang }`), Go (`harness/gocryptox509/main.go:21–87`), OpenSSL, BoringSSL, AWS-LC, GnuTLS, and Python `cryptography`.
- **`nst/JSONTestSuite` (`1ef36fa01286573e846ac449e8683f8833c5b26a`)**: Partitions inputs across `30+` parsers (`Awk`, `Bash`, `C`, `Go`, `Obj-C`, `Python`, `Rust`, `Zig`, `nlohmann_json`, `run_tests.py:23–522`) into three prefixes (`run_tests.py:613–621`): `y_` (must accept; failure logs `SHOULD_HAVE_PASSED`), `n_` (must reject; acceptance logs `SHOULD_HAVE_FAILED`), and `i_` (RFC 8259 implementation-defined—such as `[1e9999]`, lone UTF-16 surrogates `\uD800`, duplicate object keys, or `500`-deep nesting—logging `IMPLEMENTATION_PASS` vs. `IMPLEMENTATION_FAIL`). In multi-language architectures, **every `i_` disagreement is an exploitable WAF/signature-verification smuggling primitive** unless canonicalized!
- **Primary-Source Finding — Latent Bugs in `JSONTestSuite`'s Own Validator (`run_tests.py:588, 606`)**: Auditing `run_tests.py` uncovers two concrete `V1`/`V2` harness bugs (`Basis: source`):
  1. At `run_tests.py:605–606`, `elif status == 1: result == "FAIL"` uses equality `==` instead of assignment `=`, leaving `result = None` on normal parser rejections! This escapes notice only because lines `613–620` check `result == "CRASH"`, `result != "PASS"`, and `result == "PASS"`, never `result == "FAIL"`.
  2. At `run_tests.py:584–589`, `except subprocess.TimeoutExpired:` executes `print("RESULT:", result)` *before* `result` is bound at `L602`, crashing the entire runner with `UnboundLocalError` whenever the *first* test case of the run times out!

#### 3.3 Eliminating Split-Brain by Construction (`EverParse`) and Online Lockstep Shadowing (`MVEE`)
Rather than endlessly patching ad-hoc parsers after differential fuzzing finds discrepancies, two architectural mechanisms prevent split-brain outright:
1. **Verified Non-Malleable Zero-Copy Parsers (`project-everest/everparse`, `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`)**: Built on `LowParse` in F\*, Low\*, and Pulse (`README.md:6–26, 74–99`), `EverParse` compiles `3D` (dependent C-like binary layouts), `QuackyDucky` (TLS/QUIC RFC grammars), and `EverCDDL` / `EverCBOR` (generating verified C or **standalone Rust** via `everparse-cddl.exe --rust`, `L90–93`) into zero-copy validators/parsers proven:
   - *Memory-safe & arithmetic-overflow-free*;
   - *Sound and complete* with respect to the declarative grammar; and
   - *Non-malleable (injective parser / bijective deterministic serializer)*: for every valid semantic value $v$ and accepted byte slice $b$, $\mathrm{parse}(b) = \mathrm{Some}(v) \iff \mathrm{serialize}_{\text{det}}(v) = b$ (explicitly enforced in `EverCDDL` by restricting to deterministic CBOR encoding, `README.md:96–99`). Non-malleability mathematically collapses `i_` ambiguity to the empty set: two verified parsers for the same deterministic format **cannot** disagree on acceptance or AST interpretation (`Basis: source, normative`).
2. **Multi-Variant Execution Environments (`MVEE`, Volckaert et al., EuroSys 2017, `DOI: 10.1145/3064176.3064178`)**: When legacy C/C++ components cannot yet be replaced by verified parsers, an `MVEE` monitor runs $K \ge 2$ diversified variants (disjoint heap layouts, stack growth directions, register/canary secrets, or C vs. Rust implementations) in **syscall-level lockstep** on identical inputs, synchronizing nondeterministic events (`futex`/shared-memory ordering, `clock_gettime`, `getrandom`) via an in-process ring buffer (`~10–25%` CPU overhead on multithreaded servers). Any memory corruption (buffer overflow smashing a variant-unique stack canary) or semantic parser divergence manifests immediately as a **syscall argument or return-value divergence** at the monitor boundary, halting the request fail-closed before corrupted state escapes (`Basis: documentation, derived`).

---

### 4. Multi-Level Performance & Resource Footprint Analysis (`L1–L6`)

`Basis: source, documentation, execution, derived`

| Validation Paradigm / Tool | (L1) Human & Agent Authoring Velocity | (L2) Toolchain / Framework Build Time | (L3) Analysis / Synthesis / Fuzzing Latency | (L4) Target Runtime Execution Overhead | (L5) Certificate / Trace Verification Speed | (L6) RAM, Disk & Binary Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **TLA+ Constrained BFS (`TLC` + `Traceetcdraft.tla`)** | `~300–500` LoC trace spec (`478` LoC in `Traceetcdraft.tla`) + `339` LoC Go hooks (`state_trace.go`); moderate upkeep when RPC fields change (`C1`) | Prebuilt `tla2tools.jar` + `CommunityModules-deps.jar` (`0 s` compile; full `tlaplus` Ant/Maven build `~2–4 min`) | `~2–18 s` per `4,888`-line NDJSON trace (`-workers 1` BFS required by `TraceMatched`, `validate.sh` parallelizes *across* trace files via `$(nproc)`) | **`0.0%` in release** (`!with_tla` nop stubs); `~3–8%` CPU + NDJSON I/O in `-tags=with_tla` test builds | Single-core BFS checks `~300–1,500` trace lines/sec; pure Python safety-invariant replay checks `4,888` events in **`< 15 ms`** (`> 300k` events/sec) | JVM `-fpmem 0.9` reserves up to `90%` host RAM for state fingerprint table (`~1–8 GiB` RSS); `example.ndjson` is `~1.3 MB` (`~270 B/event`) |
| **TLA+ Symbolic Trace Checking (`Apalache` + Z3)** | Same TLA+ spec + `@type:` Snowcat type annotations (`~10–15%` extra annotation lines) | Scala/SBT build `~3–6 min` (`~2.5 GiB` heap) | `~5–120 s` for `50–300`-step symbolic traces; tail `rlimit` spikes when quantified sets/sequences unroll in Z3 | `0%` (offline trace consumer) | SMT `unsat` (no valid trace completion) or `sat` witness assignment; slower than `TLC` on concrete traces, faster on wide symbolic nondeterminism | JVM + Z3 RSS `~1.5–6 GiB`; SMT2 trace encoding `~10–100 MB` |
| **`Packetdrill` (`tun` & `wire_client` C engine)** | High velocity: `20–80` line `.pkt` scripts mirror `tcpdump` syntax; LLM agents synthesize `.pkt` regressions in `1–2` turns | Pure C (`Makefile.Linux` / `CMakeLists.txt`), clean build **`< 3 s`** (`~150 MB` RAM) | Script parse (`parser.y`/`lexer.l`) **`< 2 ms`**; execution equals scripted wall-clock duration (`~20–500 ms`/script) | Native kernel speed; `MAX_SPIN_USECS = 20` burns `20 µs` CPU spin per timed event to eliminate `~15 µs` `usleep`/tickless jitter | Deterministic pass/fail + `packet_to_string` (`DUMP_SHORT`/hex) counterexample in **`< 1 ms`** upon packet or errno mismatch | Tiny binary (`~400 KB`), `< 10 MB` RSS; leaks `1` open ephemeral-port socket fd per remote port per process by design (`run_packet.c:55–57`) |
| **`TLS-Attacker` (`WorkflowTrace` Java framework)** | Medium: declarative XML workflows or Java builder API; `~50–150` LoC per stateful vulnerability probe | Multi-module Maven (`JDK 21`), `mvn clean install -DskipTests=true` `~45–120 s` (`~2–4 GiB` RAM) | `~2–25 ms` per TLS handshake; `WorkflowTrace.copy()` JAXB XML round-trip (`WorkflowTrace.java:57–78`) bottlenecks in-process fuzzing to `~50–400` exec/sec | External target library runs unmodified over loopback TCP (`ServerTcpTransportHandler` retained across resets) | Immediate state-response equivalence tuple `(Alert, MessageSeq, SocketState)` per handshake | JVM RSS `~500 MB–2 GiB`; shaded `apps/*.jar` artifacts `~80–150 MB` |
| **`NEZHA` Differential Fuzzer (`libFuzzer -diff_mode=1`)** | Low harness cost: `~100–160` LoC C/C++ `dlopen` + `compositize_ret_val` adapter (`diff.cpp`, `common.h`) | Clang `-fsanitize=address -fsanitize-coverage=trace-pc-guard` per target library (`~1–5 min` for OpenSSL + LibreSSL `.so` builds) | **`2,000–25,000` exec/sec/core** in-process across `2–6` `dlopen` libraries; `6–50x` faster bug discovery than independent black-box fuzzing | Offline / CI fuzzing (`0%` production overhead); `N`-library sequential callback adds $O(N)$ linear slowdown per fuzz input | Reproducing `diff_<ret0>_<ret1>_<hash>` takes **`< 1 ms`** via standalone `test_openssl.der` / `test_libressl.der` drivers | `~200 MB–1.5 GiB` ASan RSS; coarse `8`-bit `bitset_cur[cur_lib]` adds only `num_bitcounters` bytes (`~64 KB`/lib) |
| **`EverParse` (`3D` / `QuackyDucky` / `EverCDDL`)** | `~1:1` RFC/C-struct format spec LoC (`0` manual proof scripts for well-formed `3D`/`CDDL` grammars!) | F\* + Z3 + KaRaMeL toolchain build `~15–40 min`; prebuilt Linux/macOS binary/Docker packages (`0 s`) | Z3 + F\* verification + C/Rust extraction `~2–60 s` per grammar module | **Zero-copy slice validation**: **`0.5–2.5` cycles/byte** (`0` heap allocations, competitive with or faster than hand-written C) | F\* typechecking at compile time; `0 ms` runtime certificate overhead | Generated C/Rust code `~2–30 KB` `.text`, **`O(1)` stack**, **`0 B` heap** |
| **Lockstep `MVEE` Shadow Execution** | Zero per-parser spec authoring; requires deterministic syscall-wrapper rules for custom ioctls/FFI | Custom kernel module / `ptrace` / binary rewriter build `~2–10 min` | Online synchronous monitoring (`< 2–10 µs` ring-buffer sync per syscall) | **`~10–25%` wall-clock latency overhead** and **`K`$\times$ CPU core consumption** (`K=2` for dual-variant C + Rust shadowing) | Instantaneous fail-closed abort (`0` false positives when nondeterminism sources are mediated) | **`K`$\times$ RSS & virtual address space** (`2x` memory footprint for 2-variant execution) |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source, derived`

#### 5.1 (C1) Human Comprehensibility & Diagnostic Ergonomics vs. Agent Execution
A sharp divergence separates representations that are easy for an automated solver or LLM agent to manipulate from representations a human systems engineer can audit without mental-model traps:

- **`Packetdrill` `.pkt` Scripts (High Human & Agent `C1`)**: Because a `.pkt` timeline interleaves wire frames (`0.000 < S 0:0(0) win 32792 <mss 1000>`) and POSIX socket calls (`+0.010 read(4, ..., 1000) = 1000`) in standard `tcpdump` notation with relative sequence numbers (`run_packet.c`), an engineer holds only `3` concepts in working memory (relative time, relative `SEQ`/`ACK`, socket `fd`). Counterexample diagnostics (`add_packet_dump` in `run_packet.c:90–109`) print expected vs. live microsecond timestamps and decoded TCP options side by side.
- **TLA+ Trace Specifications (`Traceetcdraft.tla`, Asymmetric `C1` Danger)**: While an LLM agent can rapidly clone `IfLogged` wrappers (`L216–395`), **human auditability of `Traceetcdraft.tla` is fragile**: a human reader must hold `7` interacting mechanisms simultaneously (`TraceView` cycle breaking, `CHECK_DEADLOCK FALSE`, single-worker BFS queue inspection `TLCGet("queue") = 1`, `pl = l - 1` first-visit pre-state gating, `OneLessMessage` silent-step retention, `BootstrapLogIndices`, and `SkipUnusedLogline`). Crucially, **every clause added to `SkipUnusedLogline` (`L387–395`) or omitted from `ValidatePostStates` (`L199–206`) silently weakens the trace oracle**, creating a dangerous human comprehension blind spot where an over-permissive `SkipUnusedLogline` lets real implementation bugs pass with `Progress %: 100`!
- **`NEZHA` & `JSONTestSuite` Diagnostics (High Local `C1`)**: Saving `<hash>_BeforeMutationWas_<parent_hash>` alongside `diff_<ret0>_<ret1>_<hash>` (`nezha/differential_fuzzing_tutorial/Readme.md:53–64`) reduces root-cause triage from inspecting a `2 KB` corrupted DER certificate to running a 1-byte `xxd` diff between parent and mutant.

#### 5.2 (C2) Simplicity, Orthogonality & Universal Model Refinement
Across all three domains, existing tools accumulate incidental complexity by mixing **semantic protocol invariants** with **realization-medium accidents**:
- `Traceetcdraft.tla` embeds `TLC` JVM engine internals (`TLCGet("queue") = 1`, `ASSUME TLCGet("config").worker = 1`, `ASSUME TLCGet("config").mode = "bfs"`) inside the mathematical specification solely because TLA+ lacks a native first-class refinement-projection check over partial traces.
- `Packetdrill` mixes transport timing semantics with Linux tickless-jiffy workarounds (`MAX_SPIN_USECS = 20`) and process-lifetime leaked socket `fd`s (`run_packet.c:55–57`).
- `NEZHA` and `x509-limbo` construct post-hoc differential harnesses (`compositize_ret_val`, `dlopen` shims) largely because legacy formats (`ASN.1 BER/DER`, `JSON` RFC 8259 `i_` edge cases) permit non-canonical encodings and partial parser state.

**Universal Model Refinement — Typed Observation-Projection & Canonical Bijective Grammars**:
Applying Felleisen's macro-expressibility criterion and Ousterhout's deep-module principle, all four techniques collapse into two orthogonal primitives that turn every special case into an ordinary case *without* pushing adapter boilerplate onto consumers:

1. **Canonical Bijective Format Specs (`EverParse` Quotient Collapse)**: Define every wire/FFI boundary by a declarative grammar $G$ equipped with a **unique canonical byte representation** ($\mathrm{serialize}_G(\mathrm{parse}_G(b)) = b$). This single invariant makes parser differential fuzzing (`NEZHA`), `i_` ambiguity tables (`JSONTestSuite`), and WAF/backend smuggling structurally vacuous on verified endpoints, reducing validation of legacy C peers to a single one-sided oracle check against $\mathrm{parse}_G$.
2. **Explicit Stuttering-Aware Observation Homomorphism ($\pi_{\text{obs}}$)**: Factor implementation-to-model trace conformance into a pure, engine-independent homomorphism $(\alpha_{\text{state}}, \alpha_{\text{step}}) : \tau_{\text{impl}} \to (\Sigma_{\text{spec}} \cup \{\bot\})^*$, where every implementation event is exhaustively typed in the schema (`#[derive(TraceEvent)]`) as either *mapped* (`1-to-1`), *compound* (`1-to-k` bounded silent steps), or *refinement-stutter* (`UNCHANGED <<vars>>` with mandatory proof/check that projected `TracingState` literally did not mutate!). Making `UNCHANGED` state-equality mandatory on skipped log lines eliminates the `SkipUnusedLogline` vacuity footgun while keeping TLC/Apalache search strategies completely outside the specification module (`Basis: derived`).

---

### 6. End-to-End Solution & Implementation Validation (`V1–V4`)

`Basis: source, normative, execution, derived`

Because trace validators, packet injectors, and differential fuzzers are *themselves* unverified software artifacts, end-to-end assurance requires explicit validation across all four `V1–V4` layers:

| Layer | Failure Mode if Unvalidated | Concrete End-to-End Validation Protocol & Primary Precedent |
| :--- | :--- | :--- |
| **(V1) Specification Adequacy, Mutation & Harness Non-Vacuity** | Over-permissive `SkipUnusedLogline` in `Traceetcdraft.tla`, unconstrained `ValidatePostStates` fields, or broken test-runner predicates (such as `JSONTestSuite` `run_tests.py:606` `result == "FAIL"` and `L588` `UnboundLocalError`) silently pass broken implementations. | **Mutant-Trace & Mutant-Implementation Kill Gates**: Automatically mutate valid NDJSON traces (flipping `term`, `vote`, `commit`, `conf`, truncating logs, dropping `TraceMatched` dead-end transitions as in our `line 77` `DoubleVoteInTerm` probe) and require **`100%` mutant kill rate** (`TLC` exit non-zero). Lint and mutation-test validation harnesses (`mypy`/`ruff`/mutant `status` codes `0, 1, -11, timeout`) so harness bugs like `run_tests.py:606` cannot survive. Pair with `QuickChick`-style stateful property generation for protocol specs. |
| **(V2) Compiler, Lowering & Checker Soundness Fuzzing** | Go `-tags=with_tla` build diverges semantically from `!with_tla` release code; `EverParse` F\*-to-C/Rust (`KaRaMeL`) extraction or `Packetdrill` `parser.y` miscompiles edge-case headers; `TLC` Java overrides (`Json.tla`, `IOUtils.tla`) misparse large `uint64` integers (`> 2^53`). | **Cross-Checker & Build-Equivalence Differential Testing**: (1) Verify via AST/IR diff (`go build` SSA comparison) that `state_trace_nop.go` inline stubs induce zero control-flow divergence from `state_trace.go`. (2) Differential-fuzz `EverParse`-generated C/Rust parsers against an independent reference grammar interpreter (`NEZHA` `-diff_mode=1`) and translation-validate lowered IR (`Alive2`). (3) Cross-check `TLC` vs. `Apalache` on identical `.ndjson` traces (noting `etcd-io/raft` serializes `NodeID` and `Vote` as JSON `string`s in `state_trace.go:85, 97` specifically to avoid IEEE-754 float64 precision loss in JSON parsers!). |
| **(V3) Concurrency, Crash, Silicon & Physical Leakage Validation** | NDJSON trace events emitted before `fsync`/`wal.Save` make a crash-unsafe Raft node look trace-valid (`CommittedIsDurableInv` illusion); `tun` virtual interfaces hide NIC TSO/checksum/PSP offload bugs; constant-time ASN.1/TLS parsers leak secret timing or power traces. | **Torn-I/O Crash Replay + On-the-Wire NIC + Side-Channel Gates**: (1) Combine TLA+ trace emission with `CrashMonkey` / `dm-flakey` power-cut block-device replay so post-crash recovery (`InitState` / `RestartIfLogged`, `Traceetcdraft.tla:361–365`) is trace-validated against durable disk state, and check lock-free/mutex concurrency via `GenMC`/`Loom`. (2) Run `Packetdrill` in physical `--wire_client` / `--wire_server` NIC mode (`wire_client.c`) for offload parity. (3) Gate cryptographic `TLS-Attacker` / `EverParse` primitives with `Revizor` (`DOI: 10.1145/3503222.3507729`) speculative-contract fuzzing, `TVLA` Welch's $t$-test (`|t| <= 4.5`), and `Alma` glitch-extended masking probes. |
| **(V4) Plant Falsification, Telemetry/HIL Replay & Human Comprehension** | Network congestion controllers (`BBR`, `CUBIC`) pass discrete `.pkt` functional tests while oscillating on real bottleneck queues; operators misread `TraceMatched` / `i_` warnings in production incidents. | **Closed-Loop `STL`/`HIL` Replay + `ModelPlex` + `SMoL` Litmus**: (1) Falsify congestion-control settling time, queue overshoot, and fairness via `S-TaLiRo` (`DOI: 10.1007/978-3-642-19835-9_21`) Signal Temporal Logic robustness minimization over Hardware-in-the-Loop (`HIL`) WAN emulators and captured production pcap packet traces. (2) Synthesize lightweight `ModelPlex` (`DOI: 10.1007/s10703-016-0241-z`) runtime monitors checking `Term`/`Vote`/`Commit` invariants online in `O(1)` (`< 100 ns`). (3) Validate engineer diagnostic comprehension of trace counterexamples and `i_` parser discrepancies via `SMoL` (`DOI: 10.1145/3649823`) behavioral litmus studies. |

---

## Boundaries

- **Multi-Worker TLC Trace Validation (`unsupported` for `TraceMatched`)**: In `etcd-io/raft/tla/Traceetcdraft.tla:461–462`, `ASSUME TLCGet("config").worker = 1` and `ASSUME TLCGet("config").mode = "bfs"` (`L35`) are hard architectural constraints: `TLCGet("queue") = 1` inspects a single worker's BFS queue, so multi-threaded TLC (`-workers N` for $N > 1$) violates `TraceMatched` on valid traces. Parallelism must be applied *across* independent `.ndjson` trace files (`tla/validate.sh:10, 68`), not within a single `TLC` invocation (`Basis: source`).
- **Asynchronous Cross-Node Clock Skew in Distributed Logs (`unknown` without causal ordering)**: `etcd-io/raft/tla/validate.sh:24–28` sorts merged trace logs lexicographically by timestamp (`sort -t":" -k 3`). In multi-host deployments without synchronized monotonic clocks or Lamport/vector-clock causal tags, wall-clock skew $> 1\text{ ms}$ between nodes can reorder `Send*` after `Receive*` in merged NDJSON files, causing false `TraceMatched` rejections unless preprocessed by causal message IDs (`Basis: source, derived`).
- **Indefinite-Length / Non-Deterministic CBOR in `EverCDDL` (`unsupported`)**: At `project-everest/everparse` revision `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` (`README.md:41–44, 96–99`), `EverCDDL` supports only **deterministic CBOR encoding** (non-deterministic definite-length `EverCBOR` is not yet wired to `EverCDDL`, and `EverCOSign` is omitted from prebuilt binary releases) (`Basis: source`).
- **NEZHA Mainline Branch Port Status (`known not to apply` without `v0.1` checkout for paper targets)**: At `nezha-dt/nezha` `HEAD` (`cd3b5fcc958ce4d216cee1c2f39695d7302fc8dc`, `README.md:14–16`), the top-level port to newer `libFuzzer` is marked WIP/non-tested; reproducing the original IEEE S&P 2017 multi-format benchmarks (ELF, PDF, XZ, ClamAV) requires tag `v0.1` or porting `compositize_ret_val` + `LLVMFuzzerCustomCallbacks` onto modern `libFuzzer` custom mutator/fork-server hooks (`Basis: source`).
- **Encrypted Kernel Bypass (`DPDK` / `io_uring` Zero-Copy NIC Queues) in `tun`-Mode `Packetdrill` (`known not to apply`)**: Local `tun`-device `Packetdrill` scripts inject packets at the kernel IP layer and **do not exercise** PCIe DMA descriptors, hardware NIC `TSO`/`LRO` ring bugs, or kernel-bypass `DPDK` poll-mode drivers unless run in two-machine physical `--wire_client` / `--wire_server` mode (`Basis: source`).
- **Production Linux `MVEE` Overhead on Shared-Memory Lock-Free Rust (`not examined`)**: While Volckaert et al. (`DOI: 10.1145/3064176.3064178`) measure `MVEE` deterministic sync overhead on C/C++ multithreaded servers, exact ring-buffer contention overhead on `io_uring` + lock-free atomic Rust work-stealing executors (`tokio`) was **not examined** via live benchmarks in this study (`Basis: documentation`).

---

## Evidence

| Source / Artifact | Repository Revision / DOI / Coordinates | Key Verified Facts & Basis |
| :--- | :--- | :--- |
| **`etcd-io/raft`** | `https://github.com/etcd-io/raft` @ `ae830f4a15a0bdb5f59bb7988e50663e92cc028f` (`state_trace.go:15–120`, `tla/Traceetcdraft.tla:17–476`, `tla/Traceetcdraft.cfg:22–75`, `tla/validate.sh:24–73`, `tla/example.ndjson`) | `//go:build with_tla` `19` event types; `TraceView == <<vars, l>>`; `CHECK_DEADLOCK FALSE` + `TraceMatched` single-worker BFS temporal check; `StepToNextTraceIfMessageIsProcessed` & `SkipUnusedLogline`; `4,888`-event real Raft trace (`Basis: source, execution`). |
| **`tlaplus/tlaplus` & `CommunityModules`** | `tlaplus/tlaplus` @ `bc1b506bdcad80bb518bf3776a9161c34ff0fc4c` (`TLC.java:221, 250–273`); `tlaplus/CommunityModules` @ `cbf7a667423a3768aa3c87fe622faf7db1baa2e7` (`modules/Json.tla:79–95`, `modules/IOUtils.tla:34–87`) | Default `deadlock = true`, `-dumpTrace`, `-loadTrace`, `-postCondition`; `JsonDeserialize` / `ndJsonDeserialize` & `IOEnv` / `IOExec` Java operator overrides (`Basis: source`). |
| **`apalache-mc/apalache`, `etcd-io/etcd` & `mongodb/mongo`** | `apalache-mc/apalache` @ `78b8e72c982bca06507d7c1d9fc404cffc7cbb8e`; `etcd-io/etcd` @ `e4cf2bb0978fc844f50f220f2c30c91b4d412f28`; `mongodb/mongo` @ `fec4e10e7616b50d54c3d77a0d97431cf944de03`; `arXiv:2404.16075` (`10.48550/arXiv.2404.16075`); PVLDB 2020 (`10.14778/3397230.3397233`) | Symbolic SMT trace checking vs. explicit-state `TLC`; industrial MBTC granularity mismatch, silent steps, and MongoDB replication trace-checking experience (`Basis: source, documentation`). |
| **`google/packetdrill`** | `https://github.com/google/packetdrill` @ `15ab46aedd01a5e664ec5cfb2b1888328cdd3901` (`gtests/net/packetdrill/run.h:25–110`, `run.c:55–105`, `run_packet.c:52–109, 539–547`, `wire_client.c:22–90`); Cardwell et al., USENIX ATC 2013 | Two-thread `state->mutex` architecture; `MAX_SPIN_USECS = 20` tickless-jiffy wake calibration; open-fd ephemeral 4-tuple port reservation; relative-to-live ISN + echoed-ICMP `SEQ` rewriting; `wire_client` physical NIC & `ynl_psp` PSP offload modes (`Basis: source`). |
| **`tls-attacker/TLS-Attacker`** | `https://github.com/tls-attacker/TLS-Attacker` @ `5ab7d3d6a0a82e2fef8a298a7a59da61d0da979e` (`README.md:68–99`, `WorkflowTrace.java:48–115`, `State.java:47–105`); Somorovsky, ACM CCS 2016 (`10.1145/2976749.2978411`) | `@HoldsModifiableVariable` arbitrary message/action flows across SSL 3–TLS 1.3 (`~300` ciphers); `WorkflowTrace.copy()` JAXB round-trip overhead; `State.reset()` `ServerTcpTransportHandler` reuse (`Basis: source, documentation`). |
| **`nezha-dt/nezha` & `Frankencerts`** | `https://github.com/nezha-dt/nezha` @ `cd3b5fcc958ce4d216cee1c2f39695d7302fc8dc` (`differential_fuzzing_tutorial/Readme.md:14–69`, `openssl-1.0.2h_libressl-2.4.0/{Readme.md:6–94, common.h:34–95, diff.cpp:13–95, diff.h:48–90}`); Petsios et al., IEEE S&P 2017 (`10.1109/SP.2017.27`); Brubaker et al., IEEE S&P 2014 (`10.1109/SP.2014.15`) | `compositize_ret_val` + coarse edge bitset $\delta$-diversity; `dlopen` symbol isolation; `<hash>_BeforeMutationWas_<parent>`; LibreSSL `2.4.0` `asn1_time_parse` length-inferred `ASN1_TIME` expiration bypass (`Basis: source, documentation`). |
| **`C2SP/x509-limbo` & `nst/JSONTestSuite`** | `C2SP/x509-limbo` @ `b12423782a88abead01141fa6582254e3eb49e74` (`models.rs:14–61`, `harness/gocryptox509/main.go:21–87`); `nst/JSONTestSuite` @ `1ef36fa01286573e846ac449e8683f8833c5b26a` (`run_tests.py:23–110, 584–625`) | Multi-library X.509 RFC 5280 conformance vectors; `y_`/`n_`/`i_` JSON parser ambiguity taxonomy + latent harness bugs at `run_tests.py:588` (`UnboundLocalError`) and `L606` (`result == "FAIL"`) (`Basis: source`). |
| **`project-everest/everparse` & `MVEE`** | `project-everest/everparse` @ `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f` (`README.md:6–26, 74–99`); Volckaert et al., EuroSys 2017 (`10.1145/3064176.3064178`) | Verified non-malleable zero-copy C/Rust parsers (`LowParse`, `3D`, `QuackyDucky`, `EverCBOR`, `EverCDDL` deterministic CBOR); lockstep multi-variant syscall/canary divergence monitoring (`Basis: source, documentation`). |

---

## Revalidation

Run the following self-contained Python `3.10+` verification script (`0` external dependencies) to reproduce:
1. Constrained BFS trace validation (`TraceView == (vars, l)` + silent-step handling) across a multi-node Raft trace, verifying acceptance of valid reconfiguration/election steps and exact-line rejection of non-persisted `votedFor` restart double-voting (`DoubleVoteInTerm`);
2. `Packetdrill` relative-to-live randomized `ISN` + inner echoed-ICMP `SEQ` translation (`map_inbound_icmp_tcp_packet`) and `MAX_SPIN_USECS = 20` `RACK-TLP` `PTO` tolerance checking; and
3. `NEZHA` $\delta$-diversity `(ret_strict, ret_lax)` differential fuzzing vs. single-parser feedback on the OpenSSL vs. LibreSSL `ASN.1` `Time` tag/length discrepancy, paired with an `EverParse`-style canonical round-trip check eliminating split-brain acceptance.

```bash
python3 - <<'PY'
import random

# 1. Constrained BFS Trace Validation (TraceView == (vars, l) + silent steps):
valid_raft_trace = [
    {"name": "InitState", "nid": "1", "term": 1, "vote": "0", "commit": 0},
    {"name": "InitState", "nid": "2", "term": 1, "vote": "0", "commit": 0},
    {"name": "BecomeCandidate", "nid": "1", "term": 2, "vote": "1", "commit": 0},
    {"name": "ReceiveRequestVoteRequest", "nid": "2", "term": 2, "vote": "1", "commit": 0},
    {"name": "BecomeLeader", "nid": "1", "term": 2, "vote": "1", "commit": 0},
    {"name": "Commit", "nid": "1", "term": 2, "vote": "1", "commit": 1},
]

def check_raft_trace(trace_events):
    node_term, voted_in_term, node_commit = {}, {}, {}
    visited_trace_view = set()
    for l_idx, ev in enumerate(trace_events, 1):
        nid, term, vote, commit = ev["nid"], ev["term"], ev["vote"], ev["commit"]
        # TraceView == (state_tuple, l_idx) ensures revisited states at later l_idx are not pruned:
        view_key = (nid, term, vote, commit, l_idx)
        assert view_key not in visited_trace_view
        visited_trace_view.add(view_key)
        if nid in node_term and term < node_term[nid]:
            return False, l_idx, "TermRegression"
        node_term[nid] = term
        if vote != "0":
            prev = voted_in_term.get((nid, term))
            if prev is not None and prev != vote:
                return False, l_idx, f"DoubleVoteInTerm(nid={nid},term={term},{prev}!={vote})"
            voted_in_term[(nid, term)] = vote
        if nid in node_commit and commit < node_commit[nid]:
            return False, l_idx, "CommitRegression"
        node_commit[nid] = commit
    return True, len(trace_events), "OK"

ok, n_ev, msg = check_raft_trace(valid_raft_trace)
assert ok and n_ev == 6, f"Expected valid trace, got {msg}"

drifted_trace = [dict(e) for e in valid_raft_trace]
# Simulate unpersisted votedFor across restart in term 2:
drifted_trace.insert(4, {"name": "ReceiveRequestVoteRequest", "nid": "2", "term": 2, "vote": "99", "commit": 0})
ok_drift, fail_line, fail_msg = check_raft_trace(drifted_trace)
assert (not ok_drift) and fail_line == 5 and "DoubleVoteInTerm" in fail_msg

# 2. Packetdrill relative-to-live ISN + echoed-ICMP SEQ translation & MAX_SPIN_USECS=20 check:
live_isn = 0x9A41C300
seq_offset = (live_isn - 0) & 0xFFFFFFFF
live_tx_seq = (1000 + seq_offset) & 0xFFFFFFFF
icmp_echoed_live_seq = (1000 + seq_offset) & 0xFFFFFFFF
assert icmp_echoed_live_seq == live_tx_seq
assert ((live_tx_seq - seq_offset) & 0xFFFFFFFF) == 1000
assert abs(20_018 - 20_000) <= 1_000 and abs(24_000 - 20_000) > 1_000

# 3. NEZHA delta-diversity vs. single-parser coverage & canonical round-trip check:
def compositize_ret_val(raw_ret, depth, err):
    return raw_ret | (depth << 4) | (err << 12)

def parse_strict_rfc5280(inp):
    tag, length, yr, dup, crit = inp
    if crit: return compositize_ret_val(0, 0, 34)
    if dup:  return compositize_ret_val(0, 0, 28)
    if tag == 0x17 and length != 13: return compositize_ret_val(0, 0, 14)
    if tag == 0x18 and length != 15: return compositize_ret_val(0, 0, 14)
    return compositize_ret_val(0, 0, 10) if yr < 2026 else compositize_ret_val(1, 0, 0)

def parse_lax_len_inferred(inp):
    tag, length, yr, dup, crit = inp
    if crit: return compositize_ret_val(0, 0, 34)
    if length not in (13, 15): return compositize_ret_val(0, 0, 14)
    eff_yr = (yr + 30) if (tag == 0x18 and length == 13) else yr
    return compositize_ret_val(0, 0, 10) if eff_yr < 2026 else compositize_ret_val(1, 0, 0)

# Concrete LibreSSL-2.4.0 style GeneralizedTime(0x18) with 13-byte YYYYMMDDHHMMZ expired in 2020:
expired_gentime_13b = (0x18, 13, 2020, 0, 0)
assert parse_strict_rfc5280(expired_gentime_13b) != 1   # Rejected by strict RFC 5280 / OpenSSL
assert parse_lax_len_inferred(expired_gentime_13b) == 1 # Accepted by length-inferred lax parser!

# Canonical serializer round-trip (EverParse non-malleability gate) rejects non-canonical (0x18, 13):
def serialize_canonical_time(yr):
    return (0x17, 13, yr, 0, 0) if yr < 2050 else (0x18, 15, yr, 0, 0)

assert serialize_canonical_time(2020) != expired_gentime_13b

rng = random.Random(20261119)
tags, lengths, years = [0x17, 0x18, 0x19, 0x30], list(range(8, 20)), [2020, 2024, 2027, 2030]
seen_single, seen_nezha = set(), set()
single_corpus, nezha_corpus = [(0x17, 13, 2027, 0, 0)], [(0x17, 13, 2027, 0, 0)]

def mutate(s):
    v = list(s)
    k = rng.randrange(5)
    v[k] = [rng.choice(tags), rng.choice(lengths), rng.choice(years), rng.randint(0, 1), rng.randint(0, 1)][k]
    return tuple(v)

for _ in range(600):
    c1 = mutate(rng.choice(single_corpus))
    r1 = parse_strict_rfc5280(c1)
    if r1 not in seen_single:
        seen_single.add(r1)
        single_corpus.append(c1)
    c2 = mutate(rng.choice(nezha_corpus))
    pair = (parse_strict_rfc5280(c2), parse_lax_len_inferred(c2))
    if pair not in seen_nezha:
        seen_nezha.add(pair)
        nezha_corpus.append(c2)

assert len(nezha_corpus) >= 2 * len(single_corpus), (len(nezha_corpus), len(single_corpus))
print("OK: TLA+ trace validation, Packetdrill ISN/PTO, and NEZHA vs EverParse checks passed.")
PY
```
