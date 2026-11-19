# X.509 PKI Path Validation, ASN.1 Differentials, Verified TLS 1.3 State Machines, and DNS/DNSSEC Validation Complexity

## Summary

Internet naming (`DNS`/`DNSSEC`), public-key infrastructure (`X.509`), and transport authentication (`TLS 1.3`) share a recurring architectural failure mode: **underspecified or permissive verification boundaries coupled with combinatorial graph/cryptographic work amplification**. Primary-source inspection across production verifiers, formal models, and differential test corpora yields five concrete engineering invariants:

1. **ASN.1 DER/BER Parser Differentials & RFC 5280 Combinatorial Budgets**: Permissive BER acceptance (indefinite lengths, non-minimal length/integer encodings, non-canonical `BOOLEAN` `0x01`, trailing bytes) creates signature-coverage and policy-interpretation splits across X.509 validators (`rustls/webpki` enforces strict canonical DER at `src/der.rs`). Beyond syntax, RFC 5280 certificate graphs are directed multigraphs with cross-signing cycles (`CVE-2024-0567`, "chain of pain") and $O(|N| \times |C|)$ Name Constraints cross-products. Production verifiers defend against exponential path-building and quadratic constraint DoS using distinct explicit budgets—creating live acceptance differentials: `rustls/webpki` enforces `Budget { signatures: 100, build_chain_calls: 200_000, name_constraint_comparisons: 250_000 }` (`src/verify_cert.rs:352-405`), whereas `OpenSSL` enforces `NAME_CHECK_MAX = 1 << 20` (`1,048,576`) per certificate (`crypto/x509/v3_ncons.c:252-297`).
2. **Adversarial Differential Testing (`Frankencerts`, `x509-limbo`) vs. Policy/Mechanism Isolation (`Hammurabi`)**: Recombining real X.509 extensions and flipping criticality flags (`sumanj/frankencert`, Brubaker et al., IEEE S&P 2014) exposed 208 cross-library discrepancies (including X.509 v1 unauthorized-CA bypasses), while `C2SP/x509-limbo` codifies cross-signed cycles and pathological chains across modern validators. `Hammurabi` (Larisch et al., ACM CCS 2022) decouples untrusted ASN.1 parsing from declarative logic-programming policy rules, reproducing Chrome/Firefox decisions over >10M Certificate Transparency chains and synthesizing differential witnesses via logic-rule comparison.
3. **Compile-Time Typestate vs. Mechanized Region/Game Proofs in TLS 1.3 (`rustls` & `miTLS`)**: TLS 1.3 eliminates RSA key-transport and downgrade surfaces via an explicit HKDF-Extract/Expand key schedule across disjoint encryption epochs (0-RTT early data, handshake, 1-RTT traffic, post-handshake key updates). `rustls/rustls` enforces key-schedule monotonicity at compile time via 12 affine typestate structs (`KeyScheduleEarly*` -> `KeySchedulePreHandshake` -> `KeyScheduleHandshakeStart` -> `KeyScheduleHandshake` -> `KeyScheduleTraffic*`, `rustls/src/tls13/key_schedule.rs`) and forbids 0-RTT completely whenever stateless session tickets are enabled (`config.max_early_data_size > 0 && config.ticketer.is_none()`, `server/tls13.rs:709`), using bounded trial-decryption skipping (`ExpectAndSkipRejectedEarlyData`) on rejection. `miTLS` (`Bhargavan et al., IEEE S&P 2017`; `project-everest/mitls-fstar`) mechanizes multi-epoch AEAD security reductions via disjoint F* HyperStack memory regions (`epoch_region_inv`, `epochs_inv`) and monotonic epoch counters (`m_rref ... increases`), though direct inspection of `MiTLS.Epochs.fst` reveals `--admit_smt_queries true` (`L32`) and an `assume False` (`L225`) in later epoch-framing glue—underscoring why proof-audit boundaries must be checked at the exact revision.
4. **DNS Multi-Feature Semantic Bugs (`SCALE`) and Bailiwick Containment**: Single-feature RFC tests miss bugs at the intersection of `DNAME` (`RFC 6672`), `CNAME`, wildcards (`*`), and zone-cut bailiwick rules. Jointly synthesizing zone files and queries from an executable RFC model (`SCALE`/`Ferret`, Kakarla et al., NSDI 2022) triggered cross-implementation divergences in 62% of generated cases and uncovered 30 unique bugs (including `CVE-2021-25215` in BIND 9). Recursive resolvers enforce bailiwick scrubbing (`NLnetLabs/unbound` `iterator/iter_scrub.c`, `pkt_sub`/`dname_subdomain_c`) to strip out-of-zone glue and cap `CNAME`/`DNAME` alias chains against cache poisoning.
5. **DNSSEC Algorithmic Complexity Attacks (`KeyTrap` `CVE-2023-50387` & `NSEC3` `CVE-2023-50868`)**: Because RFC 4034 Appendix B defines the 16-bit DNSSEC Key Tag as an unkeyed linear 1's-complement checksum, an attacker can trivially construct $K$ distinct `DNSKEY` records sharing one key tag in $O(1)$ per key and pair them with $S$ `RRSIG`s to force $K \times S$ signature verifications—compounded by `NSEC3` SHA-1 hash iteration loops (`(iterations + 1)` hashes per label in closest-encloser proofs). Post-KeyTrap patches bound this blast radius asymmetrically across resolvers: `Unbound` enforces `MAX_VALIDATE_RRSIGS = 8`, `MAX_VALIDATE_NSECS = 8`, `MAX_TAG_MATCHES = 256`, `val_validation_attempts = 32`, `MAX_NSEC3_CALCULATIONS = 8`, and `val_nsec3_key_iterations = "1024 150 2048 150 4096 150"`; `BIND 9` enforces `DEFAULT_MAX_VALIDATIONS = 16`, `DEFAULT_MAX_VALIDATION_FAILURES = 1`, `DS_DNSKEY_COMBINATIONS_PER_VALIDATION = 2`, and `DNS_NSEC3_MAXITERATIONS = 50U` (compared against RFC 9276's recommendation of `0` iterations).

## Applicability

This report covers the interaction of parsing, path/policy validation, protocol state machines, and denial-of-service resource bounding across the eight pinned open-source repositories and five peer-reviewed papers listed in `REPORT.json`:

- **X.509 / PKI Parsing & Path Validation**: Direct source inspection of `rustls/webpki` (`f6dcb14b822784c6fc23556d549e2683cc7328a1`), `openssl/openssl` (`fc355e65068efe333e0764db1c32c302af8aa7fa`), `sumanj/frankencert` (`5bbaae85cab35882dec1672ef037a42e29180b40`), and `C2SP/x509-limbo` (`b12423782a88abead01141fa6582254e3eb49e74`), framed against RFC 5280, Frankencerts (IEEE S&P 2014), and Hammurabi (ACM CCS 2022). Applies to TLS Web PKI server/client certificate validation (`EndEntityCert` / `X509_verify_cert`); S/MIME, code-signing, and private enterprise PKIs with custom EKU/policy-mapping extensions may diverge in extension enforcement.
- **TLS 1.3 Key Schedules, Multi-Epoch Records, and 0-RTT**: Direct source inspection of `rustls/rustls` (`836e411eccaf7331f4c289aabef0de32474de3b8`) and `project-everest/mitls-fstar` (`9a75fa8c46e50897b1f43002885d25a34dfa929a`), grounded in RFC 8446 / RFC 9846 and Bhargavan et al. (IEEE S&P 2017). Applies to TLS 1.3 over TCP and QUIC (noting `EndOfEarlyData` omission under RFC 9001 §8.3); TLS 1.2 renegotiation and CBC/RSA-PKCS#1v1.5 padding-oracle mechanics are outside the core scope.
- **DNS Resolution, Bailiwick Semantics, and DNSSEC Validation**: Direct source inspection of `NLnetLabs/unbound` (`5d7ef54e1f45e1ff5a1b83057987a33883784c93`) and `isc-projects/bind9` (`f13d302fb694db688dc50ea184bda28e9531c491`), grounded in RFC 2181, RFC 4034/4035, RFC 5155, RFC 6672, RFC 9276, SCALE (NSDI 2022), and KeyTrap (CCS 2024, `CVE-2023-50387`, `CVE-2023-50868`). Applies to validating recursive resolvers and authoritative zone semantics; DNS-over-HTTPS/TLS transport framing is not examined.

Executable probes quantify byte-level DER/BER splits, DAG/Name-Constraints budgets, RFC 4034 key-tag collisions, and NSEC3 hashing amplification independently of host OS networking.

## Findings

### 1. X.509 ASN.1 DER/BER Differentials, RFC 5280 Graph Complexity, and Name Constraints

Basis: normative + source + execution

#### 1.1 ASN.1 DER vs. BER Canonicalization Differentials

X.509 certificates (`RFC 5280` §4.1) are signed over the exact byte encoding of `TBSCertificate` (`ASN.1 DER`, ITU-T X.690). Whenever one validator enforces strict canonical DER while another accepts permissive BER encodings, attackers can craft ambiguous structures that pass signature verification under one parser while presenting different fields (or different `cA`/`critical` booleans, serial numbers, or trailing attributes) to another—a classic parser-differential root cause in certificate-transparency auditors, proxy terminators, and TLS clients.

Direct inspection of `rustls/webpki/src/der.rs` (`f6dcb14b822784c6fc23556d549e2683cc7328a1`, lines 40–255) establishes the concrete invariants enforced by a strict zero-copy DER parser (`untrusted::Reader`):
- **Exhaustive consumption (`der.rs:40-42`)**: `read_all` wraps `input.read_all(Error::TrailingData(T::TYPE_ID), T::from_der)`, unconditionally rejecting trailing bytes after any DER object.
- **High-tag-number rejection (`der.rs:146-149`)**: Any tag byte with `(tag & 0x1F) == 0x1F` returns `Err(Error::BadDer)`.
- **Minimal canonical definite lengths (`der.rs:154-199`)**:
  - Indefinite-length BER (`0x80`) falls into `_ => Err(Error::BadDer)`.
  - 1-byte long form (`0x81`) rejects `length_byte < 0x80`; 2-byte (`0x82`) rejects `<= 0xFF`; 3-byte (`0x83`) rejects `<= 0xFFFF`; 4-byte (`0x84`) rejects `<= 0xFFFFFF`; >4 length octets rejected.
  - Caller-supplied `size_limit` (default `TWO_BYTE_DER_SIZE = 0xFFFF` matching upstream `ring`, `der.rs:255`) bounds single TLV sizes against memory exhaustion.

Executing a comparative probe matching `webpki/src/der.rs` strict DER rules against a permissive BER decoder (`Basis: execution`, Probe 1 in **Evidence**) isolates five canonical divergence classes:

| Wire Specimen (Hex) | Structural Defect | Strict DER (`webpki`) | Permissive BER | Security Impact of Differential |
| :--- | :--- | :--- | :--- | :--- |
| `02 01 05` | Canonical `INTEGER 5` | Accept | Accept | Baseline agreement |
| `02 81 01 05` | Non-minimal long-form length (`0x81 0x01`) | **Reject** (`BadDer`) | Accept | Enables signature-malleability or CT/verifier split |
| `30 80 02 01 05 00 00` | Indefinite-length constructed `SEQUENCE` | **Reject** (`BadDer`) | Accept | Allows smuggling unparsed EOC-terminated fields |
| `01 01 01` | Non-canonical `BOOLEAN` (`0x01` instead of `0xFF`) | **Reject** (`BadDer`) | Accept (`TRUE`) | `BasicConstraints.cA` interpreted as `TRUE` by BER parser, rejected or misread by strict DER parser |
| `02 02 00 05` | Non-minimal `INTEGER` (redundant leading `0x00`) | **Reject** (`BadDer`) | Accept (`5`) | Serial-number revocation-list (`CRL`/`OCSP`) lookup bypass if raw bytes vs. normalized integer compared |
| `30 00 DE AD` | Trailing garbage after `SEQUENCE` | **Reject** (`TrailingData`) | Accept (ignores 2 bytes) | Signature-wrapper smuggling when outer parser skips tail |

#### 1.2 RFC 5280 DAG Path-Building Cycles and Exponential Blowup

A common misconception is that X.509 trust chains are simple linked lists (`Leaf -> ICA -> Root`). In deployed Web PKI, cross-signing (multiple certificates sharing the same `Subject` DN and/or public key, signed by different roots or mutually cross-signing each other) turns certificate path discovery into **directed multigraph reachability with constraints**:
- **"Chain of Pain" (`C2SP/x509-limbo/limbo/testcases/pathological.py:16-47`, `multiple_chains_expired_intermediate`)**: When `Root 2 -> Expired ICA (same Subject & Key as Root 1) -> Leaf` is sent alongside trusted `Root 1` and `Root 2`, naive greedy path builders that stop at the first matching issuer name fail on the expired cross-sign instead of backtracking to the valid `Root 1 -> Leaf` path (the real-world AddTrust 2020 / DST Root CA X3 2021 outage pattern).
- **Mutually Cross-Signed Cycles (`pathological.py:49-250`, `cve.py:14-250`)**: In `CVE-2024-0567` (GnuTLS < 3.8.3, recreated in `x509-limbo/limbo/testcases/cve.py:15-250`), `leaf -> A1 -> (A <-> B <-> C)` forms a mutually cross-signed clique where `A` is also a trusted self-signed root. Without visited-node cycle detection AND backtracking, validators either loop infinitely, hit recursion limits, or reject a valid trust anchor reachable via `A`. Conversely, `intermediate_cycle_distinct_cas` (`pathological.py:50-132`) constructs `ICA' <-> ICA'' -> EE` disconnected from any root, exposing stack/depth-counter overflows (e.g., `max_chain_depth(255)` in `pathological.py:221`).
- **Exponential DFS Blowup & Asymmetric Validator Budgets**: If an attacker supplies $d$ layers of $b$ distinct intermediates sharing identical Subject/Issuer DNs at each layer (a depth-$d$ branching-$b$ DAG with no path to a trust anchor), unbudgeted DFS performs $\sum_{k=0}^{d} b^k = O(b^d)$ recursive calls and signature verifications!

To contain this complexity, `rustls/webpki` (`src/verify_cert.rs:352-405`) threads an explicit mutable `Budget` through chain building and Name Constraints verification:

```rust
pub(crate) struct Budget {
    signatures: usize,                  // Default: 100 (Go CVE-2018-16875)
    build_chain_calls: usize,           // Default: 200_000 (mozilla::pkix)
    name_constraint_comparisons: usize, // Default: 250_000 (Go crypto/x509)
}
```

#### 1.3 RFC 5280 Name Constraints $O(|N| \times |C|)$ Quadratic Complexity & Cross-Library Split

Under RFC 5280 §4.2.1.10 and §6.1, every intermediate CA's `NameConstraints` extension (`permittedSubtrees` and `excludedSubtrees` over `dNSName`, `iPAddress`, `directoryName`, `rfc822Name`, `uniformResourceIdentifier`) must be checked against **every** Subject DN attribute and Subject Alternative Name (`SAN`) of every subordinate certificate (and in `webpki`, also trust-anchor constraints via `check_signed_chain_name_constraints`, `verify_cert.rs:331-350`). A leaf with $|N|$ SANs under a CA with $|C|$ subtrees triggers $|N| \times |C|$ comparisons (and across a depth-$d$ chain, up to $d \cdot |N| \cdot |C|$).

Direct comparison of `rustls/webpki` vs. `openssl/openssl` (`crypto/x509/v3_ncons.c:252-298`) exposes a concrete **DoS-budget differential**:
- **`rustls/webpki` (`verify_cert.rs:378-403`)**: Enforces a cumulative **chain-wide** budget of **`250,000`** comparisons (`Error::MaximumNameConstraintComparisonsExceeded`).
- **`OpenSSL` (`v3_ncons.c:252, 291-297`)**: Enforces a **per-certificate** product cap `#define NAME_CHECK_MAX (1 << 20)` (**`1,048,576`**) using overflow-safe arithmetic:
  ```c
  if (!add_lengths(&name_count, X509_NAME_entry_count(nm), sk_GENERAL_NAME_num(x->altname))
      || !add_lengths(&constraint_count, sk_GENERAL_SUBTREE_num(nc->permittedSubtrees),
                      sk_GENERAL_SUBTREE_num(nc->excludedSubtrees))
      || (name_count > 0 && constraint_count > NAME_CHECK_MAX / name_count))
      return X509_V_ERR_UNSPECIFIED;
  ```

Executing Probe 2 (`Basis: source + execution`, **Evidence**) demonstrates both thresholds concretely:
- On an adversarial binary CA DAG (`branching = 2`, `depth = 18`), unbudgeted DFS executes **`524,287` calls / `524,286` signature checks**, whereas `webpki`'s `Budget` terminates deterministically on signature **`101`** (`MaximumSignatureChecksExceeded`).
- On a certificate carrying `600` SANs under a CA with `600` Name Constraints (`360,000` pairs), **`rustls/webpki` rejects** (`360,000 > 250,000`) while **`OpenSSL` accepts** (`360,000 <= 1,048,576`), whereas `1,200 x 1,200` (`1,440,000`) is rejected by both.

#### 1.4 Adversarial Differential Testing (`Frankencerts`) vs. Declarative Logic Isolation (`Hammurabi`)

Basis: documentation + source (`sumanj/frankencert` @ `5bbaae85...`, Brubaker et al. IEEE S&P 2014 `10.1109/SP.2014.15`, Larisch et al. ACM CCS 2022 `10.1145/3548606.3560594`)

- **Frankencerts (`frankengen/franken_core.py:8-130`)**: Random fuzzing fails on X.509 because ASN.1/signature checks reject inputs immediately before policy code executes. Frankencert extracts a dictionary of real extensions keyed by OID (`get_extension_dict`, `L8-21`) from internet-harvested seed certificates, samples `[0, max_extensions]` distinct extension types, randomly flips the `critical` bit (`extension.set_critical(1 - extension.get_critical())` with probability `flip_critical_prob`, `L72-73`), optionally mutates extension bytes or validity timestamps (`ext_mod_prob`, `invalid_ts_prob`), and **re-signs the resulting certificate chain with a test CA key** so cryptographic signature verification passes and deep semantic validation logic is exercised. Across OpenSSL, NSS, GnuTLS, PolarSSL, CyaSSL, MatrixSSL, and browsers, differential testing found **208 discrepancies** across **15 distinct bugs**, including X.509 v1 certificates accepted as unauthorized CAs (enabling full MitM) and browsers displaying low-severity expiration warnings instead of untrusted-issuer errors for expired self-signed certificates.
- **Hammurabi (ACM CCS 2022)**: Addresses the structural root cause behind Frankencert's bugs—entangling ASN.1/crypto mechanism with ad-hoc C/C++ policy code. Hammurabi extracts normalized certificate facts into a **Prolog-based declarative logic engine** whose rules explicitly encode browser root-program policies (Chrome and Firefox). Validated against >10 million Certificate Transparency chains and 100K synthetic chains, Hammurabi matched browser verdicts, required <100 LoC of integration glue into Firefox and Go, and enabled automated **policy-difference witness synthesis**, uncovering **9 previously unknown Chrome-vs-Firefox validation discrepancies**.

---

### 2. Verified TLS 1.3 Record/Handshake State Machines and 0-RTT Boundaries (`miTLS` & `rustls`)

Basis: normative + source (`rustls/rustls` @ `836e411e...`, `project-everest/mitls-fstar` @ `9a75fa8c...`, Bhargavan et al. IEEE S&P 2017 `10.1109/SP.2017.58`)

TLS 1.3 (`RFC 8446` / `RFC 9846`) collapses legacy multi-round-trip negotiation and replaces CBC/MAC-then-Encrypt with mandatory AEAD (`AES-GCM`, `ChaCha20-Poly1305`) using per-record XOR nonces ($\mathrm{IV} \oplus \mathrm{seq\_num}$), encrypted inner content types (`TLSInnerPlaintext`), and four strictly ordered cryptographic **epochs**: (0) Cleartext / 0-RTT Early Data, (1) Handshake Traffic, (2) 1-RTT Application Traffic, and (3+) Post-Handshake `KeyUpdate` Traffic. Historical TLS state-machine attacks (FREAK, SMACK/SKIP-TLS, EarlyCCS) exploited missing state guards allowing out-of-order messages or unauthenticated key installation.

#### 2.1 Compile-Time Affine Typestate Key Schedule and FSM in `rustls`

In `rustls/rustls` (`rustls/src/tls13/key_schedule.rs:21-780`), the RFC 8446 §7.1 HKDF-Extract/Expand key schedule is encoded as a **compile-time linear/affine typestate machine** where every secret-mixing transition consumes `self` by value—making key-derivation ordering bugs (such as deriving application keys from an empty secret or skipping `(EC)DHE` mixing) unrepresentable in safe Rust:

```text
  [PSK] -> KeyScheduleEarlyClient / KeyScheduleEarlyServer
              |-- .client_early_traffic_secret(CH) -> EarlyTraffic{Encrypter,Decrypter} (0-RTT)
              |-- .resumption_psk_binder_key_and_sign_verify_data()
              |-- .early_exporter(CH)
              v  From<...> (or KeySchedulePreHandshake::new() without PSK)
           KeySchedulePreHandshake
              |  .into_handshake(shared_secret: SharedSecret)   [HKDF-Extract((EC)DHE)]
              v
           KeyScheduleHandshakeStart
              |  .derive_{client,server}_handshake_secrets(CH..SH)
              v
           KeyScheduleHandshake
              |  .into_traffic_with_client_finished_pending(...)  [server]
              |  .into_pre_finished_client_traffic(...)           [client]
              v
           KeyScheduleBeforeFinished / KeyScheduleTrafficWithClientFinishedPending
              |  .into_traffic(hs_hash)   [requires verified Finished transcript!]
              v
           KeyScheduleTraffic -> splits into KeyScheduleTrafficSend + KeyScheduleTrafficReceive
                                 (independent unidirectional KeyUpdate + Exporter + Resumption)
```

Notice the subtle asymmetric split (`key_schedule.rs:27-88, 601-756`):
- `KeyScheduleEarlyClient` can **only** derive an `EarlyTrafficEncrypter`, while `KeyScheduleEarlyServer` can **only** derive an `EarlyTrafficDecrypter` (`L34-88`), encoding the unidirectional nature of 0-RTT early data (`client -> server` only) directly in the type system.
- Post-handshake traffic splits into independent `KeyScheduleTrafficSend` and `KeyScheduleTrafficReceive` states (`L680-756`), permitting asynchronous unidirectional `KeyUpdate` rekeying before AEAD confidentiality/integrity sequence-number limits are reached without cross-contaminating send and receive epochs.

#### 2.2 TLS 1.3 0-RTT Non-Idempotence, Replay Containment, and Trial Decryption

Because 0-RTT (`early_data`) is encrypted under `client_early_traffic_secret = Derive-Secret(Early Secret, "c e traffic", ClientHello)`—derived solely from the resumption PSK and client-chosen `ClientHello` **before** receiving fresh server randomness or ephemeral `(EC)DHE`—0-RTT packets have **no forward secrecy** and are **inherently replayable** by any network attacker (`RFC 8446` §8). Non-idempotent application operations (e.g., financial transfers, POST mutations, state-advancing RPCs) must never be executed on 0-RTT data unless protected by single-use replay defenses.

Direct inspection of `rustls/src/server/tls13.rs:685-752, 935-948, 1252-1285` establishes `rustls`'s fail-closed 0-RTT enforcement:
1. **Stateless Tickets Hard-Blocked (`server/tls13.rs:707-709`)**:
   ```rust
   /* Non-zero max_early_data_size controls whether early_data is allowed at all.
    * We also require stateful resumption. */
   let early_data_configured = config.max_early_data_size > 0 && config.ticketer.is_none();
   ```
   Unlike TLS stacks that allow 0-RTT with stateless encrypted tickets (relying on probabilistic Bloom-filter strike registers across server fleets), `rustls` **unconditionally refuses 0-RTT whenever a stateless `ticketer` is configured**, requiring stateful single-use server-side session storage (`ServerSessionMemoryCache`).
2. **Strict Parameter Binding (`server/tls13.rs:731-735`)**: `decide_if_early_data_allowed` requires all five conditions simultaneously: (i) client sent `early_data` extension, (ii) server selected PSK `accept.index == 0` (the first offered PSK, per RFC 8446 §4.2.10), (iii) ticket passes obfuscated-age freshness check (`accept.session.is_fresh()`), (iv) identical cipher suite, and (v) identical negotiated ALPN protocol.
3. **Bounded Trial Decryption on 0-RTT Rejection (`server/tls13.rs:339-350, 440-448, 935-948`)**: When a client sends 0-RTT records in flight alongside `ClientHello` and the server rejects `early_data`, the server cannot decrypt those early-data records under handshake keys. `rustls` transitions to `ExpectAndSkipRejectedEarlyData`, enabling **trial decryption** and silently discarding undecryptable application-data records up to `max_early_data_size` bytes—bounding the CPU DoS window where an attacker feeds endless garbage records pretending to be rejected 0-RTT. On QUIC (`server/tls13.rs:406-408`), `EndOfEarlyData` is omitted per RFC 9001 §8.3 because QUIC separates 0-RTT and handshake encryption levels natively via distinct packet number spaces.

#### 2.3 Mechanized Multi-Epoch Security Proofs in `miTLS` (and Audit Boundaries)

In `Bhargavan et al., IEEE S&P 2017` (`10.1109/SP.2017.58`) and `project-everest/mitls-fstar` (`9a75fa8c46e50897b1f43002885d25a34dfa929a`), TLS 1.3's stateful record layer (`StAE` / `AEAD.Pkg`) is formalized in F* via **game-based cryptographic idealization** paired with **HyperStack memory-region separation**:
- **Idealization Guard (`src/tls/MiTLS.AEAD.Pkg.fsti:33-43, 68-75, 169-190`)**: Keys are indexed by `i:ip.t{ip.registered i}` with `safe i = ideal /\ ip.honest i`. When `model` is true, an AEAD key carries a ghost ideal log iff `safe i`, and `coerce_key` (injecting attacker-chosen key bytes) has the static precondition `ideal ==> ~(ip.honest i)`, mechanically preventing honest keys from being coerced or confused with compromised epochs.
- **Disjoint Epoch Regions & Monotonic Counters (`src/tls/MiTLS.Epochs.fst:48-142, 199-218`)**:
  - `epoch_region_inv` (`L48-61`) enforces pairwise disjointness among handshake region `hs_rgn`, reader region `region r`, and writer region `region w`.
  - `epochs_inv` (`L106-114`) enforces pairwise disjointness between writer regions across all distinct epochs $i \neq j$.
  - `epoch_ctr` (`L126-130`) is typed as a monotonic reference `m_rref r (epoch_ctr_inv r es) increases`, guaranteeing that read and write epoch indices advance monotonically (`incr_epoch_ctr`, `L199-217`) and cannot roll back to reuse nonces from an earlier key epoch.
- **Verified Proof-Debt Finding (`Basis: source`)**: Direct inspection of `MiTLS.Epochs.fst` at `9a75fa8c46e50897b1f43002885d25a34dfa929a` reveals `#set-options "--admit_smt_queries true"` at line `32` (and `#reset-options "... --admit_smt_queries true"` at line `187`) plus `assume False; //17-06-30 TODO restore framing with extra field` in `create` at line `225`. While the core `AEAD` cryptographic reduction and Low* primitives (Poly1305/GHASH injectivity, `StAE`) are mechanized, **repository-level framing glue in `MiTLS.Epochs.fst` contains unverified admits at HEAD**—a critical caveat against assuming whole-repository zero-axiom verification from paper citations alone.

---

### 3. DNS Bailiwick Semantics (`SCALE`), DNSSEC `NSEC`/`NSEC3`, and `KeyTrap` Complexity Attacks

Basis: normative + documentation + source + execution

#### 3.1 Multi-Feature DNS Semantic Differentials (`SCALE`) and Bailiwick Containment

Authoritative DNS resolution combines zone cuts (`NS` delegations), alias redirections (`CNAME`, `RFC 1034`), subtree redirections (`DNAME`, `RFC 6672` synthesizing per-query `CNAME`s), and wildcards (`*`, `RFC 4592`). In `SCALE` (*Small-scope Constraint-driven Automated Logical Execution*, Kakarla et al., USENIX NSDI 2022), the `Ferret` tool symbolically executes an executable RFC model of DNS to **jointly synthesize coupled `(zone_file, query)` pairs** targeting multi-feature corner cases—overcoming random fuzzing's inability to synthesize coherent zones and queries simultaneously. Across 8 mainstream DNS implementations (including BIND, PowerDNS, Knot, NSD), **62% of ~13,000 generated tests produced cross-implementation discrepancies**, exposing **30 unique RFC-compliance bugs**, including a remotely triggerable assertion crash in BIND 9 (`CVE-2021-25215`) involving `DNAME` record processing.

On the recursive-resolver side, **bailiwick checking** (`RFC 2181` §5.4.1, `RFC 5452`) enforces zone authority boundaries so an authoritative server for `attacker.example` cannot poison cache entries for `bank.com` via unsolicited records in the Answer, Authority, or Additional sections. In `NLnetLabs/unbound` (`iterator/iter_scrub.c:352-368, 496-615`), `scrub_normalize` validates every `DNAME` and synthesized `CNAME` against `pkt_sub(pkt, rrset->dname, zonename)` (`dname_subdomain_c`), discards multi-record `DNAME` RRsets (`rrset->rr_count != 1`), removes excessive `CNAME` chains (`normalize: removing because too many cnames`), and strips out-of-bailiwick authority/additional records before any RRset enters the validator or cache.

#### 3.2 DNSSEC `NSEC`/`NSEC3` Authenticated Denial of Existence and `CVE-2023-50868`

DNSSEC proves non-existence (`NXDOMAIN` or `NODATA`) without online signing via lexicographically ordered `NSEC` (`RFC 4035`) or SHA-1 hashed `NSEC3` (`RFC 5155`) records:
- An **`NSEC3` `NXDOMAIN` proof** (`val_nsec3.h:121-136`) requires up to three records: (1) an NSEC3 matching the **closest encloser** $E$ (proving $E$ exists), (2) an NSEC3 covering the hash of the **next closer name** $N$ (proving $N$ does not exist), and (3) an NSEC3 covering `*.E` (proving no wildcard synthesizes the answer)—unless the `NSEC3_OPTOUT` (`0x01`, `val_nsec3.h:92`) flag covers an unsigned delegation.
- **Iterated Hashing Amplification (`CVE-2023-50868`)**: Computing each `NSEC3` hash requires `iterations + 1` sequential SHA-1 invocations (`H_0 = SHA1(wire(name) || salt)`, `H_{k+1} = SHA1(H_k || salt)`). Legacy RFC 5155 permitted up to `2,500` iterations for 4096-bit keys. Because a validating resolver must walk candidate ancestor labels to locate the closest encloser during random-subdomain attacks, a single adversarial response with high `iterations` and many labels triggers tens of thousands of SHA-1 calls per packet!
- **`RFC 9276` Remediation**: Recommends setting **`iterations = 0`** (single SHA-1 pass, no salt) because offline GPU cracking easily defeats high iteration counts anyway while high iterations create asymmetric CPU DoS against validating resolvers.

#### 3.3 `KeyTrap` (`CVE-2023-50387`): Key-Tag Collision Mechanics and Production Mitigations

`KeyTrap` (Heftrig, Schulmann, Vogel, and Waidner, ACM CCS 2024, `arXiv:2406.03133`, `CVE-2023-50387`) exploits a foundational algorithmic flaw in DNSSEC `RRSIG` -> `DNSKEY` lookup (`RFC 4034` §3.1.5 & Appendix B, `RFC 4035` §5.3.1):

1. **Non-Cryptographic 16-bit Key Tag**: An `RRSIG` identifies its signing `DNSKEY` only by `(algorithm, 16-bit key_tag)`—**not** a collision-resistant hash of the public key. RFC 4034 Appendix B defines the key tag (implemented in `unbound/validator/val_sigcrypt.c:382-389` via `sldns_calc_keytag_raw`) as a simple 16-bit 1's-complement-folded sum of 16-bit words of the `DNSKEY` RDATA:
   $$\mathrm{ac} = \sum_{i=0}^{L-1} \begin{cases} b_i \ll 8 & \text{if } i \text{ even} \\ b_i & \text{if } i \text{ odd} \end{cases}, \qquad \mathrm{keytag} = (\mathrm{ac} + (\mathrm{ac} \gg 16)) \bmod 2^{16}$$
2. **Trivial $O(1)$ Multi-Collision Construction (`Basis: execution`, Probe 3)**: Because the fold is linear, adjusting the last 2 bytes of any $K$ distinct `DNSKEY` payloads forces all $K$ keys to share an arbitrary target key tag (e.g. `0xBEEF`) without brute force.
3. **Multiplicative Signature-Verification Storm**: Under RFC 4035's liberal acceptance rule (try every matching key/signature until one validates), a malicious zone publishing $K$ colliding `DNSKEY`s and $S$ invalid `RRSIG`s sharing `(algo, keytag)` forces an uncapped validator to execute **$K \times S$ full asymmetric public-key verifications per RRset**—further multiplied across `DS` x `DNSKEY` sets, `NSEC`/`NSEC3` records, and `CNAME`/`DNAME` delegation chains—stalling resolvers by up to millions of times normal query CPU cost from a single UDP/TCP response.

Direct source inspection of `NLnetLabs/unbound` (`5d7ef54e1f45e1ff5a1b83057987a33883784c93`) and `isc-projects/bind9` (`f13d302fb694db688dc50ea184bda28e9531c491`) documents the exact post-KeyTrap defense-in-depth quotas now enforced in production:

| Defense Dimension | `NLnetLabs/unbound` (`5d7ef54e...`) | `isc-projects/bind9` (`f13d302f...`) |
| :--- | :--- | :--- |
| **Per-RRset RRSIG verify cap** | `MAX_VALIDATE_RRSIGS = 8` (`val_sigcrypt.c:84, 631`) | Bounded via fetch-wide validation & failure counters (`validator.c:615, 1685-1703`) |
| **Per-query cryptographic attempts / validations** | `val_validation_attempts = 32` (`config_file.c:434`, `val_sigcrypt.c:602`) | `DEFAULT_MAX_VALIDATIONS = 16` (`resolver.c:190-192`) |
| **Per-query signature failures before abort (`ISC_R_QUOTA`)** | Bounded by `MAX_VALIDATE_RRSIGS` + `val_validation_attempts` | `DEFAULT_MAX_VALIDATION_FAILURES = 1` (`resolver.c:193-195`, `VALATTR_MAXVALIDATIONFAILS`) |
| **Key-tag / DS×DNSKEY scan cap** | `MAX_TAG_MATCHES = 256` (`val_utils.h:62`, `val_sigcrypt.c:587, 694, 777`) | `DS_DNSKEY_COMBINATIONS_PER_VALIDATION = 2` (`validator.c:131`) |
| **NSEC / NSEC3 validation & hash caps** | `MAX_VALIDATE_NSECS = 8` (`val_sigcrypt.c:86, 612`); `MAX_NSEC3_CALCULATIONS = 8` per slice (`val_nsec3.h:106`) | Enforced via `VALATTR_MAXVALIDATIONS` + `DNS_NSEC3_MAXITERATIONS` |
| **NSEC3 max hash iterations** | `val_nsec3_key_iterations = "1024 150 2048 150 4096 150"` (`config_file.c:340-341`) | `DNS_NSEC3_MAXITERATIONS = 50U` (`nsec3.h:28`, `validator.c:523`) |

Notice the resulting **availability-vs-resilience differential** across resolvers: a misconfigured (non-malicious) zone with `2` stale/broken `RRSIG`s before a valid signature or `100` `NSEC3` iterations will **fail validation in BIND 9** (`DEFAULT_MAX_VALIDATION_FAILURES = 1`, `DNS_NSEC3_MAXITERATIONS = 50`) while **succeeding in Unbound** (`MAX_VALIDATE_RRSIGS = 8`, max iterations `150`).

Executing Probe 3 (`Basis: source + execution`, **Evidence**) quantifies both attacks directly:
- Forging $K = 32$ distinct P-256 `DNSKEY`s colliding on key tag `0xBEEF` (`48879`) paired with $S = 32$ invalid `RRSIG`s drives **`1,024` uncapped verifies** down to **`9`** in Unbound (`> 8` exits loop) and **`2`** in BIND 9 (`MAX_FAILS = 1`).
- Computing a 5-label `NSEC3` closest-encloser proof in Python 3 requires **`5` SHA-1 calls (`40.7 us`)** under RFC 9276 (`iter = 0`), **`255` calls (`171.3 us`)** at BIND 9's cap (`iter = 50`), **`755` calls (`516.1 us`)** at Unbound's cap (`iter = 150`), and **`12,505` calls (`8,013.5 us`, ~197× amplification)** at legacy RFC 5155 (`iter = 2,500`).

---

### 4. Cross-Stack Synthesis: Recurring Protocol-Boundary Anti-Patterns

Basis: derived (synthesized from Sections 1–3)

| Protocol Stack | Unbounded Work / Differential Surface | Root Protocol Design Cause | Production Defense Pattern | Residual Differential Risk |
| :--- | :--- | :--- | :--- | :--- |
| **X.509 ASN.1 & Path Building** | BER/DER splits; $O(b^d)$ DAG backtracking; $O(|N|\cdot|C|)$ Name Constraints | X.690 BER legacy; cross-signed multigraphs; pairwise subtree checks | Strict canonical DER (`webpki/der.rs`); explicit `Budget` / `NAME_CHECK_MAX`; declarative policy (`Hammurabi`) | Divergent caps (`250K` vs. `1M` NC checks) and strictness splits (`webpki` vs. OpenSSL) |
| **TLS 1.3 State & 0-RTT** | Out-of-order key installation; 0-RTT replay; rejected early-data DoS | Multi-epoch concurrency; unauthenticated PSK-only 0-RTT | Affine typestate key schedule (`rustls`); stateful-only 0-RTT + bounded trial decryption; HyperStack epoch regions (`miTLS`) | Application-layer non-idempotence if 0-RTT accepted; unverified glue admits (`MiTLS.Epochs.fst`) |
| **DNS & DNSSEC** | `DNAME`/`CNAME`/wildcard interactions; `KeyTrap` $K \times S$ storms; `NSEC3` hash floods | Postel's Law ("try all signatures"); unkeyed 16-bit key tag; unbounded SHA-1 iterations | Bailiwick scrubbing (`iter_scrub.c`); strict per-query verify/fail/tag/NSEC3 quotas (`Unbound`, `BIND 9`); RFC 9276 `iter = 0` | Strict quotas break quirky legacy zones differently across `BIND 9` (`1` fail, `50` iter) vs. `Unbound` (`8` sigs, `150` iter) |

## Boundaries

- **Legacy TLS 1.0–1.2 & Post-Quantum Hybrid Key Schedules (`not examined`)**: This report examines TLS 1.3 (`RFC 8446` / `RFC 9846`) state machines in `rustls` and `miTLS`. TLS 1.2 renegotiation, CBC Lucky13 padding oracles, RSA PKCS#1 v1.5 Bleichenbacher attacks, and hybrid ML-KEM key-exchange wire formats were not examined.
- **Revocation Infrastructure (`CRL`, `OCSP`, `CRLite`) & Certificate Transparency (`not examined`)**: X.509 path building and Name Constraints were examined in `rustls/webpki`, `OpenSSL`, `Frankencerts`, and `x509-limbo`, but online revocation checking (`OCSP` stapling, `CRL` distribution points, `Must-Staple`) and SCT/CT log verification were not audited.
- **`miTLS` End-to-End Whole-Program Proof Completeness (`known not to apply` at HEAD)**: Although Bhargavan et al. (IEEE S&P 2017) formally proved the TLS 1.3 record-layer reduction in F*, direct source inspection of `project-everest/mitls-fstar` (`9a75fa8c46e50897b1f43002885d25a34dfa929a`) establishes that `src/tls/MiTLS.Epochs.fst` contains `#set-options "--admit_smt_queries true"` (`L32`, `L187`) and `assume False` (`L225`). Claiming zero-admit whole-stack verification for that repository revision is factually unsupported.
- **`Hammurabi` Upstream Repository Availability (`not examined` at source level)**: Claims regarding `Hammurabi` rely on the peer-reviewed ACM CCS 2022 publication (`DOI: 10.1145/3548606.3560594`); its Prolog rulebase repository was not directly inspected at a pinned commit SHA.
- **Additional DNS Resolvers (`Knot Resolver`, `PowerDNS Recursor`, `systemd-resolved`, `hickory-dns`) (`not examined`)**: KeyTrap and NSEC3 mitigation constants were directly extracted from `NLnetLabs/unbound` and `isc-projects/bind9` only; exact post-patch quotas in other resolvers cannot be extrapolated without inspecting their source trees.
- **Live Network Exploitation & Resolver Timing Benchmarks (`not examined`)**: Probe 3 measures local Python SHA-1 hashing and mathematical key-tag collision counts (`Basis: execution`), not live UDP/TCP network packet timings against compiled C `unbound`/`named` binaries with OpenSSL hardware-accelerated ECDSA/RSA verification.
- **Application-Layer 0-RTT Idempotence (`unsupported` at TLS layer)**: Even with `rustls`'s stateful single-use session cache (`ticketer.is_none()`), distributed multi-replica server deployments without synchronous cross-node ticket consumption cannot eliminate cross-node 0-RTT replays at the TLS layer alone; application protocols (e.g. HTTP `425 Too Early`, RFC 8470) remain responsible for rejecting non-idempotent early requests.

## Evidence

### Primary Git Source Artifacts (Observed 2026-11-19)

1. **`rustls/webpki` @ `f6dcb14b822784c6fc23556d549e2683cc7328a1`**:
   - `src/der.rs` (`L40-42, L142-255`): `read_all` trailing-data check, `read_tag_and_get_value_limited` rejecting high-tag-number form, indefinite-length BER, non-canonical 1–4-byte long lengths, and enforcing `TWO_BYTE_DER_SIZE`.
   - `src/verify_cert.rs` (`L331-405`): `check_signed_chain_name_constraints` and `Budget { signatures: 100, build_chain_calls: 200_000, name_constraint_comparisons: 250_000 }`.
2. **`openssl/openssl` @ `fc355e65068efe333e0764db1c32c302af8aa7fa`**:
   - `crypto/x509/v3_ncons.c` (`L252-335`): `#define NAME_CHECK_MAX (1 << 20)` and overflow-safe `NAME_CONSTRAINTS_check` quadratic cap (`constraint_count > NAME_CHECK_MAX / name_count`).
3. **`C2SP/x509-limbo` @ `b12423782a88abead01141fa6582254e3eb49e74`**:
   - `limbo/testcases/pathological.py` (`L16-250`): `multiple_chains_expired_intermediate`, `intermediate_cycle_distinct_cas`, `intermediate_cycle_distinct_cas_max_depth`, `intermediate_cycle_same_logical_ca`.
   - `limbo/testcases/cve.py` (`L14-250`): `cve_2024_0567` mutually cross-signed clique `A <-> B <-> C` resolving to trusted `Root A`.
4. **`sumanj/frankencert` @ `5bbaae85cab35882dec1672ef037a42e29180b40`**:
   - `README.md` (`L1-138`) and `frankengen/franken_core.py` (`L8-130`): OID-keyed seed extension harvesting (`get_extension_dict`), randomized extension recombination, critical-bit flipping (`flip_critical_prob`), and test-CA re-signing.
5. **`rustls/rustls` @ `836e411eccaf7331f4c289aabef0de32474de3b8`**:
   - `rustls/src/tls13/key_schedule.rs` (`L21-780`): Affine typestate structs `KeyScheduleEarly{Client,Server}`, `KeySchedulePreHandshake`, `KeyScheduleHandshakeStart`, `KeyScheduleHandshake`, `KeyScheduleBeforeFinished`, `KeyScheduleTraffic{,Send,Receive}`.
   - `rustls/src/server/tls13.rs` (`L339-350, L406-408, L440-448, L685-752, L935-948, L1252-1285`): `decide_if_early_data_allowed` (`config.max_early_data_size > 0 && config.ticketer.is_none()`), freshness/ALPN/suite/index checks, `ExpectAndSkipRejectedEarlyData`, `ExpectEarlyData`.
6. **`project-everest/mitls-fstar` @ `9a75fa8c46e50897b1f43002885d25a34dfa929a`**:
   - `src/tls/MiTLS.AEAD.Pkg.fsti` (`L33-75, L169-234`): `safe i = ideal /\ ip.honest i`, `coerce_key` precondition `ideal ==> ~(ip.honest i)`, `footprint`/`invariant_framing`.
   - `src/tls/MiTLS.Epochs.fst` (`L32, L48-142, L187-226`): `epoch_region_inv`, `epochs_inv`, monotonic `epoch_ctr` (`m_rref ... increases`), and observed `--admit_smt_queries true` / `assume False`.
7. **`NLnetLabs/unbound` @ `5d7ef54e1f45e1ff5a1b83057987a33883784c93`**:
   - `validator/val_sigcrypt.c` (`L84-86, L382-389, L562-655, L694-782`), `validator/val_utils.h` (`L62`), `validator/val_nsec3.h` (`L88-136`), `validator/val_nsec3.c` (`L671-765`), `util/config_file.c` (`L340-341, L434`), `iterator/iter_scrub.c` (`L352-368, L496-615`).
8. **`isc-projects/bind9` @ `f13d302fb694db688dc50ea184bda28e9531c491`**:
   - `lib/dns/resolver.c` (`L190-195, L521-522, L633-634`): `DEFAULT_MAX_VALIDATIONS = 16`, `DEFAULT_MAX_VALIDATION_FAILURES = 1`.
   - `lib/dns/validator.c` (`L81-83, L131, L523-527, L610-620, L1685-1703`): `DS_DNSKEY_COMBINATIONS_PER_VALIDATION = 2`, `over_max_fails`, `DNS_NSEC3_MAXITERATIONS` check.
   - `lib/dns/include/dns/nsec3.h` (`L28`): `#define DNS_NSEC3_MAXITERATIONS 50U`.

### Peer-Reviewed Literature & Standards

- C. Brubaker, S. Jana, B. Ray, S. Khurshid, and V. Shmatikov, *"Using Frankencerts for Automated Adversarial Testing of Certificate Verification in SSL/TLS Implementations"*, IEEE S&P 2014, pp. 414–429, DOI `10.1109/SP.2014.15`.
- J. Larisch, W. Aqeel, M. Lum, Y. Goldschlag, L. Kannan, K. Torshizi, Y. Wang, T. Chung, D. Levin, B. M. Maggs, A. Mislove, B. Parno, and C. Wilson, *"Hammurabi: A Framework for Pluggable, Logic-Based X.509 Certificate Validation Policies"*, ACM CCS 2022, DOI `10.1145/3548606.3560594`.
- K. Bhargavan, A. Delignat-Lavaud, C. Fournet, M. Kohlweiss, J. Pan, J. Protzenko, A. Rastogi, N. Swamy, S. Zanella-Béguelin, and J. K. Zinzindohoué, *"Implementing and Proving the TLS 1.3 Record Layer"*, IEEE S&P 2017, pp. 463–482, DOI `10.1109/SP.2017.58`.
- S. K. R. Kakarla, R. Beckett, T. Millstein, and G. Varghese, *"SCALE: Automatically Finding RFC Compliance Bugs in DNS Nameservers"*, USENIX NSDI 2022, `https://www.usenix.org/conference/nsdi22/presentation/kakarla`.
- E. Heftrig, H. Schulmann, N. Vogel, and M. Waidner, *"The Harder You Try, The Harder You Fail: The KeyTrap Denial-of-Service Algorithmic Complexity Attacks on DNSSEC"*, ACM CCS 2024, `CVE-2023-50387`, DOI `10.48550/arXiv.2406.03133`.
- IETF RFCs referenced normatively: RFC 2181, RFC 4034, RFC 4035, RFC 5155, RFC 5280, RFC 6672, RFC 8446 / RFC 9846, RFC 9001, RFC 9276.

### Executable Micro-Probes (Executed 2026-11-19, Python 3)

A self-contained Python 3 script tested (1) strict DER (mirroring `webpki/src/der.rs`) vs. permissive BER across 6 wire specimens, (2) unbudgeted vs. `webpki`-budgeted binary CA DAG DFS and `webpki` vs. `OpenSSL` Name Constraints matrix thresholds, and (3) exact RFC 4034 Appendix B key-tag collision synthesis ($K=32$ distinct P-256 `DNSKEY`s colliding on `0xBEEF`) plus 5-label `NSEC3` SHA-1 iteration timing:

```text
=== PROBE 1: Strict DER (webpki) vs Permissive BER ===
  Canonical INTEGER 5                    | DER=True  (OK(tag=0x02, len=1)                         ) | BER=True  (OK_BER(len=1, trailing=0))
  Non-minimal long length (0x81 0x01)    | DER=False (non-canonical length encoding               ) | BER=True  (OK_BER(len=1, trailing=0))
  Indefinite length SEQUENCE (BER)       | DER=False (indefinite-length BER forbidden             ) | BER=True  (OK_BER(indefinite))
  Non-canonical BOOLEAN 0x01 (cA=TRUE)   | DER=False (non-canonical BOOLEAN (must be 0x00 or 0xFF)) | BER=True  (OK_BER(len=1, trailing=0))
  Non-minimal INTEGER (0x00 0x05)        | DER=False (non-minimal INTEGER                         ) | BER=True  (OK_BER(len=2, trailing=0))
  Trailing garbage after SEQUENCE        | DER=False (trailing data or length mismatch            ) | BER=True  (OK_BER(len=0, trailing=2))

=== PROBE 2: RFC 5280 Path-Building DAG & Name-Constraints Budgets ===
  Binary DAG depth=10: unbounded=('NotFound', 2047, 2046) | webpki_budget=('MaximumSignatureChecksExceeded', 101, 101)
  Binary DAG depth=18: unbounded=('NotFound', 524287, 524286) | webpki_budget=('MaximumSignatureChecksExceeded', 101, 101)
  NC matrix 100x100=   10,000 | webpki(<=250,000)=True  | OpenSSL(<=1,048,576)=True
  NC matrix 600x600=  360,000 | webpki(<=250,000)=False | OpenSSL(<=1,048,576)=True
  NC matrix 1200x1200=1,440,000 | webpki(<=250,000)=False | OpenSSL(<=1,048,576)=False

=== PROBE 3: RFC 4034 Key-Tag Collisions (KeyTrap) & NSEC3 Iterations ===
  Generated 32 distinct DNSKEYs all colliding on RFC 4034 keytag 0xBEEF (48879)
  With K=32 keys x S=32 RRSIGs: uncapped=1024 sig verifies | Unbound(MAX_VALIDATE_RRSIGS=8)=9 | BIND9(MAX_FAILS=1)=2
  NSEC3 5-label proof (RFC 9276 recommended            , iter=   0):      5 SHA-1 calls (    40.7 us)
  NSEC3 5-label proof (BIND9 DNS_NSEC3_MAXITERATIONS   , iter=  50):    255 SHA-1 calls (   171.3 us)
  NSEC3 5-label proof (Unbound default cap             , iter= 150):    755 SHA-1 calls (   516.1 us)
  NSEC3 5-label proof (Legacy RFC 5155 (2048-bit key)  , iter= 500):   2505 SHA-1 calls (  1859.1 us)
  NSEC3 5-label proof (Legacy RFC 5155 (4096-bit key)  , iter=2500):  12505 SHA-1 calls (  8013.5 us)
```

## Revalidation

To cheaply verify whether these findings remain accurate on newer upstream versions:

1. **X.509 Budgets & DER Strictness**: Diff `rustls/webpki` `src/verify_cert.rs` (`impl Default for Budget`) and `src/der.rs` (`read_tag_and_get_value_limited`) against `f6dcb14b822784c6fc23556d549e2683cc7328a1`, and diff `openssl/openssl` `crypto/x509/v3_ncons.c` (`NAME_CHECK_MAX`) against `fc355e65068efe333e0764db1c32c302af8aa7fa`. Run the `C2SP/x509-limbo` harness against target verifiers to detect newly introduced cycle/cross-sign or Name Constraints regressions.
2. **TLS 1.3 Typestate & 0-RTT Anti-Replay Policy**: Check `rustls/rustls` `rustls/src/server/tls13.rs` (`decide_if_early_data_allowed`) to see whether stateless-ticket 0-RTT with strike registers has been added (`config.ticketer.is_none()` check) and diff `rustls/src/tls13/key_schedule.rs` for any weakened typestate transitions. For `project-everest/mitls-fstar`, grep `src/tls/MiTLS.Epochs.fst` for `--admit_smt_queries` and `assume False` to verify whether epoch-framing proofs have been discharged.
3. **DNSSEC KeyTrap & NSEC3 Quotas**: Check exact macro/config values in:
   - `NLnetLabs/unbound`: `MAX_VALIDATE_RRSIGS` / `MAX_VALIDATE_NSECS` (`validator/val_sigcrypt.c`), `MAX_TAG_MATCHES` (`validator/val_utils.h`), `MAX_NSEC3_CALCULATIONS` (`validator/val_nsec3.h`), `val_validation_attempts` and `val_nsec3_key_iterations` (`util/config_file.c`).
   - `isc-projects/bind9`: `DEFAULT_MAX_VALIDATIONS` / `DEFAULT_MAX_VALIDATION_FAILURES` (`lib/dns/resolver.c`), `DS_DNSKEY_COMBINATIONS_PER_VALIDATION` (`lib/dns/validator.c`), and `DNS_NSEC3_MAXITERATIONS` (`lib/dns/include/dns/nsec3.h`).
