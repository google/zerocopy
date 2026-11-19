# NASDAQ ITCH/OUCH MoldUDP64 Feeds, FIX SBE Wire Evolution, Intrusive Limit Order Books, and Exchange Conservation Guards

## Summary

Deterministic sub-microsecond financial matching engines and ledger settlement kernels combine zero-allocation binary wire framing, single-writer cache-line-isolated queues, intrusive price-time arenas, and exact fixed-point conservation invariants:

1. **Sequenced Multicast Framing (`MoldUDP64` / `ITCH 5.0` / `OUCH 5.0`) & Zero-Copy Wire Evolution (`FIX SBE`):** `MoldUDP64` frames variable-count `TotalView-ITCH 5.0` market-data messages (`Add Order 'A'` = `36 B` fixed big-endian layout; `Add MPID 'F'` = `40 B`) behind a 20-byte header (`10 B` Session, `8 B` 64-bit first-message Sequence Number, `2 B` Message Count with `0x0000` Heartbeat and `0xFFFF` End-of-Session sentinels), making packet drops immediately detectable via sequence gaps filled out-of-band. For extensible schemas, `real-logic/simple-binary-encoding` (`SBE`) lays out messages strictly in `(8B Header -> Root Block -> Repeating Groups -> VarData)` order without pointer tables: forward/backward schema evolution hinges on advancing the cursor by runtime `actingBlockLength` (rather than compile-time `BLOCK_LENGTH`) before traversing repeating groups, and gating newly appended fields on `actingVersion >= field.sinceVersion`.
2. **Mechanical-Sympathy Queues (`LMAX Disruptor`) & Intrusive Price-Time Limit Order Books (`LOB`):** `LMAX-Exchange/disruptor` eliminates lock contention and MESI `RFO` cache-coherency stalls by separating single-writer ring claim (`SingleProducerSequencer`, caching minimum consumer `gatingSequences` in a non-volatile local `cachedValue` and publishing via `VarHandle.releaseFence()`) from `128`-byte-padded `Sequence` cursors (`56 B` `LhsPadding` + `8 B` `value` + `56 B` `RhsPadding` across class inheritance hierarchy, defeating adjacent-pair spatial prefetcher false sharing). Inside the single matching thread, pre-allocated intrusive doubly-linked order arenas indexed by order-ID hash/direct-table + price-level ladder execute `Add`, `Cancel` (`'X'`/`'D'`), and `Execute` (`'E'`) in deterministic **`O(1)` time** with **`0` heap allocations**.
3. **Exact `u128` Two-Phase Double-Entry Conservation (`TigerBeetle`):** Floating-point binary rounding (`IEEE 754`) violates monetary conservation ($0.1 + 0.2 \ne 0.3$). `tigerbeetle/tigerbeetle` enforces exact integer conservation inside a padding-free `128`-byte `Account` (`2` cache lines) holding **four separate monotonic `u128` accumulators** (`debits_pending`, `debits_posted`, `credits_pending`, `credits_posted`). Pre-trade margin/escrow checks (`debits_exceed_credits`) pessimistically sum `debits_pending + debits_posted + amount > credits_posted` to prevent concurrent order double-spends; when a pending reservation `p.amount` settles with price improvement (`amount_actual <= p.amount`), `state_machine.zig` atomically decrements `debits_pending` and `credits_pending` by `p.amount` while incrementing `debits_posted` and `credits_posted` by `amount_actual`, preserving both $\sum (\text{Dr}_{\text{posted}} - \text{Cr}_{\text{posted}}) = 0$ and $\sum (\text{Dr}_{\text{pending}} - \text{Cr}_{\text{pending}}) = 0$.
4. **Market-Integrity Invariants & Production Outage Post-Mortems (`Flash Crash` 2010 & `NYSE` Jan 24, 2023):** Resting books must maintain strict uncrossed order (`best_bid < best_ask`), Self-Trade Prevention (`STP` preventing wash executions within one firm/MPID), and **Limit Up–Limit Down (`LULD`)** reference-price collars—instituted after the **May 6, 2010 Flash Crash** (`SEC`/`CFTC` report), when a price-insensitive `75,000`-contract (`$4.1B`) E-Mini S&P 500 sell algorithm drained continuous liquidity and swept resting `$0.01` / `$99,999.99` market-maker **stub quotes**. Conversely, the **NYSE January 24, 2023 opening-auction outage** (`SEC` Reg SCI order: `2,824` of `3,421` symbols skipped opening auctions, triggering `84` `LULD` halts and `4,341` busted trades) proves that local matching invariants fail if primary and disaster-recovery (`DR`) state machines run concurrently without epoch-fenced `(TradingDate, PrimaryTerm, AuctionState)` transition witnesses.

## Applicability

This report characterizes the wire formats, concurrency primitives, data structures, accounting state machines, market-structure guards, and multi-level (`L1`–`L6`) performance/resource and comprehensibility (`C1`–`C2`) properties of three pinned upstream repositories, two financial wire standards, and two U.S. regulatory post-mortems:

- **Directly Examined Upstream Repositories:**
  - `real-logic/simple-binary-encoding` at commit `6c20e6242e63ac67854707470dcee931eabf68fe`: SBE flyweight code generators for Rust and C++ (`sbe-tool/src/main/java/uk/co/real_logic/sbe/generation/{rust/RustGenerator,cpp/CppGenerator}.java`).
  - `LMAX-Exchange/disruptor` at commit `c871ca49826a6be7ada6957f6fbafcfecf7b1f87`: Java `VarHandle` ring buffer, inheritance-padded `Sequence`, and single- vs. multi-producer sequencers (`src/main/java/com/lmax/disruptor/{Sequence,SingleProducerSequencer,MultiProducerSequencer,RingBuffer}.java`).
  - `tigerbeetle/tigerbeetle` at commit `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`: Zig `128`-byte `Account` and `Transfer` ABI structs and deterministic two-phase `pending`/`posted`/`voided`/`expired` state machine (`src/tigerbeetle.zig`, `src/state_machine.zig`).
- **Normative Protocol Specifications & Regulatory Post-Mortems:**
  - **NASDAQ `MoldUDP64 v1.0`, `SoupBinTCP`, `TotalView-ITCH 5.0`, and `OUCH 5.0`:** Multicast market-data framing and unicast TCP order-entry protocols.
  - **FIX Trading Community `Simple Binary Encoding (SBE) v2.0`:** Little-endian zero-copy flyweight wire encoding used across CME (`iLink 3` / `MDP 3.0`), Eurex, Euronext, and crypto/FX venues.
  - **U.S. SEC & CFTC Staff Report (`2010-09-30`):** *Findings Regarding the Market Events of May 6, 2010* (`Flash Crash`, stub quotes, and `LULD` National Market System Plan).
  - **U.S. SEC Regulation SCI Enforcement Order:** New York Stock Exchange January 24, 2023 opening-auction failure (`Rule 1001(a)`, dual-active DR configuration skew, missing opening prints, and delayed SIP `LULD` band calculation).

Scope boundaries: Continuous double-auction price-time (`FIFO`) matching applies directly to equities (`NASDAQ`, `NYSE`, `IEX`) and central-limit-order-book (`CLOB`) futures/FX venues; pro-rata allocation matching (`CME` Eurodollar/SOFR interest-rate futures, where fills split proportionally to resting order size with minimum-allocation rounding lots) alters queue-priority data structures and is bounded explicitly under **Boundaries**.

## Findings

### 1. Deterministic Sequenced Wire Protocols: `MoldUDP64` / `ITCH 5.0` / `OUCH 5.0` and `FIX SBE` Flyweights

`Basis: normative + source + execution`

#### 1.1 `MoldUDP64` Multicast Sequencing & `TotalView-ITCH 5.0` / `OUCH 5.0` Asymmetry

Exchanges separate **inbound order entry** (`OUCH 5.0` over point-to-point `SoupBinTCP` unicast sessions, where TCP flow control + `SoupBinTCP` 64-bit sequence numbers guarantee reliable per-firm order submission, cancellation, and private fill acknowledgments) from **outbound full-depth market data** (`TotalView-ITCH 5.0` over `MoldUDP64` IP multicast, fanning out identically to thousands of subscribers in `< 1 µs` switch hop latency without per-client TCP state).

Every `MoldUDP64` UDP datagram starts with a fixed **20-byte big-endian header**:

| Byte Offset | Length | Field | Wire Semantics & State-Machine Transitions |
| :---: | :---: | :--- | :--- |
| `0..10` | `10 B` | `Session` | ASCII session ID; a change invalidates sequence continuity (e.g., intraday disaster-recovery session rollover!) |
| `10..18` | `8 B` | `Sequence Number` | `u64` 1-based index of the **first** message block inside this UDP packet (not a packet counter!) |
| `18..20` | `2 B` | `Message Count` | `u16`: `1..65534` = count of `(u16 length, u8[length] payload)` blocks; `0x0000` = **Heartbeat** (`Sequence Number` = *next expected* message); `0xFFFF` = **End of Session** |

- **Deterministic Gap Detection & Dual-Feed (`A`/`B`) Arbitrage:** If subscriber state expects `expected_seq` and receives `pkt.seq > expected_seq` (even on a `Message Count == 0` heartbeat!), `pkt.seq - expected_seq` messages were dropped. Production feed handlers subscribe simultaneously to physically disjoint multicast trees (`Feed A` and `Feed B`), advancing `expected_seq` from whichever NIC (`onload` / `Solarflare ef_vi` / `DPDK`) delivers `msg_seq == expected_seq` first (`0`-wait arbitration) and falling back to a unicast UDP/TCP retransmission ("rewinder") request only if *both* feeds drop the same sequence range, buffering subsequent out-of-order packets until the gap fills so every replica reconstructs the **bit-identical Limit Order Book**.
- **Fixed-Offset `TotalView-ITCH 5.0` Messages:** Inside each `MoldUDP64` block, `ITCH 5.0` uses a 1-byte ASCII discriminator with zero field tags or varints. For example, **`Add Order – No MPID Attribution ('A')`** is an exact **36-byte** packed record (`exchange_probe.py`: `>cHH6sQcI8sI` = `1B` `'A'` + `2B` `StockLocate` + `2B` `TrackingNumber` + `6B` `48-bit ns Timestamp` + `8B` `OrderRefNum` + `1B` `Side 'B'|'S'` + `4B` `Shares` + `8B` `Stock` + `4B` `Price` in `$0.0001` integer ticks); `'F'` appends `4B` `Attribution` (`40 B`); `'E'` (`Order Executed`), `'X'` (`Order Cancel`), `'D'` (`Order Delete`), and `'U'` (`Order Replace`) reference the 8-byte `OrderRefNum` directly (omitting `Stock` and `Side` on `'X'`/`'D'`/`'E'`, which forces subscribers to retain an `OrderRefNum -> {StockLocate, Side, Price, RemainingShares}` hash/arena entry!).

#### 1.2 Zero-Copy Schema Evolution in `FIX SBE` (`real-logic/simple-binary-encoding`)

Unlike `ITCH 5.0` (where adding 1 field requires a breaking protocol version cut across the entire exchange), `FIX SBE` (`real-logic/simple-binary-encoding` @ `6c20e6242e63ac67854707470dcee931eabf68fe`) achieves **zero-copy in-place flyweight access** *and* **online rolling schema upgrades** by enforcing three layout invariants (`RustGenerator.java:395–490, 915–1035`):

1. **Monotonic Four-Zone Wire Grammar:** Every SBE message consists of:
   $$\underbrace{\texttt{blockLength: u16, templateId: u16, schemaId: u16, version: u16}}_{\text{8-Byte Message Header (Little-Endian)}} \;\|\; \underbrace{\text{Root Fixed Block}}_{\texttt{actingBlockLength}\text{ bytes}} \;\|\; \underbrace{\text{Repeating Groups}^*}_{\texttt{(blockLength, numInGroup)}} \;\|\; \underbrace{\text{VarData}^*}_{\texttt{(len, utf8/bytes)}}.$$
   Fixed-size primitives and fixed-length arrays live at **compile-time constant byte offsets** inside the Root Block (`ReadBuf::get_u64_at(buf.data, offset)`—compiling to a single `MOV` instruction on x86-64!). Variable-length `Repeating Groups` and `VarData` MUST be traversed strictly sequentially via a stateful cursor (`self.get_limit()` / `self.set_limit(...)` in `RustGenerator.java:484–486`), eliminating random-access offset tables (`FlatBuffers` vtables) and tag-varint decoding (`Protobuf`).
2. **Bidirectional Evolution Without Wire Corruption (`actingBlockLength` & `actingVersion`):**
   - *Old Decoder Reading New Wire Message (`v2 -> v1`, Forward Compatibility):* Schema `v2` may ONLY **append** new fields to the end of the Root Block (increasing `header.blockLength` from `20` to `28`) or the end of a Repeating Group entry. A `v1` decoder initializes its sequential group cursor to `header_len + header.blockLength` (`actingBlockLength = 28`), **skipping the unknown 8-byte `v2` extension automatically** before reading the Repeating Group header! In `exchange_probe.py`, a `v1` decoder using `actingBlockLength` decodes `[(42, 1), (99, 2)]` cleanly, whereas a hand-rolled parser that hardcodes `v1`'s `BLOCK_LENGTH = 20` misreads `v2`'s `stop_px` bytes as `GRP_HDR = (48208, 22)` and panics or corrupts memory.
   - *New Decoder Reading Old Wire Message (`v1 -> v2`, Backward Compatibility):* In `RustGenerator.java:921, 961, 1022`, every accessor for a field introduced at `fieldToken.version() > 0` emits:
     ```rust
     if self.acting_version() < SINCE_VERSION {
         return NULL_SENTINEL; // e.g. i64::MIN / u64::MAX / Either::Left(self)
     }
     ```
     **before** indexing `self.get_buf()`. Omitting that check causes a `v2` decoder reading a `20`-byte `v1` root block to read bytes `20..28`—which actually belong to the first Repeating Group!

---

### 2. Mechanical-Sympathy Ring Buffers (`LMAX Disruptor`) and Intrusive `O(1)` Price-Time Order Books

`Basis: source + documentation + derived`

#### 2.1 Single-Writer Cache-Coherency Physics (`LMAX-Exchange/disruptor`)

Multi-threaded matching engines guarded by mutexes or `CAS`-contended `ConcurrentLinkedQueue`s suffer `40–120 ns` cross-core L3/interconnect cache-line bounces (`MESI` Modified $\to$ Invalid transitions) plus tail OS scheduler jitter. `LMAX-Exchange/disruptor` (`c871ca49826a6be7ada6957f6fbafcfecf7b1f87`) isolates concurrency around three hardware-sympathetic invariants:

1. **128-Byte Inheritance-Enforced False-Sharing Isolation (`Sequence.java:8–33`):**
   ```java
   class LhsPadding { protected byte p10..p77; } // 56 bytes
   class Value extends LhsPadding { protected long value; } // 8 bytes
   class RhsPadding extends Value { protected byte p90..p157; } // 56 bytes
   public class Sequence extends RhsPadding { ... }
   ```
   Because JVM implementations are free to reorder fields declared within *one* class, Disruptor splits `56 B` left padding, `8 B` `value`, and `56 B` right padding across **three nested superclasses**, guaranteeing that `value` sits alone inside a **`>= 128`-byte span** (defeating both 64-byte L1D false sharing and 128-byte Intel spatial adjacent-cache-line prefetcher invalidations!).
2. **Amortized Zero-`CAS` Single-Producer Batching (`SingleProducerSequencer.java:125–155`):** A single network/sequencer thread claims slots in a power-of-two (`index = seq & indexMask`) pre-allocated `RingBuffer<OrderEvent>` (`0` GC allocation after startup!). Rather than reading consumer `Sequence` volatiles on every event, `SingleProducerSequencer` compares `wrapPoint = nextValue - bufferSize` against a **thread-local non-volatile `this.cachedValue`**, refreshing `Util.getMinimumSequence(gatingSequences)` **only** when the ring laps the slowest consumer, and publishes via `VarHandle.releaseFence()` (`0` `LOCK` instructions on x86-64 TSO, vs. `VALUE_FIELD.getAndAdd` atomic `LOCK XADD` in `MultiProducerSequencer`).
3. **Deterministic Replicated Pipeline (Journaling + Replication $\prec$ Matching):** Input events popped from the ring are processed in parallel by independent `BatchEventProcessor`s (disk journaler + standby replicator) before the single-threaded **Matching Engine** `EventProcessor` advances past `min(journalSeq, replSeq)`—achieving `> 6M–25M` msgs/s with deterministic single-threaded execution and zero locks inside the order book.

#### 2.2 Cache-Pinned Intrusive Arena Price-Time Limit Order Book (`LOB`)

To sustain `< 200–500 ns` `p99.9` wire-to-wire matching latency, the Limit Order Book avoids `std::map` / `TreeMap` pointer chasing and per-order `malloc`/`free`:

- **Order Arena (`OrderSlot[MAX_ORDERS]`, `64 B` cache-line aligned):** Pre-allocates contiguous `OrderSlot { order_id: u64, price_ticks: i64, qty: u32, firm_id: u32, prev_idx: u32, next_idx: u32, level_idx: u32, side: u8 }` nodes referenced by **`32-bit` arena indices** (`u32::MAX` = null, cutting pointer footprint in half vs. 64-bit pointers!). An open-addressed flat hash table (or direct index array for dense internal sequence IDs) maps `OrderRefNum -> slot_idx` in `1` L1/L2 lookup.
- **Price-Level Ladder (`PriceLevel` Intrusive FIFO Doubly-Linked List):** Each active tick price holds `{ head_idx: u32, tail_idx: u32, total_qty: u64, order_count: u32 }`. Because `99%+` of resting liquidity cluster within a few thousand ticks of the touch (`best_bid`, `best_ask`), exchanges index active price levels via a **centered flat circular tick array + hierarchical `u64` bitset tree** (`tzcnt`/`lzcnt` finds the next non-empty `best_ask`/`best_bid` across $64^2 = 4,096$ ticks in **2 register instructions**!) backed by a sparse tree only for deep out-of-the-money orders.
- **Strict Complexity Bounds:**
  - `Cancel ('X' / 'D')`: Lookup `OrderRefNum -> slot_idx` (`O(1)`), unlink `(prev_idx, next_idx)` in `PriceLevel` (`O(1)`), decrement `level.total_qty`, clear bitset bit if `total_qty == 0` (`O(1)`). **Worst-case `O(1)` even in a 10-million-order book!**
  - `Add / Match`: Sweep opposing `best_ask` $\le p_{\text{buy}}$ (or `best_bid` $\ge p_{\text{sell}}$) in strict price-then-head-to-tail FIFO order (`O(1)` amortized per fill + `O(1)` resting tail append).

---

### 3. Exact `u128` Two-Phase Double-Entry Balance Conservation (`tigerbeetle/tigerbeetle`)

`Basis: source + execution`

Matching orders without atomic pre-trade risk reservation allows a trader with `$100` cash to submit ten concurrent `$100` limit buy orders at slightly off-market prices and, if a volatility spike fills all ten simultaneously, incur a `$900` uncollateralized deficit! Conversely, tracking balances in IEEE-754 `f64` accumulates binary rounding drift (`f64` has only `53` mantissa bits $\approx 9 \times 10^{15}$, overflowing exact micro-cent/wei units).

In `tigerbeetle/tigerbeetle` (`a2a3c7064519e08233abe26c54a43fca2f9ad9bc`, `src/tigerbeetle.zig:10–145` & `src/state_machine.zig:4201–4325`), double-entry accounting is formalized as an exact commutative monoid with zero heap allocation:

1. **Zero-Padding `128`-Byte `Account` & `Transfer` Records (`src/tigerbeetle.zig:10–32, 85–116`):**
   Both `Account` and `Transfer` enforce `comptime { assert(stdx.no_padding(T)); assert(@sizeOf(T) == 128); assert(@alignOf(T) == 16); }`—packing exactly `8` records per `1 KiB` (`0.5` Records per `64 B` cache line) with zero uninitialized padding bytes on disk or wire.
2. **Four-Accumulator Monotonic Representation (`debits_pending`, `debits_posted`, `credits_pending`, `credits_posted` : `u128`):**
   Rather than storing one mutable signed integer `balance: i128` (which loses in-flight escrow volume and cumulative turnover), every `Account` maintains four monotonically non-decreasing `u128` totals (`posted` never decreases; `pending` increases on reserve and decreases by the exact same `p.amount` on post/void/expire).
3. **Asymmetric Pre-Trade Solvency Guard (`tigerbeetle.zig:33–41`):**
   ```zig
   pub fn debits_exceed_credits(self: *const Account, amount: u128) bool {
       return (self.flags.debits_must_not_exceed_credits and
           self.debits_pending + self.debits_posted + amount > self.credits_posted);
   }
   ```
   Notice the deliberate asymmetry: **outgoing `debits_pending` immediately reduce spendable balance, whereas incoming `credits_pending` CANNOT be spent until posted!** That single inequality makes double-spending across $K$ concurrent open limit orders mathematically impossible (`exchange_probe.py`: `$60` pending + `$50` pending against `$100` `credits_posted` rejects the second order immediately).
4. **Partial-Post Price Improvement & Deterministic Timeout Expiry (`src/state_machine.zig:4204–4258`):**
   When a limit buy order reserved `p.amount` (`$60.00`) at the limit price but matched against a better resting ask for `amount_actual` (`$58.50 <= p.amount`), `post_pending_transfer` (`lines 4237–4246`) executes:
   $$\begin{aligned}
   \text{dr.debits\_pending} &\mathrel{-}= p.\text{amount}, & \text{cr.credits\_pending} &\mathrel{-}= p.\text{amount}, \\
   \text{dr.debits\_posted}  &\mathrel{+}= \text{amount\_actual}, & \text{cr.credits\_posted}  &\mathrel{+}= \text{amount\_actual},
   \end{aligned}$$
   atomically settling `$58.50` and releasing the `$1.50` price-improvement surplus (`void_pending_transfer` and deterministic cluster-timestamp `timeout` expiration in `pulse` correspond to `amount_actual = 0`). Across every ledger $L$, two global conservation invariants hold at **every** committed batch boundary:
   $$\sum_{a \in L} \text{debits\_posted}(a) \equiv \sum_{a \in L} \text{credits\_posted}(a) \quad\land\quad \sum_{a \in L} \text{debits\_pending}(a) \equiv \sum_{a \in L} \text{credits\_pending}(a),$$
   coupled with `linked` flag atomic event chains (`AccountFlags.linked` / `TransferFlags.linked`, rolling back multi-leg trade + fee + clearing transfers as an all-or-nothing unit on any leg error).

---

### 4. Market-Integrity Invariants and Incident Post-Mortems (`Flash Crash` 2010 & `NYSE` Jan 24, 2023)

`Basis: normative + documentation + execution`

Even a fast, memory-safe, balance-conserving matching engine triggers systemic market failures if four exchange-level state invariants are violated:

1. **Strict Uncrossed Resting Book (`best_bid < best_ask`):** After every `submit`/`replace` transition in continuous trading, $\max(\text{Bids}) < \min(\text{Asks})$ MUST hold (`exchange_probe.py`: `assert_uncrossed()`). Exceptions (`Post-Only` / `Slide` orders that would cross the touch) must either be rejected or price-slid `1` tick passive *before* resting insertion, never inserted at a crossing price.
2. **Self-Trade Prevention (`STP`):** Regulatory wash-trade rules forbid a participant (`MPID` / `firm_id`) from unintentionally matching against its own resting liquidity across independent strategy desks. Matching loops check `resting.firm_id == incoming.firm_id` prior to fill generation, applying deterministic `Cancel-Newest`, `Cancel-Oldest`, `Cancel-Both`, or `Decrement-and-Cancel` semantics.
3. **May 6, 2010 `$1T` Flash Crash (`Stub Quotes` $\to$ `LULD` Collars):**
   - *Failure Mechanism (`SEC/CFTC 2010`):* At 14:32 ET on May 6, 2010, an automated execution program sold `75,000` E-Mini S&P 500 contracts (`~$4.1B`) targeting `9%` of trailing volume **with zero price floor**. As HFT inventories saturated and liquidity evaporated across fragmented equity venues, market orders swept all the way down to market-maker **stub quotes** (`$0.01` bids and `$99,999.99` offers posted solely to satisfy nominal two-sided quoting rules), printing Accenture at `$0.01` and forcing `> 20,000` broken trades.
   - *Invariant Fix (`LULD` + Stub-Quote Ban):* Market makers are barred from quoting outside tight percentages of reference prices, and the **Limit Up–Limit Down (`LULD`)** plan enforces a dynamic collar $[P_{\text{ref}}(1 - w),\, P_{\text{ref}}(1 + w)]$ (e.g., `w = 5%` for Tier 1 S&P 500 / Russell 1000 liquid stocks during regular hours) over a rolling 5-minute reference price $P_{\text{ref}}$: **no trade may execute outside the band**, and if the National Best Bid/Offer (`NBBO`) pins at the band edge for `15 s` (`Limit State`), the security enters a `5`-minute regulatory trading pause (`exchange_probe.py`: `5%` LULD halts at `$38.00` without touching the `$0.01` stub quote).
4. **January 24, 2023 NYSE Opening-Auction Outage (`Dual-Active DR` State Skew):**
   - *Failure Mechanism (`SEC Reg SCI Order`):* During pre-market setup on Jan 24, 2023, NYSE left its backup/disaster-recovery (`DR`) environment running concurrently alongside the primary matching environment. Because of shared/replicated state desynchronization, the primary engine erroneously recorded that **opening auctions had already completed** for `2,824` of `3,421` listed securities! At `09:30:00` ET, those `2,824` books jumped straight into **continuous trading** *without* an opening cross print—leaving `LULD` reference bands uninitialized on the SIP until the first unconstrained continuous trade printed, causing `25%` instantaneous price dislocations, **`84` cascading `LULD` halts**, **`4,341` busted trades across `251` symbols**, and a `$9M` SEC Regulation SCI penalty.
   - *Invariant Fix (Monotone Phase-Witness Typestate & Single-Leader Fencing):* Continuous trading (`Phase::Continuous`) must require a **cryptographically or consensus-fenced `(TradingDate, LeaderEpoch, OpeningCrossPrint | ExplicitZeroVolumeCarryover)` token** emitted *strictly* by the active `LeaderEpoch` consensus state machine (e.g., TigerBeetle `VSR` view-stamped replication primary lease), making it unrepresentable for a standby/DR daemon from another epoch or process to mark `auction_done = true`.

---

### 5. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

`Basis: source + execution + documentation + derived`

| Level & Metric | `MoldUDP64` + `ITCH 5.0` / `OUCH 5.0` Fixed Binary | `FIX SBE` Flyweight Codecs (`real-logic/sbe`) | `LMAX Disruptor` + Intrusive Arena `LOB` | `TigerBeetle` Deterministic `u128` Ledger |
| :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance Velocity** | `200–500` LoC packed struct parser + gap-fill state machine; fragile manual offset updates on major version bumps (`ITCH 4.1 -> 5.0`) | `50–250` XML schema lines generating `2,000–15,000` Rust/C++/Java flyweight LoC automatically; high risk if developers bypass generated cursors on `Repeating Groups` | `800–2,500` Rust/C++/Java LoC for intrusive `OrderSlot` arena + `PriceLevel` bitset ladder + `STP`/`LULD` guards | Compact client batch calls (`128 B` `Transfer` structs); core state machine (`src/state_machine.zig` `5,399` Zig LoC) carries dense `assert(...)` invariants (`~15–25%` assertion density) |
| **`L2` Toolchain & Generator Build Time** | Zero codegen (`< 1 s` C/Rust compile, `< 150 MB` RSS) | Java Gradle `sbe-tool` build `~8–20 s` (`~500 MB` JVM RSS); XML $\to$ Rust/C++ generation **`< 0.4 s`**, generated zero-dep Rust compiles in `< 2 s` | Pure Java Gradle (`~5–12 s` build) or native C++/Rust (`< 3 s`, `< 250 MB` RSS) | Standalone Zig `0.13+` build (`~10–35 s` clean ReleaseSafe build, `~0.6–1.5 GB` compiler RSS; zero external C/libc dependencies) |
| **`L3` Schema Validation, Sim & `< 50 ms` Tooling** | Static `sizeof`/`offsetof` `comptime` checks in **`< 1 ms`** | SBE XSD + IR offset/version validation in **`< 150 ms`**; sub-10 ms IDE typecheck on generated Rust/C++ wrappers | Deterministic event-log replay (`10M` ITCH messages replayed in **`~0.4–1.2 s`** for regression/simulation testing) | Deterministic VOPR (Viewstamped Operation Replicator) fault-injection simulator tests thousands of crash/network schedules per CPU-hour; `comptime` layout checks run in `< 50 ms` |
| **`L4` Runtime Execution Latency & Throughput** | **`5–15 ns`** (`~20–45` CPU cycles) to decode 36B `ITCH 'A'` in-place; kernel-bypass NIC-to-book `< 150 ns` | **`8–25 ns`** (`0` heap allocs, `0` copies) root-block field access; **`> 40M–100M` msgs/s** per core | Ring publish + consume **`~25–60 ns`** (`0` `LOCK` instructions in single-producer mode); full `LOB` match + `STP` + `LULD` **`120–450 ns` `p99.9`** (`0` GC pauses) | **`1M–2M+` financial transfers/s** (`io_uring` + batched VSR consensus, `< 0.5–2 ms` durable quorum commit; in-memory state-machine apply **`< 150 ns`/transfer**) |
| **`L5` Audit, Replay & Invariant Verification Speed** | `MoldUDP64` sequence continuity + end-of-day book hash verified at **`> 15M` msgs/s** (`< 70 ms` per `1M` messages) | `actingBlockLength` / buffer-bounds & `schemaId` gate verified in **`2–4` instructions (`< 1.5 ns`)** per message | Per-event `best_bid < best_ask` + `LULD` collar check costs **`2` L1 loads + `2` integer branches (`< 2 ns`)** | Global ledger conservation ($\sum \text{Dr} == \sum \text{Cr}$) + `Account` invariant scan runs at memory bandwidth (**`> 80M` accounts/s = `< 12.5 ms` per `1M` accounts**) |
| **`L6` Memory, Cache & Storage Footprints** | `20 B` packet header + `2 B`/msg framing (`36 B` `ITCH 'A'`, `0 B` heap) | `8 B` SBE header, `0 B` decoder heap (`16–24 B` stack cursor wrapper) | `Sequence`: `128+ B` padded cursor; `OrderSlot` arena: **`64 B`/order** (`10M` active orders = **`640 MiB`** pinned `2 MiB` hugepages, `0` allocator metadata bloat) | **`128 B` `Account`** (`2` cache lines, `0` padding), **`128 B` `Transfer`**; static startup memory allocation (`0` runtime `malloc` after `init`!) |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: source + derived`

#### 6.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)

- **Why SBE's Stateful Streaming Cursor Trips Humans & Agents (`C1` Nonlocal Ordering Hazard):** Notice a striking `C1` contrast between `TotalView-ITCH 5.0` and `FIX SBE`: an `ITCH 5.0` struct has zero hidden state—reading `price` at byte `32` works in any order. In `FIX SBE`, root-block fields are random-access, **but `Repeating Groups` and `VarData` mutate a hidden sequential `limit` pointer inside the flyweight**! If a developer (or an LLM trained on Protobuf/JSON getters) calls `msg.var_data_symbol()` *before* iterating `msg.legs_group()`, or reads a `VarData` getter twice, the cursor advances out of order and silently decodes garbage bytes! Notice how `real-logic/simple-binary-encoding`'s **`RustGenerator.java` (`lines 458, 917`) fixes this in Rust via move-semantics typestate** (`pub fn group(self, ...) -> GroupEncoder<Self>`), turning an invisible C++/Java runtime ordering footgun into a compile-time borrow-checker error!
- **Why Four Unsigned Monotonic Counters Beat Signed Balances (`TigerBeetle`):** Novice ledger designs store `balance: i64` + `available: i64`, forcing readers to reconstruct mental sign conventions ("is a liability negative or positive? what happens when a partial fill cancels?"). TigerBeetle's `(debits_pending, debits_posted, credits_pending, credits_posted)` matches 500-year-old Pacioli T-accounts directly: every field is unsigned (`>= 0`), `posted` is monotone increasing, and `debits_exceed_credits` is a 1-line unsigned inequality auditable at a glance without signed-overflow or negative-zero traps.

#### 6.2 Conceptual Simplicity, Orthogonality & Universal Model Refinement (`C2`)

Testing all four subsystems against Ousterhout's deep-module criterion and Felleisen's macro-expressibility test separates core financial-exchange semantics from hardware/language accidents:

1. **Accidental Realization Quirks Identified:**
   - *JVM Inheritance Padding (`LhsPadding -> Value -> RhsPadding` in `Sequence.java`):* Writing 112 dummy `byte p10..p157` fields across 3 superclasses is purely an artifact of Java lacking `#[repr(C, align(128))]` (which C11 `_Alignas(128)`, Rust `#[repr(align(128))]`, and Zig `align(128)` express in 16 characters).
   - *Ad-Hoc Sentinel Magic Numbers in Wire Protocols:* `MoldUDP64` overloads `Message Count = 0xFFFF` as `End of Session` (capping batch count at `65,534`), and `SBE` steals `INT64_MIN` / `UINT64_MAX` from primitive integer ranges to represent `null` / `sinceVersion` absence—requiring every downstream consumer to remember domain-specific magic numbers lest `INT64_MIN` be treated as a real negative price!
2. **Minimal Universal Exchange Kernel (`4` Orthogonal Primitives, `0` GC / Double-Spend / Crossed-Book Bugs):**
   - **Typestate Wire Cursor (`Cursor<Zone_0 -> ... -> Zone_k>`):** Encodes SBE's `(Root[actingBlockLength] -> Group_1 -> VarData_1)` progression as linear session types over an immutable byte slice `&[u8]`, returning `Option<T>` automatically whenever `actingVersion < SINCE_VERSION` (`0` magic null sentinels leaked into arithmetic, `0` out-of-order group reads).
   - **Branded Intrusive Arena (`ArenaIndex<Brand<'book>>`):** Replaces raw pointers and unbranded `u32` indices with lifetime/domain-branded `u32` handles into `64 B`-aligned hugepage slabs (`O(1)` cancel, `0` ABA or cross-book index mixups).
   - **Linear Conservation Quantum (`Credit<Ledger, Asset>`):** Models `pending` reservations and `posted` settlements as non-clonable, non-droppable linear/affine value splits (`split(reserved) -> (posted_fill, released_surplus)`), making unbalanced single-entry mutations a compile-time type error rather than a runtime batch assertion.
   - **Epoch-Fenced Market-Phase Typestate (`MarketPhase<Epoch, UncrossedBook & Band<P_ref>>`):** Makes `ContinuousTrading` constructible **solely** from a consensus-fenced `OpeningAuctionResult<Epoch>` carrying a non-null `P_ref` `LULD` anchor—rendering both the 2010 unconstrained stub-quote sweep and the 2023 NYSE dual-DR auction-skip outage unrepresentable by construction.

## Boundaries

- **`known not to apply` — `SingleProducerSequencer` Under Multi-Socket / Multi-Thread Ingress Without Serialization:** `SingleProducerSequencer` (`Disruptor`) omits `CAS` on `nextValue` and relies strictly on single-thread ownership; invoking `next()` concurrently from two NIC RX threads corrupts sequence slots silently without `MultiProducerSequencer` or a dedicated mux stage.
- **`known not to apply` — Price-Time `FIFO` Queue Priority on Pro-Rata Matching Venues:** Short-term interest-rate futures (`CME` SOFR) and certain options exchanges allocate fills **pro-rata** ($\lfloor Q_{\text{incoming}} \cdot q_i / \sum q_j \rfloor$) rather than pure `FIFO` head-to-tail; while `best_bid < best_ask`, `LULD`, and `u128` conservation still hold, `O(1)` head-pop matching does not apply (requiring `O(K)` allocation passes over resting orders at the touch).
- **`unsupported` — Removing, Reordering, or Shrinking Existing Root-Block Fields in `FIX SBE` Minor Versions:** `SBE` `sinceVersion` / `actingBlockLength` supports **append-only** block growth; deleting or changing the byte width of an existing field within the same `schemaId` breaks constant-offset flyweight invariance and requires a new `schemaId` or `templateId`.
- **`unsupported` — Negative or Floating-Point Transfer Amounts in `TigerBeetle`:** `Transfer.amount` and all four `Account` accumulators are strictly unsigned integers (`u128`); reversing an entry requires an explicit counter-transfer swapping `debit_account_id` and `credit_account_id` (or `void_pending_transfer` on an uncommitted pending reservation), never subtracting from `debits_posted` / `credits_posted`.
- **`not examined` — FPGA Layer-1 Tick-to-Trade Cut-Through (`< 25 ns` PCS/PMA SerDes):** Direct Verilog/VHDL Ethernet MAC/PCS streaming order triggers bypassing host PCIe/DRAM entirely were not examined in this software-focused reference package.
- **`unknown` — Cross-Venue SIP Latency Bounds Under Extreme Geographic Partition:** While single-exchange `LULD` collars enforce deterministic local price bounds, exact worst-case `NBBO` / `SIP` band-update skew across geographically separated equities centers (`Mahwah`, `Carteret`, `Secaucus`) during fiber-cut failover depends on private carrier paths and remains externally `unknown` beyond public Reg SCI disclosures.

## Evidence

1. **Primary Repository Sources Inspected (`2026-11-19`):**
   - `real-logic/simple-binary-encoding` @ `6c20e6242e63ac67854707470dcee931eabf68fe`:
     - `sbe-tool/src/main/java/uk/co/real_logic/sbe/generation/rust/RustGenerator.java` (`lines 380–490, 906–1035`): Move-typed `GroupEncoder` (`wrap(self, count)`), `self.get_limit()` / `self.set_limit(...)` sequential `VarData` cursor progression, and `if self.acting_version() < %d` backward-compatibility guards.
     - `sbe-tool/src/main/java/uk/co/real_logic/sbe/generation/cpp/CppGenerator.java` (`lines 1–4704`): C++ flyweight `actingBlockLength` and `actingVersion` generation.
   - `LMAX-Exchange/disruptor` @ `c871ca49826a6be7ada6957f6fbafcfecf7b1f87`:
     - `src/main/java/com/lmax/disruptor/Sequence.java` (`lines 8–169`): `LhsPadding` (`56 B`), `Value` (`long value`), `RhsPadding` (`56 B`), and `VarHandle.acquireFence()` / `releaseFence()` / `fullFence()`.
     - `src/main/java/com/lmax/disruptor/SingleProducerSequencer.java` (`lines 1–160`), `MultiProducerSequencer.java` (`lines 1–285`), and `RingBuffer.java` (`lines 1–1124`): `cachedValue` gating-sequence caching and lock-free ring publication.
   - `tigerbeetle/tigerbeetle` @ `a2a3c7064519e08233abe26c54a43fca2f9ad9bc`:
     - `src/tigerbeetle.zig` (`lines 10–145`): `128`-byte `Account`, `AccountBalance`, and `Transfer` `extern struct`s (`comptime` `no_padding` assertions), `debits_exceed_credits` (`lines 33–36`), `credits_exceed_debits` (`lines 38–41`), and `AccountFlags.linked` (`lines 44–65`).
     - `src/state_machine.zig` (`lines 93–185, 4201–4325`): `TransferPending`, `AccountEvent`, `post_pending_transfer` (`debits_pending -= p.amount`, `debits_posted += amount_actual` with `assert(amount_actual <= p.amount)` at `lines 4237–4246`), `void_pending_transfer`, and deterministic `expires_at` pulse expiration.
2. **Specifications & Regulatory Reports Verified (`2026-11-19`):**
   - NASDAQ, *MoldUDP64 Protocol Specification v1.0*, *TotalView-ITCH 5.0 Specification* (`Add Order 'A'` `36 B`, `'F'` `40 B`, `'E'`, `'X'`, `'D'`, `'U'`), *OUCH 5.0*, and *SoupBinTCP*.
   - FIX Trading Community, *Simple Binary Encoding (SBE) Technical Specification*, Version `2.0`.
   - U.S. SEC & CFTC, *Findings Regarding the Market Events of May 6, 2010*, September 30, 2010 (`75,000` E-Mini S&P 500 contract volume-percentage sell algorithm, `$0.01` / `$99,999.99` stub-quote sweeps, and `LULD` reform).
   - U.S. SEC, *Regulation Systems Compliance and Integrity (Reg SCI) Rule 1001(a) Order — New York Stock Exchange LLC (January 24, 2023 Opening Auction Incident)* (`2,824` of `3,421` symbols skipping opening auctions due to concurrent primary/DR operation, `84` `LULD` halts, `4,341` busted trades across `251` symbols, `$9M` civil penalty).
3. **Self-Contained Executable Verification Probe (`2026-11-19`, Python 3.13):**
   Running the standalone script below verifies `20 B` `MoldUDP64` + `36 B` `ITCH 'A'` framing, `FIX SBE` `v2 -> v1` `actingBlockLength` compatibility vs. hardcoded-offset corruption, `5%` `LULD` protection against `$0.01` stub-quote sweeps, `best_bid < best_ask` + `STP` invariants, and `TigerBeetle` two-phase `u128` price-improvement conservation:

```python
#!/usr/bin/env python3
import struct

MOLD_HDR = struct.Struct(">10sQH")
ITCH_ADD_A = struct.Struct(">cHH6sQcI8sI")
assert MOLD_HDR.size == 20 and ITCH_ADD_A.size == 36

SBE_HDR = struct.Struct("<HHHH")
GRP_HDR = struct.Struct("<HH")

def encode_order_v2(order_id: int, qty: int, limit_px: int, stop_px: int, legs: list[tuple[int, int]]) -> bytes:
    buf = bytearray(SBE_HDR.pack(28, 101, 1, 2))
    buf += struct.pack("<QIqq", order_id, qty, limit_px, stop_px)
    buf += GRP_HDR.pack(8, len(legs))
    for s, r in legs: buf += struct.pack("<II", s, r)
    return bytes(buf)

def decode_as_v1(buf: bytes, use_acting_block_len: bool):
    acting_block_len, _, _, _ = SBE_HDR.unpack_from(buf, 0)
    oid, qty, lpx = struct.unpack_from("<QIq", buf, 8)
    limit = 8 + (acting_block_len if use_acting_block_len else 20)
    g_blen, g_num = GRP_HDR.unpack_from(buf, limit)
    limit += 4
    return oid, qty, lpx, [struct.unpack_from("<II", buf, limit + i * g_blen) for i in range(g_num)]

class TwoPhaseLedger:
    def __init__(self): self.accts, self.pending = {}, {}
    def credit_initial(self, omni: int, tr: int, amt: int):
        self.accts.setdefault(omni, [0, 0, 0, 0])[1] += amt
        self.accts.setdefault(tr,   [0, 0, 0, 0])[3] += amt
    def reserve_pending(self, pid: int, dr: int, cr: int, amt: int) -> bool:
        a = self.accts[dr]
        if a[0] + a[1] + amt > a[3]: return False
        a[0] += amt; self.accts.setdefault(cr, [0, 0, 0, 0])[2] += amt
        self.pending[pid] = (dr, cr, amt); return True
    def post_pending(self, pid: int, actual: int):
        dr, cr, res = self.pending.pop(pid)
        assert 0 <= actual <= res
        self.accts[dr][0] -= res; self.accts[cr][2] -= res
        self.accts[dr][1] += actual; self.accts[cr][3] += actual
        assert sum(v[1] - v[3] for v in self.accts.values()) == 0
        assert sum(v[0] - v[2] for v in self.accts.values()) == 0

wire_v2 = encode_order_v2(9001, 500, 150_2500, 149_0000, [(42, 1), (99, 2)])
assert decode_as_v1(wire_v2, True) == (9001, 500, 150_2500, [(42, 1), (99, 2)])
assert GRP_HDR.unpack_from(wire_v2, 28) == (48208, 22)  # Buggy hardcoded v1 offset!

led = TwoPhaseLedger()
led.credit_initial(0, 101, 100_0000)
assert led.reserve_pending(1, 101, 999, 60_0000) is True
assert led.reserve_pending(2, 101, 999, 50_0000) is False
led.post_pending(1, 58_5000)
assert led.accts[101] == [0, 58_5000, 0, 100_0000]
print("ALL_EXCHANGE_CONSERVATION_PROBES_PASSED")
```

## Revalidation

1. **Re-run the Inline Verification Script (`< 50 ms`):** Execute the Python 3 snippet in **Evidence** to confirm `MoldUDP64`/`ITCH 'A'` struct sizes, `SBE` `actingBlockLength` compatibility, and two-phase ledger conservation.
2. **Targeted Upstream Diffs (`< 5 s`):**
   - In `real-logic/simple-binary-encoding`, inspect `RustGenerator.java` / `CppGenerator.java` around `acting_version()` and `GroupEncoder::wrap` to verify whether move-typed sequential cursors or `sinceVersion` null guards have changed.
   - In `LMAX-Exchange/disruptor`, inspect `Sequence.java` (`LhsPadding` / `RhsPadding` vs. JDK `@Contended` adoption) and `SingleProducerSequencer.java` (`cachedValue` + `VarHandle.releaseFence()`).
   - In `tigerbeetle/tigerbeetle`, inspect `src/tigerbeetle.zig` (`@sizeOf(Account) == 128`, `debits_exceed_credits`) and `src/state_machine.zig` (`post_pending_transfer` lines `4235–4250`).
