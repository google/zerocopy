# USB-PD EPR VBUS Discharge, PCIe Flit-Mode Credit Flow Control, and SMBus/I2C Bus Recovery: Timer, Credit and Lockup Invariants in Zephyr, Linux, LitePCIe and Corundum

## Summary

Three hardware link protocols share one failure shape: a peer stops cooperating while it still owns a shared physical resource (VBUS voltage, receive-buffer credits, the SDA wire), and the survivor must restore a safe state using only timers and counters. This report records what the pinned open-source implementations actually do, what the governing specifications require, and where the two diverge.

- **USB Power Delivery Extended Power Range (EPR, 28/36/48 V) is not implemented by either examined policy engine.** At the pinned revisions the Linux TCPM has no EPR_Request / EPR_Mode message types and no keep-alive states, and the Zephyr USB-C subsystem defines EPR timing constants that nothing references and EPR message enums that only a message-name table references. Every hard-reset and VBUS-sequencing statement below is therefore evidence about the Standard Power Range (SPR, at most 20 V fixed, 21 V programmable) code that an EPR port would have to extend.
- **The Linux TCPCI sink-disconnect threshold formula cannot be encoded above a 31.25 V contract.** The 10-bit, 25 mV/LSB register saturates at 25.575 V; the driver returns `-EINVAL` for 36 V and 48 V requests (re-computed in probe P1).
- **Zephyr arms its SenderResponseTimer with the 5500 ms NoResponse constant, not the 24-30 ms tSenderResponse constants it defines**, arms PSTransitionTimer with the 500 ms SPR value only, and delegates hard-reset vSafe0V / vSafe5V sequencing to application callbacks.
- **The Linux sink hard-reset path re-enables the sink power path with a 5 V assumption after a 650 ms timeout even if VBUS never dropped** (the code itself notes "There is no guarantee that VBUS is on in this state").
- **No pinned FPGA core implements PCIe 6.0 flit mode, PAM4 or L0p.** LitePCIe's soft PHY trains 2.5/5.0/8.0 GT/s only; Corundum sits above vendor hard IP. What they do contain is directly reusable: LitePCIe's modular credit gate is exact under the specification's advertisement bound (exhaustively checked), Corundum gates Posted and Non-Posted traffic independently and self-accounts completion space before issuing a read.
- **Letting Completions overtake blocked Non-Posted requests is not by itself sufficient for deadlock freedom**: in a two-port toy model, bypass with a shared transmit buffer still deadlocks; only a reserved completion resource removes every deadlocked state.
- **SMBus and I2C specify two different lock-up recoveries that are routinely conflated.** I2C (NXP UM10204) is edge-based: up to nine SCL pulses. SMBus 3.2 is time-based: a device must reset its interface when SMBCLK is low for 25-35 ms, and for a stuck SMBDAT the specification only *recommends* that the controller hold SMBCLK low for at least 35 ms. Linux and Zephyr both implement nine-pulse variants, differ in where they emit STOP, and neither can recover a target that holds SCL low.

## Applicability

**Subjects and how they relate.** Four repository revisions were read directly and one specification was read in full text:

| Subject | Role in this report | Scope examined |
| --- | --- | --- |
| `zephyrproject-rtos/zephyr` | RTOS USB-C policy engine and bit-banged I2C controller | all 21 files of `subsys/usb/usb_c/`, `include/zephyr/drivers/usb_c/usbc_pd.h`, `drivers/i2c/i2c_bitbang.c` |
| `torvalds/linux` | Reference TCPM/TCPCI port manager, I2C core, PCIe flit register definitions | `drivers/usb/typec/tcpm/{tcpm.c,tcpci.c}`, `include/linux/usb/{pd.h,tcpm.h,tcpci.h}`, `drivers/i2c/{i2c-core-base.c,algos/i2c-algo-bit.c,busses/i2c-gpio.c}`, `Documentation/i2c/fault-codes.rst`, `include/uapi/linux/pci_regs.h`, `drivers/pci/pcie/tlp.c` |
| `enjoy-digital/litepcie` | Open FPGA PCIe core with a soft LTSSM and Data Link Layer | `litepcie/phy/soft/{ltssm.py,dll/*.py}`, `litepcie/core/crossbar.py`, `litepcie/tlp/controller.py`, vendor PHY wrappers |
| `corundum/corundum` | Open 100G NIC; PCIe requester/completer logic above vendor hard IP | `fpga/lib/pcie/rtl/{pcie_us_if_rq.v,dma_if_pcie_rd.v,pcie_tlp_fc_count.v}` |
| SMBus Specification 3.2 | Normative timing for the management bus | full text, timeout and clock-extension clauses |

The subjects are independent implementations; the report compares each against the protocol rule it implements and against the others. Nothing here describes their combination in one product.

**Exact observation versus extension.** Source statements hold for the exact revisions in `REPORT.json`. Statements about the USB Power Delivery specification, the PCI Express Base Specification and NXP UM10204 are *not* first-hand: those texts were not retrieved (USB-IF distributes a ZIP archive, PCI-SIG restricts access), so they are reported through the citations and constants that the pinned sources carry and through secondary summaries, and are labelled as such. Probe results labelled "toy model" are properties of small models written for this report, never of the upstream systems.

**Configuration assumptions.** Linux observations are independent of board devicetree except where noted (`port->self_powered`, optional `set_auto_vbus_discharge_threshold`). Zephyr observations cover `CONFIG_USBC_CSM_SINK_ONLY` and `CONFIG_USBC_CSM_SOURCE_ONLY` paths. LitePCIe soft-PHY observations apply only when the soft PHY (not a vendor hard IP wrapper) is instantiated.

## Findings

### 1. USB Power Delivery: timers, hard reset and VBUS discharge

#### 1.1 The timing envelope as encoded by the two stacks

Basis: source (both stacks); the "specification" column is what the stacks' own comments cite, not a first-hand reading.

| Parameter | Cited specification range | Linux `include/linux/usb/pd.h` | Zephyr `usbc_pd.h` | What actually arms the timer |
| --- | --- | --- | --- | --- |
| tSenderResponse | 24-30 ms | `PD_T_SENDER_RESPONSE 60` ("24 - 30ms, relaxed") | 24 / 27 / 30 ms (MIN/NOM/MAX) | Linux: 60 ms. Zephyr: **5500 ms** (see 1.2) |
| tPSTransition (SPR) | 450-550 ms | `PD_T_PS_TRANSITION 500` | 450 / 500 / 550 ms | both 500 ms |
| tPSTransition (EPR) | 830-1020 ms | not defined | 830 / 925 / 1020 ms | never used |
| tPSHardReset | 25-35 ms | `PD_T_PS_HARD_RESET 30` | 25 / 35 ms | Linux 30 ms, Zephyr 35 ms |
| tSafe0V | <= 650 ms | `PD_T_SAFE_0V 650` | `PD_T_SAFE_0V_MAX_MS 650` | Linux only (timeout fallback) |
| tSafe5V | <= 275 ms | not defined | `PD_T_SAFE_5V_MAX_MS 275` | never used |
| tSrcTurnOn | not cited | `PD_T_SRC_TURN_ON 275` | not defined | Linux |
| tSrcRecover | not cited | `PD_T_SRC_RECOVER 760`, `_MAX 1000` | not defined | Linux |
| tNoResponse | 4.5-5.5 s | `PD_T_NO_RESPONSE 5000` | 4500 / 5500 ms | see 1.2 |
| tSinkTx | 16-20 ms | `PD_T_SINK_TX 16` | 16 / 20 ms | Linux source-side AMS start |
| vSafe0V | <= 0.8 V | (TCPC event) | `PD_V_SAFE_0V_MAX_MV 800` | not referenced in the Zephyr policy engine |
| vSafe5V | >= 4.75 V (minimum only) | `VSAFE5V 5000` | `PD_V_SAFE_5V_MIN_MV 4750` | not referenced in the Zephyr policy engine |
| nHardResetCount | 2 | `PD_N_HARD_RESET_COUNT 2` | `PD_N_HARD_RESET_COUNT 2` | both |

Linux deliberately widens tSenderResponse to twice the cited maximum; this trades conformance for tolerance of scheduling jitter in a kernel worker. A partner that answers at 31-60 ms is accepted by Linux and would be hard-reset by a strictly conformant port.

#### 1.2 Zephyr: three timer bindings that differ from the constants beside them

Basis: source. All three lines are quoted from `subsys/usb/usb_c/` at the pinned revision.

1. `usbc_pe_common.c` line 116: `usbc_timer_init(&pe->pd_t_sender_response, PD_T_NO_RESPONSE_MAX_MS);`. The object named for the SenderResponseTimer is given the 5500 ms NoResponse duration. `PD_T_SENDER_RESPONSE_MIN_MS`, `_NOM_MS` and `_MAX_MS` (24/27/30) have no reference anywhere in the 21-file directory. The shared super-state `pe_sender_response_run` uses this one timer both for sink states (`PE_SNK_SELECT_CAPABILITY` -> `PE_SNK_HARD_RESET`) and for source states whose comments describe NoResponseTimer semantics, so a Zephyr sink whose Request is never answered waits about 5.5 s, not at most 30 ms, before issuing Hard Reset. Whether this is intentional is unknown; it is a deviation from the range the header itself documents.
2. `struct usbc_timer_t pd_t_no_response` is declared (`usbc_pe_common_internal.h` line 260), started (`usbc_pe_src_states.c` line 692) and stopped (line 206), but the directory contains no `usbc_timer_init` call for it and no `usbc_timer_expired` test of it. Runtime behaviour of starting that never-initialised timer object was not executed here.
3. `usbc_pe_snk_states.c` line 32: `usbc_timer_init(&pe->pd_t_ps_transition, PD_T_SPR_PS_TRANSITION_NOM_MS);`. The EPR constants (830/925/1020 ms) are unreferenced. Derived consequence: if this state machine were driven through an EPR-magnitude voltage step, a source using the 830-1020 ms allowance would be hard-reset by the sink's 500 ms timer on every transition.

Zephyr also contains no VBUS level sequencing of its own in the policy engine: the sink leaves `PE_SNK_Transition_to_default` when the application callback `policy_is_snk_at_default(dev)` returns true (`usbc_pe_snk_states.c` line 628), the source when `policy_check(dev, CHECK_SRC_PS_AT_DEFAULT_LEVEL)` returns true (`usbc_pe_src_states.c` line 553). The only in-stack voltage gate found is Type-C attach: `Attached.SRC` is entered only when `usbc_vbus_check_level(vbus, TC_VBUS_SAFE0V)` holds (`usbc_tc_src_states.c` lines 206-210). The discharge invariant is thus an *application obligation*, invisible in the stack's types.

#### 1.3 EPR support status

Basis: source.

- Linux `pd.h` data-message enum reads `PD_DATA_ENTER_USB = 8, /* 9-11 Reserved */ PD_DATA_REVISION = 12`; the extended-message enum ends at `PD_EXT_SINK_CAP_EXT = 15`; `PD_MAX_REV` is `PD_REV30`. The header does define field macros for an EPR adjustable-voltage Augmented PDO (`PDO_EPR_AVS_APDO_*`) and EPR power fields in the extended sink capabilities structure (`epr_min_pdp`, `epr_op_pdp`, `epr_max_pdp`), and the only EPR-specific code in `tcpm.c` logs a received Augmented PDO of type `APDO_TYPE_EPR_AVS`. There is no EPR mode entry, no EPR capability exchange and no keep-alive timer.
- Zephyr defines `PD_DATA_EPR_REQUEST = 9`, `PD_DATA_EPR_MODE = 10`, `PD_EXT_EPR_SOURCE_CAP = 17`, `PD_EXT_EPR_SINK_CAP = 18`, used only in a message-name string table; the sink ready state answers any extended message through `extended_message_not_supported(dev)` (`usbc_pe_snk_states.c` line 442).

Basis: documentation (secondary summaries of USB PD 3.1; not verified against the USB-IF text). EPR adds a liveness obligation absent from SPR: the sink sends EPR_KeepAlive every 250-500 ms (tSinkEPRKeepAlive) and the source hard-resets if none arrives within 750-1000 ms (tSourceEPRKeepAlive). The design intent is that a 48 V contract cannot outlive a hung sink policy engine by more than about one second. Neither examined stack has a state in which to host that timer.

#### 1.4 Linux TCPM hard-reset sequencing

Basis: source (`drivers/usb/typec/tcpm/tcpm.c`, state handlers at lines 6076-6190 and VBUS event handlers).

| Role | State | Action | Leaves when |
| --- | --- | --- | --- |
| both | `HARD_RESET_START` | disable PD receive, drop alternate modes | source: after `PD_T_PS_HARD_RESET` (30 ms); sink: immediately |
| source | `SRC_HARD_RESET_VBUS_OFF` | VCONN off, `tcpm_set_vbus(port, false)` | TCPC reports vSafe0V, then `PD_T_SRC_RECOVER` (760 ms); fallback timeout `PD_T_SAFE_0V + PD_T_SRC_RECOVER` = 1410 ms |
| source | `SRC_HARD_RESET_VBUS_ON` | VCONN on, VBUS on, PD receive on | VBUS-on event; else `SRC_UNATTACHED` after `PD_T_PS_SOURCE_ON` (480 ms) |
| sink | `SNK_HARD_RESET_SINK_OFF` | auto-discharge threshold set to 0, `tcpm_set_charge(port, false)` when PD-capable | VBUS-off event -> `SNK_HARD_RESET_WAIT_VBUS`; **or** 650 ms timeout -> `SNK_HARD_RESET_SINK_ON` |
| sink | `SNK_HARD_RESET_WAIT_VBUS` | wait | VBUS-on event; else unattached after 1275 ms |
| sink | `SNK_HARD_RESET_SINK_ON` | when PD-capable: `tcpm_set_current_limit(port, ..., 5000)` and `tcpm_set_charge(port, ...)` re-enabled; threshold set for `VSAFE5V` | immediately -> `SNK_STARTUP` |

Two ordering facts matter for high-voltage contracts.

- The source side is voltage-gated when the TCPC can report vSafe0V, and time-gated otherwise. The comment in the source reads: "If tcpc fails to notify vbus off, TCPM will wait for PD_T_SAFE_0V + PD_T_SRC_RECOVER before turning vbus back on." If the TCPC never reports vSafe0V, VBUS is therefore re-applied 1410 ms after it was switched off regardless of the voltage actually present.
- The sink side has a pure timeout edge, `tcpm_set_state(port, SNK_HARD_RESET_SINK_ON, PD_T_SAFE_0V);`. The comment at `SNK_HARD_RESET_SINK_OFF` reads "VBUS may or may not toggle, depending on the adapter. If it doesn't toggle, transition to SNK_HARD_RESET_SINK_ON directly after timeout", and `SNK_HARD_RESET_SINK_ON` begins "Note: There is no guarantee that VBUS is on in this state". Derived: if a source ignores Hard Reset and keeps a 20 V contract voltage on VBUS, the sink closes its path 650 ms later while telling the charger driver the supply is 5000 mV. The sink's input stage is necessarily rated for the voltage it negotiated, so this is a *stale-voltage assumption* handed to the charger driver, not by itself an over-voltage event; whether a given charger IC misbehaves is board-specific and was not examined.

#### 1.5 The TCPCI disconnect threshold cannot represent 36 V or 48 V

Basis: source + execution (probe P1 re-evaluates the upstream integer expression).

`tcpci_set_auto_vbus_discharge_threshold()` (`tcpci.c` line 374) computes, for a fixed PD contract of `V` millivolts,

```c
threshold = ((VSRC_NEW_MIN_PERCENT * requested_vbus_voltage_mv / 100) -
	     VSINKPD_MIN_IR_DROP_MV - VSRC_VALID_MIN_MV) *
	     VSINKDISCONNECT_PD_MIN_PERCENT / 100;
/* ... */
threshold = threshold / TCPC_VBUS_SINK_DISCONNECT_THRESH_LSB_MV;

if (threshold > TCPC_VBUS_SINK_DISCONNECT_THRESH_MAX)
	return -EINVAL;
```

with `VSRC_NEW_MIN_PERCENT 95`, `VSINKPD_MIN_IR_DROP_MV 750`, `VSRC_VALID_MIN_MV 500`, `VSINKDISCONNECT_PD_MIN_PERCENT 90`, `TCPC_VBUS_SINK_DISCONNECT_THRESH_LSB_MV 25` and `TCPC_VBUS_SINK_DISCONNECT_THRESH_MAX 0x3ff`, i.e. `threshold_mV = ((95 * V / 100) - 1250) * 90 / 100` and a register ceiling of 1023 x 25 mV = 25.575 V.

| Contract | Threshold | Register | Result |
| --- | --- | --- | --- |
| 5 V | 3150 mV | 126 | ok |
| 20 V | 15975 mV | 639 | ok |
| 28 V | 22815 mV | 912 | ok |
| 36 V | 29655 mV | 1186 | `-EINVAL` |
| 48 V | 39915 mV | 1596 | `-EINVAL` |

The largest encodable contract is 31.25 V. An EPR implementation on this register layout must either change the formula, clamp, or use a scaled register; simply adding EPR states to TCPM would make the 36 V and 48 V contracts fail at the point where automatic discharge on disconnect is armed, which is exactly the protection those voltages most need.

#### 1.6 Collision avoidance on the CC wire

Basis: source. PD messages are biphase-mark coded on one CC wire with no carrier arbitration beyond idle detection, so PD 3.0 lets the source signal permission through its Rp value. Linux maps `SINK_TX_NG` to `TYPEC_CC_RP_1_5` and `SINK_TX_OK` to `TYPEC_CC_RP_3_0` (`include/linux/usb/tcpm.h` lines 23-24). In `tcpm_ams_start()` a source that wants to start an Atomic Message Sequence first drives `SINK_TX_NG`, then delays `PD_T_SINK_TX` (16 ms) if it had previously advertised `SINK_TX_OK`; a PD 3.0 sink that samples anything other than Rp 3.0 A refuses to start with `-EAGAIN` ("Sink TX No Go"). Hard Reset and Soft Reset are exempt on both sides. Derived: the residual race is the 16 ms window itself. A sink that sampled SinkTxOk just before the source changed Rp may still transmit, which is why the source waits rather than transmits immediately; an actual collision is left to the protocol layer's CRC and retry.

#### 1.7 Discharge budgets at EPR voltages

Basis: derived (single-pole RC model; arithmetic in probe P1). The Zephyr header defines tSafe0V as the time to reach vSafe0V (0.8 V, 650 ms) and tSafe5V as the time to reach vSafe5V (275 ms). The vSafe5V ceiling of 5.5 V used below appears in neither header and is taken from secondary summaries. To fall from `V0` to 0.8 V within 650 ms a passive bleed needs time constant `tau <= 650 / ln(V0 / 0.8)`; to fall to 5.5 V within 275 ms it needs `tau <= 275 / ln(V0 / 5.5)`.

| V0 | tau for 0.8 V in 650 ms | tau for 5.5 V in 275 ms | Energy in 100 uF |
| --- | --- | --- | --- |
| 20 V | 201.9 ms | 213.0 ms | 0.020 J |
| 28 V | 182.8 ms | 169.0 ms | 0.039 J |
| 36 V | 170.8 ms | 146.4 ms | 0.065 J |
| 48 V | 158.8 ms | 126.9 ms | 0.115 J |

At 20 V the vSafe0V requirement is the binding one; from 28 V upward the vSafe5V step becomes binding and the binding time constant at 48 V (126.9 ms) is 37% shorter than at 20 V (201.9 ms) while the stored energy is 5.76 times larger. This is the quantitative reason a discharge circuit sized for SPR is not automatically adequate for EPR.

### 2. PCI Express: flit mode, credit accounting and ordering

#### 2.1 What flit mode changes, and what the pinned sources contain

Basis: documentation (secondary summaries of D. Das Sharma, "PCI Express 6.0 Specification: A Low-Latency, High-Bandwidth, High-Reliability, and Cost-Effective Interconnect With 64.0 GT/s PAM-4 Signaling", IEEE Micro 41(1):23-29, 2021, DOI 10.1109/MM.2020.3039925; the PCI Express Base Specification 6.x was not read).

- 64.0 GT/s uses PAM4 (two bits per unit interval). Because raw bit-error rates rise, framing moves to fixed 256-byte flits: 236 bytes of TLP payload, 6 bytes of Data Link Layer payload, 8 bytes of CRC and 6 bytes of FEC. Fixed overhead is 20/256 = 7.8%.
- The FEC is three-way interleaved and single-symbol correcting per interleave; errors beyond that are caught by the flit CRC and repaired by flit-level replay rather than per-TLP replay.
- L0p changes the active link width without leaving L0 and exists only in flit mode; flit mode also introduces flow-control credits shared across virtual channels in addition to dedicated ones.

Basis: source.

- Linux exposes flit mode only as status and logging: `PCI_EXP_FLAGS_FLIT 0x8000 /* Flit Mode Supported */`, `PCI_EXP_LNKSTA2_FLIT 0x0400 /* Flit Mode Status */`, `PCI_ERR_CAP_TLP_LOG_FLIT 0x00040000` and `PCI_ERR_CAP_TLP_LOG_SIZE 0x00f80000 /* Logged TLP Size (only in Flit mode) */` in `include/uapi/linux/pci_regs.h`. `drivers/pci/pcie/tlp.c` sets `log->header_len = flit ? tlp_len : 4` and notes "The Prefix Log registers hold dw[4..13] in Flit mode", so a flit-mode TLP log can span 14 DWORDs (dw[0..13]) where the non-flit header log is fixed at 4 (derived from those two lines). Credits, replay and LTSSM remain entirely in hardware.
- LitePCIe's soft LTSSM docstring states its scope: "Link Training and Status State Machine (PCIe Base 4.2.6), 2.5/5.0/8.0 GT/s", with "Not implemented (back to Detect): Polling.Compliance, Loopback, L0s/L1/L2". There is no flit framing, no PAM4 and no L0p. Corundum instantiates vendor hard IP (UltraScale+, Stratix 10 H-tile and P-tile wrappers) for the link and data-link layers.

Consequently every credit and ordering result below is first-hand only for non-flit framing. It transfers to flit mode to the extent that the Posted / Non-Posted / Completion credit types survive there, which the secondary sources assert but this investigation did not verify.

#### 2.2 The modular credit gate and its soundness condition

Basis: source + execution (probe P2).

PCIe flow control keeps, per credit type, a transmitter-side CREDITS_CONSUMED counter and a CREDIT_LIMIT learned from InitFC/UpdateFC DLLPs; both wrap (8 bits for header credits, 12 bits for data credits, one data credit per 4 DWORDs = 16 bytes). LitePCIe's `litepcie/phy/soft/dll/flow_control.py` implements the gate as

```python
# Gating: CREDIT_LIMIT - (CREDITS_CONSUMED + needed) mod 2^N <= 2^(N-1).
hdr_diff  = Signal(8)
data_diff = Signal(12)
self.comb += [
    hdr_diff.eq(limit_hdr[self.tlp_type] - (consumed_hdr[self.tlp_type] + 1)),
    data_diff.eq(limit_data[self.tlp_type] - (consumed_data[self.tlp_type] + self.tlp_data)),
]
self.sync += self.ok.eq(~self.reset & (infinite[self.tlp_type] | ((hdr_diff <= 128) & (data_diff <= 2048))))
```

with payload credits `(length + 3) >> 2` (a zero Length field meaning 1024 DWORDs = 256 credits).

Probe P2 compares this predicate with ground truth computed on unbounded counters (`needed <= available`) over every 8-bit residue of CREDITS_CONSUMED:

| Condition | Mismatching cases |
| --- | --- |
| header credits, receiver never leaves more than 127 unused | 0 |
| header credits, receiver allowed up to 255 unused | 32,256 |
| data credits (12 bit, need 0..256), at most 2047 unused, sampled residues | 0 |

So the modular comparison is exactly correct while the receiver keeps outstanding credits within half of the counter range (checked here up to 127 of 256 and 2047 of 4096), and beyond that it silently blocks legitimate traffic; in the header-credit sweep every mismatch is a false block, never a false admit. This is a cross-device invariant that neither side can check locally from one DLLP.

Mutation analysis of the same predicate (V1 evidence, 8-bit case under the bound):

| Mutant | Mismatching cases | Verdict |
| --- | --- | --- |
| `<` instead of `<=` | 0 | equivalent under the advertisement bound: no test at legal credit levels can kill it |
| threshold `2^N - 1` (wrap ignored) | 256 | killed only by a zero-credit test |
| forget `+ needed` | 256 | killed only by a zero-credit test |
| threshold `2^(N-2)` | 15,872 | killed by any test above a quarter range |

Two of four plausible implementation errors are visible only when exactly zero credits remain, which is the state a throughput-oriented testbench visits least.

LitePCIe soft-DLL defaults that bound the resource footprint: receiver credits Posted 16 header / 128 data (2048 bytes of payload), Non-Posted 8 / 8, Completion infinite; UpdateFC period 30 us; receive buffer 2048 DWORDs (8 KiB), replay buffer 1024 DWORDs (4 KiB) with 16 descriptors; a fourth consecutive replay (`replay_num == 3`) raises `link_error` to request retraining.

#### 2.3 Mixed finite and infinite advertisements

Basis: source + execution of the copied predicate (P2); the consequence is derived and was not simulated in RTL.

`flow_control.py` line 89 latches `infinite[t].eq((self.fc_hdr == 0) & (self.fc_data == 0))`: a type is treated as infinite only when *both* fields are zero. The same repository's Stratix V wrapper (`litepcie/phy/svpciephy.py`) configures a real hard IP to advertise `nonposted_header = 56, nonposted_data = 0, compl_header = 0, compl_data = 0`, with the comment "An endpoint must advertise infinite completion credits ... The bare Verilog defaults advertise finite completion credits, and the hard IP then occasionally drops the second completion of a split read without reporting any error." A partner with that advertisement has finite Non-Posted header credits and infinite Non-Posted data credits. Against it, P2 shows the soft gate admits a Memory Read (no payload) but refuses the first Non-Posted TLP that carries payload (`data_diff = 4095 > 2048`), and because CREDITS_CONSUMED for that type then never advances, the refusal is permanent. An endpoint normally emits only payload-free Non-Posted requests, so the exposure is limited to soft-PHY use in a root or downstream role (configuration or I/O writes) or to atomic operations. The PCIe rule that header and data may be advertised infinite independently was not read from the normative text here; the evidence that such advertisements exist in practice is the wrapper quoted above.

#### 2.4 Ordering structure: where head-of-line blocking can and cannot occur

Basis: source.

The ordering rules exist because a Completion or Posted request queued behind a Non-Posted request that is waiting for credits can close a dependency cycle (see 2.5). The two cores resolve this at different layers.

| Core | Transmit structure | Evidence | Effect |
| --- | --- | --- | --- |
| LitePCIe soft DLL | one in-order replay queue; the next descriptor is sent when `self.enable & settled & (cur_sent \| self.fc_ok)` (`retry.py` line 302) | docstring: "TLPs stored from the Transaction Layer until acknowledged, transmitted once complete (store-and-forward) and allowed by the flow control" | a TLP without credits blocks every later TLP of every type; no bypass at this layer |
| LitePCIe crossbar | separate arbitration stage for write-only ports | comment: "The controller blocks RD requests when the max number of pending requests have been sent ... To avoid blocking write_only ports when RD requests are blocked, a separate arbitration stage is used." | bounds Non-Posted requests in flight by tag count before they reach the single queue |
| Corundum `pcie_us_if_rq.v` | two ports with independent credit predicates: `port_have_credit[0] = have_np_credit_reg` (reads), `port_have_credit[1] = have_p_credit_reg` (writes); arbitration selects a port only if `port_seg_valid[cur_port][0] && port_have_credit[cur_port]` | lines 871-873: `have_p_credit_reg <= (tx_fc_ph_av > 8) && (tx_fc_pd_av > (max_payload_size_fc_reg << 1)); have_np_credit_reg <= tx_fc_nph_av > 8;` | the arbiter skips a class without credit and moves to the next port, so a credit-starved read port does not stall writes; a class is eligible only with more than 8 header credits in hand (the reason for the margin is not stated in the source) |
| Corundum `dma_if_pcie_rd.v` | requester-side completion accounting | parameters `CPLH_FC_LIMIT`, `CPLD_FC_LIMIT`; a read is issued only if `active_cplh_fc_av_reg && active_cpld_fc_av_reg` (line 820); worst-case completion headers per request from the read-completion boundary, e.g. `(req_pcie_addr_reg[5:0]+req_op_count_reg+63) >> 6` | when the limits are non-zero, completions outstanding never exceed the reserved budget. The module default `CPLH_FC_LIMIT = 0` disables the check (`!CPLH_FC_LIMIT \|\| ...`); the three top-level cores set non-zero limits (770 / 2400 for Stratix 10 H-tile, 1144 / 2888 for P-tile, 64 or 256 header credits for UltraScale depending on interface width) |

The last row is the general pattern: an endpoint advertises infinite Completion credits to the link, so the only thing preventing receive overflow is that the *requester* reserves completion space before each Non-Posted request. The LitePCIe comment quoted in 2.3 records what happens when a hard IP is configured the other way round: silently dropped completions.

A width detail in Corundum's credit counter: `pcie_tlp_fc_count.v` line 149 computes payload credits from the low 9 bits of the 10-bit Length field: `seg_fc_d = ({tlp_hdr[seg*TLP_HDR_WIDTH+96 +: 9] == 0, tlp_hdr[seg*TLP_HDR_WIDTH+96 +: 9]}+3) >> 2;`. That is exact for payloads up to 512 DWORDs (2048 bytes) and under-counts for the 4096-byte maximum payload size, which the surrounding logic does not otherwise use (`max_payload_size > 5 ? 5 : max_payload_size` clamps a related computation).

#### 2.5 Toy model: bypass alone does not remove deadlock

Basis: execution (toy model P3 written for this report; not LitePCIe, Corundum or any vendor IP).

Two ports each originate K Non-Posted requests; each received request must be answered by a Completion; a port has a transmit buffer of `txbuf` TLPs and a Non-Posted receive buffer (`npbuf` credits); Completion credits are infinite. Breadth-first search over all interleavings reports deadlocked (non-terminal, no enabled transition) states:

| K | txbuf | npbuf | FIFO, head only | bypass, shared buffer | bypass + reserved Completion slot |
| --- | --- | --- | --- | --- | --- |
| 2 | 2 | 1 | 0 | 0 | 0 |
| 3 | 2 | 1 | 1 | 1 | 0 |
| 4 | 2 | 1 | 10 | 4 | 0 |
| 3 | 3 | 1 | 0 | 0 | 0 |
| 4 | 3 | 2 | 0 | 0 | 0 |
| 2 | 1 | 1 | 1 | 1 | 0 |

Reading: deadlock appears as soon as one side can fill its shared transmit resource with Non-Posted requests while the peer's Non-Posted buffer is full (K > txbuf in this model). Allowing Completions to overtake reduces but does not eliminate deadlocked states, because a Completion that cannot be *enqueued* cannot overtake anything. Only a transmit resource reserved for Completions gives zero deadlocked states at every explored size. This is the channel-dependency argument of Dally and Seitz (IEEE Trans. Computers 36(5), 1987, DOI 10.1109/TC.1987.1676939) specialised to two message classes: the Completion class must have its own acyclic channel.

### 3. I2C and SMBus: clock stretching, timeouts and bus clear

#### 3.1 Two specifications, two mechanisms

Basis: normative (SMBus 3.2, read in full text).

- `tTIMEOUT` (detect clock low timeout) is 25 ms minimum, 35 ms maximum, in all three speed classes.
- "It is highly recommended that a target device release the bus (stop driving the bus and let SMBCLK and SMBDAT float high) when it detects any single clock held low longer than tTIMEOUT,MIN. Devices that have detected this condition must reset their communication interface and be able to receive a new START condition in no later than tTIMEOUT,MAX."
- "A timeout condition can only be ensured if the device that is forcing the timeout holds the SMBCLK low for tTIMEOUT,MAX or longer."
- Cumulative stretching is bounded separately: `tLOW:TEXT` (target, per message from START to STOP) at most 25 ms and `tLOW:CEXT` (controller, per byte) at most 10 ms. Version 3.2 uses the names TEXT/CEXT; secondary sources describing earlier versions call the same parameters SEXT/MEXT.
- For a stuck data line the specification has no requirement: "At this time there is no specification on the maximum time that a device can hold SMBDAT low after the controller raises SMBCLK after the last bit of a transaction." It recommends only that, if SMBDAT is still low tTIMEOUT,MAX after the end of a transaction, "the controller should hold SMBCLK low for at least tTIMEOUT,MAX in an attempt to reset the SMBus interface of all of the devices on the bus."

Basis: documentation (NXP UM10204 section 3.1.16 as cited by the Zephyr source comment and secondary summaries; the manual itself was not retrieved). I2C has no timeout. Its bus-clear procedure is that a controller seeing SDA stuck low sends nine clock pulses; a target that does not release within nine clocks needs a hardware reset or power cycle.

The two mechanisms are complementary, not interchangeable: SMBus recovery is *time-based* and works only on targets that implement the timeout; I2C recovery is *edge-based* and works only on targets whose state machine advances on SCL.

#### 3.2 What Linux and Zephyr implement

Basis: source.

| Aspect | Linux `i2c_generic_scl_recovery()` (`i2c-core-base.c` line 225) | Zephyr `i2c_bitbang_recover_bus()` (`i2c_bitbang.c` line 282) |
| --- | --- | --- |
| Pulse count | up to 9 (`RECOVERY_CLK_CNT 9`), loop of 18 half-cycles | always 9 |
| Early exit | yes, as soon as the bus reads free after a rising edge | no |
| STOP generation | every cycle when `set_sda` exists ("we will always create a STOP to ensure additional pulses will do no harm"); none otherwise | START, nine `i2c_write_bit(1)`, repeated START, STOP |
| SCL stuck low | detected: "SCL is stuck low, exit recovery", returns `-EBUSY` | not detected; the library "doesn't support optional protocol feature like 10-bit addresses or clock stretching" |
| No way to read the bus | "If we can't check bus status, assume recovery worked" (returns 0) | final SDA read decides 0 or `-EBUSY` |
| Timing | `RECOVERY_NDELAY 5000` ns: 7.5 us high phase + 5 us low phase per cycle, about 120 us for nine cycles (derived) | standard-mode bit timing (4.7 us low / 4.0 us high) |
| Invocation | only when a bus driver calls `i2c_recover_bus()`; `i2c-core-base.c` defines and exports it but contains no call to it | only when the application or driver calls the recover API |

Zephyr's comment documents the design disagreement directly: UM10204 "suggests the controller emit 9 SCL clock pulses", "The Linux kernel I2C bitbang recovery functionality issues a START condition followed by 9 STOP conditions", and other vendors suggest START, nine clocks with SDA high, repeated START, STOP, "The latter is what is implemented here."

Clock-stretch handling is independent of recovery. Linux's bit-banging algorithm (`sclhi()` in `i2c-algo-bit.c`) waits for SCL to read high and returns `-ETIMEDOUT` after the bit-bang adapter's own `timeout`; the GPIO bus driver sets that to `HZ / 10` (commented "100 ms") unless the firmware property `i2c-gpio,timeout-ms` overrides it. Separately, the I2C core gives any adapter that leaves `adap->timeout` at zero a transfer timeout of `HZ` (one second). `Documentation/i2c/fault-codes.rst` says of `ETIMEDOUT`: "SMBus adapters may return it when an operation took more time than allowed by the SMBus specification; for example, when a slave stretches clocks too far. I2C has no such timeouts, but it's normal for I2C adapters to impose some arbitrary limits (much longer than SMBus!) too." Both defaults exceed tTIMEOUT,MAX (by factors of 2.9 and 28.6), so SMBus conformance of a Linux controller is a per-driver property. Neither stack performs the SMBus-recommended 35 ms SMBCLK hold in the examined files.

#### 3.3 Toy model: how many pulses, and which targets remain stuck

Basis: execution (toy model P4 written for this report; not a model of any specific device).

A target is frozen while it owns SDA: either acknowledging (driving ACK low before shifting out a byte) or at any of the eight bit positions of any byte value, 2304 states in all. The controller releases SDA, so the ninth clock of a byte reads as NACK and the target stops.

| Target resets on STOP/START | Strategy | Still mid-byte afterwards | Max pulses | Mean pulses | States needing all 9 |
| --- | --- | --- | --- | --- | --- |
| yes | pulse until SDA reads high, then STOP (Linux-like early exit) | 0 | 9 | 1.00 | 1 |
| yes | always 9, then STOP (UM10204 / Zephyr-like) | 0 | 9 | 9.00 | 2304 |
| no | pulse until SDA reads high | 2048 | 9 | 1.00 | 1 |
| no | always 9 | 0 | 9 | 9.00 | 2304 |

Nine is tight: exactly one state (target acknowledging and about to send 0x00) needs all nine pulses. Early exit is nine times cheaper on average and equally effective for compliant targets, but leaves 2048 of 2304 states desynchronised for a target that does not reset its bit counter on STOP or START.

Unconditional pulsing has the opposite hazard in the write direction. A target frozen while acknowledging a byte it *received* releases SDA after one pulse; every further pulse with SDA high shifts a 1 into it. P4b counts 0 data bits for the early-exit strategy and 8 (a complete 0xFF byte) for the always-nine strategy. Basis for the real-world relevance: documentation. Linux `Documentation/i2c/gpio-fault-injection.rst` describes this state for its `incomplete_write_byte` injector: "This is a highly delicate state, the device is set up to write any data to register 0x00 (if it has registers) when further clock pulses happen on SCL. This is why bus recovery (up to 9 clock pulses) must either check SDA or send additional STOP conditions to ensure the bus has been released. Otherwise random data will be written to a device!" Linux's STOP-per-cycle is the hedge against both hazards; Zephyr's fixed nine clocks with SDA high followed by repeated START and STOP is exposed to the write-direction one (derived from the two sources; not reproduced on hardware).

The model deliberately excludes the two classes no clocking strategy can fix: a target holding SCL low (needs the SMBus timeout or a reset line) and a target whose SDA driver is latched independently of SCL (needs power cycling). The claim that nine pulses plus STOP recover any frozen target is therefore false as stated; it holds for targets whose only fault is waiting for clocks, and the pulse policy must additionally be chosen against the write-direction risk.

### 4. Cross-cutting assessment

#### 4.1 Performance and resource footprint (L1-L6)

Basis: source (line counts, constants), execution (probe timings on one host), derived (arithmetic). "Not examined" means no measurement was made; no number in this table is a benchmark of an upstream system.

| Level | USB-PD policy engines | PCIe credit / ordering logic | I2C / SMBus recovery |
| --- | --- | --- | --- |
| L1 authoring effort | Linux `tcpm.c` 9,018 lines with 103 named states, `tcpci.c` 1,057 lines; Zephyr `subsys/usb/usb_c/` 7,774 lines in 19 C source and header files. No mechanised proofs exist, so proof-to-code ratio is not applicable. Person-month and LLM token budgets: not examined | LitePCIe soft PHY 10,596 lines of Migen/Python in 36 files (Data Link Layer 2,916); Corundum `fpga/lib/pcie/rtl` 36,883 lines of Verilog in 65 files; the credit gate itself is a handful of lines | Linux recovery function 69 lines, Zephyr 39 lines |
| L2 toolchain build | not examined (no subject was built) | not examined (no synthesis or simulation run) | not examined |
| L3 analysis latency | probe P1 arithmetic: negligible | exhaustive header-credit sweeps (32,768 and 65,536 cases), a sampled data-credit sweep and deadlock search (up to 5,706 states) | 2,304-state enumeration; the whole probe file about 1.5 s wall in CPython 3.13 on one EPYC 7B12 core |
| L4 runtime behaviour | budgets, not throughput: 30 ms (Linux uses 60) response, 500 ms supply transition, 650 ms discharge, about 1 s keep-alive loss detection in EPR | one header credit per TLP, one data credit per 16 bytes; flit framing overhead 7.8%; LitePCIe UpdateFC every 30 us; link throughput not examined | Linux nine-pulse recovery about 120 us (derived); SMBus hold-low reset at least 35 ms, about 290 times longer |
| L5 checker speed | no certificates or checkers exist in either tree | none; LitePCIe ships 20 `test_soft_*.py` simulation files and Corundum 79 testbench directories under `fpga/lib/pcie/tb` (not executed here); 0 SymbiYosys `.sby` files in either repository | none |
| L6 memory / energy | timer objects only; VBUS bulk energy 0.020 J at 20 V versus 0.115 J at 48 V per 100 uF | LitePCIe replay buffer 4 KiB, receive buffer 8 KiB, 16 descriptors; FPGA LUT/BRAM use not examined | none beyond two GPIOs |

#### 4.2 Human comprehensibility and model simplicity (C1-C2)

Basis: derived from the source structure above.

**C1, comprehensibility.** The safety argument that *the sink path is never closed onto a voltage above what the load expects* is non-local in both stacks. In Linux it spans one state handler, three VBUS event handlers, the TCPC driver's threshold arithmetic and the charger driver that receives `tcpm_set_current_limit(..., 5000)`; a reader must hold about six facts across four files. In Zephyr the argument leaves the stack entirely through two boolean callbacks. Diagnostics are trace strings (`tcpm_log`, `LOG_INF("PE_SNK_Hard_Reset")`), legible to a human with a protocol analyser but carrying no stated invariant. For credits, the working-memory load is six counters per direction plus one cross-device bound that appears in neither device's code as an assertion; the equivalent `<`/`<=` mutant shows a human reviewer cannot settle the boundary by testing. For I2C, "nine clock pulses" is folklore that conflates two specifications; the Zephyr comment quoted in 3.2 is a rare case of the disagreement being written down where the reader needs it. Ease of execution by an automated agent is a different property: an agent can re-derive each of these facts mechanically, but the hidden obligations (application callback contracts, the advertisement bound) are exactly what neither a human nor an agent sees in the local code.

**C2, simplicity.** The three domains use three vocabularies for one invariant: *a grant of a shared physical resource must be reclaimable by the grantor without the grantee's cooperation*. A minimal common model has three parts: (i) a measured guard (VBUS at or below a threshold; credits available; SDA high), (ii) a bound that forces progress (PD timers and EPR keep-alive; UpdateFC and replay timers; tTIMEOUT), and (iii) a reserved return path that the blocked traffic cannot occupy (Hard Reset signalling exempt from collision avoidance; a Completion resource separate from Non-Posted; SCL owned by the controller). Under that model the "exceptions" are ordinary cases: Hard Reset is revocation, Completion bypass is the reserved path, nine clocks drain the grantee's residual state. The quirks that are *not* part of the invariant are medium-specific: 25 mV register quantisation, 8- versus 12-bit counters, open-drain wiring. The model does not make complexity vanish: where a part is missing (I2C has no bound; a shared transmit buffer has no reserved path; a sink re-enabled on a timer has no measured guard) the complexity reappears as an out-of-band reset line, a deadlock, or a stale-voltage assumption. Encoding the guard in the interface (for example, an enable operation that requires a fresh voltage reading as an argument) keeps it out of adapter and application boilerplate; this is a design suggestion, not something any examined tree does.

#### 4.3 How solutions in each domain are validated (V1-V4)

| | USB-PD | PCIe credits / ordering | I2C / SMBus |
| --- | --- | --- | --- |
| V1 specification adequacy and mutation | Basis: derived. The three Zephyr timer bindings in 1.2 are constant-substitution mutants that the tree's behaviour does not distinguish; a timer-value assertion per state would. No such check was found in the examined files | Basis: execution. P2: 0 mismatches under the bound; of four mutants one is equivalent and two die only at zero credits | Basis: execution (toy). P4 shows "until SDA high" and "always nine" are indistinguishable on compliant targets and differ on 2048 states otherwise |
| V2 lowering and checker soundness | not examined: no differential test of the two policy engines against each other or a reference interpreter | Basis: source. Simulation testbenches exist upstream (not run here); no bounded model checking artefacts; P3 is a hand-written model, not RTL | not examined |
| V3 concurrency, crash and physical faults | Basis: source. Linux runs PD events (`tcpm_pd_event_handler`) and state-machine steps, including hrtimer-delayed ones, as `kthread_work` items on one per-port worker, which removes data races but not ordering races between a timer expiry and a late VBUS event (the 650 ms edge in 1.4 is one). No fault injector for VBUS was found in the examined files | Basis: execution (toy). P3 explores all interleavings of a two-port model; PAM4 burst-error and FEC fault injection: not examined | Basis: source + documentation. Linux `i2c-gpio` creates debugfs fault injectors `incomplete_address_phase`, `incomplete_write_byte`, `lose_arbitration` and `inject_panic`; the first two stop a real transfer at an ACK so that the device holds SDA low, the read- and write-direction freezes of 3.3 (not run here) |
| V4 plant, hardware-in-the-loop and human factors | not performed. Section 1.7 gives the pass/fail thresholds a programmable-load and oscilloscope test would check (for 48 V: 5.5 V by 275 ms, 0.8 V by 650 ms) | not performed; no protocol-analyser capture was available | not performed; the SMBus hold-low recommendation is the only mechanism whose effect depends on device firmware and can only be validated on hardware |

## Boundaries

- **Not examined: the USB Power Delivery, PCI Express Base and NXP UM10204 texts.** Every statement about them is second-hand. In particular the tSenderResponse range is reported as 24-30 ms because both pinned headers say so; one secondary summary of USB PD 3.2 gives 27-33 ms. The disagreement is unresolved here.
- **Unsupported: EPR in Linux TCPM and in the Zephyr USB-C subsystem at the pinned revisions.** No finding in this report describes observed EPR behaviour of either stack. The headline hazard, a sink path closing with 5 V expectations while 48 V is present, is *not* demonstrated; what is demonstrated is the SPR code path (1.4) with the same shape and the register limit (1.5) that an EPR extension would hit.
- **Unknown: whether Zephyr's 5500 ms SenderResponseTimer binding is intentional**, and what happens at run time when the never-initialised `pd_t_no_response` timer is started. No Zephyr build was executed.
- **Unknown: whether any charger driver misbehaves on the stale 5000 mV hint** in `SNK_HARD_RESET_SINK_ON`; that depends on board hardware.
- **Not examined: Zephyr VBUS measurement drivers and TCPC drivers** (`drivers/usb_c/`), where `PD_V_SAFE_0V_MAX_MV` may be consumed; the claim in 1.2 is limited to the policy-engine directory.
- **Unsupported: PCIe 6.0 flit mode, PAM4, L0p and shared credits in LitePCIe and Corundum.** No flit retry-buffer sizing, FEC behaviour or L0p width-change race was observed anywhere; an analysis of flit retry-buffer sizing during L0p width changes could not be grounded in any pinned source.
- **Known not to apply: the toy deadlock model to real devices.** It has two ports, no switch, no Posted class and unit-size TLPs. It shows a structural condition, not that LitePCIe or Corundum deadlock. LitePCIe bounds Non-Posted requests in flight above its single queue; whether that bound is always below the queue capacity was not checked.
- **Unknown: practical reachability of the mixed-infinite credit stall (2.3).** It requires the soft PHY to transmit a Non-Posted TLP with payload to a partner advertising finite header and infinite data credits; no simulation was run.
- **Known not to apply: nine-pulse recovery to SCL-stuck or latched-SDA targets**, and SMBus timeouts to plain I2C devices.
- **Not examined: SMBus Alert, ARP, PEC, multi-controller arbitration loss during recovery, I3C.**
- **Not established: any throughput, latency, area or energy figure for an upstream system.** All measured numbers are for the probes.

## Evidence

**Repositories (read on 2026-11-19 US Pacific time; fetch timestamps 2026-11-20 01:39-02:30 UTC).** Files were fetched by exact commit from `raw.githubusercontent.com` or as commit tarballs.

- `zephyrproject-rtos/zephyr` at `fbe7a22abedfb04820714736a8038bb6af8c9751` (committed 2026-11-19): `subsys/usb/usb_c/usbc_pe_common.c` lines 116 and 1190-1280; `usbc_pe_snk_states.c` lines 32, 333-407, 442, 540-634; `usbc_pe_src_states.c` lines 43, 206, 553, 673-739; `usbc_pe_common_internal.h` line 260; `usbc_tc_src_states.c` lines 206-210; `usbc_timer.c`; `include/zephyr/drivers/usb_c/usbc_pd.h` lines 80-261 and 1003-1060; `drivers/i2c/i2c_bitbang.c` lines 11-14, 53-58, 282-320. Directory listing of `subsys/usb/usb_c/` (21 entries) confirmed from the repository tree page at that commit; identifier absence was checked with `grep -rn` over all 21 files.
- `torvalds/linux` at `8dac6df92a2e66e2098bbc69061964cfe7e8375b` (committed 2026-11-19): `include/linux/usb/pd.h` lines 44-57, 62-76, 83, 337, 663-709; `include/linux/usb/tcpm.h` lines 23-24; `drivers/usb/typec/tcpm/tcpm.c` lines 797-799, 966-972, 1890-1960, 6076-6190, 6837-6838, 6843, 6909-6910, 7012-7016; `drivers/usb/typec/tcpm/tcpci.c` lines 25-32 and 374-420; `include/linux/usb/tcpci.h` lines 162-164; `drivers/i2c/i2c-core-base.c` lines 222-304 and 1575-1576; `drivers/i2c/algos/i2c-algo-bit.c` line 76 onward (`sclhi`); `drivers/i2c/busses/i2c-gpio.c` lines 304-320, 335-336 and 597-600; `Documentation/i2c/gpio-fault-injection.rst` lines 55-84; `Documentation/i2c/fault-codes.rst` lines 128-135; `tcpm.c` lines 8891-8896 (worker setup); `include/uapi/linux/pci_regs.h` lines 497, 714, 819-820; `drivers/pci/pcie/tlp.c` lines 89-98.
- `enjoy-digital/litepcie` at `270ea39d8cd6bf7a5b62371cad0a95eb55ca8933` (committed 2026-11-19): `litepcie/phy/soft/dll/flow_control.py` lines 7-11, 21-46, 89, 97-105; `litepcie/phy/soft/dll/core.py` lines 32-41 and 65-68; `litepcie/phy/soft/dll/retry.py` lines 7-10, 299, 302; `litepcie/phy/soft/ltssm.py` lines 7-14; `litepcie/core/crossbar.py` lines 121-124; `litepcie/phy/svpciephy.py` lines 1057-1068.
- `corundum/corundum` at `1ca0151b97af85aa5dd306d74b6bcec65904d2ce` (committed 2023-12-02): `fpga/lib/pcie/rtl/pcie_us_if_rq.v` lines 381, 448, 530, 871-873; `fpga/lib/pcie/rtl/dma_if_pcie_rd.v` lines 72-75, 669-686, 820, 1386-1390; `fpga/common/rtl/mqnic_core_pcie_s10.v` lines 169-170, `mqnic_core_pcie_ptile.v` lines 170-171 and `mqnic_core_pcie_us.v` lines 174-175; `fpga/lib/pcie/rtl/pcie_tlp_fc_count.v` line 149.

**Specification read first-hand.** System Management Bus (SMBus) Specification Version 3.2, 12 January 2022, System Management Interface Forum, `https://smbus.org/specs/SMBus_3_2_20220112.pdf`: timeout definitions (page 18 of 86), AC parameter table rows tTIMEOUT, tLOW:TEXT, tLOW:CEXT with notes 3, 5 and 6, and the "SMBDAT low timeout" clause.

**Second-hand sources (web search summaries, 2026-11-20 UTC; not verified against the primary documents).** Das Sharma, IEEE Micro 41(1):23-29 (2021), DOI 10.1109/MM.2020.3039925 for flit composition, FEC and retry; USB PD EPR keep-alive ranges; NXP UM10204 Rev. 7.0 (1 October 2021) section 3.1.16 wording; Dally and Seitz, DOI 10.1109/TC.1987.1676939; PCIe ordering-table summaries.

**Probe.** One file, standard-library Python, run as `python3 link_probe.py` (CPython 3.13.15, Linux x86-64, AMD EPYC 7B12; about 1.5 s wall). P1 and P2 copy integer expressions from the cited upstream lines; P3 and P4 are toy models.

```python
#!/usr/bin/env python3
"""Micro-probes for USB-PD threshold arithmetic, PCIe credit gating, P/NP/Cpl deadlock and I2C bus clear.
P1/P2 re-evaluate arithmetic copied from upstream sources; P3/P4 are toy models written for this report."""
import itertools, math
from collections import deque

# ---- P1: Linux tcpci_set_auto_vbus_discharge_threshold() arithmetic (C unsigned integer semantics) ----
def tcpci_thresh(mv):
    thr = ((95 * mv // 100) - 750 - 500) * 90 // 100       # VSRC_NEW_MIN_PERCENT, VSINKPD_MIN_IR_DROP_MV, VSRC_VALID_MIN_MV, VSINKDISCONNECT_PD_MIN_PERCENT
    reg = thr // 25                                         # TCPC_VBUS_SINK_DISCONNECT_THRESH_LSB_MV
    return thr, reg, ("-EINVAL" if reg > 0x3ff else "ok")   # TCPC_VBUS_SINK_DISCONNECT_THRESH_MAX
for mv in (5000, 9000, 15000, 20000, 28000, 36000, 48000):
    print("P1 contract %5d mV -> threshold %5d mV, register %4d (max 1023 = 25575 mV): %s" % ((mv,) + tcpci_thresh(mv)))
print("P1 largest contract voltage the formula can encode: %d mV" % max(v for v in range(5000, 50001, 50) if tcpci_thresh(v)[2] == "ok"))
for v0 in (20.0, 28.0, 36.0, 48.0):
    print("P1 single-pole discharge from %4.1f V: tau <= %5.1f ms to reach 0.8 V in 650 ms; tau <= %5.1f ms to reach 5.5 V in 275 ms; E(100 uF) = %.3f J"
          % (v0, 650 / math.log(v0 / 0.8), 275 / math.log(v0 / 5.5), 0.5 * 100e-6 * v0 * v0))

# ---- P2: LitePCIe FlowControlTX gating predicate, exhaustive against unbounded-counter ground truth ----
def gate(limit, consumed, need, n, thr=None, strict=False, drop_need=False):
    thr = (1 << (n - 1)) if thr is None else thr
    diff = (limit - (consumed + (0 if drop_need else need))) % (1 << n)
    return diff < thr if strict else diff <= thr
def sweep(n, max_unused, needs, cstep=1, **kw):
    bad = 0
    for avail in range(max_unused + 1):
        for need in needs:
            for consumed in range(0, 1 << n, cstep):
                bad += gate((consumed + avail) % (1 << n), consumed, need, n, **kw) != (need <= avail)
    return bad
print("P2 header credits (8 bit, need=1), receiver keeps unused <= 127: mismatches =", sweep(8, 127, [1]))
print("P2 header credits, receiver over-advertises unused up to 255: mismatches =", sweep(8, 255, [1]))
print("P2 data credits (12 bit, need 0..256), unused <= 2047: mismatches =", sweep(12, 2047, range(0, 257, 16), cstep=61), "(consumed sampled every 61st residue)")
for name, kw in (("'<' instead of '<='", dict(strict=True)), ("threshold 2^N-1", dict(thr=255)), ("forget '+ needed'", dict(drop_need=True)), ("threshold 2^(N-2)", dict(thr=64))):
    print("P2 mutant %-22s: mismatching (avail, consumed) cases at unused <= 127: %d" % (name, sweep(8, 127, [1], **kw)))
inf = (56 == 0) and (0 == 0)   # infinite[t] latched from InitFC as (hdr == 0) & (data == 0)
for need, what in ((0, "MRd (no payload)"), (1, "CfgWr/IOWr (1 data credit)")):
    ok = inf or (gate(56, 0, 1, 8) and gate(0, 0, need, 12))
    print("P2 partner advertises NP hdr=56, NP data=0 (data infinite): first %-27s allowed = %s" % (what, ok))

# ---- P3: toy two-port model of Non-Posted requests and Completions sharing transmit resources ----
def explore(mode, K=2, TXCAP=2, NPBUF=1):
    """Each side wants to send K NP requests; a received NP must be answered by a Cpl.
    mode 'fifo'    : one TX FIFO, only the head may be sent (head-of-line blocking)
    mode 'bypass'  : any queued TLP with credit may be sent (Cpl passes NP) but one shared TX buffer
    mode 'reserved': Cpl passes NP and uses its own always-available slot
    NP credits = NPBUF; Cpl credits infinite (requester reserved the space before sending the NP)."""
    init = ((K, (), 0, 0), (K, (), 0, 0))            # per side: (to_originate, txq, rx_np_pending, cpl_slot)
    seen, dq, dead, done = {init}, deque([init]), 0, 0
    while dq:
        st = dq.popleft(); nxt = []
        for me in (0, 1):
            orig, txq, rxnp, cslot = st[me]; po, ptx, prx, pc = st[1 - me]
            def emit(mine, peer): nxt.append((mine, peer) if me == 0 else (peer, mine))
            if orig and len(txq) < TXCAP: emit((orig - 1, txq + ("NP",), rxnp, cslot), st[1 - me])
            sendable = range(len(txq)) if mode != "fifo" else range(min(1, len(txq)))
            for i in sendable:
                t = txq[i]; rest = txq[:i] + txq[i + 1:]
                if t == "NP" and prx < NPBUF: emit((orig, rest, rxnp, cslot), (po, ptx, prx + 1, pc))
                if t == "CPL": emit((orig, rest, rxnp, cslot), st[1 - me])
            if mode == "reserved" and cslot: emit((orig, txq, rxnp, cslot - 1), st[1 - me])     # dedicated Cpl path always drains
            if rxnp:                                                                              # service a received request
                if mode == "reserved": emit((orig, txq, rxnp - 1, cslot + 1), st[1 - me])
                elif len(txq) < TXCAP: emit((orig, txq + ("CPL",), rxnp - 1, cslot), st[1 - me])
        if not nxt:
            if all(s == (0, (), 0, 0) for s in st): done += 1
            else: dead += 1
        for s in nxt:
            if s not in seen: seen.add(s); dq.append(s)
    return len(seen), dead, done
for K, TXCAP, NPBUF in ((2, 2, 1), (3, 2, 1), (4, 2, 1), (3, 3, 1), (4, 3, 2), (2, 1, 1)):
    for mode in ("fifo", "bypass", "reserved"):
        print("P3 requests/side=%d txbuf=%d npbuf=%d %-8s: reachable states=%d deadlocked states=%d clean terminations=%d" % ((K, TXCAP, NPBUF, mode) + explore(mode, K, TXCAP, NPBUF)))

# ---- P4: toy I2C target frozen mid-transfer while it owns SDA; three controller bus-clear strategies ----
def target_states():
    for byte in range(256):
        yield ("ack", byte, 0)                        # target is driving ACK low, will then shift 'byte' out
        for i in range(8): yield ("tx", byte, i)      # target is driving bit i (MSB first)
def sda_low(s): return s[0] == "ack" or (s[0] == "tx" and not (s[1] >> (7 - s[2])) & 1)
def clock(s):                                         # one SCL pulse with the controller releasing SDA (so the 9th bit reads as NACK)
    if s[0] == "ack": return ("tx", s[1], 0)
    if s[0] == "tx": return ("tx", s[1], s[2] + 1) if s[2] < 7 else ("idle",)   # NACK sampled in the 9th clock: target stops
    return ("idle",)
def recover(s, strategy, stop_aware):
    pulses = 0
    for _ in range(9):
        if strategy == "until_sda_high" and not sda_low(s): break
        s = clock(s); pulses += 1
    if stop_aware and not sda_low(s): s = ("idle",)   # closing STOP (or the START of the next transfer) resets a compliant target
    return s, pulses
for stop_aware in (True, False):
    for strategy in ("until_sda_high", "always9"):
        res = [recover(s, strategy, stop_aware) for s in target_states()]
        print("P4 target resets on STOP/START=%-5s strategy=%-14s: frozen states=%d still mid-byte afterwards=%d max pulses=%d mean pulses=%.2f states needing 9=%d"
              % (stop_aware, strategy, len(res), sum(r[0] != ("idle",) for r in res), max(r[1] for r in res), sum(r[1] for r in res) / len(res), sum(r[1] == 9 for r in res)))
# P4b: target frozen in the WRITE direction, driving ACK for a byte it received (the state produced by
# Linux's "incomplete_write_byte" injector). Count data bits the recovery sequence clocks into it before STOP.
for strategy in ("until_sda_high", "always9"):
    acking, bits = True, 0
    for _ in range(9):
        if strategy == "until_sda_high" and not acking: break     # SDA already reads high: stop pulsing
        if acking: acking = False                                  # this pulse finishes the ACK slot
        else: bits += 1                                            # controller holds SDA high: a 1 is shifted in
    print("P4b write-direction target, strategy=%-14s: data bits clocked in before STOP=%d (%s)" % (strategy, bits, "complete spurious byte 0xff" if bits >= 8 else "no byte"))
```

Output:

```text
P1 contract  5000 mV -> threshold  3150 mV, register  126 (max 1023 = 25575 mV): ok
P1 contract  9000 mV -> threshold  6570 mV, register  262 (max 1023 = 25575 mV): ok
P1 contract 15000 mV -> threshold 11700 mV, register  468 (max 1023 = 25575 mV): ok
P1 contract 20000 mV -> threshold 15975 mV, register  639 (max 1023 = 25575 mV): ok
P1 contract 28000 mV -> threshold 22815 mV, register  912 (max 1023 = 25575 mV): ok
P1 contract 36000 mV -> threshold 29655 mV, register 1186 (max 1023 = 25575 mV): -EINVAL
P1 contract 48000 mV -> threshold 39915 mV, register 1596 (max 1023 = 25575 mV): -EINVAL
P1 largest contract voltage the formula can encode: 31250 mV
P1 single-pole discharge from 20.0 V: tau <= 201.9 ms to reach 0.8 V in 650 ms; tau <= 213.0 ms to reach 5.5 V in 275 ms; E(100 uF) = 0.020 J
P1 single-pole discharge from 28.0 V: tau <= 182.8 ms to reach 0.8 V in 650 ms; tau <= 169.0 ms to reach 5.5 V in 275 ms; E(100 uF) = 0.039 J
P1 single-pole discharge from 36.0 V: tau <= 170.8 ms to reach 0.8 V in 650 ms; tau <= 146.4 ms to reach 5.5 V in 275 ms; E(100 uF) = 0.065 J
P1 single-pole discharge from 48.0 V: tau <= 158.8 ms to reach 0.8 V in 650 ms; tau <= 126.9 ms to reach 5.5 V in 275 ms; E(100 uF) = 0.115 J
P2 header credits (8 bit, need=1), receiver keeps unused <= 127: mismatches = 0
P2 header credits, receiver over-advertises unused up to 255: mismatches = 32256
P2 data credits (12 bit, need 0..256), unused <= 2047: mismatches = 0 (consumed sampled every 61st residue)
P2 mutant '<' instead of '<='   : mismatching (avail, consumed) cases at unused <= 127: 0
P2 mutant threshold 2^N-1       : mismatching (avail, consumed) cases at unused <= 127: 256
P2 mutant forget '+ needed'     : mismatching (avail, consumed) cases at unused <= 127: 256
P2 mutant threshold 2^(N-2)     : mismatching (avail, consumed) cases at unused <= 127: 15872
P2 partner advertises NP hdr=56, NP data=0 (data infinite): first MRd (no payload)            allowed = True
P2 partner advertises NP hdr=56, NP data=0 (data infinite): first CfgWr/IOWr (1 data credit)  allowed = False
P3 requests/side=2 txbuf=2 npbuf=1 fifo    : reachable states=211 deadlocked states=0 clean terminations=1
P3 requests/side=2 txbuf=2 npbuf=1 bypass  : reachable states=211 deadlocked states=0 clean terminations=1
P3 requests/side=2 txbuf=2 npbuf=1 reserved: reachable states=196 deadlocked states=0 clean terminations=1
P3 requests/side=3 txbuf=2 npbuf=1 fifo    : reachable states=765 deadlocked states=1 clean terminations=1
P3 requests/side=3 txbuf=2 npbuf=1 bypass  : reachable states=765 deadlocked states=1 clean terminations=1
P3 requests/side=3 txbuf=2 npbuf=1 reserved: reachable states=841 deadlocked states=0 clean terminations=1
P3 requests/side=4 txbuf=2 npbuf=1 fifo    : reachable states=1747 deadlocked states=10 clean terminations=1
P3 requests/side=4 txbuf=2 npbuf=1 bypass  : reachable states=1747 deadlocked states=4 clean terminations=1
P3 requests/side=4 txbuf=2 npbuf=1 reserved: reachable states=2500 deadlocked states=0 clean terminations=1
P3 requests/side=3 txbuf=3 npbuf=1 fifo    : reachable states=1303 deadlocked states=0 clean terminations=1
P3 requests/side=3 txbuf=3 npbuf=1 bypass  : reachable states=1303 deadlocked states=0 clean terminations=1
P3 requests/side=3 txbuf=3 npbuf=1 reserved: reachable states=900 deadlocked states=0 clean terminations=1
P3 requests/side=4 txbuf=3 npbuf=2 fifo    : reachable states=5706 deadlocked states=0 clean terminations=1
P3 requests/side=4 txbuf=3 npbuf=2 bypass  : reachable states=5706 deadlocked states=0 clean terminations=1
P3 requests/side=4 txbuf=3 npbuf=2 reserved: reachable states=4096 deadlocked states=0 clean terminations=1
P3 requests/side=2 txbuf=1 npbuf=1 fifo    : reachable states=112 deadlocked states=1 clean terminations=1
P3 requests/side=2 txbuf=1 npbuf=1 bypass  : reachable states=112 deadlocked states=1 clean terminations=1
P3 requests/side=2 txbuf=1 npbuf=1 reserved: reachable states=169 deadlocked states=0 clean terminations=1
P4 target resets on STOP/START=True  strategy=until_sda_high: frozen states=2304 still mid-byte afterwards=0 max pulses=9 mean pulses=1.00 states needing 9=1
P4 target resets on STOP/START=True  strategy=always9       : frozen states=2304 still mid-byte afterwards=0 max pulses=9 mean pulses=9.00 states needing 9=2304
P4 target resets on STOP/START=False strategy=until_sda_high: frozen states=2304 still mid-byte afterwards=2048 max pulses=9 mean pulses=1.00 states needing 9=1
P4 target resets on STOP/START=False strategy=always9       : frozen states=2304 still mid-byte afterwards=0 max pulses=9 mean pulses=9.00 states needing 9=2304
P4b write-direction target, strategy=until_sda_high: data bits clocked in before STOP=0 (no byte)
P4b write-direction target, strategy=always9       : data bits clocked in before STOP=8 (complete spurious byte 0xff)
```

## Revalidation

- **EPR support appears.** `grep -n "EPR_MODE\|EPR_REQUEST\|KEEP_ALIVE" include/linux/usb/pd.h drivers/usb/typec/tcpm/tcpm.c` in Linux, and `grep -rn "EPR" subsys/usb/usb_c/` in Zephyr. Any hit outside a name table invalidates section 1.3 and makes sections 1.4-1.5 worth re-reading for the new states.
- **Zephyr timer bindings.** `grep -n "usbc_timer_init" subsys/usb/usb_c/*.c` and compare each second argument with the timer's name; three lines decide section 1.2.
- **TCPCI threshold.** Diff `tcpci_set_auto_vbus_discharge_threshold()` and the three `TCPC_VBUS_SINK_DISCONNECT_THRESH*` macros; rerun P1 with changed constants. A register scale factor or a clamp changes the 31.25 V limit.
- **Linux sink hard reset.** Read the `SNK_HARD_RESET_SINK_OFF` and `SNK_HARD_RESET_SINK_ON` cases; the finding holds while the first has a timed transition to the second and the second does not test `port->vbus_present`.
- **Credit gate.** Diff the last 10 lines of `FlowControlTX` in LitePCIe's `flow_control.py`; rerun P2. The mixed-infinite finding is decided by the single `infinite[t].eq(...)` line.
- **Corundum gating.** Check that `port_have_credit` still has one bit per traffic class in `pcie_us_if_rq.v` and that `dma_if_pcie_rd.v` still gates read issue on both `active_cpl*_fc_av_reg` flags.
- **Flit mode in open cores.** `grep -rni "flit\|pam4\|l0p" litepcie/` at a new revision; a hit means section 2.1's "unsupported" needs replacing with source findings.
- **Bus recovery.** Diff `i2c_generic_scl_recovery()` and `i2c_bitbang_recover_bus()`; rerun P4 and P4b if either changes its pulse count, exit condition or STOP placement. For hardware confirmation, the Linux `i2c-gpio` fault injectors named in 4.3 reproduce the frozen-target states without modifying a device.
- **SMBus revision.** A specification newer than 3.2 should be checked for a normative SMBDAT-low timeout, which 3.2 explicitly defers.
- A passing probe confirms only the arithmetic and the toy models; it says nothing about hardware.
