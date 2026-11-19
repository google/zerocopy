# Nanopore Squiggle Adaptive Sampling, CRISPR Coordinate Bijections, and OpenAPS Closed-Loop Insulin Dosing

## Summary

Real-time targeted nanopore DNA sequencing, CRISPR-Cas9 genome-editing verification, and closed-loop Automated Insulin Delivery (`AID`) all couple streaming biophysical measurements to irreversible physical or clinical actuation under strict latency, coordinate, and pharmacokinetic invariants. Across primary-source inspections of `nanoporetech/dorado` (`8b8fc5d36a9c0baab262a743cb175b5878e38ca6`), `LooseLab/readfish` (`dd5ea5d8396d699923d22a549ca7542547a551f6`, Payne et al., *Nat. Biotechnol.* 2021, `DOI: 10.1038/s41587-020-00746-x`), `pinellolab/CRISPResso2` (`c303946d10efd5514402cd2f0f204a3c2c080031`, Clement et al., *Nat. Biotechnol.* 2019, `DOI: 10.1038/s41587-019-0032-3`), `LoopKit/Loop` (`813f07cb18bf0d31c2dbd720b68703e454d9691e`), and `openaps/oref0` (`88cf032aa74ff25f69464a7d9cd601ee3940c0b3`), five concrete correctness and safety invariants stand out:

1. **Sub-`400 ms` Squiggle-to-Unblock Latency and `3'` Leading-Edge Strand Anchoring (`Dorado` + `readfish`)**: Nanopore R10.4.1 pores translocate single-stranded DNA `5' -> 3'` at **`~400–450 bp/s`** sampled at **`4–5 kHz`** (`~9–11` ionic-current picoamp samples/base). Selective enrichment (`Read Until`) requires GPU `libtorch` basecalling (`Dorado`) + `minimap2` PAF alignment + MinKNOW RPC pore-voltage reversal (`unblock`, `-180 mV`) within **`0.4–0.8 s` (`1–2` chunks, `< 250–360 bp` sequenced)**; a `2.2 s` Python GC/IPC stall wastes `> 1,350 bp` per off-target molecule and collapses flow-cell enrichment. Crucially, `readfish`'s `src/readfish/_config.py:45` evaluates `coord = al.r_st if al.strand == -1 else al.r_en`—anchoring panel membership at the **growing `3'` tip** of the `5' -> 3'` translocating read rather than its `5'` entry coordinate.
2. **`0`-Based Half-Open (`BED`/`BAM`/`PAF`) vs. `1`-Based Closed (`VCF`/`GFF`/`SAM`) and Strand-Asymmetric `SpCas9` Cleavage (`CRISPResso2`)**: Genomic pipelines routinely cross between `0`-based half-open intervals `[start_0, end_0)` and `1`-based closed intervals `[pos_1, end_1]` (`start_0 = pos_1 - 1`, `end_0 = end_1`). When combined with reverse-complement guide RNAs in `CRISPResso2` (`CRISPRessoCORE.py:506–575`, `default_cleavage_offset = -3` upstream of the `3'` spacer end adjacent to `5'-NGG-3'` PAM), a `20 nt` spacer spanning `0`-based `[g, g + 20)` cleaves at interbase coordinate **`g + 17` on the `+` strand** (`PAM` at `[g + 20, g + 23)`), but at **`g + 3` on the `-` strand** (`5'-CCN-3'` on `+` reference at `[g - 3, g)`). Applying the `+`-strand formula `g + 17` to a `-`-strand guide misplaces the quantification window by **`14 bp`** (missing true `1–5 bp` NHEJ indels entirely), while omitting `VCF -> BED` index conversion shifts edited-codon frame calls by **`1 bp`**.
3. **Exact `2 * peak >= end` Mathematical Singularity in `oref0` Biexponential `IOB` (`lib/iob/calculate.js:88–136`)**: Both `Loop` (`Loop#388`) and `openaps/oref0` model subcutaneous rapid-acting insulin pharmacokinetics via a biexponential Insulin-On-Board (`IOB`) curve parameterized by Duration of Insulin Action `end = dia * 60` (minutes) and time-to-peak activity `peak` (minutes), with time constant $\tau = \frac{t_p(1 - t_p/t_d)}{1 - 2 t_p / t_d}$. Direct source inspection of `oref0`'s `lib/iob/calculate.js:88–95, 130` reveals a **real unguarded boundary bug**: `rapid-acting` clamps custom `peak` to `[50, 120]` minutes while minimum `dia` is `3.0 hours` (`end = 180` minutes). Setting `dia = 3.0` and `peak = 90` (`within [50, 120]`) makes the denominator **`1 - 2 * 90 / 180 == 0`**, producing **`tau = Infinity` and `iobContrib = NaN`**! Setting `dia = 3.0` and `peak = 100` yields **`tau = -400.0` (negative time constant!)**, inverting exponential decay.
4. **Lethal `18.0182x` Glucose Unit Confusion (`mg/dL` vs. `mmol/L`) and Rate-vs-Dose (`U/hr` vs. `U`)**: Because anhydrous D-glucose has molar mass `180.156 g/mol`, `1 mmol/L = 18.0182 mg/dL` (approximated as `18` in `oref0`'s `lib/determine-basal/determine-basal.js:39–45`). Passing a `198 mg/dL` CGM reading into an Insulin Sensitivity Factor (`ISF`) expressed in `mmol/L/U` (`3.0` instead of `54.05 mg/dL/U`) commands a **lethal `32.67 U` correction bolus instead of `1.81 U`** (`18.0182x` overdose). Similarly, confusing a `5-minute` Temporary Basal Rate (`TBR` in `U/hr`, delivering `rate / 12` units per `5 min` tick) with an immediate `U` bolus introduces a `12x` dosing error.
5. **Nocturnal CGM Pressure-Induced Compression-Low V-Rebound Quarantine**: Tissue pressure when a sleeping patient lies on an interstitial electrochemical CGM sensor restricts local oxygen/glucose diffusion, creating a `15–30 min` artificial drop (`e.g., 112 -> 52 mg/dL`) that triggers zero-temp basal suspension (`negative net IOB`), followed by an instantaneous step rebound (`52 -> 115 mg/dL`, `+63 mg/dL` in `5 min`) the moment pressure lifts. Naive positive-momentum extrapolation (`eventualBG = BG + k * delta - IOB * ISF`) mistakes mechanical sensor recovery for an unannounced carbohydrate spike (`eventualBG = 324 mg/dL`) and commands a dangerous **`> 2.2 U` Super-Micro-Bolus (`SMB`) into true `112 mg/dL` euglycemia** unless gated by V-rebound morphological quarantine.

Created a runnable verification probe at `reports/nanopore-squiggle-adaptive-sampling-crispr-coordinates-and-openaps-dosing/probes/verify_genomics_and_aid_safety.py` verifying `readfish` `3'` strand coordinate anchoring and unblock latency budgets, `BED`/`VCF` + `SpCas9` strand-asymmetric cleavage coordinates, `oref0`'s `calculate.js:130` `NaN`/`tau < 0` parameter singularity, `18.0182x` unit-mixup amplification, and compression-low V-rebound `SMB` quarantine.

---

## Applicability

These findings apply directly to:

- **Streaming biosignal & hardware-in-the-loop control runtimes**, where tail latency (`p99 < 300 ms` across 512–2,675 parallel nanopore channels) directly determines physical throughput and pore survival rather than merely delaying batch output.
- **Dependent / indexed interval & strand types (`HalfOpen0<Ref, Strand>` vs. `Closed1<Ref>`)** in bioinformatics compilers, sequence-alignment DSLs, and verified clinical variant callers, eliminating silent `1 bp` coordinate shifts and `14 bp` minus-strand CRISPR cut-site inversions.
- **Safety-critical medical device control software (`IEC 62304` Class C)**, including statically proved domain preconditions on pharmacokinetic ODE/closed-form curves (`2 * t_peak < t_dia`), dimensional unit types (`MgPerDl`, `MmolPerL`, `Units`, `UnitsPerHour`), and non-Markovian sensor-fault morphology filters before irreversible actuator commands (`SMB` insulin boluses).

---

## Findings

### 1. Streaming Nanopore Squiggle Basecalling (`Dorado`) and Adaptive Unblock Control (`readfish`)

`Basis: source | documentation | execution`

Oxford Nanopore (`MinION` `512` channels / `PromethION` `2,675` channels per flow cell) measures picoampere ionic current (`squiggle`) across a biological protein nanopore at **`4–5 kHz`** while a motor enzyme ratchets single-stranded DNA **`5' -> 3'` at `~400–450 bp/s`**. Software-controlled targeted sequencing (**Adaptive Sampling / Read Until**, Payne et al., *Nat. Biotechnol.* `39:442–450`, `2021`, `DOI: 10.1038/s41587-020-00746-x`) rejects off-target molecules in real time without biochemical library capture.

Inspection of `nanoporetech/dorado` (`8b8fc5d36a9c0baab262a743cb175b5878e38ca6`, `README.md:9–72`) and `LooseLab/readfish` (`dd5ea5d8396d699923d22a549ca7542547a551f6`, `src/readfish/_config.py:35–96`) exposes the coupled latency and coordinate invariants:

1. **Translocation Latency Budget (`bp_wasted = (t_chunk + t_pipeline) * v_pore`)**:
   - `readfish` (`_config.py:90–93`) defaults to `min_chunks = 1`, `max_chunks = 2` (`0.4 s`–`0.8 s` raw signal windows = `1,600–3,200` `int16` current samples $\approx$ `180–360 bp`).
   - `Dorado` executes C++17 / CUDA / Metal `libtorch` (`CRF` / `LSTM` / `Transformer` `fast`, `hac`, `sup` models with `INT8`/`FP16` tensor-core quantization) over live `POD5` / gRPC streams, returning basecalled reads in `~50–150 ms` (`fast`/`hac`) to `mappy` (`minimap2` Cython bindings).
   - At `450 bp/s`, a `0.40 s` chunk + `0.15 s` GPU basecall/map/RPC turnaround sequences only **`248 bp`** before reversing pore voltage (`-180 mV` `unblock` pulse for `0.1 s`) to eject off-target DNA (`4–6x` target enrichment). If Python GIL contention, gRPC batch queuing, or choosing the heavy `sup` model stalls turnaround to `2.2 s` (`+ 0.8 s` chunk), **`1,350 bp`** translocate before ejection—destroying enrichment on `2–5 kb` sheared libraries and accelerating nuclease/voltage pore burnout.
2. **Biophysical `3'` Leading-Edge Coordinate Check (`_config.py:45`)**:
   In `make_decision(conf, result)` (`src/readfish/_config.py:42–47`):
   ```python
   for al in results:
       contig = al.ctg
       strand = al.strand
       coord = al.r_st if al.strand == -1 else al.r_en
       matches.append(targets.check_coord(contig, strand, coord))
   ```
   Because DNA **always enters the pore `5' -> 3'`**, a partial read prefix mapped to `0`-based half-open PAF reference coordinates `[r_st, r_en)` is moving **toward higher coordinates (`r_en`) when `strand == +1`**, and **toward lower coordinates (`r_st`) when `strand == -1`**. Checking `al.r_st` unconditionally (a classic naive bug when porting BED overlap checks) tests where the molecule *started* rather than where the pore is *headed*: a read starting `200 bp` outside a target exon and translocating *into* it gets falsely ejected (`false unblock`), whereas a read starting near the boundary of a target exon and translocating *away* into intergenic sequence gets falsely retained (`stop_receiving`) for `20+ kb`.

---

### 2. Genomic Interval Bijections (`BED` vs. `VCF`) and Strand-Asymmetric `SpCas9` Cleavage (`CRISPResso2`)

`Basis: source | normative | execution`

Genome-editing pipelines (`pinellolab/CRISPResso2` @ `c303946d10efd5514402cd2f0f204a3c2c080031`, `CRISPResso2/CRISPRessoCORE.py:23–29, 506–575`, Clement et al., `DOI: 10.1038/s41587-019-0032-3`) combine four distinct indexing conventions whose silent composition produces pervasive off-by-one (`1 bp`) and strand-mirror (`14 bp`) bugs:

| Format / Tool Layer | Start Base | End Boundary | Length Formula | Empty / Interbase Insertion `(between i-1 and i)` |
| :--- | :--- | :--- | :--- | :--- |
| **`BED` / `BAM` / `PAF` / Python slice** | `0`-based (`start_0`) | Half-open (`end_0` excluded) | `end_0 - start_0` | Zero-width `[i, i)` (`len == 0`, clean monoid!) |
| **`VCF` / `SAM` / `GFF3` / HGVS** | `1`-based (`pos_1`) | Closed (`end_1` included) | `end_1 - pos_1 + 1` | Requires anchor base (`VCF` prepends `1` left ref base!) |

**Exact Coordinate & Strand Bijection Laws**:
1. **Closed-to-Half-Open Bijection**: For any non-empty reference allele $R$ of length $L \ge 1$ at `1`-based `VCF` `POS` $= p_1$:
   $$\operatorname{to\_bed}(p_1, L) = [p_1 - 1,\; p_1 - 1 + L), \qquad \operatorname{to\_vcf}([s_0, e_0)) = (s_0 + 1,\; e_0)$$
   Note that zero-length interbase loci (**cleavage sites** and pure insertions) exist natively in `0`-based interbase coordinates (`cut_0 = k` lies strictly between `0`-based nucleotide `k - 1` and nucleotide `k`) without dummy anchor bases.
2. **Strand-Asymmetric `SpCas9` Double-Strand Break (`DSB`) Coordinate (`CRISPRessoCORE.py`)**:
   `Streptococcus pyogenes` Cas9 (`SpCas9`) recognizes a `20 nt` protospacer immediately `5'` of a `5'-NGG-3'` Protospacer Adjacent Motif (`PAM`) and introduces a blunt double-strand break **`3 bp` upstream (`cleavage_offset = -3`) of the `3'` end of the spacer** (between spacer positions `17` and `18` counting `1..20` from `5'` to `3'`). Let the `20 nt` spacer map to `0`-based half-open `[g, g + 20)` on the `+` reference genome (`verify_genomics_and_aid_safety.py`):
   - **Forward (`+`) Strand Guide** (`5'-NGG-3'` PAM at `[g + 20, g + 23)`): `5'` is at `g`, `3'` is at `g + 20`. Moving `-3` from the `3'` end places the interbase cut site at:
     $$\text{cut}_0(+) = (g + 20) + (-3) = g + 17$$
   - **Reverse (`-`) Strand Guide** (`5'-CCN-3'` reverse-complement PAM on `+` reference at `[g - 3, g)`): On the `-` strand, `5'` is at `g + 20` and **`3'` is at `g`**! Moving `3 bp` toward `5'` along the `-` strand moves **`+3` along the `+` reference**, placing the interbase cut site at:
     $$\text{cut}_0(-) = g - (-3) = g + 3$$
   **Failure Impact**: A strand-blind formula `spacer_start + 17` applied to a `-`-strand guide (`e.g., g = 500`) computes `517` instead of `503`—a **`14 bp` coordinate error** (`CRISPResso2`'s default `--quantification_window_size 1` around the cut site (`[502, 504)` vs `[516, 518)`) then misses `100%` of `1–10 bp` Cas9 indels, reporting `0%` editing efficiency on an edited clinical cell product!).

---

### 3. OpenAPS `oref0` / `Loop` Biexponential `IOB` Singularity, Unit Confusion, and CGM Rebound Guards

`Basis: source | derived | execution`

Closed-loop Automated Insulin Delivery (`AID`) controllers—`openaps/oref0` (`88cf032aa74ff25f69464a7d9cd601ee3940c0b3`, `lib/iob/calculate.js` and `lib/determine-basal/determine-basal.js`) and `LoopKit/Loop` (`813f07cb18bf0d31c2dbd720b68703e454d9691e`, `Loop#388` insulin model)—run every `5 minutes` on CGM ticks to modulate insulin pump delivery. Because subcutaneous rapid-acting insulin analogs (`humalog`/`novolog` peak `~75 min`, `fiasp`/`lyumjev` peak `~55 min`, total Duration of Insulin Action `DIA = 5–6 hours`) act with a `60–90 minute` delay relative to intravenous glucose, **every closed-loop dosing decision depends critically on subtracting active Insulin-On-Board (`IOB`)** to prevent lethal "insulin stacking" hypoglycemia.

#### A. Primary-Source Discovery: Exact `2 * peak >= end` Singularity in `oref0` (`lib/iob/calculate.js:88–136`)
In `openaps/oref0` (`lib/iob/calculate.js:83–137`), `iobCalcExponential(treatment, time, curve, dia, peak, profile)` enforces parameter bounds and then evaluates `Loop#388`'s biexponential formula:

```javascript
// openaps/oref0 lib/iob/calculate.js:88-95, 118, 130-136
if (curve === 'rapid-acting') {
    if (profile.useCustomPeakTime === true && profile.insulinPeakTime !== undefined) {
        if (profile.insulinPeakTime < 50) { peak = 50; }
        else if (profile.insulinPeakTime > 120) { peak = 120; }
        else { peak = profile.insulinPeakTime; }
    } else { peak = 75; }
}
// ... (dia minimum clamped earlier at 3 hours -> end = dia * 60 = 180 mins)
var end = dia * 60;
var tau = peak * (1 - peak / end) / (1 - 2 * peak / end);  // <--- LINE 130!
var a = 2 * tau / end;
var S = 1 / (1 - a + (1 + a) * Math.exp(-end / tau));
```

**Exact Failure Modes Verified by `verify_genomics_and_aid_safety.py`**:
1. **Division-by-Zero `NaN` Poisoning (`peak == end / 2`)**: `calculate.js` clamps `dia >= 3` hours (`end = 180` min) and `rapid-acting` custom `peak` to `[50, 120]` min **independently**, without checking the joint invariant `2 * peak < end`! At `dia = 3.0` hours and `peak = 90` minutes (both inside their allowed per-field ranges!), `1 - 2 * 90 / 180 == 0`:
   - `tau` evaluates in IEEE-754 JavaScript to `Infinity`, `a = Infinity`, `S = NaN`, and **`iobContrib = NaN`**!
   - When summed across bolus history, a single `NaN` poisons total `IOB` (`NaN`), breaking downstream safety comparisons (`if (iob > max_iob)` evaluates to **`false`** in IEEE-754 when `iob` is `NaN`!).
2. **Negative-`tau` Exponential Inversion (`2 * peak > end`)**: At `dia = 3.0` hours (`end = 180` min) and `peak = 100` minutes (also permitted by `peak <= 120`!), line 130 computes **`tau = -400.0`**, flipping $\exp(-t/\tau) = \exp(+t/400)$ into a growing positive exponential rather than a decaying pharmacokinetic tail (`Loop` avoids this in default presets by fixing `DIA = 360 min` so `2 * 75 = 150 < 360`, proving why `DIA` and `peak` must carry a **joint dependent refinement type `{ (t_p, t_d) | 0 < 2.5 * t_p <= t_d }`**).
3. **Why Truncated Linear `DIA = 3h` Stacks Insulin (`calculate.js:48–80`)**: Older pumps allowed linear/bilinear `3-hour` `DIA` curves (`iobCalcBilinear`), assuming `0%` insulin remains at `t = 180 min`. Under true `5-hour` (`300 min`) rapid-acting pharmacokinetics (`normal_t75` in probe), **`~13–18%` of a meal bolus is still active between hours `3` and `5`**; zeroing `IOB` prematurely causes post-prandial correction boluses to stack onto the uncounted tail.

#### B. Dimensional Unit Hazards (`18.0182x` `mg/dL` vs. `mmol/L` and `12x` `U/hr` vs. `U`)
In `determine-basal.js:39–45`, `convert_bg(value, profile)` checks `if (profile.out_units === "mmol/L") { return round(value / 18, 1)... }`.
- **Exact Stoichiometric Ratio**: `C6H12O6` molar mass is `180.156 g/mol`, so `1 mmol/L = 18.0156 mg/dL` (clinical standard conversion factor `18.0182`, i.e., `1 / 0.0555`).
- **Asymmetric Clinical Consequence (`verify_genomics_and_aid_safety.py`)**: At `BG = 198 mg/dL` (`11.0 mmol/L`) and target `100 mg/dL` (`5.55 mmol/L`) with true `ISF = 3.0 mmol/L/U = 54.05 mg/dL/U`, the intended correction is **`1.81 U`**. If a `mg/dL` integer (`198 - 100 = 98`) is divided by an untyped `float` `ISF = 3.0`, the naive quotient is **`32.67 U`**—an **`18.02x` overdose** capable of dropping blood glucose by `> 1,700 mg/dL` (fatal neuroglycopenia unless clamped by hardware `maxBolus`). Likewise, passing a `TBR` rate (`e.g., 2.4 U/hr`, meant to deliver `0.20 U` over `5 min`) to a bolus primitive expecting `U` causes a **`12x` overdose**.

#### C. Nocturnal CGM Pressure-Induced Compression-Low V-Rebound Hazard
Electrochemical glucose-oxidase CGM filaments measure interstitial fluid glucose, which lags capillary blood by `5–10 min` and collapses locally under mechanical tissue compression (`sleeping on the sensor`). A classic nocturnal trace `[112, 110, 68, 52, 115] mg/dL` (`5-min` ticks) exhibits two coupled hazards:
1. During the `68 -> 52 mg/dL` compression trough (`15–20 min`), the controller sets `0 U/hr` basal, accumulating **negative net `IOB` (`e.g., -0.4 U`)** relative to scheduled basal.
2. When the sleeper rolls over, interstitial perfusion returns abruptly (`52 -> 115 mg/dL`, `delta = +63 mg/dL / 5 min`). A Markovian momentum predictor (`eventualBG = 115 + 3 * 63 - (-0.4)*50 = 324 mg/dL`) misinterprets sensor recovery + negative `IOB` as a massive unannounced meal and fires a **`2.24 U` Super-Micro-Bolus (`SMB`)** into true `112 mg/dL` euglycemia! Sound AID controllers require **non-Markovian morphological quarantine**: whenever a `>= 30 mg/dL` drop into `< 70 mg/dL` recovers by `>= +25 mg/dL / 5 min` without prior carbohydrate entry, positive-delta `SMB` extrapolation must be suppressed (`QUARANTINED_COMPRESSION_LOW_REBOUND`) until 3 consecutive physiological-slope CGM ticks confirm true glycemic trend.

---

### 4. Six-Level Performance & Resource Footprint Matrix (`L1`–`L6`)

`Basis: source | documentation | execution | derived`

| Level | Metric / Resource Axis | `Dorado` + `readfish` + `CRISPResso2` (Genomics) | `Loop` / `openaps/oref0` (Closed-Loop AID) | Verification / System Engineering Implication |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | **Human & Agent Authoring Velocity** | `readfish` decision core `~500 LoC` Python; typed genomic interval + strand library `~300 LoC` (`~2–4x` bijection proof overhead) | `oref0` `IOB` + `determine-basal` `~1,800 LoC` JS; formalizing joint `DIA/peak` + unit types + `SMB` safety envelope `~3–6x` proof ratio | Dependent unit/interval types pay back immediately by making `14 bp` strand & `18x` unit bugs unrepresentable |
| **L2** | **Framework & Toolchain Build Time** | `Dorado` C++/CUDA/`libtorch` build `~8–20 min`; `readfish`/`CRISPResso2` Python wheels `< 10 s` | `oref0` Node.js zero-build (`< 2 s` install); `Loop` iOS Xcode Swift workspace build `~60–180 s` | Verify portable pure-Rust/Lean pharmacokinetic & coordinate cores once; link via C-ABI/FFI into Swift/Python |
| **L3** | **Compilation, Elaboration & Synthesis Latency** | Interval/strand linear arithmetic (`omega`/`lia`) `< 15 ms`; `minimap2` human `GRCh38` `.mmi` index build `~60–90 s` | Real-arithmetic transcendental bounds on biexponential `IOB` (`0 <= IOB(t) <= I_0` for `2.5 * peak <= end`) `~50–300 ms` (`< 30 ms` warm LSP) | Transcendental `exp(-t/tau)` monotonicity proofs factor cleanly once `tau > 0` (`2 * peak < end`) is enforced |
| **L4** | **Generated Code Execution Performance** | `Dorado` GPU (`A100`/`RTX 4090`) `~1–5 M bases/s`; `Read Until` end-to-end chunk decision **`80–250 ms` (`p99 < 400 ms` budget)** across `512–2,675` pores | `oref0` full `IOB` (`300` pump events) + `determine-basal` `< 5–25 ms` in JS (`< 50 us` in native Rust/Swift) on a `5-minute` (`300,000 ms`) BLE CGM tick | Nanopore is throughput/tail-latency bound (`GPU -> PAF -> RPC < 400 ms`); AID is ultra-low-duty-cycle (`< 0.01%` CPU) safety-bound |
| **L5** | **Proof / Certificate Verification Speed** | `BED <-> VCF` & `SpCas9` cut-site witness check `< 1 us`; alignment CIGAR reference-span check `O(#cigar_ops)` (`< 5 us`/read) | Runtime safety-monitor shield (`maxBolus`, `maxIOB`, `2*peak < end`, `NaN`-freeness, V-rebound gate) **`< 2 us` (`O(W)` window)** | Independent `< 200 LoC` verified runtime dosing shield can wrap legacy `oref0`/`Loop` heuristics in `< 5 us` |
| **L6** | **RAM, Disk & Binary Footprints** | `Dorado` `hac`/`sup` weights `~50–400 MB` VRAM; `GRCh38` `minimap2` index **`~7.5–9.0 GB` RAM**; `POD5` raw `4 kHz` stream `~15–40 GB`/flowcell | `oref0` JS bundle `< 2 MB` (`~35 MB` V8 RSS); `Loop` iOS background footprint `~25–50 MB`; BLE pump/CGM microcontroller `< 64 KB` SRAM, `< 1 mW` avg | Edge medical controllers forbid `NaN`-prone dynamic runtimes on pump MCUs; nanopore hosts require `16+ GB` unified/GPU memory |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

`Basis: derived | source`

#### (C1) Human Comprehensibility & Mental-Model Ergonomics
- **Why `0`-Based vs. `1`-Based + Reverse-Complement Overwhelms Human Working Memory**: Holding **four simultaneous binary toggles** in working memory—(`0`-based vs. `1`-based) $\times$ (half-open vs. closed) $\times$ (`+` vs. `-` reference strand) $\times$ (nucleotide locus vs. interbase cut boundary)—exceeds Miller's `4 ± 1` chunk limit even for seasoned computational biologists. Code like `al.r_st if al.strand == -1 else al.r_en` (`readfish`) or `g + 3` vs `g + 17` (`CRISPResso2`) looks "backwards" at a glance unless named by **biological direction of travel (`three_prime_leading_edge(al)`, `interbase_cut_site(guide)`)**.
- **Silent IEEE-754 `NaN` Non-Signaling Hazard in `oref0`**: In JavaScript/C/Rust floats, `NaN > max_iob` silently returns **`false`**! A clinician or engineer reading `if (iob_data.iob > profile.max_iob) { return stop_insulin(); }` assumes an ironclad upper guard, unaware that `dia = 3h, peak = 90m` at `calculate.js:130` yields `iob = NaN`, bypassing every `>` clamping guard unless written negatively (`if (!(iob <= max_iob))`) or typed over `NonNanFiniteF64`.

#### (C2) Simplicity, Orthogonality & Universal Model Refinement
- **Interbase ("Fencepost") Coordinates as the Universal Genomic Normal Form**: The perennial `BED` vs. `VCF` war disappears when nucleotides occupy unit cells `[i, i + 1)` between integer **interbase fenceposts `0, 1, ..., N`**. Under fencepost semantics:
  1. Every span (exon, spacer, deletion) is a pair of fenceposts `(a, b)` with length `b - a`;
  2. Every cleavage site (`SpCas9` DSB) or insertion locus is a degenerate zero-width fencepost `(k, k)`—requiring **zero special cases or dummy `VCF` anchor bases**; and
  3. Reverse-complementing a genome of length $N$ is a pure order-reversing involution on fenceposts $k \mapsto N - k$, turning strand-asymmetric `SpCas9` cleavage into **one strand-invariant rule**: *"advance `17` fenceposts from the guide's `5'` fencepost along its oriented direction!"* (On `+`: `g + 17`; on `-`, starting at `5'` fencepost `g + 20` and stepping `-17` yields `(g + 20) - 17 = g + 3` automatically!).
- **Linear State-Space Compartmental ODEs over Ad-Hoc Closed-Form `tau` Parameterizations**: `oref0`'s `calculate.js:130` singularity (`1 - 2 * peak / end == 0`) is an artifact of forcing a truncated finite-horizon (`t = end`) boundary condition onto a 2-compartment subcutaneous diffusion curve. Modeling insulin absorption directly as its underlying **two-compartment mass-conserving linear state-space system** ($\dot{x}_1 = -x_1/\tau_1 + u(t)$, $\dot{x}_2 = x_1/\tau_1 - x_2/\tau_2$, $\text{IOB}(t) = x_1(t) + x_2(t)$ with $\tau_1, \tau_2 > 0$) guarantees **strict positivity (`IOB >= 0`), exact mass conservation ($\int_0^\infty \text{activity}\,\mathrm{d}t = I_0$), and zero division singularities across all positive time constants**.

---

## Boundaries

1. **Modified-Base (`5mC`/`6mA`) Epigenetic Calling & RNA004 `3' -> 5'` Translocation Polarity (`known not to apply`)**: Our `readfish` `3'` leading-edge rule (`r_st` on `-1`, `r_en` on `+1`) applies strictly to **DNA** nanopore translocation (`5' -> 3'`). Direct **RNA sequencing (`SQK-RNA004`) translocates `3' -> 5'`** (entering from the `poly(A)` `3'` tail), where the leading pore edge is inverted (`5'` tip: `r_st` on `+1`, `r_en` on `-1`); applying DNA `readfish` polarity directly to direct RNA is **known not to apply**.
2. **Cas12a (`Cpf1`) Staggered `5'` Overhang Cleavage (`not examined`)**: Our single-fencepost cleavage formula covers blunt-cutting `SpCas9` (`-3` from `3'` spacer end). Class 2 Type V `Cas12a` enzymes recognize a `5'-TTTV-3'` PAM on the *`5'` side* of the spacer and cleave **staggered sites** (`~18 nt` on non-target strand, `~23 nt` on target strand), requiring a pair of strand-specific fenceposts (`not examined` in the probe).
3. **Intraperitoneal & Inhaled (`Afrezza`) Ultra-Fast Pharmacokinetics (`unknown`)**: Whether two-compartment subcutaneous biexponential curves adequately bound inhaled technosphere insulin (`peak ~12–15 min`, `DIA ~90–120 min`) under exercise-induced perfusion spikes remains clinically **`unknown`** without multi-compartment pulmonary absorption models.
4. **Hardware Pump Occlusion & Cannula Kinking Detection (`unsupported` from CGM alone)**: Distinguishing a true unannounced carbohydrate meal from silent infusion-set cannula occlusion requires pump back-pressure telemetry + ketone/imperial meal priors that are **unsupported** from univariate `5-minute` CGM glucose traces alone.

---

## Evidence

| Artifact / Source | Immutable Identity / Location | Grounded Fact / Observation |
| :--- | :--- | :--- |
| `nanoporetech/dorado` | Commit `8b8fc5d36a9c0baab262a743cb175b5878e38ca6` (`README.md:9–72`) | C++/`libtorch` CUDA/Metal `fast`/`hac`/`sup` basecalling architecture and streaming `POD5` throughput |
| `LooseLab/readfish` | Commit `dd5ea5d8396d699923d22a549ca7542547a551f6` (`src/readfish/_config.py:41–96`) | `coord = al.r_st if al.strand == -1 else al.r_en` (`line 45`), `min_chunks=1`, `max_chunks=2`, `unblock` vs `stop_receiving` |
| Payne et al. (2021) | *Nature Biotechnology* `39:442–450`, `DOI: 10.1038/s41587-020-00746-x` | Real-time `4 kHz` / `~450 bp/s` selective nanopore enrichment and pore voltage-reversal latency dynamics |
| `pinellolab/CRISPResso2` | Commit `c303946d10efd5514402cd2f0f204a3c2c080031` (`CRISPResso2/CRISPRessoCORE.py:23–29, 506–575`) | Guide spacer alignment, reverse-complement orientation, and `default_cleavage_offset = -3` quantification window |
| Clement et al. (2019) | *Nature Biotechnology* `37:224–226`, `DOI: 10.1038/s41587-019-0032-3` | Allele-specific indel/HDR quantification around Cas9 cleavage offsets |
| `openaps/oref0` | Commit `88cf032aa74ff25f69464a7d9cd601ee3940c0b3` (`lib/iob/calculate.js:83–143`, `lib/determine-basal/determine-basal.js:39–75`) | Exact `tau = peak*(1 - peak/end)/(1 - 2*peak/end)` (`line 130`) `peak >= end/2` singularity, `/ 18` `mmol/L` conversion, and `SMB` guards |
| `LoopKit/Loop` | Commit `813f07cb18bf0d31c2dbd720b68703e454d9691e` (`README.md`, `Loop#388` insulin model) | Biexponential subcutaneous `IOB` curve formulation and closed-loop basal/bolus architecture |
| Executable Verification Probe | `probes/verify_genomics_and_aid_safety.py` | Verified `ReadFish` `248 bp` vs `1,350 bp` unblock waste, `SpCas9` `517` vs `503` (`14 bp` strand delta), `oref0` `dia=3h, peak=90m -> NaN` & `peak=100m -> tau=-400`, `18.0182x` unit overdose, and V-rebound `SMB` quarantine |

---

## Revalidation

Re-run the self-contained verification probe with standard Python 3 (`>= 3.10`, zero external dependencies):

```bash
python3 reports/nanopore-squiggle-adaptive-sampling-crispr-coordinates-and-openaps-dosing/probes/verify_genomics_and_aid_safety.py
```

Expected output (`exit 0`):

```text
PASS: ReadFish fast=248 bp vs stalled=1350 bp | SpCas9 cut(+)=517 vs cut(-)=503 (delta=14 bp) | oref0 IOB(75m)=1.345U, singular(dia=3h,peak=90m)=nan, inverted_tau(peak=100m)=-400.0 | Unit mixup=32.7U vs 1.81U | Compression-low naive SMB=2.24U -> quarantined=0.00U (QUARANTINED_COMPRESSION_LOW_REBOUND)
```

Trigger revalidation if:
1. `openaps/oref0` or `Trio`/`AAPS` patches `lib/iob/calculate.js:130` to enforce `2 * peak < dia * 60` or migrates to a mass-conserving state-space compartmental solver;
2. Oxford Nanopore updates translocation motor speed beyond `450 bp/s` or `readfish` adds native direct-RNA `3' -> 5'` polarity dispatch in `_config.py`; or
3. GA4GH / VCFv4.5 updates zero-length interbase breakpoint representations.
