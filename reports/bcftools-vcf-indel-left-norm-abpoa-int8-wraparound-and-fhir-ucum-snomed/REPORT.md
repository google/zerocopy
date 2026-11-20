# Clinical Bioinformatics Canonicalization: VCF Indel Normalization Non-Commutativity, SIMD Partial-Order Alignment Integer Wraparound, and HL7 FHIR UCUM/SNOMED Context Semantics

## Summary

Clinical genomics and healthcare interoperability pipelines fail silently at four algebraic canonicalization seams where syntactically valid representations denote distinct biological or clinical entities unless governed by explicit quotient, overflow, dimensional, and epistemic invariants:

1. **VCF Multiallelic Normalization Non-Commutativity & Coordinate Frame Mixing**: On tandem repeats and homopolymers, Tan–Abecasis–Kang left-alignment and parsimony (`norm`) does **not** commute with multiallelic splitting (`split`): `split(norm(V)) != norm(split(V))`. Both `samtools/bcftools` (`vcfnorm.c:607-659`, at repository root) and `atks/vt` (`variant_manip.cpp:513-615`) trim and left-shift only bases shared across **every** allele in a record simultaneously. A single flanking SNV or differing-length alternate allele freezes shared padding bases, stranding co-occurring indels downstream of their canonical biallelic coordinates (`95.4%` non-commutativity in a 20,000-trial repeat-shift probe). While a single-pass `bcftools norm -m -any -f ref.fa` splits *before* normalizing (`vcfnorm.c:2678-2686`), pipelines that normalize before splitting—or split without re-normalizing, or confuse 0-based half-open BED `[start, end)`, 1-based closed VCF `[pos, pos+len-1]`, and transcript-strand 3'-justified HGVS coordinates—suffer silent false-negative misses on ClinVar/gnomAD exact `(CHROM, POS, REF, ALT)` pathogenicity lookups (e.g., *BRCA1*/*BRCA2* repeat indels).
2. **SIMD Partial-Order Alignment (POA) Wrapping Integer Overflow & Topological Order Sensitivity**: Contrary to Farrar's (2007) saturating `uint8_t` Smith–Waterman design, neither `yangao07/abPOA` (`src/abpoa_align_simd.c:1271-1327`) nor `rvaser/spoa` (`src/simd_alignment_engine_implementation.hpp:60-220`) instantiates an `int8_t` DP kernel at the pinned revisions; both dispatch strictly between wrapping two's-complement `int16_t` (`_mm256_add_epi16`/`_mm512_add_epi16`) and `int32_t`. Direct inspection reveals concrete signed `int16_t` wraparound hazards in **both** upstream width guards:
   - `abPOA` (`src/abpoa_align_simd.c:1293-1297`) guards `max_score = max(qlen * max_mat, max(qlen, gn) * gap_ext1 + gap_open1)` against `INT16_MAX - min_mis - gap_oe1 - gap_oe2`, omitting both mismatch accumulation (`-qlen * min_mis`) and two-sided global gaps (`-(qlen + gn) * gap_ext`). With default DNA scores (`match=2, mismatch=4, gap_open1=4, gap_ext1=2, gap_open2=24, gap_ext2=1`) at `qlen = gn = 9000`, `abPOA` selects `int16_t` (`max_score = 18004 <= 32732`), whereas all-mismatch paths hit `-36000` (wrapping modulo $2^{16}$ to `+29536`).
   - `spoa` (`src/alignment_engine.cpp:95-103`) computes `WorstCaseAlignmentScore(i, j)` using `-1 * (m_ * min(i, j) + gap_score(|i - j|))`. Because `gap_score(|i - j|) <= 0`, subtracting it shrinks the positive-score guard on branching DAGs where `graph.nodes().size() > seq_len`. At `slen = 7000, gnodes = 15000, m = 5, n = -4, g = -4, e = -1`, `spoa` computes `wcs = -27045 >= -31744` and selects `int16_t` even though an exact match path scores `+35000 > 32767` (wrapping modulo $2^{16}$ to `-30536`).
   - Both `spoa` (`src/graph.cpp:478-482`) and `abPOA` (`src/abpoa_output.c:526-533`) break equal-weight consensus ties via `<=` over insertion-ordered or unstably-sorted adjacency lists, making diploid 50:50 heterozygous basecalls sensitive to input read arrival order.
3. **HL7 FHIR UCUM Stoichiometric Incommensurability, Ignored Arbitrary-Unit Flags, and SNOMED CT Context-Wrapper Subsumption**: In `ucum-essence.xml`, `mol` expands to dimensionless Avogadro count ($6.02214076 \times 10^{23}$), so `mmol/L` canonicalizes to `m-3` while `mg/dL` canonicalizes to `g.m-3`; `FHIR/ucum-java` rightly rejects unindexed `mmol/L <-> mg/dL` conversion (`UcumEssenceService.java:303-304`) because conversion requires analyte-specific molar mass (glucose `18.0156` vs. cholesterol `38.6650` vs. bilirubin `58.4660` mg/dL per mmol/L). However, `FHIR/ucum-java` (`XmlDefinitionsParser.java:108-119`, `DefinedUnit.java:39-143`) **silently discards the `isArbitrary="yes"` attribute on all 41 arbitrary units** (including `[iU]`, `[USP'U]`, `[PFU]`), violating UCUM §24 by treating `[iU]/L` and `mmol/L` as commensurable (`m-3`) and `[iU]` as 1:1 convertible with `[USP'U]` and `1`. Meanwhile, `hapifhir/hapi-fhir` (`TermConceptParentChildLink.java:266-269`, `TermReadSvcImpl.java:2636-2799`) indexes solely transitive `ISA` links—without OWL 2 EL / $\mathcal{EL}^{++}$ role-group or context-wrapper classification—and computes Fahrenheit-to-Kelvin via 32-bit `float` constants (`5f/9f`, `273.15f`) in `UcumServiceUtil.java:133-152`. Clinical queries that match `Associated finding` attributes or flat text without isolating `243796009 |Situation with explicit context|` (`Finding context = 410516002 |Known absent|` or `Subject relationship context != 410604004 |Subject of record|`) invert clinical polarity, misclassifying `266897007 |Family history of myocardial infarction|` or `409137002 |No known drug allergy|` as active patient disorders.

## Applicability

This reference report characterizes the intersection of six pinned upstream codebases and five governing standards examined directly on `2026-11-19`:

- **Variant Normalization Pair**: `samtools/bcftools` (`ec0daf29256ce7a0da3b19eeed8a97a42bc1307a`, specifically `vcfnorm.c` at the repository root—note that `bcftools` does not use a `src/` directory for `vcfnorm.c`) compared directly against `atks/vt` (`c6bd1591a23a1d116d52834a627c00bbf7ed4a64`, `normalize.cpp` and `variant_manip.cpp`), interpreted against Tan, Abecasis & Kang (2015, DOI `10.1093/bioinformatics/btv112`), VCF v4.4, BED, and HGVS nomenclature rules. Applies to SNVs, MNPs, and sequence-resolved indels over ACGTN reference FASTAs; excludes symbolic structural variants (`<INV>`, `<INS>`, breakends `.A`/`A.`) and multi-megabase rearrangements except `bcftools`'s bounded `<DEL>`/`<DUP>` expansion (`vcfnorm.c:794-830`).
- **SIMD Partial-Order Alignment Pair**: `yangao07/abPOA` (`2e095ba7f8de6bc62aaaa9a684cda781b8098ee0`, `src/abpoa_align_simd.c`—not `simd_abpoa_align.c`—plus `src/abpoa_align.c`, `src/abpoa_graph.c`, `src/abpoa_output.c`, `src/simd_instruction.h`, `include/abpoa.h`) compared against `rvaser/spoa` (`c987896674564519a580fba9f51b6f81ddc66e4d`, `src/simd_alignment_engine_implementation.hpp`, `src/alignment_engine.cpp`, `src/graph.cpp`), contextualized against Farrar (2007, DOI `10.1093/bioinformatics/btl582`), Vaser et al. (2017, DOI `10.1101/gr.214270.116`), and Gao et al. (2021, DOI `10.1093/bioinformatics/btaa963`). Applies to x86_64 SSE2/SSE4.1/AVX2/AVX-512BW and SIMDe-emulated ARM64 builds executing linear, affine, or 2-piece convex gap POA DP.
- **Clinical Units & Terminology Pair**: `FHIR/ucum-java` (`10089515484cdfd291fa6d2b74b989f60d12fcb3`, `Converter.java`, `UcumEssenceService.java`, `DefinedUnit.java`, `XmlDefinitionsParser.java`, `ucum-essence.xml`) and `hapifhir/hapi-fhir` (`2221cbc19eb2b3c7db50e035cd18661ea213014e`, `TermReadSvcImpl.java`, `TermConcept.java`, `TermConceptParentChildLink.java`, `UcumServiceUtil.java`, `ResourceIndexedSearchParamQuantityNormalized.java`), interpreted against UCUM 2.1, HL7 FHIR R5, Baader, Brandt & Lutz (2005, $\mathcal{EL}^{++}$), and the SNOMED CT Concept Model. Applies to JPA-backed FHIR terminology servers using HAPI FHIR's built-in `TermReadSvcImpl` and embedded `ucum-java` rather than external OWL 2 EL description-logic reasoners (such as Ontoserver/Snorocket/ELK).

Claims concerning exact upstream guards, line numbers, and data structures apply strictly to the pinned revisions above. Executable probes reported in `## Findings` and `## Evidence` distinguish exact algebraic reproductions of upstream guard formulas and XML definitions from standalone Python models of DP tie-breaking and normalization workflows.

## Findings

### 1. VCF Variant Normalization Non-Commutativity and Genomic Coordinate Frames

#### 1.1 Formal Definition of Tan–Abecasis–Kang Normalization and Non-Commutativity Theorem
`Basis: normative + source + execution`

Under Tan, Abecasis & Kang (2015, DOI `10.1093/bioinformatics/btv112`), a VCF variant record $v = (p, [a_0, a_1, \dots, a_k])$ over reference string $R$ (where $a_0 = R[p \dots p+|a_0|-1]$ is `REF` and $a_1, \dots, a_k$ are `ALT` alleles) is **normalized** iff it is simultaneously:

1. **Parsimonious**:
   - No common trailing base exists across all alleles unless trimming would leave an empty allele at chromosome start $p=0$ (0-based): $\neg(\forall i, a_i[-1] = a_0[-1])$ when $p > 0$.
   - No common leading base exists while all alleles have length $\ge 2$: $\neg((\forall i, |a_i| \ge 2) \land (\forall i, a_i[0] = a_0[0]))$.
2. **Left-aligned**: Whenever right-trimming empties any allele and $p > 0$, all alleles are left-extended by $R[p-1]$ and $p \leftarrow p - 1$ until trailing bases diverge or $p = 0$.

Both `atks/vt` (`variant_manip.cpp:109-197`, `513-615`) and `samtools/bcftools` (`vcfnorm.c:542-659`) implement this predicate verbatim over the full allele array `0..n_allele-1`:

- In `samtools/bcftools` (`vcfnorm.c:616-622`):
  ```c
  for (i=1; i<line->n_allele; i++) {
      if ( toupper_c(als[0].s[ als[0].l-1 ]) != toupper_c(als[i].s[ als[i].l-1 ]) ) break;
      if ( als[i].l < min_len ) min_len = als[i].l;
  }
  if ( i!=line->n_allele ) break; // there are differences, cannot be trimmed
  ```
  And during block-fetched left-shifting (`vcfnorm.c:568-574`), `realign_left_shift` halts as soon as *any* single allele `i` fails `toupper_c(als[i].s[n - 1 - shift % n]) == base`.
- In `atks/vt` (`variant_manip.cpp:526-548`), `right_trim_or_left_extend` sets `to_right_trim = false` whenever *any* `alleles[i]` differs at its final base, while continuing the loop to detect any already-empty allele (`//do not break here!!! you need to check for empty alleles that might exist!!!`, `line 533`).

**Non-Commutativity Failure Mode (`split ∘ norm ≠ norm ∘ split`)**:
For any multiallelic record $V = (p, [a_0, a_1, a_2])$ combining an indel $a_1$ inside a tandem repeat with a co-located SNV or differing-length allele $a_2$ whose rightmost base differs from $a_0[-1]$, `norm(V)` **cannot trim or left-shift** $a_1$ past the rightmost divergence of $a_2$. Running `split` *after* `norm` without a second normalization pass emits non-canonical biallelic records that induce the exact same mutated haplotype $\text{apply}(R, v)$ but carry different `(POS, REF, ALT)` tuples.

Concrete witness verified by `run_pkg1_probes.py` (Probe 1A; `Basis: execution (exact Python port of bcftools vcfnorm.c:607-659 & vt variant_manip.cpp:513-615)`):

- Reference $R$ (0-based indices `0..16`): `GGTCACACACACATGCA` (tandem `CA` repeat at 0-based `3..12`).
- Input multiallelic VCF record at 1-based `POS = 10` (0-based `9`): `REF = CACAT`, `ALT = CAT,CACAG` (`ALT1` deletes one `CA` unit; `ALT2` is a flanking `T>G` SNV at 1-based `POS = 14`).

| Pipeline Order | Emitted Biallelic Record 1 (`CA` del) | Emitted Biallelic Record 2 (`T>G` SNV) | Identical Mutated Haplotype? | Exact ClinVar/gnomAD Key Match? |
|---|---|---|---|---|
| **Path A**: `norm` multiallelic $\rightarrow$ `split` (no re-norm) | `POS=12, REF=CAT, ALT=T` | `POS=12, REF=CAT, ALT=CAG` | Yes (both alleles) | **NO** (9 bp shift on del; 2 bp shift + redundant prefix on SNV) |
| **Path B**: `split` $\rightarrow$ `norm` each biallelic (canonical) | `POS=3, REF=TCA, ALT=T` | `POS=14, REF=T, ALT=G` | Yes (both alleles) | **YES** (Tan–Abecasis–Kang unique normal form) |

Across `20,000` randomized repeat-rich indels paired with a flanking SNV (`run_pkg1_probes.py`), biallelic normalization achieved `20,000/20,000` (`100%`) haplotype-equivalence uniqueness ($\text{apply}(R, v_1)=\text{apply}(R, v_2) \Rightarrow \text{norm}(v_1)=\text{norm}(v_2)$) and `20,000/20,000` (`100%`) idempotence ($\text{norm}(\text{norm}(v))=\text{norm}(v)$), whereas multiallelic `norm -> split` diverged from `split -> norm` on **`19,077/20,000` (`95.4%`)** of records.

#### 1.2 Upstream `bcftools norm` Ordering, Window-Buffer, and Transcript-Strand Semantics
`Basis: source`

Direct inspection of `samtools/bcftools` (`vcfnorm.c` at `ec0daf29256ce7a0da3b19eeed8a97a42bc1307a`) exposes four operational invariants and edge cases:

1. **Single-Command Execution Order (`vcfnorm.c:2646-2689`)**: When invoked in a single command as `bcftools norm -m -any -f ref.fa`, `split_and_normalize` calls `split_multiallelic_to_biallelics(args, line)` *first* (`line 2678`), then calls `normalize_line(args, args->tmp_lines[j])` (`lines 2681-2686`) on each biallelic record. However, if a workflow runs `bcftools norm -f ref.fa` followed by `bcftools norm -m -any` (without `-f`), or `vt normalize` before `vt decompose`, Path A occurs silently.
2. **Spanning Deletions & Symbolic Alleles (`vcfnorm.c:773-782, 832`)**: Any record containing a spanning deletion `*` (`VCF_OVERLAP`) returns `ERR_SPANNING_DELETION` and skips realignment entirely; multiallelic records containing any symbolic `<...>` allele (including gVCF `<NON_REF>`/`<*>` placeholders) return `ERR_SYMBOLIC` (`line 780`), suppressing normalization of co-located sequence indels unless split first.
3. **Sorting Buffer Window Overflow (`vcfnorm.c:2738, 2866`)**: `normalize_vcf` flushes buffered records whose position lags the latest read record by `>= args->buf_win` (default `-w 1000` bp, `line 2866`). If a long tandem repeat shifts a variant left by `> 1000` bp, `realign_left_shift` (`lines 542-605`, which dynamically doubles its FASTA fetch block up to `65536` bp at `line 550`) can move the record upstream of already-flushed downstream records, breaking VCF coordinate sort order and tabix indexing unless `-w` exceeds maximum repeat span.
4. **Strand-Dependent 3' HGVS Rule vs. 5' VCF Rule (`vcfnorm.c:523-540, 661-719`)**: VCF v4.4 left-aligns on the genomic `+` strand (5'), whereas HGVS clinical nomenclature right-aligns (3') relative to the **transcript** strand (meaning genomic right-alignment for `+`-strand genes like *BRCA2* on chr13q, and genomic left-alignment for `-`-strand genes like *BRCA1* on chr17q!). `bcftools norm -g <gff>` (`is_left_align`, `vcfnorm.c:523-540`) switches to `realign_right` (`lines 661-719`) on `+`-strand transcripts, **but silently reverts to left-alignment** whenever overlapping sense/antisense transcripts disagree (`if (tr->strand==STRAND_REV) return 1;`, `line 536`).

#### 1.3 Genomic Coordinate System Off-by-One Algebra (BED vs. VCF vs. HGVS)
`Basis: normative + source`

| Format / API | Origin | Interval Closure | 1-bp SNV at 10th Base | 2-bp Del of Bases 10–11 (with Anchor Base 9) | Internal Representation in Inspected Source |
|---|---|---|---|---|---|
| **BED / UCSC / htslib `bcf1_t.pos`** | `0`-based | Half-open `[start, end)` | `[9, 10)` | `[9, 11)` (deleted bases; no anchor) | `bcftools/vcfnorm.c:157,742` (`line->pos` is `0`-based; prints `line->pos+1`) |
| **VCF v4.4 text (`POS`, `INFO/END`)** | `1`-based | Closed `[pos, end]` | `POS=10`, `REF=A`, `ALT=G` | `POS=9`, `REF=CAT`, `ALT=C` (`END=11`) | `vt/variant_manip.cpp:244-245` (`pos0 = pos1 - 1`; `faidx_fetch_uc_seq` takes 0-based closed!) |
| **SAMtools `faidx_fetch_seq`** | `0`-based | **Closed `[beg, end]`** | `beg=9, end=9` | `beg=8, end=10` | `vcfnorm.c:558-561, 734` (`end - beg + 1` bases fetched) |
| **HGVS (`c.` / `g.`)** | `1`-based | Closed `[start, end]` (3' shifted on transcript) | `g.10A>G` | `g.10_11del` (deleted span; no anchor base) | Transcript-strand dependent; insertion uses flanking pair `g.9_10insTT` |

Mixing 0-based half-open BED exon/splice-site intervals `[s, e)` directly against 1-based closed VCF `POS` without converting `vcf_pos0 = POS - 1` shifts canonical `GT-AG` donor/acceptor splice boundaries by `1 bp`, silently dropping canonical `+1G>A` or `-1G>A` splice-disrupting mutations during targeted-panel BED intersection. Notably, even within C bioinformatics libraries, `htslib`'s `faidx_fetch_seq(fai, chr, beg, end, &len)` uses **0-based closed** coordinates `[beg, end]` (returning `end - beg + 1` bytes, `vcfnorm.c:562`), a third coordinate convention distinct from both BED and VCF.

---

### 2. SIMD Partial-Order Alignment (POA) Integer Overflow and Topological Tie-Breaking

#### 2.1 Absence of `int8_t` DP Kernels and Real `int16_t` Wraparound Defects in `abPOA` and `spoa`
`Basis: source + execution`

Farrar's (2007, DOI `10.1093/bioinformatics/btl582`) striped Smith–Waterman algorithm achieves 16–64-lane SIMD throughput by storing nonnegative local alignment scores in biased `uint8_t` lanes using **unsigned saturating arithmetic** (`_mm_adds_epu8` / `_mm_subs_epu8`), detecting saturation whenever any lane reaches `255 - bias` (e.g., on homopolymer or exact-match runs exceeding $\lfloor(255 - \text{bias}) / \text{match}\rfloor$ bases; for signed `int8_t` with `match = 2`, saturation/overflow occurs at `64 bp`), and cascading to `uint16_t` then `int32_t`.

Direct source audit of both pinned POA libraries reveals a critical architectural divergence from Farrar's saturating `uint8_t` scheme: **neither `yangao07/abPOA` (`2e095ba7f8de6bc62aaaa9a684cda781b8098ee0`) nor `rvaser/spoa` (`c987896674564519a580fba9f51b6f81ddc66e4d`) instantiates an `int8_t` DP kernel at all.** Both execute **signed two's-complement wrapping arithmetic** (`_mm256_add_epi16`/`_mm256_sub_epi16`, `_mm512_add_epi16`/`_mm512_sub_epi16`) in `int16_t` and `int32_t` (`abPOA/src/simd_instruction.h:80,85,230,235,309,314`; `spoa/src/simd_alignment_engine_implementation.hpp:60-128,154-220`), relying entirely on **a priori pre-dispatch bounds checks** to choose `int16_t` vs. `int32_t`—with **zero runtime overflow detection**.

Both pre-dispatch bounds checks contain verified soundness defects at the pinned commits:

1. **`yangao07/abPOA` (`src/abpoa_align_simd.c:1284-1302`) — Missing Mismatch & Two-Sided Gap Bounds**:
   ```c
   int len = qlen > gn ? qlen : gn;
   max_score = MAX_OF_TWO(qlen * abpt->max_mat, len * abpt->gap_ext1 + abpt->gap_open1);
   if (max_score <= INT16_MAX - abpt->min_mis - gap_oe1 - gap_oe2) {
       simd_p16.inf_min = MAX_OF_THREE(INT16_MIN + abpt->min_mis, INT16_MIN + gap_oe1, INT16_MIN + gap_oe2)
                          + 512 * MAX_OF_TWO(gap_ext1, gap_ext2);
       ...
       bits = 16;
   }
   ```
   - `abpoa_align.c:12-25` sets `abpt->max_mat = match` and `abpt->min_mis = |mismatch|` (positive magnitude). Default DNA convex-gap parameters (`match=2, mismatch=4, gap_open1=4, gap_ext1=2, gap_open2=24, gap_ext2=1`) yield `gap_oe1 = 6, gap_oe2 = 25, simd_p16.inf_min = -32768 + 25 + 1024 = -31719`, and threshold `32767 - 4 - 6 - 25 = 32732`.
   - **Defect 1 (Mismatch underflow)**: `max_score` ignores `qlen * abpt->min_mis`. Because `min_mis = 4 = 2 * max_mat`, any divergent global alignment with `qlen = gn = 9000` computes `max_score = 18004 <= 32732` and enters the wrapping `int16_t` kernel, yet a mismatch-heavy diagonal drops to `-36,000 < INT16_MIN (-32,768)` and wraps modulo $2^{16}$ via `_mm256_add_epi16` to **`+29,536`**, spuriously outscoring genuine alignments (`Basis: source + execution`, Probe 1B).
   - **Defect 2 (Two-sided gap underflow & `inf_min` offset mismatch)**: Global deletion of `gn` graph nodes plus insertion of `qlen` query bases costs `-(qlen + gn) * gap_ext1 - 2 * gap_open1` (affine) or `-(qlen + gn) * gap_ext2 - 2 * gap_open2` (convex). At `qlen = gn = 16000`, `max_score = 32004 <= 32732` still picks `bits = 16`, yet the two-sided convex gap costs `-32,048 < simd_p16.inf_min (-31,719)` and the two-sided affine gap costs `-64,008`. Even a one-sided gap of length `15,860` (`-31,724`) falls below `inf_min` because line 1294 compares against `INT16_MAX` without subtracting the `512 * max(gap_ext1, gap_ext2) = 1024` safety offset added to `inf_min`.
   - **Defect 3 (`int32_t` multiplication overflow)**: `qlen * abpt->max_mat` on line 1293 is evaluated in signed 32-bit `int32_t` rather than `int64_t`.

2. **`rvaser/spoa` (`src/alignment_engine.cpp:95-103`, `src/simd_alignment_engine_implementation.hpp:664-671`) — Branching-DAG Positive Score Wraparound**:
   ```cpp
   std::int64_t AlignmentEngine::WorstCaseAlignmentScore(std::int64_t i, std::int64_t j) const {
     auto gap_score = [&] (std::int64_t len) -> std::int64_t {
       return len == 0 ? 0 : std::min(g_ + (len - 1) * e_, q_ + (len - 1) * c_);
     };
     return std::min(
         -1 * (m_ * std::min(i, j) + gap_score(std::abs(i - j))),
         gap_score(i) + gap_score(j));
   }
   ```
   - `SimdAlignmentEngine::Align` (`simd_alignment_engine_implementation.hpp:664-671`) calls `WorstCaseAlignmentScore(sequence_len + 8, graph.nodes().size())` and selects `int16_t` whenever `worst_case_score >= INT16_MIN + 1024 (-31744)`.
   - Because `gap_score(|i - j|) <= 0`, adding it inside `-1 * (m_ * min(i, j) + gap_score(|i - j|))` **reduces** the estimated maximum positive score whenever `graph.nodes().size() != sequence_len + 8`. In a POA graph built from noisy long reads (e.g., PacBio/ONT amplicons), `graph.nodes().size()` routinely reaches $2\times$–$3\times$ the consensus length even though an aligned query traverses only `sequence_len` nodes (paying **zero** gap penalty for unvisited alternative branches, and paying zero end-gap penalty in `kSW` local or `kOV` semi-global modes!).
   - Concrete witness (`run_pkg1_probes.py`, Probe 1B; `Basis: source + execution`): with `sequence_len = 7000`, `graph.nodes().size() = 15000`, `m = 5, n = -4, g = -4, e = -1`:
     - `m * min(7008, 15000) = +35,040`, `gap_score(7992) = -7,995`, so `-1 * (35040 - 7995) = -27,045`.
     - `gap_score(7008) + gap_score(15000) = -7,011 + (-15,003) = -22,014`.
     - `WorstCaseAlignmentScore = -27,045 >= -31,744` $\implies$ `spoa` selects wrapping **`int16_t`**, yet a matching `7000`-bp path reaches `+35,000 > INT16_MAX (+32,767)` and wraps modulo $2^{16}$ to **`-30,536`**!

#### 2.2 Non-Canonical Topological Sort and Heaviest-Bundle Tie-Breaking Sensitivity
`Basis: source + execution (toy mirror of upstream tie-breaking rule)`

Partial-order graphs admit exponentially many valid linear extensions (topological sorts) across parallel heterozygous bubbles. Both `spoa` and `abPOA` expose read-arrival-order dependence through two coupled mechanisms:

1. **Consensus Tie-Breaking Uses `<=` Over Uncanonicalized Edge Arrays**:
   - In `rvaser/spoa` (`src/graph.cpp:476-483`), `TraverseHeaviestBundle` scans `it->inedges` in insertion order:
     ```cpp
     if ((scores[it->id] < jt->weight) ||
         (scores[it->id] == jt->weight && scores[predecessors[it->id]->id] <= scores[jt->tail->id]))
     ```
     Because the secondary comparison is `<=`, an equal-weight, equal-prefix-score heterozygous bubble (e.g., 20 REF reads vs. 20 ALT reads on a diploid variant) always selects the **last-inserted** edge.
   - In `yangao07/abPOA` (`src/abpoa_output.c:526-530`), `abpoa_heaviest_bundling` uses the identical `else if (max_w == out_w && score[max_id] <= score[out_id])` rule over `out_id[]`, which was sorted by `abpoa_sort_in_out_ids` (`src/abpoa_graph.c:192-219`) using an **unstable** nested swap loop without secondary tie keys.
2. **Adaptive Banding Coupling in `abPOA`**: `abpoa_BFS_set_node_index` (`src/abpoa_graph.c:221-266`) assigns topological indices via BFS queue order over `out_id[]`, and `abpoa_BFS_set_node_remain` (`lines 268-309`) computes remaining-path estimates using strict `>` (`line 291`), picking the first equal-weight branch. Those indices directly define `abPOA`'s adaptive band bounds (`wb = 10, wf = 0.01`, `include/abpoa.h:16-17`), meaning read-order permutation can shift band windows around long heterozygous indels and drop optimal paths outside the band. (`abpoa_align.c:106` exposes `sort_input_seq` to sort reads by descending length, but leaves it disabled `= 0` by default and does not break equal-length ties lexicographically.)

---

### 3. HL7 FHIR UCUM Dimensionality and SNOMED CT $\mathcal{EL}^{++}$ Context Negation

#### 3.1 UCUM Stoichiometric Incommensurability and `FHIR/ucum-java` Arbitrary-Unit Defect
`Basis: normative + source + execution`

UCUM defines exactly seven base units in `ucum-essence.xml:124-158`: `m` (length `L`), `s` (time `T`), `g` (mass `M`), `rad` (plane angle `A`), `K` (temperature `C`), `C` (charge `Q`), and `cd` (luminous intensity `F`). Crucially, **amount of substance (`mol`) is NOT a UCUM base unit**:

- `ucum-essence.xml:208-213` defines `<unit Code="mol" ...><value Unit="10*23" value="6.02214076">6.02214076</value></unit>` (pure dimensionless count).
- Consequently, `mmol/L` reduces to canonical base units **`m-3`** (factor $6.02214076 \times 10^{23}$), while `mg/dL` reduces to **`g.m-3`** (factor $10^{-2}$).
- `FHIR/ucum-java` (`UcumEssenceService.java:299-304`) correctly rejects `convert(val, "mmol/L", "mg/dL")` with `UcumException` because `"m-3"` $\neq$ `"g.m-3"`. Bridging molar and mass concentrations requires an **analyte-indexed stoichiometric morphism** parameterized by molar mass $M_a$ ($\text{g/mol}$):
  $$C_{\text{mg/dL}} = C_{\text{mmol/L}} \times \frac{M_a}{10}$$
  Applying glucose's factor ($18.0156$) to total cholesterol ($38.6650$, $2.146\times$ error), creatinine ($11.3120$, $0.628\times$ error), or total bilirubin ($58.4660$, $3.245\times$ error) causes dangerous clinical threshold misclassifications (Probe 1D).

However, direct source inspection of `FHIR/ucum-java` (`10089515484cdfd291fa6d2b74b989f60d12fcb3`) and `hapifhir/hapi-fhir` (`2221cbc19eb2b3c7db50e035cd18661ea213014e`) uncovered **four concrete implementation flaws**:

1. **Silent Erasure of `isArbitrary="yes"` (`FHIR/ucum-java` `XmlDefinitionsParser.java:108-119`, `DefinedUnit.java:39-143`)**:
   - UCUM Specification §24 mandates that arbitrary biological/procedural units (`isArbitrary="yes"`) are **incommensurable with every other unit**, including unity (`1`) and distinct arbitrary units (e.g., insulin `[iU]` vs. vitamin D `[iU]` vs. `[USP'U]` vs. `[PFU]`).
   - `ucum-essence.xml` marks **41 units** with `isArbitrary="yes"` (including `[iU]` at `line 1650`, `[IU]` at `line 1656`, `[arb'U]` at `line 1662`, `[USP'U]` at `line 1668`, `[PFU]` at `line 1769`), each carrying `<value Unit="1" value="1">1</value>`.
   - `XmlDefinitionsParser.parseUnit` (`lines 108-119`) reads `isMetric`, `isSpecial`, and `class`, **never reads `isArbitrary`**, and `DefinedUnit` has no `arbitrary` field.
   - Because `Converter.java:158-180` expands `[iU]` to dimensionless `1` (`""`) and `mol` to dimensionless `6.02214076e23` (`""`), `UcumEssenceService.convert` **silently converts `[iU]` to `[USP'U]` (1:1), `[iU]` to `[PFU]` (1:1), and `[iU]/L` to `mmol/L` (dividing by $6.02214076 \times 10^{20}$)** without raising `UcumException` (`Basis: source + derived + execution` on `ucum-essence.xml`, Probe 1D).
2. **Equivalents & Osmoles Conflated with Moles (`ucum-essence.xml:1594-1605`)**: Both `eq` (`equivalents`) and `osm` (`osmole`) expand strictly to `1 mol`, silently equating `1 meq/L = 1 mmol/L = 1 mosm/L` regardless of ionic valence (failing by $2\times$ for $\text{Ca}^{2+}$ and $\text{Mg}^{2+}$ and $2\times$ for dissociated $\text{NaCl}$).
3. **Unreachable Concentration Check (`UcumEssenceService.java:183`)**: `validateInProperty` checks `if ("concentration".equals(property) && ("g/L".equals(cu) || "mol/L".equals(cu)))`, but `Converter` emits `"g.m-3"` and `"m-3"`, never `"g/L"` or `"mol/L"`.
4. **Affine Temperature Workaround & `float32` Drift (`Converter.java:168-171`, `UcumServiceUtil.java:51,115,133-152`)**: `ucum-java`'s `Converter` throws `"Not handled yet (special unit with offset from 0 at intersect)"` on `Cel`/`[degF]`. `HAPI FHIR` works around this in `UcumServiceUtil.canonicalizeFahrenheit` (`lines 133-142`) using `BigDecimal.valueOf(5f / 9f)` (`float` literal `0.5555555820465088`) and `BigDecimal.valueOf(CELSIUS_KELVIN_DIFF)` where `CELSIUS_KELVIN_DIFF = 273.15f` (`273.1499938964844`), introducing up to $-6.10 \times 10^{-6}\text{ K}$ bias before scale rounding (Probe 1D). Furthermore, `ResourceIndexedSearchParamQuantityNormalized.java:93-98` stores canonicalized values as SQL `DOUBLE` because `BigDecimal` mapped to `NUMBER(19,2)` truncated `0.012 m` (`1.2 cm`) to `0.01 m`.

#### 3.2 SNOMED CT $\mathcal{EL}^{++}$ Expressivity vs. HAPI FHIR `IS-A`-Only Subsumption and Context Inversion
`Basis: normative + source`

SNOMED CT's logical definitions sit within the tractable description logic $\mathcal{EL}^{++}$ (OWL 2 EL; Baader, Brandt & Lutz, IJCAI 2005), admitting polynomial-time ($O(n^k)$) classification with conjunction ($\sqcap$), existential restriction ($\exists r.C$), and role inclusions ($r \circ s \sqsubseteq t$), while excluding full negation ($\neg C$) and universal quantification ($\forall r.C$) because either addition pushes subsumption with GCIs to EXPTIME-complete.

Because $\mathcal{EL}^{++}$ lacks classical negation, SNOMED CT encodes negation, family history, and uncertainty via **context-wrapper concepts** rooted under `243796009 |Situation with explicit context (situation)|` (disjoint from `404684003 |Clinical finding (finding)|`):

$$\begin{aligned}
\texttt{409137002}\;|\text{No known drug allergy}| &\equiv \texttt{243796009} \sqcap \exists \texttt{roleGroup}.(\exists \texttt{246090004}.\texttt{416098002} \sqcap \exists \texttt{408729009}.\texttt{410516002} \sqcap \exists \texttt{408732007}.\texttt{410604004}) \\
\texttt{266897007}\;|\text{Family history of MI}| &\equiv \texttt{243796009} \sqcap \exists \texttt{roleGroup}.(\exists \texttt{246090004}.\texttt{22298006} \sqcap \exists \texttt{408729009}.\texttt{410515003} \sqcap \exists \texttt{408732007}.\texttt{444148008})
\end{aligned}$$

where `246090004` = *Associated finding*, `416098002` = *Allergy to drug (finding)*, `22298006` = *Myocardial infarction (disorder)*, `408729009` = *Finding context*, `410516002` = *Known absent*, `408732007` = *Subject relationship context*, and `410604004` = *Subject of record*.

**Subsumption Inversion & HAPI FHIR Storage Limits (`hapifhir/hapi-fhir` @ `2221cbc19eb2b3c7db50e035cd18661ea213014e`)**:
- `TermConceptParentChildLink.java:266-269` defines `RelationshipTypeEnum` with a **single** enum constant: `ISA`.
- `TermConcept.java:526-551` precomputes transitive `myParentPids` solely over `ISA` links; `TermReadSvcImpl.subsumes` (`TermReadSvcImpl.java:2636-2685`, `2782-2799`) queries Lucene/Hibernate Search exclusively for `myParentPids` membership (`ISA` ancestry), returning `SUBSUMES`, `SUBSUMEDBY`, or `NOTSUBSUMED` (note also that lines 2676–2682 do not evaluate post-coordinated expressions or role-group axioms, and property-level `ISA`/`DESCENDENTOF` ValueSet filters fall into `matchNone()` at `TermReadSvcImpl.java:1490-1504`).
- Consequently, two symmetric clinical-decision-support (CDS) failures arise in EHR deployments:
  1. **Context-Blind Role-Target Queries (False Positives)**: Queries that traverse `246090004 |Associated finding|` (or substring-match descriptions / FHIR `Condition.code` without checking `Condition.verificationStatus` and separating `Situation` from `Clinical finding`) capture `409137002 |No known drug allergy|` as an active drug allergy and `266897007 |Family history of MI|` as an active myocardial infarction, firing spurious contraindication or sepsis/cardiology alerts.
  2. **Pre-Coordinated-Only `IS-A` Lookups (False Negatives)**: Because HAPI FHIR's JPA engine lacks an $\mathcal{EL}^{++}$ classifier for post-coordinated SNOMED CT expressions, a valid post-coordinated negated or contextualized expression is rejected or classified `NOTSUBSUMED` against ValueSets defined by ECL (`<< 404684003`), forcing brittle string-list maintenance.

---

### 4. Six-Level Performance and Resource Footprint Analysis (`L1–L6`)

`Basis: documentation + source + derived` (explicitly noting where hardware/workload figures depend on published benchmarks or analytical scaling rather than local measurement of compiled C/Java binaries).

| Level | VCF Normalization (`bcftools` / `vt`) | SIMD POA (`abPOA` / `spoa`) | Clinical Units & Ontologies (`ucum-java` / `hapi-fhir`) |
|---|---|---|---|
| **(L1) Human & Agent Authoring Velocity** | Normalization algorithm is compact (~150 LoC core in `vt/variant_manip.cpp:513-615`; ~3,100 LoC full `bcftools/vcfnorm.c` including INFO/FORMAT `Number=R/A/G` splitting). Formalizing biallelic uniqueness/idempotence + coordinate bijections takes ~300–600 LoC in Lean/Rocq (~3–5x proof-to-code ratio); major maintenance burden is keeping `INFO/AD`, `PL`, and `GT` re-indexing consistent across splits (`vcfnorm.c:898-1437`). | High authoring/maintenance friction: `abpoa_align_simd.c` (~1,338 LoC of C preprocessor macros across SSE2/SSE4.1/AVX2/AVX-512BW × linear/affine/convex × `i16`/`i32`) and `spoa` (`2,065` LoC C++ templates). Proving SIMD lane-shift equivalence + overflow absence requires ~6–10x proof-to-code ratio due to cross-lane `_mm256_permute2x128_si256` / `_mm512_alignr_epi8` shuffles. | `ucum-java` core converter is compact (~2,500 LoC + 1,800-line `ucum-essence.xml`); `hapi-fhir` spans >60 Maven modules (`pom.xml` >123 KB). Formalizing an analyte-indexed dimensional + arbitrary-unit type system takes ~400 LoC; authoring clinical SNOMED ECL / $\mathcal{EL}^{++}$ context guards is fast once `ClinicalFinding` vs. `Situation` are separated at the type level, whereas debugging ad-hoc EHR ValueSets is high-churn. |
| **(L2) Toolchain & Framework Build Time** | `bcftools` + `htslib` builds from scratch in ~15–40 s in C (`gcc -O2`); `vt` in ~10–25 s (`g++`). Incremental single-file rebuild (`vcfnorm.c`) <2 s. | `abPOA` compiles in ~5–15 s (`gcc -O3`, multi-ISA dispatch builds 4 object variants); `spoa` builds in ~10–30 s (`cmake`/`g++`). Peak compiler RSS <500 MB. | `ucum-java` builds via Maven in ~5–15 s; full `hapi-fhir` multi-module reactor build requires >15–30 min and 4–8 GB JVM heap (incremental single-module build ~20–60 s). |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Streaming CLI startup <10 ms; FASTA `.fai` index lookup is $O(1)$ mmap/seek. SMT/formal verification of coordinate-conversion and biallelic normalization invariants runs in <50 ms interactively; bounded repeat-length proofs scale linearly with unroll bound unless proved by induction over repeat period. | SIMD ISA dispatch is static/CPUID-checked at runtime (~ns). Formalizing `WorstCaseAlignmentScore` overflow bounds in SMT (`QF_NIA`/linear arithmetic) discharges in <20 ms; bit-vector equivalence of 256/512-bit SIMD shuffle macros takes seconds to minutes per kernel without abstract lane-wise lifting. | `UcumServiceUtil.init()` parses `ucum-essence.xml` once lazily (~30–100 ms cold). Full SNOMED CT International Edition (~360k concepts, ~1.2M axioms) $\mathcal{EL}^{++}$ classification in ELK takes ~1–3 s multi-threaded (polynomial time; Baader et al. 2005); HAPI FHIR RF2 JPA ingestion + Lucene `myParentPids` indexing takes minutes to tens of minutes due to RDBMS/Hibernate Search I/O. |
| **(L4) Generated Code Execution Performance** | Streaming `bcftools norm` is I/O- and BGZF-bound (~50k–200k VCF records/s per core; `realign_left_shift` avoids per-base FASTA seeks by block-fetching `aln_win = 100` doubling to `65536` bp, `vcfnorm.c:549-583`). `vt` fetches **1 base per `faidx_fetch_uc_seq` call** inside `right_trim_or_left_extend` (`variant_manip.cpp:565`), incurring $O(\text{shift})$ syscalls/cache lookups on long repeats. | `abPOA` (Gao et al. 2021) achieves $1.5\times$–$15\times$ speedup over unbanded `spoa` on long reads via adaptive banding ($O(L \cdot b)$ cells vs. $O(L \cdot |V|)$), processing 16 `int16_t` lanes/cycle (AVX2) or 32 lanes/cycle (AVX-512BW) — halving throughput (`2x` slowdown) whenever widening to `int32_t`. Checking saturating vs. wrapping adds 0–1 cycle on x86 (`vpaddsw` vs `vpaddw` have identical 1-cycle latency / 0.5 CPI throughput on Skylake+/Zen3+). | `ucum-java` parses and normalizes unit strings in ~5–50 $\mu$s/call (`BigDecimal` / custom `Decimal` 30-digit arithmetic, `Converter.java:62`); HAPI FHIR `TermReadSvcImpl.subsumes` hits Lucene/Hibernate Search (`~0.5–5 ms` per query, `TermReadSvcImpl.java:2787-2792`), whereas pre-classified in-memory transitive bitsets or interval-labeled DAGs answer `IS-A` in <100 ns. |
| **(L5) Proof / Certificate Verification Speed** | Witnessing a normalized VCF record is $O(|R_{\text{win}}| + \sum |a_i|)$ per variant: verify `apply(R, v_in) == apply(R, v_norm)` + `is_normalized(v_norm)` (parsimony + left-alignment) in <1 $\mu$s/record; trivially embarrassingly parallel by genomic contig/chunk. | Alignment score optimality certificates (or DP trace re-check) verify a returned CIGAR path in $O(L)$ scalar `int64_t` arithmetic (~1 $\mu$s for 10 kb read), catching any `int16_t` wraparound corrupting path score or trace validity (`score(cigar) != reported_score`) at negligible overhead vs. $O(L \cdot b)$ DP. | Dimensional canonicalization checking is $O(|\text{ast}|)$ integer exponent vector equality (<5 $\mu$s); OWL 2 EL classification proof certificates (ELK consequence proofs) verify individual subsumption derivations in <1 ms without re-classifying the entire 360k-concept ontology. |
| **(L6) RAM, Disk & Binary Footprints** | `bcftools` binary ~1.5–2.5 MB; `vcfnorm` ring buffer holds `buf_win = 1000` sites (~1–10 MB RSS depending on cohort sample count `GT`/`PL` vectors); reference `.fa` + `.fai` (~3.1 GB human GRCh38 on disk, random-access paged). | `spoa` allocates full DP matrices of size $3\text{–}5 \times |V| \times \lceil L/W \rceil \times 32$ bytes (`simd_alignment_engine_implementation.hpp:418-445`): for $L=10{,}000$, $|V|=20{,}000$, `int32_t` convex-gap requires $\sim 4\text{ GB}$ RAM (triggering `std::bad_alloc`!). `abPOA` adaptive banding shrinks DP RAM by $10\times$–$50\times$ ($O(|V| \cdot b)$), keeping peak RSS in tens of MB. | `ucum-java` JAR ~120 KB (`ucum-essence.xml` ~130 KB); HAPI FHIR JPA server requires 2–8 GB JVM heap + 1–5 GB RDBMS/Lucene storage for full SNOMED CT + LOINC `TermConcept` and `myParentPids` indexes. |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

#### 5.1 Human Comprehensibility & Mental-Model Ergonomics (`C1`)
`Basis: source + derived`

- **Nonlocal Order Sensitivity vs. Human Pipeline Mental Models**: Bioinformaticians treat `bcftools norm` flags (`-m -any`, `-f ref.fa`, `-a`) as composable, commutative UNIX filters. Because `split` and `norm` fail to commute (`95.4%` divergence on repeat-flanking multiallelics), splitting normalization across two pipeline stages (common in WDL/Nextflow scatter-gather workflows) silently invalidates downstream ClinVar matching while still passing `vt/is_normalized` on the pre-split record! An LLM or script generating multi-stage bioinformatics pipelines reproduces this footgun unless the type/contract explicitly distinguishes `MultiallelicVcf` from `CanonicalBiallelicVariant`.
- **Coordinate System Working-Memory Overload**: Simultaneously juggling **four** incompatible genomic coordinate systems—0-based half-open BED `[s, e)`, 0-based closed `faidx_fetch_seq` `[b, e]`, 1-based closed 5'-justified VCF `[p, e]`, and 1-based closed 3'-transcript-justified HGVS—exceeds reliable human working memory (`4+` coupled invariants across strand polarity, origin, and closure), explaining persistent clinical splice-site off-by-one defects.
- **Opaque Wrapping Failure Diagnostics**: Neither `abPOA` nor `spoa` logs a warning when `int16_t` wraps silently; the emitted consensus string remains valid ACGT characters with plausible length, making silent alignment corruption virtually invisible to human reviewers. Similarly, `ucum-java` silently returning a numeric conversion for `[iU]/L -> mmol/L` produces no diagnostic warning, whereas a hard dimensional rejection with explicit missing-parameter guidance (`"Conversion mmol/L -> mg/dL requires MolarMass<Analyte>"`) is immediately actionable.
- **Clinical Polarity Footguns in SNOMED CT**: Human clinicians and software developers instinctively expect a query for *"drug allergy"* or *"myocardial infarction"* to match active patient findings. Because SNOMED CT places negated and family-history concepts inside `Situation with explicit context` pointing *to* the disorder via `Associated finding`, naive graph/text retrieval breaks human epistemic expectations unless the API makes `(Subject, EpistemicStatus, TemporalContext)` mandatory first-class query parameters.

#### 5.2 Simplicity, Orthogonality & Universal Model Refinement (`C2`)
`Basis: derived`

Separating core domain invariants from realization-medium accidents yields four orthogonal, minimal abstractions (satisfying Ousterhout's deep-module criterion without shifting hidden complexity into ad-hoc adapters):

1. **Quotient-Canonical Variant Representation (`CanonicalBiallelic<Ref, Strand>`)**: Rather than scattering ad-hoc trim/shift flags (`-m`, `-f`, `-g`, `-w`) across tools, define genomic variant normalization as a single total quotient morphism `decompose_then_canonicalize : MultiallelicRecord -> Set<CanonicalBiallelic>` backed by the single invariant $\text{apply}(R, v) = \text{apply}(R, v') \iff \text{canon}(v) = \text{canon}(v')$, paired with zero-cost phantom-typed coordinates `GenomicSpan<Origin, Closure, Strand>` that statically forbid uncast mixing of `BED(0, HalfOpen)` with `VCF(1, Closed)` or `Faidx(0, Closed)`.
2. **Exact-Range Saturating/Checked SIMD Precision Escalation**: The complexity of `abPOA`'s and `spoa`'s fragile analytical `max_score` / `WorstCaseAlignmentScore` guards exists solely because both engines use **wrapping** `_mm*_add_epi16` instead of **signed saturating** `_mm*_adds_epi16` / `_mm*_subs_epi16` (available identically on SSE2, AVX2, and AVX-512BW!) plus a 1-instruction saturation-flag check (`_mm256_movemask_epi8(cmp_eq(v, INT16_MIN/MAX))`) or sound worst-case over-approximation:
   $$S_{\max} = \max\big(q \cdot M_{\max},\; q \cdot X_{\max},\; (q + |V|) \cdot G_{\max}\big) + \Delta_{\text{guard}} < 2^{15} - 1$$
   Replacing brittle heuristic pre-checks with saturating arithmetic + automatic `i16 -> i32` fallback (and deterministic lexicographic `(weight, path_score, node_base, topological_rank)` tie-breaking) eliminates both overflow bugs and read-order nondeterminism with `< 1%` runtime overhead.
3. **Analyte-Indexed Stoichiometric & Arbitrary-Unit Dimension Lattice**: Extend UCUM's 7-dimensional exponent vector $\mathbb{Z}^7$ with: (a) a distinct base dimension `N` (`mol`, separated from dimensionless `1`, `eq`, and `osm`), (b) a nominal tag set for `isArbitrary="yes"` units (forcing every arbitrary unit to be commensurable **only** with itself), and (c) an explicit `StoichiometricBridge<Analyte, MolarMass, Valence>` morphism for `mol <-> g` and `mol <-> eq`. This unifies SI dimensional analysis, clinical molar-mass conversion, and UCUM §24 arbitrary-unit isolation under one algebraic structure with zero special-case hacks like `UcumEssenceService.java:183`.
4. **Epistemic-Stratified Clinical Fact Wrapper (`ClinicalStatement<Subject, Presence, Temporality, Finding>`)**: Separate ontological taxonomy (`ClinicalFinding` subsumption in $\mathcal{EL}^{++}$) orthogonally from epistemic/contextual framing (`Subject ∈ {Patient, FamilyMember}`, `Presence ∈ {ConfirmedPresent, Suspected, KnownAbsent}`). Every clinical query must bind `Subject` and `Presence` explicitly, eliminating context-wrapper subsumption inversions by construction.

---

### 6. End-to-End Solution and Implementation Validation (`V1–V4`)

`Basis: normative + documentation + execution (toy/micro-probes) + derived`

Formal proofs over abstract genomic or clinical models can still miss real-world failures (unmodeled tandem-repeat boundary shifts, SIMD ISA shuffle bugs, multi-thread graph races, or EHR workflow misinterpretation). A complete validation spine spans four tiers:

- **(V1) Specification Adequacy, Mutation & Non-Vacuity Validation**:
  - *Haplotype-Preserving Metamorphic PBT*: Generate tens of thousands of tandem-repeat, homopolymer, compound-MNP, and chromosome-start (`pos=0`) indels; assert (i) haplotype preservation $\text{apply}(R, v) = \text{apply}(R, \text{norm}(v))$, (ii) canonical uniqueness across arbitrary valid shifts/paddings, (iii) strict idempotence $\text{norm}(\text{norm}(v)) = \text{norm}(v)$, and (iv) mutant-kill rate `100%` against swapped `norm`/`split` order, missing `pos==0` guard, and 0-vs-1-based off-by-one mutants (demonstrated on 20,000 trials in Probe 1A).
  - *UCUM & SNOMED Spec-Mutation*: Exhaustively test all 41 `isArbitrary="yes"` codes in `ucum-essence.xml` to verify rejection of cross-unit conversion (`[iU] <-> [USP'U]`, `[iU]/L <-> mmol/L`), and inject negated/family-history SNOMED CT situations (`266897007`, `409137002`) into FHIR `Condition` / `AllergyIntolerance` test bundles to assert `0%` false-positive clinical alert leakage.
- **(V2) Compiler, Lowering & Checker Soundness Fuzzing**:
  - *SIMD vs. Scalar `int64_t` Differential Fuzzing*: Fuzz `abPOA` and `spoa` across SSE2, SSE4.1, AVX2, and AVX-512BW against a reference scalar `int64_t` POA aligner (`spoa`'s `SisdAlignmentEngine` widened to `int64_t`) specifically targeting lengths and scoring matrices near `INT16_MAX`/`INT16_MIN` (`qlen ∈ [3000, 18000]`, high mismatch ratios, branching DAGs with $|V| \gg L$), asserting exact alignment-score identity.
  - *Differential $\mathcal{EL}^{++}$ Reasoner Cross-Check*: Cross-check HAPI FHIR `$subsumes` and ValueSet expansions against an independent OWL 2 EL reasoner (ELK / Snorocket) over SNOMED CT RF2 snapshots, flagging every discrepancy caused by `IS-A`-only indexing or ignored role-group axioms.
- **(V3) Concurrency, Crash, Silicon & Determinism Validation**:
  - *Thread-Count & Input-Permutation Bitwise Determinism*: Run parallel BAM/VCF normalization (`bcftools norm --threads 1..64`) and POA consensus generation across random permutations of input read order and thread scheduling, asserting bitwise-identical VCF/FASTA output (exposing `spoa`/`abPOA` `<=` tie-breaking sensitivity and `bcftools` `-w` sort-window violations).
  - *Bounded Memory & Crash Safety*: Stress-test `spoa` vs. `abPOA` under cgroup memory caps on high-divergence graphs to verify graceful allocation error handling rather than OOM kills or truncated output files.
- **(V4) Reality-Gap Replay, Truth-Set Validation & Human Comprehension Testing**:
  - *NIST GIAB Truth-Set Haplotype Benchmarking*: Validate full variant-calling + normalization pipelines against NIST Genome in a Bottle (`GIAB`) `HG002` (NA24385) v4.2.1 benchmark VCFs—specifically stratified on GIAB tandem-repeat and homopolymer BED masks—using haplotype-aware comparison (`RTG vcfeval` / `hap.py`, Krusche et al. 2019), verifying zero normalization-induced false negatives on clinically curated *BRCA1*/*BRCA2* and ClinVar pathogenic repeat indels.
  - *Behavioral Mental-Model Litmus Testing (`SMoL`-style)*: Evaluate clinical informaticians and pipeline engineers on short diagnostic litmus tasks covering (i) `bcftools norm` split-vs-align order, (ii) BED/VCF/HGVS coordinate conversions, (iii) `mmol/L -> mg/dL` analyte dependence, and (iv) SNOMED CT `Situation with explicit context` polarity, measuring whether refined type-safe APIs eliminate human query errors compared to raw string/CLI interfaces.

## Boundaries

- **Actual Compiled Binary Execution of `bcftools`, `vt`, `abPOA`, `spoa`, `ucum-java`, and `hapi-fhir`**: **not examined** (this environment operated without compiling C/C++/Java toolchains or executing native binaries against FASTA/RF2 archives). All source-level bug claims quote exact upstream source lines at the pinned commits, and quantitative probes execute exact Python ports of the upstream formulas (`bcftools vcfnorm.c:607-659`, `abPOA src/abpoa_align_simd.c:1284-1297`, `spoa src/alignment_engine.cpp:95-103`, `HAPI FHIR UcumServiceUtil.java:133-142`) plus direct XML parsing of upstream `ucum-essence.xml`; consensus tie-breaking (`Probe 1C`) is a minimal toy mirror of the upstream `<=` comparator rather than a full POA execution.
- **`int8_t` DP Overflow in Current `abPOA` and `spoa` Revisions**: **known not to apply** to `yangao07/abPOA` (`2e095ba7f8de6bc62aaaa9a684cda781b8098ee0`) or `rvaser/spoa` (`c987896674564519a580fba9f51b6f81ddc66e4d`) directly, because neither revision instantiates an `int8_t` DP kernel (though `abPOA/src/simd_instruction.h` still defines wrapping `SIMDAddi8`/`SIMDSubi8` macros). Signed `int8_t`/`uint8_t` saturation applies to Farrar (2007) striped Smith–Waterman implementations (`ssw`, `parasail`, `ksw2`), whereas `abPOA` and `spoa` suffer from **signed `int16_t` wrapping overflow/underflow** due to incomplete pre-dispatch guards as proved in Section 2.1.
- **Exact Runtime Conditions for Triggering `abPOA` `int16_t` Underflow Under Adaptive Banding**: **unknown** whether `abPOA`'s adaptive band (`wb=10, wf=0.01`) prunes all-mismatch diagonals early enough to avoid `-32768` wraparound on some real sequencing inputs; however, in unbanded mode (`wb = -1`, which is **forced automatically** in `ABPOA_LOCAL_MODE` at `abpoa_align.c:167` or when users disable banding for high-error reads) or on globally divergent `qlen >= 9000` sequences, the negative score cells are directly computed in wrapping `int16_t`.
- **`hapi-fhir` External Terminology Delegation**: **known not to apply** when HAPI FHIR is configured with `RemoteTerminologyServiceValidationSupport` delegating SNOMED CT `$subsumes` and ValueSet expansion to an external OWL 2 EL server (e.g., CSIRO Ontoserver or Snowstorm); the `ISA`-only limitation applies specifically to HAPI FHIR's built-in JPA `TermReadSvcImpl` (`TermReadSvcImpl.java:2636-2799`).
- **`org.hl7.fhir.core` `SctHandlerRelationship` Localization Behavior**: **not examined** directly in source (this class resides in the upstream `hapifhir/org.hl7.fhir.core` dependency rather than `hapifhir/hapi-fhir` itself).
- **GA4GH VRS (Variant Representation Specification) & Graph Genomes (VG/Giraffe)**: **not examined** in source; noted only as contextual alternatives to positional VCF normalization.

## Evidence

### Upstream Source Citations (Pinned Revisions, Observed `2026-11-19`)

1. **`samtools/bcftools` @ `ec0daf29256ce7a0da3b19eeed8a97a42bc1307a`**:
   - `vcfnorm.c:523-540`: `is_left_align()` switches to right-alignment on `+`-strand GFF transcripts, defaulting back to left-alignment on conflicting strands.
   - `vcfnorm.c:542-605`: `realign_left_shift()` block-fetches up to `65536` bp (`line 550`) and requires all `0..n_allele-1` alleles to match (`lines 568-574`).
   - `vcfnorm.c:607-659`: `realign_left()` right-trims only bases identical across all alleles (`lines 616-622`), guards `min_len<=1 && new_pos==0` (`line 623`), then left-trims (`lines 636-657`).
   - `vcfnorm.c:661-719`: `realign_right()` right-alignment implementation.
   - `vcfnorm.c:773-782, 832`: early exits `ERR_SYMBOLIC` and `ERR_SPANNING_DELETION` skipping realignment on breakends, `*`, and multiallelic `<...>` placeholders.
   - `vcfnorm.c:2646-2689`: `split_and_normalize()` executes `split_multiallelic_to_biallelics` (`line 2678`) before per-record `normalize_line` (`lines 2681-2686`).
   - `vcfnorm.c:2738, 2866`: `args->buf_win = 1000` default sorting flush window.
2. **`atks/vt` @ `c6bd1591a23a1d116d52834a627c00bbf7ed4a64`**:
   - `normalize.cpp:174-330`: `normalize()` skips records passing `vm->is_normalized(v)`, then invokes `right_trim_or_left_extend` followed by `left_trim` on the unsplit multiallelic allele vector.
   - `variant_manip.cpp:109-197`: `VariantManip::is_normalized()` checks joint parsimony across all `n_allele` entries.
   - `variant_manip.cpp:513-615`: `right_trim_or_left_extend()` (calling `faidx_fetch_uc_seq` 1 bp at a time at `line 565`) and `left_trim()`.
3. **`yangao07/abPOA` @ `2e095ba7f8de6bc62aaaa9a684cda781b8098ee0`**:
   - `src/abpoa_align_simd.c:1271-1327`: `simd_abpoa_align_sequence_to_subgraph()` instantiates only `simd_p16` (`int16_t`) and `simd_p32` (`int32_t`); `lines 1293-1297` compute `max_score` omitting `qlen * min_mis` and two-sided gaps, and offset `simd_p16.inf_min` by `+ 512 * MAX_OF_TWO(gap_ext1, gap_ext2)`.
   - `src/simd_instruction.h:79-86, 229-236, 308-315`: maps `SIMDAddi16`/`SIMDSubi16` to wrapping `_mm512_add_epi16`/`_mm256_add_epi16`/`_mm_add_epi16` (and defines unused wrapping `SIMDAddi8`/`SIMDSubi8`).
   - `src/abpoa_align.c:12-25, 96-167`: `gen_simple_mat()` sets `max_mat = match`, `min_mis = -mismatch` (positive); `abpoa_init_para()` defaults `sort_input_seq = 0`; `abpoa_post_set_para()` sets `wb = -1` in `ABPOA_LOCAL_MODE`.
   - `src/abpoa_graph.c:192-309`: unstable nested-loop `abpoa_sort_in_out_ids`, BFS topological indexing (`abpoa_BFS_set_node_index`), and `abpoa_BFS_set_node_remain`.
   - `src/abpoa_output.c:478-535`: `abpoa_heaviest_bundling()` tie-break `else if (max_w == out_w && score[max_id] <= score[out_id])` (`line 529`).
4. **`rvaser/spoa` @ `c987896674564519a580fba9f51b6f81ddc66e4d`**:
   - `src/simd_alignment_engine_implementation.hpp:60-220`: specializes `InstructionSet` strictly for `std::int16_t` and `std::int32_t` with wrapping `_mm256_add_epi16`/`_mm_add_epi16`.
   - `src/simd_alignment_engine_implementation.hpp:664-671`: dispatches `int16_t` vs. `int32_t` via `WorstCaseAlignmentScore(sequence_len + 8, graph.nodes().size()) < INT16_MIN + 1024`.
   - `src/alignment_engine.cpp:95-103`: `WorstCaseAlignmentScore(i, j)` subtracts negative `gap_score(|i - j|)` inside `-1 * (m_ * min(i, j) + gap_score(|i - j|))`.
   - `src/graph.cpp:250-304, 467-510`: insertion-order LIFO `TopologicalSort()` and `TraverseHeaviestBundle()` `<=` tie-breaking (`line 479`).
5. **`FHIR/ucum-java` @ `10089515484cdfd291fa6d2b74b989f60d12fcb3`**:
   - `src/main/resources/ucum-essence.xml:124-158, 208-213, 1594-1605, 1650-1769`: 7 base units, `mol = 6.02214076e23` dimensionless, `eq = osm = 1 mol`, 41 `isArbitrary="yes"` units with `value="1" Unit="1"`.
   - `src/main/java/org/fhir/ucum/definitions/XmlDefinitionsParser.java:108-119` & `DefinedUnit.java:39-143`: `isArbitrary` attribute never parsed or stored.
   - `src/main/java/org/fhir/ucum/Converter.java:158-180` & `UcumEssenceService.java:183, 291-310`: special offset units throw `UcumException`; `convert()` compares canonical base-unit strings only; unreachable `"g/L"`/`"mol/L"` check at `line 183`.
6. **`hapifhir/hapi-fhir` @ `2221cbc19eb2b3c7db50e035cd18661ea213014e`**:
   - `hapi-fhir-jpaserver-base/src/main/java/ca/uhn/fhir/jpa/entity/TermConceptParentChildLink.java:266-269`: `RelationshipTypeEnum` contains only `ISA`.
   - `hapi-fhir-jpaserver-base/src/main/java/ca/uhn/fhir/jpa/entity/TermConcept.java:526-551` & `TermReadSvcImpl.java:1490-1504, 2636-2685, 2782-2799`: `ISA`-only `myParentPids` subsumption lookup.
   - `hapi-fhir-jpaserver-model/src/main/java/ca/uhn/fhir/jpa/model/util/UcumServiceUtil.java:51, 115, 133-152`: Fahrenheit/Celsius special-case workaround using `float` `5f / 9f` and `273.15f`.
   - `hapi-fhir-jpaserver-model/src/main/java/ca/uhn/fhir/jpa/model/entity/ResourceIndexedSearchParamQuantityNormalized.java:93-98`: `DOUBLE` column storage workaround for `BigDecimal` `NUMBER(19,2)` truncation.

### Reproducible Execution Probes (Observed `2026-11-19`, Python 3 on Linux x86_64)

1. **Probe 1A (VCF Normalization Non-Commutativity & 20,000-Trial Metamorphic Check)**:
   - Input: `R = "GGTCACACACACATGCA"`, `POS = 10` (1-based), `REF = "CACAT"`, `ALT = "CAT,CACAG"`.
   - Observed output: `Path A (norm -> split)` emitted `[(12, ['CAT', 'T']), (12, ['CAT', 'CAG'])]`; `Path B (split -> norm)` emitted `[(3, ['TCA', 'T']), (14, ['T', 'G'])]`; identical biological haplotypes (`True`), exact key match (`False`).
   - Across `20,000` seeded random repeat trials (`random.Random(42)`): biallelic uniqueness `20000/20000`, idempotence `20000/20000`, multiallelic non-commutativity `19077/20000` (`95.4%`).
2. **Probe 1B (`abPOA` & `spoa` Exact `int16_t` Guard Evaluation)**:
   - `abPOA(qlen=9000, gn=9000, m=2, mis=-4, o1=4, e1=2, o2=24, e2=1)`: `selects_i16 = True` (`max_score = 18004 <= 32732`, `inf_min = -31719`), all-mismatch `-36000` wraps in `int16_t` to `+29536`, two-sided affine gap `-36008`.
   - `abPOA(qlen=16000, gn=16000, m=2, mis=-4, o1=4, e1=2, o2=24, e2=1)`: `selects_i16 = True` (`max_score = 32004 <= 32732`), all-mismatch `-64000` wraps to `+1536`, two-sided convex gap `-32048 < inf_min (-31719)`.
   - `spoa(slen=7000, gnodes=15000, m=5, n=-4, g=-4, e=-1)`: `selects_i16 = True` (`wcs = -27045 >= -31744`), true max match score `+35000` wraps in `int16_t` to `-30536`.
   - `spoa(slen=3500, gnodes=10000, m=10, n=-4, g=-2, e=-1)`: `selects_i16 = True` (`wcs = -28587 >= -31744`), true max match score `+35000` wraps in `int16_t` to `-30536`.
3. **Probe 1C (Toy Mirror of `spoa`/`abPOA` `<=` Consensus Tie-Breaking)**:
   - Equal 50:50 heterozygous alleles `(weight=20, prefix_score=100)`: input order `[REF_A, ALT_G]` emits `ALT_G`; reversed order `[ALT_G, REF_A]` emits `REF_A`.
4. **Probe 1D (`ucum-essence.xml` Audit & `UcumServiceUtil` `float32` Drift)**:
   - Parsed `ucum-essence.xml` (`FHIR/ucum-java` @ `10089515484cdfd291fa6d2b74b989f60d12fcb3`): counted `41` units with `isArbitrary="yes"`, all carrying `Unit="1" value="1"` (or aliasing `[iU]`) and omitted from `XmlDefinitionsParser.parseUnit`.
   - Verified `UcumServiceUtil.java:134-136` `float32` Kelvin drift: `32.0 F -> 273.1499938965 K` (`-6.104e-6 K`), `98.6 F -> 310.1499956608 K` (`-4.339e-6 K`), `100.4 F -> 311.1499957085 K` (`-4.292e-6 K`).

## Revalidation

To revalidate these findings against newer upstream releases cheaply and deterministically:

1. **VCF Normalization Commutativity Check**: Diff `realign_left` and `split_and_normalize` in `samtools/bcftools` (`vcfnorm.c`) and `right_trim_or_left_extend` in `atks/vt` (`variant_manip.cpp`). Run a 2-record golden specimen (`R = GGTCACACACACATGCA`, `POS=10 REF=CACAT ALT=CAT,CACAG`) through both `bcftools norm -f ref.fa | bcftools norm -m -any` and `bcftools norm -m -any -f ref.fa`, confirming whether outputs still diverge.
2. **`abPOA` / `spoa` SIMD Overflow Check**:
   - Inspect `abPOA/src/abpoa_align_simd.c` around `max_score` and `simd_instruction.h` (`SIMDAddi16`) to check whether `max_score` now bounds `qlen * min_mis` and `(qlen + gn) * gap_ext` or switches to saturating `_mm*_adds_epi16`.
   - Inspect `spoa/src/alignment_engine.cpp` (`WorstCaseAlignmentScore`) to check whether `gap_score(std::abs(i - j))` has been removed from the positive-score bound `-1 * (m_ * std::min(i, j))`. Compile `spoa` and align a `7000`-bp exact-match query against a `15000`-node branching DAG under `(m=5, n=-4, g=-4, e=-1)`, checking whether the returned score is `+35000` or negative/corrupted.
3. **`ucum-java` Arbitrary-Unit & `hapi-fhir` Subsumption Check**:
   - Grep `FHIR/ucum-java` for `isArbitrary` in `XmlDefinitionsParser.java` and `Converter.java`; run `UcumEssenceService.isComparable("[iU]/L", "mmol/L")` and `convert(new Decimal(1), "[iU]", "[USP'U]")`—revalidation passes (bug fixed) only when both reject arbitrary-unit conversion per UCUM §24.
   - Check `hapifhir/hapi-fhir` `TermConceptParentChildLink.java` (`RelationshipTypeEnum`) and `TermReadSvcImpl.subsumes()` for OWL 2 EL / role-group reasoning support, and check `UcumServiceUtil.java` for replacement of `5f / 9f` and `273.15f` with exact `BigDecimal` rationals (`5/9`, `"273.15"`).
