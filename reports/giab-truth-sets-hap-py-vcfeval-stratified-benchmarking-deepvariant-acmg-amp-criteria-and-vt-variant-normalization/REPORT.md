# Germline small-variant benchmarking and classification: GIAB truth sets, GA4GH/hap.py/vcfeval comparison semantics, vt and HGVS normalization, DeepVariant evaluation, and ACMG/AMP combining rules

## Summary

- A germline small-variant precision/recall number is a function of five separable choices: (1) truth-set version and its benchmark ("confident") regions, (2) stratification BEDs, (3) matching stringency (genotype, allele or local match), (4) comparison engine and its preprocessing, and (5) engine resource caps. Changing only (1) from GIAB v3.3.2 to v4.2.1 for HG002 raises GRCh38 autosomal coverage from 85.4% to 92.2% and multiplies the SNVs missed by one standard short-read pipeline 8.5-fold (1,960 → 16,615; Wagner et al. 2022). Numbers obtained against different truth versions are not comparable.
- One haplotype pair has many valid VCF encodings, so comparison must happen at the haplotype level. In an executed probe whose truth and query encode identical haplotypes differently, a toy exact-record matcher scored 2 TP / 9 FP / 7 FN, while RTG Tools vcfeval 3.13 scored 7 baseline TP / 2 FP / 2 FN; the residual errors are exactly the planted genotype-only mismatch, one planted FP and one planted FN.
- Per-record normalization (left alignment plus parsimony; Tan et al. 2015; `vt normalize`) gives each record a unique form in isolation but is not haplotype-aware. On a SNP and a deletion in the same homopolymer, the pinned `vt` produced overlapping records, and vcfeval then scored one extra FP and one extra FN (3/3 instead of 2/2). The VCF specification does not require normalization at all; the HGVS nomenclature requires the opposite (3′-most) placement.
- vcfeval chooses the matching that maximizes the number of included baseline plus call variants, with a path search capped at 50,000 simultaneously live paths or 10,000,000 iterations since the last synchronization point. Exceeding a cap removes the region's variants from scoring (GA4GH decision `N`, `BI=too-hard`) instead of failing. Executed: k equivalent heterozygous deletions per side in a 200-bp poly-A stayed scorable up to k=20 (33,059 live paths) and collapsed at k=22 (all 22 truth variants `N`, one spurious FP).
- At the pinned hap.py revision, documentation and code disagree on defaults: `--leftshift` is documented as off but defaults to on; the haplotype window is documented as 30 but `-w` defaults to 50 (30 is the block-expansion default); the enumeration threshold flag is `--xcmp-enumeration-threshold` with default 16768. The hap.py driver is Python 2 code and the repository's last commit is dated 2021-12-04.
- ACMG/AMP evidence combination has four machine-checkable formalizations. InterVar 2.2.2's `classfy` agrees with Richards et al. 2015 Table 5 on all 33,600 criterion-count combinations of a bounded box. The Tavtigian et al. 2018 Bayesian model with its published parameters (OP_VSt = 350, prior 0.10) puts five of the six Likely Pathogenic rules at posterior 0.89991, just below the 0.90 threshold; with prior 0.102 it coincides with the 2020 point system on the whole box. Both additive models move "≥2 Strong" from Pathogenic to Likely Pathogenic and "PVS1 + 1 Moderate" from Likely Pathogenic to Pathogenic. Rule formalization is not the dominant source of disagreement: nine laboratories agreed on 34% of variants before consensus discussion and 71% after (Amendola et al. 2016).

## Applicability

The report concerns the software chain that turns aligned reads into a classified germline variant: calling (DeepVariant as a production subject), representation (VCF and HGVS), benchmarking against reference truth sets (GIAB, GA4GH definitions, hap.py, vcfeval), and classification (ACMG/AMP rules, InterVar, Bayesian/point reformulations, ClinVar aggregation). Subjects relate as follows:

- **ga4gh/benchmarking-tools** (pinned) defines matching tiers, intermediate VCF annotations (`BD`, `BK`, `BI`, `BS`) and stratification requirements. **hap.py** (pinned) and **RTG Tools vcfeval** (pinned source; release 3.13 executed) implement them. The 3.13 tag resolves to the pinned rtg-tools revision `f72c7991210776631b2ee36b8038a64b45deb6da` (GitHub compare status "identical"), so the executed binary and the read source are the same release.
- **GIAB** benchmark versions are examined only through their publications (Zook et al. 2014, 2019; Wagner et al. 2022) and the pinned stratification repository, which contains scripts and manifests but no BED files. No truth VCF or BED was downloaded.
- **vt** (pinned) was built from source and executed. Building it from GitHub archives requires the `lib/htslib` submodule commit (`samtools/htslib` `5b684ce625d772dc558c68fd360c8af3ac155f7e`) and that commit's `htscodecs` submodule (`jkbonfield/htscodecs` `d7e357946ead219b81cc1becbe0de8a99d96ca84`); those are build dependencies, not separately analyzed.
- **biocommons/hgvs** (pinned) was read, not executed: its normalizer needs a transcript/sequence data provider that was not installed. The HGVS recommendations are read from the pinned website-source repository, which is the current text, not the 2016 paper's text.
- **InterVar** (pinned, version string 2.2.2 20210727) was examined only for its count-combination function; its evidence-assignment heuristics (e.g., PVS1 gene lists) were not evaluated.
- **DeepVariant** (pinned) was read for evaluation protocol, labeler and published metrics; it was not run.
- Literature subjects give the normative guideline (Richards et al. 2015), the Bayesian and point reformulations, the interlaboratory study, the benchmarking best practices and the truth-set construction papers.

Execution host for all measurements: Linux x86-64, 96 vCPU Intel Xeon @ 2.60 GHz, Python 3.13, bundled Zulu OpenJDK 11.0.27 from the RTG archive. Synthetic probe inputs are tiny and adversarially constructed; measured times are dominated by JVM start-up and do not characterize whole-genome runs. Nothing here is clinical guidance.

## Findings

### 1. Truth sets: how GIAB benchmarks are built and how versions differ

**Integration principle.** The pilot integration arbitrated "between 14 data sets from five sequencing technologies, seven read mappers and three variant callers" for NA12878/HG001 and classified regions where no confident genotype could be made (Zook et al. 2014 abstract). From v3 onward (Zook et al. 2019) each callset gets *callable regions* that exclude: regions around filtered or outlier variants; low-coverage or low-MAPQ regions; method-specific difficult regions (tandem repeats, segmental duplications); and, for gVCF inputs, hom-ref blocks or variants with GQ < 60. Calls supported by ≥2 technologies train an outlier model; outliers plus 50 bp are removed from that callset's callable regions in a second cycle. The arbitration rule is: a variant or region enters the benchmark "if at least one input callset was trustworthy and all trustworthy callsets agreed"; a discordant site is excluded together with 50 bp on each side.
Basis: documentation (Zook et al. 2014, 2019).

| Version (sample, reference) | Benchmark bases / fraction | Variants in benchmark | Source |
| --- | --- | --- | --- |
| v2.18, Sep 2014 (HG001, GRCh37, chr1–22+X) | 2.20 Gb; 77.4% of non-N; 73.9% of RefSeq CDS | 2,915,731 calls (2,741,359 SNPs) | Zook 2019 Table 1 |
| v3.3.2, Nov 2016 (HG001, GRCh37) | 2.58 Gb; 90.8%; 89.9% CDS | 3,691,156 calls (3,209,315 SNPs; 225,097 insertions) | Zook 2019 Table 1 |
| v3.3.2, Nov 2016 (HG001, GRCh38) | 2.44 Gb; 83.8%; 83.3% CDS | 3,542,487 calls (3,042,789 SNPs) | Zook 2019 Table 1 |
| v3.3.2 (HG002, GRCh38, chr1–22) | 85.4% | 3,030,495 SNVs; 475,332 indels | Wagner 2022 Table 1 |
| v4.2.1 (HG002, GRCh38, chr1–22) | 92.2% | 3,367,208 SNVs; 525,545 indels | Wagner 2022 Table 1 |
| v4.2.1 (HG002, GRCh37, chr1–22) | 94.1% | 3,353,881 SNVs; 522,388 indels | Wagner 2022 Table 1 |

v4.2.1 adds linked reads (10x Genomics) and PacBio HiFi, reaching difficult-to-map regions: of 270,860,615 GRCh38 autosomal bases in segmental duplications and low-mappability regions, v4.2.1 covers 145,585,710 (53.7%) versus 65,714,199 (24.3%) in v3.3.2, and 88% (versus 54%) of 10,009,480 bp in difficult-to-map medically relevant genes. Against v4.2.1, one Illumina GATK-BWA callset had 16,615 missed SNVs versus 1,960 against v3.3.2, 15,220 versus 1,381 of them in low-mappability/segmental-duplication regions. Benchmark self-validation: 433 of 452 (96%) curated FP/FN sites inside v3.3.2 regions and 422 of 463 (91%) outside were judged correct in the benchmark; Mendelian-inconsistent variants were 2,502 of 4,968,730 (0.05%) for the Ashkenazi trio; concordance with Platinum Genomes in the shared regions was 99.96%.
Basis: documentation (Wagner et al. 2022).

**Consequence for comparisons.** Expanding benchmark regions into harder sequence lowers measured recall without any change in the caller. A recall reported against v3.3.2 and one against v4.2.1 measure different populations of sites. Basis: derived from the counts above.

### 2. Stratification

The GA4GH stratification standard (pinned `doc/standards/GA4GHBenchmarkingPerformanceStratification.md`) requires output by variant type (SNV, insertions and deletions < 50 bp, complex variants, larger classes), sequence context (homopolymers 3–5, 6–10, > 10 bp; tandem repeats by unit and length; GC-content bins from < 15% to > 85%; mappability; segmental duplications), functional class and read-level characteristics, using zero-based BED files from a central resource. It warns that over-fine strata give confidence intervals too wide to be useful. Basis: normative (community standard text).

The pinned GIAB stratification repository describes v3.1 and holds only scripts, READMEs and manifests; BEDs live on the GIAB FTP site. The manifest `GRCh38/v3.1-GRCh38-all-stratifications.tsv` lists 182 strata (GenomeSpecific 90, LowComplexity 28, GCcontent 14, OtherDifficult 13, SegmentalDuplications 9, XY 9, ancestry 6, mappability 4, Union 4, FunctionalTechnicallyDifficultRegions 3, FunctionalRegions 2); `v3.1-GRCh38-v4.2.1-stratifications.tsv` lists 16, including `alldifficultregions`, `notinalldifficultregions`, `MHC` and `refseq_cds`. Basis: source + execution (line counts).

Krusche et al. 2019 (Table 2) show why stratification matters: adding PCR amplification drops indel recall from 97.1% to 85.8% overall, but only from 98.4% to 98.3% outside homopolymers and tandem repeats, while inside them it drops from 96.4% to 78.2%; at GC > 85% SNV recall drops from 94.4% to 84.7%. In 51–200 bp AT dinucleotide repeats, indel recall is 28.0% (PCR-free) and 12.0% (PCR); 86 of 114 truth indels there are compound heterozygous and 89% fall outside the high-confidence regions. Basis: documentation.

### 3. Comparison semantics in the GA4GH standard

**Tiers.** The best-practice paper defines three match types: genotype match (alleles and genotype agree), allele match (alleles agree, genotype may differ) and local match (a truth variant nearby). "Genotype match" is what the tools use to count TP/FP/FN; allele-only matches (`FP.GT`) and local-only matches (`FP.AL`) are additionally counted as both FP and FN. Query calls outside the truth BED are `UNK`. True negatives and specificity are deliberately not defined. Basis: documentation (Krusche et al. 2019, Table 1 and text).

**Intermediate VCF.** A comparison engine emits two sample columns, `TRUTH` and `QUERY`, with `BD` (decision TP/FP/FN/N) and `BK` (match kind): `.` = no match, `lm` = loose match, `am` = allele match ("one-sided haplotype match"), `gm` = genotype match. For genotype-level comparison the mapping is `./lm` → FN/FP, `am` → FN/FP ("genotype mismatch"), `gm` → TP; `BS` assigns a benchmarking superlocus id; `QQ` carries a ROC score (pinned `doc/ref-impl/intermediate.md` lines 45–96, 119–130). Basis: normative.

**Recorded defects in the standard documents at the pinned revision** (documentation, not code):
- "Negative Predictive Value: FP/(FP+FN)" appears for every comparison method (`GA4GHBenchmarkingPerformanceMetricsDefinitions.md` lines 53, 94, 133, 162). NPV is conventionally TN/(TN+FN); the given expression is not a predictive value, and the same document says TN is not defined (line 15). Basis: source (document text) + derived.
- Line 84 contains two concatenated, different definitions of "No-call variant (NCV)".
- `doc/ref-impl/outputs.md` lines 36–39 define `UNK` using "`BT` == `FP` and `BK` == `miss`", whereas `intermediate.md` names the decision field `BD` and uses `.` for no match.
- The 49-bp edge exclusion around confident regions (metrics doc lines 67, 110, 143, 174) is required text in a draft standard but is not described in the main text of Krusche et al. 2019 (its supplementary information was not read). Whether hap.py implements it was not examined.

### 4. hap.py at the pinned revision

**Engines** (`doc/happy.md` lines 327–357; `src/python/hap.py` lines 125–127): `xcmp` (default) enumerates haplotypes within a superlocus and converts a matching superlocus wholesale to TP; `vcfeval` assigns TP/FP per variant by optimization and ignores phasing; `scmp-distance` matches by location within `--scmp-distance` (default 30, line 140); `scmp-somatic` matches normalized alleles and ignores genotypes. The upstream micro-benchmark text says xcmp "struggles when variants are not decomposed into primitives" and that vcfeval "leads to a larger set of matches ... and therefore higher precision and recall" (`doc/microbench.md` lines 28–37). Krusche et al. recommend vcfeval "to provide the most partial matches". Basis: documentation + source.

**Counting rules.** Recall = TRUTH.TP/(TRUTH.TP+TRUTH.FN) uses the truth representation; Precision = QUERY.TP/(QUERY.TP+QUERY.FP) uses the query representation (`happy.md` lines 642–651), so TP counts can differ between the two sides when representations split or merge differently. Truth variants are PASS-only unless `--usefiltered-truth` (hap.py line 92–93). Confident-region capture uses each record's trimmed reference extent; an insertion is inside a region only if both the padding base and the following base are (`happy.md` lines 399–433), and `--adjust-conf-regions` (default True, hap.py lines 97–101) pads insertions. Confidence intervals are Brown–Cai–DasGupta "modified Jeffreys" intervals (`src/python/Tools/ci.py` lines 25–66), disabled by default (`--ci-alpha` default 0.0; `src/python/qfy.py` lines 282–283). Basis: documentation + source.

**Documentation versus code defaults** (all at `84011695b2ff2406c16a335106db6831fb67fdfe`):

| Setting | Documentation says | Code says | Basis |
| --- | --- | --- | --- |
| Left-shift query | "-L, --leftshift ... This is off by default." (`happy.md` 438); "(off by default)" (`normalisation.md` 70) | `parser.add_argument("-L", "--leftshift", ..., action="store_true", default=True` (`src/python/pre.py` 274–276); disabling needs `--no-leftshift` (277–278) | source |
| Decompose query | `normalisation.md` 71–72 "-D, --decompose ... (on by default)" | `--decompose` default True; `-D` means `--no-decompose` (`pre.py` 280–284) | source |
| Superlocus window | "-w WINDOW, --window-size ... The default value here is 30." (`happy.md` 552–560) | `"-w", "--window-size", ..., default=50` (hap.py 109–111) | source |
| Enumeration cap | `--enumeration-threshold MAX_ENUM` (`happy.md` 563) | `--xcmp-enumeration-threshold`, `default=16768` (hap.py 114–116) | source |
| Block expansion | `-e HB_EXPAND, --expand-hapblocks` (`happy.md` 577) | `--xcmp-expand-hapblocks`, `default=30` (hap.py 118–120) | source |
| Truth preprocessing | — | `--preprocess-truth` default False (hap.py 90–91): by default only the query is left-shifted/decomposed | source |

Interpretation: a reader following the manual would believe hap.py compares un-shifted queries; the code left-shifts and decomposes the query by default and leaves the truth untouched. The value 16768 is not a power of two (2^14 = 16384); the manual says each unphased het doubles candidate sequences, so this is "approximately 2^14". Whether 16768 is intentional is unknown. `bcftools norm` preprocessing (`--bcftools-norm`, off by default) is described as not haplotype-safe (`normalisation.md` 75–78). Basis: source + documentation + derived.

**Maintenance status.** The driver uses Python 2 syntax (`print "Hap.py %s" % Tools.version`, hap.py line 191). The pinned HEAD is dated 2021-12-04. DeepVariant's case study runs hap.py from a third-party container tag (`jmcdani20/hap.py:v0.3.12`, `docs/deepvariant-case-study.md` line 115) with `--engine=vcfeval --pass-only` (lines 129–130). Basis: source + documentation.

### 5. vcfeval's algorithm at the pinned revision

- **Search.** `PathFinder.bestPath()` explores, in reference order, joint assignments of each baseline and call variant to a haplotype (or exclusion) and keeps paths whose replayed haplotype sequences agree; a *sync point* is reached when only one path remains (`src/main/java/com/rtg/vcf/eval/PathFinder.java` lines 129–214).
- **Objective.** `MaxSumBoth.better()` prefers "paths that maximise total number of included variants (baseline + called)", then smaller |baseline − call| counts since the last sync point, then more frequent syncs, then allele order (`MaxSumBoth.java` lines 43–83). This is the "minimize FP + FN globally" requirement of the GA4GH draft (metrics doc line 23).
- **Caps.** When live paths exceed `com.rtg.vcf.eval.max-paths` (default 50000) or iterations since the last sync exceed `com.rtg.vcf.eval.max-iterations` (default 10000000) (`ToolsGlobalFlags.java` lines 142–143), the code logs "Evaluation too complex ... Variants in this region will not be included in results.", clears all paths and skips to the furthest position seen (`PathFinder.java` lines 162–169). Skipped variants get `BD=N` and `BI=too-hard` in GA4GH output (`Ga4ghEvalSynchronizer.java` lines 234–237, 284–287). Alleles longer than 1000 bp are not evaluated (`VcfEvalCli.java` line 148).
- **Genotype versus allele.** With two-pass evaluation, a diploid pass runs first, then a haploid ("squash-ploidy") pass on remaining FP/FN (`VcfEvalTask.java` lines 117–128); squash-pass matches are emitted as `BK=am` with `BD=FP`/`FN` (`Ga4ghEvalSynchronizer.java` lines 243–250, 296–302). `--squash-ploidy` alone treats hets as hom-alt on both sides (`VcfEvalCli.java` line 141). Phase is ignored unless `--Xobey-phase` is set (line 154).
- **Evaluation regions.** `-e` evaluates inside a BED "allowing transborder matches" (line 137); calls outside get `BD=N`, `BI=non-confident`.
Basis: source.

Cleary et al. 2015 report that on NA12878 regions with variants < 50 bp apart, "no tool except for vcfeval" (among bcftools norm, vt, SMaSH, vcflib, bcbio.variation) judged all sites in indel-containing regions consistent between two differently represented high-confidence call sets; the closest, SMaSH (Python), judged 171,227 of 184,634 consistent. Basis: documentation (the measurement used tool versions from 2015, not the pinned ones).

### 6. Executed probe: one haplotype set, several encodings

Inputs (`support/repr_probe/`): a 921-bp synthetic contig and 10 cases. A = 1-bp deletion in A6, truth left-aligned, query right-most. B = CA insertion in (CA)4, left versus right anchoring. C = GC→AT, one MNP record versus two SNPs. D = one delins record (`CGTA→CT`) versus 2-bp deletion plus adjacent SNP. E = same SNP, truth 0/1, query 1/1. F = SNP plus 1-bp deletion in one A4 run on the same haplotype (both 1/1), deletion placed at two equivalent positions. G = query-only SNP. H = truth-only SNP. I = identical SNP. J = query-only SNP outside the evaluation BED.

| Comparator | TP (truth / query) | FP | FN | Notes |
| --- | --- | --- | --- | --- |
| Toy exact matcher (POS, REF, ALT, GT), raw | 2 | 9 | 7 | toy written for this probe, not an upstream tool |
| Toy matcher after `vt normalize` on both files | 5 | 6 | 4 | normalization repairs A, B; not C, D |
| vcfeval default (genotype match) | 7 / 9 | 2 | 2 | FP = E (as 1/1) + G; FN = E + H; precision 0.8182, sensitivity 0.7778 |
| vcfeval `--squash-ploidy` | 8 / 10 | 1 | 1 | E becomes TP |
| vcfeval GA4GH mode | per record | — | — | A–D, F, I `gm`/TP; E `am` FP/FN; G FP; H FN; J `N`/`non-confident` |
| vcfeval on vt-normalized query, raw truth | 6 / 8 | 3 | 3 | F broken: query `508 CA>C` FP(`am`), truth `510 AA>A` FN(`am`) |

Basis: execution (RTG Tools 3.13 release binary; vt built at the pinned revision), with the toy matcher labelled as such.

Mechanism of the F failure (source + execution): `vt normalize` calls `right_trim_or_left_extend` then `left_trim` per record (`normalize.cpp` lines 236–237; `variant_manip.cpp` lines 513–583, 588–615), consulting only the reference. The deletion at 511 (`AA>A`) is shifted to `508 CA>C`, deleting the base that the separate SNP record at 509 changes to G. Each record is valid against the reference, but the pair is not jointly realizable; with both records normalized identically, the toy matcher counts both as TP, while vcfeval correctly rejects the pair against the un-normalized truth. hap.py's manual makes the same point for `bcftools norm` and describes its own left-shift as "safely" not moving records past each other (`happy.md` lines 461–462; `normalisation.md` 75–78); Krusche et al. 2019 state that normalization "can cause errors" when multiple records represent one complex haplotype.

### 7. Executed probe: the path-complexity cap

Setup (`support/scripts/complexity_sweep.py`): a 200-bp poly-A run; truth has k unphased heterozygous 1-bp deletions, query k heterozygous 1-bp deletions at other offsets (an equivalent haplotype set). Default caps, GA4GH output.

| k per side | max live paths (vcfeval log) | wall s | peak RSS kB | outcome |
| --- | --- | --- | --- | --- |
| 4 | 144 | 0.89 | 208,668 | all TP |
| 8 | 576 | 0.98 | 243,700 | all TP |
| 12 | 2,459 | 0.97 | 297,600 | all TP |
| 16 | 8,434 | 1.19 | 364,476 | all TP |
| 18 | 14,840 | 1.54 | 485,208 | all TP |
| 20 | 33,059 | 2.62 | 465,024 | all TP |
| 22 | 50,002 (cap) | 2.81 | 901,248 | 22 truth `N/too-hard`, 21 query `N`, 1 query FP |
| 24 | 50,002 | 2.89 | 1,483,800 | 22 truth `N`, 2 TP, 1 FP |
| 32 | 50,003 | 3.06 | 1,457,436 | 19 truth `N`, 13 TP, 1 FP |

With a lowered cap (`--XXcom.rtg.vcf.eval.max-paths=1000`) on a 10-versus-10 version in an 80-bp run (default run peak: 2,912 live paths), 8 truth and 7 query variants became `N` and one FP appeared (`support/complexity/complexity_results.json`). Interpretation: the cap is a silent denominator change. `N` variants leave both precision and recall, and a residual FP can appear where an assignment was cut mid-region. Basis: execution (real binary; synthetic, deliberately pathological inputs, so the measurement shows mechanism, not genome-wide frequency).

### 8. Representation and normalization

**VCF (normative).** POS is the first base of REF. For simple indels, REF and ALT "must include the base before the variant ... unless the variant occurs at position 1", and a padding base is required with symbolic alleles (`VCFv4.5.tex` lines 405–407). The v4.3 and v4.5 sources contain no left-alignment or normalization requirement (text search); v4.5 adds that "Variant normalisation has limited utility in regions of low complexity as almost identical haplotypes can have very different normalised representations" (line 1999). Basis: normative + execution (text search).

**Tan et al. 2015 definition.** A VCF entry is *left aligned* iff its position is smallest among entries with the same allele length representing the same variant, *parsimonious* iff it has the shortest allele length, and *normalized* iff both. Necessary and sufficient condition: the alleles end with at least two different nucleotides, and the alleles start with at least two different nucleotides or the shortest allele has length 1. Algorithm 1: repeat {if all alleles end with the same base, drop it; if any allele becomes empty, extend all alleles one base left}, then drop common leading bases while all alleles have length ≥ 2. The pinned `vt` code implements exactly this loop structure (`variant_manip.cpp` lines 521–582 and 592–614; the right-trim stops at contig position 1, line 536). `vt normalize` skips SV and VNTR types, does not check SNP REF consistency, exits on REF/reference mismatch by default and continues only with `-n`/`-m` (`normalize.cpp` lines 103–107, 120–121, 204–218), and records `OLD_VARIANT` (line 243). Basis: documentation + source.

Measured impact (Tan et al. 2015): of 1000 Genomes phase 3 non-SNP entries, 5,057,823 (19.8%) needed normalization and 473,767 (1.9%) were redundant; GATK `LeftAlignAndTrimVariants` matched 96.6% but failed on 615,515 entries, 99.9% of them multi-allelic indels; 3,994 of 9,996 (40%) array-based indels were not normalized; normalization raised overlap with 1000 Genomes from 49% to 81% (array indels). For dbSNP 141 the text gives "897 438 (14.9%)" not normalized of 6,367,920, but 897,438/6,367,920 = 14.1%, matching the table's "14%". Basis: documentation + derived arithmetic.

**HGVS 3′ rule (normative).** "for all descriptions, the most 3' position possible of the reference sequence is arbitrarily assigned to have been changed", applying to genome, gene, transcript and protein descriptions (`docs/recommendations/general.md` lines 36–38). For minus-strand genes in repeats, the g. and c. descriptions therefore name different nucleotides (lines 157–159; example `NC_000023.11:g.32343183del` = `NM_004006.2:c.5697del`, `docs/recommendations/DNA/deletion.md` lines 33–40). Exception: a c. description is not shifted into the next exon (`deletion.md` line 55). Basis: normative.

| Convention | Shift direction in genome coordinates | Basis |
| --- | --- | --- |
| VCF after vt/bcftools-style normalization | leftmost (5′ on plus strand) | source (vt) |
| HGVS g. | rightmost (3′ on plus strand) | normative |
| HGVS c./n., plus-strand transcript | rightmost | normative |
| HGVS c./n., minus-strand transcript | leftmost (3′ of the transcript) | normative + derived |

So converting a VCF indel in a repeat to HGVS always requires a shift for g.; for c. it requires one only on plus-strand transcripts. Basis: derived.

**hgvs normalizer (pinned).** Defaults: `shuffle_direction = 3`, `cross_boundaries = False`, `window_size = 20`, `validate = True` (`src/hgvs/_data/defaults.ini` lines 30–34). With `cross_boundaries` false, n./r. variants shuffle only within their exon and within the CDS or UTR segment, and variants spanning an exon–intron, UTR–CDS or CDS–UTR boundary raise `HGVSUnsupportedOperationError` (`normalizer.py` lines 217–290). Protein and conversion variants are unsupported (78–83), intronic-offset variants are unsupported (99–101), uncertain variants are returned unchanged (73–74), an insertion equal to the adjacent sequence becomes a `dup` (160–182), and an equal-length change equal to its reverse complement becomes `inv` (144–145). The shuffle is trim-suffix/trim-prefix then roll (`src/hgvs/utils/norm.py` lines 62–98, code imported from vgraph). Basis: source.

**Measured discordance (Yen et al. 2017).** Exact SNV syntax concordance between ClinVar and VEP/SnpEff exceeded 99.5% but was below 90% for non-SNVs; coding concordance was 86% for deletions and 88% for insertions; for 16.6% (113/681) of insertions the ClinVar syntax appeared wrong through failure to right-shift or to describe a duplication; about 10% of transcripts differed in version from the annotation set, and ignoring transcript matching reduced accuracy to 20–30% (coding); COSMIC insertion concordance was below 15%. Basis: documentation.

### 9. DeepVariant as a benchmark consumer

- **Training labels are themselves haplotype-matched.** `haplotype_labeler.py` finds genotype assignments for candidates and truth "that results in the same two haplotype sequences in the region", citing the GA4GH repository (lines 29–56), with defaults: max group size 8, max separation 30 bp, max genotype-option product 100,000, forced grouping 0 bp (lines 78–94). Training needs `truth_vcf` and `confident_regions` (`docs/deepvariant-details.md` lines 113–118).
- **Hold-outs.** chr20–22 have "always" been excluded from training and HG003 is excluded since v1.1 (`docs/deepvariant-details-training-data.md` lines 120–122); v1.0 used HG002–HG004 only in "v4.2 subtracting v3.3.2" regions (lines 113–115).
- **Published evaluation.** The case study (v1.10.0) benchmarks HG003 chr20 against GIAB v4.2.1 with the `noinconsistent` BED: INDEL recall 0.995484, precision 0.998643, F1 0.997061 (10,628 truth, 48 FN, 15 FP); SNP recall 0.996252, precision 0.999257, F1 0.997752 (70,166 truth, 263 FN, 52 FP) (`docs/deepvariant-case-study.md` lines 136–143). Whole-genome WGS HG003: INDEL F1 0.99598, SNP F1 0.996136 (`docs/metrics.md` lines 33–34).
- **Derived checks.** The usage guide says changes "reduced our error rate by more than 50%" relative to April 2016 (lines 195–211). From its own tables (FN+FP): SNP 2,521 → 1,098 (−56.4%), INDEL 7,014 → 4,195 (−40.2%), combined 9,535 → 5,293 (−44.5%). The claim holds for SNPs only. In `metrics.md` the SNP TRUTH.TOTAL is 3,327,496 for the WGS row and 3,327,495 for the PacBio, ONT and hybrid rows, all HG003 against the same benchmark; the one-variant difference is unexplained (unknown). Basis: documentation + derived.

### 10. ACMG/AMP evidence combination

**Table 5 (normative, Richards et al. 2015).** Pathogenic: PVS1 with (≥1 PS, or ≥2 PM, or 1 PM + 1 PP, or ≥2 PP); or ≥2 PS; or 1 PS with (≥3 PM, or 2 PM + ≥2 PP, or 1 PM + ≥4 PP). Likely pathogenic: PVS1 + 1 PM; 1 PS + 1–2 PM; 1 PS + ≥2 PP; ≥3 PM; 2 PM + ≥2 PP; 1 PM + ≥4 PP. Benign: BA1, or ≥2 BS. Likely benign: 1 BS + 1 BP, or ≥2 BP. Uncertain otherwise, or when benign and pathogenic criteria are contradictory.

**InterVar implementation.** `classfy` (`Intervar.py` lines 733–856) sums each strength list (`sum_of_list`, 727–731), applies optional user up/down-grades from an evidence file (746–820), then encodes the rules in lines 825–847 and resolves conflicts in 849–852 (`if PAS_out != -1 and BES_out != -1: BPS_out=4`, i.e. Uncertain). Its `check_BA1` docstring names ESP, 1000 Genomes and ExAC, but the code tests `1000g2015aug_all`, `esp6500siv2_all` and `gnomAD_genome_ALL` at > 0.05 (lines 1334–1350). Basis: source.

**Bayesian and point reformulations.** Tavtigian et al. 2018: OP = OP_VSt^(N_Su/8 + N_M/4 + N_St/2 + N_VSt), with benign evidence inverting the odds; Post = OP·p/((OP−1)·p+1); thresholds P > 0.99, LP > 0.90, LB < 0.10, B < 0.001; exponent 2 was "uniquely optimal"; with p = 0.10 and OP_VSt = 350 "only two of the 18" rules were inconsistent: Pathogenic (ii) (OP 350, Post 0.975) and Likely Pathogenic (i) (OP 1,514, Post 0.994). Tavtigian et al. 2020: points Su 1, M 2, St 4, VSt 8 (negative for benign) proportional to log-odds; P ≥ 10, LP 6–9, VUS 0–5, LB −1 to −6, B ≤ −7; "Operationally, the prior probability should be understood to be infinitesimally greater than 0.10", suggesting 0.102. Basis: documentation.

**Executed comparison** (`support/scripts/acmg_probe.py`; box PVS1 0–1, PS 0–4, PM 0–6, PP 0–5, BA1 0–1, BS 0–4, BP 0–7 = 33,600 count combinations; BA1 treated as a stand-alone Benign override in the additive models):

| Pair | All 33,600 | Pathogenic-only (420) | Benign-only (80) |
| --- | --- | --- | --- |
| Table 5 re-encoding vs InterVar `classfy` (executed from the pinned file) | 0 | 0 | 0 |
| Table 5 vs Bayes (p = 0.10, OP_VSt = 350) | 27,778 | 28 | — |
| Table 5 vs Bayes (p = 0.102) | 28,350 | 23 | — |
| Table 5 vs points (2020) | 28,350 | 23 | 8 |
| Bayes (p = 0.102) vs points | 0 | 0 | 0 |

At minimal counts, LP(ii)–(vi) all have OP = 350^0.75 = 80.9 and posterior 0.89991 at p = 0.10, so Bayes classifies them as VUS. Table 1 of the 2018 paper prints the same posterior rounded to 0.900, and the 2020 paper's operational prior resolves the ambiguity. Pathogenic-only disagreements with points are 19 LP→P (e.g., PM 3 + PP 4), 2 P→LP (PS 2; PS 2 + PP 1) and 2 VUS→LP (PVS1 alone = 8 points; PVS1 + PP 1 = 9). Benign-only disagreements: single BP or single BS → LB, and BS 1 + BP ≥ 3 or BP 7 → B. Most "all-box" disagreements are mixed-evidence cases: Table 5 calls any co-occurrence of a pathogenic and a benign conclusion "contradictory" (31,108 of 33,101 mixed combinations fire both sides), while additive models net the evidence. The box weights every count combination equally; these counts are not clinical frequencies. Basis: execution (toy re-encoding of Table 5 plus InterVar's own function) + derived.

**Human application.** Nine CSER laboratories classified 99 variants: within-lab agreement between ACMG-AMP and in-house methods was K-alpha 0.91 (79% concordance); inter-lab concordance was 34% initially and 71% after consensus discussion; inter-lab K-alpha was 0.72 (95% CI 0.68–0.76) for ACMG-AMP versus 0.76 (0.73–0.80) for in-house criteria; 43/194 (22%) classification pairs differed in a way likely to affect medical management. The most used criteria were PM2 (41%), PP3 (39%), BS1 (26%) and PVS1 (20%) (Amendola et al. 2016). Basis: documentation.

**Recording conflicts.** ClinVar aggregates submissions per variant–condition (RCV) and per variant (VCV) and computes an aggregate interpretation indicating consensus or disagreement (Landrum et al. 2018). The current review-status documentation assigns 4 stars for a practice guideline, 3 for an expert panel (when either exists, its review status is used for the aggregate record), 2 for "criteria provided, multiple submitters, no conflicts", 1 for "criteria provided, conflicting classifications" (conflicting values enumerated) or a single submitter, 0 without assertion criteria; pairwise conflicts are exported in `summary_of_conflicting_interpretations.txt`. Basis: documentation (web page accessed 2026-11-20; no immutable revision).

### 11. Performance and resource footprint

Every cell is measured on the host named under Applicability, quoted from a cited source, derived (arithmetic shown), or marked `not measured`.

| Level | Item | Value | Basis |
| --- | --- | --- | --- |
| L1 authoring/maintenance | Size of InterVar's combination logic | 124 lines (`Intervar.py` 733–856) for 18 rules plus grade overrides | source (line count) |
| L1 | Human effort to reach 71% interlab concordance | consensus calls and e-mail re-review across 9 laboratories; person-hours not reported | documentation (Amendola 2016) |
| L1 | Upstream maintenance state of hap.py | last commit 2021-12-04; Python 2 driver | source |
| L1 | LLM token/turn budgets, LoC per person-month for any subject | not measured | — |
| L2 build | vt from source at the pinned revision (with htslib/htscodecs submodule pins), `make -j16` | 29.07 s wall, 287.41 s user, 13.71 s system; peak per-process RSS 231,736 kB | execution (`support/build/build_vt_timing.txt`) |
| L2 | vt build friction | GitHub source archive lacks `lib/htslib` submodule; required fetching two submodule commits, `config.guess`/`config.sub`, a hand-written `htscodecs` version header, and disabling bzip2/libcurl | execution |
| L2 | hap.py build; DeepVariant build | not measured | — |
| L2 | RTG Tools | prebuilt archive, 52,566,778 bytes (includes a JRE) | execution (`ls`) |
| L3 comparison latency | vcfeval on the 921-bp probe | 0.86–1.37 s wall per run (JVM start-up dominated) | execution |
| L3 | vcfeval path search growth, k equivalent hets per side | 144 (k=4) → 33,059 (k=20) live paths; cap hit at k=22 | execution (Finding 7) |
| L3 | vt normalize on the probe | 0.004–0.010 s wall | execution |
| L3 | hap.py runtime | not measured | — |
| L4 caller runtime | DeepVariant WGS HG003, n2-standard-96 | 1 h 8 m 58 s total (make_examples 46 m 15 s; call_variants 15 m 58 s; postprocess 6 m 45 s), mean of 5 runs | documentation (`docs/metrics.md` 54–71) |
| L4 | call_variants GPU effect | "2.5x speedup ... single P100 GPU and 8 CPUs"; at most one GPU used | documentation (`deepvariant-details.md` 133–139) |
| L4 | CRAM versus BAM for one make_examples job (30×) | size 37.85 vs 66.99 GB (56.50%); runtime 96 m 53 s vs 79 m 47 s (121.43%) | documentation (`deepvariant-details.md` 247–251) |
| L5 result checking | Independent re-verification of a benchmark run | not applicable in the proof-checker sense; vcfeval/hap.py are themselves the checkers; no independent re-checker examined | derived |
| L6 memory | vcfeval peak RSS, 921-bp probe | 170,992–263,464 kB | execution |
| L6 | vcfeval peak RSS, sweep k=24 (`-Xmx4g`) | 1,483,800 kB | execution |
| L6 | SDF for a 921-bp contig | 30,119 bytes in one run (varies slightly run to run) vs 943-byte FASTA | execution |
| L6 | vt binary | 7,126,008 bytes (unstripped, `-O3`) | execution |
| L6 | DeepVariant make_examples per shard (Illumina WGS v1.8.0, 1/25 of chr20) | mean 435.1 MB, max 449.3 MB | documentation (`deepvariant-details.md` 73–76) |
| L6 | call_variants; postprocess_variants | ~4 GB per process; 2–3 GB per core, 20–50 GB with `--cpus=0` | documentation (`deepvariant-details.md` 128, 150–154) |
| L6 | Energy/power for any subject | not measured | — |

### 12. Comprehensibility and conceptual simplicity

- **C1, working-memory load of a benchmark number.** A reader must hold truth version, BED, stratum, match tier, engine, preprocessing (hap.py left-shifts and decomposes the query, not the truth, by default), PASS filtering and engine caps to interpret one recall value. hap.py reports recall in the truth representation and precision in the query representation, so TP counts can differ between the two sides. The GA4GH VCF output is the legible artifact: each record carries `BD`/`BK`/`BI`/`BS`, and the probe's broken F case was diagnosable from `BK=am` on two records sharing `BS=509`. Basis: source + execution.
- **C1, diagnostics that hide denominator changes.** The vcfeval cap produces a log warning and `BI=too-hard`, not an error or a summary-line count. A reader of `summary.txt` alone cannot see that variants were dropped. Basis: execution.
- **C1, rule legibility.** Table 5 is 18 OR-clauses (8 Pathogenic, 6 Likely Pathogenic, 2 Benign, 2 Likely Benign) with an implicit "contradictory → VUS" rule. The 2020 point system replaces it with integer addition and five ranges, but hides the prior and odds, as its authors note ("the Bayesian nature of the system is hidden"). Interlaboratory disagreement arose mainly in assigning criteria and strengths (e.g., PVS1 downgraded four times, PP1 most often modified), not in combining them. Basis: documentation + execution.
- **C2, one invariant with several mechanisms.** "Same haplotype pair ⇒ same benchmark outcome" is enforced by at least four mechanisms: per-record normalization (vt, bcftools), decomposition into primitives (hap.py pre-processing), superlocus haplotype enumeration (xcmp, DeepVariant labeler) and global path optimization (vcfeval). Only the last two compare the actual invariant (replayed haplotype sequences); the first two are canonicalizations whose uniqueness theorem (Tan et al. Lemma 1) holds per record and therefore cannot be composed across records. The minimal universal abstraction is "compare the sets of haplotype sequences over a superlocus". Its cost reappears as search complexity (Finding 7), not as adapter code. Basis: derived.
- **C2, direction as a realization accident.** VCF left alignment and HGVS 3′ shifting pick opposite representatives of the same equivalence class; neither is semantically privileged. A tool converting between them needs transcript orientation, exon boundaries (HGVS exception) and reference sequence. Basis: normative + derived.
- **C2, ordinal rules versus additive odds.** Bayes (p = 0.102) and points coincide on the whole box, so they are one model with two notations. Table 5 is a different model: it is non-additive for mixed evidence and treats P(ii)/LP(i) differently. Basis: execution.

### 13. Validation of implementations and proposed solutions

- **V1, specification adequacy and non-vacuity.** Truth sets are validated by manual curation of putative FP/FN (Wagner et al. 2022: 96% and 91% correct), Mendelian consistency (0.05% violations) and cross-benchmark concordance (99.96% with Platinum Genomes). The ACMG/AMP rules were tested for internal Bayesian consistency (Tavtigian et al. 2018: 2 of 18 inconsistent), and InterVar's encoding was checked here against an independent re-encoding on 33,600 count combinations (0 mismatches; bounded enumeration). The GA4GH draft metric text contains a wrong NPV formula (Finding 3), an example of an unvalidated specification artifact. Basis: documentation + execution.
- **V2, differential testing of comparators.** Cleary et al. 2015 compared six normalizers/comparators on two real high-confidence sets; the upstream hap.py micro-benchmark compares xcmp and vcfeval with and without decomposition; this report's probe differential-tests a toy matcher, vt-plus-matcher and vcfeval on planted equivalences and reports where each diverges. No metamorphic or fuzzing campaign against hap.py or vcfeval was found or run (not examined beyond these).
- **V3, concurrency and crash behavior.** vcfeval runs one thread-pool task per reference sequence (`VcfEvalTask.java` lines 131–137); no concurrency or crash-consistency validation of any subject was examined. Silicon, power-trace and masking validation do not apply to these subjects (known not to apply).
- **V4, field and human validation.** The precisionFDA Truth and Consistency challenges (2016) served as field trials of the GA4GH methodology, and Krusche et al. show that changing matching stringency reverses the FP ranking of two submissions (Figure 4). Amendola et al. 2016 is the empirical test of human application of the rule system (34% → 71%). STL falsification, hardware-in-the-loop replay and runtime model monitors do not apply (known not to apply).

## Boundaries

- **not examined:** GIAB truth VCF/BED files themselves (no download; only publications and manifests); hap.py execution (Python 2 build not attempted), xcmp behavior on the probe, and whether hap.py implements the 49-bp edge exclusion; DeepVariant execution; the hgvs normalizer's runtime behavior (needs a data provider); bcftools norm; ClinGen sequence-variant-interpretation refinements of individual criteria beyond those quoted from Amendola et al.; ClinVar data files; structural-variant and tandem-repeat benchmarks; somatic comparison modes; phasing-aware evaluation (`--Xobey-phase`); stratified hap.py output on real data.
- **unknown:** whether hap.py's `16768` enumeration default is intentional; the cause of the one-variant SNP TRUTH.TOTAL difference across DeepVariant metrics rows; how often the vcfeval path cap fires on real GIAB v4.2.1 comparisons (the probe shows mechanism only, on synthetic pathological input); whether the GA4GH NPV text propagated into any implementation.
- **known not to apply:** silicon/power/masking validation (V3) and plant/HIL validation (V4) to these software-only subjects; proof-certificate checking speeds (L5) in the proof-assistant sense.
- **unsupported (by the subject):** hgvs normalization of protein, conversion, intronic-offset and boundary-spanning variants (raises `HGVSUnsupportedOperationError`); vcfeval evaluation of alleles longer than 1000 bp (default) and of regions above the path/iteration caps; hap.py vcfeval engine with symbolic records (`happy.md` lines 346–347).
- **Stronger conclusions not established:** (a) vcfeval is not shown to be correct in general; the probe covers 10 planted cases and one family of complexity inputs. (b) Normalization is not shown to be harmful on real data; the probe shows a constructible failure, consistent with upstream warnings, not its frequency. (c) The ACMG disagreement counts are over uniformly weighted count combinations and do not estimate clinical discordance. (d) DeepVariant accuracies are vendor-reported and depend on hap.py version, engine, truth version and BED; they were not reproduced. (e) The "error rate reduced by more than 50%" claim is checked only against the tables in the same document.

## Evidence

Observation date for all source reads, executions and literature checks: 2026-11-20 (UTC).

**Pinned repositories (GitHub, read via `raw.githubusercontent.com` at the stated revision):**
- `Illumina/hap.py` @ `84011695b2ff2406c16a335106db6831fb67fdfe`: `src/python/hap.py` 90–127, 140–141, 191; `src/python/pre.py` 274–288; `src/python/qfy.py` 282–283; `src/python/Tools/ci.py` 25–66; `doc/happy.md` 49–81, 327–357, 399–433, 435–471, 549–581, 640–670; `doc/normalisation.md` 65–82, 123–131, 185–267; `doc/microbench.md` 17–37.
- `RealTimeGenomics/rtg-tools` @ `f72c7991210776631b2ee36b8038a64b45deb6da` (tag 3.13): `src/main/java/com/rtg/vcf/eval/PathFinder.java` 51–101, 129–214; `MaxSumBoth.java` 36–83; `VcfEvalTask.java` 110–175; `Ga4ghEvalSynchronizer.java` 59–68, 228–310; `VcfEvalCli.java` 67–84, 132–156; `src/main/java/com/rtg/launcher/globals/ToolsGlobalFlags.java` 76–104, 136–150.
- `ga4gh/benchmarking-tools` @ `e07e6ca9dc372d7b61148ecd0677f7da7cce53a4`: `doc/standards/GA4GHBenchmarkingPerformanceMetricsDefinitions.md` (lines 15, 23, 53, 67, 84, 94, 133, 162, 178); `doc/standards/GA4GHBenchmarkingPerformanceStratification.md`; `doc/ref-impl/intermediate.md` 1–133; `doc/ref-impl/outputs.md` 29–53.
- `genome-in-a-bottle/genome-stratifications` @ `badb7b3cb77acc80a888e056a6bfe5e957e1d3fa`: `README.md`; `GRCh38/v3.1-GRCh38-all-stratifications.tsv` (182 rows); `GRCh38/v3.1-GRCh38-v4.2.1-stratifications.tsv` (16 rows).
- `google/deepvariant` @ `45f2627504c59785ea2b88d0256a2ec347bce7b4`: `docs/deepvariant-details.md` 64–76, 113–157, 195–211, 247–260; `docs/deepvariant-case-study.md` 32–43, 115–143; `docs/metrics.md` 31–96; `docs/deepvariant-details-training-data.md` 98–122; `deepvariant/labeler/haplotype_labeler.py` 29–94.
- `atks/vt` @ `c6bd1591a23a1d116d52834a627c00bbf7ed4a64`: `normalize.cpp` 96–123, 174–250; `variant_manip.cpp` 510–615; `README.md`. Build dependencies: `samtools/htslib` @ `5b684ce625d772dc558c68fd360c8af3ac155f7e`, `jkbonfield/htscodecs` @ `d7e357946ead219b81cc1becbe0de8a99d96ca84`. Source-archive SHA-256: vt `43402e82704b64e6e8ff5fa7b040ba9d06715697334d0fcff0ce758f4338c9f8`, htslib `101c69b360b40f6f910fe2d9a6fffd4639d6bfe9ecb29ffd5762b4b071c29a06`, htscodecs `80997c8381ffcb104270ef7f441995944987734b2047a241d5a61733cdcc5c66`.
- `biocommons/hgvs` @ `79b9c2982394bd56b6c143940acdfe7ced432bfb`: `src/hgvs/normalizer.py` 1–463; `src/hgvs/utils/norm.py` 1–140; `src/hgvs/_data/defaults.ini` 25–37.
- `HGVSnomenclature/hgvs-nomenclature` @ `3aee3e9c2d248de3984f150dbdc640920e16eca0`: `docs/recommendations/general.md` 36–38, 157–159; `docs/recommendations/DNA/deletion.md` 20–55; `docs/recommendations/checklist.md` 37–39.
- `samtools/hts-specs` @ `510c107ba89aa13113818c9e4fa3071283cb7f7b`: `VCFv4.5.tex` 405–407, 1999; `VCFv4.3.tex` (searched; no normalization requirement).
- `WGLab/InterVar` @ `4801682d37982bb3e99b50392790878a568b42cd`: `Intervar.py` 14, 727–856, 1334–1350.

**Executed artifacts.** `rtg-tools-3.13-linux-x64.zip`, SHA-256 `b00b6c80bad520f446b1ee2a5070aced45496fd4771bb31f3c63dfa128215d26`, 52,566,778 bytes; RTG.jar was invoked as `jre/bin/java -Dtalkback=false -Dusage=false -Xmx1g -jar RTG.jar <command>` (`-Xmx4g` for the sweep). All probe scripts, inputs and outputs are under `support/` (see `support/README.md`); recorded paths are rewritten as `$WORK`, `$RTG_DIR`, `$VT`.

**Literature.** Each DOI was resolved through the doi.org handle API (responseCode 1) and its title, venue, year and first author were matched against OpenAlex metadata. The Crossref API was not reachable through the available web fetcher, which refused the request. Full texts were read from PubMed Central where available; for Zook 2014 only the publisher abstract was read, and for Poplin 2018 only the abstract via a web search summary.
- Zook et al., Nat Biotechnol 32(3):246–251, 2014, 10.1038/nbt.2835 (abstract).
- Richards et al., Genet Med 17(5):405–424, 2015, 10.1038/gim.2015.30 (Table 5; PMC4544753).
- Tan, Abecasis, Kang, Bioinformatics 31(13):2202–2204, 2015, 10.1093/bioinformatics/btv112 (PMC4481842).
- Cleary et al., bioRxiv 2015, 10.1101/023754 (v2 full text, section 2.8 and Table 1).
- Hart et al., Bioinformatics 31(2):268–270, 2015, 10.1093/bioinformatics/btu630 (DOI verified; not otherwise relied on).
- den Dunnen et al., Hum Mutat 37(6):564–569, 2016, 10.1002/humu.22981 (DOI verified; current recommendations read from the pinned site source instead).
- Amendola et al., Am J Hum Genet 98(6):1067–1076, 2016, 10.1016/j.ajhg.2016.03.024 (PMC4908185).
- Yen et al., Genome Med 9:7, 2017, 10.1186/s13073-016-0396-7 (PMC5267466).
- Landrum et al., Nucleic Acids Res 46(D1):D1062–D1067, 2018, 10.1093/nar/gkx1153 (PMC5753237).
- Tavtigian et al., Genet Med 20(9):1054–1060, 2018, 10.1038/gim.2017.210 (PMC6336098; Table 1).
- Poplin et al., Nat Biotechnol 36(10):983–987, 2018, 10.1038/nbt.4235 (abstract).
- Wang et al., Hum Mutat 39(12):1803–1813, 2018, 10.1002/humu.23615 (PMC6282708).
- Zook et al., Nat Biotechnol 37(5):561–566, 2019, 10.1038/s41587-019-0074-6 (PMC6500473; Table 1, Figure 1).
- Krusche et al., Nat Biotechnol 37(5):555–560, 2019, 10.1038/s41587-019-0054-x (PMC6699627; Tables 1–2, Figure 4).
- Tavtigian et al., Hum Mutat 41(10):1734–1737, 2020, 10.1002/humu.24088 (PMC8011844; Tables 2–3).
- Wagner et al., Cell Genomics 2(5):100128, 2022, 10.1016/j.xgen.2022.100128 (PMC9706577; Table 1).
- Brown, Cai, DasGupta, Stat Sci 16(2):101–133, 2001, 10.1214/ss/1009213286 (cited by hap.py `ci.py`; DOI verified only).
- The GA4GH metrics draft (line 178) cites "doi:10.1101/001958" for call weighting; that DOI resolves to the pedigree-calling paper by Cleary et al. (J Comput Biol 21(6):405–419, 2014), DOI verified only.
- ClinVar review status page, https://www.ncbi.nlm.nih.gov/clinvar/docs/review_status/, accessed 2026-11-20 (no immutable revision available).

## Revalidation

1. **hap.py defaults:** `curl -sSL https://raw.githubusercontent.com/Illumina/hap.py/<rev>/src/python/pre.py | sed -n 270,290p` and the same for `src/python/hap.py` lines 105–130. Compare with `doc/happy.md` lines 435–581. A newer revision either still disagrees or has been reconciled.
2. **vcfeval semantics:** diff `PathFinder.java`, `MaxSumBoth.java`, `ToolsGlobalFlags.java` (max-paths, max-iterations) and `Ga4ghEvalSynchronizer.java` between the pinned revision and the new one. Then rerun `support/scripts/repr_probe.py` (about 10 s) and check `vcfeval_default.summary.txt` = 7/9/2/2 and `vcfeval_query_vtnorm.summary.txt` = 6/8/3/3.
3. **Complexity cap:** rerun `support/scripts/complexity_sweep.py` (about 30 s) and locate the first k where `too_complex_warnings > 0` (22 at the pinned release). A changed k means the search or caps changed.
4. **vt normalization:** run the built `vt normalize` on `support/repr_probe/query.vcf` with `ref.fa`; the F-case deletion must become `508 CA>C` with `OLD_VARIANT=chrP:511:AA/A` if the per-record algorithm is unchanged.
5. **ACMG combination:** `python3 support/scripts/acmg_probe.py Intervar.py` against a new InterVar revision; any nonzero `R_vs_IV` count means InterVar's combination logic changed. Re-read Table 5 if a guideline revision is published; the additive-model results depend only on the published formulas.
6. **HGVS/VCF direction rules:** re-read `docs/recommendations/general.md` (3′ rule, minus-strand note) and grep new VCF spec versions for "normalis"/"left-align".
7. **Truth-set numbers:** they are fixed per published version. A new GIAB release needs its own README/paper counts and a new comparison table, not reuse of these.
