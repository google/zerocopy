# Automated welfare debt and fraud determination: Robodebt income averaging, Michigan MiDAS adjudication, the Dutch SyRI judgment and childcare-benefit risk model, and the Rotterdam risk-model audit

This report records mechanisms, judgments, findings and evidence, each attributed to its source. It contains no legal or benefits advice.

## Summary

- **Robodebt (Australia, 2015–2019).** Unless rebutted, annual employer-reported (ATO PAYG) income was divided evenly across a period's fortnights and run through a fortnightly income test. The Royal Commission found that averaging "neither produced accurate results nor complied with the income calculation provisions of the Social Security Act 1991 (Cth)", because entitlement depends on income actually earned in each fortnight. Recipients bore the onus of disproof; a 10% "recovery fee" was added. In *Amato* (2019) the Federal Court declared, with the Commonwealth's consent, that an averaging-based debt demand was not validly made.
- **Toy model (not the agency system).** A synthetic person who earns everything before claiming owes \$0 under a fortnightly test but \$5,407.75 under averaging. In a synthetic cohort of 2,000, 1,242 averaged debts were false and 81 understated.
- **MiDAS (Michigan, Oct 2013–Aug 2015).** Non-response to a questionnaire within ten days, or any affirmative answer, produced an automatic finding of intentional fraud and a penalty of four times the benefits. Courts attribute a 93% error figure to different reviewers. *Cahoo* (6th Cir. 2019) let the due-process claim proceed against agency officials; *Bauserman* (Mich. 2022) held damages available for state constitutional torts; the class settled for \$20 million.
- **SyRI (Netherlands, 2020).** A points-and-cutoff risk model over 17 linkable data categories was held to fail the Article 8(2) ECHR fair balance for lack of transparency and verifiability. The court left GDPR Article 22 open.
- **Childcare benefits.** The Dutch DPA held that a self-learning risk model's Dutch/non-Dutch nationality indicator was discriminatory.
- **Rotterdam.** A caret/`gbm` gradient boosting machine (315 features, 500 trees) was trained on past investigations, labelled "Ja" if a fraud amount was recorded or the running benefit was adjusted or ended. Lighthouse Reports' parity tests found higher flag rates for women, parents and people with weaker Dutch. A recomputation from the published summary statistics is consistent with an unpaired pooled t-test. By derivation, that test was also applied to paired counterfactual copies.

## Applicability

- **Documents as subjects.** Four of the five systems are known only through official reports, judgments and journalism, to which findings are attributed. The only agency code and model available were Rotterdam's, as published in `Lighthouse-Reports/suspicion_machine` at `3afc105b04ff3dcdcacbfa5ab39d9cc089264845`.
- **Court posture.** *Cahoo* (2019) and *Bauserman* (2022) decided pleading-stage motions; their facts are allegations accepted as true. The *Amato* orders and *Prygodicz* (No 2) were not read in primary form; they are reported via the Royal Commission, Victoria Legal Aid and the applicants' firms.
- **Language.** SyRI and *Ongekend onrecht* were read in official English translations; DPA quotations are translated by this report.
- **Toy models.** The averaging probe is a stylised two-band income test using official 2016–17 Newstart parameters. The parity recomputation re-tests published summary statistics only; Rotterdam's model was not run, because no R runtime was available.
- **Relationship.** The systems are compared as instances of automated welfare debt or fraud decisions; no shared code or vendor is claimed.

## Findings

### 1. Robodebt: income averaging, onus, courts and the Royal Commission

Basis: documentation (Royal Commission report, Overview and Chapters 1–7 of Volume 1; case notes and abstracts as cited).

**Iterations, as listed in the Letters Patent quoted by the report:**

| Iteration | Period |
|---|---|
| PAYG Manual Compliance Intervention | pilots from early 2015; programme from 1 July 2015 |
| Online Compliance Intervention (OCI) | assessments initiated "on or around 1 July 2016 to on or around 10 February 2017" |
| Employment Income Confirmation (EIC) | "11 February 2017 to on or around 30 September 2018" |
| Check and Update Past Income (CUPI) | "after on or around 30 September 2018" |

The online platform rolled out in September 2016, from about 1,000 recipients to "20,000 notifications per week"; previously, discrepancies triggered manual review of "about 20,000 such files a year".

**Mechanism (Overview).**
1. DHS obtained the ATO's record of what employers reported as the recipient's income for the financial year ("PAYG data").
2. An automated system compared it with the recipient's declarations and asked for an online explanation of any discrepancy.
3. If the recipient did not respond, did not explain the discrepancy, or agreed with the PAYG figure, "the amount declared by the employer would be divided up evenly, and allocated into the number of fortnights included in the period being reviewed" (called "averaging", "smoothing" or "apportioning"). The period was "often whatever employment period the employer had indicated", often the whole financial year.
4. Where, in any fortnight, the averaged amount exceeded the income a recipient could earn before the benefit was reduced, an overpayment was taken to exist, a debt was raised, and recovery began.

As at 27 January 2017, "76 per cent of those who were subject to the OCI had debts raised based on averaging of their earnings: 99,404 recipients" (DHS figures quoted by the report).

**Legal premise.** Section 1068-G7A of the Social Security Act 1991 takes ordinary income into account "in the fortnight in which it is first earned, derived or received". The report: "What cannot be done is to take income over a period of time and divide it into equal fortnightly amounts in the absence of information that it was actually received in that way".

**Onus and non-response.** Recipients received "a gross income figure with a period which might or might not accurately reflect the period worked, with the onus placed on them to provide details to contradict it". They had to establish earnings "for periods going back as long as five years", though DHS advised keeping payslips for six months. For former recipients contacted at old addresses or myGov accounts, "Their inevitable failure to respond resulted in income averaging being applied"; in the 2015 pilots "only about 40 per cent of customers were making contact".

**The 10% fee.** Section 1228B allows a 10% penalty where the debt arose from a failure to provide earnings information or from knowingly or recklessly false information. The report found "no evidence that any thought was given" to those grounds for the "euphemistically called" recovery fee.

**Legal advice and courts (Overview, unless noted).**
- **2014.** DSS's in-house lawyers raised concern that averaging might not be consistent with the legislation. The New Policy Proposal said "falsely, that the new approach would not change how income was assessed".
- **August 2018.** A Clayton Utz draft advice said averaging was not permissible. It "was never put into final form or acted on".
- **AAT.** First-tier decisions set debts aside: "averaging, of itself, could not provide evidence of actual income".
- **September 2019.** The Solicitor-General advised that averaged PAYG data could not support a debt without further evidence. That led to *Amato v Commonwealth* (VID611/2019, Davies J, consent orders 27 November 2019), with a declaration "that averaged PAYG income information was not capable of satisfying a decision-maker of the existence of a debt".
  - Per Victoria Legal Aid's summary of the annexed notes, the assumption of equal fortnightly earnings had no probative support and was contradicted by declared income, so "the conclusion was irrational"; the 10% penalty and the tax-refund garnishee also fell.
- **19 November 2019.** The government stopped raising debts solely on PAYG data. A class action began the same day.
- **May 2020.** The Solicitor-General advised that the government "was bound to fail" on unjust enrichment. The class action settled in November 2020, on the day set for trial.
- ***Prygodicz v Commonwealth (No 2)* [2021] FCA 634** (Murphy J, 11 June 2021) approved the settlement. Both the Royal Commission and Maurice Blackburn quote [5]: "a shameful chapter in the administration of the Commonwealth social security system and a massive failure of public administration". Per Maurice Blackburn and Gordon Legal, the terms included \$112 million of compensation, "in the nature of interest" (Gordon Legal), and \$8.4 million in approved legal costs (Maurice Blackburn).

**Royal Commission.** The report was presented on 7 July 2023 by Commissioner Catherine Holmes AC SC; a corrected edition was published on 11 July 2023. It lists 57 recommendations and has a sealed chapter of referrals. Findings include:
- "Robodebt was a crude and cruel mechanism, neither fair nor legal, and it made many people feel like criminals";
- averaging was used in a way that was "essentially unfair, treating many people as though they had received income at a time when they had not";
- "fraud in the welfare system was miniscule" (as spelled in the report).

Its timeline graphic says "November 2019 Federal Court declares income averaging unlawful"; the declaration itself, quoted above, is narrower.

**Scale and remediation (each figure with its source):**

| Source | Figures |
|---|---|
| Royal Commission (budget design) | "866,857 instances of possible overpayment" for 2010–11 to 2012–13; the package "was expected to save \$1.7 billion over five years" |
| Royal Commission (2020 remediation) | "\$746 million to some 381,000 affected individuals"; debts written off "\$1.751 billion" |
| Letters Patent recital | "over 400,000 debts" zeroed or repaid |
| Maurice Blackburn | debts "totalling at least \$1.7 billion against approximately 400,000"; \$707.9 million already refunded at approval; about \$751 million promised |
| Gordon Legal | about \$1.763 billion cancelled, including \$751 million repaid |
| Whiteford 2021 abstract | "more than \$1000 million to more than 400,000 people" |

**Scholarship.**
- **Carney 2019** (abstract): accountability failed at "seven different levels". His 2018 blog post argues that Centrelink bears the onus of proving a debt (*McDonald*; *Briginshaw*) and that an average "can only ever be correct if the person concerned had only one job and their rate of pay never varied".
- **Whiteford 2021** (abstract): a foreseeable "policy fiasco" that "differs ... in that it was intentional".

### 2. Toy model: averaged versus fortnightly entitlement

Basis: execution (toy model of a two-band income test, not the agency system) + normative parameters (DSS Social Security Guide) + derived arithmetic.

**Parameters.** These are official values, used only to make the illustration concrete:
- Newstart Allowance, single, aged 22 or over: \$264.35 per week from 20/09/2016 (SSG 5.2.1.20, Table 5, basic rate excluding the Energy Supplement). Doubled to \$528.70 per fortnight; the doubling is this report's arithmetic.
- Income free area \$104 per fortnight and threshold \$254 per fortnight from 1/7/2016 (SSG 4.10.2). Taper 50% between them and 60% above; the tapers have been unchanged since 2006.
- The probe applies the 60% only to income above the threshold. This follows the Guide's "60c in the dollar for income above \$250.00 pf" wording, but was not checked against a DSS worked example.

```text
entitlement(i) = max(0, 528.70 - 0.5*max(0, min(i,254)-104) - 0.6*max(0, i-254))
debt(method)   = sum over benefit fortnights f of max(0, paid_f - entitlement(income_method_f))
```

**Worked example.**
- The synthetic person works fortnights 0–9 at \$1,800 per fortnight while off payment, then receives payment in fortnights 10–25 with no income.
- The employer reports \$18,000 for the whole year, so the average is \$692.31 per fortnight.
- Entitlement at the unrounded average 692.3077 = 528.70 − (75 + 0.6 × 438.3077) = 190.7154, so the overpayment is 337.9846 per fortnight × 16 = **\$5,407.75**, or \$5,948.53 with the 10% fee.
- The actual-income debt is **\$0**.

**Synthetic cohort.**
- 2,000 irregular earners (seed 20261121) with 1–3 employment spells; the employer-reported period is the true span for half and the whole year for half; 30% under-report part-time income while on payment, so some actual debts are genuinely positive.

Results:

| Measure | Value |
|---|---|
| People with a positive averaged debt | 1,515 |
| False debts (averaged > 0, actual = 0) | 1,242 |
| Overstated (averaged > actual) | 1,470 |
| Understated (averaged < actual) | 81 |
| Sum of averaged debts / sum of actual debts | \$3,650,884.38 / \$162,313.35 |

Derived reading: averaging moves earnings from non-benefit fortnights into benefit fortnights, so it manufactures debts for people who stopped work before claiming. It can also *understate* a genuine debt, by spreading under-reported benefit-period earnings into non-benefit fortnights. The magnitudes depend entirely on the synthetic assumptions and are not estimates of the real scheme.

### 3. Michigan MiDAS: automated fraud adjudication and its review

Basis: documentation (*Cahoo v. SAS Analytics Inc.*, 912 F.3d 887, 6th Cir. Jan. 3, 2019; *Cahoo v. SAS Institute*, 6th Cir. June 15, 2023; *Bauserman v. Unemployment Insurance Agency*, Mich. No. 160813, July 26, 2022; Michigan Attorney General releases). Case facts are pleading-stage allegations.

**Decision logic, as described in *Cahoo*.**
- From October 2013 MiDAS searched current and six-year-old claim records for discrepancies; flagged claimants were not told why.
- MiDAS sent a multiple-choice questionnaire with a ten-day deadline. It began "Did you intentionally provide false information to obtain benefits you were not entitle[d] to receive?"
- "If a claimant answered any of the questions in the affirmative, or failed to respond to the questionnaire in ten calendar days, 'MiDAS robo-adjudicated the fraud issue and automatically determined that the claimant knowingly and intentionally misrepresented or concealed information'". "From October 2013 to August 2015, MiDAS exclusively determined whether claimants engaged in fraud—no human being took part in this process."

**Notice.** Questionnaires went to online accounts, many of them dormant. MiDAS took no other step ("emails, regular mail, or making phone calls"). Determinations did not state the factual basis.

**Penalties and collection.**
- Restitution plus "a penalty ... equal to four-times the amount of unemployment benefits received (or sought)", even where no benefits were received. Penalties were often \$10,000–\$50,000 and some exceeded \$187,000.
- Wage garnishment and tax-refund interception "without holding a hearing".

**The 93% figure, attributed differently:**

| Opinion | Wording | Attributed to |
|---|---|---|
| *Cahoo* 2019 | "reviewed over 22,000 of MiDAS' fraud determinations and found that 93% of them did not actually involve fraud" | the Michigan Auditor General (complaint allegation; footnote 8 notes inconsistent dates) |
| *Bauserman* 2022, fn. 5 | "approximately 93% of the automated system's fraud determinations were incorrect" | "a study conducted by the Agency", citing The Guardian (2016) |

*Bauserman* fn. 5 also cites an estimate of "approximately 40,000 people" wrongfully accused between 2013 and 2015 (Time, 2020). Neither court cites the primary review.

**Holdings.**
- ***Cahoo* 2019** (Keith, Clay and Nalbandian, JJ.) affirmed the denial of qualified immunity to the individual Agency defendants on the procedural due-process claim, and reversed it on the equal-protection and Fourth Amendment claims. SAS was not a party to the appeal.
- ***Cahoo* 2023**, after class certification was denied and with four plaintiffs remaining, reversed the denial of qualified immunity for two supervisors.
- ***Bauserman* 2022** (Cavanagh, J., for the majority): "we now hold that [monetary damages] are" available for violations of the Michigan Constitution, here due process under art. 1, § 17, "unless the Constitution has specifically delegated enforcement ... to the Legislature or the Legislature has enacted an adequate remedy". This applies whether or not the harm followed an official policy.

**Settlement.**
- The Attorney General announced a \$20 million settlement on 2022-10-20.
- The Court of Claims gave preliminary approval by order of January 19, 2023, for claimants with an auto-adjudicated intentional-misrepresentation determination between October 1, 2013 and August 31, 2015 and a first collection on or after March 9, 2015.
- The Court of Claims granted final approval on 2024-01-29 (release of 2024-01-30).

### 4. SyRI: District Court of The Hague, 5 February 2020

Basis: normative (judgment, ECLI:NL:RBDHA:2020:1878, the official English translation of ECLI:NL:RBDHA:2020:865) + documentation (van Bekkum & Zuiderveen Borgesius 2021).

**System design, as recorded by the court.**
- **Legal basis.** Section 65 of the SUWI Act, read with Section 64 and Chapter 5a of the SUWI Decree, in force from 1 January 2014.
- **Data.** Seventeen linkable categories (4.17), from work, tax, property and housing to identity, civic integration, debt, benefits and health insurance. The court: "it is hard to imagine any type of personal data that is not eligible for processing in SyRI" (6.98).
- **Scoring (6.89, the State's account).** The model consists of "i) risk indicators, ii) links and iii) a so-named cut-off point". Points are awarded per indicator, more for less probable indicators. A score below the predetermined threshold "will not result in a potential hit". Only one validated model existed, the neighbourhood-oriented approach (4.24).
- **Two phases (4.29–4.30).** The Inlichtingenbureau pseudonymises and matches the records automatically to produce potential hits. These are decrypted and assessed by the Inspectorate's analysis unit, and the Minister then issues risk reports.
- **Retention.** Unreported data are destroyed within four weeks. A risk report is held for two years and usable for 20 months.
- **Methods.** The legislation left "predictive analyses, 'deep learning' and data mining" open (6.51).

**Test.** Article 8(2) ECHR requires "a fair balance" between community interest and individual right. The court accepted the aim of economic wellbeing (6.4), required weighing "in a transparent and verifiable manner" (6.6), and read in the GDPR principles of transparency, purpose limitation and data minimisation (6.7).

**Findings (6.86–6.95).**
- The legislation is "insufficiently transparent and verifiable to conclude that the interference ... is necessary, proportional and proportionate" (6.86).
- It discloses neither "which objective factual data can justifiably lead to the conclusion that there is an increased risk" (6.87) nor "the type of algorithms used in the model", the method, validation or indicators (6.89), so data subjects cannot defend themselves (6.90).
- Transparency is "compelling" because of the risk of "discriminatory effects – unintentional or otherwise" (6.91). Given the volume of data and the use of risk profiles, "there is in fact a risk that SyRI inadvertently creates links based on bias, such as a lower socio-economic status or an immigration background" (6.93). A human check for false positives and false negatives "is deemed insufficient" (6.94).
- There are "insufficient safeguards" (6.95); purpose limitation and data minimisation also got insufficient attention (6.96–6.99).

**Left open.**
- File linkage is profiling under GDPR Article 4(4), but the court "does not give an opinion" on automated individual decision-making under Article 22 (6.56, 6.60).
- It did not assess specific GDPR provisions or ECHR Articles 6 and 13 (6.107).
- Section 64, viewed separately, is not contrary to Article 8(2) (6.110).

**Operative ruling (7.2).** Section 65 SUWI Act and Chapter 5a SUWI Decree "have no binding effect" with respect to the admitted claimants and those they represent, "for being contrary to Article 8 paragraph 2 ECHR". The claims of three other claimants were inadmissible (7.1), and costs were set at €3,250.51 (7.3).

**Commentary.** Van Bekkum and Zuiderveen Borgesius (EJSS 23(4):323–340) call the immediate effects "limited": "a court might approve a similar system if the government ensures greater transparency". Three components were secret: the risk model, the comparison algorithm and the hit-linking method. Only five SyRI projects appear to have run, and the government did not appeal.

### 5. Dutch childcare benefits: nationality in a self-learning risk model

Basis: documentation (official reports; NGO publication).

**Dutch DPA (Autoriteit Persoonsgegevens), report z2018-22445, 17 July 2020.** English renderings are this report's translations.
- **Model.** The tax administration has used a risk-classification model "sinds 2013". It is a "zelflerend model" (self-learning model) trained on correct and incorrect applications, with "enkele tientallen indicatoren" (a few dozen indicators) and a score between 0 and 1. Its output takes the form of scorecards.
- **Review.** The 100 highest-scoring applications go to staff for manual checks; in principle every application scoring above 0.8 is checked. Staff do not know why a case was selected ("De behandelend medewerker weet niet waarom het systeem een casus selecteert").
- **Nationality indicator.** "Nederlanderschap/niet-Nederlanderschap" (Dutch / non-Dutch nationality) was an indicator "in ieder geval vanaf maart 2016" (at least from March 2016) "tot oktober 2018" (until October 2018). The Belastingdienst said it had been used since 2013. Dual nationality was not itself an indicator.
- **Holdings.** Three processing operations were unlawful: retaining dual nationality, the model indicator, and use for detecting organised fraud. Two were "discriminerend en daarmee onbehoorlijk" (discriminatory and therefore improper): the model indicator and the organised-fraud use.

***Ongekend onrecht*** (Parliamentary Inquiry Committee, 17 December 2020): "basic principles of the rule of law were breached" by the administration, the legislator and the judiciary, citing the "all or nothing" approach and the absence of a hardship clause. Nationality in risk profiles was outside its remit; it cites the DPA's finding. Per a state secretary, as reported by the committee, 25,000 to 35,000 people were deemed guilty of malice or gross negligence between 2012 and 2019, and a random check found the designation unjustified in 94% of cases.

**Amnesty International, *Xenophobic Machines*** (EUR 35/4686/2021, 25 October 2021). Only the document page and press release were read. They state that non-Dutch nationals "received higher risk-scores", that "a self-learning mechanism" reproduced the bias "with no meaningful human oversight", and that reviewers were "given no information as to why" a case scored high.

### 6. Rotterdam welfare-fraud risk model and the Lighthouse Reports audit

Basis: source (`Lighthouse-Reports/suspicion_machine` at `3afc105b04ff3dcdcacbfa5ab39d9cc089264845`, which includes Rotterdam's released training code) + documentation (the Lighthouse methodology and the WIRED article) + execution (recomputation from published summary statistics).

**Deployment, as reported by Lighthouse.**
- From 2017 the city referred the top-scoring 10% of recipients (on average about 1,000) for investigation; the model was built with Accenture. The analysed model "was deployed in the years 2020 and 2021"; the system was put "on-hold" in 2021.
- Rotterdam's own evaluation found it "only 50 percent more accurate ... than selecting people at random".

**Model and training (repository).**
- The README describes a GBM "trained on a dataset of 12,707 past investigations" with 315 features and a score in [0, 1]. WIRED describes the same 12,707 as people. The methodology reports 500 trees, each of up to nine questions.
- `Source Code/16.Modelleren/train_model_finale.R` loads `gbm`/`caret` and keeps `filter(methode == "gbm")`; `Source Code/10.Functies/modelleren.R` trains with `train(target_per~., method = modellen$methode[i], ...)` and records `varImp(result, scale = T)`.
- In `data/06_feature_information/features.csv` (315 rows), age (`persoon_leeftijd_bij_onderzoek`) has relative importance 100.0 and the next feature 35.49 (ratio 2.82, derived). 63 features have importance 0.
- The trained model `data/01_raw/20220929_finale_model.rds` (14,987,547 bytes) is in the repository.

**Label (`Source Code/14.ABT/ref_basis.r`, lines 33–53).** The file's comment defines unlawfulness ("onrechtmatigheid") as a non-empty `Bedrag` (amount) or a `Gevolgen` (consequence) of ending ("Beëindiging") or adjusting ("Aanpassing") the running benefit ("lopende uitkering"):

```r
target_ond = case_when(!is.na(fraude_bedrag) ~ "Ja",
                       grepl("lopende uitkering", gevolgen) ~ "Ja",
                       TRUE ~ "Nee")) %>%
group_by(persoon_id) %>%
mutate(target_per = case_when(sum(target_ond == "Ja") > 0 ~ "Ja", TRUE ~ "Nee"))
```

So the label is per person: any "Ja" investigation makes the person "Ja". Labelled investigations are first filtered to three office locations (comment "Selectie Prestatie010"). Lighthouse notes that the label covers "both deliberate and indeliberate violation". The fraud share is "around 50 percent" in training data, against "around 21 percent" in a random sample.

**Audit design (repository).**
- `notebooks/analyze.R` scores each experiment dataset and calls `pairwise_t_test(Ja~IV)` (rstatix) with no `paired` argument.
- It computes the share above a "high-risk" threshold: `td_real_threshold <- 0.6970136` (top decile of real training scores), `td_synth_threshold <- 0.7125668` and `rw_threshold <- 0.5912492` (a normal approximation from the mean and SD that Rotterdam supplied). It also computes score deciles with `ntile`.
- `notebooks/data_generator.ipynb` makes "conditional" data as full copies of the dataset with the focus feature set to each value (`concat_combinations`), dropping combinations that violate business rules.
- Synthetic data come from a Gaussian copula ("Quality Score of 85.58 percent"). The real rows were accidentally disclosed in histogram HTML, without labels.

**Derived observation (not stated by the authors).** Each conditional copy contains the same people, so the groups are paired by construction, yet the test call is unpaired. The methodology text says "paired Student T-Tests". The recomputation below is consistent with the unpaired formula. A paired test on per-person score differences was not computed.

**Reported findings (Lighthouse and WIRED; training data unless noted).**
- Flag-rate ratios: women versus men 1.25 (men 0.90, women 1.13 of base rate); parents "almost 1.7"; poor Dutch "nearly 2.22"; failed language requirement "almost twice"; a "mothers with financial difficulties" archetype "almost three times" the lowest-risk archetype.
- Age alone moves average scores "from 0.45 to 0.559". 54 variables (17%) are subjective caseworker assessments.
- Rotterdam "acknowledged the validity of the overall findings of bias" and concluded "that the Dutch language variables were an unacceptable proxy for migrant background".

**Recomputation probe** (execution on published statistics; the model was not run). `support/parity_recompute.py` reads `results/statistical_parity/single_feature/sf_persoon_geslacht_vrouw/{sum_stats.csv,t_test.csv}` and recomputes a pooled two-sample t-test. Means are published to 3 decimals, so it reports the p-range for ±0.0005 rounding:

| Data | n (men / women) | mean | share above threshold | recomputed p range | published p |
|---|---|---|---|---|---|
| real | 7,310 / 5,335 | 0.485 / 0.495 | 0.0906 / 0.1130 | 6.79e-05 – 0.00112 | 0.000156 |
| real, conditional | 12,645 / 12,645 | 0.483 / 0.502 | 0.0905 / 0.1136 | 1.45e-25 – 5.07e-21 | 2.14e-24 |
| synthetic | 6,542 / 6,103 | 0.611 / 0.613 | 0.1013 / 0.0986 | 0.0475 – 0.509 | 0.0664 |
| synthetic, conditional | 12,508 / 12,508 | 0.609 / 0.615 | 0.0931 / 0.1102 | 7.52e-11 – 3.31e-06 | 1e-07 |

All four published p-values fall inside the recomputed ranges. Derived:
- 0.1130/0.0906 = 1.25, which matches the reported "1.25 times".
- In the synthetic data the simple gender disparity vanishes (p=0.0664; shares 0.1013 versus 0.0986), but the conditional test shows it. The Gaussian copula therefore did not preserve the joint structure that produces the simple disparity.
- The real-data rows total 12,645, not 12,707; the difference is not explained in the sources read.

### 7. Cross-system comparison

Basis: derived from sections 1–6.

| | Robodebt | MiDAS | SyRI | Childcare risk model | Rotterdam |
|---|---|---|---|---|---|
| Output | debt plus 10% fee | fraud finding, 4× penalty | risk report | manual-check selection | investigation referral |
| Core logic | annual income ÷ fortnights, then income test | non-response or "yes" ⇒ fraud | indicator points vs cutoff | self-learning scorecard | GBM score, top decile |
| Who bears the burden | recipient rebuts the average | claimant must respond in 10 days | subject cannot see indicators | applicant must supply evidence | recipient investigated |
| Human in loop | none on the default path | none from Oct 2013 to Aug 2015 (as alleged) | analysis unit after hits | reviewer, without reasons | investigator after selection |
| Review route | AAT, Federal Court, Royal Commission | 6th Cir. and Michigan courts | Article 8 ECHR claim | DPA, parliamentary inquiry | journalistic audit |

**Shared failure pattern (derived).** In each system a proxy was treated as the legally relevant fact: an average for actual fortnightly income, silence for intent, an indicator score for risk, nationality for inaccuracy, and a "Ja" label (which includes honest error) for fraud. Each system also moved the burden onto the person while withholding the basis for the decision.

### 8. Performance and resource footprint (L1–L6)

Basis: execution (host: x86-64 Linux VM, 96 logical CPUs; `python3`; probes run sequentially) + source (file sizes from the GitHub tree API at the pinned revision).

| Level | Measurement |
|---|---|
| L1 authoring | not measured |
| L2 toolchain build | not applicable (no build); R and `gbm` not installed, so not measured |
| L3 latency | not measured for the GBM. Averaging probe 0.09 s wall; parity recompute 0.21 s wall (includes reading the 12,645 × 315 synthetic CSV) |
| L4 execution | GBM scoring throughput not measured |
| L5 verification | not applicable |
| L6 footprint | averaging probe peak RSS 14,976 KB; parity recompute 60,940 KB. Repository files: model `.rds` 14,987,547 bytes; `synth_data.csv` 8,467,397 bytes; `GaussianCopula-generator.pkl` 1,076,032 bytes |

### 9. Comprehensibility, model refinement and validation (C1–C2, V1–V4)

**C1 (derived).** Each system was opaque to the affected person: Robodebt showed a gross annual figure, not the averaged fortnights behind the debt; MiDAS notices said "Your actions indicate you intentionally misled" without facts; SyRI's indicators were secret by design; childcare and Rotterdam reviewers saw scores without reasons.

A 315-feature, 500-tree GBM is not auditable per decision; probing it took counterfactual copies constrained by more than 130 inter-variable business rules.

**C2 (derived).** One invariant covers all five: an adverse determination must rest on disclosed evidence of the legally operative fact for that person and period. Averaging then needs evidence of equal fortnightly earnings (the Solicitor-General's 2019 position), non-response is not an admission, and risk scores trigger inquiry but are not findings.

**V1.** Specification adequacy was the core failure. In April 2017 the Ombudsman reported that Robodebt's business rules "accurately capture[d] the legislative and policy requirements"; per the Commission, DSS had not supplied its 2014 advice. Conformance to encoded rules cannot catch a premise that contradicts the statute; a one-line differential test of averaged against fortnightly entitlement (section 2) does.

**V2–V3.** Not applicable: there is no compiler or concurrency layer.

**V4 (empirical validation).** The 93% MiDAS and 94% childcare re-review figures are, in effect, post-hoc validation by human re-adjudication. Lighthouse's parity tests validate the Rotterdam model's outputs; Rotterdam's own ROC curve was read as "essentially random guessing" by an external expert quoted by Lighthouse.

## Boundaries

**Not examined:**
- primary text of the *Amato* orders and of *Prygodicz (No 2)* (court sites refused automated access);
- Royal Commission chapters after Chapter 7, including the full income-averaging, legal-advice and automated-decision chapters; whether the copy read is the 7 or the 11 July edition;
- the bodies of Carney 2019 and Whiteford 2021 (abstracts only), and the full Amnesty report;
- the primary Michigan audit or Agency study behind the 93% figure, including its denominator;
- the Dutch-language SyRI original; the DPA's €2.75 million fine decision; the full Dutch *Ongekend onrecht*;
- running Rotterdam's model (no R runtime), the decision trees, and the archetype results;
- paired versus unpaired p-values on the conditional copies.

**Unknown:**
- The total number of Robodebt debts, and of distinct people, over the scheme's life: no Royal Commission figure was read.
- The remediation figures conflict across sources (section 1 table); none is reconciled here.
- Whether the Rotterdam Court of Audit (Lighthouse) or the Netherlands Court of Audit (WIRED) issued the Dutch-language warning.
- Which judges wrote the *Bauserman* concurrence and second dissent, and the *Cahoo* 2023 partial dissent.
- Why the parity data contain 12,645 real rows rather than 12,707.

**Not verified:**
- the combined 2016–17 income-test parameter set, which was assembled from Guide rows and not checked against a DSS worked example;
- a later \$548.5 million appeal settlement reported by Gordon Legal, outside this report's scope.

**Known not to apply:**
- The toy averaging probe does not reproduce the agency's system: it omits the Energy Supplement, partner income, other payments and the real employment-period data.
- The *Cahoo* and *Bauserman* facts are allegations, not trial findings.

**Stronger conclusions not established:**
- That averaging is unlawful per se. The Commission says it "is not, per se, unlawful"; the defect is using it without evidence of the earnings pattern.
- That the 93% MiDAS figure has a single authoritative source.
- That Rotterdam's model was less accurate than random selection. The reported figure is "50 percent more accurate" than random.
- That the synthetic-data results stand in for the real data. The simple gender test differs between the two.

## Evidence

Evidence was acquired on 2026-11-21. Crossref `/works/<DOI>` records were checked for all three DOIs.

**Australia:**
- Royal Commission report, ISBN 978-1-921241-58-1. Landing page: https://robodebt.royalcommission.gov.au/publications/report. Read via the Monash University mirror: https://www.monash.edu/__data/assets/pdf_file/0007/3365503/report_of-the-royal-commission-into-the-robodebt-scheme.pdf
- Victoria Legal Aid: https://www.legalaid.vic.gov.au/depth-look-our-robo-debt-test-case
- Maurice Blackburn: https://www.mauriceblackburn.com.au/blog/class-actions/robodebt-class-action-settlement-approved/
- Gordon Legal: https://gordonlegal.com.au/robodebt-class-action/
- Carney's blog post: http://www.austaxpolicy.com/social-security-robo-debt/
- DSS Social Security Guide: https://guides.dss.gov.au/social-security-guide/5/2/1/20 and https://guides.dss.gov.au/social-security-guide/4/10/2
- Carney, "Robo-debt illegality: The seven veils of failed guarantees of the rule of law?", Alternative Law Journal 44(1):4–10, DOI 10.1177/1037969X18815913 (online 2018-12-17).
- Whiteford, "Debt by design ...", AJPA 80(2):340–360, DOI 10.1111/1467-8500.12479.

**Michigan:**
- *Cahoo* 2019: https://caselaw.findlaw.com/court/us-6th-circuit/1973889.html. The "912 F.3d 887" reporter citation comes from later opinions; it is not printed on that page.
- *Cahoo* 2023: https://caselaw.findlaw.com/court/us-6th-circuit/2285148.html
- *Bauserman* 2022: https://caselaw.findlaw.com/court/mi-supreme-court/2181105.html
- Attorney General releases of 2022-10-20, 2023-01-23 and 2024-01-30, under https://www.michigan.gov/ag/news/press-releases/

**Netherlands:**
- SyRI: https://data.rechtspraak.nl/uitspraken/content?id=ECLI:NL:RBDHA:2020:1878 (case C-09-550982-HA ZA 18-388).
- DPA: https://www.autoriteitpersoonsgegevens.nl/uploads/imported/onderzoek_belastingdienst_kinderopvangtoeslag.pdf
- *Ongekend onrecht* (English): https://www.houseofrepresentatives.nl/sites/default/files/atoms/files/verslag_pok_definitief-en-gb.docx.pdf
- Amnesty: https://www.amnesty.org/en/documents/eur35/4686/2021/en/
- van Bekkum & Zuiderveen Borgesius, EJSS 23(4):323–340, DOI 10.1177/13882627211031257. Read via https://repository.ubn.ru.nl/bitstream/handle/2066/245674/245674.pdf

**Rotterdam:**
- Repository `Lighthouse-Reports/suspicion_machine` at `3afc105b04ff3dcdcacbfa5ab39d9cc089264845`. Files: `README.md`; `Source Code/14.ABT/ref_basis.r` lines 33–53; `Source Code/16.Modelleren/train_model_finale.R`; `Source Code/10.Functies/modelleren.R` lines 19–31; `notebooks/analyze.R` lines 185–212 and 332–334; `notebooks/data_generator.ipynb` (`slice_data`, `concat_combinations`, `data_generator`); `data/06_feature_information/features.csv`.
- Lighthouse methodology: https://www.lighthousereports.com/methodology/suspicion-machine/
- WIRED "Inside the Suspicion Machine", read via https://pulitzercenter.org/stories/inside-suspicion-machine

**Execution** (copies in `support/`; the two upstream CSVs are in `support/suspicion_machine_inputs/`):

```text
python3 support/averaging_probe.py 528.70 104 254 0.5 0.6 > averaging_probe.out.json  # parameters as recorded in the output
python3 support/parity_recompute.py sum_stats.csv t_test.csv synth_data.csv > parity_recompute.out.json
```

`synth_data.csv` is `data/01_raw/synth_data.csv` at the pinned revision. The `*.time` files record wall time and peak RSS.

## Revalidation

- **Averaging.** Rerun the probe with the same arguments and diff against `support/averaging_probe.out.json`. For other periods, substitute rates from SSG 5.2.1.20 and 4.10.2. The worked example's \$0 actual debt holds whenever earnings fall only in non-benefit fortnights.
- **Rotterdam.** Check that `ref_basis.r` lines 46–53 and `analyze.R` line 212 are unchanged at a newer revision. Rerun `parity_recompute.py` on any `results/statistical_parity/*/` folder. To settle the paired-test question, run `analyze.R` with R, `gbm`, `caret` and `rstatix` on the conditional data, using a paired test on per-person differences.
- **Legal status.** Look for later proceedings, such as appeals, a successor to SyRI, or further *Cahoo* or *Bauserman* orders. These require rereading the court records; no cheap probe exists.
