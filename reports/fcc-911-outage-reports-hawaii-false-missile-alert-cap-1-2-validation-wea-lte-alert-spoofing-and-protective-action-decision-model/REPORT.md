# Public-warning and emergency-call software failures: FCC investigations of the 2014 multistate 911 routing outage and the 2018 Hawaii false missile alert, a state regulator's account of the December 2018 carrier outage, CAP 1.2 and the archived Google CAP validator, LTE alert spoofing, and warning-response research

## Summary

- **April 2014 multistate 911 outage (FCC Public Safety and Homeland Security Bureau report):**
  - **Cause.** A call-routing hub in Englewood, Colorado stopped assigning trunks to call centres reached over legacy CAMA trunks. Its software kept a counter of sequential log record numbers with a "pre-set maximum", and at 11:54 p.m. PDT on 9 April 2014 the counter reached that maximum.
  - **Impact.** 81 call centres (Public Safety Answering Points, PSAPs) in seven states lost 911 service for up to six hours. The affected population was more than 11 million people, and over 6,600 calls never reached a PSAP.
  - **Detection.** The fault raised no major alarm, only thousands of minor alarms that were grouped into a summary. Staff identified it at about 6:00 a.m. and failed over manually to the Miami site.
  - **Fixes.** The operator raised the counter limit and added weekly checks of it, an alarm keyed to the 15-minute call-success percentage, and per-call automatic rerouting.

  `Basis: documentation (regulator report)`
- **January 2018 Hawaii false ballistic-missile alert (FCC preliminary report, 30 January 2018):**
  - **Trigger.** A no-notice drill was run with a recording that contained both "EXERCISE, EXERCISE, EXERCISE" and the live-alert text "THIS IS NOT A DRILL".
  - **Send.** At 08:07 the warning officer chose the *live* template from a drop-down menu and clicked "yes" at the prompt "Are you sure that you want to send this Alert?".
  - **Correction.** Retransmission was cancelled at 08:12. A correcting message (a Civil Emergency Message, CEM) went out over the Emergency Alert System (EAS) and Wireless Emergency Alerts (WEA) only at 08:45. The preliminary finding attributes the 38-minute delay "largely" to a lack of preparation for responding to a false alert.

  The final report of 10 April 2018 was **not examined** (the document could not be fetched). `Basis: documentation (regulator presentation)`
- **December 2018 carrier outage.** The FCC report of 19 August 2019 was **not examined**. Washington regulator staff called the outage "a preventable technical error" in which the carrier "incorrectly configured network devices and did not build safeguards into their traffic routing infrastructure". Washington residents lost 911 for almost 50 hours. Staff estimated up to 24,000 affected calls from a 12,000-calls-per-day average, because the carrier did not supply complete failed-call data. `Basis: documentation (state regulator staff release)`
- **The Common Alerting Protocol (CAP 1.2) defines updates and cancellations by reference to earlier messages, yet makes `<references>` optional.** Whether a message has been validly cancelled therefore rests on profile rules and system state, not on the schema. Other CAP 1.2 rules relevant to validation: `<addresses>` is required when scope is `Private`; timestamps must not use the `Z` designator; a null `<language>` "SHALL be considered equivalent to 'en-US'"; and the only authentication mechanism is an optional enveloped XML signature, which processors must not reject merely because they cannot verify it. `Basis: normative`
- **A 29-case conformance probe found gaps in the archived Google CAP library (pinned revision, run under Java 8):**
  - The core validator accepts a `Private` alert with no `<addresses>` and a `Restricted` alert with no `<restriction>`.
  - It also accepts `<expires>` earlier than `<effective>`, and alerts whose `<status>` contradicts their text.
  - Update/Cancel messages without `<references>` are caught only by the IPAWS and Google profiles.
  - A whitespace-only `<language>` makes the core validator throw `IllegalStateException: No match found` instead of returning reasons.
  - Text repeated under `en-US` and `en-GB` is flagged as "same text, different language", contrary to the source comment's stated intent (primary-subtag comparison).

  `Basis: execution + source`
- **Cell-broadcast alerts in LTE are carried in System Information Block 12 (SIB12) without encryption or authentication** (Lee et al. 2019; demo abstract):
  - **Idle phones.** A phone camps on the strongest-signal base station and can receive the alert before authentication fails. The failing attach attempts last about 42 seconds.
  - **Active phones.** They are first forced into radio-link failure by overpowering their serving cell.
  - **Reach.** The full paper's abstract reports that four portable 1-W base stations reach almost all of a 50,000-seat stadium at a 90 % success rate.
  - **Standards.** 3GPP's study report TR 33.969 analyses signature-based protection of the Public Warning System. One finding is that ETWS primary notifications over GERAN leave at most 75 bytes for a signature and its parameters.

  `Basis: documentation`
- **Warning-response research and the measured response to the false alert:**
  - **Model.** The Protective Action Decision Model (PADM) puts reception, attention and comprehension before three core perceptions: threat, protective action and stakeholder.
  - **Short-message guidance.** It derives from the five content elements of Mileti and Sorensen (source, hazard, location, guidance, time). For 90-character WEAs the recommended order is source, guidance, hazard, location, time.
  - **Measured response.** Across 1.2 million tweets from 14,830 users, anxiety expressed on Twitter rose 4.6 % on the day of the false alert, rose 3.4 % every 15 minutes during the 38-minute alert, and stayed elevated for at least 7 days.

  `Basis: documentation (peer-reviewed full text and abstracts as stated)`

## Applicability

**Subjects and how they relate:**
- Three incident accounts, each a different failure class: a capacity limit in call routing, a human-machine interaction failure in alert origination, and network misconfiguration. Two come from the national regulator; the third, for the carrier outage, is a state regulator's staff release, used because the national report could not be retrieved.
- One normative format, OASIS CAP 1.2, and one open implementation of it: `google/cap-library` at the pinned revision. GitHub marks the repository archived; its last push was 23 September 2019.
- One attack line of work on the delivery channel (LTE cell broadcast), plus the 3GPP study of countermeasures and one 2026 preprint that reproduces spoofing on 5G with an open-source radio stack.
- One line of social-science work on how recipients act on warnings.

The CAP probe treats the library as an implementation of CAP 1.2 and checks it against the standard's text. The other subjects are compared only at the level of failure mode and recommendation.

**Exact observations versus extensions:**
- Execution results apply to the pinned library compiled from its `java/src` tree with the repository's bundled jars (`java/lib/*.jar`), under OpenJDK 1.8.0_432. The image was `docker.io/library/eclipse-temurin:8u432-b06-jdk`, digest `sha256:ec78c5f94688094e54ca45d91e7fa412ceb0e077bce2fde17fe0b158745abf6f`, run with networking disabled.
- The probe uses the library's default parser mode: extended XSD plus `CapValidator`. It then applies the `Ipaws1Profile` and `GoogleProfile` classes.
- The validator *web application* (`validator/src/...`) was read but not run. The hosted validator site was not contacted.
- Deployed alert-origination software, such as the system used by the Hawaii agency, was **not examined**. Nothing here says which validators such systems use.
- Spoofing results are those reported by the authors on their own hardware. This report did not reproduce them.

## Findings

### 1. Regulator investigations: cause, detection, failover, notification

| Aspect | April 2014 multistate 911 outage | 13 January 2018 Hawaii false alert | December 2018 carrier outage |
|---|---|---|---|
| Source examined | FCC PSHSB report (PS Docket 14-72), full text | FCC PSHSB preliminary report (30 Jan 2018), full text; final report not examined | Washington UTC staff release (Docket UT-181051, 22 Dec 2020); FCC report not examined |
| Failing component | PSAP Trunk Member (PTM) module of the IP selective router at the Englewood Emergency Call Management Center | Alert-origination terminal and operating procedure at the state emergency management agency | Carrier network devices and traffic-routing infrastructure |
| Software / configuration cause | PTM assigns each CAMA-trunk call a sequential log record number. "Intrado programmed it with a pre-set maximum"; at the maximum it "ceased generating additional CAMA trunk assignments", interfacing timers timed out, and calls "went nowhere" (§3.2). The report does not state the maximum's value | Drill recording deviated from the standard script and contained live-alert language. The operator selected the live template from a drop-down and confirmed a generic "Are you sure" prompt | "incorrectly configured network devices and did not build safeguards into their traffic routing infrastructure" (staff view) |
| Scope | 81 PSAPs in 7 states; > 11 million people; up to 6 h; > 6,600 failed calls; > 87 % of calls during the outage were CAMA-bound | Statewide EAS and WEA | Nationwide; Washington residents without 911 for almost 50 h; FCC settlement release cites 39 states |
| Detection | No major or critical alarm. "Several thousand minor alarms"; a commenter reports 4,500 alarms "grouped together in a summary". Staff identified the problem at about 06:00 PDT; some PSAPs learned of it only when FCC staff contacted them | The officer received the WEA on a personal phone at 08:08; the Governor was notified 08:09; Pacific Command and police were told "no missile launch" at 08:10 | Staff found the carrier "did not provide complete failed-call data"; staff also alleged 15 violations for late PSAP notification |
| Failover / correction | Manual failover to the Miami IP selective router after identification | 08:12 cancellation stops retransmission; social-media notices 08:20; CEM chosen 08:27; supervisor logs in 08:31; correction issued 08:45 | not examined |
| Operator remediation reported | Raise PTM limit at both sites and check it weekly; alarm on "percentage of successful calls processed … over a 15-minute sample period"; automatic per-call reroute to the other site | Agency "has taken steps" (not detailed in the preliminary report) | not examined |

`Basis: documentation`

### 2. Recommendations classified by the failure mode they address

| Failure mode | Recommendation (source) | Software-design implication (derived) |
|---|---|---|
| Fixed-capacity counter exhaustion | Raise limit, check weekly (operator, 2014 report §3.4) | Monotone counters need an overflow policy (wrap, reset or alarm), or headroom monitoring tied to call-completion SLOs |
| Silent failure / alarm semantics | Alarm on call-success ratio over 15 minutes (operator, 2014 report); "Situational Awareness" for all parties end to end (Bureau, §5) | Alarm on service-level outcomes (calls completed), not only component health; prevent minor-alarm aggregation from masking outages |
| Concentration of critical function | Concern over consolidation into two locations "without adequate safeguards"; NG911 transition best practices via CSRIC (§3.2, §5) | Active-active routing with per-call failover rather than manual site failover |
| Contractual / accountability gaps | "Contractual Relationship Monitoring"; "Intergovernmental and Stakeholder Information Sharing"; enforcement (§5) | Outage notification paths across vendors as a tested interface |
| Live/drill mode confusion at alert origination | Preliminary findings: "human error and inadequate safeguards"; no-preparation delay (Jan 2018) | Separate live and test templates and environments; role-based or two-person confirmation for statewide high-consequence alerts; pre-built cancel/correct templates. These are inferences from the timeline; the final report's specific recommendations were not examined |
| Missing correction path | 38-minute correction delay attributed "largely" to lack of preparation | CAP `Cancel`/`Update` messages referencing the erroneous alert should be pre-authorised and one action away. CAP itself does not require `<references>` (§3) |
| Network misconfiguration without safeguards | Staff findings (Washington UTC) | Configuration validation and blast-radius limits in routing infrastructure; not examined further |

### 3. CAP 1.2: required fields, areas, updates and cancellations

All of the following is quoted or paraphrased from CAP 1.2 §3.2 at the URL in `REPORT.json`. `Basis: normative`
- **Required alert elements:** `identifier`, `sender`, `sent`, `status`, `msgType` and `scope`.
  - `status` ∈ {Actual, Exercise, System, Test, Draft}. "Exercise" is "Actionable only by designated exercise participants; exercise identifier SHOULD appear in `<note>`".
  - `msgType` ∈ {Alert, Update, Cancel, Ack, Error}. Update "Updates and supercedes the earlier message(s) identified in `<references>`"; Cancel "Cancels the earlier message(s) identified in `<references>`".
- **Conditional elements:**
  - `<restriction>`: "(CONDITIONAL) Used when `<scope>` value is 'Restricted'".
  - `<addresses>`: "(1) Required when `<scope>` is 'Private', optional when `<scope>` is 'Public' or 'Restricted'".
- **References.** `<references>` is "(OPTIONAL)". Each entry is the extended identifier "sender,identifier,sent", with multiple entries separated by whitespace.
- **Time.** Timestamps follow the DateTime pattern, for example `2002-05-24T16:49:00-07:00`. "Alphabetic timezone designators such as 'Z' MUST NOT be used. The timezone for UTC MUST be represented as '-00:00'". If `<effective>` is absent, it equals `<sent>`. If `<expires>` is absent, "each recipient is free to set its own policy".
- **Language.** `<language>` is an RFC 3066 identifier. "If not present, an implicit default value of 'en-US' SHALL be assumed. A null value in this element SHALL be considered equivalent to 'en-US'."
- **Areas.** An `<area>` is the union of its included elements. `<areaDesc>` is required.
  - `<polygon>`: "A minimum of 4 coordinate pairs MUST be present and the first and last pairs of coordinates MUST be the same" (WGS 84).
  - `<circle>`: a center pair plus a radius in kilometres.
  - `<geocode>`: valueName/value pairs.
  - `<ceiling>` is used only with `<altitude>`.
- **Short channels.** `<headline>`: "160 characters MAY be a useful target limit". `<responseType>` codes are Shelter, Evacuate, Prepare, Execute, Avoid, Monitor, Assess, AllClear and None. "Assess" "SHOULD NOT be used in public warning applications".
- **Security (§3.3.4).** "The `<alert>` element of a CAP Alert Message MAY have an Enveloped Signature … Other XML signature mechanisms MUST NOT be used". "Processors MUST NOT reject a CAP Alert Message containing such a signature simply because they are not capable of verifying it". Authentication is therefore optional and fail-open at the format level.

### 4. How the archived CAP library validates

The pipeline runs in four stages:
1. **Schema validation.** `CapXmlParser` chooses one of two schema maps (`CapXmlParser.java:60–65, 117–121`). The default is the *extended* XSDs, which add patterns to `identifier`, `sender`, `references`, `circle`, `altitude` and `ceiling`. The header of `schema/cap12_extended.xsd` notes: "No pattern restriction is added to polygon because it can cause a stack overflow in the regex parser for large polygons" (lines 14–15).
2. **Collection of XSD errors.** The SAX handler records XSD errors as reasons of type `OTHER` and keeps building the alert.
3. **Semantic checks.** Unless strict mode is selected, `new CapValidator().validateAlert(alert)` runs on whatever was built (`CapXmlParser.java:351–363`).
4. **Throwing.** With `validate = true`, the parser throws `CapException` if any reason has level ERROR (`:322–323`).

`Basis: source`

**Checks performed by `CapValidator` (`java/src/com/google/publicalerts/cap/CapValidator.java`, the core library):**

| Check | Lines | Level observed |
|---|---|---|
| `<restriction>` present but scope ≠ Restricted | 113–118 | ERROR |
| reference identifier equals own identifier (circular) | 156–158 | ERROR |
| referenced `sent` later than own `sent` (CAP ≥ 1.1) | 160–165 | WARNING |
| language not RFC 3066 | 179–187 | ERROR |
| same human-readable text under different language | 217–243 | WARNING |
| polygon first ≠ last point | 272–274 | ERROR |
| polygon self-intersection (naive O(n²) segment test, lat/lon treated as planar, no pole coverage) | 276–279, 425–497 | ERROR |
| ceiling without altitude; altitude > ceiling | 254–262 | ERROR |
| resource MIME type, URI absoluteness, base64 `derefUri` | 285–322 | ERROR |
| `<web>` absolute URI | 324–336 | ERROR |
| HTML entities or tags in any string | 393–423 | WARNING |

The profiles add policy rules. For example, both `Ipaws1Profile.java:111–115` and `GoogleProfile.java:102–106` require that Update and Cancel carry references. The IPAWS profile class at this revision contains no WEA/CMAS-specific text-length checks; a search for `CMAM` or `WEA` in the file finds nothing.

The validator *application* is a separate class, `validator/src/com/google/publicalerts/cap/validator/CapValidator.java`. It accepts pasted XML, feeds (RSS, Atom, EDXL-DE) or an http(s) URL, which it fetches server-side (`loadUrl`, lines 258–272), under a 20-second request budget (`REQUEST_DEADLINE_MS`, line 56). It catches `CapException` and `NotCapException` around `parseAlert`. **Derived:** a `RuntimeException` thrown inside the core validator, such as the one in §6, is not caught there. That path was not executed. `Basis: source`

### 5. Conformance probe: 29 messages

Each case differs from a minimal valid CAP 1.2 baseline in one respect (`support/cap_probe/make_cases.py`). "Core" is the library parser plus `CapValidator`. "Profiles" lists only reasons beyond those the baseline already receives: the baseline lacks the IPAWS version code, `<expires>`, `<web>` and an event code, so it gets profile errors for those. The run (`support/cap_probe/CapProbe.java`; output in `support/cap_probe/results/probe_out.txt`) took place on 2026-11-21.

| Case | Spec expectation | Core outcome | Profiles (additional) |
|---|---|---|---|
| c01 valid baseline | valid | accepted | — |
| c02 missing `identifier` | invalid | ERROR (XSD) | — |
| c03 `sent` without zone | invalid | ERROR (XSD ×2) | — |
| c04 `sent` with `Z` | invalid ("MUST NOT") | ERROR (XSD ×2) | — |
| c05 Update without references | valid in core; profiles may require | **accepted** | IPAWS and Google: ERROR `UPDATE_OR_CANCEL_MUST_REFERENCE` |
| c06 Cancel with references | valid | accepted | — |
| c07 Cancel referencing itself | inconsistent | ERROR `CIRCULAR_REFERENCE` | — |
| c08 reference sent after the update | inconsistent | WARNING `POSTDATED_REFERENCE` (accepted) | — |
| c09 restriction with Public scope | inconsistent | ERROR `RESTRICTION_SCOPE_MISMATCH` | — |
| c10 Restricted without restriction | conditional element missing | **accepted** | none |
| c11 Private without addresses | **invalid ("Required")** | **accepted** | none |
| c12 polygon not closed | invalid | ERROR `INVALID_POLYGON` | — |
| c13 polygon with 3 pairs (closed) | invalid (≥ 4 pairs) | ERROR `INVALID_POLYGON` | — |
| c14 bow-tie polygon | self-intersecting | ERROR `INVALID_POLYGON_SELF_INTERSECTION` | — |
| c15 small box across 180° | valid | accepted (no false positive) | — |
| c16 circle | valid | accepted | — |
| c17 ceiling without altitude | invalid | ERROR `INVALID_AREA` | — |
| c18 altitude > ceiling | inconsistent | ERROR `INVALID_ALTITUDE_CEILING_RANGE` | — |
| c19 `<language></language>` | null ⇒ en-US | accepted, no reasons | — |
| c20 `<language> </language>` | null ⇒ en-US (or schema-invalid) | **exception `IllegalStateException: No match found`** after two XSD reasons; no alert returned | not reached |
| c21 `english_US` | invalid | ERROR (XSD ×2 + `INVALID_LANGUAGE`) | — |
| c22 same text, en-US vs es-US | suspicious | WARNING ×3 (headline, description, event) | — |
| c23 same text, en-US vs en-GB | per source comment, should not warn | **WARNING ×3** | — |
| c24 HTML in description | text should be plain | WARNING `TEXT_CONTAINS_HTML_TAGS` | — |
| c25 expires before effective | inconsistent | **accepted** | Google: ERROR `EFFECTIVE_NOT_AFTER_EXPIRES`; IPAWS: RECOMMENDATION `INFO_EFFECTIVE_IS_IGNORED` |
| c26 status Actual, headline "EXERCISE EXERCISE EXERCISE" | schema-valid; contradictory | accepted | none |
| c27 status Exercise, headline "THIS IS NOT A DRILL" | schema-valid; contradictory | accepted | none |
| c28 no `<info>` | valid in core | accepted | Google: ERROR `INFO_IS_REQUIRED` |
| c29 status `Drill` | invalid enumeration | ERROR (XSD ×2) | — |

`Basis: execution`

**Interpretation:**
- *Explicit normative violations.* Nine cases break an explicit MUST, REQUIRED or enumeration rule in CAP 1.2 §3.2: c02, c03, c04, c11, c12, c13, c17 (ceiling "MUST NOT be used except in combination with the `<altitude>` element"), c21 and c29. The core flags 8 of them and misses c11.
- *Semantic inconsistencies the text does not explicitly forbid.* Nine more cases fall in this group: c07, c08, c09, c10, c14, c18 (altitude is "the lower limit of a range" when used with ceiling), c25, c26 and c27. The core flags 5 of them (c07, c08 as a warning only, c09, c14, c18). It leaves c10 and c25 to profiles: only the Google profile flags c25 as an error, and neither profile flags c10.
- *Status/text contradictions.* c26 and c27 mirror the live/drill confusion in Hawaii. No validator can detect them, because CAP provides no machine-readable link between `<status>` and free text.
- *Null-language case.* c20 should be treated as `en-US` under the standard's null-value rule; instead it crashes the validator (§6).

`Basis: derived from normative text + execution`

**Timing** (same container; single run): a cold JVM took 341.4 ms to parse and validate all 29 cases plus both profiles. A warm `CapXmlParser(true).parseFrom` on the baseline averaged 361.4 µs per message over 5,000 iterations, after a 1,000-iteration warm-up. `Basis: execution`

### 6. Upstream defects, with source at the pinned revision

**Whitespace-only `<language>` crashes the core validator.** At `java/src/com/google/publicalerts/cap/CapValidator.java:179–192`:

```java
    // Validate language
    if (info.hasLanguage()) {
      String language = info.getLanguage().trim();
      Matcher matcher =  RFC_3066_LANGUAGE.matcher(language);
      
      if (!CapUtil.isEmptyOrWhitespace(language) && !matcher.matches()) {
        xPath.push("language");
        reasons.add(xPath.toString(), INVALID_LANGUAGE, language);
        xPath.pop();
      } else {
        reasons.addAll(
            validateHumanReadableContent(info, matcher.group(0), xPath));
      } 
    }
```

When `language` is empty after trimming, `&&` short-circuits, so `matcher.matches()` is never called. The `else` branch then calls `matcher.group(0)`, and Java throws `IllegalStateException("No match found")` because no match attempt has succeeded. This contradicts CAP 1.2, which says a null value is equivalent to en-US. Execution reproduces it as case c20.

An empty element (c19) does not crash. **Hypothesis, not verified:** the XSD's `default="en-US"` (`schema/cap12.xsd:62`) supplies the value for empty content, so the trimmed value is non-empty. `Basis: source + execution + normative`

**Language comparison uses the full tag, not the primary subtag.** Lines 213–216 state the intent:

```java
  /**
   * Within this method, {@code language} refers to a  RFC 3066 primary-subtag, as we don't want to
   * distinguish between languages with a large overlap (e.g., en-US and en-GB).
   */
```

The caller, however, passes `matcher.group(0)` (line 190). With the pattern `^([a-zA-Z]{1,8})(-[a-zA-Z0-9]{1,8})*$` (lines 72–73), `group(0)` is the whole tag (`en-US`), whereas `group(1)` would be the primary subtag (`en`). Case c23 shows the result: three `SAME_TEXT_DIFFERENT_LANGUAGE` warnings for en-US versus en-GB. `Basis: source + execution`

**History.** The pinned commit is the repository's last ("Fix langauge bug."). Its single-file diff changed line 236 from `humanReadableText.put(humanReadableField, fieldValue, fieldName);` to `humanReadableText.put(humanReadableField, fieldValue, language);`. Before that fix, the stored "language" was the field name, so any repeated text was reported as being in a different language. The intent comment and the `group(0)` argument were not changed in that commit. `Basis: source (commit diff via the GitHub API)`

**Derived note.** `humanReadableText` is an instance field (line 97). The parser creates a new `CapValidator` for each parse (`CapXmlParser.java:361`). A caller that reuses one `CapValidator` instance across alerts would get cross-alert warnings. This was not executed.

### 7. Spoofing cell-broadcast alerts

**Threat model and mechanism** (demo abstract, full text examined; DOI 10.1145/3307334.3328572). `Basis: documentation`
- **Carrier.** The alert is carried in SIB12, part of the periodically broadcast system information. "A broadcast message, known as the System Information Block (SIB), carries the CMAS alert without encryption or authentication". A phone needs SIBs for cell selection, which happens before mutual authentication.
- **Idle phones.** An idle phone camps on the eNodeB with the highest reference-signal received power. The malicious eNodeB needs no subscriber keys. "A UE attempts the authentication process up to five times before it listens to other frequency channels". These attempts take 42 seconds, during which the spoofed SIB12 is decoded and displayed.
- **Active phones.** Handover to a rogue cell fails, because the core network does not know the rogue cell. The attacker instead transmits at much higher power than the serving cell to cause a radio-link failure. The phone then re-attaches to the strongest cell and becomes vulnerable as an idle phone would.
- **Equipment.** One software-defined radio, one commercial LTE eNodeB and two laptops, with modified NextEPC and srsLTE. The demo ran inside a Faraday cage and was "tested on iOS and Android phones from all four major US carriers".

**Reach.** The abstract of the full paper (DOI 10.1145/3307334.3326082, as indexed; body not examined) states: "with only four malicious portable base stations of a single Watt of transmit power each, almost all of a 50,000-seat stadium can be attacked with a 90% success rate". The abstract does not say whether the stadium figure is measured or simulated (**unknown**). `Basis: documentation`

**Mitigations and standards status:**
- 3GPP TR 33.969 (examined as ETSI TR 133 969 V18.0.0, 2024-04) is a *study* report, not a normative specification. It analyses signature-based PWS security, with NAS-based, GBA-based and implicit-certificate key distribution. One quantitative constraint: "If the security solution is going to support ETWS Primary Notifications over GERAN then the total length of the signature and related security parameters cannot exceed 75 bytes" (§6.2.2.4).
- Whether any normative 3GPP specification or any deployed network has adopted signed warnings is **not examined**.
- A 2026 preprint (arXiv 2604.24404) reports the "first open-source 5G emergency alert spoofing attack". It modifies OpenAirInterface and proposes a device-side cross-cell check: compare a received warning with neighbouring cells' broadcasts and flag single-source alerts. This was examined at abstract level only.

`Basis: normative (study status) + documentation`

### 8. Warning-response models and message content, mapped to CAP fields

- **PADM** (Lindell and Perry 2012, abstract). Three predecision processes come first: reception, attention and comprehension of warnings, or exposure to, attention to and interpretation of environmental and social cues. Three core perceptions follow (threat, protective action and stakeholder). These "form the basis for decisions", and the decision outcome together with situational facilitators and impediments "produces a behavioral response". `Basis: documentation`
- **Short-message guidance** (Sutton and Kuligowski 2019, full text). `Basis: documentation`
  - Effective messages contain five content types: source, guidance, hazard, location and time. They attribute this to Mileti and Sorensen (1990) and later work.
  - "For 90-character WEA messages, the optimized order of message contents are as follows: source, guidance, hazard, location, time."
  - Short messages lead to "information seeking, sharing, sense making, and milling", which "delay protective action".
  - For 360-character WEAs they recommend five things: complete spelling, detailed location (landmarks), the hazard's threat, risk and impact, explicit how-to protective actions, and additional guidance.
  - Citing De Young et al. 2019, they report that more than half of a surveyed Hawaii population searched for more information before acting on the missile WEA. That figure was not checked in the original.

| Message element (Mileti–Sorensen / Sutton–Kuligowski) | CAP 1.2 field(s) | Validator coverage at the pinned library revision |
|---|---|---|
| Source | `info/senderName` (human), `alert/sender` (machine), `info/contact`, `info/web` | Google profile recommends `senderName` (`SENDER_NAME_STRONGLY_RECOMMENDED`) and requires `web`; core: none |
| Guidance | `info/instruction`, `info/responseType` | Google profile recommends both; IPAWS recommends `instruction`; core: none |
| Hazard | `info/event`, `info/eventCode`, `info/headline`, `info/description`, `urgency`/`severity`/`certainty` | Schema enforces the enumerations; IPAWS requires exactly one `eventCode` with valueName "SAME" and a three-letter value (`SAME_EVENT_CODE_REQUIRED`), and identical event codes and categories across infos |
| Location | `area/areaDesc`, `polygon`, `circle`, `geocode` | Polygon closure and self-intersection (core); IPAWS requires at least one `<area>` (`AREA_IS_REQUIRED`) and emits `AREA_SAME_GEOCODE_RECOMMENDED` |
| Time | `info/effective`, `onset`, `expires` | Both profiles require `expires`; only Google checks effective < expires |
| Order within 90 characters | not representable; a property of the rendered text | none |

`Basis: normative + source + derived`

### 9. Measured public response to the false alert

From Jones and Silver (full text, APA author copy; online 25 July 2019; print in *American Psychologist* 75(5), 2020). `Basis: documentation`
- **Data.** 1.2 million tweets from 14,830 users in Hawaii, covering 6 weeks before to 18 days after the alert.
- **Anxiety measure.** A tweet counts as anxious if it contains at least one of 114 LIWC anxiety words. "threat" and "alarm" were removed because officials used them to refer to the event.
- **Results.** Anxiety rose 4.6 % on the day of the alert and 3.4 % every 15 minutes during the 38-minute alert period. It "remained elevated for at least 7 days postalert". Users with low pre-alert anxiety expressed more anxiety at onset, and for longer.
- **Stated limitations.** Twitter users are unrepresentative. Word counts are an imperfect measure of felt anxiety. Only about 50 % of users mentioned a Hawaii locale, and 0.07 % of tweets were geocoded.

### 10. Performance and resource footprint (six levels)

| Level | CAP library / validator | Emergency-call routing (2014) | Alert origination (Hawaii) | Cell-broadcast spoofing |
|---|---|---|---|---|
| L1 authoring / maintenance | not measured; repository archived since 2019 (GitHub flag) | not measured | not measured | not measured |
| L2 toolchain build | `javac` of `java/src` in the JDK 8 container: not timed; compiled classes plus resources 710,966 B (measured) | not applicable | not applicable | not measured |
| L3 latency to verdict | Cold JVM 341.4 ms for 29 cases; warm 361.4 µs per message (measured) | Detection latency about 6 h (06:00 identification after a 23:54 onset; report) | 5 min to cancel retransmission, 38 min to correct (report) | 42 s attach-failure window per idle phone (demo abstract) |
| L4 execution | Self-intersection check is O(n²) in polygon points (source comment); large-polygon cost not measured | > 87 % of calls during the outage failed to reach CAMA PSAPs (report) | not applicable | 4 × 1 W, 90 % of a 50,000-seat stadium (full-paper abstract) |
| L5 proof / certificate checking | XML signature verification exists (`XmlSignatureValidator.java`) but was not exercised; CAP says unverifiable signatures must not cause rejection | not applicable | not applicable | Signature overhead bounded at 75 B for ETWS over GERAN (TR 33.969) |
| L6 footprint | `java/src` 665,950 B; bundled jars 4,680,051 B; JDK 8 image 279 MB (measured) | not measured | not measured | not measured |

### 11. Comprehensibility and model refinement

- **C1, human comprehension:**
  - CAP's meaning of "is this alert still in force?" is not local to the message. It depends on whether a later message names this one in `<references>`, on recipient policy when `<expires>` is absent, and on profile rules.
  - In the Hawaii timeline, a human had to recognise "THIS IS NOT A DRILL" within a recording labelled "EXERCISE". In the interface, one drop-down distinguished live from drill, and the confirmation prompt was generic.
  - In the 2014 outage, the only signal was thousands of minor alarms summarised into one item. The diagnostic was nominally present but not legible.
  - All three cases share one property: the safety-critical distinction (live vs drill, cancelled vs active, failing vs degraded) was carried by state that operators could not see. `Basis: derived`
- **C2, minimal abstractions:**
  - *Message lifecycle.* CAP encodes it with three overlapping mechanisms: `msgType`, `references`, and time bounds (`effective`/`expires`). A single explicit lifecycle (an alert ID with states active, superseded, cancelled or expired, each transition requiring a reference) would turn c05, c08 and c25 into ordinary rejected cases. In the library, those rules sit in profiles, a third layer beyond schema and core.
  - *Exercise/live.* The minimal fix for status/text contradictions is structural: forbid live templates in exercise sessions, and the reverse, at the originating system. It cannot be done by a text classifier in the validator.
  - *Counters.* The 2014 failure is a finite-counter invariant with no overflow policy. The generic remedy is to monitor outcomes (calls completed) rather than to enlarge the counter, and the operator's 15-minute success-ratio alarm is exactly that shift. `Basis: derived`

### 12. How implementations and claims are validated (V1–V4)

- **V1, specification adequacy:**
  - The library's tests (`java/test/...`, including `profile/*Test.java`) were not run.
  - This report's probe is a spec-text conformance test. It found one normative "Required" rule (c11) and one normative null-value rule (c20) not honoured by the core validator.
  - No mutation testing of the validator was performed. `Basis: execution + source`
- **V2, checker soundness:**
  - Schema and semantic validation are two independent checkers in sequence. The XSD error in c20 did not stop the semantic stage from running on a partially built alert, which is where the crash happens.
  - Fuzzing the parser with malformed XML was **not examined**. `Basis: execution + derived`
- **V3, concurrency, crash and physical channel:**
  - The spoofing work is a physical-channel validation: over-the-air experiments in a Faraday cage across carriers and handset OSes.
  - The 2014 outage is a capacity-exhaustion failure that load or soak testing with counter-headroom monitoring could expose. Whether the operator ran such tests is not stated in the report.
  - The library's thread safety was **not examined**. `Basis: documentation`
- **V4, field replay and human comprehension:**
  - Sutton and Kuligowski ground their templates in focus groups, experiments and an expert panel. Jones and Silver is an observational measurement of public response to a real false alert.
  - No study examined here tests alert *originators'* mental models of live versus drill modes, although the Hawaii timeline makes that the critical human factor.
  - Replaying the incident with the original origination software was **not examined**. `Basis: documentation`

## Boundaries

- **Not examined:**
  - The FCC final report on the Hawaii false alert (released 10 April 2018, per its FCC listing page) and the FCC report on the December 2018 carrier outage (released 19 August 2019): both document fetches failed. Statements about the December 2018 outage come only from the Washington UTC staff release, which explicitly reflects staff, not commission, views.
  - The full bodies of Lee et al. 2019 (only the demo abstract and the full paper's indexed abstract were read), Lindell and Perry 2012 (abstract only), Mileti and Sorensen 1990 and Bean et al. 2015 (metadata only; their content is cited via Sutton and Kuligowski's summary).
  - 3GPP TR 33.969 clause 10 and any normative specification adopting signed warnings.
  - Deployed alert-origination products, IPAWS-OPEN, and handset vendor behaviour after 2019.
  - The hosted CAP validator.
- **Unknown:**
  - Whether the 50,000-seat stadium result is measured or simulated.
  - Why an empty `<language>` element does not crash while a whitespace-only one does (the XSD-default hypothesis in §6 was not verified).
  - Whether the operator in 2014 had counter-headroom monitoring before the incident.
  - The PTM counter's maximum value, which the FCC report does not state.
- **Known not to apply:**
  - The probe's acceptance results do not apply to the library's strict mode (`strictXsdValidation = true`). That mode skips `CapValidator` entirely (`CapXmlParser.java:360–362`), so it neither crashes on c20 nor performs any of the semantic checks in §4.
  - The library findings do not apply to other CAP implementations.
- **Attractive stronger conclusions the evidence does not establish:**
  - That the Hawaii alert would have been prevented by message validation. The message was well-formed; the failure was mode selection.
  - That LTE alert spoofing remains possible on current networks and handsets. Only the 2019 demonstration and a 2026 5G preprint were examined.
  - That the 2014 counter limit was an integer-width overflow. The report says only "pre-set maximum".
  - That short-message guidance has measured effect sizes. The guidance is expert-panel synthesis with focus-group and experimental support, and this report did not extract effect sizes.
- **Unsupported (by subject):**
  - CAP has no machine-readable link between `<status>` and free text.
  - CAP does not require `<references>` for Update/Cancel.
  - CAP does not require authentication.

## Evidence

**Pinned source** (`google/cap-library@67dcf20373834725b15c5325a73f615d92a708fa`, fetched 2026-11-21; GitHub API reports `archived: true` and last push 2019-09-23):
- `java/src/com/google/publicalerts/cap/CapValidator.java:63–97` (namespaces, language pattern, human-readable field set, instance table), `:105–137` (`validateAlert`), `:139–173` (references), `:175–243` (info, language, human-readable text), `:245–283` (area, polygon), `:285–336` (resource, web), `:393–423` (string fields), `:425–508` (self-intersection, longitude normalisation).
- `java/src/com/google/publicalerts/cap/CapXmlParser.java:56–121` (schema maps, strict vs extended), `:305–363` (parse and validate flow).
- `java/src/com/google/publicalerts/cap/CapUtil.java:197–199` (`isEmptyOrWhitespace`).
- `java/src/com/google/publicalerts/cap/profile/us/Ipaws1Profile.java:95–200`; `java/src/com/google/publicalerts/cap/profile/GoogleProfile.java:95–160`.
- `schema/cap12.xsd:62`; `schema/cap12_extended.xsd:1–50`.
- `validator/src/com/google/publicalerts/cap/validator/CapValidator.java:56–273`.
- The pinned commit's diff ("Fix langauge bug."), retrieved through `GET /repos/google/cap-library/commits/67dcf20373834725b15c5325a73f615d92a708fa`.

**Normative and regulator documents** (read 2026-11-21):
- OASIS CAP 1.2 OASIS Standard, 01 July 2010 (HTML at the URL in `REPORT.json`). Cited: §3.2.1 alert element table, §3.2.2 info, §3.2.4 area, §3.3.4 Security Note.
- FCC PSHSB, *April 2014 Multistate 911 Outage: Cause and Impact*, Report and Recommendations, PS Docket No. 14-72 (DOC-330012A1). Cited: §1, §2.2, §3.2, §3.4, §5, Table 1, footnote 39.
- FCC PSHSB, *Preliminary Report: Hawaii Emergency Management Agency's January 13, 2018 False Ballistic Missile Alert*, 30 January 2018 (DOC-348923A1). Cited: slides 3–5.
- FCC listing pages for "Report and Recommendations, Hawaii Emergency Management Agency, January 13, 2018 False Alert" (released 10 April 2018) and "FCC Issues Report on CenturyLink Network Outage" (released 19 August 2019): metadata only.
- Washington Utilities and Transportation Commission news release, 22 December 2020, Docket UT-181051 (staff position).
- 3GPP TR 33.969 V18.0.0 as ETSI TR 133 969 V18.0.0 (2024-04). Cited: §6.2.2.4, §6.2.10.10.

**Literature** (DOIs verified against Crossref metadata on 2026-11-21; the arXiv DOI was verified through the doi.org handle API, which resolves to the arXiv abstract page, and that page was read):
- Lee G, Lee J, Lee J, Im Y, et al. *This Is Your President Speaking: Spoofing Alerts in 4G LTE Networks*. MobiSys 2019, pp. 404–416. doi:10.1145/3307334.3326082 (abstract only).
- Hollingsworth M, Lee G, Lee J, Lee J, et al. Demo abstract of the same title. MobiSys 2019, pp. 663–664. doi:10.1145/3307334.3328572 (full text).
- Lindell MK, Perry RW. Risk Analysis 32(4):616–632, 2012. doi:10.1111/j.1539-6924.2011.01647.x (abstract via Crossref).
- Sutton J, Kuligowski ED. Natural Hazards Review 20(2):04019002, 2019. doi:10.1061/(ASCE)NH.1527-6996.0000324 (full text, author-shared copy).
- Jones NM, Silver RC. American Psychologist 75(5):683–693, 2020. doi:10.1037/amp0000495 (full text, APA author copy).
- Mileti DS, Sorensen JH. Oak Ridge National Laboratory report, 1990. doi:10.2172/6137387 (metadata only).
- Bean H, Sutton J, Liu BF, Madden S, et al. Review of Communication 15(1):60–80, 2015. doi:10.1080/15358593.2015.1014402 (metadata only).
- Abou Hasna A, Chendeb N, El Falou A. arXiv:2604.24404v1, submitted 27 April 2026 (abstract).

**Execution (2026-11-21):**
- *Host and container:* Linux x86_64 VM, 96 vCPU Intel Xeon @ 2.60 GHz; rootless container `eclipse-temurin:8u432-b06-jdk` (digest above) with `--network=none`.
- *Build:* `javac -cp <java/lib jars> -d <classes> $(find java/src -name '*.java')`. Then the repository's `schema/` directory was copied to `<classes>/com/google/publicalerts/cap/schema/`, mirroring `java/build.xml`'s `src_compile` target, and the non-Java resources under `java/src` were copied alongside.
- *Probe:* `support/cap_probe/make_cases.py` writes the 29 cases and `cases.tsv`. `support/cap_probe/CapProbe.java` is the harness. Raw output is in `support/cap_probe/results/probe_out.txt`, and the per-case spec expectations in `support/cap_probe/results/cases.tsv`.

## Revalidation

- **CAP library defects (cheapest check):** compile any newer revision (or a fork) and run `CapProbe` on the 29 cases. Two outcomes identify the defects: c20 producing an exception (crash) and c23 producing warnings (full-tag comparison). Without running anything, diff `CapValidator.java` lines 179–192 and 213–243: the crash is fixed if the `else` branch no longer calls `matcher.group` when the trimmed language is empty.
- **CAP normative rules:** re-read CAP §3.2.1 for `<addresses>`, `<restriction>` and `<references>` in any successor version (for example, a CAP 1.3 draft). If `<references>` becomes required for Update/Cancel, c05 should flip to rejected in a conforming core validator.
- **Regulator findings:** these are historical documents and stable. Revalidation means re-reading the cited sections. Retrieve the FCC final Hawaii report (released 10 April 2018) and the FCC CenturyLink report (released 19 August 2019) to fill the "not examined" rows.
- **Spoofing:** check whether a normative 3GPP specification (not the TR 33.969 study) now mandates signed PWS messages, and whether handset OS release notes describe warning-message verification. Reproducing the over-the-air attack requires licensed or shielded radio facilities and is not a cheap check.
- **Warning-response research:** Jones and Silver's numbers are fixed. For message-content guidance, look for newer experiments testing the 360-character templates' effect on protective action.
