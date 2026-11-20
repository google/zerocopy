#!/usr/bin/env python3
"""Toy Python port of the per-locus likelihood-ratio arithmetic in the New York
City Forensic Statistical Tool (FST) source, propublica/nyc-dna-software at
commit 5b3500de6f0b879350dd1b487218e590eeacc138, file FST.Common/Comparison.cs.

Basis: execution (toy model of FST, not FST itself). FST is C#/.NET backed by
SQL Server stored procedures and tables (drop-out, drop-in and allele
frequencies) that ship only as compressed SQL Server backups; none of that is
executed here. Every rate and frequency below is an INVENTED illustrative value,
not an FST value.

Ported behaviours (Comparison.cs line numbers at the pinned commit):
  EvidenceAllelesAtLocus   L1049-1081  union of non-empty replicate strings + "w"
  GetFrenquencyTable       L1161-1232  freq lookup, default for unknown alleles,
                                       omega w = 1 - sum, null if w<0 or w>=1
  CheckFrequencyForRemoval L246-315    drop locus if sum(freq of evidence alleles)
                                       >= 0.97 for ANY race
  Frenquency               L1268-1353  hom: p*(p+theta*(1-p)); het: 2*p*q
  GetPermutations          L682-728    unknown genotypes over evidence alleles + w
  NumeratorDenominatorCalculation L748-998  per-row product of drop-out (per
                                       contributor, per non-empty replicate),
                                       drop-in (count of unexplained evidence
                                       alleles -> Pc0/Pc1/Pc2) and genotype freqs;
                                       rows with product == 1 are skipped
  GetGenotypeDropOutRate   L1010-1042  PHOM0/PHOM1, PHET0/PHET1/PHET2
  DoCompare                L374-511    LR = prod over loci of Pn/Pd (skip Pd==0)
"""
import itertools
import math

# ---- invented toy rates (NOT FST's database values) ----
RATES = dict(PHET1=0.20, PHET2=0.05, PHOM1=0.10)
RATES["PHET0"] = 1 - RATES["PHET1"] - RATES["PHET2"]  # Comparison.cs L1378
RATES["PHOM0"] = 1 - RATES["PHOM1"]                   # Comparison.cs L1377
PC = (0.97, 0.02, 0.01)  # Pc0, Pc1, Pc2 (invented)
DEFAULT_FREQ = 0.02      # code's hard-coded fallback when no "0" allele row exists


def evidence_alleles_at_locus(reps):
    parts = [r for r in reps if r]  # IsNullOrEmpty check: "NEG" is NOT empty
    if not parts:
        return None
    seq = ",".join(parts + ["w"]).split(",")
    out = []
    for a in seq:  # Enumerable.Distinct preserves first-occurrence order
        if a and a not in out:
            out.append(a)
    return out


def freq_table(alleles, db):
    tbl = {a: db.get(a, DEFAULT_FREQ) for a in alleles if a != "w"}
    w = 1 - sum(tbl.values())
    if w < 0 or w >= 1:
        return None
    tbl["w"] = w
    return tbl


def freq_sum(alleles, db):
    return sum(db.get(a, DEFAULT_FREQ) for a in alleles if a != "w")


def genotype_freq(a, b, tbl, theta):
    if a == b:
        p = tbl.get(a, DEFAULT_FREQ)
        return p * (p + theta * (1 - p))
    return 2 * tbl.get(a, DEFAULT_FREQ) * tbl.get(b, DEFAULT_FREQ)


def dropout(evidence, geno, rates):
    ev = evidence.split(",")
    a, b = geno
    n = sum(1 for x in (a, b) if x not in ev)
    if a == b:
        return rates["PHOM0"] if n == 0 else rates["PHOM1"]
    return rates[("PHET0", "PHET1", "PHET2")[n]]


def dropin(evidence, contributors, pc, tbl=None, isfg=False):
    alleles = [x for g in contributors for x in g]
    extras = [x for x in evidence.split(",") if x not in alleles]
    if not isfg:  # FST: rate chosen by COUNT of unexplained alleles only
        return pc[min(len(extras), 2)]
    # counterfactual ISFG-2012-style variant: Pr(C) * p_a per dropped-in allele
    if not extras:
        return pc[0]
    out = 1.0
    for x in extras:
        out *= pc[1] * tbl.get(x, DEFAULT_FREQ)
    return out


def locus_term(reps, knowns, n_unknown, db, theta, rates=RATES, pc=PC, isfg=False):
    alleles = evidence_alleles_at_locus(reps)
    tbl = freq_table(alleles, db)
    if tbl is None:
        return None
    perms = [(alleles[i], alleles[j]) for i in range(len(alleles))
             for j in range(i, len(alleles))]
    total = 0.0
    for row in itertools.product(perms, repeat=n_unknown):
        contributors = list(row) + list(knowns)
        fre = 1.0
        for g in row:
            fre *= genotype_freq(g[0], g[1], tbl, theta)
        pa = 1.0
        for ev in reps:
            if not ev:
                continue  # empty replicate (INC) is skipped
            for g in contributors:
                pa *= dropout(ev, g, rates)
            pa *= dropin(ev, contributors, pc, tbl, isfg)
        if pa != 1:  # Comparison.cs L970: rows whose product is exactly 1 are skipped
            total += pa * fre
    return total


def locus_lr(reps, suspect, db, theta, isfg=False, n_unknown_hd=1):
    pn = locus_term(reps, [suspect], 0, db, theta, isfg=isfg)
    pd = locus_term(reps, [], n_unknown_hd, db, theta, isfg=isfg)
    return pn, pd, (pn / pd if pd else float("nan"))


def bn_genotype(a, b, p, typed, theta):
    """Balding-Nichols conditional genotype probability (as in EuroForMix
    src/genoProbFuns.cpp prob_a / prob_relUnknown without relatives)."""
    def prob(x, m, n):
        return (m * theta + (1 - theta) * p[x]) / (1 + (n - 1) * theta)
    cnt = dict(typed)
    n = sum(cnt.values())
    if a == b:
        return prob(a, cnt.get(a, 0), n) * prob(a, cnt.get(a, 0) + 1, n + 1)
    return 2 * prob(a, cnt.get(a, 0), n) * prob(b, cnt.get(b, 0), n + 1)


def main():
    theta = 0.03
    print("Toy rates:", RATES, "Pc0..2 =", PC, "theta =", theta)

    print("\n[A] 0.97 frequency-sum locus removal (CheckFrequencyForRemoval)")
    # invented low-diversity locus; two-person mixture showing five alleles
    db_common = {"8": 0.45, "9": 0.12, "10": 0.08, "11": 0.25, "12": 0.08, "13": 0.01}
    reps = ["8,9,10,11,12", "8,9,11,12", "8,9,10,11"]
    s = freq_sum(evidence_alleles_at_locus(reps), db_common)
    print(f"  evidence alleles 8,9,10,11,12; freq sum = {s:.2f} -> removed: {s >= 0.97}")
    for susp in [("8", "11"), ("10", "12"), ("8", "13")]:
        pn = locus_term(reps, [susp], 1, db_common, theta)   # Hp: S + 1 unknown
        pd = locus_term(reps, [], 2, db_common, theta)       # Hd: 2 unknowns
        lr = pn / pd
        print(f"  suspect {susp}: locus LR if kept = {lr:.4g}; after removal factor = 1"
              f" -> removal multiplies total LR by {1/lr:.4g}")

    print("\n[B] Drop-in term: FST count-based Pc vs ISFG-style Pr(C)*p_a (counterfactual)")
    db = {"14": 0.10, "15": 0.10, "16": 0.01, "17": 0.20}
    reps = ["14,15,16", "14,15", "14,15"]
    for isfg in (False, True):
        pn, pd, lr = locus_lr(reps, ("14", "15"), db, theta, isfg=isfg)
        print(f"  {'ISFG-style' if isfg else 'FST code  '}: Pn={pn:.4e} Pd={pd:.4e} LR={lr:.4g}")

    print("\n[C] Genotype probability: FST hom-only theta vs Balding-Nichols conditional")
    p = {"a": 0.10, "b": 0.10}
    for g, typed in [(("a", "a"), {"a": 2}), (("a", "b"), {"a": 1, "b": 1})]:
        fst_v = genotype_freq(g[0], g[1], p, theta)
        bn_v = bn_genotype(g[0], g[1], p, typed, theta)
        print(f"  genotype {g}: FST={fst_v:.5f}  BN|suspect typed={bn_v:.5f}  ratio BN/FST={bn_v/fst_v:.3f}")

    print("\n[D] A replicate recorded as 'NEG' at a locus where other replicates have alleles")
    db = {"14": 0.10, "15": 0.10}
    reps_neg = ["14,15", "NEG", "14,15"]
    alle = evidence_alleles_at_locus(reps_neg)
    print("  allele list used for unknown genotypes:", alle)
    for label, r in [("as coded ('NEG' string)", reps_neg),
                     ("'NEG' treated as empty/INC", ["14,15", "", "14,15"])]:
        pn, pd, lr = locus_lr(r, ("14", "15"), db, theta)
        print(f"  {label:28s}: Pn={pn:.4e} Pd={pd:.4e} LR={lr:.4g}")

    print("\n[E] float32 range for the stored per-race LR ((float)P, Comparison.cs L513)")
    import struct
    big = struct.unpack("f", struct.pack("f", 3.4028234663852886e38))[0]
    print(f"  largest finite float32 = {big:.6e}; log10 = {math.log10(big):.3f}")


if __name__ == "__main__":
    main()
