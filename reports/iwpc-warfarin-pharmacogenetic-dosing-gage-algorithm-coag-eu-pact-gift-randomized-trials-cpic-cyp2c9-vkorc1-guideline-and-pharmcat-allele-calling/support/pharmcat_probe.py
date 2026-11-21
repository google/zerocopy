#!/usr/bin/env python3
"""Probe PharmCAT v3.4.0 allele calling for CYP2C9 / VKORC1 / CYP4F2 / rs12777823
on synthetic single-sample VCFs derived from the release's pharmcat_positions VCF.

Usage: python3 pharmcat_probe.py <pharmcat.jar> <pharmcat_positions.vcf> <workdir>

Each case edits genotypes (or deletes rows) of an all-reference template restricted to
CYP2C9, VKORC1 and CYP4F2 positions plus the CYP2C-cluster position rs12777823.
Runs are sequential; each run is limited by `timeout 60`, -Xmx2g and
-XX:ActiveProcessorCount=8. Peak RSS and wall time come from /usr/bin/time -v.
"""
import json
import os
import re
import subprocess
import sys

JAR, POSVCF, WORK = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(WORK, exist_ok=True)
KEEP_PX = {"PX=CYP2C9", "PX=VKORC1", "PX=CYP4F2"}

header, rows = [], []
for line in open(POSVCF):
    if line.startswith("##"):
        if line.startswith(("##fileformat", "##contig", "##FILTER", "##FORMAT", "##INFO")):
            header.append(line)
        continue
    if line.startswith("#CHROM"):
        header.append(line.rstrip("\n").rsplit("\t", 1)[0] + "\tSYNTH\n")
        continue
    f = line.rstrip("\n").split("\t")
    if f[7] in KEEP_PX or f[2] == "rs12777823":
        rows.append(f)

# rs IDs used

# rs IDs used by the cases:
#   rs1799853  CYP2C9*2 (g.94942290C>T)     rs1057910  CYP2C9*3 (g.94981296A>C)
#   rs28371686 CYP2C9*5                      rs7900194  CYP2C9*8 (A) / *27 (T)
#   rs72558193 second SNV of CYP2C9*18       rs9923231  VKORC1 -1639G>A (c.-1639; g.31096368C>T)
#   rs2108622  CYP4F2*3                      rs12777823 CYP2C cluster position of interest


def make(case, gts=None, delete=()):
    gts = gts or {}
    out = []
    for f in rows:
        if f[2] in delete:
            continue
        g = list(f)
        key = g[2] if g[2] in gts else "pos:" + g[1]
        if key in gts:
            g[9] = gts[key]
        out.append("\t".join(g) + "\n")
    path = os.path.join(WORK, case + ".vcf")
    with open(path, "w") as fh:
        fh.writelines(header + out)
    return path


CASES = [
    ("01_reference", {}, ()),
    ("02_s2_s3_unphased", {"rs1799853": "0/1", "rs1057910": "0/1"}, ()),
    ("03_s2_s3_phased_trans", {"rs1799853": "0|1", "rs1057910": "1|0"}, ()),
    ("04_s2_s3_phased_cis", {"rs1799853": "0|1", "rs1057910": "0|1"}, ()),
    ("05_s1_s3_row_deleted", {}, ("rs1057910",)),
    ("06_s3_het_gt_missing", {"rs1057910": "./."}, ()),
    ("07_s3_partial_ref", {"rs1057910": "0/."}, ()),
    ("08_s3_partial_alt", {"rs1057910": "./1"}, ()),
    ("09_s2_plus_s18_2nd_unphased", {"rs1799853": "0/1", "rs72558193": "0/1"}, ()),
    ("10_s8_het", {"rs7900194": "0/1"}, ()),
    ("11_s27_het", {"rs7900194": "0/2"}, ()),
    ("12_vkorc1_AA_cyp4f2_s3_cyp2c_AG", {"rs9923231": "1/1", "rs2108622": "0/1", "rs12777823": "0/1"}, ()),
    ("13_vkorc1_row_deleted", {}, ("rs9923231",)),
    ("14_s2_hom_s3_het_unphased", {"rs1799853": "1/1", "rs1057910": "0/1"}, ()),
    ("15_s2_s5_unphased", {"rs1799853": "0/1", "rs28371686": "0/1"}, ()),
    ("16_s80_het_no_phenotype_entry", {"pos:94938719": "0/1"}, ()),
]


def run(case, vcf):
    outdir = os.path.join(WORK, case)
    os.makedirs(outdir, exist_ok=True)
    cmd = ["timeout", "60", "/usr/bin/time", "-v", "java", "-Xmx2g", "-XX:ActiveProcessorCount=8",
           "-Djava.io.tmpdir=" + os.path.join(WORK, "tmp"), "-Duser.home=" + os.path.join(WORK, "home"),
           "-jar", JAR, "-vcf", vcf, "-o", outdir, "-reporterJson"]
    os.makedirs(os.path.join(WORK, "tmp"), exist_ok=True)
    os.makedirs(os.path.join(WORK, "home"), exist_ok=True)
    p = subprocess.run(cmd, capture_output=True, text=True)
    err = p.stderr
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", err)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", err)
    with open(os.path.join(outdir, "stdout_stderr.txt"), "w") as fh:
        fh.write(p.stdout + "\n-----\n" + err)
    return {"rc": p.returncode, "wall": wall.group(1) if wall else None,
            "max_rss_kb": int(rss.group(1)) if rss else None}


def summarize(case):
    outdir = os.path.join(WORK, case)
    res = {}
    for fn in os.listdir(outdir):
        if fn.endswith(".match.json"):
            m = json.load(open(os.path.join(outdir, fn)))
            for gc in m.get("results", []):
                if gc.get("gene") not in ("CYP2C9", "VKORC1", "CYP4F2"):
                    continue
                md = gc.get("matchData", {})
                res[gc["gene"] + ".match"] = {
                    "diplotypes": [d.get("name") for d in gc.get("diplotypes", [])],
                    "scores": [d.get("score") for d in gc.get("diplotypes", [])],
                    "missingPositions": [x.get("rsid") or x.get("position") for x in md.get("missingPositions", [])],
                    "missingAmp1Positions": md.get("missingAmp1Positions"),
                    "warnings": [w.get("message") for w in (gc.get("warnings") or [])],
                    "variantsOfInterest": [(v.get("rsid"), v.get("vcfCall")) for v in gc.get("variantsOfInterest", [])],
                    "uncallableHaplotypes_count": len(gc.get("uncallableHaplotypes") or []),
                }
        if fn.endswith(".phenotype.json"):
            ph = json.load(open(os.path.join(outdir, fn)))
            for g in ("CYP2C9", "VKORC1", "CYP4F2"):
                gr = ph.get("geneReports", {}).get(g)
                if not gr:
                    continue
                res[g + ".phenotype"] = {
                    "recommendationDiplotypes": [
                        {"label": d.get("label"), "phenotypes": d.get("phenotypes"),
                         "activityScore": d.get("activityScore")}
                        for d in gr.get("recommendationDiplotypes", [])],
                    "messages": [x.get("rule_name") for x in gr.get("messages", [])],
                }
        if fn.endswith(".report.json"):
            rep = json.load(open(os.path.join(outdir, fn)))
            w = rep.get("drugs", {}).get("CPIC Guideline Annotation", {}).get("warfarin", {})
            res["CPIC.warfarin.messages"] = [x.get("rule_name") for x in w.get("messages", [])]
    return res


if __name__ == "__main__":
    only = set(sys.argv[4:])
    summary = {}
    for case, gts, delete in CASES:
        if only and case not in only:
            continue
        vcf = make(case, gts, delete)
        meta = run(case, vcf)
        meta["calls"] = summarize(case)
        summary[case] = meta
        print(case, json.dumps(meta))
    with open(os.path.join(WORK, "summary.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
