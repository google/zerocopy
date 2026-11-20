# Support material: probes and recorded outputs

All probes are independent Python re-implementations (Python 3.13, numpy; no scipy, no R).
Their results characterise the formulas as ported here, cross-checked against numbers printed by
the upstream packages' own vignettes. They are not executions of the R packages.

## Inputs (fetch from the pinned upstream revisions)

```sh
mkdir -p data && cd data
R=https://raw.githubusercontent.com
curl -sSLO $R/cran/openEBGM/d731cb3ee8d5fe6013666e05b9e55e2494d51f25/data/caers.rda
curl -sSLO $R/cran/PhViD/bbb450c3837c6001710a328d382a27e856e601d8/data/PhViDdata.frame.rda
for f in sccs caseControl cohortMethod southworthReplication grahamReplication; do
  curl -sSLO $R/OHDSI/EmpiricalCalibration/03d4747fd805e92744d0bcaf603f4c2d0b13370b/data/$f.rda
done
for f in omopReferenceSet euadrReferenceSet ohdsiNegativeControls; do
  curl -sSLO $R/OHDSI/MethodEvaluation/d7305910f6c6a390a9e423ffc1685a97c017183e/data/$f.rda
done
sha256sum *.rda
```

Expected SHA-256 (observed 2026-11-20):

```text
54caf657dba2fd375773e9a0db043acb427aaf4b0182fa318e98aae19055d644  caers.rda
d4bb5dbcba71d5999b2b56bf6eb671c8c1ed62b5f868c0df7b3ba7d0a4db5d1b  PhViDdata.frame.rda
2f9fa2398507e16d6be43083f11897263973da4ffe56cc20bfe0a2f1189b3e62  sccs.rda
12eb089b631af168d4cdffb2632d37126f19c87905f14882b16fb60de75efd0a  caseControl.rda
9f93bdab57773c10e32bc268a444b20ac5bd111b3ed5217767c42145c8ef8069  cohortMethod.rda
50ff4fa428469c719d2fb0be53236655394708a420ea954887e65c70610d319c  southworthReplication.rda
ac567c3d249f07aa6b4bae81efcad4d9120a889c8c7ca2773cd89c9bf52ed2d6  grahamReplication.rda
8d0964fce92c557d98cb751ec2aea7c1e3e1643696231a177128579a5662fa15  omopReferenceSet.rda
5cea251e7ab03a232f871abfb448655b8474ffab325bb19b4fbae8d139203c32  euadrReferenceSet.rda
85cb76a5b0b3ded852e8c60432aae5b77836aebdd35239f70963efb9a56ad504  ohdsiNegativeControls.rda
```

## Commands (run from the package directory, with `data/` populated as above)

```sh
cd support/probes
python3 probe_openebgm.py ../../data/caers.rda                     > ../outputs/probe_openebgm.txt
python3 probe_empirical_calibration.py ../../data                  > ../outputs/probe_empirical_calibration.txt
python3 probe_reference_sets.py ../../data/omopReferenceSet.rda ../../data/euadrReferenceSet.rda \
        ../../data/ohdsiNegativeControls.rda                       > ../outputs/probe_reference_sets.txt
python3 probe_disproportionality.py ../../data/PhViDdata.frame.rda ../../data/caers.rda \
                                                                   > ../outputs/probe_disproportionality.txt
```

Recorded wall-clock times on the observation host (x86_64 Linux workstation, single process):
`probe_openebgm.py` 8.1 s, `probe_empirical_calibration.py` 12.5 s, `probe_disproportionality.py`
12.8 s, `probe_reference_sets.py` under 1 s. These time the Python ports, not the R packages.

## Files

- `probes/rda_reader.py` - minimal reader for R `.rda` (RDX2/RDX3, XDR; gzip/bzip2/xz).
- `probes/smath.py` - digamma, trigamma, regularized incomplete gamma, normal CDF, Nelder-Mead.
- `probes/probe_openebgm.py` - processRaw/squashData/negLLsquash/.reinInTheta/Qn/ebgm/quantBisect port.
- `probes/probe_empirical_calibration.py` - fitNull/calibrateP/EASE/systematic-error-model/CI port.
- `probes/probe_reference_sets.py` - row counts of the MethodEvaluation reference sets.
- `probes/probe_disproportionality.py` - PRR/ROR/chi-square/BCPNN/shrinkage-IC signal sets.
- `outputs/*.txt` - outputs recorded on 2026-11-20.
