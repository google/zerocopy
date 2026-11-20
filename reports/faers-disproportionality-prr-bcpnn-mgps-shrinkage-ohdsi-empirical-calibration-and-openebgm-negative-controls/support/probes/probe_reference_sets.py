#!/usr/bin/env python3
"""Composition of the reference sets shipped with OHDSI/MethodEvaluation@d7305910...
(data/omopReferenceSet.rda, data/euadrReferenceSet.rda, data/ohdsiNegativeControls.rda).

Basis: execution (independent .rda reader; counts the rows R would load).

Usage: python3 probe_reference_sets.py omopReferenceSet.rda euadrReferenceSet.rda ohdsiNegativeControls.rda
"""
import sys
from collections import Counter

from rda_reader import as_columns, read_rda


def main(omop, euadr, ohdsi):
    for path, name in ((omop, "omopReferenceSet"), (euadr, "euadrReferenceSet")):
        c = as_columns(read_rda(path)[name])
        gt = [int(float(g)) for g in c["groundTruth"]]
        print(f"{name}: rows={len(gt)} positives={sum(gt)} negatives={len(gt) - sum(gt)}"
              f" distinct exposures={len(set(c['exposureId']))} distinct outcomes={len(set(c['outcomeName']))}")
        tab = Counter((o, g) for o, g in zip(c["outcomeName"], gt))
        for o in sorted(set(c["outcomeName"])):
            print(f"   {o}: positive={tab[(o, 1)]} negative={tab[(o, 0)]}")
    c = as_columns(read_rda(ohdsi)["ohdsiNegativeControls"])
    print(f"ohdsiNegativeControls: rows={len(c['targetId'])}")
    print("   by target:", dict(Counter(c["targetName"])))
    print("   by outcome-of-interest nesting:", dict(Counter(c["nestingName"])))
    print("   by type:", dict(Counter(c["type"])))


if __name__ == "__main__":
    main(*sys.argv[1:4])
