#!/usr/bin/env python3
"""Look up each cited DOI in the Crossref REST API and print a summary line.

Usage: python3 verify_dois.py > doi_verification.txt
Network access to https://api.crossref.org is required.  A DOI is reported
"ok" when Crossref returns a work record; title/container/year/pages are
printed so a reader can compare them with the citation in REPORT.md.
"""
import json
import sys
import time
import urllib.parse
import urllib.request

DOIS = [
    "10.1006/inco.2000.2930",          # Abramsky-Jagadeesan-Malacaria, PCF
    "10.1006/inco.2000.2917",          # Hyland-Ong, PCF
    "10.1016/S1571-0661(05)80398-6",   # Abramsky-McCusker, IA with active expressions
    "10.1109/LICS.1997.614931",        # Laird, control
    "10.1109/LICS.1998.705669",        # Abramsky-Honda-McCusker, general references
    "10.1007/3-540-57182-5_8",         # Pitts-Stark, nu-calculus
    "10.1561/2500000017",              # Murawski-Tzevelekos, nominal game semantics
    "10.1145/1111037.1111050",         # Koutavas-Wand, small bisimulations
    "10.1145/1863543.1863566",         # Dreyer-Neis-Birkedal, ICFP 2010
    "10.1017/S095679681200024X",       # Dreyer-Neis-Birkedal, JFP 2012
    "10.1007/978-3-030-99527-0_10",    # Koutavas-Lin-Tzevelekos, TACAS 2022 (Hobbit)
    "10.1109/CSF.2011.18",             # Jagadeesan-Pitcher-Rathke-Riely, CSF 2011
    "10.1145/2240276.2240279",         # Abadi-Plotkin, TISSEC 2012
    "10.1109/CSF.2010.30",             # Abadi-Plotkin, CSF 2010
    "10.1145/73560.73577",             # Meyer-Sieber, POPL 1988
    "10.1007/978-3-642-58622-4_1",     # Abramsky-McCusker, Game Semantics (1999)
    "10.1109/LICS.2011.31",            # Murawski-Tzevelekos, LICS 2011
    "10.1007/978-3-642-31585-5_30",    # Murawski-Tzevelekos, ICALP 2012
]


def first(x):
    return x[0] if isinstance(x, list) and x else (x or "")


def main():
    for doi in DOIS:
        url = "https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="/()")
        req = urllib.request.Request(url, headers={"User-Agent": "research-bot"})
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                msg = json.load(resp)["message"]
            year = ""
            for key in ("published-print", "published-online", "issued"):
                parts = msg.get(key, {}).get("date-parts")
                if parts and parts[0] and parts[0][0]:
                    year = str(parts[0][0])
                    break
            print("ok\t%s\t%s\t%s\t%s\tvol=%s\tissue=%s\tpages=%s" % (
                doi, first(msg.get("title")), first(msg.get("container-title")),
                year, msg.get("volume", ""), msg.get("issue", ""), msg.get("page", "")))
        except Exception as e:  # report and continue
            print("FAIL\t%s\t%s" % (doi, e))
        sys.stdout.flush()
        time.sleep(0.5)


if __name__ == "__main__":
    main()
