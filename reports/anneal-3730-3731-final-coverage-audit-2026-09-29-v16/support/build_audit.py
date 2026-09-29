#!/usr/bin/env python3
"""Deterministically rebuild the v16 row ledgers from frozen issue and row review."""
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
ROOT=PACKAGE.parents[1]
REPORTS=ROOT/'reports'
V15=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-29-v15'/'support'
sys.path.insert(0,str(ROOT/'tools'))
import reference

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def load_json(name):return json.loads((HERE/name).read_text())
def read_csv(path):
    with Path(path).open(newline='') as file:return list(csv.DictReader(file))
def write_csv(path,rows,fields):
    with path.open('w',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=fields,lineterminator='\n',extrasaction='ignore')
        writer.writeheader();writer.writerows(rows)
def normal(row):
    if 'exact_reason' in row:
        package=row.get('new_local_report_package')
        return row['classification'],row['exact_reason'],[package] if package else []
    package=row.get('new_package')
    return row['disposition'],row['disposition_reason'],[package] if package else []

snapshot=load_json('issue-scope-snapshot.json')
live=load_json('live-issue-hashes.json')
for number in (3730,3731):
    old=snapshot[str(number)];new=live['issues'][str(number)]
    assert old['state']==new['state']
    assert hashlib.sha256(old['body'].encode()).hexdigest()==new['body_sha256']
    assert len(old['comments'])==len(new['comments'])==1
    for a,b in zip(old['comments'],new['comments']):
        assert hashlib.sha256(a['body'].encode()).hexdigest()==b['body_sha256']
issue_3730=set(re.findall(r'(?m)^### ([A-O]\d{2})\.',snapshot['3730']['body']))
assert len(issue_3730)==174
issue_3731=set(re.findall(r'\bI\d{3}\b',snapshot['3731']['body']+'\n'+'\n'.join(x['body'] for x in snapshot['3731']['comments'])))
assert issue_3731=={f'I{i:03d}' for i in range(1,160)}

parts=[load_json(name) for name in ('part-a.json','part-b.json','part-c.json')]
reviews={}
for part in parts:
    source=part.get('rows') or part.get('investigations',[])+part.get('suggestions',[])
    for row in source:
        assert row['id'] not in reviews,row['id']
        reviews[row['id']]=row
assert len(reviews)==318,len(reviews)

investigations=read_csv(V15/'investigation-final-v15.csv')
suggestions=read_csv(V15/'3730-crosswalk-final-v15.csv')
assert len(investigations)==159 and len(suggestions)==174
assert {r['id'] for r in investigations}==issue_3731
assert {r['3730_id'] for r in suggestions}==issue_3730
new_package_names=set()
for row in investigations:
    item=reviews.get(row['id'])
    if item:
        classification,reason,packages=normal(item)
        assert item['specific_remaining_delta']==row['specific_remaining_delta']
        assert item['v15_status']==row['status']
    else:
        classification='carried_'+row['status']
        reason=row['specific_remaining_delta'] or 'No further delta at the exact narrow completed scope.'
        packages=[]
        assert row['status'] in ('complete','not-run','conditional')
    if row['id']=='I120':packages=sorted(set(packages+['anneal-3730-pruned-lake-interactive-extension-v4-30-0-rc2']))
    row['v16_disposition']=classification
    row['v16_specific_remaining_delta']=reason
    row['v16_experiment_packages']=';'.join(packages)
    row['v16_evidence_scope_and_limit']=reason
    row['v16_evidence_files']=';'.join(f'reports/{p}/REPORT.md' for p in packages)
    new_package_names.update(packages)
invest_by_id={row['id']:row for row in investigations}
for row in suggestions:
    key=row['3730_id']
    item=reviews.get(key)
    if item:
        classification,reason,packages=normal(item)
        assert item['specific_remaining_delta']==row['specific_remaining_delta']
        assert item['v15_status']==row['status']
    else:
        classification='carried_'+row['status']
        reason=row['specific_remaining_delta'] or 'No further delta at the exact narrow completed scope.'
        packages=[]
        assert row['status'] in ('complete','not-run','conditional')
    destinations=[x for x in row['3731_destinations'].split(';') if x]
    assert set(destinations)<=issue_3731
    for destination in destinations:
        packages+=list(filter(None,invest_by_id[destination]['v16_experiment_packages'].split(';')))
    packages=sorted(set(packages))
    row['v16_disposition']=classification
    row['v16_specific_remaining_delta']=reason
    row['v16_experiment_packages']=';'.join(packages)
    row['v16_evidence_scope_and_limit']=reason
    row['v16_evidence_files']=';'.join(f'reports/{p}/REPORT.md' for p in packages)
    new_package_names.update(packages)

assert set(reviews)<={r['id'] for r in investigations}|{r['3730_id'] for r in suggestions}
assert len(new_package_names)>=10
for package in sorted(new_package_names):
    assert (REPORTS/package/'REPORT.md').is_file(),package
    assert (REPORTS/package/'REPORT.json').is_file(),package
    report,problems=reference._load_report(REPORTS/package)
    assert report and not problems,(package,problems)

write_csv(HERE/'investigation-final-v16.csv',investigations,list(investigations[0]))
write_csv(HERE/'3730-crosswalk-final-v16.csv',suggestions,list(suggestions[0]))

package_rows=[];file_rows=[]
for package in sorted(new_package_names):
    base=REPORTS/package
    files=sorted(path for path in base.rglob('*') if path.is_file())
    package_rows.append({'package':package,'files':len(files),
                         'report_sha256':sha(base/'REPORT.md'),
                         'metadata_sha256':sha(base/'REPORT.json'),
                         'offline_checker':str((base/'support/check.py').is_file())})
    for path in files:
        file_rows.append({'package':package,'relative_path':str(path.relative_to(base)),
                          'bytes':path.stat().st_size,'sha256':sha(path)})
write_csv(HERE/'new-package-review-v16.csv',package_rows,['package','files','report_sha256','metadata_sha256','offline_checker'])
write_csv(HERE/'new-file-inventory-v16.csv',file_rows,['package','relative_path','bytes','sha256'])

from collections import Counter
counts={'investigations':dict(Counter(row['status'] for row in investigations)),
        'suggestions':dict(Counter(row['status'] for row in suggestions))}
assert counts['investigations']=={'complete':2,'partial':153,'not-run':1,'conditional':3},counts
assert counts['suggestions']=={'complete':4,'partial':161,'not-run':5,'conditional':4},counts
validation={'reference_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
            'live_fetched_at_utc':live['fetched_at_utc'],'issue_hashes':live['issues'],
            'issue_3730_heading_count':len(issue_3730),'issue_3731_id_count':len(issue_3731),
            'reviewed_noncomplete_rows':len(reviews),'status_counts':counts,
            'new_package_count':len(new_package_names),'new_packages':sorted(new_package_names),
            'file_inventory_rows':len(file_rows),'new_package_loaders_passed':True,
            'generated_sha256':{name:sha(HERE/name) for name in ('investigation-final-v16.csv','3730-crosswalk-final-v16.csv','new-package-review-v16.csv','new-file-inventory-v16.csv')}}
(HERE/'validation-v16.json').write_text(json.dumps(validation,indent=2,sort_keys=True)+'\n')
print(json.dumps({'reference_commit':validation['reference_commit'],'counts':counts,'reviewed_rows':len(reviews),
                  'new_packages':len(new_package_names),'new_files':len(file_rows)},sort_keys=True))
