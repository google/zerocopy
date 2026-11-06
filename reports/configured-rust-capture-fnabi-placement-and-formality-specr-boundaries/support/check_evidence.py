"""Static package/data audit only: no compiler, native execution, network or writes."""
from pathlib import Path,PurePosixPath
import hashlib,json,tarfile
from packet_schema import packet
from restore_baseline import token_fields
ROOT=Path(__file__).resolve().parents[1]
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def js(path):return json.loads(path.read_text())

def main():
    summary=js(ROOT/'evidence-summary.json');receipts=js(ROOT/'projection-receipts.json');archive_entries={};files={}
    with tarfile.open(ROOT/'support/observations.tar.gz','r:gz') as archive:
        total=0
        for m in archive:
            p=PurePosixPath(m.name);need(m.isfile() and not p.is_absolute() and '..' not in p.parts and m.name not in archive_entries,'unsafe/duplicate archive member')
            total+=m.size;need(total<=64*1024**2,'archive expansion bound');archive_entries[m.name]=archive.extractfile(m).read()
    need(len(archive_entries)==summary['archive_regular_files']==409,'archive member count')
    need(sha((ROOT/'support/observations.tar.gz').read_bytes())==summary['archive_sha256'],'archive identity')
    for row in receipts['files']:
        data=archive_entries[row['public_archive_entry']] if 'public_archive_entry' in row else (ROOT/row['public_file']).read_bytes()
        need(len(data)==row['public_bytes'] and sha(data)==row['public_sha256'],'projection bytes')
        need((row['raw_sha256']==row['public_sha256'])==(not row['substitutions']),'undeclared projection')
    def archive_json(name):return json.loads(archive_entries[name])
    matrix=archive_json('matrix/control-results.json');need(len(matrix['controls'])==34 and matrix['all_expected_statuses_match'],'matrix size')
    counts={};compiler_counts={};packet_count=0
    for row in matrix['controls']:
        need(row['exit']==row['expected_exit'] and row['exit'] in [0,2],'control status')
        actual=archive_json('matrix/controls/'+row['label']+'/verdict.json');need(actual==row['verdict'],'verdict capture')
        counts[actual['status']]=counts.get(actual['status'],0)+1
        for name,digest in row['implementation_sha256'].items():need(sha((ROOT/'support'/name).read_bytes())==digest,'final implementation changed '+name)
        status='matrix/controls/'+row['label']+'/compiler-status.json'
        if status in archive_entries:
            code=archive_json(status)['exit'];compiler_counts[code]=compiler_counts.get(code,0)+1
        capture='matrix/controls/'+row['label']+'/independent-capture.json'
        if capture in archive_entries:packet(archive_json(capture));packet_count+=1
    need(counts=={'captured':5,'accepted':6,'rejected':23},'verdict counts')
    need(compiler_counts=={0:22,65:5},'compiler status counts')
    baseline=js(ROOT/'support/baseline-candidate.json');packet(baseline)
    need(baseline==archive_json('baseline-production/independent-capture.json')==archive_json('baseline-consumer/independent-capture.json'),'baseline producer/consumer equality')
    baseline_receipt=next(row for row in receipts['files'] if row.get('public_file')=='support/baseline-candidate.json')
    need(baseline_receipt['raw_sha256']==summary['baseline_packet_sha256'],'raw baseline packet identity')
    need(sha((ROOT/'support/baseline-candidate.json').read_bytes())==summary['baseline_public_display_sha256']==baseline_receipt['public_sha256'],'public baseline display identity')
    need(len(list(token_fields(baseline)))==8,'declared baseline provenance projection')
    native=archive_json('native/results.json');need(len(native['observations'])==5 and len(native['commands'])==15,'native case/command count')
    expected={'baseline':lambda x:4,'flip':lambda x:7,'changed-body':lambda x:1,'changed-instance':lambda x:3,'decoy':lambda x:x^9}
    for row in native['observations']:
        need(row['inputs']==256 and row['outputs']==[expected[row['case']](x) for x in range(256)],'native all-u8 result')
    need(all(row['exit']==0 for row in native['commands']),'native status')
    if (ROOT/'package-manifest.json').exists():
        manifest=js(ROOT/'package-manifest.json')
        for row in manifest['files']:
            data=(ROOT/row['path']).read_bytes();need(len(data)==row['bytes'] and sha(data)==row['sha256'],'manifest bytes '+row['path'])
    print(json.dumps({'status':'PASS','archive_files':len(archive_entries),'matrix_calls':34,'compiler_invocations':27,'complete_capture_packets_checked':packet_count+3,'native_inputs':1280,'meaning':'Static integrity/schema/status reconciliation; not a compiler replay or source-safety theorem.'}))

if __name__=='__main__':main()
