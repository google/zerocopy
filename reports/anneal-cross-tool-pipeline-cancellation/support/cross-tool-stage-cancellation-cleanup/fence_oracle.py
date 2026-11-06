#!/usr/bin/env python3
"""Synthetic generation fence using actual CLI retry-inventory digests as payloads."""
import argparse,hashlib,json,os
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESULT=HERE/'results.json';OUT=HERE/'fence-results.json'
def sha_bytes(b):return hashlib.sha256(b).hexdigest()
def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args()
    work=args.work.resolve();assert not work.exists(),'choose absent owned work path';work.mkdir()
    source=json.loads(RESULT.read_text());pointer=work/'CURRENT.json';events=[]
    for stage in source['stages']:
        label=stage['stage'];payload=sha_bytes(canonical(stage['retry']['output_after']))
        # Two generations are deliberately active in sequence. A completed
        # response from cancelled generation 1 is offered after generation 2
        # becomes current and must be rejected before any pointer write.
        current={'stage':label,'generation':2,'payload_sha256':None}
        tmp=work/'current.tmp';tmp.write_bytes(canonical(current));os.replace(tmp,pointer)
        old_before=sha_bytes(pointer.read_bytes())
        late={'stage':label,'generation':1,'payload_sha256':payload}
        accepted=late['generation']==json.loads(pointer.read_text())['generation']
        if accepted:
            tmp.write_bytes(canonical(late));os.replace(tmp,pointer)
        old_after=sha_bytes(pointer.read_bytes())
        assert not accepted and old_before==old_after
        fresh={'stage':label,'generation':2,'payload_sha256':payload}
        accepted=fresh['generation']==json.loads(pointer.read_text())['generation']
        if accepted:
            tmp.write_bytes(canonical(fresh));os.replace(tmp,pointer)
        assert accepted and json.loads(pointer.read_text())==fresh
        events.append({'stage':label,'late_generation':1,'current_generation':2,'late_rejected':True,
                       'pointer_unchanged_after_late':old_before==old_after,
                       'fresh_accepted':True,'payload_sha256':payload,'final_pointer_sha256':sha_bytes(pointer.read_bytes())})
    result={'model_only':True,'input_results_sha256':sha_bytes(RESULT.read_bytes()),
            'events':events,'atomic_pointer_method':'write temporary JSON and os.replace',
            'final_pointer':json.loads(pointer.read_text())}
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('synthetic fences',len(events),'late rejects',sum(x['late_rejected'] for x in events))

if __name__=='__main__':main()
