"""Restore the historical baseline's declared provenance prefix; never run a subject."""
from pathlib import Path
import argparse,hashlib,json
from packet_schema import packet

ROOT=Path(__file__).resolve().parents[1]
TOKEN='<MAY1_TOOLCHAIN>'
def sha(data):return hashlib.sha256(data).hexdigest()
def token_fields(value,path=()):
    if isinstance(value,dict):
        for key,child in value.items():yield from token_fields(child,path+(key,))
    elif isinstance(value,list):
        for index,child in enumerate(value):yield from token_fields(child,path+(index,))
    elif isinstance(value,str) and TOKEN in value:
        if path[-2:] not in [('origin','span'),('origin','call_site')]:
            raise ValueError('token outside the declared provenance fields')
        if value!=TOKEN+'/lib/rustlib/src/rust/library/core/src/ptr/mod.rs:809:1: 811:25':
            raise ValueError('unexpected projected provenance value')
        yield list(path)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--toolchain',required=True);parser.add_argument('--output',required=True)
    args=parser.parse_args();prefix=str(Path(args.toolchain).resolve()).encode()
    receipts=json.loads((ROOT/'projection-receipts.json').read_text())
    replacement=next(row for row in receipts['replacements'] if row['public']==TOKEN)
    if sha(prefix)!=replacement['original_prefix_sha256']:
        raise ValueError('historical prefix identity differs; produce a fresh local capture instead')
    raw=(ROOT/'support/baseline-candidate.json').read_bytes();value=json.loads(raw);packet(value)
    fields=list(token_fields(value))
    if len(fields)!=8:raise ValueError('expected exactly eight provenance fields')
    restored=raw.replace(TOKEN.encode(),prefix)
    expected=json.loads((ROOT/'evidence-summary.json').read_text())['baseline_packet_sha256']
    if sha(restored)!=expected:raise ValueError('restored packet differs from actual accepted baseline bytes')
    with Path(args.output).open('xb') as stream:stream.write(restored)
    print(json.dumps({'status':'restored','sha256':sha(restored),'fields':fields,'meaning':'Exact historical data restoration; no acceptance or compiler execution.'}))

if __name__=='__main__':main()
