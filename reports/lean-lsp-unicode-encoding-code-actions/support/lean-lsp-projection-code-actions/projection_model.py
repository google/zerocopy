#!/usr/bin/env python3
"""Illustrative source-map edit model; not an Anneal projector."""
import hashlib,json,random,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUT=HERE/'projection-stream.json'
SEED=373013

def digest(text):return hashlib.sha256(text.encode()).hexdigest()

def build(source):
    pieces=['-- synthetic header\n'];segments=[];sp=0;gp=len(pieces[0])
    for i,line in enumerate(source.splitlines(keepends=True)):
        pieces.append(line)
        segments.append({'source':[sp,sp+len(line)],'generated':[gp,gp+len(line)],'owner':'authored','line':i})
        sp+=len(line);gp+=len(line)
        suffix=f'-- synthetic obligation {i}\n';pieces.append(suffix);gp+=len(suffix)
    return ''.join(pieces),segments

def utf16_col_to_index(line,col):
    units=0
    for i,ch in enumerate(line):
        if units==col:return i
        units+=2 if ord(ch)>0xffff else 1
        if units>col:raise ValueError('split UTF-16 surrogate pair')
    if units==col:return len(line)
    raise ValueError('column beyond line')

def project_edit(source,generated,segments,version,request_version,start,end,replacement):
    if request_version!=version:raise ValueError('stale generation')
    owning=[s for s in segments if s['generated'][0]<=start<=end<=s['generated'][1]]
    if len(owning)!=1:raise ValueError('synthetic or cross-segment range')
    s=owning[0];a=s['source'][0]+start-s['generated'][0];b=a+(end-start)
    if generated[start:end]!=source[a:b]:raise ValueError('source-map byte mismatch')
    return source[:a]+replacement+source[b:]

def main():
    rng=random.Random(SEED)
    source=''.join(f'-- authored {i:02d} α 😀 token_{i:02d}\n' for i in range(64))
    version=1;events=[];build_ns=0;edit_ns=0
    for step in range(500):
        t=time.perf_counter_ns();generated,segments=build(source);build_ns+=time.perf_counter_ns()-t
        segment=segments[rng.randrange(len(segments))]
        start=segment['generated'][0]+rng.randrange(segment['generated'][1]-segment['generated'][0])
        end=min(start+rng.randrange(0,4),segment['generated'][1])
        replacement=rng.choice(['β','😀','xyz',''])
        t=time.perf_counter_ns();new_source=project_edit(source,generated,segments,version,version,start,end,replacement);edit_ns+=time.perf_counter_ns()-t
        events.append({'step':step,'version':version,'source_sha256':digest(source),'generated_sha256':digest(generated),
                       'generated_range':[start,end],'replacement':replacement,'new_source_sha256':digest(new_source)})
        source=new_source;version+=1
        if step%25==0:
            rejected=[]
            for name,kwargs in [('stale',{'request_version':version-2,'start':start,'end':end}),
                                ('synthetic',{'request_version':version,'start':0,'end':2}),
                                ('cross-segment',{'request_version':version,'start':segments[0]['generated'][1]-1,'end':segments[1]['generated'][0]+1})]:
                current,seg=build(source)
                try:project_edit(source,current,seg,version,kwargs['request_version'],kwargs['start'],kwargs['end'],'x')
                except ValueError as exc:rejected.append({'kind':name,'reason':str(exc)})
            assert len(rejected)==3
            events[-1]['rejections']=rejected
    examples={}
    for string in ['😀αx','a🦀b','α😀β']:
        examples[string]={'utf16_unit_length':len(string.encode('utf-16-le'))//2,
                          'valid':{},'invalid':{}}
        for col in range(len(string.encode('utf-16-le'))//2+2):
            try:examples[string]['valid'][str(col)]=utf16_col_to_index(string,col)
            except ValueError as exc:examples[string]['invalid'][str(col)]=str(exc)
    assert examples['😀αx']['invalid']['1']=='split UTF-16 surrogate pair'
    result={'model_only':True,'seed':SEED,'initial_lines':64,'edits':500,'events':events,
            'final_version':version,'final_source_sha256':digest(source),
            'timing_ns':{'full_build_total':build_ns,'edit_projection_total':edit_ns},
            'utf16_examples':examples}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print('model edits',len(events),'rejection checkpoints',sum('rejections' in x for x in events),
          'full build ms',round(build_ns/1e6,2),'project ms',round(edit_ns/1e6,2))

if __name__=='__main__':main()
