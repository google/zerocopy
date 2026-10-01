#!/usr/bin/env python3
"""Extract claim-relevant HIR owners, selected-file spans, and MIR forms."""
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent
ROLES=('old','new')
CASES=('neither','feature','custom','both')
OWNER=re.compile(r'DefId\(0:\d+ ~ cfg_probe\[[^]]+\](?:::(.*?))?\) => OwnerNodes')
MIR_FN=re.compile(r'^fn (\w+)\(',re.M)
SWITCH=re.compile(r'_1 = const (true|false);')
VALUE_BODY=re.compile(r'^fn value\(\) -> u32 \{(.*?)^\}',re.M|re.S)
VALUE_CONST=re.compile(r'_0 = const (\d+)_u32;')

def derive():
    cells={}
    for role in ROLES:
        for case in CASES:
            hir=(ROOT/'raw'/role/f'{case}--hir.stdout').read_text()
            mir=(ROOT/'raw'/role/f'{case}.mir').read_text()
            value_body=VALUE_BODY.search(mir)
            assert value_body is not None
            value_constants=VALUE_CONST.findall(value_body.group(1))
            assert len(value_constants)==1
            cells[f'{role}/{case}']={
                'hir_owners':OWNER.findall(hir),
                'selected_a_source_spans':len(re.findall(r'(?:inner_span|span): fixture/selected_a\.rs',hir)),
                'selected_b_source_spans':len(re.findall(r'(?:inner_span|span): fixture/selected_b\.rs',hir)),
                'mir_functions':MIR_FN.findall(mir),
                'selected_value_constant':int(value_constants[0]),
                'cfg_control_boolean':SWITCH.findall(mir),
                'mir_has_both_cfg_control_arms':all(s in mir for s in ('_0 = const 70_u32;', '_0 = const 80_u32;')),
            }
    return {'schema':1,'cells':cells}

if __name__=='__main__':
    x=derive();(ROOT/'analysis.json').write_text(json.dumps(x,indent=2)+'\n')
    print('derived',len(x['cells']),'HIR/MIR pairs')
