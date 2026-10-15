"""Closed data grammar for this observer version; no Rust semantics theorem."""
import json

class Rejected(ValueError): pass
def need(ok,message):
    if not ok:raise Rejected(message)
def fields(v,keys):need(type(v) is dict and set(v)==set(keys.split()),'unknown/missing object field')
def string(v):need(type(v) is str and len(v)<=262144,'invalid/oversized string')
def integer(v):need(type(v) is int and 0<=v<2**32,'invalid integer')
def boolean(v):need(type(v) is bool,'invalid Boolean')
def array(v,bound=512):need(type(v) is list and len(v)<=bound,'invalid/oversized array')
def nullable_string(v):
    if v is not None:string(v)

def load(path):
    def pairs(items):
        out={}
        for key,value in items:
            need(key not in out,'duplicate JSON key');out[key]=value
        return out
    data=path.read_bytes();need(len(data)<=4*1024**2,'packet/request too large')
    try:return json.loads(data,object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(Rejected('nonfinite JSON number')))
    except (UnicodeError,json.JSONDecodeError,RecursionError) as e:raise Rejected('malformed JSON') from e

def origin(v):
    fields(v,'span call_site expansion');string(v['span']);string(v['call_site']);array(v['expansion'],32)
    for e in v['expansion']:
        fields(e,'kind call_site definition_site macro_definition')
        for value in e.values():string(value)

def body(v,template):
    fields(v,'argument_count spread_argument is_polymorphic phase locals blocks required_constants origin')
    integer(v['argument_count']);boolean(v['is_polymorphic']);string(v['phase']);origin(v['origin'])
    if v['spread_argument'] is not None:integer(v['spread_argument'])
    array(v['locals'],128);array(v['blocks'],128);array(v['required_constants'])
    need(v['locals'] and v['blocks'],'empty MIR locals/blocks')
    nl=len(v['locals']);nb=len(v['blocks']);refs=set()
    for index,d in enumerate(v['locals']):
        fields(d,'id type mutability layout');need(d['id']==index and type(d['id']) is int,'noncanonical local ids');string(d['type']);string(d['mutability'])
        if template:need(d['layout'] is None,'template claims instantiated layout')
        else:
            fields(d['layout'],'size_bytes align_bytes backend_representation');integer(d['layout']['size_bytes']);integer(d['layout']['align_bytes']);need(d['layout']['align_bytes']>0,'zero alignment');string(d['layout']['backend_representation'])
    need(v['argument_count']<nl,'argument count exceeds locals')
    def local(x):integer(x);need(x<nl,'invalid local reference')
    def target(x):integer(x);need(x<nb,'invalid block target')
    def place(p):
        fields(p,'local projection');local(p['local']);array(p['projection'],16)
        for e in p['projection']:
            need(type(e) is dict,'projection object')
            if e.get('kind')=='deref':fields(e,'kind')
            elif e.get('kind')=='field':fields(e,'kind index type');integer(e['index']);string(e['type'])
            else:raise Rejected('unsupported projection constructor')
    def dependency(kind,value):
        if template:need(value is None,'template has resolved dependency')
        else:string(value);need(value,'empty instance id');refs.add((kind,value))
    def operand(o):
        need(type(o) is dict,'operand object');kind=o.get('kind')
        if kind in ['copy','move']:fields(o,'kind place');place(o['place'])
        elif kind=='function':
            fields(o,'kind definition arguments');string(o['definition']);string(o['arguments'])
        elif kind=='constant':
            fields(o,'kind type compiler_value evaluated_bits dependency');string(o['type']);string(o['compiler_value']);nullable_string(o['evaluated_bits'])
            if o['evaluated_bits'] is not None:need(o['evaluated_bits'].isdigit() and len(o['evaluated_bits'])<=40,'invalid scalar bit encoding')
            if o['dependency'] is not None:dependency('constant',o['dependency'])
            if template:need(o['evaluated_bits'] is None and o['dependency'] is None,'template evaluated constant')
        else:raise Rejected('unsupported operand constructor')
    def rvalue(r):
        need(type(r) is dict,'rvalue object');kind=r.get('kind')
        if kind=='use':fields(r,'kind operand');operand(r['operand'])
        elif kind=='reference':fields(r,'kind region borrow_kind place');string(r['region']);string(r['borrow_kind']);place(r['place'])
        elif kind=='raw_address':fields(r,'kind pointer_kind place');string(r['pointer_kind']);place(r['place'])
        elif kind=='binary':
            fields(r,'kind operator left right');need(r['operator'] in ['BitXor','BitAnd','BitOr','Eq','Ne'],'unsupported operator');operand(r['left']);operand(r['right'])
        elif kind=='unary':fields(r,'kind operator operand');need(r['operator']=='Not','unsupported unary');operand(r['operand'])
        elif kind=='aggregate':
            fields(r,'kind aggregate_kind operands closure_dependency');string(r['aggregate_kind']);array(r['operands'],128)
            for o in r['operands']:operand(o)
            if r['closure_dependency'] is not None:dependency('closure-construction',r['closure_dependency'])
        elif kind=='integer_cast':fields(r,'kind operand target_type');operand(r['operand']);string(r['target_type'])
        elif kind=='copy_for_deref':fields(r,'kind place');place(r['place'])
        else:raise Rejected('unsupported rvalue constructor')
    for index,bb in enumerate(v['blocks']):
        fields(bb,'id cleanup statements terminator origin');need(type(bb['id']) is int and bb['id']==index,'noncanonical block ids');boolean(bb['cleanup']);origin(bb['origin']);array(bb['statements'])
        for s in bb['statements']:
            fields(s,'operation origin');origin(s['origin']);op=s['operation'];need(type(op) is dict,'statement object');kind=op.get('kind')
            if kind=='assign':fields(op,'kind destination value');place(op['destination']);rvalue(op['value'])
            elif kind in ['storage_live','storage_dead']:fields(op,'kind local');local(op['local'])
            elif kind=='nop':fields(op,'kind')
            else:raise Rejected('unsupported statement constructor')
        t=bb['terminator'];need(type(t) is dict,'terminator object');kind=t.get('kind')
        if kind in ['return','unreachable','unwind_resume']:fields(t,'kind')
        elif kind=='unwind_terminate':fields(t,'kind reason');string(t['reason'])
        elif kind=='goto':fields(t,'kind target');target(t['target'])
        elif kind=='switch':
            fields(t,'kind operand cases otherwise');operand(t['operand']);array(t['cases']);target(t['otherwise']);values=set()
            for case in t['cases']:
                fields(case,'value target');string(case['value']);need(case['value'].isdigit() and case['value'] not in values,'invalid/repeated switch value');values.add(case['value']);target(case['target'])
        elif kind=='call':
            fields(t,'kind function resolved_instance arguments destination target unwind');operand(t['function']);array(t['arguments'],128)
            for a in t['arguments']:operand(a)
            place(t['destination']);dependency('call',t['resolved_instance']);string(t['unwind'])
            if t['target'] is not None:target(t['target'])
        elif kind=='drop':
            fields(t,'kind place type resolved_instance target unwind replace drop_block');place(t['place']);string(t['type']);target(t['target']);string(t['unwind']);boolean(t['replace']);dependency('drop',t['resolved_instance'])
            if t['drop_block'] is not None:target(t['drop_block'])
        else:raise Rejected('unsupported terminator constructor')
    for o in v['required_constants']:operand(o)
    return refs

def semantic(v):
    fields(v,'schema root crate_name effective_cfg language_features target codegen_target_cpu codegen_target_features additional_file_inputs environment_inputs sources local_definitions local_body_templates instances edges external_crate_metadata trust_frontier')
    need(v['schema']=='owned-configured-capture-v1','unsupported capture schema')
    for key in ['root','crate_name','target','codegen_target_cpu','codegen_target_features','trust_frontier']:string(v[key])
    for key in ['effective_cfg','language_features','additional_file_inputs','environment_inputs']:
        array(v[key],256)
        for x in v[key]:string(x)
    need(not v['language_features'] and not v['additional_file_inputs'] and not v['environment_inputs'],'unsupported feature/file/environment dependency')
    array(v['sources'],4);names=set()
    for s in v['sources']:
        fields(s,'name compiler_source');string(s['name']);string(s['compiler_source']);need(s['name'] not in names,'duplicate source');names.add(s['name'])
    array(v['local_definitions'],256);definition_ids=set();paths=set()
    for d in v['local_definitions']:
        fields(d,'id path kind parent origin hir')
        for key in ['id','path','kind','parent','hir']:string(d[key])
        need(d['id'] not in definition_ids,'duplicate local definition');definition_ids.add(d['id']);paths.add(d['path']);origin(d['origin'])
    array(v['local_body_templates'],128);templates=set()
    for t in v['local_body_templates']:
        fields(t,'definition kind query_origin body');string(t['definition']);string(t['kind']);string(t['query_origin']);need(t['definition'] in paths and t['definition'] not in templates,'template owner missing/repeated');templates.add(t['definition']);body(t['body'],True)
    array(v['instances'],64);need(v['instances'],'empty instance closure');ids=set();wanted=set()
    for i in v['instances']:
        fields(i,'id definition kind arguments query_origin body')
        for key in ['id','definition','kind','arguments','query_origin']:string(i[key])
        need(i['id'] not in ids,'duplicate instance');ids.add(i['id'])
        need(i['definition'] in paths or i['kind'].startswith(('DropGlue(','ClosureOnceShim ')),'unowned/external instance')
        for kind,target in body(i['body'],False):wanted.add((i['id'],kind,target))
    need(sum(i['definition']==v['root'] and i['arguments']=='[]' for i in v['instances'])==1,'missing/ambiguous selected root')
    array(v['edges'],256);edges=set()
    for e in v['edges']:
        fields(e,'from kind to');need(e['from'] in ids and e['to'] in ids and e['kind'] in ['call','drop','constant','closure-construction'],'dangling/unknown dependency');need((e['from'],e['kind'],e['to']) not in edges,'duplicate dependency');edges.add((e['from'],e['kind'],e['to']))
    need(edges==wanted,'missing/extra semantic dependency edge')
    array(v['external_crate_metadata'],8)
    for e in v['external_crate_metadata']:fields(e,'name crate_hash');string(e['name']);string(e['crate_hash'])

def packet(v):
    fields(v,'schema request semantic');need(v['schema']=='owned-bound-capture-v1','unsupported packet schema');need(type(v['request']) is dict,'request object');semantic(v['semantic'])
