#!/usr/bin/env python3
"""Strict consumer decoder for the captured call-free five-local choose fragment.
No eval/import of producer code. This Python decoder is an explicit trusted frontier.
"""
import argparse, copy, hashlib, json, pathlib, re

HERE = pathlib.Path(__file__).resolve().parent
BOOL = {"Untagged": {"Literal": "Bool"}}
U8 = {"Untagged": {"Literal": {"UInt": "U8"}}}
EMPTY_GENERICS = {k: [] for k in ["regions", "types", "const_generics", "trait_clauses", "regions_outlive", "types_outlive", "trait_type_constraints"]}

def keys(x, expected):
    assert isinstance(x, dict) and set(x) == set(expected), (set(x) if isinstance(x,dict) else x, expected)

def span(x):
    keys(x, ["data", "generated_from_span"])
    assert x["generated_from_span"] is None
    keys(x["data"], ["file_id", "beg", "end"])
    assert x["data"]["file_id"] == 0
    for pos in ["beg", "end"]:
        keys(x["data"][pos], ["line", "col"])
        assert all(type(v) is int and v >= 0 for v in x["data"][pos].values())

def place(x):
    keys(x, ["kind", "ty"]); keys(x["kind"], ["Local"])
    n = x["kind"]["Local"]
    assert type(n) is int and 0 <= n < 5
    assert x["ty"] == ([U8, BOOL, U8, U8, BOOL][n])
    return n

def stmt(x, structured=False):
    keys(x, ["span", "kind", "comments_before"] + (["id"] if structured else []))
    span(x["span"]); assert x["comments_before"] == []
    if structured: assert type(x["id"]) is int and x["id"] >= 0
    k=x["kind"]
    assert isinstance(k,dict) and len(k)==1
    if "StorageLive" in k or "StorageDead" in k:
        op,n=next(iter(k.items())); assert type(n) is int and 0 <= n < 5
        return ["live" if op=="StorageLive" else "dead", n]
    keys(k,["Assign"]); assert len(k["Assign"])==2
    dst,rval=k["Assign"]; d=place(dst); keys(rval,["Use"])
    assert len(rval["Use"])==2 and rval["Use"][1]=="Yes"
    operand=rval["Use"][0];keys(operand,["Copy"]); n=place(operand["Copy"])
    assert dst["ty"]==operand["Copy"]["ty"]
    return ["copy",d,n]

def term(x):
    keys(x,["span","kind","comments_before"]);span(x["span"]);assert x["comments_before"]==[]
    k=x["kind"]
    if k=="Return": return ["ret"]
    assert isinstance(k,dict) and len(k)==1
    if "Goto" in k:
        keys(k["Goto"],["target"]);n=k["Goto"]["target"];assert type(n) is int and 0<=n<4
        return ["jump",n]
    keys(k,["Switch"]);keys(k["Switch"],["discr","targets"])
    keys(k["Switch"]["discr"],["Move"]);n=place(k["Switch"]["discr"]["Move"])
    assert k["Switch"]["discr"]["Move"]["ty"]==BOOL
    keys(k["Switch"]["targets"],["If"]);yes,no=k["Switch"]["targets"]["If"]
    assert all(type(t) is int and 0<=t<4 for t in [yes,no])
    return ["branch",n,yes,no]

def header(fun, variant):
    keys(fun,["def_id","item_meta","generics","signature","src","is_global_initializer","body"])
    assert fun["def_id"]==0 and fun["generics"]==EMPTY_GENERICS and fun["src"]=="TopLevel" and fun["is_global_initializer"] is None
    meta=fun["item_meta"];keys(meta,["name","span","source_text","attr_info","is_local","opacity","lang_item"]);span(meta["span"])
    assert meta["name"]==[{"Ident":["certificate_probe",0]},{"Ident":["choose",0]}]
    assert meta["source_text"]=="pub fn choose(b: bool, x: u8, y: u8) -> u8 { if b { x } else { y } }"
    assert meta["attr_info"]=={"attributes":[],"inline":None,"rename":None,"public":True}
    assert meta["is_local"] is True and meta["opacity"]=="Transparent" and meta["lang_item"] is None
    assert fun["signature"]=={"is_unsafe":False,"abi":"Rust","inputs":[BOOL,U8,U8],"output":U8}
    keys(fun["body"],[variant]);b=fun["body"][variant]
    keys(b,["span","bound_body_regions","locals","body","comments"]);span(b["span"])
    assert b["bound_body_regions"]==0 and b["comments"]==[]
    keys(b["locals"],["arg_count","locals"]);assert b["locals"]["arg_count"]==3
    assert len(b["locals"]["locals"])==5
    for n,l in enumerate(b["locals"]["locals"]):
        keys(l,["index","name","span","ty"]);span(l["span"])
        assert l["index"]==n and l["name"]==[None,"b","x","y",None][n] and l["ty"]==[U8,BOOL,U8,U8,BOOL][n]
    return b["body"]

def unstructured(fun):
    body=header(fun,"Unstructured");assert isinstance(body,list) and len(body)==4
    result=[]
    for block in body:
        keys(block,["statements","terminator"])
        result.append({"ops":[stmt(x) for x in block["statements"]],"term":term(block["terminator"])})
    # Restriction is structural and exhaustive: no hidden exceptional exits/calls/loops.
    assert [b["term"] for b in result][1:]==[["jump",3],["jump",3],["ret"]]
    assert result[0]["term"][0]=="branch" and result[0]["term"][2:]==[1,2]
    return result

def structured(fun):
    body=header(fun,"Structured");keys(body,["span","statements"]);span(body["span"])
    ss=body["statements"];assert len(ss)==5
    pre=[stmt(ss[0],True),stmt(ss[1],True)]
    sw=ss[2];keys(sw,["span","kind","comments_before","id"]);span(sw["span"]);assert sw["comments_before"]==[] and type(sw["id"]) is int
    keys(sw["kind"],["Switch"]);keys(sw["kind"]["Switch"],["If"])
    cond,yes,no=sw["kind"]["Switch"]["If"];keys(cond,["Move"]);n=place(cond["Move"]);assert cond["Move"]["ty"]==BOOL
    branches=[]
    for branch in [yes,no]:
        keys(branch,["span","statements"]);span(branch["span"])
        branches.append([stmt(x,True) for x in branch["statements"]])
    post=[stmt(ss[3],True)]
    ret=ss[4];keys(ret,["span","kind","comments_before","id"]);span(ret["span"])
    assert ret["kind"]=="Return" and ret["comments_before"]==[] and type(ret["id"]) is int
    return {"pre":pre,"condition":n,"yes":branches[0],"no":branches[1],"post":post}

def export(path):
    d=json.loads(path.read_text());keys(d,["charon_version","translated","has_errors"])
    assert d["charon_version"]=="0.1.210" and d["has_errors"] is False
    t=d["translated"]
    keys(t,["crate_name","options","target_information","files","item_names","assoc_item_names","short_names","type_decls","fun_decls","global_decls","trait_decls","trait_impls","ordered_decls"])
    assert t["crate_name"]=="certificate_probe" and len(t["fun_decls"])==2
    assert all(t[k]==[] for k in ["type_decls","global_decls","trait_decls","trait_impls","assoc_item_names"])
    # Nonselected function and opaque driver options are pinned bytes, not semantically certified.
    return d

def fork_from_graph(graph):
    return {"pre":graph[0]["ops"],"condition":graph[0]["term"][1],"yes":graph[1]["ops"],"no":graph[2]["ops"],"post":graph[3]["ops"]}

def selected_pretty(text, marker):
    section=text.split(marker,1)[1]
    start=section.index('pub fn ')
    assert 'choose(' in section[start:section.index('{',start)]
    opening=section.index('{',start);depth=1;i=opening+1
    while depth:
        depth += (section[i]=='{')-(section[i]=='}');i+=1
    full=section[start:i]
    # Only declarations/comments in the exact approved header; body is compared in full.
    lines=[l.strip() for l in full.splitlines()]
    decl=[l for l in lines if l.startswith('let ')]
    assert decl==['let _0: u8; // return','let b_1: bool; // arg #1','let x_2: u8; // arg #2','let y_3: u8; // arg #3','let _4: bool; // anonymous local']
    body=[l for l in lines[2:-1] if l and not l.startswith('let ')]
    return body

def check():
    raw=export(HERE/'raw.sanitized.ullbc');final=export(HERE/'final.sanitized.llbc')
    graph=unstructured(raw['translated']['fun_decls'][0]);fork=structured(final['translated']['fun_decls'][0])
    expected={"pre":[["live",4],["copy",4,1]],"condition":4,"yes":[["copy",0,2]],"no":[["copy",0,3]],"post":[["dead",4]]}
    assert fork_from_graph(graph)==fork==expected
    stdout=(HERE/'aeneas.stdout').read_text();stderr=(HERE/'aeneas.stderr').read_text()
    cfg=['bb0: {','storage_live(_4);','_4 = copy b_1;','if move _4 -> bb1 else -> bb2;','}','bb1: {','_0 = copy x_2;','goto bb3;','}','bb2: {','_0 = copy y_3;','goto bb3;','}','bb3: {','storage_dead(_4);','return;','}']
    assert selected_pretty(stdout,'# ULLBC after translation from MIR:')==cfg
    assert selected_pretty(stdout,'# Final ULLBC before control-flow reconstruction:')==cfg
    structured_lines=['storage_live(_4)','_4 = copy b_1','if move _4 {','_0 = copy x_2','} else {','_0 = copy y_3','}','storage_dead(_4)','return']
    assert selected_pretty(stdout,'# Final LLBC before serialization:')==structured_lines
    built_lines=structured_lines.copy();built_lines.insert(4,'nop');built_lines.insert(7,'nop')
    assert selected_pretty(stderr,'# LLBC resulting from control-flow reconstruction:')==built_lines
    # Discriminating rejection fixtures; no negative is inferred merely from solver failure.
    mutations=[]
    for label,mutate in [
        ('unknown-opcode',lambda f:f['body']['Structured']['body']['statements'][0].update(kind={'Call':[]})),
        ('wrong-local-type',lambda f:f['body']['Structured']['locals']['locals'][4].update(ty=U8)),
        ('missing-storage-dead',lambda f:f['body']['Structured']['body']['statements'].pop(3)),
        ('unknown-semantic-field',lambda f:f['signature'].update(unsafe_extra=True)),
        ('missing-dependency-body',lambda f:f['body'].clear())]:
        mutant=copy.deepcopy(final['translated']['fun_decls'][0]);mutate(mutant)
        try: structured(mutant)
        except (AssertionError,KeyError,ValueError): mutations.append({'case':label,'accepted':False})
        else: raise AssertionError('unsupported mutant accepted:'+label)
    # Changed branch is well-formed, then rejected by exact consumer correspondence/binding.
    mutant=copy.deepcopy(final['translated']['fun_decls'][0]);ss=mutant['body']['Structured']['body']['statements']
    ss[2]['kind']['Switch']['If'][1]['statements'][0]['kind']['Assign'][1]['Use'][0]['Copy']['kind']['Local']=3
    assert structured(mutant)!=fork
    mutations.append({'case':'well-formed-wrong-branch','accepted':False,'reason':'decoded term differs; kernel counterexample retained'})
    manifest=json.loads((HERE/'capture-identities.json').read_text())
    for name,identity in manifest['captured_files'].items():
        assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==identity['preserved_sha256']
    result={'valid':True,'raw_graph':graph,'final_fork':fork,'all_selected_json_fields_validated':True,'mutations':mutations,'trust':'Python JSON/text capture is unverified; endpoint semantics and nop elimination are kernel checked; stage labels are not authenticated provenance'}
    (HERE/'capture-check-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__': check()
