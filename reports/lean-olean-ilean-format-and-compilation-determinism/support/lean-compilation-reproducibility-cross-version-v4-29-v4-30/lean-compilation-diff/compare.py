"""Normalize a probe run and optionally diff it against a second toolchain run.

Usage: python3 compare.py RUN_ROOT [OTHER_RUN_ROOT]
Raw runs.json, builds.json, lsp-raw.json, and lsp-results.json are never edited.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

def load(root, name):
    return json.loads((root/name).read_text())

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def scrub(s, root):
    s = s.replace(str(root/"project"), "<PROJECT>")
    s = s.replace(str(root/"cache"), "<CACHE>")
    s = re.sub(r"Built (\S+) \(\d+ms\)", r"Built \1 (<TIME>)", s)
    return s

def cli_output(run, root):
    lines = []
    for line in run.get("stdout", "").splitlines():
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            lines.append({"text":scrub(line,root)})
            continue
        if isinstance(value,dict) and "severity" in value:
            lines.append({"diagnostic":{
                "severity":value.get("severity"),"kind":value.get("kind"),
                "position":value.get("pos"),"end":value.get("endPos"),
                "message":scrub(value.get("data", ""),root)}})
        else:
            lines.append({"json":value})
    return {"exit":run.get("exit"),"timeout":run.get("timeout_s"),"lines":lines,
            "stderr":scrub(run.get("stderr",""),root)}

def setup_output(run, root):
    try:
        value=json.loads(run["stdout"])
    except (KeyError,json.JSONDecodeError):
        return {"status":"invalid-or-missing","exit":run.get("exit"),
                "stdout":scrub(run.get("stdout",""),root),"stderr":scrub(run.get("stderr",""),root)}
    imports={}
    for module,paths in value.get("importArts",{}).items():
        imports[module]=[]
        for path in paths:
            p=Path(path)
            imports[module].append({"location":scrub(str(p),root),
                                    "exists_now":p.is_file(),
                                    "sha256_now":digest(p) if p.is_file() else None})
    return {"status":"ok" if run.get("exit")==0 else "error","name":value.get("name"),
            "isModule":value.get("isModule"),"options":value.get("options"),
            "plugins":value.get("plugins"),"dynlibs":value.get("dynlibs"),
            "importArts":imports}

def protocol_value(msg):
    if msg is None:
        return {"status":"missing-response"}
    if "missing_response" in msg:
        return {"status":"missing-response","detail":msg["missing_response"]}
    if "error" in msg:
        error=msg["error"]
        return {"status":"protocol-error","code":error.get("code"),"message":error.get("message")}
    if "result" not in msg:
        return {"status":"malformed-response"}
    return {"status":"ok","result":msg["result"]}

def final_diagnostics(events):
    latest={}
    for event in events:
        if event.get("direction") != "server":continue
        msg=event.get("message",{})
        if msg.get("method") != "textDocument/publishDiagnostics":continue
        params=msg.get("params",{})
        version=params.get("version")
        if version is None:continue
        latest[str(version)]=sorted([{"severity":d.get("severity"),
            "range":d.get("range"),"message":d.get("message")} for d in params.get("diagnostics",[])],
            key=lambda d:(d["severity"] or 0,json.dumps(d["range"],sort_keys=True),d["message"] or ""))
    return latest

def normalize(root):
    root=root.resolve()
    runs=load(root,"runs.json")
    by_name={run["name"]:run for run in runs}
    builds=load(root,"builds.json")
    results=load(root,"lsp-results.json")
    events=load(root,"lsp-raw.json")
    identity=load(root,"identities.json")
    inputs=load(root,"inputs.json")
    out={
      "schema":"anneal-lean-compilation-diff-v1",
      "identity":identity,
      "fixture_sha256":{k:v for k,v in inputs.items() if k!="lean-toolchain"},
      "toolchain_file_sha256":inputs.get("lean-toolchain"),
      "raw_sha256":{n:digest(root/n) for n in ("runs.json","builds.json","lsp-raw.json","lsp-results.json")},
      "builds":{},"lake_cells":{},"lsp":{
        "initialize":protocol_value(results.get("initialize")),
        "final_diagnostics_by_version":final_diagnostics(events),
        "queries":{k:protocol_value(results.get(k)) for k in (
          "wait_v1","goal_v1_before","goal_v1_after","wait_v2","goal_v2_before","goal_v2_after",
          "goal_outside_tactic","unsupported_method")},
        "exception":results.get("exception")}}
    for name,value in builds.items():
        out["builds"][name]={"exit":value["build"].get("exit"),
          "timed_out":bool(value["build"].get("timeout_s")),
          "mode":"fetched" if "Fetched" in value["build"].get("stdout","") else "built",
          "artifacts":value["artifacts"],"cache_files":value["cache_files"]}
    for name,run in by_name.items():
        if name.endswith("-setup") or name=="goal-setup":
            out["lake_cells"][name]=setup_output(run,root)
        elif name.endswith("-batch") or "-batch-" in name:
            out["lake_cells"][name]=cli_output(run,root)
        elif name in ("warm-no-build","materialize-without-cache"):
            out["lake_cells"][name]={"exit":run.get("exit"),"stdout":scrub(run.get("stdout",""),root)}
    return out

def differences(a,b,path=""):
    if isinstance(a,dict) and isinstance(b,dict):
        out=[]
        for key in sorted(set(a)|set(b)):
            out += differences(a.get(key,"<MISSING>"),b.get(key,"<MISSING>"),path+"/"+str(key))
        return out
    if isinstance(a,list) and isinstance(b,list):
        out=[]
        for i in range(max(len(a),len(b))):
            out += differences(a[i] if i<len(a) else "<MISSING>",
                               b[i] if i<len(b) else "<MISSING>",path+"/"+str(i))
        return out
    return [] if a==b else [{"path":path,"left":a,"right":b}]

def behavioral_view(data):
    view={"fixture_sha256":data["fixture_sha256"],"builds":{},"lake_cells":{},"lsp":{}}
    for name,build in data["builds"].items():
        view["builds"][name]={"exit":build["exit"],"timed_out":build["timed_out"],
            "mode":build["mode"],"artifact_paths":sorted(build["artifacts"])}
    for name,cell in data["lake_cells"].items():
        if "importArts" in cell:
            view["lake_cells"][name]={"status":cell["status"],"name":cell["name"],
                "options":cell["options"],"plugins":cell["plugins"],"dynlibs":cell["dynlibs"],
                "imports":{module:[{"storage":"cache" if x["location"].startswith("<CACHE>") else "project",
                                      "exists_now":x["exists_now"]} for x in paths]
                           for module,paths in cell["importArts"].items()}}
        else:
            view["lake_cells"][name]=cell
    init=data["lsp"]["initialize"]
    result=init.get("result") or {}
    rpc=result.get("capabilities",{}).get("experimental",{}).get("rpcProvider",{})
    view["lsp"]={"serverInfo":result.get("serverInfo"),"rpcWireFormat":rpc.get("rpcWireFormat"),
        "final_diagnostics_by_version":data["lsp"]["final_diagnostics_by_version"],
        "queries":data["lsp"]["queries"],"exception":data["lsp"]["exception"]}
    return view

if __name__=="__main__":
    if len(sys.argv) not in (2,3):raise SystemExit(__doc__)
    first=Path(sys.argv[1])
    left=normalize(first)
    (first/"normalized.json").write_text(json.dumps(left,indent=2,ensure_ascii=False)+"\n")
    if len(sys.argv)==3:
        second=Path(sys.argv[2]);right=normalize(second)
        (second/"normalized.json").write_text(json.dumps(right,indent=2,ensure_ascii=False)+"\n")
        result={"fixture_identical":left["fixture_sha256"]==right["fixture_sha256"],
                "behavioral_differences":differences(behavioral_view(left),behavioral_view(right)),
                "full_differences":differences(left,right)}
        (first/"cross-version-diff.json").write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
        print(len(result["behavioral_differences"]),"behavioral differences;",
              len(result["full_differences"]),"full normalized differences")
    else:
        print("normalized one toolchain; second toolchain unavailable")
