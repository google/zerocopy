import json, subprocess, sys, urllib.request
def tree(repo, sha, path):
    # resolve the tree object for `path` at commit `sha`, then list it recursively
    out = subprocess.run(['gh','api',f'repos/{repo}/contents/{path}?ref={sha}'],capture_output=True,text=True,check=True)
    parent = path.rsplit('/',1)[0] if '/' in path else ''
    name = path.rsplit('/',1)[-1]
    lst = json.loads(subprocess.run(['gh','api',f'repos/{repo}/contents/{parent}?ref={sha}'],capture_output=True,text=True,check=True).stdout)
    tsha = [e['sha'] for e in lst if e['name']==name][0]
    t = json.loads(subprocess.run(['gh','api',f'repos/{repo}/git/trees/{tsha}?recursive=1'],capture_output=True,text=True,check=True).stdout)
    return [e for e in t['tree'] if e['type']=='blob']
def lines(repo, sha, path, files, exts):
    tot_l = tot_b = n = 0
    for e in files:
        if not any(e['path'].endswith(x) for x in exts): continue
        url = f'https://raw.githubusercontent.com/{repo}/{sha}/{path}/{e["path"]}'
        data = urllib.request.urlopen(urllib.request.Request(url, headers={'User-Agent':'research-bot'})).read()
        tot_l += data.count(b'\n'); tot_b += len(data); n += 1
    return n, tot_l, tot_b
for repo, sha, path, exts in [
    ('isabelle-prover/mirror-afp-devel','523cdc72b5ae4a91c9ab8e1025d4a30b40472720','thys/Partial_Order_Reduction',['.thy']),
    ('isabelle-prover/mirror-afp-devel','523cdc72b5ae4a91c9ab8e1025d4a30b40472720','thys/Stuttering_Equivalence',['.thy']),
    ('isabelle-prover/mirror-afp-devel','523cdc72b5ae4a91c9ab8e1025d4a30b40472720','thys/CAVA_LTL_Modelchecker/SM',['.thy']),
    ('microsoft/Armada','da7497dcf506417df1899ac58850706a31e3acd5','Armada/strategies/reduction',['.dfy']),
    ('microsoft/Ironclad','2fe4dcdc323b92e93f759cc3e373521366b7f691','ironfleet/src/Dafny/Distributed/Common/Framework',['.s.dfy']),
    ('microsoft/Ironclad','2fe4dcdc323b92e93f759cc3e373521366b7f691','ironfleet/src/Dafny/Distributed/Protocol/RSL/LivenessProof',['.dfy']),
    ('boogie-org/boogie','99eebd60b8fc42c0ad3c95b6160ad88ac4f124dc','Source/Concurrency',['.cs']),
]:
    files = tree(repo, sha, path)
    n, l, b = lines(repo, sha, path, files, exts)
    print(f'{repo}@{sha[:12]} {path} ({",".join(exts)}): {n} files, {l} lines, {b} bytes')
