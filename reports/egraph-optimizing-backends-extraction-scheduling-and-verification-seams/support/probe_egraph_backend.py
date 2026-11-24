import time, random
from functools import lru_cache

print("=== PROBE A: Deterministic AC E-Graph Saturation vs Bounded Fanout ===")

def saturate_ac(n, enode_limit=None, match_limit=None, timeout_s=2.0):
    uf = {}
    def find(x):
        while uf[x] != x:
            uf[x] = uf[uf[x]]
            x = uf[x]
        return x
    nodes_by_class = {}
    hashcons = {}
    next_id = 0
    def new_class():
        nonlocal next_id
        cid = next_id
        next_id += 1
        uf[cid] = cid
        nodes_by_class[cid] = set()
        return cid
    def add_node(op, c1=None, c2=None):
        key = (op, -1, -1) if c1 is None else (op, find(c1), find(c2))
        if key in hashcons:
            return find(hashcons[key])
        c = new_class()
        nodes_by_class[c].add(key)
        hashcons[key] = c
        return c
    def union(a, b):
        ra, rb = find(a), find(b)
        if ra == rb:
            return ra
        if ra > rb:
            ra, rb = rb, ra
        uf[rb] = ra
        nodes_by_class[ra] |= nodes_by_class[rb]
        del nodes_by_class[rb]
        return ra
    def rebuild():
        while True:
            merged = []
            new_hc = {}
            for r in sorted(nodes_by_class.keys()):
                if r not in nodes_by_class:
                    continue
                canon_ns = sorted({(op, -1, -1) if c1 == -1 else (op, find(c1), find(c2)) for op, c1, c2 in nodes_by_class[r]})
                if enode_limit is not None and len(canon_ns) > enode_limit:
                    canon_ns = canon_ns[:enode_limit]
                nodes_by_class[r] = set(canon_ns)
                for k in canon_ns:
                    if k in new_hc and find(new_hc[k]) != find(r):
                        merged.append((r, new_hc[k]))
                    else:
                        new_hc[k] = find(r)
            if not merged:
                hashcons.clear()
                hashcons.update(new_hc)
                break
            for a, b in merged:
                union(a, b)

    leaves = [add_node(f"x{i}") for i in range(n)]
    root = leaves[0]
    for lf in leaves[1:]:
        root = add_node("+", root, lf)

    iters = 0
    t0 = time.perf_counter()
    hit_timeout = False
    while True:
        iters += 1
        unions = []
        adds = []
        snapshot = {r: sorted(ns) for r, ns in sorted(nodes_by_class.items())}
        for r, ns in snapshot.items():
            if enode_limit is not None and len(ns) >= enode_limit:
                continue
            matches = 0
            for op, a, b in ns:
                if op != "+":
                    continue
                if match_limit is not None and matches >= match_limit:
                    break
                adds.append((r, ("+", b, a)))
                matches += 1
                for op2, x, y in snapshot.get(find(a), []):
                    if op2 == "+":
                        if match_limit is not None and matches >= match_limit:
                            break
                        adds.append((r, ("+", x, ("INNER", y, b))))
                        matches += 1
                for op2, x, y in snapshot.get(find(b), []):
                    if op2 == "+":
                        if match_limit is not None and matches >= match_limit:
                            break
                        adds.append((r, ("+", ("INNER", a, x), y)))
                        matches += 1
        before = (len(nodes_by_class), sum(len(ns) for ns in nodes_by_class.values()))
        for r, node in adds:
            if time.perf_counter() - t0 > timeout_s:
                hit_timeout = True
                break
            r_cur = find(r)
            if enode_limit is not None and len(nodes_by_class[r_cur]) >= enode_limit:
                continue
            op, a, b = node
            if isinstance(a, tuple):
                a = add_node("+", a[1], a[2])
            if isinstance(b, tuple):
                b = add_node("+", b[1], b[2])
            c_new = add_node(op, a, b)
            unions.append((r_cur, c_new))
        for a, b in unions:
            union(a, b)
        rebuild()
        after = (len(nodes_by_class), sum(len(ns) for ns in nodes_by_class.values()))
        dt = time.perf_counter() - t0
        if hit_timeout or dt > timeout_s:
            return len(nodes_by_class), sum(len(ns) for ns in nodes_by_class.values()), iters, dt, True
        if after == before or iters >= 20:
            max_ec = max(len(ns) for ns in nodes_by_class.values())
            return len(nodes_by_class), sum(len(ns) for ns in nodes_by_class.values()), iters, dt, False, max_ec

for n in range(2, 8):
    ec, en, it, dt, to, max_ec = saturate_ac(n, timeout_s=2.0)
    ec_c, en_c, it_c, dt_c, to_c, max_c = saturate_ac(n, enode_limit=5, match_limit=5, timeout_s=2.0)
    print(f"n={n}: full_AC=(eclasses={ec}, enodes={en}, max_ec={max_ec}, iters={it}, {dt*1000:.2f}ms) | cap5=(eclasses={ec_c}, enodes={en_c}, max_ec={max_c}, iters={it_c}, {dt_c*1000:.2f}ms)")

print("\n=== PROBE B: Schedule- vs Cost-Driven Extraction & Live-Register Peak ===")
class Node:
    def __init__(self, nid, op, args, cost):
        self.nid = nid
        self.op = op
        self.args = args
        self.cost = cost

def eval_nodes(nodes, root, env):
    memo = {}
    def go(u):
        if u in memo:
            return memo[u]
        nd = nodes[u]
        if nd.op == "in":
            v = env[nd.nid]
        elif nd.op == "add":
            v = (go(nd.args[0]) + go(nd.args[1])) & 0xffffffff
        elif nd.op == "mul":
            v = (go(nd.args[0]) * go(nd.args[1])) & 0xffffffff
        elif nd.op == "xor":
            v = go(nd.args[0]) ^ go(nd.args[1])
        else:
            raise ValueError(nd.op)
        memo[u] = v
        return v
    return go(root)

def sim_peak(node_map, order):
    rem = {u: 0 for u in node_map}
    for nd in node_map.values():
        for a in nd.args:
            rem[a] += 1
    live = set()
    peak = 0
    for u in order:
        for a in node_map[u].args:
            if not node_map[a].args and a not in live:
                live.add(a)
                peak = max(peak, len(live))
        live.add(u)
        peak = max(peak, len(live))
        for a in node_map[u].args:
            rem[a] -= 1
            if rem[a] == 0 and a in live:
                live.remove(a)
    return peak

def exact_min_peak(node_map):
    non_leaves = [u for u, nd in node_map.items() if nd.args]
    if len(non_leaves) > 18:
        return None
    idx_map = {u: i for i, u in enumerate(non_leaves)}
    n_nl = len(non_leaves)
    pred_mask = [0] * n_nl
    for i, u in enumerate(non_leaves):
        for a in node_map[u].args:
            if node_map[a].args:
                pred_mask[i] |= (1 << idx_map[a])
    all_nodes = list(node_map.keys())
    consumers_of = {u: [v for v in non_leaves if u in node_map[v].args] for u in all_nodes}

    @lru_cache(None)
    def dp(done_mask):
        if done_mask == (1 << n_nl) - 1:
            return 0
        live_set = set()
        for u in all_nodes:
            cs = consumers_of[u]
            if not cs:
                continue
            used_done = any((done_mask >> idx_map[v]) & 1 for v in cs)
            used_rem = any(not ((done_mask >> idx_map[v]) & 1) for v in cs)
            if node_map[u].args:
                if ((done_mask >> idx_map[u]) & 1) and used_rem:
                    live_set.add(u)
            elif used_done and used_rem:
                live_set.add(u)
        best_p = 10**9
        for i, u in enumerate(non_leaves):
            if not ((done_mask >> i) & 1) and (pred_mask[i] & done_mask) == pred_mask[i]:
                step_live = set(live_set)
                for a in node_map[u].args:
                    step_live.add(a)
                step_peak = len(step_live | {u})
                best_p = min(best_p, max(step_peak, dp(done_mask | (1 << i))))
        return best_p
    return dp(0)

def probe_w(W):
    dag_nodes = {}
    nid = 0
    xs = []
    for i in range(W):
        dag_nodes[nid] = Node(nid, "in", (), 0)
        xs.append(nid)
        nid += 1
    ss, s_pairs = [], []
    for i in range(W):
        a = nid; dag_nodes[a] = Node(a, "add", (xs[i], xs[(i+1)%W]), 1); nid += 1
        b = nid; dag_nodes[b] = Node(b, "mul", (a, xs[i]), 3); nid += 1
        ss.append(b)
        s_pairs.append((a, b))
    acc1 = ss[0]
    a1_nodes = []
    for i in range(1, W):
        c = nid; dag_nodes[c] = Node(c, "add", (acc1, ss[i]), 1); nid += 1
        a1_nodes.append(c)
        acc1 = c
    acc2 = ss[0]
    a2_nodes = []
    for i in range(1, W):
        c = nid; dag_nodes[c] = Node(c, "xor", (acc2, ss[i]), 1); nid += 1
        a2_nodes.append(c)
        acc2 = c
    dag_root = nid; dag_nodes[dag_root] = Node(dag_root, "add", (acc1, acc2), 1); nid += 1
    dag_ops = sum(nd.cost for nd in dag_nodes.values())

    dfs_order, vis = [], set()
    def dfs(u):
        if u in vis or not dag_nodes[u].args:
            return
        vis.add(u)
        for a in dag_nodes[u].args:
            dfs(a)
        dfs_order.append(u)
    dfs(dag_root)
    dfs_peak = sim_peak(dag_nodes, dfs_order)

    inter_order = [s_pairs[0][0], s_pairs[0][1]]
    for idx in range(W - 1):
        inter_order.extend([s_pairs[idx+1][0], s_pairs[idx+1][1], a1_nodes[idx], a2_nodes[idx]])
    inter_order.append(dag_root)
    inter_peak = sim_peak(dag_nodes, inter_order)
    dag_exact_opt = exact_min_peak(dag_nodes)

    tree_nodes = {}
    tid = [0]
    txs = []
    for i in range(W):
        tree_nodes[tid[0]] = Node(tid[0], "in", (), 0)
        txs.append(tid[0])
        tid[0] += 1
    def emit_chain(op_comb):
        cur = None
        for i in range(W):
            a = tid[0]; tree_nodes[a] = Node(a, "add", (txs[i], txs[(i+1)%W]), 1); tid[0] += 1
            b = tid[0]; tree_nodes[b] = Node(b, "mul", (a, txs[i]), 3); tid[0] += 1
            if cur is None:
                cur = b
            else:
                c = tid[0]; tree_nodes[c] = Node(c, op_comb, (cur, b), 1); tid[0] += 1
                cur = c
        return cur
    r1 = emit_chain("add")
    r2 = emit_chain("xor")
    tree_root = tid[0]; tree_nodes[tree_root] = Node(tree_root, "add", (r1, r2), 1); tid[0] += 1
    tree_ops = sum(nd.cost for nd in tree_nodes.values())

    rng = random.Random(42 + W)
    for _ in range(100):
        vals = [rng.randrange(1 << 32) for _ in range(W)]
        assert eval_nodes(dag_nodes, dag_root, {xs[i]: vals[i] for i in range(W)}) == \
               eval_nodes(tree_nodes, tree_root, {txs[i]: vals[i] for i in range(W)})

    print(f"W={W}: DAG_ops={dag_ops}, DFS_DAG_peak={dfs_peak}, Interleaved_DAG_peak={inter_peak}, ExactOpt_DAG_peak={dag_exact_opt} | RematTree_ops={tree_ops} [100/100 equiv]")

for W in [3, 4, 6, 8]:
    probe_w(W)
