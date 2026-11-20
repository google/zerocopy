"""Reference model of Toy.Views used for finite counterexample searches (supporting evidence only)."""
import itertools

EXCL, SHARED = 'x', 's'
# Cell: ('own', d, b) | ('loan', c) ; None = not covered
# View: (parent, mode, active, cells)   cells: tuple indexed by address

def view(s, v):
    return s[v] if 0 <= v < len(s) else None

def cell(s, v, a):
    vw = view(s, v)
    if vw is None: return None
    cs = vw[3]
    return cs[a] if a < len(cs) else None

def covers(s, v, a):
    return cell(s, v, a) is not None

def active(s, v):
    vw = view(s, v)
    return vw is not None and vw[2]

def parent(s, v):
    vw = view(s, v)
    return None if vw is None else vw[0]

def mode(s, v):
    return view(s, v)[1]

def can_read(s, v, a):
    c = cell(s, v, a)
    return active(s, v) and c is not None and c[0] == 'own'

def can_write(s, v, a):
    c = cell(s, v, a)
    return active(s, v) and c is not None and c[0] == 'own' and c[1] == 0

def level(s, v, a):
    return 2 if can_write(s, v, a) else (1 if can_read(s, v, a) else 0)

def proper_desc(s, d, c):
    # d is a proper descendant of c: chain of parents from d reaches c (views must exist)
    seen = set()
    x = d
    while True:
        vw = view(s, x)
        if vw is None or vw[0] is None: return False
        p = vw[0]
        if p == c: return True
        if p in seen: return False
        seen.add(p)
        x = p

def addrs(s):
    m = 0
    for vw in s: m = max(m, len(vw[3]))
    return range(m)

def base(s, v):
    return 1 if mode(s, v) == SHARED else 0

# ---------------- laws -----------------
def parents_exist(s):
    return all(vw[0] is None or vw[0] < len(s) for vw in s)

def parent_lt(s):
    return all(vw[0] is None or vw[0] < i for i, vw in enumerate(s))

def parent_covers_active(s):
    for v, vw in enumerate(s):
        if not vw[2] or vw[0] is None: continue
        p = vw[0]
        for a in addrs(s):
            if covers(s, v, a) and not (active(s, p) and covers(s, p, a)):
                return False
    return True

def loan_targets_child(s):
    for v, vw in enumerate(s):
        if not vw[2]: continue
        for a in addrs(s):
            c = cell(s, v, a)
            if c is not None and c[0] == 'loan':
                t = c[1]
                if view(s, t) is None or parent(s, t) != v or mode(s, t) != EXCL or not covers(s, t, a):
                    return False
    return True

def excl_child_loaned(s):
    for c, vw in enumerate(s):
        if not vw[2] or vw[1] != EXCL or vw[0] is None: continue
        p = vw[0]
        for a in addrs(s):
            if covers(s, c, a) and cell(s, p, a) != ('loan', c):
                return False
    return True

def shared_child_below_own(s):
    for c, vw in enumerate(s):
        if not vw[2] or vw[1] != SHARED or vw[0] is None: continue
        p = vw[0]
        for a in addrs(s):
            if covers(s, c, a):
                pc = cell(s, p, a)
                if pc is None or pc[0] != 'own' or pc[1] < 1:
                    return False
    return True

def shared_children_shared(s):
    for c, vw in enumerate(s):
        if not vw[2] or vw[0] is None: continue
        p = vw[0]
        if view(s, p) is not None and mode(s, p) == SHARED and vw[1] != SHARED:
            return False
    return True

def shared_count(s, v, a):
    return sum(1 for c, vw in enumerate(s) if vw[2] and vw[0] == v and vw[1] == SHARED and covers(s, c, a))

def depth_counts(s):
    for v, vw in enumerate(s):
        if not vw[2]: continue
        for a in addrs(s):
            c = cell(s, v, a)
            if c is not None and c[0] == 'own':
                if c[1] != base(s, v) + shared_count(s, v, a):
                    return False
    return True

def roots_disjoint(s):
    for v in range(len(s)):
        for w in range(len(s)):
            if v == w: continue
            if active(s, v) and active(s, w) and parent(s, v) is None and parent(s, w) is None:
                for a in addrs(s):
                    if covers(s, v, a) and covers(s, w, a): return False
    return True

def write_exclusive(s):
    for a in addrs(s):
        for v in range(len(s)):
            if can_write(s, v, a):
                for w in range(len(s)):
                    if w != v and can_read(s, w, a): return False
    return True

LAWS = {
    'ParentsExist': parents_exist,
    'ParentLt': parent_lt,
    'ParentCoversActive': parent_covers_active,
    'LoanTargetsChild': loan_targets_child,
    'ExclChildLoaned': excl_child_loaned,
    'SharedChildBelowOwn': shared_child_below_own,
    'SharedChildrenShared': shared_children_shared,
    'DepthCounts': depth_counts,
    'RootsDisjoint': roots_disjoint,
}

def return_authority(s, c):
    for d in range(len(s)):
        if active(s, d) and proper_desc(s, d, c):
            for a in addrs(s):
                if covers(s, c, a) and covers(s, d, a): return False
    return True

def return_authority_all(s, c):
    return not any(active(s, d) and proper_desc(s, d, c) for d in range(len(s)))

def naive_authority(s, c):
    """c is active; its parent is active and holds every cell of c as an outstanding loan:
    ('loan', c) for an exclusive child, own at a depth above the parent's baseline for a shared
    child (mirrors NaiveAuthority / returnable)"""
    vw = view(s, c)
    if vw is None or not vw[2] or vw[0] is None: return False
    p = vw[0]
    pv = view(s, p)
    if pv is None or not pv[2]: return False
    for a in addrs(s):
        if covers(s, c, a):
            pc = cell(s, p, a)
            if vw[1] == EXCL:
                if pc != ('loan', c): return False
            else:
                if pc is None or pc[0] != 'own' or pc[1] <= base(s, p): return False
    return True

def local_return_check(s, c):
    """every cell c covers is own at c's baseline depth (mirrors LocalReturnCheck)"""
    for a in addrs(s):
        if covers(s, c, a):
            x = cell(s, c, a)
            if x is None or x[0] != 'own' or x[1] != base(s, c): return False
    return True

def set_view(s, v, vw):
    s = list(s); s[v] = vw; return tuple(s)

def set_cell(cells, a, x):
    cs = list(cells)
    while len(cs) <= a: cs.append(None)
    cs[a] = x
    return tuple(cs)

def end_raw(s, c, r=lambda a: 0):
    vw = view(s, c)
    if vw is None or not vw[2] or vw[0] is None: return None
    p = vw[0]
    pv = view(s, p)
    if pv is None: return None
    if not naive_authority(s, c): return None
    pcells = pv[3]
    for a in addrs(s):
        if covers(s, c, a):
            pc = cell(s, p, a)
            if vw[1] == EXCL:
                pcells = set_cell(pcells, a, ('own', 0, r(a)))
            else:
                pcells = set_cell(pcells, a, ('own', pc[1] - 1, pc[2]))
    s1 = set_view(s, p, (pv[0], pv[1], pv[2], pcells))
    vw1 = view(s1, c)
    s1 = set_view(s1, c, (vw1[0], vw1[1], False, vw1[3]))
    return s1

def no_resurrection(s, s1):
    for u in range(len(s1)):
        for a in addrs(s1):
            if level(s1, u, a) > (level(s, u, a) if u < len(s) else 0):
                for d in range(len(s1)):
                    if active(s1, d) and proper_desc(s1, d, u) and covers(s1, d, a):
                        return False
    return True

# --------------- operations for reachability ---------------
def borrow(s, p, A, b=None):
    if not active(s, p): return None
    if mode(s, p) != EXCL: return None
    pv = view(s, p)
    for a in A:
        pc = cell(s, p, a)
        if pc is None or pc[0] != 'own' or pc[1] != 0: return None
    c = len(s)
    pcells = pv[3]; ccells = ()
    for a in A:
        pc = cell(s, p, a)
        ccells = set_cell(ccells, a, ('own', 0, pc[2]))
        pcells = set_cell(pcells, a, ('loan', c))
    s1 = set_view(s, p, (pv[0], pv[1], pv[2], pcells))
    return s1 + ((p, EXCL, True, ccells),)

def share(s, p, A):
    if not active(s, p): return None
    pv = view(s, p)
    for a in A:
        pc = cell(s, p, a)
        if pc is None or pc[0] != 'own': return None
    c = len(s)
    pcells = pv[3]; ccells = ()
    for a in A:
        pc = cell(s, p, a)
        ccells = set_cell(ccells, a, ('own', 1, pc[2]))
        pcells = set_cell(pcells, a, ('own', pc[1] + 1, pc[2]))
    s1 = set_view(s, p, (pv[0], pv[1], pv[2], pcells))
    return s1 + ((p, SHARED, True, ccells),)

def alloc(s, m, A):
    for v in range(len(s)):
        if active(s, v) and parent(s, v) is None and any(covers(s, v, a) for a in A):
            return None
    cs = ()
    for a in A:
        cs = set_cell(cs, a, ('own', 1 if m == SHARED else 0, 0))
    return s + ((None, m, True, cs),)
