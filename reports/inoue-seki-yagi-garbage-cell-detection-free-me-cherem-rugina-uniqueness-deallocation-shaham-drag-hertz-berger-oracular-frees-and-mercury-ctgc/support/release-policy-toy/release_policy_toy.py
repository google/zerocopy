#!/usr/bin/env python3
"""Toy release-policy simulator (a model, not a measurement of any real runtime).

A program is abstracted as a trace of per-object events on a logical clock:
  alloc time a, last-use time u (u >= a), unreachable time r (r >= u),
  lexical scope-exit time s (s >= u), and size in bytes.
Release policies:
  liveness oracle      frees at u (earliest safe point; cf. lifetime-based oracle)
  reachability oracle  frees at r (latest point an explicit free could name it)
  scope exit           frees at s (stack/region-style static release)
  tracing GC(period P) frees at the first collection time >= r, collections every P ticks
Reported per policy: peak retained bytes, retained byte-ticks (integral), mean drag
(release time - last use). Usage: release_policy_toy.py
"""
import math

def simulate(objs, policy, period=None):
    events = []
    for o in objs:
        if policy == 'liveness':
            f = o['u']
        elif policy == 'reachability':
            f = o['r']
        elif policy == 'scope':
            f = o['s']
        elif policy == 'gc':
            f = math.ceil(o['r'] / period) * period
        events.append((o['a'], o['size'])); events.append((f, -o['size']))
        o.setdefault('_rel', {})[policy if policy != 'gc' else f'gc{period}'] = f
    events.sort(key=lambda e: (e[0], 0 if e[1] > 0 else 1))   # allocs before frees at equal time
    live = peak = 0; last_t = 0; integral = 0
    for t, d in events:
        integral += live * (t - last_t); last_t = t
        live += d; peak = max(peak, live)
    key = policy if policy != 'gc' else f'gc{period}'
    drag = sum(o['_rel'][key] - o['u'] for o in objs) / len(objs)
    return peak, integral, drag

def list_traverse(n=1000, node=32, hold=2000):
    """Build an n-node list (one node per tick), traverse it once (node i last used at
    n+i), keep the head reachable until scope exit at 2n+hold (then all nodes die)."""
    objs = []
    for i in range(n):
        u = n + i
        end = 2 * n + hold
        objs.append(dict(a=i, u=u, r=end, s=end, size=node))
    return objs

def temp_per_iteration(n=1000, size=64):
    """A loop allocating a temporary each tick that dies at the end of the iteration;
    its scope is the whole function (declared outside the loop), lasting until 2n."""
    return [dict(a=i, u=i, r=i + 1, s=2 * n, size=size) for i in range(n)]

for name, gen in [('list traverse then hold', list_traverse), ('loop temporary, function-scoped', temp_per_iteration)]:
    print(f'== {name}')
    for pol, per in [('liveness', None), ('reachability', None), ('scope', None), ('gc', 100), ('gc', 1000)]:
        objs = gen()
        pk, integ, drag = simulate(objs, pol, per)
        label = pol if per is None else f'gc every {per}'
        print(f'   {label:20s} peak_bytes={pk:7d} byte_ticks={integ:10d} mean_drag_ticks={drag:8.1f}')
