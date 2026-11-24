use std::cmp::Reverse;
use std::collections::BinaryHeap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge {
    pub src: usize,
    pub dst: usize,
    pub w: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph {
    pub n: usize,
    pub edges: Vec<Edge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SsspWitness {
    pub dist: Vec<Option<u64>>,
    pub parent: Vec<Option<usize>>,
    pub rank: Vec<u32>,
}

pub type SsspInput = (Graph, usize);
pub type SsspCandidate = (Vec<Option<u64>>, SsspWitness);

/// Deterministic O((V + E) log V) Dijkstra fast-path producer returning (distances, witness).
pub fn dijkstra_producer(input: &SsspInput) -> Option<SsspCandidate> {
    let (graph, src) = input;
    let n = graph.n;
    if *src >= n {
        return None;
    }
    let mut adj: Vec<Vec<(usize, u64)>> = vec![Vec::new(); n];
    for e in &graph.edges {
        if e.src >= n || e.dst >= n {
            return None;
        }
        adj[e.src].push((e.dst, e.w));
    }

    let mut dist: Vec<Option<u64>> = vec![None; n];
    let mut parent: Vec<Option<usize>> = vec![None; n];
    let mut rank: Vec<u32> = vec![0; n];
    let mut heap: BinaryHeap<Reverse<(u64, u32, usize)>> = BinaryHeap::new();

    dist[*src] = Some(0);
    heap.push(Reverse((0, 0, *src)));

    while let Some(Reverse((d, r, u))) = heap.pop() {
        if dist[u] != Some(d) || rank[u] != r {
            continue;
        }
        for &(v, w) in &adj[u] {
            let nd = d.checked_add(w)?;
            let nr = r.checked_add(1)?;
            let improve = match dist[v] {
                None => true,
                Some(old) => nd < old || (nd == old && nr < rank[v]),
            };
            if improve {
                dist[v] = Some(nd);
                parent[v] = Some(u);
                rank[v] = nr;
                heap.push(Reverse((nd, nr, v)));
            }
        }
    }

    let out_dist = dist.clone();
    Some((
        out_dist,
        SsspWitness {
            dist,
            parent,
            rank,
        },
    ))
}

/// Linear O(V + E) checker matching HybridSsspChecker.lean's verified invariants:
/// 1. `out.0 == witness.dist`, `dist[src] == Some(0)`, `rank[src] == 0`.
/// 2. Triangle optimality on all edges (`dist[dst] <= dist[src] + w`, overflow-checked).
/// 3. For every reachable `v != src`, `parent[v] = Some(u)` has `rank[u] < rank[v]` and
///    an edge `(u, v, w)` in `graph` justifying `dist[u] + w == dist[v]`.
pub fn check_sssp_witness(input: &SsspInput, cand: &SsspCandidate) -> bool {
    let (graph, src) = input;
    let n = graph.n;
    let (out_dist, w) = cand;
    if *src >= n
        || out_dist.len() != n
        || w.dist.len() != n
        || w.parent.len() != n
        || w.rank.len() != n
        || out_dist != &w.dist
    {
        return false;
    }
    if w.dist[*src] != Some(0) || w.rank[*src] != 0 {
        return false;
    }

    // Build reverse-witness lookup table in O(V + E) so parent validation stays O(V + E)
    // instead of rescanning `edges` per vertex.
    let mut needs_parent: Vec<Option<(usize, u64)>> = vec![None; n];
    for v in 0..n {
        if let Some(dv) = w.dist[v] {
            if v == *src {
                continue;
            }
            let Some(u) = w.parent[v] else {
                return false;
            };
            if u >= n || w.rank[u] >= w.rank[v] {
                return false;
            }
            let Some(du) = w.dist[u] else {
                return false;
            };
            if dv < du {
                return false;
            }
            needs_parent[v] = Some((u, dv - du));
        }
    }

    let mut parent_matched = vec![false; n];
    for e in &graph.edges {
        if e.src >= n || e.dst >= n {
            return false;
        }
        if let Some(du) = w.dist[e.src] {
            let Some(bound) = du.checked_add(e.w) else {
                return false;
            };
            match w.dist[e.dst] {
                None => return false,
                Some(dv) => {
                    if dv > bound {
                        return false;
                    }
                }
            }
        }
        if let Some((req_u, req_w)) = needs_parent[e.dst] {
            if e.src == req_u && e.w == req_w {
                parent_matched[e.dst] = true;
            }
        }
    }

    for v in 0..n {
        if needs_parent[v].is_some() && !parent_matched[v] {
            return false;
        }
    }
    true
}

/// Simple textbook Bellman-Ford O(V * E) slow fallback producer.
pub fn bellman_ford_fallback(input: &SsspInput) -> SsspCandidate {
    let (graph, src) = input;
    let n = graph.n;
    let mut dist: Vec<Option<u64>> = vec![None; n];
    let mut parent: Vec<Option<usize>> = vec![None; n];
    let mut rank: Vec<u32> = vec![0; n];
    dist[*src] = Some(0);

    for _ in 0..n {
        let mut changed = false;
        for e in &graph.edges {
            if let Some(du) = dist[e.src] {
                if let Some(nd) = du.checked_add(e.w) {
                    let nr = rank[e.src].saturating_add(1);
                    let improve = match dist[e.dst] {
                        None => true,
                        Some(old) => nd < old || (nd == old && nr < rank[e.dst]),
                    };
                    if improve {
                        dist[e.dst] = Some(nd);
                        parent[e.dst] = Some(e.src);
                        rank[e.dst] = nr;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let out_dist = dist.clone();
    (
        out_dist,
        SsspWitness {
            dist,
            parent,
            rank,
        },
    )
}

pub fn mutant_zero_cycle(input: &SsspInput) -> Option<SsspCandidate> {
    let mut cand = dijkstra_producer(input)?;
    if input.0.n >= 3 {
        cand.1.parent[1] = Some(2);
        cand.1.parent[2] = Some(1);
        cand.1.rank[1] = 1;
        cand.1.rank[2] = 1;
    }
    Some(cand)
}

pub fn mutant_suboptimal_dist(input: &SsspInput) -> Option<SsspCandidate> {
    let mut cand = dijkstra_producer(input)?;
    let (_, src) = input;
    if let Some((idx, d)) = cand
        .0
        .iter_mut()
        .enumerate()
        .rev()
        .find(|(i, v)| *i != *src && v.is_some())
    {
        if let Some(val) = d {
            *val = val.saturating_add(1);
            cand.1.dist[idx] = Some(*val);
        }
    }
    Some(cand)
}

pub fn mutant_drop_reachable(input: &SsspInput) -> Option<SsspCandidate> {
    let mut cand = dijkstra_producer(input)?;
    let (_, src) = input;
    if let Some((idx, d)) = cand
        .0
        .iter_mut()
        .enumerate()
        .rev()
        .find(|(i, v)| *i != *src && v.is_some())
    {
        *d = None;
        cand.1.dist[idx] = None;
    }
    Some(cand)
}

pub fn mutant_panic(_input: &SsspInput) -> Option<SsspCandidate> {
    panic!("simulated bug in untrusted fast solver");
}

/// Deterministic synthetic directed positive-weight graph generator for scaling benchmarks.
pub fn build_layered_graph(n: usize, avg_deg: usize) -> Graph {
    let mut edges = Vec::with_capacity(n * avg_deg);
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next_u64 = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        state
    };
    for u in 0..n {
        if u + 1 < n {
            edges.push(Edge {
                src: u,
                dst: u + 1,
                w: (next_u64() % 17) + 1,
            });
        }
        for _ in 1..avg_deg {
            let v = (next_u64() as usize) % n;
            let w = (next_u64() % 64) + 1;
            edges.push(Edge { src: u, dst: v, w });
        }
    }
    Graph { n, edges }
}

/// High-diameter chain with reverse-ordered edges (forcing O(V) Bellman-Ford rounds).
pub fn build_reverse_chain_graph(n: usize) -> Graph {
    let mut edges = Vec::with_capacity(n * 2);
    // Add chord edges first, then reverse-ordered spine edges (n-2->n-1 down to 0->1)
    for u in 0..n.saturating_sub(2) {
        edges.push(Edge {
            src: u,
            dst: u + 2,
            w: 100,
        });
    }
    for u in (0..n.saturating_sub(1)).rev() {
        edges.push(Edge {
            src: u,
            dst: u + 1,
            w: 3,
        });
    }
    Graph { n, edges }
}
