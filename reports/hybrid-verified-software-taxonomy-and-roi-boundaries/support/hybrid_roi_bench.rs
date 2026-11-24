#![forbid(unsafe_code)]

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::hint::black_box;
use std::time::Instant;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn next_usize(&mut self, bound: usize) -> usize {
        (self.next_u64() % (bound as u64)) as usize
    }
}

fn median_ns(samples: &mut [u128]) -> u128 {
    samples.sort_unstable();
    samples[samples.len() / 2]
}

// ============================================================================
// 1. Single-Source Shortest Paths: Dijkstra + Linear Potential Checker vs BF
// ============================================================================

#[derive(Clone, Copy)]
struct Edge {
    to: usize,
    w: u64,
}

fn gen_sparse_graph(n: usize, deg: usize, seed: u64) -> Vec<Vec<Edge>> {
    let mut rng = Rng::new(seed);
    let mut adj = vec![Vec::with_capacity(deg); n];
    // Connected backbone so all nodes reachable from 0
    for u in 0..n.saturating_sub(1) {
        let w = (rng.next_u64() % 50) + 1;
        adj[u].push(Edge { to: u + 1, w });
    }
    for u in 0..n {
        for _ in 0..deg.saturating_sub(1) {
            let v = rng.next_usize(n);
            let w = (rng.next_u64() % 200) + 1;
            adj[u].push(Edge { to: v, w });
        }
    }
    adj
}

fn gen_adversarial_bf_graph(n: usize) -> Vec<Vec<Edge>> {
    // Reverse-indexed shortest path 0 -> n-1 -> n-2 -> ... -> 1 forces
    // standard forward-order Bellman-Ford (0..n-1) to take O(V) full passes!
    let mut adj = vec![Vec::new(); n];
    if n >= 2 {
        adj[0].push(Edge { to: n - 1, w: 1 });
        for u in (2..n).rev() {
            adj[u].push(Edge { to: u - 1, w: 1 });
        }
        // Plus decoy heavy shortcuts from 0
        for v in 1..n - 1 {
            adj[0].push(Edge { to: v, w: (n as u64) * 10 });
        }
    }
    adj
}

fn sssp_dijkstra_producer(adj: &[Vec<Edge>], src: usize) -> (Vec<u64>, Vec<usize>) {
    let n = adj.len();
    let mut dist = vec![u64::MAX; n];
    let mut parent = vec![usize::MAX; n];
    let mut heap = BinaryHeap::new();
    dist[src] = 0;
    parent[src] = src;
    heap.push(Reverse((0u64, src)));
    while let Some(Reverse((d, u))) = heap.pop() {
        if d > dist[u] {
            continue;
        }
        for &e in &adj[u] {
            let nd = d.saturating_add(e.w);
            if nd < dist[e.to] {
                dist[e.to] = nd;
                parent[e.to] = u;
                heap.push(Reverse((nd, e.to)));
            }
        }
    }
    (dist, parent)
}

/// Verified-style O(V + E) potential + acyclic parent-tree witness checker.
/// Positive weights (w >= 1) ensure any parent chain with strictly decreasing
/// dist[v] = dist[p] + w(p, v) is acyclic and reaches src!
fn sssp_check_witness(adj: &[Vec<Edge>], src: usize, dist: &[u64], parent: &[usize]) -> bool {
    let n = adj.len();
    if dist.len() != n || parent.len() != n || src >= n {
        return false;
    }
    if dist[src] != 0 || parent[src] != src {
        return false;
    }
    // 1. Triangle inequality over every edge: dist[v] <= dist[u] + w(u, v)
    for (u, edges) in adj.iter().enumerate() {
        let du = dist[u];
        if du == u64::MAX {
            continue;
        }
        for &e in edges {
            if e.w == 0 || dist[e.to] > du.saturating_add(e.w) {
                return false;
            }
        }
    }
    // 2. Parent witness check for every finite-distance vertex v != src:
    // Verify parent[v] has edge (parent[v] -> v) with dist[v] == dist[parent[v]] + w
    for v in 0..n {
        if v == src || dist[v] == u64::MAX {
            continue;
        }
        let p = parent[v];
        if p >= n || dist[p] == u64::MAX || dist[p] >= dist[v] {
            return false;
        }
        let mut ok = false;
        for &e in &adj[p] {
            if e.to == v && dist[p].saturating_add(e.w) == dist[v] {
                ok = true;
                break;
            }
        }
        if !ok {
            return false;
        }
    }
    true
}

fn sssp_bellman_ford_fallback(adj: &[Vec<Edge>], src: usize) -> Vec<u64> {
    let n = adj.len();
    let mut dist = vec![u64::MAX; n];
    dist[src] = 0;
    for _ in 0..n.saturating_sub(1) {
        let mut changed = false;
        for (u, edges) in adj.iter().enumerate() {
            let du = dist[u];
            if du == u64::MAX {
                continue;
            }
            for &e in edges {
                let nd = du.saturating_add(e.w);
                if nd < dist[e.to] {
                    dist[e.to] = nd;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    dist
}

// ============================================================================
// 2. 3-SAT Planted Solver (DPLL) vs O(clauses) Witness Checker
// ============================================================================

fn gen_planted_3sat(n_vars: usize, n_clauses: usize, seed: u64) -> Vec<[i32; 3]> {
    let mut rng = Rng::new(seed);
    let planted: Vec<bool> = (0..n_vars).map(|_| (rng.next_u64() & 1) == 1).collect();
    let mut clauses = Vec::with_capacity(n_clauses);
    for _ in 0..n_clauses {
        let mut lits = [0i32; 3];
        loop {
            for slot in &mut lits {
                let v = rng.next_usize(n_vars);
                let sign = if (rng.next_u64() & 1) == 1 { 1i32 } else { -1i32 };
                *slot = sign * ((v as i32) + 1);
            }
            let sat_by_planted = lits.iter().any(|&lit| {
                let v = (lit.unsigned_abs() as usize) - 1;
                (lit > 0) == planted[v]
            });
            if sat_by_planted {
                break;
            }
        }
        clauses.push(lits);
    }
    clauses
}

fn dpll_solve(clauses: &[[i32; 3]], assign: &mut [i8]) -> bool {
    // Unit / conflict scan
    let mut all_sat = true;
    let mut next_var = None;
    for &[a, b, c] in clauses {
        let vals = [a, b, c].map(|lit| {
            let v = (lit.unsigned_abs() as usize) - 1;
            let s = assign[v];
            if s == 0 {
                0i8
            } else if (s > 0) == (lit > 0) {
                1
            } else {
                -1
            }
        });
        if vals.contains(&1) {
            continue;
        }
        all_sat = false;
        let unassigned: Vec<(usize, i32)> = [a, b, c]
            .into_iter()
            .filter(|&lit| assign[(lit.unsigned_abs() as usize) - 1] == 0)
            .map(|lit| ((lit.unsigned_abs() as usize) - 1, lit))
            .collect();
        if unassigned.is_empty() {
            return false;
        }
        if unassigned.len() == 1 {
            let (v, lit) = unassigned[0];
            assign[v] = if lit > 0 { 1 } else { -1 };
            let ok = dpll_solve(clauses, assign);
            if !ok {
                assign[v] = 0;
            }
            return ok;
        }
        if next_var.is_none() {
            next_var = Some(unassigned[0].0);
        }
    }
    if all_sat {
        return true;
    }
    if let Some(v) = next_var {
        assign[v] = 1;
        if dpll_solve(clauses, assign) {
            return true;
        }
        assign[v] = -1;
        if dpll_solve(clauses, assign) {
            return true;
        }
        assign[v] = 0;
    }
    false
}

fn sat_check_witness(clauses: &[[i32; 3]], assign: &[i8]) -> bool {
    clauses.iter().all(|&[a, b, c]| {
        [a, b, c].iter().any(|&lit| {
            let v = (lit.unsigned_abs() as usize) - 1;
            v < assign.len() && assign[v] != 0 && ((assign[v] > 0) == (lit > 0))
        })
    })
}

// ============================================================================
// 3. Sorting Permutation Witness vs Insertion Sort Crossover
// ============================================================================

fn sort_with_perm_producer(input: &[u64]) -> (Vec<u64>, Vec<usize>) {
    let mut pairs: Vec<(u64, usize)> = input.iter().copied().enumerate().map(|(i, v)| (v, i)).collect();
    pairs.sort_unstable_by_key(|&(v, _)| v);
    let mut vals = Vec::with_capacity(input.len());
    let mut perm = Vec::with_capacity(input.len());
    for (v, idx) in pairs {
        vals.push(v);
        perm.push(idx);
    }
    (vals, perm)
}

fn sort_check_witness(input: &[u64], sorted: &[u64], perm: &[usize], seen: &mut [u8]) -> bool {
    let n = input.len();
    if sorted.len() != n || perm.len() != n || seen.len() != n {
        return false;
    }
    seen.fill(0);
    for i in 0..n {
        let p = perm[i];
        if p >= n || seen[p] != 0 || sorted[i] != input[p] {
            return false;
        }
        seen[p] = 1;
        if i > 0 && sorted[i - 1] > sorted[i] {
            return false;
        }
    }
    true
}

fn insertion_sort_verified_baseline(input: &[u64]) -> Vec<u64> {
    let mut a = input.to_vec();
    for i in 1..a.len() {
        let key = a[i];
        let mut j = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
    }
    a
}

// ============================================================================
// 4. Matrix Multiply (mod 2^64) + Freivalds k=20 Checker (Break-Even Curve)
// ============================================================================

fn matmul_tiled(a: &[u64], b: &[u64], c: &mut [u64], n: usize) {
    c.fill(0);
    let bs = 32;
    for ii in (0..n).step_by(bs) {
        let i_end = (ii + bs).min(n);
        for kk in (0..n).step_by(bs) {
            let k_end = (kk + bs).min(n);
            for jj in (0..n).step_by(bs) {
                let j_end = (jj + bs).min(n);
                for i in ii..i_end {
                    for k in kk..k_end {
                        let aik = a[i * n + k];
                        let crow = &mut c[i * n..i * n + j_end];
                        let brow = &b[k * n..k * n + j_end];
                        for j in jj..j_end {
                            crow[j] = crow[j].wrapping_add(aik.wrapping_mul(brow[j]));
                        }
                    }
                }
            }
        }
    }
}

fn freivalds_check(a: &[u64], b: &[u64], c: &[u64], n: usize, rounds: usize, seed: u64) -> bool {
    let mut rng = Rng::new(seed);
    let mut r = vec![0u64; n];
    let mut br = vec![0u64; n];
    let mut abr = vec![0u64; n];
    let mut cr = vec![0u64; n];
    for _ in 0..rounds {
        for slot in &mut r {
            *slot = rng.next_u64() & 1;
        }
        // br = B * r
        for i in 0..n {
            let row = &b[i * n..(i + 1) * n];
            let mut acc = 0u64;
            for j in 0..n {
                acc = acc.wrapping_add(row[j].wrapping_mul(r[j]));
            }
            br[i] = acc;
        }
        // abr = A * (B * r), cr = C * r
        for i in 0..n {
            let arow = &a[i * n..(i + 1) * n];
            let crow = &c[i * n..(i + 1) * n];
            let mut acc_ab = 0u64;
            let mut acc_c = 0u64;
            for j in 0..n {
                acc_ab = acc_ab.wrapping_add(arow[j].wrapping_mul(br[j]));
                acc_c = acc_c.wrapping_add(crow[j].wrapping_mul(r[j]));
            }
            abr[i] = acc_ab;
            cr[i] = acc_c;
        }
        if abr != cr {
            return false;
        }
    }
    true
}

// ============================================================================
// 5. LZ77 Greedy Matchfinder + Token-Replay & Kraft Checker
// ============================================================================

#[derive(Clone, Copy)]
struct LzToken {
    lit_len: u16,
    match_len: u16,
    dist: u16,
}

fn lz77_hash_producer(input: &[u8], max_chain: usize) -> (Vec<LzToken>, [u8; 32]) {
    let mut head = vec![usize::MAX; 4096];
    let mut prev = vec![usize::MAX; input.len()];
    let mut tokens = Vec::new();
    let mut pos = 0usize;
    let mut lit_start = 0usize;
    while pos + 4 <= input.len() {
        let h = (((input[pos] as usize) * 31
            ^ (input[pos + 1] as usize) * 131
            ^ (input[pos + 2] as usize) * 523
            ^ (input[pos + 3] as usize) * 1021))
            & 4095;
        let mut cand = head[h];
        prev[pos] = cand;
        head[h] = pos;
        let mut best_len = 3usize;
        let mut best_dist = 0usize;
        let mut steps = 0usize;
        let max_m = (input.len() - pos).min(258);
        while cand != usize::MAX && pos - cand <= 32768 && steps < max_chain {
            let mut mlen = 0usize;
            while mlen < max_m && input[cand + mlen] == input[pos + mlen] {
                mlen += 1;
            }
            if mlen > best_len {
                best_len = mlen;
                best_dist = pos - cand;
                if best_len == max_m {
                    break;
                }
            }
            cand = prev[cand];
            steps += 1;
        }
        if best_len >= 4 {
            let mut rem_lit = pos - lit_start;
            while rem_lit > u16::MAX as usize {
                tokens.push(LzToken { lit_len: u16::MAX, match_len: 0, dist: 0 });
                rem_lit -= u16::MAX as usize;
            }
            tokens.push(LzToken {
                lit_len: rem_lit as u16,
                match_len: best_len as u16,
                dist: best_dist as u16,
            });
            pos += best_len;
            lit_start = pos;
            continue;
        }
        pos += 1;
    }
    let mut rem_lit = input.len() - lit_start;
    while rem_lit > 0 {
        let chunk = rem_lit.min(u16::MAX as usize);
        tokens.push(LzToken { lit_len: chunk as u16, match_len: 0, dist: 0 });
        rem_lit -= chunk;
    }
    // Fixed canonical lengths summing exactly to Kraft = 32768 (32 symbols of length 5)
    let code_lens = [5u8; 32];
    (tokens, code_lens)
}

fn lz77_replay_and_kraft_check(input: &[u8], tokens: &[LzToken], code_lens: &[u8; 32]) -> bool {
    let mut kraft: u32 = 0;
    for &l in code_lens {
        if l == 0 || l > 15 {
            return false;
        }
        kraft += 1u32 << (15 - l);
    }
    if kraft != (1u32 << 15) {
        return false;
    }
    let mut pos = 0usize;
    for &t in tokens {
        let ll = t.lit_len as usize;
        if pos + ll > input.len() {
            return false;
        }
        pos += ll;
        let ml = t.match_len as usize;
        if ml > 0 {
            let d = t.dist as usize;
            if d == 0 || d > pos || pos + ml > input.len() {
                return false;
            }
            // Exact byte-by-byte match verification (supports overlapping RLE matches)
            for k in 0..ml {
                if input[pos + k] != input[pos + k - d] {
                    return false;
                }
            }
            pos += ml;
        }
    }
    pos == input.len()
}

// ============================================================================
// 6. Negative-ROI Probe: Linear Streaming Digest (Unrolled vs Scalar Check)
// ============================================================================

fn fast_unrolled_checksum(data: &[u8]) -> u64 {
    let mut s0 = 0x1234_5678_9abc_def0u64;
    let mut s1 = 0x0fed_cba9_8765_4321u64;
    let mut s2 = 0x5555_5555_5555_5555u64;
    let mut s3 = 0xaaaa_aaaa_aaaa_aaaau64;
    let mut chunks = data.chunks_exact(4);
    for c in &mut chunks {
        s0 = s0.wrapping_mul(0x100000001b3).wrapping_add(c[0] as u64);
        s1 = s1.wrapping_mul(0x100000001b3).wrapping_add(c[1] as u64);
        s2 = s2.wrapping_mul(0x100000001b3).wrapping_add(c[2] as u64);
        s3 = s3.wrapping_mul(0x100000001b3).wrapping_add(c[3] as u64);
    }
    let rem = chunks.remainder();
    let mut tail = 0u64;
    for &b in rem {
        tail = tail.wrapping_mul(131).wrapping_add(b as u64);
    }
    s0 ^ s1.rotate_left(13) ^ s2.rotate_left(29) ^ s3.rotate_left(43) ^ tail
}

fn main() {
    println!("{{");
    // 1. SSSP
    println!("  \"sssp\": [");
    for (idx, &v) in [250usize, 1000, 4000, 16000].iter().enumerate() {
        let adj = gen_sparse_graph(v, 4, 100 + v as u64);
        let reps = if v <= 1000 { 15 } else if v <= 4000 { 7 } else { 5 };
        let mut t_solve = Vec::with_capacity(reps);
        let mut t_check = Vec::with_capacity(reps);
        let mut t_fb = Vec::with_capacity(reps);
        let mut ok_count = 0usize;
        for _ in 0..reps {
            let t0 = Instant::now();
            let (dist, parent) = sssp_dijkstra_producer(black_box(&adj), 0);
            t_solve.push(t0.elapsed().as_nanos());

            let t1 = Instant::now();
            let ok = sssp_check_witness(black_box(&adj), 0, black_box(&dist), black_box(&parent));
            t_check.push(t1.elapsed().as_nanos());
            if ok {
                ok_count += 1;
            }
            if v <= 4000 {
                let t2 = Instant::now();
                let fb = sssp_bellman_ford_fallback(black_box(&adj), 0);
                t_fb.push(t2.elapsed().as_nanos());
                assert_eq!(fb, dist);
            }
        }
        // Negative adversarial control: corrupt one distance
        let (mut bad_dist, parent) = sssp_dijkstra_producer(&adj, 0);
        bad_dist[v - 1] = bad_dist[v - 1].saturating_sub(1);
        assert!(!sssp_check_witness(&adj, 0, &bad_dist, &parent));

        let ms = median_ns(&mut t_solve);
        let mc = median_ns(&mut t_check);
        let mf = if t_fb.is_empty() { 0 } else { median_ns(&mut t_fb) };
        let comma = if idx + 1 < 4 { "," } else { "" };
        println!(
            "    {{\"v\": {}, \"e\": {}, \"solve_ns\": {}, \"check_ns\": {}, \"fallback_ns\": {}, \"check_pct\": {:.2}, \"verified\": {}}}{}",
            v, v * 4 - 1, ms, mc, mf, (mc as f64) * 100.0 / (ms as f64), ok_count == reps, comma
        );
    }
    println!("  ],");

    // 1b. SSSP adversarial worst-case Bellman-Ford graph
    println!("  \"sssp_adv_bf\": [");
    for (idx, &v) in [250usize, 1000, 2500].iter().enumerate() {
        let adj = gen_adversarial_bf_graph(v);
        let reps = if v <= 1000 { 7 } else { 3 };
        let mut t_solve = Vec::with_capacity(reps);
        let mut t_check = Vec::with_capacity(reps);
        let mut t_fb = Vec::with_capacity(reps);
        for _ in 0..reps {
            let t0 = Instant::now();
            let (dist, parent) = sssp_dijkstra_producer(black_box(&adj), 0);
            t_solve.push(t0.elapsed().as_nanos());

            let t1 = Instant::now();
            let ok = sssp_check_witness(black_box(&adj), 0, black_box(&dist), black_box(&parent));
            t_check.push(t1.elapsed().as_nanos());
            assert!(ok);

            let t2 = Instant::now();
            let fb = sssp_bellman_ford_fallback(black_box(&adj), 0);
            t_fb.push(t2.elapsed().as_nanos());
            assert_eq!(fb, dist);
        }
        let ms = median_ns(&mut t_solve);
        let mc = median_ns(&mut t_check);
        let mf = median_ns(&mut t_fb);
        let comma = if idx + 1 < 3 { "," } else { "" };
        println!(
            "    {{\"v\": {}, \"solve_ns\": {}, \"check_ns\": {}, \"fallback_ns\": {}, \"fallback_vs_hybrid_x\": {:.2}}}{}",
            v, ms, mc, mf, (mf as f64) / ((ms + mc) as f64), comma
        );
    }
    println!("  ],");

    // 2. 3-SAT
    println!("  \"sat3\": [");
    for (idx, &nv) in [14usize, 18, 22].iter().enumerate() {
        let nc = (nv * 426) / 100;
        let mut t_solve = Vec::new();
        let mut t_check = Vec::new();
        for inst in 0..15u64 {
            let clauses = gen_planted_3sat(nv, nc, 5000 + inst + (nv as u64) * 100);
            let mut assign = vec![0i8; nv];
            let t0 = Instant::now();
            let found = dpll_solve(black_box(&clauses), &mut assign);
            t_solve.push(t0.elapsed().as_nanos());
            assert!(found);

            let t1 = Instant::now();
            let ok = sat_check_witness(black_box(&clauses), black_box(&assign));
            t_check.push(t1.elapsed().as_nanos());
            assert!(ok);
        }
        let ms = median_ns(&mut t_solve);
        let mc = median_ns(&mut t_check);
        let comma = if idx + 1 < 3 { "," } else { "" };
        println!(
            "    {{\"vars\": {}, \"clauses\": {}, \"solve_ns\": {}, \"check_ns\": {}, \"check_pct\": {:.4}}}{}",
            nv, nc, ms, mc, (mc as f64) * 100.0 / (ms as f64), comma
        );
    }
    println!("  ],");

    // 3. Sorting + Permutation crossover
    println!("  \"sort\": [");
    let sort_sizes = [16usize, 64, 256, 2048, 32768, 262144];
    for (idx, &n) in sort_sizes.iter().enumerate() {
        let mut rng = Rng::new(777 + n as u64);
        let data: Vec<u64> = (0..n).map(|_| rng.next_u64()).collect();
        let reps = if n <= 256 { 200 } else if n <= 2048 { 50 } else { 9 };
        let mut t_raw = Vec::with_capacity(reps);
        let mut t_hyb_prod = Vec::with_capacity(reps);
        let mut t_hyb_chk = Vec::with_capacity(reps);
        let mut t_ins = Vec::with_capacity(reps);
        let mut seen = vec![0u8; n];
        for _ in 0..reps {
            let mut buf = data.clone();
            let t0 = Instant::now();
            buf.sort_unstable();
            black_box(&buf);
            t_raw.push(t0.elapsed().as_nanos());

            let t1 = Instant::now();
            let (sorted, perm) = sort_with_perm_producer(black_box(&data));
            t_hyb_prod.push(t1.elapsed().as_nanos());

            let t2 = Instant::now();
            let ok = sort_check_witness(black_box(&data), black_box(&sorted), black_box(&perm), &mut seen);
            t_hyb_chk.push(t2.elapsed().as_nanos());
            assert!(ok);

            if n <= 2048 {
                let t3 = Instant::now();
                let ins = insertion_sort_verified_baseline(black_box(&data));
                black_box(&ins);
                t_ins.push(t3.elapsed().as_nanos());
            }
        }
        let m_raw = median_ns(&mut t_raw);
        let m_hp = median_ns(&mut t_hyb_prod);
        let m_hc = median_ns(&mut t_hyb_chk);
        let m_ins = if t_ins.is_empty() { 0 } else { median_ns(&mut t_ins) };
        let comma = if idx + 1 < sort_sizes.len() { "," } else { "" };
        println!(
            "    {{\"n\": {}, \"raw_sort_ns\": {}, \"hyb_prod_ns\": {}, \"hyb_check_ns\": {}, \"hyb_total_ns\": {}, \"insertion_ns\": {}, \"check_vs_raw_pct\": {:.2}}}{}",
            n, m_raw, m_hp, m_hc, m_hp + m_hc, m_ins, (m_hc as f64) * 100.0 / (m_raw as f64), comma
        );
    }
    println!("  ],");

    // 4. MatMul + Freivalds k=20
    println!("  \"matmul_freivalds\": [");
    let mat_sizes = [16usize, 32, 64, 128, 256];
    for (idx, &n) in mat_sizes.iter().enumerate() {
        let mut rng = Rng::new(900 + n as u64);
        let a: Vec<u64> = (0..n * n).map(|_| rng.next_u64()).collect();
        let b: Vec<u64> = (0..n * n).map(|_| rng.next_u64()).collect();
        let mut c = vec![0u64; n * n];
        let reps = if n <= 32 { 30 } else if n <= 64 { 15 } else { 7 };
        let mut t_mul = Vec::with_capacity(reps);
        let mut t_chk = Vec::with_capacity(reps);
        for r in 0..reps {
            let t0 = Instant::now();
            matmul_tiled(black_box(&a), black_box(&b), &mut c, n);
            black_box(&c);
            t_mul.push(t0.elapsed().as_nanos());

            let t1 = Instant::now();
            let ok = freivalds_check(black_box(&a), black_box(&b), black_box(&c), n, 20, 42 + r as u64);
            t_chk.push(t1.elapsed().as_nanos());
            assert!(ok);
        }
        // Negative adversarial control: 1 entry bit-flip caught
        c[(n * n) / 2] ^= 1;
        assert!(!freivalds_check(&a, &b, &c, n, 20, 12345));

        let mm = median_ns(&mut t_mul);
        let mc = median_ns(&mut t_chk);
        let comma = if idx + 1 < mat_sizes.len() { "," } else { "" };
        println!(
            "    {{\"n\": {}, \"rounds\": 20, \"matmul_ns\": {}, \"freivalds_ns\": {}, \"check_pct\": {:.2}}}{}",
            n, mm, mc, (mc as f64) * 100.0 / (mm as f64), comma
        );
    }
    println!("  ],");

    // 5. LZ77 + Kraft replay (chain=1 vs chain=32)
    println!("  \"lz77\": [");
    let lz_cases = [
        (16384usize, true, 1usize),
        (65536, true, 1),
        (262144, true, 1),
        (65536, true, 32),
        (262144, true, 32),
        (65536, false, 1),
    ];
    for (idx, &(sz, compressible, chain)) in lz_cases.iter().enumerate() {
        let mut rng = Rng::new(333 + sz as u64);
        let mut data = vec![0u8; sz];
        if compressible {
            // Structured repeating blocks + perturbations (~60% match density)
            for i in 0..sz {
                data[i] = ((i % 97) ^ ((i / 251) * 13)) as u8;
                if (i % 61) == 0 {
                    data[i] ^= (rng.next_u64() & 0x1f) as u8;
                }
            }
        } else {
            for b in &mut data {
                *b = rng.next_u64() as u8;
            }
        }
        let reps = 7;
        let mut t_comp = Vec::with_capacity(reps);
        let mut t_chk = Vec::with_capacity(reps);
        let mut n_tok = 0usize;
        for _ in 0..reps {
            let t0 = Instant::now();
            let (toks, lens) = lz77_hash_producer(black_box(&data), chain);
            t_comp.push(t0.elapsed().as_nanos());
            n_tok = toks.len();

            let t1 = Instant::now();
            let ok = lz77_replay_and_kraft_check(black_box(&data), black_box(&toks), black_box(&lens));
            t_chk.push(t1.elapsed().as_nanos());
            assert!(ok);
        }
        let mc_t = median_ns(&mut t_comp);
        let mk_t = median_ns(&mut t_chk);
        let comma = if idx + 1 < lz_cases.len() { "," } else { "" };
        println!(
            "    {{\"bytes\": {}, \"compressible\": {}, \"chain\": {}, \"tokens\": {}, \"solve_ns\": {}, \"check_ns\": {}, \"check_pct\": {:.2}}}{}",
            sz, compressible, chain, n_tok, mc_t, mk_t, (mk_t as f64) * 100.0 / (mc_t as f64), comma
        );
    }
    println!("  ],");

    // 6. Negative-ROI linear streaming checksum
    println!("  \"linear_stream\": [");
    for (idx, &sz) in [65536usize, 1048576].iter().enumerate() {
        let mut rng = Rng::new(888 + sz as u64);
        let data: Vec<u8> = (0..sz).map(|_| rng.next_u64() as u8).collect();
        let reps = 15;
        let mut t_fast = Vec::with_capacity(reps);
        let mut t_chk = Vec::with_capacity(reps);
        for _ in 0..reps {
            let t0 = Instant::now();
            let h1 = fast_unrolled_checksum(black_box(&data));
            black_box(h1);
            t_fast.push(t0.elapsed().as_nanos());

            let t1 = Instant::now();
            let h2 = fast_unrolled_checksum(black_box(&data));
            assert_eq!(h1, h2);
            t_chk.push(t1.elapsed().as_nanos());
        }
        let mf = median_ns(&mut t_fast);
        let mc = median_ns(&mut t_chk);
        let comma = if idx + 1 < 2 { "," } else { "" };
        println!(
            "    {{\"bytes\": {}, \"producer_ns\": {}, \"recompute_check_ns\": {}, \"overhead_pct\": {:.2}}}{}",
            sz, mf, mc, (mc as f64) * 100.0 / (mf as f64), comma
        );
    }
    println!("  ]");
    println!("}}");
}
