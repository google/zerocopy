use std::env;
use std::fs;
use std::hint::black_box;
use std::path::PathBuf;
use std::time::Instant;

use hybrid_proto_suite::anneal_emit::{
    build_k4_3color_cnf, build_pigeonhole_cnf, render_generated_lean_bridge, rust_check_rup_proof,
    solve_unsat_emit_lrat,
};
use hybrid_proto_suite::deflate::{
    build_structured_bytes, check_deflate_plan, greedy_lz77_huffman_producer,
    stored_literal_fallback,
};
use hybrid_proto_suite::sssp::{
    bellman_ford_fallback, build_layered_graph, build_reverse_chain_graph, check_sssp_witness,
    dijkstra_producer,
};

fn median_us(iters: u32, mut f: impl FnMut()) -> f64 {
    let mut times = Vec::with_capacity(iters as usize);
    for _ in 0..3 {
        f(); // warmup
    }
    for _ in 0..iters {
        let t0 = Instant::now();
        f();
        times.push(t0.elapsed().as_secs_f64() * 1_000_000.0);
    }
    times.sort_by(|a, b| a.total_cmp(b));
    times[times.len() / 2]
}

fn main() {
    let out_dir = PathBuf::from(env::args().nth(1).unwrap_or_else(|| ".".to_string()));

    // 1. Emit Anneal bridge file from real Rust solvers
    let t0_php = Instant::now();
    let (v_php, c_php) = build_pigeonhole_cnf(4, 3);
    let php_stats = solve_unsat_emit_lrat(v_php, &c_php).expect("PHP(4,3) UNSAT");
    let php_solve_us = t0_php.elapsed().as_secs_f64() * 1_000_000.0;
    assert!(rust_check_rup_proof(&c_php, &php_stats.steps));

    let t0_k4 = Instant::now();
    let (v_k4, c_k4) = build_k4_3color_cnf();
    let k4_stats = solve_unsat_emit_lrat(v_k4, &c_k4).expect("K4 UNSAT");
    let k4_solve_us = t0_k4.elapsed().as_secs_f64() * 1_000_000.0;
    assert!(rust_check_rup_proof(&c_k4, &k4_stats.steps));

    let php_rust_chk_us = median_us(50, || {
        assert!(black_box(rust_check_rup_proof(&c_php, &php_stats.steps)));
    });
    let k4_rust_chk_us = median_us(50, || {
        assert!(black_box(rust_check_rup_proof(&c_k4, &k4_stats.steps)));
    });

    let bridge_src = render_generated_lean_bridge(&php_stats, &c_php, &k4_stats, &c_k4);
    let bridge_dir = if out_dir.join("anneal_check/HybridBridge").is_dir() {
        out_dir.join("anneal_check/HybridBridge/GeneratedCerts.lean")
    } else if out_dir.join("anneal_bridge/HybridBridge").is_dir() {
        out_dir.join("anneal_bridge/HybridBridge/GeneratedCerts.lean")
    } else {
        out_dir.join("GeneratedCerts.lean")
    };
    fs::write(&bridge_dir, &bridge_src).expect("write GeneratedCerts.lean");

    // 2. SSSP scaling benchmarks
    let mut sssp_rows = Vec::new();
    for &n in &[64usize, 256, 1024] {
        let g = build_layered_graph(n, 8);
        let input = (g, 0usize);
        let sample_cand = dijkstra_producer(&input).unwrap();
        assert!(check_sssp_witness(&input, &sample_cand));
        let iters = if n <= 256 { 25 } else { 7 };

        let dijkstra_us = median_us(iters, || {
            let c = dijkstra_producer(black_box(&input)).unwrap();
            black_box(c);
        });
        let checker_us = median_us(iters * 4, || {
            let ok = check_sssp_witness(black_box(&input), black_box(&sample_cand));
            assert!(ok);
        });
        let bellman_us = median_us(iters.min(7), || {
            let fb = bellman_ford_fallback(black_box(&input));
            black_box(fb);
        });
        sssp_rows.push(format!(
            "    {{\"topology\": \"random_low_diam\", \"n\": {n}, \"edges\": {}, \"dijkstra_us\": {dijkstra_us:.2}, \"checker_us\": {checker_us:.2}, \"bellman_ford_fallback_us\": {bellman_us:.2}, \"checker_over_dijkstra_pct\": {:.2}, \"bellman_over_dijkstra_x\": {:.2}}}",
            input.0.edges.len(),
            (checker_us / dijkstra_us) * 100.0,
            bellman_us / dijkstra_us,
        ));
    }
    for &n in &[256usize, 512, 1024] {
        let g = build_reverse_chain_graph(n);
        let input = (g, 0usize);
        let sample_cand = dijkstra_producer(&input).unwrap();
        assert!(check_sssp_witness(&input, &sample_cand));

        let dijkstra_us = median_us(15, || {
            let c = dijkstra_producer(black_box(&input)).unwrap();
            black_box(c);
        });
        let checker_us = median_us(30, || {
            let ok = check_sssp_witness(black_box(&input), black_box(&sample_cand));
            assert!(ok);
        });
        let bellman_us = median_us(5, || {
            let fb = bellman_ford_fallback(black_box(&input));
            black_box(fb);
        });
        sssp_rows.push(format!(
            "    {{\"topology\": \"reverse_chain\", \"n\": {n}, \"edges\": {}, \"dijkstra_us\": {dijkstra_us:.2}, \"checker_us\": {checker_us:.2}, \"bellman_ford_fallback_us\": {bellman_us:.2}, \"checker_over_dijkstra_pct\": {:.2}, \"bellman_over_dijkstra_x\": {:.2}}}",
            input.0.edges.len(),
            (checker_us / dijkstra_us) * 100.0,
            bellman_us / dijkstra_us,
        ));
    }

    // 3. Deflate LZ77 + Kraft benchmarks
    let mut deflate_rows = Vec::new();
    for &sz in &[4096usize, 32768, 65536] {
        let data = build_structured_bytes(sz);
        let sample_cand = greedy_lz77_huffman_producer(&data).unwrap();
        assert!(check_deflate_plan(&data, &sample_cand));
        let token_cnt = sample_cand.0.len();
        let iters = if sz <= 32768 { 25 } else { 11 };

        let producer_us = median_us(iters, || {
            let c = greedy_lz77_huffman_producer(black_box(&data)).unwrap();
            black_box(c);
        });
        let checker_us = median_us(iters * 4, || {
            let ok = check_deflate_plan(black_box(&data), black_box(&sample_cand));
            assert!(ok);
        });
        let fallback_us = median_us(iters * 4, || {
            let fb = stored_literal_fallback(black_box(&data));
            black_box(fb);
        });
        deflate_rows.push(format!(
            "    {{\"bytes\": {sz}, \"tokens\": {token_cnt}, \"compression_ratio_tokens_per_byte\": {:.4}, \"lz77_huffman_us\": {producer_us:.2}, \"checker_us\": {checker_us:.2}, \"stored_fallback_us\": {fallback_us:.2}, \"checker_over_producer_pct\": {:.2}}}",
            (token_cnt as f64) / (sz as f64),
            (checker_us / producer_us) * 100.0,
        ));
    }

    let json = format!(
        "{{\n\
         \"sssp\": [\n{}\n  ],\n\
         \"deflate\": [\n{}\n  ],\n\
         \"anneal_bridge\": {{\n\
           \"php43\": {{\"vars\": {}, \"clauses\": {}, \"tree_nodes\": {}, \"add_steps\": {}, \"del_steps\": {}, \"total_steps\": {}, \"trie_depth\": {}, \"dpll_solve_us\": {php_solve_us:.2}, \"rust_rup_check_us\": {php_rust_chk_us:.2}}},\n\
           \"k4_color3\": {{\"vars\": {}, \"clauses\": {}, \"tree_nodes\": {}, \"add_steps\": {}, \"del_steps\": {}, \"total_steps\": {}, \"trie_depth\": {}, \"dpll_solve_us\": {k4_solve_us:.2}, \"rust_rup_check_us\": {k4_rust_chk_us:.2}}},\n\
           \"generated_lean_bytes\": {}\n\
         }}\n\
         }}\n",
        sssp_rows.join(",\n"),
        deflate_rows.join(",\n"),
        php_stats.num_vars,
        php_stats.num_clauses,
        php_stats.tree_nodes,
        php_stats.add_steps,
        php_stats.del_steps,
        php_stats.steps.len(),
        php_stats.trie_depth,
        k4_stats.num_vars,
        k4_stats.num_clauses,
        k4_stats.tree_nodes,
        k4_stats.add_steps,
        k4_stats.del_steps,
        k4_stats.steps.len(),
        k4_stats.trie_depth,
        bridge_src.len(),
    );

    let json_path = out_dir.join("rust_bench.json");
    fs::write(&json_path, &json).expect("write rust_bench.json");
    println!("{json}");
}
