use hybrid_proto_suite::anneal_emit::{
    build_align_pair_cut_goal, build_k4_3color_cnf, build_pigeonhole_cnf,
    build_stripe_partition_cut_goal, rust_check_rup_proof, solve_unsat_emit_lrat,
};
use hybrid_proto_suite::deflate::{
    build_structured_bytes, check_deflate_plan, greedy_lz77_huffman_producer,
    mutant_corrupt_match, mutant_kraft_oversubscribed, mutant_max_bits_16, mutant_oob_dist,
    mutant_panic as deflate_panic, stored_literal_fallback, LzToken,
};
use hybrid_proto_suite::sssp::{
    bellman_ford_fallback, build_layered_graph, check_sssp_witness, dijkstra_producer,
    mutant_drop_reachable, mutant_panic as sssp_panic, mutant_suboptimal_dist, mutant_zero_cycle,
    Edge, Graph,
};
use hybrid_proto_suite::{race_or_fallback, verify_opt, verify_or_fallback, HybridTelemetry, OriginTag};

#[test]
fn test_sssp_valid_and_adversarial_mutants() {
    let g = Graph {
        n: 5,
        edges: vec![
            Edge { src: 0, dst: 1, w: 2 },
            Edge { src: 0, dst: 2, w: 5 },
            Edge { src: 1, dst: 2, w: 0 },
            Edge { src: 1, dst: 3, w: 6 },
            Edge { src: 2, dst: 3, w: 1 },
            Edge { src: 2, dst: 1, w: 0 },
        ],
    };
    let input = (g, 0usize);
    let mut tel = HybridTelemetry::default();

    // Fast path passes checker
    let out = verify_or_fallback(
        &input,
        dijkstra_producer,
        check_sssp_witness,
        bellman_ford_fallback,
        &mut tel,
    );
    assert_eq!(out.origin, OriginTag::FastProducer);
    assert_eq!(
        out.cert.as_ref(),
        &vec![Some(0), Some(2), Some(2), Some(3), None]
    );

    // Every adversarial mutant is rejected by verify_opt -> None
    assert!(verify_opt(&input, mutant_zero_cycle, check_sssp_witness, &mut tel).is_none());
    assert!(verify_opt(&input, mutant_suboptimal_dist, check_sssp_witness, &mut tel).is_none());
    assert!(verify_opt(&input, mutant_drop_reachable, check_sssp_witness, &mut tel).is_none());
    assert!(verify_opt(&input, sssp_panic, check_sssp_witness, &mut tel).is_none());
    assert_eq!(tel.checker_rejects, 3);
    assert_eq!(tel.panics_caught, 1);

    // Fallback recovers exact shortest distances on any failed fast producer
    let recovered = verify_or_fallback(
        &input,
        mutant_zero_cycle,
        check_sssp_witness,
        bellman_ford_fallback,
        &mut tel,
    );
    assert_eq!(recovered.origin, OriginTag::VerifiedFallback);
    assert_eq!(recovered.cert.as_ref(), out.cert.as_ref());

    // Portfolio hedging accepts second producer when first panics
    let raced = race_or_fallback(
        &input,
        &[&mutant_panic_wrap, &dijkstra_wrap],
        check_sssp_witness,
        bellman_ford_fallback,
        &mut tel,
    );
    assert_eq!(raced.origin, OriginTag::PortfolioAlt(1));
    assert_eq!(raced.cert.as_ref(), out.cert.as_ref());
}

fn mutant_panic_wrap(i: &(Graph, usize)) -> Option<(Vec<Option<u64>>, hybrid_proto_suite::sssp::SsspWitness)> {
    sssp_panic(i)
}

fn dijkstra_wrap(i: &(Graph, usize)) -> Option<(Vec<Option<u64>>, hybrid_proto_suite::sssp::SsspWitness)> {
    dijkstra_producer(i)
}

#[test]
fn test_sssp_layered_random_agreement() {
    let g = build_layered_graph(128, 6);
    let input = (g, 0usize);
    let mut tel = HybridTelemetry::default();
    let d_out = verify_opt(&input, dijkstra_producer, check_sssp_witness, &mut tel).unwrap();
    let fb = bellman_ford_fallback(&input);
    assert!(check_sssp_witness(&input, &fb));
    assert_eq!(d_out.into_inner(), fb.0);
}

#[test]
fn test_deflate_lz77_kraft_and_mutants() {
    let data = build_structured_bytes(4096);
    let mut tel = HybridTelemetry::default();

    let res = verify_or_fallback(
        &data,
        |b| greedy_lz77_huffman_producer(b),
        |b, c| check_deflate_plan(b, c),
        |b| stored_literal_fallback(b),
        &mut tel,
    );
    assert_eq!(res.origin, OriginTag::FastProducer);
    // Confirm genuine compression happened (fewer tokens than input bytes)
    assert!(res.cert.as_ref().len() < data.len() / 2);

    // Every mutant rejected cleanly
    assert!(verify_opt(&data, |b| mutant_corrupt_match(b), |b, c| check_deflate_plan(b, c), &mut tel).is_none());
    assert!(verify_opt(&data, |b| mutant_oob_dist(b), |b, c| check_deflate_plan(b, c), &mut tel).is_none());
    assert!(verify_opt(&data, |b| mutant_kraft_oversubscribed(b), |b, c| check_deflate_plan(b, c), &mut tel).is_none());
    assert!(verify_opt(&data, |b| mutant_max_bits_16(b), |b, c| check_deflate_plan(b, c), &mut tel).is_none());
    assert!(verify_opt(&data, |b| deflate_panic(b), |b, c| check_deflate_plan(b, c), &mut tel).is_none());
    assert_eq!(tel.checker_rejects, 4);
    assert_eq!(tel.panics_caught, 1);

    // Stored fallback works even on adversarial inputs (and arbitrary single-byte input)
    let fb_res = verify_or_fallback(
        &data,
        |b| mutant_kraft_oversubscribed(b),
        |b, c| check_deflate_plan(b, c),
        |b| stored_literal_fallback(b),
        &mut tel,
    );
    assert_eq!(fb_res.origin, OriginTag::VerifiedFallback);
    assert_eq!(fb_res.cert.as_ref().len(), data.len());
    assert!(matches!(fb_res.cert.as_ref()[0], LzToken::Lit(_)));

    let empty: Vec<u8> = Vec::new();
    let empty_fb = stored_literal_fallback(&empty);
    assert!(check_deflate_plan(&empty, &empty_fb));
}

#[test]
fn test_anneal_dpll_lrat_and_cut_emitters() {
    let (v_php, c_php) = build_pigeonhole_cnf(4, 3);
    let stats_php = solve_unsat_emit_lrat(v_php, &c_php).expect("PHP(4,3) must be UNSAT");
    assert!(rust_check_rup_proof(&c_php, &stats_php.steps));
    assert!(stats_php.del_steps > 0);

    let (v_k4, c_k4) = build_k4_3color_cnf();
    let stats_k4 = solve_unsat_emit_lrat(v_k4, &c_k4).expect("K4 3-color must be UNSAT");
    assert!(rust_check_rup_proof(&c_k4, &stats_k4.steps));

    // Satisfiable PHP(3, 3) returns None cleanly
    let (v_sat, c_sat) = build_pigeonhole_cnf(3, 3);
    assert!(solve_unsat_emit_lrat(v_sat, &c_sat).is_none());

    let (g1, s1) = build_align_pair_cut_goal();
    assert_eq!(g1.hyps.len(), 2);
    assert_eq!(s1.len(), 7);
    let (g2, s2) = build_stripe_partition_cut_goal();
    assert_eq!(g2.hyps.len(), 3);
    assert_eq!(s2.len(), 12);
}
