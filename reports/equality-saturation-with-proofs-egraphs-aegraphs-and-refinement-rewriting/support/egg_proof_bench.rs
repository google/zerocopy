use egg::*;
use std::time::Instant;

define_language! {
    enum BvLang {
        Num(i64),
        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "<<" = Shl([Id; 2]),
        "&" = And([Id; 2]),
        "|" = Or([Id; 2]),
        "^" = Xor([Id; 2]),
        "~" = Not(Id),
        "sh1add" = Sh1Add([Id; 2]),
        "sh2add" = Sh2Add([Id; 2]),
        "sh3add" = Sh3Add([Id; 2]),
        "andn" = Andn([Id; 2]),
        "dup" = Dup(Id),
        Symbol(Symbol),
    }
}

fn non_ac_rules() -> Vec<Rewrite<BvLang, ()>> {
    vec![
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),
        rewrite!("zero-add"; "(+ 0 ?a)" => "?a"),
        rewrite!("sub-self"; "(- ?a ?a)" => "0"),
        rewrite!("xor-self"; "(^ ?a ?a)" => "0"),
        rewrite!("and-self"; "(& ?a ?a)" => "?a"),
        rewrite!("or-self"; "(| ?a ?a)" => "?a"),
        rewrite!("mul-one"; "(* ?a 1)" => "?a"),
        rewrite!("mul-two"; "(* ?a 2)" => "(<< ?a 1)"),
        rewrite!("mul-four"; "(* ?a 4)" => "(<< ?a 2)"),
        rewrite!("mul-eight"; "(* ?a 8)" => "(<< ?a 3)"),
        rewrite!("sh1add-fuse"; "(+ (<< ?a 1) ?b)" => "(sh1add ?a ?b)"),
        rewrite!("sh2add-fuse"; "(+ (<< ?a 2) ?b)" => "(sh2add ?a ?b)"),
        rewrite!("sh3add-fuse"; "(+ (<< ?a 3) ?b)" => "(sh3add ?a ?b)"),
        rewrite!("andn-fuse"; "(& ?a (~ ?b))" => "(andn ?a ?b)"),
        rewrite!("andn-chain"; "(& (andn ?a ?b) (~ ?c))" => "(andn ?a (| ?b ?c))"),
        rewrite!("neg-mask"; "(~ (- ?a 1))" => "(- 0 ?a)"),
        rewrite!("dup-expand"; "(dup ?x)" => "(+ ?x ?x)"),
    ]
}

fn ac_rules() -> Vec<Rewrite<BvLang, ()>> {
    let mut r = non_ac_rules();
    r.push(rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"));
    r.push(rewrite!("add-assoc"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"));
    r.push(rewrite!("add-assoc-rev"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"));
    r
}

fn run_flatt_shortcut_demo() -> (usize, usize, usize, usize) {
    // Build a union-find proof forest where s0 = s1 = s2 = ... = s8 is added first,
    // and then a 2-step congruence shortcut s0 -> mid -> s8 is added afterwards.
    let mut eg_opt = EGraph::<BvLang, ()>::default().with_explanations_enabled();
    let mut eg_unopt = EGraph::<BvLang, ()>::default()
        .with_explanations_enabled()
        .without_explanation_length_optimization();

    for eg in [&mut eg_opt, &mut eg_unopt] {
        for i in 0..8 {
            let lhs: PatternAst<BvLang> = format!("s{}", i).parse().unwrap();
            let rhs: PatternAst<BvLang> = format!("s{}", i + 1).parse().unwrap();
            eg.union_instantiations(&lhs, &rhs, &Subst::with_capacity(0), format!("chain_{}", i));
        }
        // Now add a 2-step shortcut s0 -> mid -> s8 after the 8-step spanning tree s0..s8
        let s0: PatternAst<BvLang> = "s0".parse().unwrap();
        let mid: PatternAst<BvLang> = "mid".parse().unwrap();
        let s8: PatternAst<BvLang> = "s8".parse().unwrap();
        eg.union_instantiations(&s0, &mid, &Subst::with_capacity(0), "shortcut_half1");
        eg.union_instantiations(&mid, &s8, &Subst::with_capacity(0), "shortcut_half2");
        eg.rebuild();
    }
    let s0_expr: RecExpr<BvLang> = "(+ s0 s0)".parse().unwrap();
    let s8_expr: RecExpr<BvLang> = "(+ s8 s8)".parse().unwrap();
    eg_opt.add_expr(&s0_expr);
    eg_opt.add_expr(&s8_expr);
    eg_unopt.add_expr(&s0_expr);
    eg_unopt.add_expr(&s8_expr);

    let mut expl_opt = eg_opt.explain_equivalence(&s0_expr, &s8_expr);
    let mut expl_unopt = eg_unopt.explain_equivalence(&s0_expr, &s8_expr);
    (
        expl_opt.get_tree_size().try_into().unwrap(),
        expl_opt.make_flat_explanation().len() - 1,
        expl_unopt.get_tree_size().try_into().unwrap(),
        expl_unopt.make_flat_explanation().len() - 1,
    )
}

fn main() {
    println!("{{");
    println!("  \"egg_version\": \"0.11.0\",");
    let (flatt_opt_dag, flatt_opt_flat, flatt_unopt_dag, flatt_unopt_flat) = run_flatt_shortcut_demo();
    println!(
        "  \"flatt_fmcad2022_shortcut_demo\": {{\"opt_dag_steps\": {}, \"opt_flat_steps\": {}, \"unopt_dag_steps\": {}, \"unopt_flat_steps\": {}}},",
        flatt_opt_dag, flatt_opt_flat, flatt_unopt_dag, flatt_unopt_flat
    );
    println!("  \"benchmarks\": [");

    let cases = vec![
        ("dst_slice_addr", "(+ (+ base (& (+ hdr (- align 1)) (~ (- align 1)))) (* idx 4))"),
        ("nested_zba_zbb", "(+ (* (& (& x (~ m1)) (~ m2)) 8) (+ (* y 4) (+ z 0)))"),
        ("deep_chain_8", "(+ (* (+ (* (+ (* (+ (* a 2) b) 4) c) 8) d) 2) (- e e))"),
        ("shared_dag_depth4", "(dup (dup (dup (dup (+ (* (& x (~ m1)) 4) (- y y))))))"),
    ];

    for (idx, (name, expr_str)) in cases.iter().enumerate() {
        for (with_ac_idx, with_ac) in [false, true].iter().enumerate() {
            let start: RecExpr<BvLang> = expr_str.parse().unwrap();
            let rules = if *with_ac { ac_rules() } else { non_ac_rules() };
            let t0 = Instant::now();
            let mut runner = Runner::default()
                .with_explanations_enabled()
                .with_iter_limit(8)
                .with_node_limit(50_000)
                .with_expr(&start)
                .run(&rules);
            let sat_us = t0.elapsed().as_micros();

            let root = runner.roots[0];
            let t1 = Instant::now();
            let extractor = Extractor::new(&runner.egraph, AstSize);
            let (best_cost, best_expr) = extractor.find_best(root);
            let ext_us = t1.elapsed().as_micros();

            let t2 = Instant::now();
            let mut expl = runner.explain_equivalence(&start, &best_expr);
            let dag_let_steps = expl.get_tree_size();
            let flat_steps = expl.make_flat_explanation().len() - 1;
            let expl_us = t2.elapsed().as_micros();
            expl.check_proof(&rules);

            let mut runner_unopt = Runner::default()
                .with_explanations_enabled()
                .without_explanation_length_optimization()
                .with_iter_limit(8)
                .with_node_limit(50_000)
                .with_expr(&start)
                .run(&rules);
            let mut expl_unopt = runner_unopt.explain_equivalence(&start, &best_expr);
            let unopt_dag_steps = expl_unopt.get_tree_size();
            let unopt_flat_steps = expl_unopt.make_flat_explanation().len() - 1;

            let comma = if idx == cases.len() - 1 && with_ac_idx == 1 { "" } else { "," };
            println!(
                "    {{\"case\": \"{}\", \"ac_enabled\": {}, \"eclasses\": {}, \"enodes\": {}, \"iterations\": {}, \"start_cost\": {}, \"best_cost\": {}, \"best_expr\": \"{}\", \"dag_let_steps_opt\": {}, \"flat_steps_opt\": {}, \"dag_let_steps_unopt\": {}, \"flat_steps_unopt\": {}, \"sat_us\": {}, \"extract_us\": {}, \"explain_us\": {}}}{}",
                name,
                with_ac,
                runner.egraph.number_of_classes(),
                runner.egraph.total_size(),
                runner.iterations.len(),
                start.as_ref().len(),
                best_cost,
                best_expr,
                dag_let_steps,
                flat_steps,
                unopt_dag_steps,
                unopt_flat_steps,
                sat_us,
                ext_us,
                expl_us,
                comma
            );
        }
    }
    println!("  ],");
    println!("  \"shared_dag_scaling\": [");
    for d in 1..=6 {
        let mut expr = "(+ (* (& x (~ m1)) 4) (- y y))".to_string();
        for _ in 0..d {
            expr = format!("(dup {})", expr);
        }
        let mut target = "(<< (andn x m1) 2)".to_string();
        for _ in 0..d {
            target = format!("(+ {} {})", target, target);
        }
        let start: RecExpr<BvLang> = expr.parse().unwrap();
        let goal: RecExpr<BvLang> = target.parse().unwrap();
        let rules = non_ac_rules();
        let mut runner = Runner::default()
            .with_explanations_enabled()
            .with_iter_limit(12)
            .with_node_limit(50_000)
            .with_expr(&start)
            .run(&rules);
        let mut expl = runner.explain_equivalence(&start, &goal);
        let dag_steps = expl.get_tree_size();
        let flat_steps = expl.make_flat_explanation().len() - 1;
        let let_bytes = expl.get_string_with_let().len();
        let flat_bytes = expl.get_flat_string().len();
        expl.check_proof(&rules);
        let comma = if d == 6 { "" } else { "," };
        println!(
            "    {{\"depth\": {}, \"dag_let_steps\": {}, \"flat_steps\": {}, \"let_sexp_bytes\": {}, \"flat_sexp_bytes\": {}}}{}",
            d, dag_steps, flat_steps, let_bytes, flat_bytes, comma
        );
    }
    println!("  ],");
    println!("  \"ac_scaling\": [");
    for n in 2..=7 {
        let mut expr = "x0".to_string();
        for i in 1..n {
            expr = format!("(+ {} x{})", expr, i);
        }
        let start: RecExpr<BvLang> = expr.parse().unwrap();
        let rules = ac_rules();
        let t0 = Instant::now();
        let runner = Runner::default()
            .with_iter_limit(10)
            .with_node_limit(100_000)
            .with_expr(&start)
            .run(&rules);
        let sat_us = t0.elapsed().as_micros();
        let comma = if n == 7 { "" } else { "," };
        println!(
            "    {{\"terms\": {}, \"eclasses\": {}, \"enodes\": {}, \"sat_us\": {}}}{}",
            n,
            runner.egraph.number_of_classes(),
            runner.egraph.total_size(),
            sat_us,
            comma
        );
    }
    println!("  ]");
    println!("}}");
}
