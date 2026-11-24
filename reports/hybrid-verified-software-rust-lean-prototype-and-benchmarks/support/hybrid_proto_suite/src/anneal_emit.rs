use std::fmt::Write;

/// `Anneal.LinearArith.NatLinExpr` mirror.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NatLinExpr {
    Cst(u64),
    Var(usize),
    Add(Box<NatLinExpr>, Box<NatLinExpr>),
    MulC(u64, Box<NatLinExpr>),
}

impl NatLinExpr {
    pub fn cst(n: u64) -> Self {
        Self::Cst(n)
    }
    pub fn var(idx: usize) -> Self {
        Self::Var(idx)
    }
    pub fn add(a: Self, b: Self) -> Self {
        Self::Add(Box::new(a), Box::new(b))
    }
    pub fn mul_c(k: u64, a: Self) -> Self {
        Self::MulC(k, Box::new(a))
    }

    pub fn to_lean(&self) -> String {
        match self {
            Self::Cst(n) => format!("(.cst {n})"),
            Self::Var(v) => format!("(.var {v})"),
            Self::Add(a, b) => format!("(.add {} {})", a.to_lean(), b.to_lean()),
            Self::MulC(k, a) => format!("(.mulC {k} {})", a.to_lean()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatCutIneq {
    pub lhs: NatLinExpr,
    pub rhs: NatLinExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatCutGoal {
    pub hyps: Vec<NatCutIneq>,
    pub concl: NatCutIneq,
}

/// `Anneal.LinearArith.CutStep` mirror.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CutStep {
    Hyp(usize),
    Comb(usize, u64, usize, u64),
    DivCut(u64, usize),
}

impl CutStep {
    pub fn to_lean(self) -> String {
        match self {
            Self::Hyp(i) => format!(".hyp {i}"),
            Self::Comb(s1, k1, s2, k2) => format!(".comb {s1} {k1} {s2} {k2}"),
            Self::DivCut(g, s) => format!(".divCut {g} {s}"),
        }
    }
}

fn collect_vars_expr(e: &NatLinExpr, vars: &mut Vec<usize>) {
    match e {
        NatLinExpr::Cst(_) => {}
        NatLinExpr::Var(idx) => {
            if !vars.contains(idx) {
                vars.push(*idx);
            }
        }
        NatLinExpr::Add(a, b) => {
            collect_vars_expr(a, vars);
            collect_vars_expr(b, vars);
        }
        NatLinExpr::MulC(_, a) => collect_vars_expr(a, vars),
    }
}

pub fn nat_goal_vars(g: &NatCutGoal) -> Vec<usize> {
    let mut vars = Vec::new();
    for iq in &g.hyps {
        collect_vars_expr(&iq.lhs, &mut vars);
        collect_vars_expr(&iq.rhs, &mut vars);
    }
    collect_vars_expr(&g.concl.lhs, &mut vars);
    collect_vars_expr(&g.concl.rhs, &mut vars);
    vars
}

/// Goal 1: `2*v0 <= 2*v1 + 1`, `2*v2 + 1 <= 2*v3` |- `v0 + v2 + 1 <= v1 + v3`.
/// Rational Farkas fails (`v0 = v1 + 0.5, v2 = v3 - 0.5`); requires two Chvatal-Gomory `divCut 2`.
pub fn build_align_pair_cut_goal() -> (NatCutGoal, Vec<CutStep>) {
    let v0 = || NatLinExpr::var(0);
    let v1 = || NatLinExpr::var(1);
    let v2 = || NatLinExpr::var(2);
    let v3 = || NatLinExpr::var(3);
    let goal = NatCutGoal {
        hyps: vec![
            NatCutIneq {
                lhs: NatLinExpr::mul_c(2, v0()),
                rhs: NatLinExpr::add(NatLinExpr::mul_c(2, v1()), NatLinExpr::cst(1)),
            },
            NatCutIneq {
                lhs: NatLinExpr::add(NatLinExpr::mul_c(2, v2()), NatLinExpr::cst(1)),
                rhs: NatLinExpr::mul_c(2, v3()),
            },
        ],
        concl: NatCutIneq {
            lhs: NatLinExpr::add(NatLinExpr::add(v0(), v2()), NatLinExpr::cst(1)),
            rhs: NatLinExpr::add(v1(), v3()),
        },
    };
    let vars = nat_goal_vars(&goal);
    let neg_concl_idx = goal.hyps.len() + vars.len();
    let steps = vec![
        CutStep::Hyp(0),
        CutStep::DivCut(2, 0),
        CutStep::Hyp(1),
        CutStep::DivCut(2, 2),
        CutStep::Comb(1, 1, 3, 1),
        CutStep::Hyp(neg_concl_idx),
        CutStep::Comb(4, 1, 5, 1),
    ];
    (goal, steps)
}

/// Goal 2 (6 variables): `4*v0 + 3 <= 4*v1`, `2*v2 <= 2*v3 + 1`, `4*v4 <= 3` |-
/// `v0 + v2 + v4 + 1 <= v1 + v3 + v5` (requires `divCut 4`, `divCut 2`, `divCut 4`,
/// plus auto-generated `0 <= v5` from `natGoalVars`).
pub fn build_stripe_partition_cut_goal() -> (NatCutGoal, Vec<CutStep>) {
    let v = |i| NatLinExpr::var(i);
    let goal = NatCutGoal {
        hyps: vec![
            NatCutIneq {
                lhs: NatLinExpr::add(NatLinExpr::mul_c(4, v(0)), NatLinExpr::cst(3)),
                rhs: NatLinExpr::mul_c(4, v(1)),
            },
            NatCutIneq {
                lhs: NatLinExpr::mul_c(2, v(2)),
                rhs: NatLinExpr::add(NatLinExpr::mul_c(2, v(3)), NatLinExpr::cst(1)),
            },
            NatCutIneq {
                lhs: NatLinExpr::mul_c(4, v(4)),
                rhs: NatLinExpr::cst(3),
            },
        ],
        concl: NatCutIneq {
            lhs: NatLinExpr::add(
                NatLinExpr::add(v(0), v(2)),
                NatLinExpr::add(v(4), NatLinExpr::cst(1)),
            ),
            rhs: NatLinExpr::add(NatLinExpr::add(v(1), v(3)), v(5)),
        },
    };
    let vars = nat_goal_vars(&goal);
    let v5_pos = vars.iter().position(|&x| x == 5).expect("v5 in vars");
    let v5_hyp_idx = goal.hyps.len() + v5_pos;
    let neg_concl_idx = goal.hyps.len() + vars.len();
    let steps = vec![
        CutStep::Hyp(0),
        CutStep::DivCut(4, 0),
        CutStep::Hyp(1),
        CutStep::DivCut(2, 2),
        CutStep::Hyp(2),
        CutStep::DivCut(4, 4),
        CutStep::Comb(1, 1, 3, 1),
        CutStep::Comb(6, 1, 5, 1),
        CutStep::Hyp(v5_hyp_idx),
        CutStep::Comb(7, 1, 8, 1),
        CutStep::Hyp(neg_concl_idx),
        CutStep::Comb(9, 1, 10, 1),
    ];
    (goal, steps)
}

/// Literal encoding matching `Anneal.BitTrieLrat.mkLit`:
/// `2 * var` = positive literal, `2 * var + 1` = negative literal.
#[inline]
pub fn mk_lit(var_id: usize, is_pos: bool) -> usize {
    if is_pos {
        2 * var_id
    } else {
        2 * var_id + 1
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RupStep {
    AddRup {
        cid: usize,
        clause: Vec<usize>,
        hints: Vec<usize>,
    },
    Del(Vec<usize>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatProofStats {
    pub num_vars: usize,
    pub num_clauses: usize,
    pub steps: Vec<RupStep>,
    pub add_steps: usize,
    pub del_steps: usize,
    pub max_cid: usize,
    pub tree_nodes: usize,
    pub trie_depth: usize,
}

/// Real recursive DPLL solver with exact unit-propagation trace logging and branch deletion.
/// For any UNSAT CNF, emits a complete `.addRup` / `.del` proof accepted by
/// `Anneal.BitTrieLrat.checkRupProof`.
pub fn solve_unsat_emit_lrat(num_vars: usize, cnf: &[Vec<usize>]) -> Option<SatProofStats> {
    let active: Vec<(usize, Vec<usize>)> = cnf.iter().cloned().enumerate().collect();
    let mut next_cid = cnf.len();
    let mut steps = Vec::new();
    let mut decisions = Vec::new();
    let mut tree_nodes = 0usize;

    let Ok(root_cid) = dpll_prove(
        num_vars,
        &active,
        &mut next_cid,
        &mut decisions,
        &mut steps,
        &mut tree_nodes,
    ) else {
        return None;
    };

    let max_cid = next_cid.saturating_sub(1).max(root_cid);
    let max_idx = max_cid.max(num_vars.saturating_sub(1));
    let mut trie_depth = 1usize;
    while (1usize << trie_depth) <= max_idx {
        trie_depth += 1;
    }
    // Note: BitTrieLrat requires depth > bit-width of every var and cid.
    let trie_depth = trie_depth + 1;

    let add_steps = steps
        .iter()
        .filter(|s| matches!(s, RupStep::AddRup { .. }))
        .count();
    let del_steps = steps
        .iter()
        .filter(|s| matches!(s, RupStep::Del(_)))
        .count();

    Some(SatProofStats {
        num_vars,
        num_clauses: cnf.len(),
        steps,
        add_steps,
        del_steps,
        max_cid,
        tree_nodes,
        trie_depth,
    })
}

fn dpll_prove(
    num_vars: usize,
    active: &[(usize, Vec<usize>)],
    next_cid: &mut usize,
    decisions: &mut Vec<usize>,
    steps: &mut Vec<RupStep>,
    tree_nodes: &mut usize,
) -> Result<usize, ()> {
    *tree_nodes += 1;
    let mut assign: Vec<Option<bool>> = vec![None; num_vars];
    for &lit in decisions.iter() {
        let v = lit / 2;
        let p = (lit & 1) == 0;
        if let Some(prev) = assign[v] {
            if prev != p {
                // Contradictory decisions cannot arise unless caller passed them.
                return Ok(*next_cid);
            }
        }
        assign[v] = Some(p);
    }

    // Unit propagation loop recording exact discovery hints.
    let mut hints = Vec::new();
    loop {
        let mut propagated = false;
        for (cid, clause) in active {
            let mut satisfied = false;
            let mut unit_lit: Option<usize> = None;
            let mut multi_unassigned = false;

            for &lit in clause {
                let v = lit / 2;
                let p = (lit & 1) == 0;
                match assign[v] {
                    Some(val) if val == p => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => match unit_lit {
                        None => unit_lit = Some(lit),
                        Some(u) if u == lit => {}
                        Some(_) => multi_unassigned = true,
                    },
                }
            }

            if satisfied {
                continue;
            }
            if !multi_unassigned {
                match unit_lit {
                    None => {
                        // Conflict clause found!
                        hints.push(*cid);
                        let learned: Vec<usize> = decisions.iter().map(|&l| l ^ 1).collect();
                        let new_cid = *next_cid;
                        *next_cid += 1;
                        steps.push(RupStep::AddRup {
                            cid: new_cid,
                            clause: learned,
                            hints,
                        });
                        return Ok(new_cid);
                    }
                    Some(u) => {
                        hints.push(*cid);
                        assign[u / 2] = Some((u & 1) == 0);
                        propagated = true;
                        break;
                    }
                }
            }
        }
        if !propagated {
            break;
        }
    }

    // Pick first unassigned variable (deterministic smallest-index heuristic).
    let Some(branch_var) = assign.iter().position(|x| x.is_none()) else {
        return Err(());
    };

    let pos_lit = mk_lit(branch_var, true);
    let neg_lit = mk_lit(branch_var, false);

    decisions.push(pos_lit);
    let cid_pos = dpll_prove(num_vars, active, next_cid, decisions, steps, tree_nodes)?;
    decisions.pop();

    decisions.push(neg_lit);
    let cid_neg = dpll_prove(num_vars, active, next_cid, decisions, steps, tree_nodes)?;
    decisions.pop();

    // Merge both unsatisfiable branches: `negate(decisions)` is RUP from `[cid_pos, cid_neg]`.
    let merged_clause: Vec<usize> = decisions.iter().map(|&l| l ^ 1).collect();
    let merged_cid = *next_cid;
    *next_cid += 1;
    steps.push(RupStep::AddRup {
        cid: merged_cid,
        clause: merged_clause,
        hints: vec![cid_pos, cid_neg],
    });
    steps.push(RupStep::Del(vec![cid_pos, cid_neg]));
    Ok(merged_cid)
}

/// Independent Rust mirror of `Anneal.BitTrieLrat.checkRupProof` used as fast pre-check
/// / self-check telemetry before emitting Lean kernel artifacts.
pub fn rust_check_rup_proof(cnf: &[Vec<usize>], steps: &[RupStep]) -> bool {
    let mut db: std::collections::BTreeMap<usize, Vec<usize>> =
        cnf.iter().cloned().enumerate().collect();
    let mut got_empty = false;

    for step in steps {
        match step {
            RupStep::Del(cids) => {
                for c in cids {
                    db.remove(c);
                }
            }
            RupStep::AddRup { cid, clause, hints } => {
                let mut assign: std::collections::BTreeMap<usize, bool> =
                    std::collections::BTreeMap::new();
                let mut conflict = false;
                for &lit in clause {
                    let v = lit / 2;
                    let req = (lit & 1) != 0; // negated target literal
                    if let Some(&prev) = assign.get(&v) {
                        if prev != req {
                            conflict = true;
                            break;
                        }
                    } else {
                        assign.insert(v, req);
                    }
                }
                if !conflict {
                    for &hid in hints {
                        let Some(hcls) = db.get(&hid) else {
                            return false;
                        };
                        let mut sat = false;
                        let mut unit: Option<usize> = None;
                        let mut multi = false;
                        for &lit in hcls {
                            let v = lit / 2;
                            let p = (lit & 1) == 0;
                            match assign.get(&v) {
                                Some(&val) if val == p => {
                                    sat = true;
                                    break;
                                }
                                Some(_) => {}
                                None => match unit {
                                    None => unit = Some(lit),
                                    Some(u) if u == lit => {}
                                    Some(_) => multi = true,
                                },
                            }
                        }
                        if sat || multi {
                            continue;
                        }
                        match unit {
                            None => {
                                conflict = true;
                                break;
                            }
                            Some(u) => {
                                assign.insert(u / 2, (u & 1) == 0);
                            }
                        }
                    }
                }
                if !conflict {
                    return false;
                }
                db.insert(*cid, clause.clone());
                if clause.is_empty() {
                    got_empty = true;
                }
            }
        }
    }
    got_empty
}

/// Builds Pigeonhole Principle `PHP(pigeons, holes)` CNF:
/// variable `p * holes + h` means pigeon `p` is in hole `h`.
pub fn build_pigeonhole_cnf(pigeons: usize, holes: usize) -> (usize, Vec<Vec<usize>>) {
    let mut clauses = Vec::new();
    // Each pigeon must occupy at least one hole.
    for p in 0..pigeons {
        let mut cls = Vec::with_capacity(holes);
        for h in 0..holes {
            cls.push(mk_lit(p * holes + h, true));
        }
        clauses.push(cls);
    }
    // No hole can hold two pigeons.
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(vec![
                    mk_lit(p1 * holes + h, false),
                    mk_lit(p2 * holes + h, false),
                ]);
            }
        }
    }
    (pigeons * holes, clauses)
}

/// Builds K4 3-coloring UNSAT CNF (12 variables, 22 clauses).
pub fn build_k4_3color_cnf() -> (usize, Vec<Vec<usize>>) {
    let mut clauses = Vec::new();
    for v in 0..4 {
        clauses.push(vec![
            mk_lit(v * 3, true),
            mk_lit(v * 3 + 1, true),
            mk_lit(v * 3 + 2, true),
        ]);
    }
    for u in 0..4 {
        for v in (u + 1)..4 {
            for c in 0..3 {
                clauses.push(vec![
                    mk_lit(u * 3 + c, false),
                    mk_lit(v * 3 + c, false),
                ]);
            }
        }
    }
    (12, clauses)
}

fn format_nat_list(xs: &[usize]) -> String {
    let parts: Vec<String> = xs.iter().map(|x| x.to_string()).collect();
    format!("[{}]", parts.join(", "))
}

pub fn render_generated_lean_bridge(
    php_stats: &SatProofStats,
    php_cnf: &[Vec<usize>],
    k4_stats: &SatProofStats,
    k4_cnf: &[Vec<usize>],
) -> String {
    let (g1, steps1) = build_align_pair_cut_goal();
    let (g2, steps2) = build_stripe_partition_cut_goal();

    let mut out = String::new();
    writeln!(
        out,
        "-- AUTO-GENERATED by Rust hybrid_proto_suite (`bench_and_emit`).\n\
         -- Imports unmodified `Anneal.LinearArith` and `Anneal.BitTrieLrat`\n\
         -- from google/zerocopy (commit 7527dd2b9ae90b60d2ae8258ffd44bd0ee1e4d82).\n\n\
         module\n\
         prelude\n\
         public import Init.Core\n\
         public import Init.NotationExtra\n\
         public import Anneal.LinearArith\n\
         public import Anneal.BitTrieLrat\n\n\
         public section\n\n\
         namespace HybridBridge\n\n\
         open Anneal.LinearArith\n\
         open Anneal.BitTrieLrat\n"
    )
    .unwrap();

    // Emit LinearArith goals + certificates
    for (name, g, steps) in [
        ("alignPair", &g1, &steps1),
        ("stripePartition", &g2, &steps2),
    ] {
        writeln!(out, "@[expose] noncomputable def {name}Goal : NatCutGoal where").unwrap();
        writeln!(out, "  hyps :=").unwrap();
        for (i, h) in g.hyps.iter().enumerate() {
            let pfx = if i == 0 { "    [" } else { "    ," };
            writeln!(
                out,
                "{pfx} ⟨{}, {}⟩",
                h.lhs.to_lean(),
                h.rhs.to_lean()
            )
            .unwrap();
        }
        writeln!(out, "    ]").unwrap();
        writeln!(
            out,
            "  concl := ⟨{}, {}⟩\n",
            g.concl.lhs.to_lean(),
            g.concl.rhs.to_lean()
        )
        .unwrap();

        writeln!(out, "@[expose] def {name}Cert : List CutStep :=").unwrap();
        for (i, s) in steps.iter().enumerate() {
            let pfx = if i == 0 { "  [" } else { "  ," };
            writeln!(out, "{pfx} {}", s.to_lean()).unwrap();
        }
        writeln!(out, "  ]\n").unwrap();
    }

    writeln!(
        out,
        "theorem alignPair_verified (v0 v1 v2 v3 : Nat)\n\
             (h0 : 2 * v0 ≤ 2 * v1 + 1) (h1 : 2 * v2 + 1 ≤ 2 * v3) :\n\
             v0 + v2 + 1 ≤ v1 + v3 :=\n\
           checkNatCutGoal_sound alignPairGoal alignPairCert rfl [v0, v1, v2, v3] h0 h1\n\n\
         /-- Negative control: cut-free Farkas combination without `divCut` fails (`= false`). -/\n\
         theorem alignPair_without_divCut_rejected :\n\
             checkNatCutGoal alignPairGoal [.hyp 0, .hyp 1, .hyp 6, .comb 0 1 1 1, .comb 3 1 2 1] = false :=\n\
           rfl\n\n\
         theorem stripePartition_verified (v0 v1 v2 v3 v4 v5 : Nat)\n\
             (h0 : 4 * v0 + 3 ≤ 4 * v1) (h1 : 2 * v2 ≤ 2 * v3 + 1) (h2 : 4 * v4 ≤ 3) :\n\
             v0 + v2 + v4 + 1 ≤ v1 + v3 + v5 :=\n\
           checkNatCutGoal_sound stripePartitionGoal stripePartitionCert rfl [v0, v1, v2, v3, v4, v5] h0 h1 h2\n\n\
         /-- Negative control: wrong divisor `divCut 2` on `4*v0 + 3 ≤ 4*v1` fails (`= false`). -/\n\
         theorem stripePartition_wrong_divisor_rejected :\n\
             checkNatCutGoal stripePartitionGoal [.hyp 0, .divCut 2 0] = false := rfl\n"
    )
    .unwrap();

    // Emit BitTrieLrat CNF & LRAT steps for PHP(4,3) and K4-3color
    for (name, stats, cnf) in [("php43", php_stats, php_cnf), ("k4Color3", k4_stats, k4_cnf)] {
        writeln!(out, "@[expose] def {name}Cnf : List Clause :=").unwrap();
        for (i, cls) in cnf.iter().enumerate() {
            let pfx = if i == 0 { "  [" } else { "  ," };
            writeln!(out, "{pfx} {}", format_nat_list(cls)).unwrap();
        }
        writeln!(out, "  ]\n").unwrap();

        writeln!(out, "@[expose] def {name}Steps : List RupStep :=").unwrap();
        for (i, st) in stats.steps.iter().enumerate() {
            let pfx = if i == 0 { "  [" } else { "  ," };
            match st {
                RupStep::AddRup { cid, clause, hints } => {
                    writeln!(
                        out,
                        "{pfx} .addRup {cid} {} {}",
                        format_nat_list(clause),
                        format_nat_list(hints)
                    )
                    .unwrap();
                }
                RupStep::Del(cids) => {
                    writeln!(out, "{pfx} .del {}", format_nat_list(cids)).unwrap();
                }
            }
        }
        writeln!(out, "  ]\n").unwrap();

        writeln!(
            out,
            "theorem {name}_unsat_verified : UnsatCnf {name}Cnf :=\n\
               checkRupProof_sound {} {name}Cnf {name}Steps rfl\n",
            stats.trie_depth
        )
        .unwrap();
    }

    writeln!(
        out,
        "/-- Negative control: tampering hint 0 -> 999 in PHP(4,3) fails closed with `.errBadHint`. -/\n\
         theorem php43_forged_hint_rejected :\n\
             checkRupProof {} php43Cnf [.addRup 99 [] [999]] = .errBadHint 99 999 := rfl\n\n\
         #print axioms alignPair_verified\n\
         #print axioms stripePartition_verified\n\
         #print axioms php43_unsat_verified\n\
         #print axioms k4Color3_unsat_verified\n\n\
         end HybridBridge\n\
         end\n",
        php_stats.trie_depth
    )
    .unwrap();
    out
}
