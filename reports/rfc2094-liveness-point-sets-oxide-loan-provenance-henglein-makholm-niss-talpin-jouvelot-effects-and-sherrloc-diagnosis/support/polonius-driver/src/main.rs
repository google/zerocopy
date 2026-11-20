//! Minimal fact-file driver for `polonius-engine` (rust-lang/polonius).
//! Usage: polonius-driver <Naive|DatafrogOpt|LocationInsensitive|Hybrid|Compare> <facts-dir> [repeat]
//! Reads the tab-separated, double-quoted `*.facts` files emitted by `rustc -Znll-facts`,
//! interns each atom kind separately, runs the selected algorithm, and prints error counts,
//! the erroring points, and the median wall time over `repeat` runs.
use polonius_engine::{Algorithm, AllFacts, Atom, FactTypes, Output};
use std::collections::HashMap;
use std::time::Instant;

macro_rules! atom {
    ($n:ident) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        struct $n(usize);
        impl From<usize> for $n { fn from(i: usize) -> Self { $n(i) } }
        impl From<$n> for usize { fn from(a: $n) -> usize { a.0 } }
        impl Atom for $n { fn index(self) -> usize { self.0 } }
    };
}
atom!(O); atom!(L); atom!(P); atom!(V); atom!(Pa);
#[derive(Copy, Clone, Debug)]
struct T;
impl FactTypes for T { type Origin = O; type Loan = L; type Point = P; type Variable = V; type Path = Pa; }

#[derive(Default)]
struct Interner { map: HashMap<String, usize>, names: Vec<String> }
impl Interner {
    fn get(&mut self, s: &str) -> usize {
        if let Some(&i) = self.map.get(s) { return i; }
        let i = self.names.len(); self.names.push(s.to_string()); self.map.insert(s.to_string(), i); i
    }
}
#[derive(Default)]
struct Interners { o: Interner, l: Interner, p: Interner, v: Interner, pa: Interner }

fn rows(dir: &str, name: &str) -> Vec<Vec<String>> {
    let path = format!("{}/{}.facts", dir, name);
    let text = std::fs::read_to_string(&path).unwrap_or_default();
    text.lines().filter(|l| !l.is_empty()).map(|l| l.split('\t').map(|f| f.trim_matches('"').to_string()).collect()).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let algo: Algorithm = args[1].parse().expect("algorithm");
    let dir = &args[2];
    let repeat: usize = args.get(3).map(|s| s.parse().unwrap()).unwrap_or(1);
    let mut i = Interners::default();
    let mut f: AllFacts<T> = AllFacts::default();
    for r in rows(dir, "loan_issued_at") { f.loan_issued_at.push((O(i.o.get(&r[0])), L(i.l.get(&r[1])), P(i.p.get(&r[2])))); }
    for r in rows(dir, "universal_region") { f.universal_region.push(O(i.o.get(&r[0]))); }
    for r in rows(dir, "cfg_edge") { f.cfg_edge.push((P(i.p.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "loan_killed_at") { f.loan_killed_at.push((L(i.l.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "subset_base") { f.subset_base.push((O(i.o.get(&r[0])), O(i.o.get(&r[1])), P(i.p.get(&r[2])))); }
    for r in rows(dir, "loan_invalidated_at") { f.loan_invalidated_at.push((P(i.p.get(&r[0])), L(i.l.get(&r[1])))); }
    for r in rows(dir, "var_used_at") { f.var_used_at.push((V(i.v.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "var_defined_at") { f.var_defined_at.push((V(i.v.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "var_dropped_at") { f.var_dropped_at.push((V(i.v.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "use_of_var_derefs_origin") { f.use_of_var_derefs_origin.push((V(i.v.get(&r[0])), O(i.o.get(&r[1])))); }
    for r in rows(dir, "drop_of_var_derefs_origin") { f.drop_of_var_derefs_origin.push((V(i.v.get(&r[0])), O(i.o.get(&r[1])))); }
    for r in rows(dir, "child_path") { f.child_path.push((Pa(i.pa.get(&r[0])), Pa(i.pa.get(&r[1])))); }
    for r in rows(dir, "path_is_var") { f.path_is_var.push((Pa(i.pa.get(&r[0])), V(i.v.get(&r[1])))); }
    for r in rows(dir, "path_assigned_at_base") { f.path_assigned_at_base.push((Pa(i.pa.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "path_moved_at_base") { f.path_moved_at_base.push((Pa(i.pa.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "path_accessed_at_base") { f.path_accessed_at_base.push((Pa(i.pa.get(&r[0])), P(i.p.get(&r[1])))); }
    for r in rows(dir, "known_placeholder_subset") { f.known_placeholder_subset.push((O(i.o.get(&r[0])), O(i.o.get(&r[1])))); }
    for r in rows(dir, "placeholder") { f.placeholder.push((O(i.o.get(&r[0])), L(i.l.get(&r[1])))); }
    let tuples = f.subset_base.len() + f.cfg_edge.len() + f.loan_invalidated_at.len() + f.loan_issued_at.len();
    let mut times = Vec::new();
    let mut out: Option<Output<T>> = None;
    for _ in 0..repeat {
        let t0 = Instant::now();
        let o = Output::compute(&f, algo, false);
        times.push(t0.elapsed().as_secs_f64());
        out = Some(o);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let o = out.unwrap();
    let mut err_points: Vec<String> = o.errors.iter().map(|(p, ls)| format!("{} loans={:?}", i.p.names[p.0], ls.iter().map(|l| i.l.names[l.0].clone()).collect::<Vec<_>>())).collect();
    err_points.sort();
    println!("algorithm={:?} dir={} points={} origins={} loans={} input_tuples(subset_base+cfg_edge+loan_invalidated_at+loan_issued_at)={} errors_at_points={} subset_errors_at_points={} move_errors_at_points={} median_s={:.6} runs={}",
        algo, dir, i.p.names.len(), i.o.names.len(), i.l.names.len(), tuples, o.errors.len(), o.subset_errors.len(), o.move_errors.len(), times[times.len()/2], repeat);
    for e in err_points { println!("  error_at {}", e); }
}
