//! Owned observer for actual pinned formality judgments/codegen. No acceptance theorem.
use std::{fs, path::PathBuf, process::ExitCode, sync::{Arc, Mutex}};
use formality_core::judgment::ProofTree;
use formality_rust::{check::check_all_crates, grammar::Crates, rust::try_term};

struct SharedWriter(Arc<Mutex<Vec<u8>>>);
impl std::io::Write for SharedWriter {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        let mut out = self.0.lock().map_err(|_| std::io::Error::other("writer mutex poisoned"))?;
        out.extend_from_slice(b); Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
}
impl libspecr::hidden::GcCompat for SharedWriter {
    fn points_to(&self, _: &mut std::collections::HashSet<usize>) {}
}
fn census(tree: &ProofTree, out: &mut String) {
    out.push_str(&format!("{}\t{:?}\t{}:{}:{}\t{:?}\n", tree.judgment_name,
        tree.rule_name, tree.file, tree.line, tree.column, tree.attributes));
    for c in &tree.children { census(c, out); }
}
fn observe() -> anyhow::Result<u8> {
    let args: Vec<String> = std::env::args().collect();
    anyhow::ensure!(args.len() >= 4, "usage: owned_e07 ACTION INPUT OUTPUT_DIR [QUERY]");
    let action = &args[1]; let input = fs::read_to_string(&args[2])?;
    let out = PathBuf::from(&args[3]); fs::create_dir(&out)?;
    let program: Crates = match try_term(&input) {
        Ok(p) => p,
        Err(e) => { fs::write(out.join("parse-error.txt"), format!("{e:#}"))?;
                    println!("parse=rejected"); return Ok(2); }
    };
    fs::write(out.join("parsed-ast.txt"), format!("{program:#?}"))?;
    let proof = match check_all_crates(&program).check_proven() {
        Ok(p) => p,
        Err(e) => { fs::write(out.join("judgment-error.txt"), format!("{e:#?}\n{e}"))?;
                    println!("parse=accepted check=rejected"); return Ok(3); }
    };
    fs::write(out.join("check-derivation.txt"), format!("{proof:#?}"))?;
    let mut rules = String::new(); census(&proof, &mut rules);
    fs::write(out.join("check-rules.tsv"), rules)?;
    println!("parse=accepted check=accepted");
    if action == "check" { return Ok(0); }
    if action == "query" {
        anyhow::ensure!(args.len() == 5, "query argument required");
        let query_text = fs::read_to_string(&args[4])?;
        let query: Arc<formality_rust::prove::test_util::TestAssertion> = try_term(&query_text)?;
        let solutions = formality_rust::prove::test_util::test_prove(program.to_prove_decls(), query);
        fs::write(out.join("query-result.txt"), format!("{solutions:#?}\n{solutions}"))?;
        let mut count = 0;
        for (constraint, tree) in solutions.iter() {
            fs::write(out.join(format!("query-{count}.constraint.txt")), format!("{constraint:#?}"))?;
            fs::write(out.join(format!("query-{count}.derivation.txt")), format!("{tree:#?}"))?;
            let mut rules = String::new(); census(&tree, &mut rules);
            fs::write(out.join(format!("query-{count}.rules.tsv")), rules)?;
            count += 1;
        }
        println!("query_solutions={count}");
        return Ok(if count == 0 { 5 } else { 0 });
    }
    anyhow::ensure!(action == "codegen" || action == "run", "unknown action");
    let generated = match formality_rust::codegen::codegen_program(&program) {
        Ok(p) => p,
        Err(e) => { fs::write(out.join("codegen-error.txt"), format!("{e:#}"))?;
                    println!("codegen=rejected"); return Ok(4); }
    };
    fs::write(out.join("generated-program.txt"), format!("{generated:#?}"))?;
    println!("codegen=accepted functions={:?} globals={:?} traits={:?} vtables={:?}",
        generated.functions.len(), generated.globals.len(), generated.traits.len(), generated.vtables.len());
    if action == "codegen" { return Ok(0); }
    let stdout = Arc::new(Mutex::new(Vec::<u8>::new()));
    let stderr = Arc::new(Mutex::new(Vec::<u8>::new()));
    type Mem = minirust_rs::mem::BasicMemory<minirust_rs::prelude::x86_64>;
    let init = minirust_rs::lang::Machine::<Mem>::new(generated,
        libspecr::DynWrite::new(SharedWriter(stdout.clone())),
        libspecr::DynWrite::new(SharedWriter(stderr.clone()))).get_internal();
    let mut machine = match init {
        Ok(m) => m,
        Err(e) => { fs::write(out.join("machine-result.txt"), format!("initialization: {e:?}"))?;
                    println!("machine=initialization-rejected"); return Ok(6); }
    };
    for steps in 0..10000 {
        match machine.step().get_internal() {
            Ok(()) => continue,
            Err(e) => {
                fs::write(out.join("machine-result.txt"), format!("steps={} result={e:?}\n", steps + 1))?;
                fs::write(out.join("machine.stdout"), stdout.lock().map_err(|_| anyhow::anyhow!("stdout poisoned"))?.clone())?;
                fs::write(out.join("machine.stderr"), stderr.lock().map_err(|_| anyhow::anyhow!("stderr poisoned"))?.clone())?;
                println!("machine_result={e:?} steps={}", steps + 1);
                return Ok(if matches!(e, minirust_rs::prelude::TerminationInfo::MachineStop) { 0 } else { 6 });
            }
        }
    }
    println!("machine=owned-step-bound-reached"); Ok(7)
}
fn main() -> ExitCode {
    match observe() {
        Ok(code) => ExitCode::from(code),
        Err(e) => { eprintln!("owned observer error: {e:#}"); ExitCode::from(8) }
    }
}
