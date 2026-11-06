use std::arch::asm;

#[cfg(not(target_arch = "aarch64"))]
compile_error!("This register-only native probe requires AArch64.");

// Each block consumes initialized integer registers, changes declared outputs and
// condition flags, and neither dereferences pointers nor touches the stack.
// Early `out` on the preinitialized destination prevents overlap with any input.
#[inline(never)]
fn compute(op: &str, a: u64, b: u64, carry: u64) -> Result<(u64, u64), String> {
    let result: u64;
    let nzcv: u64;
    macro_rules! noflags_binary {
        ($instruction:literal) => {
            unsafe {
                asm!("cmp xzr, xzr", "mov {result}, #-1", $instruction, "mrs {nzcv}, nzcv",
                    a = in(reg) a, b = in(reg) b,
                    result = out(reg) result, nzcv = lateout(reg) nzcv,
                    options(nomem, nostack));
            }
        }
    }
    macro_rules! noflags_unary {
        ($instruction:literal) => {
            unsafe {
                asm!("cmp xzr, xzr", "mov {result}, #-1", $instruction, "mrs {nzcv}, nzcv",
                    a = in(reg) a,
                    result = out(reg) result, nzcv = lateout(reg) nzcv,
                    options(nomem, nostack));
            }
        }
    }
    match op {
        "adds64" => unsafe {
            asm!("cmp xzr, xzr", "adds {result}, {a}, {b}", "mrs {nzcv}, nzcv",
                a = in(reg) a, b = in(reg) b,
                result = lateout(reg) result, nzcv = lateout(reg) nzcv,
                options(nomem, nostack));
        },
        "adcs64" => unsafe {
            // carry is restricted by main to 0 or 1. CMP carry,#1 sets C=carry.
            asm!("cmp {carry}, #1", "adcs {result}, {a}, {b}", "mrs {nzcv}, nzcv",
                a = in(reg) a, b = in(reg) b, carry = in(reg) carry,
                result = lateout(reg) result, nzcv = lateout(reg) nzcv,
                options(nomem, nostack));
        },
        "add32" => noflags_binary!("add {result:w}, {a:w}, {b:w}"),
        "lslv64" => noflags_binary!("lslv {result}, {a}, {b}"),
        "lslv32" => noflags_binary!("lslv {result:w}, {a:w}, {b:w}"),
        "rev64" => noflags_unary!("rev {result}, {a}"),
        "rev32" => noflags_unary!("rev {result:w}, {a:w}"),
        _ => return Err(format!("unknown op {op}")),
    }
    Ok((result, (nzcv >> 28) & 15))
}

fn run() -> Result<(), String> {
    let path = std::env::args().nth(1).ok_or("expected cases.tsv path")?;
    let input = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    for line in input.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        if fields.len() != 5 { return Err("expected five TSV fields".into()); }
        let a = fields[2].parse::<u64>().map_err(|e| e.to_string())?;
        let b = fields[3].parse::<u64>().map_err(|e| e.to_string())?;
        let carry = fields[4].parse::<u64>().map_err(|e| e.to_string())?;
        if carry > 1 { return Err("carry outside chosen domain".into()); }
        let (result, nzcv) = compute(fields[1], a, b, carry)?;
        println!("{}\t{}\t{}", fields[0], result, nzcv);
    }
    Ok(())
}
fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(msg) => { eprintln!("{msg}"); std::process::ExitCode::FAILURE }
    }
}
