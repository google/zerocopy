//! Valid-program target observations. Rust 1.89.0, edition 2021, std only.
//! This is a finite experiment, not an all-target semantics theorem.

mod layout;
mod numeric;
mod readiness;
mod wide_copy_drop;

pub struct Harness {
    checks: usize,
    failures: usize,
}

impl Harness {
    pub fn check(&mut self, name: &str, passed: bool) {
        self.checks += 1;
        if !passed {
            self.failures += 1;
        }
        println!("CHECK {}={}", name, if passed { "PASS" } else { "FAIL" });
    }
}

fn main() {
    println!("META suite=valid-target-v1");
    println!("META arch={}", std::env::consts::ARCH);
    println!("META os={}", std::env::consts::OS);
    println!("META endian={}", if cfg!(target_endian = "big") { "big" } else { "little" });
    println!("META pointer_bits={}", usize::BITS);
    println!("META debug_assertions={}", cfg!(debug_assertions));
    let mut h = Harness { checks: 0, failures: 0 };
    numeric::run(&mut h);
    layout::run(&mut h);
    readiness::run(&mut h);
    wide_copy_drop::run(&mut h);
    println!("SUMMARY checks={} failures={}", h.checks, h.failures);
    if h.failures != 0 {
        std::process::exit(1);
    }
}
