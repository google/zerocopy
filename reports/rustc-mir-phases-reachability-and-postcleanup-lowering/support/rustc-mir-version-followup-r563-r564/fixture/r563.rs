fn marker() {}

fn constant_branch() {
    if false {
        marker();
    }
}

fn after_return() {
    return;
    #[allow(unreachable_code)]
    marker();
}

fn diverges() -> ! {
    loop {}
}

fn after_diverge() {
    diverges();
    #[allow(unreachable_code)]
    marker();
}

fn dynamic_branch(x: bool) {
    if x {
        marker();
    }
}
