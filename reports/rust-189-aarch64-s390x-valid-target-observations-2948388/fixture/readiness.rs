use crate::Harness;

// This metadata is a finite readiness model, not a Rust permission/provenance API.
struct Readiness<const N: usize> {
    initialized: [bool; N],
    readable: [bool; N],
    stable: [bool; N],
}

impl<const N: usize> Readiness<N> {
    fn allows(&self, start: usize, len: usize) -> bool {
        let end = match start.checked_add(len) { Some(end) => end, None => return false };
        if start > N || end > N { return false; }
        (start..end).all(|i| self.initialized[i] && self.readable[i] && self.stable[i])
    }
}

fn guarded_sum<const N: usize>(bytes: &[u8; N], ready: &Readiness<N>, start: usize, len: usize) -> Option<u32> {
    if !ready.allows(start, len) { return None; }
    let end = start.checked_add(len)?;
    // get() is checked independently; all actual source bytes are initialized.
    Some(bytes.get(start..end)?.iter().map(|x| u32::from(*x)).sum())
}

pub fn run(h: &mut Harness) {
    let ready = Readiness {
        initialized: [true, true, false, true, true, true, true, true],
        readable: [true, true, true, true, false, true, true, true],
        stable: [true, true, true, true, true, false, true, true],
    };
    let bytes = [10_u8, 20, 30, 40, 50, 60, 70, 80];
    for (name, start, len, expected) in [
        ("ready_prefix", 0, 2, true),
        ("uninitialized_mask", 2, 1, false),
        ("unreadable_mask", 4, 1, false),
        ("unstable_mask", 5, 1, false),
        ("ready_suffix", 6, 2, true),
        ("whole_range", 0, 8, false),
        ("empty_at_end", 8, 0, true),
        ("empty_outside", 9, 0, false),
        ("range_past_end", 7, 2, false),
        ("addition_overflow", usize::MAX, 1, false),
    ] {
        let actual = ready.allows(start, len);
        println!("OBS readiness.{} start={} len={} allowed={}", name, start, len, actual);
        h.check(&format!("readiness.{}", name), actual == expected);
    }
    h.check("readiness.guarded_sum_prefix", guarded_sum(&bytes, &ready, 0, 2) == Some(30));
    h.check("readiness.guarded_sum_denied", guarded_sum(&bytes, &ready, 2, 1).is_none());
    h.check("readiness.guarded_sum_empty", guarded_sum(&bytes, &ready, 8, 0) == Some(0));
    let empty = Readiness { initialized: [], readable: [], stable: [] };
    h.check("readiness.empty_allocation_model", empty.allows(0, 0) && !empty.allows(0, 1));
    h.check("control.array_presence_does_not_imply_model_readiness", bytes.get(2).is_some() && !ready.allows(2, 1));
}
