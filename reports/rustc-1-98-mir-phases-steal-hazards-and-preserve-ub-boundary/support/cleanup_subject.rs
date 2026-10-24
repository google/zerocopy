#![no_std]

pub struct EffectLog {
    pub step_count: u32,
    pub trace_acc: u32,
}

impl EffectLog {
    #[inline(never)]
    pub fn record(&mut self, tag: u32) {
        self.step_count = self.step_count.wrapping_add(1);
        self.trace_acc = self.trace_acc.wrapping_mul(16).wrapping_add(tag);
    }
}

pub struct Guard<'a> {
    pub drop_tag: u32,
    pub log: &'a mut EffectLog,
}

impl<'a> Drop for Guard<'a> {
    #[inline(never)]
    fn drop(&mut self) {
        self.log.record(self.drop_tag);
    }
}

pub struct PairGuards<'a> {
    pub first: Guard<'a>,
    pub second: Guard<'a>,
}

#[inline(never)]
pub fn may_unwind_op(trigger_panic: bool, marker: u32) -> u32 {
    if trigger_panic {
        panic!("selected unwind path");
    }
    marker.wrapping_add(100)
}

pub fn partial_init_move_cleanup(
    move_first_early: bool,
    trigger_panic: bool,
    log1: &mut EffectLog,
    log2: &mut EffectLog,
) -> u32 {
    let pair = PairGuards {
        first: Guard { drop_tag: 1, log: log1 },
        second: Guard { drop_tag: 2, log: log2 },
    };
    if move_first_early {
        let moved_first = pair.first;
        moved_first.log.record(10);
        drop(moved_first);
    }
    let out = may_unwind_op(trigger_panic, 5);
    out
}

pub fn partial_field_reinit_cleanup(
    trigger_panic: bool,
    log1: &mut EffectLog,
    log2: &mut EffectLog,
) -> u32 {
    let mut pair = PairGuards {
        first: Guard { drop_tag: 1, log: log1 },
        second: Guard { drop_tag: 2, log: log2 },
    };
    let moved_first = pair.first;
    moved_first.log.record(10);
    let saved_log1 = moved_first.log as *mut EffectLog;
    core::mem::forget(moved_first);
    // At this point `pair.first` is moved-out (uninitialized in drop tracking)
    // while `pair.second` is active. If `may_unwind_op` unwinds, only `pair.second`
    // is dropped. If `may_unwind_op` returns normally, `pair.first` is reinitialized.
    let out = may_unwind_op(trigger_panic, 7);
    pair.first = Guard {
        drop_tag: 3,
        log: unsafe { &mut *saved_log1 },
    };
    out
}

pub unsafe fn ub_boundary_probe(ptr: *const u32, flag: bool) -> u32 {
    let _ = unsafe { *ptr };
    if flag {
    } else {
    }
    0
}
