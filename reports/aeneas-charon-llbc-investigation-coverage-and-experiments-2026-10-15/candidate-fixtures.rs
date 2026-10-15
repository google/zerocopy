// Candidate research inputs only: not compiled, extracted or verified here.
// Their expected behavior must be checked against an independent Rust oracle.

pub fn pick_mut<'a>(left: &'a mut u8, right: &'a mut u8, choose_left: bool) -> &'a mut u8 {
    if choose_left { left } else { right }
}

pub fn update_chosen(mut left: u8, mut right: u8, choose_left: bool, value: u8) -> (u8, u8) {
    *pick_mut(&mut left, &mut right, choose_left) = value;
    (left, right)
}

pub enum Slot<T> { Empty, Present(T) }

pub fn enum_borrow(slot: &mut Slot<(u8, u8)>) -> Option<&mut u8> {
    match slot {
        Slot::Empty => None,
        Slot::Present(pair) => Some(&mut pair.1),
    }
}

pub fn nested_update(pair: &mut (u8, u8), value: u8) {
    let mut inner = &mut pair.1;
    let outer = &mut inner;
    **outer = value;
}

pub fn loop_borrow(pair: &mut (u8, u8), mut count: u8) {
    let field = &mut pair.1;
    while count != 0 {
        *field = field.wrapping_add(1);
        count -= 1;
    }
}

pub fn generic_identity<T>(value: T) -> T { value }

pub fn borrowed_instantiation(value: &mut u8, replacement: u8) {
    *generic_identity(value) = replacement;
}

pub fn fnmut_unit(start: u8) -> u8 {
    let mut value = start;
    let mut increment = || { value = value.wrapping_add(1); };
    increment();
    increment();
    value
}

// The observable cleanup trace intentionally exceeds a value-only interface.
// Run independently in unwind and abort configurations; abort is process-level.
pub fn drop_trace(panic_now: bool, trace: &std::cell::RefCell<Vec<u8>>) {
    struct Marker<'a>(u8, &'a std::cell::RefCell<Vec<u8>>);
    impl Drop for Marker<'_> {
        fn drop(&mut self) { self.1.borrow_mut().push(self.0); }
    }
    let first = Marker(1, trace);
    let second = Marker(2, trace);
    let _moved = first;
    assert!(!panic_now);
    drop(second);
}
