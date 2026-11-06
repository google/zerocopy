use std::cell::RefCell;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    ConstructStart(u8),
    Constructed(u8),
    DropEnter(u8, u8),
    DropExit(u8, u8),
    Forgotten(u8),
    AfterScope,
}

thread_local! {
    static EVENTS: RefCell<Vec<Event>> = const { RefCell::new(Vec::new()) };
}

fn record(event: Event) {
    EVENTS.with(|events| events.borrow_mut().push(event));
}

struct Leaf {
    id: u8,
    payload: u8,
    panic_on_drop: bool,
}

impl Drop for Leaf {
    fn drop(&mut self) {
        record(Event::DropEnter(self.id, self.payload));
        self.payload = self.payload.wrapping_add(1);
        if self.panic_on_drop {
            panic!("selected destructor failure");
        }
        record(Event::DropExit(self.id, self.payload));
    }
}

fn make(id: u8, panic_on_construct: bool, panic_on_drop: bool) -> Leaf {
    record(Event::ConstructStart(id));
    if panic_on_construct {
        panic!("selected constructor failure");
    }
    record(Event::Constructed(id));
    Leaf { id, payload: id * 20 + 1, panic_on_drop }
}

struct Pair {
    first: Leaf,
    second: Leaf,
}

#[inline(never)]
fn exercise(second_panics: bool, forget_second: bool, first_drop_panics: bool) {
    {
        let pair = Pair {
            first: make(1, false, first_drop_panics),
            second: make(2, second_panics, false),
        };
        if forget_second {
            record(Event::Forgotten(pair.second.id));
            std::mem::forget(pair.second);
        }
        // The first leaf stays owned by pair until this scope ends.
        std::hint::black_box(pair.first.payload);
    }
    record(Event::AfterScope);
}

fn main() {
    use Event::*;
    std::panic::set_hook(Box::new(|_| {}));
    let prefix = vec![ConstructStart(1), Constructed(1), ConstructStart(2)];
    let cases = [
        ("normal", false, false, false, true,
            vec![Constructed(2), DropEnter(1, 21), DropExit(1, 22),
                 DropEnter(2, 41), DropExit(2, 42), AfterScope]),
        ("second_constructor_panics", true, false, false, false,
            vec![DropEnter(1, 21), DropExit(1, 22)]),
        ("forget_second", false, true, false, true,
            vec![Constructed(2), Forgotten(2), DropEnter(1, 21),
                 DropExit(1, 22), AfterScope]),
        ("first_destructor_panics", false, false, true, false,
            vec![Constructed(2), DropEnter(1, 21), DropEnter(2, 41), DropExit(2, 42)]),
    ];
    for (name, second_panics, forget_second, first_drop_panics, expected_ok, suffix) in cases {
        EVENTS.with(|events| events.borrow_mut().clear());
        let result = std::panic::catch_unwind(||
            exercise(second_panics, forget_second, first_drop_panics));
        let actual = EVENTS.with(|events| events.borrow().clone());
        let mut expected = prefix.clone();
        expected.extend(suffix);
        assert_eq!(result.is_ok(), expected_ok, "outcome for {name}");
        assert_eq!(actual, expected, "events for {name}");
        println!("{name}: returned={} events={actual:?}", result.is_ok());
    }
}
