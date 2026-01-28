use enum_dispatch::enum_dispatch;

#[enum_dispatch(Application)]
enum App {
    Menu,
    #[cfg(test)]
    DebugClock,
    #[cfg(not(test))]
    Clock,
}

#[enum_dispatch]
trait Application {
    fn run(self) -> usize;
}

struct Menu;
#[cfg(test)]
struct DebugClock;
#[cfg(not(test))]
struct Clock;

impl Application for Menu {
    fn run(self) -> usize {
        0
    }
}

#[cfg(test)]
impl Application for DebugClock {
    fn run(self) -> usize {
        1
    }
}

#[cfg(not(test))]
impl Application for Clock {
    fn run(self) -> usize {
        2
    }
}

#[test]
fn main() {
    use std::convert::TryInto;

    let menu = Menu;
    let app: App = menu.into();
    let menu: Menu = app.try_into().unwrap();
    assert_eq!(menu.run(), 0);

    #[cfg(test)]
    {
        let clock = DebugClock;
        let app: App = clock.into();
        let clock: DebugClock = app.try_into().unwrap();
        assert_eq!(clock.run(), 1);
    }

    #[cfg(not(test))]
    {
        let clock = Clock;
        let app: App = clock.into();
        let clock: Clock = app.try_into().unwrap();
        assert_eq!(clock.run(), 2);
    }
}
