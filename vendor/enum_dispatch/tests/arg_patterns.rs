#![feature(box_patterns)]
use enum_dispatch::enum_dispatch;

struct AppState;

struct TupleStruct(usize, usize);

enum Format {
    _Raw(usize),
    _Pretty(usize),
}

enum Sentinel {
    _V,
}

#[enum_dispatch(AppActionEnum)]
trait AppAction {
    fn apply(&mut self, _target: &mut AppState) -> Result<(), String>;

    fn undo(&mut self, _: &mut AppState) -> Result<(), String>;

    fn redo(
        &mut self,
        target: &mut AppState,
        TupleStruct(_a, _): TupleStruct,
    ) -> Result<(), String> {
        self.apply(target)
    }

    fn merge(
        &mut self,
        _: &mut AppActionEnum,
        _: u32,
        _: &str,
        (_index1, _index2): (usize, usize),
    ) -> bool {
        false
    }

    fn batch(&mut self, [_foo, _bar]: [u8; 2], [_baz, ref _qux @ .., _quux]: &[u16; 6]) -> bool {
        false
    }

    fn format(
        &self,
        (Format::_Raw(max_len) | Format::_Pretty(max_len)): Format,
        box _f: Box<usize>,
        0..=255: u8,
        Sentinel::_V: Sentinel,
    ) -> Option<&str> {
        if max_len > 20 {
            Some("TODO")
        } else {
            None
        }
    }
}

struct Command;
impl AppAction for Command {
    fn apply(&mut self, _target: &mut AppState) -> Result<(), String> {
        Ok(())
    }

    fn undo(&mut self, _: &mut AppState) -> Result<(), String> {
        Ok(())
    }

    fn redo(
        &mut self,
        target: &mut AppState,
        TupleStruct(_a, _): TupleStruct,
    ) -> Result<(), String> {
        self.apply(target)
    }
}

#[enum_dispatch]
enum AppActionEnum {
    Command,
}

#[test]
fn main() {
    let mut a: AppActionEnum = Command.into();
    assert_eq!(false, a.batch([0, 1], &[2, 3, 4, 5, 6, 7]));
}
