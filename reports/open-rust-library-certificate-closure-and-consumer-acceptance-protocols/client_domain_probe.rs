use std::cell::Cell;
trait Source { fn value(&self) -> u8; }
struct One;
struct Zero;
impl Source for One { fn value(&self) -> u8 { 1 } }
impl Source for Zero { fn value(&self) -> u8 { 0 } }
fn generic<S: Source>(s: &S) -> u8 { s.value() }
fn dynamic(s: &dyn Source) -> u8 { s.value() }
fn length<const N: usize>(_: [u8; N]) -> usize { N }
struct Record { pub value: u8 }
fn observe_callback(record: &mut Record, f: impl FnOnce(&mut Record)) -> u8 {
    f(record);
    record.value
}
struct Guard<'a>(&'a Cell<u32>);
impl Drop for Guard<'_> { fn drop(&mut self) { self.0.set(self.0.get() + 1); } }
fn main() {
    assert_eq!((generic(&One), generic(&Zero), dynamic(&Zero)), (1, 0, 0));
    assert_eq!((length([]), length([0; 3])), (0, 3));
    let mut record = Record { value: 1 };
    record.value = 0;
    assert_eq!(observe_callback(&mut record, |r| r.value = 2), 2);
    let drops = Cell::new(0);
    { let _guard = Guard(&drops); assert_eq!(drops.get(), 0); }
    assert_eq!(drops.get(), 1);
    std::mem::forget(Guard(&drops));
    assert_eq!(drops.get(), 1);
    println!("generic=1,0; dynamic=0; const_lengths=0,3; callback=2; drops=1; forget=1");
}
