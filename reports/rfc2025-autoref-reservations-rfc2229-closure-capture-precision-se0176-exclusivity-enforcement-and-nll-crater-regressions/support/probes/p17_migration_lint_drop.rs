// Drop-order change detected by the 2021 migration lint (compile with --edition 2018).
pub struct FancyInteger(pub i32);
impl Drop for FancyInteger { fn drop(&mut self) { println!("Just dropped {}", self.0); } }
pub struct Point { pub x: FancyInteger, pub y: FancyInteger }
pub fn f() {
    let p = Point { x: FancyInteger(10), y: FancyInteger(20) };
    let c = || { let _x = p.x; };
    c();
}
