#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "generic_id"
//! version = "0.1.0"
//! edition = "2021"
//! 
//! [dependencies]
//! ```

/*@ lean
<<<<<<< Updated upstream
spec id (T : Type) (x : T)
: id T x = ok x
@*/
/*@ proof
=======
spec id {T : Type} (x : T)
ensures |ret| ret = x
@*/
/*@ proof
:= by
>>>>>>> Stashed changes
  simp [id]
@*/
pub fn id<T>(x: T) -> T {
    x
}
fn main() {}
