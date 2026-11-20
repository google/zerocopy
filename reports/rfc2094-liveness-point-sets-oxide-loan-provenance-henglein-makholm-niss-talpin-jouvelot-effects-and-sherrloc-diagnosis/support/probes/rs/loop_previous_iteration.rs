// A mutable loan created in a loop body is stored in a vector that outlives the iteration.
pub fn previous_iteration() {
    let mut x = 0u32;
    let mut v: Vec<&mut u32> = Vec::new();
    for _ in 0..2 {
        v.push(&mut x);
    }
}
