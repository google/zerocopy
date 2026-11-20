// Rust analogue of SE-0176's `swap(&x, &x)` and `swap(&array[0], &array[1])` CONFLICT examples.
pub fn same() { let mut x = 0; std::mem::swap(&mut x, &mut x); }
pub fn elems() { let mut a = [1, 2]; std::mem::swap(&mut a[0], &mut a[1]); }
