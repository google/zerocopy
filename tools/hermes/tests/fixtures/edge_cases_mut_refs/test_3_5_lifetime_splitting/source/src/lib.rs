
pub fn partial_mut<'a, 'b>(x: &'a mut u32, y: &'b mut u32) {
    if *x > 10 {
        *y += 1;
    } else {
        *x += 1;
    }
}
