// Example quoted in the Rust blog post "Enabling the next iteration of the borrow checker
// on nightly" (2026-08-04) as accepted by legacy Polonius but rejected by Polonius Alpha:
// a conditional reborrow inside a loop.
pub struct X { next: Option<Box<X>> }
pub fn conditional() {
    let mut b = Some(Box::new(X { next: None }));
    let mut p = &mut b;
    while let Some(now) = p {
        if true {
            p = &mut now.next;
        }
    }
}
