// The pattern targeted by the former `mutable_borrow_reservation_conflict` lint:
// a shared borrow created *before* the reservation is used *during* the reservation.
pub fn f() -> Vec<usize> {
    let mut v = vec![0, 1, 2];
    let shared = &v;
    v.push(shared.len());
    v
}
