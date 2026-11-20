// Question: is an implicit reborrow of a `&mut` argument (no autoref, no explicit `&mut`) two-phase?
pub fn f(v: &mut Vec<usize>) {
    Vec::push(v, v.len());
}
