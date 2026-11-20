// A loan created in a loop body is used on a later iteration (back edge).
pub fn later_iteration(items: &mut Vec<String>) {
    let mut keep: Vec<&String> = Vec::new();
    for i in 0..3 {
        items.push(i.to_string());
        keep.push(&items[0]);
    }
}
