trait Ordinary {}
struct Node;
impl Ordinary for Node where Node: Ordinary {}
fn main() {}
