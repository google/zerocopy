fn main() { let mut b=Box::new(41u32); *b+=1; assert!(*b == 42); drop(b); }
