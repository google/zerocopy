#!/usr/bin/env python3
"""Generate a synthetic Rust library exercising the borrow-checker relaxations.

The crate contains N copies of a module with: nested `&mut self` method calls
(two-phase borrows), overloaded compound assignment, closures that use disjoint
fields of a struct, a loop that walks a linked list by reassigning a `&mut`
(NLL problem case #4), and a conditional map lookup (NLL problem case #2).
Every function is accepted by both the NLL and the Polonius-based checker and in
both editions 2018 and 2021 (closures only capture whole locals that are not
otherwise borrowed). This is a synthetic workload, not a real crate.
"""
import sys

N = int(sys.argv[1])
out = sys.argv[2]

HEADER = """#![allow(dead_code, unused)]
use std::collections::HashMap;
use std::ops::AddAssign;
"""

TEMPLATE = """
pub mod m{i} {{
    use super::*;
    pub struct W(pub Vec<usize>);
    impl W {{ pub fn len(&self) -> usize {{ self.0.len() }} pub fn push(&mut self, x: usize) {{ self.0.push(x) }} }}
    impl AddAssign<usize> for W {{ fn add_assign(&mut self, n: usize) {{ self.0.push(n) }} }}
    pub struct S {{ pub a: Vec<u32>, pub b: Vec<u32>, pub c: u32 }}
    pub struct List {{ pub value: u32, pub next: Option<Box<List>> }}
    pub fn two_phase(w: &mut W, v: &mut Vec<usize>) -> usize {{
        v.push(v.len());
        w.push(w.len());
        *w += w.len();
        v.push(v.len() + w.len());
        v.len() + w.len()
    }}
    pub fn closures(s: S) -> u32 {{
        let S {{ mut a, b, c }} = s;
        let f = |x: u32| x + c + b.len() as u32;
        a.retain(|i| *i < f(*i));
        let g = move || a.len() as u32 + c;
        g()
    }}
    pub fn walk(mut list: &mut List) -> Vec<&mut u32> {{
        let mut result = vec![];
        loop {{
            result.push(&mut list.value);
            if let Some(n) = list.next.as_mut() {{ list = n; }} else {{ return result; }}
        }}
    }}
    pub fn lookup(map: &mut HashMap<u32, u32>, key: u32) -> u32 {{
        match map.get_mut(&key) {{
            Some(v) => {{ *v += 1; *v }}
            None => {{ map.insert(key, 0); 0 }}
        }}
    }}
}}
"""

with open(out, "w") as f:
    f.write(HEADER)
    for i in range(N):
        f.write(TEMPLATE.format(i=i))
