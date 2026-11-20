#!/usr/bin/env python3
"""Generate a Rust function with N sequential two-way joins, each merging loans of two owners.

Every block borrows from `a` or `b` depending on a runtime condition, uses the
reference, and then mutates `a` after the reference is dead, so the program is
accepted by every borrow-checker configuration.
"""
import sys
n = int(sys.argv[1])
out = ["pub fn joins(c: &[bool], mut a: Vec<u32>, b: Vec<u32>) -> u32 {", "    let mut acc = 0u32;"]
for i in range(n):
    out.append(f"    let r{i}: &u32 = if c[{i} % c.len()] {{ &a[0] }} else {{ &b[0] }};")
    out.append(f"    acc = acc.wrapping_add(*r{i});")
    out.append(f"    a.push(acc);")
out.append("    acc")
out.append("}")
print("\n".join(out))
