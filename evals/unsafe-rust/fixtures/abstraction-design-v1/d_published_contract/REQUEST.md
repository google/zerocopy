# Published-contract redesign request

`Block`, its safety contract, and downstream implementations are published 1.x
commitments. The project promises ordinary SemVer compatibility throughout 1.x.
Repository search finds only `first`, which consumes less than the full
contract, but downstream consumers and implementations are not enumerable.

Review the current `Page` implementation and `first`, then explain what
proof-oriented simplification is possible in 1.x and what would require an
explicitly authorized 2.0 migration. No source edit or major release has been
authorized. Scope: Rust 1.70+, all targets/profiles.

