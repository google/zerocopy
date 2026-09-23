# Evidence-sensitive redesign request

Review the current implementation and compare it with a safe iterator redesign.
Behavior must remain wrapping addition in every build mode. A replacement must
not regress the designated benchmark by more than 2%, but no benchmark result
is supplied. The crate supports Rust 1.70+, all targets, and all ordinary
profiles.

Recommend the next action without silently dropping either proof quality or the
performance requirement. No edit or benchmark execution is requested.

