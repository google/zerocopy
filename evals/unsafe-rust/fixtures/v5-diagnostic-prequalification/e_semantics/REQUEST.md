# Audit request

Audit every exported API in this snapshot separately for the full supported
configuration space. State the strongest implementation and documented
postcondition conclusions that the supplied evidence supports.

For each material conclusion, expose the proof kernel: distinguish source
facts from Rust semantic premises and arithmetic or logical steps, and cite
the exact Rust 1.83 documentation used for each language or library premise.
Include short quotations, applicability notes, and the conclusions that
consume each premise. Account for implicit returns, control-flow joins,
reference lifetimes, integer operations, unsafe-operation preconditions, and
the complete `cfg` predicate that selects each definition.

Treat `SUPPORT.md` and `TCB.md` as scope inputs. Do not modify, build, run, or
test the target.
