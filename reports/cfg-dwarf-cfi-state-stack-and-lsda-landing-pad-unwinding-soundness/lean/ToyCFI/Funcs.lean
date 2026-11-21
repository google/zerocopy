import ToyCFI.Generator

/-!
# Example functions used throughout the package
-/

namespace Toy.CFI

/-- Frame-pointer prologue with a call, an epilogue, and a cold block that is
entered with the frame established and jumps back to the epilogue.

* block 0 (prologue): `push fp; movReg fp sp; call`, successors `[1, 2]`;
* block 1 (epilogue): `movReg sp fp; pop fp; ret`;
* block 2 (cold): `call`, successor `[1]`. -/
def coldBlocks : List Block :=
  [⟨[.push .fp, .movReg .fp .sp, .call], [1, 2]⟩,
   ⟨[.movReg .sp .fp, .pop .fp, .ret], []⟩,
   ⟨[.call], [1]⟩]

/-- Layout `0, 1, 2`: the epilogue physically precedes the cold block.
Addresses: block 0 at 0–2, block 1 at 3–5 (`ret` at 5), block 2 at 6. -/
def coldFn : Func := { blocks := coldBlocks, layout := [0, 1, 2] }

/-- Layout `0, 2, 1`: the cold block follows the prologue (the CFG order).
Addresses: block 0 at 0–2, block 2 at 3, block 1 at 4–6. -/
def coldFnFallthrough : Func := { blocks := coldBlocks, layout := [0, 2, 1] }

/-- Stack-probing loop with a frame-pointer anchor:

* block 0: `push fp; movReg fp sp`, successor `[1]`;
* block 1 (loop): `subSp page`, successors `[1, 2]`;
* block 2: `movReg sp fp; pop fp; ret`.

Addresses: block 0 at 0–1, block 1 at 2, block 2 at 3–5. -/
def probeFn (page : Nat) : Func :=
  { blocks := [⟨[.push .fp, .movReg .fp .sp], [1]⟩, ⟨[.subSp page], [1, 2]⟩,
      ⟨[.movReg .sp .fp, .pop .fp, .ret], []⟩],
    layout := [0, 1, 2] }

/-- Two paths with different frame states merge: block 1 pushes `fp`, block 2
does not, both continue to block 3.

Addresses: block 0 at 0, block 1 at 1, block 2 at 2, block 3 at 3. -/
def mergeFn : Func :=
  { blocks := [⟨[.call], [1, 2]⟩, ⟨[.push .fp], [3]⟩, ⟨[.call], [3]⟩, ⟨[.ret], []⟩],
    layout := [0, 1, 2, 3] }

/-- Balanced variant of `mergeFn`: block 2 also pushes `fp`. -/
def mergeFnBalanced : Func :=
  { blocks := [⟨[.call], [1, 2]⟩, ⟨[.push .fp], [3]⟩, ⟨[.push .fp], [3]⟩, ⟨[.ret], []⟩],
    layout := [0, 1, 2, 3] }

end Toy.CFI
