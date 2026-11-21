import ToyLayoutDfa.Basic

/-!
# Fixture layouts

Small concrete layout automata used by the examples, counterexamples and non-vacuity
witnesses. Each is meant to capture the bit-validity automaton of a familiar fixed-size
type; the Rust type named in each doc comment is an intended reading, not a proved
correspondence.
-/

namespace Toy.LayoutDfa

/-- All 257 symbols: the 256 byte values followed by `uninit`. -/
def allSyms : List Sym :=
  (List.finRange 256).map Sym.byte ++ [Sym.uninit]

/-- One edge per initialised byte value from `q` to `q'`. -/
def byteEdges (q q' : Nat) : List (Nat × Sym × Nat) :=
  (List.finRange 256).map (fun b => (q, Sym.byte b, q'))

/-- One edge per symbol (all 256 byte values and `uninit`) from `q` to `q'`: a position
that may hold any byte or be uninitialised (a padding byte). -/
def anyEdges (q q' : Nat) : List (Nat × Sym × Nat) :=
  allSyms.map (fun s => (q, s, q'))

/-- `()`: the empty layout; start = accept, no edges; language `{[]}`. -/
def unitL : Layout := ⟨0, 0, []⟩

/-- `u8`: one initialised byte, any value. -/
def u8L : Layout := ⟨0, 1, byteEdges 0 1⟩

/-- `bool`: one initialised byte, value 0 or 1. -/
def boolL : Layout := ⟨0, 1, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1)]⟩

/-- `u16`: two initialised bytes, any values. -/
def u16L : Layout := ⟨0, 2, byteEdges 0 1 ++ byteEdges 1 2⟩

/-- A two-byte type with one initialised byte followed by one padding byte (for example
`#[repr(C, align(2))] struct Dst(u8)`): byte 0 any value, byte 1 any symbol. -/
def u8PadL : Layout := ⟨0, 2, byteEdges 0 1 ++ anyEdges 1 2⟩

/-- `MaybeUninit<u8>`: one byte, any symbol including `uninit`. -/
def mu8L : Layout := ⟨0, 1, anyEdges 0 1⟩

/-! ### Small hand-made automata (over byte values 0, 1, 2 and `uninit`) -/

/-- One initialised byte with value 0. Language `{[0]}`. -/
def b0L : Layout := ⟨0, 1, [(0, Sym.byte 0, 1)]⟩

/-- One initialised byte with value 1. Language `{[1]}`. -/
def b1L : Layout := ⟨0, 1, [(0, Sym.byte 1, 1)]⟩

/-- One uninitialised byte. Language `{[uninit]}`. A position with an `uninit` edge but no
byte-value edges is not initialisation-monotone (rustc's uninit byte range covers every
value); `mu8L` is the monotone counterpart. -/
def uL : Layout := ⟨0, 1, [(0, Sym.uninit, 1)]⟩

/-- Byte 0 followed by an uninitialised byte. Language `{[0, uninit]}` (second position not
initialisation-monotone, as for `uL`). -/
def b0uL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (1, Sym.uninit, 2)]⟩

/-- `bool` followed by a position whose single edge is labelled `uninit`. Language
`{[0, uninit], [1, uninit]}` (second position not initialisation-monotone, as for `uL`). -/
def boolUL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1), (1, Sym.uninit, 2)]⟩

/-- Two `bool` bytes. Language `{[0,0], [0,1], [1,0], [1,1]}`. -/
def bool2L : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 1), (1, Sym.byte 0, 2), (1, Sym.byte 1, 2)]⟩

/-- A dead branch: byte 0 leads to state 1, which has no edges and is not accepting; byte
1 leads to the accept state. Language `{[1]}`; state 1 is reachable but not live. -/
def deadL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 2)]⟩

/-- A deterministic source with language `{[0, 1], [0, 2]}`. -/
def ndSrcL : Layout :=
  ⟨0, 3, [(0, Sym.byte 0, 1), (1, Sym.byte 1, 3), (1, Sym.byte 2, 3)]⟩

/-- A nondeterministic destination with the same language `{[0, 1], [0, 2]}`: byte 0
from the start leads to two different states, one with a single edge labelled 1, the other
with a single edge labelled 2. -/
def ndDstL : Layout :=
  ⟨0, 3, [(0, Sym.byte 0, 1), (0, Sym.byte 0, 2), (1, Sym.byte 1, 3), (2, Sym.byte 2, 3)]⟩

/-- A five-byte chain with language `{[0, 0, 0, 0, 1]}`. -/
def chainL : Layout :=
  ⟨0, 5, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 2), (2, Sym.byte 0, 3), (3, Sym.byte 0, 4),
    (4, Sym.byte 1, 5)]⟩

/-- A cyclic, deterministic automaton with three edges: byte 0, then any number of further
0 bytes (a self-loop), then byte 1. Language: `0 0* 1` (unbounded word length; not a
fixed-size layout). -/
def cycL : Layout := ⟨0, 2, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1), (1, Sym.byte 1, 2)]⟩

/-- An uninhabited layout (meant to capture `!`): start state 0, accept state 1, no edges.
Language empty; it has no branches at all, and it is not `ReachableLive` because its start
state cannot reach the accept state. -/
def neverL : Layout := ⟨0, 1, []⟩

/-- A deterministic, acyclic destination whose words have two different lengths: byte 0
leads straight to the accept state, byte 1 leads to a state whose single edge (byte 1)
leads to the accept state. Language `{[0], [1, 1]}`. -/
def varDstL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 2), (0, Sym.byte 1, 1), (1, Sym.byte 1, 2)]⟩

/-- A deterministic source with language `{[0, 0], [1, 1]}`. -/
def pairSrcL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 3), (1, Sym.byte 0, 2), (3, Sym.byte 1, 2)]⟩

/-- `cycL` with its first edge listed three times: the same edge set and language as
`cycL`, a longer edge list. -/
def cycDupL : Layout :=
  ⟨0, 2, [(0, Sym.byte 0, 1), (0, Sym.byte 0, 1), (0, Sym.byte 0, 1), (1, Sym.byte 0, 1),
    (1, Sym.byte 1, 2)]⟩

/-- A deterministic layout of fixed size 1 with a reachable dead self-loop: byte 0 leads to the
accept state; byte 1 leads to state 2, whose single edge (byte 1) returns to state 2.
Language `{[0]}`; not `Acyclic`. -/
def deadCycReachL : Layout :=
  ⟨0, 1, [(0, Sym.byte 0, 1), (0, Sym.byte 1, 2), (2, Sym.byte 1, 2)]⟩

end Toy.LayoutDfa
