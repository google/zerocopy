import ToyTailCall.Machine

/-!
# Call-site inlining of a function that contains tail calls

`inlineCallSite mode p c k` splices the callee `g` of the instruction `call g args dst next`
at `pc = k` of function `c` into `c`, in the style of a `Call`/`Return` splice:
* `g`'s slots are appended to `c`'s slots (renamed by `+ nSlots c`), followed by temporaries
  without destructors; a prologue resets them (storage-live) and assigns the arguments to the
  renamed parameters;
* `g`'s `ret op` becomes `T := op; dropSlots (g's slots, reverse declaration order);
  dst := move T; goto next`;
* `g`'s `tailCall h args` becomes, depending on `mode`,
  - `naive`: `tailCall h args` (unchanged apart from renaming), now executed in `c`'s frame;
  - `corrected`: `tᵢ := argᵢ` (all arguments first), `dropSlots (g's slots, reverse
    declaration order)`, then `call h [move tᵢ] dst next` — that is, pre-jump finalization of
    the callee's slots, then `Call`, whose continuation `next` is the `Goto(after_call)`.

Each instruction of `g` is placed in a block of fixed size `K` (padded with unreachable
`panic`s), so `g`'s `pc q` becomes `gStart + K * q`. If the site is not a well-formed call of
another function, the program is returned unchanged.

`inlineTailSite mode p c k` first rewrites a `tailCall g args` at `pc = k` into its pre-jump
reading as code (`desugarTailSite`: evaluate the arguments into fresh slots, drop `c`'s owned
slots, `call g`, then `ret` the result) and then applies `inlineCallSite mode` at the created
`call`. Only the `corrected` mode at such a site is the subject of a result here.
-/

namespace Toy.TailCall

inductive SpliceMode where
  | naive
  | corrected
  deriving DecidableEq, Repr

def renOp (off : Nat) : Operand → Operand
  | .const n => .const n
  | .copy s => .copy (s + off)
  | .move s => .move (s + off)
  | .addrOf s => .addrOf (s + off)
  | .deref s => .deref (s + off)
  | .succ s => .succ (s + off)

/-- Largest arity of a `tailCall` in `code`. -/
def maxTailArity : List Instr → Nat
  | [] => 0
  | .tailCall _ args :: is => max args.length (maxTailArity is)
  | _ :: is => maxTailArity is

/-- `assign (t + i) (ren aᵢ) (base + i + 1)` for each argument `aᵢ`. -/
def assignTemps (off t base : Nat) : Nat → List Operand → List Instr
  | _, [] => []
  | i, a :: as => .assign (t + i) (renOp off a) (base + i + 1) :: assignTemps off t base (i + 1) as

/-- The spliced block for `g`'s instruction at `pc q`. `nC`/`nG`: slot counts of `c`/`g`;
`gStart`, `K`: layout of the spliced body; `dst`, `next`: the call site's destination and
continuation. -/
def spliceInstr (mode : SpliceMode) (nC nG gStart K dst next q : Nat) : Instr → List Instr
  | .assign d op n => [.assign (d + nC) (renOp nC op) (gStart + K * n)]
  | .emit k n => [.emit k (gStart + K * n)]
  | .branchLt s k t e => [.branchLt (s + nC) k (gStart + K * t) (gStart + K * e)]
  | .goto n => [.goto (gStart + K * n)]
  | .reset ss n => [.reset (ss.map (· + nC)) (gStart + K * n)]
  | .dropSlots ss n => [.dropSlots (ss.map (· + nC)) (gStart + K * n)]
  | .call f args d n => [.call f (args.map (renOp nC)) (d + nC) (gStart + K * n)]
  | .panic => [.panic]
  | .ret op =>
    let base := gStart + K * q
    [.assign (nC + nG) (renOp nC op) (base + 1),
     .dropSlots ((List.range nG).reverse.map (· + nC)) (base + 2),
     .assign dst (.move (nC + nG)) next]
  | .tailCall h args =>
    match mode with
    | .naive => [.tailCall h (args.map (renOp nC))]
    | .corrected =>
      let base := gStart + K * q
      let t := nC + nG + 1
      assignTemps nC t base 0 args ++
      [.dropSlots ((List.range nG).reverse.map (· + nC)) (base + args.length + 1),
       .call h ((List.range args.length).map fun i => .move (t + i)) dst next]

/-- Pad a block to length `K` with unreachable `panic`s. -/
def padBlock (K : Nat) (l : List Instr) : List Instr := l ++ List.replicate (K - l.length) .panic

def spliceBody (mode : SpliceMode) (nC nG gStart K dst next : Nat) : Nat → List Instr → List Instr
  | _, [] => []
  | q, i :: is => padBlock K (spliceInstr mode nC nG gStart K dst next q i) ++
      spliceBody mode nC nG gStart K dst next (q + 1) is

/-- `c` with the call `call g args dst next` at `pc = k` replaced by `g`'s spliced body. -/
def spliceFn (mode : SpliceMode) (c g : Fn) (k : Nat) (args : List Operand) (dst next : Nat) : Fn :=
  let nC := c.nSlots
  let nG := g.nSlots
  let nT := maxTailArity g.code + 1
  let L := c.code.length
  let gStart := L + 1 + args.length
  let K := maxTailArity g.code + 3
  let prologue := .reset ((List.range (nG + nT)).map (· + nC)) (L + 1) ::
    assignTemps 0 nC (L + 1) 0 args
  { c with
    dtors := c.dtors ++ g.dtors ++ List.replicate nT .none
    code := c.code.set k (.goto L) ++ prologue ++ spliceBody mode nC nG gStart K dst next 0 g.code }

/-- Inline the callee of the `call` at `pc = k` of function `ci` (see the module docstring). -/
def inlineCallSite (mode : SpliceMode) (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.call g args dst next) =>
      if g = ci then p else
      match p.fns[g]? with
      | none => p
      | some gf =>
        if args.length = gf.nParams ∧ gf.nParams ≤ gf.nSlots ∧ dst < c.nSlots then
          ⟨p.fns.set ci (spliceFn mode c gf k args dst next)⟩
        else p
    | _ => p

/-- The `pc` of the `call` that `desugarTailSite` creates for a tail call with `a` arguments
in a function with `L` instructions. -/
def desugaredCallPc (L a : Nat) : Nat := L + a + 1

/-- Rewrite `tailCall g args` at `pc = k` of `ci` into its pre-jump reading as code:
`goto L; L: tᵢ := argᵢ; dropSlots (ci's slots, reverse declaration order);
call g [move tᵢ] y (L+a+2); ret (move y)`, with fresh slots `tᵢ`, `y` without destructors. -/
def desugarTailSite (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.tailCall g args) =>
      let nC := c.nSlots
      let a := args.length
      let y := nC + a
      let L := c.code.length
      let tail := assignTemps 0 nC L 0 args ++
        [.dropSlots ((List.range nC).reverse) (L + a + 1),
         .call g ((List.range a).map fun i => .move (nC + i)) y (L + a + 2),
         .ret (.move y)]
      ⟨p.fns.set ci { c with dtors := c.dtors ++ List.replicate (a + 1) .none,
                             code := c.code.set k (.goto L) ++ tail }⟩
    | _ => p

/-- Inline the callee of the `tailCall` at `pc = k` of `ci`: `desugarTailSite`, then
`inlineCallSite mode` at the created `call`. -/
def inlineTailSite (mode : SpliceMode) (p : Prog) (ci k : Nat) : Prog :=
  match p.fns[ci]? with
  | none => p
  | some c =>
    match c.code[k]? with
    | some (.tailCall _ args) =>
      inlineCallSite mode (desugarTailSite p ci k) ci (desugaredCallPc c.code.length args.length)
    | _ => p

end Toy.TailCall
