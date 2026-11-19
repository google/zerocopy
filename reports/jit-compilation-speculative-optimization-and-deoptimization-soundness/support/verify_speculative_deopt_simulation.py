#!/usr/bin/env python3
"""Executable model of speculative JIT compilation and deoptimization soundness.

This standalone probe (Python 3.10+, standard library only) contains:

* a small-step reference interpreter for a register bytecode with heap objects,
  mutable per-class method tables, recursive monitors, globals and an
  observable output trace;
* a speculative trace/method JIT that compiles function entries and loop
  headers (on-stack-replacement entry), inlines calls, guards on branch
  direction and receiver class, folds global constants and inlined method
  targets under registered global dependencies, and scalar-replaces
  ("sinks") allocations and their monitors;
* a deoptimizer that rebuilds one or more interpreter frames from an
  optimized frame, materializes virtual objects (two-phase, identity
  preserving, cycle safe, re-locking), and handles eager guard failure,
  lazy invalidation of on-stack activations ("patched return address"),
  self-invalidation after an effect, and non-invalidating side exits.

The checked property is observational equivalence with the reference
interpreter: same termination status, same error kind, same output trace,
same return value and same reachable heap up to isomorphism (class, fields,
monitor depth, aliasing and cycles).  The property is checked

1. for every hand-written scenario under several tiering thresholds,
2. for every single deoptimization point of each such run forced to fail even
   though its predicate holds (assumption transparency), plus sampled pairs,
3. for seeded random programs with the same single-fault sweep, and
4. negatively: each of several deliberately broken deoptimizer/compiler
   variants ("mutants") must be detected by at least one run.

Exit status 0 means every equivalence check passed and every mutant was
detected.  Options: --verbose prints a narrated lazy-deoptimization example;
--random N changes the number of seeded random programs (default 140).
"""

from __future__ import annotations

import random
import sys
import time

FUEL = 400_000          # safety net; guest programs are terminating by construction
MAX_SYM_STEPS = 600     # symbolic-execution budget per compilation
MAX_INLINE_DEPTH = 4
MAX_INLINE_SIZE = 40
MAX_COMPILES_PER_KEY = 6

BINOPS = ("add", "sub", "mul", "lt", "eq")


class GuestError(Exception):
    """A guest-visible run-time error (part of the observable outcome)."""


class HarnessFailure(Exception):
    """The probe itself misbehaved (never a legitimate guest outcome)."""


def isint(v):
    return v.__class__ is int


class Obj:
    __slots__ = ("cls", "fields", "lock")

    def __init__(self, cls, lock=0):
        self.cls = cls
        self.fields = {}
        self.lock = lock


class Func:
    def __init__(self, name, nparams, code, nregs):
        self.name = name
        self.nparams = nparams
        self.code = code
        self.nregs = max(nregs, nparams, 1)
        self.has_backedge = any(
            (ins[0] == "jmp" and ins[1] <= pc) or (ins[0] == "br" and min(ins[2], ins[3]) <= pc)
            for pc, ins in enumerate(code)
        )


class Program:
    def __init__(self, funcs, classes, globs):
        self.funcs = funcs
        self.classes = classes
        self.globals = globs
        self._live = {}

    def liveness(self, unsound=False):
        key = bool(unsound)
        if key not in self._live:
            self._live[key] = {n: compute_liveness(f, unsound) for n, f in self.funcs.items()}
        return self._live[key]


# --------------------------------------------------------------------------- assembler

def assemble(text):
    funcs, classes, globs, pending, cur = {}, {}, {}, [], None
    for raw in text.splitlines():
        line = raw.split("#")[0].strip()
        if not line:
            continue
        tok = line.split()
        if tok[0] == "class":
            classes[tok[1]] = dict(t.split("=") for t in tok[2:])
        elif tok[0] == "global":
            globs[tok[1]] = int(tok[2])
        elif tok[0] == "func":
            cur = (tok[1], int(tok[2]), [])
            pending.append(cur)
        else:
            cur[2].append(tok)
    for name, nparams, lines in pending:
        labels, ins = {}, []
        for tok in lines:
            if tok[0].endswith(":"):
                labels[tok[0][:-1]] = len(ins)
            else:
                ins.append(tok)
        regs = [0]

        def reg(t):
            if t[0] != "r":
                raise HarnessFailure(f"bad register {t!r} in {name}")
            n = int(t[1:])
            regs[0] = max(regs[0], n + 1)
            return n

        code = []
        for t in ins:
            op = t[0]
            if op == "const":
                code.append(("const", reg(t[1]), None if t[2] == "none" else int(t[2])))
            elif op == "mov":
                code.append(("mov", reg(t[1]), reg(t[2])))
            elif op in BINOPS:
                code.append((op, reg(t[1]), reg(t[2]), reg(t[3])))
            elif op == "new":
                code.append(("new", reg(t[1]), t[2]))
            elif op == "getf":
                code.append(("getf", reg(t[1]), reg(t[2]), t[3]))
            elif op == "setf":
                code.append(("setf", reg(t[1]), t[2], reg(t[3])))
            elif op == "gload":
                code.append(("gload", reg(t[1]), t[2]))
            elif op == "gstore":
                code.append(("gstore", t[1], reg(t[2])))
            elif op in ("print", "lock", "unlock", "ret"):
                code.append((op, reg(t[1])))
            elif op == "lockcount":
                code.append(("lockcount", reg(t[1]), reg(t[2])))
            elif op == "jmp":
                code.append(("jmp", labels[t[1]]))
            elif op == "br":
                code.append(("br", reg(t[1]), labels[t[2]], labels[t[3]]))
            elif op == "call":
                code.append(("call", reg(t[1]), t[2], tuple(reg(x) for x in t[3:])))
            elif op == "send":
                code.append(("send", reg(t[1]), reg(t[2]), t[3], tuple(reg(x) for x in t[4:])))
            elif op == "setmethod":
                code.append(("setmethod", t[1], t[2], t[3]))
            else:
                raise HarnessFailure(f"unknown opcode {op!r}")
        funcs[name] = Func(name, nparams, code, regs[0])
    return Program(funcs, classes, globs)


def use_def(ins, unsound=False):
    op = ins[0]
    if op == "const" or op == "new" or op == "gload":
        return (), (ins[1],)
    if op == "mov":
        return (ins[2],), (ins[1],)
    if op in BINOPS:
        return (ins[2], ins[3]), (ins[1],)
    if op == "getf" or op == "lockcount":
        return (ins[2],), (ins[1],)
    if op == "setf":
        return (ins[1], ins[3]), ()
    if op == "gstore":
        return (ins[2],), ()
    if op == "print":
        return ((), ()) if unsound else ((ins[1],), ())   # mutant: print is not a use
    if op in ("lock", "unlock", "ret", "br"):
        return (ins[1],), ()
    if op == "call":
        return tuple(ins[3]), (ins[1],)
    if op == "send":
        return (ins[2],) + tuple(ins[4]), (ins[1],)
    return (), ()


def compute_liveness(func, unsound=False):
    """live[pc] = registers whose value may be read at or after pc before being written."""
    n = len(func.code)
    live = [frozenset() for _ in range(n + 1)]
    changed = True
    while changed:
        changed = False
        for pc in range(n - 1, -1, -1):
            ins = func.code[pc]
            op = ins[0]
            if op == "jmp":
                succ = (ins[1],)
            elif op == "br":
                succ = (ins[2], ins[3])
            elif op == "ret":
                succ = ()
            else:
                succ = (pc + 1,)
            out = frozenset().union(*(live[s] for s in succ)) if succ else frozenset()
            uses, defs = use_def(ins, unsound)
            new = (out - frozenset(defs)) | frozenset(uses)
            if new != live[pc]:
                live[pc] = new
                changed = True
    return live


# --------------------------------------------------------------------------- frames and code

class IFrame:
    """Interpreter activation: the source-level state the deoptimizer must rebuild."""
    __slots__ = ("func", "pc", "regs", "wait_dst")

    def __init__(self, func, regs):
        self.func = func
        self.pc = 0
        self.regs = regs
        self.wait_dst = None


class OFrame:
    """Optimized activation: flat machine slots; may stand for several inlined IFrames."""
    __slots__ = ("code", "ip", "slots", "lazy")

    def __init__(self, code, slots):
        self.code = code
        self.ip = 0
        self.slots = slots
        self.lazy = False       # True == "return address patched to the deopt trampoline"


class Snap:
    """Deoptimization metadata for one deopt point (FrameState chain + virtual objects).

    frames: outermost-first tuples (func name, pc, wait_dst, ((reg, operand), ...)).
    virtuals: vid -> (class, monitor depth, ((field, operand), ...)).
    kind: 'before' (re-execute the top frame's instruction) or 'after_call'
          (the top frame's call completed; its result goes to wait_dst).
    """
    __slots__ = ("kind", "frames", "virtuals")

    def __init__(self, kind, frames, virtuals):
        self.kind = kind
        self.frames = frames
        self.virtuals = virtuals


class Code:
    __slots__ = ("key", "ops", "snaps", "nslots", "deps", "valid")

    def __init__(self, key):
        self.key = key
        self.ops = []
        self.snaps = []
        self.nslots = 0
        self.deps = set()
        self.valid = True       # False == not entrant; live activations may still run it


class SymFrame:
    __slots__ = ("func", "pc", "regs", "wait_dst")

    def __init__(self, func, pc, regs):
        self.func = func
        self.pc = pc
        self.regs = regs
        self.wait_dst = None


class Virt:
    __slots__ = ("cls", "fields", "lock", "slot")

    def __init__(self, cls):
        self.cls = cls
        self.fields = {}
        self.lock = 0
        self.slot = None        # set once the allocation has been forced (escaped)


# --------------------------------------------------------------------------- compiler

class Compiler:
    """Profile-directed symbolic executor producing linear guarded code plus snapshots.

    Operands are ('k', constant), ('s', machine slot) or ('v', virtual object id).
    """

    def __init__(self, eng, func, entry_pc, kind):
        self.eng = eng
        self.prog = eng.prog
        self.kind = kind
        self.entry_pc = entry_pc
        self.code = Code((func.name, entry_pc, kind))
        self.live = self.prog.liveness(eng.mutant == "unsound_liveness")
        self.nslots = func.nregs
        if kind == "osr":
            regs = [("s", i) for i in range(func.nregs)]     # every register is live-in, unknown
            if eng.mutant == "osr_assumes_preloop_constants":
                for ins in func.code[:entry_pc]:             # facts that only hold on first entry
                    if ins[0] == "const":
                        regs[ins[1]] = ("k", ins[2])
        else:
            regs = [("s", i) for i in range(func.nparams)] + [("k", None)] * (func.nregs - func.nparams)
        self.frames = [SymFrame(func, entry_pc, regs)]
        self.virt = {}
        self.known_cls = {}
        self.written_globals = set()
        self.written_methods = set()
        self.done = False

    # ---- helpers
    def new_slot(self):
        self.nslots += 1
        return self.nslots - 1

    def emit(self, *op):
        self.code.ops.append(op)

    def R(self, o):
        if o[0] == "v":
            s = self.virt[o[1]].slot
            if s is not None:
                return ("s", s)
        return o

    def snap(self, kind):
        frames, n = [], len(self.frames)
        for i, sf in enumerate(self.frames):
            live = self.live[sf.func.name]
            if i == n - 1 and kind == "before":
                need, wait = live[sf.pc], None
            else:                                   # frame is suspended in a call at sf.pc
                need, wait = live[sf.pc + 1] - {sf.wait_dst}, sf.wait_dst
            regmap = tuple((r, self.R(sf.regs[r])) for r in sorted(need))
            frames.append((sf.func.name, sf.pc, wait, regmap))
        virtuals = {}
        work = [o[1] for f in frames for _, o in f[3] if o[0] == "v"]
        while work:
            vid = work.pop()
            if vid in virtuals:
                continue
            v = self.virt[vid]
            flds = tuple((f, self.R(v.fields[f])) for f in sorted(v.fields))
            virtuals[vid] = (v.cls, v.lock, flds)
            work.extend(o[1] for _, o in flds if o[0] == "v")
        self.code.snaps.append(Snap(kind, tuple(frames), virtuals))
        return len(self.code.snaps) - 1

    def leave(self, opname):
        """End the trace by transferring to the interpreter before the current instruction."""
        self.emit(opname, self.snap("before"))
        self.done = True

    def force(self, o):
        """Materialize a virtual object (and everything it references) at this point."""
        if o[0] != "v":
            return o
        root = self.virt[o[1]]
        if root.slot is not None:
            return ("s", root.slot)
        group, work = [], [o[1]]
        while work:
            vid = work.pop()
            v = self.virt[vid]
            if v.slot is not None:
                continue
            v.slot = self.new_slot()
            self.known_cls[v.slot] = v.cls
            group.append(v)
            work.extend(x[1] for x in v.fields.values() if x[0] == "v")
        for v in group:                              # phase 1: allocate (cycles allowed)
            self.emit("alloc", v.slot, v.cls, v.lock)
        for v in group:                              # phase 2: initialize fields
            for f in sorted(v.fields):
                self.emit("setf_init", ("s", v.slot), f, self.R(v.fields[f]))
        return ("s", root.slot)

    def goto(self, target):
        sf = self.frames[-1]
        backward = target <= sf.pc
        sf.pc = target
        if backward and len(self.frames) == 1:
            if self.kind == "osr" and target == self.entry_pc:
                moves = []
                for r in sorted(self.live[sf.func.name][target]):
                    o = self.force(self.R(sf.regs[r]))
                    if o != ("s", r):
                        moves.append((r, o))
                self.emit("loop_back", tuple(moves))
                self.done = True
            else:
                self.leave("exit")

    def can_inline(self, callee):
        return (len(self.frames) < MAX_INLINE_DEPTH and not callee.has_backedge
                and len(callee.code) <= MAX_INLINE_SIZE
                and all(sf.func is not callee for sf in self.frames))

    def inline(self, callee, args, dst):
        self.frames[-1].wait_dst = dst
        regs = list(args) + [("k", None)] * (callee.nregs - len(args))
        self.frames.append(SymFrame(callee, 0, regs))

    def residual_call(self, dst, opname, head, args):
        sf = self.frames[-1]
        args = tuple(self.force(a) for a in args)
        sf.wait_dst = dst
        s = self.new_slot()
        self.emit(opname, s, head, args, self.snap("after_call"))   # state while suspended in the call
        sf.regs[dst] = ("s", s)
        sf.pc += 1

    # ---- main loop
    def compile(self):
        steps = 0
        while not self.done:
            steps += 1
            if steps > MAX_SYM_STEPS:
                self.leave("exit")
                break
            self.step()
        self.code.nslots = self.nslots
        first = self.code.ops[0][0]
        if first in ("exit", "deopt"):
            return None                                # no progress: do not install
        if self.eng.mutant == "no_dep_registration":
            self.code.deps = set()
        return self.code

    def step(self):
        eng = self.eng
        sf = self.frames[-1]
        f = sf.func
        if sf.pc >= len(f.code):
            return self.leave("deopt")
        ins = f.code[sf.pc]
        op = ins[0]
        regs = sf.regs
        R = self.R
        if op == "const":
            regs[ins[1]] = ("k", ins[2])
        elif op == "mov":
            regs[ins[1]] = R(regs[ins[2]])
        elif op in BINOPS:
            a, b = R(regs[ins[2]]), R(regs[ins[3]])
            if op == "eq":
                if a[0] == "k" and b[0] == "k":
                    regs[ins[1]] = ("k", guest_eq(a[1], b[1]))
                elif a[0] == "v" or b[0] == "v":
                    # an unescaped allocation is equal only to itself
                    regs[ins[1]] = ("k", 1 if a == b else 0)
                else:
                    s = self.new_slot()
                    self.emit("eq", s, a, b)
                    regs[ins[1]] = ("s", s)
            else:
                bad = lambda x: x[0] == "v" or (x[0] == "k" and not isint(x[1]))
                if bad(a) or bad(b):
                    return self.leave("deopt")           # interpreter will raise the type error
                if a[0] == "k" and b[0] == "k":
                    regs[ins[1]] = ("k", ARITH[op](a[1], b[1]))
                else:
                    s = self.new_slot()
                    self.emit("arith", op, s, a, b)
                    regs[ins[1]] = ("s", s)
        elif op == "new":
            if ins[2] not in eng.methods:
                return self.leave("deopt")
            vid = len(self.virt)
            self.virt[vid] = Virt(ins[2])
            regs[ins[1]] = ("v", vid)
        elif op == "getf":
            o = R(regs[ins[2]])
            if o[0] == "v":
                v = self.virt[o[1]]
                if ins[3] not in v.fields:
                    return self.leave("deopt")
                regs[ins[1]] = R(v.fields[ins[3]])
            elif o[0] == "k":
                return self.leave("deopt")
            else:
                s = self.new_slot()
                self.emit("getf", s, o, ins[3])
                regs[ins[1]] = ("s", s)
        elif op == "setf":
            o, val = R(regs[ins[1]]), R(regs[ins[3]])
            if o[0] == "v":
                self.virt[o[1]].fields[ins[2]] = val     # may build virtual cycles
            elif o[0] == "k":
                return self.leave("deopt")
            else:
                self.emit("setf", o, ins[2], self.force(val))
        elif op == "gload":
            g = ins[2]
            dep = ("global", g)
            if (dep not in eng.unstable and g not in self.written_globals and g in eng.globals
                    and (eng.globals[g] is None or isint(eng.globals[g]))):
                regs[ins[1]] = ("k", eng.globals[g])     # fold under a global dependency
                self.code.deps.add(dep)
            else:
                s = self.new_slot()
                self.emit("gload", s, g)
                regs[ins[1]] = ("s", s)
        elif op == "gstore":
            val = self.force(R(regs[ins[2]]))
            self.written_globals.add(ins[1])
            sf.pc += 1
            self.emit("gstore", ins[1], val, self.snap("before"))   # state after the effect
            return
        elif op == "print":
            a = R(regs[ins[1]])
            if a[0] == "v":
                v = self.virt[a[1]]
                self.emit("printk", ("obj", v.cls, v.lock))          # non-escaping use
            elif a[0] == "k":
                self.emit("printk", a[1])
            else:
                self.emit("print", a)
        elif op == "lock" or op == "unlock":
            o = R(regs[ins[1]])
            if o[0] == "v":
                v = self.virt[o[1]]
                if op == "lock":
                    v.lock += 1                                       # elided monitor enter
                elif v.lock == 0:
                    return self.leave("deopt")
                else:
                    v.lock -= 1
            elif o[0] == "k":
                return self.leave("deopt")
            else:
                self.emit(op, o)
        elif op == "lockcount":
            o = R(regs[ins[2]])
            if o[0] == "v":
                regs[ins[1]] = ("k", self.virt[o[1]].lock)
            elif o[0] == "k":
                return self.leave("deopt")
            else:
                s = self.new_slot()
                self.emit("lockcount", s, o)
                regs[ins[1]] = ("s", s)
        elif op == "jmp":
            return self.goto(ins[1])
        elif op == "br":
            c = R(regs[ins[1]])
            if c[0] == "k":
                if not isint(c[1]):
                    return self.leave("deopt")
                return self.goto(ins[2] if c[1] != 0 else ins[3])
            if c[0] == "v":
                return self.leave("deopt")
            seen = eng.profile_br.get((f.name, sf.pc))
            if seen is None or len(seen) != 1:
                return self.leave("exit")                 # unpredictable: side exit
            taken = next(iter(seen))
            self.emit("guard", "true" if taken else "false", c, None, self.snap("before"))
            return self.goto(ins[2] if taken else ins[3])
        elif op == "call":
            callee = self.prog.funcs.get(ins[2])
            args = [R(regs[a]) for a in ins[3]]
            if callee is None or callee.nparams != len(args):
                return self.leave("deopt")
            if self.can_inline(callee):
                return self.inline(callee, args, ins[1])
            return self.residual_call(ins[1], "call", ins[2], args)
        elif op == "send":
            r = R(regs[ins[2]])
            sel = ins[3]
            args = [R(regs[a]) for a in ins[4]]
            if r[0] == "k":
                return self.leave("deopt")
            cls = None
            if r[0] == "v":
                cls = self.virt[r[1]].cls
            elif r[1] in self.known_cls:
                cls = self.known_cls[r[1]]
            else:
                seen = eng.profile_cls.get((f.name, sf.pc))
                if seen is not None and len(seen) == 1:
                    cls = next(iter(seen))
                    self.emit("guard", "class", r, cls, self.snap("before"))
                    self.known_cls[r[1]] = cls
            dep = ("method", cls, sel)
            if cls is not None and dep not in eng.unstable and (cls, sel) not in self.written_methods:
                fn = eng.methods[cls].get(sel)
                callee = self.prog.funcs.get(fn) if fn is not None else None
                if callee is None or callee.nparams != len(args) + 1:
                    return self.leave("deopt")
                self.code.deps.add(dep)                    # devirtualized under a dependency
                if self.can_inline(callee):
                    return self.inline(callee, [r] + args, ins[1])
                return self.residual_call(ins[1], "call", fn, [r] + args)
            r = self.force(r)
            return self.residual_call(ins[1], "send", (r, sel), args)
        elif op == "ret":
            v = R(regs[ins[1]])
            if len(self.frames) > 1:
                self.frames.pop()
                caller = self.frames[-1]
                caller.regs[caller.wait_dst] = v           # virtuals flow through inlined returns
                caller.pc += 1
            else:
                self.emit("ret", self.force(v))
                self.done = True
            return
        elif op == "setmethod":
            self.written_methods.add((ins[1], ins[2]))
            sf.pc += 1
            self.emit("setmethod", ins[1], ins[2], ins[3], self.snap("before"))
            return
        else:
            raise HarnessFailure(op)
        sf.pc += 1


ARITH = {
    "add": lambda a, b: a + b,
    "sub": lambda a, b: a - b,
    "mul": lambda a, b: a * b,
    "lt": lambda a, b: 1 if a < b else 0,
}


def guest_eq(a, b):
    if isint(a) and isint(b):
        return 1 if a == b else 0
    return 1 if a is b else 0


# --------------------------------------------------------------------------- engine

STAT_KEYS = ("compiles", "osr_entries", "deopt_guard", "deopt_lazy", "deopt_self", "deopt_forced",
             "exits", "known_error_deopts", "frames_rebuilt", "max_frames", "virtuals_materialized",
             "relocked", "allocs", "invalidations", "activations_patched")


class Engine:
    def __init__(self, prog, jit=False, t_call=2, t_loop=2, force=(), mutant=None, log=None):
        self.prog = prog
        self.jit = jit
        self.t_call = t_call
        self.t_loop = t_loop
        self.force = frozenset(force)
        self.mutant = mutant
        self.log = log
        self.globals = dict(prog.globals)
        self.methods = {c: dict(m) for c, m in prog.classes.items()}
        self.out = []
        self.stack = []
        self.result = None
        self.profile_br = {}
        self.profile_cls = {}
        self.call_count = {}
        self.backedge_count = {}
        self.codes = {}
        self.ncompiles = {}
        self.dep_index = {}
        self.unstable = set()
        self.points = 0
        self.steps = 0
        self.error_in_optimized = False
        self.stats = dict.fromkeys(STAT_KEYS, 0)

    # ---- outcome
    def run(self):
        status = ("ok", None)
        try:
            self.push_call("main", [])
            stack = self.stack
            while stack:
                self.steps += 1
                if self.steps > FUEL:
                    raise HarnessFailure("fuel exhausted")
                top = stack[-1]
                if top.__class__ is IFrame:
                    self.istep(top)
                else:
                    self.ostep(top)
        except GuestError as exc:
            status = ("error", exc.args[0])
            self.result = None
            self.error_in_optimized = self.stack[-1].__class__ is OFrame
        names = sorted(self.globals)
        ids = {}

        def canon(v):
            if v.__class__ is Obj:
                if id(v) in ids:
                    return ("ref", ids[id(v)])
                n = ids[id(v)] = len(ids)
                return ("obj", n, v.cls, v.lock, tuple((f, canon(v.fields[f])) for f in sorted(v.fields)))
            return v

        heap = tuple(canon(v) for v in [self.result] + [self.globals[g] for g in names])
        tables = tuple((c, tuple(sorted(m.items()))) for c, m in sorted(self.methods.items()))
        return (status, tuple(self.out), tuple(names), heap, tables)

    def show(self, v):
        return ("obj", v.cls, v.lock) if v.__class__ is Obj else v

    def alloc(self, cls, lock=0):
        self.stats["allocs"] += 1
        return Obj(cls, lock)

    # ---- tiering
    def code_for(self, fname, pc, kind):
        key = (fname, pc, kind)
        code = self.codes.get(key)
        if code is not None and code.valid:
            return code
        if not self.jit:
            return None
        hot = (self.call_count.get(fname, 0) >= self.t_call if kind == "entry"
               else self.backedge_count.get((fname, pc), 0) >= self.t_loop)
        if not hot or self.ncompiles.get(key, 0) >= MAX_COMPILES_PER_KEY:
            return None
        self.ncompiles[key] = self.ncompiles.get(key, 0) + 1
        self.stats["compiles"] += 1
        code = Compiler(self, self.prog.funcs[fname], pc, kind).compile()
        if code is None:
            return None
        self.codes[key] = code
        for dep in code.deps:
            self.dep_index.setdefault(dep, []).append(code)
        return code

    def push_call(self, fname, args):
        func = self.prog.funcs.get(fname)
        if func is None:
            raise GuestError("nofunc")
        if func.nparams != len(args):
            raise GuestError("arity")
        self.call_count[fname] = self.call_count.get(fname, 0) + 1
        code = self.code_for(fname, 0, "entry")
        if code is not None:
            self.stack.append(OFrame(code, args + [None] * (code.nslots - len(args))))
        else:
            self.stack.append(IFrame(func, args + [None] * (func.nregs - len(args))))

    def lookup(self, recv, sel, nargs):
        if recv.__class__ is not Obj:
            raise GuestError("notobj")
        fn = self.methods[recv.cls].get(sel)
        if fn is None:
            raise GuestError("nomethod")
        return fn

    # ---- global assumptions
    def invalidate(self, dep):
        """A global assumption changed: make dependents not entrant and patch live activations."""
        codes = self.dep_index.pop(dep, None)
        if not codes:
            return
        self.unstable.add(dep)                    # speculation log: do not rely on it again
        self.stats["invalidations"] += 1
        hit = []
        for code in codes:
            if self.mutant == "skip_patch_if_not_entrant" and not code.valid:
                continue
            code.valid = False
            hit.append(code)
        if self.mutant == "no_stack_patch":
            return
        top = self.stack[-1]
        for fr in self.stack:
            # The running frame is handled by its own post-effect check; every other
            # activation is suspended in a call and gets its return "patched".
            if fr.__class__ is OFrame and fr is not top and fr.code in hit and not fr.lazy:
                fr.lazy = True
                self.stats["activations_patched"] += 1

    def forced_point(self):
        n = self.points
        self.points = n + 1
        return n in self.force

    def after_effect(self, of, snap_id):
        if not of.code.valid:
            if self.mutant != "no_self_check":
                self.deopt(of, snap_id, "self")
        elif self.forced_point():
            self.deopt(of, snap_id, "forced")

    # ---- return protocol
    def do_return(self, v):
        self.stack.pop()
        if not self.stack:
            self.result = v
            return
        caller = self.stack[-1]
        if caller.__class__ is IFrame:
            caller.regs[caller.wait_dst] = v
            caller.pc += 1
            return
        op = caller.code.ops[caller.ip]
        if caller.lazy:
            self.deopt(caller, op[4], "lazy", v)
        elif self.forced_point():
            self.deopt(caller, op[4], "forced", v)
        else:
            caller.slots[op[1]] = v
            caller.ip += 1

    # ---- deoptimizer
    def deopt(self, of, snap_id, reason, retval=None):
        snap = of.code.snaps[snap_id]
        slots = of.slots
        stats = self.stats
        mutant = self.mutant
        memo = {}

        def materialize(vid):
            order, work = [], [vid]
            while work:                                   # phase 1: allocate the reachable group
                x = work.pop()
                if x in memo:
                    continue
                cls, lock, flds = snap.virtuals[x]
                if mutant == "no_relock":
                    lock = 0
                memo[x] = self.alloc(cls, lock)
                stats["virtuals_materialized"] += 1
                if lock:
                    stats["relocked"] += 1
                order.append(x)
                work.extend(o[1] for _, o in flds if o[0] == "v")
            for i, x in enumerate(order):                 # phase 2: initialize fields
                if mutant == "shallow_materialize" and i > 0:
                    continue
                obj = memo[x]
                for fname, o in snap.virtuals[x][2]:
                    obj.fields[fname] = o[1] if o[0] == "k" else slots[o[1]] if o[0] == "s" else memo[o[1]]
            return memo[vid]

        def value(o):
            if o[0] == "k":
                return o[1]
            if o[0] == "s":
                return slots[o[1]]
            if mutant == "dup_materialize":
                memo.clear()                              # one object per reference: identity lost
            return memo[o[1]] if o[1] in memo else materialize(o[1])

        frames = []
        for fname, pc, wait, regmap in snap.frames:
            func = self.prog.funcs[fname]
            fr = IFrame(func, [None] * func.nregs)
            fr.pc = pc
            fr.wait_dst = wait
            for r, o in regmap:
                fr.regs[r] = value(o)
            frames.append(fr)
        top = frames[-1]
        if snap.kind == "after_call":
            if mutant == "reexecute_call":
                pass                                      # resume before the call: effects repeat
            elif mutant == "drop_retval":
                top.pc += 1
            else:
                top.regs[top.wait_dst] = retval
                top.pc += 1
        elif mutant == "skip_instruction" and reason in ("guard", "forced"):
            top.pc += 1
        if self.stack[-1] is not of:
            raise HarnessFailure("deoptimizing a frame that is not on top")
        self.stack.pop()
        self.stack.extend(frames)
        key = {"guard": "deopt_guard", "lazy": "deopt_lazy", "self": "deopt_self",
               "forced": "deopt_forced", "exit": "exits", "deopt": "known_error_deopts"}[reason]
        stats[key] += 1
        stats["frames_rebuilt"] += len(frames)
        stats["max_frames"] = max(stats["max_frames"], len(frames))
        if self.log is not None:
            render = lambda v: f"{v.cls}{{lock={v.lock}, {v.fields}}}" if v.__class__ is Obj else repr(v)
            self.log.append((reason, of.code.key, snap,
                             [(f.func.name, f.pc, [render(v) for v in f.regs]) for f in frames]))

    # ---- interpreter (reference semantics; also records profiles)
    def istep(self, fr):
        f = fr.func
        if fr.pc >= len(f.code):
            raise GuestError("pc")
        ins = f.code[fr.pc]
        op = ins[0]
        R = fr.regs
        if op == "const":
            R[ins[1]] = ins[2]
        elif op == "mov":
            R[ins[1]] = R[ins[2]]
        elif op == "eq":
            R[ins[1]] = guest_eq(R[ins[2]], R[ins[3]])
        elif op in ARITH:
            a, b = R[ins[2]], R[ins[3]]
            if not (isint(a) and isint(b)):
                raise GuestError("type")
            R[ins[1]] = ARITH[op](a, b)
        elif op == "new":
            if ins[2] not in self.methods:
                raise GuestError("noclass")
            R[ins[1]] = self.alloc(ins[2])
        elif op == "getf":
            o = R[ins[2]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            if ins[3] not in o.fields:
                raise GuestError("nofield")
            R[ins[1]] = o.fields[ins[3]]
        elif op == "setf":
            o = R[ins[1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            o.fields[ins[2]] = R[ins[3]]
        elif op == "gload":
            if ins[2] not in self.globals:
                raise GuestError("noglobal")
            R[ins[1]] = self.globals[ins[2]]
        elif op == "gstore":
            self.globals[ins[1]] = R[ins[2]]
            self.invalidate(("global", ins[1]))
        elif op == "print":
            self.out.append(self.show(R[ins[1]]))
        elif op == "lock" or op == "unlock":
            o = R[ins[1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            if op == "lock":
                o.lock += 1
            elif o.lock == 0:
                raise GuestError("unlock")
            else:
                o.lock -= 1
        elif op == "lockcount":
            o = R[ins[2]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            R[ins[1]] = o.lock
        elif op == "jmp":
            return self.ijump(fr, ins[1])
        elif op == "br":
            c = R[ins[1]]
            if not isint(c):
                raise GuestError("type")
            taken = c != 0
            self.profile_br.setdefault((f.name, fr.pc), set()).add(taken)
            return self.ijump(fr, ins[2] if taken else ins[3])
        elif op == "call":
            fr.wait_dst = ins[1]
            return self.push_call(ins[2], [R[a] for a in ins[3]])
        elif op == "send":
            recv = R[ins[2]]
            fn = self.lookup(recv, ins[3], len(ins[4]))
            self.profile_cls.setdefault((f.name, fr.pc), set()).add(recv.cls)
            fr.wait_dst = ins[1]
            return self.push_call(fn, [recv] + [R[a] for a in ins[4]])
        elif op == "ret":
            return self.do_return(R[ins[1]])
        elif op == "setmethod":
            if ins[1] not in self.methods:
                raise GuestError("noclass")
            self.methods[ins[1]][ins[2]] = ins[3]
            self.invalidate(("method", ins[1], ins[2]))
        else:
            raise HarnessFailure(op)
        fr.pc += 1

    def ijump(self, fr, target):
        backward = target <= fr.pc
        fr.pc = target
        if backward and self.jit:
            key = (fr.func.name, target)
            self.backedge_count[key] = self.backedge_count.get(key, 0) + 1
            code = self.code_for(fr.func.name, target, "osr")
            if code is not None:                          # on-stack replacement at the loop header
                self.stack[-1] = OFrame(code, fr.regs + [None] * (code.nslots - len(fr.regs)))
                self.stats["osr_entries"] += 1

    # ---- optimized-code executor
    def ostep(self, of):
        op = of.code.ops[of.ip]
        k = op[0]
        S = of.slots
        if k == "guard":
            a = op[2]
            a = a[1] if a[0] == "k" else S[a[1]]
            kind = op[1]
            if kind == "class":
                ok = a.__class__ is Obj and a.cls == op[3]
            elif kind == "true":
                ok = isint(a) and a != 0
            else:
                ok = isint(a) and a == 0
            if not ok:
                of.code.valid = False                     # not entrant; other activations keep running
                return self.deopt(of, op[4], "guard")
            if self.forced_point():
                return self.deopt(of, op[4], "forced")
        elif k == "arith":
            a, b = op[3], op[4]
            a = a[1] if a[0] == "k" else S[a[1]]
            b = b[1] if b[0] == "k" else S[b[1]]
            if not (isint(a) and isint(b)):
                raise GuestError("type")
            S[op[2]] = ARITH[op[1]](a, b)
        elif k == "eq":
            a, b = op[2], op[3]
            S[op[1]] = guest_eq(a[1] if a[0] == "k" else S[a[1]], b[1] if b[0] == "k" else S[b[1]])
        elif k == "getf":
            o = S[op[2][1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            if op[3] not in o.fields:
                raise GuestError("nofield")
            S[op[1]] = o.fields[op[3]]
        elif k == "setf":
            o = S[op[1][1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            v = op[3]
            o.fields[op[2]] = v[1] if v[0] == "k" else S[v[1]]
        elif k == "alloc":
            S[op[1]] = self.alloc(op[2], op[3])
        elif k == "setf_init":
            v = op[3]
            S[op[1][1]].fields[op[2]] = v[1] if v[0] == "k" else S[v[1]]
        elif k == "gload":
            if op[2] not in self.globals:
                raise GuestError("noglobal")
            S[op[1]] = self.globals[op[2]]
        elif k == "gstore":
            v = op[2]
            self.globals[op[1]] = v[1] if v[0] == "k" else S[v[1]]
            self.invalidate(("global", op[1]))
            of.ip += 1
            return self.after_effect(of, op[3])
        elif k == "print":
            self.out.append(self.show(S[op[1][1]]))
        elif k == "printk":
            self.out.append(op[1])
        elif k == "lock" or k == "unlock":
            o = S[op[1][1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            if k == "lock":
                o.lock += 1
            elif o.lock == 0:
                raise GuestError("unlock")
            else:
                o.lock -= 1
        elif k == "lockcount":
            o = S[op[2][1]]
            if o.__class__ is not Obj:
                raise GuestError("notobj")
            S[op[1]] = o.lock
        elif k == "call":
            return self.push_call(op[2], [a[1] if a[0] == "k" else S[a[1]] for a in op[3]])
        elif k == "send":
            r, sel = op[2]
            recv = r[1] if r[0] == "k" else S[r[1]]
            fn = self.lookup(recv, sel, len(op[3]))
            return self.push_call(fn, [recv] + [a[1] if a[0] == "k" else S[a[1]] for a in op[3]])
        elif k == "setmethod":
            if op[1] not in self.methods:
                raise GuestError("noclass")
            self.methods[op[1]][op[2]] = op[3]
            self.invalidate(("method", op[1], op[2]))
            of.ip += 1
            return self.after_effect(of, op[4])
        elif k == "loop_back":
            if self.mutant == "sequential_loop_moves":
                for r, o in op[1]:
                    S[r] = o[1] if o[0] == "k" else S[o[1]]
            else:
                vals = [(r, o[1] if o[0] == "k" else S[o[1]]) for r, o in op[1]]
                for r, v in vals:                          # parallel move into the loop-header layout
                    S[r] = v
            of.ip = 0
            return
        elif k == "ret":
            v = op[1]
            return self.do_return(v[1] if v[0] == "k" else S[v[1]])
        elif k == "exit" or k == "deopt":
            return self.deopt(of, op[1], k)
        else:
            raise HarnessFailure(k)
        of.ip += 1


# --------------------------------------------------------------------------- guest scenarios

SCENARIOS = {}

SCENARIOS["sunk_allocation_partial_escape"] = """
class Point norm1=point_norm1
global leak 0
func point_norm1 1
  getf r1 r0 x
  getf r2 r0 y
  add r3 r1 r2
  ret r3
func main 0
  const r0 0
  const r1 12
  const r2 0
  const r3 1
  const r9 7
Ltop:
  lt r4 r0 r1
  br r4 Lbody Lend
Lbody:
  new r5 Point
  setf r5 x r0
  add r6 r0 r0
  setf r5 y r6
  send r7 r5 norm1
  add r2 r2 r7
  eq r8 r0 r9
  br r8 Lrare Lnext
Lrare:
  gstore leak r5          # the allocation escapes only on this rare path
  print r2
Lnext:
  add r0 r0 r3
  jmp Ltop
Lend:
  print r2
  ret r2
"""

SCENARIOS["midcall_method_mutation_lazy_deopt"] = """
class Counter step=counter_step
class Box get=box_get
func counter_step 2
  getf r2 r0 n
  add r2 r2 r1
  setf r0 n r2
  ret r2
func counter_step2 2
  getf r2 r0 n
  sub r2 r2 r1
  setf r0 n r2
  ret r2
func box_get 1
  getf r1 r0 v
  ret r1
func tick 1
  const r1 0
  const r2 1
Lt:
  lt r3 r1 r2
  br r3 Ltb Lte
Ltb:
  add r1 r1 r2
  jmp Lt
Lte:
  const r4 5
  eq r5 r0 r4
  br r5 Lmut Lret
Lmut:
  setmethod Counter step counter_step2   # mutation while work() is suspended in optimized code
  print r0
Lret:
  ret r0
func work 2
  const r2 0
  const r3 1
Lw:
  lt r4 r2 r1
  br r4 Lwb Lwe
Lwb:
  new r5 Box
  setf r5 v r2
  lock r5
  call r6 tick r2          # residual call; virtual, locked Box is live across it
  send r7 r0 step r3       # inlined under class guard + (Counter, step) dependency
  send r8 r5 get
  add r7 r7 r8
  print r7
  lockcount r9 r5
  print r9
  unlock r5
  add r2 r2 r3
  jmp Lw
Lwe:
  getf r6 r0 n
  ret r6
func main 0
  new r0 Counter
  const r1 0
  setf r0 n r1
  const r2 9
  call r3 work r0 r2
  print r3
  ret r3
"""

SCENARIOS["alias_identity_after_materialization"] = """
class Node
global keep 0
func main 0
  const r0 0
  const r1 8
  const r2 1
  const r9 5
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  new r4 Node
  setf r4 v r0
  mov r5 r4
  eq r6 r0 r9
  br r6 Lrare Lcommon
Lrare:
  eq r7 r4 r5
  print r7
  setf r4 v r1
  getf r8 r5 v
  print r8
  gstore keep r4
Lcommon:
  getf r8 r5 v
  print r8
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["cyclic_virtual_graph"] = """
class Node
global ring 0
func main 0
  const r0 0
  const r1 9
  const r2 1
  const r9 6
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  new r4 Node
  new r5 Node
  setf r4 next r5
  setf r5 next r4
  setf r4 val r0
  add r6 r0 r2
  setf r5 val r6
  eq r7 r0 r9
  br r7 Lrare Lnext
Lrare:
  getf r8 r4 next
  getf r8 r8 next
  eq r10 r8 r4
  print r10
  getf r11 r8 val
  print r11
  getf r8 r5 next
  getf r11 r8 val
  print r11
  gstore ring r5
Lnext:
  getf r11 r5 val
  print r11
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["nested_inline_multiframe_deopt"] = """
class Acc
global saved 0
func h 2
  const r2 6
  eq r3 r1 r2
  br r3 Lr Lc
Lr:
  print r1
  gstore saved r0
  getf r4 r0 sum
  ret r4
Lc:
  add r4 r1 r1
  ret r4
func g 2
  const r2 1
  add r3 r1 r2
  call r4 h r0 r1
  add r4 r4 r3
  ret r4
func f 1
  new r1 Acc
  setf r1 sum r0
  call r2 g r1 r0
  getf r3 r1 sum
  add r2 r2 r3
  ret r2
func main 0
  const r0 0
  const r1 10
  const r2 1
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  call r4 f r0
  print r4
  add r0 r0 r2
  jmp Lt
Le:
  gload r5 saved
  getf r6 r5 sum
  ret r6
"""

SCENARIOS["elided_monitors_relock"] = """
class Res
global held 0
func main 0
  const r0 0
  const r1 9
  const r2 1
  const r9 4
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  new r4 Res
  setf r4 id r0
  lock r4
  lock r4
  eq r5 r0 r9
  br r5 Lrare Lnext
Lrare:
  lockcount r6 r4
  print r6
  print r4
  gstore held r4
Lnext:
  unlock r4
  lockcount r6 r4
  print r6
  unlock r4
  add r0 r0 r2
  jmp Lt
Le:
  gload r7 held
  lockcount r8 r7
  ret r8
"""

SCENARIOS["global_constant_self_invalidation"] = """
global mode 0
global other 5
func main 0
  const r0 0
  const r1 9
  const r2 1
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  gload r4 mode            # folded to a constant under a (global, mode) dependency
  gload r6 other
  add r5 r4 r6
  print r5
  add r4 r4 r2
  gstore mode r4           # the optimized code invalidates its own assumption
  add r0 r0 r2
  jmp Lt
Le:
  gload r4 mode
  ret r4
"""

SCENARIOS["polymorphic_receiver_guard_failure"] = """
class A val=a_val
class B val=b_val
func a_val 2
  getf r2 r0 k
  add r2 r2 r1
  ret r2
func a_val2 2
  getf r2 r0 k
  sub r2 r2 r1
  ret r2
func b_val 2
  getf r2 r0 k
  mul r2 r2 r1
  ret r2
func main 0
  new r4 A
  new r5 B
  const r6 10
  setf r4 k r6
  const r6 3
  setf r5 k r6
  const r0 0
  const r1 14
  const r2 1
  const r8 6
  const r9 10
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  mov r7 r4
  lt r3 r0 r8
  br r3 Lsend Lother
Lother:
  mov r7 r5
  eq r3 r0 r9
  br r3 Lmut Lsend
Lmut:
  setmethod A val a_val2
Lsend:
  send r10 r7 val r0
  print r10
  send r10 r4 val r2
  print r10
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["error_preserved_in_optimized_code"] = """
class Cell
class Empty
global cur 0
func swap 1
  const r1 0
  const r2 1
Ls:
  lt r3 r1 r2
  br r3 Lsb Lse
Lsb:
  add r1 r1 r2
  jmp Ls
Lse:
  const r4 6
  eq r5 r0 r4
  br r5 Lbad Lok
Lbad:
  new r6 Empty
  gstore cur r6            # later getf in optimized code must raise the same error
Lok:
  ret r0
func main 0
  new r4 Cell
  const r5 2
  setf r4 x r5
  gstore cur r4
  const r0 0
  const r1 12
  const r2 1
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  call r6 swap r0
  gload r7 cur
  getf r8 r7 x
  add r8 r8 r0
  print r8
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["recursive_activations_all_patched"] = """
class Box get=box_get
func box_get 1
  getf r1 r0 v
  ret r1
func box_get2 1
  getf r1 r0 v
  add r1 r1 r1
  ret r1
func down 1
  new r1 Box
  setf r1 v r0
  const r2 0
  eq r3 r0 r2
  br r3 Lbase Lrec
Lbase:
  setmethod Box get box_get2   # every suspended down() activation depends on (Box, get)
  ret r2
Lrec:
  const r4 1
  sub r5 r0 r4
  call r6 down r5
  send r7 r1 get
  add r6 r6 r7
  print r6
  ret r6
func main 0
  const r0 7
  call r1 down r0
  print r1
  ret r1
"""

SCENARIOS["escape_through_residual_call_argument"] = """
class Pair
func fill 2
  const r2 0
  const r3 1
Lf:
  lt r4 r2 r1
  br r4 Lfb Lfe
Lfb:
  getf r5 r0 a
  add r5 r5 r2
  setf r0 a r5
  add r2 r2 r3
  jmp Lf
Lfe:
  ret r0
func main 0
  const r0 0
  const r1 8
  const r2 1
  const r9 3
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  new r4 Pair
  setf r4 a r0
  lt r5 r9 r0
  br r5 Lesc Lkeep
Lesc:
  call r6 fill r4 r9       # allocation is forced before the call on this path only
  eq r7 r6 r4
  print r7
Lkeep:
  getf r8 r4 a
  print r8
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["known_error_on_folded_path"] = """
class C
global phase 0
func main 0
  const r0 0
  const r1 6
  const r2 1
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  gload r4 phase
  br r4 Lerr Lok
Lerr:
  new r5 C
  unlock r5                # monitor underflow, statically visible once phase folds to 1
Lok:
  print r0
  eq r6 r0 r2
  br r6 Lset Lnext
Lset:
  gstore phase r2
Lnext:
  add r0 r0 r2
  jmp Lt
Le:
  ret r0
"""

SCENARIOS["loop_carried_swap_osr_entry"] = """
func main 0
  const r0 0
  const r1 9
  const r2 1
  const r4 1
  const r5 2
Lt:
  lt r3 r0 r1
  br r3 Lb Le
Lb:
  mov r6 r4
  mov r4 r5                # swap through a temporary: needs a parallel move at the back edge
  mov r5 r6
  add r4 r4 r0
  print r4
  add r0 r0 r2
  jmp Lt
Le:
  print r5
  ret r4
"""

RANDOM_LIBRARY = """
class A get=a_get bump=a_bump show=a_show leak=a_leak
class B get=b_get bump=b_bump show=b_show leak=b_leak
global g0 3
global g1 0
global tick 0
global esc 0
global fin 0
func a_get 2
  getf r2 r0 x
  add r3 r2 r1
  ret r3
func b_get 2
  getf r2 r0 x
  sub r3 r2 r1
  ret r3
func alt_get 2
  getf r2 r0 x
  add r3 r2 r1
  add r3 r3 r1
  ret r3
func a_bump 2
  getf r2 r0 x
  add r2 r2 r1
  setf r0 x r2
  ret r2
func b_bump 2
  getf r2 r0 x
  sub r2 r2 r1
  setf r0 x r2
  ret r2
func a_show 2
  getf r2 r0 x
  print r2
  ret r1
func b_show 2
  print r1
  getf r2 r0 x
  ret r2
func a_leak 2
  gstore esc r0
  ret r1
func b_leak 2
  getf r2 r0 link
  gstore esc r2
  ret r1
func helper 1
  gload r1 tick
  const r2 1
  add r1 r1 r2
  gstore tick r1
  const r3 0
Lh:
  lt r4 r3 r2
  br r4 Lhb Lhe
Lhb:
  add r3 r3 r2
  jmp Lh
Lhe:
  const r5 %(k1)d
  eq r6 r1 r5
  br r6 Lm1 Lm2
Lm1:
  setmethod A get alt_get
Lm2:
  const r5 %(k2)d
  eq r6 r1 r5
  br r6 Lg1 Lg2
Lg1:
  gstore g0 r1
Lg2:
  add r7 r0 r1
  ret r7
"""


def random_program(seed):
    """A terminating, type-correct random guest program (text for assemble())."""
    rng = random.Random(seed)
    lines = [RANDOM_LIBRARY % {"k1": rng.randint(1, 9), "k2": rng.randint(1, 9)}, "func main 0"]
    n = rng.randint(4, 8)
    INT, OBJ = (0, 1, 2, 3), (4, 5, 6)
    label = [0]

    def L():
        label[0] += 1
        return f"X{label[0]}"

    def emit(s):
        lines.append("  " + s)

    def new_obj(o):
        emit(f"new r{o} {rng.choice('AB')}")
        emit(f"setf r{o} x r{rng.choice(INT)}")
        emit(f"setf r{o} link r{rng.choice(OBJ) if rng.random() < 0.4 else o}")

    def simple(locked=None):
        c = rng.randrange(10)
        i, j, k = (rng.choice(INT) for _ in range(3))
        o = rng.choice(OBJ)
        if c == 0:
            emit(f"{rng.choice(('add', 'sub', 'lt', 'eq'))} r{i} r{j} r{k}")
        elif c == 1:
            emit(f"const r{i} {rng.randint(-3, 9)}")
        elif c == 2:
            emit(f"getf r{i} r{o} x")
        elif c == 3:
            emit(f"setf r{o} x r{i}")
        elif c == 4:
            emit(f"print r{rng.choice(INT + OBJ)}")
        elif c == 5:
            emit(f"send r{i} r{o} {rng.choice(('get', 'get', 'bump', 'show', 'leak'))} r{j}")
        elif c == 6:
            emit(f"call r{i} helper r{j}")
        elif c == 7:
            emit(f"gload r{i} {rng.choice(('g0', 'g1'))}")
        elif c == 8:
            emit(f"lockcount r{i} r{o}")
        else:
            emit(f"eq r{i} r{o} r{rng.choice(OBJ)}")

    def stmt(depth):
        c = rng.randrange(13)
        if c < 6:
            simple()
        elif c == 6:
            new_obj(rng.choice(OBJ))
        elif c == 7:
            emit(f"setf r{rng.choice(OBJ)} link r{rng.choice(OBJ)}")
        elif c == 8:
            emit(f"getf r{rng.choice(OBJ)} r{rng.choice(OBJ)} link")
        elif c == 9:
            emit(f"gstore {rng.choice(('g1', 'esc'))} r{rng.choice(INT) if rng.random() < 0.5 else rng.choice(OBJ)}"
                 if rng.random() < 0.5 else f"gstore g1 r{rng.choice(INT)}")
        elif c == 10:
            o = rng.choice(OBJ)
            emit(f"lock r{o}")
            for _ in range(rng.randint(1, 3)):
                simple()
            emit(f"unlock r{o}")
        elif depth < 2:
            a, b, j = L(), L(), L()
            kind = rng.randrange(3)
            if kind == 0:
                emit(f"const r7 {rng.randint(0, n)}")
                emit("lt r12 r10 r7")
            elif kind == 1:
                emit(f"const r7 {rng.randint(0, n)}")
                emit("eq r12 r10 r7")
            else:
                emit(f"lt r12 r{rng.choice(INT)} r{rng.choice(INT)}")
            emit(f"br r12 {a} {b}")
            lines.append(f"{a}:")
            for _ in range(rng.randint(1, 3)):
                stmt(depth + 1)
            emit(f"jmp {j}")
            lines.append(f"{b}:")
            for _ in range(rng.randint(0, 2)):
                stmt(depth + 1)
            lines.append(f"{j}:")
        else:
            simple()

    for i in INT:
        emit(f"const r{i} {rng.randint(-2, 6)}")
    for o in OBJ:
        emit(f"new r{o} {rng.choice('AB')}")
        emit(f"setf r{o} x r{rng.choice(INT)}")
        emit(f"setf r{o} link r{o}")
    emit("const r10 0")
    emit(f"const r11 {n}")
    emit("const r13 1")
    lines.append("Ltop:")
    emit("lt r12 r10 r11")
    emit("br r12 Lbody Lend")
    lines.append("Lbody:")
    for _ in range(rng.randint(5, 12)):
        stmt(0)
    emit("add r10 r10 r13")
    emit("jmp Ltop")
    lines.append("Lend:")
    for i in INT:
        emit(f"print r{i}")
    emit(f"gstore fin r{rng.choice(OBJ)}")
    emit("ret r0")
    return "\n".join(lines)


# --------------------------------------------------------------------------- checking harness

MUTANTS = (
    ("no_stack_patch", "invalidation does not patch suspended activations"),
    ("skip_patch_if_not_entrant", "activations of already not-entrant code are not patched"),
    ("no_self_check", "optimized code keeps running after invalidating its own assumption"),
    ("no_dep_registration", "folded globals / inlined targets are not registered as dependencies"),
    ("dup_materialize", "one object is materialized per reference (identity lost)"),
    ("shallow_materialize", "fields of nested virtual objects are not initialized"),
    ("no_relock", "materialized objects do not get their elided monitors re-acquired"),
    ("reexecute_call", "lazy deopt resumes before the completed call (effects repeat)"),
    ("drop_retval", "lazy deopt discards the callee's return value"),
    ("skip_instruction", "eager deopt resumes after the guarded instruction"),
    ("unsound_liveness", "frame states drop a register that the interpreter still reads"),
    ("osr_assumes_preloop_constants", "loop-entry code assumes pre-loop constant assignments still hold"),
    ("sequential_loop_moves", "loop-carried values are transferred sequentially, not in parallel"),
)

THRESHOLDS = ((1, 1), (2, 2), (3, 5))


def reference(prog):
    return Engine(prog).run()


def mixed(prog, thr, force=(), mutant=None, log=None):
    eng = Engine(prog, jit=True, t_call=thr[0], t_loop=thr[1], force=force, mutant=mutant, log=log)
    return eng.run(), eng


def sample(n, cap):
    if n <= cap:
        return list(range(n))
    return sorted({(i * n) // cap for i in range(cap)})


def sweep(name, prog, thresholds, cap, pairs, totals, mutant=None):
    """Return the first divergence (or None) between mixed-mode runs and the reference."""
    ref = reference(prog)
    rng = random.Random(len(name) * 7919 + cap)
    for thr in thresholds:
        out, eng = mixed(prog, thr, mutant=mutant)
        if totals is not None:
            totals["runs"] += 1
            totals["baseline_points"] += eng.points
            for k in STAT_KEYS:
                if k == "max_frames":
                    totals[k] = max(totals[k], eng.stats[k])
                else:
                    totals[k] += eng.stats[k]
        if out != ref:
            return (name, thr, (), ref, out)
        npoints = eng.points
        singles = sample(npoints, cap)
        plans = [(i,) for i in singles]
        for _ in range(pairs if npoints > 1 else 0):
            i = rng.randrange(npoints)
            plans.append((i, i + 1 + rng.randrange(max(1, npoints - i))))
        for plan in plans:
            out, eng2 = mixed(prog, thr, force=plan, mutant=mutant)
            if totals is not None:
                totals["runs"] += 1
                totals["forced_runs"] += 1
                for k in ("deopt_forced", "virtuals_materialized", "relocked", "frames_rebuilt"):
                    totals[k] += eng2.stats[k]
                totals["max_frames"] = max(totals["max_frames"], eng2.stats["max_frames"])
            if out != ref:
                return (name, thr, plan, ref, out)
    return None


def describe(div):
    name, thr, plan, ref, out = div
    lines = [f"DIVERGENCE in {name} thresholds={thr} forced_points={plan}"]
    for label, a, b in (("status", ref[0], out[0]), ("trace", ref[1], out[1]),
                        ("heap", ref[3], out[3]), ("methods", ref[4], out[4])):
        if a != b:
            lines.append(f"  {label}: reference={a!r}")
            lines.append(f"  {label}: mixed    ={b!r}")
    return "\n".join(lines)


def narrate():
    prog = assemble(SCENARIOS["midcall_method_mutation_lazy_deopt"])
    log = []
    out, eng = mixed(prog, (2, 2), log=log)
    print("narrated lazy deoptimization (scenario midcall_method_mutation_lazy_deopt):")
    for reason, key, snap, frames in log:
        if reason != "lazy":
            continue
        print(f"  code {key} invalidated while suspended in a call; snapshot kind={snap.kind}")
        for fname, pc, wait, regmap in snap.frames:
            print(f"    frame {fname}@pc{pc} result->r{wait} live registers: "
                  + ", ".join(f"r{r}={o[0]}{o[1]}" for r, o in regmap))
        for vid, (cls, lock, flds) in sorted(snap.virtuals.items()):
            print(f"    virtual v{vid}: class {cls}, monitor depth {lock}, fields "
                  + ", ".join(f"{f}={o[0]}{o[1]}" for f, o in flds))
        for fname, pc, regs in frames:
            print(f"    rebuilt interpreter frame {fname}@pc{pc}: [" + ", ".join(regs) + "]")
        break
    print(f"  equals reference: {out == reference(prog)}")


def main(argv):
    t0 = time.time()
    totals = dict.fromkeys(STAT_KEYS + ("runs", "forced_runs", "baseline_points"), 0)
    programs = [(name, assemble(text)) for name, text in SCENARIOS.items()]
    failures = []

    # 1+2: hand-written scenarios, every single deopt point forced, plus sampled pairs
    scenario_lines = []
    error_seen_in_optimized_code = False
    for name, prog in programs:
        div = sweep(name, prog, THRESHOLDS, cap=10_000, pairs=30, totals=totals)
        if div:
            failures.append(describe(div))
        agg = dict.fromkeys(STAT_KEYS + ("points",), 0)
        for thr in THRESHOLDS:
            _, eng = mixed(prog, thr)
            agg["points"] += eng.points
            error_seen_in_optimized_code |= eng.error_in_optimized
            for k in STAT_KEYS:
                agg[k] = max(agg[k], eng.stats[k]) if k == "max_frames" else agg[k] + eng.stats[k]
        scenario_lines.append(
            "    {0}: points={points} guard={deopt_guard} lazy={deopt_lazy} self={deopt_self} exit={exits} "
            "known_error={known_error_deopts} osr={osr_entries} max_frames={max_frames} "
            "materialized={virtuals_materialized} relocked={relocked}".format(name, **agg))
    scenario_runs = totals["runs"]
    if not error_seen_in_optimized_code:
        failures.append("no scenario raised a guest error while optimized code was on top of the stack")

    # allocation accounting on one scenario: sunk allocations never reach the heap
    prog = programs[0][1]
    ref_eng = Engine(prog)
    ref_eng.run()
    _, jit_eng = mixed(prog, (2, 2))
    alloc_line = (f"sunk_allocation_partial_escape: interpreter allocations={ref_eng.stats['allocs']}, "
                  f"mixed-mode allocations={jit_eng.stats['allocs']}")
    if not jit_eng.stats["allocs"] < ref_eng.stats["allocs"]:
        failures.append("allocation sinking removed no allocations: " + alloc_line)

    # 3: seeded random programs, sampled single-fault sweep
    nrandom = 140
    if "--random" in argv:
        nrandom = int(argv[argv.index("--random") + 1])
    rand_errors = 0
    for seed in range(nrandom):
        rprog = assemble(random_program(seed))
        if reference(rprog)[0][0] != "ok":
            rand_errors += 1
        div = sweep(f"random[{seed}]", rprog, ((1, 2),), cap=14, pairs=3, totals=totals)
        if div:
            failures.append(describe(div))

    # 4: negative controls
    mutant_report = []
    random_pool = [(f"random[{s}]", assemble(random_program(s))) for s in range(24)]
    for mutant, text in MUTANTS:
        killer = None
        for name, prog in programs + random_pool:
            try:
                div = sweep(name, prog, THRESHOLDS[:2], cap=40, pairs=0, totals=None, mutant=mutant)
            except HarnessFailure as exc:
                killer = f"{name} (non-termination trap: {exc})"
                break
            if div:
                killer = f"{div[0]} thresholds={div[1]} forced={div[2]}"
                break
        mutant_report.append((mutant, text, killer))
        if killer is None:
            failures.append(f"mutant {mutant!r} survived: the suite cannot detect '{text}'")

    print("speculative deoptimization equivalence probe")
    print(f"  scenarios: {len(programs)} hand-written x {len(THRESHOLDS)} tiering thresholds, {scenario_runs} runs")
    print(f"  random programs: {nrandom} seeds ({rand_errors} with guest errors), total mixed-mode runs: {totals['runs']}")
    print(f"  forced-deopt runs: {totals['forced_runs']}; deopt points in unforced runs: {totals['baseline_points']}")
    print("  unforced runs: compiles={compiles} osr_entries={osr_entries} guard_deopts={deopt_guard} "
          "lazy_deopts={deopt_lazy} self_invalidation_deopts={deopt_self} side_exits={exits} "
          "known_error_deopts={known_error_deopts}".format(**totals))
    print("  all runs: forced_deopts={deopt_forced} interpreter_frames_rebuilt={frames_rebuilt} "
          "max_frames_from_one_optimized_frame={max_frames} virtual_objects_materialized={virtuals_materialized} "
          "relocked_on_materialization={relocked}".format(**totals))
    print("  unforced runs: dependency_invalidations={invalidations} suspended_activations_patched={activations_patched}"
          .format(**totals))
    print("  " + alloc_line)
    print("  per-scenario unforced totals over the thresholds (deopt points, deopts by cause, OSR entries, ...):")
    for line in scenario_lines:
        print(line)
    print("  negative controls (each must be detected):")
    for mutant, text, killer in mutant_report:
        print(f"    {mutant}: {'DETECTED by ' + killer if killer else 'SURVIVED'}")
    if "--verbose" in argv:
        narrate()
    print(f"  elapsed: {time.time() - t0:.1f}s")
    if failures:
        print(f"FAIL: {len(failures)} problem(s)")
        for text in failures[:10]:
            print(text)
        return 1
    print("PASS: mixed-mode execution is observationally equivalent to the reference interpreter in every run, "
          "and every negative control was detected")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
