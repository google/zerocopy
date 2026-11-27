#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Dual-polar specification adequacy audit (`0`-TCB).

Verifies specification adequacy on mutated targets using two orthogonal poles
plus a safety-precondition non-vacuity gate:

1. Baseline and non-vacuity: the baseline crate/unit passes verification
   under the locked specification (a clean Receipt v3 `crate_verified` /
   `selected_unit_verified` receipt) and, when supplied, a kernel-checked
   witness module proves `SpecsPreInhabited` / `SpecsPreInhabitedV2`. That
   predicate only constrains `specs.safety` for `unsafe` bodies; for safe
   bodies it reduces to inhabitation of the entry-argument types.
2. Pole A (clean negative pipeline rejection): running `cargo-anneal verify`
   on `(P_mut, Spec, pi_shipped)` cleanly fails verification: a Receipt v3
   envelope (`schema_version == 3`, empty `taint_reasons`, OS elaboration
   sandbox) with `exit == 1`, `status == "proof_failed"`, `phase == "audit"`,
   no resource-limit `reason`, empty stderr, and zero crash markers.
3. Pole B (discriminative kernel refutation): staging exported `Expected` and
   `Captured` `.olean` artifacts alongside `Anneal.Diag.ConcreteRefute`, a
   concrete refutation proof kernel-certifies `¬ Expected.claim` against
   `P_mut` and the locked `Spec`, rejecting vacuous (`True`) specifications
   even when Pole A fails due to proof fragility.

The baseline and mutant requests must agree on everything except the Rust
program: scope, semantic compilation flags, specification and theorem
declarations and modules, and the SHA-256 of every specification and shipped
proof source.

User-supplied witness modules are untrusted. Each is linted (restricted
header imports, no metaprogramming, meta commands, or string literals) as
defense in depth, and every Lean process runs in a `bwrap` sandbox with no
network, an allowlisted environment, read-only toolchain, library, and source
mounts, and a fresh writable output directory, so elaboration-time code can
neither reach CI credentials nor modify the staged `.olean` files. The checked
theorem's type, declaring module, and axiom closure are computed by a
separate `lean --run` inspector that only imports compiled `.olean` files and
replays the theorem's entire dependency closure through the Lean kernel in a
fresh environment, so declarations added without kernel checking are
rejected. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Protocol, Sequence
import unicodedata

# `python3 -I` omits the script's directory from `sys.path`.
_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))
import anneal_ci_lib  # noqa: E402


SCHEMA_VERSION = 1
RECEIPT_SCHEMA_VERSION = 3
ALLOWED_FOUNDATION_AXIOMS = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)
# Untainted passing status per `scope.kind` (`Scope::verified_status` in
# `trusted/cargo-anneal/src/verify.rs`).
CLEAN_VERIFIED_STATUS = {
    "crate": "crate_verified",
    "selected_unit": "selected_unit_verified",
}
PASSING_STATUSES = frozenset(
    {
        "crate_verified",
        "selected_unit_verified",
        "tainted_crate_verified",
        "tainted_selected_unit_verified",
    }
)
CRASH_MASQUERADE_MARKERS = (
    "runtime.maxrecdepth",
    "maxrecdepth",
    "deterministic timeout",
    "maxheartbeats",
    "heartbeat_limit_exceeded",
    "recursion_depth_exceeded",
    "(kernel)",
    "stack overflow",
    "thread 'main' panicked",
    "panicked at",
)
LEAN_COMPILE_INFRA_MARKERS = (
    "runtime.maxrecdepth",
    "maxrecdepth",
    "deterministic timeout",
    "maxheartbeats",
    "heartbeat_limit_exceeded",
    "recursion_depth_exceeded",
    "stack overflow",
    "thread 'main' panicked",
    "panicked at",
    "bwrap:",
    "out of memory",
    "excessive memory",
)
# Non-semantic Lean exit-`1` diagnostics (missing imports, unresolved names or
# tactics, parse errors, visibility errors, and `-DwarningAsError=true` linter
# rejections). Marked `is_infrastructure=True` so broken witnesses never count
# as `pre_vacuous` or `vacuous_spec_false_kill` on negative suite cases.
LEAN_COMPILE_NONSEMANTIC_MARKERS = (
    "unknown module prefix",
    "bad import",
    "object file '",
    "cannot find .olean",
    "cannot import",
    "lean.unknownidentifier",
    "unknown identifier",
    "unknown constant",
    "unknown namespace",
    "lean.invalidfield",
    "invalid field",
    "unknown tactic",
    "ambiguous, possible interpretations",
    "unexpected token",
    "expected token",
    "expected term",
    "expected command",
    "unexpected end of input",
    "unknown command",
    "this linter can be disabled with",
    "set_option linter.",
    "[linter.",
    "declaration uses `sorry`",
    "uses 'sorry'",
    "private declaration",
    "has not been exposed",
)
LEAN_IDENT_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
CASE_NAME_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*")
INSPECTOR_LINE_PREFIX = "AUDIT_SPEC_AXIOMS:"
# Lean's tokenizer only treats these characters as whitespace.
LEAN_WHITESPACE = " \t\r\n"
# User modules may only import the exported target modules and the bundled
# `Trusted` / `Anneal` libraries.
USER_IMPORT_PREFIXES = ("Trusted", "Anneal")
USER_IMPORT_EXACT = frozenset({"Expected", "Captured"})
# Matched against the code after the header, so `import` and `prelude` here
# only catch misplaced header keywords. Prefix operators such as `!` and `.`
# are deliberately excluded from the lookbehind so `!by_elab`, `!sorry`, and
# `_root_.sorry` are caught.
BANNED_USER_KEYWORDS_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(macro|macro_rules|syntax|declare_syntax_cat|elab|elab_rules|"
    r"initialize|builtin_initialize|meta|run_cmd|run_elab|run_meta|run_tac|"
    r"by_elab|notation|infix|infixl|infixr|prefix|postfix|axiom|opaque|"
    r"unsafe|partial|attribute|set_option|import|prelude|native_decide|"
    r"decide!|bv_decide|rfl'|grind|sleep|include_str|dbg_trace|sorry|admit|"
    r"extern|implemented_by|export)"
    r"(?![A-Za-z0-9_'!?])"
)
# Banned even when namespace-qualified (for example `Lean.reduceBool`).
BANNED_USER_IDENTS_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(ofReduceBool|ofReduceNat|reduceBool|reduceNat|trustCompiler|"
    r"skipKernelTC|addDecl|sorryAx|unsafeIO|unsafeBaseIO|unsafeEIO|unsafeCast|"
    r"dbgTrace|dbgTraceVal|dbgTraceIfShared|dbgStackTrace|dbgStackTraceIf|"
    r"dbgSleep|lean_dbg_trace|lean_dbg_trace_if_shared|lean_dbg_stack_trace|"
    r"lean_dbg_sleep|loadDynlib|loadPlugin|lean_load_dynlib|lean_load_plugin|"
    r"lean_dynlib_load|lean_dynlib_get|lean_dynlib_symbol_run_as_init|"
    r"includeStr)"
    r"(?![A-Za-z0-9_'])"
)
# Banned tactic configuration flags (`decide +native`, `decide +kernel`,
# `decide (config := { native := true })`).
BANNED_USER_TACTIC_FLAGS_RE = re.compile(
    r"\+\s*(native|kernel)(?![A-Za-z0-9_'])"
    r"|(?<![A-Za-z0-9_'])(config|native|kernel)\s*:=(?!=)"
)
BANNED_USER_HASH_COMMAND_RE = re.compile(r"#[A-Za-z_]")
BANNED_USER_ATTRIBUTE_RE = re.compile(
    r"(?<![A-Za-z0-9_'.])"
    r"(extern|implemented_by|init|builtin_init|builtin_[A-Za-z0-9_]*|export|"
    r"csimp|macro|command_elab|term_elab|tactic|env_linter)"
    r"(?![A-Za-z0-9_'])"
)

CONCRETE_REFUTE_MODULE = "Anneal.Diag.ConcreteRefute"
TOOLCHAIN_MODULE_ROOTS = frozenset({"Init", "Std", "Lean"})
# Compiled outputs copied from a sandbox output directory into the stage.
LEAN_OUTPUT_SUFFIXES = (
    ".olean",
    ".olean.server",
    ".olean.private",
    ".ir",
    ".ir.sig",
    ".ilean",
)
COMPILED_PROOF_SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ilean")
# Verdicts that show the specification is inadequate. Only these satisfy a
# suite case with `expect_adequate: false`; setup and infrastructure failures
# (`baseline_failed`, `spec_unlocked`, `crash_masquerade`, `*_error`, ...)
# never do.
SEMANTIC_INADEQUATE = frozenset(
    {"vacuous_spec_false_kill", "pre_vacuous", "mutant_verified"}
)
ARTIFACT_MARKER = ".audit-spec-case"

# `compilation` keys locating the (possibly mutated) program. Every other key
# changes semantics and must match the baseline. Defaults mirror
# `Compilation` in `trusted/cargo-anneal/src/verify.rs`.
COMPILATION_PROGRAM_KEYS = frozenset({"source_root", "crate_root", "source_files"})
COMPILATION_DEFAULTS: dict[str, Any] = {
    "crate_type": "lib",
    "panic": "unwind",
    "overflow_checks": False,
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "cfg": [],
    "env": {},
    "stdlib_crate": None,
}
DEFAULT_SPECIFICATION = "Spec.specs"
DEFAULT_THEOREM = "Proof.verify"
AUTHORED_ROLES = ("specification", "proof")
PROOF_SOURCE_KEYS = frozenset({"module", "path", "role"})

BWRAP_CANDIDATES = (Path("/usr/bin/bwrap"), Path("/bin/bwrap"))
_BWRAP_BASE_MOUNTS = (
    "--tmpfs", "/",
    "--dev", "/dev",
    "--proc", "/proc",
    "--tmpfs", "/tmp",
    # Not all of `/usr`: home directories may live under `/usr/local`.
    "--ro-bind", "/usr/lib", "/usr/lib",
    "--ro-bind-try", "/usr/lib64", "/usr/lib64",
    "--ro-bind", "/usr/bin", "/usr/bin",
    "--ro-bind-try", "/bin", "/bin",
    "--ro-bind-try", "/lib", "/lib",
    "--ro-bind-try", "/lib64", "/lib64",
    "--ro-bind-try", "/etc/ld.so.cache", "/etc/ld.so.cache",
    "--ro-bind-try", "/nix/store", "/nix/store",
)

# Runs in its own sandboxed `lean --run` process. It imports only compiled
# `.olean` files (toolchain first on the search path, `loadExts := false`,
# `level := .private`), so no user source is elaborated and no `[init]`
# callbacks run while the checked theorem's type, origin, and axiom closure are
# computed. Every non-sysroot constant in the closure is checked against Lean's
# reserved/kernel-accelerated namespaces (`TrustedBoundary.lean`), non-sysroot
# axioms/quotients/opaques are rejected, and the whole closure is replayed
# through the kernel in a fresh environment (`unsafe` and `partial` constants
# are rejected and never omitted).
AXIOM_INSPECTOR_SRC = """\
import Lean
open Lean

def auditReservedKernelRoots : List Name :=
  [`Nat, `String, `Char, `Bool, `Int, `Int8, `Int16, `Int32, `Int64, `ISize,
   `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Float, `Float32,
   `ByteArray, `Subarray, `Array, `List, `Option, `Sum, `Prod, `Fin, `Subtype,
   `Eq, `HEq, `Quot, `Classical, `Lean, `Init, `Std, `Lake, `LeanExport,
   `LeanIR, `System, `IO, `Task, `Thunk, `Unit, `PUnit, `Empty, `PEmpty, `True,
   `False, `And, `Or, `Not, `Iff, `Exists, `Sigma, `PSigma, `Decidable,
   `Nonempty, `Ordering, `Rat, `Except, `EStateM, `StateM]

def auditKernelAcceleratedNames : List Name :=
  [`Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd,
   `Nat.mod, `Nat.div, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor,
   `Nat.shiftLeft, `Nat.shiftRight, `String.ofList]

def auditHasCompoundName : Name → Bool
  | .str .anonymous _ | .num .anonymous _ | .anonymous => false
  | _ => true

def auditCollectAllMatchers (env : Environment) : NameSet := Id.run do
  let mut matchers : NameSet := {}
  for modIdx in Array.range env.header.moduleData.size do
    for entry in
        Lean.Meta.Match.Extension.extension.getModuleEntries env modIdx do
      matchers := matchers.insert entry.name
  return matchers

partial def auditIsUpstreamHelperRoot (env : Environment)
    (allMatchers : NameSet) (isOrigin : Name → Bool) (n userN : Name) : Bool :=
  if auditHasCompoundName userN && isOrigin userN then
    true
  else
    match n, userN with
    | .str rawParent _, .str userParent "splitter" =>
      (allMatchers.contains rawParent || allMatchers.contains userParent) &&
        auditIsUpstreamHelperRoot env allMatchers isOrigin rawParent userParent
    | .str rawParent _, .str userParent _ =>
      let isKnownSparse :=
        (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome
      let isKnownMatcher :=
        allMatchers.contains n || allMatchers.contains userN
      (isKnownSparse || isKnownMatcher) &&
        auditIsUpstreamHelperRoot env allMatchers isOrigin rawParent userParent
    | _, _ => false

def auditIsCompilerHelper (env : Environment) (allMatchers : NameSet)
    (isOrigin : Name → Bool) (ci : ConstantInfo) : Bool :=
  let n := ci.name
  let userN := privateToUserName n
  let hasParent := auditIsUpstreamHelperRoot env allMatchers isOrigin
  match ci, n, userN with
  | .thmInfo _, .str rawParent _, .str userParent suffix =>
    ((Lean.isReservedName env n || Lean.isReservedName env userN) &&
      hasParent rawParent userParent) ||
    ((allMatchers.contains rawParent || allMatchers.contains userParent) &&
      (suffix == "splitter" || Lean.Meta.isEqnReservedNameSuffix suffix ||
        Lean.Meta.Match.isCongrEqnReservedNameSuffix suffix) &&
      hasParent rawParent userParent)
  | .defnInfo _, .str rawParent _, .str userParent suffix =>
    isPrivateName n &&
      if suffix == "splitter" then
        (allMatchers.contains rawParent || allMatchers.contains userParent) &&
          hasParent rawParent userParent
      else if (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome then
        hasParent rawParent userParent
      else
        false
  | _, _, _ => false

def auditDeps (ci : ConstantInfo) : NameSet := Id.run do
  let mut s := ci.getUsedConstantsAsSet
  for c in ci.all do s := s.insert c
  match ci with
  | .inductInfo v =>
    for c in v.ctors do s := s.insert c
    for c in v.all do s := s.insert c
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v =>
    for c in v.all do s := s.insert c
    for r in v.rules do
      s := s.insert r.ctor
      for c in r.rhs.getUsedConstants do s := s.insert c
  -- The kernel needs `Eq` before it accepts `Quot` declarations.
  | .quotInfo _ => s := s.insert ``Eq
  | _ => pure ()
  return s

def auditFail (msg : String) : IO α := throw (IO.userError msg)

def auditModuleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def auditCheckOrigin (env : Environment) (spec : String) : IO Name := do
  match spec.splitOn "@" with
  | [c, m] =>
    let cn := c.toName
    match auditModuleOf env cn with
    | some mod =>
      unless mod == m.toName do
        auditFail s!"{c} comes from module {mod}, expected {m}"
      pure cn
    | none => auditFail s!"{c} is not an imported constant"
  | _ => auditFail s!"malformed origin spec {spec}"

def main (args : List String) : IO Unit := do
  let libDir :: modStr :: declStr :: nonce :: mode :: rest := args
    | auditFail "usage: <libDir> <module> <decl> <nonce> <mode> <origins>..."
  let sysroot ← findSysroot
  let sysrootLib := sysroot / "lib" / "lean"
  searchPathRef.set [sysrootLib, System.FilePath.mk libDir]
  let env ← importModules #[{ module := modStr.toName }] {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  unless env.header.modules.size == env.header.moduleData.size do
    auditFail "module/data array alignment failure"
  let mut sysrootMods : NameSet := {}
  let mut trustedMods : NameSet := {}
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    let d := env.header.moduleData[i]!
    unless d.constNames == d.constants.map ConstantInfo.name do
      auditFail s!"invalid constant inventory in {m}"
    let mRoot := m.getRoot
    let inSysroot ← (Lean.modToFilePath sysrootLib m "olean").pathExists
    if inSysroot then
      unless mRoot == `Init || mRoot == `Std do
        auditFail s!"disallowed sysroot module {m}"
      sysrootMods := sysrootMods.insert m
    else
      if mRoot == `Init || mRoot == `Std || mRoot == `Lean || mRoot == `Lake then
        auditFail s!"non-sysroot module {m} uses reserved sysroot prefix"
      if m == `Trusted || mRoot == `Trusted then
        trustedMods := trustedMods.insert m
  for (k, c) in env.checked.get.constants do
    if k.isAnonymous || c.name.isAnonymous || k != c.name then
      auditFail s!"mismatched checked environment key {k} for {c.name}"
  let decl := declStr.toName
  let some ci := env.find? decl | auditFail s!"missing {declStr}"
  unless (ci matches .thmInfo _) && ci.levelParams.isEmpty do
    auditFail s!"{declStr} is not a universe-monomorphic theorem"
  unless auditModuleOf env decl == some modStr.toName do
    auditFail s!"{declStr} is not declared in {modStr}"
  let expected ← match mode, rest with
    | "not_claim", [claim] => do
      let c ← auditCheckOrigin env claim
      pure (mkApp (mkConst ``Not) (mkConst c))
    | "app2", [f, a, b] => do
      let fc ← auditCheckOrigin env f
      let ac ← auditCheckOrigin env a
      let bc ← auditCheckOrigin env b
      pure (mkApp2 (mkConst fc) (mkConst ac) (mkConst bc))
    | "nv_claim", [claimConst, specOrigin, progOrigin] => do
      let cc ← auditCheckOrigin env claimConst
      let sc ← auditCheckOrigin env specOrigin
      let pc ← auditCheckOrigin env progOrigin
      let some claimCi := env.find? cc | auditFail s!"missing {claimConst}"
      unless claimCi matches .defnInfo _ do
        auditFail s!"{claimConst} is not a definition"
      let used := claimCi.getUsedConstantsAsSet
      unless used.contains sc do
        auditFail s!"{claimConst} does not reference {specOrigin}"
      unless used.contains pc do
        auditFail s!"{claimConst} does not reference {progOrigin}"
      let specMod := ((specOrigin.splitOn "@").drop 1).headD "" |>.toName
      for u in used do
        match auditModuleOf env u with
        | some mod =>
          let root := mod.getRoot
          let ok := (sysrootMods.contains mod && root == `Init) ||
            trustedMods.contains mod || mod == `Captured || mod == specMod
          unless ok do
            auditFail s!"{claimConst} references untrusted {u} from {mod}"
        | none => auditFail s!"{claimConst} references non-imported {u}"
      pure (mkConst cc)
    | _, _ => auditFail s!"unknown mode {mode}"
  unless ci.type == expected do
    auditFail s!"{declStr} has unexpected type {ci.type}"
  let allMatchers := auditCollectAllMatchers env
  let isSysConst (k : Name) : Bool :=
    match auditModuleOf env k with
    | some m => sysrootMods.contains m
    | none => false
  let isTrustedConst (k : Name) : Bool :=
    match auditModuleOf env k with
    | some m => trustedMods.contains m
    | none => false
  let mut visited : NameSet := {}
  let mut closure : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut stack : List Name := [decl]
  repeat
    match stack with
    | [] => break
    | n :: tl =>
      stack := tl
      if visited.contains n then continue
      visited := visited.insert n
      if n.isAnonymous then auditFail "anonymous constant in closure"
      let some c := env.find? n | auditFail s!"dangling constant {n}"
      unless c.name == n do
        auditFail s!"constant key {n} differs from ConstantInfo.name {c.name}"
      let some mod := auditModuleOf env n
        | auditFail s!"constant {n} has no defining module"
      let isSys := sysrootMods.contains mod
      if c.isUnsafe || c.isPartial then
        auditFail s!"unsafe or partial constant {n} in {mod}"
      if c.hasValue true && (c.value? true).isNone then
        auditFail s!"missing stored body for {n} in {mod}"
      if c matches .axiomInfo _ then
        unless isSys && (mod == `Init.Prelude || mod == `Init.Core) do
          auditFail s!"non-foundation axiom {n} in {mod}"
        axioms := axioms.push n
      if c matches .quotInfo _ then
        unless isSys && (mod == `Init.Prelude || mod == `Init.Core) &&
            (n == ``Quot || n == ``Quot.mk ||
             n == ``Quot.lift || n == ``Quot.ind) do
          auditFail s!"unauthorized quotient primitive {n} in {mod}"
      if !isSys then
        if c matches .opaqueInfo _ then
          auditFail s!"non-sysroot opaque constant {n} in {mod}"
        let userName := privateToUserName n
        let userRoot := userName.getRoot
        if !trustedMods.contains mod && userRoot == `Trusted &&
            !auditIsCompilerHelper env allMatchers isTrustedConst c then
          auditFail s!"non-Trusted module {mod} cannot declare {n} in Trusted"
        if auditKernelAcceleratedNames.contains userName ||
            (auditReservedKernelRoots.contains userRoot &&
              !auditIsCompilerHelper env allMatchers isSysConst c) then
          auditFail (s!"non-sysroot module {mod} cannot declare {n} " ++
            s!"in reserved kernel namespace {userRoot}")
      closure := closure.insert n c
      for d in auditDeps c do
        unless visited.contains d do stack := d :: stack
  let kenv ← (← mkEmptyEnvironment).toKernelEnv.replay closure
  for (n, _) in closure.toList do
    unless (kenv.find? n).isSome do
      auditFail s!"kernel replay did not admit {n}"
  let names := axioms.qsort (·.toString < ·.toString) |>.map (·.toString)
  IO.println s!"AUDIT_SPEC_AXIOMS:{nonce}:{(toJson names).compress}"
"""


class SandboxUnavailable(RuntimeError):
    """No usable OS sandbox for elaborating untrusted Lean modules."""


class StageError(RuntimeError):
    """The Pole B / non-vacuity Lean stage could not be assembled."""


class SandboxRunner(Protocol):
    """Runs a command with only `ro`/`rw` host paths visible."""

    def run(
        self,
        cmd: Sequence[str],
        *,
        ro: Sequence[Path],
        rw: Sequence[Path],
        cwd: Path,
        env: dict[str, str],
        timeout: float,
    ) -> subprocess.CompletedProcess[str]: ...


@dataclass(frozen=True)
class LeanSandbox:
    """`bwrap` jail for Lean processes that may load untrusted user code.

    The child gets no network, IPC, or PID sharing with the host (it and any
    descendants die with the sandbox), no capabilities, an allowlisted
    environment, read-only system libraries, read-only `ro` paths, and
    writable `rw` paths only.
    """

    bwrap: Path
    disable_userns: bool = True

    def argv(
        self,
        cmd: Sequence[str],
        *,
        ro: Sequence[Path],
        rw: Sequence[Path],
        cwd: Path,
        env: dict[str, str],
    ) -> list[str]:
        args = [str(self.bwrap), "--unshare-all"]
        if self.disable_userns:
            args += ["--unshare-user", "--disable-userns"]
        args += [
            "--die-with-parent",
            "--new-session",
            "--clearenv",
            "--cap-drop",
            "ALL",
            *_BWRAP_BASE_MOUNTS,
        ]
        binds = [(Path(p), False) for p in ro] + [(Path(p), True) for p in rw]
        # Parents first, so a nested bind keeps its own access mode.
        for path, writable in sorted(binds, key=lambda b: len(b[0].parts)):
            if not path.is_absolute():
                raise ValueError(f"sandbox bind must be absolute: {path}")
            args += ["--bind" if writable else "--ro-bind", str(path), str(path)]
        args += ["--chdir", str(cwd)]
        for key, val in sorted(env.items()):
            args += ["--setenv", key, val]
        return [*args, "--", *cmd]

    def run(
        self,
        cmd: Sequence[str],
        *,
        ro: Sequence[Path],
        rw: Sequence[Path],
        cwd: Path,
        env: dict[str, str],
        timeout: float,
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            self.argv(cmd, ro=ro, rw=rw, cwd=cwd, env=env),
            cwd="/",
            env={},
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            check=False,
        )

    @classmethod
    def probe(
        cls, candidates: Sequence[Path] = BWRAP_CANDIDATES
    ) -> "LeanSandbox":
        """Return a working sandbox or raise `SandboxUnavailable`.

        Only canonical system paths are considered (never `PATH`).
        """
        errors: list[str] = []
        for cand in candidates:
            try:
                if not cand.is_file():
                    continue
            except OSError:
                continue
            for disable_userns in (True, False):
                sandbox = cls(cand, disable_userns)
                try:
                    proc = sandbox.run(
                        ["/usr/bin/true"],
                        ro=(),
                        rw=(),
                        cwd=Path("/"),
                        env={},
                        timeout=60,
                    )
                except (OSError, subprocess.TimeoutExpired) as exc:
                    errors.append(f"{cand}: {exc}")
                    continue
                if proc.returncode == 0:
                    return sandbox
                errors.append(
                    f"{cand} (disable_userns={disable_userns}): "
                    f"{proc.stderr.strip()[:200]}"
                )
        raise SandboxUnavailable(
            "elaborating untrusted Lean witnesses requires a working bubblewrap "
            "at /usr/bin/bwrap or /bin/bwrap: "
            + ("; ".join(errors) or "not found")
        )


@dataclass(frozen=True)
class PoleAClassification:
    """Result of classifying a Pole A `cargo-anneal verify` invocation."""

    clean_reject: bool
    classification: str
    status: str | None
    phase: str | None
    reason: str | None
    detail: str
    returncode: int


@dataclass(frozen=True)
class LeanRefuteCheck:
    """Result of kernel-checking a Pole B or non-vacuity Lean module.

    `infrastructure_error` marks failures to stage or run the check, which say
    nothing about the specification.
    """

    passed: bool
    axioms: tuple[str, ...]
    kernel_replayed: bool
    infrastructure_error: bool
    detail: str


@dataclass(frozen=True)
class CaseResult:
    """Structured dual-polar adequacy outcome for one target/mutant case."""

    name: str
    baseline_verified: bool | None
    spec_locked: bool
    pre_non_vacuous: bool | None
    pole_a_clean_reject: bool
    pole_b_refuted: bool
    dual_polar_adequate: bool
    classification: str
    detail: str
    pole_a: dict[str, Any]
    pole_b: dict[str, Any]
    nonvacuity: dict[str, Any] | None = None


@dataclass(frozen=True)
class LockedRequest:
    """The parts of a verify request that the spec lock compares."""

    path: Path
    schema_version: Any
    scope: Any
    compilation: dict[str, Any]
    specification: str
    theorem: str
    specification_module: str
    theorem_module: str
    # module -> (role, sha256)
    sources: dict[str, tuple[str, str]]
    # Directories holding the request's inputs.
    input_dirs: tuple[Path, ...] = ()

    @property
    def scope_kind(self) -> Any:
        return self.scope.get("kind") if isinstance(self.scope, dict) else None

    def modules(self, role: str) -> tuple[str, ...]:
        return tuple(m for m, (r, _) in self.sources.items() if r == role)


def _fail_check(detail: str, *, infrastructure: bool = False) -> LeanRefuteCheck:
    return LeanRefuteCheck(
        passed=False,
        axioms=(),
        kernel_replayed=False,
        infrastructure_error=infrastructure,
        detail=detail,
    )


def _source_starts_with_module_keyword(text: str) -> bool:
    """Return whether Lean source begins with `module` (matching `stage.rs`)."""
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if text.startswith("--", i):
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        break
    return (
        text.startswith("module", i)
        and (i + 6 == n or text[i + 6].isspace())
    )


def is_lean_ident(raw: str) -> bool:
    """Return whether `raw` is a plain dotted Lean identifier."""
    return isinstance(raw, str) and LEAN_IDENT_RE.fullmatch(raw) is not None


def is_valid_case_name(raw: str) -> bool:
    """Return whether `raw` is safe to use as an artifacts subdirectory."""
    return (
        isinstance(raw, str)
        and raw not in (".", "..")
        and CASE_NAME_RE.fullmatch(raw) is not None
    )


def _module_of_decl(decl: str, label: str) -> str:
    if "." not in decl:
        raise RuntimeError(
            f"{label} must be a qualified Lean declaration name: {decl!r}"
        )
    return decl.rsplit(".", 1)[0]


def _optional_module(proof: dict[str, Any], key: str, decl: str) -> str:
    raw = proof.get(key)
    if raw is None:
        return _module_of_decl(decl, f"proof.{key.removesuffix('_module')}")
    if not is_lean_ident(raw):
        raise RuntimeError(f"invalid proof.{key}: {raw!r}")
    return raw


def _walk_without_symlinks(base: Path, rel: Path, label: str) -> Path:
    """Join `rel` onto `base`, rejecting escapes and symlinked components.

    Every component is checked before anything is resolved, so a symlink that
    happens to point back inside `base` is still rejected.
    """
    if rel.is_absolute() or not rel.parts or ".." in rel.parts:
        raise RuntimeError(f"{label} must be a relative path below its root: {rel}")
    cur = base
    for part in rel.parts:
        cur = cur / part
        if cur.is_symlink():
            raise RuntimeError(f"{label} has a symlinked path component: {cur}")
    return cur


def load_locked_request(path: Path) -> LockedRequest:
    """Parse a verify request strictly and hash its authored sources."""
    data = anneal_ci_lib.load_strict_json_object(path, "request")
    proof = data.get("proof")
    if not isinstance(proof, dict):
        raise RuntimeError(f"missing proof object in {path}")
    compilation = data.get("compilation")
    if not isinstance(compilation, dict):
        raise RuntimeError(f"missing compilation object in {path}")

    spec_decl = proof.get("specification", DEFAULT_SPECIFICATION)
    theorem_decl = proof.get("theorem", DEFAULT_THEOREM)
    for key, decl in (("specification", spec_decl), ("theorem", theorem_decl)):
        if not is_lean_ident(decl):
            raise RuntimeError(f"invalid proof.{key} in {path}: {decl!r}")
    spec_module = _optional_module(proof, "specification_module", spec_decl)
    theorem_module = _optional_module(proof, "theorem_module", theorem_decl)

    source_root = proof.get("source_root")
    if not isinstance(source_root, str) or not source_root:
        raise RuntimeError(f"invalid proof.source_root in {path}")
    req_dir = path.parent.resolve(strict=True)
    proof_root = Path(os.path.normpath(req_dir / source_root))
    if proof_root.is_symlink() or not proof_root.is_dir():
        raise RuntimeError(
            f"proof.source_root must be a regular directory: {proof_root}"
        )
    proof_root_real = proof_root.resolve(strict=True)

    raw_sources = proof.get("sources")
    if not isinstance(raw_sources, list):
        raise RuntimeError(f"invalid proof.sources in {path}")
    sources: dict[str, tuple[str, str]] = {}
    for entry in raw_sources:
        if not isinstance(entry, dict) or set(entry) != PROOF_SOURCE_KEYS:
            raise RuntimeError(f"malformed proof source entry in {path}: {entry!r}")
        mod, rel, role = entry["module"], entry["path"], entry["role"]
        if not isinstance(mod, str) or not is_lean_ident(mod):
            raise RuntimeError(f"invalid proof source module name: {mod!r}")
        if role not in AUTHORED_ROLES:
            raise RuntimeError(f"invalid role {role!r} for module {mod}")
        if not isinstance(rel, str) or not rel:
            raise RuntimeError(f"invalid path for module {mod}: {rel!r}")
        if mod in sources:
            raise RuntimeError(f"duplicate proof source module {mod} in {path}")
        src_path = _walk_without_symlinks(proof_root, Path(rel), f"source of {mod}")
        if not src_path.resolve(strict=True).is_relative_to(proof_root_real):
            raise RuntimeError(f"source of {mod} escapes proof.source_root")
        sources[mod] = (
            role,
            anneal_ci_lib.sha256_file(
                src_path, reject_symlink=True, missing_label=f"source of {mod}"
            ),
        )
    input_dirs = [req_dir, proof_root_real]
    comp_root = compilation.get("source_root")
    if isinstance(comp_root, str) and comp_root:
        input_dirs.append(Path(os.path.normpath(req_dir / comp_root)))
    locked = LockedRequest(
        path=path,
        schema_version=data.get("schema_version"),
        scope=data.get("scope"),
        compilation=_semantic_compilation(compilation),
        specification=spec_decl,
        theorem=theorem_decl,
        specification_module=spec_module,
        theorem_module=theorem_module,
        sources=sources,
        input_dirs=tuple(input_dirs),
    )
    if spec_module not in locked.modules("specification"):
        raise RuntimeError(
            f"specification module {spec_module} declaring {spec_decl} is not "
            f"a `specification` source in {path}"
        )
    if theorem_module not in locked.modules("proof"):
        raise RuntimeError(
            f"theorem module {theorem_module} is not a `proof` source in {path}"
        )
    return locked


def _semantic_compilation(compilation: dict[str, Any]) -> dict[str, Any]:
    out = {
        k: v for k, v in compilation.items() if k not in COMPILATION_PROGRAM_KEYS
    }
    for key, default in COMPILATION_DEFAULTS.items():
        out.setdefault(key, default)
    cfg = out.get("cfg")
    if isinstance(cfg, list) and all(isinstance(c, str) for c in cfg):
        out["cfg"] = sorted(set(cfg))
    return out


def lock_requests(
    baseline_request: Path | None,
    mutant_request: Path,
) -> tuple[tuple[LockedRequest, LockedRequest] | None, str]:
    """Return `(baseline, mutant)` if they only differ in the program."""
    if baseline_request is None:
        return None, "a baseline request is required to lock the spec"
    try:
        base = load_locked_request(baseline_request)
        mut = load_locked_request(mutant_request)
    except RuntimeError as exc:
        return None, f"invalid request: {exc}"
    for label, b_val, m_val in (
        ("schema_version", base.schema_version, mut.schema_version),
        ("scope", base.scope, mut.scope),
        ("semantic compilation flags", base.compilation, mut.compilation),
        ("proof.specification", base.specification, mut.specification),
        ("proof.theorem", base.theorem, mut.theorem),
        (
            "proof.specification_module",
            base.specification_module,
            mut.specification_module,
        ),
        ("proof.theorem_module", base.theorem_module, mut.theorem_module),
    ):
        if b_val != m_val:
            return None, f"{label} mismatch between baseline and mutant requests"
    base_roles = {m: r for m, (r, _) in base.sources.items()}
    mut_roles = {m: r for m, (r, _) in mut.sources.items()}
    if base_roles != mut_roles:
        return None, "authored source modules or roles differ from the baseline"
    for mod, (role, sha) in mut.sources.items():
        if base.sources[mod][1] != sha:
            what = "specification" if role == "specification" else "shipped proof"
            return None, f"{what} source SHA-256 mismatch vs baseline ({mod})"
    return (base, mut), f"spec locked against baseline ({mut.specification})"


def verify_spec_lock(
    baseline_request: Path | None,
    mutant_request: Path,
) -> tuple[bool, str]:
    """Ensure baseline and mutant agree on everything but the Rust program.

    A baseline is required: without one there is nothing to lock against.
    """
    locked, msg = lock_requests(baseline_request, mutant_request)
    return locked is not None, msg


def _pole_a(
    clean: bool,
    classification: str,
    payload: dict[str, Any],
    detail: str,
    returncode: int,
) -> PoleAClassification:
    def opt_str(key: str) -> str | None:
        val = payload.get(key)
        return val if isinstance(val, str) else None

    return PoleAClassification(
        clean_reject=clean,
        classification=classification,
        status=opt_str("status"),
        phase=opt_str("phase"),
        reason=opt_str("reason"),
        detail=detail,
        returncode=returncode,
    )


def classify_pole_a_result(
    returncode: int,
    stdout: str,
    stderr: str,
) -> PoleAClassification:
    """Classify a mutant `cargo-anneal verify` invocation for Pole A.

    Only a clean Receipt v3 `proof_failed` failure (`exit == 1`, `phase ==
    "audit"`, `reason` null, empty `taint_reasons`, OS elaboration sandbox,
    empty stderr, no crash markers) counts as a Pole A kill. Any resource-limit
    `reason` is rejected, whether or not it is a known marker.
    """
    stderr_clean = stderr.strip()
    try:
        payload = json.loads(
            stdout, object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys
        )
    except ValueError as exc:
        return _pole_a(
            False,
            "malformed_output",
            {},
            f"invalid JSON receipt stdout (exit {returncode}): {exc}",
            returncode,
        )
    if not isinstance(payload, dict):
        return _pole_a(
            False,
            "malformed_output",
            {},
            "receipt JSON root is not an object",
            returncode,
        )
    status = payload.get("status")
    reason = payload.get("reason")
    detail = str(payload.get("detail") or "")

    if not anneal_ci_lib.is_exact_int(
        payload.get("schema_version"), RECEIPT_SCHEMA_VERSION
    ):
        return _pole_a(
            False,
            "malformed_output",
            payload,
            f"expected Receipt v{RECEIPT_SCHEMA_VERSION}, got "
            f"schema_version={payload.get('schema_version')!r}",
            returncode,
        )
    if status in PASSING_STATUSES:
        if returncode == 0:
            return _pole_a(
                False,
                "mutant_verified",
                payload,
                f"mutant unexpectedly passed verification ({status})",
                returncode,
            )
        return _pole_a(
            False,
            "unexpected_failure",
            payload,
            f"passing status {status!r} with exit {returncode}",
            returncode,
        )
    if stderr_clean:
        return _pole_a(
            False,
            "crash_masquerade",
            payload,
            f"non-empty stderr on failure: {stderr_clean[:240]}",
            returncode,
        )
    if status == "proof_failed" and reason is not None:
        return _pole_a(
            False,
            "resource_limit",
            payload,
            f"proof_failed with resource-limit reason {reason!r}: {detail[:240]}",
            returncode,
        )
    combined_lower = "\n".join([detail, str(reason or "")]).lower()
    for marker in CRASH_MASQUERADE_MARKERS:
        if marker in combined_lower:
            return _pole_a(
                False,
                "crash_masquerade",
                payload,
                f"failure matched crash/resource marker `{marker}`: {detail[:240]}",
                returncode,
            )
    failures = anneal_ci_lib.validate_receipt_v3_envelope(
        payload,
        returncode=returncode,
        expected_status="proof_failed",
        expected_returncode=1,
    )
    if payload.get("phase") != "audit":
        failures.append(f"phase={payload.get('phase')!r}")
    if failures:
        return _pole_a(
            False,
            "unexpected_failure",
            payload,
            f"expected a clean audit proof_failed receipt: {', '.join(failures)}; "
            f"{detail[:240]}",
            returncode,
        )
    return _pole_a(True, "clean_proof_failed", payload, detail[:240], returncode)


def parse_inspector_output(stdout: str, nonce: str) -> tuple[str, ...] | None:
    """Parse the axiom inspector's single nonce-tagged JSON line.

    Returns the sorted axiom names, or `None` if there is not exactly one
    inspector line, the nonce differs, or the payload is malformed.
    """
    lines = [
        line
        for line in stdout.splitlines()
        if line.startswith(INSPECTOR_LINE_PREFIX)
    ]
    prefix = f"{INSPECTOR_LINE_PREFIX}{nonce}:"
    if len(lines) != 1 or not lines[0].startswith(prefix):
        return None
    try:
        data = json.loads(lines[0][len(prefix):])
    except json.JSONDecodeError:
        return None
    if not isinstance(data, list) or not all(isinstance(x, str) for x in data):
        return None
    return tuple(data)


def _scan_lean_char_literal(text: str, pos: int) -> int | None:
    """Return index past a Lean `'...'` literal at `pos`, or `None`."""
    n = len(text)
    if pos + 2 >= n or text[pos] != "'":
        return None
    if text[pos + 1] == "\\":
        esc = text[pos + 2]
        if esc == "x":
            end = pos + 5
        elif esc == "u":
            end = pos + 7
        elif esc in ("\\", "'", '"', "n", "r", "t", "0"):
            end = pos + 3
        else:
            return None
        if end < n and text[end] == "'":
            return end + 1
        return None
    if text[pos + 1] not in ("'", "\n") and text[pos + 2] == "'":
        return pos + 3
    return None


def _strip_lean_comments(
    text: str, *, allow_strings: bool = False
) -> tuple[str | None, str]:
    """Strip Lean comments, keeping `«...»` names opaque and spaced.

    Returns `(code, "")`, or `(None, reason)` for unterminated comments or
    names and (unless `allow_strings`) for string literals, which user modules
    never need. With `allow_strings`, string literals become `""`.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if text.startswith("--", i):
            nl = text.find("\n", i)
            i = n if nl == -1 else nl
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth > 0:
                return None, "unterminated block comment"
            out.append(" ")
            continue
        if ch.isalpha() or ch == "_":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] in "_'"):
                j += 1
            out.append(text[i:j])
            i = j
            continue
        char_end = _scan_lean_char_literal(text, i)
        if char_end is not None:
            out.append("'a'")
            i = char_end
            continue
        if ch == '"':
            if not allow_strings:
                return None, "string literals are not allowed"
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                return None, "unterminated string literal"
            out.append('""')
            i = j + 1
            continue
        if ch == "\u00ab":
            end = text.find("\u00bb", i + 1)
            if end == -1 or "\n" in text[i:end]:
                return None, "unterminated `«...»` name"
            inner = text[i + 1 : end]
            if not allow_strings:
                m_id = BANNED_USER_IDENTS_RE.fullmatch(inner)
                if m_id:
                    return None, f"`{m_id.group(1)}` is not allowed in user modules"
                m_attr = BANNED_USER_ATTRIBUTE_RE.fullmatch(inner)
                if m_attr:
                    return (
                        None,
                        "metaprogramming attributes are not allowed in user modules",
                    )
                m_kw = BANNED_USER_KEYWORDS_RE.fullmatch(inner)
                if m_kw:
                    return None, f"`{m_kw.group(1)}` is not allowed in user modules"
            out.append(" _q_ ")
            i = end + 1
            continue
        out.append(ch)
        i += 1
    return "".join(out), ""


def _next_word(code: str, pos: int) -> tuple[str | None, int]:
    n = len(code)
    while pos < n and code[pos] in LEAN_WHITESPACE:
        pos += 1
    match = LEAN_IDENT_RE.match(code, pos)
    if match is None:
        return None, pos
    return match.group(0), match.end()


@dataclass(frozen=True)
class LeanHeader:
    """A parsed Lean module header (`module`? `prelude`? import*)."""

    is_module: bool
    has_prelude: bool
    # (modifiers, module) per import directive; modifiers from
    # `public` / `meta` / `private` / `all`.
    imports: tuple[tuple[tuple[str, ...], str], ...]
    body_start: int


def parse_lean_header(code: str) -> LeanHeader:
    """Parse the header of comment-stripped Lean source.

    Follows `Lean.Parser.Module.header`: whitespace (including newlines) may
    separate every token, and each `import` names exactly one module. Raises
    `ValueError` on a malformed `import` directive.
    """
    word, pos = _next_word(code, 0)
    is_module = word == "module"
    if is_module:
        start = pos
        word, pos = _next_word(code, pos)
    else:
        start = 0
    has_prelude = word == "prelude"
    if not has_prelude:
        pos = start
    imports: list[tuple[tuple[str, ...], str]] = []
    while True:
        mods: list[str] = []
        word, nxt = _next_word(code, pos)
        while word in ("public", "meta", "private"):
            mods.append(word)
            word, nxt = _next_word(code, nxt)
        if word != "import":
            break
        word, nxt = _next_word(code, nxt)
        if word == "all":
            mods.append("all")
            word, nxt = _next_word(code, nxt)
        if word is None:
            raise ValueError("malformed `import` directive")
        if nxt < len(code) and code[nxt] not in LEAN_WHITESPACE:
            raise ValueError(f"malformed import of `{word}`")
        imports.append((tuple(mods), word))
        pos = nxt
    return LeanHeader(is_module, has_prelude, tuple(imports), pos)


def _attribute_blocks(code: str) -> list[str] | None:
    """Return the contents of every `@[...]`, or `None` if one is unclosed."""
    blocks: list[str] = []
    i = 0
    while (start := code.find("@[", i)) != -1:
        depth = 1
        j = start + 2
        while j < len(code) and depth:
            if code[j] == "[":
                depth += 1
            elif code[j] == "]":
                depth -= 1
            j += 1
        if depth:
            return None
        blocks.append(code[start + 2 : j - 1])
        i = j
    return blocks


def lint_user_module(text: str, allowed_imports: frozenset[str]) -> str | None:
    """Reject user witness modules that could steer elaboration.

    Returns `None` if `text` passes, else a reason string. This is defense in
    depth: elaboration is sandboxed and the verdict comes from the kernel
    replay in the out-of-process inspector.
    """
    code, reason = _strip_lean_comments(text)
    if code is None:
        return reason
    for ch in code:
        if ch in LEAN_WHITESPACE:
            continue
        if ch.isspace() or unicodedata.category(ch) in ("Cc", "Cf", "Zl", "Zp"):
            return f"unsupported character U+{ord(ch):04X}"
    try:
        header = parse_lean_header(code)
    except ValueError as exc:
        return str(exc)
    if not header.has_prelude:
        return "user module must start with `prelude`"
    for mods, mod in header.imports:
        if "meta" in mods:
            return f"`meta import` of `{mod}` is not allowed in user modules"
        if "all" in mods or "private" in mods:
            return f"`import all`/`private import` of `{mod}` is not allowed"
        allowed = (
            mod in USER_IMPORT_EXACT
            or mod in allowed_imports
            or any(
                mod == p or mod.startswith(p + ".")
                for p in USER_IMPORT_PREFIXES
            )
        )
        if not allowed:
            return f"import of `{mod}` is not allowed"
    body = code[header.body_start:]
    banned = BANNED_USER_KEYWORDS_RE.search(body)
    if banned:
        return f"`{banned.group(1)}` is not allowed in user modules"
    banned = BANNED_USER_IDENTS_RE.search(body)
    if banned:
        return f"`{banned.group(1)}` is not allowed in user modules"
    tactic_flag = BANNED_USER_TACTIC_FLAGS_RE.search(body)
    if tactic_flag:
        tok = tactic_flag.group(0).strip()
        return f"`{tok}` is not allowed in user modules"
    if BANNED_USER_HASH_COMMAND_RE.search(body):
        return "`#` commands are not allowed in user modules"
    blocks = _attribute_blocks(body)
    if blocks is None:
        return "unterminated attribute list"
    if any(BANNED_USER_ATTRIBUTE_RE.search(b) for b in blocks):
        return "metaprogramming attributes are not allowed in user modules"
    return None


def _copy_regular_tree(src: Path, dst: Path) -> None:
    """Copy a regular file/dir tree from `src` to `dst`, rejecting symlinks."""
    if src.is_symlink() or not src.is_dir():
        raise StageError(f"expected regular directory: {src}")
    dst.mkdir(parents=True, exist_ok=True)
    for root_str, dirs, files in os.walk(src, followlinks=False):
        root = Path(root_str)
        target_dir = dst / root.relative_to(src)
        target_dir.mkdir(parents=True, exist_ok=True)
        for d in dirs:
            if (root / d).is_symlink():
                raise StageError(f"symlink rejected in lean-lib: {root / d}")
        for fname in files:
            p = root / fname
            if p.is_symlink() or not p.is_file():
                raise StageError(f"non-regular file rejected in lean-lib: {p}")
            shutil.copy2(p, target_dir / fname)


def _module_file(base: Path, module: str, suffix: str) -> Path:
    parts = module.split(".")
    return base.joinpath(*parts[:-1]) / (parts[-1] + suffix)


def _lean_env(lean_bin: Path, lean_path: Path | None) -> dict[str, str]:
    """Allowlisted environment for Lean children.

    Built from scratch (never from `os.environ`), so CI credentials such as
    `ACTIONS_RUNTIME_TOKEN` and ambient `LEAN_*`/`LAKE_*`/`LD_*` variables never
    reach processes that elaborate user code.
    """
    bin_dir = lean_bin.parent
    env = {
        "PATH": f"{bin_dir}:/usr/bin:/bin",
        "HOME": "/tmp",
        "TMPDIR": "/tmp",
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
    }
    sysroot = bin_dir.parent
    if (sysroot / "lib" / "lean").is_dir():
        env["LEAN_SYSROOT"] = str(sysroot)
    if lean_path is not None:
        env["LEAN_PATH"] = str(lean_path)
    return env


@dataclass
class _LeanStage:
    """Sandboxed Lean invocations over one staging directory."""

    sandbox: SandboxRunner
    lean_bin: Path
    stage_dir: Path
    lean_memory_mb: int | None
    timeout: float
    _outputs: int = 0

    @property
    def lib_dir(self) -> Path:
        return self.stage_dir / "lib"

    @property
    def toolchain_root(self) -> Path:
        return self.lean_bin.parent.parent

    def _fresh_out_dir(self) -> Path:
        self._outputs += 1
        out = self.stage_dir / "out" / str(self._outputs)
        out.mkdir(parents=True)
        return out

    def run(
        self,
        args: Sequence[str],
        *,
        cwd: Path,
        ro: Sequence[Path],
        lean_path: Path | None,
        out_dir: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """Run Lean with `ro` (plus toolchain) read-only.

        Only `out_dir` (a fresh directory by default) is writable.
        """
        return self.sandbox.run(
            [str(self.lean_bin), *args],
            ro=(self.toolchain_root, *ro),
            rw=(out_dir or self._fresh_out_dir(),),
            cwd=cwd,
            env=_lean_env(self.lean_bin, lean_path),
            timeout=self.timeout,
        )

    def compile_classified(
        self,
        *,
        module: str,
        src: Path,
        root: Path,
        overwrite: bool,
    ) -> tuple[str | None, bool]:
        """Compile `src` into `lib_dir`, returning `(err, is_infrastructure)`.

        Only a clean exit-`1` typecheck/proof rejection with no crash,
        resource-limit, sandbox, import/name-resolution, syntax, or
        warning-as-error linter markers has `is_infrastructure=False`.
        """
        mem = ["-M", str(self.lean_memory_mb)] if self.lean_memory_mb else []
        out_dir = self._fresh_out_dir()
        olean = _module_file(out_dir, module, ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        proc = self.run(
            [
                *mem,
                "-DwarningAsError=true",
                "-R",
                str(root),
                "-o",
                str(olean),
                str(src),
            ],
            cwd=root,
            ro=(self.lib_dir, root),
            lean_path=self.lib_dir,
            out_dir=out_dir,
        )
        if proc.returncode != 0:
            combined_low = f"{proc.stderr}\n{proc.stdout}".lower()
            is_infra = (
                proc.returncode != 1
                or any(m in combined_low for m in LEAN_COMPILE_INFRA_MARKERS)
                or any(
                    m in combined_low for m in LEAN_COMPILE_NONSEMANTIC_MARKERS
                )
            )
            detail = (proc.stderr or proc.stdout).strip()[:400] or (
                f"exit {proc.returncode}"
            )
            return detail, is_infra
        if olean.is_symlink() or not olean.is_file():
            return f"no regular {olean.name} produced", True
        for suffix in LEAN_OUTPUT_SUFFIXES:
            produced = _module_file(out_dir, module, suffix)
            if not produced.exists() and not produced.is_symlink():
                continue
            if produced.is_symlink() or not produced.is_file():
                return f"non-regular output {produced.name}", True
            dest = _module_file(self.lib_dir, module, suffix)
            if dest.exists() and not overwrite:
                return f"refusing to overwrite staged {dest.name}", True
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(produced, dest)
        return None, False

    def compile(
        self,
        *,
        module: str,
        src: Path,
        root: Path,
        overwrite: bool,
    ) -> str | None:
        """Compile `src` (module `module` under `root`) into `lib_dir`."""
        err, _ = self.compile_classified(
            module=module, src=src, root=root, overwrite=overwrite
        )
        return err


def _source_imports(path: Path) -> list[str]:
    code, reason = _strip_lean_comments(
        path.read_text(encoding="utf-8"), allow_strings=True
    )
    if code is None:
        raise StageError(f"cannot parse {path}: {reason}")
    try:
        return [mod for _, mod in parse_lean_header(code).imports]
    except ValueError as exc:
        raise StageError(f"cannot parse header of {path}: {exc}") from exc


def _find_module_source(
    source_roots: Sequence[Path], module: str
) -> tuple[Path, Path] | None:
    for root in source_roots:
        src = _module_file(root, module, ".lean")
        if src.is_file() and not src.is_symlink():
            return root, src
    return None


def concrete_refute_build_plan(
    lib_dir: Path,
    source_roots: Sequence[Path],
    extra_modules: Sequence[str] = (),
) -> list[tuple[str, Path, Path]]:
    """Return `(module, root, source)` to compile, dependencies first.

    `cargo-anneal verify --export-lean-lib` prunes `Anneal.*` (and other
    bundled) modules the target's proof never imported, so any dependency of
    `Anneal.Diag.ConcreteRefute` or witness-imported `Anneal.*` / `Trusted.*`
    module missing from the export is compiled from the checked-in sources.
    `ConcreteRefute` itself is always compiled.
    """
    plan: list[tuple[str, Path, Path]] = []
    state: dict[str, str] = {}

    def visit(module: str) -> None:
        if state.get(module) == "done":
            return
        if state.get(module) == "active":
            raise StageError(f"import cycle through {module}")
        if module != CONCRETE_REFUTE_MODULE and _module_file(
            lib_dir, module, ".olean"
        ).is_file():
            state[module] = "done"
            return
        found = _find_module_source(source_roots, module)
        if found is None:
            if module.split(".")[0] in TOOLCHAIN_MODULE_ROOTS:
                state[module] = "done"
                return
            raise StageError(
                f"{module} is neither in the exported lean-lib nor under "
                f"{', '.join(str(r) for r in source_roots)}"
            )
        state[module] = "active"
        root, src = found
        for dep in _source_imports(src):
            visit(dep)
        state[module] = "done"
        plan.append((module, root, src))

    visit(CONCRETE_REFUTE_MODULE)
    for extra in extra_modules:
        visit(extra)
    return plan


def _build_concrete_refute_stage(
    *,
    stage: _LeanStage,
    artifacts_dir: Path,
    source_roots: Sequence[Path],
    forbidden_modules: tuple[str, ...],
    extra_modules: Sequence[str] = (),
) -> bool:
    """Populate `stage.lib_dir` with `lean-lib`, `ConcreteRefute`, and deps.

    Returns whether the generated `Expected.lean` uses the module system.
    Fails if any of `forbidden_modules` (the request's proof modules) left
    compiled artifacts behind, so Pole B cannot reuse a shipped proof.
    """
    lean_lib_src = artifacts_dir / "lean-lib"
    if not lean_lib_src.is_dir():
        raise StageError(f"missing exported lean-lib: {lean_lib_src}")
    for mod in forbidden_modules:
        for suffix in COMPILED_PROOF_SUFFIXES:
            leaked = _module_file(lean_lib_src, mod, suffix)
            if leaked.exists():
                raise StageError(
                    f"unexpected {leaked.name} in failed verification artifacts"
                )
    if not (lean_lib_src / "Expected.olean").is_file():
        raise StageError(f"missing exported Expected.olean in {lean_lib_src}")
    expected_src = artifacts_dir / "generated/Expected.lean"
    if expected_src.is_symlink() or not expected_src.is_file():
        raise StageError(f"missing generated/Expected.lean: {expected_src}")
    is_module_mode = _source_starts_with_module_keyword(
        expected_src.read_text(encoding="utf-8")
    )

    _copy_regular_tree(lean_lib_src, stage.lib_dir)
    for module, root, src in concrete_refute_build_plan(
        stage.lib_dir, source_roots, extra_modules=extra_modules
    ):
        err = stage.compile(module=module, src=src, root=root, overwrite=True)
        if err is not None:
            raise StageError(f"failed to compile {module}: {err}")
    return is_module_mode


def _run_axiom_inspector(
    *,
    stage: _LeanStage,
    module_name: str,
    decl: str,
    inspector_spec: tuple[str, ...],
) -> tuple[tuple[str, ...] | None, str]:
    """Check `decl`'s type, axioms, and kernel replay in a separate process.

    Returns `(axioms, "")` on success or `(None, reason)` on failure.
    """
    insp_dir = stage.stage_dir / "inspect"
    insp_dir.mkdir(exist_ok=True)
    script = insp_dir / "AuditSpecInspect.lean"
    script.write_text(AXIOM_INSPECTOR_SRC, encoding="utf-8")
    nonce = secrets.token_hex(16)
    mem = ["-M", str(stage.lean_memory_mb)] if stage.lean_memory_mb else []
    # The inspector sets its own search path (toolchain first).
    proc = stage.run(
        [
            *mem,
            "--run",
            str(script),
            str(stage.lib_dir),
            module_name,
            decl,
            nonce,
            *inspector_spec,
        ],
        cwd=insp_dir,
        ro=(stage.lib_dir, insp_dir),
        lean_path=None,
    )
    if proc.returncode != 0:
        err = (proc.stderr or proc.stdout).strip()[:400]
        return None, f"axiom inspector rejected {decl}: {err}"
    axioms = parse_inspector_output(proc.stdout, nonce)
    if axioms is None:
        return None, f"malformed axiom inspector output for {decl}"
    return axioms, ""


def _render_nonvacuity_claim_module(
    *,
    is_module_mode: bool,
    spec_mod: str,
    spec_decl: str,
    is_v2: bool,
) -> str:
    """Render `AuditSpecNvClaim.lean` strictly over `Init` + `Trusted.*`."""
    imp = "public import" if is_module_mode else "import"
    imports = "".join(
        f"{imp} {mod}\n"
        for mod in (
            "Trusted.MirAst",
            "Trusted.MirModel",
            "Trusted.MirSemantics",
            "Captured",
            spec_mod,
        )
    )
    if is_v2:
        witness_quant = (
            "    ∃ (q : _root_.Trusted.MirSemantics.Query),\n"
            "      _root_.Trusted.MirSemantics.ValidEntryArgsV2 body q ∧\n"
            "      (body.isUnsafe = _root_.Bool.true →\n"
            f"        (_root_.{spec_decl}).safety body.identity q)\n"
        )
    else:
        witness_quant = (
            "    ∃ (args : _root_.List _root_.Trusted.MirSemantics.Val),\n"
            "      _root_.Trusted.MirSemantics.ValidEntryArgs body args ∧\n"
            "      (body.isUnsafe = _root_.Bool.true →\n"
            f"        (_root_.{spec_decl}).safety body.identity args)\n"
        )
    expose = "@[expose] " if is_module_mode else ""
    return (
        ("module\n" if is_module_mode else "")
        + "prelude\n"
        + imports
        + ("\npublic section\n" if is_module_mode else "\n")
        + "namespace AuditSpecNvClaim\n"
        + f"{expose}noncomputable def claim : Prop :=\n"
        + "  ∀ (defId : _root_.Trusted.MirAst.DefId)\n"
        + "    (body : _root_.Trusted.MirAst.Body),\n"
        + "    _root_.Trusted.MirSemantics.getElem?\n"
        + "      _root_.Captured.program.bodies defId ="
        + " _root_.Option.some body →\n"
        + witness_quant
        + "end AuditSpecNvClaim\n"
        + ("end\n" if is_module_mode else "")
    )


def run_lean_verification_module(
    *,
    artifacts_dir: Path,
    source_roots: Sequence[Path],
    lean_bin: Path,
    sandbox: SandboxRunner,
    user_module_file: Path,
    user_module_name: str,
    user_decl: str,
    expected_claim_type: str,
    inspector_spec: tuple[str, ...],
    allowed_user_imports: frozenset[str] = frozenset(),
    extra_verify_imports: Sequence[str] = (),
    check_module_name: str,
    lean_memory_mb: int | None,
    timeout: float,
    forbidden_modules: tuple[str, ...] = (),
    claim_module_name: str | None = None,
    claim_module_renderer: Any = None,
    verify_proof_expr: str | None = None,
) -> LeanRefuteCheck:
    """Compile and kernel-verify a Lean witness/refutation module.

    `inspector_spec` is the out-of-process inspector's expected-type mode and
    `constant@module` origin arguments for `expected_claim_type`.
    """
    if user_module_file.is_symlink() or not user_module_file.is_file():
        raise RuntimeError(f"Lean check file must be regular: {user_module_file}")
    if not is_lean_ident(user_decl):
        raise RuntimeError(f"invalid Lean declaration name: {user_decl!r}")
    user_text = user_module_file.read_text(encoding="utf-8")
    lint_err = lint_user_module(user_text, allowed_user_imports)
    if lint_err is not None:
        return _fail_check(
            f"{user_module_name} rejected by lint: {lint_err}",
            infrastructure=True,
        )
    stripped_user, _ = _strip_lean_comments(user_text)
    assert stripped_user is not None
    user_imports = tuple(
        dict.fromkeys(mod for _, mod in parse_lean_header(stripped_user).imports)
    )
    extra_stage_modules = tuple(
        mod
        for mod in user_imports
        if mod not in USER_IMPORT_EXACT and mod not in allowed_user_imports
    )
    with tempfile.TemporaryDirectory(prefix="anneal-audit-spec-") as tmp:
        stage = _LeanStage(
            sandbox=sandbox,
            lean_bin=lean_bin,
            stage_dir=Path(tmp),
            lean_memory_mb=lean_memory_mb,
            timeout=timeout,
        )
        try:
            is_module_mode = _build_concrete_refute_stage(
                stage=stage,
                artifacts_dir=artifacts_dir,
                source_roots=source_roots,
                forbidden_modules=forbidden_modules,
                extra_modules=extra_stage_modules,
            )
            for imp_mod in user_imports:
                if not _module_file(stage.lib_dir, imp_mod, ".olean").is_file():
                    raise StageError(
                        f"missing staged {imp_mod}.olean for {user_module_name}"
                    )
        except (StageError, OSError, subprocess.TimeoutExpired) as exc:
            return _fail_check(
                f"cannot stage Lean check: {exc}", infrastructure=True
            )
        # Lean rejects importing a non-`module` file from a `module` and
        # vice versa for `public import`; report that before elaborating.
        if _source_starts_with_module_keyword(user_text) != is_module_mode:
            want = "start with `module`" if is_module_mode else "not use `module`"
            return _fail_check(
                f"{user_module_name} must {want} to match generated Expected.lean",
                infrastructure=True,
            )

        src_dir = stage.stage_dir / "src"
        src_dir.mkdir()
        if claim_module_name is not None:
            claim_src = src_dir / f"{claim_module_name}.lean"
            claim_src.write_text(
                claim_module_renderer(is_module_mode), encoding="utf-8"
            )
            try:
                c_err, _ = stage.compile_classified(
                    module=claim_module_name,
                    src=claim_src,
                    root=src_dir,
                    overwrite=False,
                )
            except (OSError, subprocess.TimeoutExpired) as exc:
                c_err = f"timed out ({exc})" if isinstance(
                    exc, subprocess.TimeoutExpired
                ) else str(exc)
            if c_err is not None:
                return _fail_check(
                    f"cannot compile {claim_module_name}: {c_err}",
                    infrastructure=True,
                )

        user_src = src_dir / f"{user_module_name}.lean"
        user_src.write_text(user_text, encoding="utf-8")
        try:
            err, is_infra = stage.compile_classified(
                module=user_module_name, src=user_src, root=src_dir, overwrite=False
            )
        except subprocess.TimeoutExpired:
            err, is_infra = "timed out", True
        except OSError as exc:
            err, is_infra = str(exc), True
        if err is not None:
            return _fail_check(
                f"{user_module_name} elaboration failed: {err}",
                infrastructure=is_infra,
            )

        imp = "public import" if is_module_mode else "import"
        verify_mods = ["Expected", *extra_verify_imports]
        if claim_module_name is not None:
            verify_mods.append(claim_module_name)
        verify_mods.append(user_module_name)
        imports = "".join(f"{imp} {mod}\n" for mod in verify_mods)
        proof_term = verify_proof_expr or f"_root_.{user_decl}"
        verify_src_text = (
            ("module\n" if is_module_mode else "")
            + "prelude\n"
            + imports
            + ("\npublic section\n" if is_module_mode else "\n")
            + f"theorem __auditSpecCheck : {expected_claim_type} :=\n"
            + f"  {proof_term}\n"
            + ("end\n" if is_module_mode else "")
        )
        verify_src = src_dir / f"{check_module_name}.lean"
        verify_src.write_text(verify_src_text, encoding="utf-8")
        try:
            err, is_infra = stage.compile_classified(
                module=check_module_name,
                src=verify_src,
                root=src_dir,
                overwrite=False,
            )
        except subprocess.TimeoutExpired:
            err, is_infra = "timed out", True
        except OSError as exc:
            err, is_infra = str(exc), True
        if err is not None:
            return _fail_check(
                f"type check failed on {user_decl}: {err}",
                infrastructure=is_infra,
            )

        try:
            axioms, inspect_err = _run_axiom_inspector(
                stage=stage,
                module_name=check_module_name,
                decl="__auditSpecCheck",
                inspector_spec=inspector_spec,
            )
        except subprocess.TimeoutExpired:
            axioms, inspect_err = None, "axiom inspector timed out"
        except OSError as exc:
            axioms, inspect_err = None, f"axiom inspector failed: {exc}"
        if axioms is None:
            return _fail_check(inspect_err, infrastructure=True)
        bad_axioms = [ax for ax in axioms if ax not in ALLOWED_FOUNDATION_AXIOMS]
        if bad_axioms:
            return LeanRefuteCheck(
                passed=False,
                axioms=axioms,
                kernel_replayed=True,
                infrastructure_error=True,
                detail=f"disallowed axiom(s) in {user_decl}: {bad_axioms}",
            )
        return LeanRefuteCheck(
            passed=True,
            axioms=axioms,
            kernel_replayed=True,
            infrastructure_error=False,
            detail=f"kernel-replayed {user_decl}",
        )


def _baseline_failures(
    proc: Any, receipt: dict[str, Any], scope_kind: Any
) -> list[str]:
    expected = CLEAN_VERIFIED_STATUS.get(scope_kind)
    if expected is None:
        return [f"unknown scope.kind {scope_kind!r}"]
    return anneal_ci_lib.validate_receipt_v3_envelope(
        receipt, returncode=proc.returncode, expected_status=expected
    )


def _check_artifacts_dir(case_art: Path, inputs: Sequence[Path]) -> None:
    """Refuse artifact directories that hold inputs or unrelated files.

    The case directory is recursively replaced on each run, so it must not
    equal or contain any request, source, or witness path, and an existing
    non-empty directory is only replaced if an earlier run marked it.
    """
    case_real = Path(os.path.realpath(case_art))
    for raw in inputs:
        inp = Path(os.path.realpath(raw))
        if inp == case_real or inp.is_relative_to(case_real):
            raise ValueError(
                f"artifacts directory {case_art} would overwrite input {raw}"
            )
    if (
        case_art.is_dir()
        and any(case_art.iterdir())
        and not (case_art / ARTIFACT_MARKER).is_file()
    ):
        raise ValueError(
            f"refusing to replace existing non-audit directory {case_art}"
        )


def default_source_roots(
    theory_root: Path, trusted_lean_root: Path | None = None
) -> tuple[Path, ...]:
    """Return `(theory_root, trusted_lean_root?)` for staging Lean deps."""
    if trusted_lean_root is None:
        cand = theory_root.parent / "trusted" / "lean"
        trusted_lean_root = cand if cand.is_dir() else None
    roots = [theory_root.resolve()]
    if trusted_lean_root is not None:
        roots.append(trusted_lean_root.resolve())
    return tuple(roots)


def audit_case(
    *,
    name: str,
    baseline_request: Path | None,
    mutant_request: Path,
    pole_b_path: Path,
    pole_b_decl: str = "PoleBRefute.refute",
    nonvacuity_path: Path | None = None,
    nonvacuity_decl: str = "NonVacuity.witness",
    cli: Path,
    capture: Path,
    sysroot: Path,
    lean: Path,
    theory_root: Path,
    artifacts_root: Path,
    trusted_lean_root: Path | None = None,
    sandbox: SandboxRunner | None = None,
    lean_memory_mb: int | None = None,
    timeout: float = 600.0,
) -> CaseResult:
    """Execute a complete dual-polar audit case and return structured result.

    Raises `SandboxUnavailable` when `sandbox` is omitted and no `bwrap`
    sandbox works: user witnesses are never elaborated unsandboxed.
    """
    if not is_valid_case_name(name):
        raise ValueError(f"invalid case name: {name!r}")
    for label, decl in (
        ("pole_b_decl", pole_b_decl),
        ("nonvacuity_decl", nonvacuity_decl),
    ):
        if not is_lean_ident(decl):
            raise ValueError(f"invalid {label}: {decl!r}")
    art_root = artifacts_root.resolve()
    case_art = artifacts_root / name
    if (
        case_art.resolve() == art_root
        or not case_art.resolve().is_relative_to(art_root)
    ):
        raise ValueError(f"case directory escapes artifacts root: {name!r}")

    def result(
        classification: str,
        detail: str,
        *,
        spec_locked: bool = True,
        baseline_verified: bool | None = None,
        pre_non_vacuous: bool | None = None,
        pole_a: dict[str, Any] | None = None,
        pole_b: dict[str, Any] | None = None,
        nonvacuity: dict[str, Any] | None = None,
        pole_a_clean: bool = False,
        pole_b_refuted: bool = False,
    ) -> CaseResult:
        return CaseResult(
            name=name,
            baseline_verified=baseline_verified,
            spec_locked=spec_locked,
            pre_non_vacuous=pre_non_vacuous,
            pole_a_clean_reject=pole_a_clean,
            pole_b_refuted=pole_b_refuted,
            dual_polar_adequate=pole_a_clean and pole_b_refuted,
            classification=classification,
            detail=detail,
            pole_a=pole_a or {},
            pole_b=pole_b or {},
            nonvacuity=nonvacuity,
        )

    if nonvacuity_path is None:
        return result(
            "nonvacuity_missing",
            "a non-vacuity witness is required for an adequacy verdict",
            spec_locked=False,
        )
    pair, lock_msg = lock_requests(baseline_request, mutant_request)
    if pair is None:
        return result("spec_unlocked", lock_msg, spec_locked=False)
    assert baseline_request is not None
    base_locked, locked = pair
    _check_artifacts_dir(
        case_art,
        (
            *base_locked.input_dirs,
            *locked.input_dirs,
            pole_b_path,
            nonvacuity_path,
        ),
    )
    if sandbox is None:
        sandbox = LeanSandbox.probe()
    source_roots = default_source_roots(theory_root, trusted_lean_root)

    allowed_user_imports = frozenset(locked.modules("specification"))
    proof_modules = tuple(
        dict.fromkeys(("Proof", locked.theorem_module, *locked.modules("proof")))
    )

    base_art = case_art / "baseline"
    mut_art = case_art / "mutant"
    if (case_art / ARTIFACT_MARKER).is_file():
        shutil.rmtree(case_art)
    case_art.mkdir(parents=True, exist_ok=True)
    (case_art / ARTIFACT_MARKER).write_text("", encoding="utf-8")

    verify_extra = ["--export-lean-lib"]
    if lean_memory_mb is not None:
        verify_extra.extend(["--lean-memory-mb", str(max(4096, lean_memory_mb))])

    try:
        proc_b, receipt_b = anneal_ci_lib.run_cargo_anneal_verify(
            cli=cli,
            request_path=baseline_request,
            cwd=baseline_request.parent,
            capture=capture,
            sysroot=sysroot,
            lean=lean,
            artifacts_dir=base_art,
            extra_flags=verify_extra,
            timeout=timeout,
            log_prefix=case_art / "baseline",
            label=f"{name}-baseline",
        )
    except (
        RuntimeError,
        OSError,
        subprocess.TimeoutExpired,
        UnicodeDecodeError,
    ) as exc:
        return result("baseline_failed", str(exc)[:400], baseline_verified=False)
    baseline_errs = _baseline_failures(proc_b, receipt_b, locked.scope_kind)
    if baseline_errs:
        return result(
            "baseline_failed",
            f"baseline verification failed: {', '.join(baseline_errs)}",
            baseline_verified=False,
        )

    pre_non_vacuous: bool | None = None
    nonvac_info: dict[str, Any] | None = None
    spec_decl = locked.specification
    spec_mod = locked.specification_module
    base_expected_path = base_art / "generated/Expected.lean"
    base_expected_text = (
        base_expected_path.read_text(encoding="utf-8")
        if base_expected_path.is_file()
        else ""
    )
    is_v2 = (
        "UnitTheoremV2" in base_expected_text
        or "CrateTheoremV2" in base_expected_text
    )
    nv_bridge = (
        "specsPreInhabitedV2_forall_getElem?"
        if is_v2
        else "specsPreInhabited_forall_getElem?"
    )
    nv_check = run_lean_verification_module(
        artifacts_dir=base_art,
        source_roots=source_roots,
        lean_bin=lean,
        sandbox=sandbox,
        user_module_file=nonvacuity_path,
        user_module_name="NonVacuity",
        user_decl=nonvacuity_decl,
        expected_claim_type="_root_.AuditSpecNvClaim.claim",
        inspector_spec=(
            "nv_claim",
            "AuditSpecNvClaim.claim@AuditSpecNvClaim",
            f"{spec_decl}@{spec_mod}",
            "Captured.program@Captured",
        ),
        allowed_user_imports=allowed_user_imports,
        extra_verify_imports=("Captured", spec_mod, CONCRETE_REFUTE_MODULE),
        check_module_name="NonVacuityVerify",
        lean_memory_mb=lean_memory_mb,
        timeout=timeout,
        claim_module_name="AuditSpecNvClaim",
        claim_module_renderer=lambda mod_mode: _render_nonvacuity_claim_module(
            is_module_mode=mod_mode,
            spec_mod=spec_mod,
            spec_decl=spec_decl,
            is_v2=is_v2,
        ),
        verify_proof_expr=(
            f"_root_.Anneal.Diag.ConcreteRefute.{nv_bridge} "
            f"_root_.{nonvacuity_decl}"
        ),
    )
    pre_non_vacuous = nv_check.passed
    nonvac_info = asdict(nv_check)
    if not nv_check.passed:
        return result(
            "nonvacuity_error" if nv_check.infrastructure_error else "pre_vacuous",
            nv_check.detail,
            baseline_verified=True,
            pre_non_vacuous=None if nv_check.infrastructure_error else False,
            nonvacuity=nonvac_info,
        )

    cmd_m = anneal_ci_lib.build_cargo_anneal_verify_cmd(
        cli=cli,
        request_path=mutant_request,
        capture=capture,
        sysroot=sysroot,
        lean=lean,
        artifacts_dir=mut_art,
        extra_flags=verify_extra,
    )
    child_env = anneal_ci_lib.strip_actions_env(None, include_oidc=True)
    try:
        proc_m = subprocess.run(
            cmd_m,
            cwd=mutant_request.parent,
            env=child_env,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        out_raw = exc.stdout if isinstance(exc.stdout, bytes) else (
            (exc.stdout or "").encode("utf-8", errors="replace")
        )
        err_raw = exc.stderr if isinstance(exc.stderr, bytes) else (
            (exc.stderr or "").encode("utf-8", errors="replace")
        )
        (case_art / "mutant.stdout").write_text(
            out_raw.decode("utf-8", errors="replace"), encoding="utf-8"
        )
        (case_art / "mutant.stderr").write_text(
            err_raw.decode("utf-8", errors="replace"), encoding="utf-8"
        )
        pole_a = _pole_a(
            False,
            "resource_limit",
            {},
            f"Pole A verification timed out after {timeout}s",
            -1,
        )
        return result(
            pole_a.classification,
            pole_a.detail,
            baseline_verified=True,
            pre_non_vacuous=pre_non_vacuous,
            pole_a=asdict(pole_a),
            nonvacuity=nonvac_info,
        )
    except OSError as exc:
        pole_a = _pole_a(
            False,
            "unexpected_failure",
            {},
            f"Pole A execution failed: {exc}"[:400],
            -1,
        )
        return result(
            pole_a.classification,
            pole_a.detail,
            baseline_verified=True,
            pre_non_vacuous=pre_non_vacuous,
            pole_a=asdict(pole_a),
            nonvacuity=nonvac_info,
        )
    (case_art / "mutant.stdout").write_text(
        proc_m.stdout.decode("utf-8", errors="replace"), encoding="utf-8"
    )
    (case_art / "mutant.stderr").write_text(
        proc_m.stderr.decode("utf-8", errors="replace"), encoding="utf-8"
    )
    try:
        m_stdout = proc_m.stdout.decode("utf-8")
        m_stderr = proc_m.stderr.decode("utf-8")
    except UnicodeDecodeError as exc:
        pole_a = _pole_a(
            False,
            "malformed_output",
            {},
            f"Pole A invalid UTF-8 output (exit {proc_m.returncode}): {exc}",
            proc_m.returncode,
        )
        return result(
            pole_a.classification,
            pole_a.detail,
            baseline_verified=True,
            pre_non_vacuous=pre_non_vacuous,
            pole_a=asdict(pole_a),
            nonvacuity=nonvac_info,
        )
    pole_a = classify_pole_a_result(proc_m.returncode, m_stdout, m_stderr)
    pole_a_dict = asdict(pole_a)
    if not pole_a.clean_reject:
        return result(
            pole_a.classification,
            pole_a.detail,
            baseline_verified=True,
            pre_non_vacuous=pre_non_vacuous,
            pole_a=pole_a_dict,
            nonvacuity=nonvac_info,
        )

    pole_b = run_lean_verification_module(
        artifacts_dir=mut_art,
        source_roots=source_roots,
        lean_bin=lean,
        sandbox=sandbox,
        user_module_file=pole_b_path,
        user_module_name="PoleBRefute",
        user_decl=pole_b_decl,
        expected_claim_type="¬ _root_.Expected.claim",
        inspector_spec=("not_claim", "Expected.claim@Expected"),
        allowed_user_imports=allowed_user_imports,
        check_module_name="PoleBVerify",
        lean_memory_mb=lean_memory_mb,
        timeout=timeout,
        forbidden_modules=proof_modules,
    )
    pole_b_dict = asdict(pole_b)
    if not pole_b.passed:
        return result(
            "pole_b_error" if pole_b.infrastructure_error else "vacuous_spec_false_kill",
            pole_b.detail,
            baseline_verified=True,
            pre_non_vacuous=pre_non_vacuous,
            pole_a=pole_a_dict,
            pole_b=pole_b_dict,
            nonvacuity=nonvac_info,
            pole_a_clean=True,
        )
    return result(
        "adequate",
        "clean Pole A rejection and kernel-replayed Pole B refutation",
        baseline_verified=True,
        pre_non_vacuous=pre_non_vacuous,
        pole_a=pole_a_dict,
        pole_b=pole_b_dict,
        nonvacuity=nonvac_info,
        pole_a_clean=True,
        pole_b_refuted=True,
    )


def matches_expectation(res: CaseResult, expect_adequate: bool) -> bool:
    """Whether `res` is the verdict a suite case expects.

    A negative expectation is only met by a semantic inadequacy verdict, so a
    negative control cannot pass because its check never ran.
    """
    if expect_adequate:
        return res.dual_polar_adequate
    return res.classification in SEMANTIC_INADEQUATE


def _abs_path(p: Path) -> Path:
    """Absolute path without resolving symlinks (they are checked later)."""
    return Path(os.path.abspath(p))


def _resolve_relative(base: Path, raw: str | None) -> Path | None:
    if raw is None:
        return None
    p = Path(raw)
    return _abs_path(p if p.is_absolute() else (base / p))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run 0-TCB dual-polar specification adequacy checks."
    )
    parser.add_argument("--name", default="case", help="case name for single run")
    parser.add_argument("--baseline-request", type=Path, help="baseline request.json")
    parser.add_argument("--mutant-request", type=Path, help="mutant request.json")
    parser.add_argument("--pole-b", type=Path, help="Pole B refutation Lean file")
    parser.add_argument(
        "--pole-b-decl",
        default="PoleBRefute.refute",
        help="Lean refutation declaration proving `¬ Expected.claim`",
    )
    parser.add_argument("--nonvacuity", type=Path, help="optional witness Lean file")
    parser.add_argument(
        "--nonvacuity-decl",
        default="NonVacuity.witness",
        help="Lean declaration witnessing precondition non-vacuity",
    )
    parser.add_argument("--suite", type=Path, help="JSON suite manifest")
    parser.add_argument("--cli", type=Path, help="path to cargo-anneal binary")
    parser.add_argument("--capture", type=Path, help="path to anneal-rustc-capture")
    parser.add_argument("--sysroot", type=Path, help="path to Rust sysroot")
    parser.add_argument("--lean", type=Path, help="path to pinned Lean binary")
    parser.add_argument("--theory-root", type=Path, help="Anneal theory/ directory")
    parser.add_argument(
        "--trusted-lean-root",
        type=Path,
        help="Trusted Lean sources (default: <theory-root>/../trusted/lean)",
    )
    parser.add_argument("--artifacts-dir", type=Path, help="retained audit artifacts dir")
    parser.add_argument("--lean-memory-mb", type=int, help="Lean `-M` limit in MiB")
    parser.add_argument("--timeout", type=float, default=600.0, help="per-step timeout")
    parser.add_argument(
        "--format",
        choices=("human", "json"),
        default="human",
        help="output format",
    )
    parser.add_argument("--json-out", type=Path, help="write JSON report to path")
    args = parser.parse_args(argv)

    anneal_root = anneal_ci_lib.default_anneal_root(__file__)
    theory_root = (args.theory_root or (anneal_root / "theory")).resolve()
    tools = anneal_ci_lib.resolve_cli_tools(
        anneal_root,
        args,
        names=("cli", "capture", "sysroot", "lean"),
    )
    for key in ("cli", "capture", "sysroot", "lean"):
        if tools[key] is None:
            print(f"audit_spec: error: could not resolve --{key}", file=sys.stderr)
            return 2
        tools[key] = tools[key].resolve()

    cases_spec: list[dict[str, Any]] = []
    if args.suite is not None:
        try:
            suite_data = anneal_ci_lib.load_strict_json_object(
                args.suite, "suite manifest"
            )
        except RuntimeError as exc:
            print(f"audit_spec: error: {exc}", file=sys.stderr)
            return 2
        suite_base = _abs_path(args.suite).parent
        raw_cases = suite_data.get("cases")
        if not isinstance(raw_cases, list) or not raw_cases:
            print("audit_spec: error: suite must have non-empty cases", file=sys.stderr)
            return 2
        for entry in raw_cases:
            if not isinstance(entry, dict):
                print("audit_spec: error: malformed suite case", file=sys.stderr)
                return 2
            cases_spec.append(
                {
                    "name": str(entry["name"]),
                    "baseline_request": _resolve_relative(
                        suite_base, entry.get("baseline_request")
                    ),
                    "mutant_request": _resolve_relative(
                        suite_base, entry["mutant_request"]
                    ),
                    "pole_b": _resolve_relative(suite_base, entry["pole_b"]),
                    "pole_b_decl": entry.get("pole_b_decl", "PoleBRefute.refute"),
                    "nonvacuity": _resolve_relative(
                        suite_base, entry.get("nonvacuity")
                    ),
                    "nonvacuity_decl": entry.get(
                        "nonvacuity_decl", "NonVacuity.witness"
                    ),
                    "expect_adequate": bool(entry.get("expect_adequate", True)),
                }
            )
    else:
        if (
            args.mutant_request is None
            or args.pole_b is None
            or args.baseline_request is None
            or args.nonvacuity is None
        ):
            print(
                "audit_spec: error: pass --suite or --baseline-request, "
                "--mutant-request, --pole-b, and --nonvacuity",
                file=sys.stderr,
            )
            return 2
        cases_spec.append(
            {
                "name": args.name,
                "baseline_request": _abs_path(args.baseline_request),
                "mutant_request": _abs_path(args.mutant_request),
                "pole_b": _abs_path(args.pole_b),
                "pole_b_decl": args.pole_b_decl,
                "nonvacuity": (
                    _abs_path(args.nonvacuity)
                    if args.nonvacuity is not None
                    else None
                ),
                "nonvacuity_decl": args.nonvacuity_decl,
                "expect_adequate": True,
            }
        )

    for item in cases_spec:
        if not is_valid_case_name(item["name"]):
            print(
                f"audit_spec: error: invalid case name {item['name']!r}",
                file=sys.stderr,
            )
            return 2
        if item["baseline_request"] is None:
            print(
                f"audit_spec: error: case {item['name']!r} needs a "
                "baseline_request",
                file=sys.stderr,
            )
            return 2
        for key in ("pole_b_decl", "nonvacuity_decl"):
            if not is_lean_ident(item[key]):
                print(
                    f"audit_spec: error: invalid {key} {item[key]!r}",
                    file=sys.stderr,
                )
                return 2

    try:
        sandbox = LeanSandbox.probe()
    except SandboxUnavailable as exc:
        print(f"audit_spec: error: {exc}", file=sys.stderr)
        return 2

    results: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="audit-spec-art-") as tmp_art:
        art_root = (
            args.artifacts_dir.resolve()
            if args.artifacts_dir is not None
            else Path(tmp_art)
        )
        art_root.mkdir(parents=True, exist_ok=True)
        for item in cases_spec:
            res = audit_case(
                name=item["name"],
                baseline_request=item["baseline_request"],
                mutant_request=item["mutant_request"],
                pole_b_path=item["pole_b"],
                pole_b_decl=item["pole_b_decl"],
                nonvacuity_path=item["nonvacuity"],
                nonvacuity_decl=item["nonvacuity_decl"],
                cli=tools["cli"],
                capture=tools["capture"],
                sysroot=tools["sysroot"],
                lean=tools["lean"],
                theory_root=theory_root,
                trusted_lean_root=args.trusted_lean_root,
                sandbox=sandbox,
                artifacts_root=art_root,
                lean_memory_mb=args.lean_memory_mb,
                timeout=args.timeout,
            )
            row = asdict(res)
            row["expect_adequate"] = item["expect_adequate"]
            row["matched_expectation"] = matches_expectation(
                res, item["expect_adequate"]
            )
            results.append(row)

    all_matched = all(r["matched_expectation"] for r in results)
    report = {
        "schema_version": SCHEMA_VERSION,
        "all_matched": all_matched,
        "cases": results,
    }
    if args.json_out is not None:
        anneal_ci_lib.atomic_write_text(
            args.json_out,
            json.dumps(report, indent=2, sort_keys=True) + "\n",
        )
    if args.format == "json":
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for r in results:
            print(
                f"{r['name']}: adequate={r['dual_polar_adequate']} "
                f"(expected={r['expect_adequate']}) "
                f"pole_a={r['pole_a_clean_reject']} "
                f"pole_b={r['pole_b_refuted']} "
                f"[{r['classification']}] {r['detail']}"
            )
    return 0 if all_matched else 1


if __name__ == "__main__":
    raise SystemExit(main())
