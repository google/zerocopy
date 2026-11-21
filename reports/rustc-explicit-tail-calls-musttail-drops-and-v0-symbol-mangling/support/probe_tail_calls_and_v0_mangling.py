#!/usr/bin/env python3
"""Empirical probe: explicit tail calls (`become`) and symbol mangling in rustc.

Every number in the emitted JSON is read back from a tool that this script ran
(rustc, the compiled binaries, Miri, llvm-nm). The script contains no table of
expected measurements: the `checks` section only states *relations* between
observed values (for example "the `become` build's stack span is 0 and the
ordinary-call build's is not"), and each check records the observed operands.

Requirements: a nightly `rustc` (the `explicit_tail_calls` feature gate and the
`-Z` flags used here are nightly-only). Optional: `miri` plus a Miri sysroot, and
`llvm-nm` from the `llvm-tools` component. Missing optional tools cause the
dependent experiments to be recorded as `"status": "skipped"` with the reason;
nothing is filled in on their behalf.

Usage:
    python3 probe_tail_calls_and_v0_mangling.py \
        --rustc /path/to/nightly/bin/rustc \
        [--miri /path/to/nightly/bin/miri --miri-sysroot /path/to/miri-sysroot] \
        [--llvm-nm /path/to/llvm-nm] [--steps 250000] [--miri-steps 250000] \
        [--max-depth 10] [--out probe_results.json]

All work happens in a temporary directory that is removed on exit. Sources are
copied there and passed to the tools by relative name, and absolute paths are
scrubbed from recorded text, so the output is host-independent apart from the
toolchain version strings.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUST_SRC = HERE / "rust"
EDITION = ["--edition", "2024"]
CRATE = "mangling_scale"


class Probe:
    def __init__(self, args: argparse.Namespace, tmp: Path) -> None:
        self.args = args
        self.tmp = tmp
        self.rustc = args.rustc
        self.sysroot = self._capture([self.rustc, "--print", "sysroot"]).strip()
        self.rustc_vv = self._capture([self.rustc, "-vV"]).strip()
        host = re.search(r"^host: (.+)$", self.rustc_vv, re.M)
        self.host = host.group(1) if host else ""
        self.miri = args.miri or self._sibling("miri")
        self.miri_sysroot = args.miri_sysroot or os.environ.get("MIRI_SYSROOT")
        self.llvm_nm = args.llvm_nm or self._llvm_tool("llvm-nm")
        self.scrub_table = [(str(tmp), "<tmp>"), (self.sysroot, "<sysroot>")]
        if self.miri_sysroot:
            self.scrub_table.append((str(Path(self.miri_sysroot).resolve()), "<miri-sysroot>"))
            self.scrub_table.append((self.miri_sysroot, "<miri-sysroot>"))
        self.scrub_table.append((str(Path.home()), "<home>"))
        self.checks: list[dict] = []
        for src in sorted(RUST_SRC.glob("*.rs")):
            shutil.copy(src, tmp / src.name)

    # ---- plumbing -------------------------------------------------------

    @staticmethod
    def _capture(cmd: list[str]) -> str:
        return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout

    def _sibling(self, name: str) -> str | None:
        cand = Path(self.rustc).resolve().parent / name
        return str(cand) if cand.exists() else shutil.which(name)

    def _llvm_tool(self, name: str) -> str | None:
        cand = Path(self.sysroot) / "lib" / "rustlib" / self.host / "bin" / name
        return str(cand) if cand.exists() else shutil.which(name)

    def scrub(self, text: str) -> str:
        for needle, repl in self.scrub_table:
            if needle:
                text = text.replace(needle, repl)
        # Thread ids in runtime abort messages differ on every run.
        text = re.sub(r"\(\d{3,}\) has overflowed", "(<tid>) has overflowed", text)
        return text

    def run(self, cmd: list[str], timeout: int = 900) -> dict:
        proc = subprocess.run(
            cmd, cwd=self.tmp, capture_output=True, text=True, timeout=timeout
        )
        shown = [self._show(c) for c in cmd]
        return {
            "cmd": " ".join(shown),
            "returncode": proc.returncode,
            "stdout": self.scrub(proc.stdout).strip().splitlines(),
            "stderr": [l for l in self.scrub(proc.stderr).strip().splitlines() if l.strip()],
        }

    def _show(self, part: str) -> str:
        if part == self.rustc:
            return "rustc"
        if self.miri and part == self.miri:
            return "miri"
        if self.llvm_nm and part == self.llvm_nm:
            return "llvm-nm"
        return self.scrub(part)

    def rustc_cmd(self, *flags: str) -> list[str]:
        return [self.rustc, *EDITION, *flags]

    def miri_cmd(self, *flags: str) -> list[str] | None:
        if not self.miri or not self.miri_sysroot:
            return None
        return [self.miri, "--sysroot", self.miri_sysroot, *EDITION, *flags]

    def check(self, name: str, passed: bool, **observed) -> None:
        self.checks.append({"name": name, "passed": bool(passed), "observed": observed})

    @staticmethod
    def kv(line: str) -> dict:
        return dict(tok.split("=", 1) for tok in line.split() if "=" in tok)

    def read(self, name: str) -> str:
        return (self.tmp / name).read_text()

    # ---- A. constant-stack mutual recursion ---------------------------

    def tail_recursion(self) -> dict:
        out: dict = {}
        steps = str(self.args.steps)
        builds = {
            "become_o0": ["-C", "opt-level=0"],
            "become_o3": ["-C", "opt-level=3"],
            "plain_o0": ["-C", "opt-level=0", "--cfg", "plain_call"],
            "plain_o3": ["-C", "opt-level=3", "--cfg", "plain_call"],
        }
        for name, flags in builds.items():
            out[f"build_{name}"] = self.run(
                self.rustc_cmd(*flags, "tail_recursion.rs", "-o", f"tr_{name}")
            )
        runs = {
            "become_o0_1MiB": ["./tr_become_o0", steps, "1048576"],
            "become_o0_64KiB": ["./tr_become_o0", steps, "65536"],
            "become_o3_1MiB": ["./tr_become_o3", steps, "1048576"],
            "plain_o0_2000_steps_1MiB": ["./tr_plain_o0", "2000", "1048576"],
            "plain_o0_1MiB": ["./tr_plain_o0", steps, "1048576"],
            "plain_o3_1MiB": ["./tr_plain_o3", steps, "1048576"],
        }
        for name, cmd in runs.items():
            out[f"run_{name}"] = self.run(cmd)

        def span(key: str) -> int | None:
            rec = out[f"run_{key}"]
            if rec["returncode"] != 0 or not rec["stdout"]:
                return None
            return int(self.kv(rec["stdout"][-1])["WITNESS_SPAN"])

        def result(key: str) -> int | None:
            rec = out[f"run_{key}"]
            if rec["returncode"] != 0 or not rec["stdout"]:
                return None
            return int(self.kv(rec["stdout"][-1])["RESULT"])

        self.check(
            "become_o0_completes_all_steps_in_64KiB_with_zero_stack_span",
            result("become_o0_64KiB") == self.args.steps and span("become_o0_64KiB") == 0,
            steps=self.args.steps,
            result=result("become_o0_64KiB"),
            stack_span_bytes=span("become_o0_64KiB"),
        )
        plain_span = span("plain_o0_2000_steps_1MiB")
        self.check(
            "plain_call_o0_stack_grows_with_step_count",
            plain_span is not None and plain_span > 0,
            steps=2000,
            stack_span_bytes=plain_span,
            bytes_per_step=(plain_span / 2000 if plain_span else None),
        )
        self.check(
            "plain_call_o0_overflows_1MiB_at_full_step_count",
            out["run_plain_o0_1MiB"]["returncode"] != 0,
            returncode=out["run_plain_o0_1MiB"]["returncode"],
            stderr=out["run_plain_o0_1MiB"]["stderr"],
        )
        out["note_plain_o3"] = (
            "The ordinary-call build at opt-level=3 is recorded but not asserted: "
            "whether LLVM turns an ordinary call in tail position into a jump is an "
            "optimization outcome, not a language guarantee."
        )

        # LLVM IR and assembly of the `become` build at opt-level=0.
        out["emit_llvm_ir_o0"] = self.run(
            self.rustc_cmd("-C", "opt-level=0", "--emit=llvm-ir", "tail_recursion.rs", "-o", "tr.ll")
        )
        ir = self.read("tr.ll")
        musttail = [l.strip() for l in ir.splitlines() if "musttail call" in l]
        out["llvm_ir_musttail_lines"] = musttail
        ret_after = 0
        lines = ir.splitlines()
        for i, l in enumerate(lines):
            if "musttail call" in l and i + 1 < len(lines) and lines[i + 1].strip().startswith("ret "):
                ret_after += 1
        out["llvm_ir_musttail_followed_by_ret"] = ret_after
        self.check(
            "two_musttail_calls_each_immediately_followed_by_ret",
            len(musttail) == 2 and ret_after == 2,
            musttail_lines=len(musttail),
            followed_by_ret=ret_after,
        )
        out["emit_asm_o0"] = self.run(
            self.rustc_cmd("-C", "opt-level=0", "--emit=asm", "tail_recursion.rs", "-o", "tr.s")
        )
        asm = self.read("tr.s")
        transfers = [
            re.sub(r"\s+", " ", l.strip())
            for l in asm.splitlines()
            if re.search(r"\b(jmp|call\w*|b|bl)\b.*(even_step|odd_step)", l)
        ]
        out["asm_transfers_to_even_or_odd_step"] = transfers
        out["target_arch"] = self.host.split("-")[0]

        # Miri: frame count instead of stack addresses.
        become = self.miri_cmd("tail_recursion.rs", "--", str(self.args.miri_steps), "1048576")
        if become is None:
            out["miri"] = {"status": "skipped", "reason": "miri or its sysroot not provided"}
        else:
            plain = self.miri_cmd("--cfg", "plain_call", "tail_recursion.rs", "--", "2000", "1048576")
            m_become = self.run(become, timeout=3600)
            m_plain = self.run(plain, timeout=3600)
            out["miri"] = {"status": "ran", "become": m_become, "plain_call_2000_steps": m_plain}
            b = self.kv(m_become["stdout"][-1]) if m_become["stdout"] else {}
            p = self.kv(m_plain["stdout"][-1]) if m_plain["stdout"] else {}
            self.check(
                "miri_become_frame_count_constant_over_all_steps",
                m_become["returncode"] == 0 and b.get("WITNESS_SPAN") == "0"
                and b.get("RESULT") == str(self.args.miri_steps),
                steps=self.args.miri_steps,
                result=b.get("RESULT"),
                frame_span=b.get("WITNESS_SPAN"),
            )
            self.check(
                "miri_plain_call_frame_count_grows_one_per_step",
                m_plain["returncode"] == 0 and p.get("WITNESS_SPAN") == "2000",
                steps=2000,
                frame_span=p.get("WITNESS_SPAN"),
            )
        return out

    # ---- B. destructor order ---------------------------------------------

    @staticmethod
    def _logs(lines: list[str]) -> dict:
        logs = {}
        for l in lines:
            parts = l.split()
            if parts and "DROP_ORDER_LOG=" in l:
                logs[parts[0]] = int(l.split("DROP_ORDER_LOG=")[1].split()[0])
        return logs

    @staticmethod
    def _normal_path(mir: str) -> list[str]:
        """Follow `return:` edges from bb0 and list drops, StorageDeads and the tail call."""
        blocks: dict[str, list[str]] = {}
        cur = None
        for line in mir.splitlines():
            m = re.match(r"\s*(bb\d+)(?: \(cleanup\))?: \{", line)
            if m:
                cur = m.group(1)
                blocks[cur] = []
            elif cur is not None:
                if line.strip() == "}":
                    cur = None
                else:
                    blocks[cur].append(line.strip())
        events: list[str] = []
        bb, seen = "bb0", set()
        while bb in blocks and bb not in seen:
            seen.add(bb)
            nxt = None
            for stmt in blocks[bb]:
                if stmt.startswith("drop("):
                    events.append(stmt.split(" -> ")[0])
                    m = re.search(r"return: (bb\d+)", stmt)
                    nxt = m.group(1) if m else None
                elif stmt.startswith("StorageDead(") and events:
                    events.append(stmt.rstrip(";"))
                elif stmt.startswith("tailcall "):
                    events.append(stmt.rstrip(";"))
                    return events
                elif stmt.startswith("goto -> "):
                    nxt = stmt.split("goto -> ")[1].rstrip(";")
                elif re.search(r"= .*\) -> \[return: (bb\d+)", stmt):
                    events.append(stmt.split(" -> ")[0])
                    nxt = re.search(r"return: (bb\d+)", stmt).group(1)
            bb = nxt
        return events

    def drop_order(self) -> dict:
        out: dict = {}
        out["build_o0"] = self.run(self.rustc_cmd("-C", "opt-level=0", "drop_order.rs", "-o", "drop_o0"))
        out["build_o3"] = self.run(self.rustc_cmd("-C", "opt-level=3", "drop_order.rs", "-o", "drop_o3"))
        out["run_native_o0"] = self.run(["./drop_o0"])
        out["run_native_o3"] = self.run(["./drop_o3"])
        logs = {
            "native_o0": self._logs(out["run_native_o0"]["stdout"]),
            "native_o3": self._logs(out["run_native_o3"]["stdout"]),
        }
        miri = self.miri_cmd("drop_order.rs")
        if miri is None:
            out["run_miri"] = {"status": "skipped", "reason": "miri or its sysroot not provided"}
        else:
            out["run_miri"] = self.run(miri, timeout=1800)
            logs["miri"] = self._logs(out["run_miri"]["stdout"])
        out["logs"] = logs
        ref = logs["native_o0"]
        self.check(
            "drop_logs_identical_across_all_executors",
            all(v == ref for v in logs.values()) and len(ref) == 5,
            executors=sorted(logs),
            logs=ref,
        )
        self.check(
            "become_and_plain_call_orders_differ",
            ref.get("S1_BECOME") != ref.get("S1_PLAIN") and ref.get("S2_BECOME") != ref.get("S2_PLAIN"),
            s1=[ref.get("S1_BECOME"), ref.get("S1_PLAIN")],
            s2=[ref.get("S2_BECOME"), ref.get("S2_PLAIN")],
        )
        # In the `become` logs every caller-owned guard precedes the callee body digit 9;
        # in the ordinary-call logs the callee body digit 9 comes first.
        s1b, s1p = str(ref.get("S1_BECOME")), str(ref.get("S1_PLAIN"))
        s2b, s2p = str(ref.get("S2_BECOME")), str(ref.get("S2_PLAIN"))
        self.check(
            "become_runs_caller_drops_before_callee_body",
            s1b.index("9") == 2 and s2b.index("9") == 5 and s1p.index("9") == 0 and s2p.index("9") == 0,
            position_of_callee_body_digit={"S1_BECOME": s1b.index("9"), "S2_BECOME": s2b.index("9"),
                                           "S1_PLAIN": s1p.index("9"), "S2_PLAIN": s2p.index("9")},
        )

        # MIR: where the drops sit relative to the tail call.
        out["dump_mir"] = self.run(
            self.rustc_cmd(
                "-C", "opt-level=0", "-Z", "dump-mir=tail_caller", "-Z", "dump-mir-dir=mirdump",
                "--emit=mir", "drop_order.rs", "-o", "drop_order.mir",
            )
        )
        dump = self.tmp / "mirdump"
        mir: dict = {}
        for fn in ("tail_caller", "tail_caller2"):
            for dump_name in ("built.after", "ElaborateDrops.after"):
                hits = sorted(dump.glob(f"drop_order.{fn}.*{dump_name}.mir"))
                if not hits:
                    continue
                text = hits[0].read_text()
                entry = {"normal_path_events": self._normal_path(text)}
                if fn == "tail_caller":
                    entry["text"] = self.scrub(text).splitlines()
                mir[f"{fn}.{dump_name}"] = entry
        out["mir"] = mir
        built2 = mir.get("tail_caller2.built.after", {}).get("normal_path_events", [])
        # Map MIR locals back to source names through the `debug name => _N;` lines, so
        # the checks below are stated against the Rust source, not against local numbering.
        hits = sorted(dump.glob("drop_order.tail_caller2.*built.after.mir"))
        names = dict(
            (local, name)
            for name, local in re.findall(r"debug (\w+) => (_\d+);", hits[0].read_text() if hits else "")
        )
        out["mir"]["tail_caller2.debug_names"] = names

        def named(event: str) -> str:
            return re.sub(r"_\d+", lambda m: names.get(m.group(0), m.group(0)), event)

        named_events = [named(e) for e in built2]
        out["mir"]["tail_caller2.built.after"]["normal_path_events_by_source_name"] = named_events
        tail_idx = [i for i, e in enumerate(built2) if e.startswith("tailcall ")]
        drops = [e for e in named_events if e.startswith("drop(")]
        # Source declaration order is p1, p2, _a, _b, _c; the expected drop order is its reverse.
        reverse_declaration_order = [f"drop({n})" for n in ("_c", "_b", "_a", "p2", "p1")]
        self.check(
            "built_mir_places_all_caller_drops_before_tailcall_in_reverse_declaration_order",
            bool(tail_idx) and tail_idx[0] == len(built2) - 1 and drops == reverse_declaration_order,
            normal_path_events_by_source_name=named_events,
        )
        dead = [e for e in named_events if e.startswith("StorageDead(")]
        self.check(
            "built_mir_storage_dead_covers_locals_but_not_parameters",
            dead == ["StorageDead(_c)", "StorageDead(_b)", "StorageDead(_a)"],
            storage_dead_events_by_source_name=dead,
        )
        return out

    # ---- C. static rejections ------------------------------------------

    def rejections(self) -> dict:
        out: dict = {}
        expect = {
            "reject_borrow_local": "error[E0597]",
            "reject_borrow_param": "error[E0597]",
            "reject_signature": "error: mismatched signatures",
            "reject_abi": "error: mismatched function ABIs",
            "reject_closure": "error: `become` is not allowed in closures",
            "reject_feature_gate": "error[E0658]",
            "reject_force_inline": "incompatible with `#[rustc_force_inline]`",
        }
        for name, needle in expect.items():
            rec = self.run(self.rustc_cmd(f"{name}.rs", "-o", f"{name}.out"))
            out[name] = rec
            head = rec["stderr"][0] if rec["stderr"] else ""
            self.check(
                f"{name}_is_rejected",
                rec["returncode"] != 0 and needle in "\n".join(rec["stderr"]),
                returncode=rec["returncode"],
                first_diagnostic_line=head,
            )
        build = self.run(self.rustc_cmd("accept_borrow_plain_call.rs", "-o", "accept_plain"))
        runrec = self.run(["./accept_plain"])
        out["accept_borrow_plain_call"] = {"build": build, "run": runrec}
        self.check(
            "same_borrow_is_accepted_with_an_ordinary_call",
            build["returncode"] == 0 and runrec["returncode"] == 0,
            build_returncode=build["returncode"],
            stdout=runrec["stdout"],
        )

        # The rejected program still gets MIR built before the borrow checker runs. Its
        # borrowed local is a plain `u64` (no destructor): record what precedes the tail
        # call in the block that performs it.
        self.run(
            self.rustc_cmd("-Z", "dump-mir=caller", "-Z", "dump-mir-dir=mir_reject",
                           "reject_borrow_local.rs", "-o", "reject_borrow_local.out2")
        )
        hits = sorted((self.tmp / "mir_reject").glob("reject_borrow_local.caller.*built.after.mir"))
        if hits:
            text = hits[0].read_text()
            names = dict(
                (local, name) for name, local in re.findall(r"debug (\w+) => (_\d+);", text)
            )
            block: list[str] = []
            for chunk in re.split(r"\n\s*\n", text):
                if "tailcall " in chunk:
                    block = [l.strip() for l in chunk.splitlines() if l.strip() not in ("}",)]
            borrowed = next((loc for loc, name in names.items() if name == "local"), None)
            before = block[: next((i for i, l in enumerate(block) if l.startswith("tailcall ")), 0)]
            out["reject_borrow_local_built_mir"] = {
                "debug_names": names,
                "block_performing_the_tail_call": block,
            }
            self.check(
                "no_storage_dead_precedes_tailcall_for_a_local_without_destructor",
                borrowed is not None
                and any(l.startswith("tailcall ") for l in block)
                and f"StorageDead({borrowed});" not in before
                and not any(l.startswith("drop(") for l in before),
                borrowed_local=borrowed,
                statements_before_tailcall=before,
            )
        return out

    # ---- D. MIR inliner ---------------------------------------------------

    @staticmethod
    def _fn_body(mir: str, name: str) -> str:
        m = re.search(rf"^fn {name}\(.*?^}}", mir, re.M | re.S)
        return m.group(0) if m else ""

    @staticmethod
    def _ir_fn(ir: str, name: str) -> list[str]:
        body, on = [], False
        for l in ir.splitlines():
            if l.startswith("define") and name in l.split("(")[0]:
                on = True
            if on:
                body.append(l)
                if l.strip() == "}":
                    break
        return body

    def inline_refusal(self) -> dict:
        out: dict = {}
        out["emit_mir_o3"] = self.run(
            self.rustc_cmd("-C", "opt-level=3", "--emit=mir", "inline_refusal.rs", "-o", "inline.mir")
        )
        mir = self.read("inline.mir")
        cb = self._fn_body(mir, "caller_of_become")
        cp = self._fn_body(mir, "caller_of_plain")
        out["mir_caller_of_become"] = cb.splitlines()
        out["mir_caller_of_plain"] = cp.splitlines()
        self.check(
            "mir_inliner_keeps_call_to_helper_with_tail_call",
            "helper_become(" in cb and "(inlined helper_become)" not in cb,
            calls_helper="helper_become(" in cb,
            inlined_scope="(inlined helper_become)" in cb,
        )
        self.check(
            "mir_inliner_inlines_identical_helper_without_tail_call",
            "(inlined helper_plain)" in cp and "helper_plain(" not in cp,
            calls_helper="helper_plain(" in cp,
            inlined_scope="(inlined helper_plain)" in cp,
        )
        llvm: dict = {}
        for level in ("0", "3"):
            rec = self.run(
                self.rustc_cmd(
                    "-C", f"opt-level={level}", "-Z", "merge-functions=disabled",
                    "--emit=llvm-ir", "inline_refusal.rs", "-o", f"inline_o{level}.ll",
                )
            )
            ir = self.read(f"inline_o{level}.ll")
            body = self._ir_fn(ir, "caller_of_become")
            llvm[f"opt_level_{level}"] = {
                "build": rec,
                "caller_of_become_call_lines": [l.strip() for l in body if " call " in l],
                "musttail_anywhere_in_module": "musttail" in ir,
                "helper_become_defined_in_module": any(
                    l.startswith("define") and "helper_become" in l for l in ir.splitlines()
                ),
            }
        merged = self.run(
            self.rustc_cmd("-C", "opt-level=3", "--emit=llvm-ir", "inline_refusal.rs",
                           "-o", "inline_o3_merged.ll")
        )
        llvm["opt_level_3_default_function_merging"] = {
            "build": merged,
            "lines_naming_caller_of_become": [
                l.strip() for l in self.read("inline_o3_merged.ll").splitlines()
                if "caller_of_become" in l and not l.lstrip().startswith(";")
            ],
        }
        out["llvm"] = llvm
        out["note_llvm"] = (
            "Recorded, not asserted: what LLVM's own inliner does with the "
            "`#[inline(always)]` helper after the MIR inliner declined it."
        )
        return out

    # ---- E. symbol mangling ------------------------------------------------

    @staticmethod
    def _mangling_source(depth: int) -> str:
        lines = [
            '#![crate_type = "lib"]',
            "pub struct Pair<A, B>(pub A, pub B);",
            "#[inline(never)]",
            "pub fn touch_gen<T>() -> usize { core::mem::size_of::<T>() }",
            "type D0 = u64;",
        ]
        for d in range(1, depth + 1):
            lines.append(f"type D{d} = Pair<D{d - 1}, D{d - 1}>;")
        lines.append(f"pub fn entry() -> usize {{ touch_gen::<D{depth}>() }}")
        return "\n".join(lines) + "\n"

    @staticmethod
    def _expanded_type(depth: int) -> str:
        t = "u64"
        for _ in range(depth):
            t = f"{CRATE}::Pair<{t}, {t}>"
        return t

    def _symbol(self, obj: str, demangle: bool) -> str | None:
        if not self.llvm_nm:
            return None
        cmd = [self.llvm_nm] + (["-C"] if demangle else []) + [obj]
        proc = subprocess.run(cmd, cwd=self.tmp, capture_output=True, text=True)
        for line in proc.stdout.splitlines():
            parts = line.split(None, 2)
            if len(parts) == 3 and parts[1] in ("T", "t", "W") and "touch_gen" in parts[2]:
                return parts[2]
        return None

    def mangling(self) -> dict:
        out: dict = {"crate_name": CRATE, "generic_item": "touch_gen::<D_depth>",
                     "type_family": "D0 = u64; D(n+1) = Pair<Dn, Dn>"}
        if not self.llvm_nm:
            out["status"] = "skipped"
            out["reason"] = "llvm-nm not found (install the llvm-tools component or pass --llvm-nm)"
            return out
        out["status"] = "ran"
        modes = {
            "default": [],
            "v0": ["-C", "symbol-mangling-version=v0"],
            "legacy": ["-Z", "unstable-options", "-C", "symbol-mangling-version=legacy"],
        }
        rows = []
        for depth in range(1, self.args.max_depth + 1):
            (self.tmp / f"ms{depth}.rs").write_text(self._mangling_source(depth))
            row: dict = {"depth": depth}
            for mode, flags in modes.items():
                obj = f"ms{depth}_{mode}.o"
                rec = self.run(
                    self.rustc_cmd("--crate-name", CRATE, "-C", "opt-level=0", "--emit=obj",
                                   *flags, f"ms{depth}.rs", "-o", obj)
                )
                sym = self._symbol(obj, demangle=False) if rec["returncode"] == 0 else None
                dem = self._symbol(obj, demangle=True) if rec["returncode"] == 0 else None
                row[f"{mode}_symbol"] = sym
                row[f"{mode}_bytes"] = len(sym) if sym else None
                if mode != "default":
                    row[f"{mode}_demangled_bytes"] = len(dem) if dem else None
                    if mode == "legacy":
                        row["legacy_demangled"] = dem
                    else:
                        expected = f"{CRATE}::touch_gen::<{self._expanded_type(depth)}>"
                        row["v0_demangled_equals_fully_expanded_type"] = dem == expected
                        row["v0_demangled_u64_leaves"] = dem.count("u64") if dem else None
                        # Count `B<base62>_` backreferences only after the crate-root identifier:
                        # the crate disambiguator before it is arbitrary base-62 text and may
                        # itself contain a `B`.
                        tail = sym.split(f"{len(CRATE)}{CRATE}", 1)[1] if sym else ""
                        row["v0_backreference_count"] = len(re.findall(r"B[0-9A-Za-z]*_", tail)) if sym else None
            rows.append(row)
        out["depth_scaling"] = rows
        v0 = [r["v0_bytes"] for r in rows]
        legacy = [r["legacy_bytes"] for r in rows]
        dem = [r["v0_demangled_bytes"] for r in rows]
        out["v0_bytes_increment_per_level"] = [b - a for a, b in zip(v0, v0[1:])]
        out["v0_demangled_bytes_ratio_per_level"] = [round(b / a, 3) for a, b in zip(dem, dem[1:])]
        if len(v0) > 1:
            out["v0_mean_bytes_per_level"] = round((v0[-1] - v0[0]) / (len(v0) - 1), 3)
        self.check(
            "default_mangling_equals_explicit_v0_at_every_depth",
            all(r["default_symbol"] == r["v0_symbol"] and r["v0_symbol"].startswith("_R") for r in rows),
            first_default_symbol=rows[0]["default_symbol"],
        )
        self.check(
            "legacy_symbol_length_constant_and_names_distinct",
            len(set(legacy)) == 1 and len({r["legacy_symbol"] for r in rows}) == len(rows)
            and all(r["legacy_symbol"].startswith("_ZN") for r in rows),
            legacy_bytes=legacy,
        )
        self.check(
            "legacy_demangled_name_carries_no_type_arguments",
            all(r["legacy_demangled"] and "Pair" not in r["legacy_demangled"] for r in rows),
            first=rows[0]["legacy_demangled"],
            last=rows[-1]["legacy_demangled"],
        )
        self.check(
            "v0_demangles_to_the_fully_expanded_type_at_every_depth",
            all(r["v0_demangled_equals_fully_expanded_type"] for r in rows),
            u64_leaves=[r["v0_demangled_u64_leaves"] for r in rows],
        )
        self.check(
            "v0_leaves_double_per_level_while_symbol_grows_by_a_bounded_increment",
            all(r["v0_demangled_u64_leaves"] == 2 ** r["depth"] for r in rows)
            and max(out["v0_bytes_increment_per_level"]) <= 16,
            v0_bytes=v0,
            increments=out["v0_bytes_increment_per_level"],
        )
        (self.tmp / "ms_gate.rs").write_text(self._mangling_source(1))
        gate = self.run(
            self.rustc_cmd("--crate-name", CRATE, "--emit=obj", "-C", "symbol-mangling-version=legacy",
                           "ms_gate.rs", "-o", "ms_gate.o")
        )
        out["legacy_without_unstable_options"] = gate
        self.check(
            "legacy_requires_z_unstable_options",
            gate["returncode"] != 0 and "requires `-Z unstable-options`" in "\n".join(gate["stderr"]),
            returncode=gate["returncode"],
            stderr=gate["stderr"],
        )
        return out

    # ---- driver ---------------------------------------------------------------

    def collect(self) -> dict:
        tools = {
            "rustc_version_verbose": self.rustc_vv.splitlines(),
            "miri_version": (
                self.scrub(self._capture([self.miri, "--version"]).strip()) if self.miri else None
            ),
            "llvm_nm_version": (
                [l.strip() for l in self._capture([self.llvm_nm, "--version"]).splitlines() if l.strip()]
                if self.llvm_nm else None
            ),
            "os": platform.system(),
            "machine": platform.machine(),
        }
        result = {
            "schema": "tail-call-and-mangling-probe/1",
            "tools": tools,
            "parameters": {
                "steps": self.args.steps,
                "miri_steps": self.args.miri_steps,
                "max_depth": self.args.max_depth,
                "edition": "2024",
            },
            "tail_recursion": self.tail_recursion(),
            "drop_order": self.drop_order(),
            "rejections": self.rejections(),
            "inline_refusal": self.inline_refusal(),
            "mangling": self.mangling(),
        }
        result["checks"] = self.checks
        result["all_checks_passed"] = all(c["passed"] for c in self.checks)
        return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default=os.environ.get("RUSTC", "rustc"))
    ap.add_argument("--miri", default=os.environ.get("MIRI"))
    ap.add_argument("--miri-sysroot", default=None)
    ap.add_argument("--llvm-nm", default=os.environ.get("LLVM_NM"))
    ap.add_argument("--steps", type=int, default=250_000)
    ap.add_argument("--miri-steps", type=int, default=250_000)
    ap.add_argument("--max-depth", type=int, default=10)
    ap.add_argument("--out", default=None, help="write JSON here instead of stdout")
    args = ap.parse_args()

    with tempfile.TemporaryDirectory(prefix="tailcall_probe_") as tmp:
        result = Probe(args, Path(tmp)).collect()

    text = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    failed = [c["name"] for c in result["checks"] if not c["passed"]]
    print(
        f"checks: {len(result['checks']) - len(failed)}/{len(result['checks'])} passed"
        + (f"; FAILED: {', '.join(failed)}" if failed else ""),
        file=sys.stderr,
    )
    return 0 if not failed else 1


if __name__ == "__main__":
    raise SystemExit(main())
