# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Interactive query operations of `WorkspacePool`."""

from __future__ import annotations

from collections import Counter
import os
from pathlib import Path
import re
import time
from typing import Any

from .client import mask_lean_comments, middle_clip, py_col_to_utf16, uri_to_path, utf16_to_py_col
from .discovery import discover_workspace, validate_no_symlink_target
from .lean_source import (
    _KINDS, _SCOPE_BOUND_RE, _SORRY_RE, _SORRY_WARN_RE, _cdiag, _col, _flatten_syms, _fmt_cand,
    _logical_lines, _match_decl, _req_lean, _safe_read_lines, _scan_decls, _walk_lean,
)


class _PoolQueries:
    """Query methods of `WorkspacePool`, which supplies `_checkout`,
    `_pos_req`, `_goal_at`, `_req_err`, `_retire_dead_worker`, and the pool
    settings they read."""

    def diagnostics(self, file: str, *, severity: str = "all", **wkw: Any) -> dict[str, Any]:
        if severity not in ("all", "warning", "error"):
            raise ValueError(
                f"Invalid `severity`: {severity!r}; expected 'all', 'warning', or 'error'."
            )
        p = _req_lean(file, home=wkw.get("caller_home"))
        with self._checkout(p, **wkw) as worker, worker.lock:
            text = p.read_text("utf-8", errors="replace")
            uri, ms, ok = worker.sync_text(p, text)
            raw_diags, fatal = worker.diags(uri), worker.has_fatal_progress(uri)
            w_err = worker.worker_error(uri)
            ctx, pid, sbx = worker.ctx, worker.lsp.proc.pid, worker.sandboxed
            lines = _logical_lines(text)
            clean = _logical_lines(mask_lean_comments(text)) + [""] * len(lines)
            sorrys = [
                (i, r.strip(), m.start(1))
                for i, (r, c) in enumerate(zip(lines, clean), 1)
                for m in _SORRY_RE.finditer(c)
            ]
            sgoals: list[dict[str, Any]] = []
            goal_timed_out = False
            if ok:
                for ln, _, col in sorrys[:8]:
                    gs, g_to = [], False
                    try:
                        gs = self._goal_at(worker, uri, ln - 1, lines[ln - 1], col, 4.0)
                    except TimeoutError:
                        g_to = goal_timed_out = True
                    except RuntimeError as exc:
                        w_err = w_err or self._req_err(worker, exc)
                        break
                    sgoals.append({"line": ln, "column": col + 1, "goals": gs, "timed_out": g_to})
        all_diags = [_cdiag(d, lines) for d in raw_diags]
        errs = [d for d in all_diags if d["severity"] == "error"]
        warns = [d for d in all_diags if d["severity"] == "warning"]
        diags = (
            all_diags
            if severity == "all"
            else [d for d in all_diags if d["severity"] == severity]
        )
        if w_err and not errs:
            synth = {"severity": "error", "line": 1, "column": 1, "message": w_err}
            if severity in ("all", "error"):
                diags.append(synth)
            errs.append(synth)
        body = [f"File: {p} ({ctx.mode} root={ctx.root}; {ms} ms; pid={pid}; sandbox={sbx})"]
        if w_err:
            body.append(f"Lean file worker error ({len(diags)} partial): {w_err}")
        elif not ok:
            body.append(f"Timed out waiting for Lean diagnostics ({len(diags)} partial).")
        if goal_timed_out:
            body.append("Timed out querying Lean goals for one or more sorry targets.")
        if fatal and not w_err:
            body.append("Fatal import/header failure reported by Lean server.")
        if hint := ctx.missing_artifacts_hint():
            body.append(hint)
        body.append(f"Errors: {len(errs)} | Warnings: {len(warns)} | sorry targets: {len(sorrys)}")
        body.extend(
            f"  L{d['line']}:{d['column']} [{d['severity']}] {d['message']}" for d in diags[:40]
        )
        sg_map = {(g["line"], g["column"]): g for g in sgoals}
        for ln, txt, col in sorrys[:20]:
            body.append(f"  sorry @ L{ln}:{col + 1}: {txt}")
            if (sg := sg_map.get((ln, col + 1))) is not None:
                if sg["timed_out"]:
                    body.append("    goal: timed out")
                elif sg["goals"]:
                    for gi, g in enumerate(sg["goals"][:2], 1):
                        if len(sg["goals"]) > 1:
                            body.append(f"    -- goal {gi}/{len(sg['goals'])} --")
                        body.extend(f"    {gl}" for gl in str(g).splitlines()[:6])
        return {
            "file": str(p), "mode": ctx.mode, "root": str(ctx.root), "sandboxed": sbx,
            "server_pid": pid, "elapsed_ms": ms,
            "completed": ok and not goal_timed_out and not w_err,
            "timed_out": ((not ok) and not w_err) or goal_timed_out, "fatal": fatal,
            "error_count": len(errs), "warning_count": len(warns), "sorry_count": len(sorrys),
            "sorry_lines": [ln for ln, _, _ in sorrys], "sorry_goals": sgoals,
            "diagnostics": diags, "text": middle_clip("\n".join(body)),
        }

    def goal(
        self, file: str, line: int, *, column: int | None = None,
        snippet: str | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p = _req_lean(file, home=wkw.get("caller_home"))
        with self._checkout(p, **wkw) as worker, worker.lock:
            text = p.read_text("utf-8", errors="replace")
            uri, ms, ok = worker.sync_text(p, text)
            w_err = worker.worker_error(uri)
            fatal = worker.has_fatal_progress(uri)
            has_errs = any(int(d.get("severity", 1)) == 1 for d in worker.diags(uri))
            lines = _logical_lines(text)
            if not (1 <= line <= len(lines)):
                raise ValueError(f"line {line} out of range 1..{len(lines)}")
            raw = lines[line - 1]
            sc, ec, fc = len(raw) - len(raw.lstrip()), len(raw.rstrip()), _col(raw, snippet, column)
            cache: dict[int, list[Any]] = {}
            tg: Any = None
            timed_out = (not ok) and not w_err
            if ok:
                try:
                    for c in (sc, fc, ec):
                        if c not in cache:
                            cache[c] = self._goal_at(worker, uri, line - 1, raw, c)
                    pos = {"line": line - 1, "character": py_col_to_utf16(raw, fc)}
                    req = {"textDocument": {"uri": uri}, "position": pos}
                    tg = worker.lsp.request("$/lean/plainTermGoal", req, 10.0)
                except TimeoutError:
                    timed_out, tg = True, None
                except RuntimeError as exc:
                    w_err = w_err or self._req_err(worker, exc)
                    tg = None
        before, focus, after = cache.get(sc, []), cache.get(fc, []), cache.get(ec, [])
        term = tg.get("goal") if isinstance(tg, dict) else None
        if w_err:
            empty_t = f"worker error (goal unknown): {w_err}"
            empty_a = empty_t
        elif timed_out:
            empty_t = empty_a = "timed out (goal unknown)"
        elif fatal:
            empty_t = "no tactic goals (fatal header/import error)"
            empty_a = "no goals (fatal header/import error)"
        elif has_errs:
            empty_t = "no tactic goals (file has errors)"
            empty_a = "no goals (file has errors)"
        else:
            empty_t = "no tactic goals"
            empty_a = "no goals"
        out = [f"File: {p}:{line} ({ms} ms)"]
        if w_err:
            out.append(f"Lean file worker error (goal unknown): {w_err}")
        elif timed_out:
            out.append("Timed out waiting for Lean goal state (partial/stale result).")
        out.append(f"Line {line}: `{raw}`")
        if column is not None or snippet:
            out.extend([f"\n--- Goal at col {fc + 1} ---", "\n\n".join(focus) or empty_t])
        out.extend([
            f"\n--- Goal BEFORE L{line} (col {sc + 1}) ---",
            "\n\n".join(before) or empty_t,
            f"\n--- Goal AFTER L{line} (col {ec + 1}) ---",
            "\n\n".join(after) or empty_a,
        ])
        if term:
            out.append(f"\n--- Term Goal ---\n{term}")
        return {
            "file": str(p), "line": line, "elapsed_ms": ms,
            "completed": ok and not timed_out and not w_err,
            "timed_out": timed_out, "goals_before": before, "goals_focus": focus,
            "goals_after": after, "term_goal": term, "text": middle_clip("\n".join(out)),
        }

    def multi_attempt(
        self, file: str, line: int, tactics: list[str], *,
        candidate_budget_s: float = 190.0, **wkw: Any,
    ) -> dict[str, Any]:
        """Try tactics in memory via `didChange` (advisory; verify via `cargo anneal`)."""
        cleaned = [str(t).strip() for t in tactics if str(t).strip()]
        if not cleaned or len(cleaned) > 12:
            raise ValueError("Provide 1..12 non-empty candidate tactics.")
        p, results = _req_lean(file, home=wkw.get("caller_home")), []
        with self._checkout(p, **wkw) as worker, worker.lock:
            orig = p.read_text("utf-8", errors="replace")
            uri, _, base_ok = worker.sync_text(p, orig)
            orig_lines = _logical_lines(orig)
            if not (1 <= line <= len(orig_lines)):
                raise ValueError(f"line {line} out of range 1..{len(orig_lines)}")
            clean = _logical_lines(mask_lean_comments(orig)) + [""] * len(orig_lines)
            raw, c_tgt = orig_lines[line - 1], clean[line - 1]
            sorry_m = _SORRY_RE.search(c_tgt)
            pcol = sorry_m.start(1) if sorry_m else (len(c_tgt.rstrip()) - len(c_tgt.strip()))
            d0 = 0
            for idx in range(line - 1, -1, -1):
                if (m := _match_decl(cln := clean[idx])) and (idx < line - 1 or m.start(1) < pcol):
                    d0 = idx
                    break
                if idx < line - 1 and _SCOPE_BOUND_RE.match(cln):
                    d0 = idx + 1
                    break
            d1 = len(orig_lines)
            for idx in range(line, len(orig_lines)):
                if _match_decl(cln := clean[idx]) or _SCOPE_BOUND_RE.match(cln):
                    d1 = idx
                    break
            bdiags = worker.diags(uri)
            dl = lambda d: int(d.get("range", {}).get("start", {}).get("line", -9))
            uns = lambda s: s == "unsolved goals" or s.startswith("unsolved goals\n")
            lsp_alive = lambda: not hasattr(worker.lsp, "is_alive") or worker.lsp.is_alive()
            w_err = worker.worker_error(uri) or (
                None if lsp_alive() else "Lean LSP process exited unexpectedly."
            )
            fatal = worker.has_fatal_progress(uri) or not base_ok
            prior = [_cdiag(d, orig_lines) for d in bdiags
                     if d.get("severity") == 1 and not uns(str(d.get("message", "")).strip())
                     and (d0 <= dl(d) < line - 1 or (fatal and 0 <= dl(d) < d0))]
            if not prior and w_err:
                prior = [{"severity": "error", "line": 1, "column": 1, "message": w_err}]
            if prior:
                if not lsp_alive():
                    self._retire_dead_worker(worker)
                results = [{"tactic": c, "evaluated": False, "closes_goal": False, "ok_step": False,
                            "uses_sorry": False, "remaining_goals": [], "errors": prior[:3],
                            "elapsed_ms": 0.0, "timed_out": False} for c in cleaned]
            else:
                berr = Counter((dl(d), str(d.get("message", "")).strip())
                               for d in bdiags if d.get("severity") == 1 and dl(d) != line - 1)
                try:
                    cand_dl = time.monotonic() + max(0.0, float(candidate_budget_s))
                    for cand_idx, cand in enumerate(cleaned):
                        rem = cand_dl - time.monotonic()
                        if rem <= 0:
                            results.append({
                                "tactic": cand, "evaluated": True, "closes_goal": False,
                                "ok_step": False, "uses_sorry": False, "remaining_goals": [],
                                "errors": [], "timed_out": True, "elapsed_ms": 0.0,
                            })
                            continue
                        t0 = time.monotonic()
                        rep, ec = _fmt_cand(raw, sorry_m, cand)
                        rls = rep.split("\n")
                        delta, mod = len(rls) - 1, list(orig_lines)
                        mod[line - 1 : line] = rls
                        body = "\n".join(mod)
                        _, _, ok = worker.sync_text(p, body, wait_s=min(15.0, rem))
                        cand_w_err = worker.worker_error(uri)
                        li, ga = (line - 1) + delta, []
                        if not lsp_alive():
                            ok = False
                            cand_w_err = cand_w_err or "Lean LSP process exited unexpectedly."
                        if ok:
                            rem_g = cand_dl - time.monotonic()
                            if rem_g <= 0:
                                ok = False
                            else:
                                try:
                                    ga = self._goal_at(
                                        worker, uri, li, mod[li], ec, min(5.0, rem_g)
                                    )
                                except TimeoutError:
                                    ok = False
                                except RuntimeError as exc:
                                    ok = False
                                    cand_w_err = cand_w_err or self._req_err(worker, exc)
                            if not lsp_alive():
                                ok = False
                                cand_w_err = cand_w_err or "Lean LSP process exited unexpectedly."
                        errs, unsv, seen, warn_sorry = [], [], Counter(), False
                        for d in worker.diags(uri):
                            ln0, msg = dl(d), str(d.get("message", "")).strip()
                            if d.get("severity") == 2:
                                if d0 <= ln0 < d1 + delta and _SORRY_WARN_RE.search(msg):
                                    warn_sorry = True
                                continue
                            if d.get("severity") != 1:
                                continue
                            tgt = (line - 1) <= ln0 <= li
                            if not tgt:
                                seen[(ln0, msg)] += 1
                                orig_ln = ln0 - (delta if ln0 > li else 0)
                                tgt = seen[(ln0, msg)] > berr.get((orig_ln, msg), 0)
                            if tgt:
                                item = msg if uns(msg) else _cdiag(d, mod)
                                (unsv if uns(msg) else errs).append(item)
                        if cand_w_err and not errs:
                            errs.append(
                                {"severity": "error", "line": 1, "column": 1, "message": cand_w_err}
                            )
                        if not errs and unsv and not ga:
                            pts = unsv[0].split("\n", 1)[1].strip() if "\n" in unsv[0] else ""
                            ga = [pts or "unsolved goals"]
                        decl_mask = mask_lean_comments("\n".join(mod[d0 : d1 + delta]))
                        cand_mask = mask_lean_comments(cand)
                        usor = bool(
                            _SORRY_RE.search(cand_mask)
                            or _SORRY_RE.search(decl_mask)
                            or warn_sorry
                        )
                        ok_step = ok and not errs and not usor and not cand_w_err
                        ms = round((time.monotonic() - t0) * 1000.0, 1)
                        results.append({
                            "tactic": cand, "evaluated": True, "closes_goal": ok_step and not ga,
                            "ok_step": ok_step, "uses_sorry": usor, "remaining_goals": ga,
                            "errors": errs, "timed_out": (not ok) and not cand_w_err,
                            "elapsed_ms": ms,
                        })
                        if not lsp_alive():
                            blk = cand_w_err or "Lean LSP process exited unexpectedly."
                            blk_err = [{
                                "severity": "error", "line": 1, "column": 1, "message": blk,
                            }]
                            for rem_cand in cleaned[cand_idx + 1 :]:
                                results.append({
                                    "tactic": rem_cand, "evaluated": False, "closes_goal": False,
                                    "ok_step": False, "uses_sorry": False, "remaining_goals": [],
                                    "errors": blk_err, "elapsed_ms": 0.0, "timed_out": False,
                                })
                            break
                finally:
                    if lsp_alive():
                        worker.sync_text(p, orig, wait_s=15.0)
                    if not lsp_alive():
                        self._retire_dead_worker(worker)
        out = [f"In-Memory Multi-Attempt (advisory; verify via `cargo anneal`) on {p}:{line}"]
        for idx, r in enumerate(results, 1):
            tag = (
                f"BLOCKED (prior error at L{r['errors'][0]['line']})" if not r["evaluated"]
                else "TIMEOUT" if r["timed_out"]
                else "INCOMPLETE (uses sorry)" if r["uses_sorry"] and not r["errors"]
                else "CLOSED (0 goals, 0 errors; advisory)" if r["closes_goal"]
                else f"STEP ({len(r['remaining_goals'])} remaining)" if r["ok_step"]
                else f"ERROR ({len(r['errors'])})"
            )
            out.append(f"[{idx}] `{r['tactic']}` -> {tag} ({r['elapsed_ms']} ms)")
            if r["errors"]:
                out.append(f"    {r['errors'][0]['message'][:220]}")
            elif r["remaining_goals"]:
                out.append("    " + "\n    ".join(r["remaining_goals"][0].splitlines()[:6]))
        return {"attempts": results, "text": middle_clip("\n".join(out))}

    def hover(
        self, file: str, line: int, *, symbol: str | None = None,
        column: int | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p, ln, col, res, _, _, timed_out, w_err = self._pos_req(
            "textDocument/hover", file, line, symbol=symbol, column=column, wkw=wkw
        )
        c = res.get("contents") if isinstance(res, dict) else None
        if isinstance(c, str):
            md = c.strip()
        elif isinstance(c, dict):
            md = str(c.get("value", "")).strip()
        elif isinstance(c, list):
            md = "\n".join(str(x.get("value", x) if isinstance(x, dict) else x).strip() for x in c)
        else:
            md = ""
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            txt = middle_clip(f"{prefix}\n{md}" if md else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean hover info at {p}:{ln}:{col}."
            txt = middle_clip(f"{prefix}\n{md}" if md else prefix)
        else:
            txt = middle_clip(md or f"No hover info at {p}:{ln}:{col}.")
        return {
            "hover": md, "line": ln, "column": col,
            "completed": (not timed_out) and not w_err, "timed_out": timed_out, "text": txt,
        }

    def definition(
        self, file: str, line: int, *, symbol: str | None = None,
        column: int | None = None, **wkw: Any,
    ) -> dict[str, Any]:
        p, ln, col, res, allowed_roots, excluded_roots, timed_out, w_err = self._pos_req(
            "textDocument/definition", file, line, symbol=symbol, column=column, wkw=wkw
        )
        locs: list[dict[str, Any]] = []
        for item in (res if isinstance(res, list) else ([res] if isinstance(res, dict) else [])):
            if not isinstance(item, dict):
                continue
            tu = item.get("targetUri") or item.get("uri")
            rng = item.get("targetSelectionRange") or item.get("targetRange") or item.get("range")
            if isinstance(tu, str) and isinstance(rng, dict):
                st = rng.get("start", {})
                tp, tl = uri_to_path(tu), int(st.get("line", 0)) + 1
                tu16 = int(st.get("character", 0))
                is_file = tu.lower().startswith("file://")
                lines = _safe_read_lines(tp, allowed_roots, excluded_roots) if is_file else None
                if lines is not None:
                    tcol = (
                        utf16_to_py_col(lines[tl - 1], tu16) + 1
                        if 1 <= tl <= len(lines) else tu16 + 1
                    )
                    lo, hi = max(1, tl - 2), min(len(lines), tl + 2)
                    snip = "\n".join(
                        f"{'>' if i == tl else ' '} {i:4d}: {lines[i - 1]}"
                        for i in range(lo, hi + 1)
                    )
                else:
                    tcol, snip = tu16 + 1, ""
                locs.append({"file": tp, "line": tl, "column": tcol, "snippet": snip})
        out = [f"{loc['file']}:{loc['line']}:{loc['column']}\n{loc['snippet']}" for loc in locs[:5]]
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            body = "\n\n".join(out)
            txt = middle_clip(f"{prefix}\n\n{body}" if body else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean definition at {p}:{ln}:{col}."
            body = "\n\n".join(out)
            txt = middle_clip(f"{prefix}\n\n{body}" if body else prefix)
        else:
            txt = middle_clip("\n\n".join(out) or f"No definition at {p}:{ln}:{col}.")
        return {
            "locations": locs, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": txt,
        }

    def completions(
        self, file: str, line: int, *, column: int | None = None, **wkw: Any
    ) -> dict[str, Any]:
        p, ln, col, res, _, _, timed_out, w_err = self._pos_req(
            "textDocument/completion", file, line, column=column, eol_default=True, wkw=wkw
        )
        if isinstance(res, dict):
            raw = res.get("items", [])
        else:
            raw = res if isinstance(res, list) else []
        items = [
            {"label": str(it.get("label", "")), "detail": str(it.get("detail") or ""),
             "kind": _KINDS.get(int(it.get("kind") or 0), "")}
            for it in raw[:30] if isinstance(it, dict)
        ]
        lines = [
            f"- {it['label']}" + (f" : {it['detail']}" if it["detail"] else "") for it in items
        ]
        if w_err:
            prefix = f"Lean file worker error at {p}:{ln}:{col}: {w_err}"
            txt = middle_clip(f"{prefix}\n" + "\n".join(lines) if lines else prefix)
        elif timed_out:
            prefix = f"Timed out waiting for Lean completions at {p}:{ln}:{col}."
            txt = middle_clip(f"{prefix}\n" + "\n".join(lines) if lines else prefix)
        else:
            txt = middle_clip("\n".join(lines) or "No completions.")
        return {
            "items": items, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": txt,
        }

    def outline(self, file: str, **wkw: Any) -> dict[str, Any]:
        ch = wkw.get("caller_home")
        p = validate_no_symlink_target(file, home=ch, kind="Lean target")
        if p.is_dir():
            syms = [{**d, "file": str(fp)} for fp in _walk_lean(p) for d in _scan_decls(fp)]
            txt = "\n".join(f"{e['file']}:{e['line']}: {e['signature']}" for e in syms[:80])
            return {
                "symbols": syms, "completed": True, "timed_out": False,
                "text": middle_clip(txt or "No Lean declarations."),
            }
        p, syms = _req_lean(str(p), home=ch), []
        with self._checkout(p, **wkw) as worker, worker.lock:
            uri, _, ok = worker.sync_text(p, p.read_text("utf-8", errors="replace"))
            w_err = worker.worker_error(uri)
            req = {"textDocument": {"uri": uri}}
            res, timed_out = None, (not ok) and not w_err
            if ok:
                try:
                    res = worker.lsp.request("textDocument/documentSymbol", req, 10.0)
                except TimeoutError:
                    timed_out = True
                except RuntimeError as exc:
                    w_err = w_err or self._req_err(worker, exc)
        if isinstance(res, list):
            _flatten_syms(res, syms)
        syms = syms or _scan_decls(p)
        lines = [
            f"{'  ' * int(s.get('depth', 0))}L{s['line']}: {s.get('kind', '')} {s['name']}".strip()
            + (f" — {s['detail']}" if s.get("detail") else "")
            for s in syms[:100]
        ]
        head = (
            [f"Lean file worker error ({w_err}); fallback regex outline."] if w_err
            else ["Timed out waiting for Lean symbols (fallback regex outline)."] if timed_out
            else []
        )
        txt = "\n".join([*head, *lines])
        return {
            "symbols": syms, "completed": (not timed_out) and not w_err,
            "timed_out": timed_out, "text": middle_clip(txt or "No symbols found."),
        }

    def local_search(
        self, query: str, *, workspace: str | None = None, max_results: int = 30, **wkw: Any
    ) -> dict[str, Any]:
        eff_art = (
            wkw.get("artifacts_dir")
            if wkw.get("artifacts_dir") is not None else self.default_artifacts_dir
        )
        eff_lp = [*self.default_extra_lean_path, *(wkw.get("extra_lean_path") or ())] or None
        ch_raw = wkw.get("caller_home")
        ch_lex = Path(os.path.abspath(str(ch_raw.expanduser()))) if ch_raw is not None else None
        ctx = discover_workspace(
            workspace or ".",
            artifacts_dir=eff_art,
            extra_lean_path=eff_lp,
            extra_lean_src_path=wkw.get("extra_lean_src_path"),
            cargo_target_dir=wkw.get("cargo_target_dir"),
            test_install_root=wkw.get("test_install_root"),
            require_lean=False,
            use_env=self.use_env,
            home=ch_lex,
        )
        roots = [
            ctx.root,
            *(e for e in ctx.lean_src_path if e.is_dir() and not e.is_relative_to(ctx.root)),
        ]
        try:
            rx = re.compile(query[6:], re.IGNORECASE) if query.startswith("regex:") else None
        except re.error as exc:
            raise ValueError(f"Invalid regex `{query[6:]}`: {exc}") from exc
        pat, hits = query.lower(), []
        for sr in dict.fromkeys(roots):
            for fp in _walk_lean(sr):
                rel = str(fp.relative_to(sr))
                for d in _scan_decls(fp):
                    hit = (bool(rx.search(d["name"]) or rx.search(rel)) if rx
                           else (pat in d["name"].lower() or pat in fp.stem.lower()))
                    if hit:
                        hits.append({**d, "file": str(fp)})
                        if len(hits) >= max_results:
                            txt = "\n".join(
                                f"{h['file']}:{h['line']}: {h['signature']}" for h in hits
                            )
                            return {"matches": hits, "text": middle_clip(txt)}
        txt = "\n".join(f"{h['file']}:{h['line']}: {h['signature']}" for h in hits)
        return {"matches": hits, "text": middle_clip(txt or f"No matches for `{query}`.")}
