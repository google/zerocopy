# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for a live Lean server."""

from __future__ import annotations

from .support import (
    _bwrap_usable,
    _CI_DIR,
    handle_mcp_request,
    json,
    _maybe_live_lean,
    mock,
    os,
    Path,
    _scrubbed_env,
    subprocess,
    sys,
    tempfile,
    WorkspacePool,
)


class LiveServerCases:
    """`LiveLeanServerIntegrationTest` methods for a live Lean server."""

    def test_live_lean_server_warmth_tools_and_multi_attempt(self) -> None:
        lean_bin = _maybe_live_lean()
        if lean_bin is None:
            msg = "no Lean 4 toolchain installed"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            unit = root / "unit"
            unit.mkdir()
            (unit / "request.json").write_text("{}", encoding="utf-8")
            art = root / "art"
            (art / "lean-lib").mkdir(parents=True)
            spec = unit / "Spec.lean"
            spec.write_text("def targetVal : Nat := 42\n", encoding="utf-8")
            subprocess.check_call(
                [str(lean_bin), "-R", str(unit), "-o", str(art / "lean-lib/Spec.olean"), str(spec)],
                cwd=str(unit), timeout=30,
            )
            lean_file = unit / "Sample.lean"
            lines = [
                "import Spec",
                "theorem add_zero_demo (n : Nat) : n + 0 = n ∧ targetVal = 42 := by",
                "  sorry -- main_tgt",
                "theorem multi_sorry : 1 = 1 ∧ 2 = 2 := by",
                "  constructor",
                "  · sorry -- first_sorry",
                "  · sorry",
                "theorem inline_pair : 1 = 1 ∧ 2 = 2 := by",
                "  exact ⟨by sorry, by sorry⟩ -- pair_tgt",
                "theorem prior_err_decl : 1 = 1 := by",
                "  bogus_prior",
                "  sorry -- prior_tgt",
                "theorem term_demo : 1 = 1 := sorry -- term_tgt",
                "namespace NS",
                "protected theorem prot_ok : 1 = 1 := by",
                "  sorry -- prot_tgt",
                "end NS",
                "theorem have_inline : 1 = 1 := by",
                "  have h : 2 = 2 := by sorry",
                "  exact rfl",
                "def astral_demo : Nat := by",
                '  let _ := "\U00010348"; exact targetVal -- astral_line',
                "def «sorry» : Nat := 1",
                "def «admit» : Nat := 2",
                "theorem root_sorryax_demo : False := «_root_».sorryAx _ false -- rsax_tgt",
                'def neg_str_demo : Bool := !"{".isEmpty',
                "theorem after_neg_demo : 1 = 1 := by",
                "  sorry -- after_neg_tgt",
                'def lit_sorry_demo : String := "sorry"',
            ]
            body = "\n".join(lines) + "\n"
            lean_file.write_text(body, encoding="utf-8")
            ln = lambda pat: next(i for i, txt in enumerate(lines, 1) if pat in txt)

            if sys.platform.startswith("linux") and os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.assertTrue(_bwrap_usable())
            use_sbx = _bwrap_usable()
            live_env = _scrubbed_env({"ANNEAL_LEAN": str(lean_bin)})
            with mock.patch.dict(os.environ, live_env, clear=True):
                pool = WorkspacePool(sandbox=use_sbx)
                try:
                    d1 = pool.diagnostics(str(lean_file), artifacts_dir=art)
                    d2 = pool.diagnostics(str(lean_file), artifacts_dir=art)
                    self.assertEqual(d1["server_pid"], d2["server_pid"])
                    self.assertEqual(d1["sandboxed"], use_sbx)
                    self.assertTrue(d1["completed"])
                    s_goals = [g for g in d1["sorry_goals"] if g["line"] == ln("main_tgt")][0]
                    self.assertIn("targetVal = 42", s_goals["goals"][0])
                    p_goals = [g for g in d1["sorry_goals"] if g["line"] == ln("pair_tgt")]
                    self.assertEqual(len(p_goals), 2)
                    self.assertIn("1 = 1", p_goals[0]["goals"][0])
                    self.assertIn("2 = 2", p_goals[1]["goals"][0])
                    self.assertEqual(d1["sorry_count"], 11)
                    self.assertIn(ln("rsax_tgt"), d1["sorry_lines"])
                    self.assertIn(ln("after_neg_tgt"), d1["sorry_lines"])
                    self.assertIn("targetVal = 42", d1["text"])
                    mcp_d = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 88, "method": "tools/call",
                        "params": {
                            "name": "lean_diagnostics",
                            "arguments": {"file": str(lean_file), "artifacts_dir": str(art)},
                        },
                    })
                    assert mcp_d is not None
                    self.assertIn("targetVal = 42", mcp_d["result"]["content"][0]["text"])

                    g = pool.goal(str(lean_file), ln("main_tgt"), artifacts_dir=art)
                    self.assertIn("targetVal = 42", "\n".join(g["goals_before"]))
                    ga = pool.goal(
                        str(lean_file), ln("astral_line"),
                        snippet="exact targetVal", artifacts_dir=art,
                    )
                    self.assertIn("Nat", "\n".join(ga["goals_focus"]))

                    ma = pool.multi_attempt(
                        str(lean_file), ln("main_tgt"),
                        ["sorry", "rfl", "constructor", "exact ⟨Nat.add_zero n, rfl⟩"],
                        artifacts_dir=art,
                    )["attempts"]
                    self.assertTrue(ma[0]["uses_sorry"] and not ma[0]["closes_goal"])
                    self.assertFalse(ma[1]["closes_goal"])
                    self.assertTrue(ma[2]["ok_step"] and not ma[2]["closes_goal"])
                    self.assertTrue(ma[3]["closes_goal"])
                    rsax_att = pool.multi_attempt(
                        str(lean_file), ln("after_neg_tgt"),
                        ["exact «_root_».sorryAx _ false"], artifacts_dir=art,
                    )["attempts"][0]
                    self.assertTrue(rsax_att["uses_sorry"] and not rsax_att["closes_goal"])

                    pe = pool.multi_attempt(
                        str(lean_file), ln("prior_tgt"), ["rfl"], artifacts_dir=art
                    )["attempts"][0]
                    self.assertFalse(pe["evaluated"])
                    for tag in ("term_tgt", "prot_tgt", "have h :"):
                        att = pool.multi_attempt(
                            str(lean_file), ln(tag), ["rfl"], artifacts_dir=art
                        )["attempts"][0]
                        self.assertTrue(att["closes_goal"], (tag, att))
                    for tag in ("first_sorry", "pair_tgt"):
                        inc_res = pool.multi_attempt(
                            str(lean_file), ln(tag), ["rfl"], artifacts_dir=art
                        )
                        inc_att = inc_res["attempts"][0]
                        self.assertTrue(inc_att["uses_sorry"] and not inc_att["closes_goal"], tag)
                        self.assertIn("INCOMPLETE", inc_res["text"])

                    hv_live = pool.hover(
                        str(lean_file), ln("astral_line"), symbol="targetVal", artifacts_dir=art
                    )
                    self.assertIn("Nat", hv_live["hover"])
                    df = pool.definition(
                        str(lean_file), ln("main_tgt") - 1, symbol="targetVal", artifacts_dir=art
                    )
                    self.assertTrue(any("Spec.lean" in loc["file"] for loc in df["locations"]))
                    comp = pool.completions(str(lean_file), ln("main_tgt"), artifacts_dir=art)
                    self.assertIsInstance(comp["items"], list)
                    outl = pool.outline(str(lean_file), artifacts_dir=art)
                    self.assertTrue(any(s["name"] == "add_zero_demo" for s in outl["symbols"]))
                    sr_live = pool.local_search("add_zero", workspace=str(unit))
                    self.assertTrue(any(m["name"] == "add_zero_demo" for m in sr_live["matches"]))

                    crash_eval = unit / "CrashEval.lean"
                    crash_body = (
                        "unsafe def bad : String := unsafeCast (1 : Nat)\n"
                        "#eval bad.length\n"
                        "theorem crash_after : 1 = 1 := by\n  sorry\n"
                        if sys.platform == "win32"
                        else "#eval show IO Unit from do\n"
                        '  let _ ← IO.Process.output '
                        '{ cmd := "/bin/sh", args := #["-c", "kill -9 $PPID"] }\n'
                        "theorem crash_after : 1 = 1 := by\n  sorry\n"
                    )
                    crash_eval.write_text(crash_body, encoding="utf-8")
                    live_cr = pool.diagnostics(str(crash_eval))
                    self.assertFalse(live_cr["completed"] or live_cr["timed_out"], live_cr)
                    self.assertGreaterEqual(live_cr["error_count"], 1, live_cr)
                    self.assertEqual(live_cr["sorry_goals"], [], live_cr)
                    live_g_cr = pool.goal(str(crash_eval), 3)
                    self.assertFalse(live_g_cr["completed"] or live_g_cr["timed_out"], live_g_cr)
                    self.assertLess(live_g_cr["elapsed_ms"], 2000.0)
                    live_h_cr = pool.hover(str(crash_eval), 3)
                    self.assertFalse(live_h_cr["completed"] or live_h_cr["timed_out"], live_h_cr)
                    live_ma_cr = pool.multi_attempt(str(crash_eval), 4, ["rfl"])
                    self.assertFalse(live_ma_cr["attempts"][0]["evaluated"], live_ma_cr)
                    crash_eval.write_text(
                        "theorem crash_after : 1 = 1 := by\n  rfl\n", encoding="utf-8"
                    )
                    live_rec = pool.diagnostics(str(crash_eval))
                    self.assertTrue(live_rec["completed"] and not live_rec["timed_out"], live_rec)
                    self.assertEqual(live_rec["error_count"], 0, live_rec)

                    if _bwrap_usable():
                        d_env = _scrubbed_env({
                            "ANNEAL_LEAN": str(lean_bin),
                            "ANNEAL_LSP_SOCKET": str(root / "live_d/lsp.sock"),
                            "ANNEAL_LSP_ARTIFACTS": str(art),
                        })
                        try:
                            out = subprocess.check_output(
                                [sys.executable, "-B", str(_CI_DIR / "anneal-lsp"), "--json", "try",
                                 str(lean_file), str(ln("term_tgt")), "rfl"],
                                cwd=str(unit), text=True, env=d_env, timeout=30,
                            )
                            self.assertTrue(json.loads(out)["attempts"][0]["closes_goal"])
                        finally:
                            subprocess.run(
                                [sys.executable, "-B", str(_CI_DIR / "anneal-lsp"), "stop-daemon"],
                                cwd=str(unit), env=d_env, capture_output=True, timeout=10,
                            )
                    self.assertEqual(lean_file.read_text(encoding="utf-8"), body)
                    self.assertFalse((unit / ".lake").exists())
                finally:
                    pool.shutdown()

                if (lean_bin.parent / "lake").is_file():
                    lk = root / "lake_demo"
                    lk.mkdir()
                    (lk / "lakefile.toml").write_text(
                        'name = "demo"\ndefaultTargets = ["Demo"]\n'
                        '[[lean_lib]]\nname = "Demo"\n',
                        encoding="utf-8",
                    )
                    (lk / "Demo.lean").write_text(
                        "theorem lake_ok : 1 = 1 := by\n  sorry\n", "utf-8"
                    )
                    lk_pool = WorkspacePool(sandbox=False)
                    try:
                        self.assertEqual(lk_pool.diagnostics(str(lk / "Demo.lean"))["mode"], "lake")
                        lk_att = lk_pool.multi_attempt(
                            str(lk / "Demo.lean"), 2, ["rfl"]
                        )["attempts"][0]
                        self.assertTrue(lk_att["closes_goal"])
                    finally:
                        lk_pool.shutdown()
