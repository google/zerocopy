// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Negative `"spec-preflight"` vectors for commands, modifiers,
//! namespaces, references, attributes, options, and tactics.

/// Returns `(label, snippet, expected reason)` rows, in table order, that
/// precede [`super::term_vectors::vectors`].
pub(super) fn vectors() -> &'static [(&'static str, &'static str, &'static str)] {
    &[
        ("eval-cmd", "#eval 1\n", "unsupported command"),
        (
            "axiom-decl",
            "axiom badAx : True\n",
            "unsupported declaration kind",
        ),
        (
            "opaque-decl",
            "opaque badOp : Nat := 0\n",
            "unsupported declaration kind",
        ),
        (
            "example-decl",
            "example : True := trivial\n",
            "unsupported declaration kind",
        ),
        (
            "macro-cmd",
            "macro \"m\" : term => `(0)\n",
            "unsupported command",
        ),
        (
            "syntax-cmd",
            "syntax \"mykw\" : term\n",
            "unsupported command",
        ),
        ("init-cmd", "initialize pure ()\n", "unsupported command"),
        (
            "notation-cmd",
            "notation \"x99\" => 1\n",
            "unsupported command",
        ),
        (
            "in-bad-lhs",
            "namespace N in def f : Nat := 0\n",
            "unsupported command on LHS of `in`",
        ),
        (
            "in-bad-rhs",
            "open Nat in namespace N\n",
            "unsupported command inside `in`",
        ),
        (
            "mutual-nested-sec",
            "mutual\nsection S\nend S\nend\n",
            "unsupported mutual-block shape",
        ),
        (
            "partial-def",
            "partial def p (n : Nat) : Nat := p n\n",
            "unsupported declaration modifier",
        ),
        (
            "unsafe-def",
            "unsafe def u : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "meta-def",
            "meta def m : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "public-def",
            "public def pub : Nat := 0\n",
            "unsupported declaration modifier",
        ),
        (
            "term-unsafe",
            "def u2 : Nat := unsafe 0\n",
            "disallowed modifier",
        ),
        (
            "public-section",
            "public section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "meta-section",
            "meta section S\nend S\n",
            "unsupported section/namespace modifier",
        ),
        (
            "partial-fixpoint",
            "def pf (n : Nat) : Nat := pf n\npartial_fixpoint\n",
            "disallowed modifier",
        ),
        (
            "unsafe-rec-ident",
            "def foo._unsafe_rec : Nat := 0\n",
            "_unsafe_rec",
        ),
        ("open-io", "open IO\n", "forbidden namespace IO"),
        ("open-lean", "open Lean\n", "forbidden namespace Lean"),
        ("open-lake", "open Lake\n", "forbidden namespace Lake"),
        ("open-system", "open System\n", "forbidden namespace System"),
        (
            "open-platform-all",
            "open System.Platform\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-platform-target",
            "open System.Platform (target)\n",
            "disallowed open item System.Platform.target",
        ),
        (
            "open-platform-hiding",
            "open System.Platform hiding target\n",
            "forbidden namespace System.Platform",
        ),
        (
            "open-scoped-io",
            "open scoped IO\n",
            "forbidden namespace IO",
        ),
        ("ns-io", "namespace IO\nend IO\n", "disallowed reference IO"),
        (
            "term-open-io",
            "def x : Nat := open IO in 0\n",
            "forbidden namespace IO",
        ),
        (
            "export-platform-target",
            "export System.Platform (target)\n",
            "disallowed export item System.Platform.target",
        ),
        (
            "ref-io",
            "def x := IO.println\n",
            "disallowed reference IO.println",
        ),
        (
            "ref-platform-target",
            "def x := System.Platform.target\n",
            "disallowed reference System.Platform.target",
        ),
        (
            "attr-impl-by",
            "@[implemented_by Nat.add] def f := Nat.add\n",
            "unsupported attribute implemented_by",
        ),
        (
            "attr-extern",
            "@[extern \"c_fn\"] def f (x : Nat) : Nat := x\n",
            "unsupported attribute kind",
        ),
        (
            "attr-csimp",
            "@[csimp] theorem t : Nat.add = Nat.add := rfl\n",
            "unsupported attribute csimp",
        ),
        (
            "attr-scoped-simp",
            "@[scoped simp] theorem t : True := trivial\n",
            "only global or local attributes",
        ),
        (
            "attr-erase-extern",
            "attribute [-extern] Nat.add\n",
            "unsupported attribute removal extern",
        ),
        (
            "deriving-unknown",
            "structure S where\n  x : Nat\nderiving UnknownClass\n",
            "unsupported deriving class",
        ),
        (
            "opt-skip-kernel",
            "set_option debug.skipKernelTC true\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "opt-non-num",
            "set_option maxHeartbeats true\n",
            "requires a numeric literal",
        ),
        (
            "opt-non-bool",
            "set_option linter.unusedVariables 1\n",
            "requires a boolean literal",
        ),
        (
            "term-opt-bad",
            "def x : Nat := set_option debug.skipKernelTC true in 0\n",
            "unsupported option debug.skipKernelTC",
        ),
        (
            "tactic-sorry",
            "theorem t : True := by sorry\n",
            "unsupported tactic",
        ),
        (
            "tactic-admit",
            "theorem t : True := by admit\n",
            "unsupported tactic",
        ),
        (
            "tactic-native-decide",
            "theorem t : 1 = 1 := by native_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-decide-native",
            "theorem t : 1 = 1 := by decide +native\n",
            "unsupported decide config option native",
        ),
        (
            "tactic-decide-valcfg",
            "theorem t : 1 = 1 := by decide (config := { native := true })\n",
            "unsupported decide config",
        ),
        (
            "tactic-bv-decide",
            "theorem t : true = true := by bv_decide\n",
            "unsupported tactic",
        ),
        (
            "tactic-grind",
            "theorem t : 1 = 1 := by grind\n",
            "unsupported tactic",
        ),
        (
            "tactic-rfl-prime",
            "theorem t : 1 = 1 := by rfl'\n",
            "unsupported tactic",
        ),
        (
            "tactic-run-tac",
            "theorem t : True := by run_tac pure ()\n",
            "unsupported tactic",
        ),
        (
            "tactic-open",
            "theorem t : True := by open Nat in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-set-option",
            "theorem t : True := by set_option maxHeartbeats 1 in trivial\n",
            "unsupported tactic",
        ),
        (
            "tactic-conv",
            "theorem t : 1 = 1 := by conv => rfl\n",
            "unsupported tactic",
        ),
    ]
}
