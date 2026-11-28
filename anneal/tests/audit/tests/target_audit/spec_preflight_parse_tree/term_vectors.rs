// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Negative `"spec-preflight"` vectors for terms, panicking helpers,
//! auto-bound implicits, `do` loops, and declaration namespaces.

/// Returns `(label, snippet, expected reason)` rows, in table order, that
/// follow [`super::command_vectors::vectors`].
pub(super) fn vectors() -> &'static [(&'static str, &'static str, &'static str)] {
    &[
        (
            "term-include-str",
            "def s := include_str \"foo\"\n",
            "disallowed syntax Lean.includeStr",
        ),
        (
            "term-by-elab",
            "def e : Nat := by_elab return 0\n",
            "disallowed syntax Lean.byElab",
        ),
        (
            "term-sorry",
            "def s : Nat := sorry\n",
            "disallowed syntax Lean.Parser.Term.sorry",
        ),
        (
            "term-dbg-trace",
            "def d : Nat := dbg_trace \"hi\"; 0\n",
            "disallowed syntax Lean.Parser.Term.dbgTrace",
        ),
        (
            "term-decl-name",
            "def f := decl_name%\n",
            "disallowed syntax Lean.Parser.Term.declName",
        ),
        (
            "term-quot",
            "def q := `(1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.quot",
        ),
        (
            "term-dyn-quot",
            "def dq := `(term| 1 + 2)\n",
            "disallowed syntax Lean.Parser.Term.dynamicQuot",
        ),
        (
            "auto-param-exploit",
            "universe u\n\
             def idAt {α : Sort u} (_f : α → Prop) (a : α) : α := a\n\
             def myTac := idAt (fun s => autoParam True s)\n\
               (.node .none `Lean.Parser.Tactic.tacticSeq #[\n\
                 .node .none `Lean.Parser.Tactic.tacticSeq1Indented #[\n\
                   .node .none `null #[\n\
                     .node .none `Lean.Parser.Tactic.tacticSorry #[.atom .none \"sorry\"]]]])\n\
             theorem evil (h : autoParam False myTac) : False := h\n",
            "disallowed identifier autoParam",
        ),
        (
            "quoted-name",
            "def qn := `foo\n",
            "disallowed syntax Lean.Parser.Term.quotedName",
        ),
        (
            "double-quoted-name",
            "def dqn := ``Nat.add\n",
            "disallowed syntax Lean.Parser.Term.doubleQuotedName",
        ),
        (
            "binder-tactic",
            "def half (n : Nat) (h : n > 0 := by omega) : Nat := n / 2\n",
            "disallowed syntax Lean.Parser.Term.binderTactic",
        ),
        (
            "scoped-instance",
            "namespace N\nscoped instance : Inhabited Unit := ⟨()⟩\nend N\n",
            "disallowed modifier Lean.Parser.Term.scoped",
        ),
        (
            "term-mod-cast",
            "theorem mc (n : Nat) : (n : Int) = (n : Int) := mod_cast (rfl : n = n)\n",
            "disallowed syntax Lean.modCast",
        ),
        (
            "term-panic",
            "def p : Nat := panic! \"boom\"\n",
            "disallowed syntax Lean.Parser.Term.panic",
        ),
        (
            "term-unreachable",
            "def u : Nat := unreachable!\n",
            "disallowed syntax Lean.Parser.Term.unreachable",
        ),
        (
            "term-assert",
            "def a : Nat := assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.assert",
        ),
        (
            "term-debug-assert",
            "def da : Nat := debug_assert! true; 0\n",
            "disallowed syntax Lean.Parser.Term.debugAssert",
        ),
        (
            "direct-panic-core",
            "def pc : Nat := panicCore \"boom\"\n",
            "disallowed identifier panicCore",
        ),
        (
            "contract-decl-val",
            "def contracted (n : Nat) : Nat\n\
             requires True\n\
             ensures _ => True\n\
             := n\n",
            "disallowed syntax Lean.Parser.Command.contractDeclVal",
        ),
        (
            "term-qed-try",
            "theorem t : True := ∎\n",
            "disallowed syntax «term∎»",
        ),
        (
            "opt-auto-implicit-true",
            "set_option autoImplicit true\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-auto-implicit-false",
            "set_option autoImplicit false\n",
            "unsupported option autoImplicit",
        ),
        (
            "opt-relaxed-auto-implicit-true",
            "set_option relaxedAutoImplicit true\n",
            "unsupported option relaxedAutoImplicit",
        ),
        (
            "term-opt-auto-implicit-true",
            "def x : Nat := set_option autoImplicit true in 0\n",
            "unsupported option autoImplicit",
        ),
        (
            "cmd-in-opt-auto-implicit-true",
            "set_option autoImplicit true in\ndef x (n : Nat) : pre_ok → True := fun _ => trivial\n",
            "unsupported option autoImplicit",
        ),
        (
            "term-get-elem-bang",
            "def x : Nat := (#[] : Array Nat)[0]!\n",
            "disallowed syntax «term__[_]_!»",
        ),
        (
            "ident-list-head-bang",
            "def x : Nat := ([] : List Nat).head!\n",
            "disallowed identifier head!",
        ),
        (
            "ident-option-get-bang",
            "def x : Nat := (none : Option Nat).get!\n",
            "disallowed identifier get!",
        ),
        (
            "ident-get-elem-bang-qual",
            "def x : Nat := GetElem?.getElem! (#[] : Array Nat) 0\n",
            "disallowed identifier GetElem?.getElem!",
        ),
        (
            "ident-out-of-bounds",
            "def x : Nat := outOfBounds\n",
            "disallowed identifier outOfBounds",
        ),
        (
            "ident-pos-slice-or-panic",
            "def x := @String.Pos.sliceOrPanic\n",
            "disallowed identifier String.Pos.sliceOrPanic",
        ),
        (
            "ident-slice-pos-slice-or-panic",
            "def x := @String.Slice.Pos.sliceOrPanic\n",
            "disallowed identifier String.Slice.Pos.sliceOrPanic",
        ),
        (
            "proj-slice-or-panic",
            "def x (s : String) (pos : s.Pos) (h : pos ≤ pos) := pos.sliceOrPanic pos pos (h := h)\n",
            "disallowed identifier pos.sliceOrPanic",
        ),
        (
            "open-only-head-bang",
            "open List (head!)\n",
            "invalid open item head!",
        ),
        (
            "export-head-bang",
            "export List (head!)\n",
            "invalid export item head!",
        ),
        (
            "open-renaming-head-bang",
            "open List renaming head! -> safeHead\n",
            "invalid open renaming item head! -> safeHead",
        ),
        (
            "open-renaming-slice-or-panic",
            "open String.Slice renaming Pos.sliceOrPanic -> safeSlice\n",
            "invalid open renaming item Pos.sliceOrPanic -> safeSlice",
        ),
        (
            "do-while",
            "def x : Nat := Id.run do\n  let mut i := 5\n  while i > 0 do\n    i := i - 1\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doWhile",
        ),
        (
            "do-repeat",
            "def x : Nat := Id.run do\n  repeat\n    break\n  return 0\n",
            "disallowed syntax Lean.Parser.Term.doRepeat",
        ),
        (
            "do-repeat-until",
            "def x : Nat := Id.run do\n  let mut i := 0\n  repeat\n    i := i + 1\n  until i > 0\n  return i\n",
            "disallowed syntax Lean.Parser.Term.doRepeatUntil",
        ),
        (
            "ident-repeat-m",
            "def x := repeatM\n",
            "disallowed identifier repeatM",
        ),
        // Declaration-namespace guards: entering or declaring under the
        // `Trusted`/`Anneal`/`Proof` roots, every `reservedKernelRoots` root
        // (including `Init` and `Std`), and the `forbiddenSysUvPrefixes`
        // sub-scopes (which an earlier reference guard may reject first),
        // with `_root_` stripped.
        (
            "ns-trusted",
            "namespace Trusted\nend Trusted\n",
            "cannot enter reserved namespace Trusted",
        ),
        (
            "ns-anneal",
            "namespace Anneal\nend Anneal\n",
            "cannot enter reserved namespace Anneal",
        ),
        (
            "ns-proof",
            "namespace Proof\nend Proof\n",
            "cannot enter reserved namespace Proof",
        ),
        (
            "ns-nat",
            "namespace Nat\nend Nat\n",
            "cannot enter reserved namespace Nat",
        ),
        (
            "ns-init",
            "namespace Init\nend Init\n",
            "cannot enter reserved namespace Init",
        ),
        (
            "ns-std",
            "namespace Std\nend Std\n",
            "cannot enter reserved namespace Std",
        ),
        (
            "ns-internal-uv",
            "namespace Internal.UV\nend Internal.UV\n",
            "Internal.UV",
        ),
        (
            "ns-dynlib",
            "namespace Dynlib\nend Dynlib\n",
            "Dynlib",
        ),
        (
            "ns-root-trusted",
            "namespace _root_.Trusted\nend _root_.Trusted\n",
            "_root_.Trusted",
        ),
        (
            "decl-bare-nat",
            "def Nat : Nat := 0\n",
            "cannot declare reserved namespace Nat",
        ),
        (
            "decl-in-std",
            "def Std.evil : Nat := 0\n",
            "cannot declare in reserved namespace Std",
        ),
        (
            "decl-in-internal-uv",
            "def Internal.UV.evil : Nat := 0\n",
            "Internal.UV",
        ),
    ]
}
