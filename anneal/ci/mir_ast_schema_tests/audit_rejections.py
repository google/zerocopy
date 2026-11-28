# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`Trusted.MirAst` schema tests for the audit's rejection of security-critical
and generic defaults."""

from __future__ import annotations

from .support import (
    audit_mir_ast_sources,
)


class AuditRejectionCases:
    """`MirAstSchemaTests` methods for the audit's rejection of security-
    critical and generic defaults."""

    def test_audit_rejects_security_critical_and_generic_defaults(self) -> None:
        base = self._load_live_sources()
        for label, filename, old, new, expected_msg in (
            (
                "program_scope_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope := .unit",
                "unexpected default on `Program.scope`",
            ),
            (
                "program_profile_default",
                "Body.lean",
                "  mirProfileVersion : Nat",
                "  mirProfileVersion : Nat := 1",
                "unexpected default on `Program.mirProfileVersion`",
            ),
            (
                "type_omitted_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  sneaky := (0 : Nat)",
                "unexpected default on `Program.sneaky`",
            ),
            (
                "binder_form_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  (binderDef : Nat := 0)",
                "unexpected default on `Program.binderDef`",
            ),
            (
                "multi_binder_line_default",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  (isUnsafe : Bool) (sneakyBypass : Bool := false)",
                "unexpected default on `Body.sneakyBypass`",
            ),
            (
                "header_binder_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ParamStruct (bad : Bool := true) where\n  x : Nat",
                "forbidden default in `structure` header",
            ),
            (
                "col0_field_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure Evil where\nbad : Nat := 1",
                "unexpected column-0 line in `Evil`",
            ),
            (
                "col0_switchtargets_field",
                "Terminators.lean",
                "  otherwise : BasicBlockId",
                "otherwise : BasicBlockId\nevilDefault : Nat := 42",
                "unexpected column-0 line in `SwitchTargets`",
            ),
            (
                "block_comment_prefixed_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "  /-\n  note\n  -/sneakyField : Bool := true",
                "unexpected default on `Program.sneakyField`",
            ),
            (
                "char_literal_quote_in_lean",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                "def quoteChar : Char := '\"' -- c\n"
                "structure AfterChar where\n  bad : Bool := true",
                "unexpected default on `AfterChar.bad`",
            ),
            (
                "extends_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ExtTest extends Foo where\n  bad : Nat := 1",
                "forbidden `extends` in `structure` header",
            ),
            (
                "extends_external_parent_rejected",
                "Body.lean",
                "structure Program where",
                "structure Program extends Trusted.Other.ProgramDefaults where",
                "forbidden `extends` in `structure` header",
            ),
            (
                "extends_basicblock_inherited_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure Wrapped extends BasicBlock where\n  x : Nat",
                "forbidden `extends` in `structure` header",
            ),
            (
                "generic_default_paren",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Bool := (default)",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "generic_default_qualified",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\n"
                "def badDefault : Bool := Inhabited.default",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "generic_default_anon_ctor",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Box := ⟨default⟩",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "ctor_double_colon_rejected",
                "Places.lean",
                "  projection : List ProjectionElem := []",
                "  projection :: sneaky : List ProjectionElem := []",
                "unparsed line in `Place`",
            ),
            (
                "private_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "@[ext] private structure PrivTest where\n  bad : Nat := 1",
                "unexpected default on `PrivTest.bad`",
            ),
            (
                "public_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "public structure PubTest where\n  bad : Nat := 1",
                "unexpected default on `PubTest.bad`",
            ),
            (
                "unknown_modifier_fails_closed",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "future_mod structure FutTest where\n  x : Nat",
                "unparsed `structure` declaration",
            ),
            (
                "body_is_unsafe_flipped_true",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  isUnsafe : Bool := true",
                "allowlisted `Body.isUnsafe` default changed",
            ),
            (
                "multiline_default_continuation",
                "Body.lean",
                "  entryDefId : DefId := 0",
                "  entryDefId : DefId := 0\n    + 1",
                "unparsed line in `Program`",
            ),
            (
                "class_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "class ClsTest where\n  bad : Nat := 1",
                "unexpected default on `ClsTest.bad`",
            ),
            (
                "unparsed_structure_header",
                "Body.lean",
                "structure Program where",
                "structure Program\nwhere",
                "unparsed `structure` declaration",
            ),
            (
                "enum_ty_id_default",
                "Types.lean",
                "  id : Nat",
                "  id : Nat := 0",
                "unexpected default on `EnumTy.id`",
            ),
            (
                "generic_default_keyword",
                "Body.lean",
                "  cleanup : Bool := false",
                "  cleanup : Bool := default",
                "forbidden `:= default`",
            ),
            (
                "stale_allowlist_entry",
                "Body.lean",
                "  cleanup : Bool := false",
                "  cleanup : Bool",
                "stale ALLOWED_DEFAULT_FIELDS entries",
            ),
            (
                "undocumented_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  extra : Nat := 0",
                "unexpected default on `Program.extra`",
            ),
            (
                "duplicate_struct_across_namespaces_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "namespace A\nstructure Dup where\n  bad : Nat := 1\nend A\n"
                "namespace B\nstructure Dup where\n  ok : Nat\nend B",
                "unexpected default on `Dup.bad`",
            ),
            (
                "duplicate_struct_across_namespaces_rejected",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "namespace A\nstructure Dup where\n  bad : Nat := 1\nend A\n"
                "namespace B\nstructure Dup where\n  ok : Nat\nend B",
                "duplicate `structure` declaration `Dup`",
            ),
            (
                "duplicate_program_in_other_file_missing_scope",
                "Types.lean",
                "  id : Nat",
                "  id : Nat\n"
                "end Trusted.MirAst\nnamespace Shadow\n"
                "structure Program where\n  extra : Nat",
                "missing required field `Program.scope`",
            ),
            (
                "optparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : optParam VerificationScope .unit",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "autoparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : autoParam VerificationScope myTac",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "optparam_binder_default",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  (isUnsafe : Bool := false) "
                "(sneaky : optParam Bool false)",
                "forbidden `optParam`/`autoParam` default on `Body.sneaky`",
            ),
            (
                "header_optparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ParamStruct (x : optParam Nat 0) where\n  y : Nat",
                "forbidden `optParam`/`autoParam`",
            ),
            (
                "inductive_ctor_default",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup (block : BasicBlockId := 0)",
                "forbidden default in `inductive` `UnwindAction`",
            ),
            (
                "inductive_ctor_optparam",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup (block : optParam BasicBlockId 0)",
                "forbidden `optParam`/`autoParam`",
            ),
            (
                "inductive_header_default",
                "Body.lean",
                "inductive VerificationScope where",
                "inductive VerificationScope (x : Nat := 0) where",
                "forbidden default in `inductive` `VerificationScope`",
            ),
            (
                "inductive_multiline_ctor_default",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup\n  (block : BasicBlockId := 0)",
                "forbidden default in `inductive` `UnwindAction`",
            ),
            (
                "col0_lemma_field_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\nlemma : Nat := 1",
                "unexpected column-0 line in `Program`",
            ),
            (
                "raw_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def rawEsc : String := r#"\\"#\n'
                'def blockHint : String := " /- "\n'
                "structure AfterRaw where\n  bad : Nat := 1",
                "unexpected default on `AfterRaw.bad`",
            ),
            (
                "zero_hash_raw_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def rawZero : String := r"\\"\n'
                'def blockHint : String := " /- "\n'
                "structure AfterRawZero where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterRawZero.bad`",
            ),
            (
                "s_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def interp : String := s!"hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterInterp where\n  bad : Nat := 1",
                "unexpected default on `AfterInterp.bad`",
            ),
            (
                "f_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def fInterp : String := f!"hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterFInterp where\n  bad : Nat := 1",
                "unexpected default on `AfterFInterp.bad`",
            ),
            (
                "prefix_bool_not_before_brace_string",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def b : Bool := !"{".isEmpty\n'
                'def c : String := " /- "\n'
                "structure AfterNot where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterNot.bad`",
            ),
            (
                "panic_macro_with_brace_not_interp",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def p : Nat := panic!"a {"\n'
                'def c : String := " /- "\n'
                "structure AfterPanic where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterPanic.bad`",
            ),
            (
                "guillemet_identifier_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def «/-» : Nat := 0\n'
                'def «"» : Nat := 0\n'
                "structure AfterGuillemet where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterGuillemet.bad`",
            ),
            (
                "unterminated_guillemet_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badGuillemet := «/-",
                "unterminated Lean guillemet identifier at EOF",
            ),
            (
                "spaced_s_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def sSp : String := s! /- " -/ "hi { -- {\n'
                '  "x" } /- "\n'
                "structure AfterSpacedS where\n  bad : Nat := 1",
                "unexpected default on `AfterSpacedS.bad`",
            ),
            (
                "spaced_f_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def fSp : Std.Format := f! "hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterSpacedF where\n  bad : Nat := 1",
                "unexpected default on `AfterSpacedF.bad`",
            ),
            (
                "double_lbrace_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def dbl : String := s!"{{ x := "a /- b" : Box }}"\n'
                "structure AfterDblBrace where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterDblBrace.bad`",
            ),
            (
                "escaped_lbrace_interp_string_preserved",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def esc : String := s!"\\{"\n'
                'def c : String := " /- "\n'
                "structure AfterEscBrace where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterEscBrace.bad`",
            ),
            (
                "guillemet_optparam_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : «optParam» VerificationScope .unit",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "guillemet_autoparam_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : «autoParam» VerificationScope myTac",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "guillemet_optparam_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : «optParam» Bool true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "guillemet_optparam_inductive",
                "Body.lean",
                "inductive VerificationScope where",
                "inductive VerificationScope where\n"
                "  | bogus (bad : «optParam» Nat 0)",
                "forbidden `optParam`/`autoParam` in Trusted.MirAst",
            ),
            (
                "guillemet_generic_default",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Bool := «default»",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "unterminated_block_comment_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\n/- unterminated",
                "unterminated Lean string/comment state at EOF",
            ),
            (
                "unterminated_interp_string_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                'end Trusted.MirAst\ndef badStr := s!"hi {',
                "unterminated Lean string/comment state at EOF",
            ),
            (
                "variable_single_line_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : Bool := true)\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_multiline_default_after_struct",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "variable\n"
                "  (bad : Bool := true)\n"
                "inductive AfterVar where | ok",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_continuation_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (good : Bool)\n"
                "(bad : Bool := true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_after_bare_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable\n"
                "(bad : Bool := true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_multiline_binder_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : Bool\n"
                ":= true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_optparam_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : optParam Bool true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "open_in_variable_single_line",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "open Trusted.MirAst in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "open_in_variable_multiline",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "open Trusted.MirAst in variable\n"
                "  (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "set_option_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "set_option autoImplicit false in "
                "variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "omit_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "omit [Inhabited Nat] in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "include_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "include x in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "umbrella_module_structure_default",
                "MirAst.lean",
                "public import Trusted.MirAst.Body",
                "public import Trusted.MirAst.Body\n"
                "structure UmbrellaBad where\n  bad : Nat := 1",
                "unexpected default on `UmbrellaBad.bad`",
            ),
        ):
            with self.subTest(case=label):
                mutated = dict(base)
                self.assertIn(old, mutated[filename])
                mutated[filename] = mutated[filename].replace(old, new, 1)
                errors = audit_mir_ast_sources(mutated)
                self.assertTrue(
                    any(expected_msg in e for e in errors),
                    f"{label}: expected {expected_msg!r} in {errors!r}",
                )

        with_ok_var = dict(base)
        with_ok_var["Body.lean"] = with_ok_var["Body.lean"].replace(
            "namespace Trusted.MirAst",
            "namespace Trusted.MirAst\n"
            "variable (good : Bool)\n"
            "(alsoGood : Nat)\n"
            "def okHelper : Nat := 0",
            1,
        )
        self.assertEqual(audit_mir_ast_sources(with_ok_var), [])

        with_sub = dict(base)
        with_sub["Sub/Extra.lean"] = (
            "namespace Trusted.MirAst\n"
            "structure SubStruct where\n"
            "  bad : Nat := 1\n"
            "end Trusted.MirAst\n"
        )
        sub_errors = audit_mir_ast_sources(with_sub)
        self.assertTrue(
            any(
                "Sub/Extra.lean" in e and "SubStruct.bad" in e
                for e in sub_errors
            ),
            sub_errors,
        )
