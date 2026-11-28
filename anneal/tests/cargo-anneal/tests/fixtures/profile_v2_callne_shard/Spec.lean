-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def tagNeIdentity : String :=
  "rust-path-v1::tag_ne"

/-- `tag_ne(x, y)` (`x != y`) returns `true` exactly when `x` and `y` are
different `Tag` variants, so `tag_ne(Tag::A, Tag::A)` returns `false`.

`x != y` is a `callNe` into `<Tag as PartialEq>::eq`. The crate has more than
`shard_min_bodies` bodies, so capture shards it, and sharding reorders the
bodies: `tag_ne` lands at index 20, which the identity conjunct pins. If the
`callNe` still pointed at its pre-reorder callee index, it would reach
`<Tag as AaaFake>::fake_eq`, which always returns `false`, and `tag_ne` would
return `true` for equal tags. -/
def tagNePost (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 20 with
  | none => False
  | some body =>
    body.identity = tagNeIdentity ∧
    ∀ q : Query,
      ValidEntryArgsV2 body q →
      match q.args with
      | [.enumVal _ x, .enumVal _ y] =>
        BehaviorV2 (entryProgForBody p 20) q
          (TerminalOut.returned ⟨.bool (!(Nat.beq x y)), q.callerMem⟩)
      | _ => False

def property (p : Program) : Prop :=
  tagNePost p

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
