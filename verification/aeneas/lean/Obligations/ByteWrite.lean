/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Zerocopy
public import Rust.Bytes
@[expose] public section
open Aeneas Aeneas.Std
namespace Zerocopy.Obligations

-- Retain all raw inputs, including unsuccessful and empty writes. These
-- expectations are independent of the specification macro and its decoders.
def write_exact_spec_contract (src dst : Slice U8)
    (run : Result (Bool × Slice U8)) : Prop :=
  run ⦃ out => out.1 = decide (src.val.length = dst.val.length) ∧
    out.2.val = if src.val.length = dst.val.length then src.val else dst.val ⦄

def write_prefix_spec_contract (src dst : Slice U8)
    (run : Result (Bool × Slice U8)) : Prop :=
  run ⦃ out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then src.val ++ dst.val.drop src.val.length else dst.val ⦄

def write_suffix_spec_contract (src dst : Slice U8)
    (run : Result (Bool × Slice U8)) : Prop :=
  run ⦃ out => out.1 = decide (src.val.length ≤ dst.val.length) ∧
    out.2.val = if src.val.length ≤ dst.val.length
      then dst.val.take (dst.val.length - src.val.length) ++ src.val else dst.val ⦄

def write_exact_spec : Prop :=
  ∀ src dst, write_exact_spec_contract src dst (util.bytewrite.exact src dst)
def write_prefix_spec : Prop :=
  ∀ src dst, write_prefix_spec_contract src dst (util.bytewrite.prefix src dst)
def write_suffix_spec : Prop :=
  ∀ src dst, write_suffix_spec_contract src dst (util.bytewrite.suffix src dst)

def write_be_word_prefix_spec_contract (n : U16) (dst : Slice U8)
    (run : Result (Bool × Slice U8)) : Prop :=
  run ⦃ out => out.1 = decide (2 ≤ dst.val.length) ∧
    out.2.val.map U8.bv = if 2 ≤ dst.val.length
      then Rust.Bytes.encodeBE 2 n.val ++ (dst.val.drop 2).map U8.bv
      else dst.val.map U8.bv ⦄
def write_be_word_prefix_spec : Prop :=
  ∀ n dst, write_be_word_prefix_spec_contract n dst (util.bytewrite.be_word_prefix n dst)

end Zerocopy.Obligations
