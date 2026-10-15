/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import DropJson

namespace AeneasSpecs.DropJson.Tests

open Lean

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def obj := Json.mkObj
private def arr (xs : List Json) := Json.arr xs.toArray
private def ctor (name : String) (value : Json) := obj [(name, value)]
private def slot (i : Nat) := obj [("kind", ctor "Local" (toJson i)), ("ty", .null)]
private def move (i : Nat) := ctor "Move" (slot i)
private def copy (i : Nat) := ctor "Copy" (slot i)
private def use (operand : Json) := ctor "Use" (arr [operand, .str "Yes"])
private def assign (i : Nat) (rhs : Json) := ctor "Assign" (arr [slot i, rhs])
private def statement (kind : Json) := obj
  [("span", .null), ("kind", kind), ("comments_before", arr [])]
private def block (statements : List Json) (terminator : Json) := obj
  [("statements", arr (statements.map statement)), ("terminator", statement terminator)]
private def goto (i : Nat) := ctor "Goto" (obj [("target", toJson i)])
private def ret := block [] (.str "Return")
private def function := obj [("kind", ctor "Fun" 0), ("generics", .null)]
private def dropped (i : Nat) (normal unwind : Nat) (kind : String := "Conditional") := ctor "Drop"
  (obj [("kind", .str kind), ("place", slot i), ("fn_ptr", function),
    ("target", toJson normal), ("on_unwind", toJson unwind)])
private def called (dest : Nat) (args : List Json) (normal unwind : Nat) := ctor "Call"
  (obj [("call", obj [("func", ctor "Regular" function), ("args", arr args), ("dest", slot dest)]),
    ("target", toJson normal), ("on_unwind", toJson unwind)])
private def declarations := obj [("arg_count", 1), ("locals", arr
  ((List.range 3).map fun i => obj [("index", toJson i), ("name", .null), ("span", .null),
    ("ty", .null), ("drop_flag_for", .null)]))]
private def body (tag : String) (code : Json) := ctor tag (obj
  [("span", .null), ("bound_body_regions", 0), ("locals", declarations),
    ("body", code), ("comments", arr [])])
private def ullbc (blocks : List Json) := body "Unstructured" (arr blocks)
private def projection (i : Nat) := obj
  [("kind", ctor "Projection" (arr [slot i, .str "Deref"])), ("ty", .null)]
private def unitConstant := ctor "Const" (ctor "Untagged"
  (arr [ctor "Adt" (arr [.null, arr []]), .null]))
private def boolConstant := ctor "Untagged" (arr [ctor "Bool" (.bool false), .null])
private def branch (left right : Nat) := ctor "Switch" (obj
  [("data", obj [("scrutinee", ctor "Value" (copy 0)),
    ("branches", arr [arr [boolConstant, 0]]), ("fallback", 1)]),
   ("branches", arr [toJson left, toJson right])])

example : acceptBody (ullbc [block [assign 0 (use (move 1))] (dropped 1 1 1), ret]) = true := by with_unfolding_all rfl
example : acceptBody (ullbc [block [] (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (copy 1))] (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl

-- Assignment restores uncertainty after evaluating every operand, including a
-- self move. A later overwrite has the same conservative effect.
example : acceptBody (ullbc [block [assign 1 (use (move 1))] (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1)), assign 1 (use unitConstant)]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1)), ctor "StorageDead" 1]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1)), ctor "StorageLive" 1]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl

-- Every branch and unwind edge participates, including a call destination
-- whose old value had already been moved away.
example : acceptBody (ullbc [block [] (branch 1 2),
    block [assign 0 (use (move 1))] (goto 3), block [] (goto 3),
    block [] (dropped 1 4 4), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1))] (called 1 [] 1 2), ret,
    block [] (dropped 1 1 1)]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [] (called 0 [move 1] 1 2), ret,
    block [] (dropped 1 1 1)]) = true := by with_unfolding_all rfl

-- Projecting or borrowing the candidate slot is forbidden throughout the
-- complete body, even if an earlier move would otherwise justify its drop.
example : acceptBody (ullbc [block [assign 0 (use (ctor "Move" (projection 1)))]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1)), assign 2 (ctor "Ref"
    (obj [("place", slot 1), ("kind", .str "Shared"), ("ptr_metadata", unitConstant)]))]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1))]
    (dropped 1 1 1 "Precise"), ret]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [block [assign 0 (use (move 1))] (dropped 1 1 1), ret,
    block [] (goto 2)]) = false := by with_unfolding_all rfl
example : acceptBody (ullbc [ret, block [] (dropped 1 0 0)]) = false := by with_unfolding_all rfl

-- Extra executable fields cannot hide an operand from the projection.
example : acceptBody (ullbc [block [assign 0 (obj
    [("Use", arr [move 1, .str "Yes"]), ("hidden", move 2)])]
    (dropped 1 1 1), ret]) = false := by with_unfolding_all rfl

private def structuredStatement (kind : Json) := obj
  [("span", .null), ("id", 0), ("kind", kind), ("comments_before", arr [])]
private def structuredBlock (statements : List Json) := obj
  [("span", .null), ("id", 0), ("statements", arr (statements.map structuredStatement))]
private def llbc (statements : List Json) := body "Structured" (structuredBlock statements)
private def structuredDrop (i : Nat) := ctor "Drop" (obj
  [("kind", .str "Conditional"), ("place", slot i), ("fn_ptr", function),
    ("on_unwind", structuredBlock [.str "UnwindResume"])])

example : acceptBody (llbc [assign 0 (use (move 1)), structuredDrop 1, .str "Return"]) = true := by with_unfolding_all rfl

-- The drop after Return is a disconnected conservative component. Connecting
-- it to the preceding move would manufacture an invalid empty fact.
example : acceptBody (llbc [assign 0 (use (move 1)), .str "Return", structuredDrop 1]) = false := by with_unfolding_all rfl
example : acceptBody (llbc [assign 0 (use (move 1)), .str "UnwindResume", structuredDrop 1]) = false := by with_unfolding_all rfl
example : acceptBody (llbc [assign 0 (use (move 1)), ctor "Abort" (.str "UnwindTerminate"),
    structuredDrop 1]) = false := by with_unfolding_all rfl
example : acceptBody (llbc [ctor "Loop" (structuredBlock []), structuredDrop 1]) = false := by with_unfolding_all rfl
example : acceptBody (llbc [ctor "Break" 0, structuredDrop 1]) = false := by with_unfolding_all rfl
example : acceptBody (llbc [ctor "Continue" 0, structuredDrop 1]) = false := by with_unfolding_all rfl

end AeneasSpecs.DropJson.Tests
