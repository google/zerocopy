-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-! Auto-generated Tier 1 Target Specifications for rustc 1.100.0 -/

namespace Anneal.ToolchainTables

structure Tier1TargetSpec where
  triple : String
  arch : String
  dataLayout : String
  llvmTarget : String
  pointerWidth : Nat
  maxAtomicWidth : Nat
  panicStrategy : String
  i686RustAbiUsesSse : Bool
  deriving Repr, DecidableEq

def spec_x86_64_unknown_linux_gnu : Tier1TargetSpec := {
  triple := "x86_64-unknown-linux-gnu",
  arch := "x86_64",
  dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
  llvmTarget := "x86_64-unknown-linux-gnu",
  pointerWidth := 64,
  maxAtomicWidth := 64,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_aarch64_unknown_linux_gnu : Tier1TargetSpec := {
  triple := "aarch64-unknown-linux-gnu",
  arch := "aarch64",
  dataLayout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32",
  llvmTarget := "aarch64-unknown-linux-gnu",
  pointerWidth := 64,
  maxAtomicWidth := 128,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_i686_unknown_linux_gnu : Tier1TargetSpec := {
  triple := "i686-unknown-linux-gnu",
  arch := "x86",
  dataLayout := "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-i128:128-f64:32:64-f80:32-n8:16:32-S128",
  llvmTarget := "i686-unknown-linux-gnu",
  pointerWidth := 32,
  maxAtomicWidth := 64,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := true
}

def spec_aarch64_apple_darwin : Tier1TargetSpec := {
  triple := "aarch64-apple-darwin",
  arch := "aarch64",
  dataLayout := "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32",
  llvmTarget := "arm64-apple-macosx",
  pointerWidth := 64,
  maxAtomicWidth := 128,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_x86_64_pc_windows_msvc : Tier1TargetSpec := {
  triple := "x86_64-pc-windows-msvc",
  arch := "x86_64",
  dataLayout := "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
  llvmTarget := "x86_64-pc-windows-msvc",
  pointerWidth := 64,
  maxAtomicWidth := 128,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_x86_64_pc_windows_gnu : Tier1TargetSpec := {
  triple := "x86_64-pc-windows-gnu",
  arch := "x86_64",
  dataLayout := "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
  llvmTarget := "x86_64-pc-windows-gnu",
  pointerWidth := 64,
  maxAtomicWidth := 128,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_aarch64_pc_windows_msvc : Tier1TargetSpec := {
  triple := "aarch64-pc-windows-msvc",
  arch := "aarch64",
  dataLayout := "e-m:w-p270:32:32-p271:32:32-p272:64:64-p:64:64-i32:32-i64:64-i128:128-n32:64-S128-Fn32",
  llvmTarget := "aarch64-pc-windows-msvc",
  pointerWidth := 64,
  maxAtomicWidth := 128,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := false
}

def spec_i686_pc_windows_msvc : Tier1TargetSpec := {
  triple := "i686-pc-windows-msvc",
  arch := "x86",
  dataLayout := "e-m:x-p:32:32-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32-a:0:32-S32",
  llvmTarget := "i686-pc-windows-msvc",
  pointerWidth := 32,
  maxAtomicWidth := 64,
  panicStrategy := "unwind",
  i686RustAbiUsesSse := true
}

end Anneal.ToolchainTables
