
import Lake
open Lake DSL

require aeneas from git "file:///usr/local/google/home/joshlf/workspace/zerocopy/anneal/lean-annotation/anneal/target/anneal-home/.anneal/toolchain/x86_64-unknown-linux-gnu-0191de6c9fa5/backends/lean" @ "main" -- 42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4

package anneal_verification

@[default_target]
lean_lib «Generated» where
  srcDir := "generated"
  roots := #[`Generated, `CoalescedTestSpecse8b55aca9078daf9.FunsExternal, `CoalescedTestSpecse8b55aca9078daf9.Funs, `CoalescedTestSpecse8b55aca9078daf9.Types]

@[default_target]
lean_lib «Anneal» where
  srcDir := "anneal"
  roots := #[`Config, `Anneal]

lean_lib «User» where
  srcDir := "user"
