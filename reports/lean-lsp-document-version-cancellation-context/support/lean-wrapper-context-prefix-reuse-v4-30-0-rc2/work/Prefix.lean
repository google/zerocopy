import Lean
open Lean Elab Command
run_cmd do
  let p := "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/support/work/ticks.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "A\n")
namespace N
run_cmd do
  let p := "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/support/work/ticks.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "B\n")
set_option maxRecDepth 1000
run_cmd do
  let p := "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/support/work/ticks.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "C\n")
def generated : Nat := 1
run_cmd do
  let p := "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/support/work/ticks.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "D\n")
theorem target : generated = 1 := by decide
run_cmd do
  let p := "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3730-lean-wrapper-context-prefix-reuse-v4-30-0-rc2/support/work/ticks.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "E\n")
end N
