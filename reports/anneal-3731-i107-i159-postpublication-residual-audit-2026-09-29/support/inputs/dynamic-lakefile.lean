import Lake
open Lake DSL
run_cmd do
  let some path ← IO.getEnv "I126_MARKER_PATH" | throwError "missing marker path"
  IO.FS.writeFile path "lake config executed\n"
package trust_fixture
@[default_target]
lean_lib Dep
