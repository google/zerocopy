import Lean
initialize do
  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""
  if !p.isEmpty then IO.FS.writeFile p "plugin-v1"
