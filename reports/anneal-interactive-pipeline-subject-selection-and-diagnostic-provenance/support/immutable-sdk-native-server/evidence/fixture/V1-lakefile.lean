import Lake
open Lake DSL

package anneal_verification where
  plugins := #[Target.mk (.mk (.packageTarget .anonymous `aeneasMetaPlugin))]

target aeneasMetaPlugin : Dynlib := do
  let artifact : System.FilePath := "<PROJECT>/Data/20261003-anneal-v1-validation/bundle/aeneas/backends/lean/.lake/build/lib/libaeneas_AeneasMeta.dylib"
  return (← inputFile artifact false).map fun path =>
    { path := path, name := "aeneas_AeneasMeta", plugin := true }

@[default_target] lean_lib Generated where
  srcDir := "generated"
  roots := #[`Generated, `ExpandOutputExpandOutput1d49e11e5683007f.Funs, `ExpandOutputExpandOutput1d49e11e5683007f.Types]
@[default_target] lean_lib Anneal where
  srcDir := "anneal"
  roots := #[`Config, `SdkIdentity, `Anneal]
