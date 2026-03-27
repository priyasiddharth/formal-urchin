import Lake
open Lake DSL

package «formal-urchin» where
  srcDir := "src"

lean_lib Interp where
  roots := #[`interp]

lean_lib Obseq where
  roots := #[`obseq]

@[default_target]
lean_exe «formal-urchin» where
  root := `Main
  supportInterpreter := true

lean_exe «interp-tests» where
  root := `InterpTests
  supportInterpreter := true
