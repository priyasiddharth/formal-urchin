import interp.test_mirlight
import interp.test_oseairlight
import interp.test_compile

def main : IO Unit := do
  IO.println "Running interp tests"
  Interp.TestMirlight.runAll
  Interp.TestOseairlight.runAll
  Interp.TestCompile.runAll
  IO.println "interp tests passed"
