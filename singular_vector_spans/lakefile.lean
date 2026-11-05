import Lake
open Lake DSL

package singular_vector_spans where
  fixedToolchain := true
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "1626233321dc564d20355d8f9d4f22e114d68600"

@[default_target]
target verify pkg : Unit := do
  return ← Job.async do
    let child ← IO.Process.spawn {
      cmd := "python3"
      args := #["verification/run.py"]
      cwd := some pkg.dir
    }
    let code ← child.wait
    if code != 0 then
      error s!"Proof verification failed (exit {code})."
