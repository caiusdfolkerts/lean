import Lake
open Lake DSL

package toric_power_maps where
  fixedToolchain := true
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

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

