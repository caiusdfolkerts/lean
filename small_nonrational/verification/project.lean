import Lake
open Lake DSL

package smallNonrational where
  fixedToolchain := true
  requiresModuleSystem := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

/-- Explicit module ownership prevents this library from shadowing Mathlib. -/
@[default_target]
lean_lib SmallNonrational where
  srcDir := "Sources"
  roots := #[]
  globs := ((include_str "audit/modules.txt").splitOn "\n").filterMap
    (fun name => if name.isEmpty then none else some (Glob.one name.toName)) |>.toArray
  moreLeanArgs := #["-t1", "-j1", "-s65536", "-DmaxHeartbeats=0",
    "-DElab.async=false", "-Ddebug.skipKernelTC=false"]

