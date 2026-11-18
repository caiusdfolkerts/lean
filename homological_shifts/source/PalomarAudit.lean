module
public import Lean

/-! Optional preparation audit reports.
All kernel, axiom, declaration and endpoint validation remains at its original
call site. Only these two filesystem output operations tolerate a read-only
working tree. JSON construction and all later validation exceptions remain
outside these handlers. No mathematical definition or proof calls this module.
-/

namespace PalomarAudit
/-- Attempt to create the output directory; output is optional in the verifier. -/
public def createDirAll (path : System.FilePath) : IO Unit := do
  try IO.FS.createDirAll path catch _ => pure ()
/-- Attempt to write a report; output is optional in the verifier. -/
public def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  try IO.FS.writeFile path contents catch _ => pure ()
end PalomarAudit
