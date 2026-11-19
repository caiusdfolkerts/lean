module
public meta import GraphGeometry
public meta import CertificateNumbers

/-! A graph module stores the 46 independent scalars of each record.
Two catalogue-wide pools index the cells for the small and six-facet
families. The other twelve fields are restored from cell incidences. -/

public meta section
open Lean Elab Term
namespace GeometricRecordFiles
open GraphNumerals CertificateNumbers

initialize cachedPools : IO.Ref (Std.HashMap String (Std.HashMap Nat PoolCell)) ← IO.mkRef {}

private def sharedPool (filename : String) : TermElabM (Std.HashMap Nat PoolCell) := do
  let parent := (System.FilePath.mk (← getFileName)).parent.getD "."
  let p := parent/filename
  if let some pool := (← cachedPools.get)[p.toString]? then return pool
  let some pool := readPool (← load p) | throwError "invalid shared cell pool"
  cachedPools.modify (·.insert p.toString pool)
  return pool

private def recordAt (poolName : String) (i : Nat) : TermElabM Expr := do
  let independent ← load (← sibling "gpack")
  unless (i + 1) * 46 ≤ independent.size do throwError "record index out of range"
  let fields := independent.extract (i*46) ((i+1)*46)
  let some full := expandGeometry fields (← sharedPool poolName) | throwError "invalid geometric data"
  mkRecord full

elab "smallFacetRecord% " n:num : term => recordAt "SmallFacetCells.gpool" n.getNat
elab "sixFacetRecord% " n:num : term => recordAt "SixFacetCells.gpool" n.getNat

end GeometricRecordFiles
