import Lean.Environment
import Lean.Data.Json

open Lean

/-- Keep facet order identical to the compiler's loader. Each invocation compares
two artifacts, so both compacted regions can stay live until process exit. -/
def loadFacets (base : String) : IO (NameMap ConstantInfo × NameMap ConstantInfo) := do
  let files : Array System.FilePath := #[base, base ++ ".server", base ++ ".private"]
  let parts ← Lean.readModuleDataParts files
  unless parts.size == 3 && parts[0]!.1.isModule do
    throw <| IO.userError s!"Expected three module facets: {base}"
  let mut publicDecls : NameMap ConstantInfo := {}
  let mut complete : NameMap ConstantInfo := {}
  for i in [:parts.size] do
    let data := parts[i]!.1
    unless data.constNames == data.constants.map (·.name) do
      throw <| IO.userError s!"Invalid declaration index: {base}"
    for info in data.constants do
      if i == 0 then publicDecls := publicDecls.insert info.name info
      complete := complete.insert info.name info
  return (publicDecls, complete)

def assertTypes (left right : NameMap ConstantInfo) (allowExposureChange : Bool) : IO Unit := do
  unless left.toList.length == right.toList.length do
    throw <| IO.userError "Declaration inventory differs"
  for (name, a) in left.toList do
    let some b := right.find? name | throw <| IO.userError s!"Missing declaration: {name}"
    unless a.levelParams == b.levelParams && Expr.equal a.type b.type &&
        a.isUnsafe == b.isUnsafe && a.isPartial == b.isPartial do
      throw <| IO.userError s!"Declaration signature differs: {name}"
    if !allowExposureChange then
      match a, b with
      | .thmInfo a, .thmInfo b =>
        unless a.all == b.all do throw <| IO.userError s!"Mutual group differs: {name}"
      | .axiomInfo _, .axiomInfo _ | .defnInfo _, .defnInfo _ |
        .opaqueInfo _, .opaqueInfo _ | .quotInfo _, .quotInfo _ |
        .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _ |
        .recInfo _, .recInfo _ => pure ()
      | _, _ => throw <| IO.userError s!"Declaration kind differs: {name}"

def main (args : List String) : IO Unit := do
  let [mode, leftPath, rightPath] := args | throw <| IO.userError "Expected mode left right"
  unless ["repeat", "exposure", "quota"].contains mode do
    throw <| IO.userError "Unknown comparison mode"
  let start ← IO.monoNanosNow
  let (leftPublic, leftFull) ← loadFacets leftPath
  let (rightPublic, rightFull) ← loadFacets rightPath
  let loaded ← IO.monoNanosNow
  assertTypes leftPublic rightPublic (mode == "exposure")
  if mode == "repeat" then assertTypes leftFull rightFull false
  let typesChecked ← IO.monoNanosNow
  let names := if mode == "repeat" then leftFull.toList else leftPublic.toList
  let mut theoremBodies := 0
  let mut differentBodies := 0
  for (name, _) in names do
    match leftFull.find? name, rightFull.find? name with
    | some (.thmInfo a), some (.thmInfo b) =>
      theoremBodies := theoremBodies + 1
      if !Expr.equal a.value b.value then differentBodies := differentBodies + 1
    | _, _ => pure ()
  let bodiesChecked ← IO.monoNanosNow
  IO.println <| (Json.mkObj [
    ("facet_load_ns", toJson (loaded - start)),
    ("type_comparison_ns", toJson (typesChecked - loaded)),
    ("theorem_body_comparison_ns", toJson (bodiesChecked - typesChecked)),
    ("theorem_bodies_compared", toJson theoremBodies),
    ("theorem_bodies_different", toJson differentBodies),
    ("public_declarations", toJson leftPublic.toList.length),
    ("baseline_full_declarations", toJson leftFull.toList.length),
    ("other_full_declarations", toJson rightFull.toList.length)]).compress
