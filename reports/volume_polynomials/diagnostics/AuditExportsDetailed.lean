module
public import LeanExport.Parse
public import Lean.Data.Json
public import Lean.Util.FoldConsts
public import Std.Data.HashSet
@[expose] public section
open Lean
/-! Read-only diagnostic: enumerate every reachable raw dependency mismatch in
existing trusted exports. This is not a substitute for Comparator/NanoDa.
Run with the exact pinned toolchain:
lean --run AuditExports.lean Challenge.export Solution.export comparator.json
No project import or project rebuild is performed. -/

def namesField (j : Json) (field : String) : Except String (Array Name) := do
  let .ok a := j.getObjValAs? (Array String) field | return #[]
  pure (a.map String.toName)

def statementEqual (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type

def hintsText : ReducibilityHints → String
  | .abbrev => "abbrev"
  | .opaque => "opaque"
  | .regular n => s!"regular({n})"

def differenceFields (a b : ConstantInfo) : String :=
  let common := s!"type_eq={a.type == b.type} levels_eq={a.levelParams == b.levelParams}"
  match a,b with
  | .defnInfo x,.defnInfo y =>
      common ++ s!" value_eq={x.value == y.value} hints_challenge={hintsText x.hints} hints_solution={hintsText y.hints} safety_eq={x.safety == y.safety} mutual_names_eq={x.all == y.all}"
  | .thmInfo x,.thmInfo y =>
      common ++ s!" value_eq={x.value == y.value} mutual_names_eq={x.all == y.all}"
  | _,_ => common

def deps (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    ds := ds ++ value.getUsedConstants
  match ci with
  | .inductInfo i => ds := ds ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => ds := ds.push i.induct
  | .recInfo i =>
      for rule in i.rules do
        ds := (ds.push rule.ctor) ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return ds

def main (args : List String) : IO UInt32 := do
  let [challengePath,solutionPath,configPath] := args
    | IO.eprintln "usage: AuditExports.lean Challenge.export Solution.export comparator.json"; return 2
  let challenge ← IO.FS.withFile challengePath .read fun h =>
    LeanExport.parseStream (IO.FS.Stream.ofHandle h)
  let solution ← IO.FS.withFile solutionPath .read fun h =>
    LeanExport.parseStream (IO.FS.Stream.ofHandle h)
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile configPath))
  let theorems ← IO.ofExcept (namesField config "theorem_names")
  let definitions ← IO.ofExcept (namesField config "definition_names")
  let selected : Std.HashSet Name := Std.HashSet.ofArray (theorems ++ definitions)
  let mut work := theorems ++ definitions
  let mut seen : Std.HashSet Name := {}
  let mut mismatches := 0
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some a := challenge.constMap[n]?
      | IO.println s!"MISSING_CHALLENGE {n}"; mismatches := mismatches + 1; continue
    let some b := solution.constMap[n]?
      | IO.println s!"MISSING_SOLUTION {n}"; mismatches := mismatches + 1; continue
    if selected.contains n then
      if !statementEqual a b then
        IO.println s!"SELECTED_STATEMENT_MISMATCH {n}"
        mismatches := mismatches + 1
      work := work ++ b.type.getUsedConstants
    else
      if a != b then
        let category := if statementEqual a b then "VALUE_OR_METADATA" else "STATEMENT"
        IO.println s!"RAW_{category}_MISMATCH {n} theorem={b.isTheorem} {differenceFields a b}"
        mismatches := mismatches + 1
      -- Continue through both values to enumerate the entire failure class.
      work := work ++ deps a ++ deps b
  IO.println s!"AUDIT_COMPLETE visited={seen.size} mismatches={mismatches}"
  return 0
