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

/-- Bounded raw syntax comparison; no normalization or mathematical inference. -/
partial def firstExprDifferences (a b : Expr) (path : String := "value")
    (fuel : Nat := 96) : Array (String × Expr × Expr) := Id.run do
  if a == b then return #[]
  if fuel == 0 then return #[(path ++ ".depth-limit", a, b)]
  let next := fuel - 1
  let recur := fun x y suffix => firstExprDifferences x y (path ++ suffix) next
  match a, b with
  | .app af aa, .app bf ba =>
      return ((recur af bf ".fn") ++ (recur aa ba ".arg")).extract 0 6
  | .lam _ aty ab _, .lam _ bty bb _ =>
      return ((recur aty bty ".domain") ++ (recur ab bb ".body")).extract 0 6
  | .forallE _ aty ab _, .forallE _ bty bb _ =>
      return ((recur aty bty ".domain") ++ (recur ab bb ".body")).extract 0 6
  | .letE _ aty av ab _, .letE _ bty bv bb _ =>
      return ((recur aty bty ".type") ++ (recur av bv ".value") ++
        (recur ab bb ".body")).extract 0 6
  | .mdata _ ab, .mdata _ bb =>
      let ds := recur ab bb ".body"
      return if ds.isEmpty then #[(path ++ ".metadata", a, b)] else ds
  | .proj an ai ab, .proj bn bi bb =>
      if an != bn || ai != bi then return #[(path ++ ".projection", a, b)]
      return recur ab bb ".body"
  | _, _ => return #[(path, a, b)]

def boundedExprText (e : Expr) : String :=
  String.ofList ((reprStr e).toList.take 500)

def principalEndpoints : Array Name := #[
  `PalomarHomological.stabilization,
  `PalomarHomological.twistedStabilization,
  `PalomarHomological.exactRankFormula,
  `PalomarHomological.canonicalRank]

def selectedTypeSummary (a b : ConstantInfo) : Json :=
  let ac := reprStr a.type
  let bc := reprStr b.type
  Json.mkObj [
    ("kind", toJson "PRINCIPAL_TYPE_SUMMARY"), ("name", toJson a.name.toString),
    ("type_equal", toJson (a.type == b.type)),
    ("level_params_equal", toJson (a.levelParams == b.levelParams)),
    ("challenge_level_params", toJson (a.levelParams.map Name.toString)),
    ("solution_level_params", toJson (b.levelParams.map Name.toString)),
    ("challenge_type_characters", toJson ac.length),
    ("solution_type_characters", toJson bc.length),
    ("challenge_type_complete", toJson (decide (ac.length ≤ 8192))),
    ("solution_type_complete", toJson (decide (bc.length ≤ 8192))),
    ("challenge_type_ast", toJson (String.ofList (ac.toList.take 8192))),
    ("solution_type_ast", toJson (String.ofList (bc.toList.take 8192)))]

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
  -- Inspect all four principal types before walking dependencies so bounded
  -- retention cannot lose an endpoint behind a large dependency mismatch list.
  let mut typeLeaves := 0
  for n in principalEndpoints do
    let some a := challenge.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_CHALLENGE {n}"; continue
    let some b := solution.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_SOLUTION {n}"; continue
    IO.println (selectedTypeSummary a b).compress
    for (path, x, y) in firstExprDifferences a.type b.type "type" do
      if typeLeaves < 48 then
        IO.println (Json.mkObj [("kind", toJson "PRINCIPAL_TYPE_DIFFERENCE"),
          ("name", toJson n.toString), ("path", toJson path),
          ("challenge", toJson (boundedExprText x)),
          ("solution", toJson (boundedExprText y))]).compress
        typeLeaves := typeLeaves + 1
  let mut work := theorems ++ definitions
  let mut seen : Std.HashSet Name := {}
  let mut mismatches := 0
  let mut rawLeaves := 0
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
        IO.println s!"SELECTED_STATEMENT_MISMATCH {n} {differenceFields a b} challenge_levels={reprStr a.levelParams} solution_levels={reprStr b.levelParams}"
        mismatches := mismatches + 1
      work := work ++ b.type.getUsedConstants
    else
      if a != b then
        let category := if statementEqual a b then "VALUE_OR_METADATA" else "STATEMENT"
        IO.println s!"RAW_{category}_MISMATCH {n} theorem={b.isTheorem} {differenceFields a b}"
        mismatches := mismatches + 1
        if !b.isTheorem then
          if let some av := a.value? (allowOpaque := true) then
            if let some bv := b.value? (allowOpaque := true) then
              for (path, x, y) in firstExprDifferences av bv do
                if rawLeaves < 48 then
                  IO.println (Json.mkObj [("kind", toJson "RAW_EXPR_DIFFERENCE"),
                    ("name", toJson n.toString), ("path", toJson path),
                    ("challenge", toJson (boundedExprText x)),
                    ("solution", toJson (boundedExprText y))]).compress
                  rawLeaves := rawLeaves + 1
      -- Continue through both values to enumerate the entire failure class.
      work := work ++ deps a ++ deps b
  IO.println s!"AUDIT_COMPLETE visited={seen.size} mismatches={mismatches} raw_difference_leaves={rawLeaves} principal_type_difference_leaves={typeLeaves}"
  return 0
