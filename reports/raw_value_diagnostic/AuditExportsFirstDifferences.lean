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
              let candidates := firstExprDifferences av bv
              let emitted := candidates.extract 0 (48 - rawLeaves)
              let depthLimit := candidates.any (fun entry => entry.1.endsWith ".depth-limit")
              let noLeaves := !(av == bv) && candidates.isEmpty
              IO.println (Json.mkObj [("kind", toJson "RAW_VALUE_DIFFERENCE_BOUNDS"),
                ("name", toJson n.toString), ("values_equal", toJson (av == bv)),
                ("candidate_limit", toJson (6 : Nat)),
                ("returned_candidates", toJson candidates.size),
                ("candidate_limit_reached", toJson (decide (6 ≤ candidates.size))),
                ("depth_limit", toJson (96 : Nat)), ("depth_limit_reached", toJson depthLimit),
                ("emitted_candidates", toJson emitted.size),
                ("omitted_candidates", toJson (candidates.size - emitted.size)),
                ("global_limit", toJson (48 : Nat)),
                ("global_limit_reached", toJson (decide (48 ≤ rawLeaves))),
                ("unequal_values_without_leaves", toJson noLeaves),
                ("bounded_enumeration_incomplete", toJson
                  (noLeaves || depthLimit || decide (6 ≤ candidates.size) ||
                    decide (emitted.size < candidates.size)))]).compress
              for (path, x, y) in emitted do
                IO.println (Json.mkObj [("kind", toJson "RAW_EXPR_DIFFERENCE"),
                  ("name", toJson n.toString), ("path", toJson path),
                  ("challenge", toJson (boundedExprText x)),
                  ("solution", toJson (boundedExprText y)),
                  ("node_text_limit", toJson (500 : Nat)),
                  ("challenge_node_characters", toJson (reprStr x).length),
                  ("solution_node_characters", toJson (reprStr y).length),
                  ("challenge_node_truncated", toJson (decide (500 < (reprStr x).length))),
                  ("solution_node_truncated", toJson (decide (500 < (reprStr y).length)))]).compress
                rawLeaves := rawLeaves + 1
      -- Continue through both values to enumerate the entire failure class.
      work := work ++ deps a ++ deps b
  IO.println s!"AUDIT_COMPLETE visited={seen.size} mismatches={mismatches} raw_difference_leaves={rawLeaves}"
  return 0
