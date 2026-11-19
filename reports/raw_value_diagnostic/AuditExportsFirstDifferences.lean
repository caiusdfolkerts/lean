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

/-- Stop after at most six genuine raw AST differences; never visit later
branches after the cap, and retain explicit depth/candidate truncation flags. -/
partial def firstExprDifferences (a b : Expr) (path : String := "value")
    (fuel : Nat := 96) (limit : Nat := 6) : Array (String × Expr × Expr) := Id.run do
  if limit == 0 || a == b then return #[]
  if fuel == 0 then return #[(path ++ ".depth-limit", a, b)]
  let recur := fun x y suffix cap => firstExprDifferences x y (path ++ suffix) (fuel-1) cap
  match a,b with
  | .app af aa, .app bf ba =>
      let first := recur af bf ".fn" limit
      if first.size >= limit then return first
      return first ++ recur aa ba ".arg" (limit-first.size)
  | .lam an aty ab ai, .lam bn bty bb bi
  | .forallE an aty ab ai, .forallE bn bty bb bi =>
      if an != bn || ai != bi then return #[(path ++ ".binder-metadata",a,b)]
      let first := recur aty bty ".domain" limit
      if first.size >= limit then return first
      return first ++ recur ab bb ".body" (limit-first.size)
  | .letE an aty av ab ai, .letE bn bty bv bb bi =>
      if an != bn || ai != bi then return #[(path ++ ".let-metadata",a,b)]
      let first := recur aty bty ".type" limit
      if first.size >= limit then return first
      let second := first ++ recur av bv ".value" (limit-first.size)
      if second.size >= limit then return second
      return second ++ recur ab bb ".body" (limit-second.size)
  | .mdata _ ab, .mdata _ bb =>
      let ds := recur ab bb ".body" limit
      return if ds.isEmpty then #[(path ++ ".metadata",a,b)] else ds
  | .proj an ai ab, .proj bn bi bb =>
      if an != bn || ai != bi then return #[(path ++ ".projection",a,b)]
      return recur ab bb ".body" limit
  | _,_ => return #[(path,a,b)]

/-- A shallow exact constructor/head description, never `reprStr` of an Expr.
Full shared-DAG AST size is deliberately not computed or rendered. -/
def shallowExprText (e : Expr) : String :=
  match e with
  | .const n levels => s!"const {reprStr n} levels={reprStr levels}"
  | .bvar i => s!"bvar {i}"
  | .fvar i => s!"fvar {reprStr i}"
  | .mvar i => s!"mvar {reprStr i}"
  | .sort level => s!"sort {reprStr level}"
  | .lit value => s!"lit {reprStr value}"
  | .app _ _ => s!"app head={(match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant")} full_ast_not_rendered=true"
  | .lam n _ _ bi => s!"lam binder={reprStr n} binder_info={reprStr bi} full_ast_not_rendered=true"
  | .forallE n _ _ bi => s!"forallE binder={reprStr n} binder_info={reprStr bi} full_ast_not_rendered=true"
  | .letE n _ _ _ nd => s!"letE binder={reprStr n} nondep={nd} full_ast_not_rendered=true"
  | .mdata _ _ => "mdata full_ast_not_rendered=true"
  | .proj n i _ => s!"proj {reprStr n} {i} full_ast_not_rendered=true"

def boundedExprText (e : Expr) : String :=
  String.ofList ((shallowExprText e).toList.take 500)

-- The early helper compile executes this bounded stress control BEFORE any
-- source build. Two shared DAGs denote >2^40 expanded leaves; traversal must
-- stop after six, and rendering must stay shallow. No mathematical source used.
#eval do
  let mut a := mkConst `Nat.zero
  let mut b := mkConst `Nat.succ
  for _ in [:40] do
    a := .app a a
    b := .app b b
  let differences := firstExprDifferences a b
  unless differences.size == 6 do throw (IO.userError "bounded DAG difference fixture failed")
  unless (firstExprDifferences a a).isEmpty do throw (IO.userError "equal DAG fixture failed")
  unless (boundedExprText a).length ≤ 500 do throw (IO.userError "shallow render fixture failed")
  IO.println "SAFE_RAW_HELPER_FIXTURE_PASS shared_dag_depth=40 candidate_count=6 shallow_text_limit=500"

def terminalTypeHead : Expr → String × Nat
  | .forallE _ _ b _ => let (head, count) := terminalTypeHead b; (head, count+1)
  | e => ((match e.getAppFn with | .const n _ => n.toString | _ => "nonconstant"), 0)

def rawTypeContext (a b : ConstantInfo) : Json :=
  let (ah, ac) := terminalTypeHead a.type
  let (bh, bc) := terminalTypeHead b.type
  Json.mkObj [("kind", toJson "RAW_TYPE_CONTEXT"), ("name", toJson a.name.toString),
    ("types_equal", toJson (a.type == b.type)),
    ("challenge_levels", toJson (a.levelParams.map Name.toString)),
    ("solution_levels", toJson (b.levelParams.map Name.toString)),
    ("challenge_conclusion_head", toJson ah), ("solution_conclusion_head", toJson bh),
    ("challenge_binders", toJson ac), ("solution_binders", toJson bc),
    ("challenge_type_characters", toJson "not-computed; shared AST never rendered"),
    ("solution_type_characters", toJson "not-computed; shared AST never rendered"),
    ("type_ast_not_printed", toJson true)]

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
  -- Report EVERY configured target before any reachable dependency traversal.
  let mut reported := 0
  let mut missing := 0
  let mut endpointLeaves := 0
  for n in theorems do
    let some a := challenge.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_CHALLENGE {n}"
        missing := missing+1
        continue
    let some b := solution.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_SOLUTION {n}"
        missing := missing+1
        continue
    let candidates := firstExprDifferences a.type b.type "type"
    let emitted := candidates.extract 0 (min 1 (48-endpointLeaves))
    reported := reported+1
    IO.println (Json.mkObj [("kind", toJson "PRINCIPAL_TYPE_SUMMARY"),
      ("name", toJson n.toString), ("type_equal", toJson (a.type == b.type)),
      ("level_params_equal", toJson (a.levelParams == b.levelParams)),
      ("challenge_level_params", toJson (a.levelParams.map Name.toString)),
      ("solution_level_params", toJson (b.levelParams.map Name.toString)),
      ("type_ast_not_rendered", toJson true),
      ("returned_candidates", toJson candidates.size),
      ("emitted_candidates", toJson emitted.size),
      ("candidate_limit", toJson (6 : Nat)),
      ("depth_limit", toJson (96 : Nat)),
      ("candidate_limit_reached", toJson (decide (6 ≤ candidates.size))),
      ("depth_limit_reached", toJson (candidates.any (fun x => x.1.endsWith ".depth-limit"))),
      ("omitted_candidates", toJson (candidates.size-emitted.size)),
      ("unequal_types_without_leaves", toJson (!(a.type == b.type) && candidates.isEmpty))]).compress
    for (path,x,y) in emitted do
      IO.println (Json.mkObj [("kind",toJson "PRINCIPAL_TYPE_DIFFERENCE"),
        ("name",toJson n.toString),("path",toJson path),
        ("challenge",toJson (boundedExprText x)),("solution",toJson (boundedExprText y)),
        ("full_ast_not_rendered",toJson true),("node_summary_limit",toJson (500 : Nat))]).compress
      endpointLeaves := endpointLeaves+1
  IO.println (Json.mkObj [("kind",toJson "PRINCIPAL_TYPE_COVERAGE"),
    ("expected_endpoints",toJson theorems.size),("reported_endpoints",toJson reported),
    ("missing_endpoints",toJson missing),("emitted_type_leaves",toJson endpointLeaves),
    ("global_type_leaf_limit",toJson (48 : Nat))]).compress
  let mut work := theorems ++ definitions
  let mut seen : Std.HashSet Name := {}
  let mut mismatches := 0
  let mut rawLeaves := 0
  let mut typeLeaves := 0
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
        IO.println (rawTypeContext a b).compress
        if !(a.type == b.type) then
          let candidates := firstExprDifferences a.type b.type "type"
          let emitted := candidates.extract 0 (48-typeLeaves)
          let depthLimit := candidates.any (fun entry => entry.1.endsWith ".depth-limit")
          IO.println (Json.mkObj [("kind", toJson "RAW_TYPE_DIFFERENCE_BOUNDS"),
            ("name", toJson n.toString), ("returned_candidates", toJson candidates.size),
            ("candidate_limit", toJson (6 : Nat)),
            ("candidate_limit_reached", toJson (decide (6 ≤ candidates.size))),
            ("emitted_candidates", toJson emitted.size),
            ("omitted_candidates", toJson (candidates.size-emitted.size)),
            ("depth_limit", toJson (96 : Nat)), ("depth_limit_reached", toJson depthLimit),
            ("global_limit", toJson (48 : Nat)),
            ("global_limit_reached", toJson (decide (48 ≤ typeLeaves))),
            ("unequal_types_without_leaves", toJson candidates.isEmpty),
            ("bounded_enumeration_incomplete", toJson (candidates.isEmpty || depthLimit ||
              decide (6 ≤ candidates.size) || decide (emitted.size < candidates.size)))]).compress
          for (path, x, y) in emitted do
            IO.println (Json.mkObj [("kind", toJson "RAW_TYPE_EXPR_DIFFERENCE"),
              ("name", toJson n.toString), ("path", toJson path),
              ("challenge", toJson (boundedExprText x)), ("solution", toJson (boundedExprText y)),
              ("node_text_limit", toJson (500 : Nat)),
              ("challenge_shallow_summary_characters", toJson (shallowExprText x).length),
              ("solution_shallow_summary_characters", toJson (shallowExprText y).length),
              ("challenge_shallow_summary_truncated", toJson (decide (500 < (shallowExprText x).length))),
              ("solution_shallow_summary_truncated", toJson (decide (500 < (shallowExprText y).length))),
              ("full_ast_not_rendered", toJson true)]).compress
            typeLeaves := typeLeaves+1
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
                  ("challenge_shallow_summary_characters", toJson (shallowExprText x).length),
                  ("solution_shallow_summary_characters", toJson (shallowExprText y).length),
                  ("challenge_shallow_summary_truncated", toJson (decide (500 < (shallowExprText x).length))),
                  ("solution_shallow_summary_truncated", toJson (decide (500 < (shallowExprText y).length))),
              ("full_ast_not_rendered", toJson true)]).compress
                rawLeaves := rawLeaves + 1
      -- Continue through both values to enumerate the entire failure class.
      work := work ++ deps a ++ deps b
  IO.println s!"AUDIT_COMPLETE visited={seen.size} mismatches={mismatches} raw_difference_leaves={rawLeaves} raw_type_difference_leaves={typeLeaves}"
  return 0
