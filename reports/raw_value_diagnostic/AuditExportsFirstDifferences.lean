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
  `PalomarProjectionAreas.positive_rank_three_obstruction,
  `PalomarProjectionAreas.positive_rank_le_three_not_realizable,
  `PalomarProjectionAreas.escapeCone_eq_divergingDiameterLimits,
  `PalomarProjectionAreas.closure_realizationLocus_eq_union_escapeCone,
  `PalomarProjectionAreas.mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence,
  `PalomarProjectionAreas.escapeCone_isClosed,
  `PalomarProjectionAreas.strict_weighted_realization_with_vertex_bound,
  `PalomarProjectionAreas.strict_nonnegative_weighted_realization_with_vertex_bound,
  `PalomarProjectionAreas.boundary_quartets_bound_sharp,
  `PalomarProjectionAreas.boundary_quartets_unique_extension,
  `PalomarProjectionAreas.selected_boundary_quartets_card_le_three,
  `PalomarProjectionAreas.selected_boundary_quartets_unique_extension,
  `PalomarProjectionAreas.exists_open_nonrealizable_strict_quartets,
  `PalomarProjectionAreas.weighted_triangles_obstruction,
  `PalomarProjectionAreas.rank_at_most_three_classification,
  `PalomarProjectionAreas.NumericProofs.twoNeZero,
  `PalomarProjectionAreas.NumericProofs.twoAtLeastTwo,
  `PalomarProjectionAreas.NumericProofs.fourNeZero]

def selectedTypeSummary (a b : ConstantInfo)
    (candidates : Array (String × Expr × Expr)) (emitted : Nat) : Json :=
  let ac := reprStr a.type
  let bc := reprStr b.type
  let noLeaves := !(a.type == b.type) && candidates.isEmpty
  let depthLimit := candidates.any (fun entry => entry.1.endsWith ".depth-limit")
  let candidateCap := decide (6 ≤ candidates.size)
  let emitCap := decide (emitted < candidates.size)
  Json.mkObj [
    ("kind", toJson "PRINCIPAL_TYPE_SUMMARY"), ("name", toJson a.name.toString),
    ("type_equal", toJson (a.type == b.type)),
    ("level_params_equal", toJson (a.levelParams == b.levelParams)),
    ("challenge_level_params", toJson (a.levelParams.map Name.toString)),
    ("solution_level_params", toJson (b.levelParams.map Name.toString)),
    ("challenge_type_characters", toJson ac.length),
    ("solution_type_characters", toJson bc.length),
    ("type_ast_text", toJson "See bounded explicit raw first-difference leaves; no implicit argument suppression."),
    ("candidate_leaf_limit", toJson (6 : Nat)),
    ("returned_candidate_count", toJson candidates.size),
    ("candidate_limit_reached", toJson candidateCap),
    ("candidate_search_depth_limit", toJson (96 : Nat)),
    ("candidate_search_depth_limit_reached", toJson depthLimit),
    ("emission_limit_per_endpoint", toJson (1 : Nat)),
    ("emitted_leaf_count", toJson emitted),
    ("candidate_leaves_not_emitted", toJson (candidates.size - emitted)),
    ("emission_truncated", toJson emitCap),
    ("unequal_type_without_leaves", toJson noLeaves),
    ("bounded_difference_enumeration_incomplete", toJson (noLeaves || depthLimit || candidateCap || emitCap))]

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
  -- Inspect all eighteen selected types before walking dependencies so bounded
  -- retention cannot lose an endpoint behind a large dependency mismatch list.
  let mut typeLeaves := 0
  let mut principalReported := 0
  let mut principalMissing := 0
  let mut unequalWithoutLeaves := 0
  for n in principalEndpoints do
    let some a := challenge.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_CHALLENGE {n}"
        principalMissing := principalMissing + 1
        continue
    let some b := solution.constMap[n]?
      | IO.println s!"MISSING_PRINCIPAL_SOLUTION {n}"
        principalMissing := principalMissing + 1
        continue
    let candidates := firstExprDifferences a.type b.type "type"
    let emitted := candidates.extract 0 (min 1 (64 - typeLeaves))
    IO.println (selectedTypeSummary a b candidates emitted.size).compress
    if n.toString.startsWith "PalomarProjectionAreas.NumericProofs." then
      let challengeTypeText := reprStr a.type
      let solutionTypeText := reprStr b.type
      IO.println (Json.mkObj [("kind", toJson "NUMERIC_SUPPORT_COMPLETE_TYPE"),
        ("name", toJson n.toString),
        ("challenge_type", toJson (String.ofList (challengeTypeText.toList.take 8000))),
        ("solution_type", toJson (String.ofList (solutionTypeText.toList.take 8000))),
        ("challenge_type_characters", toJson challengeTypeText.length),
        ("solution_type_characters", toJson solutionTypeText.length),
        ("type_text_limit", toJson (8000 : Nat)),
        ("challenge_type_truncated", toJson (decide (8000 < challengeTypeText.length))),
        ("solution_type_truncated", toJson (decide (8000 < solutionTypeText.length)))]).compress
    principalReported := principalReported + 1
    if !(a.type == b.type) && candidates.isEmpty then
      unequalWithoutLeaves := unequalWithoutLeaves + 1
      IO.println s!"PRINCIPAL_TYPE_DIAGNOSTIC_INCOMPLETE {n} unequal_type_without_difference_leaf"
    for (path, x, y) in emitted do
      IO.println (Json.mkObj [("kind", toJson "PRINCIPAL_TYPE_DIFFERENCE"),
        ("name", toJson n.toString), ("path", toJson path),
        ("challenge", toJson (boundedExprText x)),
        ("solution", toJson (boundedExprText y)),
        ("node_text_limit", toJson (500 : Nat)),
        ("challenge_node_characters", toJson (reprStr x).length),
        ("solution_node_characters", toJson (reprStr y).length),
        ("challenge_node_text_truncated", toJson (decide (500 < (reprStr x).length))),
        ("solution_node_text_truncated", toJson (decide (500 < (reprStr y).length)))]).compress
      typeLeaves := typeLeaves + 1
  IO.println (Json.mkObj [("kind", toJson "PRINCIPAL_TYPE_COVERAGE"),
    ("expected_endpoints", toJson principalEndpoints.size),
    ("reported_endpoints", toJson principalReported),
    ("missing_endpoints", toJson principalMissing),
    ("unequal_types_without_leaves", toJson unequalWithoutLeaves),
    ("global_type_leaf_limit", toJson (64 : Nat)),
    ("emitted_type_leaves", toJson typeLeaves),
    ("global_type_limit_reached", toJson (decide (64 ≤ typeLeaves)))]).compress
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
